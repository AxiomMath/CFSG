module

public import CFSG.FeitThompson.OddOrderTheorem
public import Mathlib.GroupTheory.SpecificGroups.KleinFour
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem commutator_le_self_of_le_normalizer {K A : Subgroup G}
    (h : A ≤ normalizer (K : Set G)) : ⁅K, A⁆ ≤ K := by
  rw [commutator_le]
  intro k hk a ha
  rw [show ⁅k, a⁆ = k * (a * k⁻¹ * a⁻¹) by rw [commutatorElement_def]; group]
  exact mul_mem hk ((mem_normalizer_iff.mp (h ha) k⁻¹).mp (inv_mem hk))

theorem le_normalizer_commutator_of_le_normalizers {N H K : Subgroup G}
    (hH : N ≤ normalizer (H : Set G)) (hK : N ≤ normalizer (K : Set G)) :
    N ≤ normalizer ((⁅H, K⁆ : Subgroup G) : Set G) := by
  intro g hg
  rw [mem_normalizer_iff_map_conj_eq, map_commutator, mem_normalizer_iff_map_conj_eq.mp (hH hg),
    mem_normalizer_iff_map_conj_eq.mp (hK hg)]

theorem le_normalizer_commutator_self (K A : Subgroup G) :
    K ≤ normalizer ((⁅K, A⁆ : Subgroup G) : Set G) := by
  have key : ∀ u ∈ K, ∀ x ∈ ⁅K, A⁆, u * x * u⁻¹ ∈ ⁅K, A⁆ := by
    intro u hu x hx
    have hle : ⁅K, A⁆ ≤ ⁅K, A⁆.comap (MulAut.conj u).toMonoidHom := by
      rw [commutator_le]
      intro v hv a ha
      rw [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        show u * ⁅v, a⁆ * u⁻¹ = ⁅u * v, a⁆ * ⁅u, a⁆⁻¹ by simp only [commutatorElement_def]; group]
      exact mul_mem (commutator_mem_commutator (mul_mem hu hv) ha)
        (inv_mem (commutator_mem_commutator hu ha))
    have h1 := mem_comap.mp (hle hx)
    rwa [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h1
  intro u hu
  rw [mem_normalizer_iff]
  intro x
  refine ⟨key u hu x, fun hx => ?_⟩
  have h := key u⁻¹ (inv_mem hu) _ hx
  rwa [show u⁻¹ * (u * x * u⁻¹) * u⁻¹⁻¹ = x by group] at h

theorem conj_commutatorElement_eq_inv {x u : G} (hu : u * u = 1) :
    u * ⁅x, u⁆ * u⁻¹ = ⁅x, u⁆⁻¹ := by
  have hu' : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  calc u * ⁅x, u⁆ * u⁻¹ = u * x * u * x⁻¹ * (u * u)⁻¹ := by rw [commutatorElement_def]; group
    _ = u * x * u * x⁻¹ := by rw [hu, inv_one, mul_one]
    _ = u * x * u⁻¹ * x⁻¹ := by rw [hu']
    _ = ⁅x, u⁆⁻¹ := by rw [commutatorElement_def]; group

theorem odd_orderOf_of_mem_of_odd [Finite G] {X : Subgroup G} (hX : Odd (Nat.card X)) {x : G}
    (hx : x ∈ X) : Odd (orderOf x) :=
  Odd.of_dvd_nat hX (by rw [← Subgroup.orderOf_mk x hx]; exact orderOf_dvd_natCard _)

theorem exists_mul_mem_centralizer [Finite G] {p : ℕ} [Fact p.Prime] {P N : Subgroup G}
    (hP : IsPGroup p P) (hN : ¬ p ∣ Nat.card N) (hPN : P ≤ normalizer (N : Set G)) {y : G}
    (hy : ∀ u ∈ P, y⁻¹ * (u * y * u⁻¹) ∈ N) :
    ∃ n ∈ N, y * n ∈ centralizer (P : Set G) := by
  have hmem : ∀ (u : P) (n : N), y⁻¹ * ((u : G) * (y * n) * (u : G)⁻¹) ∈ N := by
    intro u n
    have e : y⁻¹ * ((u : G) * (y * n) * (u : G)⁻¹) =
        y⁻¹ * ((u : G) * y * (u : G)⁻¹) * ((u : G) * n * (u : G)⁻¹) := by group
    rw [e]
    exact mul_mem (hy u u.2) ((mem_normalizer_iff.mp (hPN u.2) n).mp n.2)
  let _ : MulAction P N :=
    { smul := fun u n => ⟨_, hmem u n⟩
      one_smul := fun n => Subtype.ext (by
        show y⁻¹ * (((1 : P) : G) * (y * n) * ((1 : P) : G)⁻¹) = n
        simp)
      mul_smul := fun u v n => Subtype.ext (by
        show y⁻¹ * (((u * v : P) : G) * (y * n) * ((u * v : P) : G)⁻¹) =
          y⁻¹ * ((u : G) * (y * (y⁻¹ * ((v : G) * (y * n) * (v : G)⁻¹))) * (u : G)⁻¹)
        simp only [Subgroup.coe_mul]
        group) }
  obtain ⟨n, hn⟩ := hP.nonempty_fixed_point_of_prime_not_dvd_card N hN
  refine ⟨n, n.2, mem_centralizer_iff.mpr fun u hu => ?_⟩
  have h : y⁻¹ * (u * (y * n) * u⁻¹) = n :=
    congrArg Subtype.val ((MulAction.mem_fixedPoints.mp hn) ⟨u, hu⟩)
  calc u * (y * n) = y * (y⁻¹ * (u * (y * n) * u⁻¹)) * u := by group
    _ = y * n * u := by rw [h]

theorem commutator_commutator_zpowers_eq [Finite G] {X : Subgroup G} {w : G} (hw : w * w = 1)
    (hX : Odd (Nat.card X)) (hwX : w ∈ normalizer (X : Set G)) :
    ⁅⁅X, zpowers w⁆, zpowers w⁆ = ⁅X, zpowers w⁆ := by
  have hle : zpowers w ≤ normalizer (X : Set G) := zpowers_le.mpr hwX
  apply le_antisymm
  · exact commutator_le_self_of_le_normalizer
      (le_normalizer_commutator_of_le_normalizers hle (le_normalizer (H := zpowers w)))
  · rw [commutator_le]
    intro x hx u hu
    have hu2 : u * u = 1 := by
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hu
      rw [← zpow_add, ← two_mul, zpow_mul, zpow_two, hw, one_zpow]
    have hcmem : ⁅x, u⁆ ∈ ⁅X, zpowers w⁆ := commutator_mem_commutator hx hu
    have hcX : ⁅x, u⁆ ∈ X := commutator_le_self_of_le_normalizer hle hcmem
    obtain ⟨k, hk⟩ := odd_orderOf_of_mem_of_odd hX hcX
    set c := ⁅x, u⁆ with hc
    have hj : u * c ^ (k + 1) * u⁻¹ = (c ^ (k + 1))⁻¹ := by
      rw [← conj_pow, hc, conj_commutatorElement_eq_inv hu2, inv_pow]
    have key : ⁅c ^ (k + 1), u⁆ = c := by
      calc ⁅c ^ (k + 1), u⁆ = c ^ (k + 1) * (u * c ^ (k + 1) * u⁻¹)⁻¹ := by
            rw [commutatorElement_def]; group
        _ = c ^ (k + 1) * c ^ (k + 1) := by rw [hj, inv_inv]
        _ = c ^ (2 * k + 1) * c := by
            rw [← pow_add, ← pow_succ]
            congr 1
            omega
        _ = c := by rw [← hk, pow_orderOf_eq_one, one_mul]
    rw [← key]
    exact commutator_mem_commutator (pow_mem hcmem _) hu

theorem exists_commutator_zpowers_ne [Finite G] {W X : Subgroup G} (hW : IsKleinFour W)
    (hWX : W ≤ normalizer (X : Set G)) (hX : Odd (Nat.card X)) (hX1 : X ≠ ⊥) :
    ∃ w ∈ W, w ≠ 1 ∧ ⁅X, zpowers w⁆ ≠ X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hcon
  push Not at hcon
  set D := ⁅X, X⁆ with hD
  have : Group.IsSolvable X := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hX
  have : Nontrivial X := (nontrivial_iff_ne_bot X).mpr hX1
  have hDlt : D < X := by
    rw [hD, ← X.range_subtype, MonoidHom.range_eq_map, ← map_commutator,
      map_subtype_lt_map_subtype]
    exact Group.IsSolvable.commutator_lt_top_of_nontrivial X
  have hDmem : ∀ x ∈ X, ∀ d ∈ D, x * d * x⁻¹ ∈ D := fun x hx d hd =>
    (mem_normalizer_iff.mp (le_normalizer_commutator_self X X hx) d).mp hd
  have hcommD : ∀ a ∈ X, ∀ b ∈ X, a * b * a⁻¹ * b⁻¹ ∈ D := fun a ha b hb => by
    have := commutator_mem_commutator ha hb
    rwa [commutatorElement_def] at this
  have hsqW : ∀ w ∈ W, w * w = 1 := fun w hw =>
    congrArg Subtype.val (@IsKleinFour.mul_self W _ hW ⟨w, hw⟩)
  have hinv : ∀ w ∈ W, w ≠ 1 → ∀ x ∈ X, w * x * w⁻¹ * x ∈ D := by
    intro w hw hw1 x hx
    have hww := hsqW w hw
    have hwX : ∀ y ∈ X, w * y * w⁻¹ ∈ X := fun y hy =>
      (mem_normalizer_iff.mp (hWX hw) y).mp hy
    have hXle : ⁅X, zpowers w⁆ ≤ X :=
      commutator_le_self_of_le_normalizer (zpowers_le.mpr (hWX hw))
    rw [← hcon w hw hw1, Subgroup.commutator_def] at hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, -, b, hb, rfl⟩ := hy
      have hb' : b = 1 ∨ b = w := by
        obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hb
        have hord : orderOf w = 2 := orderOf_eq_prime (by rw [sq]; exact hww) hw1
        rw [← zpow_mod_orderOf, hord, Nat.cast_ofNat]
        rcases Int.emod_two_eq_zero_or_one k with h | h
        · left
          rw [h, zpow_zero]
        · right
          rw [h, zpow_one]
      rcases hb' with rfl | rfl
      · simp only [commutatorElement_one_right, mul_one, mul_inv_cancel]
        exact one_mem _
      · rw [conj_commutatorElement_eq_inv hww, inv_mul_cancel]
        exact one_mem _
    | one =>
      simp only [mul_one, mul_inv_cancel]
      exact one_mem _
    | mul y z hy hz ihy ihz =>
      have hyX : y ∈ X := hXle (by rw [Subgroup.commutator_def]; exact hy)
      have hzX : z ∈ X := hXle (by rw [Subgroup.commutator_def]; exact hz)
      have e : w * (y * z) * w⁻¹ * (y * z) = (w * y * w⁻¹ * y) *
          (y⁻¹ * (w * z * w⁻¹) * y⁻¹⁻¹ * (w * z * w⁻¹)⁻¹) * (w * z * w⁻¹ * z) := by group
      rw [e]
      exact mul_mem (mul_mem ihy (hcommD _ (inv_mem hyX) _ (hwX z hzX))) ihz
    | inv y hy ihy =>
      have hyX : y ∈ X := hXle (by rw [Subgroup.commutator_def]; exact hy)
      have e : w * y⁻¹ * w⁻¹ * y⁻¹ = (y * (w * y * w⁻¹ * y) * y⁻¹)⁻¹ := by group
      rw [e]
      exact inv_mem (hDmem y hyX _ ihy)
  have : Nontrivial W :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [@IsKleinFour.card_four W _ hW]; norm_num)
  obtain ⟨v₁, hv₁⟩ := exists_ne (1 : W)
  obtain ⟨v₂, hv₂⟩ : ∃ v : W, v ∉ zpowers v₁ := by
    by_contra h
    push Not at h
    exact (@IsKleinFour.not_isCyclic W _ hW) ⟨⟨v₁, fun v => mem_zpowers_iff.mp (h v)⟩⟩
  have hw₁ : (v₁ : G) ≠ 1 := fun h => hv₁ (Subtype.ext h)
  have hw₂ : (v₂ : G) ≠ 1 := by
    intro h
    apply hv₂
    rw [show v₂ = 1 from Subtype.ext h]
    exact one_mem _
  have hw₁₂ : (v₁ : G) * v₂ ≠ 1 := by
    intro h
    apply hv₂
    have : v₂ = v₁ := by
      apply Subtype.ext
      calc (v₂ : G) = (v₁ : G) * (v₁ * v₂) := by
            rw [← mul_assoc, hsqW _ v₁.2, one_mul]
        _ = v₁ := by rw [h, mul_one]
    rw [this]
    exact mem_zpowers _
  have hsq : ∀ x ∈ X, x * x ∈ D := by
    intro x hx
    have ha : (v₂ : G) * x * (v₂ : G)⁻¹ ∈ X := (mem_normalizer_iff.mp (hWX v₂.2) x).mp hx
    have h1 := hinv _ v₂.2 hw₂ x hx
    have h2 := hinv _ v₁.2 hw₁ _ ha
    have h3 := hinv _ (mul_mem v₁.2 v₂.2) hw₁₂ x hx
    have e : x * x = (x * ((v₂ : G) * x * (v₂ : G)⁻¹ * x) * x⁻¹) *
        (((v₁ : G) * ((v₂ : G) * x * (v₂ : G)⁻¹) * (v₁ : G)⁻¹ * ((v₂ : G) * x * (v₂ : G)⁻¹))⁻¹ *
          ((v₁ : G) * v₂ * x * ((v₁ : G) * v₂)⁻¹ * x)) := by group
    rw [e]
    exact mul_mem (hDmem x hx _ h1) (mul_mem (inv_mem h2) h3)
  have hXD : X ≤ D := by
    intro x hx
    obtain ⟨k, hk⟩ := odd_orderOf_of_mem_of_odd hX hx
    have e : x = (x * x) ^ (k + 1) := by
      rw [← sq, ← pow_mul, show 2 * (k + 1) = orderOf x + 1 by omega, pow_succ,
        pow_orderOf_eq_one, one_mul]
    rw [e]
    exact pow_mem (hsq x hx) _
  exact hDlt.not_ge hXD

theorem inf_centralizer_eq_iSup_of_isKleinFour [Finite G] {W X : Subgroup G}
    (hW : IsKleinFour W) (hWX : W ≤ normalizer (X : Set G)) (hX : Odd (Nat.card X))
    (hXW : ⁅X, W⁆ = X) :
    X ⊓ centralizer (W : Set G) =
      ⨆ w ∈ W, ⨆ (_ : w ≠ 1), ⁅X ⊓ centralizer ({w} : Set G), W⁆ ⊓ centralizer (W : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsqW : ∀ w ∈ W, w * w = 1 := fun w hw =>
    congrArg Subtype.val (@IsKleinFour.mul_self W _ hW ⟨w, hw⟩)
  have hcommW : ∀ u ∈ W, ∀ v ∈ W, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (isMulCommutative_iff.mp (@IsKleinFour.isMulCommutative W _ hW)
      ⟨u, hu⟩ ⟨v, hv⟩)
  have hWp : IsPGroup 2 W :=
    IsPGroup.of_card (n := 2) (by rw [@IsKleinFour.card_four W _ hW]; norm_num)
  refine le_antisymm ?_ (iSup₂_le fun w _ => iSup_le fun _ =>
    inf_le_inf_right _ ((commutator_mono inf_le_left le_rfl).trans hXW.le))
  suffices h : ∀ n, ∀ X : Subgroup G, Nat.card X = n → W ≤ normalizer (X : Set G) →
      Odd (Nat.card X) → ⁅X, W⁆ = X →
      X ⊓ centralizer (W : Set G) ≤ ⨆ w ∈ W, ⨆ (_ : w ≠ 1),
        ⁅X ⊓ centralizer ({w} : Set G), W⁆ ⊓ centralizer (W : Set G) from
    h _ X rfl hWX hX hXW
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro X hn hWX hX hXW
  by_cases hX1 : X = ⊥
  · subst hX1
    rw [bot_inf_eq]
    exact bot_le
  obtain ⟨w, hw, hw1, hne⟩ := exists_commutator_zpowers_ne hW hWX hX hX1
  set X₁ := ⁅X, zpowers w⁆ with hX₁
  have hww := hsqW w hw
  have hwN : zpowers w ≤ normalizer (X : Set G) := zpowers_le.mpr (hWX hw)
  have hzW : zpowers w ≤ W := zpowers_le.mpr hw
  have hX₁X : X₁ ≤ X := commutator_le_self_of_le_normalizer hwN
  have hWz : W ≤ normalizer ((zpowers w : Subgroup G) : Set G) := fun u hu =>
    centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun v hv => hcommW _ (hzW hv) _ hu)
  have hWX₁ : W ≤ normalizer (X₁ : Set G) := le_normalizer_commutator_of_le_normalizers hWX hWz
  have hXX₁ : X ≤ normalizer (X₁ : Set G) := le_normalizer_commutator_self X _
  have hX₁odd : Odd (Nat.card X₁) := Odd.of_dvd_nat hX (card_dvd_of_le hX₁X)
  have hX₁W : ⁅X₁, W⁆ = X₁ := by
    refine le_antisymm (commutator_le_self_of_le_normalizer hWX₁) ?_
    calc X₁ = ⁅X₁, zpowers w⁆ := (commutator_commutator_zpowers_eq hww hX (hWX hw)).symm
      _ ≤ ⁅X₁, W⁆ := commutator_mono le_rfl hzW
  have hlt : Nat.card X₁ < n := by
    rw [← hn]
    exact card_lt_of_lt (lt_of_le_of_ne hX₁X hne)
  have hIH : X₁ ⊓ centralizer (W : Set G) ≤ ⨆ w ∈ W, ⨆ (_ : w ≠ 1),
      ⁅X ⊓ centralizer ({w} : Set G), W⁆ ⊓ centralizer (W : Set G) :=
    (ih _ hlt X₁ rfl hWX₁ hX₁odd hX₁W).trans (iSup₂_mono fun v _ => iSup_mono fun _ =>
      inf_le_inf_right _ (commutator_mono (inf_le_inf_right _ hX₁X) le_rfl))
  have hwp : IsPGroup 2 (zpowers w) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, orderOf_eq_prime (by rw [sq]; exact hww) hw1, pow_one])
  have hstepC : ∀ x ∈ X, ∃ c ∈ X ⊓ centralizer ({w} : Set G), c⁻¹ * x ∈ X₁ := by
    intro x hx
    obtain ⟨m, hm, hxm⟩ := exists_mul_mem_centralizer hwp (Nat.two_dvd_ne_zero.mpr
      (Nat.odd_iff.mp hX₁odd)) (hzW.trans hWX₁) (y := x) (fun u hu => by
        rw [show x⁻¹ * (u * x * u⁻¹) = ⁅x⁻¹, u⁆ by rw [commutatorElement_def]; group]
        exact commutator_mem_commutator (inv_mem hx) hu)
    refine ⟨x * m, ⟨mul_mem hx (hX₁X hm), mem_centralizer_singleton_iff.mpr ?_⟩, ?_⟩
    · exact ((mem_centralizer_iff.mp hxm) w (mem_zpowers w)).symm
    · rw [mul_inv_rev, inv_mul_cancel_right]
      exact inv_mem hm
  set Y := ⁅X ⊓ centralizer ({w} : Set G), W⁆ with hY
  have hYX : Y ≤ X := (commutator_mono inf_le_left le_rfl).trans hXW.le
  have hstepD : ∀ x ∈ X, ∃ y ∈ Y, y⁻¹ * x ∈ X₁ := by
    intro x hx
    rw [← hXW, Subgroup.commutator_def] at hx
    induction hx using Subgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, u, hu, rfl⟩ := hz
      obtain ⟨c, hc, hca⟩ := hstepC a ha
      refine ⟨⁅c, u⁆, commutator_mem_commutator hc hu, ?_⟩
      have e : ⁅c, u⁆⁻¹ * ⁅a, u⁆ =
          (u * c) * (u⁻¹ * (c⁻¹ * a) * u⁻¹⁻¹ * (c⁻¹ * a)⁻¹) * (u * c)⁻¹ := by
        rw [commutatorElement_def, commutatorElement_def]; group
      rw [e]
      have huc : u * c ∈ normalizer (X₁ : Set G) := mul_mem (hWX₁ hu) (hXX₁ hc.1)
      refine (mem_normalizer_iff.mp huc _).mp (mul_mem ?_ (inv_mem hca))
      exact (mem_normalizer_iff.mp (hWX₁ (inv_mem hu)) _).mp hca
    | one => exact ⟨1, one_mem _, by rw [inv_one, one_mul]; exact one_mem _⟩
    | mul x₁ x₂ _ _ ih₁ ih₂ =>
      obtain ⟨y₁, hy₁, h₁⟩ := ih₁
      obtain ⟨y₂, hy₂, h₂⟩ := ih₂
      refine ⟨y₁ * y₂, mul_mem hy₁ hy₂, ?_⟩
      have e : (y₁ * y₂)⁻¹ * (x₁ * x₂) = (y₂⁻¹ * (y₁⁻¹ * x₁) * y₂⁻¹⁻¹) * (y₂⁻¹ * x₂) := by group
      rw [e]
      exact mul_mem ((mem_normalizer_iff.mp (hXX₁ (hYX (inv_mem hy₂))) _).mp h₁) h₂
    | inv x _ ih =>
      obtain ⟨y, hy, h⟩ := ih
      refine ⟨y⁻¹, inv_mem hy, ?_⟩
      have e : y⁻¹⁻¹ * x⁻¹ = y * (y⁻¹ * x)⁻¹ * y⁻¹ := by group
      rw [e]
      exact (mem_normalizer_iff.mp (hXX₁ (hYX hy)) _).mp (inv_mem h)
  have hWC : W ≤ normalizer ((X ⊓ centralizer ({w} : Set G) : Subgroup G) : Set G) := by
    intro u hu
    have huw : u * w * u⁻¹ = w := by rw [hcommW u hu w hw, mul_inv_cancel_right]
    rw [mem_normalizer_iff]
    intro z
    simp only [mem_inf, mem_centralizer_singleton_iff]
    refine and_congr (mem_normalizer_iff.mp (hWX hu) z) ⟨fun h => ?_, fun h => ?_⟩
    · calc u * z * u⁻¹ * w = u * z * u⁻¹ * (u * w * u⁻¹) := by rw [huw]
        _ = u * (z * w) * u⁻¹ := by group
        _ = u * (w * z) * u⁻¹ := by rw [h]
        _ = u * w * u⁻¹ * (u * z * u⁻¹) := by group
        _ = w * (u * z * u⁻¹) := by rw [huw]
    · have h' : u * (z * w) * u⁻¹ = u * (w * z) * u⁻¹ := by
        calc u * (z * w) * u⁻¹ = u * z * u⁻¹ * (u * w * u⁻¹) := by group
          _ = w * (u * z * u⁻¹) := by rw [huw, h]
          _ = u * w * u⁻¹ * (u * z * u⁻¹) := by rw [huw]
          _ = u * (w * z) * u⁻¹ := by group
      exact mul_left_cancel (mul_right_cancel h')
  have hWY : W ≤ normalizer (Y : Set G) :=
    le_normalizer_commutator_of_le_normalizers hWC le_normalizer
  have hWYX₁ : W ≤ normalizer ((Y ⊓ X₁ : Subgroup G) : Set G) := by
    intro u hu
    rw [mem_normalizer_iff]
    intro z
    simp only [mem_inf]
    exact and_congr (mem_normalizer_iff.mp (hWY hu) z) (mem_normalizer_iff.mp (hWX₁ hu) z)
  have hYX₁odd : ¬ 2 ∣ Nat.card (Y ⊓ X₁ : Subgroup G) := fun h2 =>
    Nat.not_even_iff_odd.mpr hX₁odd
      (even_iff_two_dvd.mpr (h2.trans (card_dvd_of_le inf_le_right)))
  intro c hc
  obtain ⟨hcX, hcW⟩ := mem_inf.mp hc
  obtain ⟨y, hyY, hyc⟩ := hstepD c hcX
  have hcu : ∀ u ∈ W, u * c = c * u := fun u hu => (mem_centralizer_iff.mp hcW) u hu
  obtain ⟨m, hm, hym⟩ := exists_mul_mem_centralizer hWp hYX₁odd hWYX₁ (y := y) (fun u hu => by
    refine mem_inf.mpr ⟨mul_mem (inv_mem hyY) ((mem_normalizer_iff.mp (hWY hu) y).mp hyY), ?_⟩
    have e : y⁻¹ * (u * y * u⁻¹) = (y⁻¹ * c) * (u * (y⁻¹ * c)⁻¹ * u⁻¹) := by
      calc y⁻¹ * (u * y * u⁻¹) = y⁻¹ * c * (c⁻¹ * (u * c)) * (c⁻¹ * y) * u⁻¹ := by group
        _ = y⁻¹ * c * u * (c⁻¹ * y) * u⁻¹ := by rw [hcu u hu, inv_mul_cancel_left]
        _ = (y⁻¹ * c) * (u * (y⁻¹ * c)⁻¹ * u⁻¹) := by group
    rw [e]
    exact mul_mem hyc ((mem_normalizer_iff.mp (hWX₁ hu) _).mp (inv_mem hyc)))
  have hterm : ⁅X ⊓ centralizer ({w} : Set G), W⁆ ⊓ centralizer (W : Set G) ≤
      ⨆ w ∈ W, ⨆ (_ : w ≠ 1), ⁅X ⊓ centralizer ({w} : Set G), W⁆ ⊓ centralizer (W : Set G) :=
    le_iSup₂_of_le w hw (le_iSup_of_le hw1 le_rfl)
  have e : c = (y * m) * ((y * m)⁻¹ * c) := by group
  rw [e]
  refine mul_mem (hterm (mem_inf.mpr ⟨mul_mem hyY (mem_inf.mp hm).1, hym⟩))
    (hIH (mem_inf.mpr ⟨?_, ?_⟩))
  · rw [mul_inv_rev, mul_assoc]
    exact mul_mem (inv_mem (mem_inf.mp hm).2) hyc
  · exact mul_mem (inv_mem hym) hcW

end CFSG.ComponentClassification.FooteLit
