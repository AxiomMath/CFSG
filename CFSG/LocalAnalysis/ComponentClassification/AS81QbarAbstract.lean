module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.Tactic.NormNum.Prime

public section

namespace CFSG.ComponentClassification.AS81.Qbar

open Subgroup

theorem derivedSeries_add_le {H : Type*} [Group H] {S : Subgroup H} {a : ℕ}
    (ha : derivedSeries H a ≤ S) (b : ℕ) :
    derivedSeries H (a + b) ≤ (derivedSeries S b).map S.subtype := by
  induction b with
  | zero =>
    rw [add_zero, derivedSeries_zero, ← MonoidHom.range_eq_map, range_subtype]
    exact ha
  | succ b ih =>
    rw [← add_assoc, derivedSeries_succ, derivedSeries_succ, map_commutator]
    exact commutator_mono ih ih

section Regular

variable {W : Type*} [Group W]

theorem mem_of_commute_of_transitive {C : Subgroup (MulAut W)}
    (hCab : ∀ a ∈ C, ∀ b ∈ C, a * b = b * a)
    (htrans : ∀ x y : W, x ≠ 1 → y ≠ 1 → ∃ c ∈ C, c x = y)
    {φ : MulAut W} (hφ : ∀ c ∈ C, φ * c = c * φ) : φ ∈ C := by
  by_cases hW : ∃ x₀ : W, x₀ ≠ 1
  · obtain ⟨x₀, hx₀⟩ := hW
    have hφx : φ x₀ ≠ 1 := fun h => hx₀ ((MulEquiv.map_eq_one_iff φ).mp h)
    obtain ⟨c₀, hc₀, hc₀x⟩ := htrans x₀ (φ x₀) hx₀ hφx
    have key : φ = c₀ := by
      refine MulEquiv.ext fun y => ?_
      by_cases hy : y = 1
      · rw [hy, map_one, map_one]
      obtain ⟨d, hd, rfl⟩ := htrans x₀ y hx₀ hy
      have h1 : φ (d x₀) = d (φ x₀) := by
        rw [← MulAut.mul_apply, hφ d hd, MulAut.mul_apply]
      rw [h1, ← hc₀x, ← MulAut.mul_apply, ← MulAut.mul_apply, hCab d hd c₀ hc₀]
    rw [key]
    exact hc₀
  · push Not at hW
    have : φ = 1 := MulEquiv.ext fun y => by rw [hW y, map_one, MulAut.one_apply]
    rw [this]
    exact one_mem C

theorem derivedSeries_two_le_ker {H : Type*} [Group H] {C : Subgroup (MulAut W)}
    (hC : IsCyclic C) (htrans : ∀ x y : W, x ≠ 1 → y ≠ 1 → ∃ c ∈ C, c x = y)
    (ρ : H →* MulAut W) (hρ : ∀ h, ρ h ∈ normalizer (C : Set (MulAut W))) :
    derivedSeries H 2 ≤ ρ.ker := by
  have hCab : ∀ a ∈ C, ∀ b ∈ C, a * b = b * a := fun a ha b hb => by
    have := hC.commGroup.mul_comm ⟨a, ha⟩ ⟨b, hb⟩
    exact congrArg Subtype.val this
  let ρ' : H →* normalizer (C : Set (MulAut W)) := ρ.codRestrict _ hρ
  let σ : H →* MulAut C := C.normalizerMonoidHom.comp ρ'
  have : IsMulCommutative (MulAut C) := by
    refine ⟨⟨fun a b => (IsCyclic.mulAutMulEquiv C).injective ?_⟩⟩
    rw [map_mul, map_mul, mul_comm]
  have hcomm : commutator H ≤ σ.ker := Abelianization.commutator_subset_ker σ
  have hρC : ∀ h ∈ commutator H, ρ h ∈ C := by
    intro h hh
    have h1 := hcomm hh
    rw [MonoidHom.mem_ker] at h1
    refine mem_of_commute_of_transitive hCab htrans fun c hc => ?_
    have h2 := congrArg (fun e : MulAut C => (e ⟨c, hc⟩ : MulAut W)) h1
    simp only [σ, MonoidHom.comp_apply, MulAut.one_apply] at h2
    have h3 : ρ h * c * (ρ h)⁻¹ = c := h2
    calc ρ h * c = ρ h * c * (ρ h)⁻¹ * ρ h := by group
      _ = c * ρ h := by rw [h3]
  intro h hh
  rw [derivedSeries_succ, derivedSeries_one] at hh
  refine (commutator_le.mpr ?_ : ⁅commutator H, commutator H⁆ ≤ ρ.ker) hh
  intro a ha b hb
  rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_def,
    hCab _ (hρC a ha) _ (hρC b hb), mul_inv_cancel_right, mul_inv_cancel]

theorem isSolvable_mulAut_of_card_le_four [Finite W] (hW : Nat.card W ≤ 4) :
    Group.IsSolvable (MulAut W) := by
  have : Group.IsSolvable (Equiv.Perm W) := Equiv.Perm.isSolvable hW
  exact Group.isSolvable_of_isSolvable_injective (f := MulAut.toPerm W) fun a b h =>
    MulEquiv.ext fun x => congrArg (fun e : Equiv.Perm W => e x) h

end Regular

section Eight

variable {W : Type*} [Group W] [Finite W]

@[expose] def fixSubgroup (φ : MulAut W) : Subgroup W where
  carrier := {w | φ w = w}
  mul_mem' := by
    intro a b ha hb
    change φ (a * b) = a * b
    rw [map_mul, show φ a = a from ha, show φ b = b from hb]
  one_mem' := map_one φ
  inv_mem' := by
    intro a ha
    change φ a⁻¹ = a⁻¹
    rw [map_inv, show φ a = a from ha]

theorem orderOf_ne_five_of_card_eight (hW : Nat.card W = 8) (φ : MulAut W) : orderOf φ ≠ 5 := by
  intro h5
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hP : IsPGroup 5 (zpowers φ) := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h5,
    pow_one])
  have hmod := hP.card_modEq_card_fixedPoints W
  have hfix : MulAction.fixedPoints (zpowers φ) W = (fixSubgroup φ : Set W) := by
    ext w
    constructor
    · intro hw
      exact hw ⟨φ, mem_zpowers φ⟩
    · intro hw
      rintro ⟨g, k, rfl⟩
      change (φ ^ k) w = w
      have hw' : φ w = w := hw
      induction k using Int.induction_on with
      | zero => rfl
      | succ k ih =>
        rw [zpow_add_one, MulAut.mul_apply, hw', ih]
      | pred k ih =>
        rw [zpow_sub_one, MulAut.mul_apply]
        have h1 : φ⁻¹ w = w := by
          conv_lhs => rw [← hw']
          exact MulAut.inv_apply_self W φ w
        rw [h1, ih]
  have hcard : Nat.card (MulAction.fixedPoints (zpowers φ) W) = Nat.card (fixSubgroup φ) := by
    rw [hfix]
    rfl
  rw [hcard, hW] at hmod
  have hdvd : Nat.card (fixSubgroup φ) ∣ 2 ^ 3 := by
    rw [show (2 : ℕ) ^ 3 = 8 by norm_num, ← hW]
    exact (fixSubgroup φ).card_subgroup_dvd_card
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  rw [hk'] at hmod
  have hk3 : k = 3 := by
    interval_cases k <;> simp_all [Nat.ModEq]
  have htop : fixSubgroup φ = ⊤ := by
    apply eq_top_of_card_eq
    rw [hk', hk3, hW]
    norm_num
  have hφ1 : φ = 1 := MulEquiv.ext fun w => by
    have : w ∈ fixSubgroup φ := by rw [htop]; exact mem_top w
    exact this
  rw [hφ1, orderOf_one] at h5
  omega

omit [Finite W] in
theorem apply_ne_one (φ : MulAut W) {x : W} (hx : x ≠ 1) : φ x ≠ 1 :=
  fun h => hx ((MulEquiv.map_eq_one_iff φ).mp h)

theorem exists_cyclic_transitive_of_card_eight (hW : Nat.card W = 8)
    {Γ₀ : Subgroup (MulAut W)} (hodd : Odd (Nat.card Γ₀))
    (htrans : ∀ x y : W, x ≠ 1 → y ≠ 1 → ∃ g ∈ Γ₀, g x = y) :
    ∃ P : Subgroup (MulAut W), IsCyclic P ∧ P ≤ Γ₀ ∧
      (∀ x y : W, x ≠ 1 → y ≠ 1 → ∃ c ∈ P, c x = y) ∧
      ∀ φ ∈ normalizer (Γ₀ : Set (MulAut W)), φ ∈ normalizer (P : Set (MulAut W)) := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have : Finite (MulAut W) := Finite.of_injective (MulAut.toPerm W) fun a b h =>
    MulEquiv.ext fun x => congrArg (fun e : Equiv.Perm W => e x) h
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : W, x₀ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : Subsingleton W := ⟨fun a b => (hcon a).trans (hcon b).symm⟩
    have := Nat.card_unique (α := W)
    omega
  set n := Nat.card Γ₀ with hn
  have hdvd8 : n ∣ 40320 := by
    have h1 : n ∣ Nat.card (MulAut W) := Γ₀.card_subgroup_dvd_card
    have h2 : Nat.card (MulAut W) ∣ Nat.card (Equiv.Perm W) := by
      have hinj : Function.Injective (MulAut.toPerm W) := fun a b h =>
        MulEquiv.ext fun x => congrArg (fun e : Equiv.Perm W => e x) h
      have := (MulAut.toPerm W).range.card_subgroup_dvd_card
      rwa [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv] at this
    rw [Nat.card_perm, hW] at h2
    exact h1.trans h2
  have h7 : 7 ∣ n := by
    have horb : MulAction.orbit Γ₀ x₀ = {w : W | w ≠ 1} := by
      ext w
      constructor
      · rintro ⟨g, rfl⟩
        exact apply_ne_one (g : MulAut W) hx₀
      · intro hw
        obtain ⟨g, hg, hgw⟩ := htrans x₀ w hx₀ hw
        exact ⟨⟨g, hg⟩, hgw⟩
    have h1 := MulAction.index_stabilizer Γ₀ x₀
    rw [horb] at h1
    have h2 : ({w : W | w ≠ 1} : Set W).ncard = 7 := by
      have h3 : ({w : W | w ≠ 1} : Set W) = (Set.univ : Set W) \ {1} := by
        ext w
        simp
      rw [h3, Set.ncard_sdiff (Set.singleton_subset_iff.mpr (Set.mem_univ 1)), Set.ncard_univ,
        hW, Set.ncard_singleton]
    rw [h2] at h1
    rw [hn, ← h1]
    exact (MulAction.stabilizer Γ₀ x₀).index_dvd_card
  have h5 : ¬ 5 ∣ n := by
    intro h
    have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := Γ₀) 5 h
    exact orderOf_ne_five_of_card_eight hW (g : MulAut W) (by rw [Subgroup.orderOf_coe]; exact hg)
  have h63 : n ∣ 63 := by
    have hc2 : Nat.Coprime n (2 ^ 7) :=
      Nat.Coprime.pow_right 7 (Nat.coprime_two_right.mpr hodd)
    have h1 : n ∣ 315 := hc2.dvd_of_dvd_mul_left (by norm_num; exact hdvd8)
    have hc5 : Nat.Coprime n 5 :=
      ((Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 5)).mpr h5).symm
    exact hc5.dvd_of_dvd_mul_left (by norm_num; exact h1)
  have hd : n / 7 ∣ 9 := by
    obtain ⟨d, hd⟩ := h7
    rw [hd, Nat.mul_div_cancel_left d (by norm_num)]
    rw [hd] at h63
    exact (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 7)).mp (by simpa using h63)
  obtain ⟨P⟩ : Nonempty (Sylow 7 Γ₀) := inferInstance
  have hP7 : Nat.card (P : Subgroup Γ₀) = 7 := by
    obtain ⟨k, hk⟩ := P.isPGroup'.exists_card_eq
    have hkd : 7 ^ k ∣ 63 := hk ▸ (Subgroup.card_subgroup_dvd_card (P : Subgroup Γ₀)).trans h63
    have hk1 : k ≤ 1 := by
      by_contra hk2
      push Not at hk2
      have : 7 ^ 2 ∣ 63 := (Nat.pow_dvd_pow 7 hk2).trans hkd
      norm_num at this
    interval_cases k
    · exfalso
      have hidx := (P : Subgroup Γ₀).index_mul_card
      rw [hk, pow_zero, mul_one] at hidx
      exact P.not_dvd_index (by rw [hidx, ← hn]; exact h7)
    · rw [hk, pow_one]
  have hidx : (P : Subgroup Γ₀).index = n / 7 := by
    have h1 := (P : Subgroup Γ₀).index_mul_card
    rw [hP7] at h1
    rw [hn, ← h1, Nat.mul_div_cancel _ (by norm_num)]
  have hsub : Subsingleton (Sylow 7 Γ₀) := by
    have h1 := card_sylow_modEq_one 7 Γ₀
    have h2 : Nat.card (Sylow 7 Γ₀) ∣ 9 := (hidx ▸ P.card_dvd_index).trans hd
    have h3 : Nat.card (Sylow 7 Γ₀) = 1 := by
      have hle : Nat.card (Sylow 7 Γ₀) ≤ 9 := Nat.le_of_dvd (by norm_num) h2
      interval_cases h : Nat.card (Sylow 7 Γ₀) <;> simp_all [Nat.ModEq]
    exact (Nat.card_eq_one_iff_unique.mp h3).1
  have hPn : (P : Subgroup Γ₀).Normal := P.normal_of_subsingleton
  set P' : Subgroup (MulAut W) := (P : Subgroup Γ₀).map Γ₀.subtype with hP'
  have hP'card : Nat.card P' = 7 := by
    rw [hP', card_map_of_injective Γ₀.subtype_injective, hP7]
  have hP'le : P' ≤ Γ₀ := map_subtype_le _
  have hP'n : ∀ g ∈ Γ₀, ∀ c ∈ P', g⁻¹ * c * g ∈ P' := by
    rintro g hg _ ⟨c, hc, rfl⟩
    refine ⟨⟨g, hg⟩⁻¹ * c * ⟨g, hg⟩, ?_, rfl⟩
    have := hPn.conj_mem c hc (⟨g, hg⟩⁻¹)
    rwa [inv_inv] at this
  refine ⟨P', isCyclic_of_prime_card hP'card, hP'le, ?_, ?_⟩
  ·
    have hnofix : ∀ x : W, x ≠ 1 → ∃ c ∈ P', c x ≠ x := by
      intro x hx
      by_contra hcon
      push Not at hcon
      have hall : ∀ c ∈ P', ∀ y : W, c y = y := by
        intro c hc y
        by_cases hy : y = 1
        · rw [hy, map_one]
        obtain ⟨g, hg, rfl⟩ := htrans x y hx hy
        have h1 := hcon _ (hP'n g hg c hc)
        rw [MulAut.mul_apply, MulAut.mul_apply] at h1
        calc c (g x) = g (g⁻¹ (c (g x))) := (MulAut.apply_inv_self W g _).symm
          _ = g x := by rw [h1]
      have hbot : P' = ⊥ := eq_bot_iff.mpr fun c hc =>
        (mem_bot).mpr (MulEquiv.ext fun y => hall c hc y)
      rw [hbot, card_bot] at hP'card
      omega
    intro x y hx hy
    have hsubset : MulAction.orbit P' x ⊆ {w : W | w ≠ 1} := by
      rintro _ ⟨c, rfl⟩
      exact apply_ne_one (c : MulAut W) hx
    have hncard : (MulAction.orbit P' x).ncard ∣ 7 := by
      rw [← MulAction.index_stabilizer P' x, ← hP'card]
      exact (MulAction.stabilizer P' x).index_dvd_card
    have h7' : (MulAction.orbit P' x).ncard = 7 := by
      rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).mp hncard with h | h
      · exfalso
        obtain ⟨c, hc, hcx⟩ := hnofix x hx
        have hx' : x ∈ MulAction.orbit P' x := MulAction.mem_orbit_self x
        have hcx' : c x ∈ MulAction.orbit P' x := ⟨⟨c, hc⟩, rfl⟩
        obtain ⟨a, ha⟩ := Set.ncard_eq_one.mp h
        rw [ha] at hx' hcx'
        exact hcx (hcx'.trans hx'.symm)
      · exact h
    have hW7 : ({w : W | w ≠ 1} : Set W).ncard = 7 := by
      have h3 : ({w : W | w ≠ 1} : Set W) = (Set.univ : Set W) \ {1} := by
        ext w
        simp
      rw [h3, Set.ncard_sdiff (Set.singleton_subset_iff.mpr (Set.mem_univ 1)), Set.ncard_univ,
        hW, Set.ncard_singleton]
    have heq : MulAction.orbit P' x = {w : W | w ≠ 1} :=
      Set.eq_of_subset_of_ncard_le hsubset (by rw [h7', hW7]) (Set.toFinite _)
    have hy' : y ∈ MulAction.orbit P' x := by
      rw [heq]
      exact hy
    obtain ⟨⟨c, hc⟩, hcy⟩ := hy'
    exact ⟨c, hc, hcy⟩
  ·
    intro φ hφ
    have hle : P'.map (MulAut.conj φ).toMonoidHom ≤ P' := by
      set Q₀ : Subgroup (MulAut W) := P'.map (MulAut.conj φ).toMonoidHom with hQ₀
      have hQ₀le : Q₀ ≤ Γ₀ := by
        rintro _ ⟨c, hc, rfl⟩
        exact (mem_normalizer_iff.mp hφ c).mp (hP'le hc)
      have hQ₀card : Nat.card Q₀ = 7 := by
        rw [hQ₀, card_map_of_injective (MulAut.conj φ).injective, hP'card]
      have hQ₀p : IsPGroup 7 (Q₀.subgroupOf Γ₀) := by
        refine IsPGroup.of_card (n := 1) ?_
        rw [pow_one, ← hQ₀card]
        exact Nat.card_congr (subgroupOfEquivOfLe hQ₀le).toEquiv
      obtain ⟨R, hR⟩ := hQ₀p.exists_le_sylow
      have hRP : R = P := Subsingleton.elim R P
      intro c hc
      have hc' : (⟨c, hQ₀le hc⟩ : Γ₀) ∈ (P : Subgroup Γ₀) := by
        rw [← hRP]
        exact hR (mem_subgroupOf.mpr hc)
      exact ⟨⟨c, hQ₀le hc⟩, hc', rfl⟩
    have heq : P'.map (MulAut.conj φ).toMonoidHom = P' :=
      eq_of_le_of_card_ge hle (le_of_eq (card_map_of_injective (MulAut.conj φ).injective).symm)
    rw [mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      rw [← heq]
      exact ⟨h, hh, rfl⟩
    · intro hh
      rw [← heq] at hh
      obtain ⟨h', hh', hh'e⟩ := hh
      have : h' = h := (MulAut.conj φ).injective hh'e
      rwa [← this]

end Eight

end CFSG.ComponentClassification.AS81.Qbar
