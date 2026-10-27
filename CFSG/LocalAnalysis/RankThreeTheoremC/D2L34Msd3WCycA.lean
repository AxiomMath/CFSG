module

import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.F5Baum
import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3WNormal
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open

variable {G : Type} [Group G]

theorem eq_one_of_cube_sub_one_zmod_three : ∀ x : ZMod 3, x * x * x - 1 = 0 → x = 1 := by decide

theorem zmod_three_pow_pow (x : ZMod 3) (r : ℕ) : x ^ 3 ^ r = x := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact ZMod.pow_card_pow x

theorem pow_three_eq_one_of_mul_cyclic {D₀ : Subgroup G} (hD₀p : IsPGroup 3 D₀)
    (hD₀c : IsCyclic D₀) {u d : G} (hu : u ^ 3 = 1) (hun : ∀ e ∈ D₀, u * e * u⁻¹ ∈ D₀)
    (hd : d ∈ D₀) (hx : (d * u) ^ 3 = 1) : d ^ 3 = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let σ : D₀ →* D₀ :=
    { toFun := fun e => ⟨u * e * u⁻¹, hun e e.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
  obtain ⟨k, hk⟩ := MonoidHom.map_cyclic σ
  have hσ : ∀ e ∈ D₀, u * e * u⁻¹ = e ^ k := fun e he => by
    have h := congrArg Subtype.val (hk ⟨e, he⟩)
    simpa [σ] using h
  have hu' : u * u * u = 1 := by rw [← pow_three']; exact hu
  have hσ2 : ∀ e ∈ D₀, u * (u * e * u⁻¹) * u⁻¹ = e ^ (k * k) := by
    intro e he
    calc u * (u * e * u⁻¹) * u⁻¹ = u * e ^ k * u⁻¹ := by rw [hσ e he]
      _ = (e ^ k) ^ k := hσ (e ^ k) (D₀.zpow_mem he k)
      _ = e ^ (k * k) := by rw [← zpow_mul]
  have hσ3 : ∀ e ∈ D₀, e ^ (k * k * k) = e := by
    intro e he
    calc e ^ (k * k * k) = (e ^ (k * k)) ^ k := by rw [← zpow_mul]
      _ = u * e ^ (k * k) * u⁻¹ := (hσ (e ^ (k * k)) (D₀.zpow_mem he _)).symm
      _ = u * (u * (u * e * u⁻¹) * u⁻¹) * u⁻¹ := by rw [hσ2 e he]
      _ = (u * u * u) * e * (u * u * u)⁻¹ := by group
      _ = e := by rw [hu']; group
  have hcube : (d * u) ^ 3 = d ^ (1 + k + k * k) := by
    have e1 : (d * u) ^ 3 =
        d * (u * d * u⁻¹) * (u * (u * d * u⁻¹) * u⁻¹) * (u * u * u) := by
      rw [pow_succ, pow_succ, pow_one]
      group
    rw [e1, hσ2 d hd, hσ d hd, hu', mul_one, zpow_add, zpow_add, zpow_one]
  have h1 : d ^ (1 + k + k * k) = 1 := hcube ▸ hx
  have h2 : d ^ (k * k * k - 1) = 1 := by
    rw [zpow_sub, zpow_one, hσ3 d hd]
    exact mul_inv_cancel d
  obtain ⟨b, hb⟩ := IsPGroup.iff_orderOf.mp hD₀p ⟨d, hd⟩
  have hb' : orderOf d = 3 ^ b := (Subgroup.orderOf_coe (⟨d, hd⟩ : D₀)).trans hb
  rcases Nat.eq_zero_or_pos b with hb0 | hbpos
  · rw [hb0, pow_zero] at hb'
    have := orderOf_eq_one_iff.mp hb'
    rw [this]
    simp
  · have hdv1 : ((3 ^ b : ℕ) : ℤ) ∣ 1 + k + k * k := by
      rw [← hb']
      exact orderOf_dvd_iff_zpow_eq_one.mpr h1
    have hdv2 : ((3 ^ b : ℕ) : ℤ) ∣ k * k * k - 1 := by
      rw [← hb']
      exact orderOf_dvd_iff_zpow_eq_one.mpr h2
    have h3b : (3 : ℤ) ∣ ((3 ^ b : ℕ) : ℤ) := by
      exact_mod_cast dvd_pow_self 3 hbpos.ne'
    have h3k : (3 : ℤ) ∣ k * k * k - 1 := h3b.trans hdv2
    have hz : ((k * k * k - 1 : ℤ) : ZMod 3) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr h3k
    push_cast at hz
    have hk1 : (k : ZMod 3) = 1 := eq_one_of_cube_sub_one_zmod_three _ hz
    have hkm : (3 : ℤ) ∣ k - 1 := by
      have h : ((k - 1 : ℤ) : ZMod 3) = 0 := by
        push_cast
        rw [hk1]
        simp
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd (k - 1) 3).mp h
    obtain ⟨m, hm⟩ := hkm
    have hk' : k = 1 + 3 * m := by omega
    have hs : 1 + k + k * k = 3 * (1 + 3 * m + 3 * m * m) := by rw [hk']; ring
    have hcop : IsCoprime ((3 : ℤ) ^ b) (1 + 3 * m + 3 * m * m) :=
      IsCoprime.pow_left ⟨-(m + m * m), 1, by ring⟩
    rw [hs] at hdv1
    have hdv3 : (3 : ℤ) ^ b ∣ 3 := by
      refine hcop.dvd_of_dvd_mul_right ?_
      push_cast at hdv1
      exact hdv1
    have hdv4 : orderOf d ∣ 3 := by
      rw [hb']
      exact_mod_cast hdv3
    exact orderOf_dvd_iff_pow_eq_one.mp hdv4

theorem conj_eq_of_pow_three_of_cyclic {W D₀ : Subgroup G} (hWp : IsPGroup 3 W)
    (hD₀c : IsCyclic D₀) (hWN : ∀ w ∈ W, ∀ e ∈ D₀, w * e * w⁻¹ ∈ D₀) {d w : G} (hd : d ∈ D₀)
    (hd3 : d ^ 3 = 1) (hw : w ∈ W) : w * d * w⁻¹ = d := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_cases hd1 : d = 1
  · subst hd1
    simp
  have hord : orderOf d = 3 := orderOf_eq_prime hd3 hd1
  let σ : D₀ →* D₀ :=
    { toFun := fun e => ⟨w * e * w⁻¹, hWN w hw e e.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
  obtain ⟨m, hm⟩ := MonoidHom.map_cyclic σ
  have hσ : ∀ e ∈ D₀, w * e * w⁻¹ = e ^ m := fun e he => by
    have h := congrArg Subtype.val (hm ⟨e, he⟩)
    simpa [σ] using h
  have hpow : ∀ n : ℕ, ∀ e ∈ D₀, w ^ n * e * (w ^ n)⁻¹ = e ^ (m ^ n) := by
    intro n
    induction n with
    | zero =>
      intro e he
      simp
    | succ n ih =>
      intro e he
      calc w ^ (n + 1) * e * (w ^ (n + 1))⁻¹ = w * (w ^ n * e * (w ^ n)⁻¹) * w⁻¹ := by group
        _ = w * e ^ (m ^ n) * w⁻¹ := by rw [ih e he]
        _ = (w * e * w⁻¹) ^ (m ^ n) := by rw [conj_zpow]
        _ = (e ^ m) ^ (m ^ n) := by rw [hσ e he]
        _ = e ^ (m ^ (n + 1)) := by rw [← zpow_mul, pow_succ']
  obtain ⟨r, hr⟩ := hWp ⟨w, hw⟩
  have hwr : w ^ 3 ^ r = 1 := by simpa using congrArg Subtype.val hr
  have hdd : d ^ (m ^ 3 ^ r) = d := by
    have := hpow (3 ^ r) d hd
    rw [hwr] at this
    simpa using this.symm
  have h1 : d ^ (m ^ 3 ^ r - 1) = 1 := by
    rw [zpow_sub, zpow_one, hdd]
    exact mul_inv_cancel d
  have h2 : (3 : ℤ) ∣ m ^ 3 ^ r - 1 := by
    have := orderOf_dvd_iff_zpow_eq_one.mpr h1
    rw [hord] at this
    exact_mod_cast this
  have h3 : (3 : ℤ) ∣ m - 1 := by
    have hz : ((m ^ 3 ^ r - 1 : ℤ) : ZMod 3) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr h2
    push_cast at hz
    rw [zmod_three_pow_pow] at hz
    have h : ((m - 1 : ℤ) : ZMod 3) = 0 := by
      push_cast
      exact hz
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd (m - 1) 3).mp h
  have h4 : d ^ (m - 1) = 1 := by
    refine orderOf_dvd_iff_zpow_eq_one.mp ?_
    rw [hord]
    exact_mod_cast h3
  rw [hσ d hd]
  calc d ^ m = d ^ (m - 1) * d := by rw [← zpow_add_one]; congr 1; ring
    _ = d := by rw [h4, one_mul]


section Fin

variable [Finite G]

theorem mem_of_pow_three_of_cyclic_normal {W D₀ F : Subgroup G} (hWp : IsPGroup 3 W)
    (hmax : ∀ A : Subgroup G, A ≤ W → IsElemAbelian 3 A → Nat.card A ≤ 27)
    (hFW : F ≤ W) (hFel : IsElemAbelian 3 F) (hF27 : Nat.card F = 27) (hD₀W : D₀ ≤ W)
    (hWN : W ≤ Subgroup.normalizer (D₀ : Set G)) (hD₀c : IsCyclic D₀) {a : G} (ha : a ∈ D₀)
    (ha3 : a ^ 3 = 1) : a ∈ F := by
  have hWN' : ∀ w ∈ W, ∀ e ∈ D₀, w * e * w⁻¹ ∈ D₀ := fun w hw e he =>
    (Subgroup.mem_normalizer_iff.mp (hWN hw) e).mp he
  set A : Subgroup G := Subgroup.closure ((F : Set G) ∪ {a}) with hA
  have hAW : A ≤ W := by
    refine (Subgroup.closure_le W).2 ?_
    rintro x (hx | hx)
    · exact hFW hx
    · rw [Set.mem_singleton_iff.mp hx]
      exact hD₀W ha
  have hAel : IsElemAbelian 3 A := by
    refine CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.isElemAbelian_closure (p := 3) ?_ ?_
    · rintro x (hx | hx) y (hy | hy)
      · exact congrArg Subtype.val (hFel.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
      · rw [Set.mem_singleton_iff.mp hy]
        have h := conj_eq_of_pow_three_of_cyclic hWp hD₀c hWN' ha ha3 (hFW hx)
        calc x * a = x * a * x⁻¹ * x := by group
          _ = a * x := by rw [h]
      · rw [Set.mem_singleton_iff.mp hx]
        have h := conj_eq_of_pow_three_of_cyclic hWp hD₀c hWN' ha ha3 (hFW hy)
        calc a * y = (y * a * y⁻¹) * y := by rw [h]
          _ = y * a := by group
      · rw [Set.mem_singleton_iff.mp hx, Set.mem_singleton_iff.mp hy]
    · rintro x (hx | hx)
      · exact hFel.2 x hx
      · rw [Set.mem_singleton_iff.mp hx]
        exact ha3
  have hAle : Nat.card A ≤ 27 := hmax A hAW hAel
  have hFA : F ≤ A := fun x hx => Subgroup.subset_closure (Or.inl hx)
  have hFeq : F = A := Subgroup.eq_of_le_of_card_ge hFA (by rw [hF27]; exact hAle)
  rw [hFeq]
  exact Subgroup.subset_closure (Or.inr (Set.mem_singleton a))

theorem not_isCyclic_inf_sup_of_mul {W D₀ W₂ F : Subgroup G} (hFW : F ≤ W)
    (hFel : IsElemAbelian 3 F) (hF27 : Nat.card F = 27)
    (hWN : W ≤ Subgroup.normalizer (D₀ : Set G)) (hD₀c : IsCyclic D₀) (hW₂W : W₂ ≤ W)
    (hfac : ∀ w ∈ W, ∃ a ∈ D₀, ∃ b ∈ W₂, w = a * b) :
    ¬ IsCyclic ↥(W₂ ⊓ (D₀ ⊔ F)) := by
  intro hcyc
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set X : Subgroup G := W₂ ⊓ (D₀ ⊔ F) with hX
  have hFN : F ≤ Subgroup.normalizer (D₀ : Set G) := hFW.trans hWN
  have hXN : X ≤ Subgroup.normalizer (D₀ : Set G) := inf_le_left.trans (hW₂W.trans hWN)
  have hDF3 : Nat.card (D₀ ⊓ F : Subgroup G) ≤ 3 := by
    have := hD₀c
    have hc : IsCyclic ↥(D₀ ⊓ F) := Subgroup.isCyclic_of_le inf_le_left
    exact CFSG.AGLEmbeddingD2.Tits.MsidePrelim.card_le_of_isElemAbelian_of_isCyclic
      (CFSG.AGLEmbeddingD2.Tits.MsidePrelim.isElemAbelian_of_le hFel inf_le_right) hc
  have hFX : F ≤ D₀ ⊔ X := by
    intro f hf
    obtain ⟨a, ha, b, hb, hab⟩ := hfac f (hFW hf)
    have hbX : b ∈ X := by
      refine ⟨hb, ?_⟩
      have : b = a⁻¹ * f := by rw [hab]; group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (D₀.inv_mem ha)) (Subgroup.mem_sup_right hf)
    rw [hab]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hbX)
  have hS : D₀ ⊔ F = D₀ ⊔ X :=
    le_antisymm (sup_le le_sup_left hFX) (sup_le le_sup_left inf_le_right)
  have h1 := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hFN
  have h2 := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hXN
  rw [hF27] at h1
  rw [← hS] at h2
  have hD0pos : 0 < Nat.card D₀ := Nat.card_pos
  have hkey : Nat.card X * Nat.card (D₀ ⊓ F : Subgroup G) =
      27 * Nat.card (D₀ ⊓ X : Subgroup G) := by
    have : Nat.card D₀ * (Nat.card X * Nat.card (D₀ ⊓ F : Subgroup G)) =
        Nat.card D₀ * (27 * Nat.card (D₀ ⊓ X : Subgroup G)) := by
      calc Nat.card D₀ * (Nat.card X * Nat.card (D₀ ⊓ F : Subgroup G))
          = (Nat.card D₀ * Nat.card X) * Nat.card (D₀ ⊓ F : Subgroup G) := by ring
        _ = (Nat.card (D₀ ⊔ F : Subgroup G) * Nat.card (D₀ ⊓ X : Subgroup G)) *
              Nat.card (D₀ ⊓ F : Subgroup G) := by rw [h2]
        _ = (Nat.card (D₀ ⊔ F : Subgroup G) * Nat.card (D₀ ⊓ F : Subgroup G)) *
              Nat.card (D₀ ⊓ X : Subgroup G) := by ring
        _ = (Nat.card D₀ * 27) * Nat.card (D₀ ⊓ X : Subgroup G) := by rw [h1]
        _ = Nat.card D₀ * (27 * Nat.card (D₀ ⊓ X : Subgroup G)) := by ring
    exact Nat.eq_of_mul_eq_mul_left hD0pos this
  have hmul := Nat.mul_le_mul_left (Nat.card X) hDF3
  have hDXpos : 0 < Nat.card (D₀ ⊓ X : Subgroup G) := Nat.card_pos
  have hXge : 9 * Nat.card (D₀ ⊓ X : Subgroup G) ≤ Nat.card X := by omega
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have hgS : (g : G) ∈ D₀ ⊔ F := g.2.2
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left D₀ F hFN, Set.mem_mul] at hgS
  obtain ⟨a, ha, f, hf, hgaf⟩ := hgS
  have hf3 : f * f * f = 1 := by rw [← pow_three']; exact hFel.2 f hf
  have hfN : ∀ e ∈ D₀, f * e * f⁻¹ ∈ D₀ := fun e he =>
    (Subgroup.mem_normalizer_iff.mp (hFN hf) e).mp he
  have hg3 : (g : G) ^ 3 ∈ D₀ := by
    have e1 : (g : G) ^ 3 = a * (f * a * f⁻¹) * (f * (f * a * f⁻¹) * f⁻¹) * (f * f * f) := by
      rw [← hgaf, pow_succ, pow_succ, pow_one]
      group
    rw [e1, hf3, mul_one]
    exact D₀.mul_mem (D₀.mul_mem ha (hfN a ha)) (hfN _ (hfN a ha))
  have hg3X : (g : G) ^ 3 ∈ D₀ ⊓ X := ⟨hg3, X.pow_mem g.2 3⟩
  have hordX : orderOf g = Nat.card X := orderOf_eq_card_of_forall_mem_zpowers hg
  have hordg : orderOf (g : G) = Nat.card X := by
    rw [Subgroup.orderOf_coe]
    exact hordX
  have hcardz : Nat.card (Subgroup.zpowers ((g : G) ^ 3)) ≤ Nat.card (D₀ ⊓ X : Subgroup G) :=
    Subgroup.card_le_of_le (Subgroup.zpowers_le.mpr hg3X)
  have hord3 : orderOf ((g : G) ^ 3) = orderOf (g : G) / Nat.gcd (orderOf (g : G)) 3 :=
    orderOf_pow' (g : G) (by norm_num)
  rw [Nat.card_zpowers, hord3, hordg] at hcardz
  have hdvd : Nat.gcd (Nat.card X) 3 ∣ Nat.card X := Nat.gcd_dvd_left _ _
  have hgcd : Nat.gcd (Nat.card X) 3 ≤ 3 :=
    Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_right _ _)
  have hdiv : Nat.card X / Nat.gcd (Nat.card X) 3 * Nat.gcd (Nat.card X) 3 = Nat.card X :=
    Nat.div_mul_cancel hdvd
  have hle3 : Nat.card X ≤ 3 * (Nat.card X / Nat.gcd (Nat.card X) 3) := by
    calc Nat.card X = Nat.card X / Nat.gcd (Nat.card X) 3 * Nat.gcd (Nat.card X) 3 := hdiv.symm
      _ ≤ Nat.card X / Nat.gcd (Nat.card X) 3 * 3 := Nat.mul_le_mul_left _ hgcd
      _ = 3 * (Nat.card X / Nat.gcd (Nat.card X) 3) := by ring
  omega

theorem exists_E9_le_inf_of_cyclic_normal_mul {W D₀ W₂ F : Subgroup G} (hWp : IsPGroup 3 W)
    (hmax : ∀ A : Subgroup G, A ≤ W → IsElemAbelian 3 A → Nat.card A ≤ 27) (hFW : F ≤ W)
    (hFel : IsElemAbelian 3 F) (hF27 : Nat.card F = 27) (hD₀W : D₀ ≤ W)
    (hWN : W ≤ Subgroup.normalizer (D₀ : Set G)) (hD₀c : IsCyclic D₀) (hW₂W : W₂ ≤ W)
    (hfac : ∀ w ∈ W, ∃ a ∈ D₀, ∃ b ∈ W₂, w = a * b) :
    ∃ E : Subgroup G, E ≤ W₂ ∧ E ≤ F ∧ IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  have hnc := not_isCyclic_inf_sup_of_mul hFW hFel hF27 hWN hD₀c hW₂W hfac
  have hXp : IsPGroup 3 ↥(W₂ ⊓ (D₀ ⊔ F)) := hWp.to_le (inf_le_left.trans hW₂W)
  obtain ⟨E, hEX, hEel, hE9⟩ := exists_E9_le_of_not_isCyclic hXp hnc
  refine ⟨E, hEX.trans inf_le_left, ?_, hEel, hE9⟩
  intro e he
  have heS : e ∈ D₀ ⊔ F := (hEX he).2
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left D₀ F (hFW.trans hWN),
    Set.mem_mul] at heS
  obtain ⟨a, ha, f, hf, rfl⟩ := heS
  have hx : (a * f) ^ 3 = 1 := hEel.2 _ he
  have ha3 : a ^ 3 = 1 :=
    pow_three_eq_one_of_mul_cyclic (hWp.to_le hD₀W) hD₀c (hFel.2 f hf)
      (fun e he => (Subgroup.mem_normalizer_iff.mp (hWN (hFW hf)) e).mp he) ha hx
  exact F.mul_mem (mem_of_pow_three_of_cyclic_normal hWp hmax hFW hFel hF27 hD₀W hWN hD₀c ha ha3)
    hf

theorem pow_three_mem_of_cyclic_normal_mul {W D₀ W₂ F : Subgroup G} (hWp : IsPGroup 3 W)
    (hmax : ∀ A : Subgroup G, A ≤ W → IsElemAbelian 3 A → Nat.card A ≤ 27) (hFW : F ≤ W)
    (hFel : IsElemAbelian 3 F) (hF27 : Nat.card F = 27) (hD₀W : D₀ ≤ W)
    (hWN : W ≤ Subgroup.normalizer (D₀ : Set G)) (hD₀c : IsCyclic D₀) (hW₂W : W₂ ≤ W)
    (hfac : ∀ w ∈ W, ∃ a ∈ D₀, ∃ b ∈ W₂, w = a * b) (hW₂el : IsElemAbelian 3 W₂)
    (hW₂F : W₂ ≤ F) {w : G} (hw : w ∈ W) (hw3 : w ^ 3 = 1) : w ∈ F := by
  obtain ⟨a, ha, b, hb, rfl⟩ := hfac w hw
  have hb3 : b ^ 3 = 1 := hW₂el.2 b hb
  have ha3 : a ^ 3 = 1 :=
    pow_three_eq_one_of_mul_cyclic (hWp.to_le hD₀W) hD₀c hb3
      (fun e he => (Subgroup.mem_normalizer_iff.mp (hWN (hW₂W hb)) e).mp he) ha hw3
  exact F.mul_mem (mem_of_pow_three_of_cyclic_normal hWp hmax hFW hFel hF27 hD₀W hWN hD₀c ha ha3)
    (hW₂F hb)

end Fin

end CFSG.LocalAnalysis.RankThreeTheoremC
