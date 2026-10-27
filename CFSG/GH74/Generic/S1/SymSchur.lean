module

public import CFSG.GH74.Generic.S1.SymNbhd
public import CFSG.GH74.GLS.LU.Local.L3Cover

public section

namespace CFSG.GH74.Generic.S1

open Subgroup CFSG CFSG.Assembly.LowTwoRank CFSG.RankThree.PerfectCover CFSG.GH74.GLS.LU.Local
open scoped MatrixGroups commutatorElement

theorem ker_comp_le_center_of_perfect {L K J : Type*} [Group L] [Group K] [Group J] (a : L →* K)
    (c : K →* J) (hL : Group.IsPerfect L) (hc : c.ker ≤ center K) (ha : a.ker ≤ center L) :
    (c.comp a).ker ≤ center L := by
  intro z hz
  have hz' : a z ∈ center K := hc (by simpa using hz)
  have hcomm : ∀ l, z * l * z⁻¹ * l⁻¹ ∈ center L := by
    intro l
    apply ha
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv]
    have h1 := mem_center_iff.1 hz' (a l)
    calc a z * a l * (a z)⁻¹ * (a l)⁻¹ = (a z * a l) * (a l * a z)⁻¹ := by group
      _ = 1 := by rw [h1]; simp
  have hconj : ∀ l, z * l * z⁻¹ = (z * l * z⁻¹ * l⁻¹) * l := by
    intro l; group
  have hge : commutator L ≤ centralizer ({z} : Set L) := by
    rw [commutator_eq_closure, Subgroup.closure_le]
    rintro _ ⟨x, y, rfl⟩
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
    have h1 : z * ⁅x, y⁆ * z⁻¹ = ⁅(z * x * z⁻¹ * x⁻¹) * x, (z * y * z⁻¹ * y⁻¹) * y⁆ := by
      rw [← hconj, ← hconj]
      simp only [commutatorElement_def]
      group
    have h2 : ⁅(z * x * z⁻¹ * x⁻¹) * x, (z * y * z⁻¹ * y⁻¹) * y⁆ = ⁅x, y⁆ :=
      CFSG.LieType.Steinberg.commutatorElement_mul_mul_of_mem_center (hcomm x) (hcomm y) x y
    have h3 : z * ⁅x, y⁆ * z⁻¹ = ⁅x, y⁆ := h1.trans h2
    have h4 := congrArg (fun w => w * z) h3
    exact (by simpa [mul_assoc] using h4 : z * ⁅x, y⁆ = ⁅x, y⁆ * z).symm
  rw [mem_center_iff]
  intro g
  have hg : g ∈ commutator L := by rw [hL.commutator_eq_top]; trivial
  exact mem_centralizer_singleton_iff.1 (hge hg)

theorem lieModel_psl_four {J : Type} [Group J] {p n : ℕ} (hp : p.Prime) (hn : 1 ≤ n)
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = p ^ n)
    (e : J ≃* StatedProj (StatedSL 4 F)) : CFSG.Models.LieModel J .PSL 4 p n := by
  have hadm : StatedLieAdmissible .PSL 4 p n :=
    ⟨hp, hn, by norm_num, fun h => by simp at h, fun h => by simp at h⟩
  exact ⟨hadm, Or.inl ⟨hadm, F, inferInstance, inferInstance, hF, ⟨e⟩⟩⟩

theorem lieModel_psu_four {J : Type} [Group J] {p n : ℕ} (hp : p.Prime) (hn : 1 ≤ n)
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = (p ^ n) ^ 2)
    (e : J ≃* StatedProj (StatedSU 4 (p ^ n) F)) : CFSG.Models.LieModel J .PSU 4 p n := by
  have hadm : StatedLieAdmissible .PSU 4 p n :=
    ⟨hp, hn, by norm_num, fun h => by simp at h⟩
  exact ⟨hadm, Or.inl ⟨hadm, F, inferInstance, inferInstance, hF, ⟨e⟩⟩⟩

open CFSG.Blueprint in
theorem card_hopfMultiplier_psl_four
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    {J : Type} [Group J] {p n : ℕ} (hp2 : p ≠ 2) (hm : CFSG.Models.LieModel J .PSL 4 p n) :
    Nat.card (hopfMultiplier J) = Nat.gcd 4 (p ^ n - 1) := by
  obtain ⟨-, ⟨e⟩⟩ := hGA J .PSL 4 p n hm
  have hgen : Multiplier.genericOrders .PSL 4 p n = (Nat.gcd 4 (p ^ n - 1), 1) := rfl
  have hexc : Multiplier.exceptionalOrders .PSL 4 p n = (1, 1) := by
    unfold Multiplier.exceptionalOrders
    split <;> simp_all
  rw [← Nat.card_congr (hopfMultiplierEquivGriess J).toEquiv, Nat.card_congr e.toEquiv,
    Nat.card_prod]
  unfold Multiplier.generic Multiplier.exceptional
  rw [hgen, hexc]
  simp only [Nat.card_prod, Nat.card_zmod, Nat.card_congr (Multiplicative.toAdd : _ ≃ _)]
  simp

open CFSG.Blueprint in
theorem card_hopfMultiplier_psu_four
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    {J : Type} [Group J] {p n : ℕ} (hp2 : p ≠ 2) (h3 : ¬ (p = 3 ∧ n = 1))
    (hm : CFSG.Models.LieModel J .PSU 4 p n) :
    Nat.card (hopfMultiplier J) = Nat.gcd 4 (p ^ n + 1) := by
  obtain ⟨-, ⟨e⟩⟩ := hGA J .PSU 4 p n hm
  have hgen : Multiplier.genericOrders .PSU 4 p n = (Nat.gcd 4 (p ^ n + 1), 1) := rfl
  have hexc : Multiplier.exceptionalOrders .PSU 4 p n = (1, 1) := by
    unfold Multiplier.exceptionalOrders
    split <;> simp_all
  rw [← Nat.card_congr (hopfMultiplierEquivGriess J).toEquiv, Nat.card_congr e.toEquiv,
    Nat.card_prod]
  unfold Multiplier.generic Multiplier.exceptional
  rw [hgen, hexc]
  simp only [Nat.card_prod, Nat.card_zmod, Nat.card_congr (Multiplicative.toAdd : _ ≃ _)]
  simp

theorem exists_cover_psl_gen (n : ℕ) {J : Type} [Group J] {F : Type} [Field F]
    (e : J ≃* StatedProj (StatedSL n F)) :
    ∃ p₀ : SL(n, F) →* J, Function.Surjective p₀ ∧ p₀.ker = center SL(n, F) := by
  let φ := specialLinearGroupEquivStatedSL n F
  refine ⟨(e.symm.toMonoidHom.comp (QuotientGroup.mk' _)).comp φ.toMonoidHom,
    (e.symm.surjective.comp (QuotientGroup.mk'_surjective _)).comp φ.surjective, ?_⟩
  ext x
  have h1 : x ∈ ((e.symm.toMonoidHom.comp (QuotientGroup.mk' _)).comp φ.toMonoidHom).ker ↔
      φ x ∈ (e.symm.toMonoidHom.comp (QuotientGroup.mk'
        ((StatedScalars (Fin n) F).subgroupOf (StatedSL n F)))).ker := Iff.rfl
  rw [h1, CFSG.LieType.Steinberg.ker_comp_mk' _ e.symm, ← map_center_eq_statedScalars]
  exact ⟨fun ⟨y, hy, hxy⟩ => (φ.injective hxy) ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩

theorem card_scalars_statedSU_four {p n : ℕ} (hp : p.Prime) (hn : 1 ≤ n) {F : Type} [Field F]
    (hF : Nat.card F = (p ^ n) ^ 2) :
    Nat.card ((StatedScalars (Fin 4) F).subgroupOf (StatedSU 4 (p ^ n) F)) =
      Nat.gcd 4 (p ^ n + 1) := by
  have h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p n F :=
    ⟨hp, hn, by rw [hF, ← pow_mul, mul_comm]⟩
  have h1 := CFSG.ClassicalGroups.UnitaryFlag.card_unitaryScalars h (n := 4) (by norm_num)
  rw [CFSG.ClassicalGroups.UnitaryFlag.unitaryScalars_eq h (by norm_num)] at h1
  exact h1


theorem schurOdd_lin (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    {K L : Type} [Group K] [Group L] [Finite L] {F : Type} [Field F] [Finite F]
    (hF : Nat.card F % 4 = 3) (e : K ≃* ↥(StatedSL 4 F)) (a : L →* K)
    (ha : Function.Surjective a) (hL : Group.IsPerfect L) (hker : a.ker ≤ center L) :
    a.ker = ⊥ := by
  have : Finite K := Finite.of_equiv _ e.symm.toEquiv
  obtain ⟨p, n, hp, hn, hcard⟩ := CFSG.GH74.Generic.exists_prime_pow_card F
  have hp2 : p ≠ 2 := by
    rintro rfl
    have h2 : 2 ∣ Nat.card F := by rw [hcard]; exact dvd_pow_self 2 (by omega)
    omega
  have hm : CFSG.Models.LieModel (StatedProj (StatedSL 4 F)) .PSL 4 p n :=
    lieModel_psl_four hp hn hcard (MulEquiv.refl _)
  have hcardM := card_hopfMultiplier_psl_four hGA hp2 hm
  have : Finite (hopfMultiplier (StatedProj (StatedSL 4 F))) := Nat.finite_of_card_ne_zero (by
    rw [hcardM]
    exact (Nat.gcd_pos_of_pos_left _ (by norm_num)).ne')
  obtain ⟨p₀, hp₀, hk₀⟩ := exists_cover_psl_gen 4 (MulEquiv.refl (StatedProj (StatedSL 4 F)))
  let c : K →* StatedProj (StatedSL 4 F) :=
    (QuotientGroup.mk' ((StatedScalars (Fin 4) F).subgroupOf (StatedSL 4 F))).comp e.toMonoidHom
  have hc : Function.Surjective c := (QuotientGroup.mk'_surjective _).comp e.surjective
  have hcker : c.ker ≤ center K := by
    intro x hx
    have hx' : e x ∈ (StatedScalars (Fin 4) F).subgroupOf (StatedSL 4 F) := by
      have := (MonoidHom.mem_ker.1 hx)
      exact (QuotientGroup.eq_one_iff _).1 this
    have h1 := CFSG.LieType.Universal.Spin.statedScalars_subgroupOf_le_center (StatedSL 4 F) hx'
    rw [mem_center_iff] at h1 ⊢
    intro y
    apply e.injective
    rw [map_mul, map_mul]
    exact h1 (e y)
  have hqcent := ker_comp_le_center_of_perfect a c hL hcker hker
  have hS₀ : Group.IsPerfect SL(4, F) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect (by norm_num)
  obtain ⟨α, hα⟩ := exists_surjective_of_card_hopfMultiplier_le hS₀ hL p₀ hp₀ hk₀.le (c.comp a)
    (hc.comp ha) hqcent (by
      rw [hcardM, hk₀, CFSG.OrderReductions.LinearOrders.card_specialLinear_center F 4
        (by norm_num), hcard])
  have h1 : Nat.card L ≤ Nat.card K :=
    calc Nat.card L ≤ Nat.card SL(4, F) := Nat.card_le_card_of_surjective α hα
      _ = Nat.card K :=
        Nat.card_congr ((specialLinearGroupEquivStatedSL 4 F).toEquiv.trans e.symm.toEquiv)
  have hbij : Function.Bijective a := ha.bijective_of_nat_card_le h1
  exact (MonoidHom.ker_eq_bot_iff a).2 hbij.1

theorem schurOdd_uni (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    {K L : Type} [Group K] [Group L] [Finite L] {q : ℕ} {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = q ^ 2) (hq : q % 4 = 1) (e : K ≃* ↥(StatedSU 4 q F)) (a : L →* K)
    (ha : Function.Surjective a) (hL : Group.IsPerfect L) (hker : a.ker ≤ center L) :
    a.ker = ⊥ := by
  have : Finite K := Finite.of_equiv _ e.symm.toEquiv
  obtain ⟨p, n, hu, rfl, hp2⟩ := FrameUni.exists_unitaryFieldData hF hq
  have hp : p.Prime := hu.prime
  have hm : CFSG.Models.LieModel (StatedProj (StatedSU 4 (p ^ n) F)) .PSU 4 p n :=
    lieModel_psu_four hp hu.one_le hF (MulEquiv.refl _)
  have h3 : ¬ (p = 3 ∧ n = 1) := by
    rintro ⟨rfl, rfl⟩
    simp at hq
  have hcardM := card_hopfMultiplier_psu_four hGA hp2 h3 hm
  have : Finite (hopfMultiplier (StatedProj (StatedSU 4 (p ^ n) F))) :=
    Nat.finite_of_card_ne_zero (by
      rw [hcardM]
      exact (Nat.gcd_pos_of_pos_left _ (by norm_num)).ne')
  have : Fact p.Prime := ⟨hp⟩
  let p₀ : ↥(StatedSU 4 (p ^ n) F) →* StatedProj (StatedSU 4 (p ^ n) F) := QuotientGroup.mk' _
  have hp₀ : Function.Surjective p₀ := QuotientGroup.mk'_surjective _
  have hk₀ : p₀.ker = (StatedScalars (Fin 4) F).subgroupOf (StatedSU 4 (p ^ n) F) :=
    QuotientGroup.ker_mk' _
  have hk₀c : p₀.ker ≤ center ↥(StatedSU 4 (p ^ n) F) := by
    rw [hk₀]
    exact CFSG.LieType.Universal.Spin.statedScalars_subgroupOf_le_center _
  let c : K →* StatedProj (StatedSU 4 (p ^ n) F) := p₀.comp e.toMonoidHom
  have hc : Function.Surjective c := hp₀.comp e.surjective
  have hcker : c.ker ≤ center K := by
    intro x hx
    have h1 : e x ∈ p₀.ker := hx
    have h2 := hk₀c h1
    rw [mem_center_iff] at h2 ⊢
    intro y
    apply e.injective
    rw [map_mul, map_mul]
    exact h2 (e y)
  have hqcent := ker_comp_le_center_of_perfect a c hL hcker hker
  have hS₀ : Group.IsPerfect ↥(StatedSU 4 (p ^ n) F) :=
    CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hF (by norm_num) (fun h => by
      simp only [Prod.mk.injEq] at h
      omega)
  obtain ⟨α, hα⟩ := exists_surjective_of_card_hopfMultiplier_le hS₀ hL p₀ hp₀ hk₀c (c.comp a)
    (hc.comp ha) hqcent (by rw [hcardM, hk₀, card_scalars_statedSU_four hp hu.one_le hF])
  have h1 : Nat.card L ≤ Nat.card K :=
    calc Nat.card L ≤ Nat.card ↥(StatedSU 4 (p ^ n) F) := Nat.card_le_card_of_surjective α hα
      _ = Nat.card K := (Nat.card_congr e.toEquiv).symm
  have hbij : Function.Bijective a := ha.bijective_of_nat_card_le h1
  exact (MonoidHom.ker_eq_bot_iff a).2 hbij.1

theorem s1SchurOdd_of_griess (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels) :
    S1SchurOddProp := by
  intro K L _ _ _ hK a ha hL hker _
  rcases hK with ⟨F, _, _, hF, ⟨e⟩⟩ | ⟨q, F, _, _, hF, hq, ⟨e⟩⟩
  · exact schurOdd_lin hGA hF e a ha hL hker
  · exact schurOdd_uni hGA hF hq e a ha hL hker

end CFSG.GH74.Generic.S1
