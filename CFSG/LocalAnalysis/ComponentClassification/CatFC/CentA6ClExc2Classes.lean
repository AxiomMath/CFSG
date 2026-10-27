module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClExc2Basic
public import CFSG.LocalAnalysis.SteinbergBMOddResidualToral
public import CFSG.LocalAnalysis.SteinbergBMOddResidualFieldCoset
public import CFSG.LocalAnalysis.SteinbergBMEvenG2FixedNoNormalSL2
public import CFSG.LocalAnalysis.SteinbergCEOddResidualE6GraphCore

public section

namespace CFSG.ComponentClassification.CatFC

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LocalAnalysis.SteinbergCE
  CFSG.LocalAnalysis.SteinbergCE.E6GraphCoset CFSG.ComponentClassification.CatLeafProof
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

set_option linter.unusedSectionVars false


theorem two_dvd_card_of_A6 {S : Type*} [Group S] (eS : S ≃* alternatingGroup (Fin 6)) :
    2 ∣ Nat.card S := by
  rw [Nat.card_congr eS.toEquiv, a6sq_card]
  norm_num

theorem a6_inner_diagonal_false {τ : Tag} (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E8)
    {F : Type} [Field F] [Finite F] (hF : Odd (Nat.card F)) {α : MulAut (adjointGroup τ F)}
    {g : adjointGroup τ F} {a : Fin τ.rank → Fˣ}
    (hαg : ∀ h : adjointGroup τ F, (α h : ModGL τ F) =
      (g : ModGL τ F) * rootDiagUnit τ a * h * (rootDiagUnit τ a)⁻¹ * (g : ModGL τ F)⁻¹)
    (hα : α ^ 2 = 1) (S : Subgroup (α.toMonoidHom.eqLocus (MonoidHom.id (adjointGroup τ F))))
    (hSn : S.Normal) (hSs : IsSimpleGroup S) (hSnab : ∃ x y : S, x * y ≠ y * x)
    (eS : S ≃* alternatingGroup (Fin 6)) : False := by
  have : Fintype F := Fintype.ofFinite F
  have hF2 : ringChar F ≠ 2 := fun h => by
    have := FiniteField.even_card_iff_char_two.1 h
    rw [← Nat.card_eq_fintype_card] at this
    exact (Nat.not_even_iff_odd.2 hF) (Nat.even_iff.2 this)
  obtain ⟨φ, hφ⟩ :=
    CFSG.LocalAnalysis.SteinbergBM.odd_residual_inner_diagonal_fixed_normal_simple_contains_SL2
      hτ hF hαg hα S hSn hSs hSnab
  exact false_of_injective_SL2_A6 hF2 φ hφ eS

theorem a6_quadratic_field_coset_false {τ : Tag} {F : Type} [Field F] [Finite F] {p e : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (he : 1 ≤ e) (hF : Nat.card F = (p ^ e) ^ 2) (δ : F ≃+* F)
    (hδ : ∀ c, δ c = c ^ (p ^ e)) {α : MulAut (adjointGroup τ F)} {g : adjointGroup τ F}
    {a : Fin τ.rank → Fˣ}
    (hαg : ∀ h : adjointGroup τ F, (α h : ModGL τ F) = (g : ModGL τ F) * rootDiagUnit τ a *
      Units.map (entrywiseHom δ.toRingHom) (h : ModGL τ F) * (rootDiagUnit τ a)⁻¹ *
        (g : ModGL τ F)⁻¹)
    (hα : α ^ 2 = 1)
    (S : Subgroup (α.toMonoidHom.eqLocus (MonoidHom.id (adjointGroup τ F)))) (hSn : S.Normal)
    (hSs : IsSimpleGroup S) (hSnab : ∃ x y : S, x * y ≠ y * x)
    (eS : S ≃* alternatingGroup (Fin 6)) : False := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : CharP F p := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    (k := 2 * e) hp (by omega) (by rw [hF, ← pow_mul, mul_comm])
  have hF2 : ringChar F ≠ 2 := by rw [ringChar.eq F p]; exact hp2
  obtain ⟨hQ1, -⟩ := exceptional_Lang_quadratic_field_coset_conjugacy hp he F hF δ.toRingHom hδ
  obtain ⟨β, hβ, hβα⟩ := hQ1 τ
  obtain ⟨-, hconj⟩ := hβα g a
  obtain ⟨ψ, -, -, ⟨e₁, -⟩, -⟩ := hconj α hαg (by rw [← sq]; exact hα)
  have hβfix : (β.toMonoidHom.eqLocus (MonoidHom.id (adjointGroup τ F))).map
      (adjointGroup τ F).subtype = entrywiseFixedGroup τ δ := by
    ext y
    simp only [Subgroup.mem_map, entrywiseFixedGroup, Subgroup.mem_inf]
    constructor
    · rintro ⟨u, hu, rfl⟩
      refine ⟨u.2, ?_⟩
      change Units.map (entrywiseHom δ.toRingHom) (u : ModGL τ F) = u
      rw [← hβ u]
      exact congrArg Subtype.val hu
    · rintro ⟨hyG, hyδ⟩
      refine ⟨⟨y, hyG⟩, Subtype.ext ?_, rfl⟩
      change (β ⟨y, hyG⟩ : ModGL τ F) = y
      rw [hβ]
      exact hyδ
  let e₂ : ↥(β.toMonoidHom.eqLocus (MonoidHom.id (adjointGroup τ F))) ≃*
      ↥(entrywiseFixedGroup τ δ) :=
    (Subgroup.equivMapOfInjective _ _ Subtype.val_injective).trans (MulEquiv.subgroupCongr hβfix)
  obtain ⟨S', hS'n, hS's, hS'nab, ⟨eS'⟩⟩ :=
    CFSG.LocalAnalysis.SteinbergBM.exists_normal_simple_of_mulEquiv (e₁.trans e₂) S hSn hSs
      hSnab
  obtain ⟨φ, hφ⟩ := CFSG.LocalAnalysis.SteinbergBM.exists_injective_SL2_of_normal_simple_entrywiseFixedGroup
    hF2 δ S' hS'n hS's hS'nab
  exact false_of_injective_SL2_A6 (ringChar_fixSubfield_ne_two hF2 δ)
    (eS'.symm.toMonoidHom.comp φ) (eS'.symm.injective.comp hφ) eS

theorem a6_E6_graph_field_coset_false {F : Type} [Field F] [Finite F]
    {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (he : 1 ≤ e) (hF : Nat.card F = (p ^ e) ^ 2)
    (δ : F ≃+* F) (hδ : ∀ c, δ c = c ^ (p ^ e)) {α : MulAut (adjointGroup TwistTag.E6.tag F)}
    {g : adjointGroup TwistTag.E6.tag F} {a : Fin TwistTag.E6.tag.rank → Fˣ}
    (hαg : ∀ h : adjointGroup TwistTag.E6.tag F, (α h : ModGL TwistTag.E6.tag F) =
      (g : ModGL TwistTag.E6.tag F) * rootDiagUnit TwistTag.E6.tag a * diagramMap TwistTag.E6 F *
        Units.map (entrywiseHom δ.toRingHom) (h : ModGL TwistTag.E6.tag F) *
          (diagramMap TwistTag.E6 F)⁻¹ * (rootDiagUnit TwistTag.E6.tag a)⁻¹ *
            (g : ModGL TwistTag.E6.tag F)⁻¹)
    (hα : α ^ 2 = 1)
    (S : Subgroup (α.toMonoidHom.eqLocus (MonoidHom.id (adjointGroup TwistTag.E6.tag F))))
    (hSn : S.Normal) (hSs : IsSimpleGroup S) (hSnab : ∃ x y : S, x * y ≠ y * x)
    (eS : S ≃* alternatingGroup (Fin 6)) : False := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : CharP F p := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    (k := 2 * e) hp (by omega) (by rw [hF, ← pow_mul, mul_comm])
  have hF2 : ringChar F ≠ 2 := by rw [ringChar.eq F p]; exact hp2
  obtain ⟨-, β, hβ, hβα⟩ :=
    exceptional_Lang_quadratic_field_coset_conjugacy hp he F hF δ.toRingHom hδ
  obtain ⟨-, hconj⟩ := hβα g a
  obtain ⟨ψ, -, -, ⟨e₁, -⟩, -⟩ := hconj α hαg (by rw [← sq]; exact hα)
  have hβfix : (β.toMonoidHom.eqLocus (MonoidHom.id (adjointGroup TwistTag.E6.tag F))).map
      (adjointGroup TwistTag.E6.tag F).subtype = twistedFixedGroup TwistTag.E6 F δ.toRingHom := by
    ext y
    simp only [Subgroup.mem_map, twistedFixedGroup, Subgroup.mem_inf]
    constructor
    · rintro ⟨u, hu, rfl⟩
      refine ⟨u.2, ?_⟩
      change twistHom TwistTag.E6 F δ.toRingHom (u : ModGL TwistTag.E6.tag F) = u
      rw [twistHom_apply, ← hβ u]
      exact congrArg Subtype.val hu
    · rintro ⟨hyG, hyσ⟩
      refine ⟨⟨y, hyG⟩, Subtype.ext ?_, rfl⟩
      change (β ⟨y, hyG⟩ : ModGL TwistTag.E6.tag F) = y
      rw [hβ]
      change twistHom TwistTag.E6 F δ.toRingHom y = y at hyσ
      rw [twistHom_apply] at hyσ
      exact hyσ
  let e₂ : ↥(β.toMonoidHom.eqLocus (MonoidHom.id (adjointGroup TwistTag.E6.tag F))) ≃*
      ↥(twistedFixedGroup TwistTag.E6 F δ.toRingHom) :=
    (Subgroup.equivMapOfInjective _ _ Subtype.val_injective).trans (MulEquiv.subgroupCongr hβfix)
  obtain ⟨S', hS'n, hS's, hS'nab, ⟨eS'⟩⟩ :=
    CFSG.LocalAnalysis.SteinbergBM.exists_normal_simple_of_mulEquiv (e₁.trans e₂) S hSn hSs
      hSnab
  obtain ⟨φ, hφ⟩ :=
    CFSG.LocalAnalysis.SteinbergBM.exists_injective_SL2_of_normal_simple_twistedFixedGroup
      hF2 δ S' hS'n hS's hS'nab
  exact false_of_injective_SL2_A6 (ringChar_fixSubfield_ne_two hF2 δ)
    (eS'.symm.toMonoidHom.comp φ) (eS'.symm.injective.comp hφ) eS

theorem a6_E6_graph_coset_core_false
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) {e : ℕ}
    (he : 1 ≤ e) (k : Type) [Field k] [IsAlgClosed k] [CharP k p]
    (halg : letI := ZMod.algebra k p; Algebra.IsAlgebraic (ZMod p) k) (ε : ℕ)
    (hε : ε = 0 ∨ ε = 1) {x : ModGL TwistTag.E6.tag k} (hx : x ∈ graphRational k p e ε)
    (hx2 : (x * diagramMap TwistTag.E6 k) ^ 2 = 1) (S : Subgroup (graphCosetFixed k p e ε x))
    (hSn : S.Normal) (hSs : IsSimpleGroup S) (hSnab : ∃ a b : S, a * b ≠ b * a)
    (eS : S ≃* alternatingGroup (Fin 6)) : False := by
  classical
  obtain ⟨hfin, -⟩ := E6_rational_graph_coset_fixed_components p hp he k halg ε hε
  have : Finite (graphRational k p e ε) := hfin
  have hXR : graphCosetFixed k p e ε x ≤ graphRational k p e ε :=
    inf_le_left.trans (Subgroup.commutator_le_self _)
  have : Finite (graphCosetFixed k p e ε x) :=
    Finite.of_injective _ (Subgroup.inclusion_injective hXR)
  have hS2 := CFSG.LocalAnalysis.SteinbergCA.isPComponent_two_of_normal_simple S hSn hSs hSnab
    (two_dvd_card_of_A6 eS)
  set L := S.map (graphCosetFixed k p e ε x).subtype with hLdef
  have hLX : L ≤ graphCosetFixed k p e ε x := Subgroup.map_subtype_le S
  have hLsub : L.subgroupOf (graphCosetFixed k p e ε x) = S :=
    Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) S
  obtain ⟨AK, c, hAK, hc⟩ := exists_conj_eq_rationalRootGroup p hp he k halg ε hε hx hx2
    Nat.prime_two hLX (hLsub ▸ hS2)
  have : CharP (fixSubfield (iterateFrobeniusEquiv k p e)) p :=
    (fixSubfield (iterateFrobeniusEquiv k p e)).subtype.charP Subtype.val_injective p
  have hinj := e4RootSL2_injective k p hp e
  have hk : ringChar k ≠ 2 := by
    rw [ringChar.eq k p]
    exact hp
  let e₁ : S ≃* L := S.equivMapOfInjective _ (Subgroup.subtype_injective _)
  let e₂ : L ≃* L.map (MulAut.conj c).toMonoidHom :=
    L.equivMapOfInjective _ (MulAut.conj c).injective
  refine false_of_hom_A6 ((e₁.trans e₂).symm.trans eS) hp
    (e4RootSL2 k p e) (fun s => hc ▸ e4RootSL2_mem_rationalRootGroup k p e hAK s) ?_ ?_
  · rw [← map_one (e4RootSL2 k p e)]
    exact fun h => neg_one_ne_one_SL2 (ringChar_fixSubfield_ne_two hk _) (hinj h)
  · rw [← map_one (e4RootSL2 k p e)]
    exact fun h => CFSG.LocalAnalysis.SteinbergCA.uSL_one_ne_one_and_ne_neg_one.1 (hinj h)

end CFSG.ComponentClassification.CatFC
