module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTD4
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HOutDiagMain

public section

namespace CFSG.LocalAnalysis.GLTheoremA.HSubT

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10

theorem conj_of_quotient_eq {Q : Type} [Group Q] (hQ : commutator Q = ⊤) {R : Type} [Group R]
    (θ : Q ⧸ Subgroup.center Q ≃* R) (r : R) (α : Q →* Q)
    (hα : ∀ x : Q, θ (QuotientGroup.mk (α x)) = r * θ (QuotientGroup.mk x) * r⁻¹) :
    ∃ l₁ : Q, ∀ x : Q, α x = l₁ * x * l₁⁻¹ := by
  obtain ⟨l₁, hl₁⟩ := QuotientGroup.mk_surjective (θ.symm r)
  have hθl : θ (QuotientGroup.mk l₁) = r := by
    rw [hl₁]
    exact θ.apply_symm_apply r
  obtain ⟨β, hβ0⟩ : ∃ β : Q →* Q, ∀ x, β x = l₁ * x * l₁⁻¹ :=
    ⟨MonoidHom.mk' (fun x => l₁ * x * l₁⁻¹) (fun x y => by
      show l₁ * (x * y) * l₁⁻¹ = (l₁ * x * l₁⁻¹) * (l₁ * y * l₁⁻¹)
      group), fun x => rfl⟩
  have hβ : ∀ x : Q, θ (QuotientGroup.mk (β x)) = r * θ (QuotientGroup.mk x) * r⁻¹ := by
    intro x
    rw [hβ0 x]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_inv, hθl]
  have hc : ∀ x : Q, (β x)⁻¹ * α x ∈ Subgroup.center Q := by
    intro x
    have hmk : (QuotientGroup.mk (β x) : Q ⧸ Subgroup.center Q) = QuotientGroup.mk (α x) := by
      apply θ.injective
      rw [hβ x, hα x]
    exact QuotientGroup.eq.1 hmk
  have hmul : ∀ y z : Q, (β (y * z))⁻¹ * α (y * z) = ((β y)⁻¹ * α y) * ((β z)⁻¹ * α z) := by
    intro y z
    have hcu := Subgroup.mem_center_iff.1 (hc y) ((β z)⁻¹)
    rw [map_mul, map_mul, mul_inv_rev]
    calc (β z)⁻¹ * (β y)⁻¹ * (α y * α z) = (β z)⁻¹ * ((β y)⁻¹ * α y) * α z := by
          simp only [mul_assoc]
      _ = ((β y)⁻¹ * α y) * (β z)⁻¹ * α z := by rw [hcu]
      _ = ((β y)⁻¹ * α y) * ((β z)⁻¹ * α z) := by simp only [mul_assoc]
  have hcy1 : ∀ y : Q, (β y)⁻¹ * α y = 1 := fun y =>
    CFSG.LocalAnalysis.GLTheoremA.S171.hod_central_hom_trivial hQ (fun y => (β y)⁻¹ * α y) hc hmul y
  exact ⟨l₁, fun x => ((inv_mul_eq_one.1 (hcy1 x)).symm).trans (hβ0 x)⟩

section Cert


theorem d4InnerDiagRes_holds : D4InnerDiagRes := by
  intro H _ _ J B b _hJq hcat hIn hb
  obtain ⟨hBN, hM⟩ := hIn
  obtain ⟨hcomm, lab, hlab, hraw⟩ :=
    CFSG.StandardType.Canonical.largeEvenMarking_markedModel hM
  have hlabD : lab = ⟨.D, 4, 1⟩ := by
    obtain ⟨R0, inst0, I0, F0, -, -, θ0, -, hm0⟩ :=
      CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
    have hMX : CFSG.StandardType.MarkedModel lab (PSimple 3 J) :=
      CFSG.StandardType.MarkedModel.of_mulEquiv θ0.symm hm0
    obtain ⟨q, hv, hq, ⟨e'⟩⟩ := CFSG.LocalAnalysis.GLTheoremA.CatB.lieIndex_isD4two hcat
    obtain ⟨h1, h2⟩ := CFSG.LocalAnalysis.GLTheoremA.primePower_eq_of_card_eq Nat.prime_two
      (s := 1) (by norm_num) (hq.trans (by norm_num))
    have hm := CFSG.Models.lieModel_D 4 q hv e'
    rw [h1, h2] at hm
    exact CFSG.LocalAnalysis.GLTheoremA.S171.hod_lab_d4 (hm.toBlueprint (by decide)) hMX
  subst hlabD
  obtain ⟨R, inst, I, F, ⟨-, -, θ, hP, -⟩, hI⟩ :=
    CFSG.StandardType.Canonical.largeEvenRawDatum_exists
      (CFSG.LocalAnalysis.GLTheoremA.rk2_inndiag_subset_inn_of_notDerived hlab
        (by decide) (by decide) (by decide) (by decide) _ hraw)
  obtain ⟨φ, hφI, hind⟩ := hP b hb
  obtain ⟨r, hr⟩ := hI hφI
  have hbJ : ∀ x : ↥J, b⁻¹ * (x : H) * b ∈ J := fun x =>
    (Subgroup.mem_normalizer_iff.1 (hBN hb) (b⁻¹ * (x : H) * b)).mpr
      (by rw [show b * (b⁻¹ * (x : H) * b) * b⁻¹ = (x : H) by group]; exact x.2)
  have hbJ' : ∀ x : ↥J, b * (x : H) * b⁻¹ ∈ J := fun x =>
    (Subgroup.mem_normalizer_iff.1 (hBN hb) (x : H)).mp x.2
  let cJ : ↥J ≃* ↥J :=
    { toFun := fun x => ⟨b⁻¹ * (x : H) * b, hbJ x⟩
      invFun := fun x => ⟨b * (x : H) * b⁻¹, hbJ' x⟩
      left_inv := fun x => Subtype.ext (by
        show b * (b⁻¹ * (x : H) * b) * b⁻¹ = (x : H)
        group)
      right_inv := fun x => Subtype.ext (by
        show b⁻¹ * (b * (x : H) * b⁻¹) * b = (x : H)
        group)
      map_mul' := fun x y => Subtype.ext (by
        show b⁻¹ * ((x : H) * (y : H)) * b = (b⁻¹ * (x : H) * b) * (b⁻¹ * (y : H) * b)
        group) }
  have hcJ : ∀ x : ↥J, ((cJ x : ↥J) : H) = b⁻¹ * (x : H) * b := fun x => rfl
  have hcore : ∀ z : ↥J, z ∈ GLAPPrimeCore 3 ↥J → cJ z ∈ GLAPPrimeCore 3 ↥J := by
    intro z hz
    have hmap : (GLAPPrimeCore 3 ↥J).map cJ.toMonoidHom = GLAPPrimeCore 3 ↥J :=
      CFSG.pPrimeCore_map_iso 3 cJ
    have hm : cJ z ∈ (GLAPPrimeCore 3 ↥J).map cJ.toMonoidHom := Subgroup.mem_map_of_mem _ hz
    rw [hmap] at hm
    exact hm
  let αQ : PQuot 3 J →* PQuot 3 J :=
    QuotientGroup.map (GLAPPrimeCore 3 ↥J) (GLAPPrimeCore 3 ↥J) cJ.toMonoidHom
      (fun z hz => hcore z hz)
  have hα : ∀ q : PQuot 3 J, θ (QuotientGroup.mk (αQ q)) = r * θ (QuotientGroup.mk q) * r⁻¹ := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    have hrel : indRel 3 J b (QuotientGroup.mk x) (αQ (QuotientGroup.mk x)) :=
      ⟨x, cJ x, rfl, rfl, rfl⟩
    have h := hind (QuotientGroup.mk x) (αQ (QuotientGroup.mk x)) hrel
    rw [← hr, MulAut.conj_apply] at h
    exact h.symm
  obtain ⟨l₁, hl₁⟩ := conj_of_quotient_eq hcomm θ r αQ hα
  obtain ⟨l₀, rfl⟩ := QuotientGroup.mk_surjective l₁
  refine ⟨(l₀ : H)⁻¹, J.inv_mem l₀.2, fun y hy => ?_⟩
  obtain ⟨yJ, rfl⟩ : ∃ yJ : ↥J, (yJ : H) = y := ⟨⟨y, hy⟩, rfl⟩
  have hmk : (QuotientGroup.mk (l₀ * yJ * l₀⁻¹) : PQuot 3 J) = QuotientGroup.mk (cJ yJ) := by
    have h := hl₁ (QuotientGroup.mk yJ)
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at h ⊢
    exact h.symm
  have hcen : (l₀ * yJ * l₀⁻¹)⁻¹ * cJ yJ ∈ GLAPPrimeCore 3 ↥J := QuotientGroup.eq.1 hmk
  have hz : (((l₀ * yJ * l₀⁻¹)⁻¹ * cJ yJ : ↥J) : H) ∈ GLAPPrimeCoreOf 3 J :=
    Subgroup.mem_map_of_mem J.subtype hcen
  have e : (((l₀ : H)⁻¹)⁻¹ * (yJ : H) * (l₀ : H)⁻¹)⁻¹ * (b⁻¹ * (yJ : H) * b) =
      (((l₀ * yJ * l₀⁻¹)⁻¹ * cJ yJ : ↥J) : H) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv, hcJ]
  rw [e]
  exact hz

end Cert

end CFSG.LocalAnalysis.GLTheoremA.HSubT

end
