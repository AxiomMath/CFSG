module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeE6FourRigid

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.SeitzReduction.E6Pilot
  CFSG.HardMathSupport.Timmesfeld.Steinberg CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1T

set_option linter.unusedSectionVars false

section NoInv


private theorem torus_inv_bruhat {L : Type} [Field L] {w : WeylGroup Tag.E6}
    {hT u v : ModGL Tag.E6 L} (hhT : hT ∈ torusGroup Tag.E6 L) (huU : u ∈ posUnipotent Tag.E6 L)
    (hvI : v ∈ rootSpan Tag.E6 L (inversionSet w)) (b : Fin Tag.E6.rank → Lˣ)
    (hb : rootDiagUnit Tag.E6 b ∈ torusGroup Tag.E6 L)
    (hconj : hT * u * canonicalRep (coxeterSystem Tag.E6) L w * v * rootDiagUnit Tag.E6 b =
      (rootDiagUnit Tag.E6 b)⁻¹ * (hT * u * canonicalRep (coxeterSystem Tag.E6) L w * v)) :
    rootDiagUnit Tag.E6 b * u * (rootDiagUnit Tag.E6 b)⁻¹ = u ∧
      rootDiagUnit Tag.E6 b * v * (rootDiagUnit Tag.E6 b)⁻¹ = v ∧
      rootDiagUnit Tag.E6 b⁻¹ = canonicalRep (coxeterSystem Tag.E6) L w *
        rootDiagUnit Tag.E6 b * (canonicalRep (coxeterSystem Tag.E6) L w)⁻¹ := by
  obtain ⟨h1, h2, h3⟩ := twisted_torus_bruhat hhT huU hvI (a := b⁻¹) (b := b)
    (by rw [← rootDiagUnit_inv]; exact inv_mem hb) hb
    (by rw [← rootDiagUnit_inv]; exact hconj)
  refine ⟨?_, h2, h3⟩
  rw [← rootDiagUnit_inv] at h1
  calc rootDiagUnit Tag.E6 b * u * (rootDiagUnit Tag.E6 b)⁻¹ =
      rootDiagUnit Tag.E6 b * ((rootDiagUnit Tag.E6 b)⁻¹ * u * (rootDiagUnit Tag.E6 b)⁻¹⁻¹) *
        (rootDiagUnit Tag.E6 b)⁻¹ := by rw [h1]
    _ = u := by group

theorem false_of_inverts_innerTorus
    {L : Type} [Field L] {ω : Lˣ} (hω : orderOf ω = 3) {h : ModGL Tag.E6 L}
    (hh : h ∈ adjointGroup Tag.E6 L)
    (hinv : ∀ j : Fin 5, h * dV ω (e6InnerVec j) * h⁻¹ = (dV ω (e6InnerVec j))⁻¹) : False := by
  classical
  have hω3 : ω ^ 3 = 1 := pow_three_of_orderOf hω
  set kbS : List (List ℕ) := (Native.stdBasis 5).map (liftL (τ := .E6) e6InnerVec) with hkbS
  have hlenkb : kbS.length = 5 := by
    rw [hkbS, List.length_map, length_stdBasis']
  have hidx : ∀ j : Fin kbS.length, j.val < Tag.E6.rank := fun j =>
    lt_of_lt_of_le j.2 (by rw [hlenkb]; decide)
  have hfam : ∀ j : Fin kbS.length,
      famV (τ := .E6) ω kbS j = e6TorParam ⟨j.val, hidx j⟩ ω := by
    intro j
    apply rootDiagUnit_injective (τ := .E6) (K := L)
    change dV ω (listVec Tag.E6.rank (kbS.get j)) = _
    have hj : kbS.get j =
        liftL (τ := .E6) e6InnerVec ((Native.stdBasis 5).get ⟨j.val, by
          rw [length_stdBasis']; exact hlenkb ▸ j.2⟩) := by
      simp [hkbS]
    rw [hj, listVec_liftL, listVec_stdBasis', subLin_single, dV_e6InnerVec hω3,
      torusElt_eq_rootDiagUnit_e6TorParam]
  have hcert := Certificates.certificate13614
  unfold Native.e6FourCoreCheck at hcert
  simp only [Bool.and_eq_true, List.all_eq_true] at hcert
  obtain ⟨⟨-, hstd0⟩, -⟩ := hcert
  obtain ⟨hker0, -⟩ := famData0_of_famOK0W hω length_liftL_mem lt_of_mem_liftL_mem hstd0
  have hanti : ∀ w' : WeylGroup .E6, (∀ j : Fin kbS.length, ∀ z,
      rootChar (e6TorParam ⟨j.val, hidx j⟩ ω) (w' • z) =
        (rootChar (e6TorParam ⟨j.val, hidx j⟩ ω) z)⁻¹) → False := by
    intro w' hw'
    refine false_of_anti_E6 hω (w := w') fun j z => ?_
    rw [hfam j]
    exact hw' j z
  have hg1 : h ∈ toralCentralizer .E6 L 1 := by
    refine mem_toralCentralizer.2 ⟨hh, ?_⟩
    rw [rootDiagUnit_one, one_mul, inv_one, mul_one]
  obtain ⟨w, -, hT, hhT, u, hu, v, hv, hgdec⟩ :=
    (Chevalley_toral_centralizer_Bruhat_factors .E6 L 1).1 h hg1
  have huU : u ∈ posUnipotent .E6 L := rootSpan_mono Set.inter_subset_right hu
  have hvI : v ∈ rootSpan .E6 L (inversionSet w) := rootSpan_mono Set.inter_subset_right hv
  have hrel : ∀ j : Fin kbS.length,
      rootDiagUnit .E6 (e6TorParam ⟨j.val, hidx j⟩ ω) * u *
          (rootDiagUnit .E6 (e6TorParam ⟨j.val, hidx j⟩ ω))⁻¹ = u ∧
      rootDiagUnit .E6 (e6TorParam ⟨j.val, hidx j⟩ ω) * v *
          (rootDiagUnit .E6 (e6TorParam ⟨j.val, hidx j⟩ ω))⁻¹ = v ∧
      rootDiagUnit .E6 (e6TorParam ⟨j.val, hidx j⟩ ω)⁻¹ =
        canonicalRep (coxeterSystem Tag.E6) L w *
          rootDiagUnit .E6 (e6TorParam ⟨j.val, hidx j⟩ ω) *
            (canonicalRep (coxeterSystem Tag.E6) L w)⁻¹ := by
    intro j
    have hj5 : j.val < 5 := by have := j.2; omega
    have hx := hinv ⟨j.val, hj5⟩
    rw [dV_e6InnerVec hω3, torusElt_eq_rootDiagUnit_e6TorParam] at hx
    refine torus_inv_bruhat hhT huU hvI _
      (by rw [← torusElt_eq_rootDiagUnit_e6TorParam]; exact torusElt_mem_torusGroup _ _) ?_
    rw [← hgdec]
    rw [mul_inv_eq_iff_eq_mul] at hx
    exact hx
  have hbot : rootSpan .E6 L (∅ : Set (Fin Tag.E6.rank → ℤ)) = ⊥ := by
    simp [rootSpan]
  have hposfin : {β : Fin Tag.E6.rank → ℤ | IsRoot .E6 β ∧ 0 < height β}.Finite :=
    (finite_setOf_isRoot _).subset fun β hβ => hβ.1
  have hu1 : u = 1 := by
    have hm := mem_rootSpan_inter_of_conj_eq_family (famV (τ := .E6) ω kbS) hposfin
      (fun β hβ => hβ.1) (fun α hα hr => (positive_root_collection .E6 L).2 α hα hr) huU
      (fun j => by rw [hfam j]; exact (hrel j).1)
    rw [hker0, Set.empty_inter, hbot, Subgroup.mem_bot] at hm
    exact hm
  have hv1 : v = 1 := by
    have hm := mem_rootSpan_inter_of_conj_eq_family (famV (τ := .E6) ω kbS)
      (inversionSet_finite w) (fun β hβ => hβ.1)
      (fun α hα hr => (bruhat_cell_factorization .E6 L).2.1 w α hα hr) hvI
      (fun j => by rw [hfam j]; exact (hrel j).2.1)
    rw [hker0, Set.empty_inter, hbot, Subgroup.mem_bot] at hm
    exact hm
  refine hanti w⁻¹ fun j z => ?_
  have h3 := (hrel j).2.2
  rw [CFSG.LieType.Chevalley.canonicalRep_conj_rootDiagUnit] at h3
  have h4 := rootDiagUnit_injective (τ := .E6) (K := L) h3
  have h5 : rootChar (e6TorParam ⟨j.val, hidx j⟩ ω)⁻¹ z =
      rootChar (e6TorParam ⟨j.val, hidx j⟩ ω) (w⁻¹ • z) := by
    rw [h4, CFSG.LieType.Chevalley.rootChar_weylTuple]
  rw [← h5, CFSG.LieType.Chevalley.rootChar_inv_apply]

end NoInv

end CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3

end
