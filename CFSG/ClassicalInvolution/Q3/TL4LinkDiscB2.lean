module

public import CFSG.ClassicalInvolution.Q3.TL4LinkDiscB
public import CFSG.ClassicalInvolution.Q3.TL4Conn26Ex

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T8
open CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected dAdj)

namespace LinkDisc

theorem eq_or_eq_of_mem_pair {α : Type} {a b x y l : α} (hx : x = a ∨ x = b)
    (hy : y = a ∨ y = b) (hxy : x ≠ y) (hl : l = a ∨ l = b) : l = x ∨ l = y := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> rcases hl with rfl | rfl <;>
    first | exact Or.inl rfl | exact Or.inr rfl | exact absurd rfl hxy

section Cit3


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem false_of_edge_of_oddCore_eq_bot (hL : TightLargeHypR r n Y R S t)
    (hc : DConnected (CoreAssembly.conjClass (tightCore R))) {J M : Subgroup Y}
    (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (hM : M ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (hMJ : M ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) J)
    (hB2 : ∀ L ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R),
      secImg (CoreAssembly.conjClass (tightCore R)) t L =
          secImg (CoreAssembly.conjClass (tightCore R)) t J ∨
        secImg (CoreAssembly.conjClass (tightCore R)) t L =
          secImg (CoreAssembly.conjClass (tightCore R)) t M)
    (hO : classicalInvolutionOddCore ↥(layerY (CoreAssembly.conjClass (tightCore R)) t) = ⊥) :
    False := by
  have h := TightLargeHypR.typeRFam hL
  have hΩ := h.hyp
  have hcl := hΩ.conjInvariant
  have hd := hL.datum
  have ht := hd.isUniqueInvolution_core
  have hK : tightCore R ∈ CoreAssembly.conjClass (tightCore R) :=
    CoreAssembly.mem_conjClass_self _
  have hsub : ∀ L ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R),
      L = J ∨ L = M := by
    intro L hL'
    have key : ∀ {N : Subgroup Y},
        N ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R) →
        secImg (CoreAssembly.conjClass (tightCore R)) t L =
          secImg (CoreAssembly.conjClass (tightCore R)) t N → L = N := by
      intro N hN heq
      obtain ⟨ν, hν, e⟩ := exists_conj_of_secImg_eq h (xMem_of_mem_omegaNbr_core hL hN)
        (xMem_of_mem_omegaNbr_core hL hL') heq.symm
      rw [hO, Subgroup.mem_bot] at hν
      rw [e, hν, OneMemClass.coe_one, conjSub_one]
    rcases hB2 L hL' with e | e
    · exact Or.inl (key hJ e)
    · exact Or.inr (key hM e)
  have hKM : tightCore R ≠ M := fun e => hM.2.1 e.symm
  have hKJ : tightCore R ≠ J := fun e => hJ.2.1 e.symm
  have hJK : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) M :=
    Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ hJ.1 hM.1 hMJ
  have hconj : ∀ {g : Y} {N L : Subgroup Y}, conjSub g (tightCore R) = N →
      L ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) N →
        L = conjSub g J ∨ L = conjSub g M := by
    intro g N L hg hLN
    have h1 := omegaNbr_conj hcl hLN g⁻¹
    rw [← hg, conjSub_inv_conjSub] at h1
    rcases hsub _ h1 with e | e
    · exact Or.inl (by rw [← e, conjSub_conjSub_inv])
    · exact Or.inr (by rw [← e, conjSub_conjSub_inv])
  have hnbrJ : ∀ L ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) J,
      L = tightCore R ∨ L = M := by
    obtain ⟨g, hg⟩ := hJ.1
    intro L hL'
    exact eq_or_eq_of_mem_pair (hconj hg (Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ hK hJ.1 hJ))
      (hconj hg hMJ) hKM (hconj hg hL')
  have hnbrM : ∀ L ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) M,
      L = tightCore R ∨ L = J := by
    obtain ⟨g, hg⟩ := hM.1
    intro L hL'
    exact eq_or_eq_of_mem_pair (hconj hg (Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ hK hM.1 hM))
      (hconj hg hJK) hKJ (hconj hg hL')
  have hstep : ∀ {A B : Subgroup Y}, (A = tightCore R ∨ A = J ∨ A = M) →
      B ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) A → B = tightCore R ∨ B = J ∨ B = M := by
    intro A B hA hBA
    rcases hA with rfl | rfl | rfl
    · rcases hsub B hBA with e | e
      · exact Or.inr (Or.inl e)
      · exact Or.inr (Or.inr e)
    · rcases hnbrJ B hBA with e | e
      · exact Or.inl e
      · exact Or.inr (Or.inr e)
    · rcases hnbrM B hBA with e | e
      · exact Or.inl e
      · exact Or.inr (Or.inl e)
  have hall : ∀ L ∈ CoreAssembly.conjClass (tightCore R), L = tightCore R ∨ L = J ∨ L = M := by
    intro L hL'
    have hp := hc _ hK _ hL'
    clear hL'
    induction hp with
    | refl => exact Or.inl rfl
    | @tail B C hB' hBC ih =>
      obtain ⟨hCΩ, hadj⟩ := hBC
      rcases hadj with h1 | h2
      · exact hstep ih h1
      · have hBΩ : B ∈ CoreAssembly.conjClass (tightCore R) := by
          rcases ih with rfl | rfl | rfl
          · exact hK
          · exact hJ.1
          · exact hM.1
        exact hstep ih (Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ hCΩ hBΩ h2)
  have hKY : tightCore R ≤ layerY (CoreAssembly.conjClass (tightCore R)) t := by
    refine (Subgroup.closure_le _).mpr fun x hx => coreAt_le_layerY (xMem_core hL) ?_
    exact Subgroup.subset_closure ⟨⟨Subgroup.subset_closure hx, hd.cent hx.1⟩, hx.2⟩
  have hOK : oddCoreOf (tightCore R) ≤
      oddCoreOf (layerY (CoreAssembly.conjClass (tightCore R)) t) :=
    le_oddCoreOf_of_normal_odd ((oddCoreOf_le_self _).trans hKY)
      (fun y hy => mem_normalizer_oddCore_of_mem_normalizer
        (h.tight _ hK t ht (layerY_le_centralizer hy))) (oddCoreOf_odd_natCard _)
  have hOK' : classicalInvolutionOddCore ↥(tightCore R) = ⊥ := by
    have h1 : oddCoreOf (tightCore R) = ⊥ := by
      refine le_bot_iff.mp (hOK.trans ?_)
      unfold oddCoreOf
      rw [hO, Subgroup.map_bot]
    exact (Subgroup.map_eq_bot_iff_of_injective _ (tightCore R).subtype_injective).mp h1
  have hK2 : IsPGroup 2 ↥(tightCore R) := isPGroup_of_oddCore_eq_bot h hK hOK'
  have hconj2 : ∀ {N : Subgroup Y}, N ∈ CoreAssembly.conjClass (tightCore R) → IsPGroup 2 ↥N := by
    rintro _ ⟨g, rfl⟩
    exact hK2.map _
  have hJ2 := hconj2 hJ.1
  have hM2 := hconj2 hM.1
  have hJN : J ≤ Subgroup.normalizer ((tightCore R : Subgroup Y) : Set Y) :=
    le_normalizer_of_isPGroup h hJ hJ2
  have hJK2 : IsPGroup 2 ↥(J ⊔ tightCore R) := hJ2.to_sup_of_normal_right' hK2 hJN
  have hMN : M ≤ Subgroup.normalizer ((J ⊔ tightCore R : Subgroup Y) : Set Y) := by
    intro m hm
    have e1 := mem_normalizer_iff_conjSub_eq.mp (le_normalizer_of_isPGroup h hMJ hM2 hm)
    have e2 := mem_normalizer_iff_conjSub_eq.mp (le_normalizer_of_isPGroup h hM hM2 hm)
    rw [mem_normalizer_iff_conjSub_eq, Thompson.conjSub_sup, e1, e2]
  have hN2 : IsPGroup 2 ↥(M ⊔ (J ⊔ tightCore R)) := hM2.to_sup_of_normal_right' hJK2 hMN
  have hgen : omegaGen (CoreAssembly.conjClass (tightCore R)) ≤ M ⊔ (J ⊔ tightCore R) := by
    refine iSup₂_le fun L hL' => ?_
    rcases hall L hL' with rfl | rfl | rfl
    · exact le_sup_right.trans le_sup_right
    · exact le_sup_left.trans le_sup_right
    · exact le_sup_left
  exact hL.notInO2 ⟨omegaGen (CoreAssembly.conjClass (tightCore R)), omegaGen_normal hcl,
    hN2.to_le hgen, le_omegaGen hK ht.mem⟩

@[expose] def TightLinkEdgeOddR (r n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TightLargeHypR r n Y R S t → DConnected (CoreAssembly.conjClass (tightCore R)) →
      ¬ TriNbrAll R t → LinkAlphaBad R t →
      (∀ J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R), NoGNbr R t J) →
      classicalInvolutionOddCore ↥(layerY (CoreAssembly.conjClass (tightCore R)) t) ≠ ⊥ →
      ∀ J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R),
      ∀ M ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R),
        M ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) J →
          ¬ ∀ L ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R),
            secImg (CoreAssembly.conjClass (tightCore R)) t L =
                secImg (CoreAssembly.conjClass (tightCore R)) t J ∨
              secImg (CoreAssembly.conjClass (tightCore R)) t L =
                secImg (CoreAssembly.conjClass (tightCore R)) t M

theorem tightLinkEdgeNoTriR_of (hB : TightLinkEdgeOddR r n) : TightLinkEdgeNoTriR r n := by
  intro Y _ _ R S t hL hc hT hα hall J hJ M hM hMJ hB2
  by_cases hO : classicalInvolutionOddCore
      ↥(layerY (CoreAssembly.conjClass (tightCore R)) t) = ⊥
  · exact false_of_edge_of_oddCore_eq_bot hL hc hJ hM hMJ hB2 hO
  · exact hB Y R S t hL hc hT hα hall hO J hJ M hM hMJ hB2

end Cit3

end LinkDisc

end CFSG.ClassicalInvolution.Q3.TL4
