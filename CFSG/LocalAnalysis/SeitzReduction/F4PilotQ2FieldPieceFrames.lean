module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2FieldPieceConj
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2FieldPieceModel

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint
open CFSG.Quasithin (perfectCore perfectCore_le)

local instance f4PilotQ2FieldPieceFramesNeZeroRank : NeZero Tag.F4.rank := ⟨by decide⟩


section Frame

variable (k : Type) [Field k] in
@[expose] def Q2pFrame (γ : Fin (Tag.rank .F4) → ℤ) (U : Subgroup (adjointGroup .F4 k)) : Prop :=
  U.map (adjointGroup .F4 k).subtype ≤ rootSubgroup .F4 k γ ⊔ rootSubgroup .F4 k (-γ) ∧
    IsCyclic U ∧ Nat.card U = 3

variable {k : Type} [Field k]

theorem isCyclic_card_map_of_injective_q2p {G H : Type*} [Group G] [Group H] {U : Subgroup G}
    {f : G →* H} (hf : Function.Injective f) (hc : IsCyclic U) (h3 : Nat.card U = 3) :
    IsCyclic (U.map f) ∧ Nat.card (U.map f) = 3 :=
  ⟨isCyclic_of_surjective _ (U.equivMapOfInjective f hf).surjective,
    by rw [Subgroup.card_map_of_injective hf, h3]⟩

theorem map_conj_map_subtype_q2p (m : adjointGroup .F4 k) (H : Subgroup (adjointGroup .F4 k)) :
    (H.map (MulAut.conj m).toMonoidHom).map (adjointGroup .F4 k).subtype =
      (H.map (adjointGroup .F4 k).subtype).map
        (MulAut.conj (m : ModGL .F4 k)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  rfl

theorem Q2pFrame.map_conj_weylRepC {γ : Fin (Tag.rank .F4) → ℤ} {U : Subgroup (adjointGroup .F4 k)}
    (h : Q2pFrame k γ U) (hγ : IsRoot .F4 γ) (w : WeylGroup .F4) :
    Q2pFrame k (w • γ) (U.map (MulAut.conj (weylRepC k w)).toMonoidHom) :=
  ⟨map_conj_weylRepC_le_rootPair w hγ h.1,
    isCyclic_card_map_of_injective_q2p (MulAut.conj (weylRepC k w)).injective h.2.1 h.2.2⟩

theorem Q2pFrame.map_conj_n1242 {U : Subgroup (adjointGroup .F4 k)} (h : Q2pFrame k rootR U) :
    Q2pFrame k root1242 (U.map (MulAut.conj (n1242 k)).toMonoidHom) := by
  refine ⟨?_, isCyclic_card_map_of_injective_q2p (MulAut.conj (n1242 k)).injective h.2.1 h.2.2⟩
  rw [map_conj_map_subtype_q2p]
  refine (Subgroup.map_mono h.1).trans ?_
  rw [Subgroup.map_sup, map_conj_n1242_rootSubgroup isRoot_rootR,
    map_conj_n1242_rootSubgroup (IsRoot.neg isRoot_rootR), smul_neg, w1242_smul_rootR]

theorem Q2pFrame.map_subtype_le {γ θ : Fin (Tag.rank .F4) → ℤ} {U : Subgroup (adjointGroup .F4 k)}
    (h : Q2pFrame k γ U) (hγ : IsRoot .F4 γ) (h0 : iform θ γ = 0) :
    U.map (adjointGroup .F4 k).subtype ≤ rootSpan .F4 k (orthRoots θ) :=
  h.1.trans (rootPair_le_rootSpan_orthRoots_q2p hγ h0)

theorem exists_smul_rootR_eq_q2p {γ : Fin (Tag.rank .F4) → ℤ} (hγ : IsRoot .F4 γ)
    (hl : iform γ γ = 4) : ∃ w : WeylGroup .F4, w • rootR = γ := by
  obtain ⟨w, hw⟩ := exists_smul_eq_rootR hγ hl
  exact ⟨w⁻¹, by rw [← hw, inv_smul_smul]⟩

theorem exists_smul_rootS_eq_q2p {γ : Fin (Tag.rank .F4) → ℤ} (hγ : IsRoot .F4 γ)
    (hs : iform γ γ = 2) : ∃ w : WeylGroup .F4, w • rootS = γ := by
  obtain ⟨w, hw⟩ := exists_smul_eq_rootS hγ hs
  exact ⟨w⁻¹, by rw [← hw, inv_smul_smul]⟩

end Frame

section Data

@[expose] def Q2pFrameData (θ γ₁ γ₂ : Fin (Tag.rank .F4) → ℤ) (j : Fin (Tag.rank .F4))
    (m : Fin (Tag.rank .F4) → Fin 3 → ℤ) : Prop :=
  θ ∈ rootFinset .F4 ∧ γ₁ ∈ rootFinset .F4 ∧ γ₂ ∈ rootFinset .F4 ∧ iform γ₁ γ₂ = 0 ∧
    iform θ γ₁ = 0 ∧ iform θ γ₂ = 0 ∧ iform θ (Pi.single j 1) = 0 ∧
      iform γ₁ (Pi.single j 1) = 0 ∧ iform γ₂ (Pi.single j 1) = 0 ∧
        Q2pTorusGen ![θ, γ₁, γ₂] j m

theorem q2pFrameData_aX : Q2pFrameData rootR (f4Vec 0 1 2 2) (f4Vec 0 1 2 0) 1
    ![![1, 0, 0], ![0, 0, 0], ![-1, 1, 1], ![1, 1, 0]] := by
  unfold Q2pFrameData Q2pTorusGen
  decide +kernel

theorem q2pFrameData_aY : Q2pFrameData rootS (f4Vec 1 1 1 0) (f4Vec 0 1 2 0) 1
    ![![-1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, 0]] := by
  unfold Q2pFrameData Q2pTorusGen
  decide +kernel

theorem q2pFrameData_aZ : Q2pFrameData (f4Vec 0 1 2 0) rootR (f4Vec 0 1 2 2) 1
    ![![0, 1, 0], ![0, 0, 0], ![1, -1, 1], ![0, 1, 1]] := by
  unfold Q2pFrameData Q2pTorusGen
  decide +kernel

theorem q2pFrameData_aZ' : Q2pFrameData (f4Vec 0 1 2 0) rootS (f4Vec 1 1 1 0) 1
    ![![0, -1, -1], ![0, 0, 0], ![1, 0, -1], ![0, 1, 0]] := by
  unfold Q2pFrameData Q2pTorusGen
  decide +kernel

theorem q2pFrameData_bX : Q2pFrameData rootR (f4Vec 0 1 2 2) (f4Vec 0 1 1 0) 2
    ![![1, 0, 0], ![0, -1, -1], ![0, 0, 0], ![1, 1, 0]] := by
  unfold Q2pFrameData Q2pTorusGen
  decide +kernel

theorem q2pFrameData_bY : Q2pFrameData rootS (f4Vec 1 1 1 0) (f4Vec 0 1 1 0) 2
    ![![-1, -1, 0], ![1, -1, -1], ![0, 0, 0], ![1, 0, 0]] := by
  unfold Q2pFrameData Q2pTorusGen
  decide +kernel

theorem q2pFrameData_bZ : Q2pFrameData (f4Vec 0 1 1 0) rootR (f4Vec 0 1 2 2) 2
    ![![0, 1, 0], ![-1, 0, -1], ![0, 0, 0], ![0, 1, 1]] := by
  unfold Q2pFrameData Q2pTorusGen
  decide +kernel

theorem q2pFrameData_bZ' : Q2pFrameData (f4Vec 0 1 1 0) rootS (f4Vec 1 1 1 0) 2
    ![![0, -1, -1], ![-1, 1, -1], ![0, 0, 0], ![0, 1, 0]] := by
  unfold Q2pFrameData Q2pTorusGen
  decide +kernel

theorem q2pFrameData_cY : Q2pFrameData rootS (f4Vec 1 2 2 0) (f4Vec 0 0 1 0) 0
    ![![0, 0, 0], ![1, 1, 0], ![0, 1, -1], ![1, 0, 0]] := by
  unfold Q2pFrameData Q2pTorusGen
  decide +kernel

theorem q2pFrameData_cX' : Q2pFrameData root1242 (f4Vec 1 2 2 2) (f4Vec 1 2 2 0) 0
    ![![0, 0, 0], ![1, 1, 1], ![-1, 1, 1], ![1, 1, 0]] := by
  unfold Q2pFrameData Q2pTorusGen
  decide +kernel

theorem q2pFrameData_cZ : Q2pFrameData (f4Vec 1 2 2 0) rootS (f4Vec 0 0 1 0) 0
    ![![0, 0, 0], ![1, 1, 0], ![1, 0, -1], ![0, 1, 0]] := by
  unfold Q2pFrameData Q2pTorusGen
  decide +kernel

theorem q2pFrameData_cZ' : Q2pFrameData (f4Vec 1 2 2 0) root1242 (f4Vec 1 2 2 2) 0
    ![![0, 0, 0], ![1, 1, 1], ![1, -1, 1], ![0, 1, 1]] := by
  unfold Q2pFrameData Q2pTorusGen
  decide +kernel

theorem q2pFrameData_dX : Q2pFrameData rootR (f4Vec 0 1 0 0) (f4Vec 0 1 2 1) 3
    ![![1, 0, 0], ![0, -1, -1], ![-1, 0, 1], ![0, 0, 0]] := by
  unfold Q2pFrameData Q2pTorusGen
  decide +kernel

theorem q2pFrameData_dX' : Q2pFrameData root1242 (f4Vec 1 0 0 0) (f4Vec 1 2 2 1) 3
    ![![-1, -1, -1], ![1, 0, 1], ![-1, 0, 1], ![0, 0, 0]] := by
  unfold Q2pFrameData Q2pTorusGen
  decide +kernel

theorem q2pFrameData_dZ₁ : Q2pFrameData (f4Vec 0 1 2 1) rootR (f4Vec 0 1 0 0) 3
    ![![0, 1, 0], ![-1, 0, -1], ![1, -1, 0], ![0, 0, 0]] := by
  unfold Q2pFrameData Q2pTorusGen
  decide +kernel

theorem q2pFrameData_dZ₁' : Q2pFrameData (f4Vec 0 1 2 1) (f4Vec 1 2 2 1) (f4Vec 1 1 2 1) 3
    ![![0, -1, -1], ![-1, 1, -1], ![1, 1, 1], ![0, 0, 0]] := by
  unfold Q2pFrameData Q2pTorusGen
  decide +kernel

theorem q2pFrameData_dZ₂ : Q2pFrameData (f4Vec 1 2 2 1) (f4Vec 0 1 2 1) (f4Vec 1 1 2 1) 3
    ![![-1, 0, -1], ![1, -1, -1], ![1, 1, 1], ![0, 0, 0]] := by
  unfold Q2pFrameData Q2pTorusGen
  decide +kernel

theorem q2pFrameData_dZ₂' : Q2pFrameData (f4Vec 1 2 2 1) root1242 (f4Vec 1 0 0 0) 3
    ![![-1, -1, -1], ![1, 1, 0], ![1, -1, 0], ![0, 0, 0]] := by
  unfold Q2pFrameData Q2pTorusGen
  decide +kernel

end Data

theorem perfectCore_frame_eq {k K₂ : Type} [Field k] [Field K₂] [Finite k] [Finite K₂]
    [CharP K₂ 2] (hk : Nat.card k = 2) (hK₂ : Nat.card K₂ = 2 ^ 2) (ι : k →+* K₂)
    {θ γ₁ γ₂ : Fin (Tag.rank .F4) → ℤ} {j : Fin (Tag.rank .F4)}
    {m : Fin (Tag.rank .F4) → Fin 3 → ℤ} (hD : Q2pFrameData θ γ₁ γ₂ j m)
    {U₁ U₂ : Subgroup (adjointGroup .F4 k)} (h₁ : Q2pFrame k γ₁ U₁) (h₂ : Q2pFrame k γ₂ U₂) :
    perfectCore (rootSpan .F4 K₂ (orthRoots θ) ⊓ centralizer
      ((((U₁ ⊔ U₂).map (adjointGroup .F4 k).subtype).map (baseChangeGL ι) :
        Subgroup (ModGL .F4 K₂)) : Set (ModGL .F4 K₂))) =
      rootSpan .F4 K₂ (amalgamRoots {j}) := by
  obtain ⟨hθ, hγ₁, hγ₂, h12, hθ₁, hθ₂, hjθ, hj₁, hj₂, hm⟩ := hD
  obtain ⟨hc₁, h3₁⟩ := isCyclic_card_map_of_injective_q2p (adjointGroup .F4 k).subtype_injective
    h₁.2.1 h₁.2.2
  obtain ⟨hc₂, h3₂⟩ := isCyclic_card_map_of_injective_q2p (adjointGroup .F4 k).subtype_injective
    h₂.2.1 h₂.2.2
  rw [Subgroup.map_sup]
  exact perfectCore_rootSpan_orthRoots_inf_centralizer_eq hk hK₂ ι (mem_rootFinset.1 hθ)
    (mem_rootFinset.1 hγ₁) (mem_rootFinset.1 hγ₂) h12 hθ₁ hθ₂ hjθ hj₁ hj₂ hm h₁.1 h₂.1 hc₁ hc₂
    h3₁ h3₂

end CFSG.SeitzReduction.F4Pilot
