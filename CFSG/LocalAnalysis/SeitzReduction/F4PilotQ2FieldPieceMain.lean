module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2FieldPieceFrames
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2FieldRowMain

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint
open CFSG.Quasithin (perfectCore perfectCore_le)
open CFSG.LieType.Ree (ReeTag)

local instance f4PilotQ2FieldPieceMainNeZeroRank : NeZero Tag.F4.rank := ⟨by decide⟩

section Levi

variable {k : Type} [Field k]

theorem sup_le_levi_of_frames (N : AmalgamNeighbour) {γ₁ γ₂ : Fin (Tag.rank .F4) → ℤ}
    (hγ₁ : IsRoot .F4 γ₁) (hγ₂ : IsRoot .F4 γ₂) (h₁₀ : iform N.root γ₁ = 0)
    (h₂₀ : iform N.root γ₂ = 0) {U₁ U₂ : Subgroup (adjointGroup .F4 k)} (h₁ : Q2pFrame k γ₁ U₁)
    (h₂ : Q2pFrame k γ₂ U₂) : U₁ ⊔ U₂ ≤ N.levi k := by
  rw [AmalgamNeighbour.levi_eq k N]
  refine sup_le ?_ ?_ <;> rw [subgroupOf, ← map_le_iff_le_comap]
  · exact h₁.map_subtype_le hγ₁ h₁₀
  · exact h₂.map_subtype_le hγ₂ h₂₀

theorem map_conj_inv_weylRepC_le_levi (w : WeylGroup .F4) (N : AmalgamNeighbour)
    {V : Subgroup (adjointGroup .F4 k)}
    (hV : V.map (adjointGroup .F4 k).subtype ≤ rootSpan .F4 k (orthRoots (w • N.root))) :
    V.map (MulAut.conj (weylRepC k w)⁻¹).toMonoidHom ≤ N.levi k := by
  rw [AmalgamNeighbour.levi_eq k N]
  rintro _ ⟨v, hv, rfl⟩
  rw [mem_subgroupOf]
  have h1 : (v : ModGL .F4 k) ∈ (rootSpan .F4 k (orthRoots N.root)).map
      (MulAut.conj (canonicalRep (coxeterSystem .F4) k w)).toMonoidHom := by
    rw [(canonical_weyl_root_transport .F4 k).1 w _ fun α hα => hα.1, image_smul_orthRoots]
    exact hV ⟨v, hv, rfl⟩
  obtain ⟨u, hu, hvu⟩ := h1
  have hcoe : (((MulAut.conj (weylRepC k w)⁻¹).toMonoidHom v : adjointGroup .F4 k) :
      ModGL .F4 k) = (canonicalRep (coxeterSystem .F4) k w)⁻¹ * (v : ModGL .F4 k) *
        canonicalRep (coxeterSystem .F4) k w := by
    change (((weylRepC k w)⁻¹ * v * (weylRepC k w)⁻¹⁻¹ : adjointGroup .F4 k) : ModGL .F4 k) = _
    rw [inv_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    rfl
  rw [hcoe, ← hvu]
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [show (canonicalRep (coxeterSystem .F4) k w)⁻¹ * (canonicalRep (coxeterSystem .F4) k w * u *
      (canonicalRep (coxeterSystem .F4) k w)⁻¹) * canonicalRep (coxeterSystem .F4) k w = u by
    group]
  exact hu

end Levi

section Steps

variable {K : Type} [Field K] [Finite K] [CharP K 2] {σ : K ≃+* K} {G : Type} [Group G]
  [Finite G] {L : Subgroup G} {e : L ≃* adjointGroup .F4 (fixSubfield σ)}

theorem Q2FieldParam.range_restrict_eq_of_frames (hk : Nat.card (fixSubfield σ) = 2)
    (hK : Nat.card K = 2 ^ 2) {N : AmalgamNeighbour} {E X : Subgroup G}
    (h : Q2FieldParam σ e N E) (hE : E = centralizerPerfectCore X) {j : Fin (Tag.rank .F4)}
    (hJ : ({j} : Finset (Fin (Tag.rank .F4))) ⊆ N.nodes) {γ₁ γ₂ : Fin (Tag.rank .F4) → ℤ}
    {m : Fin (Tag.rank .F4) → Fin 3 → ℤ} (hD : Q2pFrameData N.root γ₁ γ₂ j m)
    {U₁ U₂ : Subgroup (adjointGroup .F4 (fixSubfield σ))}
    (h₁ : Q2pFrame (fixSubfield σ) γ₁ U₁) (h₂ : Q2pFrame (fixSubfield σ) γ₂ U₂) :
    (h.restrict hJ).range = centralizerPerfectCore (X ⊔ subgroupToG e (U₁ ⊔ U₂)) :=
  h.range_restrict_eq_centralizerPerfectCore_sup_GL hE hJ
    (sup_le_levi_of_frames N (mem_rootFinset.1 hD.2.1) (mem_rootFinset.1 hD.2.2.1)
      hD.2.2.2.2.1 hD.2.2.2.2.2.1 h₁ h₂)
    (perfectCore_frame_eq hk hK _ hD h₁ h₂)

theorem Q2FieldParam.centralizerPerfectCore_conj_frames_eq (hk : Nat.card (fixSubfield σ) = 2)
    (hK : Nat.card K = 2 ^ 2) {N : AmalgamNeighbour} {E X : Subgroup G}
    (h : Q2FieldParam σ e N E) (hE : E = centralizerPerfectCore X) (w : WeylGroup .F4)
    {θ : Fin (Tag.rank .F4) → ℤ} (hθ : w • N.root = θ) {j : Fin (Tag.rank .F4)}
    {γ₁ γ₂ γ₁' γ₂' : Fin (Tag.rank .F4) → ℤ} {m m' : Fin (Tag.rank .F4) → Fin 3 → ℤ}
    (hD : Q2pFrameData θ γ₁ γ₂ j m) (hD' : Q2pFrameData θ γ₁' γ₂' j m')
    {U₁ U₂ U₁' U₂' : Subgroup (adjointGroup .F4 (fixSubfield σ))}
    (h₁ : Q2pFrame (fixSubfield σ) γ₁ U₁) (h₂ : Q2pFrame (fixSubfield σ) γ₂ U₂)
    (h₁' : Q2pFrame (fixSubfield σ) γ₁' U₁') (h₂' : Q2pFrame (fixSubfield σ) γ₂' U₂') :
    centralizerPerfectCore (X.map (MulAut.conj ((e.symm (weylRepC (fixSubfield σ) w) : L) :
        G)).toMonoidHom ⊔ subgroupToG e (U₁ ⊔ U₂)) =
      centralizerPerfectCore (X.map (MulAut.conj ((e.symm (weylRepC (fixSubfield σ) w) : L) :
        G)).toMonoidHom ⊔ subgroupToG e (U₁' ⊔ U₂')) := by
  have hle : ∀ {γ₁ γ₂ : Fin (Tag.rank .F4) → ℤ} {m : Fin (Tag.rank .F4) → Fin 3 → ℤ}
      {U₁ U₂ : Subgroup (adjointGroup .F4 (fixSubfield σ))}, Q2pFrameData θ γ₁ γ₂ j m →
      Q2pFrame (fixSubfield σ) γ₁ U₁ → Q2pFrame (fixSubfield σ) γ₂ U₂ →
      (U₁ ⊔ U₂).map (MulAut.conj (weylRepC (fixSubfield σ) w)⁻¹).toMonoidHom ≤
        N.levi (fixSubfield σ) := fun hD h₁ h₂ => by
    refine map_conj_inv_weylRepC_le_levi w N ?_
    rw [hθ, Subgroup.map_sup]
    exact sup_le (h₁.map_subtype_le (mem_rootFinset.1 hD.2.1) hD.2.2.2.2.1)
      (h₂.map_subtype_le (mem_rootFinset.1 hD.2.2.1) hD.2.2.2.2.2.1)
  refine h.centralizerPerfectCore_map_conj_sup_eq hE _ (hle hD h₁ h₂) (hle hD' h₁' h₂') ?_
  rw [map_conj_baseChangeGL_weylRepC_rootSpan_orthRoots, hθ, perfectCore_frame_eq hk hK _ hD h₁ h₂,
    perfectCore_frame_eq hk hK _ hD' h₁' h₂']

end Steps

section Bookkeeping

variable {G : Type} [Group G] {L : Subgroup G}

theorem subgroupToG_sup_q2p {K : Type} [Field K] (e : L ≃* adjointGroup .F4 K)
    (A B : Subgroup (adjointGroup .F4 K)) :
    subgroupToG e (A ⊔ B) = subgroupToG e A ⊔ subgroupToG e B := by
  unfold subgroupToG
  rw [Subgroup.map_sup, Subgroup.map_sup]

theorem subgroupToG_trans_map_q2p {K K' : Type} [Field K] [Field K'] (e : L ≃* adjointGroup .F4 K)
    (f : adjointGroup .F4 K ≃* adjointGroup .F4 K') (W : Subgroup (adjointGroup .F4 K)) :
    subgroupToG (e.trans f) (W.map f.toMonoidHom) = subgroupToG e W := by
  have hc : (e.trans f).symm.toMonoidHom.comp f.toMonoidHom = e.symm.toMonoidHom :=
    MonoidHom.ext fun x => by simp
  have h : (W.map f.toMonoidHom).map (e.trans f).symm.toMonoidHom = W.map e.symm.toMonoidHom := by
    rw [Subgroup.map_map, hc]
  unfold subgroupToG
  rw [h]

theorem subgroupToG_trans_symm_q2p {K : Type} [Field K] (e : L ≃* adjointGroup .F4 K)
    (ψ : MulAut (adjointGroup .F4 K)) (W : Subgroup (adjointGroup .F4 K)) :
    subgroupToG (e.trans ψ.symm) W = subgroupToG e (W.map ψ.toMonoidHom) := by
  unfold subgroupToG
  congr 1
  rw [Subgroup.map_map]
  rfl

end Bookkeeping

section StepsG

variable {K : Type} [Field K] [Finite K] [CharP K 2] {σ : K ≃+* K} {G : Type} [Group G]
  [Finite G] {L : Subgroup G} {e : L ≃* adjointGroup .F4 (fixSubfield σ)}

theorem Q2FieldParam.range_restrict_eq_of_frames' (hk : Nat.card (fixSubfield σ) = 2)
    (hK : Nat.card K = 2 ^ 2) {N : AmalgamNeighbour} {E X : Subgroup G}
    (h : Q2FieldParam σ e N E) (hE : E = centralizerPerfectCore X)
    {A₀ : Subgroup (adjointGroup .F4 (fixSubfield σ))} (hXA : X = subgroupToG e A₀)
    {j : Fin (Tag.rank .F4)} (hJ : ({j} : Finset (Fin (Tag.rank .F4))) ⊆ N.nodes)
    {γ₁ γ₂ : Fin (Tag.rank .F4) → ℤ} {m : Fin (Tag.rank .F4) → Fin 3 → ℤ}
    (hD : Q2pFrameData N.root γ₁ γ₂ j m) {U₁ U₂ : Subgroup (adjointGroup .F4 (fixSubfield σ))}
    (h₁ : Q2pFrame (fixSubfield σ) γ₁ U₁) (h₂ : Q2pFrame (fixSubfield σ) γ₂ U₂) :
    (h.restrict hJ).range = centralizerPerfectCore (subgroupToG e (A₀ ⊔ (U₁ ⊔ U₂))) := by
  rw [h.range_restrict_eq_of_frames hk hK hE hJ hD h₁ h₂, hXA, ← subgroupToG_sup_q2p]

theorem Q2FieldParam.centralizerPerfectCore_conj_frames_eq' (hk : Nat.card (fixSubfield σ) = 2)
    (hK : Nat.card K = 2 ^ 2) {N : AmalgamNeighbour} {E X : Subgroup G}
    (h : Q2FieldParam σ e N E) (hE : E = centralizerPerfectCore X)
    {A₀ : Subgroup (adjointGroup .F4 (fixSubfield σ))} (hXA : X = subgroupToG e A₀)
    (w : WeylGroup .F4) {θ : Fin (Tag.rank .F4) → ℤ} (hθ : w • N.root = θ)
    {j : Fin (Tag.rank .F4)} {γ₁ γ₂ γ₁' γ₂' : Fin (Tag.rank .F4) → ℤ}
    {m m' : Fin (Tag.rank .F4) → Fin 3 → ℤ} (hD : Q2pFrameData θ γ₁ γ₂ j m)
    (hD' : Q2pFrameData θ γ₁' γ₂' j m')
    {U₁ U₂ U₁' U₂' : Subgroup (adjointGroup .F4 (fixSubfield σ))}
    (h₁ : Q2pFrame (fixSubfield σ) γ₁ U₁) (h₂ : Q2pFrame (fixSubfield σ) γ₂ U₂)
    (h₁' : Q2pFrame (fixSubfield σ) γ₁' U₁') (h₂' : Q2pFrame (fixSubfield σ) γ₂' U₂') :
    centralizerPerfectCore (subgroupToG e
        (A₀.map (MulAut.conj (weylRepC (fixSubfield σ) w)).toMonoidHom ⊔ (U₁ ⊔ U₂))) =
      centralizerPerfectCore (subgroupToG e
        (A₀.map (MulAut.conj (weylRepC (fixSubfield σ) w)).toMonoidHom ⊔ (U₁' ⊔ U₂'))) := by
  have h' := h.centralizerPerfectCore_conj_frames_eq hk hK hE w hθ hD hD' h₁ h₂ h₁' h₂'
  rwa [hXA, ← subgroupToG_map_conj_q2p, ← subgroupToG_sup_q2p, ← subgroupToG_sup_q2p] at h'

end StepsG

section Tori

variable {K : Type} [Field K] {k : Type} [Field k]

theorem q2pFrame_map_adjointGroupF4RingEquiv (ε : K ≃+* k) {X₀ : Subgroup (adjointGroup .F4 K)}
    (hXJ : X₀ ≤ (highestRootRankOne K).subgroupOf (adjointGroup .F4 K)) (hcyc : IsCyclic X₀)
    (hX₀ : Nat.card X₀ = 3) :
    Q2pFrame k rootR (X₀.map (adjointGroupF4RingEquiv ε).toMonoidHom) := by
  refine ⟨?_, isCyclic_card_map_of_injective_q2p (adjointGroupF4RingEquiv ε).injective hcyc hX₀⟩
  rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  have hxJ : (x : ModGL .F4 K) ∈ rootSubgroup .F4 K rootR ⊔ rootSubgroup .F4 K (-rootR) := by
    have h := mem_subgroupOf.1 (hXJ hx)
    rwa [highestRootRankOne_eq_rootSL2R] at h
  exact map_baseChangeGL_rootPair_le_q2p (ε : K →+* k) rootR ⟨_, hxJ, rfl⟩

theorem q2pFrame_map_graphAutF4 [Finite K] [CharP K ReeTag.F4.prime] (ε : K ≃+* k)
    {X₀ : Subgroup (adjointGroup .F4 K)}
    (hXJ : X₀ ≤ (highestRootRankOne K).subgroupOf (adjointGroup .F4 K)) (hcyc : IsCyclic X₀)
    (hX₀ : Nat.card X₀ = 3) :
    Q2pFrame k rootS ((X₀.map (graphAutF4 K).toMonoidHom).map
      (adjointGroupF4RingEquiv ε).toMonoidHom) := by
  obtain ⟨hc, h3⟩ := isCyclic_card_map_of_injective_q2p (graphAutF4 K).injective hcyc hX₀
  refine ⟨?_, isCyclic_card_map_of_injective_q2p (adjointGroupF4RingEquiv ε).injective hc h3⟩
  have hφ : X₀.map (graphAutF4 K).toMonoidHom ≤ rootSL2 K rootS := by
    rw [← map_graphAutF4_rootSL2R]
    refine Subgroup.map_mono fun x hx => ?_
    rw [rootSL2_rootR, ← highestRootRankOne_eq_rootSL2R]
    exact hXJ hx
  rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  exact map_baseChangeGL_rootPair_le_q2p (ε : K →+* k) rootS ⟨_, mem_subgroupOf.1 (hφ hx), rfl⟩

theorem exists_frame_long_q2p {A : Subgroup (adjointGroup .F4 k)} (hA : Q2pFrame k rootR A)
    {γ : Fin (Tag.rank .F4) → ℤ} (hγ : γ ∈ rootFinset .F4) (hl : iform γ γ = 4) :
    ∃ w : WeylGroup .F4, w • rootR = γ ∧
      Q2pFrame k γ (A.map (MulAut.conj (weylRepC k w)).toMonoidHom) := by
  obtain ⟨w, hw⟩ := exists_smul_rootR_eq_q2p (mem_rootFinset.1 hγ) hl
  refine ⟨w, hw, ?_⟩
  rw [← hw]
  exact hA.map_conj_weylRepC isRoot_rootR w

theorem exists_frame_short_q2p {B : Subgroup (adjointGroup .F4 k)} (hB : Q2pFrame k rootS B)
    {γ : Fin (Tag.rank .F4) → ℤ} (hγ : γ ∈ rootFinset .F4) (hs : iform γ γ = 2) :
    ∃ w : WeylGroup .F4, w • rootS = γ ∧
      Q2pFrame k γ (B.map (MulAut.conj (weylRepC k w)).toMonoidHom) := by
  obtain ⟨w, hw⟩ := exists_smul_rootS_eq_q2p (mem_rootFinset.1 hγ) hs
  refine ⟨w, hw, ?_⟩
  rw [← hw]
  exact hB.map_conj_weylRepC isRoot_rootS w

end Tori

theorem f4TwoFieldPieceInput_holds : F4TwoFieldPieceInput := by
  intro G _ _ L K _ _ _ e t hw X₀ hXJ hcyc hX₀ K₂ _ _ _ σ hK₂ hσ ε hX hY
  have hK : Nat.card K = 2 := by rw [hw.card_eq]; norm_num
  have hk : Nat.card (fixSubfield σ) = 2 := by rw [← Nat.card_congr ε.toEquiv, hK]
  have hK₂' : Nat.card K₂ = 2 ^ 2 := by rw [hK₂]; norm_num
  set A : Subgroup (adjointGroup .F4 (fixSubfield σ)) :=
    X₀.map (adjointGroupF4RingEquiv ε).toMonoidHom with hAdef
  set B : Subgroup (adjointGroup .F4 (fixSubfield σ)) :=
    (X₀.map (graphAutF4 K).toMonoidHom).map (adjointGroupF4RingEquiv ε).toMonoidHom with hBdef
  have hA : Q2pFrame (fixSubfield σ) rootR A :=
    q2pFrame_map_adjointGroupF4RingEquiv ε hXJ hcyc hX₀
  have hB : Q2pFrame (fixSubfield σ) rootS B := q2pFrame_map_graphAutF4 ε hXJ hcyc hX₀
  have hXe : subgroupToG e X₀ = subgroupToG (e.trans (adjointGroupF4RingEquiv ε)) A :=
    (subgroupToG_trans_map_q2p e _ X₀).symm
  have hYe : subgroupToG (e.trans (graphAutF4 K).symm) X₀ =
      subgroupToG (e.trans (adjointGroupF4RingEquiv ε)) B := by
    rw [subgroupToG_trans_symm_q2p, ← subgroupToG_trans_map_q2p e (adjointGroupF4RingEquiv ε)]
  have hX'E : (centralizerPerfectCore (subgroupToG e X₀)).map (MulAut.conj
      (((e.trans (adjointGroupF4RingEquiv ε)).symm (n1242 (fixSubfield σ)) : L) : G)).toMonoidHom =
        centralizerPerfectCore (subgroupToG (e.trans (adjointGroupF4RingEquiv ε)) (A.map
          (MulAut.conj (n1242 (fixSubfield σ))).toMonoidHom)) := by
    rw [map_centralizerPerfectCore, hXe, subgroupToG_map_conj_q2p]
  have hX'0 : Q2pFrame (fixSubfield σ) root1242
      (A.map (MulAut.conj (n1242 (fixSubfield σ))).toMonoidHom) := hA.map_conj_n1242
  obtain ⟨wa, hwa, hZa⟩ := exists_frame_long_q2p hA (γ := f4Vec 0 1 2 0) (by decide +kernel)
    (by decide +kernel)
  obtain ⟨wc, hwc, hZc⟩ := exists_frame_long_q2p hA (γ := f4Vec 1 2 2 0) (by decide +kernel)
    (by decide +kernel)
  obtain ⟨w₁₂, -, hX₁₂⟩ := exists_frame_long_q2p hA (γ := f4Vec 0 1 2 2) (by decide +kernel)
    (by decide +kernel)
  obtain ⟨w₁₄, -, hX₁₄⟩ := exists_frame_long_q2p hA (γ := f4Vec 1 2 2 2) (by decide +kernel)
    (by decide +kernel)
  obtain ⟨w₃₄, -, hX₃₄⟩ := exists_frame_long_q2p hA (γ := f4Vec 0 1 0 0) (by decide +kernel)
    (by decide +kernel)
  obtain ⟨w₂₃, -, hX₂₃⟩ := exists_frame_long_q2p hA (γ := f4Vec 1 0 0 0) (by decide +kernel)
    (by decide +kernel)
  obtain ⟨wb, hwb, hZb⟩ := exists_frame_short_q2p hB (γ := f4Vec 0 1 1 0) (by decide +kernel)
    (by decide +kernel)
  obtain ⟨wd₁, hwd₁, hZd₁⟩ := exists_frame_short_q2p hB (γ := f4Vec 0 1 2 1)
    (by decide +kernel) (by decide +kernel)
  obtain ⟨wd₂, hwd₂, hZd₂⟩ := exists_frame_short_q2p hB (γ := f4Vec 1 2 2 1)
    (by decide +kernel) (by decide +kernel)
  obtain ⟨w₂, -, hX₂⟩ := exists_frame_short_q2p hB (γ := f4Vec 1 1 1 0) (by decide +kernel)
    (by decide +kernel)
  obtain ⟨w₄, -, hX₄⟩ := exists_frame_short_q2p hB (γ := f4Vec 0 0 1 0) (by decide +kernel)
    (by decide +kernel)
  obtain ⟨w₅, -, hX₅⟩ := exists_frame_short_q2p hB (γ := f4Vec 1 1 2 1) (by decide +kernel)
    (by decide +kernel)
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    rw [hX.range_restrict_eq_of_frames' hk hK₂' rfl hXe one_subset_nodes_X_fieldRow q2pFrameData_aX
        hX₁₂ hZa,
      hY.range_restrict_eq_of_frames' hk hK₂' rfl hYe one_subset_nodes_Y q2pFrameData_aY hX₂ hZa]
    calc _ = _ := by congr 2; ac_rfl
      _ = _ := hX.centralizerPerfectCore_conj_frames_eq' hk hK₂' rfl hXe wa hwa q2pFrameData_aZ
          q2pFrameData_aZ' hA hX₁₂ hB hX₂
      _ = _ := by congr 2; ac_rfl
  ·
    rw [hX.range_restrict_eq_of_frames' hk hK₂' rfl hXe two_subset_nodes_X q2pFrameData_bX hX₁₂
        hZb,
      hY.range_restrict_eq_of_frames' hk hK₂' rfl hYe two_subset_nodes_Y q2pFrameData_bY hX₂ hZb]
    calc _ = _ := by congr 2; ac_rfl
      _ = _ := hY.centralizerPerfectCore_conj_frames_eq' hk hK₂' rfl hYe wb hwb q2pFrameData_bZ
          q2pFrameData_bZ' hA hX₁₂ hB hX₂
      _ = _ := by congr 2; ac_rfl
  ·
    rw [hY.range_restrict_eq_of_frames' hk hK₂' rfl hYe zero_subset_Y q2pFrameData_cY hZc hX₄,
      hX.toX'.range_restrict_eq_of_frames' hk hK₂' hX'E rfl zero_subset_X' q2pFrameData_cX' hX₁₄
        hZc]
    calc _ = _ := by congr 2; ac_rfl
      _ = _ := hX.centralizerPerfectCore_conj_frames_eq' hk hK₂' rfl hXe wc hwc q2pFrameData_cZ
          q2pFrameData_cZ' hB hX₄ hX'0 hX₁₄
      _ = _ := by congr 2; ac_rfl
  ·
    rw [hX.range_restrict_eq_of_frames' hk hK₂' rfl hXe three_subset_X q2pFrameData_dX hX₃₄ hZd₁,
      hX.toX'.range_restrict_eq_of_frames' hk hK₂' hX'E rfl three_subset_X' q2pFrameData_dX'
        hX₂₃ hZd₂]
    calc _ = _ := by congr 2; ac_rfl
      _ = _ := hY.centralizerPerfectCore_conj_frames_eq' hk hK₂' rfl hYe wd₁ hwd₁
          q2pFrameData_dZ₁ q2pFrameData_dZ₁' hA hX₃₄ hZd₂ hX₅
      _ = _ := by congr 2; ac_rfl
      _ = _ := hY.centralizerPerfectCore_conj_frames_eq' hk hK₂' rfl hYe wd₂ hwd₂
          q2pFrameData_dZ₂ q2pFrameData_dZ₂' hZd₁ hX₅ hX'0 hX₂₃
      _ = _ := by congr 2; ac_rfl

theorem twoFieldPairInput_holds : TwoFieldPairInput :=
  twoFieldPairInput_of_pieceInput f4TwoFieldPieceInput_holds

end CFSG.SeitzReduction.F4Pilot
