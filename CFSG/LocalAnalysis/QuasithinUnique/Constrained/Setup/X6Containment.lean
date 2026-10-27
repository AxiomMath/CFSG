module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Basic
public import CFSG.LieType.Chevalley.SylowOpposition
public import CFSG.LieType.Chevalley.ChevalleySplitBN
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.QuasithinUnique.Setup.X6

open CFSG.ABGLocalTools
open scoped Pointwise

section MaximalOvergroups

@[expose] def HasInvariantMaximalOvergroups (X : Type*) [Group X] (U : Subgroup X) : Prop :=
  ∃ Q₁ Q₂ : Subgroup X, Q₁ ≠ Q₂ ∧ (∀ M : Subgroup X, U ≤ M → (M ⋖ ⊤ ↔ M = Q₁ ∨ M = Q₂)) ∧
    Q₁ ⊔ Q₂ = ⊤ ∧ ¬ Q₁.Normal ∧ ¬ Q₂.Normal ∧
    ∀ α : MulAut X, U.map α.toMonoidHom = U →
      Q₁.map α.toMonoidHom = Q₁ ∧ Q₂.map α.toMonoidHom = Q₂

theorem HasInvariantMaximalOvergroups.map {X X' : Type*} [Group X] [Group X'] {U : Subgroup X}
    (h : HasInvariantMaximalOvergroups X U) (e : X ≃* X') :
    HasInvariantMaximalOvergroups X' (U.map e.toMonoidHom) := by
  obtain ⟨Q₁, Q₂, hne, hmax, hgen, hn₁, hn₂, hinv⟩ := h
  have key : ∀ x y : Subgroup X, x.map e.toMonoidHom ⋖ y.map e.toMonoidHom ↔ x ⋖ y :=
    fun x y => apply_covBy_apply_iff (MulEquiv.mapSubgroup e)
  have hnn : ∀ Q : Subgroup X, ¬ Q.Normal → ¬ (Q.map e.toMonoidHom).Normal := by
    intro Q hQ hn
    apply hQ
    have := hn.map e.symm.toMonoidHom e.symm.surjective
    rwa [map_symm_map] at this
  refine ⟨Q₁.map e.toMonoidHom, Q₂.map e.toMonoidHom, ?_, ?_, ?_, hnn _ hn₁, hnn _ hn₂, ?_⟩
  · intro hEq
    exact hne (Subgroup.map_injective (f := e.toMonoidHom) e.injective hEq)
  · intro M' hUM'
    have hA : (M'.map e.symm.toMonoidHom).map e.toMonoidHom = M' := by
      have := map_symm_map e.symm M'
      simpa using this
    have hUM : U ≤ M'.map e.symm.toMonoidHom := by
      have := Subgroup.map_mono (f := e.symm.toMonoidHom) hUM'
      rwa [map_symm_map] at this
    conv_lhs => rw [← hA, ← Subgroup.map_top_of_surjective e.toMonoidHom e.surjective]
    rw [key, hmax _ hUM]
    constructor
    · rintro (h | h)
      · left; rw [← h, hA]
      · right; rw [← h, hA]
    · rintro (h | h)
      · left; rw [h, map_symm_map]
      · right; rw [h, map_symm_map]
  · rw [← Subgroup.map_sup, hgen, Subgroup.map_top_of_surjective _ e.surjective]
  · intro α' hα'
    set α : MulAut X := e.trans (α'.trans e.symm) with hα
    have hαU : U.map α.toMonoidHom = U := by
      have h := hα'
      rw [map_comm_equiv] at h
      exact Subgroup.map_injective (f := e.toMonoidHom) e.injective h
    obtain ⟨h1, h2⟩ := hinv α hαU
    refine ⟨?_, ?_⟩
    · rw [map_comm_equiv, ← hα, h1]
    · rw [map_comm_equiv, ← hα, h2]

theorem HasInvariantMaximalOvergroups.of_isSylow {X X' : Type*} [Group X] [Group X'] [Finite X]
    [Finite X'] (e : X ≃* X') {U₀ : Subgroup X'} (h₀ : HasInvariantMaximalOvergroups X' U₀)
    (hU₀ : CFSG.QuasithinUnique.IsSylowTwoOf U₀ ⊤) {U : Subgroup X}
    (hU : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤) : HasInvariantMaximalOvergroups X U := by
  have hU' : IsSylowOf 2 (U.map e.toMonoidHom) ⊤ := by
    have := isSylowOf_map_injective (p := 2) e.toMonoidHom e.injective
      (isSylowTwoOf_iff_isSylowOf.1 hU)
    rwa [Subgroup.map_top_of_surjective _ e.surjective] at this
  obtain ⟨k, -, hk⟩ := (isSylowTwoOf_iff_isSylowOf.1 hU₀).exists_mem_conj hU'
  have hconj : U₀.map (MulAut.conj k).toMonoidHom = U.map e.toMonoidHom := by
    ext x
    rw [Subgroup.mem_map_equiv]
    simp only [MulAut.conj_symm_apply]
    exact (hk x).symm
  have h1 := h₀.map (MulAut.conj k)
  rw [hconj] at h1
  have h2 := h1.map e.symm
  rwa [map_symm_map] at h2

theorem HasInvariantMaximalOvergroups.twoGenerating {X : Type} [Group X] [Finite X]
    {U : Subgroup X} (hZ : Subgroup.center X = ⊥) (hU : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤)
    (h : HasInvariantMaximalOvergroups X U) : TwoGeneratingSylowOvergroups X := by
  obtain ⟨Q₁, Q₂, -, -, hgen, hn₁, hn₂, hinv⟩ := h
  intro D hD R hR
  exact automorphism_invariant_generating_Sylow_overgroups_lift hZ
    (isSylowTwoOf_iff_isSylowOf.1 hU) hn₁ hn₂ hgen hinv hD (isSylowTwoOf_iff_isSylowOf.1 hR)

section Ambient

variable {M : Type} [Group M]

theorem hasInvariantMaximalOvergroups_of_ambient [Finite M] {C U B P₁ P₂ : Subgroup M}
    (hU : CFSG.QuasithinUnique.IsSylowTwoOf U C)
    (hB : C ⊓ Subgroup.normalizer (U : Set M) = B)
    (hcov : ∀ A : Subgroup M, A ≤ C → (B ⋖ A ↔ A = P₁ ∨ A = P₂))
    (hP₁ : P₁ ≤ C) (hP₂ : P₂ ≤ C) (h₁ : P₁ ≠ C) (h₂ : P₂ ≠ C) (hgen : P₁ ⊔ P₂ = C)
    (hcont : ∀ A : Subgroup M, U ≤ A → A ≤ C → A ≠ C → A ≤ P₁ ∨ A ≤ P₂)
    (hinv : ∀ α : MulAut C, (U.subgroupOf C).map α.toMonoidHom = U.subgroupOf C →
      (P₁.subgroupOf C).map α.toMonoidHom = P₁.subgroupOf C ∧
        (P₂.subgroupOf C).map α.toMonoidHom = P₂.subgroupOf C) :
    HasInvariantMaximalOvergroups C (U.subgroupOf C) := by
  obtain ⟨hc, hn₁, hn₂, hg, -⟩ := ambient_covers_data hU.1 hB hcov hP₁ hP₂ h₁ h₂ hgen
  have hU' : CFSG.QuasithinUnique.IsSylowTwoOf (U.subgroupOf C) ⊤ := isSylowTwoOf_subgroupOf_top hU
  have hB₁ : B ⋖ P₁ := (hcov P₁ hP₁).2 (Or.inl rfl)
  have hB₂ : B ⋖ P₂ := (hcov P₂ hP₂).2 (Or.inr rfl)
  have hlt₁ : P₁ < C := lt_of_le_of_ne hP₁ h₁
  have hlt₂ : P₂ < C := lt_of_le_of_ne hP₂ h₂
  have hmaxA : ∀ A : Subgroup M, U ≤ A → A ≤ C → (A ⋖ C ↔ A = P₁ ∨ A = P₂) := by
    intro A hUA hAC
    constructor
    · intro hA
      rcases hcont A hUA hAC hA.ne with h | h
      · left
        exact (h.eq_or_lt.resolve_right fun hlt => hA.2 hlt hlt₁)
      · right
        exact (h.eq_or_lt.resolve_right fun hlt => hA.2 hlt hlt₂)
    · rintro (rfl | rfl)
      · refine ⟨hlt₁, fun c hc hcC => ?_⟩
        rcases hcont c (hUA.trans hc.le) hcC.le hcC.ne with h | h
        · exact lt_irrefl _ (hc.trans_le h)
        · exact hB₂.2 hB₁.lt (hc.trans_le h)
      · refine ⟨hlt₂, fun c hc hcC => ?_⟩
        rcases hcont c (hUA.trans hc.le) hcC.le hcC.ne with h | h
        · exact hB₁.2 hB₂.lt (hc.trans_le h)
        · exact lt_irrefl _ (hc.trans_le h)
  refine ⟨P₁.subgroupOf C, P₂.subgroupOf C, ?_, ?_, hg,
    not_normal_of_covBy_normalizer hU' ((hc _).2 (Or.inl rfl)) hn₁,
    not_normal_of_covBy_normalizer hU' ((hc _).2 (Or.inr rfl)) hn₂, hinv⟩
  · intro hEq
    apply h₁
    have : P₁ = P₂ := by
      have := congrArg (Subgroup.map C.subtype) hEq
      rwa [Subgroup.map_subgroupOf_eq_of_le hP₁, Subgroup.map_subgroupOf_eq_of_le hP₂] at this
    rw [← hgen, ← this, sup_idem]
  · intro M' hUM'
    have hAC : M'.map C.subtype ≤ C := Subgroup.map_subtype_le M'
    have hAeq : M' = (M'.map C.subtype).subgroupOf C :=
      (Subgroup.comap_map_eq_self_of_injective C.subtype_injective M').symm
    have hUA : U ≤ M'.map C.subtype := by
      have := Subgroup.map_mono (f := C.subtype) hUM'
      rwa [Subgroup.map_subgroupOf_eq_of_le hU.1] at this
    have htop : M' ⋖ ⊤ ↔ M'.map C.subtype ⋖ C := by
      conv_lhs => rw [hAeq, ← Subgroup.subgroupOf_self C]
      exact subgroupOf_covBy_iff hAC le_rfl
    rw [htop, hmaxA _ hUA hAC]
    have key : ∀ P : Subgroup M, P ≤ C → (M'.map C.subtype = P ↔ M' = P.subgroupOf C) := by
      intro P hP
      constructor
      · rintro rfl; exact hAeq
      · rintro rfl; exact Subgroup.map_subgroupOf_eq_of_le hP
    rw [key _ hP₁, key _ hP₂]

end Ambient

end MaximalOvergroups

section Chevalley

open CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley

variable {τ : Tag} {K : Type} [Field K]

theorem rootSubgroup_le_posUnipotent_of_pos
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (hpos : 0 < height α) : rootSubgroup τ K α ≤ posUnipotent τ K :=
  le_iSup₂_of_le α ⟨hα, hpos⟩ le_rfl

theorem torusGroup_normalizes_rootSubgroup
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    torusGroup τ K ≤ Subgroup.normalizer (rootSubgroup τ K α : Set (ModGL τ K)) := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨⟨i, s⟩, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_normalizer_iff]
  intro g
  have h := map_conj_torusElt_rootSubgroup i s hα (R := K)
  constructor
  · intro hg
    rw [← h]
    exact ⟨g, hg, rfl⟩
  · intro hg
    rw [← h] at hg
    obtain ⟨g', hg', he⟩ := hg
    have : g' = g := by
      simpa [MulAut.conj_apply] using he
    rwa [← this]

theorem yUnit_eq_weylElt_mul
    (i : Fin τ.rank) (c : K) :
    yUnit τ K i c = weylElt τ K i 1 * xUnit τ K i (-c) * (weylElt τ K i 1)⁻¹ := by
  refine Units.ext ?_
  rw [coe_yUnit, Units.val_mul, Units.val_mul, coe_xUnit, weylElt_mul_xOp_mul_inv]
  congr 1
  simp

theorem adjointGroup_le_of_weylElt_mem
    {M : Subgroup (ModGL τ K)} (hU : posUnipotent τ K ≤ M)
    (hn : ∀ i : Fin τ.rank, weylElt τ K i 1 ∈ M) : adjointGroup τ K ≤ M := by
  refine (Subgroup.closure_le _).2 ?_
  rintro g ⟨i, c, hg | hg⟩
  · have : g = xUnit τ K i c := Units.ext hg
    rw [this]
    exact hU (xUnit_mem_posUnipotent i c)
  · have : g = yUnit τ K i c := Units.ext hg
    rw [this, yUnit_eq_weylElt_mul]
    exact mul_mem (mul_mem (hn i) (hU (xUnit_mem_posUnipotent i (-c)))) (inv_mem (hn i))

theorem reduced_word_extraction_of_posUnipotent
    (M : Subgroup (ModGL τ K))
    (hU : posUnipotent τ K ≤ M) :
    ∀ (ω : List (Fin τ.rank)), (coxeterSystem τ).IsReduced ω →
      ∀ h ∈ torusGroup τ K,
        h * canonicalRep (coxeterSystem τ) K ((coxeterSystem τ).wordProd ω) ∈ M →
        ∀ i ∈ ω, weylElt τ K i 1 ∈ M := by
  intro ω
  induction ω with
  | nil => intro _ _ _ _ i hi; exact absurd hi List.not_mem_nil
  | cons i ω ih =>
    intro hred h hh hz
    set w := (coxeterSystem τ).wordProd (i :: ω) with hwdef
    have hw' : w = simple τ i * (coxeterSystem τ).wordProd ω := (coxeterSystem τ).wordProd_cons i ω
    have hred' : (coxeterSystem τ).IsReduced ω := by
      have := hred.drop 1
      simpa using this
    have hlen : (coxeterSystem τ).length w =
        (coxeterSystem τ).length ((coxeterSystem τ).wordProd ω) + 1 := by
      rw [hred.eq, hred'.eq, List.length_cons]
    have hdesc : (coxeterSystem τ).IsLeftDescent w i := by
      rw [isLeftDescent_iff_length, hw', ← mul_assoc, simple_mul_simple_self, one_mul, ← hw', hlen]
    have hneg := (smul_single_mem_negRoots_iff w⁻¹ i).2
      ((coxeterSystem τ).isRightDescent_inv_iff.2 hdesc)
    set α := -(w⁻¹ • (Pi.single i 1 : Fin τ.rank → ℤ)) with hα
    have hαr : IsRoot τ α := IsRoot.neg hneg.1
    have hαp : 0 < height α := by rw [hα, height_neg]; linarith [hneg.2]
    have hwα : w • α = -Pi.single i 1 := by rw [hα, smul_neg, smul_inv_smul]
    have hY : rootSubgroup τ K (-Pi.single i 1) ≤ M := by
      intro y hy
      have hy' : h⁻¹ * y * h ∈ rootSubgroup τ K (-Pi.single i 1) := by
        have := (Subgroup.mem_normalizer_iff.1
          (torusGroup_normalizes_rootSubgroup (K := K) (isRoot_neg_single τ i) (inv_mem hh)) y).1 hy
        simpa only [inv_inv, SetLike.mem_coe] using this
      rw [← hwα, ← (canonical_weyl_root_transport τ K).2.1 w α hαr] at hy'
      obtain ⟨u, hu, hun⟩ := hy'
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hun
      have hu' : u ∈ M := hU (rootSubgroup_le_posUnipotent_of_pos hαr hαp hu)
      have hyz : y = (h * canonicalRep (coxeterSystem τ) K w) * u *
          (h * canonicalRep (coxeterSystem τ) K w)⁻¹ := by
        have h1 : h * (canonicalRep (coxeterSystem τ) K w * u *
            (canonicalRep (coxeterSystem τ) K w)⁻¹) * h⁻¹ = y := by
          rw [hun]; group
        rw [← h1]; group
      rw [hyz]
      exact mul_mem (mul_mem hz hu') (inv_mem hz)
    have hX : rootSubgroup τ K (Pi.single i 1) ≤ M :=
      le_trans (rootSubgroup_le_posUnipotent_of_pos (isRoot_single τ i)
        (by rw [height_single]; exact one_pos)) hU
    have hn : weylElt τ K i 1 ∈ M := by
      rw [weylElt_eq_xUnit_mul]
      refine mul_mem (mul_mem ?_ ?_) ?_
      · rw [← pinnedX_single]; exact hX (Subgroup.subset_closure ⟨_, rfl⟩)
      · rw [← pinnedX_neg_single]; exact hY (Subgroup.subset_closure ⟨_, rfl⟩)
      · rw [← pinnedX_single]; exact hX (Subgroup.subset_closure ⟨_, rfl⟩)
    have hrep : weylElt τ K i 1 * canonicalRep (coxeterSystem τ) K
        ((coxeterSystem τ).wordProd ω) = canonicalRep (coxeterSystem τ) K w := by
      rw [hw']
      exact weylElt_mul_canonicalRep_of_length_eq (by rw [← hw', hlen])
    have hz' : ((weylElt τ K i 1)⁻¹ * h * weylElt τ K i 1) *
        canonicalRep (coxeterSystem τ) K ((coxeterSystem τ).wordProd ω) ∈ M := by
      have e : ((weylElt τ K i 1)⁻¹ * h * weylElt τ K i 1) *
          canonicalRep (coxeterSystem τ) K ((coxeterSystem τ).wordProd ω) =
          (weylElt τ K i 1)⁻¹ * (h * canonicalRep (coxeterSystem τ) K w) := by
        rw [← hrep]; group
      rw [e]
      exact mul_mem (inv_mem hn) hz
    have hh' : (weylElt τ K i 1)⁻¹ * h * weylElt τ K i 1 ∈ torusGroup τ K := by
      have := (Subgroup.mem_normalizer_iff.1 (inv_mem (weylElt_mem_normalizer_torus τ K i 1)) h).1
        hh
      rw [inv_inv] at this
      exact this
    intro j hj
    rcases List.mem_cons.1 hj with rfl | hj
    · exact hn
    · exact ih hred' _ hh' hz' j hj

theorem le_parabolicSubgroup_of_posUnipotent_le
    {M : Subgroup (ModGL τ K)}
    (hMC : M ≤ adjointGroup τ K) (hU : posUnipotent τ K ≤ M) :
    M ≤ parabolicSubgroup τ K {i | weylElt τ K i 1 ∈ M} := by
  intro g hg
  have hg' : g ∈ ⋃ w, bruhatCell τ K w := by
    rw [← adjointGroup_eq_iUnion_bruhatCell]
    exact hMC hg
  obtain ⟨w, hw⟩ := Set.mem_iUnion.1 hg'
  obtain ⟨ω, hω, rfl⟩ := (coxeterSystem τ).exists_isReduced w
  obtain ⟨b, hb, b', hb', hgb⟩ := mem_bruhatCell.1 hw
  obtain ⟨u₁, hu₁, h₁, hh₁, rfl⟩ : b ∈ (posUnipotent τ K : Set (ModGL τ K)) *
      (torusGroup τ K : Set (ModGL τ K)) := by
    rw [← (triangular_borel_structure.{0, 0} τ K).2.2.2.2.2.1]
    exact hb
  obtain ⟨h₂, hh₂, u₂, hu₂, rfl⟩ : b' ∈ (torusGroup τ K : Set (ModGL τ K)) *
      (posUnipotent τ K : Set (ModGL τ K)) := by
    rw [← (triangular_borel_structure.{0, 0} τ K).2.2.2.2.1]
    exact hb'
  have hnorm : canonicalRep (coxeterSystem τ) K ((coxeterSystem τ).wordProd ω) ∈
      Subgroup.normalizer (torusGroup τ K : Set (ModGL τ K)) :=
    (canonical_weyl_root_transport τ K).2.2 _
  have hh : canonicalRep (coxeterSystem τ) K ((coxeterSystem τ).wordProd ω) * h₂ *
      (canonicalRep (coxeterSystem τ) K ((coxeterSystem τ).wordProd ω))⁻¹ ∈ torusGroup τ K := by
    have := (Subgroup.mem_normalizer_iff.1 hnorm h₂).1 hh₂
    simpa only [SetLike.mem_coe] using this
  have hz : (h₁ * (canonicalRep (coxeterSystem τ) K ((coxeterSystem τ).wordProd ω) * h₂ *
      (canonicalRep (coxeterSystem τ) K ((coxeterSystem τ).wordProd ω))⁻¹)) *
      canonicalRep (coxeterSystem τ) K ((coxeterSystem τ).wordProd ω) ∈ M := by
    have e : (h₁ * (canonicalRep (coxeterSystem τ) K ((coxeterSystem τ).wordProd ω) * h₂ *
        (canonicalRep (coxeterSystem τ) K ((coxeterSystem τ).wordProd ω))⁻¹)) *
        canonicalRep (coxeterSystem τ) K ((coxeterSystem τ).wordProd ω) = u₁⁻¹ * g * u₂⁻¹ := by
      rw [← hgb]; group
    rw [e]
    exact mul_mem (mul_mem (inv_mem (hU hu₁)) hg) (inv_mem (hU hu₂))
  have hletters := reduced_word_extraction_of_posUnipotent M hU ω hω _ (mul_mem hh₁ hh) hz
  have hwJ := wordProd_mem_parabolicWeylGroup (J := {i | weylElt τ K i 1 ∈ M}) hletters
  exact bruhatCell_subset_parabolicSubgroup hwJ hw

theorem chevalley_positive_root_overgroup_parabolic_containment
    {M : Subgroup (ModGL τ K)}
    (hMC : M ≤ adjointGroup τ K) (hU : posUnipotent τ K ≤ M) :
    M ≤ parabolicSubgroup τ K {i | weylElt τ K i 1 ∈ M} ∧
    ({i | weylElt τ K i 1 ∈ M} = Set.univ ↔ M = adjointGroup τ K) ∧
    (M ≠ adjointGroup τ K → ∃ J : Set (Fin τ.rank), J ≠ Set.univ ∧ M ≤ parabolicSubgroup τ K J ∧
      parabolicSubgroup τ K J ≠ adjointGroup τ K) := by
  have hle := le_parabolicSubgroup_of_posUnipotent_le hMC hU
  have hiff : {i | weylElt τ K i 1 ∈ M} = Set.univ ↔ M = adjointGroup τ K := by
    constructor
    · intro h
      refine le_antisymm hMC (adjointGroup_le_of_weylElt_mem hU fun i => ?_)
      have : i ∈ {i | weylElt τ K i 1 ∈ M} := by rw [h]; trivial
      exact this
    · rintro rfl
      exact Set.eq_univ_of_forall fun i => weylElt_mem_adjointGroup i 1
  refine ⟨hle, hiff, fun hne => ⟨{i | weylElt τ K i 1 ∈ M}, fun h => hne (hiff.1 h), hle,
    fun hP => ?_⟩⟩
  have h1 : parabolicSubgroup τ K Set.univ ≤ parabolicSubgroup τ K {i | weylElt τ K i 1 ∈ M} := by
    rw [(standard_parabolic_cells τ K).2.2.2.2.2.1, hP]
  have h2 : Set.univ ⊆ {i | weylElt τ K i 1 ∈ M} :=
    ((standard_parabolic_cells τ K).2.2.2.1 _ _).1 h1
  exact hne (hiff.1 (Set.eq_univ_of_univ_subset h2))

theorem unique_Chevalley_positive_Sylow
    (p : ℕ) [Fact p.Prime] [Finite K] [CharP K p] :
    IsSylowOf p (posUnipotent τ K) (adjointGroup τ K) ∧
      Nat.card (posUnipotent τ K) =
        Nat.card K ^ {α : Fin τ.rank → ℤ | IsRoot τ α ∧ 0 < height α}.ncard := by
  have := finite_modGL (τ := τ) (K := K)
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem τ).length
  refine ⟨?_, card_posUnipotent⟩
  obtain ⟨PU, hPU⟩ := (exceptional_ordinary_Sylow_opposition τ K p w₀ hw₀).1
  refine ⟨PU, ?_⟩
  rw [hPU, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 posUnipotent_le_adjointGroup]

end Chevalley

end CFSG.QuasithinUnique.Setup.X6
