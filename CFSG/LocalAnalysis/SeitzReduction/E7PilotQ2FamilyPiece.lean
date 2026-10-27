module

public import CFSG.LocalAnalysis.SeitzReduction.E7PilotQ2FamilyFrame
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotQ2SwapMain
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotQ2PieceMain
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotQ2FamilyParam

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E7Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.Quasithin (perfectCore perfectCore_le perfectCore_mono le_perfectCore_of_perfect)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)

local instance e7PilotQ2FamilyPieceNeZeroRank : NeZero Tag.E7.rank := ⟨by decide⟩

section General

variable {G : Type} [Group G]

theorem mem_normalizer_map_conj_of_commute {H : Subgroup G} {c g : G}
    (hc : c ∈ normalizer (H : Set G)) (hcg : Commute c g) :
    c ∈ normalizer ((H.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff] at hc ⊢
  have hmem : ∀ t, t ∈ H.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * t * g ∈ H := by
    intro t
    constructor
    · rintro ⟨u, hu, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rwa [show g⁻¹ * (g * u * g⁻¹) * g = u by group]
    · intro ht
      refine ⟨g⁻¹ * t * g, ht, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  intro s
  rw [hmem, hmem, hc (g⁻¹ * s * g)]
  have h : g⁻¹ * (c * s * c⁻¹) * g = c * (g⁻¹ * s * g) * c⁻¹ :=
    calc g⁻¹ * (c * s * c⁻¹) * g = (g⁻¹ * c) * s * (c⁻¹ * g) := by group
      _ = (c * g⁻¹) * s * (g * c⁻¹) := by rw [← hcg.inv_right.eq, hcg.inv_left.eq]
      _ = c * (g⁻¹ * s * g) * c⁻¹ := by group
  rw [h]

theorem mem_normalizer_perfectCore_of_mem {W : Subgroup G} {c : G} (hc : c ∈ W) :
    c ∈ normalizer (perfectCore W : Set G) :=
  CFSG.Quasithin.normalizer_le_normalizer_perfectCore W (le_normalizer hc)

end General

section Pieces


variable {K : Type} [Field K]

theorem map_leviPiece_eq_rootSpan {N : E7Neighbour} {J : Finset (Fin (Tag.rank .E7))}
    (hJ : J ⊆ N.nodes) :
    (leviPiece K N J).map ((adjointGroup .E7 K).subtype.comp (N.levi K).subtype) =
      rootSpan .E7 K (amalgamRoots J) := by
  have hle : rootSpan .E7 K (amalgamRoots J) ≤ (N.levi K).map (adjointGroup .E7 K).subtype := by
    rw [← map_subtype_levi_adjDatumE7 J]
    exact map_mono (levi_le_neighbourLevi hJ)
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro hg
    obtain ⟨y, hy, rfl⟩ := hle hg
    exact ⟨⟨y, hy⟩, hg, rfl⟩

theorem rootSpan_amalgamRoots_eq_iSup (J : Finset (Fin (Tag.rank .E7))) :
    rootSpan .E7 K (amalgamRoots J) = ⨆ j ∈ J, rootSpan .E7 K (amalgamRoots {j}) := by
  refine le_antisymm (iSup₂_le fun γ hγ => ?_) (iSup₂_le fun j hj => ?_)
  · obtain ⟨j, hj, hγj⟩ := hγ
    refine le_trans ?_ (le_iSup₂_of_le (f := fun j (_ : j ∈ J) =>
      rootSpan .E7 K (amalgamRoots {j})) j hj le_rfl)
    exact le_iSup₂_of_le (f := fun α (_ : α ∈ amalgamRoots {j}) => rootSubgroup .E7 K α) γ
      ⟨j, Finset.mem_singleton_self j, hγj⟩ le_rfl
  · exact rootSpan_mono_E7 (amalgamRoots_mono (Finset.singleton_subset_iff.2 hj))

theorem leviPiece_eq_iSup {N : E7Neighbour} {J : Finset (Fin (Tag.rank .E7))}
    (hJ : J ⊆ N.nodes) : leviPiece K N J = ⨆ j ∈ J, leviPiece K N {j} := by
  have hinj : Function.Injective ((adjointGroup .E7 K).subtype.comp (N.levi K).subtype) :=
    (adjointGroup .E7 K).subtype_injective.comp (N.levi K).subtype_injective
  apply Subgroup.map_injective hinj
  rw [map_leviPiece_eq_rootSpan hJ, Subgroup.map_iSup, rootSpan_amalgamRoots_eq_iSup]
  refine iSup_congr fun j => ?_
  rw [Subgroup.map_iSup]
  exact iSup_congr fun hj =>
    (map_leviPiece_eq_rootSpan (Finset.singleton_subset_iff.2 (hJ hj))).symm

end Pieces

section Canonical


variable {G : Type} [Group G] {L : Subgroup G} {k : Type} [Field k]

@[expose] noncomputable def frameTorusG (e : L ≃* adjointGroup .E7 k)
    (A : Subgroup (adjointGroup .E7 k)) (f : PairFrame) (m : Fin 6) : Subgroup G :=
  ((A.map (MulAut.conj (wordRep k (f.word m))).toMonoidHom).map e.symm.toMonoidHom).map L.subtype

theorem frameTorusG_coverIdx (e : L ≃* adjointGroup .E7 k) (A : Subgroup (adjointGroup .E7 k))
    (f : PairFrame) (i : Fin 2) :
    frameTorusG e A f (PairFrame.coverIdx i) = nonsplitNeighbourE7G e A (f.nbr i) := by
  rw [frameTorusG, f.word_coverIdx]
  rfl

theorem conj_wordRep_mem_levi_frame {a : adjointGroup .E7 k}
    (ha : (a : ModGL .E7 k) ∈ EPilot.highRootSL2 .E7 k) (f : PairFrame) {i : Fin 2} {m : Fin 6}
    (hm : m ≠ PairFrame.coverIdx i) :
    wordRep k (f.word m) * a * (wordRep k (f.word m))⁻¹ ∈ (f.nbr i).levi k := by
  apply mem_levi_of_coe_mem
  rw [map_subtype_levi]
  have h1 := conj_wordElt_mem_rootSL2_E7 (f.word m) ha
  rw [f.word_smul_highRoot] at h1
  have h0 : iform (f.nbr i).root (f.root m) = 0 := by
    rw [← f.root_coverIdx, f.iform_root_root, ite_eq_right (Ne.symm hm)]
  have h0' : iform (f.nbr i).root (-f.root m) = 0 := by rw [iform_neg_right_E7, h0, neg_zero]
  have hle : rootSubgroup .E7 k (f.root m) ⊔ rootSubgroup .E7 k (-f.root m) ≤
      rootSpan .E7 k (orthRoots (f.nbr i).root) :=
    sup_le
      (le_iSup₂_of_le (f := fun α (_ : α ∈ orthRoots (f.nbr i).root) => rootSubgroup .E7 k α) _
        ⟨f.isRoot_root m, h0⟩ le_rfl)
      (le_iSup₂_of_le (f := fun α (_ : α ∈ orthRoots (f.nbr i).root) => rootSubgroup .E7 k α) _
        ⟨IsRoot.neg (f.isRoot_root m), h0'⟩ le_rfl)
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_wordRep]
  exact hle h1

theorem map_leviPiece_node_eq_perfectCore_iInf [Finite G] {K : Type} [Field K] [Finite K]
    [CharP K 2] {σ : K ≃+* K} (hk : Nat.card (fixSubfield σ) = 2) (hK : Nat.card K = 2 ^ 2)
    (e : L ≃* adjointGroup .E7 (fixSubfield σ)) {A : Subgroup (adjointGroup .E7 (fixSubfield σ))}
    (hAJ : A ≤ posJE7 (fixSubfield σ)) (hA : Nat.card A = Nat.card (fixSubfield σ) + 1)
    (f : PairFrame) (i : Fin 2)
    (h : TwoFieldParam σ e (f.nbr i)
      (centralizerPerfectCore (nonsplitNeighbourE7G e A (f.nbr i)))) :
    ((leviPiece K (f.nbr i) {f.node}).map h.Φ.toMonoidHom).map
        (centralizerPerfectCore (nonsplitNeighbourE7G e A (f.nbr i))).subtype =
      perfectCore (⨅ m : Fin 6, centralizer (frameTorusG e A f m : Set G)) := by
  have : Finite (fixSubfield σ) := Nat.finite_of_card_ne_zero (by rw [hk]; norm_num)
  have : Finite (ModGL .E7 K) := finite_modGL
  have hA3 : Nat.card A = 3 := by rw [hA, hk]
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hcyc : IsCyclic A := isCyclic_of_prime_card hA3
  obtain ⟨⟨a, haA⟩, hgen⟩ := IsCyclic.exists_generator (α := A)
  have hAa : A = Subgroup.zpowers a := by
    refine le_antisymm (fun y hy => ?_) (Subgroup.zpowers_le.2 haA)
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 (hgen ⟨y, hy⟩)
    exact Subgroup.mem_zpowers_iff.2 ⟨n, by simpa using congrArg Subtype.val hn⟩
  have hxJ : (a : ModGL .E7 (fixSubfield σ)) ∈ EPilot.highRootSL2 .E7 (fixSubfield σ) := hAJ haA
  have hx : orderOf (a : ModGL .E7 (fixSubfield σ)) = 3 := by
    rw [Subgroup.orderOf_coe, ← Nat.card_zpowers, ← hAa, hA3]
  set y : Fin 6 → adjointGroup .E7 (fixSubfield σ) :=
    fun m => wordRep _ (f.word m) * a * (wordRep _ (f.word m))⁻¹ with hydef
  have hy : ∀ m, ((y m : adjointGroup .E7 (fixSubfield σ)) : ModGL .E7 (fixSubfield σ)) =
      wordElt _ (f.word m) * (a : ModGL .E7 (fixSubfield σ)) * (wordElt _ (f.word m))⁻¹ := by
    intro m
    simp only [hydef, Subgroup.coe_mul, Subgroup.coe_inv, coe_wordRep]
  have hXm : ∀ m, centralizer (frameTorusG e A f m : Set G) =
      centralizer ({((e.symm (y m) : L) : G)} : Set G) := by
    intro m
    rw [frameTorusG, hAa, MonoidHom.map_zpowers]
    exact E8Pilot.centralizer_map_map_zpowers e _
  have hyN : ∀ m, m ≠ PairFrame.coverIdx i → y m ∈ (f.nbr i).levi (fixSubfield σ) :=
    fun m hm => conj_wordRep_mem_levi_frame hxJ f hm
  set T : Subgroup (ModGL .E7 K) := ((f.nbr i).levi K).map (adjointGroup .E7 K).subtype ⊓
    ⨅ (m : Fin 6) (_ : m ≠ PairFrame.coverIdx i), centralizer
      ({baseChangeGL (fixSubfield σ).subtype (wordElt (fixSubfield σ) (f.word m) *
        (a : ModGL .E7 (fixSubfield σ)) * (wordElt (fixSubfield σ) (f.word m))⁻¹)} :
          Set (ModGL .E7 K)) with hT
  have hTeq := perfectCore_levi_inf_frame_eq hk hK (fixSubfield σ).subtype hxJ hx f i
  set ψ : (f.nbr i).levi K →* ModGL .E7 K :=
    (adjointGroup .E7 K).subtype.comp ((f.nbr i).levi K).subtype with hψ
  have hψinj : Function.Injective ψ :=
    (adjointGroup .E7 K).subtype_injective.comp ((f.nbr i).levi K).subtype_injective
  have hψrange : ψ.range = ((f.nbr i).levi K).map (adjointGroup .E7 K).subtype := by
    rw [hψ, MonoidHom.range_comp, Subgroup.range_subtype]
  set S : Subgroup ((f.nbr i).levi K) := T.comap ψ with hS
  have hSmap : S.map ψ = T := by
    rw [hS, Subgroup.map_comap_eq, hψrange]
    exact inf_of_le_right inf_le_left
  have hScore : perfectCore S = leviPiece K (f.nbr i) {f.node} :=
    E8Pilot.perfectCore_eq_of_map_eq hψinj (by
      rw [hSmap, map_leviPiece_eq_rootSpan (Finset.singleton_subset_iff.2 (f.node_mem_nodes i))]
      exact hTeq)
  set F : (f.nbr i).levi K →* G :=
    (centralizerPerfectCore (nonsplitNeighbourE7G e A (f.nbr i))).subtype.comp h.Φ.toMonoidHom
    with hF
  have hFinj : Function.Injective F := Subtype.val_injective.comp h.Φ.injective
  set z : ∀ m, m ≠ PairFrame.coverIdx i → (f.nbr i).levi K :=
    fun m hm => leviInclusion σ (f.nbr i) ⟨y m, hyN m hm⟩ with hzdef
  have hFz : ∀ m hm, F (z m hm) = ((e.symm (y m) : L) : G) :=
    fun m hm => h.fix ⟨y m, hyN m hm⟩
  have hψz : ∀ m hm, ψ (z m hm) = baseChangeGL (fixSubfield σ).subtype
      (wordElt _ (f.word m) * (a : ModGL .E7 (fixSubfield σ)) * (wordElt _ (f.word m))⁻¹) := by
    intro m hm
    rw [← hy m]
    rfl
  have hEW : centralizerPerfectCore (nonsplitNeighbourE7G e A (f.nbr i)) ⊓
      ⨅ (m : Fin 6) (_ : m ≠ PairFrame.coverIdx i), centralizer (frameTorusG e A f m : Set G) =
        S.map F := by
    ext g
    constructor
    · rintro ⟨hgE, hgW⟩
      have hgf : F (h.Φ.symm ⟨g, hgE⟩) = g := by simp [hF]
      refine ⟨h.Φ.symm ⟨g, hgE⟩, ?_, hgf⟩
      refine Subgroup.mem_comap.2 (mem_inf.2 ⟨⟨_, (h.Φ.symm ⟨g, hgE⟩).2, rfl⟩, ?_⟩)
      refine Subgroup.mem_iInf.2 fun m => Subgroup.mem_iInf.2 fun hm => ?_
      have hgm : g ∈ centralizer (frameTorusG e A f m : Set G) :=
        Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hgW m) hm
      rw [hXm m, mem_centralizer_singleton_iff, ← hFz m hm] at hgm
      rw [← hgf, ← map_mul, ← map_mul] at hgm
      have hcomm := hFinj hgm
      rw [mem_centralizer_singleton_iff, ← hψz m hm, ← map_mul, ← map_mul, hcomm]
    · rintro ⟨u, hu, rfl⟩
      refine mem_inf.2 ⟨(h.Φ u).2, ?_⟩
      refine Subgroup.mem_iInf.2 fun m => Subgroup.mem_iInf.2 fun hm => ?_
      have hTm := Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1
        (mem_inf.1 (Subgroup.mem_comap.1 hu)).2 m) hm
      rw [mem_centralizer_singleton_iff, ← hψz m hm, ← map_mul, ← map_mul] at hTm
      have hcomm := hψinj hTm
      rw [hXm m, mem_centralizer_singleton_iff, ← hFz m hm, ← map_mul, ← map_mul, hcomm]
  have hsplit : ⨅ m : Fin 6, centralizer (frameTorusG e A f m : Set G) =
      centralizer (nonsplitNeighbourE7G e A (f.nbr i) : Set G) ⊓
        ⨅ (m : Fin 6) (_ : m ≠ PairFrame.coverIdx i),
          centralizer (frameTorusG e A f m : Set G) := by
    rw [iInf_split_single _ (PairFrame.coverIdx i), frameTorusG_coverIdx]
  rw [hsplit, E8Pilot.perfectCore_inf_eq_perfectCore_perfectCore_inf,
    ← F4Pilot.centralizerPerfectCore_def, hEW, ← CFSG.Quasithin.map_perfectCore, hScore,
    Subgroup.map_map]

theorem mem_normalizer_perfectCore_iInf_frameTorusG (e : L ≃* adjointGroup .E7 k)
    (A : Subgroup (adjointGroup .E7 k)) (f : PairFrame) {c : G}
    (hc : c ∈ centralizer (L : Set G)) :
    c ∈ normalizer
      (perfectCore (⨅ m : Fin 6, centralizer (frameTorusG e A f m : Set G)) : Set G) :=
  mem_normalizer_perfectCore_of_mem
    (Subgroup.mem_iInf.2 fun _ => centralizer_le (map_subtype_le _) hc)

theorem map_leviPiece_node_eq_of_frame [Finite G] {K : Type} [Field K] [Finite K] [CharP K 2]
    {σ : K ≃+* K} (hk : Nat.card (fixSubfield σ) = 2) (hK : Nat.card K = 2 ^ 2)
    (e : L ≃* adjointGroup .E7 (fixSubfield σ)) {A : Subgroup (adjointGroup .E7 (fixSubfield σ))}
    (hAJ : A ≤ posJE7 (fixSubfield σ)) (hA : Nat.card A = Nat.card (fixSubfield σ) + 1)
    (f : PairFrame)
    (h₀ : TwoFieldParam σ e (f.nbr 0)
      (centralizerPerfectCore (nonsplitNeighbourE7G e A (f.nbr 0))))
    (h₁ : TwoFieldParam σ e (f.nbr 1)
      (centralizerPerfectCore (nonsplitNeighbourE7G e A (f.nbr 1)))) :
    ((leviPiece K (f.nbr 0) {f.node}).map h₀.Φ.toMonoidHom).map
        (centralizerPerfectCore (nonsplitNeighbourE7G e A (f.nbr 0))).subtype =
      ((leviPiece K (f.nbr 1) {f.node}).map h₁.Φ.toMonoidHom).map
        (centralizerPerfectCore (nonsplitNeighbourE7G e A (f.nbr 1))).subtype := by
  rw [map_leviPiece_node_eq_perfectCore_iInf hk hK e hAJ hA f 0 h₀,
    map_leviPiece_node_eq_perfectCore_iInf hk hK e hAJ hA f 1 h₁]

theorem mem_normalizer_map_leviPiece_node [Finite G] {K : Type} [Field K] [Finite K] [CharP K 2]
    {σ : K ≃+* K} (hk : Nat.card (fixSubfield σ) = 2) (hK : Nat.card K = 2 ^ 2)
    (e : L ≃* adjointGroup .E7 (fixSubfield σ)) {A : Subgroup (adjointGroup .E7 (fixSubfield σ))}
    (hAJ : A ≤ posJE7 (fixSubfield σ)) (hA : Nat.card A = Nat.card (fixSubfield σ) + 1)
    (f : PairFrame) (i : Fin 2)
    (h : TwoFieldParam σ e (f.nbr i)
      (centralizerPerfectCore (nonsplitNeighbourE7G e A (f.nbr i))))
    {c : G} (hc : c ∈ centralizer (L : Set G)) :
    c ∈ normalizer ((((leviPiece K (f.nbr i) {f.node}).map h.Φ.toMonoidHom).map
      (centralizerPerfectCore (nonsplitNeighbourE7G e A (f.nbr i))).subtype : Subgroup G) :
        Set G) := by
  rw [map_leviPiece_node_eq_perfectCore_iInf hk hK e hAJ hA f i h]
  exact mem_normalizer_perfectCore_iInf_frameTorusG e A f hc

end Canonical

section WeylTransfer


theorem map_conj_leviPiece_of_word {F : Type} [Field F] {N : E7Neighbour}
    {a b : Fin (Tag.rank .E7)} (ha : a ∈ N.nodes) (hb : b ∈ N.nodes)
    (ω : List (Fin (Tag.rank .E7)))
    (hω : (coxeterSystem .E7).wordProd ω • (Pi.single a 1 : Fin (Tag.rank .E7) → ℤ) =
      Pi.single b 1)
    (y : N.levi F) (hy : ((y : adjointGroup .E7 F) : ModGL .E7 F) = wordElt F ω) :
    (leviPiece F N {a}).map (MulAut.conj y).toMonoidHom = leviPiece F N {b} := by
  have hinj : Function.Injective ((adjointGroup .E7 F).subtype.comp (N.levi F).subtype) :=
    (adjointGroup .E7 F).subtype_injective.comp (N.levi F).subtype_injective
  apply Subgroup.map_injective hinj
  rw [Subgroup.map_map, map_leviPiece_eq_rootSpan (Finset.singleton_subset_iff.2 hb)]
  have hcomp : ((adjointGroup .E7 F).subtype.comp (N.levi F).subtype).comp
      (MulAut.conj y).toMonoidHom = (MulAut.conj (wordElt F ω)).toMonoidHom.comp
        ((adjointGroup .E7 F).subtype.comp (N.levi F).subtype) := by
    refine MonoidHom.ext fun x => ?_
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, hy]
  rw [hcomp, ← Subgroup.map_map, map_leviPiece_eq_rootSpan (Finset.singleton_subset_iff.2 ha),
    rootSpan_amalgamRoots_singleton, rootSpan_amalgamRoots_singleton, Subgroup.map_sup,
    map_conj_prod_weylElt_rootSubgroup F ω (isRoot_single _ a),
    map_conj_prod_weylElt_rootSubgroup F ω (isRoot_neg_single _ a), smul_neg, hω]

variable {K : Type} [Field K] [CharP K 2] {σ : K ≃+* K} {G : Type} [Group G] {L : Subgroup G}
  {e : L ≃* adjointGroup .E7 (fixSubfield σ)}

theorem TwoFieldParam.mem_normalizer_map_leviPiece_of_word {N : E7Neighbour} {E : Subgroup G}
    (h : TwoFieldParam σ e N E) {a b : Fin (Tag.rank .E7)} (ha : a ∈ N.nodes) (hb : b ∈ N.nodes)
    (ω : List (Fin (Tag.rank .E7)))
    (hω : (coxeterSystem .E7).wordProd ω • (Pi.single a 1 : Fin (Tag.rank .E7) → ℤ) =
      Pi.single b 1)
    (hωN : wordElt (fixSubfield σ) ω ∈ rootSpan .E7 (fixSubfield σ) (orthRoots N.root))
    {c : G} (hc : c ∈ centralizer (L : Set G))
    (hca : c ∈ normalizer ((((leviPiece K N {a}).map h.Φ.toMonoidHom).map E.subtype :
      Subgroup G) : Set G)) :
    c ∈ normalizer ((((leviPiece K N {b}).map h.Φ.toMonoidHom).map E.subtype :
      Subgroup G) : Set G) := by
  set y : N.levi (fixSubfield σ) :=
    ⟨⟨wordElt (fixSubfield σ) ω, wordElt_mem_adjointGroup ω⟩, mem_subgroupOf.2 hωN⟩ with hydef
  set g : G := ((e.symm (y : adjointGroup .E7 (fixSubfield σ)) : L) : G) with hg
  have hyK : (((leviInclusion σ N y : N.levi K) : adjointGroup .E7 K) : ModGL .E7 K) =
      wordElt K ω := by
    rw [coe_leviInclusion]
    exact baseChangeGL_wordElt _ ω
  have hpiece := map_conj_leviPiece_of_word ha hb ω hω (leviInclusion σ N y) hyK
  have heq : ((leviPiece K N {b}).map h.Φ.toMonoidHom).map E.subtype =
      (((leviPiece K N {a}).map h.Φ.toMonoidHom).map E.subtype).map
        (MulAut.conj g).toMonoidHom := by
    rw [← hpiece, Subgroup.map_map, Subgroup.map_map, Subgroup.map_map, Subgroup.map_map]
    congr 1
    refine MonoidHom.ext fun x => ?_
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      Subgroup.coe_subtype]
    exact h.map_conj_of_mem y x
  rw [heq]
  exact mem_normalizer_map_conj_of_commute hca (mem_centralizer_iff.1 hc g (e.symm _).2).symm

theorem wordProd_pair_single_E7 {a b : Fin (Tag.rank .E7)}
    (hab : (a, b) = (2, 3) ∨ (a, b) = (3, 1) ∨ (a, b) = (3, 4) ∨ (a, b) = (4, 5) ∨
      (a, b) = (5, 6) ∨ (a, b) = (2, 0)) :
    (coxeterSystem .E7).wordProd [a, b] • (Pi.single a 1 : Fin (Tag.rank .E7) → ℤ) =
      Pi.single b 1 := by
  simp only [CoxeterSystem.wordProd_cons, CoxeterSystem.wordProd_nil, mul_one, mul_smul,
    simple_smul]
  rcases hab with h | h | h | h | h | h <;> simp only [Prod.mk.injEq] at h <;>
    obtain ⟨rfl, rfl⟩ := h <;> exact List.ofFn_injective (by decide +kernel)

theorem TwoFieldParam.mem_normalizer_map_leviPiece_of_pair {N : E7Neighbour} {E : Subgroup G}
    (h : TwoFieldParam σ e N E) {a b : Fin (Tag.rank .E7)} (ha : a ∈ N.nodes) (hb : b ∈ N.nodes)
    (hab : (a, b) = (2, 3) ∨ (a, b) = (3, 1) ∨ (a, b) = (3, 4) ∨ (a, b) = (4, 5) ∨
      (a, b) = (5, 6) ∨ (a, b) = (2, 0))
    {c : G} (hc : c ∈ centralizer (L : Set G))
    (hca : c ∈ normalizer ((((leviPiece K N {a}).map h.Φ.toMonoidHom).map E.subtype :
      Subgroup G) : Set G)) :
    c ∈ normalizer ((((leviPiece K N {b}).map h.Φ.toMonoidHom).map E.subtype :
      Subgroup G) : Set G) := by
  refine h.mem_normalizer_map_leviPiece_of_word ha hb [a, b] (wordProd_pair_single_E7 hab)
    (wordElt_mem_rootSpan_of_nodes fun i hi => ?_) hc hca
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl
  exacts [ha, hb]

end WeylTransfer


section AllNodes


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2] {σ : K ≃+* K}

theorem TwoFieldParam.mem_normalizer_map_leviPiece_single (hk : Nat.card (fixSubfield σ) = 2)
    (hK : Nat.card K = 2 ^ 2) {e : L ≃* adjointGroup .E7 (fixSubfield σ)}
    {A : Subgroup (adjointGroup .E7 (fixSubfield σ))} (hAJ : A ≤ posJE7 (fixSubfield σ))
    (hA : Nat.card A = Nat.card (fixSubfield σ) + 1) {N : E7Neighbour}
    (h : TwoFieldParam σ e N (centralizerPerfectCore (nonsplitNeighbourE7G e A N)))
    {j : Fin (Tag.rank .E7)} (hj : j ∈ N.nodes) {c : G} (hc : c ∈ centralizer (L : Set G)) :
    c ∈ normalizer ((((leviPiece K N {j}).map h.Φ.toMonoidHom).map
      (centralizerPerfectCore (nonsplitNeighbourE7G e A N)).subtype : Subgroup G) : Set G) := by
  cases N
  · have h2 : c ∈ normalizer ((((leviPiece K .high {2}).map h.Φ.toMonoidHom).map
        (centralizerPerfectCore (nonsplitNeighbourE7G e A .high)).subtype : Subgroup G) :
          Set G) := mem_normalizer_map_leviPiece_node hk hK e hAJ hA .hs 0 h hc
    have h5 : c ∈ normalizer ((((leviPiece K .high {5}).map h.Φ.toMonoidHom).map
        (centralizerPerfectCore (nonsplitNeighbourE7G e A .high)).subtype : Subgroup G) :
          Set G) := mem_normalizer_map_leviPiece_node hk hK e hAJ hA .hf 0 h hc
    have h3 := h.mem_normalizer_map_leviPiece_of_pair (by decide) (by decide) (Or.inl rfl) hc h2
    have h1 := h.mem_normalizer_map_leviPiece_of_pair (by decide) (by decide)
      (Or.inr (Or.inl rfl)) hc h3
    have h4 := h.mem_normalizer_map_leviPiece_of_pair (by decide) (by decide)
      (Or.inr (Or.inr (Or.inl rfl))) hc h3
    have h6 := h.mem_normalizer_map_leviPiece_of_pair (by decide) (by decide)
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) hc h5
    simp only [E7Neighbour.nodes, Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [h1, h2, h3, h4, h5, h6]
  · have h2 : c ∈ normalizer ((((leviPiece K .seven {2}).map h.Φ.toMonoidHom).map
        (centralizerPerfectCore (nonsplitNeighbourE7G e A .seven)).subtype : Subgroup G) :
          Set G) := mem_normalizer_map_leviPiece_node hk hK e hAJ hA .hs 1 h hc
    have h0 : c ∈ normalizer ((((leviPiece K .seven {0}).map h.Φ.toMonoidHom).map
        (centralizerPerfectCore (nonsplitNeighbourE7G e A .seven)).subtype : Subgroup G) :
          Set G) := mem_normalizer_map_leviPiece_node hk hK e hAJ hA .sf 0 h hc
    have h3 := h.mem_normalizer_map_leviPiece_of_pair (by decide) (by decide) (Or.inl rfl) hc h2
    have h1 := h.mem_normalizer_map_leviPiece_of_pair (by decide) (by decide)
      (Or.inr (Or.inl rfl)) hc h3
    have h4 := h.mem_normalizer_map_leviPiece_of_pair (by decide) (by decide)
      (Or.inr (Or.inr (Or.inl rfl))) hc h3
    simp only [E7Neighbour.nodes, Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl
    exacts [h0, h1, h2, h3, h4]
  · have h5 : c ∈ normalizer ((((leviPiece K .four {5}).map h.Φ.toMonoidHom).map
        (centralizerPerfectCore (nonsplitNeighbourE7G e A .four)).subtype : Subgroup G) :
          Set G) := mem_normalizer_map_leviPiece_node hk hK e hAJ hA .hf 1 h hc
    have h0 : c ∈ normalizer ((((leviPiece K .four {0}).map h.Φ.toMonoidHom).map
        (centralizerPerfectCore (nonsplitNeighbourE7G e A .four)).subtype : Subgroup G) :
          Set G) := mem_normalizer_map_leviPiece_node hk hK e hAJ hA .sf 1 h hc
    have h6 := h.mem_normalizer_map_leviPiece_of_pair (by decide) (by decide)
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) hc h5
    simp only [E7Neighbour.nodes, Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl | rfl
    exacts [h0, h5, h6]

theorem TwoFieldParam.mem_normalizer_map_leviPiece (hk : Nat.card (fixSubfield σ) = 2)
    (hK : Nat.card K = 2 ^ 2) {e : L ≃* adjointGroup .E7 (fixSubfield σ)}
    {A : Subgroup (adjointGroup .E7 (fixSubfield σ))} (hAJ : A ≤ posJE7 (fixSubfield σ))
    (hA : Nat.card A = Nat.card (fixSubfield σ) + 1) {N : E7Neighbour}
    (h : TwoFieldParam σ e N (centralizerPerfectCore (nonsplitNeighbourE7G e A N)))
    {J : Finset (Fin (Tag.rank .E7))} (hJ : J ⊆ N.nodes) {c : G}
    (hc : c ∈ centralizer (L : Set G)) :
    c ∈ normalizer ((((leviPiece K N J).map h.Φ.toMonoidHom).map
      (centralizerPerfectCore (nonsplitNeighbourE7G e A N)).subtype : Subgroup G) : Set G) := by
  rw [leviPiece_eq_iSup hJ]
  simp only [Subgroup.map_iSup]
  refine F4Pilot.mem_normalizer_iSup fun j => ?_
  by_cases hj : j ∈ J
  · rw [iSup_pos hj]
    exact h.mem_normalizer_map_leviPiece_single hk hK hAJ hA (hJ hj) hc
  · rw [iSup_neg hj, mem_normalizer_iff]
    intro x
    simp only [mem_bot]
    constructor
    · rintro rfl
      group
    · intro hx
      calc x = c⁻¹ * (c * x * c⁻¹) * c := by group
        _ = 1 := by rw [hx]; group

end AllNodes

end CFSG.SeitzReduction.E7Pilot
