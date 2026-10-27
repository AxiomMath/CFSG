module

public import CFSG.LocalAnalysis.SeitzReduction.E8PilotQ2PieceFrame
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotQ2FieldMain

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E8Pilot

open Subgroup CFSG.Open CFSG.EvenSmallLie CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Steinberg.Adjoint
open CFSG.Quasithin (perfectCore perfectCore_le perfectCore_mono le_perfectCore_of_perfect)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)

local instance e8PilotQ2PieceMainNeZeroRank : NeZero Tag.E8.rank := ⟨by decide⟩

section General

variable {G : Type} [Group G]

theorem centralizer_map_map_zpowers {L : Subgroup G} {M : Type} [Group M] (e : L ≃* M) (a : M) :
    centralizer
        ((((Subgroup.zpowers a).map e.symm.toMonoidHom).map L.subtype : Subgroup G) : Set G) =
      centralizer ({((e.symm a : L) : G)} : Set G) := by
  rw [MonoidHom.map_zpowers, MonoidHom.map_zpowers, Subgroup.zpowers_eq_closure,
    Subgroup.centralizer_closure]
  rfl

theorem perfectCore_inf_eq_perfectCore_perfectCore_inf [Finite G] (C W : Subgroup G) :
    perfectCore (C ⊓ W) = perfectCore (perfectCore C ⊓ W) := by
  refine le_antisymm ?_ (perfectCore_mono (inf_le_inf_right W (perfectCore_le C)))
  exact le_perfectCore_of_perfect
    (le_inf (perfectCore_mono inf_le_left) ((perfectCore_le _).trans inf_le_right))
    (CFSG.Quasithin.perfectCore_perfect _)

theorem perfectCore_eq_of_map_eq [Finite G] {H : Type} [Group H] [Finite H] {ψ : G →* H}
    (hψ : Function.Injective ψ) {S R : Subgroup G} (h : perfectCore (S.map ψ) = R.map ψ) :
    perfectCore S = R := by
  apply Subgroup.map_injective hψ
  rw [CFSG.Quasithin.map_perfectCore, h]

end General

section Piece


variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K]

@[expose] noncomputable def q2FrameG (e : L ≃* adjointGroup .E8 K)
    (A : Subgroup (adjointGroup .E8 K)) (k : Fin 7) : Subgroup G :=
  ((A.map (MulAut.conj (wordRep K (q2FrameWord k))).toMonoidHom).map e.symm.toMonoidHom).map
    L.subtype

theorem q2FrameG_frameIdx (e : L ≃* adjointGroup .E8 K) (A : Subgroup (adjointGroup .E8 K))
    (N : E8Neighbour) : q2FrameG e A N.frameIdx = q2NeighbourG e A N := by
  cases N <;> rfl

theorem conj_wordRep_mem_levi {a : adjointGroup .E8 K}
    (ha : (a : ModGL .E8 K) ∈ EPilot.highRootSL2 .E8 K) {N : E8Neighbour} {k : Fin 7}
    (hk : k ≠ N.frameIdx) :
    wordRep K (q2FrameWord k) * a * (wordRep K (q2FrameWord k))⁻¹ ∈ N.levi K := by
  apply mem_levi_of_coe_mem
  rw [map_subtype_levi]
  have h1 := conj_wordElt_mem_rootSL2 (q2FrameWord k) ha
  rw [q2FrameWord_smul_highRoot] at h1
  have h0 : iform N.root (q2FrameRoot k) = 0 := by
    rw [← E8Neighbour.q2FrameRoot_frameIdx, iform_q2FrameRoot, ite_eq_right (Ne.symm hk)]
  have h0' : iform N.root (-q2FrameRoot k) = 0 := by rw [iform_neg_right_E8, h0, neg_zero]
  have hle : rootSubgroup .E8 K (q2FrameRoot k) ⊔ rootSubgroup .E8 K (-q2FrameRoot k) ≤
      rootSpan .E8 K (orthRoots N.root) :=
    sup_le
      (le_iSup₂_of_le (f := fun α (_ : α ∈ orthRoots N.root) => rootSubgroup .E8 K α) _
        ⟨isRoot_q2FrameRoot k, h0⟩ le_rfl)
      (le_iSup₂_of_le (f := fun α (_ : α ∈ orthRoots N.root) => rootSubgroup .E8 K α) _
        ⟨IsRoot.neg (isRoot_q2FrameRoot k), h0'⟩ le_rfl)
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_wordRep]
  exact hle h1

theorem map_leviPiece_zero {K₂ : Type} [Field K₂] (N : E8Neighbour) :
    (leviPiece K₂ N {0}).map ((adjointGroup .E8 K₂).subtype.comp (N.levi K₂).subtype) =
      rootSpan .E8 K₂ (amalgamRoots {0}) := by
  rw [← Subgroup.map_map, leviPiece, subgroupOf_map_subtype,
    Subgroup.map_inf_eq _ _ _ (adjointGroup .E8 K₂).subtype_injective, subgroupOf_map_subtype,
    map_subtype_levi, inf_of_le_left (rootSpan_le_adjointGroup_E8 _)]
  exact inf_of_le_left
    (rootSpan_mono (amalgamRoots_subset_orthRoots_iff_subset_nodes.2 (by cases N <;> decide)))

theorem map_leviPiece_zero_eq_perfectCore_iInf [Finite G] (hK : Nat.card K = 2)
    (e : L ≃* adjointGroup .E8 K) {K₂ : Type} [Field K₂] [Finite K₂] [CharP K₂ 2] (ι : K →+* K₂)
    (hK₂ : Nat.card K₂ = 2 ^ 2) {A : Subgroup (adjointGroup .E8 K)} (hAJ : A ≤ posJE8 K)
    (hA : Nat.card A = Nat.card K + 1) (N : E8Neighbour)
    (h : TwoFieldParam ι e N (centralizerPerfectCore (q2NeighbourG e A N))) :
    ((leviPiece K₂ N {0}).map h.Φ.toMonoidHom).map
        (centralizerPerfectCore (q2NeighbourG e A N)).subtype =
      perfectCore (⨅ k : Fin 7, centralizer (q2FrameG e A k : Set G)) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  have : Finite (ModGL .E8 K₂) := finite_modGL
  have hA3 : Nat.card A = 3 := by rw [hA, hK]
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hcyc : IsCyclic A := isCyclic_of_prime_card hA3
  obtain ⟨⟨a, haA⟩, hgen⟩ := IsCyclic.exists_generator (α := A)
  have hAa : A = Subgroup.zpowers a := by
    refine le_antisymm (fun y hy => ?_) (Subgroup.zpowers_le.2 haA)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hgen ⟨y, hy⟩)
    exact Subgroup.mem_zpowers_iff.2 ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hxJ : (a : ModGL .E8 K) ∈ EPilot.highRootSL2 .E8 K := hAJ haA
  have hx : orderOf (a : ModGL .E8 K) = 3 := by
    rw [Subgroup.orderOf_coe, ← Nat.card_zpowers, ← hAa, hA3]
  set y : Fin 7 → adjointGroup .E8 K :=
    fun k => wordRep K (q2FrameWord k) * a * (wordRep K (q2FrameWord k))⁻¹ with hydef
  have hy : ∀ k, ((y k : adjointGroup .E8 K) : ModGL .E8 K) =
      wordElt K (q2FrameWord k) * (a : ModGL .E8 K) * (wordElt K (q2FrameWord k))⁻¹ := by
    intro k
    simp only [hydef, Subgroup.coe_mul, Subgroup.coe_inv, coe_wordRep]
  have hXk : ∀ k, centralizer (q2FrameG e A k : Set G) =
      centralizer ({((e.symm (y k) : L) : G)} : Set G) := by
    intro k
    rw [q2FrameG, hAa, MonoidHom.map_zpowers]
    exact centralizer_map_map_zpowers e _
  have hyN : ∀ k, k ≠ N.frameIdx → y k ∈ N.levi K := fun k hk => conj_wordRep_mem_levi hxJ hk
  set T : Subgroup (ModGL .E8 K₂) := (N.levi K₂).map (adjointGroup .E8 K₂).subtype ⊓
    ⨅ (k : Fin 7) (_ : k ≠ N.frameIdx), centralizer
      ({baseChangeGL ι (wordElt K (q2FrameWord k) * (a : ModGL .E8 K) *
        (wordElt K (q2FrameWord k))⁻¹)} : Set (ModGL .E8 K₂)) with hT
  have hTeq := perfectCore_levi_inf_q2Frame_eq hK hK₂ ι hxJ hx N
  set ψ : N.levi K₂ →* ModGL .E8 K₂ := (adjointGroup .E8 K₂).subtype.comp (N.levi K₂).subtype
    with hψ
  have hψinj : Function.Injective ψ :=
    (adjointGroup .E8 K₂).subtype_injective.comp (N.levi K₂).subtype_injective
  have hψrange : ψ.range = (N.levi K₂).map (adjointGroup .E8 K₂).subtype := by
    rw [hψ, MonoidHom.range_comp, Subgroup.range_subtype]
  set S : Subgroup (N.levi K₂) := T.comap ψ with hS
  have hSmap : S.map ψ = T := by
    rw [hS, Subgroup.map_comap_eq, hψrange]
    exact inf_of_le_right inf_le_left
  have hScore : perfectCore S = leviPiece K₂ N {0} :=
    perfectCore_eq_of_map_eq hψinj (by rw [hSmap, map_leviPiece_zero]; exact hTeq)
  set f : N.levi K₂ →* G :=
    (centralizerPerfectCore (q2NeighbourG e A N)).subtype.comp h.Φ.toMonoidHom with hf
  have hfinj : Function.Injective f := Subtype.val_injective.comp h.Φ.injective
  set z : ∀ k, k ≠ N.frameIdx → N.levi K₂ := fun k hk => leviBaseChange ι N ⟨y k, hyN k hk⟩
    with hzdef
  have hfz : ∀ k hk, f (z k hk) = ((e.symm (y k) : L) : G) := fun k hk => h.fix ⟨y k, hyN k hk⟩
  have hψz : ∀ k hk, ψ (z k hk) = baseChangeGL ι (wordElt K (q2FrameWord k) *
      (a : ModGL .E8 K) * (wordElt K (q2FrameWord k))⁻¹) := by
    intro k hk
    rw [← hy k]
    rfl
  have hEW : centralizerPerfectCore (q2NeighbourG e A N) ⊓
      ⨅ (k : Fin 7) (_ : k ≠ N.frameIdx), centralizer (q2FrameG e A k : Set G) = S.map f := by
    ext g
    constructor
    · rintro ⟨hgE, hgW⟩
      have hgf : f (h.Φ.symm ⟨g, hgE⟩) = g := by simp [hf]
      refine ⟨h.Φ.symm ⟨g, hgE⟩, ?_, hgf⟩
      refine Subgroup.mem_comap.2 (mem_inf.2 ⟨⟨_, (h.Φ.symm ⟨g, hgE⟩).2, rfl⟩, ?_⟩)
      refine Subgroup.mem_iInf.2 fun k => Subgroup.mem_iInf.2 fun hk => ?_
      have hgk : g ∈ centralizer (q2FrameG e A k : Set G) :=
        Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hgW k) hk
      rw [hXk k, mem_centralizer_singleton_iff, ← hfz k hk] at hgk
      rw [← hgf, ← map_mul, ← map_mul] at hgk
      have hcomm := hfinj hgk
      rw [mem_centralizer_singleton_iff, ← hψz k hk, ← map_mul, ← map_mul, hcomm]
    · rintro ⟨u, hu, rfl⟩
      refine mem_inf.2 ⟨(h.Φ u).2, ?_⟩
      refine Subgroup.mem_iInf.2 fun k => Subgroup.mem_iInf.2 fun hk => ?_
      have hTk := Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1
        (mem_inf.1 (Subgroup.mem_comap.1 hu)).2 k) hk
      rw [mem_centralizer_singleton_iff, ← hψz k hk, ← map_mul, ← map_mul] at hTk
      have hcomm := hψinj hTk
      rw [hXk k, mem_centralizer_singleton_iff, ← hfz k hk, ← map_mul, ← map_mul, hcomm]
  have hsplit : ⨅ k : Fin 7, centralizer (q2FrameG e A k : Set G) =
      centralizer (q2NeighbourG e A N : Set G) ⊓
        ⨅ (k : Fin 7) (_ : k ≠ N.frameIdx), centralizer (q2FrameG e A k : Set G) := by
    rw [iInf_split_single _ N.frameIdx, q2FrameG_frameIdx]
  rw [hsplit, perfectCore_inf_eq_perfectCore_perfectCore_inf, ← F4Pilot.centralizerPerfectCore_def,
    hEW, ← CFSG.Quasithin.map_perfectCore, hScore, Subgroup.map_map]

theorem e8TwoFieldPieceInput_holds : E8TwoFieldPieceInput := by
  intro G _ _ L K _ e t hw K₂ _ _ _ ι hK₂ A hAJ hA N N' h h'
  have hK : Nat.card K = 2 := by rw [hw.card_eq, pow_one]
  rw [map_leviPiece_zero_eq_perfectCore_iInf hK e ι hK₂ hAJ hA N h,
    map_leviPiece_zero_eq_perfectCore_iInf hK e ι hK₂ hAJ hA N' h']

end Piece

end CFSG.SeitzReduction.E8Pilot
