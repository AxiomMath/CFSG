module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotToral
public import CFSG.LieType.Chevalley.RootDiagonalWeylTransporter

public section

namespace CFSG.SeitzReduction.F4Pilot

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

local instance f4PilotToralCentralizerNeZeroRank : NeZero Tag.F4.rank := ⟨by decide⟩

variable {K : Type} [Field K]

section Pair


variable (K) in
@[expose] noncomputable def rootSL2R : Subgroup (ModGL .F4 K) :=
  rootSubgroup .F4 K rootR ⊔ rootSubgroup .F4 K (-rootR)

theorem torusElt_mem_rootPair {τ : Tag} (i : Fin τ.rank) (u : Kˣ) :
    torusElt τ K i u ∈ rootSubgroup τ K (Pi.single i 1) ⊔ rootSubgroup τ K (-Pi.single i 1) := by
  have hw : ∀ t : Kˣ, weylElt τ K i t ∈
      rootSubgroup τ K (Pi.single i 1) ⊔ rootSubgroup τ K (-Pi.single i 1) := fun t => by
    rw [weylElt_eq_xUnit_mul]
    exact mul_mem (mul_mem (Subgroup.mem_sup_left (xUnit_mem_rootSubgroup i _))
      (Subgroup.mem_sup_right (yUnit_mem_rootSubgroup i _)))
      (Subgroup.mem_sup_left (xUnit_mem_rootSubgroup i _))
  have e : torusElt τ K i u = weylElt τ K i u * (weylElt τ K i 1)⁻¹ :=
    eq_mul_inv_of_mul_eq (weylElt_eq_torusElt_mul_weylElt_one i u).symm
  rw [e]
  exact mul_mem (hw u) (inv_mem (hw 1))

end Pair

section Conj


theorem rootDiagUnit_rDiag_mem_rootSL2R (c : Kˣ) : rootDiagUnit .F4 (rDiag c) ∈ rootSL2R K := by
  have hl : iform (Pi.single 0 1 : Fin (Tag.rank .F4) → ℤ) (Pi.single 0 1) = 4 := by
    decide +kernel
  obtain ⟨w, hw⟩ := exists_smul_eq_rootR (isRoot_single .F4 0) hl
  set n := canonicalRep (coxeterSystem .F4) K w with hn
  have hconj : rootDiagUnit .F4 (rDiag c) =
      n * rootDiagUnit .F4 (fun j => c ^ Tag.cartan .F4 0 j) * n⁻¹ := by
    refine (rootDiagUnit_eq_conj_canonicalRep_iff _ _ w).2 fun v => ?_
    have h1 : rootChar (fun j => c ^ Tag.cartan .F4 0 j) v =
        c ^ (∑ j, Tag.cartan .F4 0 j * v j) := by
      rw [rootChar]
      simp only [← zpow_mul]
      rw [Finset.prod_zpow_eq_zpow_sum]
    rw [rootChar_rDiag, h1]
    congr 1
    have h2 : iform rootR (w • v) = iform (Pi.single 0 1) v := by rw [← hw, iform_smul]
    have hd : Tag.F4.symmetrizer 0 0 = 2 := by decide
    rw [iform_rootR, iform_single_left, hd] at h2
    linarith
  rw [hconj, ← torusElt_eq_rootDiagUnit]
  have hmap : (rootSubgroup .F4 K (Pi.single 0 1) ⊔ rootSubgroup .F4 K (-Pi.single 0 1)).map
      (MulAut.conj n).toMonoidHom = rootSL2R K := by
    rw [Subgroup.map_sup, (canonical_weyl_root_transport .F4 K).2.1 w _ (isRoot_single _ 0),
      (canonical_weyl_root_transport .F4 K).2.1 w _ (IsRoot.neg (isRoot_single _ 0)), smul_neg, hw]
    rfl
  rw [← hmap]
  exact ⟨_, torusElt_mem_rootPair 0 c, rfl⟩

theorem torusLineR_le_normalizer :
    torusLineR K ≤ Subgroup.normalizer (rootSpan .F4 K C3Set : Set (ModGL .F4 K)) := by
  intro t ht
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => ?_, fun hy => ?_⟩
  · rw [(commute_of_mem_torusLineR_of_mem_rootSpan ht hy).eq, mul_inv_cancel_right]
    exact hy
  · have hz := (commute_of_mem_torusLineR_of_mem_rootSpan (inv_mem ht) hy).eq
    have e : y = t * y * t⁻¹ := by
      calc y = t⁻¹ * (t * y * t⁻¹) * t := by group
        _ = (t * y * t⁻¹) * t⁻¹ * t := by rw [hz]
        _ = t * y * t⁻¹ := by group
    rw [e]
    exact hy

end Conj

section Full


theorem rootSpan_C3Set_le_centralizer_rootSL2R :
    rootSpan .F4 K C3Set ≤ Subgroup.centralizer (rootSL2R K : Set (ModGL .F4 K)) := by
  rw [Subgroup.le_centralizer_iff]
  have hneg : iform (-rootR) (-rootR) = 4 := by
    rw [show (-rootR : Fin (Tag.rank .F4) → ℤ) = (-1 : ℤ) • rootR by simp, iform_smul_left,
      iform_smul_right, iform_rootR_rootS_values.1]
    norm_num
  refine sup_le ?_ ?_
  · rw [← Subgroup.le_centralizer_iff]
    exact rootSpan_C3Set_le_centralizer isRoot_rootR iform_rootR_rootS_values.1
      fun γ hγ => (iform_eq_zero_of_mem_C3Set hγ).1
  · rw [← Subgroup.le_centralizer_iff]
    exact rootSpan_C3Set_le_centralizer (IsRoot.neg isRoot_rootR) hneg
      fun γ hγ => (iform_eq_zero_of_mem_C3Set hγ).2

theorem centralizer_rootSL2R [Finite K] (hK : ringChar K = 2) (hq : 4 ≤ Nat.card K) :
    adjointGroup .F4 K ⊓ Subgroup.centralizer (rootSL2R K : Set (ModGL .F4 K)) =
      rootSpan .F4 K C3Set := by
  refine le_antisymm (fun g hg => ?_)
    (le_inf (rootSpan_le_adjointGroup K C3Set) rootSpan_C3Set_le_centralizer_rootSL2R)
  obtain ⟨hgC, hgJ⟩ := Subgroup.mem_inf.1 hg
  obtain ⟨c, hc⟩ := exists_three_le_orderOf hq
  have hd := rootDiagUnit_rDiag_mem_rootSL2R (K := K) c
  have hgd : g ∈ toralCentralizer .F4 K (rDiag c) := by
    refine mem_toralCentralizer.2 ⟨hgC, ?_⟩
    rw [Subgroup.mem_centralizer_iff.1 hgJ _ hd, mul_inv_cancel_right]
  rw [(toralCentralizer_rDiag_eq_sup hK hc).1, ← SetLike.mem_coe,
    Subgroup.coe_mul_of_left_le_normalizer_right _ _ torusLineR_le_normalizer] at hgd
  obtain ⟨t, ht, x, hx, rfl⟩ := Set.mem_mul.1 hgd
  have hxJ := rootSpan_C3Set_le_centralizer_rootSL2R hx
  have htJ : t ∈ Subgroup.centralizer (rootSL2R K : Set (ModGL .F4 K)) := by
    have := mul_mem hgJ (inv_mem hxJ)
    rwa [mul_inv_cancel_right] at this
  obtain ⟨l, rfl⟩ := mem_torusLineR.1 ht
  have hcomm : Commute (rootDiagUnit .F4 (rDiag l)) (pinnedX .F4 K rootR 1) :=
    (Subgroup.mem_centralizer_iff.1 htJ _
      (le_sup_left (a := rootSubgroup .F4 K rootR) (mem_rootSubgroup.2 ⟨1, rfl⟩))).symm
  rw [eq_one_of_commute_pinnedX_rootR hK hcomm, rDiag_one, rootDiagUnit_one, one_mul]
  exact hx

theorem f4RootDiagUnit_mem_adjointGroup (b : Fin (Tag.rank .F4) → Kˣ) :
    rootDiagUnit .F4 b ∈ adjointGroup .F4 K := by
  obtain ⟨⟨B, hB, -⟩, hdiag⟩ := G2_F4_root_character_diagonals_inner .F4 (Or.inr rfl) K
  obtain ⟨-, -, h, -⟩ := hdiag B hB b
  exact h

theorem rootSL2R_le_adjointGroup : rootSL2R K ≤ adjointGroup .F4 K := by
  refine sup_le ?_ ?_ <;> refine (Subgroup.closure_le _).2 ?_ <;> rintro _ ⟨c, rfl⟩ <;>
    exact pinnedX_mem_adjointGroup _ c

theorem centralizer_rDiag_eq_subgroupOf [Finite K] (hK : ringChar K = 2) {c : Kˣ}
    (hc : 3 ≤ orderOf c) :
    Subgroup.centralizer {(⟨rootDiagUnit .F4 (rDiag c), f4RootDiagUnit_mem_adjointGroup _⟩ :
        adjointGroup .F4 K)} =
      (torusLineR K ⊔ rootSpan .F4 K C3Set).subgroupOf (adjointGroup .F4 K) := by
  ext g
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_subgroupOf,
    ← (toralCentralizer_rDiag_eq_sup hK hc).1, mem_toralCentralizer, Subtype.ext_iff,
    Subgroup.coe_mul, Subgroup.coe_mul]
  constructor
  · intro h
    refine ⟨g.2, ?_⟩
    rw [← h, mul_inv_cancel_right]
  · intro h
    exact (mul_inv_eq_iff_eq_mul.1 h.2).symm

theorem centralizer_rootSL2R_subgroupOf [Finite K] (hK : ringChar K = 2) (hq : 4 ≤ Nat.card K) :
    Subgroup.centralizer ((rootSL2R K).subgroupOf (adjointGroup .F4 K) : Set (adjointGroup .F4 K)) =
      (rootSpan .F4 K C3Set).subgroupOf (adjointGroup .F4 K) := by
  ext g
  rw [Subgroup.mem_subgroupOf, ← centralizer_rootSL2R hK hq, Subgroup.mem_inf]
  refine ⟨fun h => ⟨g.2, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩,
    fun h => Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
  · have := Subgroup.mem_centralizer_iff.1 h ⟨y, rootSL2R_le_adjointGroup hy⟩
      (Subgroup.mem_subgroupOf.2 hy)
    exact congrArg Subtype.val this
  · exact Subtype.ext (Subgroup.mem_centralizer_iff.1 h.2 y (Subgroup.mem_subgroupOf.1 hy))

end Full

end CFSG.SeitzReduction.F4Pilot
