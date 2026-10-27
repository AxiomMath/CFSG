module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftOffenderAll
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftMaxSL2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftMaxBlocks
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftMaxDel

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open CFSG.QuasithinUnique.Setup.Offender CFSG.QuasithinUnique.Setup.Layer CFSG.QuasithinUnique
  CFSG.Quasithin.B6 CFSG.QuasithinUnique.Setup.SL2Modules
open scoped MatrixGroups LinearAlgebra.Projectivization commutatorElement
open Projectivization

universe v

section Defs

variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]

structure EvenSL2MaxOutput (H T M : Subgroup (V ≃ₗ[ZMod 2] V)) (n : ℕ) (F : Type) [Field F]
    [Fintype (ℙ F (Fin 2 → F))] [DecidableEq (ℙ F (Fin 2 → F))] (r : ℕ)
    (Lc : Fin r → Subgroup (V ≃ₗ[ZMod 2] V)) : Prop where
  offenders : EvenSL2OffenderOutput H T n F r Lc
  U_sylow : ∀ i, IsSylowTwoOf (T ⊓ Lc i) (Lc i)
  D_eq : T ⊓ oddGen H = ⨆ i, T ⊓ Lc i
  M_eq_normalizer : M = Subgroup.normalizer ((T ⊓ oddGen H : Subgroup _) : Set _) ⊓ H
  M_eq_P : M = (⨆ i, localNormalizer T (Lc i)) ⊔ T
  M_inf_K : M ⊓ oddGen H = ⨆ i, localNormalizer T (Lc i)
  M_inf_L : ∀ i, M ⊓ Lc i = localNormalizer T (Lc i)
  normalizer_T_le : Subgroup.normalizer (T : Set _) ⊓ H ≤ M
  index_eq : M.relIndex H = (2 ^ n + 1) ^ r
  P_maximal : ∀ i, localNormalizer T (Lc i) < Lc i ∧ ∀ Y : Subgroup (V ≃ₗ[ZMod 2] V),
    localNormalizer T (Lc i) ≤ Y → Y ≤ Lc i → Y = localNormalizer T (Lc i) ∨ Y = Lc i
  index_L : ∀ i, (localNormalizer T (Lc i)).relIndex (Lc i) = 2 ^ n + 1
  Q_sylow : ∀ i, IsSylowTwoOf (T ⊓ blockB H (Lc i)) (blockB H (Lc i))
  M_inf_B : ∀ i, M ⊓ blockB H (Lc i) =
    Subgroup.normalizer ((T ⊓ Lc i : Subgroup _) : Set _) ⊓ blockB H (Lc i)
  M_inf_J : M ⊓ offenderJ H =
    ⨆ i, Subgroup.normalizer ((T ⊓ Lc i : Subgroup _) : Set _) ⊓ blockB H (Lc i)
  M_eq_R : M = (⨆ i, Subgroup.normalizer ((T ⊓ Lc i : Subgroup _) : Set _) ⊓ blockB H (Lc i)) ⊔ T
  natural : NaturalFamily H F r Lc → (∀ i, T ⊓ blockB H (Lc i) = T ⊓ Lc i) ∧
    (∀ i, M ⊓ blockB H (Lc i) =
      Subgroup.normalizer ((T ⊓ blockB H (Lc i) : Subgroup _) : Set _) ⊓ blockB H (Lc i)) ∧
    ∀ i, (M ⊓ blockB H (Lc i)).relIndex (blockB H (Lc i)) = 2 ^ n + 1
  deleted : DeletedFamily H n r Lc → ∀ i, ∃ (Ω : Type) (_ : Fintype Ω) (_ : DecidableEq Ω),
    Fintype.card Ω = 5 ∧ ∃ ψ : ↥(blockB H (Lc i)) ≃* Equiv.Perm Ω,
      ((Lc i).subgroupOf (blockB H (Lc i))).map ψ.toMonoidHom = alternatingGroup Ω ∧
      ∃ ω : Ω, (∀ q ∈ (T ⊓ blockB H (Lc i)).subgroupOf (blockB H (Lc i)), ψ q ω = ω) ∧
        (∀ ω' : Ω, (∀ q ∈ (T ⊓ blockB H (Lc i)).subgroupOf (blockB H (Lc i)), ψ q ω' = ω') →
          ω' = ω) ∧
        ((M ⊓ blockB H (Lc i)).subgroupOf (blockB H (Lc i))).map ψ.toMonoidHom =
          MulAction.stabilizer (Equiv.Perm Ω) ω ∧
        ((M ⊓ Lc i).subgroupOf (blockB H (Lc i))).map ψ.toMonoidHom =
          alternatingGroup Ω ⊓ MulAction.stabilizer (Equiv.Perm Ω) ω ∧
        (M ⊓ blockB H (Lc i)).relIndex (blockB H (Lc i)) = 5

end Defs

section Main

variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem isSylowTwoOf_of_isSylowOf {G : Type*} [Group G] [Finite G] {S K : Subgroup G}
    (h : CFSG.ABGLocalTools.IsSylowOf 2 S K) : IsSylowTwoOf S K :=
  CFSG.ABGLocalTools.isSylowOf_iff.1 h

theorem even_SL2_maximal_subgroup_intersections
    {H T M E : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hns : ¬ Group.IsSolvable ↥H)
    (hO2 : ∀ N : Subgroup (V ≃ₗ[ZMod 2] V), N ≤ H → (N.subgroupOf H).Normal → IsPGroup 2 N →
      N = ⊥)
    (hT : IsSylowTwoOf T H) (hTn : ¬ (T.subgroupOf H).Normal) (hTM : T ≤ M) (hMH : M < H)
    (hmax : ∀ Y : Subgroup (V ≃ₗ[ZMod 2] V), T ≤ Y → Y < H → Y ≤ M)
    (hEH : E ≤ H) (hEne : E ≠ ⊥) (hEel : CFSG.IsElementaryAbelian 2 E)
    (hEoff : Nat.card V ≤ weight (MonoidHom.id (V ≃ₗ[ZMod 2] V)) E)
    {n : ℕ} (hn : 2 ≤ n) {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 2 ^ n)
    [Fintype (ℙ F (Fin 2 → F))] [DecidableEq (ℙ F (Fin 2 → F))]
    {Lstar : Subgroup (V ≃ₗ[ZMod 2] V)} (hLstar : IsComponentIn Lstar H)
    (α : (↥Lstar ⧸ Subgroup.center ↥Lstar) ≃* SL(2, F))
    {r : ℕ} {Lc : Fin r → Subgroup (V ≃ₗ[ZMod 2] V)} (hLc : IsCompListIn H r Lc) :
    EvenSL2MaxOutput H T M n F r Lc := by
  classical
  have hfin : Finite (V ≃ₗ[ZMod 2] V) := finite_linearEquiv
  have off := even_SL2_whole_action_offenders hns hO2 hT hTn hTM hMH hmax hEH hEne hEel hEoff hn hF
    hLstar α hLc
  have layer := off.family.layer
  have common := off.family.common
  let ctx : FamilyCtx H T n F r Lc := familyCtx_of_layer hn hF hLc layer
  have hLK : ∀ i, Lc i ≤ oddGen H := fun i => by
    rw [layer.K_eq]
    exact le_iSup Lc i
  have hKH : oddGen H ≤ H := oddGen_le_self H
  have hHK : H ≤ Subgroup.normalizer (oddGen H : Set (V ≃ₗ[ZMod 2] V)) := fun h hh =>
    mem_normalizer_oddGen ctx hh
  have hKn : ((oddGen H).subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).2 hHK
  have hKnorm : ∀ i, oddGen H ≤ Subgroup.normalizer (Lc i : Set (V ≃ₗ[ZMod 2] V)) := by
    intro i
    rw [layer.K_eq]
    refine iSup_le fun j => ?_
    by_cases hji : j = i
    · subst hji
      exact Subgroup.le_normalizer
    · have : Lc j ≤ Subgroup.centralizer (Lc i : Set (V ≃ₗ[ZMod 2] V)) := fun x hx =>
        Subgroup.mem_centralizer_iff.2 fun z hz => (hLc.elem_commute hji x hx z hz).symm
      exact this.trans (Subgroup.centralizer_le_normalizer _)
  have hT2 : CFSG.ABGLocalTools.IsSylowOf 2 T H := isSylowOf_two_of hT
  have hD : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ oddGen H) (oddGen H) :=
    hT2.inf_of_le_normalizer hKH hHK
  have hU : ∀ i, CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ Lc i) (Lc i) := fun i => by
    have := hD.inf_of_le_normalizer (hLK i) (hKnorm i)
    rwa [inf_assoc, inf_eq_right.2 (hLK i)] at this
  have hcoat : ∀ i, localNormalizer T (Lc i) < Lc i ∧
      (∀ Y : Subgroup (V ≃ₗ[ZMod 2] V), localNormalizer T (Lc i) ≤ Y → Y ≤ Lc i →
        Y = localNormalizer T (Lc i) ∨ Y = Lc i) ∧
      (localNormalizer T (Lc i)).relIndex (Lc i) = 2 ^ n + 1 := fun i =>
    localNormalizer_coatom hF (hU i) (layer.iso i).some
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8⟩ := transitive_direct_product_rel hT2 hTM hMH hmax
    layer.r_pos hKH hKn layer.K_eq (fun i j hij => hLc.elem_commute hij) layer.direct
    layer.H_eq_KT layer.transitive (fun i => ⟨(hcoat i).1, (hcoat i).2.1⟩)
  have hindex : M.relIndex H = (2 ^ n + 1) ^ r := by
    rw [c8, Finset.prod_congr rfl fun i _ => (hcoat i).2.2, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
  have hJH : offenderJ H ≤ H := offenderJ_le
  have hJn : H ≤ Subgroup.normalizer (offenderJ H : Set (V ≃ₗ[ZMod 2] V)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJH).1 layer.J_normal
  have hBJ : ∀ i, blockB H (Lc i) ≤ offenderJ H := fun i => by
    rw [common.J_eq]
    exact le_iSup (fun j => blockB H (Lc j)) i
  have hBH : ∀ i, blockB H (Lc i) ≤ H := fun i => (hBJ i).trans hJH
  have hBn : ∀ i, offenderJ H ≤ Subgroup.normalizer (blockB H (Lc i) : Set (V ≃ₗ[ZMod 2] V)) :=
    fun i => (Subgroup.normal_subgroupOf_iff_le_normalizer (hBJ i)).1 (common.B_normal i)
  have hJsyl : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ offenderJ H) (offenderJ H) :=
    hT2.inf_of_le_normalizer hJH hJn
  have hQsyl : ∀ i, CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ blockB H (Lc i)) (blockB H (Lc i)) :=
    fun i => by
      have := hJsyl.inf_of_le_normalizer (hBJ i) (hBn i)
      rwa [inf_assoc, inf_eq_right.2 (hBJ i)] at this
  have hDL : ∀ i, (T ⊓ oddGen H) ⊓ Lc i = T ⊓ Lc i := fun i => by
    rw [inf_assoc, inf_eq_right.2 (hLK i)]
  obtain ⟨hblock, hprod⟩ := normalizer_inf_iSup_blocks (fun i => blockB H (Lc i)) Lc
    (fun i => T ⊓ Lc i) (T ⊓ oddGen H) common.B_comm common.L_le_B (fun i => inf_le_right)
    (fun i => blockB_le_normalizer ctx i) c2 hDL
  have hMJ : M ⊓ offenderJ H =
      ⨆ i, Subgroup.normalizer ((T ⊓ Lc i : Subgroup _) : Set _) ⊓ blockB H (Lc i) := by
    have h1 : M ⊓ offenderJ H =
        Subgroup.normalizer ((T ⊓ oddGen H : Subgroup _) : Set _) ⊓ offenderJ H := by
      rw [c3, inf_assoc, inf_eq_right.2 hJH]
    rw [h1, common.J_eq]
    exact hprod
  have hMB : ∀ i, M ⊓ blockB H (Lc i) =
      Subgroup.normalizer ((T ⊓ Lc i : Subgroup _) : Set _) ⊓ blockB H (Lc i) := fun i => by
    rw [c3, inf_assoc, inf_eq_right.2 (hBH i)]
    exact hblock i
  have hMR : M =
      (⨆ i, Subgroup.normalizer ((T ⊓ Lc i : Subgroup _) : Set _) ⊓ blockB H (Lc i)) ⊔ T := by
    apply le_antisymm
    · intro m hm
      obtain ⟨j, hj, t, ht, rfl⟩ := mem_sup_mul (L := offenderJ H) (A := T)
        (fun t ht => hJn (hT.1 ht)) (show m ∈ offenderJ H ⊔ T by
          rw [layer.H_eq_JT]
          exact hMH.le hm)
      have hjM : j ∈ M := by
        have := M.mul_mem hm (M.inv_mem (hTM ht))
        simpa using this
      have hjR : j ∈ M ⊓ offenderJ H := ⟨hjM, hj⟩
      rw [hMJ] at hjR
      exact Subgroup.mul_mem_sup hjR ht
    · refine sup_le (iSup_le fun i => ?_) hTM
      rw [← hMB i]
      exact inf_le_left
  have hnatural : NaturalFamily H F r Lc → (∀ i, T ⊓ blockB H (Lc i) = T ⊓ Lc i) ∧
      (∀ i, M ⊓ blockB H (Lc i) =
        Subgroup.normalizer ((T ⊓ blockB H (Lc i) : Subgroup _) : Set _) ⊓ blockB H (Lc i)) ∧
      ∀ i, (M ⊓ blockB H (Lc i)).relIndex (blockB H (Lc i)) = 2 ^ n + 1 := by
    intro hnat
    have hB : ∀ i, blockB H (Lc i) = Lc i := hnat.B_eq
    refine ⟨fun i => by rw [hB i], fun i => ?_, fun i => ?_⟩
    · rw [hMB i, hB i]
    · rw [hB i, c6 i]
      exact (hcoat i).2.2
  have hdeleted : DeletedFamily H n r Lc → ∀ i, ∃ (Ω : Type) (_ : Fintype Ω) (_ : DecidableEq Ω),
      Fintype.card Ω = 5 ∧ ∃ ψ : ↥(blockB H (Lc i)) ≃* Equiv.Perm Ω,
        ((Lc i).subgroupOf (blockB H (Lc i))).map ψ.toMonoidHom = alternatingGroup Ω ∧
        ∃ ω : Ω, (∀ q ∈ (T ⊓ blockB H (Lc i)).subgroupOf (blockB H (Lc i)), ψ q ω = ω) ∧
          (∀ ω' : Ω, (∀ q ∈ (T ⊓ blockB H (Lc i)).subgroupOf (blockB H (Lc i)), ψ q ω' = ω') →
            ω' = ω) ∧
          ((M ⊓ blockB H (Lc i)).subgroupOf (blockB H (Lc i))).map ψ.toMonoidHom =
            MulAction.stabilizer (Equiv.Perm Ω) ω ∧
          ((M ⊓ Lc i).subgroupOf (blockB H (Lc i))).map ψ.toMonoidHom =
            alternatingGroup Ω ⊓ MulAction.stabilizer (Equiv.Perm Ω) ω ∧
          (M ⊓ blockB H (Lc i)).relIndex (blockB H (Lc i)) = 5 := by
    intro hdel i
    obtain ⟨ψs, βs, h5, hmodel, -⟩ := off.deleted hdel
    obtain ⟨-, hψL, -⟩ := hmodel i
    obtain ⟨ω, hfix, huniq, hstab, halt, hidx⟩ := deleted_stabilizer_facts h5 (ψs i)
      (common.L_le_B i) (inf_le_right) (inf_le_inf_left T (common.L_le_B i)) hψL (hU i)
      (fun q hq => mem_normalizer_inf (Subgroup.le_normalizer hq.1)
        (blockB_le_normalizer ctx i hq.2)) (hMB i)
    have hLM : (M ⊓ blockB H (Lc i)) ⊓ Lc i = M ⊓ Lc i := by
      rw [inf_assoc, inf_eq_right.2 (common.L_le_B i)]
    rw [hLM] at halt
    exact ⟨ℙ F (Fin 2 → F), inferInstance, inferInstance, h5, ψs i, hψL, ω, hfix, huniq, hstab,
      halt, hidx⟩
  exact
    { offenders := off
      U_sylow := fun i => isSylowTwoOf_of_isSylowOf (hU i)
      D_eq := c2
      M_eq_normalizer := c3
      M_eq_P := c4
      M_inf_K := c5
      M_inf_L := c6
      normalizer_T_le := c7
      index_eq := hindex
      P_maximal := fun i => ⟨(hcoat i).1, (hcoat i).2.1⟩
      index_L := fun i => (hcoat i).2.2
      Q_sylow := fun i => isSylowTwoOf_of_isSylowOf (hQsyl i)
      M_inf_B := hMB
      M_inf_J := hMJ
      M_eq_R := hMR
      natural := hnatural
      deleted := hdeleted }

end Main

end CFSG.QuasithinUnique.Setup.Lift
