module

public import CFSG.ClassicalInvolution.RouteD.TWS7Nodes
public import CFSG.ClassicalInvolution.RouteD.GapsEnd4Aux
public import CFSG.ClassicalInvolution.RouteD.LocalTwinPartner
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123

public section

namespace CFSG.ClassicalInvolution.RouteD.TWS7

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.RouteD CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.Timmesfeld CFSG.ClassicalInvolution.RouteD.Gaps
open scoped MatrixGroups

set_option linter.unusedSectionVars false

local macro "fr_idx" : tactic =>
  `(tactic| first
    | (simp [DNodes.adj_def]; done)
    | (simp [DNodes.adj_def]; omega)
    | (simp; done)
    | (simp; omega)
    | omega)

section Unipotent

variable {F : Type} [Field F]

@[expose] def tv : SL(2, F) := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two_of]⟩

theorem coe_tv_pow (n : ℕ) : (((tv : SL(2, F)) ^ n : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
    !![1, (n : F); 0, 1] := by
  induction n with
  | zero => ext i j; fin_cases i <;> fin_cases j <;> simp
  | succ n ih =>
    rw [pow_succ, Matrix.SpecialLinearGroup.coe_mul, ih]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [tv, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem tv_pow_char {p : ℕ} [CharP F p] : (tv : SL(2, F)) ^ p = 1 := by
  refine Subtype.ext ?_
  rw [coe_tv_pow]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem tv_ne_one : (tv : SL(2, F)) ≠ 1 := by
  intro h
  have := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 1) h
  simp [tv] at this

theorem diagConj2_tv : diagConj2 (-1 : Fˣ) 1 (tv : SL(2, F)) = (tv : SL(2, F))⁻¹ := by
  refine Subtype.ext ?_
  rw [coe_diagConj2, Matrix.SpecialLinearGroup.coe_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tv, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.adjugate_fin_two]

theorem exists_inverted_unipotent {p : ℕ} [CharP F p] (h2 : (2 : F) ≠ 0) {X : Type} [Group X]
    {W U V : Subgroup X} (h : LinearBlockStandardPair F W U V) {v : X} (hv : v ∈ V)
    (hv2 : orderOf v = 2) :
    ∃ x ∈ U, x ≠ 1 ∧ x ^ p = 1 ∧ v * x * v⁻¹ = x⁻¹ := by
  obtain ⟨θ, -, hker, hU, hV⟩ := pair_normalize h
  rw [← hV] at hv
  have hvθ := eq_block_neg_one h2 hker (by omega : 1 + 2 ≤ 3) hv hv2
  set n : SL(3, F) := blockSL F 3 2 1 (by omega) (-1) with hn
  have hnn : n * n = 1 := by
    rw [hn, ← map_mul]
    have : (-1 : SL(2, F)) * (-1) = 1 := by simp
    rw [this, map_one]
  have hvv : v * v = 1 := by rw [hvθ, ← map_mul, hnn, map_one]
  have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_right hvv
  have hinj := comp_blockSL_injective hker (by omega : 0 + 2 ≤ 3) (by omega : 2 < 3)
  refine ⟨θ (blockSL F 3 2 0 (by omega) tv), ?_, ?_, ?_, ?_⟩
  · rw [← hU]
    exact ⟨_, ⟨_, rfl⟩, rfl⟩
  · intro h1
    have : θ (blockSL F 3 2 0 (by omega) tv) = θ (blockSL F 3 2 0 (by omega) 1) := by
      rw [h1, map_one, map_one]
    exact tv_ne_one (hinj this)
  · rw [← map_pow, ← map_pow, tv_pow_char, map_one, map_one]
  · have e1 : n * blockSL F 3 2 0 (by omega) tv =
        blockSL F 3 2 0 (by omega) (diagConj2 (-1) 1 tv) * n := by
      rw [hn, blockSL_neg_one_mul, diagConj3_blockSL_zero]
    rw [hvi, hvθ, ← map_mul, ← map_mul, e1, mul_assoc, hnn, mul_one, diagConj2_tv, map_inv,
      map_inv]

end Unipotent

section Twin

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G}


theorem exists_fixed_twin_data (c : TCtx p f .POmegaPlus 4 Ω K z)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hshape : LocalShapeT p f 2 .POmegaPlus 4 Ω z) {β : Subgroup G} {t : G} (hβ : β ∈ Ω)
    (ht : IsClassicalMember p f β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField p f) W K β)
    (hfix : HasFixedMember Ω K β z) :
    ∃ M M' J : Subgroup G,
      M ∈ centralizingMembers Ω {z} ∧ M ≠ K ∧ ¬ locImg Ω z M ≤ c.d.Q₁ ∧
      M' ∈ centralizingMembers Ω {z} ∧ M' ≠ K ∧ ¬ locImg Ω z M' ≤ c.d.Q₁ ∧
      J ∈ centralizingMembers Ω {z} ∧ J ≠ K ∧ ¬ locImg Ω z J ≤ c.d.Q₁ ∧
      Commutes M M' ∧ Commutes M J ∧ Commutes M' J ∧ Commutes β M ∧ Commutes β M' ∧
      conjSub t J = J ∧ (∃ W, LinearBlockStandardPair (GaloisField p f) W β J) ∧
      ¬ Commutes β J ∧ ∃ x ∈ J, x ≠ 1 ∧ x ^ p = 1 ∧ t * x * t⁻¹ = x⁻¹ := by
  classical
  have hΩ := c.hΩ
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f c.hp2
  have hf0 : 0 < f := Nat.pos_of_ne_zero c.hf
  obtain ⟨M, hMΩ, hKM, hβM, hMN⟩ := hfix
  have hMN' : ∃ N ∈ centralizingMembers Ω {z}, N ≠ M ∧ ¬ Commutes M N := by
    by_contra h
    exact hMN fun N hN hNM => by_contra fun hc => h ⟨N, hN, hNM, hc⟩
  obtain ⟨nd, h0, h1⟩ :=
    exists_dnodes_of_pair_four c hsingle hshape hβ ht hKβ hMΩ hKM hβM
  obtain ⟨W, hW⟩ := hKβ
  have hnKβ : ¬ Commutes K β := not_commutes_of_linearBlockStandardPair hW
  have hKne : K ≠ β := ne_of_linearBlockStandardPair hW
  have hMz : M ∈ centralizingMembers Ω {z} :=
    mem_centralizingMembers_of_commutes hMΩ c.hz.mem (commutes_symm hKM)
  obtain ⟨N, hNz, hNM, hNc⟩ := hMN'
  have hML : IsLayerMember c M :=
    IsLayerMember.of_not_commutes c hMz hNz (fun h => hNM h.symm) hNc
  obtain ⟨w, hw⟩ := hΩ.classical M hMΩ
  obtain ⟨cx⟩ := exists_ctx_member c hsingle hshape hMΩ hw
  obtain ⟨T, hTw, hTQ⟩ := cx.exists_twin
  have hKw : K ∈ centralizingMembers Ω {w} := mem_centralizingMembers_of_commutes c.hK hw.mem hKM
  have hβw : β ∈ centralizingMembers Ω {w} := mem_centralizingMembers_of_commutes hβ hw.mem hβM
  have hKL := IsLayerMember.of_not_commutes cx hKw hβw hKne hnKβ
  have hKT : K ≠ T := fun h => hKL.2.2 (by rw [h, hTQ])
  have hTK : Commutes T K := cx.commutes_T_of_ne hTw hTQ.le hKw hKT
  have hnβK : ¬ Commutes β K := fun h => hnKβ (commutes_symm h)
  have hβT : β ≠ T := fun h => hnβK (h ▸ hTK)
  have hTβ : Commutes T β := cx.commutes_T_of_ne hTw hTQ.le hβw hβT
  have hMw : M ∈ centralizingMembers Ω {w} := ⟨hMΩ, le_centralizer_of_isClassicalMember hw⟩
  have hTM : Commutes T M := cx.commutes_T_of_ne hTw hTQ.le hMw (cx.twin_ne hTw hTQ.le).symm
  have hTz : T ∈ centralizingMembers Ω {z} := mem_centralizingMembers_of_commutes hTw.1 c.hz.mem hTK
  have hTKne : T ≠ K := hKT.symm
  have hTQz : ¬ locImg Ω z T ≤ c.d.Q₁ := by
    intro hTQz
    obtain ⟨zT, hzT⟩ := hΩ.classical T hTw.1
    obtain ⟨g₁, hg₁⟩ := hsingle T hTw.1
    obtain ⟨g₂, hg₂⟩ := hsingle M hMΩ
    have hKconj : ∃ g : G, T = conjSub g K := ⟨g₁, hg₁⟩
    have hMconj : ∃ g : G, T = conjSub g M := ⟨g₁ * g₂⁻¹, by
      rw [hg₁, hg₂, ← conjSub_mul, mul_assoc, inv_mul_cancel, mul_one]⟩
    have e1 := centralizingMembers_eq_of_twin c.hp2 hf0 hΩ c.hz hzT hKconj hTz
      fun N hN hNT => c.commutes_T_of_ne hTz hTQz hN hNT
    have e2 := centralizingMembers_eq_of_twin c.hp2 hf0 hΩ hw hzT hMconj hTw
      fun N hN hNT => cx.commutes_T_of_ne hTw hTQ.le hN hNT
    have hβz : β ∈ centralizingMembers Ω {z} := by rw [← e1, e2]; exact hβw
    exact hnKβ (c.commutes_K_of_ne hβz hKne.symm)
  have hKJ : ∀ a : ℕ, ∀ h : a < 4, 2 ≤ a → Commutes K (nd.J ⟨a, h⟩) := by
    intro a h ha
    rw [← h0]
    exact nd.commutes_of_not_adj (fin_ne_of_val_ne (by fr_idx)) (by fr_idx)
  have hJz : ∀ a : ℕ, ∀ h : a < 4, 2 ≤ a → nd.J ⟨a, h⟩ ∈ centralizingMembers Ω {z} := fun a h ha =>
    mem_centralizingMembers_of_commutes (nd.mem _) c.hz.mem (commutes_symm (hKJ a h ha))
  have hJw : ∀ a : Fin 4, nd.J a ∈ centralizingMembers Ω {w} := fun a =>
    mem_centralizingMembers_of_commutes (nd.mem a) hw.mem (commutes_symm (nd.commK a))
  have hadj1 : ∀ a : ℕ, ∀ h : a < 4, 2 ≤ a →
      DNodes.Adj (⟨1, by omega⟩ : Fin 4) ⟨a, h⟩ := fun a h ha => by fr_idx
  have key : ∀ a : ℕ, ∀ h : a < 4, 2 ≤ a → ¬ locImg Ω z (nd.J ⟨a, h⟩) ≤ c.d.Q₁ →
      ∃ M M' J : Subgroup G,
        M ∈ centralizingMembers Ω {z} ∧ M ≠ K ∧ ¬ locImg Ω z M ≤ c.d.Q₁ ∧
        M' ∈ centralizingMembers Ω {z} ∧ M' ≠ K ∧ ¬ locImg Ω z M' ≤ c.d.Q₁ ∧
        J ∈ centralizingMembers Ω {z} ∧ J ≠ K ∧ ¬ locImg Ω z J ≤ c.d.Q₁ ∧
        Commutes M M' ∧ Commutes M J ∧ Commutes M' J ∧ Commutes β M ∧ Commutes β M' ∧
        conjSub t J = J ∧ (∃ W, LinearBlockStandardPair (GaloisField p f) W β J) ∧
        ¬ Commutes β J ∧ ∃ x ∈ J, x ≠ 1 ∧ x ^ p = 1 ∧ t * x * t⁻¹ = x⁻¹ := by
    intro a h ha hQ
    have hJK : nd.J ⟨a, h⟩ ≠ K := by
      rw [← h0]
      exact nd.ne_J hΩ (fin_ne_of_val_ne (by fr_idx)) |>.symm
    have hnβJ : ¬ Commutes β (nd.J ⟨a, h⟩) := by
      have := nd.not_commutes_of_adj (hadj1 a h ha)
      rwa [h1] at this
    have hJT : nd.J ⟨a, h⟩ ≠ T := fun hJT => hnβJ (by rw [hJT]; exact commutes_symm hTβ)
    obtain ⟨W₁, hW₁⟩ := nd.pair_of_adj (a := ⟨a, h⟩) (b := ⟨1, by omega⟩)
      (DNodes.Adj.symm (hadj1 a h ha))
    obtain ⟨W₂, hW₂⟩ := nd.pair_of_adj (hadj1 a h ha)
    rw [h1] at hW₁ hW₂
    refine ⟨M, T, nd.J ⟨a, h⟩, hMz, hML.2.1, hML.2.2, hTz, hTKne, hTQz, hJz a h ha, hJK, hQ,
      commutes_symm hTM, nd.commK _, cx.commutes_T_of_ne hTw hTQ.le (hJw _) hJT, hβM,
      commutes_symm hTβ, conjSub_eq_of_standardPair h2 hW₁ ht.mem ht.orderOf_eq_two, ⟨W₂, hW₂⟩,
      hnβJ, ?_⟩
    exact exists_inverted_unipotent h2 hW₁ ht.mem ht.orderOf_eq_two
  by_cases hQ2 : locImg Ω z (nd.J ⟨2, by omega⟩) ≤ c.d.Q₁
  · refine key 3 (by omega) (by omega) fun hQ3 => ?_
    have := c.eq_of_locImg_le_Q₁ (hJz 2 (by omega) (by omega)) (hJz 3 (by omega) (by omega))
      hQ2 hQ3
    exact nd.ne_J hΩ (fin_ne_of_val_ne (by fr_idx)) this
  · exact key 2 (by omega) (by omega) hQ2

end Twin

end CFSG.ClassicalInvolution.RouteD.TWS7
