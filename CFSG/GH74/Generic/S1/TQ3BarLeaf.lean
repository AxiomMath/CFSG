module

public import CFSG.GH74.Generic.S1.TQ3BarGeom
public import CFSG.GH74.Generic.S1.TQ3BarMain
public import CFSG.GH74.Generic.S1.TLeafA
public import CFSG.GH74.Generic.S1.TLeafBar

public section

open Matrix CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.Assembly.LowTwoRank Subgroup CFSG.GH74.Generic
open CFSG.ClassicalInvolution.WeakCT CFSG.GH74.Filter.ClassicalOdd
open scoped MatrixGroups commutatorElement

namespace CFSG.GH74.Generic.S1

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F]

theorem exists_q3Frame {x : G} {K : Subgroup (CentralizerBar x)} (hset : S1Setup G x K)
    (hfront : S1Front G x K) {u : Fin 4 → G} {hu : ∀ i, u i ∈ centralizer ({x} : Set G)}
    (hf : S1Frame x K u hu) (hF3 : Nat.card F = 3) (hlin : S1SymFrameLin x u F)
    (hodd : S1FrameOddFree x u) : ∃ Fr : Q3Frame G F, Fr.X = symX x u := by
  obtain ⟨hconj, hsq, hXc, hprod, -⟩ := symX_facts hset.shape.2 hset.inv hf
  have hw : ∀ e j, symX x u (e.succAbove j) ∈ centralizer ({symX x u e} : Set G) := fun e j =>
    mem_centralizer_singleton_iff.2 (hXc _ _)
  have hloc : ∀ e : Fin 5, ∃ (K' : Subgroup (CentralizerBar (symX x u e)))
      (hw' : ∀ j, symX x u (e.succAbove j) ∈ centralizer ({symX x u e} : Set G)),
        S1Setup G (symX x u e) K' ∧ S1Front G (symX x u e) K' ∧
        ∃ e' : ↥K' ≃* ↥(StatedSL 4 F), ∀ j, ActsAsReflOn e' (barOf (hw' j)) (reflDiag F j) := by
    intro e
    obtain ⟨K', hw', hset', hfront', -, e', he'⟩ := hlin e
    exact ⟨K', hw', hset', hfront', e', he'⟩
  choose D hDK hDact using sym_layerData3 x u hF3 hodd hw hloc
  have hK4 : (D 4).K = K := (hDK 4).trans hfront.layer_eq
  refine ⟨⟨symX x u, D, hsq, ?_, hXc, hprod, fun e j => hDact e j, ?_, ?_⟩, rfl⟩
  · intro e h
    have h1 := hconj e
    rw [h] at h1
    have : x = 1 := isConj_one_right.1 h1.symm
    have := hset.inv
    rw [‹x = 1›, orderOf_one] at this
    exact absurd this (by norm_num)
  · rw [hK4]
    exact hfront.cent_eq
  · rw [hK4]
    exact hset.shape.2

namespace Q3Frame

variable (Fr : Q3Frame G F)

theorem cfg (hF3 : Nat.card F = 3) {c : G} (hcJ : c ∈ symJ3 Fr.X 3) (hc2 : orderOf c = 2)
    (hcc : ∀ a ∈ symJ3 Fr.X 3, a * c = c * a) :
    Q3Cfg G F c (Fr.X 4) (Fr.X 2) (Fr.X 4 * c) (symJ3 Fr.X 0 ⊔ symJ3 Fr.X 1) (symJ3 Fr.X 3) := by
  have h2 := q3_two_ne_zero hF3
  have hF4 : Nat.card F % 4 = 3 := by rw [hF3]
  obtain ⟨s, hs, hsc, hss, hs1, hsmat⟩ := Fr.exists_s hF3 hcJ hc2
  obtain ⟨s₀, hs₀c, hs₀2, hs₀1, hs₀x⟩ := Fr.exists_s0
  have hc22 : c * c = 1 := by
    have := pow_orderOf_eq_one c
    rw [hc2] at this
    rw [← sq]
    exact this
  have hcX4 : c * Fr.X 4 = Fr.X 4 * c := by
    have := (Fr.D 4).ι_comm_self s
    rwa [hsc] at this
  have hprod : s₀ * s ∈ blkLin (F := F) 0 1 :=
    neg_mul_mem_lin hF4 h2 (a := 0) (b := 1) (c := 2) (d := 3) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) hs₀c hs₀1 hs hss hs1
  have hmat := central_mul_mat hF4 h2 hs₀c hs₀1 hs hss hs1
  have hprod1 : s₀ * s ≠ 1 := by
    intro h
    have h1 := congrArg (fun z : ↥(StatedSL 4 F) => ((z : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) 0 0) h
    simp only [hmat, zblkMat, Matrix.diagonal_apply_eq] at h1
    simp at h1
    apply h2
    linear_combination -h1
  have hys : Fr.X 4 * c = (Fr.D 4).ι (s₀ * s) := by
    rw [map_mul, hs₀x, hsc]
  have hX2c : Fr.X 2 ∈ centralizer ({c} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← Fr.X23_eq_c hF3 hcJ hc2]
    exact (Subgroup.mem_centralizer_singleton_iff.1 (Fr.X_mul_mem_cent 2 3 2)).symm
  refine ⟨hc2, Fr.orderOf_X 4, Fr.orderOf_X 2, ?_, ?_, ?_, hX2c, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  ·
    calc Fr.X 4 * c * (Fr.X 4 * c) = Fr.X 4 * (c * Fr.X 4) * c := by group
      _ = Fr.X 4 * (Fr.X 4 * c) * c := by rw [hcX4]
      _ = (Fr.X 4 * Fr.X 4) * (c * c) := by group
      _ = 1 := by rw [Fr.X_sq 4, hc22, one_mul]
  · intro h
    apply hprod1
    apply (Fr.D 4).ι_injective
    rw [← hys, h, map_one]
  · exact Subgroup.mem_centralizer_singleton_iff.2 hcX4.symm
  · rw [Subgroup.mem_centralizer_singleton_iff]
    calc Fr.X 4 * c * c = (c * Fr.X 4) * c := by rw [hcX4]
      _ = c * (Fr.X 4 * c) := by rw [mul_assoc]
  · rw [mul_assoc, hc22, mul_one]
  · refine Subgroup.mem_sup_right ?_
    rw [symJ3_one (linBlockOps3 hF3) Fr.X Fr.D Fr.hw Fr.act]
    exact ⟨s₀ * s, hprod, hys.symm⟩
  · exact (Fr.A_data hF3).1
  · exact (Fr.A_data hF3).2
  · exact Fr.A_center hF3
  · have hJ2le : symJ3 Fr.X 1 ≤ centralizer (Fr.X '' {k | k ≠ 0 ∧ k ≠ 1}) := oddRes_le _
    refine sup_le (le_inf (fun g hg => ?_) (fun g hg => ?_)) (le_inf (fun g hg => ?_) (fun g hg => ?_))
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Fr.J1_comm_X 2 (by decide) (by decide) g hg).symm
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact Fr.comm_sys hF3 0 3 (by decide) g hg c hcJ
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.1 (hJ2le hg) (Fr.X 2) ⟨2, ⟨by decide, by decide⟩, rfl⟩).symm
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact Fr.comm_sys hF3 1 3 (by decide) g hg c hcJ
  · intro Q hQ hperf
    exact Fr.perfect_le_A hF3 hcJ hc2 hQ hperf
  · intro Q hQ hperf
    exact Fr.perfect_eq_bot_cent_x hF3 hcJ hc2 hQ hperf
  · intro g hg
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hcc g hg
  · exact sup_comm_three (J := symJ3 Fr.X) (fun i j hij => Fr.comm_sys hF3 i j hij)
  · exact oddRes_oddGenerated _
  · obtain ⟨q8, hq8, hq8blk⟩ := exists_q8_blkLin (F := F) hF4 (c := 2) (d := 3) (by decide)
    refine ⟨(Fr.D 4).ι.comp q8, (Fr.D 4).ι_injective.comp hq8, fun g => ?_⟩
    rw [symJ3_three (linBlockOps3 hF3) Fr.X Fr.D Fr.hw Fr.act]
    exact ⟨q8 g, hq8blk g, rfl⟩
  · obtain ⟨q8, hq8, hq8blk⟩ := exists_q8_blkLin (F := F) hF4 (c := 0) (d := 1) (by decide)
    refine ⟨(Fr.D 4).ι.comp q8, (Fr.D 4).ι_injective.comp hq8, fun g => ?_⟩
    refine Subgroup.mem_sup_right ?_
    rw [symJ3_one (linBlockOps3 hF3) Fr.X Fr.D Fr.hw Fr.act]
    exact ⟨q8 g, hq8blk g, rfl⟩

end Q3Frame


theorem s1LeafCompBar3_of_KL3 (hK : KL3Table) : S1LeafCompBar3 := by
  intro G _ _ x K hset hfront u hu hf F _ _ hF3 hlin hodd c hcJ hc2 hcc
  obtain ⟨Fr, hFrX⟩ := exists_q3Frame hset hfront hf hF3 hlin hodd
  rw [← hFrX] at hcJ hcc ⊢
  exact q3_main hK hset.simple hset.nonab hset.kgh hset.gen4 hF3 (Fr.cfg hF3 hcJ hc2 hcc)

end CFSG.GH74.Generic.S1
