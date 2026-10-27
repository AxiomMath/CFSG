module

public import CFSG.LocalAnalysis.ComponentInitial.FourGroupCommuting
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y54R
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7S2

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open CFSG.LocalAnalysis.ComponentInitial.FourGroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private theorem y7c_eq_of_sq_eq_one_of_isCyclic {Z : Type*} [Group Z] [Finite Z] [IsCyclic Z]
    {a b : Z} (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1) : a = b := by
  classical
  have := Fintype.ofFinite Z
  by_contra hab
  have h := IsCyclic.card_pow_eq_one_le (α := Z) (n := 2) (by norm_num)
  have hsub : ({1, a, b} : Finset Z) ⊆ Finset.univ.filter (fun x : Z => x ^ 2 = 1) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hx with rfl | rfl | rfl
    · simp
    · exact ha
    · exact hb
  have hcard : ({1, a, b} : Finset Z).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simpa using hab
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨Ne.symm ha1, Ne.symm hb1⟩
  have := Finset.card_le_card hsub
  omega

theorem y7c_t_sq (s : Setting3 G L) : s.t ^ 2 = 1 := by
  simpa [s.t_order] using pow_orderOf_eq_one s.t

theorem y7c_card_M3 (c : Ctx5 G L) (hH : F33Hyp c.s c.e) : Nat.card ↥(M3 c.s) = 2 ^ 6 := by
  have hF : c.s.fr.F ≤ M3 c.s := (y54_M3_cand c hH).1
  have h := Subgroup.relIndex_mul_card (H := c.s.fr.F) (K := M3 c.s)
  rw [inf_of_le_left hF] at h
  rw [y54_M3_relIndex c hH, (y54_F_isE3 hH).2] at h
  rw [← h]
  norm_num

theorem y7c_M3_elem (c : Ctx7 G L) (hH : F33Hyp c.s c.e) (h57 : c.toCtx5.Fact57) :
    IsElemAbelian 2 (M3 c.s) := by
  rcases h57.2 with ⟨hV1, hElem⟩ | ⟨hV1, hComm, hHom, htinv⟩
  · exact hElem
  · exfalso
    obtain ⟨w, hwV, hzVc, hw1, hz1, hwz, hw2, hz2, hwz2, henum⟩ := f3_V_elems hH
    have hd2 : c.d ^ 2 = 1 := y5_d_sq c.toCtx5
    have hd1 : c.d ≠ 1 := by
      intro h
      have hdord : orderOf c.d = 2 := c.d_order
      rw [h, orderOf_one] at hdord
      norm_num at hdord
    have hzd : c.s.fr.z ≠ c.d := by
      intro h
      apply c.d_not_mem
      rw [zt, ← h]
      exact Subgroup.subset_closure (by simp)
    have hzV : c.s.fr.z ∈ V1 c.e := by
      rw [c.hV]
      exact Subgroup.subset_closure (by simp)
    have hdV : c.d ∈ V1 c.e := by
      rw [c.hV]
      exact Subgroup.subset_closure (by simp)
    haveI : IsCyclic ↥(V1 c.e) := by
      rw [hV1]
      exact inferInstance
    have hzV2 : (⟨c.s.fr.z, hzV⟩ : ↥(V1 c.e)) ^ 2 = 1 := Subtype.ext (by simpa using hz2)
    have hdV2 : (⟨c.d, hdV⟩ : ↥(V1 c.e)) ^ 2 = 1 := Subtype.ext (by simpa using hd2)
    have hzV1 : (⟨c.s.fr.z, hzV⟩ : ↥(V1 c.e)) ≠ 1 := by
      intro h
      exact hz1 (by simpa using congrArg Subtype.val h)
    have hdV1 : (⟨c.d, hdV⟩ : ↥(V1 c.e)) ≠ 1 := by
      intro h
      exact hd1 (by simpa using congrArg Subtype.val h)
    exact hzd (congrArg Subtype.val
      (y7c_eq_of_sq_eq_one_of_isCyclic hzV2 hdV2 hzV1 hdV1))

theorem y7c_conjSub_t_M3 (c : Ctx5 G L) (hH : F33Hyp c.s c.e) :
    conjSub c.s.t (M3 c.s) = M3 c.s := by
  have htR : c.s.t ∈ c.s.R := by
    rw [y5_R_eq hH]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers c.s.t)
  have hnorm : ∀ m ∈ M3 c.s, c.s.t * m * c.s.t⁻¹ ∈ M3 c.s :=
    y54_R_norm_M3 c hH c.s.t htR
  refine Subgroup.eq_of_le_of_card_ge (fun x hx => ?_) ?_
  · rw [conjSub, Subgroup.mem_map] at hx
    obtain ⟨y, hy, hxy⟩ := hx
    rw [← hxy]
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hnorm y hy
  · rw [conjSub, Subgroup.card_map_of_injective (f := (MulAut.conj c.s.t).toMonoidHom)
      (MulAut.conj c.s.t).injective]

theorem y7c_card_V1 (c : Ctx7 G L) (hH : F33Hyp c.s c.e) : Nat.card ↥(V1 c.e) = 4 := by
  obtain ⟨w, hwV, hzVc, hw1, hz1, hwz, hw2, hz2, hwz2, henum⟩ := f3_V_elems hH
  have hd2 : c.d ^ 2 = 1 := y5_d_sq c.toCtx5
  have hd1 : c.d ≠ 1 := by
    intro h
    have hdord : orderOf c.d = 2 := c.d_order
    rw [h, orderOf_one] at hdord
    norm_num at hdord
  have hzd : c.s.fr.z ≠ c.d := by
    intro h
    apply c.d_not_mem
    rw [zt, ← h]
    exact Subgroup.subset_closure (by simp)
  have hz' : c.s.fr.z * c.s.fr.z = 1 := by rw [← pow_two]; exact hz2
  have hd' : c.d * c.d = 1 := by rw [← pow_two]; exact hd2
  have hcomm : c.s.fr.z * c.d = c.d * c.s.fr.z := by
    have hdzc : c.d ∈ Subgroup.centralizer (c.s.fr.A : Set G) := by
      have h := c.d_mem
      simp only [C0, centIn, Subgroup.mem_inf] at h
      exact h.2
    exact Subgroup.mem_centralizer_iff.mp hdzc c.s.fr.z (s3_z_mem_A c.s)
  have hcl : closure ({c.s.fr.z, c.d} : Set G) =
      kleinFourOf c.s.fr.z c.d hz' hd' hcomm := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact left_mem_kleinFourOf
      · exact right_mem_kleinFourOf
    · exact kleinFourOf_le (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))
  rw [c.hV, hcl]
  exact card_kleinFourOf hz1 hd1 hzd

theorem y7c_V1_comm_P (c : Ctx7 G L) (h5 : c.toCtx5.Facts5) (h75 : c.Fact75) :
    ∀ v ∈ V1 c.e, ∀ x ∈ P7 c.e, v * x = x * v := by
  have hV1M3 : V1 c.e ≤ M3 c.s := inf_le_right
  have hcommM3 : IsMulCommutative (M3 c.s) := by
    rcases h5.2.2.2.2.2.2 with ⟨-, hE⟩ | ⟨-, hMC, -, -⟩
    · exact hE.1
    · exact hMC
  have hcommV1 : ∀ a ∈ V1 c.e, ∀ b ∈ V1 c.e, a * b = b * a := by
    haveI : IsMulCommutative ↥(M3 c.s) := hcommM3
    intro a ha b hb
    exact Subgroup.mul_comm_of_mem_isMulCommutative (M3 c.s) (hV1M3 ha) (hV1M3 hb)
  have hV1M4 : V1 c.e ≤ M4 c.e := by
    intro v hv
    have hv0 : v ∈ C0 c.e := (Subgroup.mem_inf.mp hv).1
    simp only [M4, centIn, Subgroup.mem_inf]
    exact ⟨h5.2.2.2.2.1.2.1 hv0, by
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      exact hcommV1 w hw v hv⟩
  have hV1V2 : V1 c.e ≤ V2 c.e := by
    rw [V2]
    exact le_inf hV1M3 hV1M4
  have hM6cent : M6 c.e ≤ Subgroup.centralizer (V1 c.e : Set G) := by
    intro x hx
    simp only [M6, centIn, Subgroup.mem_inf] at hx
    exact hx.2
  have hM7cent : M7 c.s ≤ Subgroup.centralizer (V1 c.e : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hv2 : v ∈ V2 c.e := hV1V2 hv
    have hvc : v ∈ cen (M7 c.s) := h75.2.1.2.2 hv2
    simp only [cen, Subgroup.mem_inf] at hvc
    exact (Subgroup.mem_centralizer_iff.mp hvc.2 x hx).symm
  have hPcent : P7 c.e ≤ Subgroup.centralizer (V1 c.e : Set G) := by
    rw [P7]
    exact sup_le hM6cent hM7cent
  intro v hv x hx
  exact Subgroup.mem_centralizer_iff.mp (hPcent hx) v hv

end CFSG.OddStandard.HigherRank.YamadaG23
