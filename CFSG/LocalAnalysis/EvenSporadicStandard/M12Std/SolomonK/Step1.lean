module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.SolomonK.BasicSylow
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.SolomonK.SelfNormalizing
public import CFSG.CGT.Timmesfeld75.Fusion

public section

namespace CFSG.EvenSporadicStandard.M12Std.SolomonK

open Subgroup CFSG.CGT.Timmesfeld75

variable {K : Type} [Group K] [Finite K]

theorem GoodE.weaklyClosed (hP : P12Facts) (hK : SolomonA12HypK K) {E : Subgroup K}
    (hE : GoodE E) {U : Subgroup K} (hU : IsPGroup 2 U) (hEU : E ≤ U) :
    WeaklyClosedIn E U := by
  refine ⟨hEU, fun g hg => ?_⟩
  obtain ⟨S, hUS⟩ := hU.exists_le_sylow
  exact GoodE.conj_eq_of_le hP hK hE (hEU.trans hUS) (hg.trans hUS)

theorem GoodE.le_of_normal_isPGroup (hP : P12Facts) (hK : SolomonA12HypK K) {E : Subgroup K}
    (hE : GoodE E) {Q : Subgroup K} (hQ : Q.Normal) (hQ2 : IsPGroup 2 Q) : Q ≤ E := by
  by_contra hQE
  haveI : Q.Normal := hQ
  obtain ⟨S, hES⟩ := hE.isPGroup.exists_le_sylow
  have hQS : Q ≤ S := IsPGroup.le_sylow_of_normal hQ2 S
  set N : Subgroup K := normalizer (E : Set K) with hN
  set T : Subgroup K := Q ⊔ E with hT
  have hQT : Q ≤ T := by rw [hT]; exact le_sup_left
  have hET : E ≤ T := by rw [hT]; exact le_sup_right
  have hT2 : IsPGroup 2 T := (S.isPGroup').to_le (by rw [hT]; exact sup_le hQS hES)
  set M : Subgroup K := (Q ⊓ N) ⊔ E with hM
  have hEM : E ≤ M := by rw [hM]; exact le_sup_right
  have hMN : M ≤ N := by
    rw [hM]
    exact sup_le inf_le_right (by rw [hN]; exact Subgroup.le_normalizer)
  have hMT : M ≤ T := by
    rw [hM, hT]
    exact sup_le (inf_le_left.trans le_sup_left) le_sup_right
  have hM2 : IsPGroup 2 M := hT2.to_le hMT
  have hNM : N ≤ normalizer (M : Set K) := by
    have hNQ : N ≤ normalizer (Q : Set K) := by
      rw [hN, Subgroup.normalizer_eq_top (H := Q)]
      exact le_top
    have hNN : N ≤ normalizer (N : Set K) := Subgroup.le_normalizer
    have hNQN : N ≤ normalizer (Q ⊓ N : Subgroup K) :=
      (le_inf hNQ hNN).trans (inf_normalizer_le_normalizer_inf (H := Q) (K := N))
    have h1 := (le_inf hNQN hN.le).trans (inf_normalizer_le_normalizer_sup (Q ⊓ N) E)
    rwa [← hM] at h1
  have hMnorm : ∀ g ∈ normalizer (E : Set K), ∀ m ∈ M, g * m * g⁻¹ ∈ M := by
    intro g hg m hm
    exact Subgroup.le_normalizer_iff.mp hNM g (by rwa [← hN] at hg) m hm
  have hME : M = E := hE.eq_of_isPGroup hEM hMN hMnorm hM2
  have hQNE : Q ⊓ N ≤ E := by
    have h1 : Q ⊓ N ≤ M := by rw [hM]; exact le_sup_left
    rwa [hME] at h1
  haveI : Group.IsNilpotent ↥T := IsPGroup.isNilpotent hT2
  have hnc : NormalizerCondition ↥T := Group.normalizerCondition_of_isNilpotent
  set H : Subgroup ↥T := E.subgroupOf T with hH
  have hHtop : H ≠ ⊤ := by
    intro htop
    apply hQE
    rw [hH] at htop
    exact hQT.trans (Subgroup.subgroupOf_eq_top.mp htop)
  have hHlt : H < ⊤ := lt_top_iff_ne_top.mpr hHtop
  obtain ⟨x, hxnorm, hxH⟩ := (SetLike.lt_iff_le_and_exists.mp (hnc H hHlt)).2
  have hxmem : ∀ e ∈ E, (x : K) * e * (x : K)⁻¹ ∈ E := by
    intro e he
    have hH' : (⟨e, hET he⟩ : ↥T) ∈ H := by
      rw [hH, Subgroup.mem_subgroupOf]
      exact he
    have hx' : x * (⟨e, hET he⟩ : ↥T) * x⁻¹ ∈ H :=
      (Subgroup.mem_normalizer_iff.mp hxnorm (⟨e, hET he⟩ : ↥T)).mp hH'
    rw [hH, Subgroup.mem_subgroupOf] at hx'
    simpa using hx'
  have hxN : (x : K) ∈ N := by
    rw [hN, mem_normalizer_iff_conjSubgroup_eq]
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · intro y hy
      have hy' : (x : K)⁻¹ * y * (x : K) ∈ E :=
        (mem_conjSubgroup (g := (x : K)) (T := E)).mp hy
      have hmem := hxmem ((x : K)⁻¹ * y * (x : K)) hy'
      have heq : (x : K) * ((x : K)⁻¹ * y * (x : K)) * (x : K)⁻¹ = y := by group
      rwa [heq] at hmem
    · rw [conjSubgroup, Subgroup.card_map_of_injective (MulAut.conj (x : K)).injective]
  have hxT' : (x : K) ∈ Q ⊔ E := x.2
  obtain ⟨q, hqQ, e, heE, hqe⟩ :=
    (Subgroup.mem_sup_of_normal_left (s := Q) (t := E) (x := (x : K))).mp hxT'
  have heN : e ∈ N := by rw [hN]; exact Subgroup.le_normalizer heE
  have hqN : q ∈ N := by
    have hq : q = (x : K) * e⁻¹ := by rw [← hqe]; group
    rw [hq]
    exact N.mul_mem hxN (N.inv_mem heN)
  have hqE : q ∈ E := hQNE ⟨hqQ, hqN⟩
  have hxE : (x : K) ∈ E := by
    rw [← hqe]
    exact E.mul_mem hqE heE
  exact hxH (by rw [hH, Subgroup.mem_subgroupOf]; exact hxE)

theorem eq_bot_of_normal_isPGroup (hP : P12Facts) (hK : SolomonA12HypK K) {Q : Subgroup K}
    (hQ : Q.Normal) (hQ2 : IsPGroup 2 Q) : Q = ⊥ := by
  haveI : Q.Normal := hQ
  obtain ⟨E, hE⟩ := hK.exists_goodE
  have hQE : Q ≤ E := hE.le_of_normal_isPGroup hP hK hQ hQ2
  set N : Subgroup K := normalizer (E : Set K) with hN
  set C : Subgroup K := Subgroup.centralizer (Q : Set K) with hC
  have hCnormal : C.Normal := inferInstance
  haveI : C.Normal := hCnormal
  have hEC : E ≤ C := by
    intro e he
    rw [hC, Subgroup.mem_centralizer_iff]
    intro q hq
    exact hE.comm q (hQE hq) e he
  set M : Subgroup K := C ⊓ N with hM
  have hEM : E ≤ M := by
    rw [hM]
    exact le_inf hEC (by rw [hN]; exact Subgroup.le_normalizer)
  have hMN : M ≤ normalizer (E : Set K) := by
    rw [hM]
    exact inf_le_right.trans hN.le
  have hNM : N ≤ normalizer (M : Set K) := by
    have hNC : N ≤ normalizer (C : Set K) := by
      rw [hN, Subgroup.normalizer_eq_top (H := C)]
      exact le_top
    have hNN : N ≤ normalizer (N : Set K) := Subgroup.le_normalizer
    have h1 := (le_inf hNC hNN).trans (inf_normalizer_le_normalizer_inf (H := C) (K := N))
    rwa [← hM] at h1
  have hMnorm : ∀ g ∈ normalizer (E : Set K), ∀ m ∈ M, g * m * g⁻¹ ∈ M := by
    intro g hg m hm
    exact Subgroup.le_normalizer_iff.mp hNM g (by rwa [← hN] at hg) m hm
  rcases hE.eq_or_eq hEM hMN hMnorm with hME | hMN'
  · exfalso
    have hCE : C = E := by
      refine eq_of_normalizer_le hK.fusionSimple.1 hCnormal hEC hE.isPGroup hE.comm ?_
      intro g hgC hgN
      have hgN' : g ∈ N := by rwa [← hN] at hgN
      have hgM : g ∈ M := by rw [hM]; exact ⟨hgC, hgN'⟩
      rwa [hME] at hgM
    exact hE.not_normal (hCE ▸ hCnormal)
  · have hM_eq_N : M = N := by rw [hN]; exact hMN'
    have hNleC : N ≤ C := by
      rw [← hM_eq_N, hM]
      exact inf_le_left
    have hcenter : Q ≤ center K := by
      intro x hx
      rw [Subgroup.mem_center_iff]
      intro g
      have hxE : x ∈ E := hQE hx
      have hyQ : g⁻¹ * x * g ∈ Q := hQ.conj_mem' x hx g
      have hyE : g⁻¹ * x * g ∈ E := hQE hyQ
      obtain ⟨h, hhN, hhconj⟩ :=
        normalizer_controls_fusion_of_weaklyClosedIn_pGroup hE.isPGroup
          (fun U hU hEU => hE.weaklyClosed hP hK hU hEU)
          (hE.comm x hxE) (hE.comm (g⁻¹ * x * g) hyE) rfl
      have hhC : h ∈ C := hNleC hhN
      have hhC' : h ∈ Subgroup.centralizer (Q : Set K) := by rwa [hC] at hhC
      have hhx : x * h = h * x := Subgroup.mem_centralizer_iff.mp hhC' x hx
      have hxh : h⁻¹ * x * h = x := by
        rw [mul_assoc, hhx, ← mul_assoc, inv_mul_cancel, one_mul]
      have hgconj : g⁻¹ * x * g = x := hhconj.symm.trans hxh
      have hgx : x * g = g * x := by
        calc x * g = g * (g⁻¹ * x * g) := by group
          _ = g * x := by rw [hgconj]
      exact hgx.symm
    have hbot : Q ≤ ⊥ := by rwa [hK.fusionSimple.2.1] at hcenter
    exact le_antisymm hbot bot_le

end CFSG.EvenSporadicStandard.M12Std.SolomonK
