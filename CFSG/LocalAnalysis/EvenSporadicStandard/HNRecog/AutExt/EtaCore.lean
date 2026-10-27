module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.ML1.A5Facts
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.ML1.CoreSq
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.ML1.FibreSplit

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4.EtaGz

open CFSG.EvenSporadicStandard.HNRecog.ML1 CFSG.EvenSporadicStandard.HNRecog.Fpf

variable {L L' : Type} [Group L] [Group L'] [Finite L] [Finite L'] {N : Subgroup L}
  {N' : Subgroup L'} {θ : L →* A5 × A5} {θ' : L' →* A5 × A5} {ψ : A5 × A5 ≃* A5 × A5}
  {φ : L → L'} {z : L}

theorem exists_mulEquiv_of_coreHyp [N.Normal] (h : CoreHyp N N' θ θ' ψ φ z) :
    ∃ e : L ≃* L', ∀ l : L, θ' (e l) = ψ (θ l) := by
  classical
  let F : Subgroup (L × L') := fibre θ θ' ψ N φ
  haveI hFin : Finite ↥F :=
    Finite.of_injective (fun x : ↥F => (x : L × L')) Subtype.coe_injective
  haveI hΔnorm : (h.graph.subgroupOf F).Normal := h.graph_normal
  have hΔP : IsPGroup 2 ↥(h.graph.subgroupOf F) := h.isPGroup_graph
  let T : Subgroup ↥F := (default : Sylow 2 ↥F).toSubgroup
  have hΔT : h.graph.subgroupOf F ≤ T :=
    IsPGroup.le_sylow_of_normal hΔP (default : Sylow 2 ↥F)
  let c : ↥F := ⟨(z, (1 : L')), h.mem_fibre_z⟩
  have hc_sq : c ^ 2 = 1 := by
    apply Subtype.ext
    apply Prod.ext <;> simp [c, h.z_sq]
  have hcP : IsPGroup 2 ↥(Subgroup.zpowers c) := by
    refine IsPGroup.of_card_dvd_pow (n := 1) ?_
    rw [Nat.card_zpowers]
    simpa using orderOf_dvd_of_pow_eq_one hc_sq
  haveI hcnorm : (Subgroup.zpowers c).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_zpowers_iff] at hn ⊢
    obtain ⟨k, hk⟩ := hn
    refine ⟨k, ?_⟩
    rw [← hk]
    have hconj : MulAut.conj g c = c := by
      rw [MulAut.conj_apply]
      have hcomm : g * c = c * g := Subgroup.mem_center_iff.mp h.fibre_central g
      rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
    calc c ^ k = (MulAut.conj g c) ^ k := by rw [hconj]
      _ = MulAut.conj g (c ^ k) := (map_zpow (MulAut.conj g) c k).symm
      _ = g * c ^ k * g⁻¹ := by rw [MulAut.conj_apply]
  have hzT : c ∈ T := by
    have hle : Subgroup.zpowers c ≤ T :=
      IsPGroup.le_sylow_of_normal hcP (default : Sylow 2 ↥F)
    exact hle (Subgroup.mem_zpowers c)
  have hTodd : Odd T.index := by
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
    exact (default : Sylow 2 ↥F).not_dvd_index
  have hsq : ∀ t ∈ T, t ^ 2 ∈ h.graph.subgroupOf F := by
    intro t ht
    obtain ⟨k, hk⟩ := (default : Sylow 2 ↥F).isPGroup' ⟨t, ht⟩
    have hk₁ : t ^ (2 ^ k) = 1 := by
      have := congrArg (fun x : ↥T => (x : ↥F)) hk
      simpa using this
    have hk₂ : t.1 ^ (2 ^ k) = 1 := by
      have := congrArg (Subgroup.subtype F) hk₁
      simpa using this
    have hθk : θ t.1.1 ^ (2 ^ k) = 1 := by
      have := congrArg (fun p : L × L' => θ p.1) hk₂
      simpa using this
    have hθ2 : θ t.1.1 ^ 2 = 1 :=
      sq_eq_one_of_two_power (θ t.1.1) k hθk
    have hmem : t.1 ^ 2 ∈ h.graph := h.sq_mem_graph t.2 hθ2
    rw [Subgroup.mem_subgroupOf]
    simpa using hmem
  obtain ⟨e, he⟩ := exists_mulEquiv_of_fibre F z (φ z)
    h.mem_fibre_z h.mem_fibre_z'
    h.fibre_proj₁ h.fibre_proj₂
    h.fibre_kernel₁ h.fibre_kernel₂
    (h.graph.subgroupOf F) h.fibre_central h.z_not_mem_graph
    ⟨h.mem_fibre_zz', h.zz'_mem_graph⟩
    T hΔT hzT hTodd hsq
  exact ⟨e, fun l => ((mem_fibre_iff θ θ' ψ N φ l (e l)).1 (he l)).1⟩

end CFSG.EvenSporadicStandard.HNRecog.Section4.EtaGz
