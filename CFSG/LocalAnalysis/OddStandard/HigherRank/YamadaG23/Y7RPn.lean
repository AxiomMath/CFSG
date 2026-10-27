module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7S1
public import CFSG.Quasithin.Background.E1Defs

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

section Aux

private lemma map_conj_eq_of_mem_conj {H : Subgroup G} {t : G} (ht : t * t = 1)
    (h : ∀ x ∈ H, t * x * t⁻¹ ∈ H) : H.map (MulAut.conj t) = H := by
  apply le_antisymm
  · rintro x ⟨y, hy, rfl⟩
    change t * y * t⁻¹ ∈ H
    exact h y hy
  · intro x hx
    refine Subgroup.mem_map.mpr ⟨t * x * t⁻¹, h x hx, ?_⟩
    change t * (t * x * t⁻¹) * t⁻¹ = x
    have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
    rw [ht']
    calc t * (t * x * t) * t = (t * t) * x * (t * t) := by group
      _ = x := by rw [ht]; simp

private lemma map_conj_eq_of_comm {H : Subgroup G} {t : G}
    (h : ∀ x ∈ H, t * x = x * t) : H.map (MulAut.conj t) = H := by
  apply le_antisymm
  · rintro x ⟨y, hy, rfl⟩
    change t * y * t⁻¹ ∈ H
    have hy' : t * y * t⁻¹ = y := by rw [h y hy]; group
    rw [hy']
    exact hy
  · intro x hx
    refine Subgroup.mem_map.mpr ⟨x, hx, ?_⟩
    change t * x * t⁻¹ = x
    rw [h x hx]
    group

private lemma conj_mem_pCoreOf {p : ℕ} {H : Subgroup G} {g n : G} (hg : g ∈ H)
    (hn : n ∈ pCoreOf p H) : g * n * g⁻¹ ∈ pCoreOf p H := by
  rcases Subgroup.mem_map.mp hn with ⟨n', hn', rfl⟩
  refine Subgroup.mem_map.mpr ⟨⟨g, hg⟩ * n' * ⟨g, hg⟩⁻¹, ?_, rfl⟩
  exact (inferInstance : (CFSG.pCore p H).Normal).conj_mem n' hn' ⟨g, hg⟩

end Aux

theorem Ctx7.t_mem_normalizer_P7 (c : Ctx7 G L) (h53 : c.toCtx5.Fact53) (h71 : c.Fact71) :
    c.s.t ∈ normalizer (P7 c.e : Set G) := by
  obtain ⟨⟨_hN_C0, hN_C0_le_N_V1⟩, ⟨hN_C1, _hHM6, _hAT, _hCom, _hQuot⟩,
      ⟨hC6, _hM3M6, _hM4M6⟩⟩ := h71
  obtain ⟨_hN_At, hNAd_le_NC0, _hJr⟩ := h53
  have ht2 : c.s.t * c.s.t = 1 := by
    have h : c.s.t ^ 2 = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one, c.s.t_order]
    simpa [pow_two] using h
  have htinv : c.s.t⁻¹ = c.s.t := inv_eq_of_mul_eq_one_right ht2
  have hLcomm : ∀ x ∈ L, c.s.t * x = x * c.s.t := fun x hx =>
    (Subgroup.mem_centralizer_iff.mp c.s.t_mem x hx).symm
  have hC6_le_K : C6 c.e ≤ normalizer (C1 c.e : Set G) := by
    simp only [C6, pCoreOf]
    exact Subgroup.map_subtype_le _
  have htC6 : c.s.t ∈ C6 c.e := by
    rw [hC6]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers c.s.t)
  have htK : c.s.t ∈ normalizer (C1 c.e : Set G) := hC6_le_K htC6
  have hNA_le_NV1 : normIn c.s.H c.s.fr.A ≤ normalizer (V1 c.e : Set G) :=
    calc normIn c.s.H c.s.fr.A
        ≤ normIn c.s.H c.s.fr.A ⊔ zpowers c.d := le_sup_left
      _ ≤ normalizer (C0 c.e : Set G) := hNAd_le_NC0
      _ ≤ normalizer (V1 c.e : Set G) := hN_C0_le_N_V1
  have hM6_le_NV1 : M6 c.e ≤ normalizer (V1 c.e : Set G) := by
    simp only [M6, centIn]
    exact le_trans inf_le_right (Subgroup.centralizer_le_normalizer (V1 c.e : Set G))
  have hNC1_le_NV1 : normalizer (C1 c.e : Set G) ≤ normalizer (V1 c.e : Set G) := by
    rw [hN_C1]
    exact sup_le hNA_le_NV1 hM6_le_NV1
  have ht_NV1 : c.s.t ∈ normalizer (V1 c.e : Set G) := hNC1_le_NV1 htK
  have hM6_conj : ∀ m ∈ M6 c.e, c.s.t * m * c.s.t⁻¹ ∈ M6 c.e := by
    intro m hm
    simp only [M6, centIn, Subgroup.mem_inf] at hm ⊢
    obtain ⟨hmC6, hmC⟩ := hm
    refine ⟨conj_mem_pCoreOf htK hmC6, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hw : c.s.t⁻¹ * v * c.s.t ∈ V1 c.e := by
      have h1 : c.s.t * v * c.s.t⁻¹ ∈ V1 c.e :=
        (Subgroup.mem_normalizer_iff.mp ht_NV1 v).mp hv
      simpa only [htinv] using h1
    have hmw : (c.s.t⁻¹ * v * c.s.t) * m = m * (c.s.t⁻¹ * v * c.s.t) :=
      Subgroup.mem_centralizer_iff.mp hmC _ hw
    calc v * (c.s.t * m * c.s.t⁻¹)
        = c.s.t * ((c.s.t⁻¹ * v * c.s.t) * m) * c.s.t⁻¹ := by group
      _ = c.s.t * (m * (c.s.t⁻¹ * v * c.s.t)) * c.s.t⁻¹ := by rw [hmw]
      _ = (c.s.t * m * c.s.t⁻¹) * v := by group
  have hM6map : (M6 c.e).map (MulAut.conj c.s.t) = M6 c.e :=
    map_conj_eq_of_mem_conj ht2 hM6_conj
  have hB_le_S : c.s.fr.B ≤ c.s.fr.S := by
    simp only [SFrame.B, centIn]
    exact inf_le_left
  have hF_le_S : c.s.fr.F ≤ c.s.fr.S := by
    simp only [SFrame.F]
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact mul_mem (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
    · exact mul_mem (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
    · rw [SFrame.z]
      exact pow_mem (Subgroup.subset_closure (by simp)) 2
  have hB_le_L : c.s.fr.B ≤ L := le_trans hB_le_S c.s.sylow_S.1
  have hF_le_L : c.s.fr.F ≤ L := le_trans hF_le_S c.s.sylow_S.1
  have hB_map : (c.s.fr.B).map (MulAut.conj c.s.t) = c.s.fr.B :=
    map_conj_eq_of_comm (fun x hx => hLcomm x (hB_le_L hx))
  have hF_map : (c.s.fr.F).map (MulAut.conj c.s.t) = c.s.fr.F :=
    map_conj_eq_of_comm (fun x hx => hLcomm x (hF_le_L hx))
  have hnormLB_map : (normIn L c.s.fr.B).map (MulAut.conj c.s.t) = normIn L c.s.fr.B :=
    map_conj_eq_of_comm (fun x hx => hLcomm x hx.1)
  have hnormLF_map : (normIn L c.s.fr.F).map (MulAut.conj c.s.t) = normIn L c.s.fr.F :=
    map_conj_eq_of_comm (fun x hx => hLcomm x hx.1)
  have htC3 : c.s.t ∈ C3 c.s := by
    simp only [C3]
    exact Subgroup.mem_sup_right (Subgroup.mem_sup_right (Subgroup.mem_zpowers c.s.t))
  have htC7 : c.s.t ∈ C7 c.s := by
    simp only [C7]
    exact Subgroup.mem_sup_right (Subgroup.mem_sup_right htC3)
  have hC3_map : (C3 c.s).map (MulAut.conj c.s.t) = C3 c.s :=
    map_conj_eq_of_mem_conj ht2 fun x hx =>
      (C3 c.s).mul_mem ((C3 c.s).mul_mem htC3 hx) ((C3 c.s).inv_mem htC3)
  have hC7_map : (C7 c.s).map (MulAut.conj c.s.t) = C7 c.s :=
    map_conj_eq_of_mem_conj ht2 fun x hx =>
      (C7 c.s).mul_mem ((C7 c.s).mul_mem htC7 hx) ((C7 c.s).inv_mem htC7)
  have hM3_map : (M3 c.s).map (MulAut.conj c.s.t) = M3 c.s := by
    simp only [M3]
    rw [Subgroup.map_sup, Subgroup.map_commutator, hC3_map, hnormLF_map, hF_map]
  have hM7_map : (M7 c.s).map (MulAut.conj c.s.t) = M7 c.s := by
    simp only [M7]
    rw [Subgroup.map_sup, Subgroup.map_commutator, hC7_map, hnormLB_map, Subgroup.map_sup,
      hB_map, hM3_map]
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  simp only [P7]
  rw [Subgroup.map_sup, hM6map, hM7_map]

end CFSG.OddStandard.HigherRank.YamadaG23
