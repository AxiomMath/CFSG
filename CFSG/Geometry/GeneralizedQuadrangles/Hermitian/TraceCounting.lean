module

public import CFSG.Geometry.GeneralizedQuadrangles.Hermitian.Triads

public section

namespace CFSG.Geometry.GeneralizedQuadrangles

open SimpleGraph CFSG.Geometry.GeneralizedPolygons

universe u

variable {V : Type u} {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj]
  {c : Γ.Coloring (Fin 2)} {q : ℕ}

theorem ncard_traceSet_inter_neighborSet_le_of_not_mem_span
    (hΓ : IsThasQuadrangle Γ c q) {a b h : V} (ha : c a = 0) (hab : Γ.dist a b = 4)
    (hh : c h = 0) (hspan : h ∉ spanSet Γ a b) :
    {u | u ∈ traceSet Γ a b ∧ Γ.dist h u = 2}.ncard ≤ q + 1 := by
  classical
  have hP : IsGeneralizedPolygon Γ 4 := hΓ.gp
  have hT : IsThick Γ := hΓ.thick
  by_cases hcl : h ∈ clSet Γ a b
  ·
    obtain ⟨w, hwspan, hhwle⟩ := hcl
    have hwh : h ≠ w := by
      intro heq
      exact hspan (heq ▸ hwspan)
    have hw0 : c w = 0 := (color_eq_of_mem_span hP hT c hab hwspan).trans ha
    have hhw : Γ.dist h w = 2 := by
      have heven : Even (Γ.dist h w) := (hP.eq_iff_even_dist c h w).1 (by rw [hh, hw0])
      have hne : Γ.dist h w ≠ 0 := by
        intro h0
        exact hwh ((hP.connected.dist_eq_zero_iff).mp h0)
      obtain ⟨k, hk⟩ := heven
      omega
    have hsub : {u | u ∈ traceSet Γ a b ∧ Γ.dist h u = 2} ⊆
        Γ.neighborSet (commonNeighbor hP hhw) := by
      intro u hu
      obtain ⟨huT, hhu⟩ := hu
      have huw : Γ.dist u w = 2 := by
        rw [SimpleGraph.dist_comm]
        exact dist_eq_two_of_mem_span_of_mem_trace hP hT hab hwspan huT
      obtain ⟨m, hm, -⟩ :=
        existsUnique_commonNeighbor_of_pairwise_dist_two hP hhu hhw huw
      have hm_eq : m = commonNeighbor hP hhw :=
        (existsUnique_commonNeighbor hP hhw).unique ⟨hm.1, hm.2.2⟩
          ⟨commonNeighbor_adj_left hP hhw, commonNeighbor_adj_right hP hhw⟩
      rw [mem_neighborSet, ← hm_eq]
      exact hm.2.1.symm
    have hle1 : (traceSet Γ a b ∩ Γ.neighborSet (commonNeighbor hP hhw)).ncard ≤ 1 := by
      rw [Set.ncard_le_one]
      intro u hu u' hu'
      by_contra hne
      have h4 : Γ.dist u u' = 4 := dist_eq_four_of_mem_trace hP hab hu.1 hu'.1 hne
      have h2 : Γ.dist u u' = 2 :=
        dist_eq_two_of_adj_of_adj_of_ne hP hu.2.symm hu'.2 hne
      omega
    calc {u | u ∈ traceSet Γ a b ∧ Γ.dist h u = 2}.ncard
        ≤ (traceSet Γ a b ∩ Γ.neighborSet (commonNeighbor hP hhw)).ncard :=
          Set.ncard_le_ncard (fun u hu => ⟨hu.1, hsub hu⟩)
      _ ≤ 1 := hle1
      _ ≤ q + 1 := by omega
  ·
    have hah : Γ.dist a h = 4 := by
      have hgt : 2 < Γ.dist h a := by
        by_contra hle
        exact hcl ⟨a, left_mem_spanSet hab, by omega⟩
      have heven : Even (Γ.dist h a) := (hP.eq_iff_even_dist c h a).1 (by rw [hh, ha])
      have hle : Γ.dist h a ≤ 4 := hP.dist_le (by norm_num) h a
      rw [SimpleGraph.dist_comm]
      obtain ⟨k, hk⟩ := heven
      omega
    have hbh : Γ.dist b h = 4 := by
      have hgt : 2 < Γ.dist h b := by
        by_contra hle
        exact hcl ⟨b, right_mem_spanSet hab, by omega⟩
      have hb0 : c b = 0 := by
        have h := (hP.eq_iff_even_dist c b a).2 (by
          rw [SimpleGraph.dist_comm, hab]; exact ⟨2, rfl⟩)
        rwa [h]
      have heven : Even (Γ.dist h b) := (hP.eq_iff_even_dist c h b).1 (by rw [hh, hb0])
      have hle : Γ.dist h b ≤ 4 := hP.dist_le (by norm_num) h b
      rw [SimpleGraph.dist_comm]
      obtain ⟨k, hk⟩ := heven
      omega
    have hset : {u | u ∈ traceSet Γ a b ∧ Γ.dist h u = 2} = centreSet Γ a b h := by
      ext u
      simp [centreSet, and_assoc]
    rw [hset]
    exact le_of_eq (ncard_centreSet hΓ ha hab hah hbh hcl)

theorem mem_spanSet_of_ncard_traceSet_inter_neighborSet
    (hΓ : IsThasQuadrangle Γ c q) {a b h : V} (ha : c a = 0) (hab : Γ.dist a b = 4)
    (hh : c h = 0)
    (hcard : q + 1 < {u | u ∈ traceSet Γ a b ∧ Γ.dist h u = 2}.ncard) :
    h ∈ spanSet Γ a b := by
  by_contra hspan
  exact absurd (ncard_traceSet_inter_neighborSet_le_of_not_mem_span hΓ ha hab hh hspan)
    (by omega)

end CFSG.Geometry.GeneralizedQuadrangles
