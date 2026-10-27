module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisSigH
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisP313b

public noncomputable section

namespace CFSG.ComponentClassification.GHarris

open CFSG CFSG.Open Subgroup SCert CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G]

namespace GHSylow

variable (D : GHSylow G)

omit [Finite G]
  in
theorem toG_invRep_zero : D.toG (SE.invRep 0) = D.z :=
  congrArg D.toG (show SE.invRep 0 = SE.gen 0 by decide)

theorem centralizer_rep_V_le_H (hC : GorensteinHaradaThmCInput) (h10 : D.FusN 1 0)
    (h20 : D.FusN 2 0) {i : Fin 9} (hi : i = 0 ∨ i = 1 ∨ i = 2) :
    centralizer ({D.toG (SE.invRep i)} : Set G) ≤ normalizer (sigW D.V : Set G) := by
  refine D.centralizer_V_le_H hC h10 h20 ?_ ?_
  · rcases hi with rfl | rfl | rfl
    · rw [D.toG_invRep_zero]; exact D.z_mem_V
    · exact D.t_mem_V
    · exact D.a1l_mem_V
  · rcases hi with rfl | rfl | rfl
    · rw [D.toG_invRep_zero]; exact D.z_ne_one
    · exact D.t_ne_one
    · exact fun h => absurd (D.toG_eq_one_iff.mp h) (by decide)

theorem centralizer_t_le_H (hC : GorensteinHaradaThmCInput) (h10 : D.FusN 1 0)
    (h20 : D.FusN 2 0) : centralizer ({D.t} : Set G) ≤ normalizer (sigW D.V : Set G) :=
  D.centralizer_rep_V_le_H hC h10 h20 (i := 1) (Or.inr (Or.inl rfl))

theorem centralizer_z_le_H (hC : GorensteinHaradaThmCInput) (h10 : D.FusN 1 0)
    (h20 : D.FusN 2 0) : centralizer ({D.z} : Set G) ≤ normalizer (sigW D.V : Set G) :=
  D.M_le_H hC h10 h20

theorem centralizer_repA_le_H (hC : GorensteinHaradaThmCInput)
    (hidx : ∀ N : Subgroup G, N.Normal → N.index ≠ 2) (hxa : ¬ ∃ g : G, g⁻¹ * D.x * g = D.a)
    (hA : ¬ D.caseB) {i : Fin 9} (hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 7) :
    centralizer ({D.toG (SE.invRep i)} : Set G) ≤ normalizer (sigW D.V : Set G) := by
  obtain ⟨hP, -, n, hna, hnt, -⟩ := D.fusion_A hC hidx hxa hA
  have h10 : D.FusN 1 0 := hP 1 (by decide)
  have h20 : D.FusN 2 0 := hP 2 (by decide)
  have hMH : D.M ≤ normalizer (sigW D.V : Set G) := D.M_le_H hC h10 h20
  have hnH : n ∈ normalizer (sigW D.V : Set G) :=
    D.centralizer_t_le_H hC h10 h20 (mem_centralizer_singleton_iff.mpr (by
      calc n * D.t = n * (n⁻¹ * D.t * n) := by rw [hnt]
        _ = D.t * n := by group))
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
  · exact D.centralizer_rep_V_le_H hC h10 h20 (Or.inl rfl)
  · exact D.centralizer_rep_V_le_H hC h10 h20 (Or.inr (Or.inl rfl))
  · exact D.centralizer_rep_V_le_H hC h10 h20 (Or.inr (Or.inr rfl))
  · obtain ⟨m, hm, hmt⟩ := D.conj_t_invRep_A hC hA (i := 3) (Or.inr (Or.inl rfl))
    have h := centralizer_le_of_conj (inv_mem (hMH hm)) (D.centralizer_t_le_H hC h10 h20)
    rwa [inv_inv, hmt] at h
  · obtain ⟨m, hm, hmt⟩ := D.conj_t_invRep_A hC hA (i := 4) (Or.inr (Or.inr rfl))
    have h := centralizer_le_of_conj (inv_mem (hMH hm)) (D.centralizer_t_le_H hC h10 h20)
    rwa [inv_inv, hmt] at h
  · have h := centralizer_le_of_conj hnH (D.centralizer_z_le_H hC h10 h20)
    rwa [← hna, show n * (n⁻¹ * D.a * n) * n⁻¹ = D.a by group] at h

theorem H_eq_top_A (hC : GorensteinHaradaThmCInput)
    (hidx : ∀ N : Subgroup G, N.Normal → N.index ≠ 2) (hxa : ¬ ∃ g : G, g⁻¹ * D.x * g = D.a)
    (hA : ¬ D.caseB)
    (hN : centralizer ({D.x} : Set G) ≤ normalizer (sigW D.V : Set G)) :
    normalizer (sigW D.V : Set G) = ⊤ := by
  obtain ⟨hP, ⟨gy, hgyM, hgy⟩, n, -, hnt, -, s₁, hs₁, s₂, hs₂, hedge⟩ :=
    D.fusion_A hC hidx hxa hA
  have h10 : D.FusN 1 0 := hP 1 (by decide)
  have h20 : D.FusN 2 0 := hP 2 (by decide)
  set H := normalizer (sigW D.V : Set G) with hH
  have hMH : D.M ≤ H := D.M_le_H hC h10 h20
  have hSH : (D.S : Subgroup G) ≤ H := D.S_le_M.trans hMH
  have hnH : n ∈ H := D.centralizer_t_le_H hC h10 h20 (mem_centralizer_singleton_iff.mpr (by
    calc n * D.t = n * (n⁻¹ * D.t * n) := by rw [hnt]
      _ = D.t * n := by group))
  refine D.eq_top_of_centralizer_le hSH fun u hu hu2 hu1 =>
    D.centralizer_le_of_reps hSH ?_ hu hu2 hu1
  intro i
  fin_cases i
  · exact D.centralizer_repA_le_H hC hidx hxa hA (Or.inl rfl)
  · exact D.centralizer_repA_le_H hC hidx hxa hA (Or.inr (Or.inl rfl))
  · exact D.centralizer_repA_le_H hC hidx hxa hA (Or.inr (Or.inr (Or.inl rfl)))
  · exact D.centralizer_repA_le_H hC hidx hxa hA (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact D.centralizer_repA_le_H hC hidx hxa hA
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  · exact hN
  · have h := centralizer_le_of_conj (hMH hgyM) hN
    rwa [← hgy, show gy * (gy⁻¹ * D.y * gy) * gy⁻¹ = D.y by group] at h
  · exact D.centralizer_repA_le_H hC hidx hxa hA
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
  · have hk : s₂ * n⁻¹ * s₁⁻¹ ∈ H :=
      mul_mem (mul_mem (hSH hs₂) (inv_mem hnH)) (inv_mem (hSH hs₁))
    have h := centralizer_le_of_conj hk hN
    have e : s₂ * n⁻¹ * s₁⁻¹ * D.x * (s₂ * n⁻¹ * s₁⁻¹)⁻¹ = D.al := by
      calc s₂ * n⁻¹ * s₁⁻¹ * D.x * (s₂ * n⁻¹ * s₁⁻¹)⁻¹ =
          s₂ * (n⁻¹ * (s₁⁻¹ * D.x * s₁) * n) * s₂⁻¹ := by group
        _ = D.al := by rw [hedge]; group
    rwa [e] at h

theorem mem_normalizer_klein_zt {n : G} (hnt : n⁻¹ * D.t * n = D.z)
    (hnz : n⁻¹ * D.z * n = D.t ∨ n⁻¹ * D.z * n = D.t * D.z) :
    n ∈ normalizer (klein D.z D.t D.t_mul_t D.z_comm_t : Set G) := by
  set B := klein D.z D.t D.t_mul_t D.z_comm_t with hB
  have hle : B.map (MulAut.conj n⁻¹).toMonoidHom ≤ B := by
    rw [map_le_iff_le_comap]
    refine klein_le ?_ ?_
    · change n⁻¹ * D.z * n⁻¹⁻¹ ∈ B
      rw [inv_inv]
      rcases hnz with h | h <;> rw [h]
      · exact mem_klein_right
      · exact mul_mem mem_klein_right mem_klein_left
    · change n⁻¹ * D.t * n⁻¹⁻¹ ∈ B
      rw [inv_inv, hnt]
      exact mem_klein_left
  have heq : B.map (MulAut.conj n⁻¹).toMonoidHom = B :=
    eq_of_le_of_card_ge hle (by
      rw [card_map_of_injective (f := (MulAut.conj n⁻¹).toMonoidHom) (MulAut.conj n⁻¹).injective])
  have hmem : n⁻¹ ∈ normalizer (B : Set G) := by
    rw [mem_normalizer_iff_map_conj_eq, ← MulEquiv.toMonoidHom_eq_coe]
    exact heq
  simpa using inv_mem hmem

theorem H_eq_top_B (hC : GorensteinHaradaThmCInput)
    (hidx : ∀ N : Subgroup G, N.Normal → N.index ≠ 2) (hxa : ¬ ∃ g : G, g⁻¹ * D.x * g = D.a)
    (hB : D.caseB)
    (hN : centralizer ({D.x} : Set G) ≤ normalizer (sigW D.V : Set G))
    (hK : centralizer ({D.a3a4} : Set G) ≤ normalizer (sigW D.V : Set G)) :
    normalizer (sigW D.V : Set G) = ⊤ := by
  obtain ⟨hP, -, -, -, ⟨gy, hgyM, hgy⟩, ⟨g₁, hg₁M, hg₁⟩, -, -, n, hna, hnt, hnz, s₁, hs₁, s₂,
    hs₂, hedge⟩ := D.fusion_B hC hidx hxa hB
  have h10 : D.FusN 1 0 := hP 1 (by decide)
  have h20 : D.FusN 2 0 := hP 2 (by decide)
  set H := normalizer (sigW D.V : Set G) with hH
  have hMH : D.M ≤ H := D.M_le_H hC h10 h20
  have hSH : (D.S : Subgroup G) ≤ H := D.S_le_M.trans hMH
  have hBV : klein D.z D.t D.t_mul_t D.z_comm_t ≤ D.V := klein_le D.z_mem_V D.t_mem_V
  have hB4 : 4 ≤ Nat.card (klein D.z D.t D.t_mul_t D.z_comm_t) :=
    (card_klein D.z_mul_z D.z_ne_one D.t_ne_one D.z_ne_t.symm).ge
  have hnH : n ∈ H := D.normalizer_le_H hC h10 h20 hBV hB4 (D.mem_normalizer_klein_zt hnt hnz)
  refine D.eq_top_of_centralizer_le hSH fun u hu hu2 hu1 =>
    D.centralizer_le_of_reps hSH ?_ hu hu2 hu1
  intro i
  fin_cases i
  · exact D.centralizer_rep_V_le_H hC h10 h20 (Or.inl rfl)
  · exact D.centralizer_rep_V_le_H hC h10 h20 (Or.inr (Or.inl rfl))
  · exact D.centralizer_rep_V_le_H hC h10 h20 (Or.inr (Or.inr rfl))
  · exact hK
  · have h := centralizer_le_of_conj (hMH hg₁M) hK
    rwa [← hg₁, show g₁ * (g₁⁻¹ * D.a1a4 * g₁) * g₁⁻¹ = D.a1a4 by group] at h
  · exact hN
  · have h := centralizer_le_of_conj (hMH hgyM) hN
    rwa [← hgy, show gy * (gy⁻¹ * D.y * gy) * gy⁻¹ = D.y by group] at h
  · have h := centralizer_le_of_conj hnH hK
    rwa [← hna, show n * (n⁻¹ * D.a * n) * n⁻¹ = D.a by group] at h
  · rcases hedge with hedge | hedge
    · have hk : s₂ * n⁻¹ * s₁⁻¹ ∈ H :=
        mul_mem (mul_mem (hSH hs₂) (inv_mem hnH)) (inv_mem (hSH hs₁))
      have h := centralizer_le_of_conj hk hN
      have e : s₂ * n⁻¹ * s₁⁻¹ * D.x * (s₂ * n⁻¹ * s₁⁻¹)⁻¹ = D.al := by
        calc s₂ * n⁻¹ * s₁⁻¹ * D.x * (s₂ * n⁻¹ * s₁⁻¹)⁻¹ =
            s₂ * (n⁻¹ * (s₁⁻¹ * D.x * s₁) * n) * s₂⁻¹ := by group
          _ = D.al := by rw [hedge]; group
      rwa [e] at h
    · have hk : s₁ * n * s₂⁻¹ ∈ H :=
        mul_mem (mul_mem (hSH hs₁) hnH) (inv_mem (hSH hs₂))
      have h := centralizer_le_of_conj hk hN
      have e : s₁ * n * s₂⁻¹ * D.x * (s₁ * n * s₂⁻¹)⁻¹ = D.al := by
        calc s₁ * n * s₂⁻¹ * D.x * (s₁ * n * s₂⁻¹)⁻¹ =
            s₁ * n * (s₂⁻¹ * D.x * s₂) * n⁻¹ * s₁⁻¹ := by group
          _ = D.al := by rw [← hedge]; group
      rwa [e] at h

end GHSylow

end CFSG.ComponentClassification.GHarris
