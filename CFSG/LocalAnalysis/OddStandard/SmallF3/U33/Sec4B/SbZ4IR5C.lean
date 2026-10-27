module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4IR3C
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4IR5B
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4IZ4
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4IZ2B
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4IZ3C

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {X : Type} [Group X] [Finite X]

private lemma z4i_Y_inf_N {N Q Y V V' B K : Subgroup X} {ρ t τ l : X} [N.Normal]
    (h : Z4IData N Q Y V V' B K ρ t τ l) : Y ⊓ N = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  have hxQN : x ∈ Q ⊓ N := ⟨h.Y_le_Q hx.1, hx.2⟩
  rw [h.Q_inf_N] at hxQN
  exact hxQN

theorem Z4IData.exists_syl {N Q Y V V' B K : Subgroup X} {ρ t τ l : X} [N.Normal]
    (h : Z4IData N Q Y V V' B K ρ t τ l) :
    ∃ (P M : Subgroup X) (t' : X), IsPGroup 2 P ∧
      (∀ P'' : Subgroup X, IsPGroup 2 P'' → P ≤ P'' → P'' ≤ P) ∧ z4iQf P = Q ∧ M ≤ P ∧
      M.relIndex P = 2 ∧ t' ∈ P ∧ t' ∉ M ∧ t' * t' = 1 ∧ (∃ g : X, t' = g * t * g⁻¹) ∧
      ∀ u ∈ M, u * u = 1 →
        (∀ y ∈ Y, u * y = y * u) ∨ (∃ g : X, u = g * l * g⁻¹) ∨
          (∃ g : X, u = g * (τ * l) * g⁻¹) := by
  have hN : Odd (Nat.card N) := h.odd_N
  have hZ := h.toZEData
  obtain ⟨P, hP2, hQP, hPW, hmaxP⟩ :=
    z4i_exists_lift_max N hN h.isPGroup_Q hZ.Vc_pgroup hZ.Q_le_Vc
      (fun P'' hP'' hle => hZ.Vc_maximal hP'' hle)
  have hQf : z4iQf P = Q :=
    z4i_Qf_lift N hN hP2 hQP (by rw [hPW]; exact hZ.Qf_Vc)
  obtain ⟨M, hMP, hM2, hMW⟩ :=
    z4i_index_two_lift N hN hP2
      (M := z4iM (K.map (z4iπ N)) (z4iπ N τ) (z4iπ N l))
      (by rw [hPW]; exact hZ.M_le_Vc) (by rw [hPW]; exact hZ.M_relIndex)
  have hπtT3 : z4iπ N t ∈ z4iT3 (z4iπ N t) (z4iπ N τ) (z4iπ N l) :=
    ZEData.t_mem_T3 _ _ _
  have hπtV : z4iπ N t ∈ z4iVc (K.map (z4iπ N)) (z4iπ N t) (z4iπ N τ) (z4iπ N l) :=
    ZEData.T3_le_Vc (K.map (z4iπ N)) (z4iπ N t) (z4iπ N τ) (z4iπ N l) hπtT3
  rw [← hPW] at hπtV
  obtain ⟨t', ht'P, ht'π⟩ := Subgroup.mem_map.mp hπtV
  have ht'sq : t' * t' = 1 := by
    refine z4iπ_injOn N hN hP2 (P.mul_mem ht'P ht'P) P.one_mem ?_
    rw [map_mul, ht'π, ← map_mul, h.t_sq, map_one]
  have ht'1 : t' ≠ 1 := fun h1 =>
    (z4i_map_ne_one N hN h.t_sq h.t_ne_one) (by rw [← ht'π, h1, map_one])
  have ht'M : t' ∉ M := by
    intro ht'M
    apply hZ.t_not_mem_M
    have hmem : z4iπ N t ∈ M.map (z4iπ N) := by
      rw [← ht'π]
      exact Subgroup.mem_map_of_mem (z4iπ N) ht'M
    rwa [hMW] at hmem
  obtain ⟨g₀, hg₀⟩ := z4i_exists_conj_of_map_eq N hN ht'sq ht'1 h.t_sq ht'π
  have hinvol : ∀ u ∈ M, u * u = 1 →
      (∀ y ∈ Y, u * y = y * u) ∨ (∃ g : X, u = g * l * g⁻¹) ∨
        (∃ g : X, u = g * (τ * l) * g⁻¹) := by
    intro u huM hu2
    by_cases hu1 : u = 1
    · left
      intro y _
      rw [hu1]; group
    · have huMq : z4iπ N u ∈ z4iM (K.map (z4iπ N)) (z4iπ N τ) (z4iπ N l) := by
        rw [← hMW]
        exact Subgroup.mem_map_of_mem (z4iπ N) huM
      have hu2q : z4iπ N u * z4iπ N u = 1 := by
        rw [← map_mul, hu2, map_one]
      rcases hZ.invol_M huMq hu2q with hcent | hconj | hconj
      · left
        intro y hy
        exact z4i_commute_of_map N (Q := Y) (z4i_Y_inf_N h)
          (fun x hx => h.normal_Y u x hx) hy
          (hcent (z4iπ N y) (Subgroup.mem_map_of_mem (z4iπ N) hy))
      · right; left
        obtain ⟨wbar, hwbarK, hu_eq⟩ := hconj
        obtain ⟨w, hwK, hwbar_eq⟩ := Subgroup.mem_map.mp hwbarK
        have hb2 : (w * l * w⁻¹) * (w * l * w⁻¹) = 1 := by
          rw [show (w * l * w⁻¹) * (w * l * w⁻¹) = w * (l * l) * w⁻¹ by group,
            h.l_sq]
          group
        have hπb : z4iπ N u = z4iπ N (w * l * w⁻¹) := by
          rw [hu_eq, ← hwbar_eq]
          simp only [map_mul, map_inv]
        obtain ⟨g, hg⟩ := z4i_exists_conj_of_map_eq N hN hu2 hu1 hb2 hπb
        exact ⟨g * w, by rw [hg]; group⟩
      · right; right
        obtain ⟨wbar, hwbarK, hu_eq⟩ := hconj
        obtain ⟨w, hwK, hwbar_eq⟩ := Subgroup.mem_map.mp hwbarK
        have htaul2 : (τ * l) * (τ * l) = 1 := by
          calc (τ * l) * (τ * l) = τ * (l * τ) * l := by group
            _ = τ * (τ * l) * l := by rw [← h.tau_l]
            _ = (τ * τ) * (l * l) := by group
            _ = 1 := by rw [h.tau_sq, h.l_sq, one_mul]
        have hb2 : (w * (τ * l) * w⁻¹) * (w * (τ * l) * w⁻¹) = 1 := by
          rw [show (w * (τ * l) * w⁻¹) * (w * (τ * l) * w⁻¹) =
            w * ((τ * l) * (τ * l)) * w⁻¹ by group, htaul2]
          group
        have hπb : z4iπ N u = z4iπ N (w * (τ * l) * w⁻¹) := by
          rw [hu_eq, ← hwbar_eq]
          simp only [map_mul, map_inv]
        obtain ⟨g, hg⟩ := z4i_exists_conj_of_map_eq N hN hu2 hu1 hb2 hπb
        exact ⟨g * w, by rw [hg]; group⟩
  exact ⟨P, M, t', hP2, hmaxP, hQf, hMP, hM2, ht'P, ht'M, ht'sq, ⟨g₀, hg₀⟩, hinvol⟩

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
