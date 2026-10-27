module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.Elementary
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.NotationAPI

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin

theorem lemma2513 : Lemma2513 := by
  intro G _ _ T M hs N t zK h
  have hf := h.facts2511
  have hS : N.S ≤ T := N.S_le_T
  have hSt : N.S ≤ Subgroup.centralizer ({t} : Set G) := hf.sylow.le
  have ht1 : t ≠ 1 := hf.t_ne_one
  have ht2 : t * t = 1 := by have := hf.t_sq; rwa [sq] at this
  have hzT : N.z ∈ centerOf T := N.tuple.z_mem
  have hzS : N.z ∈ N.S := N.tuple.center_le hzT
  have hz2 : N.z * N.z = 1 := by have := N.tuple.z_sq; rwa [sq] at this
  have hzconj : ∀ y ∈ T, y⁻¹ * N.z * y = N.z := by
    intro y hy
    have hc : y * N.z = N.z * y := Subgroup.mem_centralizer_iff.mp hzT.2 y hy
    calc y⁻¹ * N.z * y = y⁻¹ * (N.z * y) := mul_assoc _ _ _
      _ = y⁻¹ * (y * N.z) := by rw [hc]
      _ = N.z := inv_mul_cancel_left _ _
  have hTC : T ⊓ Subgroup.centralizer ({t} : Set G) = N.S :=
    hf.sylow.eq_of_le (le_inf hS hSt) inf_le_right (hs.setting.isPGroup.to_le inf_le_left)
  have hmemS : ∀ y ∈ T, y * t = t * y → y ∈ N.S := by
    intro y hyT hyt
    rw [← hTC]
    exact ⟨hyT, Subgroup.mem_centralizer_singleton_iff.mpr hyt⟩
  have htZ : t ∈ centerOf N.S := by
    rw [hf.centerS_z]; exact Subgroup.subset_closure (Set.mem_insert _ _)
  have htS : t ∈ N.S := htZ.1
  have hcomm : t * N.z = N.z * t := (Subgroup.mem_centralizer_iff.mp htZ.2 N.z hzS).symm
  have hZs : ∀ w ∈ centerOf N.S, w = 1 ∨ w = t ∨ w = N.z ∨ w = t * N.z := by
    intro w hw
    rw [hf.centerS_z] at hw
    exact mem_closure_pair_of_involutions ht2 hz2 hcomm hw
  have hconj : ∀ y ∈ T ⊓ Subgroup.normalizer (N.S : Set G), y ∉ N.S →
      y⁻¹ * t * y = t * N.z := by
    intro y hy hyS
    have hyN := Subgroup.mem_normalizer_iff.mp hy.2
    have hmemZ : y⁻¹ * t * y ∈ centerOf N.S := by
      refine ⟨?_, Subgroup.mem_centralizer_iff.mpr fun s hs' => ?_⟩
      · have e : y * (y⁻¹ * t * y) * y⁻¹ = t := by group
        exact (hyN (y⁻¹ * t * y)).mpr (by rw [e]; exact htS)
      · have hs'' : y * s * y⁻¹ ∈ N.S := (hyN s).mp hs'
        have hc := Subgroup.mem_centralizer_iff.mp htZ.2 _ hs''
        calc s * (y⁻¹ * t * y) = y⁻¹ * ((y * s * y⁻¹) * t) * y := by group
          _ = y⁻¹ * (t * (y * s * y⁻¹)) * y := by rw [hc]
          _ = y⁻¹ * t * y * s := by group
    rcases hZs _ hmemZ with h1 | h1 | h1 | h1
    · exfalso
      apply ht1
      calc t = y * (y⁻¹ * t * y) * y⁻¹ := by group
        _ = 1 := by rw [h1]; group
    · exfalso
      refine hyS (hmemS y hy.1 ?_)
      calc y * t = y * (y⁻¹ * t * y) := by rw [h1]
        _ = t * y := by group
    · exfalso
      refine hf.not_conj y⁻¹ ?_
      rw [inv_inv, ← h1]
      group
    · exact h1
  have hNT : N.S ≤ T ⊓ Subgroup.normalizer (N.S : Set G) :=
    le_inf hS Subgroup.le_normalizer
  have hrel : N.S.relIndex (T ⊓ Subgroup.normalizer (N.S : Set G)) = 2 := by
    rw [Subgroup.relIndex_eq_two_iff]
    refine ⟨N.x, N.x_mem, fun b hb => ?_⟩
    by_cases hbS : b ∈ N.S
    · refine Or.inr ⟨hbS, fun hbx => N.x_not_mem ?_⟩
      have := N.S.mul_mem (N.S.inv_mem hbS) hbx
      simpa using this
    · refine Or.inl ⟨?_, hbS⟩
      have h1 := hconj b hb hbS
      have h2 := hconj N.x N.x_mem N.x_not_mem
      have h3 := hzconj N.x N.x_mem.1
      have h4 : (b * N.x)⁻¹ * t * (b * N.x) = t := by
        calc (b * N.x)⁻¹ * t * (b * N.x) = N.x⁻¹ * (b⁻¹ * t * b) * N.x := by group
          _ = N.x⁻¹ * (t * N.z) * N.x := by rw [h1]
          _ = (N.x⁻¹ * t * N.x) * (N.x⁻¹ * N.z * N.x) := by group
          _ = t * N.z * N.z := by rw [h2, h3]
          _ = t := by rw [mul_assoc, hz2, mul_one]
      refine hmemS _ (T.mul_mem hb.1 N.x_mem.1) ?_
      calc (b * N.x) * t = (b * N.x) * ((b * N.x)⁻¹ * t * (b * N.x)) := by rw [h4]
        _ = t * (b * N.x) := by group
  have hcard : Nat.card ↥(T ⊓ Subgroup.normalizer (N.S : Set G)) = 2 * Nat.card N.S := by
    have := Subgroup.relIndex_mul_card (H := N.S) (K := T ⊓ Subgroup.normalizer (N.S : Set G))
    rw [hrel, inf_eq_left.mpr hNT] at this
    exact this.symm
  have hzKZ : zK ∈ centerOf N.S := by
    rw [hf.centerS_zK]
    exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hzK1 : zK ≠ 1 := by
    intro h1
    refine h.facts254.z_not_mem ?_
    have := hf.zK_proj
    rwa [h1, inv_one, one_mul] at this
  have hzKt : zK ≠ t := by
    intro h1
    apply ht1
    have hK0 : t ∈ N.K0 := by rw [← h1]; exact hf.zK_mem
    have hmem : t ∈ N.K0 ⊓ N.SC := ⟨hK0, hf.t_mem⟩
    rw [h.facts258.K0_inf_SC] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hzKcases : zK = N.z ∨ zK = t * N.z := by
    rcases hZs zK hzKZ with h1 | h1 | h1 | h1
    · exact absurd h1 hzK1
    · exact absurd h1 hzKt
    · exact Or.inl h1
    · exact Or.inr h1
  refine ⟨⟨hcard, hconj⟩, ?_, ?_⟩
  ·
    intro hx
    rcases hzKcases with rfl | rfl
    · exact ⟨rfl, hconj N.x N.x_mem N.x_not_mem⟩
    · exfalso
      refine N.x_not_mem (hmemS N.x N.x_mem.1 ?_)
      have h3 := hzconj N.x N.x_mem.1
      have h4 : N.x⁻¹ * t * N.x = t := by
        have h5 : (N.x⁻¹ * t * N.x) * (N.x⁻¹ * N.z * N.x) = t * N.z := by
          calc (N.x⁻¹ * t * N.x) * (N.x⁻¹ * N.z * N.x) = N.x⁻¹ * (t * N.z) * N.x := by group
            _ = t * N.z := hx
        rw [h3] at h5
        exact mul_right_cancel h5
      calc N.x * t = N.x * (N.x⁻¹ * t * N.x) := by rw [h4]
        _ = t * N.x := by group
  ·
    rintro ⟨g, hg⟩
    rcases hzKcases with rfl | rfl
    · exact ⟨rfl, hconj N.x N.x_mem N.x_not_mem⟩
    · exfalso
      refine hf.not_conj g⁻¹ ?_
      have h1 : g⁻¹ * t * g = N.z := by
        rw [hg, ← mul_assoc, ht2, one_mul]
      rw [inv_inv, ← h1]
      group

end CFSG.QuasithinUnique
