module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6Endgame
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6Datum
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6FactsGroup

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin A6Facts

theorem lemma2525 : Lemma2525 := by
  intro G _ _ T M hs N t zK h
  have hf := h.facts2511
  have hK0 : N.K0 = N.K := h.concl2520
  have hKH : N.H ≤ Subgroup.normalizer (N.K : Set G) := by
    rw [← hK0]; exact N.H_le_normalizer_K0
  have h254 := h.facts254
  have h258 := h.facts258
  have htx : N.x⁻¹ * t * N.x = t * N.z := h.concl2513.1.2 N.x N.x_mem N.x_not_mem
  by_contra hcon
  have hzK : N.z = zK := by
    rcases N.z_cases h254 hf with hz | hz
    · exact hz
    · exfalso
      apply hcon
      refine ⟨?_, hz⟩
      rw [htx, hz, ← mul_assoc, hf.t_mul_t, one_mul]
  have hxz : N.x⁻¹ * N.z * N.x = N.z := by
    have hc : N.x * N.z = N.z * N.x :=
      Subgroup.mem_centralizer_iff.mp N.tuple.z_mem.2 N.x N.x_mem.1
    calc N.x⁻¹ * N.z * N.x = N.x⁻¹ * (N.z * N.x) := mul_assoc _ _ _
      _ = N.x⁻¹ * (N.x * N.z) := by rw [hc]
      _ = N.z := inv_mul_cancel_left _ _
  have hS2 : IsPGroup 2 ↥N.S := N.tuple.sylow.isPGroup
  have hSKx : N.SK ⊓ CFSG.conjugate N.SC N.x = ⊥ :=
    N.SK_inf_conjugate_SC hK0 hKH h254 h258 hf hzK
  have hcomm : ∀ a ∈ N.SK, ∀ b ∈ CFSG.conjugate N.SC N.x, a * b = b * a := by
    intro a ha b hb
    have haS : a ∈ N.S := N.SK_le_S ha
    have hbS : b ∈ N.S := h.concl255.2.1 hb
    have h1 : b * a⁻¹ * b⁻¹ ∈ N.SK :=
      Subgroup.le_normalizer_iff.mp (N.S_le_normalizer_SK hKH) b hbS a⁻¹ (N.SK.inv_mem ha)
    have h2 : a * b * a⁻¹ ∈ CFSG.conjugate N.SC N.x :=
      Subgroup.le_normalizer_iff.mp N.S_le_normalizer_conjugate_SC a haS b hb
    have h3 : a * b * a⁻¹ * b⁻¹ ∈ N.SK ⊓ CFSG.conjugate N.SC N.x := by
      refine ⟨?_, ?_⟩
      · have := N.SK.mul_mem ha h1
        simpa [mul_assoc] using this
      · exact (CFSG.conjugate N.SC N.x).mul_mem h2 ((CFSG.conjugate N.SC N.x).inv_mem hb)
    rw [hSKx, Subgroup.mem_bot] at h3
    calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
      _ = b * a := by rw [h3, one_mul]
  obtain ⟨D⟩ := exists_a6Datum N hKH h258 h.concl2521
  have hsq : ∀ b ∈ CFSG.conjugate N.SC N.x, b * b = 1 := by
    intro b hb
    have hbS : b ∈ N.S := h.concl255.2.1 hb
    have hbH := N.S_le_H hbS
    have hcentD : ∀ d ∈ P0, d ∈ A6Models.psl29 → D.Φ b * d = d * D.Φ b := by
      intro d hdP hdpsl
      obtain ⟨a, haSK, rfl⟩ := D.exists_mem_SK hKH h254 h258.simple hdP hdpsl
      have haH := N.S_le_H (N.SK_le_S haSK)
      have h1 := hcomm a haSK b hb
      calc D.Φ b * D.Φ a = D.Φ (b * a) := (D.mul b hbH a haH).symm
        _ = D.Φ (a * b) := by rw [h1]
        _ = D.Φ a * D.Φ b := D.mul a haH b hbH
    have hsqΦ : D.Φ b * D.Φ b = 1 := P0_sq_of_centralizes_D (D.S_mem b hbS) hcentD
    have hbb : D.Φ (b * b) = 1 := by rw [D.mul b hbH b hbH, hsqΦ]
    have hbbS : b * b ∈ N.S := N.S.mul_mem hbS hbS
    have hbbSC : b * b ∈ N.SC := D.mem_SC_of_Φ_eq_one hK0 hbbS hbb
    have hbbX : b * b ∈ CFSG.conjugate N.SC N.x := (CFSG.conjugate N.SC N.x).mul_mem hb hb
    have h3 : b * b ∈ N.SC ⊓ CFSG.conjugate N.SC N.x := ⟨hbbSC, hbbX⟩
    rw [h.concl255.1, Subgroup.mem_bot] at h3
    exact h3
  have hSCsq : ∀ a : ↥N.SC, a * a = 1 := by
    intro a
    have hmem : N.x⁻¹ * (a : G) * N.x ∈ CFSG.conjugate N.SC N.x := by
      rw [mem_conjugate_iff]
      have e : N.x * (N.x⁻¹ * (a : G) * N.x) * N.x⁻¹ = a := by group
      rw [e]; exact a.2
    have h1 := hsq _ hmem
    apply Subtype.ext
    have e : (a : G) * a = N.x * ((N.x⁻¹ * (a : G) * N.x) * (N.x⁻¹ * (a : G) * N.x)) * N.x⁻¹ := by
      group
    simp only [Subgroup.coe_mul, Subgroup.coe_one]
    rw [e, h1]
    group
  have : Fact (IsPGroup 2 ↥N.SC) := ⟨hS2.to_le N.SC_le_S⟩
  exact h.concl2524 (frattini_eq_bot_of_exponent_two (fun a b => comm_of_exponent_two hSCsq a b)
    (fun y => by rw [sq]; exact hSCsq y))

end CFSG.QuasithinUnique
