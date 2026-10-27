module

public import CFSG.ClassicalInvolution.Asc77.AscT7ERCase
public import CFSG.ClassicalInvolution.Asc77.AscT7DRFive
public import CFSG.ClassicalInvolution.Asc77.AscT7ERConj

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

variable (p f : ℕ) [Fact p.Prime]

theorem c25_1_proved : C25_1 p f := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp g hg x hx hx4
  have hs : Hyp23Setting p f Ω K K' z := hyp.std.setting
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  have hJ : conjSub g⁻¹ K ∈ Ω := hΩ.conjInvariant g⁻¹ K hK
  have hJz : IsUniqueInvolution (conjSub g⁻¹ K) (g⁻¹ * z * g⁻¹⁻¹) := hs.hz.conj g⁻¹
  have hne : g⁻¹ * z * g⁻¹⁻¹ ≠ z := by
    intro h
    apply hyp.ht.2.1
    rw [← hg]
    calc g * z * g⁻¹ = g * (g⁻¹ * z * g⁻¹⁻¹) * g⁻¹ := by rw [h]
      _ = z := by group
  exact fun h => T7ER.not_commute_of_orderOf_four hs hyp.hW hyp.hE4 hJ
    (T7ER.not_mem_twinSet_of_ne hs.hz hJz hne) hx hx4 h.symm

theorem c25_2_t_proved : C25_2_t p f := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp
  have hs : Hyp23Setting p f Ω K K' z := hyp.std.setting
  have hst : AscStand p f Ω K := hs.stand
  have hp : p ≠ 2 := hst.odd
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  have hK : K ∈ Ω := hst.mem
  have hK' : K' ∈ Ω := hs.hK'.1
  have hKK' : K' ≠ K := hs.hne
  have hRsyl : IsSylow2In R K := T7C.isSylow2In_of_mem_RSet_of_le hp hΩ hK hyp.hR.1 hyp.hR.2.1
  have hRS : R ≤ (S : Subgroup G) := hyp.hR.2.2
  obtain ⟨htS, htz, g, hg⟩ := hyp.ht
  have hmem : conjSub t R ∈ RSet Ω := RSet.conj hΩ.conjInvariant hyp.hR.1 t
  have hle : conjSub t R ≤ (S : Subgroup G) := by
    intro x hx
    rw [mem_conjSub_iff] at hx
    have h1 : t * (t⁻¹ * x * t) * t⁻¹ ∈ (S : Subgroup G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ htS (hRS hx)) (Subgroup.inv_mem _ htS)
    simpa [mul_assoc] using h1
  rcases hyp.hRS _ hmem hle with hRt | hRt
  · obtain ⟨s', hs'2, hs'z, ⟨y, hy⟩, hs'K⟩ := T7ER.exists_notNormalizing_conj hyp hg hRt
    obtain ⟨c, hcz, hcS⟩ := T7ER.exists_conj_mem_sylow_of_centralizes S hyp.hzS hs'2 hs'z
    refine ⟨c⁻¹ * s' * c, hcS, ⟨c⁻¹ * y, ?_⟩, ?_⟩
    · calc c⁻¹ * y * z * (c⁻¹ * y)⁻¹ = c⁻¹ * (y * z * y⁻¹) * c := by group
        _ = c⁻¹ * s' * c := by rw [hy]
    · have hmem' : conjSub (c⁻¹ * s' * c) R ∈ RSet Ω :=
        RSet.conj hΩ.conjInvariant hyp.hR.1 _
      have hle' : conjSub (c⁻¹ * s' * c) R ≤ (S : Subgroup G) := by
        intro x hx
        rw [mem_conjSub_iff] at hx
        have h1 : (c⁻¹ * s' * c) * ((c⁻¹ * s' * c)⁻¹ * x * (c⁻¹ * s' * c)) * (c⁻¹ * s' * c)⁻¹ ∈
            (S : Subgroup G) :=
          Subgroup.mul_mem _ (Subgroup.mul_mem _ hcS (hRS hx)) (Subgroup.inv_mem _ hcS)
        simpa [mul_assoc] using h1
      rcases hyp.hRS _ hmem' hle' with h | h
      · exfalso
        have hKt : conjSub (c⁻¹ * s' * c) K = K := by
          by_contra hne
          have hK2 : conjSub (c⁻¹ * s' * c) K ∈ Ω := hΩ.conjInvariant _ K hK
          have hRK : R ≤ conjSub (c⁻¹ * s' * c) K := h ▸ conjSub_mono hRsyl.1
          have := hΩ.card_le_two_of_le_inf hK hK2 (Ne.symm hne) hRsyl.2.1 hRsyl.1 hRK
          have h8 := (hΩ.isQuatSub_of_mem_RSet hp hyp.hR.1).eight_le
          omega
        have h1 : conjSub s' (conjSub c K) = conjSub c K := by
          have h2 : conjSub (c * (c⁻¹ * s' * c)) K = conjSub (s' * c) K := by
            congr 1; group
          rw [conjSub_mul, hKt, conjSub_mul] at h2
          exact h2.symm
        rcases T7ER.conjSub_eq_of_centralizes hs hcz with h3 | h3
        · rw [h3] at h1
          exact hs'K h1
        · rw [h3] at h1
          exact hs'K ((T7ER.normalizes_iff_of_centralizes hs hs'z).mpr h1)
      · exact h
  · exact ⟨t, htS, ⟨g, hg⟩, hRt⟩

end CFSG.ClassicalInvolution.Asc77
