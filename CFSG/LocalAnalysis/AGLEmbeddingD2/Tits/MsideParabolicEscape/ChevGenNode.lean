module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGenCentre

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGen

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.Steinberg
  CFSG.AGLEmbedding.ParabHub

theorem card_sl2_field {F : Type} [Field F] [Finite F] :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) = Nat.card F * (Nat.card F ^ 2 - 1) := by
  haveI := Fintype.ofFinite F
  have h := Matrix.card_SL_field (𝔽 := F) 2
  rw [Fintype.card_eq_nat_card] at h
  rw [h, Fin.prod_univ_two]
  have hq : 2 ≤ Nat.card F := by
    have := Finite.one_lt_card (α := F)
    omega
  obtain ⟨k, hk⟩ : ∃ k, Nat.card F = k + 2 := ⟨Nat.card F - 2, by omega⟩
  rw [hk]
  have e1 : (k + 2) ^ 2 - (k + 2) ^ (0 : ℕ) = (k + 1) * (k + 3) := by
    apply Nat.sub_eq_of_eq_add; simp; ring
  have e2 : (k + 2) ^ 2 - (k + 2) ^ ((1 : Fin 2) : ℕ) = (k + 2) * (k + 1) := by
    apply Nat.sub_eq_of_eq_add; simp; ring
  have e3 : (k + 2) ^ 2 - 1 = (k + 1) * (k + 3) := by
    apply Nat.sub_eq_of_eq_add; ring
  rw [show (((0 : Fin 2) : ℕ)) = 0 from rfl, e1, e2, e3, show k + 2 - 1 = k + 1 from rfl]
  rw [show (k + 1) * (k + 3) * ((k + 2) * (k + 1)) = ((k + 2) * ((k + 1) * (k + 3))) * (k + 1) by
    ring]
  exact Nat.mul_div_cancel _ (by omega)

theorem exists_order_inverted_sl2 {F : Type} [Field F] [Finite F] [CharP F 2] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpd : p ∣ Nat.card F ^ 2 - 1) :
    ∃ w n : Matrix.SpecialLinearGroup (Fin 2) F, w ^ p = 1 ∧ w ≠ 1 ∧ n * w * n⁻¹ = w⁻¹ := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcard : p ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) := by
    rw [card_sl2_field]
    exact hpd.mul_left _
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' p hcard
  have hw1 : w ≠ 1 := fun h => by
    rw [h, orderOf_one] at hw
    exact hp.one_lt.ne' hw.symm
  obtain ⟨n, -, hn⟩ := exists_involution_inverting w
  exact ⟨w, n, by rw [← hw]; exact pow_orderOf_eq_one w, hw1, hn⟩

theorem oddNode_of_hasSL2Node {K : Type} [Group K] {D : UniversalRootDatum K} {i : Fin D.rank}
    {F : Type} [Field F] [Finite F] [CharP F 2] (h : HasSL2Node D i F) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpd : p ∣ Nat.card F ^ 2 - 1) : OddNode (rankOne D.rootGroup i) p := by
  obtain ⟨φ, hφ, hu, hl⟩ := h
  obtain ⟨w, n, hw, hw1, hn⟩ := exists_order_inverted_sl2 (F := F) hp hp2 hpd
  have hmem : ∀ A : Matrix.SpecialLinearGroup (Fin 2) F, φ A ∈ rankOne D.rootGroup i := by
    intro A
    have hle : Subgroup.closure (Set.range (sl2Upper (k := F)) ∪ Set.range sl2Lower) ≤
        (rankOne D.rootGroup i).comap φ := by
      rw [Subgroup.closure_le]
      rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
      · exact Subgroup.mem_sup_left (hu c)
      · exact Subgroup.mem_sup_right (hl c)
    exact hle (CFSG.LieType.Steinberg.Sp.mem_closure_sl2 A)
  refine ⟨φ w, hmem w, φ n, hmem n, by rw [← map_pow, hw, map_one],
    fun h1 => hw1 (hφ (by rw [h1, map_one])), ?_⟩
  simpa [map_mul, map_inv] using congrArg φ hn

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGen
