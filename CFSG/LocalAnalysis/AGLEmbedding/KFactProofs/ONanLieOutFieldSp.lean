module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanLieOutFieldDefs
public import CFSG.RankThree.PartOne.S11d.FixedFactsPSp

public section

namespace CFSG.AGLEmbedding.LieOut

open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.Sec66T CFSG.RankThree.PartOne.FieldFix
open CFSG.Assembly.LowTwoRank (StatedLieAdmissible StatedClassicalModel StatedProj StatedSp)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  (spLinearAutGroup spSemilinearAutGroup)

theorem fixesNonLocalized_psp {T : Type} [Group T] [Finite T] {p n f : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (h : StatedClassicalModel T .PSp n 2 f) (hq : ¬ (n = 2 ∧ f = p))
    {α : MulAut T} (hαp : α ^ p = 1) (hαinn : α ∉ innerAut T) : FixesNonLocalized α := by
  have h0 := h
  have hf : 1 ≤ f := h.1.2.1
  have hn : 2 ≤ n := h.1.2.2.1
  have hp2 : p ≠ 2 := by omega
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have : Finite (StatedProj (StatedSp n K)) := Finite.of_equiv T e.toEquiv
  have hα'inn : MulAut.congr e α ∉ innerAut (StatedProj (StatedSp n K)) :=
    fun h => hαinn ((mem_innerAut_congr e α).mp h)
  have hα'p : MulAut.congr e α ^ p = 1 := by rw [← map_pow, hαp, map_one]
  have hα'ord : orderOf (MulAut.congr e α) = p :=
    orderOf_eq_prime hα'p (fun h1 => hα'inn (h1 ▸ (innerAut _).one_mem))
  obtain ⟨-, -, -, -, -, -, -, hidx, hrel, hdesc⟩ :=
    CFSG.RankThree.Classical.SteinbergBY.symplectic_prime_semilinear_field_descent
      Nat.prime_two hf hn hK
  have hE : MulAut.congr e α ∈ spSemilinearAutGroup n K := by
    have hidx' : (spSemilinearAutGroup n K).index ≤ 2 := Nat.le_of_dvd (by norm_num) hidx
    refine OutStructure.mem_of_pow_mem_of_index_le_two _ hidx' (hp.odd_of_ne_two hp2) ?_
    rw [hα'p]
    exact Subgroup.one_mem _
  have hD : MulAut.congr e α ∉ spLinearAutGroup n K := by
    intro hD
    have hcop : Nat.gcd 2 (2 ^ f - 1) = 1 := by
      have h1 : (2 : ℕ) ^ f % 2 = 0 := by
        obtain ⟨g, hg⟩ := Nat.exists_eq_add_of_le hf
        rw [hg, pow_add]
        simp
      have h2 : 1 ≤ (2 : ℕ) ^ f := Nat.one_le_two_pow
      exact Nat.coprime_two_left.mpr (by rw [Nat.odd_iff]; omega)
    rw [hcop, Nat.dvd_one] at hrel
    exact hα'inn (Subgroup.relIndex_eq_one.mp hrel hD)
  obtain ⟨hpf, -⟩ := hdesc p hp _ hE hD hα'ord
  obtain ⟨f₀, rfl⟩ := hpf
  have hf₀ : 1 ≤ f₀ := by
    rcases Nat.eq_zero_or_pos f₀ with h0 | h0
    · simp [h0] at hf
    · exact h0
  have hadm₀ : StatedLieAdmissible .PSp n 2 f₀ := by
    refine ⟨Nat.prime_two, hf₀, hn, fun hc => hq ⟨(Prod.mk.inj hc).1, ?_⟩⟩
    have h2 : 2 ^ f₀ = 2 := (Prod.mk.inj hc).2
    have : f₀ = 1 := by
      by_contra hne
      have : 2 ^ 2 ≤ 2 ^ f₀ := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    rw [this, mul_one]
  exact FixesNonLocalized.of_fixedFacts
    (fixedFacts_PSp hp hp5 ((lieModel_classical_iff (by decide)).mpr h0) hf₀ hadm₀ α hαp hαinn)

end CFSG.AGLEmbedding.LieOut
