module

public import CFSG.GroupTheory.WeirSylow.Orthogonal
import CFSG.LocalAnalysis.AGLEmbeddingD2.CyclicSylowGL
import CFSG.RankThree.PartOne.Q1327T.R8Homo

public section

namespace CFSG.AGLEmbeddingD2.HeisSpinPlus

open Module QuadraticMap CFSG.GroupTheory.WeirSylow CFSG.Assembly.LowTwoRank
  CFSG.AGLEmbeddingD2.CyclicSylowGL

theorem weirE_five_eq_four [Fact (Nat.Prime 5)] {K : Type} [Field K] [Fintype K] {f : ℕ}
    (hf : Odd f) (hK : Fintype.card K = 2 ^ f) : weirE 5 K = 4 := by
  have hdvd : ∀ j : ℕ, weirE 5 K ∣ j ↔ 4 ∣ j := fun j => by
    have h1 := dvd_pow_sub_one_iff_weirE (p := 5) (K := K) j
    have hpos : 1 ≤ Fintype.card K ^ j := Nat.one_le_pow _ _ Fintype.card_pos
    have h2 : ((Fintype.card K ^ j - 1 : ℕ) : ℤ) = (Fintype.card K : ℤ) ^ j - 1 := by
      rw [Nat.cast_sub hpos, Nat.cast_pow, Nat.cast_one]
    rw [← h2, Int.natCast_dvd_natCast, five_dvd_pow_sub_one_iff hK j] at h1
    rw [← h1]
    obtain ⟨a, rfl⟩ := hf
    constructor
    · intro h
      have hc : Nat.Coprime 4 (2 * a + 1) := by
        rw [show (4 : ℕ) = 2 ^ 2 from rfl]
        exact Nat.Coprime.pow_left 2 (by simp)
      exact hc.dvd_of_dvd_mul_left h
    · intro h
      exact Dvd.dvd.mul_left h _
  exact Nat.dvd_antisymm ((hdvd 4).2 dvd_rfl) ((hdvd _).1 dvd_rfl)

theorem isMulCommutative_of_isPGroup_five_orthogonal {K : Type} [Field K] [Finite K] {f : ℕ}
    (hf : Odd f) (hK : Nat.card K = 2 ^ f) {V : Type} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (hdim : finrank K V = 2 * 10) (Q : QuadraticForm K V)
    (hQ : (polarBilin Q).Nondegenerate) (hplus : IsPlusType Q)
    (P : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)) (hP : IsPGroup 5 P) :
    IsMulCommutative P := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hp1 : Odd 5 := ⟨2, rfl⟩
  have hKc : Fintype.card K = 2 ^ f := by rw [Fintype.card_eq_nat_card, hK]
  have hpK : ¬ 5 ∣ Fintype.card K := by rw [hKc]; exact not_five_dvd_two_pow f
  have hE : weirE 5 K = 4 := weirE_five_eq_four hf hKc
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun g : V ≃ₗ[K] V => (g : V → V))
    fun g h hgh => LinearEquiv.ext (congrFun hgh)
  obtain ⟨S, hPS⟩ := hP.exists_le_sylow
  obtain ⟨-, h2, -⟩ := sylow_orthogonal_even hp1 hpK (n := 10) (by norm_num) hdim Q hQ (ε := 1)
    (Or.inl ⟨rfl, hplus⟩) S
  have hnd : ¬ (5 : ℤ) ∣ (Fintype.card K : ℤ) ^ 10 - 1 := by
    have h := dvd_pow_sub_one_iff_weirE (p := 5) (K := K) 10
    rw [hE] at h
    exact fun hh => by
      have := h.1 hh
      omega
  obtain ⟨P'⟩ : Nonempty (Sylow 5 (StatedSp (10 - 1) K)) := inferInstance
  obtain ⟨φ⟩ := h2 (by simpa using hnd) P'
  obtain ⟨ψ⟩ := sylow_Sp hp1 K hpK (10 - 1) P'
  obtain ⟨χ⟩ := CFSG.RankThree.PartOne.Q1327T.R8.nonempty_sigmaModel_mulEquiv_homo (p := 5)
    (e := weirE 5 K) (a := weirA 5 K) (N := if Even (weirE 5 K) then 2 * (10 - 1) else 10 - 1)
    (by rw [hE]; norm_num)
  let ε' := φ.trans (ψ.trans χ)
  refine ⟨⟨fun a b => ?_⟩⟩
  have hab : (⟨a.1, hPS a.2⟩ : (S : Subgroup _)) * ⟨b.1, hPS b.2⟩ =
      ⟨b.1, hPS b.2⟩ * ⟨a.1, hPS a.2⟩ :=
    ε'.injective (by rw [map_mul, map_mul]; exact mul_comm _ _)
  have hab' : a.1 * b.1 = b.1 * a.1 := congrArg Subtype.val hab
  exact Subtype.ext hab'

end CFSG.AGLEmbeddingD2.HeisSpinPlus
