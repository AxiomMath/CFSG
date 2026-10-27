module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.LieChar
public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoAutCard
import CFSG.Dihedral.Glauberman.DicksonMaxUp
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSmallReeTorus

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbedding CFSG.ComponentClassification.OuterAutomorphisms

theorem kFactLinTwoPrimeRank : KFactLinTwoPrimeRank := by
  intro K _ _ d ⟨e⟩ p hp _ ⟨q, hqp, hq1, hd⟩
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨e'⟩ :=
    nonempty_mulEquiv_psl2GF_of_isLinTwoIndex (p := p) (n := 1) ⟨q, hd, hqp, hq1⟩
  obtain ⟨E, -, hE, hEcard⟩ := pRank_attained p hp (⊤ : Subgroup K)
  obtain ⟨S, hES⟩ := (show IsPGroup p E from fun x =>
    ⟨1, Subtype.ext (by simpa using hE.2 x x.2)⟩).exists_le_sylow
  obtain ⟨T⟩ : Nonempty (Sylow p (PSL2GF p 1)) := inferInstance
  have hS : Nat.card S = p := by
    rw [S.card_eq_multiplicity, Nat.card_congr (e.trans e').toEquiv, ← T.card_eq_multiplicity,
      (psl2GF_sylow p 1 le_rfl T).2, pow_one]
  have hle : p ^ Open.pRank p (⊤ : Subgroup K) ≤ p ^ 1 := by
    rw [← hEcard, pow_one, ← hS]
    exact Subgroup.card_le_of_le hES
  exact (Nat.pow_le_pow_iff_right hp.one_lt).mp hle

theorem not_dvd_card_outer_of_linTwo {K : Type} [Group K] [Finite K] {p n : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hn : 1 ≤ n) (hn2 : n ≤ 2) (hq : 4 ≤ p ^ n) (e : K ≃* PSL2GF p n) :
    ¬ p ∣ Nat.card (Outer K) := by
  have hp : p.Prime := Fact.out
  rw [Nat.card_congr (equivalence e).toEquiv]
  have hF : Nat.card (GaloisField p n) = p ^ n := GaloisField.card p n (by omega)
  have h2 : Nat.card (GaloisField p n) ≠ 2 := by omega
  have h3 : Nat.card (GaloisField p n) ≠ 3 := by omega
  have : IsSimpleGroup (PSL2GF p n) :=
    CFSG.ComponentClassification.CatalogueBGeneralLinear.projectiveSpecialLinear_simple 2 _
      le_rfl (Or.inr h2) (Or.inr h3)
  have hcenter : Subgroup.center (PSL2GF p n) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (PSL2GF p n)) with h | h
    · exact h
    · exfalso
      obtain ⟨x, y, hxy⟩ :=
        ComponentClassification.CatalogueBSmallRee.projectiveSpecialLinear_two_nonabelian _ h2 h3
      exact hxy (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top x) y).symm
  have hinj : Function.Injective (MulAut.conj : PSL2GF p n →* MulAut (PSL2GF p n)) := by
    intro a b hab
    have hc : b⁻¹ * a ∈ Subgroup.center (PSL2GF p n) := by
      rw [Subgroup.mem_center_iff]
      intro x
      have hx := congrArg (fun φ : MulAut (PSL2GF p n) => φ x) hab
      simp only [MulAut.conj_apply] at hx
      calc x * (b⁻¹ * a) = b⁻¹ * (b * x * b⁻¹) * b * b⁻¹ * a := by group
        _ = b⁻¹ * (a * x * a⁻¹) * b * b⁻¹ * a := by rw [hx]
        _ = b⁻¹ * a * x := by group
    rw [hcenter, Subgroup.mem_bot, inv_mul_eq_one] at hc
    exact hc.symm
  have hinner : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.inner (PSL2GF p n)) =
      Nat.card (PSL2GF p n) := by
    rw [CFSG.ComponentClassification.OuterAutomorphisms.inner, MonoidHom.range_eq_map,
      Subgroup.card_map_of_injective hinj, Subgroup.card_top]
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (CFSG.ComponentClassification.OuterAutomorphisms.inner (PSL2GF p n))
  rw [card_mulAut_psl2GF p n hn, hinner,
    CFSG.Glauberman.Dickson.MaxUp.card_psl2_galoisField hp2 (by omega)] at hcard
  have hodd : Odd (p ^ (2 * n)) := (hp.odd_of_ne_two hp2).pow
  have heven : Even (p ^ n * (p ^ (2 * n) - 1)) :=
    (Nat.Odd.sub_odd hodd odd_one).mul_left _
  have hhalf := Nat.two_mul_div_two_of_even heven
  have hpos : 0 < p ^ n * (p ^ (2 * n) - 1) / 2 := by
    have h1 : 1 < p ^ (2 * n) := Nat.one_lt_pow (by omega) hp.one_lt
    have h2' : 0 < p ^ n * (p ^ (2 * n) - 1) := Nat.mul_pos (pow_pos hp.pos n) (by omega)
    omega
  have hout : Nat.card (Outer (PSL2GF p n)) = 2 * n := by
    have hsq : (p ^ n) ^ 2 = p ^ (2 * n) := by rw [← pow_mul, mul_comm]
    rw [hsq] at hcard
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [← hcard]
    calc p ^ n * (p ^ (2 * n) - 1) * n = 2 * (p ^ n * (p ^ (2 * n) - 1) / 2) * n := by
          rw [hhalf]
      _ = 2 * n * (p ^ n * (p ^ (2 * n) - 1) / 2) := by ring
  rw [hout]
  intro hdvd
  have hle := Nat.le_of_dvd (by omega) hdvd
  interval_cases n
  · have : p ≤ 2 := by omega
    exact hp2 (le_antisymm this hp.two_le)
  · have h4 : p ∣ 2 ^ 2 := by simpa using hdvd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h4))

@[expose] def KFactLinThreeOut : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (d : TauCeti.ValidLieTypeIndex),
    Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group) → ∀ p : ℕ, p.Prime → p ≠ 2 →
    (∃ q : TauCeti.PrimePower, q.p = p ∧ q.exponent = 1 ∧ d.1 = .A 2 q) →
    ¬ p ∣ Nat.card (Outer K)

@[expose] def KFactUnitaryThreeOut : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (d : TauCeti.ValidLieTypeIndex),
    Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group) → ∀ p : ℕ, p.Prime → p ≠ 2 →
    (∃ q : TauCeti.PrimePower, q.p = p ∧ q.exponent = 1 ∧ d.1 = .twistedA 2 q) →
    ¬ p ∣ Nat.card (Outer K)

theorem kFactLieCharOut_of (hL3 : KFactLinThreeOut) (hU3 : KFactUnitaryThreeOut) :
    KFactLieCharOut := by
  intro K _ _ d hK p hp hp2 ⟨q, hqp, hcase⟩
  rcases hcase with ⟨hq2, hd⟩ | ⟨hq1, hd | hd⟩
  · have : Fact p.Prime := ⟨hp⟩
    obtain ⟨e⟩ := hK
    obtain ⟨e'⟩ := nonempty_mulEquiv_psl2GF_of_isLinTwoIndex (p := p) (n := q.exponent)
      ⟨q, hd, hqp, rfl⟩
    have hrange := ((TauCeti.LieTypeIndex.valid_iff _).mp d.2).1
    rw [hd] at hrange
    have h4 : 4 ≤ q.card := ((TauCeti.LieTypeIndex.inStandardRange_iff _).mp hrange).2 rfl
    rw [TauCeti.PrimePower.card_def, hqp] at h4
    exact not_dvd_card_outer_of_linTwo hp2 q.exponent_pos hq2 h4 (e.trans e')
  · exact hL3 K d hK p hp hp2 ⟨q, hqp, hq1, hd⟩
  · exact hU3 K d hK p hp hp2 ⟨q, hqp, hq1, hd⟩

end CFSG.AGLEmbeddingD2
