module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossFamBCDEvenWeir
public import CFSG.GroupTheory.WeirSylow.CrossRankForms

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.S172C.Rank

open QuadraticMap Module CFSG.GroupTheory.WeirSylow CFSG.Open CFSG.RankThree.Classical2

theorem not_dvd_pow_add_one_of_dvd_add_one {p q n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ q + 1) (heven : Even n) : ¬ (p : ℤ) ∣ (q : ℤ) ^ n - (-1) := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro h
  have h1 : (((q : ℤ) ^ n - (-1) : ℤ) : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 h
  have h2 : (q : ZMod p) = -1 := by
    have := (ZMod.natCast_eq_zero_iff (q + 1) p).2 hpq
    rw [Nat.cast_add, Nat.cast_one] at this
    exact eq_neg_of_add_eq_zero_left this
  push_cast at h1
  rw [h2, heven.neg_one_pow, sub_neg_eq_add, one_add_one_eq_two] at h1
  have h3 : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h1
  have h4 : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).1 h3
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h4)

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V}

theorem pRank_top_orthogonalGroup_minus_eq (hQ : (polarBilin Q).Nondegenerate) {n : ℕ}
    (hdim : finrank F V = 2 * n) (hminus : ¬ IsPlusType Q) (hn : 1 ≤ n) (heven : Even n) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1) :
    CFSG.Open.pRank p (⊤ : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)) = n - 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fintype F := Fintype.ofFinite F
  have hp1 : Odd p := hp.odd_of_ne_two hp2
  have hpK : ¬ p ∣ Nat.card F := fun h => hp.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right h).1 hpq))
  have hpK' : ¬ p ∣ Fintype.card F := by rwa [← Nat.card_eq_fintype_card]
  have hmin : IsMinusType Q :=
    (CFSG.LocalAnalysis.RankFourTheoremC.isPlusType_or_isMinusType Q hQ hn hdim).resolve_left hminus
  obtain ⟨P⟩ : Nonempty (Sylow p (TauCeti.QuadraticMap.orthogonalGroup Q)) := inferInstance
  obtain ⟨-, h2, -⟩ := sylow_orthogonal_even hp1 hpK' hn hdim Q hQ (ε := -1) (Or.inr ⟨rfl, hmin⟩) P
  obtain ⟨P'⟩ : Nonempty (Sylow p (StatedSp (n - 1) F)) := inferInstance
  have hdvd : ¬ (p : ℤ) ∣ (Fintype.card F : ℤ) ^ n - (-1) := by
    rw [← Nat.card_eq_fintype_card]
    exact not_dvd_pow_add_one_of_dvd_add_one hp hp2 hpq heven
  obtain ⟨φ⟩ := h2 hdvd P'
  rw [CFSG.LocalAnalysis.RankFourTheoremC.pRank_top_eq_of_sylow_mulEquiv P P' φ]
  refine pRank_top_statedSp_eq_of_dvd hp1 ?_ (n - 1)
  have hq : 1 ≤ Nat.card F := Nat.card_pos
  have : Nat.card F ^ 2 - 1 = (Nat.card F + 1) * (Nat.card F - 1) := by
    obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le hq
    rw [hc]
    simp only [Nat.add_sub_cancel_left, pow_two]
    ring_nf
    omega
  rw [this]
  exact Dvd.dvd.mul_right hpq _

theorem card_le_pow_pred_of_isElemAbelian_orthDerived (hQ : (polarBilin Q).Nondegenerate) {n : ℕ}
    (hdim : finrank F V = 2 * n) (hminus : ¬ IsPlusType Q) (hn : 1 ≤ n) (heven : Even n) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1) (E : Subgroup ↥(orthDerived Q))
    (hE : IsElemAbelian p E) : Nat.card E ≤ p ^ (n - 1) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hle : orthDerived Q ≤ TauCeti.QuadraticMap.orthogonalGroup Q :=
    fun g hg => Subgroup.commutator_le_self _ hg
  have hinj : Function.Injective (Subgroup.inclusion hle) := Subgroup.inclusion_injective hle
  have hpg : IsPGroup p E := fun g => ⟨1, Subtype.ext (by simpa using hE.2 g g.2)⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hpg
  have hE' : IsElemAbelian p (E.map (Subgroup.inclusion hle)) :=
    CFSG.SectionRank.isElemAbelian_map hE _
  have hk' : Nat.card (E.map (Subgroup.inclusion hle)) = p ^ k := by
    rw [Subgroup.card_map_of_injective hinj, hk]
  have hrank := CFSG.SectionRank.le_pRank hp.one_lt (le_top : E.map (Subgroup.inclusion hle) ≤ ⊤) hE' hk'
  rw [pRank_top_orthogonalGroup_minus_eq hQ hdim hminus hn heven hp hp2 hpq] at hrank
  rw [hk]
  exact Nat.pow_le_pow_right hp.pos hrank

end CFSG.LocalAnalysis.GLTheoremA.S172C.Rank

end
