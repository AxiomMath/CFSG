module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace K421GrpProof

open CFSG.Open

theorem isElemAbelian_zpowers {G : Type} [Group G] {p : ℕ} {x : G} (hx : x ^ p = 1) :
    IsElemAbelian p (Subgroup.zpowers x) := by
  refine ⟨inferInstance, fun y hy => ?_⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]

theorem le_pRank_of_orderOf {G : Type} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]
    {C : Subgroup G} {x : G} (hx : x ∈ C) (ho : orderOf x = p) : 1 ≤ CFSG.Open.pRank p C := by
  have hE : IsElemAbelian p (Subgroup.zpowers x) :=
    isElemAbelian_zpowers (by rw [← ho]; exact pow_orderOf_eq_one x)
  have hmem : (1 : ℕ) ∈ {k | ∃ E : Subgroup G, E ≤ C ∧ IsElemAbelian p E ∧ Nat.card E = p ^ k} :=
    ⟨Subgroup.zpowers x, (Subgroup.zpowers_le).2 hx, hE, by rw [Nat.card_zpowers, ho, pow_one]⟩
  have hbdd : BddAbove {k | ∃ E : Subgroup G, E ≤ C ∧ IsElemAbelian p E ∧ Nat.card E = p ^ k} := by
    refine ⟨Nat.card G, ?_⟩
    rintro k ⟨E, -, -, hk⟩
    have h1 : p ^ k ≤ Nat.card G := hk ▸ Subgroup.card_le_card_group E
    exact (Nat.lt_pow_self hp.out.one_lt).le.trans h1
  exact le_csSup hbdd hmem

theorem pRank_le_of_card {G : Type} [Group G] [Finite G] {p a m : ℕ} (hp : p.Prime)
    (h : Nat.card G = p ^ a * m) (hm : ¬ p ∣ m) (H : Subgroup G) : CFSG.Open.pRank p H ≤ a := by
  have hne : ({k | ∃ E : Subgroup G, E ≤ H ∧ IsElemAbelian p E ∧ Nat.card E = p ^ k} :
      Set ℕ).Nonempty :=
    ⟨0, Subgroup.zpowers (1 : G), by simp, isElemAbelian_zpowers (by simp), by simp⟩
  refine csSup_le hne ?_
  rintro k ⟨E, -, -, hk⟩
  have hdvd : p ^ k ∣ p ^ a * m := by
    rw [← h, ← hk]
    exact Subgroup.card_subgroup_dvd_card E
  have hcop : Nat.Coprime (p ^ k) m := Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).2 hm)
  have h2 : p ^ k ∣ p ^ a := hcop.dvd_of_dvd_mul_right hdvd
  exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 h2

theorem not_isPSolvable_of_simple {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S) {p : ℕ}
    (hp : p.Prime) (hdvd : p ∣ Nat.card S) (hne : Nat.card S ≠ p) :
    ¬ CFSG.HallHigman.IsPSolvable p S := by
  intro hsolv
  haveI := hS
  have hsimple : IsSimpleGroup (↥(⊤ : Subgroup S) ⧸ (⊥ : Subgroup ↥(⊤ : Subgroup S))) :=
    MulEquiv.isSimpleGroup ((QuotientGroup.quotientBot).trans Subgroup.topEquiv)
  have hidx : (⊥ : Subgroup ↥(⊤ : Subgroup S)).index = Nat.card S := by
    rw [Subgroup.index_bot, Nat.card_congr Subgroup.topEquiv.toEquiv]
  rcases hsolv ⊤ (Subgroup.Normal.isSubnormal inferInstance) ⊥ hsimple with h | h
  · rw [hidx] at h
    exact hne h
  · rw [hidx] at h
    exact (Nat.Prime.coprime_iff_not_dvd hp).mp h hdvd

theorem not_isPSolvable_of_embedding {S X : Type} [Group S] [Group X] [Finite S] [Finite X] {p : ℕ}
    [hp : Fact p.Prime] (hS : IsSimpleGroup S) (hdvd : p ∣ Nat.card S) (hne : Nat.card S ≠ p)
    (φ : S →* X) (hφ : Function.Injective φ) {C : Subgroup X} (hC : φ.range ≤ C) :
    ¬ CFSG.HallHigman.IsPSolvable p ↥C := by
  intro hsolv
  have h1 := CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure.isPSolvable_of_le
    hsolv hC
  have h2 := CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.QuasisimpleSolvableNormal.isPSolvable_of_mulEquiv
    (MonoidHom.ofInjective hφ).symm h1
  exact not_isPSolvable_of_simple hS hp.out hdvd hne h2

theorem rank_ge_one_of_embedding {S X : Type} [Group S] [Group X] [Finite S] [Finite X] {p : ℕ}
    [hp : Fact p.Prime] (hdvd : p ∣ Nat.card S) (φ : S →* X) (hφ : Function.Injective φ)
    {C : Subgroup X} (hC : φ.range ≤ C) : 1 ≤ CFSG.Open.pRank p C := by
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
  exact le_pRank_of_orderOf (hC ⟨x, rfl⟩) (by rw [orderOf_injective φ hφ x]; exact hx)

end K421GrpProof

end CFSG.LocalAnalysis.RankThreeUC.S15
