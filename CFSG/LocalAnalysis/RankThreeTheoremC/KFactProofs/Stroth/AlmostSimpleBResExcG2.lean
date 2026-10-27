module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBResAt
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieExcRank
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBResExcE

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration CFSG.TauCetiBridge TauCeti CFSG.RankThree.PartOne.K128
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem hasIndepPair_of_injective_pi {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e) {G : Type*} [Group G]
    (Ψ : (Fin 2 → Multiplicative (ZMod (p ^ e))) →* G) (hΨ : Function.Injective Ψ) :
    HasIndepPair p G := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero (p ^ e) := ⟨pow_ne_zero e hp.ne_zero⟩
  have hdvd : p ∣ Nat.card (Multiplicative (ZMod (p ^ e))) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
    exact dvd_pow_self p (by omega)
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hdvd
  obtain ⟨h0, h1, h2, h3⟩ := two_indep_of_blockHom Ψ hΨ (MonoidHom.id G) hg (fun y hy _ => hy)
  exact ⟨_, _, h0, h1, h2, h3⟩

section


theorem hasIndepPair_adjointG2 (k : Type) [Field k] [Finite k] [CharP k 2] {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hd : p ∣ Nat.card k ^ 2 - 1) : HasIndepPair p (adjointGroup .G2 k) := by
  have hQ : 2 ≤ Nat.card k := Finite.one_lt_card
  have he : 1 ≤ (Nat.card k ^ 2 - 1).factorization p := by
    refine (Nat.Prime.factorization_pos_of_dvd hp ?_ hd)
    have : 1 < Nat.card k ^ 2 := Nat.one_lt_pow (by norm_num) (by omega)
    omega
  rcases dvd_pred_or_succ_of_dvd_sq_sub_one hp (by omega) (by omega) hd with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · obtain ⟨Ψ, hΨ⟩ := exists_injective_G2_split k hp (by omega) h1 h2
    exact hasIndepPair_of_injective_pi hp he Ψ hΨ
  · obtain ⟨Ψ, hΨ⟩ := exists_injective_G2_qplus k hp (by omega) h1 h2
    exact hasIndepPair_of_injective_pi hp he Ψ hΨ

theorem fixesPair_adjointG2 {f p : ℕ} (hf : 2 ≤ f) (K : Type) [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2 ^ f) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hrk1 : ¬ RankLE1 p (adjointGroup Tag.G2 K))
    {α : MulAut (adjointGroup Tag.G2 K)} (hαp : α ^ p = 1)
    (hα : α ∉ inner (adjointGroup Tag.G2 K)) : FixesIndepPair p α := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hαo : orderOf α = p := orderOf_eq_prime hαp (fun h1 => hα (h1 ▸
    (CFSG.ComponentClassification.OuterAutomorphisms.inner (adjointGroup Tag.G2 K)).one_mem))
  obtain ⟨x, σ, hσ, hασ⟩ :=
    CFSG.HardMathSupport.Lang.E6Descent.G2_form_even hf K hK hp α hαo hα
  obtain ⟨δ, hδ⟩ := CFSG.HardMathSupport.Lang.E6Descent.exists_conj_eq_entrywiseAdjointAut_of_form
    Tag.G2 Nat.prime_two (by omega) K hK hp α hαo x σ hσ hασ
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hK]
    intro hd'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hd'))
  obtain ⟨hdvd, hc⟩ := CFSG.RankThree.Chevalley.SteinbergBT.card_fixSubfield Nat.prime_two
    (by omega) hK σ
  rw [hσ] at hdvd hc
  haveI : Finite (fixSubfield σ) :=
    Nat.finite_of_card_ne_zero (by rw [hc]; exact (pow_pos (by norm_num) _).ne')
  haveI : CharP (fixSubfield σ) 2 := RingHom.charP (fixSubfield σ).subtype
    (fixSubfield σ).subtype_injective 2
  have hFk : Nat.card K = Nat.card (fixSubfield σ) ^ p := by
    rw [hK, hc, ← pow_mul, Nat.div_mul_cancel hdvd]
  have hd : p ∣ Nat.card K ^ 2 - 1 := by
    by_contra h
    exact hrk1 (CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross.Untw.rankLE1_G2
      hp hp5 hpK h)
  have hdk : p ∣ Nat.card (fixSubfield σ) ^ 2 - 1 := by
    have h1 : 1 ≤ Nat.card K ^ 2 := Nat.one_le_pow _ _ Nat.card_pos
    have h2 : 1 ≤ Nat.card (fixSubfield σ) ^ 2 := Nat.one_le_pow _ _ Nat.card_pos
    rw [← ZMod.natCast_eq_zero_iff] at hd ⊢
    push_cast [Nat.cast_sub h1, Nat.cast_sub h2] at hd ⊢
    have hcast : ((Nat.card K : ℕ) : ZMod p) = ((Nat.card (fixSubfield σ) : ℕ) : ZMod p) := by
      rw [hFk]
      push_cast
      rw [ZMod.pow_card]
    rw [hcast] at hd
    exact hd
  exact fixesPair_of_entrywise_conj (r := 1) (j := 1) σ (by simp) (by rw [pow_one]; exact hδ)
    (hasIndepPair_adjointG2 (fixSubfield σ) hp hp5 hdk)

theorem chevTwoOuterFixesPair_G2_geFive :
    ChevTwoOuterFixesPairAt (fun p => 5 ≤ p) LieIndexG2 := by
  intro p hp hp2 hp5 L _ _ hrk ⟨d, hchar, hF, ⟨e⟩⟩ hne α hα hαp
  obtain ⟨d, hv⟩ := d
  cases d with
  | G2 q =>
    have hq2 : q.p = 2 := hchar
    obtain ⟨K, _, _, hK, hchK, ⟨eK⟩⟩ :=
      exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.g2 q hv
    haveI : CharP K 2 := hq2 ▸ hchK
    let θ : L ≃* adjointGroup Tag.G2 K := e.trans eK
    obtain ⟨hrk2, E, hE, hEc⟩ := rank_data_of_pRank hp hrk θ
    have hK2 : Nat.card K = 2 ^ q.exponent := by rw [hK, PrimePower.card_def, hq2]
    have h3 : 3 ≤ q.card := (LieTypeIndex.inStandardRange_iff _).1
      ((LieTypeIndex.valid_iff _).1 hv).1
    have hf2 : 2 ≤ q.exponent := by
      by_contra h
      have h1 : q.exponent = 1 := by have := q.exponent_pos; omega
      rw [PrimePower.card_def, hq2, h1] at h3
      omega
    exact FixesIndepPair.of_mulEquiv θ
      (fixesPair_adjointG2 hf2 K hK2 hp hp5 (not_rankLE1_of_sq hp hE hEc)
        (α := MulAut.congr θ α) (by rw [← map_pow, hαp, map_one])
        ((congr_mem_inner_iff θ α).not.2 hα))
  | A _ _ => exact absurd hF (by simp [LieIndexG2])
  | twistedA _ _ => exact absurd hF (by simp [LieIndexG2])
  | B _ _ => exact absurd hF (by simp [LieIndexG2])
  | C _ _ => exact absurd hF (by simp [LieIndexG2])
  | D _ _ => exact absurd hF (by simp [LieIndexG2])
  | twistedD _ _ => exact absurd hF (by simp [LieIndexG2])
  | E6 _ => exact absurd hF (by simp [LieIndexG2])
  | E7 _ => exact absurd hF (by simp [LieIndexG2])
  | E8 _ => exact absurd hF (by simp [LieIndexG2])
  | F4 _ => exact absurd hF (by simp [LieIndexG2])
  | twistedE6 _ => exact absurd hF (by simp [LieIndexG2])
  | trialityD4 _ => exact absurd hF (by simp [LieIndexG2])
  | suzuki _ => exact absurd hF (by simp [LieIndexG2])
  | reeG2 _ => exact absurd hF (by simp [LieIndexG2])
  | reeF4 _ => exact absurd hF (by simp [LieIndexG2])
  | tits => exact absurd hF (by simp [LieIndexG2])

end

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
