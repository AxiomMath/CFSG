module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.LedgerCited2
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SmallThreeOrders
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.JStarElimUnitaryLie
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

theorem primePower_card_three {q : TauCeti.PrimePower} (hq : q.card = 3) :
    q.p = 3 ∧ q.exponent = 1 := by
  have hdvd : q.p ∣ 3 := by
    rw [← hq, TauCeti.PrimePower.card_def]
    exact dvd_pow_self q.p (Nat.ne_of_gt q.exponent_pos)
  have h3 : q.p = 3 := by
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hdvd with h | h
    · exact absurd h q.prime_p.ne_one
    · exact h
  have hpow : q.p ^ q.exponent = 3 := by
    rw [← TauCeti.PrimePower.card_def]
    exact hq
  rw [h3] at hpow
  exact ⟨h3, ((by norm_num : Nat.Prime 3).pow_eq_iff.mp hpow).2⟩

theorem isSmallUnitary_three_of_isUThreeThree {X : Type} [Group X] (h : IsUThreeThree X) :
    IsSmallUnitary 3 X := by
  obtain ⟨d, ⟨q, hq3, hd⟩, he⟩ := h
  obtain ⟨hp, hn⟩ := primePower_card_three hq3
  exact ⟨d, ⟨q, hp, hn, hd⟩, he⟩

theorem autThreePowInner_of_card_mulAut {X : Type} [Group X] [Finite X]
    (hcenter : Subgroup.center X = ⊥) (hcard : Nat.card (MulAut X) = 2 * Nat.card X) :
    AutThreePowInner X := by
  have hXpos : 0 < Nat.card X := Nat.card_pos
  have hinj : Function.Injective (MulAut.conj : X →* MulAut X) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hgc : g ∈ Subgroup.center X := by
      rw [Subgroup.mem_center_iff]
      intro h
      have h1 := DFunLike.congr_fun hg h
      rw [MulAut.conj_apply, MulAut.one_apply, mul_inv_eq_iff_eq_mul] at h1
      exact h1.symm
    rw [hcenter, Subgroup.mem_bot] at hgc
    exact hgc
  have hInn : Nat.card (MulAut.conj : X →* MulAut X).range = Nat.card X :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hfin : Finite (MulAut X) := Nat.finite_of_card_ne_zero (by omega)
  have hindex : (MulAut.conj : X →* MulAut X).range.index = 2 := by
    have h := Subgroup.index_mul_card (H := (MulAut.conj : X →* MulAut X).range)
    rw [hInn, hcard] at h
    have h2 : (MulAut.conj : X →* MulAut X).range.index * Nat.card X = 2 * Nat.card X := h
    exact Nat.eq_of_mul_eq_mul_right hXpos h2
  have : (MulAut.conj : X →* MulAut X).range.Normal := Subgroup.normal_of_index_eq_two hindex
  intro ψ k hψ
  have hit : ∀ (n : ℕ) (x : X), (ψ ^ n) x = ψ^[n] x := by
    intro n
    induction n with
    | zero => intro x; rfl
    | succ n ih =>
      intro x
      rw [pow_succ', MulAut.mul_apply, ih, Function.iterate_succ_apply']
  have hpow : ψ ^ (3 ^ k) = 1 := by
    apply MulEquiv.ext
    intro x
    rw [hit, hψ]
    rfl
  have hq : (QuotientGroup.mk' (MulAut.conj : X →* MulAut X).range ψ) ^ (3 ^ k) = 1 := by
    rw [← map_pow, hpow, map_one]
  have hqcard : Nat.card (MulAut X ⧸ (MulAut.conj : X →* MulAut X).range) = 2 := by
    rw [← Subgroup.index_eq_card, hindex]
  have hord2 : orderOf (QuotientGroup.mk' (MulAut.conj : X →* MulAut X).range ψ) ∣ 2 := by
    have h := orderOf_dvd_natCard (QuotientGroup.mk' (MulAut.conj : X →* MulAut X).range ψ)
    rwa [hqcard] at h
  have hord3 : orderOf (QuotientGroup.mk' (MulAut.conj : X →* MulAut X).range ψ) ∣ 3 ^ k :=
    orderOf_dvd_of_pow_eq_one hq
  have hord1 := Nat.eq_one_of_dvd_coprimes
    (Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 2 3)) hord2 hord3
  have hq1 : QuotientGroup.mk' (MulAut.conj : X →* MulAut X).range ψ = 1 :=
    orderOf_eq_one_iff.mp hord1
  have hmem : ψ ∈ (MulAut.conj : X →* MulAut X).range := (QuotientGroup.eq_one_iff ψ).mp hq1
  obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp hmem
  refine ⟨a, fun x => ?_⟩
  rw [← ha, MulAut.conj_apply]


theorem lieModel_of_isUThreeThree {X : Type} [Group X] (h : IsUThreeThree X) :
    CFSG.Blueprint.LieModel X .PSU 3 3 1 := by
  obtain ⟨⟨i, hv⟩, ⟨q, hq3, hd⟩, ⟨e⟩⟩ := h
  have hd' : i = .twistedA 2 q := hd
  subst hd'
  obtain ⟨hp, hn⟩ := primePower_card_three hq3
  have hmod := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
  rw [hp, hn] at hmod
  exact Or.inl ⟨by decide, hmod⟩

theorem u33_simple_card_center {X : Type} [Group X] [Finite X] (h : IsUThreeThree X) :
    IsSimpleGroup X ∧ Nat.card X = 6048 ∧ Subgroup.center X = ⊥ := by
  have hsu := isSmallUnitary_three_of_isUThreeThree h
  have hcard : Nat.card X = 6048 := card_of_isSmallUnitary_three hsu
  obtain ⟨d, ⟨q, hqp, hqe, hdq⟩, ⟨e⟩⟩ := hsu
  have hdU : IsUnitaryIndex 3 d := ⟨q, hqp, hdq⟩
  have hsimpleCat : IsSimpleGroup (CatGroup d) := unitaryTarget_isSimpleGroup hdU
  have hsimple : IsSimpleGroup X := MulEquiv.isSimpleGroup e
  refine ⟨hsimple, hcard, ?_⟩
  rcases hsimple.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h0 | h0
  · exact h0
  · exfalso
    have : IsMulCommutative X := Subgroup.center_eq_top_iff.mp h0
    have hp := Group.is_simple_iff_prime_card.mp hsimple
    rw [hcard] at hp
    norm_num at hp

theorem outU33_proved :
    OutU33 := by
  intro X _ hX
  obtain ⟨e⟩ := CFSG.GH74.KGroups.U33.equiv_of_lieModel (lieModel_of_isUThreeThree hX)
  haveI : Finite X := CFSG.GH74.KGroups.U33.finite_K e
  obtain ⟨-, hcard, hcen⟩ := u33_simple_card_center hX
  refine autThreePowInner_of_card_mulAut hcen ?_
  rw [CFSG.GH74.KGroups.U33.card_mulAut e, hcard]

theorem u33FactsExact_proved : U33FactsExact := by
  intro X _ _ hX
  obtain ⟨hsimple, hcard, hcen⟩ := u33_simple_card_center hX
  refine ⟨hcen, ?_⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hsu := isSmallUnitary_three_of_isUThreeThree hX
  obtain ⟨d, ⟨q, hqp, hqe, hdq⟩, ⟨e⟩⟩ := hsu
  have hdU : IsUnitaryIndex 3 d := ⟨q, hqp, hdq⟩
  have hfe : d.1.fieldExponent = 1 := by
    rw [hdq]
    exact (TauCeti.LieTypeIndex.fieldExponent_twistedA 2 q).trans hqe
  have hstruct := kFactUnitarySylowStructure X 3 d (by norm_num) hdU ⟨e⟩
  have hub : ∀ (E : Subgroup X) (k : ℕ), IsElemAbelian 3 E → Nat.card E = 3 ^ k → k ≤ 2 := by
    intro E k hEel hEk
    by_contra hk
    push Not at hk
    have hE3 : IsPGroup 3 E := by
      intro g
      obtain ⟨-, hg⟩ := hEel
      refine ⟨1, Subtype.ext ?_⟩
      simpa using hg g.1 g.2
    obtain ⟨U, hEU⟩ := hE3.exists_le_sylow
    obtain ⟨hUcard, hUcomm, -, -⟩ := hstruct U
    rw [hfe, mul_one] at hUcard
    have hle : Nat.card E ≤ Nat.card (U : Subgroup X) := Subgroup.card_le_of_le hEU
    have hk3 : k = 3 := by
      rw [hUcard, hEk] at hle
      have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp hle
      omega
    have hEU' : E = (U : Subgroup X) := by
      refine Subgroup.eq_of_le_of_card_ge hEU ?_
      rw [hUcard, hEk, hk3]
    have hcomm : ∀ a ∈ (U : Subgroup X), ∀ b ∈ (U : Subgroup X), a * b = b * a := by
      intro a ha b hb
      rw [← hEU'] at ha hb
      exact hEel.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩ |> congrArg Subtype.val
    have hbot : ⁅(U : Subgroup X), (U : Subgroup X)⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact (hcomm a ha b hb).symm
    have hUc : (U : Subgroup X) ⊓ Subgroup.centralizer ((U : Subgroup X) : Set X) = U := by
      refine inf_eq_left.mpr (fun a ha => ?_)
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact hcomm b hb a ha
    rw [hUc] at hUcomm
    rw [hUcomm] at hbot
    have : Nat.card (U : Subgroup X) = 1 := by
      rw [show (U : Subgroup X) = ⊥ from hbot]
      exact Subgroup.card_bot
    rw [hUcard] at this
    norm_num at this
  apply le_antisymm
  · unfold Open.pRank
    refine csSup_le' ?_
    rintro r ⟨E, -, hEel, hEcard⟩
    exact hub E r hEel hEcard
  · obtain ⟨U⟩ : Nonempty (Sylow 3 X) := inferInstance
    obtain ⟨-, -, -, E, hEU, hEel, hEcard⟩ := hstruct U
    rw [hfe, mul_one] at hEcard
    exact le_pRank_of_isElemAbelian Nat.prime_three hEel (by simpa using hEcard) |>.trans
      (CFSG.PreuniquenessRankFour.Helpers.pRank_mono 3 Nat.prime_three le_top)

end CFSG.AGLEmbeddingD2.McLaughlin
