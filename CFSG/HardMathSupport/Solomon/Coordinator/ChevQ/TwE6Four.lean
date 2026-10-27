module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Seitz2313Even
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.D44

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.HardMathSupport.Dickson.I271
  CFSG.LieType.Seitz CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier CFSG.Blueprint.Multiplier
open scoped commutatorElement


@[expose] def TwE6FourOut : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (d : TauCeti.ValidLieTypeIndex), IsTwistedE6FourIndex d.1 →
    Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group) →
    ∀ E : Subgroup (MulAut S), IsElemAbelian 3 E → E ≤ (MulAut.conj : S →* MulAut S).range

@[expose] def TwE6FourRank : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (d : TauCeti.ValidLieTypeIndex), IsTwistedE6FourIndex d.1 →
    Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group) →
    (∃ A : Subgroup S, IsElemAbelian 3 A ∧ Nat.card A = 3 ^ 4 ∧
      ∃ U : Subgroup S, U ≠ ⊥ ∧ IsPGroup 2 ↥U ∧ A ≤ Subgroup.normalizer (U : Set S)) ∧
    (∀ E : Subgroup (MulAut S), IsElemAbelian 3 E → Nat.card E = 3 ^ 4 →
      E ≤ (MulAut.conj : S →* MulAut S).range →
      ∃ U : Subgroup S, U ≠ ⊥ ∧ IsPGroup 2 ↥U ∧ ∀ φ ∈ E, ∀ u ∈ U, φ u ∈ U)

theorem isTwistedE6FourIndex_evenScope {d : TauCeti.LieTypeIndex} (h : IsTwistedE6FourIndex d) :
    Seitz2313Cover.EvenScope d := by
  cases d <;> simp_all [IsTwistedE6FourIndex, IsTwoPow, Seitz2313Cover.EvenScope]

theorem isQuasisimple_of_open_aux {Q : Type*} [Group Q] (h : CFSG.Open.IsQuasisimple Q) :
    CFSG.IsQuasisimple Q := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨⟨h1⟩, h2, ?_⟩
  by_contra hc
  push Not at hc
  have hZ : commutator Q ≤ Subgroup.center Q := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [← QuotientGroup.eq_one_iff]
    change QuotientGroup.mk' (Subgroup.center Q) ⁅x, y⁆ = 1
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hc _ _
  rw [h1] at hZ
  have hall : ∀ q : Q ⧸ Subgroup.center Q, q = 1 := fun q => by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    exact (QuotientGroup.eq_one_iff x).mpr (hZ (Subgroup.mem_top x))
  obtain ⟨a, b, hab⟩ := exists_pair_ne (Q ⧸ Subgroup.center Q)
  exact hab ((hall a).trans (hall b).symm)

theorem twE64_center (hGA : GriessAllModelsStatement) {Y : Type} [Group Y] [Finite Y]
    (hq : CFSG.Open.IsQuasisimple Y) (hQ : IsLieQuot Y IsTwistedE6FourIndex) :
    Subgroup.center Y = ⊥ := by
  obtain ⟨⟨d, hv⟩, hd, ⟨e⟩⟩ := hQ
  cases d with
  | twistedE6 q =>
    obtain ⟨hq2, hqe⟩ := hd
    have hm : CFSG.Models.LieModel (TauCeti.CFSGIndex.lie ⟨.twistedE6 q, hv⟩).Group .twistedE6 0
        q.p q.exponent :=
      ⟨⟨q.prime_p, q.exponent_pos, rfl⟩, Or.inr ⟨rfl, ⟨.twistedE6 q, hv⟩, ⟨rfl, rfl⟩,
        ⟨MulEquiv.refl _⟩⟩⟩
    rw [hq2, hqe] at hm
    have h := center_dvd_table hGA (isQuasisimple_of_open_aux hq) e hm
    have h1 : (genericOrders .twistedE6 0 2 2).1 * (genericOrders .twistedE6 0 2 2).2 *
        ((exceptionalOrders .twistedE6 0 2 2).1 * (exceptionalOrders .twistedE6 0 2 2).2) = 1 := by
      decide
    rw [h1] at h
    exact Subgroup.eq_bot_of_card_eq _ (Nat.dvd_one.1 h)
  | _ => exact absurd hd (by simp [IsTwistedE6FourIndex])


theorem exists_sub_card_pow {G : Type*} [Group G] [Finite G] {p m k : ℕ} (hp : p.Prime)
    {A : Subgroup G} (hA : Nat.card A = p ^ m) (hk : k ≤ m) :
    ∃ E : Subgroup G, E ≤ A ∧ Nat.card E = p ^ k := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨D, hD⟩ := Sylow.exists_subgroup_card_pow_prime p
    (show p ^ k ∣ Nat.card A by rw [hA]; exact pow_dvd_pow p hk)
  refine ⟨D.map A.subtype, Subgroup.map_subtype_le D, ?_⟩
  rw [Subgroup.card_map_of_injective A.subtype_injective]
  exact hD

theorem pRank_bot_eq_zero' {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) :
    CFSG.Open.pRank p (⊥ : Subgroup G) = 0 :=
  i271_pRank_eq hp (E := ⊥) ⟨inferInstance, fun y hy => by
    rw [Subgroup.mem_bot] at hy
    rw [hy, one_pow]⟩ (by rw [Subgroup.card_bot, pow_zero])

theorem closure_plane_eq_top_of_hyperGamma {S : Type*} [Group S] {p : ℕ} (hp : p.Prime)
    {E : Subgroup (MulAut S)} (hcard : Nat.card E = p ^ 2) (h : seitzHyperGamma p E = ⊤) :
    Subgroup.closure {s : S | ∃ f ∈ E, f ≠ 1 ∧ f s = s} = ⊤ := by
  rw [eq_top_iff, ← h, ← closure_eq_seitzHyperGamma]
  apply Subgroup.closure_mono
  rintro s ⟨F, hFE, hrel, hs⟩
  have h1 := Subgroup.relIndex_mul_card F E
  rw [inf_of_le_left hFE, hrel, hcard] at h1
  have hFcard : Nat.card F = p := by
    have : p * Nat.card F = p * p := by rw [h1]; ring
    exact Nat.eq_of_mul_eq_mul_left hp.pos this
  have hF : F ≠ ⊥ := by
    rintro rfl
    rw [Subgroup.card_bot] at hFcard
    exact hp.one_lt.ne hFcard
  obtain ⟨⟨f, hf⟩, hf1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hF
  exact ⟨f, hFE hf, fun h => hf1 (Subtype.ext h), hs f hf⟩

theorem chevQTwistedE6Four_of_inputs (hGA : GriessAllModelsStatement) (hOut : TwE6FourOut)
    (hRank : TwE6FourRank) : ChevQTwistedE6Four := by
  classical
  intro X _ _ hXK K B hH hNorm hLie
  have hBN : B ≤ Subgroup.normalizer (K : Set X) := hNorm.1
  have hBel : IsElemAbelian 3 B := hH.scp.2.1
  have hq : CFSG.Open.IsQuasisimple ↥K := i116e_isQuasisimple hH.core hH.comp
  have hperf : commutator ↥K = ⊤ := hq.1
  have hZ : Subgroup.center ↥K = ⊥ := twE64_center hGA hq hLie
  have hZ1 : CFSG.Open.pRank 3 (Subgroup.center ↥K) ≤ 1 := by
    rw [hZ, pRank_bot_eq_zero' Nat.prime_three]
    exact Nat.zero_le _
  obtain ⟨d, hd, ⟨e⟩⟩ := hLie
  have hs : Seitz2313Cover.EvenScope d.1 := isTwistedE6FourIndex_evenScope hd
  by_cases hc3 : 3 ≤ CFSG.Open.pRank 3 (B ⊓ Subgroup.centralizer (K : Set X))
  · exact Or.inl ⟨hH.rank_four, isInGOne_of_centralizing hBN inf_le_left inf_le_right hc3⟩
  have hc1 : 1 ≤ CFSG.Open.pRank 3 (B ⊓ Subgroup.centralizer (K : Set X)) :=
    one_le_pRank_centralizer hH.prime hBel hH.centralized
  have hCel : IsElemAbelian 3 (B ⊓ Subgroup.centralizer (K : Set X)) :=
    i271_isElemAbelian_of_le hBel inf_le_left
  obtain ⟨r, hr⟩ := exists_pow_autOrderIn hH.prime hBel hBN
  have hm := pRank_eq_add_autOrderIn hH.prime hBel hBN hr
  let eK : ↥K ≃* (↥K ⧸ Subgroup.center ↥K) :=
    (QuotientGroup.quotientBot.symm).trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
  obtain ⟨A₀, hA₀el, hA₀card, U₀, hU₀0, hU₀2, hA₀N⟩ := (hRank ↥K d hd ⟨eK.trans e⟩).1
  have h2loc : 4 ≤ GLATwoLocalRank 3 ↥K :=
    le_glaTwoLocalRank_of_le_normalizer (by norm_num) hU₀0 hU₀2 hA₀el hA₀N hA₀card
  have h4 := le_twoLocalRank_of_central Nat.prime_three hCel inf_le_right hZ (n := 4)
    (by norm_num) h2loc
  have hrk := hH.rank_local
  have hr4 : 4 ≤ r := by omega
  obtain ⟨A', hA'le, hA'el, hA'card⟩ := exists_sub_autImage (k := 4) hH.prime hBel hperf
    (by rw [hr]; exact pow_dvd_pow 3 hr4)
  have hinn : A' ≤ (MulAut.conj : (↥K ⧸ Subgroup.center ↥K) →*
      MulAut (↥K ⧸ Subgroup.center ↥K)).range := hOut _ d hd ⟨e⟩ A' hA'el
  obtain ⟨U, hU0, hU2, hUinv⟩ := (hRank _ d hd ⟨e⟩).2 A' hA'el hA'card hinn
  have hgenE : ∀ E : Subgroup (MulAut (↥K ⧸ Subgroup.center ↥K)), E ≤ A' → E ≠ ⊥ →
      IsElemAbelian 3 E → seitzHyperGamma 3 E = ⊤ := fun E hEA' hE0 hEel =>
    seitzHyperGamma_eq_top_of_seitz2313Even seitz2313Even_holds Nat.prime_three (by norm_num) d
      ⟨e⟩ hs hEel hE0 ⟨U, hU0, hU2, fun φ hφ u hu => hUinv φ (hEA' hφ) u hu⟩
  by_cases hc2 : 2 ≤ CFSG.Open.pRank 3 (B ⊓ Subgroup.centralizer (K : Set X))
  ·
    obtain ⟨E, hEA', hEcard⟩ := exists_sub_card_pow Nat.prime_three hA'card (k := 2) (by norm_num)
    have hEel : IsElemAbelian 3 E := i271_isElemAbelian_of_le hA'el hEA'
    have hE0 : E ≠ ⊥ := fun h => by
      rw [h, Subgroup.card_bot] at hEcard
      norm_num at hEcard
    exact Or.inl (caseA_of_planeGen hH hBN hc2 hZ1 E (hEA'.trans hA'le) hEel hEcard
      (closure_plane_eq_top_of_hyperGamma Nat.prime_three hEcard (hgenE E hEA' hE0 hEel)))
  ·
    obtain ⟨E, hEA', hEcard⟩ := exists_sub_card_pow Nat.prime_three hA'card (k := 3) (by norm_num)
    have hEel : IsElemAbelian 3 E := i271_isElemAbelian_of_le hA'el hEA'
    have hE0 : E ≠ ⊥ := fun h => by
      rw [h, Subgroup.card_bot] at hEcard
      norm_num at hEcard
    exact Or.inl (caseA_of_hyperGen3 hH hBN hZ1 E (hEA'.trans hA'le) hEcard
      (by rw [closure_eq_seitzHyperGamma]; exact hgenE E hEA' hE0 hEel))

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
