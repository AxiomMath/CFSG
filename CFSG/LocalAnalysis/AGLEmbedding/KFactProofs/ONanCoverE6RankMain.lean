module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanCoverThreeLin
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanCoverE6RankTw
public import CFSG.Adapters.TauCetiExceptional.EvenAll
public import CFSG.RankThree.Chevalley.SteinbergBTTwistedE6ModelCover

public section

namespace CFSG.AGLEmbedding.KFactProofs.CoverThree

open CFSG.Open TauCeti
open CFSG.RankThree.PartOne.N143 (IsLieE6Index)

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.RankThree.Chevalley CFSG.LieType.Chevalley
  CFSG.AGLEmbedding.KFactProofs.CoverE6

theorem three_ne_zero_of_card {F : Type} [Field F] {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e)
    (hF : Nat.card F = p ^ e) (hp3 : p ≠ 3) : (3 : F) ≠ 0 := by
  intro h
  have hchar : ringChar F = p := ringChar_eq_of_card hp he hF
  have h3 : ringChar F ∣ 3 := (ringChar.spec F 3).1 (by exact_mod_cast h)
  rw [hchar] at h3
  exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h3)

theorem four_le_pRank_untwisted
    {K : Type} [Group K] [Finite K] (q : PrimePower) (hv : (LieTypeIndex.E6 q).Valid)
    (hq3 : 3 ∣ q.card - 1) (e : K ⧸ Subgroup.center K ≃* ValidLieTypeIndex.Group ⟨.E6 q, hv⟩) :
    4 ≤ Open.pRank 3 (⊤ : Subgroup K) := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hcard : Nat.card (GaloisField q.p q.exponent) = q.card := by
    rw [GaloisField.card q.p q.exponent q.exponent_pos.ne', PrimePower.card_def]
  obtain ⟨br⟩ := (CFSG.TauCetiBridge.Even.chevalleyBridgesAll).e6 q hv
    (GaloisField q.p q.exponent) hcard
  have hmod : UntwistedChevalleyModel (K ⧸ Subgroup.center K) .E6 q.card :=
    ⟨GaloisField q.p q.exponent, inferInstance, inferInstance, hcard, ⟨e.trans br.symm⟩⟩
  obtain ⟨F, _, _, hF, φ, hφ, hker⟩ := exists_surj_adjointGroup_of_model hmod
  have hp3 : q.p ≠ 3 := by
    intro h
    have h1 : 0 < q.card := by rw [PrimePower.card_def]; exact pow_pos q.prime_p.pos _
    have h2 : 3 ∣ q.card := by
      rw [PrimePower.card_def, h]
      exact dvd_pow_self 3 q.exponent_pos.ne'
    omega
  have h3 : (3 : F) ≠ 0 := three_ne_zero_of_card q.prime_p q.exponent_pos
    (by rw [hF, PrimePower.card_def]) hp3
  obtain ⟨h, w, hcomm, hord, hinv, hfix⟩ := exists_inverter_data_adjoint F h3
  exact four_le_pRank_of_inverter_data φ hφ hker.le h w hcomm hord hinv hfix

theorem four_le_pRank_twisted
    {K : Type} [Group K] [Finite K] (q : PrimePower) (hv : (LieTypeIndex.twistedE6 q).Valid)
    (hq3 : 3 ∣ q.card + 1)
    (e : K ⧸ Subgroup.center K ≃* ValidLieTypeIndex.Group ⟨.twistedE6 q, hv⟩) :
    4 ≤ Open.pRank 3 (⊤ : Subgroup K) := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hcard : Nat.card (GaloisField q.p (q.exponent * 2)) = q.card ^ 2 := by
    rw [GaloisField.card q.p (q.exponent * 2) (by have := q.exponent_pos; omega),
      PrimePower.card_def, pow_mul]
  obtain ⟨br⟩ := (CFSG.TauCetiBridge.Even.chevalleyBridgesAll).twistedE6 q hv
    (GaloisField q.p (q.exponent * 2)) hcard
    (iterateFrobenius (GaloisField q.p (q.exponent * 2)) q.p q.exponent)
    (fun x => by rw [iterateFrobenius_def, PrimePower.card_def])
  have hmod : TwistedChevalleyModel (K ⧸ Subgroup.center K) .E6 (q.p ^ q.exponent) :=
    ⟨GaloisField q.p (q.exponent * 2), inferInstance, inferInstance,
      by rw [hcard, PrimePower.card_def]; rfl,
      iterateFrobenius (GaloisField q.p (q.exponent * 2)) q.p q.exponent,
      fun c => by rw [iterateFrobenius_def], ⟨e.trans br.symm⟩⟩
  obtain ⟨F, _, _, hF, σ, hσ, φ, hφ, hker⟩ :=
    exists_surj_graphFixedRootGroup_of_model q.prime_p q.exponent_pos hmod
  have hcl := (finite_fixed_root_group_perfect TwistTag.E6 q.prime_p q.exponent_pos F hF σ hσ).2.2.1
  have hp3 : q.p ≠ 3 := by
    intro h
    have h2 : 3 ∣ q.card := by
      rw [PrimePower.card_def, h]
      exact dvd_pow_self 3 q.exponent_pos.ne'
    omega
  have h3 : (3 : F) ≠ 0 := three_ne_zero_of_card q.prime_p (e := q.exponent * 2)
    (by have := q.exponent_pos; omega) (by rw [hF, ← pow_mul]) hp3
  let k := RingHom.eqLocusField σ (RingHom.id F)
  have h3k : (3 : ↥k) ≠ 0 := fun h =>
    h3 (by have := congrArg k.subtype h; rwa [map_ofNat, map_zero] at this)
  obtain ⟨h, w, hcomm, hord, hinv, hfix⟩ := exists_inverter_data_twisted k.subtype σ
    (fun c => RingHom.mem_eqLocusField.1 c.2) hcl h3k
  exact four_le_pRank_of_inverter_data φ hφ hker.le h w hcomm hord hinv hfix

theorem coverE6RankFour
    : CoverE6RankFour := by
  intro K _ _ _ _ _ _ d hd ⟨e⟩
  obtain ⟨dd, hv⟩ := d
  cases dd with
  | E6 q => exact four_le_pRank_untwisted q hv hd e
  | twistedE6 q => exact four_le_pRank_twisted q hv hd e
  | A r q => exact absurd hd (by simp [IsLieE6Index])
  | twistedA r q => exact absurd hd (by simp [IsLieE6Index])
  | B r q => exact absurd hd (by simp [IsLieE6Index])
  | C r q => exact absurd hd (by simp [IsLieE6Index])
  | D r q => exact absurd hd (by simp [IsLieE6Index])
  | twistedD r q => exact absurd hd (by simp [IsLieE6Index])
  | E7 q => exact absurd hd (by simp [IsLieE6Index])
  | E8 q => exact absurd hd (by simp [IsLieE6Index])
  | F4 q => exact absurd hd (by simp [IsLieE6Index])
  | G2 q => exact absurd hd (by simp [IsLieE6Index])
  | trialityD4 q => exact absurd hd (by simp [IsLieE6Index])
  | suzuki m => exact absurd hd (by simp [IsLieE6Index])
  | reeG2 m => exact absurd hd (by simp [IsLieE6Index])
  | reeF4 m => exact absurd hd (by simp [IsLieE6Index])
  | tits => exact absurd hd (by simp [IsLieE6Index])

end CFSG.AGLEmbedding.KFactProofs.CoverThree
