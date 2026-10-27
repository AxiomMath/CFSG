module

public import CFSG.HardMathSupport.Solomon.Coordinator.I19DefCharHolds

public section

namespace CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3

open CFSG.Blueprint.Chevalley
open CFSG.HardMathSupport.Solomon.LocalBalance (innerAut)

private theorem conj_injective_of_center_eq_bot {S : Type} [Group S]
    (hZ : Subgroup.center S = ⊥) : Function.Injective (MulAut.conj : S →* MulAut S) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  have hmem : a ∈ Subgroup.center S := by
    refine Subgroup.mem_center_iff.2 fun g => ?_
    have h1 := congrArg (fun φ : MulAut S => φ g) ha
    simp only [MulAut.conj_apply, MulAut.one_apply] at h1
    exact (mul_inv_eq_iff_eq_mul.1 h1).symm
  rw [hZ, Subgroup.mem_bot] at hmem
  exact hmem

private theorem pPrimeCore_eq_bot_of_map_eq_bot {S : Type} [Group S] {p : ℕ}
    (H : Subgroup S) {T : Subgroup (MulAut S)} (f : S →* MulAut S) (hf : Function.Injective f)
    (hT : Subgroup.map f H = T) (hcore : CFSG.pPrimeCore p ↥T = ⊥) :
    CFSG.pPrimeCore p ↥H = ⊥ := by
  subst hT
  let ψ : ↥H ≃* ↥(Subgroup.map f H) := Subgroup.equivMapOfInjective H f hf
  apply Subgroup.map_injective (f := ψ.toMonoidHom) ψ.injective
  rw [Subgroup.map_bot, pPrimeCore_map_iso p ψ]
  exact hcore

theorem glaPPrimeCoreOf_centralizer_adjointG2
    (p : ℕ) (K : Type) [Field K] [Finite K] [CharP K p] [Fact p.Prime] (hp2 : p ≠ 2)
    (z : ↥(adjointGroup Tag.G2 K)) (hz : orderOf z = p) :
    CFSG.Open.GLAPPrimeCoreOf p (Subgroup.centralizer {z}) = ⊥ := by
  have hprime : p.Prime := Fact.out
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K p
  let q : TauCeti.PrimePower := ⟨p, (n : ℕ), hprime, n.pos⟩
  have hKq : Nat.card K = q.card :=
    (Nat.card_eq_fintype_card).trans (hn.trans (TauCeti.PrimePower.card_def q).symm)
  have h3 : 3 ≤ q.card := by
    have hp3 : 3 ≤ p := by
      have := hprime.two_le
      omega
    rw [TauCeti.PrimePower.card_def]
    exact le_trans hp3 (Nat.le_self_pow n.ne_zero p)
  have hv : (TauCeti.LieTypeIndex.G2 q).Valid :=
    (TauCeti.LieTypeIndex.valid_iff _).2
      ⟨(TauCeti.LieTypeIndex.inStandardRange_iff _).2 h3,
        fun h => by simpa [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff] using h⟩
  have hcen : Subgroup.center ↥(adjointGroup Tag.G2 K) = ⊥ :=
    CFSG.LieType.Chevalley.center_adjointGroup_eq_bot
  haveI hfin : Finite ↥(adjointGroup Tag.G2 K) :=
    CFSG.LieType.Chevalley.generated_group_finite Tag.G2 K
  obtain ⟨hsimp, hnc, -⟩ :=
    CFSG.LieType.Chevalley.odd_pinned_Chevalley_p_components Tag.G2 K hK2
  obtain ⟨b⟩ := CFSG.TauCetiBridge.untwistedBridge_G2 q hv hp2 K hKq
  let eQ : ↥(adjointGroup Tag.G2 K) ≃* ↥(adjointGroup Tag.G2 K) ⧸
      Subgroup.center ↥(adjointGroup Tag.G2 K) :=
    ((QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot).symm
  let idx : TauCeti.ValidLieTypeIndex := ⟨TauCeti.LieTypeIndex.G2 q, hv⟩
  have hnon : Nonempty (↥(adjointGroup Tag.G2 K) ≃* (TauCeti.CFSGIndex.lie idx).Group) :=
    ⟨eQ.trans b⟩
  have hch : idx.1.characteristic = p := TauCeti.LieTypeIndex.characteristic_G2 q
  have hinj : Function.Injective
      (MulAut.conj : ↥(adjointGroup Tag.G2 K) →* MulAut ↥(adjointGroup Tag.G2 K)) :=
    conj_injective_of_center_eq_bot hcen
  have hxo : orderOf (MulAut.conj z : MulAut ↥(adjointGroup Tag.G2 K)) = p := by
    rw [orderOf_injective
      (MulAut.conj : ↥(adjointGroup Tag.G2 K) →* MulAut ↥(adjointGroup Tag.G2 K)) hinj z]
    exact hz
  have hx : (MulAut.conj z : MulAut ↥(adjointGroup Tag.G2 K)) ∈
      innerAut ↥(adjointGroup Tag.G2 K) :=
    MonoidHom.mem_range.2 ⟨z, rfl⟩
  have hcore := CFSG.HardMathSupport.Solomon.Coordinator.defCharInnerCoreFree_holds
    ↥(adjointGroup Tag.G2 K) hsimp hnc idx hnon p hprime hp2 hch (MulAut.conj z) hx hxo
    (innerAut ↥(adjointGroup Tag.G2 K)) le_rfl
  have hCD : (Subgroup.centralizer ({z} : Set ↥(adjointGroup Tag.G2 K))).map
      (MulAut.conj : ↥(adjointGroup Tag.G2 K) →* MulAut ↥(adjointGroup Tag.G2 K)) =
      innerAut ↥(adjointGroup Tag.G2 K) ⊓
        Subgroup.centralizer ({MulAut.conj z} : Set (MulAut ↥(adjointGroup Tag.G2 K))) := by
    ext a
    constructor
    · rintro ⟨c, hc, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff] at hc
      refine Subgroup.mem_inf.2 ⟨MonoidHom.mem_range.2 ⟨c, rfl⟩, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hc]
    · intro ha
      obtain ⟨hain, hcz⟩ := Subgroup.mem_inf.1 ha
      obtain ⟨c, rfl⟩ := MonoidHom.mem_range.1 hain
      rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul] at hcz
      exact ⟨c, Subgroup.mem_centralizer_singleton_iff.2 (hinj hcz), rfl⟩
  have hcoreC : CFSG.pPrimeCore p ↥(Subgroup.centralizer ({z} : Set ↥(adjointGroup Tag.G2 K))) =
      ⊥ :=
    pPrimeCore_eq_bot_of_map_eq_bot _ MulAut.conj hinj hCD
      ((Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)).1 hcore)
  show Subgroup.map (Subgroup.centralizer ({z} : Set ↥(adjointGroup Tag.G2 K))).subtype
    (CFSG.pPrimeCore p ↥(Subgroup.centralizer ({z} : Set ↥(adjointGroup Tag.G2 K)))) = ⊥
  rw [hcoreC, Subgroup.map_bot]

end CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3
