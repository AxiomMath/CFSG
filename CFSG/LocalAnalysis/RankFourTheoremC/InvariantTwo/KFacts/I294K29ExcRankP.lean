module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294K29ExcRankGen
public import CFSG.HardMathSupport.Timmesfeld.Steinberg.PrimeChar

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.RankFourTheoremC

namespace ExcRank

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

@[expose] def TypeCoverP (τ : Tag) (p n q : ℕ) : Prop :=
  ∀ x : Fin τ.rank → ZMod p, ∀ w : WeylGroup τ,
    (∀ v, pPairing x (w • v) = (q : ZMod p) * pPairing x v) →
    ∃ w' : WeylGroup τ, (∀ v, pPairing x (w' • v) = (q : ZMod p) * pPairing x v) ∧
      ∃ S : Submodule (ZMod p) (Fin τ.rank → ZMod p), x ∈ S ∧ p ^ n ≤ Nat.card S ∧
        ∀ z ∈ S, ∀ v, pPairing z (w' • v) = (q : ZMod p) * pPairing z v

theorem typeCover_of_typeCoverP {τ : Tag} {p n q : ℕ} (hp : p.Prime) (h : TypeCoverP τ p n q) :
    TypeCover τ p n q := by
  classical
  intro L _ _ hL a ha w hw
  haveI : Fact p.Prime := ⟨hp⟩
  have hpL : (p : L) ≠ 0 := by
    intro h0
    have h1 : ringChar L ∣ p := (CharP.cast_eq_zero_iff L (ringChar L) p).1 h0
    rcases CharP.char_is_prime_or_zero L (ringChar L) with hq | hq
    · exact hL ((Nat.prime_dvd_prime_iff_eq hq hp).1 h1)
    · rw [hq] at h1
      exact hp.ne_zero (Nat.eq_zero_of_zero_dvd h1)
  haveI : NeZero (p : L) := ⟨hpL⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L p
  let ζu : Lˣ := (hζ.isUnit hp.ne_zero).unit
  have hζu : (ζu : L) = ζ := IsUnit.unit_spec _
  have hord : orderOf ζu = p := by
    rw [← orderOf_units, hζu]
    exact hζ.eq_orderOf.symm
  let tu : ZMod p → Lˣ := fun z => ζu ^ z.val
  have htu_zero : tu 0 = 1 := by simp [tu]
  have htu_add : ∀ z z', tu (z + z') = tu z * tu z' := by
    intro z z'
    have h1 := pow_mod_orderOf ζu (z.val + z'.val)
    rw [hord] at h1
    simp only [tu]
    rw [ZMod.val_add, h1, pow_add]
  have htu_inj : Function.Injective tu := by
    intro z z' hzz
    have h1 : z.val ≡ z'.val [MOD orderOf ζu] := pow_eq_pow_iff_modEq.1 hzz
    rw [hord] at h1
    exact ZMod.val_injective p (Nat.ModEq.eq_of_lt_of_lt h1 (ZMod.val_lt z) (ZMod.val_lt z'))
  have htu_p : ∀ z, tu z ^ p = 1 := by
    intro z
    have h1 : ζu ^ p = 1 := by
      have := pow_orderOf_eq_one ζu
      rwa [hord] at this
    simp only [tu]
    rw [← pow_mul, mul_comm, pow_mul, h1, one_pow]
  have hsurj : ∀ b : Lˣ, b ^ p = 1 → ∃ z, b = tu z := by
    intro b hb
    have hb' : ((b : Lˣ) : L) ^ p = 1 := by
      have := congrArg (fun u : Lˣ => (u : L)) hb
      simpa using this
    obtain ⟨i, hi, hib⟩ := hζ.eq_pow_of_pow_eq_one hb'
    refine ⟨(i : ZMod p), ?_⟩
    simp only [tu]
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hi]
    exact Units.ext (by rw [Units.val_pow_eq_pow_val, hζu, hib])
  let tuHom : Multiplicative (ZMod p) →* Lˣ :=
    { toFun := fun z => tu (Multiplicative.toAdd z)
      map_one' := htu_zero
      map_mul' := fun z z' => htu_add _ _ }
  have htu_zsmul : ∀ (z : ZMod p) (k : ℤ), tu (z * (k : ZMod p)) = tu z ^ k := by
    intro z k
    have h1 := map_zpow tuHom (Multiplicative.ofAdd z) k
    have h2 : (Multiplicative.ofAdd z) ^ k = Multiplicative.ofAdd (z * (k : ZMod p)) := by
      rw [← ofAdd_zsmul, zsmul_eq_mul, mul_comm]
    rw [h2] at h1
    exact h1
  have hchar : ∀ (x : Fin τ.rank → ZMod p) (v : Fin τ.rank → ℤ),
      rootChar (fun i => tu (x i)) v = tu (pPairing x v) := by
    intro x v
    simp only [rootChar, pPairing]
    have h1 : ∀ i, tu (x i) ^ v i = tu (x i * ((v i : ℤ) : ZMod p)) := fun i =>
      (htu_zsmul (x i) (v i)).symm
    simp only [h1]
    have h2 : ∀ (s : Finset (Fin τ.rank)),
        ∏ i ∈ s, tu (x i * ((v i : ℤ) : ZMod p)) = tu (∑ i ∈ s, x i * ((v i : ℤ) : ZMod p)) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp [htu_zero]
      | insert j s hj ih => rw [Finset.prod_insert hj, Finset.sum_insert hj, htu_add, ih]
    exact h2 Finset.univ
  have hpow : ∀ (z : ZMod p), tu z ^ q = tu (z * (q : ZMod p)) := by
    intro z
    have := htu_zsmul z (q : ℤ)
    rw [zpow_natCast, Int.cast_natCast] at this
    exact this.symm
  choose x hx using fun i => hsurj (a i) (ha i)
  have ha' : a = fun i => tu (x i) := funext hx
  subst ha'
  have hw' : ∀ v, pPairing x (w • v) = (q : ZMod p) * pPairing x v := by
    intro v
    have h1 := hw v
    rw [hchar, hchar, hpow] at h1
    rw [mul_comm]
    exact htu_inj h1
  obtain ⟨w', hw'a, S, hxS, hcard, hS⟩ := h x w hw'
  let B : Subgroup (Fin τ.rank → Lˣ) :=
    { carrier := {b | ∃ z ∈ S, ∀ i, b i = tu (z i)}
      mul_mem' := by
        rintro b b' ⟨z, hz, hb⟩ ⟨z', hz', hb'⟩
        exact ⟨z + z', S.add_mem hz hz', fun i => by
          rw [Pi.mul_apply, hb, hb', Pi.add_apply, htu_add]⟩
      one_mem' := ⟨0, S.zero_mem, fun i => by rw [Pi.one_apply, Pi.zero_apply, htu_zero]⟩
      inv_mem' := by
        rintro b ⟨z, hz, hb⟩
        refine ⟨-z, S.neg_mem hz, fun i => ?_⟩
        rw [Pi.inv_apply, hb, Pi.neg_apply]
        refine inv_eq_of_mul_eq_one_right ?_
        calc tu (z i) * tu (-z i) = tu (z i + -z i) := (htu_add _ _).symm
          _ = tu 0 := congrArg tu (add_neg_cancel (z i))
          _ = 1 := htu_zero }
  have hBmem : ∀ b, b ∈ B ↔ ∃ z ∈ S, ∀ i, b i = tu (z i) := fun b => Iff.rfl
  refine ⟨w', fun v => ?_, B, (hBmem _).2 ⟨x, hxS, fun i => rfl⟩, ?_, ?_, ?_⟩
  · rw [hchar, hchar, hpow, hw'a v, mul_comm]
  · rintro b hb i
    obtain ⟨z, -, hz⟩ := (hBmem b).1 hb
    rw [hz i]
    exact htu_p _
  · have hcardB : Nat.card S = Nat.card B := by
      refine Nat.card_congr (Equiv.ofBijective
        (fun z => ⟨fun i => tu ((z : Fin τ.rank → ZMod p) i), (hBmem _).2 ⟨z, z.2, fun i => rfl⟩⟩)
        ⟨fun z z' hzz => ?_, fun b => ?_⟩)
      · apply Subtype.ext
        funext i
        exact htu_inj (congrFun (congrArg Subtype.val hzz) i)
      · obtain ⟨z, hz, hb⟩ := (hBmem b.1).1 b.2
        exact ⟨⟨z, hz⟩, Subtype.ext (funext fun i => (hb i).symm)⟩
    rw [← hcardB]
    exact hcard
  · rintro b hb v
    obtain ⟨z, hz, hbz⟩ := (hBmem b).1 hb
    have hb' : b = fun i => tu (z i) := funext hbz
    rw [hb', hchar, hchar, hpow, hS z hz v, mul_comm]

end ExcRank

end CFSG.LocalAnalysis.RankFourTheoremC
