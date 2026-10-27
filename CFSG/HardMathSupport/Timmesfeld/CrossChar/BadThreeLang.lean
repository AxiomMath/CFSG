module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerE8Five
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeLarge

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.DefChar CFSG.LieType.SeitzGeneration CFSG.LieType.Chevalley
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.TauCetiBridge CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KE CFSG.RankThree.Lattice

section


@[expose] def LangToralPlane (τ : Tag) (p : ℕ) : Prop :=
  ∀ (K : Type) [Field K] [Finite K], ¬ p ∣ Nat.card K →
    ∀ A : Subgroup (adjointGroup τ K), (∀ x ∈ A, x ^ p = 1) → Nat.card A = p ^ 2 →
      ∃ w : WeylGroup τ, ∃ Fr : AlgebraicClosure K →+* AlgebraicClosure K,
        (∀ c, Fr c = c ^ Nat.card K) ∧
        ∃ g0 ∈ adjointGroup τ (AlgebraicClosure K),
          Units.map (entrywiseHom Fr) g0 =
            g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w ∧
          ∃ c : adjointGroup τ K, ∀ x ∈ A,
            baseChangeGL (algebraMap K (AlgebraicClosure K))
              ((c * x * c⁻¹ : adjointGroup τ K) : ModGL τ K) ∈
              (twistedTorusOf (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w)
                (Units.map (entrywiseHom Fr))).map (MulAut.conj g0).toMonoidHom

theorem langToralPlane_E8_five_iff : LangToralPlane Tag.E8 5 ↔ E8FiveToralPlane := Iff.rfl

theorem localDeltaIn_eq_bot_of_toralPlane {τ : Tag} {p : ℕ} (hp : p.Prime)
    (htor : LangToralPlane τ p) {Q : ℕ → Prop}
    (hT1 : ∀ w : WeylGroup τ, LangTorusPlaneBalance τ w p Q) (K : Type) [Field K] [Finite K]
    (hpK : ¬ p ∣ Nat.card K) (hQ : Q (Nat.card K))
    {D : Subgroup (MulAut (adjointGroup τ K))} (hD : IsElemAbelian p D) (hcard : Nat.card D = p ^ 3)
    (hDin : D ≤ innerAut (adjointGroup τ K)) {H : Subgroup (MulAut (adjointGroup τ K))}
    (hH : innerAut (adjointGroup τ K) ≤ H) : localDeltaIn p H D = ⊥ := by
  have hinj := mulAut_conj_injective_adjointGroup (τ := τ) (K := K)
  set D₀ := D.comap (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K))
    with hD₀
  have hDD : D₀.map MulAut.conj = D := Subgroup.map_comap_eq_self hDin
  have hD₀card : Nat.card D₀ = p ^ 3 := by
    rw [← hcard, ← hDD, Subgroup.card_map_of_injective hinj]
  have hpow₀ : ∀ x ∈ D₀, x ^ p = 1 := fun x hx => by
    have hx' : (MulAut.conj x) ^ p = 1 := hD.2 _ hx
    exact hinj (by rw [map_pow, hx', map_one])
  obtain ⟨A, hAD₀, hAcard⟩ := exists_subgroup_card_sq_le hp hD₀card
  obtain ⟨w, Fr, hFr, g0, hg0C, hg0, c, hc⟩ :=
    htor K hpK A (fun x hx => hpow₀ x (hAD₀ hx)) hAcard
  refine localDeltaIn_eq_bot_of_conj_sub hH (E := A) ?_ c ?_
  · rw [← hDD]
    exact Subgroup.map_mono hAD₀
  · refine hT1 w K hQ Fr hFr g0 hg0C hg0 _ ?_ ?_ ?_ H hH
    · rintro _ ⟨x, hx, rfl⟩
      change (c * x * c⁻¹) ^ p = 1
      rw [conj_pow, hpow₀ x (hAD₀ hx), mul_one, mul_inv_cancel]
    · rw [Subgroup.card_map_of_injective (MulAut.conj c).injective, hAcard]
      have := hp.two_le
      nlinarith
    · rintro _ ⟨x, hx, rfl⟩
      exact hc x hx

end

section Three


@[expose] def ThreeLargeQ (q : ℕ) : Prop := ¬ 3 ∣ q ∧ q ≠ 2 ∧ q ≠ 4

theorem f4ThreeInnerNonsplitLarge_of_toral (htor : LangToralPlane Tag.F4 3)
    (hT1 : ∀ w : WeylGroup Tag.F4, LangTorusPlaneBalance Tag.F4 w 3 ThreeLargeQ) :
    F4ThreeInnerNonsplitLarge := by
  intro K _ _ h3 h2 h4 D hD hcard hDin _ H hH _
  exact localDeltaIn_eq_bot_of_toralPlane Nat.prime_three htor hT1 K h3 ⟨h3, h2, h4⟩ hD hcard hDin
    hH

theorem e8ThreeInnerNonsplitLarge_of_toral (htor : LangToralPlane Tag.E8 3)
    (hT1 : ∀ w : WeylGroup Tag.E8, LangTorusPlaneBalance Tag.E8 w 3 ThreeLargeQ) :
    E8ThreeInnerNonsplitLarge := by
  intro ℓ f hℓ hℓ3 hf hq2 hq4 K _ _ hK D hD hcard hDin _ H hH _
  have h3 : ¬ 3 ∣ Nat.card K := by
    rw [hK]
    intro h
    exact hℓ3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hℓ).1
      (Nat.prime_three.dvd_of_dvd_pow h)).symm
  exact localDeltaIn_eq_bot_of_toralPlane Nat.prime_three htor hT1 K h3
    ⟨h3, hK ▸ hq2, hK ▸ hq4⟩ hD hcard hDin hH

theorem e7ThreeInnerNonsplitLarge_of_toral (htor : LangToralPlane Tag.E7 3)
    (hT1 : ∀ w : WeylGroup Tag.E7, LangTorusPlaneBalance Tag.E7 w 3 fun q => ¬ 3 ∣ q ∧ q ≠ 2) :
    E7ThreeInnerNonsplitLarge := by
  intro ℓ f hℓ hℓ3 hf hq2 K _ _ hK D hD hcard hDin _ H hH _
  have h3 : ¬ 3 ∣ Nat.card K := by
    rw [hK]
    intro h
    exact hℓ3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hℓ).1
      (Nat.prime_three.dvd_of_dvd_pow h)).symm
  exact localDeltaIn_eq_bot_of_toralPlane Nat.prime_three htor hT1 K h3 ⟨h3, hK ▸ hq2⟩ hD hcard
    hDin hH

end Three

end CFSG.HardMathSupport.Timmesfeld.CrossChar
