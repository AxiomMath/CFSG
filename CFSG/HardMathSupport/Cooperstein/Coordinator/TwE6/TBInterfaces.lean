module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6.Interfaces
public import CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6.OuterInv
public import CFSG.HardMathSupport.Cooperstein.Coordinator.F4Exc.Family

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin.SmithCurtis
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Minuscule


@[expose] def TwTransBound {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f)) : Prop :=
  ∀ (k : Type) [Field k] [Finite k] [CharP k 2] [Algebra K k] (m : ℕ)
    (ρ : Representation k ↥(TwistedE6.fixedGroup K σ) (Fin m → k)) (y : Fin m → k)
    (χ : ↥(TwistedE6.fixedGroup K σ) → k) (J : Finset (Fin TwistTag.E6.foldedTag.rank)),
    IsSimpleRep ρ → IsCoverType (twistedE6CoverRankOne hf hK σ hσ) ρ y χ J →
    ((∃ a : Fin TwistTag.E6.foldedTag.rank, a ∉ J ∧ (a.val = 1 ∨ a.val = 2)) → 96 ≤ m) ∧
    ((∃ a b : Fin TwistTag.E6.foldedTag.rank, a ≠ b ∧ a ∉ J ∧ b ∉ J) → 144 ≤ m)

@[expose] def TwCopiesNormalize {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f)) : Prop :=
  ∀ (a : Fin TwistTag.E6.foldedTag.rank) (w : ↥(relWeylTwist TwistTag.E6)),
    (∀ i ∈ TwistTag.E6.orbit a, ∃ j ∈ TwistTag.E6.orbit a,
      (w : WeylGroup TwistTag.E6.tag) • (Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ) =
        Pi.single j 1) →
    Subgroup.map (MulAut.conj ((twistedE6CoverData hf hK σ hσ).nhatW w)).toMonoidHom
        (Rhat hf hK σ hσ a).range = (Rhat hf hK σ hσ a).range

@[expose] def TwF1Residual {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f)) : Prop :=
  f = 1 → ∀ (k : Type) [Field k] [Finite k] [CharP k 2] [Algebra K k] (m : ℕ)
    (ρ : Representation k ↥(TwistedE6.fixedGroup K σ) (Fin m → k)) (y : Fin m → k)
    (χ : ↥(TwistedE6.fixedGroup K σ) → k) (J : Finset (Fin TwistTag.E6.foldedTag.rank)),
    IsSimpleRep ρ → (∃ x, ρ x ≠ 1) →
    IsCoverType (twistedE6CoverRankOne hf hK σ hσ) ρ y χ J → J = Finset.univ.erase twN0 →
    (∀ (a : Fin TwistTag.E6.foldedTag.rank) (w : (orbitField TwistTag.E6 K σ a)ˣ),
      χ (hatH hf hK σ hσ a w) = 1) → 79 ≤ m

@[expose] def twM0 (f g : ℕ) : ℕ := (2 ^ f - 1) / (2 ^ Nat.gcd f g - 1)

@[expose] def TwPeriodArith : Prop :=
  ∀ f g : ℕ, 1 ≤ f → 1 ≤ g → g ∣ 2 * f → 3 ≤ 2 * f / g →
    (3 ≤ twM0 f g ∧ Odd (twM0 f g) ∧ twM0 f g ∣ 2 ^ f - 1 ∧
      ∀ j : ℕ, 0 < j → j < f → ¬ twM0 f g ∣ 2 ^ j - 1) ∧
    (∀ n a : ℕ, (n = f ∨ n = 2 * f) → (2 ^ n - 1) ∣ (2 ^ g - 1) * a → twM0 f g ∣ a) ∧
    (∀ (n : ℕ) (J' : Finset ℕ), (n = f ∨ n = 2 * f) → (∀ b ∈ J', b < n) → J'.Nonempty →
      (2 ^ n - 1) ∣ (2 ^ g - 1) * ∑ b ∈ J', 2 ^ b →
      ∃ D ⊆ J', (2 * f / g + 1) / 2 ≤ D.card ∧ ∀ b ∈ D, ∀ b' ∈ D, b ≠ b' → b % f ≠ b' % f)

abbrev TwN : Type := Fin TwistTag.E6.foldedTag.rank

@[expose] def twA (f : ℕ) : TwN → TwN → ℤ := fun b a =>
  (![![2, -1, 0, 0], ![-1, 2, -(1 + 2 ^ f), 0], ![0, -1, 2, -1], ![0, 0, -1, 2]] :
    Fin 4 → Fin 4 → ℤ) b a

@[expose] def twRefl (f : ℕ) (a : TwN) (e : TwN → ℤ) : TwN → ℤ := fun b => e b - twA f b a * e a

@[expose] def twAct (f : ℕ) (l : List TwN) (e : TwN → ℤ) : TwN → ℤ := l.foldr (twRefl f) e

@[expose] def twRoot (f : ℕ) (a : TwN) : TwN → ℤ := fun b => twA f b a

@[expose] def twWt {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f))
    {k : Type} [Field k] [Algebra K k] {V : Type} [AddCommGroup V] [Module k V]
    (ρ : Representation k ↥(TwistedE6.fixedGroup K σ) V) (e : TwN → ℤ) : Submodule k V where
  carrier := {v | ∀ (a : TwN) (w : (orbitField TwistTag.E6 K σ a)ˣ),
    ρ (hatH hf hK σ hσ a w) v =
      (algebraMap K k ((w : orbitField TwistTag.E6 K σ a) : K)) ^ (e a) • v}
  add_mem' := fun {a b} ha hb i t => by rw [map_add, ha i t, hb i t, smul_add]
  zero_mem' := fun i t => by simp
  smul_mem' := fun c v hv i t => by rw [map_smul, hv i t, smul_comm]

@[expose] def twNdig (f : ℕ) (a : TwN) : ℕ := if a.val < 2 then 2 * f else f

@[expose] def twNode (s : Fin Tag.F4.rank) : TwN :=
  ⟨3 - s.val, by have h : s.val < 4 := s.2; show 3 - s.val < 4; omega⟩

@[expose] def twWd (l : List (Fin Tag.F4.rank)) : List TwN := l.map fun x => twNode x

@[expose] def twV (f : ℕ) (s : Fin Tag.F4.rank) (lam : TwN → ℤ) (b i j : ℕ) : TwN → ℤ :=
  twAct f (twWd (F4Exc.gamWord s i)) (twAct f (twWd (F4Exc.uWord s j))
    (fun c => lam c - 2 ^ b * twRoot f (twNode s) c))

@[expose] def TwStringOfHighest {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f)) : Prop :=
  ∀ (k : Type) [Field k] [CharP k 2] [Algebra K k] {V : Type} [AddCommGroup V] [Module k V]
    (ρ : Representation k ↥(TwistedE6.fixedGroup K σ) V) (y : V)
    (χ : ↥(TwistedE6.fixedGroup K σ) → k) (J : Finset TwN) (a : TwN),
    IsSimpleRep ρ → IsCoverType (twistedE6CoverRankOne hf hK σ hσ) ρ y χ J →
    ∃ J' : Finset ℕ, (∀ i ∈ J', i < twNdig f a) ∧
      (∀ z : (orbitField TwistTag.E6 K σ a)ˣ, χ (hatH hf hK σ hσ a z) =
        (algebraMap K k ((z : orbitField TwistTag.E6 K σ a) : K)) ^ (∑ i ∈ J', 2 ^ i)) ∧
      Module.finrank k (orbitSpan (ρ.comp (Rhat hf hK σ hσ a)) y) = 2 ^ J'.card ∧
      (J' = ∅ → ∀ g, ρ (Rhat hf hK σ hσ a g) y = y) ∧
      (∀ b ∈ J', ∃ e ∈ orbitSpan (ρ.comp (Rhat hf hK σ hσ a)) y, e ≠ 0 ∧
        ∀ z : (orbitField TwistTag.E6 K σ a)ˣ, ρ (hatH hf hK σ hσ a z) e =
          (algebraMap K k ((z : orbitField TwistTag.E6 K σ a) : K)) ^
            (((∑ i ∈ J', 2 ^ i : ℕ) : ℤ) - 2 ^ (b + 1)) • e)

@[expose] def TwWeightShift {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f)) : Prop :=
  ∀ (k : Type) [Field k] [CharP k 2] [Algebra K k] {V : Type} [AddCommGroup V] [Module k V]
    (ρ : Representation k ↥(TwistedE6.fixedGroup K σ) V) (s : TwN) (E : TwN → ℤ) (y : V),
    y ∈ twWt hf hK σ hσ ρ E → ∀ (m : ℕ) (e : V),
      e ∈ orbitSpan (ρ.comp (Rhat hf hK σ hσ s)) y →
      (∀ z : (orbitField TwistTag.E6 K σ s)ˣ, ρ (hatH hf hK σ hσ s z) e =
        (algebraMap K k ((z : orbitField TwistTag.E6 K σ s) : K)) ^ (E s - 2 * (m : ℤ)) • e) →
      e ∈ twWt hf hK σ hσ ρ (fun b => E b - (m : ℤ) * twA f b s)

@[expose] def TwExistsDigit : Prop :=
  ∀ (f : ℕ) (s : Fin Tag.F4.rank), 3 ≤ f → (s.val = 0 ∨ s.val = 3) →
    ∀ J' : Finset ℕ, (∀ i ∈ J', i < 2 * f) → 2 ≤ J'.card →
      ∃ dg ∈ J', ∀ (i i' : Fin 12), i ≠ i' → ∀ (j j' : Fin 8),
        ¬ ∀ c : TwN, (((2 ^ f - 1 : ℕ)) : ℤ) ∣
          twV f s (fun c => if c = twNode s then ((∑ b ∈ J', 2 ^ b : ℕ) : ℤ) else 0) dg i j c -
            twV f s (fun c => if c = twNode s then ((∑ b ∈ J', 2 ^ b : ℕ) : ℤ) else 0) dg i' j' c

@[expose] def TwSepM0 : Prop :=
  ∀ (f g : ℕ), 1 ≤ f → 1 ≤ g → g ∣ 2 * f → 3 ≤ 2 * f / g →
    ∀ (s : Fin Tag.F4.rank) (lam : TwN → ℤ), (∀ c, ((twM0 f g : ℕ) : ℤ) ∣ lam c) →
      ∀ (b b' : ℕ) (i i' : Fin 12) (j j' : Fin 8),
        (∀ c : TwN, ((twM0 f g : ℕ) : ℤ) ∣ twV f s lam b i j c - twV f s lam b' i' j' c) →
          i = i' ∧ b % f = b' % f

end CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6
