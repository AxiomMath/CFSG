module

public import CFSG.HardMathSupport.Solomon.Coordinator.Defs

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator

@[expose] def oPrimeP (p : ℕ) (H : Type*) [Group H] : Subgroup H :=
  (CFSG.pCore p (H ⧸ GLAPPrimeCore p H)).comap (QuotientGroup.mk' (GLAPPrimeCore p H))

instance oPrimeP.normal (p : ℕ) (H : Type*) [Group H] : (oPrimeP p H).Normal := by
  unfold oPrimeP
  have : (CFSG.pCore p (H ⧸ GLAPPrimeCore p H)).Normal := CFSG.pCore_normal
  exact Subgroup.normal_comap _

variable {G : Type*} [Group G]

@[expose] def oPrimePOf (p : ℕ) (X : Subgroup G) : Subgroup G :=
  (oPrimeP p ↥X).map X.subtype

@[expose] def centralizerQuot (L U : Subgroup G) : Subgroup G where
  carrier := {g | g ∈ Subgroup.normalizer (L : Set G) ∧ g ∈ Subgroup.normalizer (U : Set G) ∧
    ∀ x ∈ L, x * g * x⁻¹ * g⁻¹ ∈ U}
  one_mem' := ⟨one_mem _, one_mem _, fun x _ => by simp⟩
  mul_mem' := by
    rintro g h ⟨hgL, hgU, hg⟩ ⟨hhL, hhU, hh⟩
    refine ⟨mul_mem hgL hhL, mul_mem hgU hhU, fun x hx => ?_⟩
    have h1 : x * (g * h) * x⁻¹ * (g * h)⁻¹ =
        (x * g * x⁻¹ * g⁻¹) * (g * (x * h * x⁻¹ * h⁻¹) * g⁻¹) := by group
    rw [h1]
    refine U.mul_mem (hg x hx) ?_
    have := (Subgroup.mem_normalizer_iff.1 hgU _).1 (hh x hx)
    simpa using this
  inv_mem' := by
    rintro g ⟨hgL, hgU, hg⟩
    refine ⟨inv_mem hgL, inv_mem hgU, fun x hx => ?_⟩
    have h1 : x * g⁻¹ * x⁻¹ * (g⁻¹)⁻¹ = g⁻¹ * (x * g * x⁻¹ * g⁻¹)⁻¹ * g := by group
    rw [h1]
    have h2 : (x * g * x⁻¹ * g⁻¹)⁻¹ ∈ U := U.inv_mem (hg x hx)
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem hgU) _).1 h2
    simpa using this

@[expose] def IsHatON (X : Type*) [Group X] : Prop :=
  commutator X = ⊤ ∧ Nat.card (Subgroup.center X) = 3 ∧
    Nonempty ((X ⧸ Subgroup.center X) ≃*
      (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.ONan).Group)

@[expose] def IsFiTwentyTwo (X : Type*) [Group X] : Prop :=
  Nonempty (X ≃* (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.Fi22).Group)

section Lemma31

variable [Finite G]

@[expose] def Lemma31iii (p : ℕ) (B L : Subgroup G) : Prop :=
  p = 3 ∧ GLATwoLocalRank 3 G = 4 ∧ IsLThreeFour (↥L ⧸ oPrimeP 3 ↥L) ∧
    (centralizerQuot L (oPrimePOf 3 L)).relIndex (B ⊓ Subgroup.normalizer (L : Set G)) = 9 ∧
    ∀ b ∈ B ⊓ Subgroup.normalizer (L : Set G), ∃ l ∈ L, l⁻¹ * b ∈ centralizerQuot L (oPrimePOf 3 L)

@[expose] def Lemma31iv (p : ℕ) (B L : Subgroup G) : Prop :=
  p = 3 ∧ GLATwoLocalRank 3 G = 4 ∧ IsHatON (↥L ⧸ GLAPPrimeCore 3 ↥L) ∧
    (centralizerQuot L (GLAPPrimeCoreOf 3 L)).relIndex (B ⊓ Subgroup.normalizer (L : Set G)) = 27

@[expose] def Lemma31v (p : ℕ) (L : Subgroup G) : Prop :=
  p = 5 ∧ GLATwoLocalRank 5 G = 4 ∧ IsFiTwentyTwo (↥L ⧸ GLAPPrimeCore 5 ↥L)

@[expose] noncomputable def lambdaLOf (p : ℕ) (B : Subgroup G) (b : G) : Subgroup G :=
  sSup {L | GLAPComponent p (Subgroup.centralizer ({b} : Set G)) L ∧
    ¬ IsStronglyLocallyOneBalanced p B b L ∧ Lemma31iii p B L}

@[expose] noncomputable def lambdaONOf (p : ℕ) (B : Subgroup G) (b : G) : Subgroup G :=
  sSup {L | GLAPComponent p (Subgroup.centralizer ({b} : Set G)) L ∧
    ¬ IsStronglyLocallyOneBalanced p B b L ∧ Lemma31iv p B L}

@[expose] noncomputable def lambdaMOf (p : ℕ) (B : Subgroup G) (b : G) : Subgroup G :=
  sSup {L | GLAPComponent p (Subgroup.centralizer ({b} : Set G)) L ∧
    ¬ IsStronglyLocallyOneBalanced p B b L ∧ Lemma31v p L}

@[expose] noncomputable def lambdaMGroup (p : ℕ) (B : Subgroup G) : Subgroup G :=
  ⨆ (b : G) (_ : b ∈ B) (_ : b ≠ 1), lambdaMOf p B b

end Lemma31

end CFSG.HardMathSupport.Solomon.LocalBalance
