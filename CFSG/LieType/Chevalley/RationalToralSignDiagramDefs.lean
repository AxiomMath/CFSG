module

public import CFSG.LieType.Chevalley.SignCharacterMasks

public noncomputable section

namespace CFSG.LieType.Chevalley.ToralSign

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint Matrix

variable {τ : Tag}

@[expose] def natBits (m : ℕ) : Fin τ.rank → Bool :=
  fun j => m.testBit j

variable (τ) in
@[expose] def signMaskChar (m : ℕ) : Multiplicative (Fin τ.rank → ℤ) →* ℤˣ :=
  maskChar (natBits m)

theorem signMaskChar_single (m : ℕ) (j : Fin τ.rank) :
    signMaskChar τ m (Multiplicative.ofAdd (Pi.single j 1)) =
      (-1) ^ ((m / 2 ^ (j : ℕ) % 2 : ℕ) : ℤ) := by
  rw [signMaskChar, maskChar_apply]
  congr 1
  rw [maskPairing, Finset.sum_eq_single j (fun k _ hk => by simp [hk]) (by simp)]
  simp only [natBits, Nat.testBit_eq_decide_div_mod_eq, Pi.single_eq_same]
  rcases Nat.mod_two_eq_zero_or_one (m / 2 ^ (j : ℕ)) with h | h <;> simp [h]

@[expose] def charOrbit
    (χ : Multiplicative (Fin τ.rank → ℤ) →* ℤˣ) :
    Set (Multiplicative (Fin τ.rank → ℤ) →* ℤˣ) :=
  {χ' | ∃ t : WeylGroup τ, IsCharConj χ χ' t}

@[expose] def permLatticeHom (π : Equiv.Perm (Fin τ.rank)) :
    (Fin τ.rank → ℤ) →+ (Fin τ.rank → ℤ) where
  toFun := permLattice π
  map_zero' := rfl
  map_add' _ _ := rfl

@[expose] def permChar (ρ : Equiv.Perm (Fin τ.rank)) (χ : Multiplicative (Fin τ.rank → ℤ) →* ℤˣ) :
    Multiplicative (Fin τ.rank → ℤ) →* ℤˣ :=
  χ.comp (AddMonoidHom.toMultiplicative (permLatticeHom ρ.symm))

theorem permChar_apply (ρ : Equiv.Perm (Fin τ.rank)) (χ : Multiplicative (Fin τ.rank → ℤ) →* ℤˣ)
    (v : Fin τ.rank → ℤ) :
    permChar ρ χ (Multiplicative.ofAdd v) = χ (Multiplicative.ofAdd (permLattice ρ.symm v)) :=
  rfl

variable (τ) in
@[expose] def wordElt
    (l : List (Fin τ.rank)) : WeylGroup τ :=
  (coxeterSystem τ).wordProd l.reverse

@[expose] def thetaMap
    (ω : WeylGroup τ) (ρ : Equiv.Perm (Fin τ.rank)) (v : Fin τ.rank → ℤ) :
    Fin τ.rank → ℤ :=
  ω • permLattice ρ v

@[expose] def iterOrbit {α : Type*} (f : α → α) (a : α) : Set α :=
  Set.range fun k : ℕ => f^[k] a

@[expose] def simpleUnion (χ : Multiplicative (Fin τ.rank → ℤ) →* ℤˣ) : Set (Fin τ.rank → ℤ) :=
  ⋃ i : KernelComponent χ, (simpleRoots (componentRoots χ i) : Set (Fin τ.rank → ℤ))

@[expose] def orbitReflection
    (O : Finset (Fin τ.rank → ℤ)) : WeylGroup τ :=
  (O.toList.map rootReflection).prod

@[expose] def orbitReflectionGroup
    (θ : (Fin τ.rank → ℤ) → Fin τ.rank → ℤ)
    (Δ : Set (Fin τ.rank → ℤ)) : Subgroup (WeylGroup τ) :=
  Subgroup.closure {g | ∃ β ∈ Δ, ∃ O : Finset (Fin τ.rank → ℤ),
    (O : Set (Fin τ.rank → ℤ)) = iterOrbit θ β ∧ g = orbitReflection O}

structure ThetaProperties (ρ : Equiv.Perm (Fin τ.rank)) (p : ℕ)
    (χ : Multiplicative (Fin τ.rank → ℤ) →* ℤˣ) (ω : WeylGroup τ) : Prop where
  image_kernelRoots : thetaMap ω ρ '' kernelRoots χ = kernelRoots χ
  image_simpleUnion : thetaMap ω ρ '' simpleUnion χ = simpleUnion χ
  ncard_iterOrbit : ∀ α ∈ kernelRoots χ,
    (iterOrbit (thetaMap ω ρ) α).ncard = 1 ∨ (iterOrbit (thetaMap ω ρ) α).ncard = p
  pairwise_iterOrbit : ∀ α ∈ kernelRoots χ,
    (iterOrbit (thetaMap ω ρ) α).Pairwise fun x y => x ⬝ᵥ (τ.symmetrizedCartan *ᵥ y) = 0
  commute_rootReflection : ∀ β ∈ simpleUnion χ, ∀ x ∈ iterOrbit (thetaMap ω ρ) β,
    ∀ y ∈ iterOrbit (thetaMap ω ρ) β, Commute (rootReflection x) (rootReflection y)
  smul_mem_kernelRoots : ∀ g ∈ orbitReflectionGroup (thetaMap ω ρ) (simpleUnion χ),
    ∀ α ∈ kernelRoots χ, g • α ∈ kernelRoots χ
  smul_thetaMap : ∀ g ∈ orbitReflectionGroup (thetaMap ω ρ) (simpleUnion χ),
    ∀ v : Fin τ.rank → ℤ, g • thetaMap ω ρ v = thetaMap ω ρ (g • v)
  exists_image_iterOrbit : ∀ α ∈ kernelRoots χ,
    ∃ g ∈ orbitReflectionGroup (thetaMap ω ρ) (simpleUnion χ), ∃ β ∈ simpleUnion χ,
      (g • ·) '' iterOrbit (thetaMap ω ρ) α = iterOrbit (thetaMap ω ρ) β

structure SignRep (τ : Tag) where
  mask : ℕ
  orbitSize : ℕ
  omegaOrder : ℕ
  omegaWords : List (List (Fin τ.rank))

structure RationalToralSignDiagram (τ : Tag) (ρ : Equiv.Perm (Fin τ.rank)) (p : ℕ)
    (reps : List (SignRep τ)) : Prop where
  mask_lt : ∀ e ∈ reps, e.mask < 2 ^ τ.rank
  permChar_eq : ∀ e ∈ reps, permChar ρ (signMaskChar τ e.mask) = signMaskChar τ e.mask
  image_charOrbit : ∀ e ∈ reps,
    permChar ρ '' charOrbit (signMaskChar τ e.mask) = charOrbit (signMaskChar τ e.mask)
  card_charOrbit : ∀ e ∈ reps, Nat.card (charOrbit (signMaskChar τ e.mask)) = e.orbitSize
  pairwise_not_mem : reps.Pairwise fun e e' =>
    signMaskChar τ e'.mask ∉ charOrbit (signMaskChar τ e.mask)
  exists_rep : ∀ χ : Multiplicative (Fin τ.rank → ℤ) →* ℤˣ, permChar ρ χ ∈ charOrbit χ →
    ∃ e ∈ reps, χ ∈ charOrbit (signMaskChar τ e.mask)
  card_kernelPosStabilizer : ∀ e ∈ reps,
    Nat.card (kernelPosStabilizer (signMaskChar τ e.mask)) = e.omegaOrder
  coe_kernelPosStabilizer : ∀ e ∈ reps,
    (kernelPosStabilizer (signMaskChar τ e.mask) : Set (WeylGroup τ)) =
      {w | ∃ l ∈ e.omegaWords, wordElt τ l = w}
  theta : ∀ e ∈ reps, ∀ l ∈ e.omegaWords,
    ThetaProperties ρ p (signMaskChar τ e.mask) (wordElt τ l)

end CFSG.LieType.Chevalley.ToralSign
