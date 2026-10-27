module

public import CFSG.Adapters.TauCetiExceptional.ReeEquiv

public noncomputable section

namespace CFSG.TauCetiBridge.Ree

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Quasithin.G2U CFSG.TauCetiBridge.BigCell TauCeti
open CFSG.LieType.Chevalley TauCeti.G2ShortRoot.PrimeField

variable {L : Type} [Field L] [Algebra (ZMod 3) L] (hZ : ZerosInAdjoint L)

@[expose] def nativeSteinberg (S : points L →* points L) :
    adjointGroup .G2 L →* adjointGroup .G2 L :=
  ((adEquiv hZ).toMonoidHom.comp S).comp (adEquiv hZ).symm.toMonoidHom

theorem nativeSteinberg_comp (S : points L →* points L) :
    ((adEquiv hZ : points L ≃* adjointGroup .G2 L) : points L →* adjointGroup .G2 L).comp S =
      (nativeSteinberg hZ S).comp
        ((adEquiv hZ : points L ≃* adjointGroup .G2 L) : points L →* adjointGroup .G2 L) := by
  ext g
  simp [nativeSteinberg]

@[expose] def fixedPointCandidateEquiv (S : points L →* points L) :
    FixedPointCandidate S ≃* FixedPointCandidate (nativeSteinberg hZ S) :=
  FixedPointCandidate.congr (adEquiv hZ) (nativeSteinberg_comp hZ S)

abbrev reeExp (a : ℕ) (i : Fin Tag.G2.rank) : ℕ :=
  if i ∈ reeG2Long then 3 ^ a else 3 ^ (a + 1)

theorem nodeMap_swap (i : Fin 2) : nodeMap (Equiv.swap 0 1 i) = reeG2Perm (nodeMap i) := by
  fin_cases i <;> rfl

theorem reeExp_nodeMap_zero (a : ℕ) : reeExp a (nodeMap 0) = 3 ^ (a + 1) :=
  ite_eq_right (by decide)

theorem reeExp_nodeMap_one (a : ℕ) : reeExp a (nodeMap 1) = 3 ^ a :=
  ite_eq_left (by decide)

theorem mul_specialIsogenyExponent_inl (a : ℕ) :
    ∀ i : Fin 2, 3 ^ a * specialIsogenyExponent (.inl i) = reeExp a (nodeMap i)
  | 0 => by rw [reeExp_nodeMap_zero, specialIsogenyExponent_inl, ite_eq_left rfl, pow_succ]
  | 1 => by
    rw [reeExp_nodeMap_one, specialIsogenyExponent_inl, ite_eq_right (by decide), mul_one]

theorem mul_specialIsogenyExponent_inr (a : ℕ) :
    ∀ i : Fin 2, 3 ^ a * specialIsogenyExponent (.inr i) = reeExp a (nodeMap i)
  | 0 => by rw [reeExp_nodeMap_zero, specialIsogenyExponent_inr, ite_eq_left rfl, pow_succ]
  | 1 => by
    rw [reeExp_nodeMap_one, specialIsogenyExponent_inr, ite_eq_right (by decide), mul_one]

@[expose] def IsReeSteinberg (a : ℕ) (S : points L →* points L) : Prop :=
  ∀ (k : Fin 2 ⊕ Fin 2) (u : L), S (rootSubgroupPoints k L (Multiplicative.ofAdd u)) =
    rootSubgroupPoints (specialIsogenyRootIndex k) L
      (Multiplicative.ofAdd (u ^ (3 ^ a * specialIsogenyExponent k)))

variable {a : ℕ} {S : points L →* points L}

theorem nativeSteinberg_xElement
    (hS : IsReeSteinberg a S) (i : Fin Tag.G2.rank) (c : L) :
    nativeSteinberg hZ S (xElement i c) = xElement (reeG2Perm i) (c ^ reeExp a i) := by
  obtain ⟨j, rfl⟩ := nodeMap_surjective i
  rw [← adEquiv_rootSubgroupPoints_inl hZ j c]
  simp only [nativeSteinberg, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.symm_apply_apply]
  rw [hS, specialIsogenyRootIndex_inl, adEquiv_rootSubgroupPoints_inl, nodeMap_swap,
    mul_specialIsogenyExponent_inl]

theorem nativeSteinberg_yElement
    (hS : IsReeSteinberg a S) (i : Fin Tag.G2.rank) (c : L) :
    nativeSteinberg hZ S (yElement i c) = yElement (reeG2Perm i) (c ^ reeExp a i) := by
  obtain ⟨j, rfl⟩ := nodeMap_surjective i
  rw [← adEquiv_rootSubgroupPoints_inr hZ j c]
  simp only [nativeSteinberg, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.symm_apply_apply]
  rw [hS, specialIsogenyRootIndex_inr, adEquiv_rootSubgroupPoints_inr, nodeMap_swap,
    mul_specialIsogenyExponent_inr]

end CFSG.TauCetiBridge.Ree
