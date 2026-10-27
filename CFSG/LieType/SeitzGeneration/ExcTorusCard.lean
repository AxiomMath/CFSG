module

public import CFSG.RankThree.PartOne.KE.CTTorusFixed

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KE
  CFSG.RankThree.PartOne.KE.CTTorus
open scoped Matrix

section Lattice

variable {r : ℕ}

@[expose] def lat (B : Matrix (Fin r) (Fin r) ℤ) : AddSubgroup (Fin r → ℤ) :=
  (LinearMap.range B.mulVecLin).toAddSubgroup

theorem natCard_quot_lat (B : Matrix (Fin r) (Fin r) ℤ) (hB : B.det ≠ 0) :
    Nat.card ((Fin r → ℤ) ⧸ lat B) = B.det.natAbs := by
  have hli : LinearIndependent ℤ B.col := Matrix.linearIndependent_cols_of_det_ne_zero hB
  have hspan : LinearMap.range B.mulVecLin = Submodule.span ℤ (Set.range B.col) :=
    Matrix.range_mulVecLin B
  have h := Submodule.natAbs_det_basis_change (Pi.basisFun ℤ (Fin r)) (LinearMap.range B.mulVecLin)
    ((Module.Basis.span hli).map (LinearEquiv.ofEq _ _ hspan.symm))
  have hcomp : ((↑) ∘ ((Module.Basis.span hli).map (LinearEquiv.ofEq _ _ hspan.symm)) :
      Fin r → Fin r → ℤ) = B.col := by
    funext j
    simp [Module.Basis.span_apply]
  rw [hcomp, Module.Basis.det_apply] at h
  exact h.symm

end Lattice

section Characters

variable {r : ℕ} {L : Type} [Field L]

@[expose] def charKerEquiv (B : Matrix (Fin r) (Fin r) ℤ) :
    (Multiplicative ((Fin r → ℤ) ⧸ lat B) →* Lˣ) ≃
      {χ : Multiplicative (Fin r → ℤ) →* Lˣ //
        ∀ u, χ (Multiplicative.ofAdd (B *ᵥ u)) = 1} where
  toFun φ := ⟨φ.comp (QuotientAddGroup.mk' (lat B)).toMultiplicative, fun u => by
    have : QuotientAddGroup.mk' (lat B) (B *ᵥ u) = 0 :=
      (QuotientAddGroup.eq_zero_iff _).2 ⟨u, rfl⟩
    show φ (Multiplicative.ofAdd (QuotientAddGroup.mk' (lat B) (B *ᵥ u))) = 1
    rw [this]
    exact map_one φ⟩
  invFun χ := AddMonoidHom.toMultiplicativeLeft
    (QuotientAddGroup.lift (lat B) (MonoidHom.toAdditiveRight χ.1) (by
      rintro _ ⟨u, rfl⟩
      exact congrArg Additive.ofMul (χ.2 u)))
  left_inv φ := by
    refine MonoidHom.ext fun x => ?_
    obtain ⟨y, hy⟩ := QuotientAddGroup.mk_surjective (Multiplicative.toAdd x)
    have hx : x = Multiplicative.ofAdd (QuotientAddGroup.mk y : (Fin r → ℤ) ⧸ lat B) := by
      rw [hy]
      rfl
    rw [hx]
    rfl
  right_inv χ := by
    apply Subtype.ext
    ext u
    rfl

theorem natCard_charKer (B : Matrix (Fin r) (Fin r) ℤ) (hB : B.det ≠ 0) [IsAlgClosed L] {ℓ : ℕ}
    [CharP L ℓ] (hcop : ¬ ℓ ∣ B.det.natAbs) :
    Nat.card {χ : Multiplicative (Fin r → ℤ) →* Lˣ //
      ∀ u, χ (Multiplicative.ofAdd (B *ᵥ u)) = 1} = B.det.natAbs := by
  have hcard := natCard_quot_lat B hB
  have hfin : Finite ((Fin r → ℤ) ⧸ lat B) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; simpa using hB)
  have hfinG : Finite (Multiplicative ((Fin r → ℤ) ⧸ lat B)) := hfin
  have hnz : NeZero ((B.det.natAbs : ℕ) : L) := ⟨fun h => hcop ((CharP.cast_eq_zero_iff L ℓ _).1 h)⟩
  have hn0 : B.det.natAbs ≠ 0 := Int.natAbs_ne_zero.2 hB
  have : NeZero B.det.natAbs := ⟨hn0⟩
  have : HasEnoughRootsOfUnity L B.det.natAbs := IsSepClosed.hasEnoughRootsOfUnity L _
  have hexp : Monoid.exponent (Multiplicative ((Fin r → ℤ) ⧸ lat B)) ∣ B.det.natAbs := by
    have := Group.exponent_dvd_nat_card (G := Multiplicative ((Fin r → ℤ) ⧸ lat B))
    rwa [show Nat.card (Multiplicative ((Fin r → ℤ) ⧸ lat B)) = B.det.natAbs from hcard] at this
  have : HasEnoughRootsOfUnity L (Monoid.exponent (Multiplicative ((Fin r → ℤ) ⧸ lat B))) :=
    HasEnoughRootsOfUnity.of_dvd L hexp
  have h1 := CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity
    (Multiplicative ((Fin r → ℤ) ⧸ lat B)) L
  rw [← Nat.card_congr (charKerEquiv B), h1]
  exact hcard

end Characters

section Torus

variable {τ : Tag} {L : Type} [Field L]

@[expose] def charHom (a : Fin τ.rank → Lˣ) : Multiplicative (Fin τ.rank → ℤ) →* Lˣ where
  toFun v := rootChar a (Multiplicative.toAdd v)
  map_one' := rootChar_zero a
  map_mul' _ _ := rootChar_add a _ _

theorem rootChar_eq_charHom_of_single (χ : Multiplicative (Fin τ.rank → ℤ) →* Lˣ)
    (u : Fin τ.rank → ℤ) :
    rootChar (fun i => χ (Multiplicative.ofAdd (Pi.single i 1))) u =
      χ (Multiplicative.ofAdd u) := by
  have hv : u = ∑ i, u i • (Pi.single i 1 : Fin τ.rank → ℤ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hv]
  conv_rhs => rw [hv]
  rw [rootChar_sum, ofAdd_sum, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [rootChar_zsmul, rootChar_single, ofAdd_zsmul, map_zpow]

theorem natCard_fixedCharTuples [IsAlgClosed L] (M : Matrix (Fin τ.rank) (Fin τ.rank) ℤ)
    (Fr : L →+* L) {q ℓ : ℕ} [CharP L ℓ] (hFr : ∀ c, Fr c = c ^ q)
    (hB : (M - (q : ℤ) • (1 : Matrix (Fin τ.rank) (Fin τ.rank) ℤ)).det ≠ 0)
    (hcop : ¬ ℓ ∣ (M - (q : ℤ) • (1 : Matrix (Fin τ.rank) (Fin τ.rank) ℤ)).det.natAbs) :
    Nat.card (fixedCharTuples M Fr) =
      (M - (q : ℤ) • (1 : Matrix (Fin τ.rank) (Fin τ.rank) ℤ)).det.natAbs := by
  set B : Matrix (Fin τ.rank) (Fin τ.rank) ℤ := M - (q : ℤ) • 1 with hBdef
  have hBu : ∀ u, B *ᵥ u = M *ᵥ u - (q : ℤ) • u := fun u => by
    rw [hBdef, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hmem : ∀ a : Fin τ.rank → Lˣ, a ∈ fixedCharTuples M Fr ↔
      ∀ u, charHom a (Multiplicative.ofAdd (B *ᵥ u)) = 1 := fun a => by
    rw [mem_fixedCharTuples_iff]
    refine forall_congr' fun u => ?_
    show _ ↔ rootChar a (B *ᵥ u) = 1
    rw [hBu, rootChar_sub, rootChar_zsmul, zpow_natCast, mul_inv_eq_one, map_units_eq_pow hFr]
  rw [← natCard_charKer B hB hcop (L := L)]
  refine Nat.card_congr (Equiv.ofBijective (fun a => ⟨charHom a.1, (hmem a.1).1 a.2⟩) ⟨?_, ?_⟩)
  · intro a b h
    apply Subtype.ext
    funext i
    have h1 := congrArg (fun χ : {χ : Multiplicative (Fin τ.rank → ℤ) →* Lˣ // _} =>
      χ.1 (Multiplicative.ofAdd (Pi.single i 1))) h
    have h2 : rootChar a.1 (Pi.single i 1) = rootChar b.1 (Pi.single i 1) := h1
    have h3 := rootChar_single (τ := τ) a.1 i
    have h4 := rootChar_single (τ := τ) b.1 i
    rw [h3, h4] at h2
    exact h2
  · rintro ⟨χ, hχ⟩
    refine ⟨⟨fun i => χ (Multiplicative.ofAdd (Pi.single i 1)), (hmem _).2 ?_⟩, ?_⟩
    · intro u
      have := rootChar_eq_charHom_of_single χ (B *ᵥ u)
      exact this.trans (hχ u)
    · apply Subtype.ext
      refine MonoidHom.ext fun v => ?_
      exact rootChar_eq_charHom_of_single χ (Multiplicative.toAdd v)

end Torus

end CFSG.LieType.SeitzGeneration
