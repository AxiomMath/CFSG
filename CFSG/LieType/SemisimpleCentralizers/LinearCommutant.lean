module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitKGSLBasic

public section

open Matrix

namespace CFSG.LieType.SemisimpleCentralizers

open CFSG.StandardType.LinNonsplit

theorem centralizer_mulEquiv_pi_generalLinearGroup_overField {K : Type} [Field K] [Finite K]
    {ι : Type} [Fintype ι] [DecidableEq ι] (A : Subgroup (GL ι K))
    (hA : (Nat.card A : K) ≠ 0) :
    ∃ (n : ℕ) (D : Fin n → Type) (_ : ∀ i, Field (D i)) (_ : ∀ i, Finite (D i))
      (_ : ∀ i, Algebra K (D i)) (d : Fin n → ℕ),
      (∀ i, 0 < Module.finrank K (D i) ∧
        Nat.card (D i) = Nat.card K ^ Module.finrank K (D i)) ∧
      (∀ i, ringChar (D i) = ringChar K) ∧ (∀ i, 0 < d i) ∧
      Nonempty (Subgroup.centralizer (A : Set (GL ι K)) ≃* Π i, GL (Fin (d i)) (D i)) := by
  classical
  let n := Fintype.card ι
  let eι : ι ≃ Fin n := Fintype.equivFin ι
  let φ : GL ι K ≃* GL (Fin n) K := Units.mapEquiv (Matrix.reindexAlgEquiv K K eι)
  let A' : Subgroup (GL (Fin n) K) := A.map φ.toMonoidHom
  have hcardNat : Nat.card A' = Nat.card A := by
    change Nat.card ↥(A.map φ.toMonoidHom) = Nat.card ↥A
    exact Subgroup.card_map_of_injective (f := φ.toMonoidHom) (K := A) φ.injective
  have hcard : (Nat.card A' : K) ≠ 0 := by
    rw [hcardNat]
    exact hA
  obtain ⟨r, D, d, hField, hFinite, hAlg, Φ, θ, hd, hΦinj, hΦrange, hθinj, hθrange, hθapply⟩ :=
    exists_piMat_commutant A' hcard
  refine ⟨r, D, hField, hFinite, hAlg, d, ?_, ?_, ?_, ?_⟩
  · intro i
    letI : Field (D i) := hField i
    letI : Finite (D i) := hFinite i
    letI : Algebra K (D i) := hAlg i
    exact ⟨Module.finrank_pos, Module.natCard_eq_pow_finrank⟩
  · intro i
    letI : Algebra K (D i) := hAlg i
    letI : Field (D i) := hField i
    rw [ringChar.eq_iff]
    exact charP_of_injective_algebraMap (FaithfulSMul.algebraMap_injective K (D i)) (ringChar K)
  · intro i
    exact Nat.pos_of_ne_zero (NeZero.ne (d i))
  · have hcent : (Subgroup.centralizer (A : Set (GL ι K))).map φ.toMonoidHom =
        Subgroup.centralizer (A' : Set (GL (Fin n) K)) := by
      ext y
      simp only [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_iff]
      constructor
      · intro h g hg
        obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hg
        simpa using congrArg φ (h a ha)
      · intro h a ha
        replace h := h (φ a) (Subgroup.mem_map.mpr ⟨a, ha, rfl⟩)
        simpa using congrArg φ.symm h
    let θ' : (Π i, GL (Fin (d i)) (D i)) →*
        Subgroup.centralizer (A' : Set (GL (Fin n) K)) :=
      θ.codRestrict _ (fun w => by
        rw [← hθrange]
        exact MonoidHom.mem_range.mpr ⟨w, rfl⟩)
    have hθ'inj : Function.Injective θ' := fun x y hxy =>
      hθinj (Subtype.ext_iff.mp hxy)
    have hθ'surj : Function.Surjective θ' := by
      intro y
      have hy : (y : GL (Fin n) K) ∈ θ.range := by rw [hθrange]; exact y.2
      obtain ⟨w, hw⟩ := MonoidHom.mem_range.mp hy
      exact ⟨w, Subtype.ext hw⟩
    let eC' : Subgroup.centralizer (A' : Set (GL (Fin n) K)) ≃*
        Π i, GL (Fin (d i)) (D i) :=
      (MulEquiv.ofBijective θ' ⟨hθ'inj, hθ'surj⟩).symm
    let eC : Subgroup.centralizer (A : Set (GL ι K)) ≃*
        Subgroup.centralizer (A' : Set (GL (Fin n) K)) :=
      (Subgroup.equivMapOfInjective (Subgroup.centralizer (A : Set (GL ι K)))
        φ.toMonoidHom φ.injective).trans (MulEquiv.subgroupCongr hcent)
    exact ⟨eC.trans eC'⟩

theorem centralizer_mulEquiv_pi_generalLinearGroup {K : Type} [Field K] [Finite K]
    {ι : Type} [Fintype ι] [DecidableEq ι] (A : Subgroup (GL ι K))
    (hA : (Nat.card A : K) ≠ 0) :
    ∃ (n : ℕ) (D : Fin n → Type) (_ : ∀ i, Field (D i)) (_ : ∀ i, Finite (D i))
      (d : Fin n → ℕ),
      (∀ i, ringChar (D i) = ringChar K) ∧ (∀ i, 0 < d i) ∧
      Nonempty (Subgroup.centralizer (A : Set (GL ι K)) ≃* Π i, GL (Fin (d i)) (D i)) := by
  obtain ⟨n, D, hField, hFinite, _hAlg, d, _hcard, hchar, hd, he⟩ :=
    centralizer_mulEquiv_pi_generalLinearGroup_overField A hA
  exact ⟨n, D, hField, hFinite, d, hchar, hd, he⟩

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

variable {C : Type*} [Group C] {H : ι → Type*} [∀ i, Group (H i)]

end CFSG.LieType.SemisimpleCentralizers
