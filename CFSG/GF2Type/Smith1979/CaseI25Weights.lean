module

public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RingTheory.Idempotents
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Finiteness
import Mathlib.RingTheory.IntegralDomain

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979

namespace LemmaW

section GroupRing

variable {A : Type*} [CommGroup A]

@[expose] noncomputable def eSub (U : Subgroup A) : MonoidAlgebra (ZMod 2) A :=
  ∑ᶠ u : U, MonoidAlgebra.of (ZMod 2) A (u : A)

theorem eSub_eq_sum (U : Subgroup A) [Fintype U] :
    eSub U = ∑ u : U, MonoidAlgebra.of (ZMod 2) A (u : A) :=
  finsum_eq_sum_of_fintype _

theorem sup_eq_top_of_index_eq_three {H H' : Subgroup A} (h : H.index = 3) (h' : H'.index = 3)
    (hne : H ≠ H') : H ⊔ H' = ⊤ := by
  have hd : (H ⊔ H').index ∣ 3 := h ▸ Subgroup.index_dvd_of_le le_sup_left
  rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h3
  · exact Subgroup.index_eq_one.mp h1
  · exfalso
    have key : ∀ {K : Subgroup A}, K.index = 3 → K ≤ H ⊔ H' → H ⊔ H' ≤ K := by
      intro K hK hle
      have := Subgroup.relIndex_mul_index hle
      rw [hK, h3] at this
      have h1 : K.relIndex (H ⊔ H') = 1 := by omega
      exact Subgroup.relIndex_eq_one.mp h1
    have e1 : H ⊔ H' ≤ H := key h le_sup_left
    have e2 : H ⊔ H' ≤ H' := key h' le_sup_right
    exact hne (le_antisymm (le_sup_left.trans e2) (le_sup_right.trans e1))

abbrev Hyperplane (A : Type*) [Group A] : Type _ := {H : Subgroup A // H.index = 3}

@[expose] noncomputable def eps (A : Type*) [CommGroup A] :
    Option (Hyperplane A) → MonoidAlgebra (ZMod 2) A
  | none => eSub ⊤
  | some H => eSub H.1 - eSub ⊤

theorem two_eq_zero_monoidAlgebra : (2 : MonoidAlgebra (ZMod 2) A) = 0 := by
  have h : (2 : ZMod 2) = 0 := by decide
  calc (2 : MonoidAlgebra (ZMod 2) A)
      = algebraMap (ZMod 2) (MonoidAlgebra (ZMod 2) A) 2 := (map_ofNat _ 2).symm
    _ = 0 := by rw [h, map_zero]

variable [Finite A]

theorem card_subgroup_odd (hA : ∀ a : A, a ^ 3 = 1) (U : Subgroup A) : Odd (Nat.card U) := by
  have hp : IsPGroup 3 U := fun u => ⟨1, Subtype.ext (by simp [hA])⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hp
  rw [hn]
  exact Odd.pow (by decide)

theorem of_mul_eSub {U : Subgroup A} {a : A} (ha : a ∈ U) :
    MonoidAlgebra.of (ZMod 2) A a * eSub U = eSub U := by
  haveI : Fintype U := Fintype.ofFinite U
  rw [eSub_eq_sum, Finset.mul_sum]
  simp only [← map_mul]
  exact Fintype.sum_equiv (Equiv.mulLeft (⟨a, ha⟩ : U)) _ _ (fun u => by simp)

theorem mul_eSub_of_invariant (hA : ∀ a : A, a ^ 3 = 1) {U : Subgroup A}
    {X : MonoidAlgebra (ZMod 2) A} (hX : ∀ a ∈ U, MonoidAlgebra.of (ZMod 2) A a * X = X) :
    X * eSub U = X := by
  haveI : Fintype U := Fintype.ofFinite U
  rw [eSub_eq_sum, Finset.mul_sum]
  have h1 : ∀ u : U, X * MonoidAlgebra.of (ZMod 2) A (u : A) = X := fun u => by
    rw [mul_comm]
    exact hX u u.2
  simp only [h1, Finset.sum_const, Finset.card_univ]
  rw [← Nat.card_eq_fintype_card, ← Nat.cast_smul_eq_nsmul (ZMod 2),
    ZMod.natCast_eq_one_iff_odd.mpr (card_subgroup_odd hA U), one_smul]

theorem eSub_mul_eSub_of_le (hA : ∀ a : A, a ^ 3 = 1) {U U' : Subgroup A} (h : U ≤ U') :
    eSub U * eSub U' = eSub U' := by
  rw [mul_comm]
  exact mul_eSub_of_invariant hA (fun a ha => of_mul_eSub (h ha))

theorem eSub_mul_eSub_of_sup (hA : ∀ a : A, a ^ 3 = 1) {H H' : Subgroup A} (h : H ⊔ H' = ⊤) :
    eSub H * eSub H' = eSub ⊤ := by
  set X := eSub H * eSub H' with hXdef
  let S : Subgroup A :=
    { carrier := {a | MonoidAlgebra.of (ZMod 2) A a * X = X}
      mul_mem' := fun {a b} ha hb => by
        have ha' : MonoidAlgebra.of (ZMod 2) A a * X = X := ha
        have hb' : MonoidAlgebra.of (ZMod 2) A b * X = X := hb
        show MonoidAlgebra.of (ZMod 2) A (a * b) * X = X
        rw [map_mul, mul_assoc, hb', ha']
      one_mem' := by
        show MonoidAlgebra.of (ZMod 2) A 1 * X = X
        rw [map_one, one_mul]
      inv_mem' := fun {a} ha => by
        have ha' : MonoidAlgebra.of (ZMod 2) A a * X = X := ha
        show MonoidAlgebra.of (ZMod 2) A a⁻¹ * X = X
        calc MonoidAlgebra.of (ZMod 2) A a⁻¹ * X
            = MonoidAlgebra.of (ZMod 2) A a⁻¹ * (MonoidAlgebra.of (ZMod 2) A a * X) := by rw [ha']
          _ = X := by rw [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul] }
  have hH : H ≤ S := fun a ha => by
    show MonoidAlgebra.of (ZMod 2) A a * X = X
    rw [hXdef, ← mul_assoc, of_mul_eSub ha]
  have hH' : H' ≤ S := fun a ha => by
    show MonoidAlgebra.of (ZMod 2) A a * X = X
    rw [hXdef, mul_left_comm, of_mul_eSub ha]
  have hTop : (⊤ : Subgroup A) ≤ S := h ▸ sup_le hH hH'
  have h1 : X * eSub ⊤ = X :=
    mul_eSub_of_invariant hA (fun a _ => hTop (Subgroup.mem_top a))
  have h2 : eSub H' * eSub ⊤ = eSub ⊤ := eSub_mul_eSub_of_le hA le_top
  have h3 : eSub H * eSub ⊤ = eSub ⊤ := eSub_mul_eSub_of_le hA le_top
  rw [← h1, hXdef, mul_assoc, h2, h3]

theorem orthogonalIdempotents_eps (hA : ∀ a : A, a ^ 3 = 1) : OrthogonalIdempotents (eps A) := by
  have hTT : eSub (⊤ : Subgroup A) * eSub ⊤ = eSub (⊤ : Subgroup A) :=
    eSub_mul_eSub_of_le hA le_rfl
  have hHT : ∀ H : Subgroup A, eSub H * eSub ⊤ = eSub (⊤ : Subgroup A) := fun H =>
    eSub_mul_eSub_of_le hA le_top
  have hHH : ∀ H : Subgroup A, eSub H * eSub H = eSub H := fun H =>
    eSub_mul_eSub_of_le hA le_rfl
  have hTH : ∀ H : Subgroup A, eSub (⊤ : Subgroup A) * eSub H = eSub (⊤ : Subgroup A) :=
    fun H => by rw [mul_comm]; exact hHT H
  refine ⟨?_, ?_⟩
  · rintro (_ | H)
    · exact hTT
    · show (eSub H.1 - eSub ⊤) * (eSub H.1 - eSub ⊤) = eSub H.1 - eSub ⊤
      linear_combination hHH H.1 - hHT H.1 - hTH H.1 + hTT
  · rintro (_ | H) (_ | K) hne
    · exact absurd rfl hne
    · show eSub ⊤ * (eSub K.1 - eSub ⊤) = 0
      linear_combination hTH K.1 - hTT
    · show (eSub H.1 - eSub ⊤) * eSub ⊤ = 0
      linear_combination hHT H.1 - hTT
    · have hHK : eSub H.1 * eSub K.1 = eSub (⊤ : Subgroup A) :=
        eSub_mul_eSub_of_sup hA (sup_eq_top_of_index_eq_three H.2 K.2
          (fun h => hne (congrArg some (Subtype.ext h))))
      show (eSub H.1 - eSub ⊤) * (eSub K.1 - eSub ⊤) = 0
      linear_combination hHK - hHT H.1 - hTH K.1 + hTT

theorem span_eps_eq_top (hA : ∀ a : A, a ^ 3 = 1) : Ideal.span (Set.range (eps A)) = ⊤ := by
  by_contra hne
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
  letI : Field (MonoidAlgebra (ZMod 2) A ⧸ M) := Ideal.Quotient.field M
  set mk : MonoidAlgebra (ZMod 2) A →+* MonoidAlgebra (ZMod 2) A ⧸ M := Ideal.Quotient.mk M
  let φ : A →* (MonoidAlgebra (ZMod 2) A ⧸ M) :=
    (mk.toMonoidHom).comp (MonoidAlgebra.of (ZMod 2) A)
  let χ : A →* (MonoidAlgebra (ZMod 2) A ⧸ M)ˣ := φ.toHomUnits
  haveI : Finite χ.range := Finite.of_surjective χ.rangeRestrict χ.rangeRestrict_surjective
  have hχ3 : ∀ g : χ.range, g ^ 3 = 1 := by
    rintro ⟨_, a, rfl⟩
    apply Subtype.ext
    simp [← map_pow, hA a]
  haveI : IsCyclic χ.range :=
    isCyclic_of_injective_ringHom ((Units.coeHom _).comp χ.range.subtype)
      (fun x y hxy => Subtype.ext (Units.ext hxy))
  have hidx : χ.ker.index ∣ 3 := by
    rw [Subgroup.index_ker, ← IsCyclic.exponent_eq_card]
    exact Monoid.exponent_dvd_of_forall_pow_eq_one hχ3
  have h2 : (2 : MonoidAlgebra (ZMod 2) A ⧸ M) = 0 := by
    rw [← map_ofNat mk 2, two_eq_zero_monoidAlgebra, map_zero]
  have himg : mk (eSub χ.ker) = 1 := by
    haveI : Fintype χ.ker := Fintype.ofFinite _
    rw [eSub_eq_sum, map_sum]
    have h1 : ∀ u : χ.ker, mk (MonoidAlgebra.of (ZMod 2) A (u : A)) = 1 := fun u => by
      have hu : χ (u : A) = 1 := u.2
      have := congrArg Units.val hu
      simpa [χ, φ] using this
    simp only [h1, Finset.sum_const, Finset.card_univ]
    rw [← Nat.card_eq_fintype_card]
    obtain ⟨k, hk⟩ := card_subgroup_odd hA χ.ker
    rw [hk, nsmul_eq_mul]
    push_cast
    rw [h2]
    ring
  rcases (Nat.dvd_prime Nat.prime_three).mp hidx with h1 | h3
  · have htop : χ.ker = ⊤ := Subgroup.index_eq_one.mp h1
    have hmem : eSub (⊤ : Subgroup A) ∈ M := hle (Ideal.subset_span ⟨none, rfl⟩)
    have h0 : mk (eSub (⊤ : Subgroup A)) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    rw [htop, h0] at himg
    exact zero_ne_one himg
  · have hmem : eSub χ.ker ∈ M := by
      have e1 : eSub χ.ker = eps A (some ⟨χ.ker, h3⟩) + eps A none := by simp [eps]
      rw [e1]
      exact M.add_mem (hle (Ideal.subset_span ⟨_, rfl⟩)) (hle (Ideal.subset_span ⟨_, rfl⟩))
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hmem] at himg
    exact zero_ne_one himg

theorem sum_eps (hA : ∀ a : A, a ^ 3 = 1) [Fintype (Option (Hyperplane A))] :
    ∑ i : Option (Hyperplane A), eps A i = 1 := by
  have he := orthogonalIdempotents_eps hA
  set g : MonoidAlgebra (ZMod 2) A := 1 - ∑ i, eps A i with hg
  have hker : Ideal.span (Set.range (eps A)) ≤
      LinearMap.ker (LinearMap.mulLeft (MonoidAlgebra (ZMod 2) A) g) := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    have h1 : (∑ j, eps A j) * eps A i = eps A i := by
      rw [mul_comm]
      exact he.mul_sum_of_mem (Finset.mem_univ i)
    simp only [LinearMap.mem_ker, LinearMap.mulLeft_apply, SetLike.mem_coe]
    rw [hg, sub_mul, one_mul, h1, sub_self]
  have h1 : (1 : MonoidAlgebra (ZMod 2) A) ∈
      LinearMap.ker (LinearMap.mulLeft (MonoidAlgebra (ZMod 2) A) g) :=
    hker (by rw [span_eps_eq_top hA]; trivial)
  simp only [LinearMap.mem_ker, LinearMap.mulLeft_apply, mul_one] at h1
  exact (sub_eq_zero.mp h1).symm

end GroupRing

section Idempotents

variable {ι : Type*} {k M : Type*} [Ring k] [AddCommGroup M] [Module k M]

theorem iSupIndep_range_of_orthogonalIdempotents {p : ι → Module.End k M}
    (hp : OrthogonalIdempotents p) : iSupIndep fun i => LinearMap.range (p i) := by
  rw [iSupIndep_def]
  intro i
  rw [Submodule.disjoint_def]
  intro x hx hx'
  have hle : (⨆ j, ⨆ (_ : j ≠ i), LinearMap.range (p j)) ≤ LinearMap.ker (p i) := by
    refine iSup₂_le fun j hj => ?_
    rintro _ ⟨z, rfl⟩
    rw [LinearMap.mem_ker, ← Module.End.mul_apply, hp.ortho (Ne.symm hj)]
    rfl
  have h0 : p i x = 0 := hle hx'
  obtain ⟨y, rfl⟩ := hx
  have hidem : p i (p i y) = p i y := by
    rw [← Module.End.mul_apply, (hp.idem i).eq]
  calc p i y = p i (p i y) := hidem.symm
    _ = 0 := h0

theorem iSup_range_eq_top_of_sum_eq_one [Fintype ι] {p : ι → Module.End k M}
    (h : ∑ i, p i = 1) : ⨆ i, LinearMap.range (p i) = ⊤ := by
  rw [eq_top_iff]
  intro v _
  have hv : v = ∑ i, p i v := by
    have := congrArg (fun f : Module.End k M => f v) h
    simpa [LinearMap.sum_apply] using this.symm
  rw [hv]
  exact Submodule.sum_mem _ fun i _ => Submodule.mem_iSup_of_mem i ⟨v, rfl⟩

end Idempotents

theorem finrank_eq_sum_range {k M ι : Type*} [Field k] [AddCommGroup M] [Module k M]
    [FiniteDimensional k M] [Fintype ι] [DecidableEq ι] {p : ι → Module.End k M}
    (hp : OrthogonalIdempotents p) (h : ∑ i, p i = 1) :
    Module.finrank k M = ∑ i, Module.finrank k (LinearMap.range (p i)) := by
  have hint : DirectSum.IsInternal fun i => LinearMap.range (p i) :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
      (iSupIndep_range_of_orthogonalIdempotents hp) (iSup_range_eq_top_of_sum_eq_one h)
  rw [← (LinearEquiv.ofBijective (DirectSum.coeLinearMap _) hint).finrank_eq,
    Module.finrank_directSum]

section Spaces

variable {A : Type*} [CommGroup A] {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
variable (ρ : Representation (ZMod 2) A V)

@[expose] def fixedSpace (U : Subgroup A) : Submodule (ZMod 2) V where
  carrier := {v | ∀ u ∈ U, ρ u v = v}
  zero_mem' := fun u _ => map_zero _
  add_mem' := fun {x y} hx hy u hu => by rw [map_add, hx u hu, hy u hu]
  smul_mem' := fun c x hx u hu => by rw [map_smul, hx u hu]

theorem mem_fixedSpace {U : Subgroup A} {v : V} : v ∈ fixedSpace ρ U ↔ ∀ u ∈ U, ρ u v = v :=
  Iff.rfl

@[expose] noncomputable def weightSpace (H : Subgroup A) : Submodule (ZMod 2) V :=
  LinearMap.range (ρ.asAlgebraHom (eSub H - eSub ⊤))

@[expose] noncomputable def weightFamily : Option (Hyperplane A) → Submodule (ZMod 2) V :=
  fun i => LinearMap.range (ρ.asAlgebraHom (eps A i))

theorem weightFamily_some (H : Hyperplane A) : weightFamily ρ (some H) = weightSpace ρ H.1 :=
  rfl

theorem asAlgebraHom_eSub (U : Subgroup A) [Fintype U] :
    ρ.asAlgebraHom (eSub U) = ∑ u : U, ρ (u : A) := by
  rw [eSub_eq_sum, map_sum]
  simp

variable [Finite A]

theorem asAlgebraHom_eSub_top [Fintype A] :
    ρ.asAlgebraHom (eSub (⊤ : Subgroup A)) = ∑ a : A, ρ a := by
  haveI : Fintype (⊤ : Subgroup A) := Fintype.ofFinite _
  rw [asAlgebraHom_eSub]
  exact Fintype.sum_equiv Subgroup.topEquiv.toEquiv _ _ (fun u => rfl)

theorem apply_asAlgebraHom_eSub {U : Subgroup A} {a : A} (ha : a ∈ U) (v : V) :
    ρ a (ρ.asAlgebraHom (eSub U) v) = ρ.asAlgebraHom (eSub U) v := by
  have := congrArg (fun x => ρ.asAlgebraHom x v) (of_mul_eSub ha)
  simpa [map_mul, Representation.asAlgebraHom_of, Module.End.mul_apply] using this

theorem asAlgebraHom_eSub_apply_of_mem (hA : ∀ a : A, a ^ 3 = 1) {U : Subgroup A} {v : V}
    (hv : v ∈ fixedSpace ρ U) : ρ.asAlgebraHom (eSub U) v = v := by
  haveI : Fintype U := Fintype.ofFinite U
  rw [asAlgebraHom_eSub, LinearMap.sum_apply]
  have h1 : ∀ u : U, ρ (u : A) v = v := fun u => hv u u.2
  simp only [h1, Finset.sum_const, Finset.card_univ]
  rw [← Nat.card_eq_fintype_card, ← Nat.cast_smul_eq_nsmul (ZMod 2),
    ZMod.natCast_eq_one_iff_odd.mpr (card_subgroup_odd hA U), one_smul]

theorem range_asAlgebraHom_eSub (hA : ∀ a : A, a ^ 3 = 1) (U : Subgroup A) :
    LinearMap.range (ρ.asAlgebraHom (eSub U)) = fixedSpace ρ U := by
  ext v
  constructor
  · rintro ⟨w, rfl⟩ u hu
    exact apply_asAlgebraHom_eSub ρ hu w
  · intro hv
    exact ⟨v, asAlgebraHom_eSub_apply_of_mem ρ hA hv⟩

theorem mem_weightSpace_iff (hA : ∀ a : A, a ^ 3 = 1) (H : Subgroup A) (v : V) :
    v ∈ weightSpace ρ H ↔ v ∈ fixedSpace ρ H ∧ ρ.asAlgebraHom (eSub ⊤) v = 0 := by
  have hTH : eSub (⊤ : Subgroup A) * eSub H = eSub ⊤ := by
    rw [mul_comm]
    exact eSub_mul_eSub_of_le hA le_top
  have hTT : eSub (⊤ : Subgroup A) * eSub ⊤ = eSub ⊤ := eSub_mul_eSub_of_le hA le_rfl
  constructor
  · rintro ⟨w, rfl⟩
    refine ⟨fun h hh => ?_, ?_⟩
    · have := congrArg (fun x => ρ.asAlgebraHom x w)
        (show MonoidAlgebra.of (ZMod 2) A h * (eSub H - eSub ⊤) = eSub H - eSub ⊤ by
          rw [mul_sub, of_mul_eSub hh, of_mul_eSub (Subgroup.mem_top h)])
      simpa [map_mul, Representation.asAlgebraHom_of, Module.End.mul_apply] using this
    · have := congrArg (fun x => ρ.asAlgebraHom x w)
        (show eSub (⊤ : Subgroup A) * (eSub H - eSub ⊤) = 0 by
          rw [mul_sub, hTH, hTT, sub_self])
      simpa [map_mul, Module.End.mul_apply] using this
  · rintro ⟨hv, h0⟩
    refine ⟨v, ?_⟩
    rw [map_sub, LinearMap.sub_apply, h0, sub_zero]
    exact asAlgebraHom_eSub_apply_of_mem ρ hA hv

end Spaces

section Decomposition

variable {A : Type*} [CommGroup A] [Finite A] {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
variable (ρ : Representation (ZMod 2) A V)

theorem weightFamily_none (hA : ∀ a : A, a ^ 3 = 1) : weightFamily ρ none = fixedSpace ρ ⊤ :=
  range_asAlgebraHom_eSub ρ hA ⊤

theorem orthogonalIdempotents_asAlgebraHom_eps (hA : ∀ a : A, a ^ 3 = 1) :
    OrthogonalIdempotents fun i => ρ.asAlgebraHom (eps A i) :=
  (orthogonalIdempotents_eps hA).map ρ.asAlgebraHom.toRingHom

theorem sum_asAlgebraHom_eps (hA : ∀ a : A, a ^ 3 = 1) [Fintype (Option (Hyperplane A))] :
    ∑ i, ρ.asAlgebraHom (eps A i) = 1 := by
  rw [← map_sum, sum_eps hA, map_one]

theorem iSup_weightFamily (hA : ∀ a : A, a ^ 3 = 1) : ⨆ i, weightFamily ρ i = ⊤ := by
  haveI := Fintype.ofFinite (Option (Hyperplane A))
  exact iSup_range_eq_top_of_sum_eq_one (sum_asAlgebraHom_eps ρ hA)

theorem finrank_eq_fixedSpace_add_sum (hA : ∀ a : A, a ^ 3 = 1) [FiniteDimensional (ZMod 2) V]
    [Fintype (Hyperplane A)] :
    Module.finrank (ZMod 2) V = Module.finrank (ZMod 2) (fixedSpace ρ ⊤) +
      ∑ H : Hyperplane A, Module.finrank (ZMod 2) (weightSpace ρ H.1) := by
  classical
  have key := finrank_eq_sum_range (orthogonalIdempotents_asAlgebraHom_eps ρ hA)
    (sum_asAlgebraHom_eps ρ hA)
  rw [Fintype.sum_option] at key
  rw [key, ← range_asAlgebraHom_eSub ρ hA ⊤]
  rfl

end Decomposition

section Even

theorem even_of_two_pow_modEq_one {d : ℕ} (h : 2 ^ d ≡ 1 [MOD 3]) : Even d := by
  by_contra hodd
  rw [Nat.not_even_iff_odd] at hodd
  obtain ⟨j, rfl⟩ := hodd
  have h4 : 4 ^ j ≡ 1 [MOD 3] := by
    simpa using Nat.ModEq.pow j (show 4 ≡ 1 [MOD 3] by decide)
  have h2 : 2 ^ (2 * j + 1) ≡ 2 [MOD 3] := by
    calc 2 ^ (2 * j + 1) = 4 ^ j * 2 := by rw [pow_succ, pow_mul]; norm_num
      _ ≡ 1 * 2 [MOD 3] := h4.mul_right 2
      _ = 2 := one_mul 2
  exact absurd (h2.symm.trans h) (by decide)

variable {A : Type*} [Group A]

theorem even_finrank_of_no_fixed (hA : ∀ a : A, a ^ 3 = 1) {W : Type*} [AddCommGroup W]
    [Module (ZMod 2) W] [Module.Finite (ZMod 2) W] (σ : Representation (ZMod 2) A W)
    (hfix : ∀ w : W, (∀ a, σ a w = w) → w = 0) : Even (Module.finrank (ZMod 2) W) := by
  haveI : Finite W := Module.finite_of_finite (ZMod 2)
  letI : MulAction A W :=
    { smul := fun a w => σ a w
      one_smul := fun w => by
        show σ 1 w = w
        rw [map_one]
        rfl
      mul_smul := fun a b w => by
        show σ (a * b) w = σ a (σ b w)
        rw [map_mul]
        rfl }
  have hp : IsPGroup 3 A := fun a => ⟨1, by simp [hA]⟩
  have hmod := hp.card_modEq_card_fixedPoints W
  haveI : Unique (MulAction.fixedPoints A W) :=
    ⟨⟨⟨0, fun a => map_zero (σ a)⟩⟩, fun x => Subtype.ext (hfix x.1 fun a => x.2 a)⟩
  have hfp : Nat.card (MulAction.fixedPoints A W) = 1 := Nat.card_unique
  rw [hfp, Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W), Nat.card_zmod] at hmod
  exact even_of_two_pow_modEq_one hmod

end Even

section WeightLemmas

variable {A : Type*} [CommGroup A] [Finite A] {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
variable (ρ : Representation (ZMod 2) A V)

theorem even_finrank_weightSpace (hA : ∀ a : A, a ^ 3 = 1) [Module.Finite (ZMod 2) V]
    (H : Subgroup A) : Even (Module.finrank (ZMod 2) (weightSpace ρ H)) := by
  have hinv : ∀ a : A, weightSpace ρ H ≤ (weightSpace ρ H).comap (ρ a) := by
    intro a w hw
    rw [Submodule.mem_comap, mem_weightSpace_iff ρ hA]
    obtain ⟨hfix, h0⟩ := (mem_weightSpace_iff ρ hA H w).mp hw
    refine ⟨fun h hh => ?_, ?_⟩
    · rw [← Module.End.mul_apply, ← map_mul, mul_comm, map_mul, Module.End.mul_apply,
        hfix h hh]
    · have := congrArg (fun x => ρ.asAlgebraHom x w)
        (show eSub (⊤ : Subgroup A) * MonoidAlgebra.of (ZMod 2) A a = eSub ⊤ by
          rw [mul_comm]
          exact of_mul_eSub (Subgroup.mem_top a))
      simpa [map_mul, Representation.asAlgebraHom_of, Module.End.mul_apply, h0] using this
  refine even_finrank_of_no_fixed hA (ρ.subrepresentation (weightSpace ρ H) hinv) ?_
  intro w hw
  have hw' : ∀ a, ρ a (w : V) = w := fun a => congrArg Subtype.val (hw a)
  have h1 := asAlgebraHom_eSub_apply_of_mem ρ hA (U := ⊤) (v := (w : V)) (fun u _ => hw' u)
  have h2 := ((mem_weightSpace_iff ρ hA H w).mp w.2).2
  exact Subtype.ext (h1.symm.trans h2)

theorem eq_one_of_forall_mem_hyperplane (hA : ∀ a : A, a ^ 3 = 1) {a : A}
    (ha : ∀ H : Hyperplane A, weightSpace ρ H.1 ≠ ⊥ → a ∈ H.1) : ρ a = 1 := by
  have hle : ⨆ i, weightFamily ρ i ≤ LinearMap.ker (ρ a - 1) := by
    refine iSup_le fun i => ?_
    rcases i with _ | H
    · rw [weightFamily_none ρ hA]
      intro v hv
      rw [LinearMap.mem_ker, LinearMap.sub_apply, hv a (Subgroup.mem_top a),
        Module.End.one_apply, sub_self]
    · rw [weightFamily_some]
      intro v hv
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
      by_cases hbot : weightSpace ρ H.1 = ⊥
      · rw [hbot, Submodule.mem_bot] at hv
        rw [hv, map_zero]
      · exact ((mem_weightSpace_iff ρ hA H.1 v).mp hv).1 a (ha H hbot)
  rw [iSup_weightFamily ρ hA, top_le_iff] at hle
  refine LinearMap.ext fun v => ?_
  have hv : v ∈ LinearMap.ker (ρ a - 1) := by rw [hle]; exact Submodule.mem_top
  rwa [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hv

theorem iInf_hyperplane_weightSpace_ne_bot (hA : ∀ a : A, a ^ 3 = 1)
    (hfaith : Function.Injective ρ) :
    ⨅ H : {H : Hyperplane A // weightSpace ρ H.1 ≠ ⊥}, H.1.1 = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro a ha
  rw [Subgroup.mem_iInf] at ha
  exact hfaith ((eq_one_of_forall_mem_hyperplane ρ hA fun H hH => ha ⟨H, hH⟩).trans
    (map_one ρ).symm)

theorem map_weightSpace (hA : ∀ a : A, a ^ 3 = 1) {b : V ≃ₗ[ZMod 2] V} {σ : A ≃* A}
    (hb : ∀ a v, ρ (σ a) (b v) = b (ρ a v)) (H : Subgroup A) :
    (weightSpace ρ H).map (b : V →ₗ[ZMod 2] V) = weightSpace ρ (H.map σ.toMonoidHom) := by
  haveI : Fintype A := Fintype.ofFinite A
  have hT : ∀ v, ρ.asAlgebraHom (eSub ⊤) (b v) = b (ρ.asAlgebraHom (eSub ⊤) v) := by
    intro v
    rw [asAlgebraHom_eSub_top, LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
    calc ∑ a : A, ρ a (b v) = ∑ a : A, ρ (σ a) (b v) :=
          (Fintype.sum_equiv σ.toEquiv (fun a => ρ (σ a) (b v)) (fun a => ρ a (b v))
            (fun a => rfl)).symm
      _ = ∑ a : A, b (ρ a v) := Finset.sum_congr rfl fun a _ => hb a v
  ext w
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨v, hv, rfl⟩
    rw [mem_weightSpace_iff ρ hA] at hv ⊢
    refine ⟨fun h' hh' => ?_, ?_⟩
    · obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.mp hh'
      show ρ (σ h) (b v) = b v
      rw [hb, hv.1 h hh]
    · rw [LinearEquiv.coe_coe, hT, hv.2, map_zero]
  · intro hw
    rw [mem_weightSpace_iff ρ hA] at hw
    refine ⟨b.symm w, ?_, b.apply_symm_apply w⟩
    rw [mem_weightSpace_iff ρ hA]
    refine ⟨fun h hh => ?_, ?_⟩
    · apply b.injective
      rw [← hb, b.apply_symm_apply]
      exact hw.1 (σ h) (Subgroup.mem_map_of_mem _ hh)
    · apply b.injective
      rw [← hT, b.apply_symm_apply, hw.2, map_zero]

theorem finrank_weightSpace_map (hA : ∀ a : A, a ^ 3 = 1) {b : V ≃ₗ[ZMod 2] V} {σ : A ≃* A}
    (hb : ∀ a v, ρ (σ a) (b v) = b (ρ a v)) (H : Subgroup A) :
    Module.finrank (ZMod 2) (weightSpace ρ (H.map σ.toMonoidHom)) =
      Module.finrank (ZMod 2) (weightSpace ρ H) := by
  rw [← map_weightSpace ρ hA hb H]
  exact b.finrank_map_eq _

end WeightLemmas

section Corollary

variable {A : Type*} [CommGroup A] [Finite A] {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
variable (ρ : Representation (ZMod 2) A V)

theorem exists_hyperplane_weightSpace_ne_bot (hA : ∀ a : A, a ^ 3 = 1)
    (hfaith : Function.Injective ρ) [Nontrivial A] :
    ∃ H : Hyperplane A, weightSpace ρ H.1 ≠ ⊥ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨a, ha⟩ := exists_ne (1 : A)
  refine ha (hfaith ?_)
  rw [map_one]
  exact eq_one_of_forall_mem_hyperplane ρ hA fun H hH => absurd (hcon H) hH

theorem two_le_finrank_weightSpace (hA : ∀ a : A, a ^ 3 = 1) [Module.Finite (ZMod 2) V]
    {H : Subgroup A} (h : weightSpace ρ H ≠ ⊥) :
    2 ≤ Module.finrank (ZMod 2) (weightSpace ρ H) := by
  have hne : Module.finrank (ZMod 2) (weightSpace ρ H) ≠ 0 := fun h0 =>
    h (Submodule.finrank_eq_zero.mp h0)
  obtain ⟨k, hk⟩ := even_finrank_weightSpace ρ hA H
  omega

theorem sum_finrank_weightSpace_le (hA : ∀ a : A, a ^ 3 = 1) [Module.Finite (ZMod 2) V]
    (T : Finset (Subgroup A)) (hT : ∀ H ∈ T, H.index = 3) :
    ∑ H ∈ T, Module.finrank (ZMod 2) (weightSpace ρ H) ≤ Module.finrank (ZMod 2) V := by
  classical
  haveI : Fintype (Hyperplane A) := Fintype.ofFinite _
  rw [finrank_eq_fixedSpace_add_sum ρ hA]
  refine le_trans ?_ (Nat.le_add_left _ _)
  rw [← Finset.sum_subtype_of_mem (fun H => Module.finrank (ZMod 2) (weightSpace ρ H)) hT]
  exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)

theorem two_mul_le_finrank (hA : ∀ a : A, a ^ 3 = 1) [Module.Finite (ZMod 2) V]
    (hfaith : Function.Injective ρ) [Nontrivial A] {B : Type*} (β : B → (V ≃ₗ[ZMod 2] V))
    (σ : B → (A ≃* A)) (hβ : ∀ b a v, ρ (σ b a) (β b v) = β b (ρ a v)) {m : ℕ}
    (horb : ∀ H : Subgroup A, H.index = 3 →
      m ≤ (Set.range fun b => H.map (σ b).toMonoidHom).ncard) :
    2 * m ≤ Module.finrank (ZMod 2) V := by
  classical
  obtain ⟨H₀, hH₀⟩ := exists_hyperplane_weightSpace_ne_bot ρ hA hfaith
  have h2 : 2 ≤ Module.finrank (ZMod 2) (weightSpace ρ H₀.1) :=
    two_le_finrank_weightSpace ρ hA hH₀
  set 𝒪 : Set (Subgroup A) := Set.range fun b => H₀.1.map (σ b).toMonoidHom with h𝒪
  have hfin : 𝒪.Finite := Set.toFinite _
  have hidx : ∀ K ∈ 𝒪, K.index = 3 := by
    rintro _ ⟨b, rfl⟩
    exact (Subgroup.index_map_equiv H₀.1 (σ b)).trans H₀.2
  have hdim : ∀ K ∈ 𝒪, Module.finrank (ZMod 2) (weightSpace ρ K) =
      Module.finrank (ZMod 2) (weightSpace ρ H₀.1) := by
    rintro _ ⟨b, rfl⟩
    exact finrank_weightSpace_map ρ hA (hβ b) H₀.1
  have hsum := sum_finrank_weightSpace_le ρ hA hfin.toFinset
    (fun K hK => hidx K (hfin.mem_toFinset.mp hK))
  calc 2 * m ≤ 2 * 𝒪.ncard := Nat.mul_le_mul_left 2 (horb H₀.1 H₀.2)
    _ = ∑ _K ∈ hfin.toFinset, 2 := by
      rw [Finset.sum_const, smul_eq_mul, ← Set.ncard_eq_toFinset_card 𝒪 hfin, mul_comm]
    _ ≤ ∑ K ∈ hfin.toFinset, Module.finrank (ZMod 2) (weightSpace ρ K) :=
      Finset.sum_le_sum fun K hK => by
        rw [hdim K (hfin.mem_toFinset.mp hK)]
        exact h2
    _ ≤ Module.finrank (ZMod 2) V := hsum

end Corollary

end LemmaW

end CFSG.GF2Type.Smith1979
