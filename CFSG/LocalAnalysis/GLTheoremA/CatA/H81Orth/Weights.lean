module

public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RingTheory.Idempotents
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.Data.SetLike.Fintype
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H81Orth.Wt

section GroupRing

variable {K : Type*} [Field K] {A : Type*} [CommGroup A] {p : ℕ}

@[expose] noncomputable def eSub (U : Subgroup A) : MonoidAlgebra K A :=
  ((Nat.card U : K))⁻¹ • ∑ᶠ u : U, MonoidAlgebra.of K A (u : A)

theorem eSub_eq_sum (U : Subgroup A) [Fintype U] :
    eSub U = ((Nat.card U : K))⁻¹ • ∑ u : U, MonoidAlgebra.of K A (u : A) := by
  rw [eSub, finsum_eq_sum_of_fintype]

private theorem eq_top_of_index_prime {H L : Subgroup A} (hp : p.Prime) (h : H.index = p)
    (hle : H ≤ L) (hne : L ≠ H) : L = ⊤ := by
  have hd : L.index ∣ p := h ▸ Subgroup.index_dvd_of_le hle
  rcases (Nat.dvd_prime hp).mp hd with h1 | hpp
  · exact Subgroup.index_eq_one.mp h1
  · exfalso
    have h3 := Subgroup.relIndex_mul_index hle
    rw [hpp, h] at h3
    have h1 : H.relIndex L = 1 := Nat.eq_of_mul_eq_mul_right hp.pos (h3.trans (one_mul p).symm)
    exact hne (le_antisymm (Subgroup.relIndex_eq_one.mp h1) hle)

private theorem sup_eq_top_of_index_eq_prime {H H' : Subgroup A} (hp : p.Prime) (h : H.index = p)
    (h' : H'.index = p) (hne : H ≠ H') : H ⊔ H' = ⊤ := by
  by_cases hL : H ⊔ H' = H
  · have hle : H' ≤ H := hL ▸ le_sup_right
    have htop := eq_top_of_index_prime hp h' hle hne
    rw [htop, Subgroup.index_top] at h
    exact absurd h.symm hp.ne_one
  · exact eq_top_of_index_prime hp h le_sup_left hL

abbrev Hyperplane (A : Type*) [Group A] (p : ℕ) : Type _ := {H : Subgroup A // H.index = p}

variable (K A p) in
@[expose] noncomputable def eps : Option (Hyperplane A p) → MonoidAlgebra K A
  | none => eSub ⊤
  | some H => eSub H.1 - eSub ⊤

variable [Finite A]

theorem card_subgroup_ne_zero (hp : p.Prime) (hA : ∀ a : A, a ^ p = 1) (hpK : (p : K) ≠ 0)
    (U : Subgroup A) : (Nat.card U : K) ≠ 0 := by
  haveI := Fact.mk hp
  have hP : IsPGroup p U := fun u => ⟨1, Subtype.ext (by simp [hA])⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hP
  rw [hn, Nat.cast_pow]
  exact pow_ne_zero n hpK

theorem of_mul_eSub {U : Subgroup A} {a : A} (ha : a ∈ U) :
    MonoidAlgebra.of K A a * eSub U = eSub U := by
  haveI : Fintype U := Fintype.ofFinite U
  rw [eSub_eq_sum, mul_smul_comm, Finset.mul_sum]
  simp only [← map_mul]
  congr 1
  exact Fintype.sum_equiv (Equiv.mulLeft (⟨a, ha⟩ : U)) _ _ (fun u => by simp)

variable (hp : p.Prime) (hA : ∀ a : A, a ^ p = 1) (hpK : (p : K) ≠ 0)

include hp hA hpK

theorem mul_eSub_of_invariant {U : Subgroup A} {X : MonoidAlgebra K A}
    (hX : ∀ a ∈ U, MonoidAlgebra.of K A a * X = X) : X * eSub U = X := by
  haveI : Fintype U := Fintype.ofFinite U
  rw [eSub_eq_sum, mul_smul_comm, Finset.mul_sum]
  have h1 : ∀ u : U, X * MonoidAlgebra.of K A (u : A) = X := fun u => by
    rw [mul_comm]
    exact hX u u.2
  simp only [h1, Finset.sum_const, Finset.card_univ]
  rw [← Nat.card_eq_fintype_card, ← Nat.cast_smul_eq_nsmul K, smul_smul,
    inv_mul_cancel₀ (card_subgroup_ne_zero hp hA hpK U), one_smul]

theorem eSub_mul_eSub_of_le {U U' : Subgroup A} (h : U ≤ U') :
    eSub U * eSub U' = (eSub U' : MonoidAlgebra K A) := by
  rw [mul_comm]
  exact mul_eSub_of_invariant hp hA hpK (fun a ha => of_mul_eSub (h ha))

theorem eSub_mul_eSub_of_sup {H H' : Subgroup A} (h : H ⊔ H' = ⊤) :
    eSub H * eSub H' = (eSub ⊤ : MonoidAlgebra K A) := by
  set X : MonoidAlgebra K A := eSub H * eSub H' with hXdef
  let S : Subgroup A :=
    { carrier := {a | MonoidAlgebra.of K A a * X = X}
      mul_mem' := fun {a b} ha hb => by
        have ha' : MonoidAlgebra.of K A a * X = X := ha
        have hb' : MonoidAlgebra.of K A b * X = X := hb
        show MonoidAlgebra.of K A (a * b) * X = X
        rw [map_mul, mul_assoc, hb', ha']
      one_mem' := by
        show MonoidAlgebra.of K A 1 * X = X
        rw [map_one, one_mul]
      inv_mem' := fun {a} ha => by
        have ha' : MonoidAlgebra.of K A a * X = X := ha
        show MonoidAlgebra.of K A a⁻¹ * X = X
        calc MonoidAlgebra.of K A a⁻¹ * X
            = MonoidAlgebra.of K A a⁻¹ * (MonoidAlgebra.of K A a * X) := by rw [ha']
          _ = X := by rw [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul] }
  have hH : H ≤ S := fun a ha => by
    show MonoidAlgebra.of K A a * X = X
    rw [hXdef, ← mul_assoc, of_mul_eSub ha]
  have hH' : H' ≤ S := fun a ha => by
    show MonoidAlgebra.of K A a * X = X
    rw [hXdef, mul_left_comm, of_mul_eSub ha]
  have hTop : (⊤ : Subgroup A) ≤ S := h ▸ sup_le hH hH'
  have h1 : X * eSub ⊤ = X :=
    mul_eSub_of_invariant hp hA hpK (fun a _ => hTop (Subgroup.mem_top a))
  have h2 : eSub H' * eSub ⊤ = (eSub ⊤ : MonoidAlgebra K A) :=
    eSub_mul_eSub_of_le hp hA hpK le_top
  have h3 : eSub H * eSub ⊤ = (eSub ⊤ : MonoidAlgebra K A) :=
    eSub_mul_eSub_of_le hp hA hpK le_top
  rw [← h1, hXdef, mul_assoc, h2, h3]

theorem orthogonalIdempotents_eps : OrthogonalIdempotents (eps K A p) := by
  have hTT : eSub (⊤ : Subgroup A) * eSub ⊤ = (eSub (⊤ : Subgroup A) : MonoidAlgebra K A) :=
    eSub_mul_eSub_of_le hp hA hpK le_rfl
  have hHT : ∀ H : Subgroup A,
      eSub H * eSub ⊤ = (eSub (⊤ : Subgroup A) : MonoidAlgebra K A) := fun H =>
    eSub_mul_eSub_of_le hp hA hpK le_top
  have hHH : ∀ H : Subgroup A, eSub H * eSub H = (eSub H : MonoidAlgebra K A) := fun H =>
    eSub_mul_eSub_of_le hp hA hpK le_rfl
  have hTH : ∀ H : Subgroup A,
      eSub (⊤ : Subgroup A) * eSub H = (eSub (⊤ : Subgroup A) : MonoidAlgebra K A) :=
    fun H => by rw [mul_comm]; exact hHT H
  refine ⟨?_, ?_⟩
  · rintro (_ | H)
    · exact hTT
    · show (eSub H.1 - eSub ⊤) * (eSub H.1 - eSub ⊤) = (eSub H.1 - eSub ⊤ : MonoidAlgebra K A)
      linear_combination hHH H.1 - hHT H.1 - hTH H.1 + hTT
  · rintro (_ | H) (_ | L) hne
    · exact absurd rfl hne
    · show eSub ⊤ * (eSub L.1 - eSub ⊤) = (0 : MonoidAlgebra K A)
      linear_combination hTH L.1 - hTT
    · show (eSub H.1 - eSub ⊤) * eSub ⊤ = (0 : MonoidAlgebra K A)
      linear_combination hHT H.1 - hTT
    · have hHL : eSub H.1 * eSub L.1 = (eSub (⊤ : Subgroup A) : MonoidAlgebra K A) :=
        eSub_mul_eSub_of_sup hp hA hpK (sup_eq_top_of_index_eq_prime hp H.2 L.2
          (fun h => hne (congrArg some (Subtype.ext h))))
      show (eSub H.1 - eSub ⊤) * (eSub L.1 - eSub ⊤) = (0 : MonoidAlgebra K A)
      linear_combination hHL - hHT H.1 - hTH L.1 + hTT

theorem span_eps_eq_top : Ideal.span (Set.range (eps K A p)) = ⊤ := by
  by_contra hne
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
  letI : Field (MonoidAlgebra K A ⧸ M) := Ideal.Quotient.field M
  let f : MonoidAlgebra K A →ₐ[K] MonoidAlgebra K A ⧸ M := Ideal.Quotient.mkₐ K M
  let φ : A →* (MonoidAlgebra K A ⧸ M) :=
    (f : MonoidAlgebra K A →* MonoidAlgebra K A ⧸ M).comp (MonoidAlgebra.of K A)
  let χ : A →* (MonoidAlgebra K A ⧸ M)ˣ := φ.toHomUnits
  haveI : Finite χ.range := Finite.of_surjective χ.rangeRestrict χ.rangeRestrict_surjective
  have hχp : ∀ g : χ.range, g ^ p = 1 := by
    rintro ⟨_, a, rfl⟩
    apply Subtype.ext
    simp [← map_pow, hA a]
  haveI : IsCyclic χ.range :=
    isCyclic_of_injective_ringHom ((Units.coeHom _).comp χ.range.subtype)
      (fun x y hxy => Subtype.ext (Units.ext hxy))
  have hidx : χ.ker.index ∣ p := by
    rw [Subgroup.index_ker, ← IsCyclic.exponent_eq_card]
    exact Monoid.exponent_dvd_of_forall_pow_eq_one hχp
  have himg : f (eSub χ.ker) = 1 := by
    haveI : Fintype χ.ker := Fintype.ofFinite _
    rw [eSub_eq_sum, map_smul, map_sum]
    have h1 : ∀ u : χ.ker, f (MonoidAlgebra.of K A (u : A)) = 1 := fun u => by
      have hu : χ (u : A) = 1 := u.2
      have := congrArg Units.val hu
      simpa [χ, φ] using this
    simp only [h1, Finset.sum_const, Finset.card_univ]
    rw [← Nat.card_eq_fintype_card, ← Nat.cast_smul_eq_nsmul K, smul_smul,
      inv_mul_cancel₀ (card_subgroup_ne_zero hp hA hpK χ.ker), one_smul]
  rcases (Nat.dvd_prime hp).mp hidx with h1 | hpp
  · have htop : χ.ker = ⊤ := Subgroup.index_eq_one.mp h1
    have hmem : eSub (⊤ : Subgroup A) ∈ M := hle (Ideal.subset_span ⟨none, rfl⟩)
    have h0 : f (eSub (⊤ : Subgroup A)) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    rw [htop, h0] at himg
    exact zero_ne_one himg
  · have hmem : eSub χ.ker ∈ M := by
      have e1 : eSub χ.ker = eps K A p (some ⟨χ.ker, hpp⟩) + eps K A p none := by simp [eps]
      rw [e1]
      exact M.add_mem (hle (Ideal.subset_span ⟨_, rfl⟩)) (hle (Ideal.subset_span ⟨_, rfl⟩))
    rw [show f (eSub χ.ker) = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr hmem] at himg
    exact zero_ne_one himg

theorem sum_eps [Fintype (Option (Hyperplane A p))] :
    ∑ i : Option (Hyperplane A p), eps K A p i = 1 := by
  have he := orthogonalIdempotents_eps hp hA hpK
  set g : MonoidAlgebra K A := 1 - ∑ i, eps K A p i with hg
  have hker : Ideal.span (Set.range (eps K A p)) ≤
      LinearMap.ker (LinearMap.mulLeft (MonoidAlgebra K A) g) := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    have h1 : (∑ j, eps K A p j) * eps K A p i = eps K A p i := by
      rw [mul_comm]
      exact he.mul_sum_of_mem (Finset.mem_univ i)
    simp only [LinearMap.mem_ker, LinearMap.mulLeft_apply, SetLike.mem_coe]
    rw [hg, sub_mul, one_mul, h1, sub_self]
  have h1 : (1 : MonoidAlgebra K A) ∈
      LinearMap.ker (LinearMap.mulLeft (MonoidAlgebra K A) g) :=
    hker (by rw [span_eps_eq_top hp hA hpK]; trivial)
  simp only [LinearMap.mem_ker, LinearMap.mulLeft_apply, mul_one] at h1
  exact (sub_eq_zero.mp h1).symm

end GroupRing

section Idempotents

variable {ι : Type*} {k M : Type*} [Ring k] [AddCommGroup M] [Module k M]

private theorem iSupIndep_range_of_orthogonalIdempotents {e : ι → Module.End k M}
    (he : OrthogonalIdempotents e) : iSupIndep fun i => LinearMap.range (e i) := by
  rw [iSupIndep_def]
  intro i
  rw [Submodule.disjoint_def]
  intro x hx hx'
  have hle : (⨆ j, ⨆ (_ : j ≠ i), LinearMap.range (e j)) ≤ LinearMap.ker (e i) := by
    refine iSup₂_le fun j hj => ?_
    rintro _ ⟨z, rfl⟩
    rw [LinearMap.mem_ker, ← Module.End.mul_apply, he.ortho (Ne.symm hj)]
    rfl
  have h0 : e i x = 0 := hle hx'
  obtain ⟨y, rfl⟩ := hx
  have hidem : e i (e i y) = e i y := by
    rw [← Module.End.mul_apply, (he.idem i).eq]
  calc e i y = e i (e i y) := hidem.symm
    _ = 0 := h0

private theorem iSup_range_eq_top_of_sum_eq_one [Fintype ι] {e : ι → Module.End k M}
    (h : ∑ i, e i = 1) : ⨆ i, LinearMap.range (e i) = ⊤ := by
  rw [eq_top_iff]
  intro v _
  have hv : v = ∑ i, e i v := by
    have := congrArg (fun f : Module.End k M => f v) h
    simpa [LinearMap.sum_apply] using this.symm
  rw [hv]
  exact Submodule.sum_mem _ fun i _ => Submodule.mem_iSup_of_mem i ⟨v, rfl⟩

private theorem finrank_biSup_eq_sum [DecidableEq ι] {K : Type*} [Field K] [Module K M]
    [FiniteDimensional K M] {S : ι → Submodule K M} (hS : iSupIndep S) (s : Finset ι) :
    Module.finrank K (⨆ i ∈ s, S i : Submodule K M) = ∑ i ∈ s, Module.finrank K (S i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hdis : Disjoint (S a) (⨆ i ∈ s, S i) := hS.disjoint_biSup (by simpa using ha)
    have h := Submodule.finrank_sup_add_finrank_inf_eq (S a) (⨆ i ∈ s, S i)
    rw [hdis.eq_bot, finrank_bot, add_zero] at h
    rw [Finset.iSup_insert, Finset.sum_insert ha, ← ih]
    exact h

end Idempotents

section Spaces

variable {K : Type*} [Field K] {A : Type*} [CommGroup A] {p : ℕ}
variable {V : Type*} [AddCommGroup V] [Module K V] (ρ : Representation K A V)

@[expose] def fixedSpace (U : Subgroup A) : Submodule K V where
  carrier := {v | ∀ u ∈ U, ρ u v = v}
  zero_mem' := fun u _ => map_zero _
  add_mem' := fun {x y} hx hy u hu => by rw [map_add, hx u hu, hy u hu]
  smul_mem' := fun c x hx u hu => by rw [map_smul, hx u hu]

theorem mem_fixedSpace {U : Subgroup A} {v : V} : v ∈ fixedSpace ρ U ↔ ∀ u ∈ U, ρ u v = v :=
  Iff.rfl

@[expose] noncomputable def weightSpace (H : Subgroup A) : Submodule K V :=
  LinearMap.range (ρ.asAlgebraHom (eSub H - eSub ⊤))

@[expose] noncomputable def weightFamily : Option (Hyperplane A p) → Submodule K V :=
  fun i => LinearMap.range (ρ.asAlgebraHom (eps K A p i))

theorem weightFamily_some (H : Hyperplane A p) : weightFamily ρ (some H) = weightSpace ρ H.1 :=
  rfl

theorem asAlgebraHom_eSub (U : Subgroup A) [Fintype U] :
    ρ.asAlgebraHom (eSub U) = ((Nat.card U : K))⁻¹ • ∑ u : U, ρ (u : A) := by
  rw [eSub_eq_sum, map_smul, map_sum]
  simp

variable [Finite A]

theorem apply_asAlgebraHom_eSub {U : Subgroup A} {a : A} (ha : a ∈ U) (v : V) :
    ρ a (ρ.asAlgebraHom (eSub U) v) = ρ.asAlgebraHom (eSub U) v := by
  have := congrArg (fun x => ρ.asAlgebraHom x v) (of_mul_eSub (K := K) ha)
  simpa [map_mul, Representation.asAlgebraHom_of, Module.End.mul_apply] using this

theorem apply_eq_of_mem_weightSpace {H : Subgroup A} {h : A} (hh : h ∈ H) {v : V}
    (hv : v ∈ weightSpace ρ H) : ρ h v = v := by
  obtain ⟨w, rfl⟩ := hv
  have := congrArg (fun x => ρ.asAlgebraHom x w)
    (show MonoidAlgebra.of K A h * (eSub H - eSub ⊤) = (eSub H - eSub ⊤ : MonoidAlgebra K A) by
      rw [mul_sub, of_mul_eSub hh, of_mul_eSub (Subgroup.mem_top h)])
  simpa [map_mul, Representation.asAlgebraHom_of, Module.End.mul_apply] using this

theorem apply_asAlgebraHom_comm (X : MonoidAlgebra K A) (a : A) (v : V) :
    ρ a (ρ.asAlgebraHom X v) = ρ.asAlgebraHom X (ρ a v) := by
  have := congrArg (fun x => ρ.asAlgebraHom x v) (mul_comm (MonoidAlgebra.of K A a) X)
  simpa [map_mul, Representation.asAlgebraHom_of, Module.End.mul_apply] using this

theorem apply_mem_weightSpace (H : Subgroup A) (a : A) {v : V} (hv : v ∈ weightSpace ρ H) :
    ρ a v ∈ weightSpace ρ H := by
  obtain ⟨w, rfl⟩ := hv
  exact ⟨ρ a w, (apply_asAlgebraHom_comm ρ _ a w).symm⟩

variable (hp : p.Prime) (hA : ∀ a : A, a ^ p = 1) (hpK : (p : K) ≠ 0)

include hp hA hpK

theorem asAlgebraHom_eSub_apply_of_mem {U : Subgroup A} {v : V} (hv : v ∈ fixedSpace ρ U) :
    ρ.asAlgebraHom (eSub U) v = v := by
  haveI : Fintype U := Fintype.ofFinite U
  rw [asAlgebraHom_eSub, LinearMap.smul_apply, LinearMap.sum_apply]
  have h1 : ∀ u : U, ρ (u : A) v = v := fun u => hv u u.2
  simp only [h1, Finset.sum_const, Finset.card_univ]
  rw [← Nat.card_eq_fintype_card, ← Nat.cast_smul_eq_nsmul K, smul_smul,
    inv_mul_cancel₀ (card_subgroup_ne_zero hp hA hpK U), one_smul]

theorem range_asAlgebraHom_eSub (U : Subgroup A) :
    LinearMap.range (ρ.asAlgebraHom (eSub U)) = fixedSpace ρ U := by
  ext v
  constructor
  · rintro ⟨w, rfl⟩ u hu
    exact apply_asAlgebraHom_eSub ρ hu w
  · intro hv
    exact ⟨v, asAlgebraHom_eSub_apply_of_mem ρ hp hA hpK hv⟩

theorem mem_weightSpace_iff (H : Subgroup A) (v : V) :
    v ∈ weightSpace ρ H ↔ v ∈ fixedSpace ρ H ∧ ρ.asAlgebraHom (eSub ⊤) v = 0 := by
  have hTH : eSub (⊤ : Subgroup A) * eSub H = (eSub ⊤ : MonoidAlgebra K A) := by
    rw [mul_comm]
    exact eSub_mul_eSub_of_le hp hA hpK le_top
  have hTT : eSub (⊤ : Subgroup A) * eSub ⊤ = (eSub ⊤ : MonoidAlgebra K A) :=
    eSub_mul_eSub_of_le hp hA hpK le_rfl
  constructor
  · intro hv
    refine ⟨fun h hh => apply_eq_of_mem_weightSpace ρ hh hv, ?_⟩
    obtain ⟨w, rfl⟩ := hv
    have := congrArg (fun x => ρ.asAlgebraHom x w)
      (show eSub (⊤ : Subgroup A) * (eSub H - eSub ⊤) = (0 : MonoidAlgebra K A) by
        rw [mul_sub, hTH, hTT, sub_self])
    simpa [map_mul, Module.End.mul_apply] using this
  · rintro ⟨hv, h0⟩
    refine ⟨v, ?_⟩
    rw [map_sub, LinearMap.sub_apply, h0, sub_zero]
    exact asAlgebraHom_eSub_apply_of_mem ρ hp hA hpK hv

theorem weightFamily_none : weightFamily (p := p) ρ none = fixedSpace ρ ⊤ :=
  range_asAlgebraHom_eSub ρ hp hA hpK ⊤

theorem orthogonalIdempotents_asAlgebraHom_eps :
    OrthogonalIdempotents fun i => ρ.asAlgebraHom (eps K A p i) :=
  (orthogonalIdempotents_eps hp hA hpK).map ρ.asAlgebraHom.toRingHom

theorem sum_asAlgebraHom_eps [Fintype (Option (Hyperplane A p))] :
    ∑ i, ρ.asAlgebraHom (eps K A p i) = 1 := by
  rw [← map_sum, sum_eps hp hA hpK, map_one]

theorem iSupIndep_weightFamily : iSupIndep (weightFamily (p := p) ρ) :=
  iSupIndep_range_of_orthogonalIdempotents (orthogonalIdempotents_asAlgebraHom_eps ρ hp hA hpK)

theorem iSup_weightFamily : ⨆ i, weightFamily (p := p) ρ i = ⊤ := by
  haveI := Fintype.ofFinite (Option (Hyperplane A p))
  exact iSup_range_eq_top_of_sum_eq_one (sum_asAlgebraHom_eps ρ hp hA hpK)

theorem finrank_eq_fixedSpace_add_sum [FiniteDimensional K V] [Fintype (Hyperplane A p)] :
    Module.finrank K V = Module.finrank K (fixedSpace ρ ⊤) +
      ∑ H : Hyperplane A p, Module.finrank K (weightSpace ρ H.1) := by
  classical
  have key := finrank_biSup_eq_sum (iSupIndep_weightFamily ρ hp hA hpK) Finset.univ
  have h1 : (⨆ i ∈ (Finset.univ : Finset (Option (Hyperplane A p))), weightFamily ρ i) = ⊤ := by
    rw [← iSup_weightFamily ρ hp hA hpK]
    simp
  rw [h1, finrank_top, Fintype.sum_option, weightFamily_none ρ hp hA hpK] at key
  exact key

theorem eq_zero_of_mem_weightSpace_of_fixed {H : Hyperplane A p} {a : A} (ha : a ∉ H.1) {v : V}
    (hv : v ∈ weightSpace ρ H.1) (hfix : ρ a v = v) : v = 0 := by
  let S : Subgroup A :=
    { carrier := {g | ρ g v = v}
      mul_mem' := fun {g g'} hg hg' => by
        have hg1 : ρ g v = v := hg
        have hg2 : ρ g' v = v := hg'
        show ρ (g * g') v = v
        rw [map_mul, Module.End.mul_apply, hg2, hg1]
      one_mem' := by
        show ρ 1 v = v
        rw [map_one]
        rfl
      inv_mem' := fun {g} hg => by
        have hg1 : ρ g v = v := hg
        show ρ g⁻¹ v = v
        calc ρ g⁻¹ v = ρ g⁻¹ (ρ g v) := by rw [hg1]
          _ = v := Representation.inv_self_apply ρ g v }
  have hHS : H.1 ≤ S := fun h hh => apply_eq_of_mem_weightSpace ρ hh hv
  have haS : Subgroup.zpowers a ≤ S := Subgroup.zpowers_le.mpr hfix
  have hne : H.1 ⊔ Subgroup.zpowers a ≠ H.1 := fun h =>
    ha (h ▸ (le_sup_right : Subgroup.zpowers a ≤ H.1 ⊔ Subgroup.zpowers a)
      (Subgroup.mem_zpowers a))
  have htop : H.1 ⊔ Subgroup.zpowers a = ⊤ :=
    eq_top_of_index_prime hp H.2 le_sup_left hne
  have hfixTop : v ∈ fixedSpace ρ ⊤ := fun g _ =>
    (sup_le hHS haS : H.1 ⊔ Subgroup.zpowers a ≤ S) (htop ▸ Subgroup.mem_top g)
  have h1 := asAlgebraHom_eSub_apply_of_mem ρ hp hA hpK hfixTop
  have h2 := ((mem_weightSpace_iff ρ hp hA hpK H.1 v).mp hv).2
  exact h1.symm.trans h2

theorem eq_one_of_forall_mem_hyperplane (hρ : Function.Injective ρ) {a : A}
    (ha : ∀ H : Hyperplane A p, weightSpace ρ H.1 ≠ ⊥ → a ∈ H.1) : a = 1 := by
  apply hρ
  rw [map_one]
  have hle : ⨆ i, weightFamily (p := p) ρ i ≤ LinearMap.ker (ρ a - 1) := by
    refine iSup_le fun i => ?_
    rcases i with _ | H
    · rw [weightFamily_none ρ hp hA hpK]
      intro v hv
      rw [LinearMap.mem_ker, LinearMap.sub_apply, hv a (Subgroup.mem_top a),
        Module.End.one_apply, sub_self]
    · rw [weightFamily_some]
      intro v hv
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
      by_cases hbot : weightSpace ρ H.1 = ⊥
      · rw [hbot, Submodule.mem_bot] at hv
        rw [hv, map_zero]
      · exact apply_eq_of_mem_weightSpace ρ (ha H hbot) hv
  rw [iSup_weightFamily ρ hp hA hpK, top_le_iff] at hle
  refine LinearMap.ext fun v => ?_
  have hv : v ∈ LinearMap.ker (ρ a - 1) := by rw [hle]; exact Submodule.mem_top
  rwa [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hv

end Spaces

section Isometry

variable {K : Type*} [Field K] {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]

open scoped Matrix in
theorem exists_ne_zero_fixed_of_odd_finrank (h2 : (2 : K) ≠ 0) {B : LinearMap.BilinForm K W}
    (hB : B.SeparatingLeft) {g : W →ₗ[K] W} (hg : ∀ x y, B (g x) (g y) = B x y) {n : ℕ}
    (hn : Odd n) (hgn : g ^ n = 1) (hodd : Odd (Module.finrank K W)) :
    ∃ w : W, w ≠ 0 ∧ g w = w := by
  classical
  let b := Module.finBasis K W
  set M := LinearMap.toMatrix b b g with hM
  set G := LinearMap.BilinForm.toMatrix b B with hG
  have hGdet : G.det ≠ 0 :=
    (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp
      (LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft hB)
  have hMGM : Mᵀ * G * M = G := by
    have h := LinearMap.BilinForm.toMatrix_comp b b B g g
    have hcomp : B.comp g g = B := LinearMap.ext₂ hg
    rw [hcomp] at h
    exact h.symm
  have hd2 : M.det ^ 2 = 1 := by
    have h := congrArg Matrix.det hMGM
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at h
    have h' : (M.det ^ 2 - 1) * G.det = 0 := by linear_combination h
    exact sub_eq_zero.mp ((mul_eq_zero.mp h').resolve_right hGdet)
  have hdn : M.det ^ n = 1 := by
    rw [hM, LinearMap.det_toMatrix, ← map_pow, hgn, map_one]
  have hdet1 : M.det = 1 := by
    obtain ⟨k, rfl⟩ := hn
    have h : M.det ^ (2 * k + 1) = M.det := by rw [pow_succ, pow_mul, hd2, one_pow, one_mul]
    rw [← h]
    exact hdn
  have key : (M - 1)ᵀ * G * M = -(G * (M - 1)) := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, sub_mul, sub_mul, one_mul, hMGM, mul_sub,
      mul_one]
    abel
  have hdet := congrArg Matrix.det key
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hdet1, mul_one, Matrix.det_neg,
    Matrix.det_mul, Fintype.card_fin, hodd.neg_one_pow] at hdet
  have h0 : (M - 1).det = 0 := by
    have h' : 2 * ((M - 1).det * G.det) = 0 := by linear_combination hdet
    exact (mul_eq_zero.mp ((mul_eq_zero.mp h').resolve_left h2)).resolve_right hGdet
  have hdg : LinearMap.det (g - 1) = 0 := by
    rw [← LinearMap.det_toMatrix b, map_sub, LinearMap.toMatrix_one]
    exact h0
  obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff _).mp
    (bot_lt_iff_ne_bot.mp (LinearMap.bot_lt_ker_of_det_eq_zero hdg))
  refine ⟨w, hw0, ?_⟩
  have hw' : (g - 1) w = 0 := hw
  rwa [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hw'

end Isometry

section Isometric

variable {K : Type*} [Field K] {A : Type*} [CommGroup A] {p : ℕ} [Finite A]
variable {V : Type*} [AddCommGroup V] [Module K V] (ρ : Representation K A V)
variable (hp : p.Prime) (hA : ∀ a : A, a ^ p = 1) (hpK : (p : K) ≠ 0)
variable (Q : QuadraticForm K V) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
variable (h2 : (2 : K) ≠ 0) (hρQ : ∀ (a : A) (v : V), Q (ρ a v) = Q v) (hp2 : p ≠ 2)

private theorem polar_sum_left {ι : Type*} (s : Finset ι) (f : ι → V) (y : V) :
    QuadraticMap.polar Q (∑ i ∈ s, f i) y = ∑ i ∈ s, QuadraticMap.polar Q (f i) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [QuadraticMap.polar_zero_left]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, QuadraticMap.polar_add_left, ih]

private theorem polar_sum_right {ι : Type*} (s : Finset ι) (x : V) (f : ι → V) :
    QuadraticMap.polar Q x (∑ i ∈ s, f i) = ∑ i ∈ s, QuadraticMap.polar Q x (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [QuadraticMap.polar_zero_right]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, QuadraticMap.polar_add_right, ih]

include hρQ in
theorem polar_apply_apply (a : A) (x y : V) :
    QuadraticMap.polar Q (ρ a x) (ρ a y) = QuadraticMap.polar Q x y := by
  simp only [QuadraticMap.polar, ← map_add, hρQ]

include hρQ in
theorem polar_apply_left (a : A) (x y : V) :
    QuadraticMap.polar Q (ρ a x) y = QuadraticMap.polar Q x (ρ a⁻¹ y) := by
  have h := polar_apply_apply ρ Q hρQ a x (ρ a⁻¹ y)
  rwa [Representation.self_inv_apply] at h

include hρQ in
theorem polar_asAlgebraHom_eSub_left (U : Subgroup A) (x y : V) :
    QuadraticMap.polar Q (ρ.asAlgebraHom (eSub U) x) y =
      QuadraticMap.polar Q x (ρ.asAlgebraHom (eSub U) y) := by
  haveI : Fintype U := Fintype.ofFinite U
  rw [asAlgebraHom_eSub, LinearMap.smul_apply, LinearMap.smul_apply,
    QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right, LinearMap.sum_apply,
    LinearMap.sum_apply, polar_sum_left, polar_sum_right]
  congr 1
  calc ∑ u : U, QuadraticMap.polar Q (ρ (u : A) x) y
      = ∑ u : U, QuadraticMap.polar Q x (ρ ((u : A)⁻¹) y) :=
        Finset.sum_congr rfl fun u _ => polar_apply_left ρ Q hρQ _ x y
    _ = ∑ u : U, QuadraticMap.polar Q x (ρ (u : A) y) :=
        Fintype.sum_equiv (Equiv.inv U) _ _ (fun u => by simp)

include hρQ in
theorem polar_asAlgebraHom_eps_left (i : Option (Hyperplane A p)) (x y : V) :
    QuadraticMap.polar Q (ρ.asAlgebraHom (eps K A p i) x) y =
      QuadraticMap.polar Q x (ρ.asAlgebraHom (eps K A p i) y) := by
  rcases i with _ | H
  · exact polar_asAlgebraHom_eSub_left ρ Q hρQ ⊤ x y
  · show QuadraticMap.polar Q (ρ.asAlgebraHom (eSub H.1 - eSub ⊤) x) y =
      QuadraticMap.polar Q x (ρ.asAlgebraHom (eSub H.1 - eSub ⊤) y)
    rw [map_sub, LinearMap.sub_apply, LinearMap.sub_apply, QuadraticMap.polar_sub_left,
      QuadraticMap.polar_sub_right, polar_asAlgebraHom_eSub_left ρ Q hρQ,
      polar_asAlgebraHom_eSub_left ρ Q hρQ]

include hp hA hpK hρQ in
theorem polar_eq_zero_of_mem_weightFamily {i j : Option (Hyperplane A p)} (hij : i ≠ j) {v w : V}
    (hv : v ∈ weightFamily ρ i) (hw : w ∈ weightFamily ρ j) : QuadraticMap.polar Q v w = 0 := by
  obtain ⟨v', rfl⟩ := hv
  obtain ⟨w', rfl⟩ := hw
  rw [polar_asAlgebraHom_eps_left ρ Q hρQ i, ← Module.End.mul_apply,
    (orthogonalIdempotents_asAlgebraHom_eps ρ hp hA hpK).ortho hij]
  simp

include hp hA hpK hQ hρQ in
theorem nondegenerate_weightFamily (i : Option (Hyperplane A p)) {v : V}
    (hv : v ∈ weightFamily ρ i) (h : ∀ w ∈ weightFamily ρ i, QuadraticMap.polar Q v w = 0) :
    v = 0 := by
  have hidem : ρ.asAlgebraHom (eps K A p i) v = v := by
    obtain ⟨v', rfl⟩ := hv
    rw [← Module.End.mul_apply, ((orthogonalIdempotents_asAlgebraHom_eps ρ hp hA hpK).idem i).eq]
  refine hQ.1 v fun w => ?_
  rw [QuadraticMap.polarBilin_apply_apply]
  calc QuadraticMap.polar Q v w
      = QuadraticMap.polar Q (ρ.asAlgebraHom (eps K A p i) v) w := by rw [hidem]
    _ = QuadraticMap.polar Q v (ρ.asAlgebraHom (eps K A p i) w) :=
        polar_asAlgebraHom_eps_left ρ Q hρQ i v w
    _ = 0 := h _ ⟨w, rfl⟩

include hp hA hpK hQ h2 hρQ hp2 in
theorem even_finrank_weightSpace [FiniteDimensional K V] (H : Hyperplane A p) :
    Even (Module.finrank K (weightSpace ρ H.1)) := by
  by_contra hodd
  rw [Nat.not_even_iff_odd] at hodd
  obtain ⟨a, ha⟩ : ∃ a : A, a ∉ H.1 := by
    by_contra hcon
    push Not at hcon
    have htop : H.1 = ⊤ := (Subgroup.eq_top_iff' _).mpr hcon
    have h := H.2
    rw [htop, Subgroup.index_top] at h
    exact hp.ne_one h.symm
  have hinv : ∀ g : A, weightSpace ρ H.1 ≤ (weightSpace ρ H.1).comap (ρ g) :=
    fun g v hv => apply_mem_weightSpace ρ H.1 g hv
  let ρS := ρ.subrepresentation (weightSpace ρ H.1) hinv
  let B : LinearMap.BilinForm K (weightSpace ρ H.1) :=
    LinearMap.BilinForm.restrict (QuadraticMap.polarBilin Q) (weightSpace ρ H.1)
  have hB : B.SeparatingLeft := by
    intro x hx
    refine Subtype.ext (nondegenerate_weightFamily ρ hp hA hpK Q hQ hρQ (some H) x.2
      fun w hw => ?_)
    exact hx ⟨w, hw⟩
  have hg : ∀ x y, B (ρS a x) (ρS a y) = B x y := fun x y => polar_apply_apply ρ Q hρQ a x y
  have hgp : ρS a ^ p = 1 := by rw [← map_pow, hA a, map_one]
  obtain ⟨w, hw0, hgw⟩ :=
    exists_ne_zero_fixed_of_odd_finrank h2 hB hg (hp.odd_of_ne_two hp2) hgp hodd
  exact hw0 (Subtype.ext (eq_zero_of_mem_weightSpace_of_fixed ρ hp hA hpK ha w.2
    (congrArg Subtype.val hgw)))

include hp hA hpK hQ h2 hρQ hp2 in
theorem two_le_finrank_weightSpace [FiniteDimensional K V] (H : Hyperplane A p)
    (h : weightSpace ρ H.1 ≠ ⊥) : 2 ≤ Module.finrank K (weightSpace ρ H.1) := by
  have hne : Module.finrank K (weightSpace ρ H.1) ≠ 0 := fun h0 =>
    h (Submodule.finrank_eq_zero.mp h0)
  obtain ⟨k, hk⟩ := even_finrank_weightSpace ρ hp hA hpK Q hQ h2 hρQ hp2 H
  omega

end Isometric

section Config

variable {K : Type*} [Field K] {A : Type*} [CommGroup A] {p : ℕ} [Finite A]
variable {V : Type*} [AddCommGroup V] [Module K V] (ρ : Representation K A V)
variable (hp : p.Prime) (hA : ∀ a : A, a ^ p = 1) (hpK : (p : K) ≠ 0)

private theorem index_biInf_le (s : Finset (Hyperplane A p)) :
    (⨅ H ∈ s, H.1).index ≤ p ^ s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.iInf_insert, Finset.card_insert_of_notMem ha, pow_succ, mul_comm]
    calc (a.1 ⊓ ⨅ H ∈ s, H.1).index ≤ a.1.index * (⨅ H ∈ s, H.1).index := Subgroup.index_inf_le
      _ = p * (⨅ H ∈ s, H.1).index := by rw [a.2]
      _ ≤ p * p ^ s.card := Nat.mul_le_mul_left p ih

private theorem card_biInf_erase [DecidableEq (Hyperplane A p)] (hp : p.Prime)
    {T : Finset (Hyperplane A p)} (hT0 : ⨅ H ∈ T, H.1 = ⊥) (hcard : Nat.card A = p ^ T.card)
    {H₀ : Hyperplane A p} (hH₀ : H₀ ∈ T) :
    H₀.1 ⊓ (⨅ H ∈ T.erase H₀, H.1) = ⊥ ∧ Nat.card (⨅ H ∈ T.erase H₀, H.1 : Subgroup A) = p := by
  set L : Subgroup A := ⨅ H ∈ T.erase H₀, H.1 with hL
  have hinf : H₀.1 ⊓ L = ⊥ := by
    calc H₀.1 ⊓ L = ⨅ H ∈ insert H₀ (T.erase H₀), H.1 := (Finset.iInf_insert _ _ _).symm
      _ = ⨅ H ∈ T, H.1 := by rw [Finset.insert_erase hH₀]
      _ = ⊥ := hT0
  have hcardT : (T.erase H₀).card + 1 = T.card := Finset.card_erase_add_one hH₀
  have hLidx : L.index ≤ p ^ (T.erase H₀).card := index_biInf_le _
  have h1 : (H₀.1 ⊓ L).index ≤ H₀.1.index * L.index := Subgroup.index_inf_le
  rw [hinf, Subgroup.index_bot, hcard, H₀.2, ← hcardT, pow_succ] at h1
  have hLge : p ^ (T.erase H₀).card ≤ L.index := by
    have h3 : p * p ^ (T.erase H₀).card ≤ p * L.index := by rwa [mul_comm] at h1
    exact Nat.le_of_mul_le_mul_left h3 hp.pos
  have hLeq : L.index = p ^ (T.erase H₀).card := le_antisymm hLidx hLge
  have h2 := Subgroup.card_mul_index L
  rw [hLeq, hcard, ← hcardT, pow_succ] at h2
  refine ⟨hinf, ?_⟩
  exact Nat.eq_of_mul_eq_mul_right (pow_pos hp.pos _) (h2.trans (mul_comm _ _))

variable (Q : QuadraticForm K V) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
variable (h2 : (2 : K) ≠ 0) (hρQ : ∀ (a : A) (v : V), Q (ρ a v) = Q v) (hp2 : p ≠ 2)

include hp hA hpK in
theorem fixedSpace_eq_biSup (U : Subgroup A) (I : Finset (Option (Hyperplane A p)))
    (hI : ∀ i ∈ I, weightFamily ρ i ≤ fixedSpace ρ U)
    (hI' : ∀ i ∉ I, ∀ v ∈ weightFamily ρ i, (∀ u ∈ U, ρ u v = v) → v = 0) :
    fixedSpace ρ U = ⨆ i ∈ I, weightFamily (p := p) ρ i := by
  classical
  haveI : Fintype (Option (Hyperplane A p)) := Fintype.ofFinite _
  apply le_antisymm
  · intro v hv
    have hsum : ∑ i, ρ.asAlgebraHom (eps K A p i) v = v := by
      have := congrArg (fun f : Module.End K V => f v) (sum_asAlgebraHom_eps ρ hp hA hpK)
      simpa [LinearMap.sum_apply] using this
    have hzero : ∀ i ∉ I, ρ.asAlgebraHom (eps K A p i) v = 0 := fun i hi =>
      hI' i hi _ ⟨v, rfl⟩ fun u hu => by rw [apply_asAlgebraHom_comm, hv u hu]
    rw [← hsum]
    refine Submodule.sum_mem _ fun i _ => ?_
    by_cases hi : i ∈ I
    · exact Submodule.mem_iSup_of_mem i (Submodule.mem_iSup_of_mem hi ⟨v, rfl⟩)
    · rw [hzero i hi]
      exact Submodule.zero_mem _
  · exact iSup₂_le hI

include hp hA hpK in
theorem finrank_fixedSpace_eq [FiniteDimensional K V] {T : Finset (Hyperplane A p)}
    (hT : ∀ H : Hyperplane A p, H ∈ T ↔ weightSpace ρ H.1 ≠ ⊥) (U : Subgroup A)
    [DecidablePred fun H : Hyperplane A p => U ≤ H.1] :
    Module.finrank K (fixedSpace ρ U) = Module.finrank K (fixedSpace ρ ⊤) +
      ∑ H ∈ T.filter (fun H => U ≤ H.1), Module.finrank K (weightSpace ρ H.1) := by
  classical
  set T' := T.filter (fun H => U ≤ H.1) with hT'
  have hmem : ∀ H : Hyperplane A p, H ∈ T' ↔ weightSpace ρ H.1 ≠ ⊥ ∧ U ≤ H.1 := fun H => by
    rw [hT', Finset.mem_filter, hT]
  have hI := fixedSpace_eq_biSup ρ hp hA hpK U (insert none (T'.image some)) ?_ ?_
  · rw [hI, finrank_biSup_eq_sum (iSupIndep_weightFamily ρ hp hA hpK),
      Finset.sum_insert (by simp), Finset.sum_image (fun a _ b _ h => Option.some.inj h),
      weightFamily_none ρ hp hA hpK]
    rfl
  · intro i hi
    rcases i with _ | H
    · rw [weightFamily_none ρ hp hA hpK]
      exact fun v hv u _ => hv u (Subgroup.mem_top u)
    · have hH : H ∈ T' := by simpa using hi
      exact fun v hv u hu => apply_eq_of_mem_weightSpace ρ (((hmem H).mp hH).2 hu) hv
  · intro i hi v hv hfix
    rcases i with _ | H
    · exact absurd (Finset.mem_insert_self _ _) hi
    · by_cases hbot : weightSpace ρ H.1 = ⊥
      · rw [weightFamily_some, hbot, Submodule.mem_bot] at hv
        exact hv
      · have hUH : ¬ U ≤ H.1 := fun hle => hi (Finset.mem_insert_of_mem
          (Finset.mem_image_of_mem some ((hmem H).mpr ⟨hbot, hle⟩)))
        obtain ⟨u, huU, huH⟩ := SetLike.not_le_iff_exists.mp hUH
        exact eq_zero_of_mem_weightSpace_of_fixed ρ hp hA hpK huH hv (hfix u huU)

include hp hA hpK in
theorem iInf_eq_bot_of_faithful (hρ : Function.Injective ρ) {T : Finset (Hyperplane A p)}
    (hT : ∀ H : Hyperplane A p, H ∈ T ↔ weightSpace ρ H.1 ≠ ⊥) : ⨅ H ∈ T, H.1 = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro a ha
  simp only [Subgroup.mem_iInf] at ha
  exact eq_one_of_forall_mem_hyperplane ρ hp hA hpK hρ fun H hH => ha H ((hT H).mpr hH)

include hp hA hpK in
theorem apply_sub_mem_weightSpace {H₁ : Hyperplane A p} {y : A}
    (hy : ∀ H : Hyperplane A p, H ≠ H₁ → weightSpace ρ H.1 ≠ ⊥ → y ∈ H.1) (v : V) :
    ρ y v - v ∈ weightSpace ρ H₁.1 := by
  classical
  haveI : Fintype (Option (Hyperplane A p)) := Fintype.ofFinite _
  have hsum : ∑ i, ρ.asAlgebraHom (eps K A p i) v = v := by
    have := congrArg (fun f : Module.End K V => f v) (sum_asAlgebraHom_eps ρ hp hA hpK)
    simpa [LinearMap.sum_apply] using this
  have hterm : ∀ i, ρ y (ρ.asAlgebraHom (eps K A p i) v) - ρ.asAlgebraHom (eps K A p i) v ∈
      weightSpace ρ H₁.1 := by
    intro i
    rcases i with _ | H
    · have hfix : ρ.asAlgebraHom (eps K A p none) v ∈ fixedSpace ρ ⊤ := by
        rw [← weightFamily_none ρ hp hA hpK]
        exact ⟨v, rfl⟩
      rw [hfix y (Subgroup.mem_top y), sub_self]
      exact Submodule.zero_mem _
    · have hmem : ρ.asAlgebraHom (eps K A p (some H)) v ∈ weightSpace ρ H.1 := ⟨v, rfl⟩
      by_cases hH : H = H₁
      · subst hH
        exact Submodule.sub_mem _ (apply_mem_weightSpace ρ _ y hmem) hmem
      · by_cases hbot : weightSpace ρ H.1 = ⊥
        · rw [hbot, Submodule.mem_bot] at hmem
          rw [hmem, map_zero, sub_self]
          exact Submodule.zero_mem _
        · rw [apply_eq_of_mem_weightSpace ρ (hy H hH hbot) hmem, sub_self]
          exact Submodule.zero_mem _
  have hsub : ρ y v - v =
      ∑ i, (ρ y (ρ.asAlgebraHom (eps K A p i) v) - ρ.asAlgebraHom (eps K A p i) v) := by
    rw [Finset.sum_sub_distrib, ← map_sum, hsum]
  rw [hsub]
  exact Submodule.sum_mem _ fun i _ => hterm i

include hp hA hpK in
private theorem exists_planes_aux [FiniteDimensional K V] (hρ : Function.Injective ρ) {r d : ℕ}
    (hr : 2 ≤ r) (hcard : Nat.card A = p ^ r) {T : Finset (Hyperplane A p)}
    (hT : ∀ H : Hyperplane A p, H ∈ T ↔ weightSpace ρ H.1 ≠ ⊥) (hTcard : T.card = r)
    (hd : ∀ H ∈ T, Module.finrank K (weightSpace ρ H.1) = d) :
    ∃ yy zz : A, yy ≠ 1 ∧ zz ∉ Subgroup.zpowers yy ∧
      Module.finrank K (fixedSpace ρ (Subgroup.zpowers yy)) =
        Module.finrank K (fixedSpace ρ ⊤) + (r - 1) * d ∧
      Module.finrank K (fixedSpace ρ (Subgroup.zpowers yy ⊔ Subgroup.zpowers zz)) =
        Module.finrank K (fixedSpace ρ ⊤) + (r - 2) * d ∧
      (∀ a : A, (∀ v ∈ fixedSpace ρ (Subgroup.zpowers yy), ρ a v = v) →
        a ∈ Subgroup.zpowers yy) ∧
      ∀ v : V, ρ zz (ρ yy v - v) = ρ yy v - v := by
  classical
  haveI := Fact.mk hp
  have hT0 : ⨅ H ∈ T, H.1 = ⊥ := iInf_eq_bot_of_faithful ρ hp hA hpK hρ hT
  have hcard' : Nat.card A = p ^ T.card := by rw [hTcard]; exact hcard
  have key : ∀ H₀ ∈ T, ∃ y : A, y ≠ 1 ∧ y ∈ (⨅ H ∈ T.erase H₀, H.1 : Subgroup A) ∧
      y ∉ H₀.1 ∧ Subgroup.zpowers y = (⨅ H ∈ T.erase H₀, H.1 : Subgroup A) := by
    intro H₀ hH₀
    obtain ⟨hinf, hcardL⟩ := card_biInf_erase hp hT0 hcard' hH₀
    set L : Subgroup A := ⨅ H ∈ T.erase H₀, H.1 with hL
    have hLne : L ≠ ⊥ := fun h => by
      rw [h, Subgroup.card_bot] at hcardL
      exact hp.ne_one hcardL.symm
    obtain ⟨⟨y, hyL⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hLne
    have hy1' : y ≠ 1 := fun h => hy1 (Subtype.ext h)
    refine ⟨y, hy1', hyL, fun hy => hy1' ?_, ?_⟩
    · have : y ∈ H₀.1 ⊓ L := ⟨hy, hyL⟩
      rwa [hinf, Subgroup.mem_bot] at this
    · refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hyL) ?_
      rw [Nat.card_zpowers, orderOf_eq_prime (hA y) hy1', hcardL]
  obtain ⟨H₁, hH₁, H₂, hH₂, h12⟩ := Finset.one_lt_card.mp (by omega : 1 < T.card)
  obtain ⟨yy, hyy1, hyyL, hyyH, hyyz⟩ := key H₁ hH₁
  obtain ⟨zz, hzz1, hzzL, hzzH, hzzz⟩ := key H₂ hH₂
  have hLle : ∀ {H₀ H : Hyperplane A p}, H ∈ T.erase H₀ →
      (⨅ H' ∈ T.erase H₀, H'.1 : Subgroup A) ≤ H.1 := fun {H₀ H} hH => iInf₂_le H hH
  have hH₂mem : H₂ ∈ T.erase H₁ := Finset.mem_erase.mpr ⟨Ne.symm h12, hH₂⟩
  have hsum : ∀ S : Finset (Hyperplane A p), S ⊆ T →
      ∑ H ∈ S, Module.finrank K (weightSpace ρ H.1) = S.card * d := fun S hS => by
    rw [Finset.sum_congr rfl (fun H hH => hd H (hS hH)), Finset.sum_const, smul_eq_mul]
  have hfilt1 : T.filter (fun H => Subgroup.zpowers yy ≤ H.1) = T.erase H₁ := by
    ext H
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨hH, hle⟩
      refine ⟨fun h => ?_, hH⟩
      subst h
      exact hyyH (hle (Subgroup.mem_zpowers yy))
    · rintro ⟨hne, hH⟩
      refine ⟨hH, ?_⟩
      rw [hyyz]
      exact hLle (Finset.mem_erase.mpr ⟨hne, hH⟩)
  have hfilt2 : T.filter (fun H => Subgroup.zpowers yy ⊔ Subgroup.zpowers zz ≤ H.1) =
      (T.erase H₁).erase H₂ := by
    ext H
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨hH, hle⟩
      have hy : yy ∈ H.1 := hle (Subgroup.mem_sup_left (Subgroup.mem_zpowers yy))
      have hz : zz ∈ H.1 := hle (Subgroup.mem_sup_right (Subgroup.mem_zpowers zz))
      exact ⟨fun h => hzzH (h ▸ hz), fun h => hyyH (h ▸ hy), hH⟩
    · rintro ⟨hne2, hne1, hH⟩
      refine ⟨hH, sup_le ?_ ?_⟩
      · rw [hyyz]
        exact hLle (Finset.mem_erase.mpr ⟨hne1, hH⟩)
      · rw [hzzz]
        exact hLle (Finset.mem_erase.mpr ⟨hne2, hH⟩)
  refine ⟨yy, zz, hyy1, ?_, ?_, ?_, ?_, ?_⟩
  · intro hmem
    rw [hyyz] at hmem
    exact hzzH (hLle hH₂mem hmem)
  · rw [finrank_fixedSpace_eq ρ hp hA hpK hT, hfilt1, hsum _ (Finset.erase_subset _ _),
      Finset.card_erase_of_mem hH₁, hTcard]
  · rw [finrank_fixedSpace_eq ρ hp hA hpK hT, hfilt2,
      hsum _ ((Finset.erase_subset _ _).trans (Finset.erase_subset _ _)),
      Finset.card_erase_of_mem hH₂mem, Finset.card_erase_of_mem hH₁, hTcard]
    congr 2
  · intro a ha
    rw [hyyz]
    simp only [Subgroup.mem_iInf]
    intro H hH
    by_contra haH
    have hne : weightSpace ρ H.1 ≠ ⊥ := (hT H).mp (Finset.mem_of_mem_erase hH)
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    have hyH : Subgroup.zpowers yy ≤ H.1 := by
      rw [hyyz]
      exact hLle hH
    have hvfix : v ∈ fixedSpace ρ (Subgroup.zpowers yy) := fun u hu =>
      apply_eq_of_mem_weightSpace ρ (hyH hu) hv
    exact hv0 (eq_zero_of_mem_weightSpace_of_fixed ρ hp hA hpK haH hv (ha v hvfix))
  · intro v
    have hzH₁ : zz ∈ H₁.1 := hLle (Finset.mem_erase.mpr ⟨h12, hH₁⟩) hzzL
    have hyH : ∀ H : Hyperplane A p, H ≠ H₁ → weightSpace ρ H.1 ≠ ⊥ → yy ∈ H.1 :=
      fun H hne hbot => hLle (Finset.mem_erase.mpr ⟨hne, (hT H).mpr hbot⟩) hyyL
    exact apply_eq_of_mem_weightSpace ρ hzH₁ (apply_sub_mem_weightSpace ρ hp hA hpK hyH v)

include hp hA hpK in
theorem exists_planes_of_mem [FiniteDimensional K V] [DecidableEq (Hyperplane A p)]
    (hρ : Function.Injective ρ) {r : ℕ}
    (hcard : Nat.card A = p ^ r) {T : Finset (Hyperplane A p)}
    (hT : ∀ H : Hyperplane A p, H ∈ T ↔ weightSpace ρ H.1 ≠ ⊥) (hTcard : T.card = r)
    {H₁ H₂ : Hyperplane A p} (hH₁ : H₁ ∈ T) (hH₂ : H₂ ∈ T) (h12 : H₁ ≠ H₂) :
    ∃ yy zz : A, yy ≠ 1 ∧ zz ∉ Subgroup.zpowers yy ∧
      Module.finrank K (fixedSpace ρ (Subgroup.zpowers yy)) =
        Module.finrank K (fixedSpace ρ ⊤) +
          ∑ H ∈ T.erase H₁, Module.finrank K (weightSpace ρ H.1) ∧
      Module.finrank K (fixedSpace ρ (Subgroup.zpowers yy ⊔ Subgroup.zpowers zz)) =
        Module.finrank K (fixedSpace ρ ⊤) +
          ∑ H ∈ (T.erase H₁).erase H₂, Module.finrank K (weightSpace ρ H.1) ∧
      (∀ a : A, (∀ v ∈ fixedSpace ρ (Subgroup.zpowers yy), ρ a v = v) →
        a ∈ Subgroup.zpowers yy) ∧
      ∀ v : V, ρ zz (ρ yy v - v) = ρ yy v - v := by
  classical
  haveI := Fact.mk hp
  have hT0 : ⨅ H ∈ T, H.1 = ⊥ := iInf_eq_bot_of_faithful ρ hp hA hpK hρ hT
  have hcard' : Nat.card A = p ^ T.card := by rw [hTcard]; exact hcard
  have key : ∀ H₀ ∈ T, ∃ y : A, y ≠ 1 ∧ y ∈ (⨅ H ∈ T.erase H₀, H.1 : Subgroup A) ∧
      y ∉ H₀.1 ∧ Subgroup.zpowers y = (⨅ H ∈ T.erase H₀, H.1 : Subgroup A) := by
    intro H₀ hH₀
    obtain ⟨hinf, hcardL⟩ := card_biInf_erase hp hT0 hcard' hH₀
    set L : Subgroup A := ⨅ H ∈ T.erase H₀, H.1 with hL
    have hLne : L ≠ ⊥ := fun h => by
      rw [h, Subgroup.card_bot] at hcardL
      exact hp.ne_one hcardL.symm
    obtain ⟨⟨y, hyL⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hLne
    have hy1' : y ≠ 1 := fun h => hy1 (Subtype.ext h)
    refine ⟨y, hy1', hyL, fun hy => hy1' ?_, ?_⟩
    · have : y ∈ H₀.1 ⊓ L := ⟨hy, hyL⟩
      rwa [hinf, Subgroup.mem_bot] at this
    · refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hyL) ?_
      rw [Nat.card_zpowers, orderOf_eq_prime (hA y) hy1', hcardL]
  obtain ⟨yy, hyy1, hyyL, hyyH, hyyz⟩ := key H₁ hH₁
  obtain ⟨zz, hzz1, hzzL, hzzH, hzzz⟩ := key H₂ hH₂
  have hLle : ∀ {H₀ H : Hyperplane A p}, H ∈ T.erase H₀ →
      (⨅ H' ∈ T.erase H₀, H'.1 : Subgroup A) ≤ H.1 := fun {H₀ H} hH => iInf₂_le H hH
  have hH₂mem : H₂ ∈ T.erase H₁ := Finset.mem_erase.mpr ⟨Ne.symm h12, hH₂⟩
  have hfilt1 : T.filter (fun H => Subgroup.zpowers yy ≤ H.1) = T.erase H₁ := by
    ext H
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨hH, hle⟩
      refine ⟨fun h => ?_, hH⟩
      subst h
      exact hyyH (hle (Subgroup.mem_zpowers yy))
    · rintro ⟨hne, hH⟩
      refine ⟨hH, ?_⟩
      rw [hyyz]
      exact hLle (Finset.mem_erase.mpr ⟨hne, hH⟩)
  have hfilt2 : T.filter (fun H => Subgroup.zpowers yy ⊔ Subgroup.zpowers zz ≤ H.1) =
      (T.erase H₁).erase H₂ := by
    ext H
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨hH, hle⟩
      have hy : yy ∈ H.1 := hle (Subgroup.mem_sup_left (Subgroup.mem_zpowers yy))
      have hz : zz ∈ H.1 := hle (Subgroup.mem_sup_right (Subgroup.mem_zpowers zz))
      exact ⟨fun h => hzzH (h ▸ hz), fun h => hyyH (h ▸ hy), hH⟩
    · rintro ⟨hne2, hne1, hH⟩
      refine ⟨hH, sup_le ?_ ?_⟩
      · rw [hyyz]
        exact hLle (Finset.mem_erase.mpr ⟨hne1, hH⟩)
      · rw [hzzz]
        exact hLle (Finset.mem_erase.mpr ⟨hne2, hH⟩)
  refine ⟨yy, zz, hyy1, ?_, ?_, ?_, ?_, ?_⟩
  · intro hmem
    rw [hyyz] at hmem
    exact hzzH (hLle hH₂mem hmem)
  · rw [finrank_fixedSpace_eq ρ hp hA hpK hT, hfilt1]
  · rw [finrank_fixedSpace_eq ρ hp hA hpK hT, hfilt2]
  · intro a ha
    rw [hyyz]
    simp only [Subgroup.mem_iInf]
    intro H hH
    by_contra haH
    have hne : weightSpace ρ H.1 ≠ ⊥ := (hT H).mp (Finset.mem_of_mem_erase hH)
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    have hyH : Subgroup.zpowers yy ≤ H.1 := by
      rw [hyyz]
      exact hLle hH
    have hvfix : v ∈ fixedSpace ρ (Subgroup.zpowers yy) := fun u hu =>
      apply_eq_of_mem_weightSpace ρ (hyH hu) hv
    exact hv0 (eq_zero_of_mem_weightSpace_of_fixed ρ hp hA hpK haH hv (ha v hvfix))
  · intro v
    have hzH₁ : zz ∈ H₁.1 := hLle (Finset.mem_erase.mpr ⟨h12, hH₁⟩) hzzL
    have hyH : ∀ H : Hyperplane A p, H ≠ H₁ → weightSpace ρ H.1 ≠ ⊥ → yy ∈ H.1 :=
      fun H hne hbot => hLle (Finset.mem_erase.mpr ⟨hne, (hT H).mpr hbot⟩) hyyL
    exact apply_eq_of_mem_weightSpace ρ hzH₁ (apply_sub_mem_weightSpace ρ hp hA hpK hyH v)

variable (hρ : Function.Injective ρ)

include hp hA hpK hQ h2 hρQ hp2 hρ in
theorem exists_support [FiniteDimensional K V] {r : ℕ} (hcard : Nat.card A = p ^ r) :
    ∃ T : Finset (Hyperplane A p), (∀ H : Hyperplane A p, H ∈ T ↔ weightSpace ρ H.1 ≠ ⊥) ∧
      r ≤ T.card ∧
      Module.finrank K V = Module.finrank K (fixedSpace ρ ⊤) +
        ∑ H ∈ T, Module.finrank K (weightSpace ρ H.1) ∧
      (∀ H ∈ T, 2 ≤ Module.finrank K (weightSpace ρ H.1)) ∧
      Even (∑ H ∈ T, Module.finrank K (weightSpace ρ H.1)) := by
  classical
  haveI : Fintype (Hyperplane A p) := Fintype.ofFinite _
  set T : Finset (Hyperplane A p) := Finset.univ.filter (fun H => weightSpace ρ H.1 ≠ ⊥) with hTdef
  have hT : ∀ H : Hyperplane A p, H ∈ T ↔ weightSpace ρ H.1 ≠ ⊥ := fun H => by simp [hTdef]
  refine ⟨T, hT, ?_, ?_, ?_, ?_⟩
  · have h1 := index_biInf_le T
    rw [iInf_eq_bot_of_faithful ρ hp hA hpK hρ hT, Subgroup.index_bot, hcard] at h1
    exact (Nat.pow_le_pow_iff_right hp.one_lt).mp h1
  · rw [finrank_eq_fixedSpace_add_sum ρ hp hA hpK]
    congr 1
    refine (Finset.sum_filter_of_ne fun H _ hH hbot => ?_).symm
    rw [hbot, finrank_bot] at hH
    exact hH rfl
  · exact fun H hH => two_le_finrank_weightSpace ρ hp hA hpK Q hQ h2 hρQ hp2 H ((hT H).mp hH)
  · exact Finset.sum_induction _ Even (fun _ _ => Even.add) Even.zero fun H _ =>
      even_finrank_weightSpace ρ hp hA hpK Q hQ h2 hρQ hp2 H

include hp hA hpK hQ h2 hρQ hp2 hρ in
theorem exists_support_two [FiniteDimensional K V] {r : ℕ} (hcard : Nat.card A = p ^ r)
    (hle : Module.finrank K V ≤ Module.finrank K (fixedSpace ρ ⊤) + 2 * r + 1) :
    ∃ T : Finset (Hyperplane A p), (∀ H : Hyperplane A p, H ∈ T ↔ weightSpace ρ H.1 ≠ ⊥) ∧
      T.card = r ∧ (∀ H ∈ T, Module.finrank K (weightSpace ρ H.1) = 2) ∧
      Module.finrank K V = Module.finrank K (fixedSpace ρ ⊤) + 2 * r := by
  obtain ⟨T, hT, hr, hsum, hge, k, hk⟩ :=
    exists_support ρ hp hA hpK Q hQ h2 hρQ hp2 hρ hcard
  have hle2 : 2 * T.card ≤ ∑ H ∈ T, Module.finrank K (weightSpace ρ H.1) := by
    calc 2 * T.card = ∑ _H ∈ T, 2 := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ _ := Finset.sum_le_sum hge
  have hTr : T.card = r := by omega
  have hS : ∑ H ∈ T, Module.finrank K (weightSpace ρ H.1) = 2 * r := by omega
  refine ⟨T, hT, hTr, ?_, by omega⟩
  have hsum2 : ∑ _H ∈ T, 2 = ∑ H ∈ T, Module.finrank K (weightSpace ρ H.1) := by
    rw [Finset.sum_const, smul_eq_mul, hS, hTr, mul_comm]
  exact fun H hH => ((Finset.sum_eq_sum_iff_of_le hge).mp hsum2 H hH).symm

include hp hA hpK hQ h2 hρQ hp2 hρ in
theorem exists_config_seven (hcard : Nat.card A = p ^ 3) (hV : Module.finrank K V = 7) :
    ∃ H₁ H₂ H₃ : Hyperplane A p, H₁ ≠ H₂ ∧ H₁ ≠ H₃ ∧ H₂ ≠ H₃ ∧ H₁.1 ⊓ H₂.1 ⊓ H₃.1 = ⊥ ∧
      Module.finrank K (fixedSpace ρ ⊤) = 1 ∧
      Module.finrank K (weightSpace ρ H₁.1) = 2 ∧ Module.finrank K (weightSpace ρ H₂.1) = 2 ∧
      Module.finrank K (weightSpace ρ H₃.1) = 2 ∧
      ∀ H : Hyperplane A p, H ≠ H₁ → H ≠ H₂ → H ≠ H₃ → weightSpace ρ H.1 = ⊥ := by
  classical
  haveI : FiniteDimensional K V := Module.finite_of_finrank_pos (by omega)
  obtain ⟨T, hT, hTc, hd, hsum⟩ :=
    exists_support_two ρ hp hA hpK Q hQ h2 hρQ hp2 hρ hcard (r := 3) (by omega)
  obtain ⟨H₁, H₂, H₃, h12, h13, h23, rfl⟩ := Finset.card_eq_three.mp hTc
  refine ⟨H₁, H₂, H₃, h12, h13, h23, ?_, by omega, hd H₁ (by simp), hd H₂ (by simp),
    hd H₃ (by simp), ?_⟩
  · rw [Subgroup.eq_bot_iff_forall]
    intro a ha
    obtain ⟨ha12, ha3⟩ := Subgroup.mem_inf.mp ha
    obtain ⟨ha1, ha2⟩ := Subgroup.mem_inf.mp ha12
    refine eq_one_of_forall_mem_hyperplane ρ hp hA hpK hρ fun H hH => ?_
    have hHT := (hT H).mpr hH
    simp only [Finset.mem_insert, Finset.mem_singleton] at hHT
    rcases hHT with rfl | rfl | rfl
    exacts [ha1, ha2, ha3]
  · intro H h1 h2' h3
    by_contra hne
    have hHT := (hT H).mpr hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hHT
    rcases hHT with h | h | h
    exacts [h1 h, h2' h, h3 h]

include hp hA hpK hQ h2 hρQ hp2 hρ in
theorem exists_config_eight_four (hcard : Nat.card A = p ^ 4) (hV : Module.finrank K V = 8) :
    ∃ H₁ H₂ H₃ H₄ : Hyperplane A p, H₁ ≠ H₂ ∧ H₁ ≠ H₃ ∧ H₁ ≠ H₄ ∧ H₂ ≠ H₃ ∧ H₂ ≠ H₄ ∧
      H₃ ≠ H₄ ∧ H₁.1 ⊓ H₂.1 ⊓ H₃.1 ⊓ H₄.1 = ⊥ ∧ fixedSpace ρ ⊤ = ⊥ ∧
      Module.finrank K (weightSpace ρ H₁.1) = 2 ∧ Module.finrank K (weightSpace ρ H₂.1) = 2 ∧
      Module.finrank K (weightSpace ρ H₃.1) = 2 ∧ Module.finrank K (weightSpace ρ H₄.1) = 2 ∧
      ∀ H : Hyperplane A p, H ≠ H₁ → H ≠ H₂ → H ≠ H₃ → H ≠ H₄ → weightSpace ρ H.1 = ⊥ := by
  classical
  haveI : FiniteDimensional K V := Module.finite_of_finrank_pos (by omega)
  obtain ⟨T, hT, hTc, hd, hsum⟩ :=
    exists_support_two ρ hp hA hpK Q hQ h2 hρQ hp2 hρ hcard (r := 4) (by omega)
  obtain ⟨H₄, t, hH₄, rfl, ht⟩ := Finset.card_eq_succ.mp hTc
  obtain ⟨H₁, H₂, H₃, h12, h13, h23, rfl⟩ := Finset.card_eq_three.mp ht
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hH₄
  obtain ⟨h41, h42, h43⟩ := hH₄
  refine ⟨H₁, H₂, H₃, H₄, h12, h13, Ne.symm h41, h23, Ne.symm h42, Ne.symm h43, ?_,
    Submodule.finrank_eq_zero.mp (by omega), hd H₁ (by simp), hd H₂ (by simp), hd H₃ (by simp),
    hd H₄ (by simp), ?_⟩
  · rw [Subgroup.eq_bot_iff_forall]
    intro a ha
    obtain ⟨ha123, ha4⟩ := Subgroup.mem_inf.mp ha
    obtain ⟨ha12, ha3⟩ := Subgroup.mem_inf.mp ha123
    obtain ⟨ha1, ha2⟩ := Subgroup.mem_inf.mp ha12
    refine eq_one_of_forall_mem_hyperplane ρ hp hA hpK hρ fun H hH => ?_
    have hHT := (hT H).mpr hH
    simp only [Finset.mem_insert, Finset.mem_singleton] at hHT
    rcases hHT with rfl | rfl | rfl | rfl
    exacts [ha4, ha1, ha2, ha3]
  · intro H h1 h2' h3 h4
    by_contra hne
    have hHT := (hT H).mpr hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hHT
    rcases hHT with h | h | h | h
    exacts [h4 h, h1 h, h2' h, h3 h]

include hp hA hpK hQ h2 hρQ hp2 hρ in
theorem exists_config_eight_three (hcard : Nat.card A = p ^ 3) (hV : Module.finrank K V = 8)
    (hfix : fixedSpace ρ ⊤ ≠ ⊥) :
    ∃ H₁ H₂ H₃ : Hyperplane A p, H₁ ≠ H₂ ∧ H₁ ≠ H₃ ∧ H₂ ≠ H₃ ∧ H₁.1 ⊓ H₂.1 ⊓ H₃.1 = ⊥ ∧
      Module.finrank K (fixedSpace ρ ⊤) = 2 ∧
      Module.finrank K (weightSpace ρ H₁.1) = 2 ∧ Module.finrank K (weightSpace ρ H₂.1) = 2 ∧
      Module.finrank K (weightSpace ρ H₃.1) = 2 ∧
      ∀ H : Hyperplane A p, H ≠ H₁ → H ≠ H₂ → H ≠ H₃ → weightSpace ρ H.1 = ⊥ := by
  classical
  haveI : FiniteDimensional K V := Module.finite_of_finrank_pos (by omega)
  have hc : Module.finrank K (fixedSpace ρ ⊤) ≠ 0 := fun h =>
    hfix (Submodule.finrank_eq_zero.mp h)
  obtain ⟨T, hT, hTc, hd, hsum⟩ :=
    exists_support_two ρ hp hA hpK Q hQ h2 hρQ hp2 hρ hcard (r := 3) (by omega)
  obtain ⟨H₁, H₂, H₃, h12, h13, h23, rfl⟩ := Finset.card_eq_three.mp hTc
  refine ⟨H₁, H₂, H₃, h12, h13, h23, ?_, by omega, hd H₁ (by simp), hd H₂ (by simp),
    hd H₃ (by simp), ?_⟩
  · rw [Subgroup.eq_bot_iff_forall]
    intro a ha
    obtain ⟨ha12, ha3⟩ := Subgroup.mem_inf.mp ha
    obtain ⟨ha1, ha2⟩ := Subgroup.mem_inf.mp ha12
    refine eq_one_of_forall_mem_hyperplane ρ hp hA hpK hρ fun H hH => ?_
    have hHT := (hT H).mpr hH
    simp only [Finset.mem_insert, Finset.mem_singleton] at hHT
    rcases hHT with rfl | rfl | rfl
    exacts [ha1, ha2, ha3]
  · intro H h1 h2' h3
    by_contra hne
    have hHT := (hT H).mpr hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hHT
    rcases hHT with h | h | h
    exacts [h1 h, h2' h, h3 h]

include hp hA hpK hQ h2 hρQ hp2 hρ in
theorem exists_planes_seven (hcard : Nat.card A = p ^ 3) (hV : Module.finrank K V = 7) :
    ∃ yy zz : A, yy ≠ 1 ∧ zz ∉ Subgroup.zpowers yy ∧
      Module.finrank K (fixedSpace ρ (Subgroup.zpowers yy)) = 5 ∧
      Module.finrank K (fixedSpace ρ (Subgroup.zpowers yy ⊔ Subgroup.zpowers zz)) = 3 ∧
      (∀ a : A, (∀ v ∈ fixedSpace ρ (Subgroup.zpowers yy), ρ a v = v) →
        a ∈ Subgroup.zpowers yy) ∧
      ∀ v : V, ρ zz (ρ yy v - v) = ρ yy v - v := by
  classical
  haveI : FiniteDimensional K V := Module.finite_of_finrank_pos (by omega)
  obtain ⟨T, hT, hTc, hd, hsum⟩ :=
    exists_support_two ρ hp hA hpK Q hQ h2 hρQ hp2 hρ hcard (r := 3) (by omega)
  obtain ⟨yy, zz, h1, h2', h3, h4, h5⟩ :=
    exists_planes_aux ρ hp hA hpK hρ (r := 3) (d := 2) (by norm_num) hcard hT hTc hd
  exact ⟨yy, zz, h1, h2', by omega, by omega, h5.1, h5.2⟩

include hp hA hpK hQ h2 hρQ hp2 hρ in
theorem exists_planes_eight_four (hcard : Nat.card A = p ^ 4) (hV : Module.finrank K V = 8) :
    ∃ yy zz : A, yy ≠ 1 ∧ zz ∉ Subgroup.zpowers yy ∧
      Module.finrank K (fixedSpace ρ (Subgroup.zpowers yy)) = 6 ∧
      Module.finrank K (fixedSpace ρ (Subgroup.zpowers yy ⊔ Subgroup.zpowers zz)) = 4 ∧
      (∀ a : A, (∀ v ∈ fixedSpace ρ (Subgroup.zpowers yy), ρ a v = v) →
        a ∈ Subgroup.zpowers yy) ∧
      ∀ v : V, ρ zz (ρ yy v - v) = ρ yy v - v := by
  classical
  haveI : FiniteDimensional K V := Module.finite_of_finrank_pos (by omega)
  obtain ⟨T, hT, hTc, hd, hsum⟩ :=
    exists_support_two ρ hp hA hpK Q hQ h2 hρQ hp2 hρ hcard (r := 4) (by omega)
  obtain ⟨yy, zz, h1, h2', h3, h4, h5⟩ :=
    exists_planes_aux ρ hp hA hpK hρ (r := 4) (d := 2) (by norm_num) hcard hT hTc hd
  exact ⟨yy, zz, h1, h2', by omega, by omega, h5.1, h5.2⟩

include hp hA hpK hQ h2 hρQ hp2 hρ in
theorem exists_planes_eight_three (hcard : Nat.card A = p ^ 3) (hV : Module.finrank K V = 8)
    (hfix : fixedSpace ρ ⊤ ≠ ⊥) :
    ∃ yy zz : A, yy ≠ 1 ∧ zz ∉ Subgroup.zpowers yy ∧
      Module.finrank K (fixedSpace ρ (Subgroup.zpowers yy)) = 6 ∧
      Module.finrank K (fixedSpace ρ (Subgroup.zpowers yy ⊔ Subgroup.zpowers zz)) = 4 ∧
      (∀ a : A, (∀ v ∈ fixedSpace ρ (Subgroup.zpowers yy), ρ a v = v) →
        a ∈ Subgroup.zpowers yy) ∧
      ∀ v : V, ρ zz (ρ yy v - v) = ρ yy v - v := by
  classical
  haveI : FiniteDimensional K V := Module.finite_of_finrank_pos (by omega)
  have hc : Module.finrank K (fixedSpace ρ ⊤) ≠ 0 := fun h =>
    hfix (Submodule.finrank_eq_zero.mp h)
  obtain ⟨T, hT, hTc, hd, hsum⟩ :=
    exists_support_two ρ hp hA hpK Q hQ h2 hρQ hp2 hρ hcard (r := 3) (by omega)
  obtain ⟨yy, zz, h1, h2', h3, h4, h5⟩ :=
    exists_planes_aux ρ hp hA hpK hρ (r := 3) (d := 2) (by norm_num) hcard hT hTc hd
  exact ⟨yy, zz, h1, h2', by omega, by omega, h5.1, h5.2⟩

end Config

end CFSG.LocalAnalysis.GLTheoremA.H81Orth.Wt
