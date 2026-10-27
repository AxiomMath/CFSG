module

public import CFSG.FeitThompson.Local.QuadraticElementCentralizerQuotientCore
public import CFSG.FeitThompson.Definitions.PuigSubgroupIteration

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

variable {G : Type*} [Group G] {p : ℕ}

theorem le_normalizer_of_forall_conj_mem {U A : Subgroup G}
    (hU : ∀ u ∈ U, ∀ a ∈ A, u * a * u⁻¹ ∈ A) : U ≤ normalizer (A : Set G) :=
  fun u hu => mem_normalizer_iff.2 fun a =>
    ⟨hU u hu a, fun ha => by simpa [mul_assoc] using hU u⁻¹ (inv_mem hu) _ ha⟩

theorem map_mk'_sup_eq_map_mk' (C X : Subgroup G) [C.Normal] :
    (X ⊔ C).map (QuotientGroup.mk' C) = X.map (QuotientGroup.mk' C) := by
  rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq]

theorem actsQuadratically_conjNormal_of_mem_of_isMulCommutative {P : Subgroup G} [P.Normal]
    {A : Subgroup G} (hAcomm : IsMulCommutative A) (hAP : P ≤ normalizer (A : Set G)) {a : G}
    (ha : a ∈ A) : ActsQuadratically (MulAut.conjNormal (H := P)) a := by
  rw [actsQuadratically_conjNormal_iff, Subgroup.centralizer_closure, mem_centralizer_iff]
  rintro y ⟨v, hv, rfl⟩
  have hy : v⁻¹ * a * v * a⁻¹ ∈ A :=
    mul_mem ((mem_normalizer_iff''.1 (hAP hv) a).1 ha) (inv_mem ha)
  exact isMulCommutative_iff_of_setLike.1 hAcomm _ hy _ ha

theorem mk_mem_pCore_quotient_centralizer_of_mem_abelian_pGroup [Finite G] [Group.IsSolvable G]
    (hp : p.Prime) (hGodd : Odd (Nat.card G)) {P : Subgroup G} [P.Normal] (hP : IsPGroup p P)
    {A : Subgroup G} (hAcomm : IsMulCommutative A) (hAp : IsPGroup p A)
    (hAP : P ≤ normalizer (A : Set G)) {a : G} (ha : a ∈ A) :
    QuotientGroup.mk' (centralizer (P : Set G)) a ∈ pCore p (G ⧸ centralizer (P : Set G)) := by
  have : Fact p.Prime := ⟨hp⟩
  have hord : ∃ k, orderOf a = p ^ k := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 hAp ⟨a, ha⟩
    exact ⟨k, by rwa [Subgroup.orderOf_mk] at hk⟩
  exact mk_mem_pCore_quotient_centralizer_of_quadratic hp hGodd hP hord
    (actsQuadratically_conjNormal_of_mem_of_isMulCommutative hAcomm hAP ha)

theorem map_mk'_centralizer_le_pCore_of_le_sSup [Finite G] [Group.IsSolvable G]
    (hp : p.Prime) (hGodd : Odd (Nat.card G)) {P : Subgroup G} [P.Normal] (hP : IsPGroup p P)
    {𝒜 : Set (Subgroup G)} (hcomm : ∀ A ∈ 𝒜, IsMulCommutative A) (hAp : ∀ A ∈ 𝒜, IsPGroup p A)
    (hnorm : ∀ A ∈ 𝒜, P ≤ normalizer (A : Set G)) {X : Subgroup G} (hX : X ≤ sSup 𝒜) :
    X.map (QuotientGroup.mk' (centralizer (P : Set G)))
      ≤ pCore p (G ⧸ centralizer (P : Set G)) := by
  rw [map_le_iff_le_comap]
  refine hX.trans (sSup_le fun A hA a ha => mem_comap.2 ?_)
  exact mk_mem_pCore_quotient_centralizer_of_mem_abelian_pGroup hp hGodd hP (hcomm A hA)
    (hAp A hA) (hnorm A hA) ha

theorem map_mk'_centralizer_le_pCore_of_le_iSup [Finite G] [Group.IsSolvable G]
    (hp : p.Prime) (hGodd : Odd (Nat.card G)) {P : Subgroup G} [P.Normal] (hP : IsPGroup p P)
    {ι : Sort*} {A : ι → Subgroup G} (hcomm : ∀ i, IsMulCommutative (A i))
    (hAp : ∀ i, IsPGroup p (A i)) (hnorm : ∀ i, P ≤ normalizer (A i : Set G))
    {X : Subgroup G} (hX : X ≤ ⨆ i, A i) :
    X.map (QuotientGroup.mk' (centralizer (P : Set G)))
      ≤ pCore p (G ⧸ centralizer (P : Set G)) :=
  map_mk'_centralizer_le_pCore_of_le_sSup hp hGodd hP (𝒜 := Set.range A)
    (fun _ ⟨i, hi⟩ => hi ▸ hcomm i) (fun _ ⟨i, hi⟩ => hi ▸ hAp i)
    (fun _ ⟨i, hi⟩ => hi ▸ hnorm i) (by rwa [sSup_range])

theorem map_mk'_centralizer_le_pCore_of_eq_closure [Finite G] [Group.IsSolvable G]
    (hp : p.Prime) (_hpodd : Odd p) (hGodd : Odd (Nat.card G)) {P : Subgroup G} [P.Normal]
    (hP : IsPGroup p P) {𝒜 : Set (Subgroup G)} (hcomm : ∀ A ∈ 𝒜, IsMulCommutative A)
    (hAp : ∀ A ∈ 𝒜, IsPGroup p A) (hnorm : ∀ A ∈ 𝒜, ∀ u ∈ P, ∀ a ∈ A, u * a * u⁻¹ ∈ A)
    {X : Subgroup G} (hX : X = closure (⋃ A ∈ 𝒜, (A : Set G))) :
    (X ⊔ centralizer (P : Set G)).map (QuotientGroup.mk' (centralizer (P : Set G)))
      ≤ pCore p (G ⧸ centralizer (P : Set G)) := by
  rw [map_mk'_sup_eq_map_mk']
  have hXle : X ≤ sSup 𝒜 := by
    rw [hX, closure_le]
    simp only [Set.iUnion_subset_iff]
    exact fun A hA => (le_sSup hA : A ≤ sSup 𝒜)
  exact map_mk'_centralizer_le_pCore_of_le_sSup hp hGodd hP hcomm hAp
    (fun A hA => le_normalizer_of_forall_conj_mem (hnorm A hA)) hXle

theorem sSup_le_puigLambda_of_isMulCommutative {P : Subgroup G} {𝒜 : Set (Subgroup G)}
    (hcomm : ∀ A ∈ 𝒜, IsMulCommutative A) (hnorm : ∀ A ∈ 𝒜, P ≤ normalizer (A : Set G)) :
    sSup 𝒜 ≤ puigLambda P :=
  sSup_le fun A hA => le_puigLambda (hcomm A hA) (hnorm A hA)

end

end CFSG.FeitThompson
