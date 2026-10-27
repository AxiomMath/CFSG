module

public import CFSG.FeitThompson.Definitions.RawNormalPrimeSetCore
public import Mathlib.GroupTheory.Solvable
public import Mathlib.Order.CompletePartialOrder
import CFSG.FeitThompson.Local.CoprimeActionSelfCentralizingFixedPGroup
import CFSG.FeitThompson.Local.PuigLambdaAbelianGeneratedPrimeCore
import CFSG.FeitThompson.Local.PCoreSelfCentralizingNoNormalComplement
import CFSG.FeitThompson.Local.MaximalPlaneDerivedNormalComplement
import CFSG.FeitThompson.Local.PrimeFixedSylowNotNarrow

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

variable {G : Type*} [Group G] {p : ℕ}

theorem isPGroup_centralizer_of_inf_pCore_le [Finite G] [Group.IsSolvable G] (hp : p.Prime)
    (hp' : pComplCore p G = ⊥) {P : Subgroup G} [P.Normal] (hP : IsPGroup p P)
    (hPC : pCore p G ⊓ centralizer (P : Set G) ≤ P) :
    IsPGroup p (centralizer (P : Set G)) := by
  have := Fact.mk hp
  set Q := pCore p G with hQdef
  have hQnormal : Q.Normal := pCore_normal p G
  have hQp : IsPGroup p Q := isPGroup_pCore hp G
  have hCQ : centralizer (Q : Set G) ≤ Q := centralizer_pCore_le_pCore hp hp'
  have hPQ : P ≤ Q := le_pCore hp ‹P.Normal› hP
  rw [isPGroup_iff_primeFactors_card_subset hp.ne_zero, hp.primeFactors]
  intro q hq
  simp only [Finset.mem_singleton]
  by_contra hqp
  have hqprime := Nat.prime_of_mem_primeFactors hq
  have := Fact.mk hqprime
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := centralizer (P : Set G)) q
    (Nat.dvd_of_mem_primeFactors hq)
  set u : G := (x : G) with hudef
  have huC : u ∈ centralizer (P : Set G) := x.2
  have hu : orderOf u = q := by rw [hudef, orderOf_coe, hx]
  set A : Subgroup G := zpowers u with hAdef
  set φ : A →* MulAut Q := (MulAut.conjNormal (H := Q)).comp A.subtype with hφdef
  have hAC : A ≤ centralizer (P : Set G) := zpowers_le.2 huC
  have hPfix : ∀ (v : G) (hv : v ∈ P),
      (⟨v, hPQ hv⟩ : Q) ∈ FixedPoints.subgroup φ.range Q := by
    intro v hv
    rw [mem_fixedPoints_range_iff]
    intro a
    refine Subtype.ext ?_
    change (a : G) * v * (a : G)⁻¹ = v
    rw [← mem_centralizer_iff.1 (hAC a.2) v hv]
    group
  have hself : centralizer (FixedPoints.subgroup φ.range Q : Set Q)
      ≤ FixedPoints.subgroup φ.range Q := by
    intro y hy
    have hyP : (y : G) ∈ centralizer (P : Set G) := by
      rw [mem_centralizer_iff]
      intro v hv
      exact congrArg Subtype.val (mem_centralizer_iff.1 hy _ (hPfix v hv))
    exact hPfix (y : G) (hPC ⟨y.2, hyP⟩)
  have hcop : (Nat.card A).Coprime (Nat.card Q) := by
    obtain ⟨n, hn⟩ := hQp.exists_card_eq
    rw [hAdef, Nat.card_zpowers, hu, hn]
    exact ((Nat.coprime_primes hqprime hp).2 hqp).pow_right n
  have hucent : u ∈ centralizer (Q : Set G) :=
    mem_centralizer_of_conjNormal_eq_one (Q := Q)
      (eq_one_of_coprime_of_centralizer_fixedPoints_le hp hQp φ hcop hself ⟨u, mem_zpowers u⟩)
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 hQp ⟨u, hCQ hucent⟩
  rw [orderOf_mk, hu] at hk
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    exact hqprime.one_lt.ne' hk
  exact hqp ((Nat.prime_dvd_prime_iff_eq hp hqprime).1 (hk ▸ dvd_pow_self p hk0)).symm

theorem centralizer_le_pCore_of_inf_pCore_le [Finite G] [Group.IsSolvable G] (hp : p.Prime)
    (hp' : pComplCore p G = ⊥) {P : Subgroup G} [P.Normal] (hP : IsPGroup p P)
    (hPC : pCore p G ⊓ centralizer (P : Set G) ≤ P) :
    centralizer (P : Set G) ≤ pCore p G :=
  le_pCore hp Subgroup.normal_centralizer (isPGroup_centralizer_of_inf_pCore_le hp hp' hP hPC)

theorem comap_mk'_pCore_quotient_le_pCore [Finite G] (hp : p.Prime) {N : Subgroup G} [N.Normal]
    (hN : IsPGroup p N) :
    (pCore p (G ⧸ N)).comap (QuotientGroup.mk' N) ≤ pCore p G := by
  refine le_pCore hp ((pCore_normal p (G ⧸ N)).comap _) ?_
  refine isPGroup_of_isPGroup_map hp (f := QuotientGroup.mk' N)
    ((isPGroup_pCore hp (G ⧸ N)).to_le (map_comap_le _ _)) (hN.to_le ?_)
  rw [QuotientGroup.ker_mk']
  exact inf_le_left

theorem le_pCore_of_le_sSup_of_inf_pCore_le [Finite G] [Group.IsSolvable G] (hp : p.Prime)
    (hGodd : Odd (Nat.card G)) (hp' : pComplCore p G = ⊥) {P : Subgroup G} [P.Normal]
    (hP : IsPGroup p P) (hPC : pCore p G ⊓ centralizer (P : Set G) ≤ P)
    {𝒜 : Set (Subgroup G)} (hcomm : ∀ A ∈ 𝒜, IsMulCommutative A) (hAp : ∀ A ∈ 𝒜, IsPGroup p A)
    (hnorm : ∀ A ∈ 𝒜, P ≤ normalizer (A : Set G)) {X : Subgroup G} (hX : X ≤ sSup 𝒜) :
    X ≤ pCore p G := by
  have hCp : IsPGroup p (centralizer (P : Set G)) :=
    isPGroup_centralizer_of_inf_pCore_le hp hp' hP hPC
  have hstep : X.map (QuotientGroup.mk' (centralizer (P : Set G)))
      ≤ pCore p (G ⧸ centralizer (P : Set G)) :=
    map_mk'_centralizer_le_pCore_of_le_sSup hp hGodd hP hcomm hAp hnorm hX
  exact (map_le_iff_le_comap.1 hstep).trans (comap_mk'_pCore_quotient_le_pCore hp hCp)

theorem le_pCore_of_le_iSup_of_inf_pCore_le [Finite G] [Group.IsSolvable G] (hp : p.Prime)
    (hGodd : Odd (Nat.card G)) (hp' : pComplCore p G = ⊥) {P : Subgroup G} [P.Normal]
    (hP : IsPGroup p P) (hPC : pCore p G ⊓ centralizer (P : Set G) ≤ P)
    {ι : Sort*} {A : ι → Subgroup G} (hcomm : ∀ i, IsMulCommutative (A i))
    (hAp : ∀ i, IsPGroup p (A i)) (hnorm : ∀ i, P ≤ normalizer (A i : Set G))
    {X : Subgroup G} (hX : X ≤ ⨆ i, A i) :
    X ≤ pCore p G :=
  le_pCore_of_le_sSup_of_inf_pCore_le hp hGodd hp' hP hPC (𝒜 := Set.range A)
    (fun _ ⟨i, hi⟩ => hi ▸ hcomm i) (fun _ ⟨i, hi⟩ => hi ▸ hAp i)
    (fun _ ⟨i, hi⟩ => hi ▸ hnorm i) (by rwa [sSup_range])

theorem le_pCore_of_eq_closure_of_inf_pCore_le [Finite G] [Group.IsSolvable G] (hp : p.Prime)
    (_hpodd : Odd p) (hGodd : Odd (Nat.card G)) (hp' : pComplCore p G = ⊥) {P : Subgroup G}
    [P.Normal] (hP : IsPGroup p P) (hPC : pCore p G ⊓ centralizer (P : Set G) ≤ P)
    {𝒜 : Set (Subgroup G)} (hcomm : ∀ A ∈ 𝒜, IsMulCommutative A) (hAp : ∀ A ∈ 𝒜, IsPGroup p A)
    (hnorm : ∀ A ∈ 𝒜, ∀ u ∈ P, ∀ a ∈ A, u * a * u⁻¹ ∈ A)
    {X : Subgroup G} (hX : X = closure (⋃ A ∈ 𝒜, (A : Set G))) :
    X ≤ pCore p G := by
  have hXle : X ≤ sSup 𝒜 := by
    rw [hX, closure_le]
    simp only [Set.iUnion_subset_iff]
    exact fun A hA => (le_sSup hA : A ≤ sSup 𝒜)
  exact le_pCore_of_le_sSup_of_inf_pCore_le hp hGodd hp' hP hPC hcomm hAp
    (fun A hA => le_normalizer_of_forall_conj_mem (hnorm A hA)) hXle

end

end CFSG.FeitThompson
