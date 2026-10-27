module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenAutomorphisms
public import CFSG.LieType.Chevalley.EvenF4AutomorphismNormalForm
public import CFSG.LieType.Chevalley.EvenTrialityAutomorphismNormalForm
public import CFSG.LieType.Chevalley.OddExceptionalOuterTwoRank
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogLargeReeModel
public import CFSG.Sporadic.Schreier.TitsOuterTwo
public import CFSG.GroupTheory.ABGDGroups.LinearStructure
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoStandardDefs
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHullAutomorphisms

public section

namespace CFSG.ComponentClassification.RankTwoExceptional

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHull
open CFSG.ComponentClassification.RankTwoStandard

section Commutator

theorem commutator_le_ker {M N : Type*} [Group M] [Group N] (Φ : M →* N)
    (hN : ∀ a b : N, a * b = b * a) : commutator M ≤ Φ.ker := by
  rw [commutator_def, commutator_le]
  intro a _ b _
  rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
  exact hN _ _

theorem odd_card_commutator_of_hom {M N : Type*} [Group M] [Group N] [Finite M] (Φ : M →* N)
    (hN : ∀ a b : N, a * b = b * a) (hodd : Odd (Nat.card Φ.ker)) :
    Odd (Nat.card (commutator M)) :=
  hodd.of_dvd_nat (Subgroup.card_dvd_of_le (commutator_le_ker Φ hN))

theorem odd_card_commutator_of_comm {M : Type*} [Group M] (h : ∀ a b : M, a * b = b * a) :
    Odd (Nat.card (commutator M)) := by
  have hbot : commutator M = ⊥ := by
    rw [commutator_def, commutator_eq_bot_iff_le_centralizer]
    intro a _
    rw [mem_centralizer_iff]
    intro b _
    exact h b a
  rw [hbot, Subgroup.card_bot]
  exact odd_one

theorem odd_card_commutator_outer_of_equiv {S C : Type*} [Group S] [Group C] (e : S ≃* C)
    (h : Odd (Nat.card (commutator (Outer C)))) : Odd (Nat.card (commutator (Outer S))) := by
  let E : Outer S ≃* Outer C := OuterAutomorphisms.equivalence e
  have hmap : (commutator (Outer S)).map E.toMonoidHom = commutator (Outer C) := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective E.toMonoidHom E.surjective]
  have hc : Nat.card (commutator (Outer S)) =
      Nat.card ((commutator (Outer S)).map E.toMonoidHom) :=
    Nat.card_congr ((commutator (Outer S)).equivMapOfInjective E.toMonoidHom E.injective).toEquiv
  rw [hc, hmap]
  exact h

theorem outer_comm_of_ker_eq_inner {C N : Type*} [Group C] [Group N] (Θ : MulAut C →* N)
    (hN : ∀ a b : N, a * b = b * a) (hker : Θ.ker = inner C) (x y : Outer C) :
    x * y = y * x := by
  have hle : inner C ≤ Θ.ker := hker.ge
  have hinj : Function.Injective (QuotientGroup.lift (inner C) Θ hle) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_lift, hker, QuotientGroup.map_mk'_self]
  apply hinj
  rw [map_mul, map_mul]
  exact hN _ _

theorem odd_card_of_pow_three_eq_one {M : Type*} [Group M] [Finite M] (N : Subgroup M)
    (h : ∀ x ∈ N, x ^ 3 = 1) : Odd (Nat.card N) := by
  rw [Nat.odd_iff]
  by_contra h2
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := N) 2 (by omega)
  have h3 : x ^ 3 = 1 := Subtype.ext (by simpa using h x x.2)
  have h4 := orderOf_dvd_of_pow_eq_one h3
  rw [hx] at h4
  omega

end Commutator

section Perfect

variable {A : Type} [Group A]

theorem inner_le_comap_inner :
    innerAutomorphismSubgroup A ≤
      (inner (A ⧸ center A)).comap (PerfectAutomorphisms.centerQuotientHom A) := by
  rintro _ ⟨a, rfl⟩
  refine ⟨(a : A ⧸ center A), ?_⟩
  ext x
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (center A) x
  change (QuotientGroup.mk' (center A)) a * (QuotientGroup.mk' (center A)) x *
      ((QuotientGroup.mk' (center A)) a)⁻¹ =
    PerfectAutomorphisms.onCenterQuotient (MulAut.conj a) ((QuotientGroup.mk' (center A)) x)
  rw [PerfectAutomorphisms.onCenterQuotient_apply_mk, MulAut.conj_apply, map_mul, map_mul,
    map_inv]

@[expose] noncomputable def outerToQuot (A : Type) [Group A] :
    outerAutomorphismGroup A →* Outer (A ⧸ center A) :=
  QuotientGroup.map _ _ (PerfectAutomorphisms.centerQuotientHom A) inner_le_comap_inner

theorem outerToQuot_injective [Group.IsPerfect A] : Function.Injective (outerToQuot A) := by
  intro x y hxy
  obtain ⟨α, rfl⟩ := QuotientGroup.mk'_surjective (innerAutomorphismSubgroup A) x
  obtain ⟨β, rfl⟩ := QuotientGroup.mk'_surjective (innerAutomorphismSubgroup A) y
  have hxy' : (QuotientGroup.mk' (inner (A ⧸ center A)))
      (PerfectAutomorphisms.centerQuotientHom A α) =
      (QuotientGroup.mk' (inner (A ⧸ center A))) (PerfectAutomorphisms.centerQuotientHom A β) :=
    hxy
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hxy'
  obtain ⟨s, hs⟩ := hxy'
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (center A) s
  have hαβ : α⁻¹ * β = MulAut.conj a := by
    apply PerfectAutomorphisms.centerQuotientHom_injective A
    rw [CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_conj, hs, map_mul, map_inv]
  change (QuotientGroup.mk' (innerAutomorphismSubgroup A)) α =
    (QuotientGroup.mk' (innerAutomorphismSubgroup A)) β
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, hαβ]
  exact ⟨a, rfl⟩

theorem odd_card_commutator_outer_of_quot [Finite A] (hA : commutator A = ⊤)
    (h : Odd (Nat.card (commutator (Outer (A ⧸ center A))))) :
    Odd (Nat.card (commutator (outerAutomorphismGroup A))) := by
  have : Group.IsPerfect A := (Group.isPerfect_def).2 hA
  have hle : (commutator (outerAutomorphismGroup A)).map (outerToQuot A) ≤
      commutator (Outer (A ⧸ center A)) := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator]
    exact commutator_mono le_top le_top
  rw [← Nat.card_congr ((commutator (outerAutomorphismGroup A)).equivMapOfInjective _
    outerToQuot_injective).toEquiv.symm]
  exact h.of_dvd_nat (Subgroup.card_dvd_of_le hle)

end Perfect

section Families

variable {S : Type} [Group S]

theorem odd_card_commutator_outer_G2
    {m : ℕ} (hm : 2 ≤ m)
    (h : ChevalleyExceptionalModel S .G2 2 m) : Odd (Nat.card (commutator (Outer S))) := by
  obtain ⟨-, hmod⟩ := h
  have hmod' : UntwistedChevalleyModel S .G2 (2 ^ m) := hmod
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := LieType.Chevalley.nonempty_mulEquiv_adjointGroup .G2 hmod'
  obtain ⟨-, Θ, -, -, hker, -⟩ :=
    UnbalancedCatalog.even_G2_exact_automorphism_normal_form hm K hK
  exact odd_card_commutator_outer_of_equiv e (odd_card_commutator_of_comm
    (outer_comm_of_ker_eq_inner Θ (fun a b => ABGDGroups.ringEquiv_mul_comm a b) hker))

theorem odd_card_commutator_outer_F4
    {m : ℕ} (h : ChevalleyExceptionalModel S .F4 2 m) :
    Odd (Nat.card (commutator (Outer S))) := by
  obtain ⟨⟨hp, hm, -⟩, hmod⟩ := h
  have hmod' : UntwistedChevalleyModel S .F4 (2 ^ m) := hmod
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := LieType.Chevalley.nonempty_mulEquiv_adjointGroup .F4 hmod'
  have : CharP K LieType.Ree.ReeTag.F4.prime :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hm hK
  obtain ⟨-, -, ⟨Θ, -, -, hker⟩, -⟩ :=
    LieType.Chevalley.even_F4_exact_automorphism_normal_form hm K hK
  exact odd_card_commutator_outer_of_equiv e (odd_card_commutator_of_comm
    (outer_comm_of_ker_eq_inner Θ (fun a b => mul_comm a b) hker))

theorem odd_card_commutator_outer_E [Finite S]
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {m : ℕ}
    (hm : 1 ≤ m) (h : UntwistedChevalleyModel S τ (2 ^ m)) :
    Odd (Nat.card (commutator (Outer S))) := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := LieType.Chevalley.nonempty_mulEquiv_adjointGroup τ h
  have : Finite (adjointGroup τ K) := Finite.of_equiv S e.toEquiv
  have : Finite (MulAut (adjointGroup τ K)) := MulEquiv.finite_left
  obtain ⟨Φ, -, hker, -⟩ := LieType.Chevalley.exists_outer_hom_E (K := K) hτ
  have hcomm : ∀ a b : RingAut K × Multiplicative (ZMod (LieType.Chevalley.exactE τ)),
      a * b = b * a :=
    fun a b => Prod.ext (ABGDGroups.ringEquiv_mul_comm a.1 b.1) (mul_comm a.2 b.2)
  refine odd_card_commutator_outer_of_equiv e (odd_card_commutator_of_hom Φ hcomm ?_)
  rw [hker]
  have hKu : Odd (Nat.card Kˣ) := by
    rw [Nat.card_units, hK]
    have h2 : Even (2 ^ m) := (Nat.even_pow' (by omega)).mpr even_two
    obtain ⟨k, hk⟩ := h2
    exact ⟨k - 1, by have := Nat.one_le_two_pow (n := m); omega⟩
  have hdom : Odd (Nat.card (Fin τ.rank → Kˣ)) := by
    rw [Nat.card_pi, Finset.prod_const]
    exact hKu.pow
  exact hdom.of_dvd_nat (Subgroup.card_range_dvd _)

theorem odd_card_commutator_outer_twistedE6 [Finite S]
    {m : ℕ}
    (h : ChevalleyExceptionalModel S .twistedE6 2 m) :
    Odd (Nat.card (commutator (Outer S))) := by
  obtain ⟨⟨hp, hm, -⟩, hmod⟩ := h
  have hmod' : TwistedChevalleyModel S .E6 (2 ^ m) := hmod
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ :=
    LieType.Chevalley.exists_mulEquiv_graphFixedRootGroup_card .E6 hp hm hmod'
  have hK2 : Nat.card K = (2 ^ m) ^ 2 := hK
  have : Finite (LieType.Chevalley.twistedE6RootGroup K σ) := Finite.of_equiv S e.toEquiv
  have : Finite (MulAut (LieType.Chevalley.twistedE6RootGroup K σ)) := MulEquiv.finite_left
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, -, -, hker, -, hcube, -⟩, -⟩ :=
    LieType.Chevalley.twisted_E6_all_characteristic_exact_automorphism_normal_form hp hm K hK2 σ hσ
  have hle : inner (LieType.Chevalley.twistedE6RootGroup K σ) ≤ Θ.ker := by
    rw [hker]
    exact le_sup_left
  let Φ := QuotientGroup.lift (inner (LieType.Chevalley.twistedE6RootGroup K σ)) Θ hle
  have hcube' : ∀ x ∈ Φ.ker, x ^ 3 = 1 := by
    intro x hx
    rw [QuotientGroup.ker_lift, hker] at hx
    obtain ⟨α, hα, rfl⟩ := hx
    have h3 := hcube (QuotientGroup.mk ⟨α, hα⟩)
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
      Subgroup.coe_pow] at h3
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact h3
  exact odd_card_commutator_outer_of_equiv e (odd_card_commutator_of_hom Φ
    (fun a b => ABGDGroups.ringEquiv_mul_comm a b) (odd_card_of_pow_three_eq_one Φ.ker hcube'))

theorem odd_card_commutator_outer_trialityD4
    {m : ℕ}
    (h : ChevalleyExceptionalModel S .trialityD4 2 m) :
    Odd (Nat.card (commutator (Outer S))) := by
  obtain ⟨⟨hp, hm, -⟩, hmod⟩ := h
  have hmod' : TwistedChevalleyModel S .D4 (2 ^ m) := hmod
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ :=
    LieType.Chevalley.exists_mulEquiv_graphFixedRootGroup_card .D4 hp hm hmod'
  obtain ⟨-, -, ⟨Θ, -, -, hker, -⟩, -⟩ :=
    LieType.Chevalley.even_triality_exact_automorphism_normal_form hm K hK σ hσ
  exact odd_card_commutator_outer_of_equiv e (odd_card_commutator_of_comm
    (outer_comm_of_ker_eq_inner Θ (fun a b => ABGDGroups.ringEquiv_mul_comm a b) hker))

theorem odd_card_commutator_outer_twistedF4
    {f : ℕ}
    (h : ReeTitsModel S .twistedF4 2 f) : Odd (Nat.card (commutator (Outer S))) := by
  obtain ⟨-, -, -, hcyc, -⟩ :=
    UnbalancedCatalog.large_Ree_model_field_outer_group_and_inner_involutions S 2 f h
  exact odd_card_commutator_of_comm fun a b => (IsCyclic.isMulCommutative).is_comm.comm a b

theorem odd_card_commutator_outer_Tits
    (h : ReeTitsModel S .Tits 2 1) :
    Odd (Nat.card (commutator (Outer S))) := by
  obtain ⟨-, -, hO, -⟩ := Sporadic.Schreier.Tits.CTI_Tits_model_outer_two_part_bound S 2 1 h
  have : Fact (Nat.Prime (Nat.card (Outer S))) := ⟨by rw [hO]; exact Nat.prime_two⟩
  have : IsCyclic (Outer S) := isCyclic_of_prime_card rfl
  exact odd_card_commutator_of_comm fun a b => (IsCyclic.isMulCommutative).is_comm.comm a b

end Families

end CFSG.ComponentClassification.RankTwoExceptional
