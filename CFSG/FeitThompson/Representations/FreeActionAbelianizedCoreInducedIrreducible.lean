module

public import Mathlib.GroupTheory.FixedPointFree
public import Mathlib.GroupTheory.Solvable
public import CFSG.FeitThompson.Local.QuadraticActionsDescendSections
public import CFSG.FeitThompson.Representations.InducedIrreducibleNormOrbitFormula
public import CFSG.FeitThompson.OddOrder.DerivedPGroupInvariantAlternatingForm
import CFSG.FeitThompson.Local.FrattiniQuotientAutomorphismKernelPGroup
import CFSG.FeitThompson.Representations.CentralActionCasesComplementOrderBound
import CFSG.FeitThompson.Representations.SolvableGroupNonprincipalLinearCharacter
import CFSG.FeitThompson.Representations.FixedPointFreeActsFreelyOnLinearChars
import CFSG.FeitThompson.Representations.LinearCharactersSeparateElements
import CFSG.FeitThompson.Representations.QuotientIrreducibleCharsDegreeSum
import CFSG.FeitThompson.Representations.NormalInducedCharactersOrthogonal
import CFSG.FeitThompson.Representations.RegularRepresentationContainsIrreducibles
import CFSG.FeitThompson.Representations.AbelianGroupIrreducibleCharacters

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup
open NormalInduction (conjClassFun conjClassFun_apply)

variable {L : Type*} [Group L] {K E : Subgroup L}

theorem mulAut_abelianization_ext {G : Type*} [Group G] {f g : MulAut (Abelianization G)}
    (h : ∀ x : G, f (Abelianization.of x) = g (Abelianization.of x)) : f = g := by
  ext y
  obtain ⟨x, rfl⟩ := abelianization_of_surjective (H := G) y
  exact h x

def abelConjHom (K : Subgroup L) [K.Normal] : L →* MulAut (Abelianization ↥K) :=
  abelianizationAut (MulAut.conjNormal (H := K))

theorem abelConjHom_of [K.Normal] (u : L) (x : ↥K) :
    abelConjHom K u (Abelianization.of x)
      = Abelianization.of (MulAut.conjNormal (H := K) u x) :=
  abelianizationAut_of _ u x

theorem abelConjHom_eq_one_of_mem [K.Normal] {k : L} (hk : k ∈ K) : abelConjHom K k = 1 := by
  refine mulAut_abelianization_ext fun x => ?_
  rw [abelConjHom_of]
  have h : MulAut.conjNormal (H := K) k x = ⟨k, hk⟩ * x * ⟨k, hk⟩⁻¹ := by
    refine Subtype.ext ?_
    rw [MulAut.conjNormal_apply, Subgroup.coe_mul, Subgroup.coe_mul, InvMemClass.coe_inv]
  rw [h, map_mul, map_mul, map_inv, mul_comm (Abelianization.of (⟨k, hk⟩ : ↥K))]
  simp

def conjZpowersAut (K : Subgroup L) [K.Normal] (u : L) : ↥(zpowers u) →* MulAut ↥K :=
  (MulAut.conjNormal (H := K)).comp (zpowers u).subtype

@[simp] theorem conjZpowersAut_apply [K.Normal] (u : L) (a : ↥(zpowers u)) :
    conjZpowersAut K u a = MulAut.conjNormal (H := K) (a : L) := (rfl)

theorem isInvariantSubgroup_conjZpowersAut_commutator [K.Normal] (u : L) :
    IsInvariantSubgroup (conjZpowersAut K u) (_root_.commutator ↥K) :=
  isInvariantSubgroup_of_characteristic _ _

theorem fixedPointFree_quotientAut_conjZpowersAut [Finite L] [K.Normal] [Group.IsSolvable ↥K]
    (hcop : (Nat.card ↥K).Coprime (Nat.card ↥E)) {u : L} (hu : u ∈ E)
    (hC : K ⊓ centralizer ({u} : Set L) ≤ ⁅K, K⁆) :
    MonoidHom.FixedPointFree
      ((isInvariantSubgroup_conjZpowersAut_commutator (K := K) u).quotientAut
        ⟨u, mem_zpowers u⟩ : ↥K ⧸ _root_.commutator ↥K → ↥K ⧸ _root_.commutator ↥K) := by
  have hN := isInvariantSubgroup_conjZpowersAut_commutator (K := K) u
  have horder : orderOf u ∣ Nat.card ↥E := by
    have h : orderOf ((⟨u, hu⟩ : ↥E) : L) ∣ Nat.card ↥E := by
      rw [Subgroup.orderOf_coe]; exact orderOf_dvd_natCard _
    exact h
  have hcop' : (Nat.card ↥(zpowers u)).Coprime (Nat.card ↥K) := by
    rw [Nat.card_zpowers]
    exact (Nat.Coprime.coprime_dvd_right horder hcop).symm
  refine fixedPointFree_quotientAut_of_forall_fixed_mem hN hcop' fun y hy => ?_
  have h1 := congrArg (fun z : ↥K => (z : L)) hy
  simp only [conjZpowersAut_apply, MulAut.conjNormal_apply] at h1
  have h2 : (y : L) ∈ K ⊓ centralizer ({u} : Set L) := by
    refine ⟨y.2, mem_centralizer_singleton_iff.2 ?_⟩
    conv_lhs => rw [← h1]
    group
  obtain ⟨z, hz, hzy⟩ := (Subgroup.map_subtype_commutator K) ▸ hC h2
  exact (show z = y from Subtype.ext hzy) ▸ hz

theorem abelConjHom_eq_quotientAut [K.Normal] (u : L) :
    abelConjHom K u
      = (isInvariantSubgroup_conjZpowersAut_commutator (K := K) u).quotientAut
          ⟨u, mem_zpowers u⟩ :=
  mulAut_abelianization_ext fun x => by
    rw [abelConjHom_of]
    exact ((isInvariantSubgroup_conjZpowersAut_commutator (K := K) u).quotientAut_mk
      ⟨u, mem_zpowers u⟩ x).symm

theorem fixedPointFree_abelConjHom [Finite L] [K.Normal] [Group.IsSolvable ↥K]
    (hcop : (Nat.card ↥K).Coprime (Nat.card ↥E)) {u : L} (hu : u ∈ E)
    (hC : K ⊓ centralizer ({u} : Set L) ≤ ⁅K, K⁆) :
    MonoidHom.FixedPointFree (abelConjHom K u) := fun x hx =>
  fixedPointFree_quotientAut_conjZpowersAut (E := E) hcop hu hC x
    (abelConjHom_eq_quotientAut (K := K) u ▸ hx)

theorem inertiaGroup_comp_of [Finite L] [K.Normal] (hKE : K.IsComplement' E)
    (hFPF : ∀ u ∈ E, u ≠ 1 → MonoidHom.FixedPointFree (abelConjHom K u))
    {θ : Abelianization ↥K → ℂ} (hθ : θ ∈ Irr (Abelianization ↥K)) (hθ1 : θ ≠ 1) :
    inertiaGroup K (θ ∘ (Abelianization.of : ↥K →* Abelianization ↥K)) = K := by
  have := finite_abelianization ↥K
  set lam : ↥K → ℂ := θ ∘ (Abelianization.of : ↥K →* Abelianization ↥K) with hlam
  have hlamIrr : lam ∈ Irr ↥K :=
    irrTrivialOn_subset_Irr (mem_irrTrivialOn_comp_mk (N := _root_.commutator ↥K) hθ)
  refine le_antisymm (fun t ht => ?_) (le_inertiaGroup K (Irr_subset_classFun hlamIrr))
  obtain ⟨k, hk, e, he, rfl⟩ := Set.mem_mul.1 (hKE.mul_eq.symm ▸ Set.mem_univ t)
  by_cases he1 : e = 1
  · subst he1; simpa using hk
  have hkI : k ∈ inertiaGroup K lam := le_inertiaGroup K (Irr_subset_classFun hlamIrr) hk
  have heI : e ∈ inertiaGroup K lam := by
    have h : k⁻¹ * (k * e) ∈ inertiaGroup K lam :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ hkI) ht
    simpa using h
  rw [mem_inertiaGroup] at heI
  have hinv : ∀ y : Abelianization ↥K, θ (abelConjHom K e⁻¹ y) = θ y := by
    intro y
    obtain ⟨x, rfl⟩ := abelianization_of_surjective (H := ↥K) y
    rw [abelConjHom_of]
    have h := congrFun heI x
    rw [conjClassFun_apply] at h
    exact h
  exact absurd (eq_one_of_forall_apply_aut_eq (hFPF e⁻¹ (E.inv_mem he) (by simpa using he1))
    hθ hinv) hθ1

theorem exists_mem_Irr_indClassFun_mem_Irr_of_centralizer_le_commutator
    [Fintype L] [K.Normal] [Nontrivial ↥K]
    [Group.IsSolvable ↥K] (hKE : K.IsComplement' E)
    (hcop : (Nat.card ↥K).Coprime (Nat.card ↥E))
    (hC : ∀ e ∈ E, e ≠ 1 → K ⊓ centralizer ({e} : Set L) ≤ ⁅K, K⁆) :
    ∃ lam ∈ Irr ↥K, lam ≠ 1 ∧ lam 1 = 1 ∧ indClassFun K lam ∈ Irr L ∧
      indClassFun K lam 1 = (Nat.card ↥E : ℂ) := by
  have := nontrivial_abelianization_of_isSolvable ↥K
  have := finite_abelianization ↥K
  obtain ⟨q, hq⟩ := exists_ne (1 : Abelianization ↥K)
  obtain ⟨θ, hθ, hne⟩ := exists_mem_Irr_apply_ne_one (A := Abelianization ↥K) hq
  have hθ1 : θ ≠ 1 := fun h => hne (by rw [h]; rfl)
  set lam : ↥K → ℂ := θ ∘ (Abelianization.of : ↥K →* Abelianization ↥K) with hlam
  have hlamIrr : lam ∈ Irr ↥K :=
    irrTrivialOn_subset_Irr (mem_irrTrivialOn_comp_mk (N := _root_.commutator ↥K) hθ)
  have hlam1 : lam 1 = 1 := by
    rw [hlam, show (θ ∘ (Abelianization.of : ↥K →* Abelianization ↥K)) 1 = θ 1 from rfl,
      Irr.apply_one_eq_one hθ]
  have hlamne : lam ≠ 1 := by
    intro h
    obtain ⟨g, rfl⟩ := abelianization_of_surjective (H := ↥K) q
    refine hne ?_
    have hg := congrFun h g
    rw [hlam] at hg
    exact hg
  have hI : inertiaGroup K lam = K :=
    inertiaGroup_comp_of hKE
      (fun u hu hu1 => fixedPointFree_abelConjHom (E := E) hcop hu (hC u hu hu1)) hθ hθ1
  have hnorm : cfInner (indClassFun K lam) (indClassFun K lam) = 1 := by
    rw [cfInner_self_indClassFun K hlamIrr, hI, Subgroup.relIndex_self]
    simp
  refine ⟨lam, hlamIrr, hlamne, hlam1, ?_, ?_⟩
  · obtain ⟨W, hW⟩ := NormalInducedFamily.exists_fdRep_character_eq_of_mem_indFam K
      ((mem_indFam _).2 ⟨lam, hlamIrr, rfl⟩)
    refine mem_Irr.2 ⟨W, ?_, hW⟩
    rw [isIrreducible_iff_cfInner_self_eq_one, ← fdRepCharacter_eq W, hW]
    exact hnorm
  · rw [NormalInducedFamily.indClassFun_one_eq_index_mul, hlam1, mul_one,
      hKE.symm.index_eq_card]

end CFSG.FeitThompson
