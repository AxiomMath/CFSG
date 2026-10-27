module

public import CFSG.FeitThompson.Representations.TypeIIIVLocalCharacterConstants
public import CFSG.FeitThompson.Local.FixedFreeComplementsInvariantSections
public import CFSG.FeitThompson.Representations.PrimeInvariantCharsInnerKernel
import CFSG.FeitThompson.OddOrder.QuotientFrobeniusAction
import CFSG.FeitThompson.OddOrder.RegularPrimeActionLargeAbelianization
import CFSG.FeitThompson.OddOrder.PConfigCoprimeFrobeniusAction
import CFSG.FeitThompson.Representations.PrimeTIUniformNonprincipalConstants
import CFSG.FeitThompson.OddOrder.PTypeClausesIndependentOfComplement
import CFSG.FeitThompson.Representations.NonprincipalRowRestrictionsDetectCores
public import CFSG.FeitThompson.Representations.MinimalAbelianCoreBridgeCharacter
import CFSG.FeitThompson.Local.NormalComplementDerivedIntersection
import CFSG.FeitThompson.Local.PComplementControlSylowNormalizer
import CFSG.FeitThompson.Local.ControlledPlaneCentralizersPrimeCore
import CFSG.FeitThompson.Representations.SolvableFrobeniusKernelInducedIndexDegree
import CFSG.FeitThompson.Local.PComplSubgroupNormalizedBySylow
import CFSG.FeitThompson.Local.PrimeActionChiefFactorsBelowFitting
import CFSG.FeitThompson.Local.CriticalRegularComplementFixedPoints
public import Mathlib.GroupTheory.FixedPointFree
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup CFSG.FeitThompson.Prep06

variable {G : Type*} [Group G] {M U W₁ W₂ : Subgroup G}

theorem le_normalizer_hallCoreIn (M : Subgroup G) :
    M ≤ normalizer ((hallCoreIn M : Subgroup G) : Set G) := by
  rw [hallCoreIn_eq]
  exact le_normalizer_map_subtype_hallCore M

theorem le_normalizer_centralizer_hallCoreIn (M : Subgroup G) :
    M ≤ normalizer ((centralizer ((hallCoreIn M : Subgroup G) : Set G) : Subgroup G) : Set G) :=
  (le_normalizer_hallCoreIn M).trans (normalizer_le_normalizer_centralizer _)

theorem derivedOf_eq_subgroupOf_commutator (M : Subgroup G) :
    derivedOf M = (⁅M, M⁆ : Subgroup G).subgroupOf M :=
  derivedOf_eq M ▸ commutator_eq_subgroupOf_commutator M

instance normal_derivedOf (M : Subgroup G) : (derivedOf M).Normal :=
  derivedOf_eq_subgroupOf_commutator M ▸ normal_subgroupOf_commutator_self M

theorem coe_coe_mem_commutator (M : Subgroup G) (x : ↥(derivedOf M)) :
    ((x : ↥M) : G) ∈ (⁅M, M⁆ : Subgroup G) :=
  Subgroup.mem_subgroupOf.1 (show (x : ↥M) ∈ (⁅M, M⁆ : Subgroup G).subgroupOf M by
    rw [← derivedOf_eq_subgroupOf_commutator]; exact x.2)

theorem coe_coe_conjNormal_derivedOf (M : Subgroup G) (w : ↥M) (x : ↥(derivedOf M)) :
    (((MulAut.conjNormal (H := derivedOf M) w x : ↥(derivedOf M)) : ↥M) : G)
      = (w : G) * ((x : ↥M) : G) * (w : G)⁻¹ := by
  rw [MulAut.conjNormal_apply (H := derivedOf M) w x]
  push_cast
  rfl

theorem mapsTo_conjNormal_subgroupOf_hallCoreIn (M : Subgroup G) (w : ↥M) :
    ∀ x ∈ ((hallCoreIn M).subgroupOf M).subgroupOf (derivedOf M),
      MulAut.conjNormal (H := derivedOf M) w x ∈
        ((hallCoreIn M).subgroupOf M).subgroupOf (derivedOf M) := by
  intro x hx
  simp only [Subgroup.mem_subgroupOf] at hx ⊢
  rw [coe_coe_conjNormal_derivedOf]
  exact (Subgroup.mem_normalizer_iff.1 (le_normalizer_hallCoreIn M w.2) _).1 hx

variable [Finite G]

theorem natCard_derivedOf (M : Subgroup G) :
    Nat.card ↥(derivedOf M) = Nat.card ↥(⁅M, M⁆ : Subgroup G) := by
  rw [derivedOf_eq_subgroupOf_commutator]
  exact Nat.card_eq_of_bijective _
    (Subgroup.subgroupOfEquivOfLe (Subgroup.commutator_le_self M)).bijective

theorem IsWitnessedPConfiguration.fixedPointFree_conjOnNormalized_E
    (hc : IsWitnessedPConfiguration M U W₁ W₂) {b : ↥W₁} (hb1 : b ≠ 1) :
    MonoidHom.FixedPointFree (conjOnNormalized U hc.le_normalizer_E b) := by
  intro u hu
  have hcoe : (b : G) * (u : G) * (b : G)⁻¹ = (u : G) := by
    have hx := congrArg (Subtype.val) hu
    rwa [conjOnNormalized_apply_coe] at hx
  have hcomm : (u : G) ∈ centralizer ({(b : G)} : Set G) := by
    refine mem_centralizer_singleton_iff.2 ?_
    have h2 := congrArg (fun z : G => z * (b : G)) hcoe
    simp only [inv_mul_cancel_right] at h2
    exact h2.symm
  have hmem : (u : G) ∈ (⁅M, M⁆ : Subgroup G) ⊓ centralizer ({(b : G)} : Set G) :=
    mem_inf.2 ⟨hc.le_commutator_E u.2, hcomm⟩
  rw [hc.inf_centralizer_eq_W₂ (b : G) b.2 (fun hcon => hb1 (Subtype.ext hcon))] at hmem
  exact Subtype.ext (Subgroup.disjoint_def.1 hc.disjoint_hallCore_E (hc.le_hallCore_W₂ hmem) u.2)

theorem IsWitnessedPConfiguration.le_normalizer_coreC
    (hc : IsWitnessedPConfiguration M U W₁ W₂) :
    W₁ ≤ normalizer (((U ⊓ centralizer ((hallCoreIn M : Subgroup G) : Set G) :
      Subgroup G)) : Set G) := fun _ hg =>
  Subgroup.inf_normalizer_le_normalizer_inf
    (Subgroup.mem_inf.2 ⟨hc.le_normalizer_E hg,
      le_normalizer_centralizer_hallCoreIn M (hc.le_M_W₁ hg)⟩)

theorem IsWitnessedPConfiguration.natCard_W₁_dvd_relIndex_inf_centralizer_hallCoreIn_sub_one
    (hc : IsWitnessedPConfiguration M U W₁ W₂) (hqprime : (Nat.card ↥W₁).Prime)
    (hsolvM : Group.IsSolvable ↥M) :
    Nat.card ↥W₁ ∣ (U ⊓ centralizer ((hallCoreIn M : Subgroup G) : Set G)).relIndex U - 1 := by
  set C : Subgroup ↥U :=
    (U ⊓ centralizer ((hallCoreIn M : Subgroup G) : Set G)).subgroupOf U with hCdef
  have hUsolv : Group.IsSolvable ↥U := by
    have : Group.IsSolvable ↥(U.subgroupOf M) := inferInstance
    exact Group.isSolvable_of_surjective
      (f := (Subgroup.subgroupOfEquivOfLe hc.le_M_E).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hc.le_M_E).surjective
  have hCnormal : C.Normal := by
    rw [hCdef]
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).2 fun g hg => ?_
    exact Subgroup.inf_normalizer_le_normalizer_inf
      (Subgroup.mem_inf.2 ⟨Subgroup.le_normalizer hg,
        le_normalizer_centralizer_hallCoreIn M (hc.le_M_E hg)⟩)
  have hinv : IsInvariantSubgroup (conjOnNormalized U hc.le_normalizer_E) C :=
    isInvariantSubgroup_subgroupOf hc.le_normalizer_E hc.le_normalizer_coreC
  obtain ⟨b, hbW, hb1, hbgen⟩ := exists_zpowers_eq_of_prime_natCard (B := W₁) hqprime
  have hbtop : Subgroup.zpowers (⟨b, hbW⟩ : ↥W₁) = ⊤ := by
    ext x
    simp only [Subgroup.mem_top, iff_true, Subgroup.mem_zpowers_iff]
    have hx : (x : G) ∈ Subgroup.zpowers b := by rw [hbgen]; exact x.2
    obtain ⟨k, hk⟩ := hx
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  have hfree : MonoidHom.FixedPointFree
      (conjOnNormalized U hc.le_normalizer_E (⟨b, hbW⟩ : ↥W₁)) :=
    hc.fixedPointFree_conjOnNormalized_E
      (fun hcon => hb1 (by simpa using congrArg Subtype.val hcon))
  have hqfree := fixedPointFree_quotientAut (q := Nat.card ↥W₁) hqprime rfl hbtop hfree hinv
  have hdvd := prime_dvd_card_sub_one_of_fixedPointFree hqprime (A := ↥W₁)
    (ρ := hinv.quotientAut) (a := (⟨b, hbW⟩ : ↥W₁)) rfl hqfree
  rwa [← Subgroup.index_eq_card, ← Subgroup.relIndex] at hdvd

theorem subgroupOf_hallCoreIn_self (M : Subgroup G) :
    (hallCoreIn M).subgroupOf M = hallCore ↥M := by
  rw [hallCoreIn_eq, Subgroup.subgroupOf,
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective]

theorem coreCentralizer_hallCore_eq_subgroupOf (M U : Subgroup G) :
    coreCentralizer (hallCore ↥M) (U.subgroupOf M)
      = (U ⊓ centralizer ((hallCoreIn M : Subgroup G) : Set G)).subgroupOf M := by
  ext x
  rw [mem_coreCentralizer]
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff,
    SetLike.mem_coe]
  refine and_congr Iff.rfl ⟨fun h y hy => ?_, fun h n hn => ?_⟩
  · rw [hallCoreIn_eq] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    have h2 := congrArg (fun t : ↥M => (t : G)) (h z hz)
    push_cast at h2
    exact h2
  · refine Subtype.ext ?_
    have h1 := h ((n : ↥M) : G) (by rw [hallCoreIn_eq]; exact ⟨n, hn, rfl⟩)
    push_cast
    exact h1

theorem isMulCommutative_hallCore_of_commutator_eq_bot (M : Subgroup G)
    (hHcomm : ⁅(hallCoreIn M : Subgroup G), (hallCoreIn M : Subgroup G)⁆ = ⊥) :
    IsMulCommutative ↥(hallCore ↥M : Subgroup ↥M) := by
  have hab : IsMulCommutative ↥(hallCoreIn M : Subgroup G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.1
      (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hHcomm)
  rw [← subgroupOf_hallCoreIn_self]
  exact isMulCommutative_subgroupOf_of_isMulCommutative hab

theorem relIndex_coreCentralizer_hallCore (hUM : U ≤ M) :
    (coreCentralizer (hallCore ↥M) (U.subgroupOf M)).relIndex (U.subgroupOf M)
      = (U ⊓ centralizer ((hallCoreIn M : Subgroup G) : Set G)).relIndex U := by
  rw [coreCentralizer_hallCore_eq_subgroupOf, Subgroup.relIndex_subgroupOf hUM]

theorem apply_one_eq_relIndex_coreCentralizer_of_sup_eq {L : Type*} [Group L] [Finite L]
    {N V Q K : Subgroup L} [N.Normal] [IsMulCommutative ↥N] [IsMulCommutative ↥V]
    (hK : N ⊔ V = K) (hN : N ≠ ⊥) (hNV : N ⊓ V = ⊥) (hL : K ⊔ Q = ⊤) (hKQ : K ⊓ Q = ⊥)
    (hQV : Q ≤ normalizer (V : Set L)) {q : ℕ} (hq : q.Prime)
    (hQcard : Nat.card ↥Q = q) (hqV : q.Coprime (Nat.card ↥V))
    (hmin : ∀ A ≤ N, V ≤ normalizer (A : Set L) → Q ≤ normalizer (A : Set L) → A = ⊥ ∨ A = N)
    {θ : ↥K → ℂ} (hθ : θ ∈ Irr ↥K) (hdet : ∃ x : ↥K, (x : L) ∈ N ∧ θ x ≠ θ 1)
    (hinv : ∀ t ∈ Q, ∀ x y : ↥K, (y : L) = t⁻¹ * (x : L) * t → θ y = θ x) :
    θ 1 = ((coreCentralizer N V).relIndex V : ℂ) := by
  subst hK
  have : Fintype ↥(N ⊔ V) := Fintype.ofFinite _
  exact apply_one_eq_relIndex_coreCentralizer hN hNV hL hKQ hQV hq hQcard hqV hmin hθ hdet hinv

section Quotient

variable {L : Type*} [Group L]

theorem coreCentralizer_eq_inf_centralizer (N V : Subgroup L) :
    coreCentralizer N V = V ⊓ centralizer (N : Set L) := by
  ext u
  rw [mem_coreCentralizer, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  exact and_congr Iff.rfl ⟨fun h n hn => h n hn, fun h n hn => h n hn⟩

theorem normal_coreCentralizer {N V Q K : Subgroup L} [N.Normal] (hK : N ⊔ V = K)
    (hL : K ⊔ Q = ⊤) (hQV : Q ≤ normalizer (V : Set L)) :
    (coreCentralizer N V).Normal := by
  rw [coreCentralizer_eq_inf_centralizer, ← Subgroup.normalizer_eq_top_iff, eq_top_iff,
    ← hL, ← hK]
  have hcen : ∀ g : L, g ∈ normalizer ((centralizer (N : Set L) : Subgroup L) : Set L) := by
    intro g
    have h : (centralizer (N : Set L)).Normal := inferInstance
    rw [← Subgroup.normalizer_eq_top_iff] at h
    rw [h]
    exact Subgroup.mem_top g
  refine sup_le (sup_le (fun g hg => ?_) (fun g hg => ?_)) (fun g hg => ?_)
  · refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun c hc => ?_)
    exact (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hc).2 g hg).symm
  · exact Subgroup.inf_normalizer_le_normalizer_inf
      (Subgroup.mem_inf.2 ⟨Subgroup.le_normalizer hg, hcen g⟩)
  · exact Subgroup.inf_normalizer_le_normalizer_inf (Subgroup.mem_inf.2 ⟨hQV hg, hcen g⟩)

theorem normal_of_sup_eq_of_sup_eq_top {N V Q K : Subgroup L} [N.Normal] (hK : N ⊔ V = K)
    (hL : K ⊔ Q = ⊤) (hQV : Q ≤ normalizer (V : Set L)) : K.Normal := by
  rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hL]
  refine sup_le Subgroup.le_normalizer fun t ht => ?_
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, ← hK, Subgroup.map_sup,
    Subgroup.mem_normalizer_iff_map_conj_eq.1 (hQV ht),
    Subgroup.mem_normalizer_iff_map_conj_eq.1
      (show t ∈ normalizer (N : Set L) from Subgroup.le_normalizer_of_normal ht)]

theorem isMulCommutative_map_of_commutator_le_ker {L' : Type*} [Group L'] {X : Subgroup L}
    (f : L →* L') (h : ⁅X, X⁆ ≤ f.ker) : IsMulCommutative ↥(X.map f) := by
  refine ⟨⟨fun x y => ?_⟩⟩
  obtain ⟨a, ha, hax⟩ := x.2
  obtain ⟨b, hb, hby⟩ := y.2
  have hc : f (a * b * a⁻¹ * b⁻¹) = 1 := by
    have h1 := h (Subgroup.commutator_mem_commutator ha hb)
    rwa [commutatorElement_def] at h1
  simp only [map_mul, map_inv] at hc
  refine Subtype.ext ?_
  push_cast
  rw [← hax, ← hby]
  have hb2 : f a * f b * (f a)⁻¹ = f b := mul_inv_eq_one.mp hc
  calc f a * f b = f a * f b * (f a)⁻¹ * f a := by group
    _ = f b * f a := by rw [hb2]

theorem coreCentralizer_map_mk'_eq_bot {N V : Subgroup L} [N.Normal]
    [(coreCentralizer N V).Normal] (hNV : N ⊓ V = ⊥) :
    coreCentralizer (N.map (QuotientGroup.mk' (coreCentralizer N V)))
      (V.map (QuotientGroup.mk' (coreCentralizer N V))) = ⊥ := by
  set C := coreCentralizer N V with hCdef
  set f := QuotientGroup.mk' C with hf
  rw [Subgroup.eq_bot_iff_forall]
  intro z hz
  rw [mem_coreCentralizer] at hz
  obtain ⟨hzV, hzc⟩ := hz
  obtain ⟨v, hv, rfl⟩ := hzV
  have hvC : v ∈ C := by
    rw [hCdef, mem_coreCentralizer]
    refine ⟨hv, fun n hn => ?_⟩
    have h1 := hzc (f n) (Subgroup.mem_map_of_mem f hn)
    have h2 : (n * v)⁻¹ * (v * n) ∈ C := by
      rw [← map_mul, ← map_mul] at h1
      exact (QuotientGroup.eq (s := C)).1 h1
    have hcomm : (n * v)⁻¹ * (v * n) = v⁻¹ * n⁻¹ * v * n := by group
    have h3 : (n * v)⁻¹ * (v * n) ∈ N := by
      rw [hcomm]
      exact mul_mem (by simpa using ‹N.Normal›.conj_mem n⁻¹ (N.inv_mem hn) v⁻¹) hn
    have h5 : (n * v)⁻¹ * (v * n) ∈ N ⊓ V :=
      Subgroup.mem_inf.2 ⟨h3, coreCentralizer_le_left N V h2⟩
    rw [hNV, Subgroup.mem_bot, inv_mul_eq_one] at h5
    exact h5
  exact (QuotientGroup.eq_one_iff v).2 hvC

theorem inf_map_mk'_eq_bot_of_le {N V C : Subgroup L} [C.Normal] (hCV : C ≤ V)
    (hNV : N ⊓ V = ⊥) :
    N.map (QuotientGroup.mk' C) ⊓ V.map (QuotientGroup.mk' C) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  rintro z ⟨hz1, hz2⟩
  obtain ⟨n, hn, hnz⟩ := hz1
  obtain ⟨v, hv, hvz⟩ := hz2
  have hnv : n⁻¹ * v ∈ C := (QuotientGroup.eq (s := C)).1 (hnz.trans hvz.symm)
  have hnV : n ∈ V := by
    have h1 : n = v * (n⁻¹ * v)⁻¹ := by group
    rw [h1]
    exact mul_mem hv (V.inv_mem (hCV hnv))
  have hn1 : n = 1 := by
    have h2 := Subgroup.mem_inf.2 ⟨hn, hnV⟩
    rw [hNV, Subgroup.mem_bot] at h2
    exact h2
  rw [← hnz, hn1, map_one]

theorem minimal_map_mk'_of_minimal {N V Q C : Subgroup L} [N.Normal] [C.Normal]
    (hQN : Q ≤ normalizer (N : Set L)) (hVN : V ≤ normalizer (N : Set L))
    (hmin : ∀ A ≤ N, V ≤ normalizer (A : Set L) → Q ≤ normalizer (A : Set L) →
      A = ⊥ ∨ A = N) :
    ∀ Ā ≤ N.map (QuotientGroup.mk' C),
      V.map (QuotientGroup.mk' C) ≤ normalizer ((Ā : Subgroup (L ⧸ C)) : Set (L ⧸ C)) →
      Q.map (QuotientGroup.mk' C) ≤ normalizer ((Ā : Subgroup (L ⧸ C)) : Set (L ⧸ C)) →
      Ā = ⊥ ∨ Ā = N.map (QuotientGroup.mk' C) := by
  intro Ā hĀ hV hQ
  set f := QuotientGroup.mk' C with hf
  set A : Subgroup L := N ⊓ Ā.comap f with hA
  have hAN : A ≤ N := inf_le_left
  have hnorm : ∀ X : Subgroup L, X ≤ normalizer (N : Set L) →
      X.map f ≤ normalizer ((Ā : Subgroup (L ⧸ C)) : Set (L ⧸ C)) →
      X ≤ normalizer (A : Set L) := by
    intro X hXN hXĀ
    refine Subgroup.le_normalizer_iff.2 fun g hg a ha => ?_
    obtain ⟨haN, haĀ⟩ := Subgroup.mem_inf.1 ha
    refine Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.1 (hXN hg) a).1 haN, ?_⟩
    have hfg : f g ∈ normalizer ((Ā : Subgroup (L ⧸ C)) : Set (L ⧸ C)) :=
      hXĀ (Subgroup.mem_map_of_mem f hg)
    have h3 : f (g * a * g⁻¹) = f g * f a * (f g)⁻¹ := by simp
    rw [Subgroup.mem_comap, h3]
    exact (Subgroup.mem_normalizer_iff.1 hfg (f a)).1 haĀ
  rcases hmin A hAN (hnorm V hVN hV) (hnorm Q hQN hQ) with h | h
  · left
    rw [Subgroup.eq_bot_iff_forall]
    intro z hz
    obtain ⟨n, hn, hnz⟩ := hĀ hz
    have hnA : n ∈ A := Subgroup.mem_inf.2 ⟨hn, by rw [Subgroup.mem_comap, hnz]; exact hz⟩
    rw [h, Subgroup.mem_bot] at hnA
    rw [← hnz, hnA, map_one]
  · right
    refine le_antisymm hĀ fun z hz => ?_
    obtain ⟨n, hn, hnz⟩ := hz
    have hnA : n ∈ A := by rw [h]; exact hn
    rw [← hnz]
    exact Subgroup.mem_comap.1 (Subgroup.mem_inf.1 hnA).2

def quotImageRestrict (C K : Subgroup L) [C.Normal] : ↥K →* ↥(K.map (QuotientGroup.mk' C)) :=
  MonoidHom.codRestrict ((QuotientGroup.mk' C).comp K.subtype) _
    fun x => Subgroup.mem_map_of_mem _ x.2

@[simp] theorem coe_quotImageRestrict_apply (C K : Subgroup L) [C.Normal] (x : ↥K) :
    ((quotImageRestrict C K x : ↥(K.map (QuotientGroup.mk' C))) : L ⧸ C)
      = QuotientGroup.mk (x : L) := (rfl)

theorem quotImageRestrict_surjective (C K : Subgroup L) [C.Normal] :
    Function.Surjective (quotImageRestrict C K) := by
  rintro ⟨z, hz⟩
  obtain ⟨a, ha, haz⟩ := hz
  exact ⟨⟨a, ha⟩, Subtype.ext (by rw [coe_quotImageRestrict_apply]; exact haz)⟩

theorem mem_ker_quotImageRestrict_iff (C K : Subgroup L) [C.Normal] {x : ↥K} :
    x ∈ (quotImageRestrict C K).ker ↔ (x : L) ∈ C := by
  rw [MonoidHom.mem_ker, ← Subtype.coe_inj, coe_quotImageRestrict_apply]
  exact QuotientGroup.eq_one_iff (x : L)

theorem exists_mem_Irr_comp_eq_of_surjective {A B : Type*} [Group A] [Group B] [Finite A]
    {f : A →* B} (hf : Function.Surjective f) {θ : A → ℂ} (hθ : θ ∈ Irr A)
    (hker : ∀ x ∈ f.ker, θ x = θ 1) :
    ∃ χ ∈ Irr B, χ ∘ f = θ := by
  obtain ⟨ψ, hψ, hψθ⟩ := exists_comp_mk_eq_of_mem_irrTrivialOn (N := f.ker)
    (mem_irrTrivialOn.2 ⟨hθ, hker⟩)
  set e := QuotientGroup.quotientKerEquivOfSurjective f hf with he
  have hev : ∀ a : A, e (QuotientGroup.mk a) = f a := fun _ => rfl
  refine ⟨ψ ∘ e.symm, ?_, ?_⟩
  · refine mem_Irr_of_comp_mulEquiv e ?_
    have h1 : (ψ ∘ (e.symm : B → A ⧸ f.ker)) ∘ (e : (A ⧸ f.ker) → B) = ψ := by
      funext z; simp
    rw [h1]; exact hψ
  · funext a
    have h2 : e.symm (f a) = QuotientGroup.mk a := by rw [← hev a]; simp
    simp only [Function.comp_apply, h2]
    exact congrFun hψθ a

theorem apply_one_eq_relIndex_coreCentralizer_of_commutator_le [Finite L]
    {N V Q K : Subgroup L} [N.Normal] [IsMulCommutative ↥N]
    (hK : N ⊔ V = K) (hN : N ≠ ⊥) (hNV : N ⊓ V = ⊥) (hL : K ⊔ Q = ⊤) (hKQ : K ⊓ Q = ⊥)
    (hQV : Q ≤ normalizer (V : Set L)) {q : ℕ} (hq : q.Prime)
    (hQcard : Nat.card ↥Q = q) (hqV : q.Coprime (Nat.card ↥V))
    (hmin : ∀ A ≤ N, V ≤ normalizer (A : Set L) → Q ≤ normalizer (A : Set L) → A = ⊥ ∨ A = N)
    (hVder : ⁅V, V⁆ ≤ coreCentralizer N V)
    {θ : ↥K → ℂ} (hθ : θ ∈ Irr ↥K) (hdet : ∃ x : ↥K, (x : L) ∈ N ∧ θ x ≠ θ 1)
    (hCker : ∀ x : ↥K, (x : L) ∈ coreCentralizer N V → θ x = θ 1)
    (hinv : ∀ t ∈ Q, ∀ x y : ↥K, (y : L) = t⁻¹ * (x : L) * t → θ y = θ x) :
    θ 1 = (((coreCentralizer N V).relIndex V : ℕ) : ℂ) := by
  classical
  set C := coreCentralizer N V with hCdef
  have hCV : C ≤ V := coreCentralizer_le_left N V
  have hCnormal : C.Normal := normal_coreCentralizer hK hL hQV
  have hKnormal : K.Normal := normal_of_sup_eq_of_sup_eq_top hK hL hQV
  have hCK : C ≤ K := hK ▸ hCV.trans le_sup_right
  have hfsurj : Function.Surjective (QuotientGroup.mk' C) := QuotientGroup.mk'_surjective C
  have hNbar : (N.map (QuotientGroup.mk' C)).Normal := ‹N.Normal›.map _ hfsurj
  have hNab : IsMulCommutative ↥(N.map (QuotientGroup.mk' C)) := inferInstance
  have hVab : IsMulCommutative ↥(V.map (QuotientGroup.mk' C)) := by
    refine isMulCommutative_map_of_commutator_le_ker _ ?_
    rw [QuotientGroup.ker_mk']
    exact hVder
  have hKbar : N.map (QuotientGroup.mk' C) ⊔ V.map (QuotientGroup.mk' C)
      = K.map (QuotientGroup.mk' C) := by rw [← Subgroup.map_sup, hK]
  have hNbne : N.map (QuotientGroup.mk' C) ≠ ⊥ := by
    intro h
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
    refine hN (le_bot_iff.1 ?_)
    rw [← hNV]
    exact le_inf le_rfl (h.trans hCV)
  have hNVbar : N.map (QuotientGroup.mk' C) ⊓ V.map (QuotientGroup.mk' C) = ⊥ :=
    inf_map_mk'_eq_bot_of_le hCV hNV
  have hLbar : K.map (QuotientGroup.mk' C) ⊔ Q.map (QuotientGroup.mk' C) = ⊤ := by
    rw [← Subgroup.map_sup, hL, Subgroup.map_top_of_surjective _ hfsurj]
  have hKQbar : K.map (QuotientGroup.mk' C) ⊓ Q.map (QuotientGroup.mk' C) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    rintro z ⟨hz1, hz2⟩
    obtain ⟨k, hk, hkz⟩ := hz1
    obtain ⟨t, ht, htz⟩ := hz2
    have hkt : k⁻¹ * t ∈ C := (QuotientGroup.eq (s := C)).1 (hkz.trans htz.symm)
    have htK : t ∈ K := by
      have h1 : t = k * (k⁻¹ * t) := by group
      rw [h1]; exact mul_mem hk (hCK hkt)
    have ht1 : t = 1 := by
      have h2 := Subgroup.mem_inf.2 ⟨htK, ht⟩
      rw [hKQ, Subgroup.mem_bot] at h2
      exact h2
    rw [← htz, ht1, map_one]
  have hQVbar : Q.map (QuotientGroup.mk' C)
      ≤ normalizer ((V.map (QuotientGroup.mk' C) : Subgroup (L ⧸ C)) : Set (L ⧸ C)) :=
    map_le_normalizer_map_of_le_normalizer _ hQV
  have hQC : Q ⊓ C = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨hxQ, hxC⟩ := Subgroup.mem_inf.1 hx
    have h3 := Subgroup.mem_inf.2 (⟨hCK hxC, hxQ⟩ : (x ∈ K) ∧ (x ∈ Q))
    rw [hKQ, Subgroup.mem_bot] at h3
    exact h3
  have hQcardbar : Nat.card ↥(Q.map (QuotientGroup.mk' C)) = q := by
    rw [natCard_map_mk'_eq hQC, hQcard]
  have hqVbar : q.Coprime (Nat.card ↥(V.map (QuotientGroup.mk' C))) :=
    hqV.coprime_dvd_right (Subgroup.card_map_dvd V _)
  have hnormN : ∀ X : Subgroup L, X ≤ normalizer (N : Set L) := fun _ => by
    rw [Subgroup.normalizer_eq_top_iff.2 ‹N.Normal›]; exact le_top
  have hminbar := minimal_map_mk'_of_minimal (C := C) (hnormN Q) (hnormN V) hmin
  obtain ⟨χ, hχ, hχθ⟩ := exists_mem_Irr_comp_eq_of_surjective (quotImageRestrict_surjective C K) hθ
    fun x hx => hCker x ((mem_ker_quotImageRestrict_iff C K).1 hx)
  have hχval : ∀ x : ↥K, χ (quotImageRestrict C K x) = θ x := fun x => congrFun hχθ x
  have hχ1 : χ 1 = θ 1 := by
    have h := hχval 1
    rwa [map_one] at h
  have hθcong : ∀ a b : ↥K, ((a : L) : L ⧸ C) = ((b : L) : L ⧸ C) → θ a = θ b := by
    intro a b hab
    rw [← hχval a, ← hχval b]
    congr 1
    exact Subtype.ext (by rw [coe_quotImageRestrict_apply, coe_quotImageRestrict_apply]; exact hab)
  have hdetbar : ∃ x : ↥(K.map (QuotientGroup.mk' C)),
      (x : L ⧸ C) ∈ N.map (QuotientGroup.mk' C) ∧ χ x ≠ χ 1 := by
    obtain ⟨x, hxN, hxne⟩ := hdet
    refine ⟨quotImageRestrict C K x, ?_, ?_⟩
    · rw [coe_quotImageRestrict_apply]
      exact Subgroup.mem_map_of_mem _ hxN
    · rw [hχval x, hχ1]; exact hxne
  have hinvbar : ∀ t ∈ Q.map (QuotientGroup.mk' C),
      ∀ x y : ↥(K.map (QuotientGroup.mk' C)),
      (y : L ⧸ C) = t⁻¹ * (x : L ⧸ C) * t → χ y = χ x := by
    intro t ht x y hxy
    obtain ⟨s, hs, hst⟩ := ht
    obtain ⟨a, ha⟩ := quotImageRestrict_surjective C K x
    obtain ⟨b, hb⟩ := quotImageRestrict_surjective C K y
    have hcK : s⁻¹ * (a : L) * s ∈ K := by
      have h := hKnormal.conj_mem (a : L) a.2 s⁻¹
      simpa [mul_assoc] using h
    have hθc : θ ⟨s⁻¹ * (a : L) * s, hcK⟩ = θ a := hinv s hs a _ rfl
    have hxv : ((a : L) : L ⧸ C) = (x : L ⧸ C) := by rw [← ha, coe_quotImageRestrict_apply]
    have hyv : ((b : L) : L ⧸ C) = (y : L ⧸ C) := by rw [← hb, coe_quotImageRestrict_apply]
    have hmk : ((b : L) : L ⧸ C) = ((⟨s⁻¹ * (a : L) * s, hcK⟩ : ↥K) : L ⧸ C) := by
      rw [hyv, hxy, ← hst, ← hxv]
      push_cast
      simp
    rw [← ha, ← hb, hχval, hχval, hθcong b _ hmk, hθc]
  have hdeg := apply_one_eq_relIndex_coreCentralizer_of_sup_eq
    (N := N.map (QuotientGroup.mk' C)) (V := V.map (QuotientGroup.mk' C))
    (Q := Q.map (QuotientGroup.mk' C)) (K := K.map (QuotientGroup.mk' C))
    hKbar hNbne hNVbar hLbar hKQbar hQVbar hq hQcardbar hqVbar hminbar hχ hdetbar hinvbar
  rw [coreCentralizer_map_mk'_eq_bot hNV, Subgroup.relIndex_bot_left] at hdeg
  rw [← hχ1, hdeg, natCard_map_mk'_eq_relIndex]

end Quotient

theorem commutator_subgroupOf_le_subgroupOf_commutator (M U : Subgroup G) :
    ⁅U.subgroupOf M, U.subgroupOf M⁆ ≤ (⁅U, U⁆ : Subgroup G).subgroupOf M := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  rw [Subgroup.mem_subgroupOf]
  have h : ((a * b * a⁻¹ * b⁻¹ : ↥M) : G) = (a : G) * (b : G) * (a : G)⁻¹ * (b : G)⁻¹ := by
    push_cast; rfl
  rw [commutatorElement_def, h, ← commutatorElement_def]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_subgroupOf.1 ha)
    (Subgroup.mem_subgroupOf.1 hb)

namespace IsWitnessedPConfiguration

variable (hc : IsWitnessedPConfiguration M U W₁ W₂)
include hc

theorem hallCoreIn_le_commutator : hallCoreIn M ≤ (⁅M, M⁆ : Subgroup G) := by
  rw [hallCoreIn_eq]; exact hc.hallCore_le_commutator

theorem subgroupOf_hallCoreIn_le_derivedOf : (hallCoreIn M).subgroupOf M ≤ derivedOf M := by
  rw [derivedOf_eq_subgroupOf_commutator]
  exact Subgroup.comap_mono hc.hallCoreIn_le_commutator

theorem subgroupOf_E_le_derivedOf : U.subgroupOf M ≤ derivedOf M := by
  rw [derivedOf_eq_subgroupOf_commutator]
  exact Subgroup.comap_mono hc.le_commutator_E

theorem normal_subgroupOf_hallCoreIn_derivedOf :
    (((hallCoreIn M).subgroupOf M).subgroupOf (derivedOf M)).Normal := by
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer
    hc.subgroupOf_hallCoreIn_le_derivedOf).2 fun g _ =>
      Subgroup.mem_normalizer_iff.2 fun y => ?_
  simp only [Subgroup.mem_subgroupOf]
  have h := Subgroup.mem_normalizer_iff.1 (le_normalizer_hallCoreIn M g.2) (y : G)
  exact ⟨fun hy => by simpa using h.1 hy, fun hy => h.2 (by simpa using hy)⟩

theorem isComplement'_subgroupOf_hallCoreIn_E_derivedOf :
    (((hallCoreIn M).subgroupOf M).subgroupOf (derivedOf M)).IsComplement'
      ((U.subgroupOf M).subgroupOf (derivedOf M)) := by
  have := hc.normal_subgroupOf_hallCoreIn_derivedOf
  refine (isComplement'_of_sup_eq_top_of_inf_eq_bot ?_ ?_).symm
  · rw [← Subgroup.subgroupOf_sup hc.subgroupOf_hallCoreIn_le_derivedOf
      hc.subgroupOf_E_le_derivedOf, ← Subgroup.subgroupOf_sup (hallCoreIn_le M) hc.le_M_E,
      hallCoreIn_eq, hc.sup_hallCore_E, ← derivedOf_eq_subgroupOf_commutator,
      Subgroup.subgroupOf_self]
  · rw [show ((hallCoreIn M).subgroupOf M).subgroupOf (derivedOf M) ⊓
        (U.subgroupOf M).subgroupOf (derivedOf M)
        = (((hallCoreIn M).subgroupOf M ⊓ U.subgroupOf M).subgroupOf (derivedOf M)) from
      (Subgroup.comap_inf _ _ _).symm,
      show (hallCoreIn M).subgroupOf M ⊓ U.subgroupOf M
        = ((hallCoreIn M ⊓ U).subgroupOf M) from (Subgroup.comap_inf _ _ _).symm,
      hallCoreIn_eq, disjoint_iff.1 hc.disjoint_hallCore_E,
      Subgroup.bot_subgroupOf, Subgroup.bot_subgroupOf]

theorem mapsTo_conjNormal_subgroupOf_E {w : ↥M} (hw : (w : G) ∈ W₁) :
    ∀ x ∈ (U.subgroupOf M).subgroupOf (derivedOf M),
      MulAut.conjNormal (H := derivedOf M) w x ∈ (U.subgroupOf M).subgroupOf (derivedOf M) := by
  intro x hx
  simp only [Subgroup.mem_subgroupOf] at hx ⊢
  rw [coe_coe_conjNormal_derivedOf]
  exact (Subgroup.mem_normalizer_iff.1 (hc.le_normalizer_E hw) _).1 hx

theorem eq_one_of_conjNormal_derivedOf_eq_self {w : ↥M} (hw : (w : G) ∈ W₁)
    (hw1 : (w : G) ≠ 1) :
    ∀ x ∈ (U.subgroupOf M).subgroupOf (derivedOf M),
      MulAut.conjNormal (H := derivedOf M) w x = x → x = 1 := by
  intro x hx hfix
  have hxU : ((x : ↥M) : G) ∈ U := by simpa [Subgroup.mem_subgroupOf] using hx
  have hcomm : ((x : ↥M) : G) ∈ centralizer ({(w : G)} : Set G) := by
    refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    have h1 : (w : G) * ((x : ↥M) : G) * (w : G)⁻¹ = ((x : ↥M) : G) := by
      rw [← coe_coe_conjNormal_derivedOf, hfix]
    calc ((x : ↥M) : G) * (w : G)
        = ((w : G) * ((x : ↥M) : G) * (w : G)⁻¹) * (w : G) := by rw [h1]
      _ = (w : G) * ((x : ↥M) : G) := by group
  have hW₂ : ((x : ↥M) : G) ∈ W₂ := by
    rw [← hc.inf_centralizer_eq_W₂ (w : G) hw hw1]
    exact Subgroup.mem_inf.2 ⟨coe_coe_mem_commutator M x, hcomm⟩
  exact Subtype.ext (Subtype.ext
    (Subgroup.disjoint_def.1 hc.disjoint_hallCore_E (hc.le_hallCore_W₂ hW₂) hxU))

theorem exists_mem_W₁_pow_natCard_eq_one :
    ∃ w : ↥M, (w : G) ∈ W₁ ∧ (w : G) ≠ 1 ∧ w ^ Nat.card ↥W₁ = 1 := by
  obtain ⟨w₀, hw₀⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hc.ne_bot_W₁
  refine ⟨⟨(w₀ : G), hc.le_M_W₁ w₀.2⟩, w₀.2, fun hcon => hw₀ (Subtype.ext hcon), ?_⟩
  have h1 : (w₀ : ↥W₁) ^ Nat.card ↥W₁ = 1 := pow_card_eq_one'
  have h2 : ((w₀ : G)) ^ Nat.card ↥W₁ = 1 := by
    rw [← Subgroup.coe_pow, h1, Subgroup.coe_one]
  exact Subtype.ext (by rw [Subgroup.coe_pow]; exact h2)

theorem apply_eq_apply_one_of_mem_subgroupOf_inf_centralizer
    (hqprime : (Nat.card ↥W₁).Prime)
    {θ : ↥(derivedOf M) → ℂ} (hθ : θ ∈ Irr ↥(derivedOf M))
    (hθinv : ∀ (w : ↥M) (x : ↥(derivedOf M)),
      θ (MulAut.conjNormal (H := derivedOf M) w x) = θ x)
    {x : ↥(derivedOf M)}
    (hx : (x : ↥M) ∈ (U ⊓ centralizer ((hallCoreIn M : Subgroup G) : Set G)).subgroupOf M) :
    θ x = θ 1 := by
  have := hc.normal_subgroupOf_hallCoreIn_derivedOf
  obtain ⟨w, hwW, hw1, hwpow⟩ := hc.exists_mem_W₁_pow_natCard_eq_one
  have hqK : ¬ Nat.card ↥W₁ ∣ Nat.card ↥(derivedOf M) := by
    rw [natCard_derivedOf]
    exact (Nat.Prime.coprime_iff_not_dvd hqprime).1 hc.coprime_natCard_W₁_natCard_commutator
  have hbq : MulAut.conjNormal (H := derivedOf M) w ^ Nat.card ↥W₁ = 1 := by
    rw [← map_pow, hwpow, map_one]
  have hsub := subset_charValueKernel_centralizer_inf_of_fixed
    (E := ((hallCoreIn M).subgroupOf M).subgroupOf (derivedOf M))
    (U := (U.subgroupOf M).subgroupOf (derivedOf M))
    hqprime hqK hbq hc.isComplement'_subgroupOf_hallCoreIn_E_derivedOf
    (mapsTo_conjNormal_subgroupOf_hallCoreIn M w) (hc.mapsTo_conjNormal_subgroupOf_E hwW)
    (hc.eq_one_of_conjNormal_derivedOf_eq_self hwW hw1) hθ (hθinv w)
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hx
  refine mem_charValueKernel.1 (hsub (Subgroup.mem_inf.2 ⟨?_, ?_⟩))
  · refine Subgroup.mem_centralizer_iff.2 fun e he => ?_
    have heG : ((e : ↥M) : G) ∈ hallCoreIn M := by
      simpa [Subgroup.mem_subgroupOf] using he
    exact Subtype.ext (Subtype.ext (Subgroup.mem_centralizer_iff.1 hx.2 _ heG))
  · simpa [Subgroup.mem_subgroupOf] using hx.1

theorem hallCore_subgroupOf_ne_bot : (hallCore ↥M : Subgroup ↥M) ≠ ⊥ := fun h =>
  hc.hallCore_ne_bot (by rw [h, Subgroup.map_bot])

theorem sup_derivedOf_subgroupOf_W₁_eq_top : derivedOf M ⊔ W₁.subgroupOf M = ⊤ := by
  rw [derivedOf_eq_subgroupOf_commutator]
  exact hc.isComplement'_subgroupOf_commutator_W₁.sup_eq_top

theorem inf_derivedOf_subgroupOf_W₁_eq_bot : derivedOf M ⊓ W₁.subgroupOf M = ⊥ := by
  rw [derivedOf_eq_subgroupOf_commutator]
  exact disjoint_iff.1 hc.isComplement'_subgroupOf_commutator_W₁.disjoint

theorem coprime_natCard_subgroupOf_W₁_subgroupOf_E :
    (Nat.card ↥(W₁.subgroupOf M)).Coprime (Nat.card ↥(U.subgroupOf M)) := by
  rw [natCard_subgroupOf_eq_of_le hc.le_M_W₁, natCard_subgroupOf_eq_of_le hc.le_M_E]
  exact hc.coprime_natCard_W₁_natCard_commutator.coprime_dvd_right
    (Subgroup.card_dvd_of_le hc.le_commutator_E)

theorem apply_one_eq_relIndex_of_isMinimalAbelianCore
    (hmac : IsMinimalAbelianCore (derivedOf M) (W₁.subgroupOf M) (W₂.subgroupOf M)
      (hallCore ↥M) (U.subgroupOf M))
    {θ : ↥(derivedOf M) → ℂ} (hθ : θ ∈ Irr ↥(derivedOf M))
    (hθinv : ∀ (w : ↥M) (x : ↥(derivedOf M)),
      θ (MulAut.conjNormal (H := derivedOf M) w x) = θ x)
    (hθdet : ∃ x : ↥(derivedOf M), (x : ↥M) ∈ (hallCoreIn M).subgroupOf M ∧ θ x ≠ θ 1) :
    θ 1 = (((U ⊓ centralizer ((hallCoreIn M : Subgroup G) : Set G)).relIndex U : ℕ) : ℂ) := by
  have := hmac.isMulCommutative_core
  have := hmac.isMulCommutative_compl
  have hdet : ∃ x : ↥(derivedOf M), (x : ↥M) ∈ (hallCore ↥M : Subgroup ↥M) ∧ θ x ≠ θ 1 := by
    obtain ⟨x, hx, hne⟩ := hθdet
    exact ⟨x, by rwa [← subgroupOf_hallCoreIn_self], hne⟩
  have hinv : ∀ t ∈ W₁.subgroupOf M, ∀ x y : ↥(derivedOf M),
      (y : ↥M) = t⁻¹ * (x : ↥M) * t → θ y = θ x := by
    intro t _ x y hxy
    have hy : y = MulAut.conjNormal (H := derivedOf M) t⁻¹ x := by
      refine Subtype.ext ?_
      rw [MulAut.conjNormal_apply (H := derivedOf M) t⁻¹ x, hxy]
      group
    rw [hy]
    exact hθinv t⁻¹ x
  rw [apply_one_eq_relIndex_coreCentralizer_of_sup_eq
      (N := hallCore ↥M) (V := U.subgroupOf M) (Q := W₁.subgroupOf M) (K := derivedOf M)
      hmac.sup_eq hc.hallCore_subgroupOf_ne_bot hmac.inf_eq_bot
      hc.sup_derivedOf_subgroupOf_W₁_eq_top hc.inf_derivedOf_subgroupOf_W₁_eq_bot
      hmac.le_normalizer hmac.prime_natCard rfl hc.coprime_natCard_subgroupOf_W₁_subgroupOf_E
      hmac.minimal hθ hdet hinv,
    relIndex_coreCentralizer_hallCore hc.le_M_E]

theorem le_hallCore_subgroupOf_W₂ : W₂.subgroupOf M ≤ hallCore ↥M := by
  rw [← subgroupOf_hallCoreIn_self, hallCoreIn_eq]
  exact Subgroup.comap_mono hc.le_hallCore_W₂

theorem sup_hallCore_subgroupOf_E_eq_derivedOf : hallCore ↥M ⊔ U.subgroupOf M = derivedOf M := by
  rw [← subgroupOf_hallCoreIn_self, ← Subgroup.subgroupOf_sup (hallCoreIn_le M) hc.le_M_E,
    hallCoreIn_eq, hc.sup_hallCore_E, ← derivedOf_eq_subgroupOf_commutator]

theorem inf_hallCore_subgroupOf_E_eq_bot : hallCore ↥M ⊓ U.subgroupOf M = ⊥ := by
  rw [← subgroupOf_hallCoreIn_self, Subgroup.subgroupOf, Subgroup.subgroupOf,
    ← Subgroup.comap_inf, hallCoreIn_eq, disjoint_iff.1 hc.disjoint_hallCore_E]
  simp

theorem le_normalizer_subgroupOf_E :
    W₁.subgroupOf M ≤ normalizer ((U.subgroupOf M : Subgroup ↥M) : Set ↥M) := by
  intro w hw
  refine Subgroup.mem_normalizer_iff.2 fun y => ?_
  simp only [Subgroup.mem_subgroupOf]
  have h := Subgroup.mem_normalizer_iff.1
    (hc.le_normalizer_E (Subgroup.mem_subgroupOf.1 hw)) ((y : G))
  exact ⟨fun hy => by simpa using h.1 hy, fun hy => h.2 (by simpa using hy)⟩

theorem apply_one_eq_relIndex_of_core_clauses
    (hHabel : IsMulCommutative ↥(hallCore ↥M : Subgroup ↥M))
    (hqprime : (Nat.card ↥W₁).Prime)
    (hmin : ∀ N ≤ (hallCore ↥M : Subgroup ↥M),
      U.subgroupOf M ≤ normalizer ((N : Subgroup ↥M) : Set ↥M) →
      W₁.subgroupOf M ≤ normalizer ((N : Subgroup ↥M) : Set ↥M) →
      N = ⊥ ∨ N = hallCore ↥M)
    (hCder : U ⊓ centralizer ((hallCoreIn M : Subgroup G) : Set G) = ⁅U, U⁆)
    {θ : ↥(derivedOf M) → ℂ} (hθ : θ ∈ Irr ↥(derivedOf M))
    (hθinv : ∀ (w : ↥M) (x : ↥(derivedOf M)),
      θ (MulAut.conjNormal (H := derivedOf M) w x) = θ x)
    (hθdet : ∃ x : ↥(derivedOf M), (x : ↥M) ∈ (hallCoreIn M).subgroupOf M ∧ θ x ≠ θ 1) :
    θ 1 = (((U ⊓ centralizer ((hallCoreIn M : Subgroup G) : Set G)).relIndex U : ℕ) : ℂ) := by
  have := hHabel
  have := hallCore_normal (G := ↥M)
  have hqprime' : (Nat.card ↥(W₁.subgroupOf M)).Prime := by
    rwa [natCard_subgroupOf_eq_of_le hc.le_M_W₁]
  have hdet : ∃ x : ↥(derivedOf M), (x : ↥M) ∈ (hallCore ↥M : Subgroup ↥M) ∧ θ x ≠ θ 1 := by
    obtain ⟨x, hx, hne⟩ := hθdet
    exact ⟨x, by rwa [← subgroupOf_hallCoreIn_self], hne⟩
  have hinv : ∀ t ∈ W₁.subgroupOf M, ∀ x y : ↥(derivedOf M),
      (y : ↥M) = t⁻¹ * (x : ↥M) * t → θ y = θ x := by
    intro t _ x y hxy
    have hy : y = MulAut.conjNormal (H := derivedOf M) t⁻¹ x := by
      refine Subtype.ext ?_
      rw [MulAut.conjNormal_apply (H := derivedOf M) t⁻¹ x, hxy]
      group
    rw [hy]
    exact hθinv t⁻¹ x
  have hVder : ⁅U.subgroupOf M, U.subgroupOf M⁆
      ≤ coreCentralizer (hallCore ↥M) (U.subgroupOf M) := by
    rw [coreCentralizer_hallCore_eq_subgroupOf, hCder]
    exact commutator_subgroupOf_le_subgroupOf_commutator M U
  have hCker : ∀ x : ↥(derivedOf M),
      ((x : ↥M) ∈ coreCentralizer (hallCore ↥M) (U.subgroupOf M)) → θ x = θ 1 := by
    intro x hx
    rw [coreCentralizer_hallCore_eq_subgroupOf] at hx
    exact hc.apply_eq_apply_one_of_mem_subgroupOf_inf_centralizer hqprime hθ hθinv hx
  rw [apply_one_eq_relIndex_coreCentralizer_of_commutator_le
      (N := hallCore ↥M) (V := U.subgroupOf M) (Q := W₁.subgroupOf M) (K := derivedOf M)
      hc.sup_hallCore_subgroupOf_E_eq_derivedOf hc.hallCore_subgroupOf_ne_bot
      hc.inf_hallCore_subgroupOf_E_eq_bot
      hc.sup_derivedOf_subgroupOf_W₁_eq_top hc.inf_derivedOf_subgroupOf_W₁_eq_bot
      hc.le_normalizer_subgroupOf_E hqprime' rfl
      hc.coprime_natCard_subgroupOf_W₁_subgroupOf_E hmin hVder hθ hdet hCker hinv,
    relIndex_coreCentralizer_hallCore hc.le_M_E]

theorem isMinimalAbelianCore_of_core_clauses
    (hHabel : IsMulCommutative ↥(hallCore ↥M : Subgroup ↥M))
    (hUabel : IsMulCommutative ↥(U.subgroupOf M))
    (hqprime : (Nat.card ↥W₁).Prime)
    (hmin : ∀ N ≤ (hallCore ↥M : Subgroup ↥M),
      U.subgroupOf M ≤ normalizer ((N : Subgroup ↥M) : Set ↥M) →
      W₁.subgroupOf M ≤ normalizer ((N : Subgroup ↥M) : Set ↥M) →
      N = ⊥ ∨ N = hallCore ↥M) :
    IsMinimalAbelianCore (derivedOf M) (W₁.subgroupOf M) (W₂.subgroupOf M) (hallCore ↥M)
      (U.subgroupOf M) where
  normal := hallCore_normal
  isMulCommutative_core := hHabel
  isMulCommutative_compl := hUabel
  right_le := hc.le_hallCore_subgroupOf_W₂
  sup_eq := hc.sup_hallCore_subgroupOf_E_eq_derivedOf
  inf_eq_bot := hc.inf_hallCore_subgroupOf_E_eq_bot
  le_normalizer := hc.le_normalizer_subgroupOf_E
  prime_natCard := by rwa [natCard_subgroupOf_eq_of_le hc.le_M_W₁]
  minimal := hmin

theorem isMulCommutative_subgroupOf_E_of_isMulCommutative (hU : IsMulCommutative ↥U) :
    IsMulCommutative ↥(U.subgroupOf M) := by
  refine ⟨⟨fun x y => ?_⟩⟩
  have hx : ((x : ↥M) : G) ∈ U := Subgroup.mem_subgroupOf.1 x.2
  have hy : ((y : ↥M) : G) ∈ U := Subgroup.mem_subgroupOf.1 y.2
  have h := congrArg Subtype.val (hU.is_comm.comm (⟨_, hx⟩ : ↥U) ⟨_, hy⟩)
  exact Subtype.ext (Subtype.ext (by push_cast; exact h))

theorem isMulCommutative_subgroupOf_E_of_isTypeIII (hG : IsMinimalOddSimple G) (hM : IsCoatom M)
    (htype : IsTypeIII M) : IsMulCommutative ↥(U.subgroupOf M) :=
  hc.isMulCommutative_subgroupOf_E_of_isMulCommutative
    (htype.clauses_of_isWitnessedPConfiguration_of_minimalSimple hG.simple hG.nonabelian hG.odd
      hG.solvable hM hc).2.2.1

theorem minimal_hallCore_of_chief
    (hHcomm : ⁅(hallCoreIn M : Subgroup G), (hallCoreIn M : Subgroup G)⁆ = ⊥)
    (hCHU : (hallCoreIn M : Subgroup G) ⊓ centralizer (U : Set G) = ⊥)
    (hchief : ∀ H₀ : Subgroup G, H₀ ≤ hallCoreIn M → M ≤ normalizer (H₀ : Set G) →
      hallCoreIn M ⊓ centralizer (U : Set G) ≤ H₀ → H₀ < hallCoreIn M →
      (∀ H₁ : Subgroup G, M ≤ normalizer (H₁ : Set G) →
        ¬ (H₀ < H₁ ∧ H₁ < hallCoreIn M)) → H₀ = ⊥) :
    ∀ N ≤ (hallCore ↥M : Subgroup ↥M),
      U.subgroupOf M ≤ normalizer ((N : Subgroup ↥M) : Set ↥M) →
      W₁.subgroupOf M ≤ normalizer ((N : Subgroup ↥M) : Set ↥M) →
      N = ⊥ ∨ N = hallCore ↥M := by
  intro N hNH hNU hNW₁
  have habel : IsMulCommutative ↥(hallCore ↥M : Subgroup ↥M) :=
    isMulCommutative_hallCore_of_commutator_eq_bot M hHcomm
  have hHnorm : (hallCore ↥M : Subgroup ↥M) ≤ normalizer ((N : Subgroup ↥M) : Set ↥M) := by
    refine Subgroup.le_normalizer_iff.2 fun h hh n hn => ?_
    have hcomm : h * n * h⁻¹ = n := by
      have h1 : h * n = n * h :=
        congrArg Subtype.val (habel.is_comm.comm (⟨h, hh⟩ : ↥(hallCore ↥M)) ⟨n, hNH hn⟩)
      calc h * n * h⁻¹ = n * h * h⁻¹ := by rw [h1]
        _ = n := by group
    rw [hcomm]; exact hn
  have hnormal : N.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff,
      ← hc.sup_derivedOf_subgroupOf_W₁_eq_top, ← hc.sup_hallCore_subgroupOf_E_eq_derivedOf]
    exact sup_le (sup_le hHnorm hNU) hNW₁
  have hAle : N.map M.subtype ≤ hallCoreIn M := by
    rw [hallCoreIn_eq]; exact Subgroup.map_mono hNH
  have hAnorm : M ≤ normalizer ((N.map M.subtype : Subgroup G) : Set G) :=
    le_normalizer_map_subtype_of_normal hnormal
  rcases eq_or_lt_of_le hAle with heq | hlt
  · right
    exact Subgroup.map_injective M.subtype_injective (by rw [heq, hallCoreIn_eq])
  · left
    set A := N.map M.subtype with hAdef
    set S : Set (Subgroup G) :=
      {X | A ≤ X ∧ X < hallCoreIn M ∧ M ≤ normalizer ((X : Subgroup G) : Set G)} with hSdef
    obtain ⟨H₀, hH₀S, hH₀max⟩ :=
      (Set.toFinite S).exists_maximalFor (fun X : Subgroup G => Nat.card ↥X) S
        ⟨A, le_rfl, hlt, hAnorm⟩
    have hno : ∀ H₁ : Subgroup G, M ≤ normalizer ((H₁ : Subgroup G) : Set G) →
        ¬ (H₀ < H₁ ∧ H₁ < hallCoreIn M) := by
      rintro H₁ hH₁ ⟨h1, h2⟩
      exact h1.ne (Subgroup.eq_of_le_of_card_ge h1.le
        (hH₀max ⟨hH₀S.1.trans h1.le, h2, hH₁⟩ (Subgroup.card_le_of_le h1.le)))
    have hbot := hchief H₀ hH₀S.2.1.le hH₀S.2.2 (by rw [hCHU]; exact bot_le) hH₀S.2.1 hno
    exact (Subgroup.map_eq_bot_iff_of_injective _ M.subtype_injective).1
      (le_bot_iff.1 (hbot ▸ hH₀S.1))

theorem isMinimalAbelianCore_of_isTypeIII (hG : IsMinimalOddSimple G) (hM : IsCoatom M)
    (htype : IsTypeIII M)
    (hHcomm : ⁅(hallCoreIn M : Subgroup G), (hallCoreIn M : Subgroup G)⁆ = ⊥)
    (hCHU : (hallCoreIn M : Subgroup G) ⊓ centralizer (U : Set G) = ⊥)
    (hchief : ∀ H₀ : Subgroup G, H₀ ≤ hallCoreIn M → M ≤ normalizer (H₀ : Set G) →
      hallCoreIn M ⊓ centralizer (U : Set G) ≤ H₀ → H₀ < hallCoreIn M →
      (∀ H₁ : Subgroup G, M ≤ normalizer (H₁ : Set G) →
        ¬ (H₀ < H₁ ∧ H₁ < hallCoreIn M)) → H₀ = ⊥) :
    IsMinimalAbelianCore (derivedOf M) (W₁.subgroupOf M) (W₂.subgroupOf M) (hallCore ↥M)
      (U.subgroupOf M) :=
  hc.isMinimalAbelianCore_of_core_clauses
    (isMulCommutative_hallCore_of_commutator_eq_bot M hHcomm)
    (hc.isMulCommutative_subgroupOf_E_of_isTypeIII hG hM htype)
    (htype.clauses_of_isWitnessedPConfiguration_of_minimalSimple hG.simple hG.nonabelian
      hG.odd hG.solvable hM hc).1.prime_natCard_W₁
    (hc.minimal_hallCore_of_chief hHcomm hCHU hchief)

theorem apply_one_eq_relIndex_of_invariant_of_detect
    (hG : IsMinimalOddSimple G) (hM : IsCoatom M) (htype : IsTypeIII M ∨ IsTypeIV M)
    (hHcomm : ⁅(hallCoreIn M : Subgroup G), (hallCoreIn M : Subgroup G)⁆ = ⊥)
    (hCHU : (hallCoreIn M : Subgroup G) ⊓ centralizer (U : Set G) = ⊥)
    (hchief : ∀ H₀ : Subgroup G, H₀ ≤ hallCoreIn M → M ≤ normalizer (H₀ : Set G) →
      hallCoreIn M ⊓ centralizer (U : Set G) ≤ H₀ → H₀ < hallCoreIn M →
      (∀ H₁ : Subgroup G, M ≤ normalizer (H₁ : Set G) →
        ¬ (H₀ < H₁ ∧ H₁ < hallCoreIn M)) → H₀ = ⊥)
    (_hCder : U ⊓ centralizer ((hallCoreIn M : Subgroup G) : Set G) = ⁅U, U⁆)
    {θ : ↥(derivedOf M) → ℂ} (hθ : θ ∈ Irr ↥(derivedOf M))
    (hθinv : ∀ (w : ↥M) (x : ↥(derivedOf M)),
      θ (MulAut.conjNormal (H := derivedOf M) w x) = θ x)
    (hθdet : ∃ x : ↥(derivedOf M), (x : ↥M) ∈ (hallCoreIn M).subgroupOf M ∧ θ x ≠ θ 1) :
    θ 1 = (((U ⊓ centralizer ((hallCoreIn M : Subgroup G) : Set G)).relIndex U : ℕ) : ℂ) := by
  rcases htype with hT | hT
  · exact hc.apply_one_eq_relIndex_of_isMinimalAbelianCore
      (hc.isMinimalAbelianCore_of_isTypeIII hG hM hT hHcomm hCHU hchief) hθ hθinv hθdet
  ·
    exact hc.apply_one_eq_relIndex_of_core_clauses
      (isMulCommutative_hallCore_of_commutator_eq_bot M hHcomm)
      (hT.clauses_of_isWitnessedPConfiguration_of_minimalSimple hG.simple hG.nonabelian
        hG.odd hG.solvable hM hc).1.prime_natCard_W₁
      (hc.minimal_hallCore_of_chief hHcomm hCHU hchief) _hCder hθ hθinv hθdet

end IsWitnessedPConfiguration

end CFSG.FeitThompson

namespace CFSG.FeitThompson.Proofs

open Subgroup CFSG.FeitThompson CFSG.FeitThompson.Prep06

universe u

open scoped Classical in
private theorem row_kernel_and_degree {G : Type u} [Group G] [Fintype G]
    (hG : IsMinimalOddSimple G) {M U W₁ W₂ : Subgroup G} (hM : IsCoatom M)
    (htype : IsTypeIII M ∨ IsTypeIV M) (hc : IsWitnessedPConfiguration M U W₁ W₂)
    (hHcomm : ⁅(hallCoreIn M : Subgroup G), (hallCoreIn M : Subgroup G)⁆ = ⊥)
    (hCHU : (hallCoreIn M : Subgroup G) ⊓ centralizer (U : Set G) = ⊥)
    (hchief : ∀ H₀ : Subgroup G, H₀ ≤ hallCoreIn M → M ≤ normalizer (H₀ : Set G) →
      hallCoreIn M ⊓ centralizer (U : Set G) ≤ H₀ → H₀ < hallCoreIn M →
      (∀ H₁ : Subgroup G, M ≤ normalizer (H₁ : Set G) →
        ¬ (H₀ < H₁ ∧ H₁ < hallCoreIn M)) → H₀ = ⊥)
    (hCder : U ⊓ centralizer ((hallCoreIn M : Subgroup G) : Set G) = ⁅U, U⁆)
    (h : IsPrimeCyclicTIHyp (derivedOf M) (W₁.subgroupOf M) (W₂.subgroupOf M))
    {σ : ↥(classFun ↥(W₁.subgroupOf M ⊔ W₂.subgroupOf M)) →ₗ[ℂ] ↥(classFun ↥M)}
    (hσ : IsCyclicTIIsometry (W₁.subgroupOf M ⊔ W₂.subgroupOf M) (W₁.subgroupOf M)
      (W₂.subgroupOf M) σ)
    (j : ↑(Irr ↥(W₂.subgroupOf M))) (hj : j ≠ principalIrr ↥(W₂.subgroupOf M)) :
    (∀ x : ↥(derivedOf M),
        (x : ↥M) ∈ (U ⊓ centralizer ((hallCoreIn M : Subgroup G) : Set G)).subgroupOf M →
        h.primeTIres σ j x = h.primeTIres σ j 1) ∧
      (∃ x : ↥(derivedOf M), (x : ↥M) ∈ (hallCoreIn M).subgroupOf M ∧
        h.primeTIres σ j x ≠ h.primeTIres σ j 1) ∧
      h.primeTIres σ j 1
        = (((U ⊓ centralizer ((hallCoreIn M : Subgroup G) : Set G)).relIndex U : ℕ) : ℂ) := by
  have hqprime : (Nat.card ↥W₁).Prime := by
    rcases htype with hT | hT
    · exact (hT.clauses_of_isWitnessedPConfiguration_of_minimalSimple hG.simple hG.nonabelian
        hG.odd hG.solvable hM hc).1.prime_natCard_W₁
    · exact (hT.clauses_of_isWitnessedPConfiguration_of_minimalSimple hG.simple hG.nonabelian
        hG.odd hG.solvable hM hc).1.prime_natCard_W₁
  have hIrr : h.primeTIres σ j ∈ Irr ↥(derivedOf M) := h.primeTIres_mem_Irr hσ j
  have hinv : ∀ (w : ↥M) (x : ↥(derivedOf M)),
      h.primeTIres σ j (MulAut.conjNormal (H := derivedOf M) w x) = h.primeTIres σ j x := by
    intro w x
    refine IsMinimalAbelianCore.primeTIres_conj_eq h hσ j w⁻¹ x _ ?_
    show ((MulAut.conjNormal (H := derivedOf M) w x : ↥(derivedOf M)) : ↥M) = _
    rw [MulAut.conjNormal_apply (H := derivedOf M) w x]
    group
  have hdet : ∃ x : ↥(derivedOf M), (x : ↥M) ∈ (hallCoreIn M).subgroupOf M ∧
      h.primeTIres σ j x ≠ h.primeTIres σ j 1 :=
    h.exists_mem_primeTIres_ne hσ (Subgroup.comap_mono hc.le_hallCore_W₂) hj
  exact ⟨fun x hx =>
      hc.apply_eq_apply_one_of_mem_subgroupOf_inf_centralizer hqprime hIrr hinv hx,
    hdet,
    hc.apply_one_eq_relIndex_of_invariant_of_detect hG hM htype hHcomm hCHU hchief hCder
      hIrr hinv hdet⟩

open scoped Classical in
theorem FPF_type_iii_iv_row_degree_and_kernel
    (h₁ : Statements.FPF_type_iii_iv_core_elementary_chief_kernel_trivial.{u})
    (_h₂ : Statements.FPF_type_iii_v_second_factor_prime.{u}) :
    Statements.FPF_type_iii_iv_row_degree_and_kernel.{u} := by
  intro G _ _ hG M U W₁ W₂ hM htype hc σ w l δ μ hsetup d n dsign hdeg hsign hdn
  have : Fintype ↑(Irr ↥(W₁.subgroupOf M)) := Fintype.ofFinite _
  have h := hc.isPrimeCyclicTIHyp_subgroupOf hG.odd
  have hσ := hsetup.isometry
  have hcard1 : Nat.card ↥(W₁.subgroupOf M) = Nat.card ↥W₁ :=
    natCard_subgroupOf_eq_of_le hc.le_M_W₁
  obtain ⟨hcIIToIV, hUne⟩ : IsPConfigurationIIToIV M U W₁ W₂ ∧ U ≠ ⊥ := by
    rcases htype with hT | hT
    · obtain ⟨t1, t2, -, -⟩ := hT.clauses_of_isWitnessedPConfiguration_of_minimalSimple
        hG.simple hG.nonabelian hG.odd hG.solvable hM hc
      exact ⟨t1, t2⟩
    · obtain ⟨t1, t2, -⟩ := hT.clauses_of_isWitnessedPConfiguration_of_minimalSimple
        hG.simple hG.nonabelian hG.odd hG.solvable hM hc
      refine ⟨t1, fun hb => t2 ?_⟩
      subst hb
      refine ⟨⟨fun a b => ?_⟩⟩
      have ha : a = 1 := Subtype.ext (Subgroup.mem_bot.1 a.2)
      have hb : b = 1 := Subtype.ext (Subgroup.mem_bot.1 b.2)
      rw [ha, hb, one_mul]
  have hqprime : (Nat.card ↥W₁).Prime := hcIIToIV.prime_natCard_W₁
  have hqodd : Odd (Nat.card ↥W₁) := hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card W₁)
  have hδ : ∀ j, δ j = h.primeTISign σ j := by
    intro j
    refine (h.existsUnique_primeTISign hσ j).unique ⟨hsetup.sign j, ?_⟩
      ⟨h.primeTISign_eq_one_or_eq_neg_one j, ?_⟩
    · rw [← rowData_w_eq h hsetup.toIsRowData]
      exact hsetup.mu_zero_mem j
    · exact h.primeTIirr_principal_left (σ := σ) j ▸
        h.primeTIirr_principal_left_mem_Irr hσ j
  have hμ : ∀ i j, μ i j = h.primeTIirr σ i j := by
    intro i j
    rw [hsetup.mu_eq i j, rowData_l_eq h hsetup.toIsRowData i,
      rowData_w_eq h hsetup.toIsRowData, hδ j, h.primeTIirr_eq_mul i j,
      h.primeTIirr_principal_left]
  obtain ⟨-, -, hHcomm, hCHU, hchief, hCder, hN, hnt, -⟩ := h₁ G hG M U W₁ W₂ hM htype hc
  have hu1 : 1 < (U ⊓ centralizer ((hallCoreIn M : Subgroup G) : Set G)).relIndex U := by
    have := hN
    rw [Subgroup.relIndex, Subgroup.index_eq_card]
    exact Finite.one_lt_card_iff_nontrivial.2 hnt
  have hdvd := hc.natCard_W₁_dvd_relIndex_inf_centralizer_hallCoreIn_sub_one hqprime
    (hG.solvable M hM.1)
  have hrow : ∀ j, (∑ᶠ i : ↑(Irr ↥(W₁.subgroupOf M)), μ i j) = h.primeTIrow σ j := by
    intro j
    rw [finsum_eq_sum_of_fintype, h.primeTIrow_def]
    exact Finset.sum_congr rfl fun i _ => hμ i j
  have hres : ∀ j, resClassFun (derivedOf M) (μ (principalIrr ↥(W₁.subgroupOf M)) j)
      = h.primeTIres σ j := by
    intro j
    rw [hμ]
    exact (h.primeTIres_def j).symm
  obtain ⟨j₀, hj₀⟩ := IsPrimeCyclicTIHyp.exists_ne_principalIrr_right h
  have hdu : d = (U ⊓ centralizer ((hallCoreIn M : Subgroup G) : Set G)).relIndex U := by
    have hd0 : μ (principalIrr ↥(W₁.subgroupOf M)) j₀ 1 = (d : ℂ) :=
      hdeg (principalIrr ↥(W₁.subgroupOf M)) j₀ hj₀
    rw [hμ, ← h.primeTIres_one j₀,
      (row_kernel_and_degree hG hM htype hc hHcomm hCHU hchief hCder h hσ j₀ hj₀).2.2] at hd0
    exact Nat.cast_injective hd0.symm
  have hsign1 : dsign = 1 := by
    have hδ0 := hsign j₀ hj₀
    rcases hsetup.sign j₀ with hs | hs
    · rw [← hδ0, hs]
    · exfalso
      have hneg : dsign = -1 := by rw [← hδ0, hs]
      rw [hneg] at hdn
      have hnat : d + 1 = n * Nat.card ↥W₁ := by
        have hcast : ((d + 1 : ℕ) : ℂ) = ((n * Nat.card ↥W₁ : ℕ) : ℂ) := by
          push_cast
          linear_combination hdn
        exact Nat.cast_injective hcast
      have hq1 : Nat.card ↥W₁ ∣ d + 1 := ⟨n, by rw [hnat]; ring⟩
      have hq2 : Nat.card ↥W₁ ∣ d - 1 := by rw [hdu]; exact hdvd
      have h2 : Nat.card ↥W₁ ∣ 2 := by
        have hsub := Nat.dvd_sub hq1 hq2
        have hd1 : 1 ≤ d := by omega
        rwa [show d + 1 - (d - 1) = 2 by omega] at hsub
      rw [(Nat.prime_dvd_prime_iff_eq hqprime Nat.prime_two).1 h2] at hqodd
      exact (Nat.not_odd_iff_even.2 (by decide)) hqodd
  refine ⟨fun j hj => ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hu1, hdvd, hdu, hsign1, ?_⟩
  · rw [hres]; exact h.primeTIres_mem_Irr hσ j
  · rw [hres]; exact (row_kernel_and_degree hG hM htype hc hHcomm hCHU hchief hCder h hσ j hj).1
  · rw [hres]; exact (row_kernel_and_degree hG hM htype hc hHcomm hCHU hchief hCder h hσ j hj).2.1
  · rw [hres]; exact (row_kernel_and_degree hG hM htype hc hHcomm hCHU hchief hCder h hσ j hj).2.2
  · rw [hrow, hres]; exact (h.indClassFun_primeTIres hσ j).symm
  · rw [hrow, h.primeTIrow_one j,
      (row_kernel_and_degree hG hM htype hc hHcomm hCHU hchief hCder h hσ j hj).2.2, hcard1]
  · rw [hrow, h.cfInner_self_primeTIrow hσ j, hcard1]
  · have hd1 : 1 ≤ d := by omega
    rw [hsign1] at hdn
    have hnat : d - 1 = n * Nat.card ↥W₁ := by
      have hcast : ((d - 1 : ℕ) : ℂ) = ((n * Nat.card ↥W₁ : ℕ) : ℂ) := by
        push_cast [Nat.cast_sub hd1]
        linear_combination hdn
      exact Nat.cast_injective hcast
    rw [← hdu, hnat]

end CFSG.FeitThompson.Proofs
