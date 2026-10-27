module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.M11Spec
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.M11Iso

public section

namespace CFSG.EvenSporadicStandard.HNRecog

open Subgroup

theorem probeG_mem_closure {G : Type*} [Group G] (y j : G) (p : List ℕ) :
    probeG y j p ∈ closure ({y, j} : Set G) := by
  refine Subgroup.list_prod_mem _ ?_
  intro x hx
  obtain ⟨e, -, rfl⟩ := List.mem_map.1 hx
  exact mul_mem (pow_mem (subset_closure (by simp)) e) (subset_closure (by simp))

theorem coe_probeG {G : Type*} [Group G] (P : Subgroup G) (y j : ↥P) (p : List ℕ) :
    ((probeG y j p : ↥P) : G) = probeG (y : G) (j : G) p := by
  induction p with
  | nil => rfl
  | cons e p ih =>
    simp only [probeG, List.map_cons, List.prod_cons, Subgroup.coe_mul, Subgroup.coe_pow] at ih ⊢
    rw [ih]

theorem closure_pair_subtype_eq_top {G : Type*} [Group G] {K : Subgroup G} {a b : G}
    (ha : a ∈ K) (hb : b ∈ K) (h : closure ({a, b} : Set G) = K) :
    closure ({⟨a, ha⟩, ⟨b, hb⟩} : Set ↥K) = ⊤ := by
  subst h
  have := Subgroup.closure_closure_coe_preimage (k := ({a, b} : Set G))
  convert this using 2
  ext x
  simp [Subtype.ext_iff]

theorem mem_of_orderOf_eleven {G : Type*} [Group G] {E : Subgroup G} [E.Normal]
    (hi : E.index = 2) {t : G} (ht : orderOf t = 11) : t ∈ E := by
  have h2 : orderOf (QuotientGroup.mk t : G ⧸ E) ∣ 2 := by
    have hc : Nat.card (G ⧸ E) = 2 := hi
    rw [← hc]
    exact orderOf_dvd_natCard _
  have h11 : orderOf (QuotientGroup.mk t : G ⧸ E) ∣ 11 := by
    rw [← ht]
    exact orderOf_map_dvd (QuotientGroup.mk' E) t
  have h1 : orderOf (QuotientGroup.mk t : G ⧸ E) = 1 :=
    Nat.dvd_one.1 (by simpa using Nat.dvd_gcd h2 h11)
  exact (QuotientGroup.eq_one_iff t).1 (orderOf_eq_one_iff.1 h1)

section Cert


theorem nonempty_mulEquiv_native_m11_of_subgroup {G : Type*} [Group G] {K : Subgroup G} {a b : G}
    (ha : a ∈ K) (hb : b ∈ K) (hcard : Nat.card ↥K = 7920) (hgen : closure ({a, b} : Set G) = K)
    (hrel : ∀ w ∈ TauCeti.Sporadic.m11Presentation.relatorLetters,
      CFSG.Sporadic.Bridge.wordProd (fun i => if i = 0 then a else if i = 1 then b else 1) w = 1) :
    Nonempty (↥K ≃* ↥CFSG.Blueprint.NativeSporadic.M11) := by
  refine TwoHSData.nonempty_mulEquiv_native_m11 (α := ⟨a, ha⟩) (β := ⟨b, hb⟩) hcard
    (closure_pair_subtype_eq_top ha hb hgen) fun w hw => ?_
  apply Subtype.ext
  have hfun : (fun i : ℕ => (((if i = 0 then ⟨a, ha⟩ else if i = 1 then ⟨b, hb⟩ else 1 : ↥K)) : G))
      = fun i => if i = 0 then a else if i = 1 then b else 1 := by
    funext i
    split_ifs <;> rfl
  rw [CFSG.Sporadic.Bridge.coe_wordProd, hfun, hrel w hw]
  rfl

end Cert

end CFSG.EvenSporadicStandard.HNRecog
