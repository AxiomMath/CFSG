module

public import CFSG.GH74.GLS.Stage2.Signalizer.L46EDefs
public import CFSG.GH74.GLS.Stage2.Signalizer.L64Sub
public import CFSG.GH74.GLS.Stage2.Signalizer.Stmt46E

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.L46E

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
open scoped commutatorElement

@[expose] def AutFactD1H : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (H X : Subgroup G) (p : ℕ)
    (h : Sig4Sub G z H p X), ⁅Em H, X⁆ ≠ ⊥ →
    C43d1 k (zSec z H h.A.z_mem (pCore p ↥H)) (xBar p H X) →
    ∀ E : Subgroup G, E ≤ H ⊓ centralizer (X : Set G) →
      (E.subgroupOf (H ⊓ centralizer (X : Set G))).Normal → z ∈ normalizer (E : Set G) →
      Odd (Nat.card ↥E) → ¬ p ∣ Nat.card ↥E → E ≤ centralizer ((⁅Em H, X⁆ : Subgroup G) : Set G)

@[expose] def ComponentsLemma : Prop :=
  ∀ {A : Type} [Group A] [Finite A] {D : Subgroup A} [D.Normal], Group.IsSolvable ↥D →
    ∀ (X E : Subgroup A), E ≤ centralizer (X : Set A) →
      (∀ e ∈ E, ∀ k ∈ ⁅layer A, X⁆, ⁅k, e⁆ ∈ D) →
        E ≤ centralizer ((⁅layer A, X⁆ : Subgroup A) : Set A)

theorem lemma4_6E_core (hT3 : ComponentsLemma) (h43 : Prop4_3E) (hB : AutFactB) (hC : AutFactCOdd)
    (hD1 : AutFactD1H) (hE : AutFactE) : Lemma4_6E := by
  classical
  intro G _ _ z k S hctx H X p h hEne E hEle hEn hzE hodd hp'
  have hp : p.Prime := h.A.prime
  have hXH : X ≤ H := h.A.X_le
  have hconcl := L64.prop4_3Esub_of h43 hctx h hEne
  by_cases hd : C43d1 k (zSec z H h.A.z_mem (pCore p ↥H)) (xBar p H X)
  · exact hD1 G z k H X p h hEne hd E hEle hEn hzE hodd hp'
  have hbce : C43b p (xBar p H X) ∨ C43c (zSec z H h.A.z_mem (pCore p ↥H)) p (xBar p H X) ∨
      C43e (xBar p H X) := by
    rcases hconcl with h1 | h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact absurd h1 hd
    · exact Or.inr (Or.inr h1)
  have hEH : E ≤ H := hEle.trans inf_le_left
  let O : Subgroup ↥H := pCore p ↥H
  let π : ↥H →* Sec H O := QuotientGroup.mk' O
  let X' : Subgroup ↥H := X.subgroupOf H
  let E' : Subgroup ↥H := E.subgroupOf H
  have hEX' : E' ≤ centralizer (X' : Set ↥H) := by
    intro e he x hx
    have h1 := Subgroup.mem_centralizer_iff.1 (hEle he).2 (x : G) hx
    exact Subtype.ext h1
  have hcard : Nat.card ↥E' = Nat.card ↥E :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEH).toEquiv
  have key : ∀ e ∈ E', π e ∈ centralizer ((ncl (xBar p H X) : Subgroup (Sec H O)) : Set (Sec H O)) := by
    intro e he
    have hcentX : π e ∈ centralizer ((xBar p H X : Subgroup (Sec H O)) : Set (Sec H O)) := by
      rintro _ ⟨x, hx, rfl⟩
      have h1 := Subgroup.mem_centralizer_iff.1 (hEX' he) x hx
      show π x * π e = π e * π x
      rw [← map_mul, ← map_mul, h1]
    have hdvd : orderOf (π e) ∣ Nat.card ↥E := by
      have h2 : orderOf (π e) ∣ orderOf e := orderOf_map_dvd π e
      have h3 : orderOf e ∣ Nat.card ↥E' := by
        have := Subgroup.orderOf_dvd_natCard E' he
        exact this
      exact h2.trans (h3.trans (hcard ▸ dvd_rfl))
    have hcop : Nat.Coprime (orderOf (π e)) p := by
      refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 fun hpd => hp' ?_)
      exact hpd.trans hdvd
    rcases hbce with hb | hc | he3
    · exact hB _ p _ hp hb (π e) hcentX hcop
    · exact hC _ p _ _ hp h.A.odd hc (π e) hcentX hcop
    ·
      have h3 : 3 ∣ Nat.card ↥(xBar p H X) := by rw [he3.2]
      obtain ⟨xb, hxb⟩ := exists_prime_orderOf_dvd_card' (G := ↥(xBar p H X)) 3 h3
      obtain ⟨x, hx, hxπ⟩ := Subgroup.mem_map.1 xb.2
      obtain ⟨m, hm⟩ := h.A.pgroup ⟨(x : G), (Subgroup.mem_subgroupOf.1 hx)⟩
      have hxm : x ^ (p ^ m) = 1 := Subtype.ext (by simpa using congrArg Subtype.val hm)
      have h4 : orderOf (xb : Sec H O) ∣ p ^ m := by
        rw [← hxπ]
        exact orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hxm, map_one])
      have h5 : orderOf (xb : Sec H O) = 3 := by rw [Subgroup.orderOf_coe]; exact hxb
      have hp3 : p = 3 := by
        have : 3 ∣ p ^ m := h5 ▸ h4
        exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1
          (Nat.prime_three.dvd_of_dvd_pow this)).symm
      subst hp3
      have hodd' : Odd (orderOf (π e)) := Odd.of_dvd_nat hodd hdvd
      exact hE _ _ he3 (π e) hcentX hodd' hcop
  have hcomm : ∀ e ∈ E', ∀ k ∈ ⁅layer ↥H, X'⁆, ⁅k, e⁆ ∈ O := by
    intro e he k hk
    have hkK : π k ∈ ncl (xBar p H X) := by
      have hle : ⁅layer ↥H, X'⁆ ≤ (ncl (xBar p H X)).comap π := by
        rw [Subgroup.commutator_le]
        intro a _ x hx
        show π ⁅a, x⁆ ∈ ncl (xBar p H X)
        rw [map_commutatorElement, commutatorElement_def]
        have hx' : π x ∈ xBar p H X := Subgroup.mem_map_of_mem _ hx
        have h1 : π a * π x * (π a)⁻¹ ∈ ncl (xBar p H X) :=
          (Subgroup.normalClosure_normal).conj_mem (π x) (Subgroup.subset_normalClosure hx') (π a)
        exact (ncl (xBar p H X)).mul_mem h1 ((ncl (xBar p H X)).inv_mem
          (Subgroup.subset_normalClosure hx'))
      exact hle hk
    have h1 := Subgroup.mem_centralizer_iff.1 (key e he) (π k) hkK
    have h2 : π ⁅k, e⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_def]
      rw [← mul_inv_eq_one] at h1
      simpa [mul_assoc] using h1
    exact (QuotientGroup.eq_one_iff _).1 h2
  have hmain := hT3 (D := O) (L64.isSolvable_pCore hp H) X' E' hEX' hcomm
  intro g hg
  have h2 : ⁅(layer ↥H).map H.subtype, X⁆ = (⁅layer ↥H, X'⁆).map H.subtype := by
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hXH]
  show g ∈ centralizer (((⁅(layer ↥H).map H.subtype, X⁆ : Subgroup G)) : Set G)
  rw [h2]
  rintro _ ⟨k, hk, rfl⟩
  have h3 := Subgroup.mem_centralizer_iff.1 (hmain (show (⟨g, hEH hg⟩ : ↥H) ∈ E' from hg)) k hk
  have h4 := congrArg Subtype.val h3
  exact h4

end CFSG.GH74.GLS.Stage2.Signalizer.L46E
