module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec3Defs
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec3Tools
public import CFSG.LocalAnalysis.OddStandard.Solomon75LPlusTwoElt
public import CFSG.LocalAnalysis.OddStandard.Solomon75Thm11Skeleton

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS CFSG.ComponentClassification.CatalogueBPrimeJoin

open scoped commutatorElement

section Reduce

variable {X : Type} [Group X] [Finite X]

theorem pPrimeCoreOf_le_oddCoreOf {C K : Subgroup X} (hKC : K ≤ C)
    (hsub : (K.subgroupOf C).IsSubnormal) : pPrimeCoreOf 2 K ≤ oddCoreOf C := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := CFSG.ComponentClassification.CatalogueBHeldSmallCore.primeCore_subnormal_intersection
    2 (K.subgroupOf C) hsub
  let e : ↥(K.subgroupOf C) ≃* ↥K := Subgroup.subgroupOfEquivOfLe hKC
  have h2 : (pPrimeCore 2 ↥(K.subgroupOf C)).map e.toMonoidHom = pPrimeCore 2 ↥K :=
    pPrimeCore_map_iso 2 e
  rintro _ ⟨k, hk, rfl⟩
  have hk' : k ∈ (pPrimeCore 2 ↥(K.subgroupOf C)).map e.toMonoidHom := by rw [h2]; exact hk
  obtain ⟨k', hk', hkk⟩ := hk'
  rw [h1] at hk'
  refine ⟨⟨(k : X), hKC k.2⟩, ?_, rfl⟩
  have : ((k' : ↥C) : X) = (k : X) := by
    have := congrArg (fun y : ↥K => (y : X)) hkk
    exact this
  have hmem : ((k' : ↥(K.subgroupOf C)) : ↥C) ∈ pPrimeCore 2 ↥C := hk'
  have heq : (⟨(k : X), hKC k.2⟩ : ↥C) = ((k' : ↥(K.subgroupOf C)) : ↥C) :=
    Subtype.ext this.symm
  rw [heq]
  exact hmem

theorem exists_isAhatIntr_subgroupOf_of_covered {u : X} {Lu E H : Subgroup X}
    (hu : orderOf u = 2) (hLu : IsAhatIntr X u Lu) (hEC : E ≤ centralizer ({u} : Set X))
    (hEH : E ≤ H) (hcov : Lu ≤ E ⊔ oddCoreOf (centralizer ({u} : Set X))) (huH : u ∈ H) :
    ∃ J' : Subgroup X, J' ≤ H ∧ IsAhatIntr ↥H ⟨u, huH⟩ (J'.subgroupOf H) ∧
      (∀ x ∈ Lu ⊓ H, (∃ k : ℕ, x ^ 2 ^ k = 1) → x ∈ J') := by
  obtain ⟨hJC, huJ, hJpc, n, hn, hdc⟩ := hLu
  obtain ⟨J', hJ'CH, hJ'pc, -, hJ'two, ⟨q⟩⟩ := exists_isPComponent_inf_of_covered
    (C := centralizer ({u} : Set X)) (H := H) (O := oddCoreOf (centralizer ({u} : Set X)))
    (E := E) (J := Lu) (oddCoreOf_le _) (le_normalizer_oddCoreOf _) (odd_card_oddCoreOf _) hEC hEH
    hJC hJpc hcov
  have hJ'C : J' ≤ centralizer ({u} : Set X) := hJ'CH.trans inf_le_left
  have hJ'H : J' ≤ H := hJ'CH.trans inf_le_right
  have hcen : centralizer ({(⟨u, huH⟩ : ↥H)} : Set ↥H) =
      (centralizer ({u} : Set X)).subgroupOf H := centralizer_singleton_subgroup huH
  have hu2 : u ^ 2 ^ 1 = 1 := by
    rw [pow_one, ← hu]
    exact pow_orderOf_eq_one _
  have huJ' : u ∈ J' := hJ'two u (Subgroup.mem_inf.2 ⟨huJ, huH⟩) ⟨1, hu2⟩
  refine ⟨J', hJ'H, ⟨?_, huJ', ?_, n, hn, ?_⟩, hJ'two⟩
  · rw [hcen]
    exact Subgroup.subgroupOf_mono H hJ'C
  · rw [hcen]
    exact (isPComponent_subgroupOf_subgroupOf_iff hJ'C hJ'H).2 hJ'pc
  · obtain ⟨q₀⟩ := nonempty_quotPPrimeCore_equiv (Subgroup.subgroupOfEquivOfLe hJ'H)
    exact GH74.GLS.Stage12.McLRec.isDoubleCoverOfAlt_congr (q₀.trans q).symm hdc

theorem SolMinCEx.le_KProdIn_of_isIntrinsicIn (h : SolMinCEx X) {H H' L : Subgroup X} {u : X}
    (hH : H ≠ ⊤) (hH'H : H' ≤ H) (hL : IsIntrinsicIn X H' L u) : L ≤ KProdIn H := by
  obtain ⟨hu, huL, ⟨hLH', hLpc⟩, hLeq, Lu, hLu, hLuEq⟩ := hL
  have hLH : L ≤ H := hLH'.trans hH'H
  set E : Subgroup X := oPrimeResidualOf 2 (L ⊓ centralizer ({u} : Set X)) with hE
  have hEL : E ≤ L ⊓ centralizer ({u} : Set X) := Subgroup.map_subtype_le _
  have hEC : E ≤ centralizer ({u} : Set X) := hEL.trans inf_le_right
  have hEL' : E ≤ L := hEL.trans inf_le_left
  have hEH : E ≤ H := hEL'.trans hLH
  have hOLu : pPrimeCoreOf 2 Lu ≤ oddCoreOf (centralizer ({u} : Set X)) :=
    pPrimeCoreOf_le_oddCoreOf hLu.1 (isPComponent_two_iff.1 hLu.2.2.1).1
  have hcov : Lu ≤ E ⊔ oddCoreOf (centralizer ({u} : Set X)) :=
    calc Lu = pPrimeCoreOf 2 Lu ⊔ E := hLuEq
      _ ≤ oddCoreOf (centralizer ({u} : Set X)) ⊔ E := sup_le_sup_right hOLu E
      _ = E ⊔ oddCoreOf (centralizer ({u} : Set X)) := sup_comm _ _
  have huH : u ∈ H := hLH huL
  obtain ⟨J', hJ'H, hJ'int, hJ'two⟩ :=
    exists_isAhatIntr_subgroupOf_of_covered hu hLu hEC hEH hcov huH
  have hu' : orderOf (⟨u, huH⟩ : ↥H) = 2 := by rw [Subgroup.orderOf_mk]; exact hu
  have hJ'K : J'.subgroupOf H ≤ KProd ↥H := h.ihSub hH ⟨u, huH⟩ hu' _ (Or.inl hJ'int)
  have hEJ' : E ≤ J' := by
    rw [hE, oPrimeResidualOf_two_eq_oTwoPrimeOf, oTwoPrimeOf_le_iff]
    intro x hx h2
    have hxE : x ∈ E := by
      rw [hE, oPrimeResidualOf_two_eq_oTwoPrimeOf]
      exact mem_oTwoPrimeOf_of_twoElt hx h2
    have hxLu : x ∈ Lu := by
      have : E ≤ Lu := by rw [hLuEq]; exact le_sup_right
      exact this hxE
    obtain ⟨k, hk⟩ := h2
    exact hJ'two x (Subgroup.mem_inf.2 ⟨hxLu, hEH hxE⟩) ⟨k, hk⟩
  have hEW : E ≤ KProdIn H := by
    have h1 : J' ≤ KProdIn H := by
      have h2 := Subgroup.map_mono (f := H.subtype) hJ'K
      rwa [Subgroup.map_subgroupOf_eq_of_le hJ'H] at h2
    exact hEJ'.trans h1
  have hgen : primeResidual 2 ↥(L.subgroupOf H) = ⊤ := by
    have := (isPComponent_two_iff.1 hLpc).2
    have hq : IsTwoGenQuasi ↥L := (isTwoGenQuasi_subgroupOf_iff hLH').1 this
    exact (isTwoGenQuasi_congr_iff (Subgroup.subgroupOfEquivOfLe hLH)).2 hq |>.1
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOL : pPrimeCoreOf 2 L ≤ L := Subgroup.map_subtype_le _
  have hOodd : Odd (Nat.card ((pPrimeCoreOf 2 L).subgroupOf H)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hOL.trans hLH)).toEquiv]
    have h1 : Nat.card (pPrimeCoreOf 2 L) = Nat.card (pPrimeCore 2 ↥L) :=
      Subgroup.card_map_of_injective L.subtype_injective
    rw [h1]
    exact Nat.coprime_two_left.1 pPrimeCore_coprime_card
  have hEK : E.subgroupOf H ≤ KProd ↥H := by
    have h1 : E.subgroupOf H ≤ (KProdIn H).subgroupOf H := Subgroup.subgroupOf_mono H hEW
    have h2 : (KProdIn H).subgroupOf H = KProd ↥H := by
      unfold KProdIn
      exact Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
    rwa [h2] at h1
  have hsub : L.subgroupOf H ≤ KProd ↥H ⊔ (pPrimeCoreOf 2 L).subgroupOf H := by
    have h1 : L.subgroupOf H = (pPrimeCoreOf 2 L).subgroupOf H ⊔ E.subgroupOf H := by
      conv_lhs => rw [hLeq]
      exact Subgroup.subgroupOf_sup (hOL.trans hLH) hEH
    rw [h1, sup_comm]
    exact sup_le_sup_right hEK _
  have hLK := le_of_le_sup_odd_of_primeResidual (N := KProd ↥H) hOodd hgen hsub
  have h2 := Subgroup.map_mono (f := H.subtype) hLK
  rwa [Subgroup.map_subgroupOf_eq_of_le hLH] at h2

theorem centralizer_ne_top_of_involution {Y : Type} [Group Y] [IsSimpleGroup Y]
    (hnonab : ∃ a b : Y, a * b ≠ b * a) {s : Y} (hs : orderOf s = 2) :
    centralizer ({s} : Set Y) ≠ ⊤ := by
  intro htop
  have hc : s ∈ center Y := by
    have := Subgroup.centralizer_eq_top_iff_subset.1 htop
    simpa using this
  have hZ : center Y = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center Y) with h1 | h1
    · exact h1
    · exfalso
      obtain ⟨a, b, hab⟩ := hnonab
      exact hab (Subgroup.mem_center_iff.mp (by rw [h1]; exact Subgroup.mem_top b) a)
  rw [hZ, Subgroup.mem_bot] at hc
  rw [hc, orderOf_one] at hs
  exact absurd hs (by norm_num)

end Reduce

end CFSG.OddStandard.Solomon75
