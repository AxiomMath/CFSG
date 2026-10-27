module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Thm11CaseA
public import CFSG.LocalAnalysis.OddStandard.Solomon75Thm11Mono
public import CFSG.LocalAnalysis.OddStandard.Solomon75Thm11Quot

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS

structure SolMinCEx (X : Type) [Group X] [Finite X] : Prop where
  ih : ∀ (Y : Type) [Group Y] [Finite Y], Nat.card Y < Nat.card X → SolomonThm11At Y
  witness : ∃ (t : X) (L : Subgroup X), orderOf t = 2 ∧ (IsAhatIntr X t L ∨ IsMLIntr X t L) ∧
    ¬ L ≤ KProd X

structure SolCEx (X : Type) [Group X] [Finite X] : Prop extends SolMinCEx X where
  simple : IsSimpleGroup X
  nonabelian : ∃ a b : X, a * b ≠ b * a

@[expose] def SolLemma31 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], SolMinCEx X → IsSimpleGroup X

section MinCEx

variable {X : Type} [Group X] [Finite X]

theorem SolMinCEx.not_thm11At (h : SolMinCEx X) : ¬ SolomonThm11At X := by
  obtain ⟨t, L, ht, hL, hnot⟩ := h.witness
  exact fun h' => hnot (h' t ht L hL)

theorem SolMinCEx.ihSub (h : SolMinCEx X) {H : Subgroup X} (hH : H ≠ ⊤) : SolomonThm11At ↥H := by
  refine h.ih ↥H ?_
  have hdvd : Nat.card H ∣ Nat.card X := Subgroup.card_subgroup_dvd_card H
  refine lt_of_le_of_ne (Nat.le_of_dvd Nat.card_pos hdvd) fun heq => hH ?_
  exact (Subgroup.card_eq_iff_eq_top H).1 heq

theorem SolMinCEx.ihQuot (h : SolMinCEx X) {N : Subgroup X} [N.Normal] (hN : N ≠ ⊥) :
    SolomonThm11At (X ⧸ N) := by
  refine h.ih (X ⧸ N) ?_
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup N
  have hpos : 1 < Nat.card N := by
    have h1 : Nat.card N ≠ 1 := fun h1 => hN (Subgroup.card_eq_one.1 h1)
    have : 0 < Nat.card N := Nat.card_pos
    omega
  have hXpos : 0 < Nat.card (X ⧸ N) := Nat.card_pos
  rw [hcard]
  nlinarith

theorem SolMinCEx.le_KProdIn (h : SolMinCEx X) {H : Subgroup X} (hH : H ≠ ⊤) {t : X}
    (ht : orderOf t = 2) (htH : t ∈ H) {L : Subgroup X} (hLH : L ≤ H)
    (hL : IsAhatIntr X t L ∨ IsMLIntr X t L) : L ≤ KProdIn H :=
  (h.ihSub hH).le_KProdIn ht htH hLH hL

theorem SolMinCEx.pPrimeCore_eq_bot (h : SolMinCEx X) : pPrimeCore 2 X = ⊥ := by
  by_contra hne
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : Odd (Nat.card (pPrimeCore 2 X)) :=
    Nat.coprime_two_left.1 pPrimeCore_coprime_card
  exact h.not_thm11At (solomonThm11At_of_odd_quotient hodd (h.ihQuot hne))

omit [Finite X] in
theorem nonabelian_of_isTwoGenQuasi {L : Subgroup X} (h : IsTwoGenQuasi ↥L) :
    ∃ a b : X, a * b ≠ b * a := by
  by_contra hcomm
  push Not at hcomm
  obtain ⟨a, b, hab⟩ := h.2.2.2
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
  exact hab (congrArg (fun z : ↥L => (((z : ↥L ⧸ pPrimeCore 2 ↥L) :
    (↥L ⧸ pPrimeCore 2 ↥L) ⧸ center (↥L ⧸ pPrimeCore 2 ↥L)))) (Subtype.ext (hcomm x y)))

theorem SolMinCEx.nonabelian (h : SolMinCEx X) : ∃ a b : X, a * b ≠ b * a := by
  obtain ⟨t, L, -, hL, -⟩ := h.witness
  exact nonabelian_of_isTwoGenQuasi
    (hL.elim isTwoGenQuasi_of_isAhatIntr isTwoGenQuasi_of_isMLIntr)

theorem SolMinCEx.le_KProd_of_le_subnormal (h : SolMinCEx X) {N : Subgroup X}
    (hNs : N.IsSubnormal) (hN : N ≠ ⊤) {t : X} (ht : orderOf t = 2) (htN : t ∈ N)
    {L : Subgroup X} (hLN : L ≤ N) (hL : IsAhatIntr X t L ∨ IsMLIntr X t L) : L ≤ KProd X :=
  (h.le_KProdIn hN ht htN hLN hL).trans (KProdIn_le_KProd_of_subnormal hNs)

theorem SolMinCEx.solCEx (h : SolMinCEx X) (hs : IsSimpleGroup X) : SolCEx X :=
  { h with simple := hs, nonabelian := h.nonabelian }

end MinCEx

section LComp

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem not_isSolvable_of_isTwoGenQuasi {L : Subgroup X} (h : IsTwoGenQuasi ↥L) :
    ¬ Group.IsSolvable ↥L := by
  intro hs
  have h1 : Group.IsSolvable ((↥L ⧸ pPrimeCore 2 ↥L) ⧸ center (↥L ⧸ pPrimeCore 2 ↥L)) :=
    inferInstance
  have : IsSimpleGroup ((↥L ⧸ pPrimeCore 2 ↥L) ⧸ center (↥L ⧸ pPrimeCore 2 ↥L)) := h.2.2.1
  obtain ⟨a, b, hab⟩ := h.2.2.2
  exact hab (IsSimpleGroup.comm_iff_isSolvable.2 h1 a b)

theorem IsAhatIntr.isLComp {t : X} (ht : orderOf t = 2) {L : Subgroup X}
    (h : IsAhatIntr X t L) : IsLComp X L :=
  ⟨⟨t, ht, h.1, h.2.2.1⟩, not_isSolvable_of_isTwoGenQuasi (isTwoGenQuasi_of_isAhatIntr h)⟩

end LComp

section MaxDeg

variable {X : Type} [Group X] [Finite X]

theorem natCard_eq_factorial_of_isDoubleCoverOfAlt {K : Type} [Group K] [Finite K] {m : ℕ}
    (hm : 2 ≤ m) (h : IsDoubleCoverOfAlt K m) : Nat.card K = m.factorial := by
  obtain ⟨-, hc, ⟨e⟩⟩ := h
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (center K)
  have hnt : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.2 hm
  have h2 : Nat.card (K ⧸ center K) = m.factorial / 2 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
      Fintype.card_fin]
  rw [h1, hc, h2]
  exact Nat.div_mul_cancel (Nat.dvd_factorial two_pos hm)

theorem le_natCard_of_isDoubleCoverOfAlt_quotient {L : Subgroup X} {m : ℕ} (hm : 2 ≤ m)
    (h : IsDoubleCoverOfAlt (L ⧸ pPrimeCore 2 L) m) : m ≤ Nat.card X := by
  have h1 : m ≤ Nat.card (L ⧸ pPrimeCore 2 L) := by
    rw [natCard_eq_factorial_of_isDoubleCoverOfAlt hm h]
    exact Nat.self_le_factorial m
  refine h1.trans ((Nat.card_le_card_of_surjective _ QuotientGroup.mk_surjective).trans ?_)
  exact Subgroup.card_le_card_group L

theorem exists_isMaxAhatDeg_of_isAhatIntr {t : X} {L : Subgroup X} (ht : orderOf t = 2)
    (h : IsAhatIntr X t L) : ∃ n, IsMaxAhatDeg X n := by
  obtain ⟨n, hn, hcov⟩ := h.2.2.2
  let S : Set ℕ := {m | 8 ≤ m ∧ ∃ (t : X) (L : Subgroup X), orderOf t = 2 ∧ IsAhatIntr X t L ∧
    IsDoubleCoverOfAlt (L ⧸ pPrimeCore 2 L) m}
  have hne : S.Nonempty := ⟨n, hn, t, L, ht, h, hcov⟩
  have hbdd : BddAbove S := by
    refine ⟨Nat.card X, fun m hm => ?_⟩
    obtain ⟨hm8, t', L', -, -, hc⟩ := hm
    exact le_natCard_of_isDoubleCoverOfAlt_quotient (by omega) hc
  have hmem : sSup S ∈ S := Nat.sSup_mem hne hbdd
  exact ⟨sSup S, hmem.1, hmem.2, fun m t' L' hm ht' hL' hc =>
    le_csSup hbdd ⟨hm, t', L', ht', hL', hc⟩⟩

theorem IsMLIntr.exists_isAhatIntr {t : X} {M : Subgroup X} (h : IsMLIntr X t M) :
    ∃ (s : X) (J : Subgroup X), orderOf s = 2 ∧ IsAhatIntr X s J := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq := isTwoGenQuasi_of_isMLIntr h
  have hnt : Nontrivial ↥M := by
    by_contra hnot
    rw [not_nontrivial_iff_subsingleton] at hnot
    obtain ⟨a, b, hab⟩ := hq.2.2.2
    exact hab (Subsingleton.elim (a * b) (b * a))
  have hdvd : 2 ∣ Nat.card ↥M := by
    by_contra hnd
    have hcop : Nat.Coprime 2 (Nat.card ↥M) := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hnd
    have h1 := CFSG.ComponentClassification.CatalogueBPrimeJoin.primeResidual_eq_bot_of_coprime_card
      (G := ↥M) 2 hcop
    rw [hq.1] at h1
    exact top_ne_bot h1
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  have hx2 : orderOf (x : X) = 2 := by rw [Subgroup.orderOf_coe]; exact hx
  obtain ⟨J, hJ, -⟩ := h.2.2.2 (x : X) x.2 hx2
  exact ⟨x, J, hx2, hJ⟩

theorem SolMinCEx.exists_isMaxAhatDeg (h : SolMinCEx X) : ∃ n, IsMaxAhatDeg X n := by
  obtain ⟨t, L, ht, hL, -⟩ := h.witness
  rcases hL with hL | hL
  · exact exists_isMaxAhatDeg_of_isAhatIntr ht hL
  · obtain ⟨s, J, hs, hJ⟩ := hL.exists_isAhatIntr
    exact exists_isMaxAhatDeg_of_isAhatIntr hs hJ

end MaxDeg

theorem solomonThm11_of_cases (h31 : SolLemma31)
    (h3 : ∀ (X : Type) [Group X] [Finite X], SolCEx X → HypA X → False)
    (h4 : ∀ (X : Type) [Group X] [Finite X], SolCEx X → ¬ HypA X → False) :
    SolomonThm11 := by
  have key : ∀ (N : ℕ) (X : Type) [Group X] [Finite X], Nat.card X = N → SolomonThm11At X := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      intro X _ _ hN
      by_contra hfail
      have hmin : SolMinCEx X := by
        refine ⟨fun Y _ _ hY => ih (Nat.card Y) (hN ▸ hY) Y rfl, ?_⟩
        by_contra hw
        apply hfail
        intro t ht L hL
        by_contra hnot
        exact hw ⟨t, L, ht, hL, hnot⟩
      have hcex : SolCEx X := hmin.solCEx (h31 X hmin)
      by_cases hA : HypA X
      · exact h3 X hcex hA
      · exact h4 X hcex hA
  exact fun X _ _ => key _ X rfl

end CFSG.OddStandard.Solomon75
