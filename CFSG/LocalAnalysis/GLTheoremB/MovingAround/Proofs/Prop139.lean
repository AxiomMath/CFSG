module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Sec13d
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Sec13e
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma118R

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)
open CFSG.HardMathSupport.Solomon.LocalBalance (barAut barAut_mk barOf)
open scoped MatrixGroups
open Sec13d

namespace Prop139

@[expose] def InputRankOneOmega3 : Prop :=
  ∀ (ε : Bool) (n : ℕ) (X : Type) [Group X] [Finite X], 1 ≤ n → IsOmegaTwo ε (n + 1) X →
    HasFixedPointFreeOrder ε n 3 → CFSG.Open.pRank 3 (⊤ : Subgroup X) = 1 → IsAltType 5 X

@[expose] def InputOmegaPDvd : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (ε : Bool) (n : ℕ) (X : Type) [Group X] [Finite X],
    1 ≤ n → IsOmegaTwo ε (n + 1) X → HasFixedPointFreeOrder ε n p → p ∣ Nat.card X

variable {G : Type} [Group G] [Finite G]

@[expose] def BigComp (p : ℕ) (M D L : Subgroup G) : Prop :=
  GLAPComponent p (Istar p M D) L ∧ (3 < p ∨ 2 ≤ CFSG.Open.pRank p L)

@[expose] def SummandOf (p : ℕ) (M D L : Subgroup G) : Prop :=
  GLAPComponent p M L ∧ ¬ barX p M (gammaStar p D) ≤
    Subgroup.centralizer ((barX p M L : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) :
      Set (↥M ⧸ GLAPPrimeCore p ↥M))

@[expose] def KBig (p : ℕ) (M D T : Subgroup G) : Subgroup G :=
  ⨆ (L : Subgroup G) (_ : BigComp p M D L), derivedInf (Nof T ⊓ L)

@[expose] def FrattiniBoundStatement : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A D T : Subgroup G}
    (h : Sec13 G m p B M E A D T), CFSG.Open.pRank p (B ⊓ KBig p M D T) ≤ 1

theorem center_bot_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (hY : Subgroup.center Y = ⊥) : Subgroup.center X = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  rw [Subgroup.mem_center_iff] at hx
  have he : e x ∈ Subgroup.center Y := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨g', rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, hx g']
  rw [hY, Subgroup.mem_bot] at he
  exact e.injective (by rw [he, map_one])

theorem centre_barOf_bot {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {L : Subgroup G}
    (hpi : IsPiGroup p (↥L ⧸ CFSG.pCore 2 ↥L)) (hnh : ¬ IsHatSeven (↥L ⧸ CFSG.pCore 2 ↥L))
    (hPi : InputPiCenter) : Subgroup.center (barOf p L) = ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  have e1 : barOf p L ≃* (↥L ⧸ CFSG.pCore 2 ↥L) :=
    QuotientGroup.quotientMulEquivOfEq (glaPPrimeCore_eq_pCore_two hp hp2 hpi)
  exact center_bot_of_mulEquiv e1 (hPi _ p hp hp2 hpi hnh)

theorem piType_of_comp {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {L : Subgroup G}
    (hpi : IsPiGroup p (↥L ⧸ CFSG.pCore 2 ↥L)) (hnh : ¬ IsHatSeven (↥L ⧸ CFSG.pCore 2 ↥L))
    (hPi : InputPiCenter) :
    (∃ k : ℕ, 1 ≤ k ∧ IsAltType (k * p + 2) (barOf p L)) ∨
      (∃ (n : ℕ) (ε : Bool), 1 ≤ n ∧ IsOmegaTwo ε (n + 1) (barOf p L) ∧
        HasFixedPointFreeOrder ε n p) ∨
      (p = 3 ∧ Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ≃* alternatingGroup (Fin 7))) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have e1 : barOf p L ≃* (↥L ⧸ CFSG.pCore 2 ↥L) :=
    QuotientGroup.quotientMulEquivOfEq (glaPPrimeCore_eq_pCore_two hp hp2 hpi)
  have hZ : Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) = ⊥ := hPi _ p hp hp2 hpi hnh
  have eZ : (↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) ≃*
      (↥L ⧸ CFSG.pCore 2 ↥L) :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have e2 : barOf p L ≃* ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) :=
    e1.trans eZ.symm
  have hnt : Nontrivial ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) :=
    hpi.1.2.toNontrivial
  obtain ⟨-, -, hcases⟩ := hpi
  rcases hcases with ⟨k, ⟨f⟩⟩ | ⟨n, ε, hn, hΩ, hfpf⟩ | ⟨h3, ⟨f⟩⟩
  · refine Or.inl ⟨k, ?_, ⟨e2.trans f⟩⟩
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · exfalso
      subst h0
      have key : ∀ σ : Equiv.Perm (Fin 2), Equiv.Perm.sign σ = 1 → σ = 1 := by decide
      have hsub2 : Subsingleton (alternatingGroup (Fin 2)) :=
        ⟨fun a b => Subtype.ext ((key _ (Equiv.Perm.mem_alternatingGroup.1 a.2)).trans
          (key _ (Equiv.Perm.mem_alternatingGroup.1 b.2)).symm)⟩
      have hsub : ∀ n : ℕ, n = 2 → Subsingleton (alternatingGroup (Fin n)) := by
        rintro n rfl
        exact hsub2
      have hs := hsub (0 * p + 2) (by simp)
      have hX : Subsingleton ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) :=
        ⟨fun a b => f.injective (Subsingleton.elim _ _)⟩
      exact (not_nontrivial_iff_subsingleton.2 hX) hnt
    · exact h0
  · exact Or.inr (Or.inl ⟨n, ε, hn, isOmegaTwo_of_mulEquiv e2 hΩ, hfpf⟩)
  · exact Or.inr (Or.inr ⟨h3, ⟨eZ.symm.trans f⟩⟩)

theorem pRank_top_barOf (p : ℕ) [Fact p.Prime] (L : Subgroup G) :
    CFSG.Open.pRank p (⊤ : Subgroup (barOf p L)) = CFSG.Open.pRank p L := by
  have hN : ¬ p ∣ Nat.card (GLAPPrimeCore p ↥L) := not_dvd_card_pPrimeCore (Fact.out) L
  have h1 := CFSG.SectionRank.pRank_quotient_eq (GLAPPrimeCore p ↥L) hN
  exact h1.trans (CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := p) L).symm

theorem one_le_pRank_of_elem {p : ℕ} (hp : p.Prime) {X : Type} [Group X] [Finite X] {x : X}
    (hx : x ^ p = 1) (hx1 : x ≠ 1) : 1 ≤ CFSG.Open.pRank p (⊤ : Subgroup X) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hord : orderOf x = p := orderOf_eq_prime hx hx1
  have hE : IsElemAbelian p (Subgroup.zpowers x) := by
    refine ⟨inferInstance, fun y hy => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]
  have hcard : Nat.card (Subgroup.zpowers x) = p ^ 1 := by
    rw [Nat.card_zpowers, hord, pow_one]
  exact CFSG.SectionRank.le_pRank hp.one_lt le_top hE hcard

theorem pRank_top_alt {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hAlt : Lemma118R.Input10_6AltRank)
    {X : Type} [Group X] [Finite X] {k : ℕ} (hk : 1 ≤ k) (hX : IsAltType (k * p + 2) X) :
    CFSG.Open.pRank p (⊤ : Subgroup X) = k := by
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have h5 : 5 ≤ k * p + 2 := by nlinarith
  have hX' : IsAltType (k * p + 2) ↥(⊤ : Subgroup X) := by
    obtain ⟨e⟩ := hX
    exact ⟨(Subgroup.topEquiv).trans e⟩
  obtain ⟨h1, h2⟩ := hAlt (k * p + 2) p X ⊤ h5 hp hp2 hX'
  have hdiv : (k * p + 2) / p = k := by
    rw [show k * p + 2 = 2 + p * k by ring, Nat.add_mul_div_left _ _ (by omega : 0 < p),
      Nat.div_eq_of_lt (by omega : 2 < p)]
    simp
  rw [hdiv] at h1 h2
  apply le_antisymm
  · exact CFSG.SectionRank.pRank_le hp.one_lt (fun E _ hE => h1 E le_top hE)
  · obtain ⟨E, -, hEel, hcard⟩ := h2
    exact CFSG.SectionRank.le_pRank hp.one_lt le_top hEel hcard

theorem bInf_le_derivedInf {m p : ℕ} {B M E A D T : Subgroup G} (h : Sec13 G m p B M E A D T)
    (hL133 : Lemma133Statement) (hL137i : Lemma137_iStatement)
    (hL137ii : Lemma137_ii_iiiStatement) (hPi : InputPiCenter) (hAb : InputAbIdx2)
    (hNo7 : Lemma137_noA7Statement) {L : Subgroup G}
    (hL : GLAPComponent p (Istar p M D) L) (hL1 : 3 < p ∨ 2 ≤ CFSG.Open.pRank p L) :
    B ⊓ L ≤ derivedInf (Nof T ⊓ L) := by
  have hS : GLStanding G m p := h.standing
  have hp : p.Prime := hS.prime
  have hp2 : p ≠ 2 := hS.ne_two
  haveI : Fact p.Prime := ⟨hp⟩
  have h133 := (hL133 h).2 L hL
  have hBN : B ≤ Nof T := hL137i h
  have hBel : IsElemAbelian p B := h.bOne.1.1
  have h137 := hL137ii h hL hL1
  have hΩ : ∀ (ε : Bool) (n : ℕ), IsOmegaTwo ε (n + 1) (↥L ⧸ CFSG.pCore 2 ↥L) →
      (IsOmegaTwo ε (n + 1) ↥(barX p (Nof T) (Nof T ⊓ L)) ∨
        Nonempty (↥(barX p (Nof T) (Nof T ⊓ L)) ≃* ↥(StatedSp n (ZMod 2)))) := by
    intro ε n hX
    by_cases hc : barX p M T ≤ Subgroup.centralizer
        ((barX p M L : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) : Set (↥M ⧸ GLAPPrimeCore p ↥M))
    · exact Or.inl ((h137.2.2.2.1 ε n hX).1 hc)
    · exact Or.inr ((h137.2.2.2.1 ε n hX).2 hc)
  have hA : ∀ k : ℕ, IsAltType (k * p + 2) (↥L ⧸ CFSG.pCore 2 ↥L) →
      (IsAltType (k * p + 2) ↥(barX p (Nof T) (Nof T ⊓ L)) ∨
        Nonempty (↥(barX p (Nof T) (Nof T ⊓ L)) ≃* Equiv.Perm (Fin (k * p)))) := by
    intro k hX
    by_cases hc : barX p M T ≤ Subgroup.centralizer
        ((barX p M L : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) : Set (↥M ⧸ GLAPPrimeCore p ↥M))
    · exact Or.inl ((h137.2.2.2.2 k hX).1 hc)
    · exact Or.inr ((h137.2.2.2.2 k hX).2 hc)
  have hidx := index_pow_two_of_piType hPi hAb hp hp2 h133.1.2.1 h133.1.2.2
    (fun h3 => hNo7 h hL h3) hΩ hA
  intro x hx
  obtain ⟨hxB, hxL⟩ := Subgroup.mem_inf.1 hx
  exact mem_derivedInf_of_pow_eq_one hp hp2 h137.1 hidx (hBN hxB) hxL (hBel.2 x hxB)

theorem isElemAbelian_of_le_B {p : ℕ} {B E : Subgroup G} (hB : IsElemAbelian p B) (hE : E ≤ B) :
    IsElemAbelian p E :=
  isElemAbelian_of_comm_pow (fun x hx y hy => elemAbelian_comm hB (hE hx) (hE hy))
    (fun x hx => hB.2 x (hE hx))

theorem exists_nontriv_pRank {p : ℕ} (hp : p.Prime) {H : Subgroup G}
    (hH : 1 ≤ CFSG.Open.pRank p H) :
    ∃ E : Subgroup G, E ≤ H ∧ IsElemAbelian p E ∧ ∃ x ∈ E, x ≠ 1 := by
  obtain ⟨E, hEH, hEel, hcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt H
  refine ⟨E, hEH, hEel, ?_⟩
  by_contra hcon
  push_neg at hcon
  have hbot : E = ⊥ := (Subgroup.eq_bot_iff_forall E).2 hcon
  rw [hbot, Subgroup.card_bot] at hcard
  have h1 : 1 < p ^ CFSG.Open.pRank p H := Nat.one_lt_pow (by omega) hp.one_lt
  omega

theorem inf_comps_bot {m p : ℕ} {B M E A D T : Subgroup G} (h : Sec13 G m p B M E A D T)
    (hL133 : Lemma133Statement) (hPi : InputPiCenter) {L1 L2 : Subgroup G}
    (h1 : GLAPComponent p (Istar p M D) L1) (h2 : GLAPComponent p (Istar p M D) L2)
    (hne : L1 ≠ L2) : B ⊓ L1 ⊓ L2 = ⊥ := by
  have hS : GLStanding G m p := h.standing
  have hp : p.Prime := hS.prime
  have hp2 : p ≠ 2 := hS.ne_two
  haveI : Fact p.Prime := ⟨hp⟩
  have hBel : IsElemAbelian p B := h.bOne.1.1
  have hL1 := (hL133 h).2 L1 h1
  have hc1 : Subgroup.center (barOf p L1) = ⊥ :=
    centre_barOf_bot hp hp2 hL1.1.2.1 hL1.1.2.2 hPi
  have hX1 : IsComponentOf (barX p (Istar p M D) L1) ⊤ := h1.2.2.1
  have hX2 : IsComponentOf (barX p (Istar p M D) L2) ⊤ := h2.2.2.1
  have hne' : barX p (Istar p M D) L1 ≠ barX p (Istar p M D) L2 :=
    fun heq => hne (glaPComponent_unique h1 h2 heq)
  have hcomm : ⁅barX p (Istar p M D) L1, barX p (Istar p M D) L2⁆ = ⊥ :=
    Sec13e.commute_of_isComponentOf hX1 hX2 hne'
  have hcen : Subgroup.center ↥(barX p (Istar p M D) L1) = ⊥ :=
    center_bot_of_mulEquiv (quotEquivBarX hp h1.1 h1.2.1).symm hc1
  have hcm : ∀ a ∈ barX p (Istar p M D) L1, ∀ b ∈ barX p (Istar p M D) L2, a * b = b * a := by
    intro a ha b hb
    have hmem := Subgroup.commutator_mem_commutator ha hb
    rw [hcomm, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    exact hmem
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  obtain ⟨hx1, hxL2⟩ := Subgroup.mem_inf.1 hx
  obtain ⟨hxB, hxL1⟩ := Subgroup.mem_inf.1 hx1
  have hxI : x ∈ Istar p M D := h1.1 hxL1
  set y : ↥(Istar p M D) ⧸ GLAPPrimeCore p ↥(Istar p M D) :=
    QuotientGroup.mk' (GLAPPrimeCore p ↥(Istar p M D)) ⟨x, hxI⟩ with hy
  have hy1 : y ∈ barX p (Istar p M D) L1 :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hxL1)
  have hy2 : y ∈ barX p (Istar p M D) L2 :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hxL2)
  have hw : (⟨y, hy1⟩ : ↥(barX p (Istar p M D) L1)) ∈ Subgroup.center ↥(barX p (Istar p M D) L1) := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact hcm g.1 g.2 y hy2
  rw [hcen, Subgroup.mem_bot] at hw
  have hy_one : y = 1 := congrArg Subtype.val hw
  have hxO : (⟨x, hxI⟩ : ↥(Istar p M D)) ∈ GLAPPrimeCore p ↥(Istar p M D) :=
    (QuotientGroup.eq_one_iff _).1 hy_one
  have hxp : (⟨x, hxI⟩ : ↥(Istar p M D)) ^ p = 1 := by
    apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    exact hBel.2 x hxB
  have hdvd : orderOf (⟨x, hxI⟩ : ↥(Istar p M D)) ∣ p := orderOf_dvd_of_pow_eq_one hxp
  rcases (Nat.dvd_prime hp).1 hdvd with h1' | hpx
  · have h0 : (⟨x, hxI⟩ : ↥(Istar p M D)) = 1 := orderOf_eq_one_iff.1 h1'
    exact congrArg Subtype.val h0
  · exfalso
    have hord : orderOf (⟨⟨x, hxI⟩, hxO⟩ : ↥(GLAPPrimeCore p ↥(Istar p M D))) = p := by
      rw [← Subgroup.orderOf_coe]
      exact hpx
    have hdiv := orderOf_dvd_natCard (⟨⟨x, hxI⟩, hxO⟩ : ↥(GLAPPrimeCore p ↥(Istar p M D)))
    rw [hord] at hdiv
    exact not_dvd_card_pPrimeCore hp (Istar p M D) hdiv

theorem two_comps_false {m p : ℕ} {B M E A D T : Subgroup G} (h : Sec13 G m p B M E A D T)
    (hL133 : Lemma133Statement) (hL137i : Lemma137_iStatement) (hL137ii : Lemma137_ii_iiiStatement)
    (hPi : InputPiCenter) (hAb : InputAbIdx2) (hNo7 : Lemma137_noA7Statement)
    (hFB : FrattiniBoundStatement) {L1 L2 : Subgroup G} (h1 : BigComp p M D L1)
    (h2 : BigComp p M D L2) (hne : L1 ≠ L2) (hr1 : 1 ≤ CFSG.Open.pRank p L1)
    (hr2 : 1 ≤ CFSG.Open.pRank p L2) : False := by
  have hS : GLStanding G m p := h.standing
  have hp : p.Prime := hS.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hBel : IsElemAbelian p B := h.bOne.1.1
  have hBc : Nat.card B = p ^ GLATwoLocalRank p G := h.bOne.1.2.1
  have hsub : ∀ L : Subgroup G, BigComp p M D L → B ⊓ L ≤ KBig p M D T := fun L hL =>
    (bInf_le_derivedInf h hL133 hL137i hL137ii hPi hAb hNo7 hL.1 hL.2).trans
      (le_iSup₂ (f := fun L (_ : BigComp p M D L) => derivedInf (Nof T ⊓ L)) L hL)
  have hrk1 : CFSG.Open.pRank p (B ⊓ L1) = CFSG.Open.pRank p L1 := by
    obtain ⟨-, -, -, -, hr⟩ := (hL133 h).2 L1 h1.1
    exact hr
  have hrk2 : CFSG.Open.pRank p (B ⊓ L2) = CFSG.Open.pRank p L2 := by
    obtain ⟨-, -, -, -, hr⟩ := (hL133 h).2 L2 h2.1
    exact hr
  obtain ⟨E1, hE1B, hE1el, x1, hx1E1, hx1⟩ :=
    exists_nontriv_pRank hp (H := B ⊓ L1) (by rw [hrk1]; exact hr1)
  have hx1B : x1 ∈ B ⊓ L1 := hE1B hx1E1
  have hx1p : x1 ^ p = 1 := hE1el.2 x1 hx1E1
  have hord1 : orderOf x1 = p := orderOf_eq_prime hx1p hx1
  obtain ⟨E2, hE2B, hE2el, x2, hx2E2, hx2⟩ :=
    exists_nontriv_pRank hp (H := B ⊓ L2) (by rw [hrk2]; exact hr2)
  have hx2B : x2 ∈ B ⊓ L2 := hE2B hx2E2
  have hZ1 : Subgroup.zpowers x1 ≤ B ⊓ KBig p M D T :=
    Subgroup.zpowers_le.2 (Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hx1B).1, hsub L1 h1 hx1B⟩)
  have hZ2 : Subgroup.zpowers x2 ≤ B ⊓ KBig p M D T :=
    Subgroup.zpowers_le.2 (Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hx2B).1, hsub L2 h2 hx2B⟩)
  have hE'le : Subgroup.zpowers x1 ⊔ Subgroup.zpowers x2 ≤ B ⊓ KBig p M D T := sup_le hZ1 hZ2
  have hE'B : Subgroup.zpowers x1 ⊔ Subgroup.zpowers x2 ≤ B := hE'le.trans inf_le_left
  have hE'el := isElemAbelian_of_le_B hBel hE'B
  obtain ⟨k, hk⟩ : ∃ k : ℕ, Nat.card ↥(Subgroup.zpowers x1 ⊔ Subgroup.zpowers x2) = p ^ k := by
    have hdvd := Subgroup.card_dvd_of_le hE'B
    rw [hBc] at hdvd
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp).1 hdvd
    exact ⟨k, hk⟩
  have hkle : k ≤ CFSG.Open.pRank p (B ⊓ KBig p M D T) :=
    CFSG.SectionRank.le_pRank hp.one_lt hE'le hE'el hk
  have hk1 : k ≤ 1 := hkle.trans (hFB h)
  have hcardle : Nat.card ↥(Subgroup.zpowers x1 ⊔ Subgroup.zpowers x2) ≤
      Nat.card ↥(Subgroup.zpowers x1) := by
    rw [hk, Nat.card_zpowers, hord1]
    calc p ^ k ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos hk1
      _ = p := pow_one p
  have heq : Subgroup.zpowers x1 = Subgroup.zpowers x1 ⊔ Subgroup.zpowers x2 :=
    Subgroup.eq_of_le_of_card_ge le_sup_left hcardle
  have hx2Z : x2 ∈ Subgroup.zpowers x1 := by
    rw [heq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x2)
  have hx2L1 : x2 ∈ L1 := (Subgroup.zpowers_le.2 (Subgroup.mem_inf.1 hx1B).2) hx2Z
  have hbot := inf_comps_bot h hL133 hPi h1.1 h2.1 hne
  have hmem : x2 ∈ B ⊓ L1 ⊓ L2 :=
    Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hx2B).1, hx2L1⟩,
      (Subgroup.mem_inf.1 hx2B).2⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  exact hx2 hmem

end Prop139

open Prop139

theorem prop139_of_inputs (hL137i : Lemma137_iStatement) (hL137ii : Lemma137_ii_iiiStatement)
    (hL137iv : Lemma137_iv_vStatement) (hL138 : Lemma138Statement) (hL133 : Lemma133Statement)
    (hNo7 : Lemma137_noA7Statement) (hPi : InputPiCenter) (hAb : InputAbIdx2)
    (hAlt : Lemma118R.Input10_6AltRank) (hRank1 : InputRankOneOmega3)
    (hOmD : InputOmegaPDvd) (hFB : FrattiniBoundStatement) : Prop139Statement := by
  intro G _ _ m p B M E A D T h
  have hS : GLStanding G m p := h.standing
  have hp : p.Prime := hS.prime
  have hp2 : p ≠ 2 := hS.ne_two
  haveI : Fact p.Prime := ⟨hp⟩
  have hrk_le : ∀ L : Subgroup G, GLAPComponent p (Istar p M D) L → CFSG.Open.pRank p L ≤ 1 := by
    intro L hL
    by_contra hc
    have hbig : BigComp p M D L := ⟨hL, Or.inr (by omega)⟩
    have hsubL : B ⊓ L ≤ B ⊓ KBig p M D T :=
      le_inf inf_le_left ((bInf_le_derivedInf h hL133 hL137i hL137ii hPi hAb hNo7 hL hbig.2).trans
        (le_iSup₂ (f := fun L (_ : BigComp p M D L) => derivedInf (Nof T ⊓ L)) L hbig))
    have hmono := CFSG.SectionRank.pRank_mono hp.one_lt hsubL
    obtain ⟨-, -, -, -, hr⟩ := (hL133 h).2 L hL
    have hFB' := hFB h
    omega
  have hrk_ge : ∀ L : Subgroup G, GLAPComponent p (Istar p M D) L → 1 ≤ CFSG.Open.pRank p L := by
    intro L hL
    obtain ⟨⟨-, hpi, hnh⟩, -⟩ := (hL133 h).2 L hL
    rcases piType_of_comp hp hp2 hpi hnh hPi with ⟨k, hk1, hk⟩ | ⟨n, ε, hn, hΩ, hfpf⟩ | ⟨h3, hA7⟩
    · have hk' := pRank_top_alt hp hp2 hAlt hk1 hk
      rw [pRank_top_barOf] at hk'
      omega
    · have hdvd : p ∣ Nat.card (barOf p L) := hOmD p hp hp2 ε n _ hn hΩ hfpf
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
      have hx1 : x ≠ 1 := by
        intro h1
        rw [h1, orderOf_one] at hx
        exact hp.one_lt.ne hx
      rw [← pRank_top_barOf p L]
      exact one_le_pRank_of_elem hp (by have h := pow_orderOf_eq_one x; rwa [hx] at h) hx1
    · exact absurd hA7 (hNo7 h hL h3)
  by_cases hp3 : p = 3
  ·
    subst hp3
    refine Or.inr ⟨rfl, fun L hL => ?_⟩
    have hpr1 : CFSG.Open.pRank 3 L = 1 := le_antisymm (hrk_le L hL) (hrk_ge L hL)
    obtain ⟨⟨-, hpi, hnh⟩, -⟩ := (hL133 h).2 L hL
    rcases piType_of_comp hp hp2 hpi hnh hPi with ⟨k, hk1, hk⟩ | ⟨n, ε, hn, hΩ, hfpf⟩ | ⟨h3, hA7⟩
    · have hk' := pRank_top_alt hp hp2 hAlt hk1 hk
      rw [pRank_top_barOf, hpr1] at hk'
      subst hk'
      rw [one_mul] at hk
      exact hk
    · have hrk : CFSG.Open.pRank 3 (⊤ : Subgroup (barOf 3 L)) = 1 := by
        rw [pRank_top_barOf, hpr1]
      exact hRank1 ε n (barOf 3 L) hn hΩ hfpf hrk
    · exact absurd hA7 (hNo7 h hL rfl)
  ·
    have hp3' : 3 < p := by
      have := hp.two_le
      by_contra hc
      have h23 : p = 2 ∨ p = 3 := by omega
      rcases h23 with h2 | h3
      · exact hp2 h2
      · exact hp3 h3
    have hIof : Iof p M D ≠ ⊥ := (hL133 h).1
    obtain ⟨L0, hL0, hL0ne⟩ : ∃ L0 : Subgroup G, SummandOf p M D L0 ∧ L0 ≠ ⊥ := by
      by_contra hno
      apply hIof
      unfold Iof
      rw [iSup₂_eq_bot]
      intro L0 hL0
      by_contra hne
      exact hno ⟨L0, hL0, hne⟩
    have hIstarM : Istar p M D ≤ M := istar_le_M p M D
    have hsumle : ∀ L : Subgroup G, SummandOf p M D L → L ≤ Iof p M D := fun L hL => by
      unfold Iof
      exact le_iSup₂_of_le L hL le_rfl
    have hIof_le : Iof p M D ≤ Istar p M D := by
      unfold Istar
      exact le_iSup₂_of_le (1 : G) M.one_mem (le_of_eq (gLBConj_one _).symm)
    have hsumcomp : ∀ L : Subgroup G, SummandOf p M D L → GLAPComponent p (Istar p M D) L :=

      fun L hL => glaPComponent_of_le hp hL.1 ((hsumle L hL).trans hIof_le) hIstarM
    have hL0I : GLAPComponent p (Istar p M D) L0 := hsumcomp L0 hL0
    have huniq : ∀ L : Subgroup G, GLAPComponent p (Istar p M D) L → L = L0 := by
      intro L hL
      by_contra hne
      exact two_comps_false h hL133 hL137i hL137ii hPi hAb hNo7 hFB
        (L1 := L) (L2 := L0) ⟨hL, Or.inl hp3'⟩ ⟨hL0I, Or.inl hp3'⟩ hne
        (hrk_ge L hL) (hrk_ge L0 hL0I)
    have hIof_eq : Iof p M D = L0 := by
      apply le_antisymm
      · unfold Iof
        refine iSup₂_le fun L hL => ?_
        exact (huniq L (hsumcomp L hL)).le
      · exact hsumle L0 hL0
    have hIstar_eq : Istar p M D = L0 := by
      apply le_antisymm
      · unfold Istar
        refine iSup₂_le fun g hg => ?_
        rw [hIof_eq]
        have hL0le : L0 ≤ Istar p M D := (hsumle L0 hL0).trans hIof_le
        have hgL0 : GLBConj g L0 ≤ Istar p M D :=
          (gLBConj_mono g hL0le).trans (istar_conj_le p hg)
        have hgc : GLAPComponent p (Istar p M D) (GLBConj g L0) :=
          glaPComponent_of_le hp (glaPComponent_conj_mem hL0.1 hg) hgL0 hIstarM
        exact (huniq _ hgc).le
      · exact (hsumle L0 hL0).trans hIof_le
    have hpr1 : CFSG.Open.pRank p L0 = 1 := le_antisymm (hrk_le L0 hL0I) (hrk_ge L0 hL0I)
    have htype : IsAltType (p + 2) (barOf p L0) ∨
        ∃ (ε : Bool) (n : ℕ), 1 ≤ n ∧ IsOmegaTwo ε (n + 1) (barOf p L0) ∧
          HasFixedPointFreeOrder ε n p := by
      obtain ⟨⟨-, hpi, hnh⟩, -⟩ := (hL133 h).2 L0 hL0I
      rcases piType_of_comp hp hp2 hpi hnh hPi with ⟨k, hk1, hk⟩ | ⟨n, ε, hn, hΩ, hfpf⟩ | ⟨h3, hA7⟩
      · have hk' := pRank_top_alt hp hp2 hAlt hk1 hk
        rw [pRank_top_barOf, hpr1] at hk'
        subst hk'
        left
        rw [one_mul] at hk
        exact hk
      · exact Or.inr ⟨ε, n, hn, hΩ, hfpf⟩
      · exact absurd h3 (by omega)
    refine Or.inl ⟨hp3', hIof_eq.trans hIstar_eq.symm, L0, ?_, hIof_eq, hpr1, htype⟩
    rw [hIof_eq.trans hIstar_eq.symm]
    exact hL0I

end CFSG.LocalAnalysis.GLTheoremB.MovingAround
