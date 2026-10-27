module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.SchurFacts
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims126

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open scoped MatrixGroups commutatorElement

section NotL227

theorem card_quot_center_of_L227 {X : Type} [Group X] [Finite X] (hX : IsLTwoTwentySeven X) :
    Nat.card (X ⧸ Subgroup.center X) = 9828 := by
  obtain ⟨e⟩ := hX
  have hcard : Nat.card X = 9828 :=
    (Nat.card_congr e.toEquiv).trans CFSG.RankThree.PartTwo.KFacts.card_psl2_27
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK : 4 ≤ Nat.card (GaloisField 3 3) := by
    rw [GaloisField.card 3 3 (by norm_num)]
    norm_num
  haveI : IsSimpleGroup PSL(2, GaloisField 3 3) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hK
  haveI : IsSimpleGroup X := e.isSimpleGroup_congr.2 inferInstance
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ : Subgroup.center X = ⊥ := by
    rcases (inferInstance : (Subgroup.center X).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := X) 2 (by rw [hcard]; norm_num)
      have hn : (Subgroup.zpowers g).Normal := by
        refine ⟨fun n hn k => ?_⟩
        have hc : n ∈ Subgroup.center X := h ▸ Subgroup.mem_top n
        have h1 : k * n = n * k := (Subgroup.mem_center_iff.1 hc k)
        rw [h1, mul_inv_cancel_right]
        exact hn
      rcases hn.eq_bot_or_eq_top with h1 | h1
      · have : g ∈ Subgroup.zpowers g := Subgroup.mem_zpowers g
        rw [h1, Subgroup.mem_bot] at this
        rw [this, orderOf_one] at hg
        omega
      · have h2 := Nat.card_zpowers g
        rw [h1, Subgroup.card_top, hcard, hg] at h2
        omega
  rw [hZ]
  exact (Nat.card_congr (QuotientGroup.quotientBot : X ⧸ (⊥ : Subgroup X) ≃* X).toEquiv).trans hcard

theorem not_isAltType_of_card {Y : Type} [Group Y] (hY : Nat.card Y = 9828) {n : ℕ} (hn : 5 ≤ n) :
    ¬ IsAltType n Y := by
  rintro ⟨f⟩
  have h1 := (Nat.card_congr f.toEquiv).symm.trans hY
  rw [Prop126b.card_alt' n (by omega)] at h1
  have h5 : 5 ∣ n.factorial := Nat.dvd_factorial (by norm_num) hn
  have h2 : 2 ∣ n.factorial := Nat.dvd_factorial (by norm_num) (by omega)
  have h5' : 5 ∣ n.factorial / 2 := by
    obtain ⟨k, hk⟩ := h2
    rw [hk, Nat.mul_div_cancel_left k (by norm_num)]
    rw [hk] at h5
    exact (Nat.Coprime.dvd_mul_left (by norm_num : Nat.Coprime 5 2)).1 h5
  rw [h1] at h5'
  omega

theorem not_isLpType_two_seven_of_card {Y : Type} [Group Y] (hY : Nat.card Y = 9828) :
    ¬ IsLpType 2 7 Y := by
  rintro ⟨F, hF, hfin, hcF, ⟨f⟩⟩
  letI := hF
  haveI := hfin
  have h1 : Nat.card (StatedProj (StatedSL 2 F)) ∣ Nat.card (StatedSL 2 F) :=
    Subgroup.card_quotient_dvd_card _
  rw [CFSG.Open.StatedAPI.card_statedSL_two F, hcF] at h1
  have h2 := (Nat.card_congr f.toEquiv).symm.trans hY
  rw [h2] at h1
  have := Nat.le_of_dvd (by norm_num) h1
  omega

theorem not_isSporType_He_of_card {Y : Type} [Group Y] (hY : Nat.card Y = 9828) :
    ¬ IsSporType .He Y := by
  rintro ⟨f⟩
  have hP : Nat.card (PresentedGroup TauCeti.Sporadic.hePresentation.relatorSet) = 9828 := by
    rw [← hY]
    exact (Nat.card_congr f.toEquiv).symm
  have hgc : TauCeti.Sporadic.hePresentation.generatorCount = 2 := by
    simp [TauCeti.GroupPresentation.generatorCount]
  let i0 : Fin TauCeti.Sporadic.hePresentation.generatorCount := ⟨0, by rw [hgc]; norm_num⟩
  let i1 : Fin TauCeti.Sporadic.hePresentation.generatorCount := ⟨1, by rw [hgc]; norm_num⟩
  have hrel : ∀ t ∈ TauCeti.Sporadic.hePresentation.transcribed,
      PresentedGroup.mk TauCeti.Sporadic.hePresentation.relatorSet t.toFreeGroup = 1 := by
    intro t ht
    exact PresentedGroup.one_of_mem
      ((TauCeti.GroupPresentation.mem_relatorSet_iff _ _).2 ⟨t, ht, rfl⟩)
  set α : PresentedGroup TauCeti.Sporadic.hePresentation.relatorSet :=
    PresentedGroup.mk _ (FreeGroup.of i0) with hα
  set β : PresentedGroup TauCeti.Sporadic.hePresentation.relatorSet :=
    PresentedGroup.mk _ (FreeGroup.of i1) with hβ
  have hα2 : α ^ 2 = 1 := by
    have := hrel (.pow (.gen i0) 2) (by
      rw [TauCeti.Sporadic.hePresentation_transcribed]
      exact List.mem_cons_self)
    rw [TauCeti.Relator.toFreeGroup_pow, TauCeti.Relator.toFreeGroup_gen, map_pow] at this
    exact this
  have hβ7 : β ^ 7 = 1 := by
    have := hrel (.pow (.gen i1) 7) (by
      rw [TauCeti.Sporadic.hePresentation_transcribed]
      exact List.mem_cons_of_mem _ List.mem_cons_self)
    rw [TauCeti.Relator.toFreeGroup_pow, TauCeti.Relator.toFreeGroup_gen, map_pow] at this
    exact this
  have hαβ : (α * β) ^ 17 = 1 := by
    have := hrel (.pow (.mul (.gen i0) (.gen i1)) 17) (by
      rw [TauCeti.Sporadic.hePresentation_transcribed]
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    rw [TauCeti.Relator.toFreeGroup_pow, TauCeti.Relator.toFreeGroup_mul,
      TauCeti.Relator.toFreeGroup_gen, TauCeti.Relator.toFreeGroup_gen, map_pow, map_mul] at this
    exact this
  have hord : orderOf (α * β) = 1 := by
    have h1 : orderOf (α * β) ∣ 17 := orderOf_dvd_of_pow_eq_one hαβ
    have h2 : orderOf (α * β) ∣ 9828 := hP ▸ orderOf_dvd_natCard (α * β)
    have h3 : orderOf (α * β) ∣ Nat.gcd 17 9828 := Nat.dvd_gcd h1 h2
    have h4 : Nat.gcd 17 9828 = 1 := by norm_num
    rw [h4] at h3
    exact Nat.dvd_one.1 h3
  have hab : α * β = 1 := orderOf_eq_one_iff.1 hord
  have hb : β = α⁻¹ := eq_inv_of_mul_eq_one_right hab
  have ha1 : α = 1 := by
    have h7 : α⁻¹ ^ 7 = 1 := hb ▸ hβ7
    have h7' : α ^ 7 = 1 := by
      rw [inv_pow] at h7
      exact inv_eq_one.1 h7
    calc α = α ^ 7 * (α ^ 2)⁻¹ ^ 3 := by group
      _ = 1 := by rw [h7', hα2]; group
  have hb1 : β = 1 := by rw [hb, ha1, inv_one]
  have htop : (⊤ : Subgroup (PresentedGroup TauCeti.Sporadic.hePresentation.relatorSet)) ≤ ⊥ := by
    rw [← PresentedGroup.closure_range_of, Subgroup.closure_le]
    rintro _ ⟨⟨v, hv⟩, rfl⟩
    have hv2 : v < 2 := hgc ▸ hv
    interval_cases v
    · exact (Subgroup.mem_bot).2 ha1
    · exact (Subgroup.mem_bot).2 hb1
  have hsub : Subsingleton (PresentedGroup TauCeti.Sporadic.hePresentation.relatorSet) := by
    refine ⟨fun x y => ?_⟩
    have hx := htop (Subgroup.mem_top x)
    have hy := htop (Subgroup.mem_top y)
    rw [Subgroup.mem_bot] at hx hy
    rw [hx, hy]
  rw [Nat.card_unique] at hP
  omega

theorem notL227_holds : Prop126b.NotL227 := by
  intro X _ _ hX
  have h := card_quot_center_of_L227 hX
  exact ⟨fun n hn => not_isAltType_of_card h hn, not_isSporType_He_of_card h,
    not_isLpType_two_seven_of_card h⟩

end NotL227

section Generic

theorem nontrivial_of_isQuasisimple {Q : Type*} [Group Q] (hq : CFSG.Open.IsQuasisimple Q) :
    Nontrivial Q := by
  haveI : Nontrivial (Q ⧸ Subgroup.center Q) := hq.2.toNontrivial
  exact (QuotientGroup.mk_surjective (s := Subgroup.center Q)).nontrivial

theorem not_isPGroup_of_isQuasisimple {Q : Type*} [Group Q] [Finite Q] {p : ℕ} (hp : p.Prime)
    (hq : CFSG.Open.IsQuasisimple Q) : ¬ IsPGroup p Q := by
  intro hP
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := hP.isNilpotent
  haveI := nontrivial_of_isQuasisimple hq
  have := IsSolvable.commutator_lt_top_of_nontrivial Q
  rw [hq.1] at this
  exact lt_irrefl _ this

theorem eq_bot_of_perfect_of_le_solvable {G : Type*} [Group G] {Q H : Subgroup G}
    (hperf : ⁅Q, Q⁆ = Q) (hQH : Q ≤ H) (hH : Group.IsSolvable ↥H) : Q = ⊥ := by
  haveI : Group.IsSolvable ↥Q := solvable_of_solvable_injective (Subgroup.inclusion_injective hQH)
  by_contra hne
  haveI : Nontrivial ↥Q := (Subgroup.nontrivial_iff_ne_bot _).2 hne
  have h1 := IsSolvable.commutator_lt_top_of_nontrivial ↥Q
  have h2 : commutator ↥Q = ⊤ := Group.isPerfect_def.1 (Subgroup.isPerfect_iff.2 hperf)
  rw [h2] at h1
  exact lt_irrefl _ h1

theorem isQuasisimple_of_simple {J : Type*} [Group J] (hs : IsSimpleGroup J)
    (hnc : ∃ x y : J, x * y ≠ y * x) : CFSG.Open.IsQuasisimple J := by
  have hZ : Subgroup.center J = ⊥ := by
    rcases (inferInstance : (Subgroup.center J).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      obtain ⟨x, y, hxy⟩ := hnc
      have hx : x ∈ Subgroup.center J := h ▸ Subgroup.mem_top x
      exact hxy ((Subgroup.mem_center_iff.1 hx y).symm)
  refine ⟨?_, ?_⟩
  · rcases (inferInstance : (commutator J).Normal).eq_bot_or_eq_top with h | h
    · exfalso
      obtain ⟨x, y, hxy⟩ := hnc
      apply hxy
      have hm : ⁅x, y⁆ ∈ commutator J := Subgroup.commutator_mem_commutator
        (Subgroup.mem_top x) (Subgroup.mem_top y)
      rw [h, Subgroup.mem_bot] at hm
      exact commutatorElement_eq_one_iff_mul_comm.1 hm
    · exact h
  · exact ((QuotientGroup.quotientMulEquivOfEq hZ).trans
      (QuotientGroup.quotientBot : J ⧸ (⊥ : Subgroup J) ≃* J)).isSimpleGroup_congr.2 hs

theorem glaPComponent_of_simple_normal {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {X J : Subgroup G} (hJX : J ≤ X) (hn : (J.subgroupOf X).Normal) (hs : IsSimpleGroup ↥J)
    (hnc : ∃ x y : ↥J, x * y ≠ y * x) (hpJ : p ∣ Nat.card ↥J) : GLAPComponent p X J := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hsn : IsSubnormal J X := IsSubnormal.step hJX hn (IsSubnormal.refl X)
  have hcore : GLAPPrimeCore p ↥J = ⊥ := by
    rcases (GLAPPrimeCore.normal p ↥J).eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      have hcop : Nat.Coprime p (Nat.card ↥(GLAPPrimeCore p ↥J)) := CFSG.pPrimeCore_coprime_card
      rw [h, Subgroup.card_top] at hcop
      exact (Nat.Prime.coprime_iff_not_dvd hp).1 hcop hpJ
  have hqJ : CFSG.Open.IsQuasisimple ↥J := isQuasisimple_of_simple hs hnc
  have e : (↥J ⧸ GLAPPrimeCore p ↥J) ≃* ↥J :=
    (QuotientGroup.quotientMulEquivOfEq hcore).trans QuotientGroup.quotientBot
  have hqbar : CFSG.Open.IsQuasisimple ↥(barX p X J) :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv
      (e.symm.trans (quotEquivBarX hp hJX hsn)) hqJ
  refine ⟨hJX, hsn, ⟨le_top, ?_, hqbar⟩, ?_⟩
  · have := isSubnormal_barX (C := X) p hsn
    rwa [barX_self] at this
  · intro J' hlt hsn' heq
    have hJ'J : IsSubnormal J' J := isSubnormal_of_le_of_le hsn' hlt.le hJX
    rcases CFSG.Open.IsSubnormal.eq_bot_or_eq_of_isSimpleGroup hJ'J hs with h | h
    · subst h
      have hne : barX p X J ≠ ⊥ :=
        (Subgroup.nontrivial_iff_ne_bot _).1 (nontrivial_of_isQuasisimple hqbar)
      apply hne
      unfold barX
      rw [← heq, Subgroup.bot_subgroupOf, Subgroup.map_bot]
    · exact hlt.ne h

end Generic

section PermFacts

open Equiv Equiv.Perm

variable {α : Type} [Fintype α] [DecidableEq α]

@[expose] def altOn (s : Finset α) : Subgroup (Perm α) :=
  (alternatingGroup.ofSubtype s).range.map (alternatingGroup α).subtype

theorem mem_altOn {s : Finset α} {g : Perm α} :
    g ∈ altOn s ↔ g ∈ alternatingGroup α ∧ g.support ⊆ s := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k.2, (alternatingGroup.mem_range_ofSubtype_iff s k).1 hk⟩
  · rintro ⟨hA, hs⟩
    exact ⟨⟨g, hA⟩, (alternatingGroup.mem_range_ofSubtype_iff s ⟨g, hA⟩).2 hs, rfl⟩

@[expose] noncomputable def altOnEquiv (s : Finset α) : ↥(altOn s) ≃* ↥(alternatingGroup (Fin s.card)) :=
  ((((alternatingGroup.ofSubtype s).range).equivMapOfInjective _
      (alternatingGroup α).subtype_injective).symm.trans
    (MonoidHom.ofInjective (alternatingGroup.ofSubtype_injective (s := s))).symm).trans
    (Equiv.altCongrHom s.equivFin)

theorem isSimpleGroup_altOn {s : Finset α} (h5 : 5 ≤ s.card) : IsSimpleGroup ↥(altOn s) :=
  (altOnEquiv s).isSimpleGroup_congr.2
    (alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; exact h5))

theorem isSolvable_altOn {s : Finset α} (h4 : s.card ≤ 4) : Group.IsSolvable ↥(altOn s) := by
  haveI : Group.IsSolvable ↥(alternatingGroup (Fin s.card)) :=
    alternatingGroup.isSolvable (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; exact h4)
  exact solvable_of_surjective (f := (altOnEquiv s).symm.toMonoidHom) (altOnEquiv s).symm.surjective

theorem card_altOn {s : Finset α} (h2 : 2 ≤ s.card) :
    Nat.card ↥(altOn s) = s.card.factorial / 2 := by
  rw [Nat.card_congr (altOnEquiv s).toEquiv, Prop126b.card_alt' _ h2]

theorem altOn_noncomm {s : Finset α} (h5 : 5 ≤ s.card) : ∃ x y : ↥(altOn s), x * y ≠ y * x := by
  by_contra hcon
  push Not at hcon
  have hc : commutator ↥(alternatingGroup (Fin s.card)) = ⊤ :=
    commutator_alternatingGroup_eq_top (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; exact h5)
  have hab : ∀ x y : ↥(alternatingGroup (Fin s.card)), x * y = y * x := by
    intro x y
    have h := congrArg (altOnEquiv s) (hcon ((altOnEquiv s).symm x) ((altOnEquiv s).symm y))
    simpa using h
  have hbot : commutator ↥(alternatingGroup (Fin s.card)) = ⊥ := by
    rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x _
    rw [Subgroup.mem_centralizer_iff]
    intro y _
    exact hab y x
  rw [hc] at hbot
  have h1 : Nat.card ↥(alternatingGroup (Fin s.card)) = 1 := by
    rw [← Subgroup.card_top (G := ↥(alternatingGroup (Fin s.card))), hbot, Subgroup.card_bot]
  rw [Prop126b.card_alt' s.card (by omega)] at h1
  have h120 : Nat.factorial 5 ≤ s.card.factorial := Nat.factorial_le h5
  have h5f : Nat.factorial 5 = 120 := rfl
  omega

theorem dvd_factorial_div_two {p m : ℕ} (hp : Nat.Coprime p 2) (hp1 : 1 ≤ p) (hpm : p ≤ m)
    (h2 : 2 ≤ m) : p ∣ m.factorial / 2 := by
  have h5 : p ∣ m.factorial := Nat.dvd_factorial hp1 hpm
  obtain ⟨k, hk⟩ := Nat.dvd_factorial (by norm_num : 0 < 2) h2
  rw [hk, Nat.mul_div_cancel_left k (by norm_num)]
  rw [hk] at h5
  exact (Nat.Coprime.dvd_mul_left hp).1 h5

theorem three_dvd_card_altOn {s : Finset α} (h5 : 5 ≤ s.card) : 3 ∣ Nat.card ↥(altOn s) := by
  rw [card_altOn (by omega)]
  exact dvd_factorial_div_two (by norm_num) (by norm_num) (by omega) (by omega)

@[expose] def cA (σ : Perm α) : Subgroup (Perm α) :=
  alternatingGroup α ⊓ Subgroup.centralizer ({σ} : Set (Perm α))

theorem mem_cA {σ g : Perm α} : g ∈ cA σ ↔ g ∈ alternatingGroup α ∧ g * σ = σ * g := by
  rw [cA, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]

@[expose] def uSub (σ : Perm α) : Subgroup (Perm α) where
  carrier := {u | u * σ = σ * u ∧ ∀ x, ∃ k : ℕ, u x = (σ ^ k) x}
  mul_mem' := by
    rintro u v ⟨hu, hu'⟩ ⟨hv, hv'⟩
    refine ⟨by rw [mul_assoc, hv, ← mul_assoc, hu, mul_assoc], fun x => ?_⟩
    obtain ⟨j, hj⟩ := hv' x
    obtain ⟨k, hk⟩ := hu' x
    refine ⟨k + j, ?_⟩
    have hc : u * σ ^ j = σ ^ j * u := (Commute.pow_right (hu : Commute u σ) j).eq
    calc (u * v) x = u ((σ ^ j) x) := by rw [Perm.mul_apply, hj]
      _ = (σ ^ j) (u x) := by rw [← Perm.mul_apply, hc, Perm.mul_apply]
      _ = (σ ^ (k + j)) x := by rw [hk, ← Perm.mul_apply, ← pow_add, add_comm]
  one_mem' := ⟨by rw [one_mul, mul_one], fun x => ⟨0, by simp⟩⟩
  inv_mem' := by
    rintro u ⟨hu, hu'⟩
    refine ⟨?_, fun x => ?_⟩
    · calc u⁻¹ * σ = u⁻¹ * (σ * u) * u⁻¹ := by group
        _ = u⁻¹ * (u * σ) * u⁻¹ := by rw [hu]
        _ = σ * u⁻¹ := by group
    · obtain ⟨k, hk⟩ := hu' (u⁻¹ x)
      have h1 : (σ ^ k) (u⁻¹ x) = x := by rw [← hk]; simp
      have hN : 0 < orderOf σ := orderOf_pos σ
      refine ⟨(orderOf σ - 1) * k, ?_⟩
      have h2 : σ ^ ((orderOf σ - 1) * k) * σ ^ k = 1 := by
        have : (orderOf σ - 1) * k + k = orderOf σ * k := by
          rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hN]
        rw [← pow_add, this, pow_mul, pow_orderOf_eq_one, one_pow]
      calc u⁻¹ x = (σ ^ ((orderOf σ - 1) * k) * σ ^ k) (u⁻¹ x) := by rw [h2]; rfl
        _ = (σ ^ ((orderOf σ - 1) * k)) x := by rw [Perm.mul_apply, h1]

theorem pow_apply_of_mem_uSub {σ u : Perm α} (hu : u ∈ uSub σ) {x : α} {k : ℕ}
    (hk : u x = (σ ^ k) x) : ∀ m : ℕ, (u ^ m) x = (σ ^ (m * k)) x
  | 0 => by simp
  | m + 1 => by
    have hc : u ^ m * σ ^ k = σ ^ k * u ^ m := (Commute.pow_pow (hu.1 : Commute u σ) m k).eq
    rw [pow_succ, Perm.mul_apply, hk, ← Perm.mul_apply, hc, Perm.mul_apply,
      pow_apply_of_mem_uSub hu hk m, ← Perm.mul_apply, ← pow_add]
    congr 2
    ring

theorem pow_three_of_mem_uSub {σ u : Perm α} (hσ : σ ^ 3 = 1) (hu : u ∈ uSub σ) : u ^ 3 = 1 := by
  ext x
  obtain ⟨k, hk⟩ := hu.2 x
  rw [pow_apply_of_mem_uSub hu hk 3, pow_mul, hσ, one_pow]

theorem uSub_le_alt {σ : Perm α} (hσ : σ ^ 3 = 1) : uSub σ ≤ alternatingGroup α := by
  intro u hu
  rw [Perm.mem_alternatingGroup]
  have h3 := congrArg Perm.sign (pow_three_of_mem_uSub hσ hu)
  rw [map_pow, map_one] at h3
  rcases Int.units_eq_one_or (Perm.sign u) with h | h
  · exact h
  · rw [h] at h3
    exact absurd h3 (by decide)

theorem isPGroup_uSub {σ : Perm α} (hσ : σ ^ 3 = 1) : IsPGroup 3 ↥(uSub σ) := by
  intro u
  refine ⟨1, ?_⟩
  apply Subtype.ext
  simpa using pow_three_of_mem_uSub hσ u.2

theorem uSub_le_cA {σ : Perm α} (hσ : σ ^ 3 = 1) : uSub σ ≤ cA σ :=
  fun u hu => mem_cA.2 ⟨uSub_le_alt hσ hu, hu.1⟩

theorem conj_mem_uSub {σ c u : Perm α} (hc : c * σ = σ * c) (hu : u ∈ uSub σ) :
    c * u * c⁻¹ ∈ uSub σ := by
  refine ⟨?_, fun x => ?_⟩
  · have h1 : Commute c σ := hc
    have h2 : Commute u σ := hu.1
    exact ((h1.mul_left h2).mul_left h1.inv_left).eq
  · obtain ⟨k, hk⟩ := hu.2 (c⁻¹ x)
    refine ⟨k, ?_⟩
    have hck : c * σ ^ k = σ ^ k * c := (Commute.pow_right (hc : Commute c σ) k).eq
    rw [Perm.mul_apply, Perm.mul_apply, hk, ← Perm.mul_apply, hck, Perm.mul_apply]
    simp

theorem cycleOf_mem_uSub (σ : Perm α) (x : α) : σ.cycleOf x ∈ uSub σ := by
  refine ⟨?_, fun y => ?_⟩
  · ext y
    rw [Perm.mul_apply, Perm.mul_apply, Perm.cycleOf_apply, Perm.cycleOf_apply]
    by_cases h : σ.SameCycle x y
    · rw [if_pos (Perm.sameCycle_apply_right.2 h), if_pos h]
    · rw [if_neg (mt Perm.sameCycle_apply_right.1 h), if_neg h]
  · by_cases h : σ.SameCycle x y
    · exact ⟨1, by rw [Perm.cycleOf_apply, if_pos h, pow_one]⟩
    · exact ⟨0, by rw [Perm.cycleOf_apply, if_neg h, pow_zero]; rfl⟩

theorem exists_pow_of_comm_uSub {σ g : Perm α} (hg : g * σ = σ * g)
    (hgu : ∀ u ∈ uSub σ, g * u = u * g) {y : α} (hy : σ y ≠ y) : ∃ k : ℕ, g y = (σ ^ k) y := by
  have hc := hgu _ (cycleOf_mem_uSub σ y)
  have h1 : (σ.cycleOf y) (g y) = σ (g y) := by
    have e1 : (σ.cycleOf y) (g y) = g ((σ.cycleOf y) y) := by
      rw [← Perm.mul_apply, ← hc, Perm.mul_apply]
    rw [e1, Perm.cycleOf_apply, if_pos (Perm.SameCycle.refl σ y), ← Perm.mul_apply, hg,
      Perm.mul_apply]
  by_cases hs : σ.SameCycle y (g y)
  · obtain ⟨k, -, hk⟩ := hs.exists_pow_eq'
    exact ⟨k, hk.symm⟩
  · exfalso
    rw [Perm.cycleOf_apply, if_neg hs] at h1
    apply hy
    have : g (σ y) = g y := by rw [← Perm.mul_apply, hg, Perm.mul_apply, ← h1]
    exact g.injective this

theorem commutator_apply_eq_of_pow {σ g₁ g₂ : Perm α} (h₁ : g₁ * σ = σ * g₁)
    (h₂ : g₂ * σ = σ * g₂) (e₁ : ∀ y, σ y ≠ y → ∃ k : ℕ, g₁ y = (σ ^ k) y)
    (e₂ : ∀ y, σ y ≠ y → ∃ k : ℕ, g₂ y = (σ ^ k) y) {y : α} (hy : σ y ≠ y) :
    ⁅g₁, g₂⁆ y = y := by
  have hc21 : Commute (g₂ * g₁) σ :=
    Commute.mul_left (h₂ : Commute g₂ σ) (h₁ : Commute g₁ σ)
  set w := (g₂ * g₁)⁻¹ y with hw
  have hwy : σ w ≠ w := by
    intro h
    apply hy
    have h2 : (g₂ * g₁) (σ w) = (g₂ * g₁) w := by rw [h]
    rw [← Perm.mul_apply, hc21.eq, Perm.mul_apply] at h2
    simpa [hw] using h2
  obtain ⟨k₁, hk₁⟩ := e₁ w hwy
  obtain ⟨k₂, hk₂⟩ := e₂ w hwy
  have hc1 : g₁ * σ ^ k₂ = σ ^ k₂ * g₁ := (Commute.pow_right (h₁ : Commute g₁ σ) k₂).eq
  have hc2 : g₂ * σ ^ k₁ = σ ^ k₁ * g₂ := (Commute.pow_right (h₂ : Commute g₂ σ) k₁).eq
  have L : (g₁ * g₂) w = (σ ^ (k₂ + k₁)) w := by
    rw [Perm.mul_apply, hk₂, ← Perm.mul_apply, hc1, Perm.mul_apply, hk₁, ← Perm.mul_apply,
      ← pow_add]
  have R : (g₂ * g₁) w = (σ ^ (k₁ + k₂)) w := by
    rw [Perm.mul_apply, hk₁, ← Perm.mul_apply, hc2, Perm.mul_apply, hk₂, ← Perm.mul_apply,
      ← pow_add]
  have key : (g₁ * g₂) w = (g₂ * g₁) w := by rw [L, R, add_comm]
  have hwy' : (g₂ * g₁) w = y := by rw [hw]; simp
  rw [commutatorElement_def]
  calc (g₁ * g₂ * g₁⁻¹ * g₂⁻¹) y = (g₁ * g₂) ((g₂ * g₁)⁻¹ y) := by
        rw [mul_inv_rev]; simp only [Perm.mul_apply]
    _ = (g₂ * g₁) w := key
    _ = y := hwy'

theorem eq_one_of_mem_uSub_of_mem_core {σ : Perm α} (hσ : σ ^ 3 = 1) {x : Perm α}
    (hxU : x ∈ uSub σ) (hxO : x ∈ GLAPPrimeCoreOf 3 (cA σ)) : x = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨y, hy, rfl⟩ := hxO
  have h3 : y ^ 3 = 1 := Subtype.ext (by simpa using pow_three_of_mem_uSub hσ hxU)
  have hcop : Nat.Coprime 3 (Nat.card ↥(GLAPPrimeCore 3 ↥(cA σ))) := CFSG.pPrimeCore_coprime_card
  have hdvd : orderOf y ∣ Nat.card ↥(GLAPPrimeCore 3 ↥(cA σ)) := by
    have := orderOf_dvd_natCard (⟨y, hy⟩ : ↥(GLAPPrimeCore 3 ↥(cA σ)))
    rwa [Subgroup.orderOf_mk] at this
  have h3' : orderOf y ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  have hg : orderOf y ∣ Nat.gcd 3 (Nat.card ↥(GLAPPrimeCore 3 ↥(cA σ))) := Nat.dvd_gcd h3' hdvd
  rw [hcop] at hg
  have : y = 1 := orderOf_eq_one_iff.1 (Nat.dvd_one.1 hg)
  rw [this]
  rfl

theorem comm_uSub_of_glaPComponent {σ : Perm α} (hσ : σ ^ 3 = 1) {Q : Subgroup (Perm α)}
    (hQ : GLAPComponent 3 (cA σ) Q) : ∀ q ∈ Q, ∀ u ∈ uSub σ, q * u = u * q := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hUC := uSub_le_cA hσ
  have hUn : ((uSub σ).subgroupOf (cA σ)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hg := (mem_cA.1 g.2).2
    simpa using conj_mem_uSub hg hn
  have hUbn : (barX 3 (cA σ) (uSub σ)).Normal := hUn.map _ (QuotientGroup.mk'_surjective _)
  have hcomp := (CFSG.Adapters.isComponentOf_top_iff _).1 hQ.2.2.1
  rcases CFSG.GorensteinWalter.component_le_or_commutator_eq_bot_of_normal hcomp hUbn with
    hle | hbot
  · exfalso
    have hp : IsPGroup 3 ↥(barX 3 (cA σ) (uSub σ)) := by
      have h1 : IsPGroup 3 ↥((uSub σ).subgroupOf (cA σ)) :=
        (isPGroup_uSub hσ).of_equiv (Subgroup.subgroupOfEquivOfLe hUC).symm
      exact h1.map _
    exact not_isPGroup_of_isQuasisimple Nat.prime_three hQ.2.2.1.2.2 (hp.to_le hle)
  · intro q hq u hu
    have hqC := hQ.1 hq
    have huC := hUC hu
    have hmem : ⁅QuotientGroup.mk' (GLAPPrimeCore 3 ↥(cA σ)) ⟨q, hqC⟩,
        QuotientGroup.mk' (GLAPPrimeCore 3 ↥(cA σ)) ⟨u, huC⟩⁆ ∈
        ⁅barX 3 (cA σ) Q, barX 3 (cA σ) (uSub σ)⁆ :=
      Subgroup.commutator_mem_commutator ⟨⟨q, hqC⟩, Subgroup.mem_subgroupOf.2 hq, rfl⟩
        ⟨⟨u, huC⟩, Subgroup.mem_subgroupOf.2 hu, rfl⟩
    have hbot' : ⁅barX 3 (cA σ) Q, barX 3 (cA σ) (uSub σ)⁆ = ⊥ := hbot
    rw [hbot', Subgroup.mem_bot, ← map_commutatorElement] at hmem
    have h1 : ⁅(⟨q, hqC⟩ : ↥(cA σ)), ⟨u, huC⟩⁆ ∈ GLAPPrimeCore 3 ↥(cA σ) :=
      (QuotientGroup.eq_one_iff _).1 hmem
    have h2 : ⁅q, u⁆ ∈ GLAPPrimeCoreOf 3 (cA σ) := ⟨_, h1, rfl⟩
    have h3 : ⁅q, u⁆ ∈ uSub σ := by
      rw [commutatorElement_def]
      exact (uSub σ).mul_mem (conj_mem_uSub (mem_cA.1 hqC).2 hu) ((uSub σ).inv_mem hu)
    exact commutatorElement_eq_one_iff_mul_comm.1 (eq_one_of_mem_uSub_of_mem_core hσ h3 h2)

theorem altOn_le_cA (σ : Perm α) : altOn σ.supportᶜ ≤ cA σ := by
  intro g hg
  obtain ⟨hA, hs⟩ := mem_altOn.1 hg
  refine mem_cA.2 ⟨hA, ?_⟩
  have hd : Perm.Disjoint g σ := by
    intro x
    by_cases hx : σ x = x
    · exact Or.inr hx
    · left
      by_contra hgx
      have h1 : x ∈ g.support := Perm.mem_support.2 hgx
      have h2 := hs h1
      rw [Finset.mem_compl, Perm.mem_support] at h2
      exact h2 hx
  exact hd.commute.eq

theorem altOn_normal_cA (σ : Perm α) : ((altOn σ.supportᶜ).subgroupOf (cA σ)).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  obtain ⟨hnA, hns⟩ := mem_altOn.1 hn
  have hg := mem_cA.1 g.2
  refine mem_altOn.2 ⟨?_, ?_⟩
  · simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact (alternatingGroup α).mul_mem ((alternatingGroup α).mul_mem hg.1 hnA)
      ((alternatingGroup α).inv_mem hg.1)
  · intro y hy
    rw [Finset.mem_compl, Perm.mem_support, not_not]
    rw [Perm.mem_support] at hy
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Perm.mul_apply] at hy
    have hgi : (g : Perm α)⁻¹ * σ = σ * (g : Perm α)⁻¹ := (Commute.inv_left (hg.2 : Commute _ σ)).eq
    have h1 : (n : Perm α) ((g : Perm α)⁻¹ y) ≠ (g : Perm α)⁻¹ y := by
      intro h
      apply hy
      rw [h]
      simp
    have h2 := hns (Perm.mem_support.2 h1)
    rw [Finset.mem_compl, Perm.mem_support, not_not] at h2
    have h3 : (g : Perm α)⁻¹ (σ y) = (g : Perm α)⁻¹ y := by
      rw [← Perm.mul_apply, hgi, Perm.mul_apply, h2]
    exact (g : Perm α)⁻¹.injective h3

theorem glaPComponent_cA {σ : Perm α} (hσ : σ ^ 3 = 1) {Q : Subgroup (Perm α)}
    (hQ : GLAPComponent 3 (cA σ) Q) : Q = altOn σ.supportᶜ ∧ 5 ≤ σ.supportᶜ.card := by
  have hcomm := comm_uSub_of_glaPComponent hσ hQ
  have hQC : Q ≤ cA σ := hQ.1
  have he : ∀ g ∈ Q, ∀ y, σ y ≠ y → ∃ k : ℕ, g y = (σ ^ k) y := fun g hg y hy =>
    exists_pow_of_comm_uSub (mem_cA.1 (hQC hg)).2 (fun u hu => hcomm g hg u hu) hy
  have hperf : ⁅Q, Q⁆ = Q := glaPComponent_perfect hQ
  have hQalt : Q ≤ altOn σ.supportᶜ := by
    rw [← hperf, Subgroup.commutator_le]
    intro g₁ h₁ g₂ h₂
    refine mem_altOn.2 ⟨?_, ?_⟩
    · have a1 := (mem_cA.1 (hQC h₁)).1
      have a2 := (mem_cA.1 (hQC h₂)).1
      rw [commutatorElement_def]
      exact (alternatingGroup α).mul_mem ((alternatingGroup α).mul_mem
        ((alternatingGroup α).mul_mem a1 a2) ((alternatingGroup α).inv_mem a1))
        ((alternatingGroup α).inv_mem a2)
    · intro y hy
      rw [Finset.mem_compl, Perm.mem_support, not_not]
      by_contra hσy
      rw [Perm.mem_support] at hy
      exact hy (commutator_apply_eq_of_pow (mem_cA.1 (hQC h₁)).2 (mem_cA.1 (hQC h₂)).2
        (he g₁ h₁) (he g₂ h₂) hσy)
  have hsn : IsSubnormal Q (altOn σ.supportᶜ) :=
    isSubnormal_of_le_of_le hQ.2.1 hQalt (altOn_le_cA σ)
  have hne : Q ≠ ⊥ := by
    rintro rfl
    have h := (Subgroup.nontrivial_iff_ne_bot _).1 (nontrivial_of_isQuasisimple hQ.2.2.1.2.2)
    apply h
    rw [Subgroup.bot_subgroupOf, Subgroup.map_bot]
  by_cases h5 : 5 ≤ σ.supportᶜ.card
  · rcases CFSG.Open.IsSubnormal.eq_bot_or_eq_of_isSimpleGroup hsn (isSimpleGroup_altOn h5) with
      h | h
    · exact absurd h hne
    · exact ⟨h, h5⟩
  · exact absurd (eq_bot_of_perfect_of_le_solvable hperf hQalt (isSolvable_altOn (by omega))) hne

theorem glaPComponent_altOn (σ : Perm α) (h5 : 5 ≤ σ.supportᶜ.card) :
    GLAPComponent 3 (cA σ) (altOn σ.supportᶜ) :=
  glaPComponent_of_simple_normal Nat.prime_three (altOn_le_cA σ) (altOn_normal_cA σ)
    (isSimpleGroup_altOn h5) (altOn_noncomm h5) (three_dvd_card_altOn h5)

@[expose] def kleinOn (s : Finset α) : Subgroup (Perm α) :=
  ((alternatingGroup.kleinFour ↥s).map (alternatingGroup.ofSubtype s)).map
    (alternatingGroup α).subtype

theorem mem_kleinOn {s : Finset α} (h4 : s.card = 4) {g : Perm α} :
    g ∈ kleinOn s ↔ g ∈ altOn s ∧ (g = 1 ∨ g.cycleType = {2, 2}) := by
  have hc : Nat.card ↥s = 4 := by rw [Nat.card_eq_fintype_card, Fintype.card_coe, h4]
  constructor
  · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
    have hk' : k ∈ (alternatingGroup.kleinFour ↥s : Set _) := hk
    rw [alternatingGroup.coe_kleinFour_of_card_eq_four hc] at hk'
    refine ⟨⟨_, ⟨k, rfl⟩, rfl⟩, ?_⟩
    rcases hk' with h1 | h1
    · left
      rw [Set.mem_singleton_iff] at h1
      rw [h1, map_one]
      rfl
    · right
      show (Perm.ofSubtype (k : Perm ↥s)).cycleType = {2, 2}
      rw [Perm.cycleType_ofSubtype]
      exact h1
  · rintro ⟨⟨_, ⟨k, rfl⟩, rfl⟩, h⟩
    refine ⟨_, ⟨k, ?_, rfl⟩, rfl⟩
    have : k ∈ (alternatingGroup.kleinFour ↥s : Set _) := by
      rw [alternatingGroup.coe_kleinFour_of_card_eq_four hc]
      rcases h with h | h
      · left
        rw [Set.mem_singleton_iff]
        apply alternatingGroup.ofSubtype_injective (s := s)
        rw [map_one]
        exact Subtype.ext h
      · right
        show (k : Perm ↥s).cycleType = {2, 2}
        rw [← Perm.cycleType_ofSubtype]
        exact h
    exact this

theorem card_kleinOn {s : Finset α} (h4 : s.card = 4) : Nat.card ↥(kleinOn s) = 4 := by
  have hc : Nat.card ↥s = 4 := by rw [Nat.card_eq_fintype_card, Fintype.card_coe, h4]
  rw [kleinOn, Subgroup.card_map_of_injective (alternatingGroup α).subtype_injective,
    Subgroup.card_map_of_injective alternatingGroup.ofSubtype_injective,
    alternatingGroup.kleinFour_card_of_card_eq_four hc]

theorem kleinOn_normal_cA (σ : Perm α) (h4 : σ.supportᶜ.card = 4) :
    ((kleinOn σ.supportᶜ).subgroupOf (cA σ)).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf, mem_kleinOn h4] at hn ⊢
  obtain ⟨hna, hn1⟩ := hn
  refine ⟨?_, ?_⟩
  · have := (altOn_normal_cA σ).conj_mem n (Subgroup.mem_subgroupOf.2 hna) g
    exact Subgroup.mem_subgroupOf.1 this
  · simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rcases hn1 with h | h
    · left
      rw [h, mul_one, mul_inv_cancel]
    · right
      rw [Perm.cycleType_conj]
      exact h

theorem kleinOn_le_core (σ : Perm α) (h4 : σ.supportᶜ.card = 4) :
    kleinOn σ.supportᶜ ≤ GLAPPrimeCoreOf 3 (cA σ) := by
  have hle : kleinOn σ.supportᶜ ≤ cA σ := fun g hg => altOn_le_cA σ ((mem_kleinOn h4).1 hg).1
  have hsn : IsSubnormal (kleinOn σ.supportᶜ) (cA σ) :=
    IsSubnormal.step hle (kleinOn_normal_cA σ h4) (IsSubnormal.refl _)
  refine Prop95Parts.Input18.le_glaPPrimeCoreOf_of_coprime Nat.prime_three hsn ?_
  rw [card_kleinOn h4]
  norm_num

theorem swap_mul_swap_mem_kleinOn {s : Finset α} (h4 : s.card = 4) {a b c d : α}
    (hnd : [a, b, c, d].Nodup) (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) (hd : d ∈ s) :
    Equiv.swap a b * Equiv.swap c d ∈ kleinOn s := by
  rw [mem_kleinOn h4]
  have hab : a ≠ b := by intro h; simp [h] at hnd
  have hcd : c ≠ d := by intro h; simp [h] at hnd
  refine ⟨mem_altOn.2 ⟨?_, ?_⟩, Or.inr (Perm.cycleType_swap_mul_swap_of_nodup hnd)⟩
  · rw [Perm.mem_alternatingGroup, Perm.sign_mul, Perm.sign_swap hab, Perm.sign_swap hcd]
    rfl
  · intro z hz
    have h1 := Perm.support_mul_le (Equiv.swap a b) (Equiv.swap c d) hz
    rw [Perm.support_swap hab, Perm.support_swap hcd] at h1
    simp only [Finset.sup_eq_union, Finset.mem_union, Finset.mem_insert,
      Finset.mem_singleton] at h1
    rcases h1 with (h | h) | (h | h) <;> (subst h; assumption)

theorem mem_altOn_of_threeCycle {T : Finset α} {c : Perm α} (hc : c.IsThreeCycle)
    (hs : c.support ⊆ T) : c ∈ altOn T :=
  mem_altOn.2 ⟨hc.mem_alternatingGroup, hs⟩

theorem altOn_le_sup_erase {T : Finset α} (h5 : 5 ≤ T.card) {y f : α} (hyf : y ≠ f) :
    altOn T ≤ altOn (T.erase y) ⊔ altOn (T.erase f) := by
  intro g hg
  obtain ⟨hA, hs⟩ := mem_altOn.1 hg
  obtain ⟨g', rfl⟩ : g ∈ (Perm.ofSubtype : Perm ↥T →* Perm α).range :=
    Perm.mem_range_ofSubtype_iff.2 (fun z hz => hs hz)
  have hg'A : g' ∈ alternatingGroup ↥T := by
    rw [Perm.mem_alternatingGroup, ← Perm.sign_ofSubtype]
    exact hA
  rw [← Perm.closure_three_cycles_eq_alternating] at hg'A
  clear hg hA hs
  induction hg'A using Subgroup.closure_induction with
  | mem c' hc' =>
    have hc : (Perm.ofSubtype c' : Perm α).IsThreeCycle := by
      have h1 : c'.IsThreeCycle := hc'
      unfold Perm.IsThreeCycle at h1 ⊢
      rw [Perm.cycleType_ofSubtype]
      exact h1
    set c : Perm α := Perm.ofSubtype c' with hcdef
    have hcT : c.support ⊆ T := by
      intro z hz
      by_contra hzT
      rw [Perm.mem_support, hcdef, Perm.ofSubtype_apply_of_not_mem c' hzT] at hz
      exact hz rfl
    by_cases hy : y ∈ c.support
    · by_cases hf : f ∈ c.support
      ·
        have hcard : 2 ≤ (T \ c.support).card := by
          rw [Finset.card_sdiff_of_subset hcT, hc.card_support]
          omega
        obtain ⟨v, hv, w, hw, hvw⟩ := Finset.one_lt_card.1 (by omega : 1 < (T \ c.support).card)
        rw [Finset.mem_sdiff] at hv hw
        have hvy : v ≠ y := fun h => hv.2 (h ▸ hy)
        have hwy : w ≠ y := fun h => hw.2 (h ▸ hy)
        have hvf : v ≠ f := fun h => hv.2 (h ▸ hf)
        have hwf : w ≠ f := fun h => hw.2 (h ▸ hf)
        set h : Perm α := Equiv.swap y v * Equiv.swap y w with hhdef
        have hh3 : h.IsThreeCycle := Perm.isThreeCycle_swap_mul_swap_same hvy.symm hwy.symm hvw
        have hhs : h.support ⊆ T.erase f := by
          intro z hz
          have h1 := Perm.support_mul_le (Equiv.swap y v) (Equiv.swap y w) hz
          rw [Perm.support_swap hvy.symm, Perm.support_swap hwy.symm] at h1
          simp only [Finset.sup_eq_union, Finset.mem_union, Finset.mem_insert,
            Finset.mem_singleton] at h1
          rw [Finset.mem_erase]
          rcases h1 with (h1 | h1) | (h1 | h1) <;> subst h1
          · exact ⟨hyf, hcT hy⟩
          · exact ⟨hvf, hv.1⟩
          · exact ⟨hyf, hcT hy⟩
          · exact ⟨hwf, hw.1⟩
        have hhT : altOn (T.erase f) ≤ altOn (T.erase y) ⊔ altOn (T.erase f) := le_sup_right
        have hhmem : h ∈ altOn (T.erase f) := mem_altOn_of_threeCycle hh3 hhs
        have hyw : h y = w := by
          rw [hhdef, Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hwy hvw.symm]
        set c₀ : Perm α := h⁻¹ * c * h with hc₀
        have hc₀mem : c₀ ∈ altOn (T.erase y) := by
          refine mem_altOn.2 ⟨?_, ?_⟩
          · have hhA := (mem_altOn.1 hhmem).1
            exact (alternatingGroup α).mul_mem ((alternatingGroup α).mul_mem
              ((alternatingGroup α).inv_mem hhA) hc.mem_alternatingGroup) hhA
          · have hsupp : c₀.support = c.support.map (h⁻¹).toEmbedding := by
              rw [hc₀, show h = h⁻¹⁻¹ by rw [inv_inv], inv_inv]
              exact Perm.support_conj
            rw [hsupp]
            intro z hz
            rw [Finset.mem_map] at hz
            obtain ⟨t, ht, rfl⟩ := hz
            rw [Finset.mem_erase]
            constructor
            · intro htw
              have : t = h y := by
                rw [Equiv.toEmbedding_apply] at htw
                rw [← htw]
                simp
              rw [hyw] at this
              exact hw.2 (this ▸ ht)
            · rw [Equiv.toEmbedding_apply]
              by_contra hT
              have hfix : h (h⁻¹ t) = h⁻¹ t := by
                by_contra hne
                exact hT ((Finset.mem_erase.1 (hhs (Perm.mem_support.2 hne))).2)
              rw [show h (h⁻¹ t) = t by simp] at hfix
              exact hT (hfix ▸ hcT ht)
        have hcc : c = h * c₀ * h⁻¹ := by rw [hc₀]; group
        rw [hcc]
        exact (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hhT hhmem) (Subgroup.mem_sup_left hc₀mem))
          (hhT (Subgroup.inv_mem _ hhmem)))
      · refine Subgroup.mem_sup_right (mem_altOn_of_threeCycle hc ?_)
        intro z hz
        exact Finset.mem_erase.2 ⟨fun h => hf (h ▸ hz), hcT hz⟩
    · refine Subgroup.mem_sup_left (mem_altOn_of_threeCycle hc ?_)
      intro z hz
      exact Finset.mem_erase.2 ⟨fun h => hy (h ▸ hz), hcT hz⟩
  | one => rw [map_one]; exact Subgroup.one_mem _
  | mul a b _ _ ha hb => rw [map_mul]; exact Subgroup.mul_mem _ ha hb
  | inv a _ ha => rw [map_inv]; exact Subgroup.inv_mem _ ha

theorem altOn_erase_le_gLBConj {F : Finset α} {f y : α} {c : Perm α} (hcy : c y = f)
    (hcF : ∀ z ∈ F, z ≠ f → c z = z) (hfF : f ∈ F) :
    altOn ((insert y F).erase f) ≤ GLBConj c (altOn F) := by
  intro g hg
  obtain ⟨hA, hs⟩ := mem_altOn.1 hg
  rw [mem_gLBConj]
  refine mem_altOn.2 ⟨?_, ?_⟩
  · rw [Perm.mem_alternatingGroup] at hA ⊢
    rw [Perm.sign_mul, Perm.sign_mul, hA, mul_one, ← Perm.sign_mul, mul_inv_cancel, map_one]
  · rw [Perm.support_conj]
    intro z hz
    rw [Finset.mem_map] at hz
    obtain ⟨t, ht, rfl⟩ := hz
    have ht' := hs ht
    rw [Finset.mem_erase, Finset.mem_insert] at ht'
    rw [Equiv.toEmbedding_apply]
    rcases ht'.2 with h | h
    · subst h
      rw [hcy]
      exact hfF
    · rw [hcF t h ht'.1]
      exact h

theorem exists_fixed_of_pow_three {τ : Perm α} (hτ : τ ^ 3 = 1) {F : Finset α}
    (hF : ∀ z, τ z ∈ F ↔ z ∈ F) (h3 : ¬ 3 ∣ F.card) : ∃ f ∈ F, τ f = f := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let τ' : Perm ↥F := τ.subtypePerm hF
  have hτ' : τ' ^ 3 ^ 1 = 1 := by
    rw [pow_one, Perm.subtypePerm_pow]
    ext z
    simp [hτ]
  obtain ⟨⟨f, hf⟩, hfix⟩ := Perm.exists_fixed_point_of_prime (p := 3) (n := 1)
    (by rwa [Fintype.card_coe]) hτ'
  exact ⟨f, hf, by simpa [τ'] using congrArg Subtype.val hfix⟩

theorem card_dvd_of_free (P : Subgroup (Perm α)) :
    ∀ S : Finset α, (∀ g ∈ P, ∀ x ∈ S, g x ∈ S) →
      (∀ g ∈ P, g ≠ 1 → ∀ x ∈ S, g x ≠ x) → Nat.card P ∣ S.card := by
  classical
  haveI : Fintype ↥P := Fintype.ofFinite _
  intro S
  induction S using Finset.strongInduction with
  | H S ih =>
    intro hinv hfree
    by_cases hS : S = ∅
    · subst hS
      simp
    · obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.2 hS
      set O : Finset α := Finset.univ.image (fun g : ↥P => (g : Perm α) x) with hO
      have hinj : Function.Injective (fun g : ↥P => (g : Perm α) x) := by
        intro g h hgh
        simp only at hgh
        by_contra hne
        have h1 : (h : Perm α)⁻¹ * g ≠ 1 := by
          intro h1
          apply hne
          apply Subtype.ext
          rw [← mul_left_cancel_iff (a := (h : Perm α)⁻¹), h1, inv_mul_cancel]
        apply hfree _ (P.mul_mem (P.inv_mem h.2) g.2) h1 x hx
        rw [Perm.mul_apply, hgh]
        simp
      have hOcard : O.card = Nat.card ↥P := by
        rw [hO, Finset.card_image_of_injective _ hinj, Finset.card_univ, Nat.card_eq_fintype_card]
      have hOS : O ⊆ S := by
        intro z hz
        rw [hO, Finset.mem_image] at hz
        obtain ⟨g, -, rfl⟩ := hz
        exact hinv _ g.2 x hx
      have hxO : x ∈ O := by
        rw [hO, Finset.mem_image]
        exact ⟨1, Finset.mem_univ _, rfl⟩
      have hinv' : ∀ g ∈ P, ∀ z ∈ S \ O, g z ∈ S \ O := by
        intro g hg z hz
        rw [Finset.mem_sdiff] at hz ⊢
        refine ⟨hinv g hg z hz.1, fun hgz => hz.2 ?_⟩
        rw [hO, Finset.mem_image] at hgz ⊢
        obtain ⟨k, -, hk⟩ := hgz
        refine ⟨⟨g⁻¹ * k, P.mul_mem (P.inv_mem hg) k.2⟩, Finset.mem_univ _, ?_⟩
        simp only [Subgroup.coe_mk, Perm.mul_apply]
        rw [hk]
        simp
      have hlt : S \ O ⊂ S := Finset.sdiff_ssubset hOS ⟨x, hxO⟩
      have h1 := ih (S \ O) hlt hinv' (fun g hg hg1 z hz => hfree g hg hg1 z (Finset.mem_sdiff.1 hz).1)
      have h2 : S.card = (S \ O).card + O.card := (Finset.card_sdiff_add_card_eq_card hOS).symm
      rw [h2, hOcard]
      exact dvd_add h1 dvd_rfl

theorem altOn_insert_le {F : Finset α} (h4 : 4 ≤ F.card) {f y : α} (hfF : f ∈ F) (hyF : y ∉ F)
    {c : Perm α} (hcy : c y = f) (hcF : ∀ z ∈ F, z ≠ f → c z = z) :
    altOn (insert y F) ≤ altOn F ⊔ GLBConj c (altOn F) := by
  have hyf : y ≠ f := fun h => hyF (h ▸ hfF)
  have h5 : 5 ≤ (insert y F).card := by
    rw [Finset.card_insert_of_notMem hyF]
    omega
  refine (altOn_le_sup_erase h5 hyf).trans (sup_le ?_ ?_)
  · rw [Finset.erase_insert hyF]
    exact le_sup_left
  · exact (altOn_erase_le_gLBConj hcy hcF hfF).trans le_sup_right

theorem perm_key {σa σb : Perm α} (hb : σb ^ 3 = 1) (ha : σa ^ 3 = 1) (hab : σa * σb = σb * σa)
    (hF : σa.supportᶜ.card = 7) {x : α} (hx : σa x ≠ x) (hbx : σb x = x) :
    ∃ (c : Perm α) (y : α), y ∉ σa.supportᶜ ∧
      ((5 ≤ σb.supportᶜ.card ∧ c ∈ altOn σb.supportᶜ) ∨
        (σb.supportᶜ.card = 4 ∧ c ∈ kleinOn σb.supportᶜ)) ∧
      altOn (insert y σa.supportᶜ) ≤ altOn σa.supportᶜ ⊔ GLBConj c (altOn σa.supportᶜ) := by
  have memF : ∀ (τ : Perm α) (z : α), z ∈ τ.supportᶜ ↔ τ z = z := fun τ z => by
    rw [Finset.mem_compl, Perm.mem_support, not_not]
  have hbF : ∀ z, σb z ∈ σa.supportᶜ ↔ z ∈ σa.supportᶜ := by
    intro z
    rw [memF, memF]
    constructor
    · intro h
      have : σb (σa z) = σb z := by rw [← Perm.mul_apply, ← hab, Perm.mul_apply, h]
      exact σb.injective this
    · intro h
      rw [← Perm.mul_apply, hab, Perm.mul_apply, h]
  obtain ⟨f, hfF, hbf⟩ := exists_fixed_of_pow_three hb hbF (by rw [hF]; norm_num)
  have hx1 : σa (σa x) ≠ σa x := fun h => hx (σa.injective h)
  have hx3eq : σa (σa (σa x)) = x := by
    have := congrArg (fun g : Perm α => g x) ha
    simpa [pow_succ, Perm.mul_apply] using this
  have hx2 : σa (σa x) ≠ x := by
    intro h
    have h' := congrArg σa h
    rw [hx3eq] at h'
    exact hx h'.symm
  have hbx1 : σb (σa x) = σa x := by rw [← Perm.mul_apply, ← hab, Perm.mul_apply, hbx]
  have hbx2 : σb (σa (σa x)) = σa (σa x) := by
    rw [← Perm.mul_apply, ← hab, Perm.mul_apply, hbx1]
  have hxF : x ∉ σa.supportᶜ := by rw [memF]; exact hx
  have hx1F : σa x ∉ σa.supportᶜ := by rw [memF]; exact hx1
  have hx2F : σa (σa x) ∉ σa.supportᶜ := by
    rw [memF]
    intro h
    exact hx1 (σa.injective h)
  have hfx : f ≠ x := fun h => hxF (h ▸ hfF)
  have hfx1 : f ≠ σa x := fun h => hx1F (h ▸ hfF)
  have hfx2 : f ≠ σa (σa x) := fun h => hx2F (h ▸ hfF)
  have hfb : f ∈ σb.supportᶜ := (memF σb f).2 hbf
  have hxb : x ∈ σb.supportᶜ := (memF σb x).2 hbx
  have hx1b : σa x ∈ σb.supportᶜ := (memF σb _).2 hbx1
  have hx2b : σa (σa x) ∈ σb.supportᶜ := (memF σb _).2 hbx2
  have h4 : 4 ≤ σb.supportᶜ.card := by
    have hsub : ({f, x, σa x, σa (σa x)} : Finset α) ⊆ σb.supportᶜ := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl | rfl <;> assumption
    have hcard : ({f, x, σa x, σa (σa x)} : Finset α).card = 4 := by
      rw [Finset.card_insert_of_notMem (by simp [hfx, hfx1, hfx2]),
        Finset.card_insert_of_notMem (by simp [Ne.symm hx, Ne.symm hx2]),
        Finset.card_pair (Ne.symm hx1)]
    exact hcard ▸ Finset.card_le_card hsub
  have hF4 : 4 ≤ σa.supportᶜ.card := by omega
  rcases Nat.lt_or_ge 4 σb.supportᶜ.card with h5 | h5
  ·
    refine ⟨Equiv.swap f (σa x) * Equiv.swap f x, σa x, hx1F, Or.inl ⟨h5, ?_⟩, ?_⟩
    · refine mem_altOn.2 ⟨(Perm.isThreeCycle_swap_mul_swap_same hfx1 hfx
        hx).mem_alternatingGroup, ?_⟩
      intro z hz
      have h1 := Perm.support_mul_le (Equiv.swap f (σa x)) (Equiv.swap f x) hz
      rw [Perm.support_swap hfx1, Perm.support_swap hfx] at h1
      simp only [Finset.sup_eq_union, Finset.mem_union, Finset.mem_insert,
        Finset.mem_singleton] at h1
      rcases h1 with (h | h) | (h | h) <;> (subst h; assumption)
    · refine altOn_insert_le hF4 hfF hx1F ?_ ?_
      · rw [Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne (Ne.symm hfx1) hx,
          Equiv.swap_apply_right]
      · intro z hz hzf
        have hzx : z ≠ x := fun h => hxF (h ▸ hz)
        have hzx1 : z ≠ σa x := fun h => hx1F (h ▸ hz)
        rw [Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hzf hzx,
          Equiv.swap_apply_of_ne_of_ne hzf hzx1]
  ·
    have h4' : σb.supportᶜ.card = 4 := by omega
    have hnd : [f, x, σa x, σa (σa x)].Nodup := by
      simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, List.not_mem_nil,
        List.nodup_nil, not_or, or_false]
      exact ⟨⟨hfx, hfx1, hfx2⟩, ⟨Ne.symm hx, Ne.symm hx2⟩, Ne.symm hx1, not_false, trivial⟩
    refine ⟨Equiv.swap f x * Equiv.swap (σa x) (σa (σa x)), x, hxF,
      Or.inr ⟨h4', swap_mul_swap_mem_kleinOn h4' hnd hfb hxb hx1b hx2b⟩, ?_⟩
    refine altOn_insert_le hF4 hfF hxF ?_ ?_
    · rw [Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne (Ne.symm hx) (Ne.symm hx2),
        Equiv.swap_apply_right]
    · intro z hz hzf
      have hzx : z ≠ x := fun h => hxF (h ▸ hz)
      have hzx1 : z ≠ σa x := fun h => hx1F (h ▸ hz)
      have hzx2 : z ≠ σa (σa x) := fun h => hx2F (h ▸ hz)
      rw [Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hzx1 hzx2,
        Equiv.swap_apply_of_ne_of_ne hzf hzx]

end PermFacts

section AltTransport

open Equiv

@[expose] noncomputable def conjEquivAlt (n : ℕ) (h5 : 5 ≤ n) (h6 : n ≠ 6) :
    Perm (Fin n) ≃* MulAut ↥(alternatingGroup (Fin n)) :=
  MulEquiv.ofBijective (MulAut.conjNormal (H := alternatingGroup (Fin n)))
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n h5 h6)

variable {Y : Type} [Group Y] {K : Subgroup Y} {n : ℕ}

@[expose] noncomputable def permHom (e : ↥K ≃* ↥(alternatingGroup (Fin n))) (h5 : 5 ≤ n) (h6 : n ≠ 6) :
    ↥(Subgroup.normalizer (K : Set Y)) →* Perm (Fin n) :=
  (conjEquivAlt n h5 h6).symm.toMonoidHom.comp
    ((MulAut.congr e).toMonoidHom.comp K.normalizerMonoidHom)

@[expose] noncomputable def theta (e : ↥K ≃* ↥(alternatingGroup (Fin n))) : ↥K →* Perm (Fin n) :=
  (alternatingGroup (Fin n)).subtype.comp e.toMonoidHom

@[expose] noncomputable def thetaInv (e : ↥K ≃* ↥(alternatingGroup (Fin n))) :
    ↥(alternatingGroup (Fin n)) →* Y :=
  K.subtype.comp e.symm.toMonoidHom

theorem theta_injective (e : ↥K ≃* ↥(alternatingGroup (Fin n))) : Function.Injective (theta e) :=
  (alternatingGroup (Fin n)).subtype_injective.comp e.injective

theorem thetaInv_injective (e : ↥K ≃* ↥(alternatingGroup (Fin n))) :
    Function.Injective (thetaInv e) :=
  K.subtype_injective.comp e.symm.injective

theorem theta_apply (e : ↥K ≃* ↥(alternatingGroup (Fin n))) (k : ↥K) :
    theta e k = ((e k : ↥(alternatingGroup (Fin n))) : Perm (Fin n)) := rfl

theorem theta_symm (e : ↥K ≃* ↥(alternatingGroup (Fin n))) (u : ↥(alternatingGroup (Fin n))) :
    theta e (e.symm u) = u := by
  rw [theta_apply, MulEquiv.apply_symm_apply]

theorem theta_conj (e : ↥K ≃* ↥(alternatingGroup (Fin n))) (h5 : 5 ≤ n) (h6 : n ≠ 6)
    (b : ↥(Subgroup.normalizer (K : Set Y))) (k : ↥K) :
    theta e (K.normalizerMonoidHom b k) =
      permHom e h5 h6 b * theta e k * (permHom e h5 h6 b)⁻¹ := by
  have h : conjEquivAlt n h5 h6 (permHom e h5 h6 b) = MulAut.congr e (K.normalizerMonoidHom b) := by
    simp [permHom]
  have h2 := congrArg (fun ψ : MulAut ↥(alternatingGroup (Fin n)) =>
    ((ψ (e k) : ↥(alternatingGroup (Fin n))) : Perm (Fin n))) h
  simpa [conjEquivAlt, MulAut.conjNormal_apply, theta] using h2.symm

theorem comm_iff_theta (e : ↥K ≃* ↥(alternatingGroup (Fin n))) (h5 : 5 ≤ n) (h6 : n ≠ 6)
    (b : ↥(Subgroup.normalizer (K : Set Y))) (k : ↥K) :
    (k : Y) * b = b * k ↔ theta e k * permHom e h5 h6 b = permHom e h5 h6 b * theta e k := by
  have hc := theta_conj e h5 h6 b k
  have hco : ((K.normalizerMonoidHom b k : ↥K) : Y) = (b : Y) * k * (b : Y)⁻¹ :=
    K.normalizerMonoidHom_apply_apply_coe b k
  constructor
  · intro h
    have hk : K.normalizerMonoidHom b k = k := by
      apply Subtype.ext
      rw [hco, ← h]
      group
    rw [hk] at hc
    calc theta e k * permHom e h5 h6 b
        = (permHom e h5 h6 b * theta e k * (permHom e h5 h6 b)⁻¹) * permHom e h5 h6 b := by
          rw [← hc]
      _ = permHom e h5 h6 b * theta e k := by group
  · intro h
    have h1 : theta e (K.normalizerMonoidHom b k) = theta e k := by
      rw [hc, ← h]
      group
    have h2 := congrArg Subtype.val (theta_injective e h1)
    rw [hco] at h2
    calc (k : Y) * b = ((b : Y) * k * (b : Y)⁻¹) * b := by rw [h2]
      _ = b * k := by group

theorem map_theta_centralizer (e : ↥K ≃* ↥(alternatingGroup (Fin n))) (h5 : 5 ≤ n) (h6 : n ≠ 6)
    (b : ↥(Subgroup.normalizer (K : Set Y))) :
    ((K ⊓ Subgroup.centralizer ({(b : Y)} : Set Y)).subgroupOf K).map (theta e) =
      cA (permHom e h5 h6 b) := by
  ext g
  constructor
  · intro hg
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hg
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff] at hk
    exact mem_cA.2 ⟨(e k).2, (comm_iff_theta e h5 h6 b k).1 hk.2⟩
  · intro hg
    obtain ⟨hgA, hgc⟩ := mem_cA.1 hg
    have hθ : theta e (e.symm ⟨g, hgA⟩) = g := by rw [theta_symm]
    refine Subgroup.mem_map.2 ⟨e.symm ⟨g, hgA⟩, ?_, hθ⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    refine ⟨(e.symm ⟨g, hgA⟩).2, (comm_iff_theta e h5 h6 b _).2 ?_⟩
    rw [hθ]
    exact hgc

theorem pull_push (e : ↥K ≃* ↥(alternatingGroup (Fin n))) {H : Subgroup Y} (hHK : H ≤ K) :
    (((H.subgroupOf K).map (theta e)).subgroupOf (alternatingGroup (Fin n))).map (thetaInv e) =
      H := by
  ext y
  constructor
  · intro hy
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hy
    rw [Subgroup.mem_subgroupOf] at hu
    obtain ⟨k, hk, hku⟩ := Subgroup.mem_map.1 hu
    have hk' : e k = u := Subtype.ext hku
    rw [Subgroup.mem_subgroupOf] at hk
    show ((e.symm u : ↥K) : Y) ∈ H
    rw [← hk', MulEquiv.symm_apply_apply]
    exact hk
  · intro hy
    refine Subgroup.mem_map.2 ⟨e ⟨y, hHK hy⟩, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf]
      exact Subgroup.mem_map.2 ⟨⟨y, hHK hy⟩, Subgroup.mem_subgroupOf.2 hy, rfl⟩
    · show ((e.symm (e ⟨y, hHK hy⟩) : ↥K) : Y) = y
      rw [MulEquiv.symm_apply_apply]

variable [Finite Y]

theorem glaPComponent_push (e : ↥K ≃* ↥(alternatingGroup (Fin n))) {X Q : Subgroup Y}
    (hXK : X ≤ K) (hQ : GLAPComponent 3 X Q) :
    GLAPComponent 3 ((X.subgroupOf K).map (theta e)) ((Q.subgroupOf K).map (theta e)) := by
  have h1 := Prop126b.glaPComponent_subgroupOf Nat.prime_three hXK hQ
  refine glaPComponent_map Nat.prime_three (theta e) ?_ h1
  rw [(MonoidHom.ker_eq_bot_iff _).2 (theta_injective e), inf_bot_eq, Subgroup.card_bot]
  exact Nat.coprime_one_right 3

theorem glaPComponent_pull (e : ↥K ≃* ↥(alternatingGroup (Fin n)))
    {X Q : Subgroup (Perm (Fin n))} (hX : X ≤ alternatingGroup (Fin n))
    (hQ : GLAPComponent 3 X Q) :
    GLAPComponent 3 ((X.subgroupOf (alternatingGroup (Fin n))).map (thetaInv e))
      ((Q.subgroupOf (alternatingGroup (Fin n))).map (thetaInv e)) := by
  have h1 := Prop126b.glaPComponent_subgroupOf Nat.prime_three hX hQ
  refine glaPComponent_map Nat.prime_three (thetaInv e) ?_ h1
  rw [(MonoidHom.ker_eq_bot_iff _).2 (thetaInv_injective e), inf_bot_eq, Subgroup.card_bot]
  exact Nat.coprime_one_right 3

end AltTransport

section BarZ3

@[expose] noncomputable def barZ3Congr {Y₁ Y₂ : Type} [Group Y₁] [Group Y₂] {Q₁ : Subgroup Y₁}
    {Q₂ : Subgroup Y₂} (f : ↥Q₁ ≃* ↥Q₂) : Prop126b.barZ3 Q₁ ≃* Prop126b.barZ3 Q₂ :=
  l119_centerQuot_equiv (Prop126b.barCongr 3 f)

theorem barZ3_simple {Y₁ : Type} [Group Y₁] [Finite Y₁] {S : Subgroup Y₁} (hs : IsSimpleGroup ↥S)
    (hnc : ∃ x y : ↥S, x * y ≠ y * x) (h3 : 3 ∣ Nat.card ↥S) :
    Nonempty (Prop126b.barZ3 S ≃* ↥S) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcore : GLAPPrimeCore 3 ↥S = ⊥ := by
    rcases (GLAPPrimeCore.normal 3 ↥S).eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      have hcop : Nat.Coprime 3 (Nat.card ↥(GLAPPrimeCore 3 ↥S)) := CFSG.pPrimeCore_coprime_card
      rw [h, Subgroup.card_top] at hcop
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hcop h3
  have e1 : (↥S ⧸ GLAPPrimeCore 3 ↥S) ≃* ↥S :=
    (QuotientGroup.quotientMulEquivOfEq hcore).trans QuotientGroup.quotientBot
  have hZ : Subgroup.center ↥S = ⊥ := by
    rcases (inferInstance : (Subgroup.center ↥S).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      obtain ⟨x, y, hxy⟩ := hnc
      have hx : x ∈ Subgroup.center ↥S := h ▸ Subgroup.mem_top x
      exact hxy ((Subgroup.mem_center_iff.1 hx y).symm)
  exact ⟨(l119_centerQuot_equiv e1).trans
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot)⟩

theorem factorial_eq_of_alt_equiv {m k : ℕ} (hm : 2 ≤ m) (hk : 2 ≤ k)
    (f : ↥(alternatingGroup (Fin m)) ≃* ↥(alternatingGroup (Fin k))) :
    m.factorial / 2 = k.factorial / 2 := by
  rw [← Prop126b.card_alt' m hm, ← Prop126b.card_alt' k hk]
  exact Nat.card_congr f.toEquiv

end BarZ3

section AnCent

theorem nonempty_quot_center_quot {K : Type*} [Group K] (hperf : commutator K = ⊤)
    (N : Subgroup K) [N.Normal] (hN : N ≤ Subgroup.center K) :
    Nonempty (((K ⧸ N) ⧸ Subgroup.center (K ⧸ N)) ≃* (K ⧸ Subgroup.center K)) := by
  set f : K →* (K ⧸ N) ⧸ Subgroup.center (K ⧸ N) :=
    (QuotientGroup.mk' (Subgroup.center (K ⧸ N))).comp (QuotientGroup.mk' N) with hfdef
  have hf : Function.Surjective f :=
    (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)
  set X : Subgroup K := (Subgroup.center (K ⧸ N)).comap (QuotientGroup.mk' N) with hX
  have hXc : X ≤ Subgroup.center K := by
    have h1 : ⁅(⊤ : Subgroup K), X⁆ ≤ N := by
      rw [Subgroup.commutator_le]
      intro k _ y hy
      rw [← QuotientGroup.eq_one_iff]
      show QuotientGroup.mk' N ⁅k, y⁆ = 1
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_center_iff.1 hy (QuotientGroup.mk' N k))
    have h2 : ⁅⁅(⊤ : Subgroup K), X⁆, (⊤ : Subgroup K)⁆ = ⊥ := by
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro c hc k _
      have hcz : c ∈ Subgroup.center K := hN (h1 hc)
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_center_iff.1 hcz k).symm
    have hP : Group.IsPerfect ↥(⊤ : Subgroup K) := by
      refine Subgroup.isPerfect_iff.2 ?_
      rw [← commutator_def, hperf]
    have h3 := CFSG.LocalCores.perfect_double_commutator hP h2
    intro y hy
    rw [Subgroup.mem_center_iff]
    intro k
    have hm : ⁅k, y⁆ ∈ ⁅(⊤ : Subgroup K), X⁆ := Subgroup.commutator_mem_commutator (Subgroup.mem_top k) hy
    rw [h3, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hm
    exact hm
  have hker : f.ker = Subgroup.center K := by
    ext x
    rw [MonoidHom.mem_ker]
    constructor
    · intro hx
      have hx' : QuotientGroup.mk' (Subgroup.center (K ⧸ N)) (QuotientGroup.mk' N x) = 1 := hx
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx'
      exact hXc hx'
    · intro hx
      show QuotientGroup.mk' _ (QuotientGroup.mk' N x) = 1
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_center_iff]
      intro g
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
      show QuotientGroup.mk' N g * QuotientGroup.mk' N x = QuotientGroup.mk' N x * QuotientGroup.mk' N g
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hx g]
  exact ⟨(QuotientGroup.quotientKerEquivOfSurjective f hf).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hker)⟩

variable {Y : Type} [Group Y] [Finite Y]

theorem barZ3_of_glaPComponent_alt {K : Subgroup Y} {n : ℕ} (h5 : 5 ≤ n) (h6 : n ≠ 6)
    (e : ↥K ≃* ↥(alternatingGroup (Fin n))) {b : Y} (hb : b ∈ Subgroup.normalizer (K : Set Y))
    (hb3 : b ^ 3 = 1) {Q : Subgroup Y}
    (hQ : GLAPComponent 3 (K ⊓ Subgroup.centralizer ({b} : Set Y)) Q) :
    ∃ m : ℕ, 5 ≤ m ∧ m % 3 = n % 3 ∧
      Nonempty (Prop126b.barZ3 Q ≃* ↥(alternatingGroup (Fin m))) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set bN : ↥(Subgroup.normalizer (K : Set Y)) := ⟨b, hb⟩ with hbN
  set σ := permHom e h5 h6 bN with hσ
  have hσ3 : σ ^ 3 = 1 := by
    rw [hσ, ← map_pow]
    have : bN ^ 3 = 1 := Subtype.ext (by simpa [hbN] using hb3)
    rw [this, map_one]
  have hQK : Q ≤ K := hQ.1.trans inf_le_left
  have hpush := glaPComponent_push e inf_le_left hQ
  have hmap : ((K ⊓ Subgroup.centralizer ({b} : Set Y)).subgroupOf K).map (theta e) = cA σ :=
    map_theta_centralizer e h5 h6 bN
  rw [hmap] at hpush
  obtain ⟨hQeq, hm5⟩ := glaPComponent_cA hσ3 hpush
  refine ⟨σ.supportᶜ.card, hm5, ?_, ?_⟩
  · have := Equiv.Perm.card_compl_support_modEq (p := 3) (n := 1) (σ := σ)
      (by rw [pow_one]; exact hσ3)
    rw [Fintype.card_fin] at this
    exact this
  · have e1 : ↥Q ≃* ↥((Q.subgroupOf K).map (theta e)) :=
      (Subgroup.subgroupOfEquivOfLe hQK).symm.trans
        ((Q.subgroupOf K).equivMapOfInjective _ (theta_injective e))
    have e2 : ↥((Q.subgroupOf K).map (theta e)) ≃* ↥(altOn σ.supportᶜ) :=
      MulEquiv.subgroupCongr hQeq
    obtain ⟨e3⟩ := barZ3_simple (isSimpleGroup_altOn hm5) (altOn_noncomm hm5)
      (three_dvd_card_altOn hm5)
    exact ⟨(barZ3Congr (e1.trans e2)).trans (e3.trans (altOnEquiv _))⟩

theorem inputAnCent_of_inputs (hAC : Prop126b.InputAltCentre) : Prop126b.InputAnCent := by
  intro Y _ _ K n hn8 hn3 hq hAn b hbN hb3 _ Q hQ
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set M : Subgroup Y := Subgroup.normalizer (K : Set Y) with hM
  have hKM : K ≤ M := Subgroup.le_normalizer
  have hKn : (K.subgroupOf M).Normal := Subgroup.normal_in_normalizer
  have hKsn : IsSubnormal K M := IsSubnormal.step hKM hKn (IsSubnormal.refl M)
  have hbM : b ∈ M := hbN
  have hb3' : b ^ 3 = 1 := by rw [← hb3]; exact pow_orderOf_eq_one b
  set K₁ : Subgroup (↥M ⧸ GLAPPrimeCore 3 ↥M) := barX 3 M K with hK₁
  have eK : (↥K ⧸ GLAPPrimeCore 3 ↥K) ≃* ↥K₁ := quotEquivBarX Nat.prime_three hKM hKsn
  have h3K : 3 ∣ Nat.card ↥K := by
    obtain ⟨f⟩ := hAn
    have h1 : 3 ∣ Nat.card (↥K ⧸ Subgroup.center ↥K) := by
      rw [Nat.card_congr f.toEquiv, Prop126b.card_alt' n (by omega)]
      exact dvd_factorial_div_two (by norm_num) (by norm_num) (by omega) (by omega)
    exact h1.trans (Subgroup.card_quotient_dvd_card _)
  have hcoreK : GLAPPrimeCore 3 ↥K ≠ ⊤ := by
    intro h
    have hcop : Nat.Coprime 3 (Nat.card ↥(GLAPPrimeCore 3 ↥K)) := CFSG.pPrimeCore_coprime_card
    rw [h, Subgroup.card_top] at hcop
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hcop h3K
  have hcoreZ : GLAPPrimeCore 3 ↥K ≤ Subgroup.center ↥K := l119_normal_le_center hq hcoreK
  haveI : Nontrivial (↥K ⧸ GLAPPrimeCore 3 ↥K) := by
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    apply hcoreK
    rw [eq_top_iff]
    intro x _
    have : (QuotientGroup.mk' (GLAPPrimeCore 3 ↥K) x) = 1 := Subsingleton.elim _ _
    exact (QuotientGroup.eq_one_iff x).1 this
  have hq0 : CFSG.Open.IsQuasisimple (↥K ⧸ GLAPPrimeCore 3 ↥K) :=
    CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.isQuasisimple_of_surjective_of_nontrivial
      hq (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  have hq1 : CFSG.Open.IsQuasisimple ↥K₁ :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv eK hq0
  have hK₁sn : IsSubnormal K₁ ⊤ := by
    have := isSubnormal_barX (C := M) 3 hKsn
    rwa [barX_self] at this
  have hcore1 : GLAPPrimeCore 3 ↥K₁ = ⊥ :=
    Prop126b.primeCore_sub_eq_bot Nat.prime_three (glaPPrimeCore_quotient_eq_bot Nat.prime_three)
      hK₁sn
  have hAn1 : IsAltType n (↥K₁ ⧸ Subgroup.center ↥K₁) := by
    obtain ⟨f⟩ := hAn
    obtain ⟨g⟩ := nonempty_quot_center_quot hq.1 (GLAPPrimeCore 3 ↥K) hcoreZ
    exact ⟨((l119_centerQuot_equiv eK).symm.trans g).trans f⟩
  obtain ⟨e₁⟩ := hAC ↥K₁ n hn8 hq1 hcore1 hAn1
  set β : ↥M ⧸ GLAPPrimeCore 3 ↥M := QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) ⟨b, hbM⟩ with hβ
  have hβN : β ∈ Subgroup.normalizer (K₁ : Set (↥M ⧸ GLAPPrimeCore 3 ↥M)) := by
    have h1 := l119_barX_gLBConj (p := 3) (C := M) (H := K) hbM hKM
    rw [mem_normalizer_iff_gLBConj_eq.1 hbN] at h1
    exact mem_normalizer_iff_gLBConj_eq.2 h1.symm
  have hβ3 : β ^ 3 = 1 := by
    rw [hβ, ← map_pow]
    have : (⟨b, hbM⟩ : ↥M) ^ 3 = 1 := Subtype.ext (by simpa using hb3')
    rw [this, map_one]
  have hd : IsPGroup 3 (Subgroup.zpowers b) := l119_isPGroup_zpowers hb3'
  have hQ1 := Prop126b.glaPComponent_barX_inf_centralizer Nat.prime_three hbM hKM hbN hd hQ
  obtain ⟨m, hm5, hm3, ⟨f⟩⟩ := barZ3_of_glaPComponent_alt (by omega) (by omega) e₁ hβN hβ3 hQ1
  refine ⟨m, hm5, by omega, ?_⟩
  have hQM : Q ≤ M := hQ.1.trans (inf_le_left.trans hKM)
  exact ⟨(l119_centerQuot_equiv (Prop126b.barOfBarX Nat.prime_three hQM)).trans f⟩

theorem inputAnCent_holds : Prop126b.InputAnCent :=
  inputAnCent_of_inputs SchurFacts.inputAltCentre_holds

end AnCent

section Input23_7

theorem card_eq_three_pow_pRank {Y : Type} [Group Y] [Finite Y] {B : Subgroup Y}
    (hB : IsElemAbelian 3 B) : Nat.card ↥B = 3 ^ CFSG.Open.pRank 3 B := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : IsPGroup 3 ↥B := by
    intro x
    exact ⟨1, Subtype.ext (by simpa using hB.2 x x.2)⟩
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  have hmem : k ∈ {j | ∃ E : Subgroup Y, E ≤ B ∧ IsElemAbelian 3 E ∧ Nat.card ↥E = 3 ^ j} :=
    ⟨B, le_rfl, hB, hk⟩
  have hbd : ∀ j ∈ {j | ∃ E : Subgroup Y, E ≤ B ∧ IsElemAbelian 3 E ∧ Nat.card ↥E = 3 ^ j},
      j ≤ k := by
    rintro j ⟨E, hEB, -, hE⟩
    have h1 : Nat.card ↥E ≤ Nat.card ↥B := Subgroup.card_le_of_le hEB
    rw [hE, hk] at h1
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h1
  have hr : CFSG.Open.pRank 3 B = k := by
    unfold CFSG.Open.pRank
    exact le_antisymm (csSup_le ⟨k, hmem⟩ hbd) (le_csSup ⟨k, hbd⟩ hmem)
  rw [hr, hk]

theorem primeCoreOf_map_of_injective {G G' : Type*} [Group G] [Group G'] (p : ℕ) (f : G →* G')
    (hf : Function.Injective f) (X : Subgroup G) :
    GLAPPrimeCoreOf p (X.map f) = (GLAPPrimeCoreOf p X).map f := by
  have h1 : GLAPPrimeCore p ↥(X.map f) =
      (GLAPPrimeCore p ↥X).map (Subgroup.equivMapOfInjective X f hf).toMonoidHom :=
    (CFSG.pPrimeCore_map_iso p (Subgroup.equivMapOfInjective X f hf)).symm
  have h2 : (X.map f).subtype.comp (Subgroup.equivMapOfInjective X f hf).toMonoidHom =
      f.comp X.subtype := by
    ext x
    rfl
  unfold GLAPPrimeCoreOf
  rw [h1, Subgroup.map_map, h2, Subgroup.map_map]

theorem false_of_central_product {I : Type} [Group I] [Finite I] {ι : Type}
    (Q : ι → Subgroup (I ⧸ CFSG.pCore 2 I)) (hQ : ∀ i, IsAltType 7 ↥(Q i) ∨ IsHatSeven ↥(Q i))
    (hcomm : ∀ i j, i ≠ j → ∀ x ∈ Q i, ∀ y ∈ Q j, x * y = y * x) (htop : (⨆ i, Q i) = ⊤)
    (S : Subgroup I) (hs : IsSimpleGroup ↥S) (hnc : ∃ x y : ↥S, x * y ≠ y * x)
    (hcard : 2520 < Nat.card ↥S) : False := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O : Subgroup I := CFSG.pCore 2 I with hO
  haveI : O.Normal := CFSG.pCore_normal (p := 2) (G := I)
  set π : I →* I ⧸ O := QuotientGroup.mk' O with hπ
  have hSO : O.subgroupOf S = ⊥ := by
    have hn : (O.subgroupOf S).Normal := Subgroup.Normal.subgroupOf inferInstance S
    rcases hn.eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      have hle : S ≤ O := Subgroup.subgroupOf_eq_top.1 h
      have hp : IsPGroup 2 ↥S := (CFSG.pCore_isPGroup (p := 2) (G := I)).to_le hle
      exact not_isPGroup_of_isQuasisimple Nat.prime_two (isQuasisimple_of_simple hs hnc) hp
  have hπS : ∀ s ∈ S, π s = 1 → s = 1 := by
    intro s hs' h1
    have hsO : s ∈ O := (QuotientGroup.eq_one_iff s).1 h1
    have : (⟨s, hs'⟩ : ↥S) ∈ O.subgroupOf S := Subgroup.mem_subgroupOf.2 hsO
    rw [hSO, Subgroup.mem_bot] at this
    exact congrArg Subtype.val this
  have hex : ∃ i, ∃ s ∈ S, ∃ q ∈ Q i, π s * q ≠ q * π s := by
    by_contra hcon
    push Not at hcon
    obtain ⟨x, y, hxy⟩ := hnc
    apply hxy
    have hle : (⨆ i, Q i) ≤ Subgroup.centralizer ({π x} : Set (I ⧸ O)) :=
      iSup_le fun i q hq => Subgroup.mem_centralizer_singleton_iff.2 (hcon i x x.2 q hq).symm
    have hcen : π x * π y = π y * π x :=
      (Subgroup.mem_centralizer_singleton_iff.1 (hle (htop ▸ Subgroup.mem_top (π y)))).symm
    have h1 : π ((x : I) * y * (x : I)⁻¹ * (y : I)⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcen]
      group
    have h2 := hπS _ (S.mul_mem (S.mul_mem (S.mul_mem x.2 y.2) (S.inv_mem x.2)) (S.inv_mem y.2)) h1
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    calc (x : I) * y = ((x : I) * y * (x : I)⁻¹ * (y : I)⁻¹) * (y * x) := by group
      _ = y * x := by rw [h2, one_mul]
  obtain ⟨i, s₀, hs₀, q₀, hq₀, hsq⟩ := hex
  have hQn : (Q i).Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← htop]
    refine iSup_le fun j => ?_
    by_cases hij : j = i
    · subst hij
      exact Subgroup.le_normalizer
    · intro x hx
      rw [Subgroup.mem_normalizer_iff]
      intro h
      have hc : ∀ w ∈ Q i, x * w * x⁻¹ = w := fun w hw => by
        rw [hcomm j i hij x hx w hw, mul_inv_cancel_right]
      constructor
      · intro hh
        rw [hc h hh]
        exact hh
      · intro hh
        have h2 : x * (x * h * x⁻¹) * x⁻¹ = x * h * x⁻¹ := hc _ hh
        have h3 : h = x * h * x⁻¹ := by
          calc h = x⁻¹ * (x * h * x⁻¹) * x := by group
            _ = x⁻¹ * (x * (x * h * x⁻¹) * x⁻¹) * x := by rw [h2]
            _ = x * h * x⁻¹ := by group
        rw [h3]
        exact hh
  haveI := hQn
  set N : Subgroup (I ⧸ O) := Subgroup.centralizer (Q i : Set (I ⧸ O)) with hN
  haveI : N.Normal := Subgroup.normal_centralizer
  have hsup : Q i ⊔ N = ⊤ := by
    rw [eq_top_iff, ← htop]
    refine iSup_le fun j => ?_
    by_cases hij : j = i
    · subst hij
      exact le_sup_left
    · refine le_sup_of_le_right fun x hx => ?_
      rw [hN, Subgroup.mem_centralizer_iff]
      intro w hw
      exact (hcomm j i hij x hx w hw).symm
  set φ : ↥S →* (I ⧸ O) ⧸ N := (QuotientGroup.mk' N).comp (π.comp S.subtype) with hφ
  have hφinj : Function.Injective φ := by
    rcases (φ.normal_ker).eq_bot_or_eq_top with h | h
    · exact (MonoidHom.ker_eq_bot_iff φ).1 h
    · exfalso
      apply hsq
      have hmem : (⟨s₀, hs₀⟩ : ↥S) ∈ φ.ker := h ▸ Subgroup.mem_top _
      rw [MonoidHom.mem_ker] at hmem
      have hN' : π s₀ ∈ N := (QuotientGroup.eq_one_iff _).1 hmem
      rw [hN, Subgroup.mem_centralizer_iff] at hN'
      exact (hN' q₀ hq₀).symm
  have hφQ : φ.range ≤ (Q i).map (QuotientGroup.mk' N) := by
    rintro _ ⟨s, rfl⟩
    have hmem : π s ∈ ((Q i ⊔ N : Subgroup (I ⧸ O)) : Set (I ⧸ O)) := by
      rw [hsup]
      exact Subgroup.mem_top _
    rw [Subgroup.mul_normal (Q i) N, Set.mem_mul] at hmem
    obtain ⟨q, hq, c, hc, hqc⟩ := hmem
    refine ⟨q, hq, ?_⟩
    show QuotientGroup.mk' N q = QuotientGroup.mk' N (π s)
    have hc1 : QuotientGroup.mk' N c = 1 := (QuotientGroup.eq_one_iff c).2 hc
    rw [← hqc, map_mul, hc1, mul_one]
  have hcardQ : Nat.card ↥((Q i).map (QuotientGroup.mk' N)) ≤ 2520 := by
    have h2520 : Nat.card (↥(Q i) ⧸ Subgroup.center ↥(Q i)) = 2520 := by
      obtain ⟨f⟩ := Prop126b.isAltType_seven_quot_center (hQ i)
      rw [Nat.card_congr f.toEquiv, Prop126b.card_alt' 7 (by norm_num)]
      rfl
    set ψ : ↥(Q i) →* ↥((Q i).map (QuotientGroup.mk' N)) := (QuotientGroup.mk' N).subgroupMap (Q i)
    have hψ : Function.Surjective ψ := (QuotientGroup.mk' N).subgroupMap_surjective (Q i)
    have hZ : Subgroup.center ↥(Q i) ≤ ψ.ker := by
      intro z hz
      rw [MonoidHom.mem_ker]
      apply Subtype.ext
      show QuotientGroup.mk' N (z : I ⧸ O) = 1
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hN, Subgroup.mem_centralizer_iff]
      intro w hw
      have := Subgroup.mem_center_iff.1 hz ⟨w, hw⟩
      exact congrArg Subtype.val this
    set ψ' := QuotientGroup.lift (Subgroup.center ↥(Q i)) ψ hZ
    have hψ' : Function.Surjective ψ' := by
      intro t
      obtain ⟨u, rfl⟩ := hψ t
      exact ⟨QuotientGroup.mk u, rfl⟩
    calc Nat.card ↥((Q i).map (QuotientGroup.mk' N))
        ≤ Nat.card (↥(Q i) ⧸ Subgroup.center ↥(Q i)) := Nat.card_le_card_of_surjective ψ' hψ'
      _ = 2520 := h2520
  have h1 : Nat.card ↥S ≤ Nat.card ↥((Q i).map (QuotientGroup.mk' N)) :=
    calc Nat.card ↥S = Nat.card ↥φ.range := Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv
      _ ≤ _ := Subgroup.card_le_of_le hφQ
  omega

section Transport23

open Equiv

variable {Y : Type} [Group Y] {K : Subgroup Y} {n : ℕ}

theorem pull_mono (e : ↥K ≃* ↥(alternatingGroup (Fin n))) {X X' : Subgroup (Perm (Fin n))}
    (h : X ≤ X') :
    (X.subgroupOf (alternatingGroup (Fin n))).map (thetaInv e) ≤
      (X'.subgroupOf (alternatingGroup (Fin n))).map (thetaInv e) :=
  Subgroup.map_mono fun _ hx => h hx

theorem primeCoreOf_pull (e : ↥K ≃* ↥(alternatingGroup (Fin n))) {X : Subgroup (Perm (Fin n))}
    (hX : X ≤ alternatingGroup (Fin n)) {u : ↥(alternatingGroup (Fin n))}
    (hu : (u : Perm (Fin n)) ∈ GLAPPrimeCoreOf 3 X) :
    thetaInv e u ∈ GLAPPrimeCoreOf 3 ((X.subgroupOf (alternatingGroup (Fin n))).map (thetaInv e)) := by
  rw [primeCoreOf_map_of_injective 3 _ (thetaInv_injective e)]
  refine Subgroup.mem_map_of_mem _ ?_
  have hXeq : (X.subgroupOf (alternatingGroup (Fin n))).map (alternatingGroup (Fin n)).subtype = X :=
    Subgroup.map_subgroupOf_eq_of_le hX
  rw [← hXeq, primeCoreOf_map_of_injective 3 _ (alternatingGroup (Fin n)).subtype_injective] at hu
  obtain ⟨v, hv, hvu⟩ := Subgroup.mem_map.1 hu
  have : v = u := Subtype.ext hvu
  rw [← this]
  exact hv

theorem gLBConj_push_le (e : ↥K ≃* ↥(alternatingGroup (Fin n))) {J : Subgroup Y} (hJK : J ≤ K)
    {g : Y} (hgK : g ∈ K) :
    GLBConj (theta e ⟨g, hgK⟩) ((J.subgroupOf K).map (theta e)) ≤
      ((GLBConj g J).subgroupOf K).map (theta e) := by
  intro z hz
  rw [mem_gLBConj] at hz
  obtain ⟨j, hj, hjz⟩ := Subgroup.mem_map.1 hz
  set gK : ↥K := ⟨g, hgK⟩
  refine Subgroup.mem_map.2 ⟨gK⁻¹ * j * gK, ?_, ?_⟩
  · rw [Subgroup.mem_subgroupOf, mem_gLBConj]
    have : g * ((gK⁻¹ * j * gK : ↥K) : Y) * g⁻¹ = j := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, gK]
      group
    rw [this]
    exact Subgroup.mem_subgroupOf.1 hj
  · rw [map_mul, map_mul, map_inv, hjz]
    group

theorem altOn_le_alt {α : Type} [Fintype α] [DecidableEq α] (T : Finset α) :
    altOn T ≤ alternatingGroup α := fun _ hg => (mem_altOn.1 hg).1

theorem cA_le_alt {α : Type} [Fintype α] [DecidableEq α] (σ : Perm α) :
    cA σ ≤ alternatingGroup α := inf_le_left

end Transport23

theorem input23_7_amb_holds : Prop126b.Input23_7_amb := by
  intro Y _ _ K B n hn8 hn3 hKalt hBN hBel hfaith a haB ha1 J hJ hJty W hW I hI hcp
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e⟩ := hKalt
  have h5 : 5 ≤ n := by omega
  have h6 : n ≠ 6 := by omega
  set ρ : ↥B →* Equiv.Perm (Fin n) := (permHom e h5 h6).comp (Subgroup.inclusion hBN) with hρ
  have hρapp : ∀ b : ↥B, ρ b = permHom e h5 h6 ⟨b, hBN b.2⟩ := fun b => rfl
  have hB3 : ∀ b ∈ B, b ^ 3 = 1 := fun b hb => hBel.2 b hb
  have hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hBel.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hσ3 : ∀ b : ↥B, ρ b ^ 3 = 1 := by
    intro b
    rw [← map_pow]
    have : b ^ 3 = 1 := Subtype.ext (by simpa using hB3 b b.2)
    rw [this, map_one]
  have hσc : ∀ b c : ↥B, ρ b * ρ c = ρ c * ρ b := by
    intro b c
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hBc b b.2 c c.2)
  have hρinj : Function.Injective ρ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro b hb
    rw [MonoidHom.mem_ker] at hb
    rw [Subgroup.mem_bot]
    by_contra hb1
    obtain ⟨q, hqK, hq⟩ := hfaith b b.2 (fun h => hb1 (Subtype.ext h))
    apply hq
    have h1 : theta e ⟨q, hqK⟩ * permHom e h5 h6 ⟨b, hBN b.2⟩ =
        permHom e h5 h6 ⟨b, hBN b.2⟩ * theta e ⟨q, hqK⟩ := by
      have : permHom e h5 h6 ⟨b, hBN b.2⟩ = 1 := hb
      rw [this, one_mul, mul_one]
    exact ((comm_iff_theta e h5 h6 ⟨b, hBN b.2⟩ ⟨q, hqK⟩).2 h1).symm
  set aB : ↥B := ⟨a, haB⟩ with haBdef
  set σa := ρ aB with hσa
  have hJK : J ≤ K := hJ.1.trans inf_le_left
  have hJpush := glaPComponent_push e inf_le_left hJ
  have hmapA : ((K ⊓ Subgroup.centralizer ({a} : Set Y)).subgroupOf K).map (theta e) = cA σa :=
    map_theta_centralizer e h5 h6 ⟨a, hBN haB⟩
  rw [hmapA] at hJpush
  obtain ⟨hJeq, hJ5⟩ := glaPComponent_cA (hσ3 aB) hJpush
  change (J.subgroupOf K).map (theta e) = altOn σa.supportᶜ at hJeq
  change 5 ≤ σa.supportᶜ.card at hJ5
  have hF7 : σa.supportᶜ.card = 7 := by
    obtain ⟨f7⟩ := hJty
    have e1 : ↥J ≃* ↥(altOn σa.supportᶜ) := ((Subgroup.subgroupOfEquivOfLe hJK).symm.trans
        ((J.subgroupOf K).equivMapOfInjective _ (theta_injective e))).trans
      (MulEquiv.subgroupCongr hJeq)
    obtain ⟨e3⟩ := barZ3_simple (isSimpleGroup_altOn hJ5) (altOn_noncomm hJ5)
      (three_dvd_card_altOn hJ5)
    have fm : ↥(alternatingGroup (Fin σa.supportᶜ.card)) ≃* ↥(alternatingGroup (Fin 7)) :=
      (altOnEquiv _).symm.trans (e3.symm.trans ((barZ3Congr e1).symm.trans f7))
    have hfac := factorial_eq_of_alt_equiv (by omega) (by norm_num) fm
    have h7 : Nat.factorial 7 / 2 = 2520 := rfl
    rw [h7] at hfac
    by_contra hne
    rcases Nat.lt_or_ge σa.supportᶜ.card 7 with hlt | hge
    · have h1 : (σa.supportᶜ.card).factorial ≤ Nat.factorial 6 := Nat.factorial_le (by omega)
      have h2 : Nat.factorial 6 = 720 := rfl
      omega
    · have h1 : Nat.factorial 8 ≤ (σa.supportᶜ.card).factorial := Nat.factorial_le (by omega)
      have h2 : Nat.factorial 8 = 40320 := rfl
      omega
  have hfree : ∀ b : ↥B, b ≠ 1 → ∀ x, σa x ≠ x → ρ b x ≠ x := by
    intro b hb1 x hx hbx
    have hbY : (b : Y) ≠ 1 := fun h => hb1 (Subtype.ext h)
    set σb := ρ b with hσb
    obtain ⟨c, y, hyF, hcases, hgen⟩ := perm_key (hσ3 b) (hσ3 aB) (hσc aB b) hF7 hx hbx
    have hmapB : ((K ⊓ Subgroup.centralizer ({(b : Y)} : Set Y)).subgroupOf K).map (theta e) =
        cA σb := map_theta_centralizer e h5 h6 ⟨b, hBN b.2⟩
    have hpullB : ((cA σb).subgroupOf (alternatingGroup (Fin n))).map (thetaInv e) =
        K ⊓ Subgroup.centralizer ({(b : Y)} : Set Y) := by
      rw [← hmapB]
      exact pull_push e inf_le_left
    have hcA : c ∈ alternatingGroup (Fin n) := by
      rcases hcases with ⟨-, hc⟩ | ⟨h4, hc⟩
      · exact (mem_altOn.1 hc).1
      · exact (mem_altOn.1 ((mem_kleinOn h4).1 hc).1).1
    set g : Y := thetaInv e ⟨c, hcA⟩ with hg
    have hgK : g ∈ K := (e.symm ⟨c, hcA⟩).2
    have hθg : theta e ⟨g, hgK⟩ = c := theta_symm e ⟨c, hcA⟩
    have hWb : GLAPPrimeCoreOf 3 (K ⊓ Subgroup.centralizer ({(b : Y)} : Set Y)) ⊔
        GLAPLayer 3 (K ⊓ Subgroup.centralizer ({(b : Y)} : Set Y)) ≤ W := by
      rw [hW]
      exact le_iSup_of_le (b : Y) (le_iSup_of_le b.2 (le_iSup_of_le hbY le_rfl))
    have hgW : g ∈ W := by
      rcases hcases with ⟨h5b, hc⟩ | ⟨h4, hc⟩
      · have hL := glaPComponent_pull e (cA_le_alt σb) (glaPComponent_altOn σb h5b)
        rw [hpullB] at hL
        have hgL : g ∈ ((altOn σb.supportᶜ).subgroupOf (alternatingGroup (Fin n))).map
            (thetaInv e) := Subgroup.mem_map.2 ⟨⟨c, hcA⟩, Subgroup.mem_subgroupOf.2 hc, rfl⟩
        have hLle : ((altOn σb.supportᶜ).subgroupOf (alternatingGroup (Fin n))).map (thetaInv e) ≤
            GLAPLayer 3 (K ⊓ Subgroup.centralizer ({(b : Y)} : Set Y)) := le_sSup hL
        exact hWb (Subgroup.mem_sup_right (hLle hgL))
      · have hcO : c ∈ GLAPPrimeCoreOf 3 (cA σb) := kleinOn_le_core σb h4 hc
        have h1 := primeCoreOf_pull e (cA_le_alt σb) (u := ⟨c, hcA⟩) hcO
        rw [hpullB] at h1
        exact hWb (Subgroup.mem_sup_left h1)
    have hJI : J ≤ I := by
      rw [hI]
      refine le_iSup₂_of_le 1 W.one_mem ?_
      rw [gLBConj_one]
    have hJgI : GLBConj g J ≤ I := by
      rw [hI]
      exact le_iSup₂_of_le g hgW le_rfl
    have hJgK : GLBConj g J ≤ K :=
      calc GLBConj g J ≤ GLBConj g K := gLBConj_mono g hJK
        _ = K := gLBConj_eq_of_mem_normalizer (Subgroup.le_normalizer hgK)
    set T : Finset (Fin n) := insert y σa.supportᶜ with hT
    have hT8 : T.card = 8 := by rw [hT, Finset.card_insert_of_notMem hyF, hF7]
    set S : Subgroup Y := ((altOn T).subgroupOf (alternatingGroup (Fin n))).map (thetaInv e) with hS
    have hS_le : S ≤ J ⊔ GLBConj g J := by
      have h1 : altOn T ≤ ((J ⊔ GLBConj g J).subgroupOf K).map (theta e) := by
        refine hgen.trans ?_
        rw [Subgroup.subgroupOf_sup hJK hJgK, Subgroup.map_sup, ← hJeq]
        refine sup_le_sup le_rfl ?_
        rw [← hθg]
        exact gLBConj_push_le e hJK hgK
      have h2 := pull_mono e h1
      rwa [pull_push e (sup_le hJK hJgK)] at h2
    have hSI : S ≤ I := hS_le.trans (sup_le hJI hJgI)
    have eS : ↥S ≃* ↥(altOn T) :=
      (((altOn T).subgroupOf (alternatingGroup (Fin n))).equivMapOfInjective _
        (thetaInv_injective e)).symm.trans (Subgroup.subgroupOfEquivOfLe (altOn_le_alt T))
    have hT5 : 5 ≤ T.card := by omega
    have hSs : IsSimpleGroup ↥S := eS.isSimpleGroup_congr.2 (isSimpleGroup_altOn hT5)
    have hSnc : ∃ x y : ↥S, x * y ≠ y * x := by
      obtain ⟨u, v, huv⟩ := altOn_noncomm hT5
      refine ⟨eS.symm u, eS.symm v, fun h => huv ?_⟩
      have := congrArg eS h
      simpa using this
    have hScard : Nat.card ↥S = 20160 := by
      rw [Nat.card_congr eS.toEquiv, card_altOn (by omega), hT8]
      rfl
    have eS' : ↥(S.subgroupOf I) ≃* ↥S := Subgroup.subgroupOfEquivOfLe hSI
    obtain ⟨ι, Q, hQ, hQc, hQt⟩ := hcp
    refine false_of_central_product Q hQ hQc hQt (S.subgroupOf I)
      (eS'.isSimpleGroup_congr.2 hSs) ?_ (by rw [Nat.card_congr eS'.toEquiv, hScard]; norm_num)
    obtain ⟨u, v, huv⟩ := hSnc
    refine ⟨eS'.symm u, eS'.symm v, fun h => huv ?_⟩
    have := congrArg eS' h
    simpa using this
  have hinv : ∀ g ∈ ρ.range, ∀ x ∈ σa.support, g x ∈ σa.support := by
    rintro g ⟨b, rfl⟩ x hx
    rw [Equiv.Perm.mem_support] at hx ⊢
    intro h
    apply hx
    have h1 : (ρ b) (σa x) = (ρ b) x := by
      rw [← Equiv.Perm.mul_apply, hσc b aB, Equiv.Perm.mul_apply, h]
    exact (ρ b).injective h1
  have hfree' : ∀ g ∈ ρ.range, g ≠ 1 → ∀ x ∈ σa.support, g x ≠ x := by
    rintro g ⟨b, rfl⟩ hg1 x hx
    have hb1 : b ≠ 1 := by
      rintro rfl
      exact hg1 (map_one ρ)
    exact hfree b hb1 x (Equiv.Perm.mem_support.1 hx)
  have hdvd := card_dvd_of_free ρ.range σa.support hinv hfree'
  have hcardB : Nat.card ↥ρ.range = 3 ^ CFSG.Open.pRank 3 B := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hρinj).toEquiv]
    exact card_eq_three_pow_pRank hBel
  have hsupp : σa.support.card = n - 7 := by
    have h1 := Finset.card_compl σa.support
    rw [hF7, Fintype.card_fin] at h1
    have h2 : σa.support.card ≤ n := by
      have := Finset.card_le_univ σa.support
      rwa [Fintype.card_fin] at this
    omega
  rw [← hcardB, ← hsupp]
  exact hdvd

end Input23_7

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims126

end
