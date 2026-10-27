module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.AltDown
public import CFSG.LocalAnalysis.GLTheoremA.S6.AltDefs
import CFSG.LocalAnalysis.GLTheoremA.PartI.AltDownPerm
import CFSG.LocalAnalysis.GLTheoremA.PartI.AltDownComp
import CFSG.LocalAnalysis.GL83PartI.I_27_9_3.Component
public import CFSG.HardMathSupport.Solomon.LocalBalance.Components

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.LocalAnalysis.GLTheoremA.AltDown (mem_range_ofSubtype_compl_iff nonempty_range_ofSubtype_equiv)

variable {p : ℕ}

theorem p_dvd_card_alternatingGroup {α : Type*} [Fintype α] [DecidableEq α] (hp : p.Prime)
    (hp2 : p ≠ 2) (h : p ≤ Nat.card α) : p ∣ Nat.card (alternatingGroup α) := by
  haveI : Nontrivial α := by
    rw [← Fintype.one_lt_card_iff_nontrivial, ← Nat.card_eq_fintype_card]
    have := hp.two_le
    omega
  have h1 := two_mul_nat_card_alternatingGroup (α := α)
  rw [Nat.card_perm] at h1
  have h2 : p ∣ (Nat.card α).factorial := (Nat.Prime.dvd_factorial hp).2 h
  rw [← h1] at h2
  exact Nat.Coprime.dvd_of_dvd_mul_left ((Nat.coprime_primes hp Nat.prime_two).2 hp2) h2

@[expose] def altFix {n : ℕ} (τ : Equiv.Perm (Fin n)) : Subgroup ↥(alternatingGroup (Fin n)) :=
  (alternatingGroup.ofSubtype (τ.supportᶜ)).range

theorem mem_altFix_iff {n : ℕ} {τ : Equiv.Perm (Fin n)} {k : ↥(alternatingGroup (Fin n))} :
    k ∈ altFix τ ↔ ∀ u ∈ τ.support, (k : Equiv.Perm (Fin n)) u = u :=
  mem_range_ofSubtype_compl_iff τ.support k

theorem altFix_eq_fixingSubgroup {n : ℕ} (τ : Equiv.Perm (Fin n)) :
    altFix τ = fixingSubgroup ↥(alternatingGroup (Fin n)) (τ.support : Set (Fin n)) := by
  ext k
  rw [mem_altFix_iff, mem_fixingSubgroup_iff]
  constructor
  · intro h x hx
    exact h x (Finset.mem_coe.1 hx)
  · intro h x hx
    exact h x (Finset.mem_coe.2 hx)

theorem altFix_le_centralizer {n : ℕ} {τ : Equiv.Perm (Fin n)} {P : Subgroup ↥(alternatingGroup (Fin n))}
    (hsupp : ∀ g ∈ P, (g : Equiv.Perm (Fin n)).support ⊆ τ.support) :
    altFix τ ≤ Subgroup.centralizer (P : Set ↥(alternatingGroup (Fin n))) := by
  intro k hk
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  have hd : Equiv.Perm.Disjoint (g : Equiv.Perm (Fin n)) (k : Equiv.Perm (Fin n)) := by
    rw [Equiv.Perm.disjoint_iff_disjoint_support, Finset.disjoint_left]
    intro u hu hu'
    exact (Equiv.Perm.mem_support.1 hu') ((mem_altFix_iff.1 hk) u (hsupp g hg hu))
  exact Subtype.ext hd.commute.eq

theorem conj_mem_altFix {n : ℕ} {τ : Equiv.Perm (Fin n)} {g k : ↥(alternatingGroup (Fin n))}
    (hg : (g : Equiv.Perm (Fin n)) * τ = τ * (g : Equiv.Perm (Fin n))) (hk : k ∈ altFix τ) :
    g * k * g⁻¹ ∈ altFix τ := by
  rw [mem_altFix_iff] at hk ⊢
  intro u hu
  have hgi : ∀ v ∈ τ.support, (g : Equiv.Perm (Fin n))⁻¹ v ∈ τ.support := by
    intro v hv
    rw [Equiv.Perm.mem_support] at hv ⊢
    intro h
    apply hv
    have h1 : τ ((g : Equiv.Perm (Fin n))⁻¹ v) = (g : Equiv.Perm (Fin n))⁻¹ (τ v) := by
      apply (g : Equiv.Perm (Fin n)).injective
      have := congrArg (fun f : Equiv.Perm (Fin n) => f ((g : Equiv.Perm (Fin n))⁻¹ v)) hg
      simpa using this
    rw [h] at h1
    exact (((g : Equiv.Perm (Fin n))⁻¹).injective h1).symm
  show ((g : Equiv.Perm (Fin n)) * (k : Equiv.Perm (Fin n)) * (g : Equiv.Perm (Fin n))⁻¹) u = u
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hk _ (hgi u hu)]
  simp

theorem nonempty_altFix_equiv {n m : ℕ} (τ : Equiv.Perm (Fin n)) (hm : n - τ.support.card = m) :
    Nonempty (↥(altFix τ) ≃* ↥(alternatingGroup (Fin m))) := by
  have hcard : (τ.supportᶜ).card = m := by
    rw [Finset.card_compl, Fintype.card_fin]; exact hm
  exact nonempty_range_ofSubtype_equiv τ.supportᶜ m hcard

theorem altFix_isPComponent (hp : p.Prime) (hp2 : p ≠ 2) {n : ℕ} {τ : ↥(alternatingGroup (Fin n))}
    {P : Subgroup ↥(alternatingGroup (Fin n))} (hτP : τ ∈ P)
    (hsupp : ∀ g ∈ P, (g : Equiv.Perm (Fin n)).support ⊆ (τ : Equiv.Perm (Fin n)).support)
    (h5 : 5 ≤ n - (τ : Equiv.Perm (Fin n)).support.card)
    (hpn : p ≤ n - (τ : Equiv.Perm (Fin n)).support.card) :
    GLAPComponent p (Subgroup.centralizer (P : Set ↥(alternatingGroup (Fin n))))
      (altFix (τ : Equiv.Perm (Fin n))) := by
  classical
  set m := n - (τ : Equiv.Perm (Fin n)).support.card with hm
  have hle := altFix_le_centralizer (τ := (τ : Equiv.Perm (Fin n))) hsupp
  have hnorm : ((altFix (τ : Equiv.Perm (Fin n))).subgroupOf
      (Subgroup.centralizer (P : Set ↥(alternatingGroup (Fin n))))).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hle).2 fun c hc => ?_
    have hcτ : (c : Equiv.Perm (Fin n)) * (τ : Equiv.Perm (Fin n)) =
        (τ : Equiv.Perm (Fin n)) * (c : Equiv.Perm (Fin n)) := by
      have := Subgroup.mem_centralizer_iff.1 hc τ hτP
      exact (congrArg Subtype.val this).symm
    have hcinv : c⁻¹ ∈ Subgroup.centralizer (P : Set ↥(alternatingGroup (Fin n))) :=
      Subgroup.inv_mem _ hc
    have hcτ' : ((c⁻¹ : ↥(alternatingGroup (Fin n))) : Equiv.Perm (Fin n)) *
        (τ : Equiv.Perm (Fin n)) = (τ : Equiv.Perm (Fin n)) *
          ((c⁻¹ : ↥(alternatingGroup (Fin n))) : Equiv.Perm (Fin n)) := by
      have := Subgroup.mem_centralizer_iff.1 hcinv τ hτP
      exact (congrArg Subtype.val this).symm
    rw [Subgroup.mem_normalizer_iff]
    intro k
    constructor
    · exact conj_mem_altFix hcτ
    · intro hk
      have h2 := conj_mem_altFix hcτ' hk
      rwa [show c⁻¹ * (c * k * c⁻¹) * c⁻¹⁻¹ = k by group] at h2
  obtain ⟨e⟩ := nonempty_altFix_equiv (τ : Equiv.Perm (Fin n)) hm.symm
  have hcardm : 5 ≤ Nat.card (Fin m) := by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; exact h5
  haveI : IsSimpleGroup (alternatingGroup (Fin m)) := alternatingGroup.isSimpleGroup hcardm
  haveI : IsSimpleGroup ↥(altFix (τ : Equiv.Perm (Fin n))) := e.isSimpleGroup
  have hnc : ∃ a b : ↥(altFix (τ : Equiv.Perm (Fin n))), a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    haveI : Nontrivial (alternatingGroup (Fin m)) :=
      alternatingGroup.nontrivial_of_three_le_card (by omega)
    obtain ⟨a, ha⟩ := exists_ne (1 : alternatingGroup (Fin m))
    have hZ := alternatingGroup.center_eq_bot (α := Fin m) (by omega)
    have hmem : a ∈ Subgroup.center (alternatingGroup (Fin m)) := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply e.symm.injective
      rw [map_mul, map_mul]
      exact hcon _ _
    rw [hZ, Subgroup.mem_bot] at hmem
    exact ha hmem
  have hpL : p ∣ Nat.card ↥(altFix (τ : Equiv.Perm (Fin n))) := by
    rw [Nat.card_congr e.toEquiv]
    exact p_dvd_card_alternatingGroup hp hp2 (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; exact hpn)
  exact GL83.PiGen.glaPComponent_of_normal_simple hp hle hnorm hnc hpL

theorem centralizer_singleton_eq_fixSubgroup_conj {Q : Type*} [Group Q] (x : Q) :
    Subgroup.centralizer ({x} : Set Q) = fixSubgroup (MulAut.conj x) := by
  ext g
  rw [mem_fixSubgroup, MulAut.conj_apply, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    rw [← h]
    group
  · intro h
    exact (mul_inv_eq_iff_eq_mul.1 h).symm

theorem altFix_unique (hp : p.Prime) (hp2 : p ≠ 2) {n : ℕ} {σ : ↥(alternatingGroup (Fin n))}
    (hσp : σ ^ p = 1) (h5 : 5 ≤ n - (σ : Equiv.Perm (Fin n)).support.card)
    {I : Subgroup ↥(alternatingGroup (Fin n))}
    (hI : GLAPComponent p (Subgroup.centralizer ({σ} : Set ↥(alternatingGroup (Fin n)))) I) :
    I = altFix (σ : Equiv.Perm (Fin n)) := by
  classical
  rw [centralizer_singleton_eq_fixSubgroup_conj] at hI
  have hIF := AltDown.le_range_ofSubtype_of_glaPComponent hp hp2 hσp hI
  have hFC : altFix (σ : Equiv.Perm (Fin n)) ≤ fixSubgroup (MulAut.conj σ) := fun k hk =>
    AltDown.mem_fixSubgroup_conj.2 (Subtype.ext (AltDown.commute_of_mem_range_ofSubtype_compl hk).eq)
  set m := n - (σ : Equiv.Perm (Fin n)).support.card with hm
  obtain ⟨e⟩ := nonempty_altFix_equiv (σ : Equiv.Perm (Fin n)) hm.symm
  have hcardm : 5 ≤ Nat.card (Fin m) := by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; exact h5
  haveI : IsSimpleGroup (alternatingGroup (Fin m)) := alternatingGroup.isSimpleGroup hcardm
  haveI : IsSimpleGroup ↥(altFix (σ : Equiv.Perm (Fin n))) := e.isSimpleGroup
  haveI : Nontrivial ↥I := AltDown.nontrivial_of_glaPComponent hp hI
  exact AltDown.eq_of_isSubnormal_of_isSimpleGroup
    (glaPComponent_of_le hp hI hIF hFC).2.1 ((Subgroup.nontrivial_iff_ne_bot I).1 inferInstance)

@[expose] def altOn {n : ℕ} (T : Finset (Fin n)) : Subgroup ↥(alternatingGroup (Fin n)) :=
  (alternatingGroup.ofSubtype T).range

theorem mem_altOn_iff {n : ℕ} {T : Finset (Fin n)} {k : ↥(alternatingGroup (Fin n))} :
    k ∈ altOn T ↔ (k : Equiv.Perm (Fin n)).support ⊆ T :=
  alternatingGroup.mem_range_ofSubtype_iff T k

theorem altFix_eq_altOn {n : ℕ} (τ : Equiv.Perm (Fin n)) : altFix τ = altOn (τ.support)ᶜ := rfl

theorem nonempty_altOn_equiv {n : ℕ} (T : Finset (Fin n)) {m : ℕ} (h : T.card = m) :
    Nonempty (↥(altOn T) ≃* ↥(alternatingGroup (Fin m))) :=
  nonempty_range_ofSubtype_equiv T m h

theorem movedLettersOf_altOn {n : ℕ} {T : Finset (Fin n)} (hT : 3 ≤ T.card) :
    movedLettersOf (MulEquiv.refl ↥(alternatingGroup (Fin n))) (altOn T) = (T : Set (Fin n)) := by
  classical
  ext i
  constructor
  · rintro ⟨h, hh, hi⟩
    exact Finset.mem_coe.2 ((mem_altOn_iff.1 hh) (Equiv.Perm.mem_support.2 hi))
  · intro hi
    have hi' : i ∈ T := Finset.mem_coe.1 hi
    obtain ⟨j₁, hj₁, j₂, hj₂, h12, hj₁i, hj₂i⟩ : ∃ j₁ ∈ T, ∃ j₂ ∈ T, j₁ ≠ j₂ ∧ j₁ ≠ i ∧ j₂ ≠ i := by
      have h2 : 1 < (T.erase i).card := by rw [Finset.card_erase_of_mem hi']; omega
      obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 h2
      exact ⟨a, (Finset.mem_erase.1 ha).2, b, (Finset.mem_erase.1 hb).2, hab,
        (Finset.mem_erase.1 ha).1, (Finset.mem_erase.1 hb).1⟩
    have hsign : Equiv.Perm.sign (Equiv.swap i j₁ * Equiv.swap j₁ j₂) = 1 := by
      rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (Ne.symm hj₁i), Equiv.Perm.sign_swap h12]
      decide
    refine ⟨⟨Equiv.swap i j₁ * Equiv.swap j₁ j₂, Equiv.Perm.mem_alternatingGroup.2 hsign⟩, ?_, ?_⟩
    · rw [mem_altOn_iff]
      refine (Equiv.Perm.support_mul_le _ _).trans (sup_le ?_ ?_)
      · intro u hu
        rw [Equiv.Perm.support_swap (Ne.symm hj₁i)] at hu
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with rfl | rfl
        · exact hi'
        · exact hj₁
      · intro u hu
        rw [Equiv.Perm.support_swap h12] at hu
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with rfl | rfl
        · exact hj₁
        · exact hj₂
    · show (Equiv.swap i j₁ * Equiv.swap j₁ j₂) i ≠ i
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hj₁i.symm hj₂i.symm,
        Equiv.swap_apply_left]
      exact hj₁i

theorem isRootAlt_altOn {n : ℕ} {T : Finset (Fin n)} (hT : 3 ≤ T.card) :
    IsRootAlt (MulEquiv.refl ↥(alternatingGroup (Fin n))) (altOn T) T.card :=
  ⟨nonempty_altOn_equiv T rfl, by
    unfold MovesExactly
    rw [movedLettersOf_altOn hT]
    exact Set.ncard_coe_finset T⟩

theorem movedLettersOf_top {Q : Type} [Group Q] {N : ℕ} (hN : 3 ≤ N)
    (e : Q ≃* ↥(alternatingGroup (Fin N))) : movedLettersOf e (⊤ : Subgroup Q) = Set.univ := by
  classical
  refine Set.eq_univ_of_forall fun i => ?_
  have h1 := movedLettersOf_altOn (n := N) (T := (Finset.univ : Finset (Fin N))) (by simpa using hN)
  have h2 : i ∈ movedLettersOf (MulEquiv.refl ↥(alternatingGroup (Fin N)))
      (altOn (Finset.univ : Finset (Fin N))) := by
    rw [h1]
    exact Finset.mem_coe.2 (Finset.mem_univ i)
  obtain ⟨h, -, hh⟩ := h2
  exact ⟨e.symm h, Subgroup.mem_top _, by simpa using hh⟩

theorem isRootAlt_top {Q : Type} [Group Q] {N : ℕ} (hN : 3 ≤ N)
    (e : Q ≃* ↥(alternatingGroup (Fin N))) : IsRootAlt e (⊤ : Subgroup Q) N :=
  ⟨⟨Subgroup.topEquiv.trans e⟩, by
    unfold MovesExactly
    rw [movedLettersOf_top hN e, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]⟩

theorem card_support_eq_of_cycleType {n : ℕ} {σ : Equiv.Perm (Fin n)} (hσ : σ.cycleType = {p}) :
    σ.support.card = p := by
  rw [← Equiv.Perm.sum_cycleType, hσ]
  simp

theorem pow_eq_one_of_cycleType_eq {n : ℕ} {σ : Equiv.Perm (Fin n)} (hσ : σ.cycleType = {p}) :
    σ ^ p = 1 := by
  have h1 : orderOf σ = p := by
    rw [← Equiv.Perm.lcm_cycleType, hσ]
    simp
  rw [← h1]
  exact pow_orderOf_eq_one σ

theorem altFix_isPComponent_cycle (hp : p.Prime) (hp2 : p ≠ 2) {n : ℕ}
    {σ : ↥(alternatingGroup (Fin n))} (hσ : (σ : Equiv.Perm (Fin n)).cycleType = {p})
    (h2p : 2 * p ≤ n) (h5 : p + 5 ≤ n) :
    GLAPComponent p (Subgroup.centralizer ({σ} : Set ↥(alternatingGroup (Fin n))))
      (altFix (σ : Equiv.Perm (Fin n))) := by
  have hc := card_support_eq_of_cycleType hσ
  have h := altFix_isPComponent hp hp2 (P := Subgroup.zpowers σ) (Subgroup.mem_zpowers σ)
    (by
      intro g hg
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
      rw [Subgroup.coe_zpow]
      exact Equiv.Perm.support_zpow_le _ _)
    (by rw [hc]; omega) (by rw [hc]; omega)
  rwa [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] at h

theorem altFix_unique_cycle (hp : p.Prime) (hp2 : p ≠ 2) {n : ℕ}
    {σ : ↥(alternatingGroup (Fin n))} (hσ : (σ : Equiv.Perm (Fin n)).cycleType = {p})
    (h5 : p + 5 ≤ n) {I : Subgroup ↥(alternatingGroup (Fin n))}
    (hI : GLAPComponent p (Subgroup.centralizer ({σ} : Set ↥(alternatingGroup (Fin n)))) I) :
    I = altFix (σ : Equiv.Perm (Fin n)) := by
  have hc := card_support_eq_of_cycleType hσ
  exact altFix_unique hp hp2 (Subtype.ext (by simpa using pow_eq_one_of_cycleType_eq hσ))
    (by rw [hc]; omega) hI

theorem altFix_unique_of_component (hp : p.Prime) (hp2 : p ≠ 2) {n : ℕ} {σ : ↥(alternatingGroup (Fin n))}
    (hσp : σ ^ p = 1) {I : Subgroup ↥(alternatingGroup (Fin n))}
    (hI : GLAPComponent p (Subgroup.centralizer ({σ} : Set ↥(alternatingGroup (Fin n)))) I) :
    I = altFix (σ : Equiv.Perm (Fin n)) ∧ 5 ≤ n - (σ : Equiv.Perm (Fin n)).support.card := by
  classical
  have hI' : GLAPComponent p (fixSubgroup (MulAut.conj σ)) I := by
    rw [← centralizer_singleton_eq_fixSubgroup_conj]; exact hI
  have hIF := AltDown.le_range_ofSubtype_of_glaPComponent hp hp2 hσp hI'
  have hFC : altFix (σ : Equiv.Perm (Fin n)) ≤ fixSubgroup (MulAut.conj σ) := fun k hk =>
    AltDown.mem_fixSubgroup_conj.2 (Subtype.ext (AltDown.commute_of_mem_range_ofSubtype_compl hk).eq)
  obtain ⟨k, hk⟩ : ∃ k, n - (σ : Equiv.Perm (Fin n)).support.card = k := ⟨_, rfl⟩
  obtain ⟨e⟩ := nonempty_altFix_equiv (σ : Equiv.Perm (Fin n)) hk
  haveI : Nontrivial ↥I := AltDown.nontrivial_of_glaPComponent hp hI'
  have hk5 : 5 ≤ k := by
    by_contra hlt
    haveI : Group.IsPerfect ↥I := Subgroup.isPerfect_iff.2 (glaPComponent_perfect hI')
    have hdvd : Nat.card ↥I ∣ k.factorial := by
      have h1 : Nat.card ↥I ∣ Nat.card ↥(altFix (σ : Equiv.Perm (Fin n))) :=
        Subgroup.card_dvd_of_le hIF
      rw [Nat.card_congr e.toEquiv] at h1
      exact h1.trans (by simpa using AltDown.natCard_alternatingGroup_dvd_factorial (Fin k))
    exact AltDown.false_of_isPerfect_of_card_dvd_twentyFour
      (hdvd.trans (AltDown.factorial_dvd_twentyFour (not_le.1 hlt)))
  have hcardk : 5 ≤ Nat.card (Fin k) := by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; exact hk5
  haveI : IsSimpleGroup (alternatingGroup (Fin k)) := alternatingGroup.isSimpleGroup hcardk
  haveI : IsSimpleGroup ↥(altFix (σ : Equiv.Perm (Fin n))) := e.isSimpleGroup
  refine ⟨AltDown.eq_of_isSubnormal_of_isSimpleGroup (glaPComponent_of_le hp hI' hIF hFC).2.1
    ((Subgroup.nontrivial_iff_ne_bot I).1 inferInstance), by rw [hk]; exact hk5⟩

theorem nonempty_pQuot_equiv_of_simple (hp : p.Prime) {Y : Type} [Group Y] [Finite Y]
    {F : Subgroup Y} [IsSimpleGroup ↥F] (hpF : p ∣ Nat.card ↥F) :
    Nonempty (PQuot p F ≃* ↥F) := by
  have hcore : GLAPPrimeCore p ↥F = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (GLAPPrimeCore p ↥F) with h | h
    · exact h
    · exfalso
      have hcop := coprime_card_gLAPPrimeCore_aux p ↥F
      rw [h, Subgroup.card_top] at hcop
      exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hcop hpF)
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hcore).trans QuotientGroup.quotientBot⟩

theorem nonempty_pQuot_equiv_altFix (hp : p.Prime) (hp2 : p ≠ 2) {n m : ℕ} (τ : Equiv.Perm (Fin n))
    (hm : n - τ.support.card = m) (h5 : 5 ≤ m) (hpm : p ≤ m) :
    Nonempty (PQuot p (altFix τ) ≃* ↥(alternatingGroup (Fin m))) := by
  obtain ⟨e⟩ := nonempty_altFix_equiv τ hm
  have hcardm : 5 ≤ Nat.card (Fin m) := by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; exact h5
  haveI : IsSimpleGroup (alternatingGroup (Fin m)) := alternatingGroup.isSimpleGroup hcardm
  haveI : IsSimpleGroup ↥(altFix τ) := e.isSimpleGroup
  have hpF : p ∣ Nat.card ↥(altFix τ) := by
    rw [Nat.card_congr e.toEquiv]
    exact p_dvd_card_alternatingGroup hp hp2 (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; exact hpm)
  obtain ⟨e₁⟩ := nonempty_pQuot_equiv_of_simple hp hpF
  exact ⟨e₁.trans e⟩

end CFSG.LocalAnalysis.GLTheoremA
