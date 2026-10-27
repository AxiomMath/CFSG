module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutU42Aut
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
public import CFSG.LocalAnalysis.ComponentInitial.TwoPrimeSolvable
public import CFSG.LocalAnalysis.GLTheoremA.S4.Lemma49i
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.LocalAnalysis.GLTheoremA.PartI.I1412
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)

private theorem u42_p_exponent {q : TauCeti.PrimePower} (hq : q.card = 2) :
    q.p = 2 ∧ q.exponent = 1 := by
  have hcard : q.p ^ q.exponent = 2 := by rw [← TauCeti.PrimePower.card_def]; exact hq
  have hp : q.p = 2 := by
    have hdvd : q.p ∣ 2 := by
      rw [← hcard]
      exact dvd_pow_self q.p q.exponent_pos.ne'
    exact (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).1 hdvd
  refine ⟨hp, ?_⟩
  rw [hp] at hcard
  exact Nat.pow_right_injective (le_refl 2) (show 2 ^ q.exponent = 2 ^ 1 by simpa using hcard)

private theorem u42_lieModel {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedA 3 q).Valid) (hq : q.card = 2) :
    Blueprint.LieModel (TauCeti.CFSGIndex.lie ⟨.twistedA 3 q, hv⟩).Group .PSU 4 2 1 := by
  obtain ⟨hp, hf⟩ := u42_p_exponent hq
  have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 3 q hv
    (MulEquiv.refl (TauCeti.CFSGIndex.lie ⟨.twistedA 3 q, hv⟩).Group)
  rw [hp, hf] at h
  exact Or.inl ⟨by decide, h⟩

private theorem u42_card {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedA 3 q).Valid) (hq : q.card = 2) :
    Nat.card (MulAut (TauCeti.CFSGIndex.lie ⟨.twistedA 3 q, hv⟩).Group) = 51840 ∧
      Nat.card (TauCeti.CFSGIndex.lie ⟨.twistedA 3 q, hv⟩).Group = 25920 :=
  CFSG.EvenSporadicStandard.M22Std.card_mulAut_of_lieModel_psu42 (u42_lieModel hv hq)

private theorem u42_finite {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedA 3 q).Valid) (hq : q.card = 2) :
    Finite (TauCeti.CFSGIndex.lie ⟨.twistedA 3 q, hv⟩).Group := by
  obtain ⟨-, hS⟩ := u42_card hv hq
  exact Nat.finite_of_card_ne_zero (by rw [hS]; norm_num)


private theorem u42_simple {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedA 3 q).Valid) (hq : q.card = 2) :
    IsSimpleGroup (TauCeti.CFSGIndex.lie ⟨.twistedA 3 q, hv⟩).Group := by
  obtain ⟨hp, hf⟩ := u42_p_exponent hq
  have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 3 q hv
    (MulEquiv.refl (TauCeti.CFSGIndex.lie ⟨.twistedA 3 q, hv⟩).Group)
  rw [hp, hf] at h
  exact (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity _ 4 2 1 h).2

private theorem u42_isSubnormal_top {T : Type} [Group T] [IsSimpleGroup T] {H K : Subgroup T}
    (h : IsSubnormal H K) : K = ⊤ → H = ⊥ ∨ H = ⊤ := by
  induction h with
  | refl H => intro hK; exact Or.inr hK
  | @step H M K hle hn _ ih =>
    intro hK
    rcases ih hK with hM | hM
    · exact Or.inl (le_bot_iff.1 (hM ▸ hle))
    · subst hM
      haveI : H.Normal :=
        ⟨fun n hn' g => (Subgroup.normal_subgroupOf_iff le_top).1 hn n g hn' (Subgroup.mem_top g)⟩
      exact IsSimpleGroup.eq_bot_or_eq_top_of_normal H

private theorem u42_center_eq_bot {T : Type} [Group T] [IsSimpleGroup T]
    (hnc : ∃ a b : T, a * b ≠ b * a) : Subgroup.center T = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center T) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnc
    have ha : a ∈ Subgroup.center T := by
      rw [h]
      exact Subgroup.mem_top a
    exact hab ((Subgroup.mem_center_iff.1 ha b).symm)

private theorem u42_pSimple_top_equiv {p : ℕ} (hp : p.Prime) {T : Type} [Group T] [Finite T]
    [IsSimpleGroup T] (hnc : ∃ a b : T, a * b ≠ b * a) {I : Subgroup T}
    (hI : GLAPComponent p (⊤ : Subgroup T) I) : Nonempty (PSimple p I ≃* T) := by
  have hIeq : I = ⊤ := by
    rcases u42_isSubnormal_top hI.2.1 rfl with h | h
    · exact absurd h (glaPComponent_ne_bot' hI)
    · exact h
  subst hIeq
  have hq : CFSG.Open.IsQuasisimple (PQuot p (⊤ : Subgroup T)) :=
    isQuasisimple_pQuot_of_glaPComponent hp hI
  have hnt : Nontrivial (↥(⊤ : Subgroup T) ⧸ GLAPPrimeCore p ↥(⊤ : Subgroup T)) := by
    haveI : Nontrivial (PQuot p (⊤ : Subgroup T) ⧸ Subgroup.center (PQuot p (⊤ : Subgroup T))) :=
      hq.2.toNontrivial
    exact (QuotientGroup.mk'_surjective
      (Subgroup.center (PQuot p (⊤ : Subgroup T)))).nontrivial
  have hOb : GLAPPrimeCore p ↥(⊤ : Subgroup T) = ⊥ := by
    let ψ : ↥(⊤ : Subgroup T) ≃* T := Subgroup.topEquiv
    haveI : ((GLAPPrimeCore p ↥(⊤ : Subgroup T)).map ψ.toMonoidHom).Normal :=
      Subgroup.Normal.map (GLAPPrimeCore.normal p _) ψ.toMonoidHom ψ.surjective
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        ((GLAPPrimeCore p ↥(⊤ : Subgroup T)).map ψ.toMonoidHom) with h | h
    · exact (Subgroup.map_eq_bot_iff_of_injective _ ψ.injective).1 h
    · exfalso
      have htop : GLAPPrimeCore p ↥(⊤ : Subgroup T) = ⊤ := by
        apply Subgroup.map_injective (f := ψ.toMonoidHom) ψ.injective
        rw [h, Subgroup.map_top_of_surjective _ ψ.surjective]
      obtain ⟨a, b, hab⟩ := exists_pair_ne (↥(⊤ : Subgroup T) ⧸ GLAPPrimeCore p ↥(⊤ : Subgroup T))
      apply hab
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
      rw [QuotientGroup.eq, htop]
      exact Subgroup.mem_top _
  have hZtop : Subgroup.center ↥(⊤ : Subgroup T) = ⊥ := by
    have h1 := Subgroup.map_center_eq (Subgroup.topEquiv : ↥(⊤ : Subgroup T) ≃* T)
    rw [u42_center_eq_bot hnc] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ Subgroup.topEquiv.injective).1 h1
  let e1 : PQuot p (⊤ : Subgroup T) ≃* ↥(⊤ : Subgroup T) :=
    (QuotientGroup.quotientMulEquivOfEq hOb).trans QuotientGroup.quotientBot
  let e2 : PSimple p (⊤ : Subgroup T) ≃*
      (↥(⊤ : Subgroup T) ⧸ Subgroup.center ↥(⊤ : Subgroup T)) :=
    QuotientGroup.congr _ _ e1 (Subgroup.map_center_eq e1)
  let e3 : (↥(⊤ : Subgroup T) ⧸ Subgroup.center ↥(⊤ : Subgroup T)) ≃* ↥(⊤ : Subgroup T) :=
    (QuotientGroup.quotientMulEquivOfEq hZtop).trans QuotientGroup.quotientBot
  exact ⟨e2.trans (e3.trans Subgroup.topEquiv)⟩

private theorem u42_kLevel_eq_one {p : ℕ} {S : Type} [Group S] (h : IsChevSimple p S) :
    kLevel p S = 1 := by
  unfold kLevel
  rw [if_pos h]

private theorem u42_nonab_of_card_not_prime {T : Type} [Group T] [IsSimpleGroup T]
    (hc : ¬ (Nat.card T).Prime) : ∃ a b : T, a * b ≠ b * a := by
  by_contra h
  push Not at h
  letI : CommGroup T := { ‹Group T› with mul_comm := fun a b => h a b }
  exact hc ((CommGroup.is_simple_iff_prime_card (α := T)).1 ‹IsSimpleGroup T›)

private theorem u42_false_of_solvable_component {p : ℕ} {S : Type} [Group S] [Finite S]
    {X I : Subgroup S} (hsolv : Group.IsSolvable ↥X) (hI : GLAPComponent p X I) : False := by
  haveI := hsolv
  have hJX : I ≤ X := hI.1
  have hperf : ⁅I, I⁆ = I := glaPComponent_perfect hI
  have hne : I ≠ ⊥ := glaPComponent_ne_bot' hI
  have hJ'ne : I.subgroupOf X ≠ ⊥ := by
    intro h0
    apply hne
    rw [← Subgroup.map_subgroupOf_eq_of_le hJX, h0, Subgroup.map_bot]
  have hlt : ⁅I.subgroupOf X, I.subgroupOf X⁆ < I.subgroupOf X :=
    Group.IsSolvable.commutator_lt_of_ne_bot hJ'ne
  have heq : ⁅I.subgroupOf X, I.subgroupOf X⁆ = I.subgroupOf X := by
    apply Subgroup.map_injective (f := X.subtype) X.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hJX]
    exact hperf
  rw [heq] at hlt
  exact lt_irrefl _ hlt

private theorem u42_fixSubgroup_one {K : Type*} [Group K] : fixSubgroup (1 : MulAut K) = ⊤ := by
  ext x
  rw [mem_fixSubgroup]
  simp

private theorem u42_prime_dvd_25920 {r : ℕ} (hr : r.Prime) (h : r ∣ 25920) :
    r = 2 ∨ r = 3 ∨ r = 5 := by
  have h' : r ∣ 2 ^ 6 * 3 ^ 4 * 5 := by norm_num; exact h
  rcases (Nat.Prime.dvd_mul hr).1 h' with h1 | h1
  · rcases (Nat.Prime.dvd_mul hr).1 h1 with h2 | h2
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h2))
    · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1
        (hr.dvd_of_dvd_pow h2)))
  · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hr (by norm_num)).1 h1))

abbrev U42NoFifteen (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.twistedA 3 q).Valid) :
    Prop :=
  ∀ x : (TauCeti.CFSGIndex.lie ⟨.twistedA 3 q, hv⟩).Group, orderOf x ≠ 15

private theorem u42_card_outer {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedA 3 q).Valid) (hq : q.card = 2) :
    Nat.card (Outer (TauCeti.CFSGIndex.lie ⟨.twistedA 3 q, hv⟩).Group) = 2 := by
  obtain ⟨hAut, hS⟩ := u42_card hv hq
  haveI := u42_simple hv hq
  have hnc := u42_nonab_of_card_not_prime (T := (TauCeti.CFSGIndex.lie ⟨.twistedA 3 q, hv⟩).Group)
    (by rw [hS]; norm_num)
  have hZ := u42_center_eq_bot hnc
  have hinj : Function.Injective (MulAut.conj : (TauCeti.CFSGIndex.lie ⟨.twistedA 3 q, hv⟩).Group →*
      MulAut (TauCeti.CFSGIndex.lie ⟨.twistedA 3 q, hv⟩).Group) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hc : g ∈ Subgroup.center (TauCeti.CFSGIndex.lie ⟨.twistedA 3 q, hv⟩).Group := by
      rw [Subgroup.mem_center_iff]
      intro h
      have h3 := congrArg (fun φ : MulAut (TauCeti.CFSGIndex.lie ⟨.twistedA 3 q, hv⟩).Group => φ h) hg
      simp only [MulAut.conj_apply, MulAut.one_apply] at h3
      exact (mul_inv_eq_iff_eq_mul.1 h3).symm
    rw [hZ, Subgroup.mem_bot] at hc
    exact hc
  have hinner : Nat.card (inner (TauCeti.CFSGIndex.lie ⟨.twistedA 3 q, hv⟩).Group) =
      Nat.card (TauCeti.CFSGIndex.lie ⟨.twistedA 3 q, hv⟩).Group :=
    Nat.card_range_of_injective hinj
  have hidx := (inner (TauCeti.CFSGIndex.lie ⟨.twistedA 3 q, hv⟩).Group).card_mul_index
  rw [hinner, hS, hAut] at hidx
  have hO : (inner (TauCeti.CFSGIndex.lie ⟨.twistedA 3 q, hv⟩).Group).index =
      Nat.card (Outer (TauCeti.CFSGIndex.lie ⟨.twistedA 3 q, hv⟩).Group) := rfl
  rw [hO] at hidx
  omega

private theorem u42_conj_of_pow {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedA 3 q).Valid) (hq : q.card = 2)
    (α : MulAut (TauCeti.CFSGIndex.lie ⟨.twistedA 3 q, hv⟩).Group) (hα : α ^ 3 = 1) :
    ∃ g : (TauCeti.CFSGIndex.lie ⟨.twistedA 3 q, hv⟩).Group, MulAut.conj g = α := by
  have hout : ¬ 3 ∣ Nat.card (Outer (TauCeti.CFSGIndex.lie ⟨.twistedA 3 q, hv⟩).Group) := by
    rw [u42_card_outer hv hq]
    norm_num
  let π : MulAut (TauCeti.CFSGIndex.lie ⟨.twistedA 3 q, hv⟩).Group →*
      Outer (TauCeti.CFSGIndex.lie ⟨.twistedA 3 q, hv⟩).Group :=
    QuotientGroup.mk' _
  have hp' : π α ^ 3 = 1 := by
    rw [← map_pow, hα, map_one]
  have hord : orderOf (π α) ∣ 3 := orderOf_dvd_of_pow_eq_one hp'
  haveI : Finite (Outer (TauCeti.CFSGIndex.lie ⟨.twistedA 3 q, hv⟩).Group) :=
    Nat.finite_of_card_ne_zero (by rw [u42_card_outer hv hq]; norm_num)
  have hdvd : orderOf (π α) ∣ Nat.card (Outer (TauCeti.CFSGIndex.lie ⟨.twistedA 3 q, hv⟩).Group) :=
    orderOf_dvd_natCard _
  have hmem : α ∈ inner (TauCeti.CFSGIndex.lie ⟨.twistedA 3 q, hv⟩).Group := by
    rcases (Nat.dvd_prime Nat.prime_three).1 hord with h1 | h1
    · exact (QuotientGroup.eq_one_iff α).1 (orderOf_eq_one_iff.1 h1)
    · rw [h1] at hdvd
      exact absurd hdvd hout
  obtain ⟨g, hg⟩ := hmem
  exact ⟨g, hg⟩

private theorem u42_fix_conj {S : Type} [Group S] (g : S) :
    fixSubgroup (MulAut.conj g) = Subgroup.centralizer ({g} : Set S) := by
  ext x
  rw [mem_fixSubgroup, Subgroup.mem_centralizer_iff]
  simp only [MulAut.conj_apply, Set.mem_singleton_iff, forall_eq]
  exact mul_inv_eq_iff_eq_mul

private theorem u42_centralizer_solvable {S : Type} [Group S] [Finite S]
    (hcard : Nat.card S = 25920) (h15 : ∀ x : S, orderOf x ≠ 15) (g : S) (hg3 : g ^ 3 = 1)
    (hg1 : g ≠ 1) : Group.IsSolvable ↥(Subgroup.centralizer ({g} : Set S)) := by
  have hord : orderOf g = 3 := orderOf_eq_prime hg3 hg1
  have hnd : ¬ 5 ∣ Nat.card (Subgroup.centralizer ({g} : Set S)) := by
    intro hdvd
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    obtain ⟨h, hh⟩ := exists_prime_orderOf_dvd_card' 5 hdvd
    have hcomm : Commute g (h : S) := by
      have hmem : (h : S) ∈ Subgroup.centralizer ({g} : Set S) := h.2
      rw [Subgroup.mem_centralizer_iff] at hmem
      exact hmem g (Set.mem_singleton g)
    have hordh : orderOf (h : S) = 5 := by rw [Subgroup.orderOf_coe, hh]
    have hco : (orderOf g).Coprime (orderOf (h : S)) := by
      rw [hord, hordh]
      norm_num
    have hx : orderOf (g * (h : S)) = 15 := by
      rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime hco, hord, hordh]
    exact h15 _ hx
  have hdvdS : Nat.card (Subgroup.centralizer ({g} : Set S)) ∣ 25920 :=
    hcard ▸ Subgroup.card_subgroup_dvd_card _
  refine CFSG.LocalAnalysis.ComponentInitial.isSolvable_of_card_primeFactors_le_two ?_
  have hsub : (Nat.card (Subgroup.centralizer ({g} : Set S))).primeFactors ⊆ ({2, 3} : Finset ℕ) := by
    intro r hr
    have hrp : r.Prime := Nat.prime_of_mem_primeFactors hr
    have hrm : r ∣ Nat.card (Subgroup.centralizer ({g} : Set S)) := Nat.dvd_of_mem_primeFactors hr
    rcases u42_prime_dvd_25920 hrp (hrm.trans hdvdS) with h | h | h
    · simp [h]
    · simp [h]
    · exact absurd (h ▸ hrm) hnd
  exact (Finset.card_le_card hsub).trans (by decide)

theorem u42_fixSubgroup_solvable_of_noFifteen
    {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.twistedA 3 q).Valid) (hq : q.card = 2)
    (h15 : U42NoFifteen q hv)
    (α : MulAut (TauCeti.CFSGIndex.lie ⟨.twistedA 3 q, hv⟩).Group) (hα : α ^ 3 = 1) (hα1 : α ≠ 1) :
    Group.IsSolvable ↥(fixSubgroup α) := by
  obtain ⟨hAut, hS⟩ := u42_card hv hq
  haveI := u42_simple hv hq
  obtain ⟨g, rfl⟩ := u42_conj_of_pow hv hq α hα
  haveI := u42_finite hv hq
  have hnc := u42_nonab_of_card_not_prime (T := (TauCeti.CFSGIndex.lie ⟨.twistedA 3 q, hv⟩).Group)
    (by rw [hS]; norm_num)
  have hZ := u42_center_eq_bot hnc
  have hg3 : g ^ 3 = 1 := by
    have h1 : MulAut.conj (g ^ 3) = 1 := by
      rw [map_pow]
      exact hα
    have h2 : g ^ 3 ∈ Subgroup.center (TauCeti.CFSGIndex.lie ⟨.twistedA 3 q, hv⟩).Group := by
      rw [Subgroup.mem_center_iff]
      intro h
      have h3 := congrArg (fun φ : MulAut (TauCeti.CFSGIndex.lie ⟨.twistedA 3 q, hv⟩).Group =>
        φ h) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at h3
      exact (mul_inv_eq_iff_eq_mul.1 h3).symm
    rw [hZ, Subgroup.mem_bot] at h2
    exact h2
  have hg1 : g ≠ 1 := by
    rintro rfl
    exact hα1 (by rw [map_one])
  rw [u42_fix_conj]
  exact u42_centralizer_solvable hS h15 g hg3 hg1

theorem u42_downLe_of_noFifteen
    {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.twistedA 3 q).Valid) (hq : q.card = 2)
    (h15 : U42NoFifteen q hv) :
    DownLe 3 1 (TauCeti.CFSGIndex.lie ⟨.twistedA 3 q, hv⟩).Group := by
  intro α hα I hI
  by_cases hα1 : α = 1
  · subst hα1
    rw [u42_fixSubgroup_one] at hI
    obtain ⟨hAut, hS⟩ := u42_card hv hq
    haveI := u42_simple hv hq
    haveI := u42_finite hv hq
    have hnc := u42_nonab_of_card_not_prime (T := (TauCeti.CFSGIndex.lie ⟨.twistedA 3 q, hv⟩).Group)
      (by rw [hS]; norm_num)
    obtain ⟨f⟩ := u42_pSimple_top_equiv (by norm_num : Nat.Prime 3) hnc hI
    have hT : IsChevSimple 3 (TauCeti.CFSGIndex.lie ⟨.twistedA 3 q, hv⟩).Group :=
      Or.inr ⟨TauCeti.CFSGIndex.lie ⟨.twistedA 3 q, hv⟩, ⟨hq, rfl⟩, ⟨MulEquiv.refl _⟩⟩
    exact (kLevel_congr 3 f).trans_le (u42_kLevel_eq_one hT).le
  · exfalso
    haveI := u42_finite hv hq
    exact u42_false_of_solvable_component
      (u42_fixSubgroup_solvable_of_noFifteen hv hq h15 α hα hα1) hI

section Gf4

open Polynomial

private theorem u42_exists_cube_root {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4) :
    ∃ w : K, w ^ 2 + w + 1 = 0 := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hcard : Nat.card Kˣ = 3 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hK]
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3 (by rw [hcard])
  have h3 : (u : K) ^ 3 = 1 := by
    have := pow_orderOf_eq_one u
    rw [hu] at this
    exact congrArg Units.val this
  have h1 : (u : K) ≠ 1 := by
    intro h
    have : u = 1 := by
      ext
      simpa using h
    rw [this, orderOf_one] at hu
    norm_num at hu
  refine ⟨(u : K), ?_⟩
  have hfac : ((u : K) - 1) * ((u : K) ^ 2 + (u : K) + 1) = 0 := by
    linear_combination h3
  rcases mul_eq_zero.1 hfac with h | h
  · exact absurd (sub_eq_zero.1 h) h1
  · exact h

private theorem u42_mem_of_card_four {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4)
    {w : K} (hw : w ^ 2 + w + 1 = 0) (x : K) :
    x = 0 ∨ x = 1 ∨ x = w ∨ x = w ^ 2 := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have hx : x ^ 4 = x := by
    have := FiniteField.pow_card x
    rw [Fintype.card_eq_nat_card, hK] at this
    exact this
  have hfac : x * (x - 1) * (x - w) * (x - w ^ 2) = 0 := by
    linear_combination hx + (x * (x - 1) * (w - 1 - x)) * hw
  rcases mul_eq_zero.1 hfac with h | h
  · rcases mul_eq_zero.1 h with h | h
    · rcases mul_eq_zero.1 h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl (sub_eq_zero.1 h))
    · exact Or.inr (Or.inr (Or.inl (sub_eq_zero.1 h)))
  · exact Or.inr (Or.inr (Or.inr (sub_eq_zero.1 h)))

private theorem u42_charpoly_form {K : Type} [Field K] (hK2 : (2 : K) = 0)
    (f : K →+* K) (hf : ∀ x, f x = x ^ 2) (A : Matrix (Fin 4) (Fin 4) K) (hdet : A.det = 1)
    (hu : (A.map f).transpose * A = 1) :
    ∃ a b : K, A.charpoly = X ^ 4 + C a ^ 2 * X ^ 3 + C b * X ^ 2 + C a * X + 1 ∧ b ^ 2 = b := by
  have hunit : IsUnit A := (Matrix.isUnit_iff_isUnit_det A).2 (by rw [hdet]; exact isUnit_one)
  have hinv : A⁻¹ = (A.map f).transpose := Matrix.inv_eq_left_inv hu
  have h1 : A⁻¹.charpoly = A.charpoly.reverse := by
    rw [Matrix.charpoly_inv A hunit, hdet, Matrix.reverse_charpoly]
    norm_num
  have h2 : A⁻¹.charpoly = A.charpoly.map f := by
    rw [hinv, Matrix.charpoly_transpose, Matrix.charpoly_map]
  have hrev : A.charpoly.reverse = A.charpoly.map f := h1.symm.trans h2
  have hdeg : A.charpoly.natDegree = 4 := by
    rw [Matrix.charpoly_natDegree_eq_dim]
    simp
  have hmonic : A.charpoly.Monic := Matrix.charpoly_monic A
  have hlead : A.charpoly.coeff 4 = 1 := by
    have := hmonic.coeff_natDegree
    rwa [hdeg] at this
  have hcoeff : ∀ i, i ≤ 4 → A.charpoly.coeff (4 - i) = (A.charpoly.coeff i) ^ 2 := by
    intro i hi
    have := congrArg (fun p => Polynomial.coeff p i) hrev
    simp only [Polynomial.coeff_reverse, Polynomial.coeff_map, hdeg] at this
    rw [Polynomial.revAt_le (by omega), hf] at this
    exact this
  have hc0 : A.charpoly.coeff 0 = 1 := by
    have h := hcoeff 0 (by norm_num)
    rw [Nat.sub_zero, hlead] at h
    have hsq : (A.charpoly.coeff 0 - 1) ^ 2 = 0 := by
      linear_combination -h + (1 - A.charpoly.coeff 0) * hK2
    exact sub_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 hsq)
  have hc3 : A.charpoly.coeff 3 = (A.charpoly.coeff 1) ^ 2 := hcoeff 1 (by norm_num)
  have hb : (A.charpoly.coeff 2) ^ 2 = A.charpoly.coeff 2 := (hcoeff 2 (by norm_num)).symm
  refine ⟨A.charpoly.coeff 1, A.charpoly.coeff 2, ?_, hb⟩
  conv_lhs => rw [Polynomial.as_sum_range_C_mul_X_pow A.charpoly, hdeg]
  simp [Finset.sum_range_succ, hlead, hc0, hc3]
  ring

end Gf4

section Identities

open Polynomial

private theorem u42_id_zero_0 {K : Type} [Field K] (a b : K) (h2 : (2 : K) = 0) (ha : a = 0) (hb : b = 0) :
    (X ^ 3 - 1 : K[X]) = (1 + X + X ^ 2 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8 + X ^ 9 + X ^ 10 + X ^ 12 + X ^ 13 + X ^ 14) * (X ^ 4 + C a ^ 2 * X ^ 3 + C b * X ^ 2 + C a * X + 1) + (X + X ^ 2 + X ^ 3) * (X ^ 15 - 1) := by
  subst a b
  have h2' : (2 : K[X]) = 0 := by
    have h := congrArg C h2
    rw [map_ofNat, map_zero] at h
    exact h
  simp only [map_pow, map_zero, map_one]
  linear_combination (-1 + X ^ 3 - X ^ 4 - X ^ 5 - X ^ 6 - X ^ 8 - X ^ 9 - X ^ 10 - X ^ 12 - X ^ 13 - X ^ 14 - X ^ 16 - X ^ 17 - X ^ 18) * h2'

private theorem u42_id_zero_1 {K : Type} [Field K] (a b : K) (h2 : (2 : K) = 0) (ha : a = 0) (hb : b = 1) :
    (X ^ 3 - 1 : K[X]) = (1 + X + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 7 + X ^ 10 + X ^ 11 + X ^ 12 + X ^ 13) * (X ^ 4 + C a ^ 2 * X ^ 3 + C b * X ^ 2 + C a * X + 1) + (X + X ^ 2) * (X ^ 15 - 1) := by
  subst a b
  have h2' : (2 : K[X]) = 0 := by
    have h := congrArg C h2
    rw [map_ofNat, map_zero] at h
    exact h
  simp only [map_pow, map_zero, map_one]
  linear_combination (-1 - X ^ 4 - X ^ 5 - X ^ 6 - X ^ 7 - X ^ 8 - X ^ 9 - X ^ 10 - X ^ 11 - X ^ 12 - X ^ 13 - X ^ 14 - X ^ 15 - X ^ 16 - X ^ 17) * h2'

private theorem u42_id_one_0 {K : Type} [Field K] (a b : K) (h2 : (2 : K) = 0) (ha : a = 1) (hb : b = 0) :
    (X ^ 3 - 1 : K[X]) = (X ^ 3 + X ^ 4 + X ^ 5 + X ^ 9 + X ^ 10 + X ^ 11) * (X ^ 4 + C a ^ 2 * X ^ 3 + C b * X ^ 2 + C a * X + 1) + (1) * (X ^ 15 - 1) := by
  subst a b
  have h2' : (2 : K[X]) = 0 := by
    have h := congrArg C h2
    rw [map_ofNat, map_zero] at h
    exact h
  simp only [map_pow, map_zero, map_one]
  linear_combination (-X ^ 4 - X ^ 5 - X ^ 6 - X ^ 7 - X ^ 8 - X ^ 9 - X ^ 10 - X ^ 11 - X ^ 12 - X ^ 13 - X ^ 14 - X ^ 15) * h2'

private theorem u42_id_one_1 {K : Type} [Field K] (a b : K) (h2 : (2 : K) = 0) (ha : a = 1) (hb : b = 1) :
    (X ^ 5 - 1 : K[X]) = (1 + X) * (X ^ 4 + C a ^ 2 * X ^ 3 + C b * X ^ 2 + C a * X + 1) + 0 * (X ^ 15 - 1) := by
  subst a b
  have h2' : (2 : K[X]) = 0 := by
    have h := congrArg C h2
    rw [map_ofNat, map_zero] at h
    exact h
  simp only [map_pow, map_zero, map_one]
  linear_combination (-1 - X - X ^ 2 - X ^ 3 - X ^ 4) * h2'

private theorem u42_id_w_0 {K : Type} [Field K] (w a b : K) (hw : w ^ 2 + w + 1 = 0)
    (h2 : (2 : K) = 0) (ha : a = w) (hb : b = 0) :
    (X ^ 3 - 1 : K[X]) = (C w + C w ^ 2 * X + X ^ 2 + X ^ 3 + C w * X ^ 4 + C w ^ 2 * X ^ 5 + C w ^ 2 * X ^ 6 + X ^ 7 + C w * X ^ 8 + C w * X ^ 9 + C w ^ 2 * X ^ 10 + X ^ 11 + X ^ 12 + C w * X ^ 13 + C w ^ 2 * X ^ 14) * (X ^ 4 + C a ^ 2 * X ^ 3 + C b * X ^ 2 + C a * X + 1) + (C w ^ 2 + C w ^ 2 * X ^ 3) * (X ^ 15 - 1) := by
  subst a b
  have hw' : C w ^ 2 + C w + 1 = 0 := by
    have h := congrArg C hw
    rw [map_add, map_add, map_pow, map_one, map_zero] at h
    exact h
  have h2' : (2 : K[X]) = 0 := by
    have h := congrArg C h2
    rw [map_ofNat, map_zero] at h
    exact h
  simp only [map_pow, map_zero, map_one]
  linear_combination (1 - 2 * X + X ^ 2 - C w * X ^ 2 + 2 * X ^ 3 - C w * X ^ 3 + C w * X ^ 4 - C w ^ 2 * X ^ 4 - 4 * X ^ 5 - X ^ 6 - C w * X ^ 6 + 2 * X ^ 7 - 2 * C w * X ^ 7 + C w * X ^ 8 - C w ^ 2 * X ^ 8 - 2 * X ^ 9 + C w * X ^ 9 - C w ^ 2 * X ^ 9 - 4 * X ^ 10 + 2 * X ^ 11 - 2 * C w * X ^ 11 + X ^ 12 - C w * X ^ 12 + C w * X ^ 13 - C w ^ 2 * X ^ 13 - 4 * X ^ 14 - X ^ 15 - C w * X ^ 15 + X ^ 16 - C w * X ^ 16 + C w * X ^ 17 - C w ^ 2 * X ^ 17 - 2 * X ^ 18) * hw' + (-1 - C w + X + C w * X - X ^ 2 - X ^ 3 - C w * X ^ 3 - 2 * C w * X ^ 4 + 2 * X ^ 5 + 2 * C w * X ^ 5 + C w * X ^ 6 - 2 * X ^ 7 - 2 * C w * X ^ 8 + X ^ 9 + 2 * X ^ 10 + 2 * C w * X ^ 10 - 2 * X ^ 11 - X ^ 12 - C w * X ^ 12 - 2 * C w * X ^ 13 + 2 * X ^ 14 + 2 * C w * X ^ 14 + C w * X ^ 15 - X ^ 16 - C w * X ^ 17 + X ^ 18 + C w * X ^ 18) * h2'

private theorem u42_id_w_1 {K : Type} [Field K] (w a b : K) (hw : w ^ 2 + w + 1 = 0)
    (h2 : (2 : K) = 0) (ha : a = w) (hb : b = 1) :
    (X ^ 3 - 1 : K[X]) = (C w ^ 2 + X + C w * X ^ 3 + C w ^ 2 * X ^ 4 + C w * X ^ 5 + X ^ 6 + C w ^ 2 * X ^ 8 + C w * X ^ 10 + X ^ 11 + C w ^ 2 * X ^ 12 + X ^ 13) * (X ^ 4 + C a ^ 2 * X ^ 3 + C b * X ^ 2 + C a * X + 1) + (C w + X ^ 2) * (X ^ 15 - 1) := by
  subst a b
  have hw' : C w ^ 2 + C w + 1 = 0 := by
    have h := congrArg C hw
    rw [map_add, map_add, map_pow, map_one, map_zero] at h
    exact h
  have h2' : (2 : K[X]) = 0 := by
    have h := congrArg C h2
    rw [map_ofNat, map_zero] at h
    exact h
  simp only [map_pow, map_zero, map_one]
  linear_combination (-1 + X - C w * X - X ^ 2 + C w * X ^ 3 - C w ^ 2 * X ^ 3 - 4 * X ^ 4 + X ^ 5 - C w * X ^ 5 - X ^ 6 - C w * X ^ 6 + C w * X ^ 7 - C w ^ 2 * X ^ 7 - X ^ 8 - C w * X ^ 8 - C w * X ^ 9 - X ^ 10 - X ^ 11 + C w * X ^ 11 - C w ^ 2 * X ^ 11 - 2 * X ^ 12 + 2 * X ^ 13 - 2 * C w * X ^ 13 - 2 * X ^ 14 + C w * X ^ 15 - C w ^ 2 * X ^ 15 - 2 * X ^ 16) * hw' + (C w - X + X ^ 2 - C w * X ^ 3 + 2 * X ^ 4 + 2 * C w * X ^ 4 - X ^ 5 - C w * X ^ 5 + C w * X ^ 6 - 2 * C w * X ^ 7 + C w * X ^ 8 + X ^ 12 - 2 * X ^ 13 + X ^ 14 - X ^ 15 - C w * X ^ 15 + X ^ 16 + C w * X ^ 16 - X ^ 17) * h2'

private theorem u42_id_wsq_0 {K : Type} [Field K] (w a b : K) (hw : w ^ 2 + w + 1 = 0)
    (h2 : (2 : K) = 0) (ha : a = w ^ 2) (hb : b = 0) :
    (X ^ 3 - 1 : K[X]) = (C w ^ 2 + C w * X + X ^ 2 + X ^ 3 + C w ^ 2 * X ^ 4 + C w * X ^ 5 + C w * X ^ 6 + X ^ 7 + C w ^ 2 * X ^ 8 + C w ^ 2 * X ^ 9 + C w * X ^ 10 + X ^ 11 + X ^ 12 + C w ^ 2 * X ^ 13 + C w * X ^ 14) * (X ^ 4 + C a ^ 2 * X ^ 3 + C b * X ^ 2 + C a * X + 1) + (C w + C w * X ^ 3) * (X ^ 15 - 1) := by
  subst a b
  have hw' : C w ^ 2 + C w + 1 = 0 := by
    have h := congrArg C hw
    rw [map_add, map_add, map_pow, map_one, map_zero] at h
    exact h
  have h2' : (2 : K[X]) = 0 := by
    have h := congrArg C h2
    rw [map_ofNat, map_zero] at h
    exact h
  simp only [map_pow, map_zero, map_one]
  linear_combination (-1 + C w * X - C w ^ 2 * X + X ^ 2 - C w * X ^ 2 - C w * X ^ 3 + C w ^ 3 * X ^ 3 - C w ^ 4 * X ^ 3 - 4 * X ^ 4 + C w ^ 2 * X ^ 4 - C w ^ 3 * X ^ 4 + 2 * C w * X ^ 5 - 2 * C w ^ 2 * X ^ 5 + X ^ 6 - C w ^ 2 * X ^ 6 + 2 * X ^ 7 - 2 * C w * X ^ 7 + C w ^ 3 * X ^ 7 - C w ^ 4 * X ^ 7 - 4 * X ^ 8 + C w ^ 2 * X ^ 8 - C w ^ 3 * X ^ 8 - 2 * X ^ 9 + C w * X ^ 9 - C w ^ 3 * X ^ 9 + 2 * C w * X ^ 10 - 2 * C w ^ 2 * X ^ 10 + 2 * X ^ 11 - 2 * C w * X ^ 11 + C w ^ 3 * X ^ 11 - C w ^ 4 * X ^ 11 - X ^ 12 - C w * X ^ 12 + C w ^ 3 * X ^ 12 - C w ^ 4 * X ^ 12 - 4 * X ^ 13 + C w ^ 2 * X ^ 13 - C w ^ 3 * X ^ 13 + 2 * C w * X ^ 14 - 2 * C w ^ 2 * X ^ 14 + X ^ 15 - C w ^ 2 * X ^ 15 + X ^ 16 - C w * X ^ 16 + C w ^ 3 * X ^ 16 - C w ^ 4 * X ^ 16 - 2 * X ^ 17 + C w ^ 2 * X ^ 17 - C w ^ 3 * X ^ 17) * hw' + (C w - C w * X - X ^ 2 + C w * X ^ 3 + 2 * X ^ 4 + 2 * C w * X ^ 4 - 2 * C w * X ^ 5 - X ^ 6 - C w * X ^ 6 - 2 * X ^ 7 + 2 * X ^ 8 + 2 * C w * X ^ 8 + X ^ 9 - 2 * C w * X ^ 10 - 2 * X ^ 11 + C w * X ^ 12 + 2 * X ^ 13 + 2 * C w * X ^ 13 - 2 * C w * X ^ 14 - X ^ 15 - C w * X ^ 15 - X ^ 16 + X ^ 17 + C w * X ^ 17 - C w * X ^ 18) * h2'

private theorem u42_id_wsq_1 {K : Type} [Field K] (w a b : K) (hw : w ^ 2 + w + 1 = 0)
    (h2 : (2 : K) = 0) (ha : a = w ^ 2) (hb : b = 1) :
    (X ^ 3 - 1 : K[X]) = (C w + X + C w ^ 2 * X ^ 3 + C w * X ^ 4 + C w ^ 2 * X ^ 5 + X ^ 6 + C w * X ^ 8 + C w ^ 2 * X ^ 10 + X ^ 11 + C w * X ^ 12 + X ^ 13) * (X ^ 4 + C a ^ 2 * X ^ 3 + C b * X ^ 2 + C a * X + 1) + (C w ^ 2 + X ^ 2) * (X ^ 15 - 1) := by
  subst a b
  have hw' : C w ^ 2 + C w + 1 = 0 := by
    have h := congrArg C hw
    rw [map_add, map_add, map_pow, map_one, map_zero] at h
    exact h
  have h2' : (2 : K[X]) = 0 := by
    have h := congrArg C h2
    rw [map_ofNat, map_zero] at h
    exact h
  simp only [map_pow, map_zero, map_one]
  linear_combination (1 + X - C w * X - X ^ 2 - 2 * X ^ 3 + C w ^ 2 * X ^ 3 - C w ^ 3 * X ^ 3 + 2 * C w * X ^ 4 - 2 * C w ^ 2 * X ^ 4 - X ^ 5 - C w * X ^ 5 + X ^ 6 - C w ^ 2 * X ^ 6 + C w ^ 3 * X ^ 6 - C w ^ 4 * X ^ 6 - 4 * X ^ 7 + C w ^ 2 * X ^ 7 - C w ^ 3 * X ^ 7 + X ^ 8 - C w * X ^ 8 + C w ^ 3 * X ^ 8 - C w ^ 4 * X ^ 8 - C w ^ 2 * X ^ 9 - X ^ 10 - X ^ 11 + C w * X ^ 11 - C w ^ 3 * X ^ 11 - 2 * X ^ 12 + 2 * X ^ 13 - 2 * C w * X ^ 13 + C w ^ 3 * X ^ 13 - C w ^ 4 * X ^ 13 - 2 * X ^ 14 + C w * X ^ 14 - C w ^ 2 * X ^ 14 - 2 * X ^ 15 + C w ^ 2 * X ^ 15 - C w ^ 3 * X ^ 15 + C w * X ^ 16 - C w ^ 2 * X ^ 16) * hw' + (-1 - C w - X + X ^ 2 + X ^ 3 + C w * X ^ 3 - 2 * C w * X ^ 4 + C w * X ^ 5 - X ^ 6 - C w * X ^ 6 + 2 * X ^ 7 + 2 * C w * X ^ 7 - X ^ 8 - C w * X ^ 8 + X ^ 12 - 2 * X ^ 13 + X ^ 14 + C w * X ^ 15 - C w * X ^ 16 - X ^ 17) * h2'

end Identities

section Matrices

open Polynomial

private theorem u42_aeval_of_identity {K : Type} [Field K] (A : Matrix (Fin 4) (Fin 4) K)
    (p q r T : K[X]) (hp : aeval A p = 0) (h15 : A ^ 15 = 1)
    (hT : T = q * p + r * (X ^ 15 - 1)) : aeval A T = 0 := by
  rw [hT, map_add, map_mul, map_mul, hp, map_sub, map_pow, aeval_X, map_one, h15, sub_self]
  simp

private theorem u42_pow_of_charpoly {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4)
    (hK2 : (2 : K) = 0)
    {w : K} (hw : w ^ 2 + w + 1 = 0) (A : Matrix (Fin 4) (Fin 4) K) (a b : K)
    (hχ : A.charpoly = X ^ 4 + C a ^ 2 * X ^ 3 + C b * X ^ 2 + C a * X + 1) (hb : b ^ 2 = b)
    (h15 : A ^ 15 = 1) : A ^ 3 = 1 ∨ A ^ 5 = 1 := by
  have hCH : aeval A (X ^ 4 + C a ^ 2 * X ^ 3 + C b * X ^ 2 + C a * X + 1 : K[X]) = 0 := by
    rw [← hχ]
    exact Matrix.aeval_self_charpoly A
  have hb01 : b = 0 ∨ b = 1 := by
    have h : b * (b - 1) = 0 := by linear_combination hb
    rcases mul_eq_zero.1 h with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.1 h)
  have hcube : ∀ h : aeval A (X ^ 3 - 1 : K[X]) = 0, A ^ 3 = 1 := by
    intro h
    simp only [map_sub, map_pow, aeval_X, map_one] at h
    exact sub_eq_zero.1 h
  have hfive : ∀ h : aeval A (X ^ 5 - 1 : K[X]) = 0, A ^ 5 = 1 := by
    intro h
    simp only [map_sub, map_pow, aeval_X, map_one] at h
    exact sub_eq_zero.1 h
  rcases u42_mem_of_card_four hK hw a with ha | ha | ha | ha <;> rcases hb01 with hb' | hb'
  · exact Or.inl (hcube (u42_aeval_of_identity A _ _ _ _ hCH h15 (u42_id_zero_0 a b hK2 ha hb')))
  · exact Or.inl (hcube (u42_aeval_of_identity A _ _ _ _ hCH h15 (u42_id_zero_1 a b hK2 ha hb')))
  · exact Or.inl (hcube (u42_aeval_of_identity A _ _ _ _ hCH h15 (u42_id_one_0 a b hK2 ha hb')))
  · exact Or.inr (hfive (u42_aeval_of_identity A _ _ _ _ hCH h15 (u42_id_one_1 a b hK2 ha hb')))
  · exact Or.inl (hcube (u42_aeval_of_identity A _ _ _ _ hCH h15
      (u42_id_w_0 w a b hw hK2 ha hb')))
  · exact Or.inl (hcube (u42_aeval_of_identity A _ _ _ _ hCH h15
      (u42_id_w_1 w a b hw hK2 ha hb')))
  · exact Or.inl (hcube (u42_aeval_of_identity A _ _ _ _ hCH h15
      (u42_id_wsq_0 w a b hw hK2 ha hb')))
  · exact Or.inl (hcube (u42_aeval_of_identity A _ _ _ _ hCH h15
      (u42_id_wsq_1 w a b hw hK2 ha hb')))

end Matrices

section Transport

open Polynomial

private theorem u42_two_eq_zero {K : Type} [Field K] [CharP K 2] : (2 : K) = 0 := by
  exact_mod_cast CharP.cast_eq_zero K 2

private theorem u42_mem_SU_matrix {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 4)
    (g : GL (Fin 4) K) (hg : g ∈ StatedSU 4 (2 ^ 1) K) :
    (g : Matrix (Fin 4) (Fin 4) K).det = 1 ∧
      ((g : Matrix (Fin 4) (Fin 4) K).map (CFSG.LieType.BorelTits.unitaryInvolution K 2 1)).transpose *
        (g : Matrix (Fin 4) (Fin 4) K) = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
  rw [← CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hF 4] at hg
  exact CFSG.LieType.Universal.Unitary.mem_SUid.1 hg

private theorem u42_SU_fifteen {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 4)
    (g : GL (Fin 4) K) (hg : g ∈ StatedSU 4 (2 ^ 1) K) (h15 : g ^ 15 = 1) :
    g ^ 3 = 1 ∨ g ^ 5 = 1 := by
  have h2 : (2 : K) = 0 := u42_two_eq_zero
  obtain ⟨w, hw⟩ := u42_exists_cube_root hK
  obtain ⟨hdet, hu⟩ := u42_mem_SU_matrix hK g hg
  obtain ⟨a, b, hχ, hb⟩ := u42_charpoly_form h2 (CFSG.LieType.BorelTits.unitaryInvolution K 2 1 : K →+* K)
    (fun x => (CFSG.LieType.BorelTits.unitaryInvolution_apply (K := K) (p := 2) (f := 1) x).trans
      (by norm_num))
    (g : Matrix (Fin 4) (Fin 4) K)
    hdet hu
  have hM : (g : Matrix (Fin 4) (Fin 4) K) ^ 15 = 1 := by
    rw [← Units.val_pow_eq_pow_val, h15, Units.val_one]
  rcases u42_pow_of_charpoly hK h2 hw (g : Matrix (Fin 4) (Fin 4) K) a b hχ hb hM with h | h
  · left
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, h, Units.val_one]
  · right
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, h, Units.val_one]

private theorem u42_proj_fifteen {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 4)
    (y : StatedProj (StatedSU 4 (2 ^ 1) K)) (hy : y ^ 15 = 1) : y ^ 3 = 1 ∨ y ^ 5 = 1 := by
  classical
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective y
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hy
  unfold StatedScalars at hy
  obtain ⟨c, hc⟩ := MonoidHom.mem_range.1 hy
  obtain ⟨hdet, hun⟩ := u42_mem_SU_matrix hK _ (h ^ 15 : StatedSU 4 (2 ^ 1) K).2
  rw [← hc] at hdet hun
  have hc3 : (c : K) ^ 3 = 1 := by
    have h00 := congrFun (congrFun hun 0) 0
    simp [Matrix.mul_apply, Matrix.transpose_apply, Matrix.diagonal_apply, frobenius_def] at h00
    linear_combination h00
  have hc4 : (c : K) ^ 4 = 1 := by
    simpa [Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin] using hdet
  have hc1 : (c : K) = 1 := by linear_combination hc4 - (c : K) * hc3
  have hcu : c = 1 := Units.val_eq_one.1 hc1
  have h1 : ((h ^ 15 : StatedSU 4 (2 ^ 1) K) : GL (Fin 4) K) = 1 := by
    rw [← hc, hcu, map_one]
  have hpow : (h : GL (Fin 4) K) ^ 15 = 1 := by
    rw [← Subgroup.coe_pow, h1]
  rcases u42_SU_fifteen hK (h : GL (Fin 4) K) h.2 hpow with h3 | h5
  · left
    have hh : h ^ 3 = 1 := Subtype.ext (by simpa using h3)
    rw [← QuotientGroup.mk_pow, hh, QuotientGroup.mk_one]
  · right
    have hh : h ^ 5 = 1 := Subtype.ext (by simpa using h5)
    rw [← QuotientGroup.mk_pow, hh, QuotientGroup.mk_one]

private theorem u42_proj_fifteen_gen {P F : ℕ} [Fact P.Prime] (hP : P = 2) (hPF : P ^ F = 2 ^ 1)
    (y : StatedProj (StatedSU 4 (P ^ F) (GaloisField P (2 * F)))) (hy : y ^ 15 = 1) :
    y ^ 3 = 1 ∨ y ^ 5 = 1 := by
  subst hP
  have hF : F = 1 := by
    have h := hPF
    rw [pow_one] at h
    exact Nat.pow_right_injective (le_refl 2) (show 2 ^ F = 2 ^ 1 by rw [pow_one]; exact h)
  subst hF
  have hK : Nat.card (GaloisField 2 (2 * 1)) = 4 := by
    rw [GaloisField.card 2 (2 * 1) (by norm_num)]
    norm_num
  exact u42_proj_fifteen hK y hy

end Transport

theorem u42_noFifteen {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.twistedA 3 q).Valid)
    (hq : q.card = 2) : U42NoFifteen q hv := by
  intro x hx
  have h15 : x ^ 15 = 1 := by
    rw [← hx]
    exact pow_orderOf_eq_one x
  haveI : Fact (TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA 3 q, hv⟩).Prime :=
    ⟨TauCeti.ValidLieTypeIndex.characteristic_prime _⟩
  have hchar : TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA 3 q, hv⟩ = q.p :=
    TauCeti.LieTypeIndex.characteristic_twistedA 3 q
  have hfe : TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA 3 q, hv⟩ = q.exponent :=
    TauCeti.LieTypeIndex.fieldExponent_twistedA 3 q
  have hP : TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA 3 q, hv⟩ = 2 := by
    rw [hchar]
    exact (u42_p_exponent hq).1
  have hPF : TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA 3 q, hv⟩ ^
      TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA 3 q, hv⟩ = 2 ^ 1 := by
    rw [hchar, hfe, pow_one, ← TauCeti.PrimePower.card_def]
    exact hq
  let e := CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj 3 q hv
  have hy : (e x) ^ 15 = 1 := by
    rw [← map_pow, h15, map_one]
  rcases u42_proj_fifteen_gen hP hPF (e x) hy with h | h
  · have hx3 : x ^ 3 = 1 := by
      apply e.injective
      rw [map_pow, h, map_one]
    have hd := orderOf_dvd_of_pow_eq_one hx3
    rw [hx] at hd
    norm_num at hd
  · have hx5 : x ^ 5 = 1 := by
      apply e.injective
      rw [map_pow, h, map_one]
    have hd := orderOf_dvd_of_pow_eq_one hx5
    rw [hx] at hd
    norm_num at hd

theorem u42_fixSubgroup_solvable (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedA 3 q).Valid) (hq : q.card = 2)
    (α : MulAut (TauCeti.CFSGIndex.lie ⟨.twistedA 3 q, hv⟩).Group) (hα : α ^ 3 = 1) (hα1 : α ≠ 1) :
    IsSolvable ↥(CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup α) :=
  u42_fixSubgroup_solvable_of_noFifteen hv hq (u42_noFifteen hv hq) α hα hα1

theorem u42_downLe (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedA 3 q).Valid) (hq : q.card = 2) :
    DownLe 3 1 (TauCeti.CFSGIndex.lie ⟨.twistedA 3 q, hv⟩).Group :=
  u42_downLe_of_noFifteen hv hq (u42_noFifteen hv hq)

end CFSG.LocalAnalysis.GLTheoremA
