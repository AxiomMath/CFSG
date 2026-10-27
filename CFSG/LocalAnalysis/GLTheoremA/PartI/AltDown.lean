module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.I1412Levels
import CFSG.LocalAnalysis.GLTheoremA.PartI.AltDownPerm
import CFSG.LocalAnalysis.GLTheoremA.PartI.AltDownComp
import CFSG.LocalAnalysis.AGLEmbedding.AltOuterOdd

public section

namespace CFSG.LocalAnalysis.GLTheoremA.AltDown

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open Equiv Equiv.Perm

theorem exists_conj_of_alt {n p : ℕ} (hn : 5 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2)
    {α : MulAut (alternatingGroup (Fin n))} (hα : α ^ p = 1) (hα1 : α ≠ 1) :
    ∃ x : alternatingGroup (Fin n), x ≠ 1 ∧ x ^ p = 1 ∧ α = MulAut.conj x := by
  have hOut := CFSG.AGLEmbedding.card_outer_alternatingGroup_dvd_four n hn
  have hne : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer
      (alternatingGroup (Fin n))) ≠ 0 := fun h => by
    rw [h] at hOut
    norm_num at hOut
  haveI : Finite (CFSG.ComponentClassification.OuterAutomorphisms.Outer
      (alternatingGroup (Fin n))) := Nat.finite_of_card_ne_zero hne
  set q := QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner
      (alternatingGroup (Fin n))) α with hq
  have hqp : q ^ p = 1 := by rw [hq, ← map_pow, hα, map_one]
  have hq1 : q = 1 := by
    rcases (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one hqp) with h | h
    · exact orderOf_eq_one_iff.1 h
    · exact absurd (h ▸ orderOf_dvd_natCard q)
        (CFSG.AGLEmbedding.not_dvd_card_outer_alternatingGroup n hn p hp hp2)
  have hαin : α ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (alternatingGroup (Fin n)) := by
    rw [hq, QuotientGroup.mk'_apply] at hq1
    exact (QuotientGroup.eq_one_iff α).1 hq1
  obtain ⟨x, rfl⟩ : ∃ x : alternatingGroup (Fin n), MulAut.conj x = α := hαin
  refine ⟨x, ?_, ?_, rfl⟩
  · intro h
    apply hα1
    rw [h, map_one]
  · have hc : MulAut.conj (x ^ p) = 1 := by
      rw [map_pow]
      exact hα
    have hcen : x ^ p ∈ Subgroup.center (alternatingGroup (Fin n)) := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h := DFunLike.congr_fun hc g
      rw [MulAut.conj_apply, MulAut.one_apply] at h
      exact (mul_inv_eq_iff_eq_mul.1 h).symm
    have hZ : Subgroup.center (alternatingGroup (Fin n)) = ⊥ :=
      alternatingGroup.center_eq_bot (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)
    rw [hZ, Subgroup.mem_bot] at hcen
    exact hcen

theorem mem_fixSubgroup_conj {G : Type*} [Group G] {x g : G} :
    g ∈ fixSubgroup (MulAut.conj x) ↔ Commute g x := by
  rw [mem_fixSubgroup, MulAut.conj_apply, mul_inv_eq_iff_eq_mul]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

theorem commute_coe {α : Type*} [Fintype α] [DecidableEq α] {g h : alternatingGroup α}
    (hgh : Commute g h) : Commute (g : Perm α) (h : Perm α) :=
  congrArg Subtype.val hgh.eq

theorem le_range_ofSubtype_of_glaPComponent {n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {x : alternatingGroup (Fin n)} (hxp : x ^ p = 1)
    {I : Subgroup (alternatingGroup (Fin n))}
    (hI : GLAPComponent p (fixSubgroup (MulAut.conj x)) I) :
    I ≤ (alternatingGroup.ofSubtype ((x : Perm (Fin n)).support)ᶜ).range := by
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hσp : (x : Perm (Fin n)) ^ p = 1 := by simpa using congrArg Subtype.val hxp
  have hNC : cycleGroup (x : Perm (Fin n)) ≤ fixSubgroup (MulAut.conj x) := fun g hg =>
    mem_fixSubgroup_conj.2 (Subtype.ext (commute_of_mem_cycleGroup hg).eq)
  have hNn : ∀ g ∈ fixSubgroup (MulAut.conj x), ∀ m ∈ cycleGroup (x : Perm (Fin n)),
      g * m * g⁻¹ ∈ cycleGroup (x : Perm (Fin n)) := fun g hg m hm =>
    cycleGroup_conj_mem (commute_coe (mem_fixSubgroup_conj.1 hg)) hm
  have hNp : IsPGroup p (cycleGroup (x : Perm (Fin n))) := fun g =>
    ⟨1, by rw [pow_one]; exact Subtype.ext (pow_eq_one_of_mem_cycleGroup hσp g.2)⟩
  have hcomm := glaPComponent_commute_of_normal_isPGroup hp hI hNC hNn hNp
  have hI_comm : ∀ a ∈ I, ∀ c ∈ (x : Perm (Fin n)).cycleFactorsFinset,
      Commute (a : Perm (Fin n)) c := by
    intro a ha c hc
    obtain ⟨c', hc'N, hc'⟩ := exists_mem_cycleGroup_of_mem_cycleFactorsFinset hodd hσp hc
    rw [← hc']
    exact congrArg Subtype.val (hcomm a ha c' hc'N)
  have hI_comm_σ : ∀ a ∈ I, Commute (a : Perm (Fin n)) (x : Perm (Fin n)) := fun a ha =>
    commute_coe (mem_fixSubgroup_conj.1 (hI.1 ha))
  calc I = ⁅I, I⁆ := (glaPComponent_perfect hI).symm
    _ ≤ _ := by
      refine Subgroup.commutator_le.2 fun a ha b hb => ?_
      rw [mem_range_ofSubtype_compl_iff]
      intro u hu
      have h := commutator_apply_of_mem_support (hI_comm_σ a ha) (hI_comm_σ b hb)
        (hI_comm a ha) (hI_comm b hb) hu
      simpa [commutatorElement_def] using h

theorem factorial_dvd_twentyFour {m : ℕ} (h : m < 5) : Nat.factorial m ∣ 24 := by
  interval_cases m <;> decide

end CFSG.LocalAnalysis.GLTheoremA.AltDown

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open Equiv Equiv.Perm CFSG.LocalAnalysis.GLTheoremA.AltDown

theorem kdAltDown_holds : KDAltDown := by
  intro n p hn hp hp2 α hα hα1 I hI
  obtain ⟨x, hx1, hxp, rfl⟩ := exists_conj_of_alt hn hp hp2 hα hα1
  have hσp : (x : Perm (Fin n)) ^ p = 1 := by simpa using congrArg Subtype.val hxp
  have hσ1 : (x : Perm (Fin n)) ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hIF := le_range_ofSubtype_of_glaPComponent hp hp2 hxp hI
  obtain ⟨m, hm⟩ : ∃ m, ((x : Perm (Fin n)).support)ᶜ.card = m := ⟨_, rfl⟩
  have hmn : m + p ≤ n := by
    have h := Finset.card_compl ((x : Perm (Fin n)).support)
    have h1 := le_card_support_of_pow_eq_one hp hσp hσ1
    have h2 : ((x : Perm (Fin n)).support).card ≤ n := by
      simpa using Finset.card_le_univ ((x : Perm (Fin n)).support)
    rw [Fintype.card_fin, hm] at h
    omega
  obtain ⟨e⟩ := nonempty_range_ofSubtype_equiv ((x : Perm (Fin n)).support)ᶜ m hm
  have hIdvd : Nat.card I ∣ m.factorial := by
    have h1 := Subgroup.card_dvd_of_le hIF
    rw [Nat.card_congr e.toEquiv] at h1
    exact h1.trans (by simpa using natCard_alternatingGroup_dvd_factorial (Fin m))
  haveI : Nontrivial ↥I := nontrivial_of_glaPComponent hp hI
  have hm5 : 5 ≤ m := by
    by_contra hlt
    haveI : Group.IsPerfect ↥I := Subgroup.isPerfect_iff.2 (glaPComponent_perfect hI)
    exact false_of_isPerfect_of_card_dvd_twentyFour
      (hIdvd.trans (factorial_dvd_twentyFour (not_le.1 hlt)))
  have hmp : p ≤ m := by
    by_contra hlt
    refine not_coprime_card_of_glaPComponent hp hI ?_
    have hpm : ¬ p ∣ m.factorial := fun h => hlt ((Nat.Prime.dvd_factorial hp).1 h)
    exact ((Nat.Prime.coprime_iff_not_dvd hp).2 hpm).coprime_dvd_right hIdvd
  have hm5' : 5 ≤ Nat.card (Fin m) := by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; exact hm5
  haveI : IsSimpleGroup (alternatingGroup (Fin m)) := alternatingGroup.isSimpleGroup hm5'
  haveI : IsSimpleGroup ↥(alternatingGroup.ofSubtype ((x : Perm (Fin n)).support)ᶜ).range :=
    e.isSimpleGroup
  have hFC : (alternatingGroup.ofSubtype ((x : Perm (Fin n)).support)ᶜ).range ≤
      fixSubgroup (MulAut.conj x) := fun k hk =>
    mem_fixSubgroup_conj.2 (Subtype.ext (commute_of_mem_range_ofSubtype_compl hk).eq)
  have hIeq := eq_of_isSubnormal_of_isSimpleGroup (glaPComponent_of_le hp hI hIF hFC).2.1
    ((Subgroup.nontrivial_iff_ne_bot I).1 inferInstance)
  exact ⟨m, max_le hm5 hmp, hmn, nonempty_pSimple_equiv hp hI
    (alternatingGroup.center_eq_bot (by omega)) ((MulEquiv.subgroupCongr hIeq).trans e)⟩

end CFSG.LocalAnalysis.GLTheoremA
