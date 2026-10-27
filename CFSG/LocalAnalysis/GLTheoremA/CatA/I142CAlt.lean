module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.CentQAlt
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LayerBridge

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I142C

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator CFSG.LocalAnalysis.GLTheoremA.AltDown
open scoped commutatorElement

theorem perfect_le_layer_alt8_three_cycle {x : alternatingGroup (Fin 8)}
    (hσ : (x : Equiv.Perm (Fin 8)).cycleType = {3}) {P : Subgroup (alternatingGroup (Fin 8))}
    (hP : P ≤ Subgroup.centralizer {x}) (hperf : ⁅P, P⁆ = P) :
    P ≤ GLALayer (Subgroup.centralizer {x}) := by
  set σ : Equiv.Perm (Fin 8) := (x : Equiv.Perm (Fin 8)) with hσdef
  have hcyc : σ.IsCycle := Equiv.Perm.card_cycleType_eq_one.1 (by rw [hσ]; rfl)
  have hfac : σ.cycleFactorsFinset = {σ} := hcyc.cycleFactorsFinset_eq_singleton
  have hcomm : ∀ a ∈ P, Commute (a : Equiv.Perm (Fin 8)) σ := fun a ha =>
    cq_commute_coe (Subgroup.mem_centralizer_singleton_iff.1 (hP ha))
  have hPF : P ≤ (alternatingGroup.ofSubtype σ.supportᶜ).range := by
    calc P = ⁅P, P⁆ := hperf.symm
      _ ≤ _ := by
        refine Subgroup.commutator_le.2 fun a ha b hb => ?_
        rw [mem_range_ofSubtype_compl_iff]
        intro u hu
        have h := commutator_apply_of_mem_support (hcomm a ha) (hcomm b hb)
          (fun c hc => by rw [hfac, Finset.mem_singleton] at hc; rw [hc]; exact hcomm a ha)
          (fun c hc => by rw [hfac, Finset.mem_singleton] at hc; rw [hc]; exact hcomm b hb) hu
        simpa [commutatorElement_def] using h
  have hFC : (alternatingGroup.ofSubtype σ.supportᶜ).range ≤ Subgroup.centralizer {x} :=
    fun k hk => Subgroup.mem_centralizer_singleton_iff.2
      (Subtype.ext (commute_of_mem_range_ofSubtype_compl hk).eq)
  have hFn : ((alternatingGroup.ofSubtype σ.supportᶜ).range.subgroupOf
      (Subgroup.centralizer {x})).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hFC]
    intro h c hh hc
    rw [mem_range_ofSubtype_compl_iff] at hh ⊢
    intro u hu
    have hcσ : Commute (c : Equiv.Perm (Fin 8)) σ :=
      congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hc)
    have hmem := apply_mem_support_of_commute hcσ.inv_left hu
    have hh' := hh _ hmem
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Equiv.Perm.mul_apply]
    rw [hh']
    simp
  have hcard5 : (σ.supportᶜ).card = 5 := by
    have h1 : σ.support.card = 3 := by rw [← Equiv.Perm.sum_cycleType, hσ]; rfl
    rw [Finset.card_compl, h1]
    simp
  obtain ⟨e⟩ := nonempty_range_ofSubtype_equiv σ.supportᶜ 5 hcard5
  haveI : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup_five
  haveI hFs : IsSimpleGroup ↥(alternatingGroup.ofSubtype σ.supportᶜ).range := e.isSimpleGroup
  have hA5 : ∃ a b : alternatingGroup (Fin 5), a * b ≠ b * a := by
    refine ⟨⟨Equiv.swap 0 1 * Equiv.swap 1 2, ?_⟩, ⟨Equiv.swap 0 1 * Equiv.swap 2 3, ?_⟩, ?_⟩
    · exact Equiv.Perm.mem_alternatingGroup.2 (by decide)
    · exact Equiv.Perm.mem_alternatingGroup.2 (by decide)
    · intro h
      have := congrArg Subtype.val h
      revert this
      decide
  have hFnon : ∃ a b : ↥(alternatingGroup.ofSubtype σ.supportᶜ).range,
      a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hA5
    exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩
  have hFq : CFSG.Open.IsQuasisimple ↥(alternatingGroup.ofSubtype σ.supportᶜ).range :=
    b3Lie_isQuasisimple_of_simple hFnon
  have hFcomp : CFSG.Open.IsComponentOf (alternatingGroup.ofSubtype σ.supportᶜ).range
      (Subgroup.centralizer {x}) :=
    ⟨hFC, CFSG.Open.IsSubnormal.step hFC hFn (CFSG.Open.IsSubnormal.refl _), hFq⟩
  exact hPF.trans (le_sSup (show (alternatingGroup.ofSubtype σ.supportᶜ).range ∈
    {M : Subgroup (alternatingGroup (Fin 8)) |
      CFSG.Open.IsComponentOf M (Subgroup.centralizer {x})} from hFcomp))

theorem perfectInLayer_conj_alt (n : ℕ) (hn : n = 5 ∨ n = 6 ∨ n = 8) {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) {y : alternatingGroup (Fin n)} (hy : y ^ q = 1) (hy1 : y ≠ 1) :
    PerfectInLayer (MulAut.conj y) := by
  intro P hP hperf
  rw [fixSubgroup_conj_eq_centralizer'] at hP ⊢
  have hσq : (y : Equiv.Perm (Fin n)) ^ q = 1 := by simpa using congrArg Subtype.val hy
  have hσ1 : (y : Equiv.Perm (Fin n)) ≠ 1 := fun h => hy1 (Subtype.ext h)
  haveI : Fact q.Prime := ⟨hq⟩
  have hord : orderOf (y : Equiv.Perm (Fin n)) = q := orderOf_eq_prime hσq hσ1
  obtain ⟨k, hk, hkn⟩ := cq_cycleType_of_prime_order (y : Equiv.Perm (Fin n)) hq hord
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · exfalso
      apply hσ1
      rw [h0] at hk
      exact Equiv.Perm.cycleType_eq_zero.1 (by rw [hk]; rfl)
    · exact h0
  by_cases hspec : n = 8 ∧ q = 3 ∧ k = 1
  · obtain ⟨rfl, rfl, rfl⟩ := hspec
    exact perfect_le_layer_alt8_three_cycle (by simpa using hk) hP hperf
  · have hPbot : P = ⊥ := by
      by_contra hne
      have hdiv : Nat.card P ∣ (n - k * q).factorial * q ^ k * k.factorial := by
        rw [← cq_card_centralizer_replicate (y : Equiv.Perm (Fin n)) hk1 hk]
        exact (Subgroup.card_dvd_of_le hP).trans (cq_card_centralizer_dvd_alt y)
      haveI : Nontrivial ↥P := (Subgroup.nontrivial_iff_ne_bot P).2 hne
      haveI : Group.IsPerfect ↥P := Subgroup.isPerfect_iff.2 hperf
      have hq3 : 3 ≤ q := by
        have := hq.two_le
        omega
      have hqn : q ≤ n := by nlinarith
      have hq357 : q = 3 ∨ q = 5 ∨ q = 7 := by
        have hq8 : q ≤ 8 := by rcases hn with rfl | rfl | rfl <;> omega
        interval_cases q <;> first | omega | (exfalso; revert hq; norm_num)
      have hkle : k ≤ 2 := by rcases hq357 with rfl | rfl | rfl <;> omega
      rcases hn with rfl | rfl | rfl <;> rcases hq357 with rfl | rfl | rfl <;> interval_cases k <;>
        first
          | omega
          | (norm_num [Nat.factorial] at hdiv
             exact false_of_perfect_card_dvd (by norm_num) hdiv)
    rw [hPbot]
    exact bot_le

theorem conj_injective_of_center {S : Type} [Group S] (hz : Subgroup.center S = ⊥) :
    Function.Injective (MulAut.conj : S →* MulAut S) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  have hz' : a ∈ Subgroup.center S := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h := congrArg (fun φ : MulAut S => φ g) ha
    simp only [MulAut.conj_apply, MulAut.one_apply] at h
    exact (mul_inv_eq_iff_eq_mul.1 h).symm
  rw [hz, Subgroup.mem_bot] at hz'
  exact hz'

theorem exists_conj_of_pow_eq_one {S : Type} [Group S] {p : ℕ} (hp : p.Prime)
    (hO : ¬ p ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer S))
    {β : MulAut S} (hβ : β ^ p = 1) : ∃ x : S, MulAut.conj x = β := by
  have hmem : β ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner S := by
    have h1 : (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner S) β) ^ p = 1 := by
      rw [← map_pow, hβ, map_one]
    have h2 := orderOf_dvd_of_pow_eq_one h1
    rcases (Nat.dvd_prime hp).1 h2 with h | h
    · rw [orderOf_eq_one_iff] at h
      exact (QuotientGroup.eq_one_iff β).1 h
    · exfalso
      apply hO
      rw [← h]
      exact orderOf_dvd_natCard _
  obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 hmem
  exact ⟨x, hx⟩

theorem perfectInLayer_of_alt {S : Type} [Group S] (n : ℕ) (hn : n = 5 ∨ n = 6 ∨ n = 8)
    (e : S ≃* alternatingGroup (Fin n)) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {x : S}
    (hx : x ^ q = 1) (hx1 : x ≠ 1) : PerfectInLayer (MulAut.conj x) := by
  refine CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.perfectInLayer_of_congr e
    (MulAut.conj x) ?_
  rw [CFSG.ComponentClassification.OuterAutomorphisms.congr_conj]
  refine perfectInLayer_conj_alt n hn hq hq2 (y := e x) ?_ ?_
  · rw [← map_pow, hx, map_one]
  · intro h
    apply hx1
    exact e.injective (by rw [h, map_one])

end CFSG.LocalAnalysis.GLTheoremA.I142C
