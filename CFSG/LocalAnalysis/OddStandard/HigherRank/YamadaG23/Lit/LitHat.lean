module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit.LitMono2
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit.LitPerf
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit.LitS5
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit.LitSolvP

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup
open scoped commutatorElement

structure LitMonoData {G : Type*} [Group G] (A M : Subgroup G) : Prop where
  normal : M.Normal
  simple : IsSimpleGroup ↥M
  nonab : ¬ ∀ a ∈ M, ∀ b ∈ M, a * b = b * a
  A_le : A ≤ M
  cent : centralizer (M : Set G) = ⊥
  min : ∀ K : Subgroup G, K.Normal → K ≠ ⊥ → M ≤ K

private theorem lit_isPerfect_of_isSimpleGroup_of_not_comm {Y : Type*} [Group Y]
    (hY : IsSimpleGroup Y) (hnc : ¬ ∀ a b : Y, a * b = b * a) : Group.IsPerfect Y := by
  rw [Group.isPerfect_def]
  rcases hY.eq_bot_or_eq_top_of_normal (commutator Y) with h | h
  · exfalso
    haveI : IsMulCommutative Y := (commutator_eq_bot_iff Y).mp h
    exact hnc fun a b => mul_comm a b
  · exact h

theorem lit_monoData {G : Type} [Group G] [Finite G] {A : Subgroup G}
    {φ : ↥(normalizer (A : Set G)) →* Equiv.Perm (Fin 6)} (h : LitBar A φ) :
    ∃ M : Subgroup G, LitMonoData A M ∧ ∀ σ ∈ alternatingGroup (Fin 6),
      ∃ g : ↥(normalizer (A : Set G)), (g : G) ∈ M ∧ φ g = σ := by
  obtain ⟨M, hMnorm, hMs, hAM, hCent, hMin, hA6⟩ := lit_mono h
  refine ⟨M, ⟨hMnorm, hMs, ?_, hAM, hCent, hMin⟩, hA6⟩
  intro hcomm
  haveI : IsMulCommutative ↥M := IsMulCommutative.of_comm fun a b =>
    Subtype.ext (hcomm a a.2 b b.2)
  have hprime : (Nat.card M).Prime := (Group.is_simple_iff_prime_card (α := ↥M)).mp hMs
  have h16 : 16 ∣ Nat.card M := by
    rw [← h.card]
    exact Subgroup.card_dvd_of_le hAM
  rcases hprime.eq_one_or_self_of_dvd 16 h16 with h1 | hp
  · norm_num at h1
  · rw [← hp] at hprime
    norm_num at hprime

theorem lit_hat {X G : Type} [Group X] [Finite X] [Group G] [Finite G] {Z A : Subgroup X}
    [Z.Normal] (h : LitCtx Z A) (hnab : ¬ ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (φ : ↥(normalizer (A : Set X)) →* Equiv.Perm (Fin 6)) (hφs : Function.Surjective φ)
    (hφk : ∀ g : ↥(normalizer (A : Set X)), φ g = 1 ↔ ∀ a ∈ A, ⁅a, (g : X)⁆ ∈ Z)
    (hO : ∀ a ∈ A, ∀ x ∈ CFSG.oddCore X, x * a = a * x) {π : X →* G}
    (hπ : Function.Surjective π) (hk : π.ker = litP Z) {M : Subgroup G}
    (d : LitMonoData (A.map π) M) :
    (litPerf (M.comap π)).map π = M ∧
      (∀ x ∈ litPerf (M.comap π), ∀ y ∈ π.ker, x * y = y * x) ∧ Z ≤ litPerf (M.comap π) := by
  have hnc : ¬ ∀ a b : ↥M, a * b = b * a := by
    intro h
    exact d.nonab fun a ha b hb => congrArg Subtype.val (h ⟨a, ha⟩ ⟨b, hb⟩)
  have hMperf : ⁅M, M⁆ = M :=
    Subgroup.isPerfect_iff.mp (lit_isPerfect_of_isSimpleGroup_of_not_comm d.simple hnc)
  have hHmap : (litPerf (M.comap π)).map π = M := lit_perf_map hπ hMperf
  haveI hKnorm : (M.comap π).Normal := d.normal.comap π
  haveI hHnorm : (litPerf (M.comap π)).Normal := litPerf_normal (M.comap π)
  have hsolv : Group.IsSolvable ↥π.ker := by
    rw [hk]
    exact lit_solvable_litP h.central
  let D : Subgroup X := centralizer (CFSG.oddCore X : Set X)
  have hDnorm : D.Normal := Subgroup.normal_centralizer (H := CFSG.oddCore X)
  have hAD : A ≤ D := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact hO a ha y hy
  have hA_ne_bot : A.map π ≠ ⊥ := by
    intro hbot
    have hAle : A ≤ litP Z := by
      rw [← hk]
      exact (Subgroup.map_eq_bot_iff A).mp hbot
    have hAZ : A ≤ Z := by
      have h1 : A ≤ A ⊓ litP Z := le_inf le_rfl hAle
      rwa [lit_A_inf_litP h] at h1
    have hdvd : Nat.card A ∣ Nat.card Z := Subgroup.card_dvd_of_le hAZ
    rw [h.card_A, h.card_Z] at hdvd
    norm_num at hdvd
  have hDmap_ne : D.map π ≠ ⊥ := by
    intro hbot
    exact hA_ne_bot (le_bot_iff.mp ((Subgroup.map_mono hAD).trans (le_of_eq hbot)))
  have hDmap_norm : (D.map π).Normal := hDnorm.map π hπ
  have hMD : M ≤ D.map π := d.min (D.map π) hDmap_norm hDmap_ne
  haveI : D.Normal := hDnorm
  have hHD : litPerf (M.comap π) ≤ D := lit_perf_le hsolv hMD
  refine ⟨hHmap, ?_, ?_⟩
  · intro x hx y hy
    have hxD : x ∈ D := hHD hx
    have hx_odd : ∀ o ∈ CFSG.oddCore X, x * o = o * x := fun o ho =>
      (Subgroup.mem_centralizer_iff.mp hxD o ho).symm
    have hx_Z : ∀ z ∈ Z, x * z = z * x := fun z hz => (h.central z hz x).symm
    have hcent_le : π.ker ≤ Subgroup.centralizer ({x} : Set X) := by
      rw [hk]
      show Z ⊔ CFSG.oddCore X ≤ Subgroup.centralizer ({x} : Set X)
      refine sup_le ?_ ?_
      · intro z hz
        rw [Subgroup.mem_centralizer_iff]
        intro w hw
        rw [Set.mem_singleton_iff] at hw
        subst hw
        exact hx_Z z hz
      · intro o ho
        rw [Subgroup.mem_centralizer_iff]
        intro w hw
        rw [Set.mem_singleton_iff] at hw
        subst hw
        exact hx_odd o ho
    exact Subgroup.mem_centralizer_iff.mp (hcent_le hy) x (Set.mem_singleton x)
  · refine lit_s5 h hnab φ hφs hφk ?_
    rw [sup_comm]
    intro a ha
    have hpaM : π a ∈ M := d.A_le ⟨a, ha, rfl⟩
    have hpaH : π a ∈ (litPerf (M.comap π)).map π := by
      rw [hHmap]
      exact hpaM
    obtain ⟨k, hkH, hkπ⟩ := Subgroup.mem_map.mp hpaH
    have hmem : a * k⁻¹ ∈ litP Z := by
      rw [← hk, MonoidHom.mem_ker, map_mul, map_inv, hkπ, mul_inv_cancel]
    have ha_eq : a = (a * k⁻¹) * k := by group
    rw [ha_eq]
    exact mul_mem_sup hmem hkH

end CFSG.OddStandard.HigherRank.YamadaG23
