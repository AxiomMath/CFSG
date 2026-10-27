module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Glauberman.Basic
public import CFSG.GH74.GLS.Stage2.Signalizer.L53Kfam

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.GlaubermanB

open Subgroup
open CFSG.GH74.GLS.Bg (kLowInfty Kfam Klow Kup classTwo zOf gen)
open CFSG.GH74.GLS.Stage2.Signalizer.L53 (le_gen gen_le gen_mono Kfam_succ_even Kfam_succ_odd
  Kfam_subset_classTwo Kfam_mono_aux)
open scoped commutatorElement

variable {G : Type} [Group G]

theorem comm_zOf_eq_bot (A : Subgroup G) :
    ⁅A ⊓ centralizer (A : Set G), A ⊓ centralizer (A : Set G)⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro z hz
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hw).2 z (Subgroup.mem_inf.mp hz).1).symm

theorem comm_eq_one_of_mem_centralizer {B : Subgroup G} {w g : G}
    (hw : w ∈ centralizer (B : Set G)) (hg : g ∈ B) : ⁅w, g⁆ = 1 := by
  rw [commutatorElement_eq_one_iff_mul_comm]
  exact (Subgroup.mem_centralizer_iff.mp hw g hg).symm

theorem comm_mem_of_normalizer {B : Subgroup G} {x g : G} (hx : x ∈ normalizer (B : Set G))
    (hg : g ∈ B) : ⁅x, g⁆ ∈ B := by
  have e : ⁅x, g⁆ = (x * g * x⁻¹) * g⁻¹ := by simp only [commutatorElement_def]
  rw [e]
  exact B.mul_mem ((Subgroup.mem_normalizer_iff.mp hx g).mp hg) (B.inv_mem hg)

theorem exists_element_ab [Finite G] {S T A : Subgroup G} (hTS : T ≤ S) (hAn : A.Normal)
    (hAT : A ≤ T) (hA2 : ⁅⁅A, A⁆, A⁆ = ⊥) (hTA : ⁅T, A⁆ ≤ A ⊓ centralizer (A : Set G))
    (hbad : ¬ ∀ m, 1 ≤ m → gen (Kfam S m) ≤ T) :
    ∃ g ∈ S, g ∉ T ∧ (∀ x ∈ A, iterComm x g 3 ∈ A ⊓ centralizer (A : Set G)) ∧
      ∀ z ∈ A ⊓ centralizer (A : Set G), iterComm z g 2 = 1 := by
  classical
  have hAS : A ∈ classTwo S := ⟨hAT.trans hTS, hA2⟩
  have hZn : (A ⊓ centralizer (A : Set G)).Normal := by
    have : (centralizer (A : Set G)).Normal := Subgroup.normal_centralizer
    infer_instance
  have hZA : A ⊓ centralizer (A : Set G) ≤ A := inf_le_left
  have h3 : ∀ g : G, (∀ x ∈ A, ⁅⁅x, g⁆, g⁆ = 1) → ∀ x ∈ A, iterComm x g 3 ∈ A ⊓ centralizer (A : Set G) := by
    intro g h x hx
    show ⁅⁅⁅x, g⁆, g⁆, g⁆ ∈ _
    rw [h x hx, commutatorElement_one_left]
    exact Subgroup.one_mem _
  have h2 : ∀ g : G, (∀ x ∈ A, ⁅⁅x, g⁆, g⁆ = 1) → ∀ z ∈ A ⊓ centralizer (A : Set G),
      iterComm z g 2 = 1 := fun g h z hz => h z (hZA hz)
  obtain ⟨m, hm⟩ := not_forall.mp hbad
  obtain ⟨hm1, hm2⟩ := not_imp.mp hm
  have hex : ∃ n, 1 ≤ n ∧ ¬ gen (Kfam S n) ≤ T := ⟨m, hm1, hm2⟩
  obtain ⟨n, hn1, hnbad, hmin⟩ : ∃ n, 1 ≤ n ∧ ¬ gen (Kfam S n) ≤ T ∧
      ∀ m, m < n → 1 ≤ m → gen (Kfam S m) ≤ T := by
    refine ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2, fun m hlt hm1 => ?_⟩
    by_contra hc
    exact Nat.find_min hex hlt ⟨hm1, hc⟩
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  by_cases hA : A ∈ Kfam S k
  ·
    have hAQ : A ≤ gen (Kfam S k) := le_gen hA
    obtain ⟨B, hB, hBT⟩ : ∃ B ∈ Kfam S (k + 1), ¬ B ≤ T := by
      by_contra hc
      push Not at hc
      exact hnbad (gen_le hc)
    obtain ⟨g, hgB, hgT⟩ := SetLike.not_le_iff_exists.mp hBT
    have hBcl := Kfam_subset_classTwo S _ hB
    have hgS : g ∈ S := hBcl.1 hgB
    by_cases hk : Even k
    · rw [Kfam_succ_even S hk] at hB
      obtain ⟨-, hQnorm, hall⟩ := hB
      have hAB : A ≤ normalizer (B : Set G) := hAQ.trans hQnorm
      refine ⟨g, hgS, hgT, ?_, ?_⟩
      ·
        intro x hx
        show ⁅⁅⁅x, g⁆, g⁆, g⁆ ∈ _
        have h1 : ⁅x, g⁆ ∈ B := comm_mem_of_normalizer (hAB hx) hgB
        have h2' : ⁅⁅⁅x, g⁆, g⁆, g⁆ ∈ ⁅⁅B, B⁆, B⁆ :=
          Subgroup.commutator_mem_commutator (Subgroup.commutator_mem_commutator h1 hgB) hgB
        rw [hBcl.2, Subgroup.mem_bot] at h2'
        rw [h2']
        exact Subgroup.one_mem _
      ·
        have hBZA : ⁅B, A ⊓ centralizer (A : Set G)⁆ ≤ B ⊓ centralizer (B : Set G) := by
          refine hall _ ⟨hZA.trans (hAT.trans hTS), ?_⟩ (hZA.trans hAQ)
            ((le_top).trans (Subgroup.normalizer_eq_top_iff.mpr hZn).ge) ?_ ?_
          · rw [comm_zOf_eq_bot A]; exact Subgroup.commutator_bot_left _
          · rw [comm_zOf_eq_bot A]; exact Subgroup.commutator_bot_right B
          · have h1 : ⁅zOf B, A ⊓ centralizer (A : Set G)⁆ ≤ A ⊓ centralizer (A : Set G) :=
              Subgroup.commutator_le_right _ _
            exact le_bot_iff.mp ((Subgroup.commutator_mono_left h1).trans (comm_zOf_eq_bot A).le)
        intro z hz
        show ⁅⁅z, g⁆, g⁆ = 1
        have : ⁅z, g⁆ ∈ B ⊓ centralizer (B : Set G) := by
          rw [← commutatorElement_inv]
          exact (B ⊓ centralizer (B : Set G)).inv_mem
            (hBZA (Subgroup.commutator_mem_commutator hgB hz))
        exact comm_eq_one_of_mem_centralizer (Subgroup.mem_inf.mp this).2 hgB
    · rw [Kfam_succ_odd S hk] at hB
      have h1 : ⁅A, B⁆ ≤ B ⊓ centralizer (B : Set G) := by
        rw [Subgroup.commutator_comm]
        exact (Subgroup.commutator_mono_right hAQ).trans hB.2
      have hq : ∀ x ∈ A, ⁅⁅x, g⁆, g⁆ = 1 := by
        intro x hx
        have hxg : ⁅x, g⁆ ∈ B ⊓ centralizer (B : Set G) :=
          h1 (Subgroup.commutator_mem_commutator hx hgB)
        exact comm_eq_one_of_mem_centralizer (Subgroup.mem_inf.mp hxg).2 hgB
      exact ⟨g, hgS, hgT, h3 g hq, h2 g hq⟩
  ·
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hA hAS
    by_cases hk : Even k
    · exfalso
      apply hA
      obtain ⟨j, hj⟩ := hk
      have hk' : ¬ Even (k - 1) := by
        rw [Nat.not_even_iff_odd]
        exact ⟨j - 1, by omega⟩
      have e : Kfam S k = Kup S (gen (Kfam S (k - 1))) := by
        have := Kfam_succ_odd S hk'
        rwa [Nat.sub_add_cancel (by omega)] at this
      rw [e]
      refine ⟨hAS, ?_⟩
      have hQ' : gen (Kfam S (k - 1)) ≤ T := hmin (k - 1) (by omega) (by omega)
      calc ⁅A, gen (Kfam S (k - 1))⁆ ≤ ⁅A, T⁆ := Subgroup.commutator_mono_right hQ'
        _ = ⁅T, A⁆ := Subgroup.commutator_comm A T
        _ ≤ A ⊓ centralizer (A : Set G) := hTA
    · have hk1 : k = 1 := by
        by_contra hne
        obtain ⟨j, hj⟩ : Odd k := Nat.not_even_iff_odd.mp hk
        have hj1 : 1 ≤ j := by omega
        have h1 := (Kfam_mono_aux S j).1
        have hk2 : k + 1 = 2 * j + 2 := by omega
        apply hnbad
        rw [hk2]
        exact (gen_mono h1).trans (hmin (2 * j) (by omega) (by omega))
      subst hk1
      have hA' : A ∉ Klow S (gen (Kfam S 0)) := by
        rwa [Kfam_succ_even S (by decide : Even 0)] at hA
      have hQ₀ : gen (Kfam S 0) ≤ normalizer (A : Set G) :=
        le_top.trans (Subgroup.normalizer_eq_top_iff.mpr hAn).ge
      obtain ⟨A₂, hA₂, -, hAA₂, hc1, hc2, hc3⟩ : ∃ A₂ ∈ classTwo S, A₂ ≤ gen (Kfam S 0) ∧
          A ≤ normalizer (A₂ : Set G) ∧ ⁅A, ⁅A₂, A₂⁆⁆ = ⊥ ∧
          ⁅⁅zOf A, A₂⁆, A₂⁆ = ⊥ ∧ ¬ ⁅A, A₂⁆ ≤ zOf A := by
        by_contra hcon
        push Not at hcon
        exact hA' ⟨hAS, hQ₀, fun A₂ hA₂ hA₂Q hAA₂ h1 h2 => hcon A₂ hA₂ hA₂Q hAA₂ h1 h2⟩
      rw [Subgroup.commutator_le] at hc3
      push Not at hc3
      obtain ⟨a, ha, g, hg, hag⟩ := hc3
      have hgS : g ∈ S := hA₂.1 hg
      have hgT : g ∉ T := by
        intro hgT
        apply hag
        have : ⁅g, a⁆ ∈ A ⊓ centralizer (A : Set G) :=
          hTA (Subgroup.commutator_mem_commutator hgT ha)
        have e : ⁅a, g⁆ = ⁅g, a⁆⁻¹ := (commutatorElement_inv g a).symm
        rw [e]
        exact (A ⊓ centralizer (A : Set G)).inv_mem this
      refine ⟨g, hgS, hgT, ?_, ?_⟩
      ·
        intro x hx
        show ⁅⁅⁅x, g⁆, g⁆, g⁆ ∈ _
        have hxg : ⁅x, g⁆ ∈ A₂ := comm_mem_of_normalizer (hAA₂ hx) hg
        have hxgA : ⁅x, g⁆ ∈ A := comm_mem_of_normal hAn hx g
        have hc : ⁅A₂, A₂⁆ ≤ centralizer (A : Set G) := by
          have : ⁅⁅A₂, A₂⁆, A⁆ = ⊥ := by rw [Subgroup.commutator_comm]; exact hc1
          exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp this
        have hZ : ⁅⁅x, g⁆, g⁆ ∈ A ⊓ centralizer (A : Set G) :=
          Subgroup.mem_inf.mpr ⟨comm_mem_of_normal hAn hxgA g,
            hc (Subgroup.commutator_mem_commutator hxg hg)⟩
        exact comm_mem_of_normal hZn hZ g
      · intro z hz
        show ⁅⁅z, g⁆, g⁆ = 1
        have : ⁅⁅z, g⁆, g⁆ ∈ ⁅⁅zOf A, A₂⁆, A₂⁆ :=
          Subgroup.commutator_mem_commutator (Subgroup.commutator_mem_commutator hz hg) hg
        rw [hc2] at this
        exact Subgroup.mem_bot.mp this

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.GlaubermanB

end
