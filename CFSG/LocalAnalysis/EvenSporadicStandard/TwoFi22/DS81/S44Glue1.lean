module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Facts
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.S44Act
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.S44FrameG

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.S44

open Subgroup CFSG.Quasithin CFSG.EvenSmallLie CFSG.EvenSmallLie.UnitarySix

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G] {L E : Subgroup G} {t : G}

theorem card_normalizer_inf_centralizer (D : Facts G t L E)
    (hLH : L.relIndex (centralizer ({t} : Set G)) = 2) :
    Nat.card ↥(normalizer (E : Set G) ⊓ centralizer ({t} : Set G)) =
      2 * Nat.card ↥(normalizer (E : Set G) ⊓ L) := by
  set N := normalizer (E : Set G)
  set H := centralizer ({t} : Set G)
  have h1 : N.relIndex H = N.relIndex L :=
    relIndex_eq_of_forall_eq_mul D.le_centralizer fun h hh => D.exists_eq_mul hh
  have hA := Subgroup.relIndex_mul_card (H := N) (K := H)
  have hB := Subgroup.relIndex_mul_card (H := N) (K := L)
  have hC := Subgroup.relIndex_mul_card (H := L) (K := H)
  rw [inf_of_le_left D.le_centralizer, hLH] at hC
  have hr : N.relIndex L ≠ 0 := relIndex_ne_zero_of_finite _ _
  rw [h1] at hA
  rw [← hA] at hC
  rw [← hB] at hC
  have : N.relIndex L * Nat.card ↥(N ⊓ H) = N.relIndex L * (2 * Nat.card ↥(N ⊓ L)) := by
    rw [← hC]
    ring
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hr) this

def conjOrb (K : Subgroup G) (x : G) : Set G := {y | ∃ n ∈ K, n * x * n⁻¹ = y}

theorem mem_conjOrb_self (K : Subgroup G) (x : G) : x ∈ conjOrb K x :=
  ⟨1, K.one_mem, by simp⟩

theorem conjOrb_eq_of_mem {K : Subgroup G} {x y : G} (h : y ∈ conjOrb K x) :
    conjOrb K y = conjOrb K x := by
  obtain ⟨m, hm, rfl⟩ := h
  ext z
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n * m, K.mul_mem hn hm, by simp [mul_assoc]⟩
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n * m⁻¹, K.mul_mem hn (K.inv_mem hm), by simp [mul_assoc]⟩

theorem image_conj_conjOrb {K : Subgroup G} {ν : G} (h1 : ∀ n ∈ K, ν * n * ν⁻¹ ∈ K)
    (h2 : ∀ n ∈ K, ν⁻¹ * n * ν ∈ K) (x : G) :
    (fun e => ν * e * ν⁻¹) '' conjOrb K x = conjOrb K (ν * x * ν⁻¹) := by
  ext z
  constructor
  · rintro ⟨_, ⟨n, hn, rfl⟩, rfl⟩
    exact ⟨ν * n * ν⁻¹, h1 n hn, by group⟩
  · rintro ⟨m, hm, rfl⟩
    refine ⟨ν⁻¹ * m * ν * x * (ν⁻¹ * m * ν)⁻¹, ⟨ν⁻¹ * m * ν, h2 m hm, rfl⟩, ?_⟩
    group

theorem exists_swap {O : Fin 5 → Set G} (F : FrameModelG G L E t O) (D : Facts G t L E)
    (hCE : centralizer (E : Set G) = E) {ν : G} (hν : ν ∈ normalizer (E : Set G))
    (hνH : ν ∈ centralizer ({t} : Set G)) (hνL : ν ∉ L) :
    (fun e => ν * e * ν⁻¹) '' O 0 = O 1 := by
  set NL := normalizer (E : Set G) ⊓ L with hNL
  have hνL' : ν ∈ normalizer (L : Set G) := D.centralizer_le hνH
  have hconjL : ∀ {g : G}, g ∈ normalizer (L : Set G) → ∀ n ∈ L, g * n * g⁻¹ ∈ L :=
    fun hg n hn => (mem_normalizer_iff.1 hg n).1 hn
  have hνI : ν⁻¹ ∈ normalizer (E : Set G) := Subgroup.inv_mem _ hν
  have hνI' : ν⁻¹ ∈ normalizer (L : Set G) := Subgroup.inv_mem _ hνL'
  have h1 : ∀ n ∈ NL, ν * n * ν⁻¹ ∈ NL := fun n hn =>
    ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hν hn.1) hνI, hconjL hνL' n hn.2⟩
  have h2 : ∀ n ∈ NL, ν⁻¹ * n * ν ∈ NL := fun n hn => by
    have e : ν⁻¹ * n * ν = ν⁻¹ * n * ν⁻¹⁻¹ := by rw [inv_inv]
    rw [e]
    exact ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hνI hn.1) (Subgroup.inv_mem _ hνI),
      hconjL hνI' n hn.2⟩
  have htν : ν * t * ν⁻¹ = t := by
    rw [mul_inv_eq_iff_eq_mul]
    exact mem_centralizer_singleton_iff.1 hνH
  obtain ⟨x₀, hx₀E, hO0⟩ := F.isOrbit 0
  have hx₀ : x₀ ∈ O 0 := by
    rw [hO0]
    exact mem_conjOrb_self NL x₀
  have hcxE : ν * x₀ * ν⁻¹ ∈ E := (mem_normalizer_iff.1 hν x₀).1 hx₀E
  have hcx1 : ν * x₀ * ν⁻¹ ≠ 1 := by
    intro h
    apply F.not_mem_one 0
    have : x₀ = 1 := by
      have := congrArg (fun y => ν⁻¹ * y * ν) h
      simpa [mul_assoc] using this
    rwa [this] at hx₀
  have hcxt : ν * x₀ * ν⁻¹ ≠ t := by
    intro h
    apply F.not_mem_t 0
    have : x₀ = t := by
      have := congrArg (fun y => ν⁻¹ * y * ν) h
      have h3 : ν⁻¹ * t * ν = t := by
        have hc : t * ν = ν * t := (mem_centralizer_singleton_iff.1 hνH).symm
        calc ν⁻¹ * t * ν = ν⁻¹ * (t * ν) := by group
          _ = ν⁻¹ * (ν * t) := by rw [hc]
          _ = t := by group
      simpa [mul_assoc, h3] using this
    rwa [this] at hx₀
  rcases F.cover _ hcxE hcx1 with h | ⟨j, hj⟩
  · exact absurd h hcxt
  obtain ⟨xj, hxjE, hOj⟩ := F.isOrbit j
  have hO0' : O 0 = conjOrb NL x₀ := hO0
  have hOj' : O j = conjOrb NL xj := hOj
  have hkey : (fun e => ν * e * ν⁻¹) '' O 0 = O j := by
    rw [hO0', image_conj_conjOrb h1 h2, hOj']
    rw [hOj'] at hj
    exact conjOrb_eq_of_mem hj
  have hcard : (O j).ncard = 22 := by
    rw [← hkey, Set.ncard_image_of_injective]
    · simpa using F.ncard 0
    · intro a b hab
      simpa using hab
  have hj01 : j = 0 ∨ j = 1 := by
    have := F.ncard j
    rw [hcard] at this
    revert this
    fin_cases j <;> simp
  rcases hj01 with rfl | rfl
  · exfalso
    obtain ⟨n, hn, hconj⟩ := F.frameAut (conjE ν hν) (by
      intro e he
      show ν * (e : G) * ν⁻¹ = t
      rw [he]
      exact htν) (by
      intro e he
      show ν * (e : G) * ν⁻¹ ∈ O 0
      rw [← hkey]
      exact ⟨e, he, rfl⟩)
    have hcent : n⁻¹ * ν ∈ centralizer (E : Set G) := by
      rw [mem_centralizer_iff]
      intro e he
      have := hconj ⟨e, he⟩
      change ν * e * ν⁻¹ = n * e * n⁻¹ at this
      have h4 : n⁻¹ * ν * e = e * (n⁻¹ * ν) := by
        calc n⁻¹ * ν * e = n⁻¹ * (ν * e * ν⁻¹) * ν := by group
          _ = n⁻¹ * (n * e * n⁻¹) * ν := by rw [this]
          _ = e * (n⁻¹ * ν) := by group
      exact h4.symm
    rw [hCE] at hcent
    apply hνL
    have : ν = n * (n⁻¹ * ν) := by group
    rw [this]
    exact mul_mem hn.2 (D.E_le hcent)
  · exact hkey

end CFSG.EvenSporadicStandard.TwoFi22.DS81.S44
