module

public import CFSG.ClassicalInvolution.Asc77.AscT7L7
public import CFSG.ClassicalInvolution.AschTight.S1916Omega

public section

namespace CFSG.ClassicalInvolution.Asc77.AscAET

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Disconnected.AschTight.S1916
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem le_centralizer_of_conjSub_eq {J P : Subgroup G} {c : G} (hcJ : c ∈ trivialOnQuot J)
    (hPJ : P ≤ J) (hP2 : IsPGroup 2 P) (hc : conjSub c P = P) :
    P ≤ Subgroup.centralizer ({c} : Set G) := by
  intro y hy
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h1 : c * y * c⁻¹ ∈ P := by
    have := conj_mem_conjSub (n := c) hy
    rwa [hc] at this
  have h2 : ⁅c, y⁆ ∈ P := by
    rw [commutatorElement_def]
    exact P.mul_mem h1 (P.inv_mem hy)
  have h3 : ⁅c, y⁆ ∈ oddCoreOf J := hcJ.2 y (hPJ hy)
  have h4 : ⁅c, y⁆ = 1 :=
    eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard J) h3
      (hP2.to_le (Subgroup.zpowers_le.mpr h2))
  exact (commutatorElement_eq_one_iff_mul_comm.mp h4).symm

theorem exists_conj_centralized {J M U₀ : Subgroup G} {c : G}
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) (hcJ : c ∈ trivialOnQuot J)
    (hcM : c ∈ Subgroup.normalizer (M : Set G)) (hU2 : IsPGroup 2 U₀) (hUJ : U₀ ≤ J)
    (hUM : U₀ ≤ Subgroup.normalizer (M : Set G)) :
    ∃ x ∈ J ⊓ Subgroup.normalizer (M : Set G),
      conjSub x U₀ ≤ Subgroup.centralizer ({c} : Set G) := by
  set O : Subgroup G := oddCoreOf J ⊓ Subgroup.normalizer (M : Set G) with hO
  have hOodd : Odd (Nat.card O) :=
    (oddCoreOf_odd_natCard J).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  have hOJ : O ≤ J := inf_le_left.trans (Balance.oddCoreIn_le J)
  have hNO : ∀ g ∈ Subgroup.normalizer (J : Set G), g ∈ Subgroup.normalizer (M : Set G) →
      g ∈ Subgroup.normalizer (O : Set G) := fun g hgJ hgM =>
    mem_normalizer_inf (mem_normalizer_oddCore_of_mem_normalizer hgJ) (Subgroup.le_normalizer hgM)
  have hUO : U₀ ≤ Subgroup.normalizer (O : Set G) := fun u hu =>
    hNO u (Subgroup.le_normalizer (hUJ hu)) (hUM hu)
  have hcO : c ∈ Subgroup.normalizer (O : Set G) := hNO c hcJ.1 hcM
  set P : Subgroup G := O ⊔ U₀ with hP
  have hPJM : P ≤ J ⊓ Subgroup.normalizer (M : Set G) :=
    sup_le (le_inf hOJ inf_le_right) (le_inf hUJ hUM)
  have hle : conjSub c P ≤ P := by
    rw [hP, conjSub_sup]
    refine sup_le ?_ ?_
    · intro x hx
      rw [mem_conjSub_iff] at hx
      have h1 := (Subgroup.mem_normalizer_iff.mp hcO (c⁻¹ * x * c)).mp hx
      have e : c * (c⁻¹ * x * c) * c⁻¹ = x := by group
      rw [e] at h1
      exact Subgroup.mem_sup_left h1
    · intro x hx
      rw [mem_conjSub_iff] at hx
      have hu : c⁻¹ * x * c ∈ U₀ := hx
      have hcommN : ⁅c, c⁻¹ * x * c⁆ ∈ Subgroup.normalizer (M : Set G) := by
        rw [commutatorElement_def]
        exact (Subgroup.normalizer (M : Set G)).mul_mem
          ((Subgroup.normalizer (M : Set G)).mul_mem
            ((Subgroup.normalizer (M : Set G)).mul_mem hcM (hUM hu))
            ((Subgroup.normalizer (M : Set G)).inv_mem hcM))
          ((Subgroup.normalizer (M : Set G)).inv_mem (hUM hu))
      have hcomm : ⁅c, c⁻¹ * x * c⁆ ∈ O := ⟨hcJ.2 _ (hUJ hu), hcommN⟩
      have e : x = ⁅c, c⁻¹ * x * c⁆ * (c⁻¹ * x * c) := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact P.mul_mem (Subgroup.mem_sup_left hcomm) (Subgroup.mem_sup_right hu)
  have hcP : c ∈ Subgroup.normalizer (P : Set G) :=
    mem_normalizer_iff_conjSub_eq.mpr
      (Subgroup.eq_of_le_of_card_ge hle (natCard_conjSub P c).ge)
  obtain ⟨U₁, hU₁, hfix⟩ := T3.exists_sylow_normalized (K := P) (W := Subgroup.zpowers c) hc2
    (Subgroup.zpowers_le.mpr hcP)
  have hU₀syl : IsSylow2In U₀ P := T7L.isSylow2In_sup_of_normalizes hOodd hU2 hUO
  obtain ⟨x, hxP, hx⟩ := IsSylow2In.exists_conj hU₀syl hU₁
  refine ⟨x, hPJM hxP, ?_⟩
  rw [hx]
  exact le_centralizer_of_conjSub_eq hcJ (hU₁.1.trans (hPJM.trans inf_le_left)) hU₁.2.1
    (hfix c (Subgroup.mem_zpowers c))

omit [Finite G] in
theorem le_normalizer_of_relIndex_two {A R : Subgroup G} (hAR : A ≤ R) (h2 : A.relIndex R = 2) :
    R ≤ Subgroup.normalizer (A : Set G) := by
  have hnorm : (A.subgroupOf R).Normal := Subgroup.normal_of_index_eq_two h2
  have key : ∀ r ∈ R, ∀ a ∈ A, r * a * r⁻¹ ∈ A := by
    intro r hr a ha
    have h1 := hnorm.conj_mem ⟨a, hAR ha⟩ (Subgroup.mem_subgroupOf.mpr ha) ⟨r, hr⟩
    exact Subgroup.mem_subgroupOf.mp h1
  intro r hr
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => key r hr h hh, fun hh => ?_⟩
  have := key r⁻¹ (R.inv_mem hr) _ hh
  simpa [mul_assoc] using this

theorem exists_sylow_centralized_over {J U₁ R₀ : Subgroup G} {c : G}
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) (hcJ : c ∈ trivialOnQuot J)
    (hR₀ : IsSylow2In R₀ J) (hUR : U₁ ≤ R₀) (hidx : U₁.relIndex R₀ = 2)
    (hU₁c : U₁ ≤ Subgroup.centralizer ({c} : Set G)) :
    ∃ P : Subgroup G, IsSylow2In P J ∧ U₁ ≤ P ∧ P ≤ Subgroup.centralizer ({c} : Set G) := by
  set D : Subgroup G := J ⊓ Subgroup.normalizer (U₁ : Set G) with hD
  have hR₀D : R₀ ≤ D := le_inf hR₀.1 (le_normalizer_of_relIndex_two hUR hidx)
  have hcU : c ∈ Subgroup.normalizer (U₁ : Set G) := by
    have hcc : c ∈ Subgroup.centralizer (U₁ : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      exact Subgroup.mem_centralizer_singleton_iff.mp (hU₁c hh)
    exact Subgroup.centralizer_le_normalizer _ hcc
  have hcD : c ∈ Subgroup.normalizer (D : Set G) :=
    mem_normalizer_inf hcJ.1 (Subgroup.le_normalizer hcU)
  obtain ⟨P, hPD, hfix⟩ := T3.exists_sylow_normalized (K := D) (W := Subgroup.zpowers c) hc2
    (Subgroup.zpowers_le.mpr hcD)
  have hPJ' : P ≤ J := hPD.1.trans inf_le_left
  have hPc : P ≤ Subgroup.centralizer ({c} : Set G) :=
    le_centralizer_of_conjSub_eq hcJ hPJ' hPD.2.1 (hfix c (Subgroup.mem_zpowers c))
  have hR₀D' : IsSylow2In R₀ D := IsSylow2In.of_le hR₀ hR₀D inf_le_left
  have hcard : Nat.card R₀ = Nat.card P := hR₀D'.natCard_eq hPD
  have hPJ : IsSylow2In P J := hR₀.of_natCard_le hPD.2.1 hPJ' hcard.le
  have hU2 : IsPGroup 2 U₁ := hR₀.2.1.to_le hUR
  have hU₁D : U₁ ≤ D := le_inf (hUR.trans hR₀.1) Subgroup.le_normalizer
  have hsup2 : IsPGroup 2 ↥(P ⊔ U₁) :=
    IsPGroup.to_sup_of_normal_right' hPD.2.1 hU2 (hPD.1.trans inf_le_right)
  have hPU : P ⊔ U₁ = P := hPD.2.2 _ (sup_le hPD.1 hU₁D) hsup2 le_sup_left
  exact ⟨P, hPJ, hPU ▸ le_sup_right, hPc⟩

end CFSG.ClassicalInvolution.Asc77.AscAET
