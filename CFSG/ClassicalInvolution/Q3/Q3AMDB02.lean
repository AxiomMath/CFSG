module

public import CFSG.ClassicalInvolution.Q3.Q3AMDB01

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.Q3T8.Asc77 CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Q3.Q3CP

section Elementary

variable {G : Type} [Group G]

theorem exists_fixed_conj_of_three [Finite G] {P : Subgroup G} (hP : IsPGroup 2 P)
    {R₁ R₂ R₃ : Subgroup G} (h12 : R₁ ≠ R₂) (h13 : R₁ ≠ R₃) (h23 : R₂ ≠ R₃)
    (hstab : ∀ s ∈ P, ∀ Q ∈ ({R₁, R₂, R₃} : Set (Subgroup G)),
      conjSub s Q ∈ ({R₁, R₂, R₃} : Set (Subgroup G))) :
    ∃ Q ∈ ({R₁, R₂, R₃} : Set (Subgroup G)), ∀ s ∈ P, conjSub s Q = Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set V : Set (Subgroup G) := {R₁, R₂, R₃} with hV
  let _inst : MulAction ↥P ↥V :=
    { smul := fun s Q => ⟨conjSub (s : G) (Q : Subgroup G), hstab s s.2 Q Q.2⟩
      one_smul := fun Q => Subtype.ext (conjSub_one _)
      mul_smul := fun s s' Q => Subtype.ext (conjSub_mul _ _ _) }
  have hcard : Nat.card ↥V = 3 := by
    rw [Nat.card_coe_set_eq]
    exact Set.ncard_eq_three.mpr ⟨R₁, R₂, R₃, h12, h13, h23, rfl⟩
  obtain ⟨⟨Q, hQ⟩, hfix⟩ := hP.nonempty_fixed_point_of_prime_not_dvd_card
    (α := ↥V) (by rw [hcard]; norm_num)
  refine ⟨Q, hQ, fun s hs => ?_⟩
  exact congrArg Subtype.val (hfix ⟨s, hs⟩)

theorem mul_conj_eq_of_conjSub_eq {M R : Subgroup G} {w : G} (hw : IsUniqueInvolution M w)
    (hwR : w ∈ R) (hRM : R ≤ M) {s : G} (hs : conjSub s R = R) : s * w * s⁻¹ = w := by
  have hmem : s * w * s⁻¹ ∈ R := hs ▸ conj_mem_conjSub hwR
  have hsq : (s * w * s⁻¹) * (s * w * s⁻¹) = 1 := by
    calc (s * w * s⁻¹) * (s * w * s⁻¹) = s * (w * w) * s⁻¹ := by group
      _ = 1 := by rw [hw.sq]; group
  rcases hw.unique _ (hRM hmem) hsq with h | h
  · exfalso
    apply hw.ne_one
    have e : w = s⁻¹ * (s * w * s⁻¹) * s := by group
    rw [e, h]
    group
  · exact h

theorem isSylow2In_top_conj {P : Subgroup G} (h : IsSylow2In P ⊤) (g : G) :
    IsSylow2In (conjSub g P) ⊤ := by
  have h1 := h.conj g
  rwa [show conjSub g (⊤ : Subgroup G) = ⊤ from
    Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective] at h1

end Elementary

section Axis


variable {G : Type} [Group G] [Finite G]

theorem PspSetting.eq_axis_of_mem_RSet_of_le [IsSimpleGroup G] {Ω : Set (Subgroup G)}
    {K J K' : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}
    (hset : PspSetting Ω K J S R T W z t K')
    {t₁ t₂ t₃ : G} {R₁ R₂ R₃ : Subgroup G} (hax : BadAxis K J K' z t t₁ t₂ t₃ R₁ R₂ R₃)
    {S₀ : Sylow 2 G} (h₁S : R₁ ≤ (S₀ : Subgroup G)) (h₂S : R₂ ≤ (S₀ : Subgroup G))
    (h₃S : R₃ ≤ (S₀ : Subgroup G)) {Q : Subgroup G} (hQ : Q ∈ RSet Ω)
    (hQS : Q ≤ (S₀ : Subgroup G)) : Q = R₁ ∨ Q = R₂ ∨ Q = R₃ := by
  have hstd := hset.bad.std
  have hΩ : HypOmegaMod Ω := hstd.stand.hyp
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hstd.stand.trans hstd.noTwins hM
  have hKΩ : K ∈ Ω := hstd.stand.mem
  have hJΩ : J ∈ Ω := hstd.hJ.1
  have hR₁Ω : R₁ ∈ RSet Ω := mem_RSet_of_isSylow2In hKΩ hax.syl₁
  have hR₂Ω : R₂ ∈ RSet Ω := mem_RSet_of_isSylow2In hJΩ hax.syl₂
  by_contra hcon
  push Not at hcon
  obtain ⟨hQ₁, hQ₂, hQ₃⟩ := hcon
  have hcomm₁ : Commutes Q R₁ := l67Gen G Ω hΩ S₀ Q hQ R₁ hR₁Ω hQS h₁S hQ₁
  have hcomm₂ : Commutes Q R₂ := l67Gen G Ω hΩ S₀ Q hQ R₂ hR₂Ω hQS h₂S hQ₂
  obtain ⟨M, hM, hQM⟩ := exists_isSylow2In_of_mem_RSet hQ
  obtain ⟨m, hm⟩ := hΩ.exists_uniqueInvolution hM
  have hnorm : ∀ {A : Subgroup G} {R' : Subgroup G}, A ∈ Ω → IsSylow2In R' A → R' ∈ RSet Ω →
      Commutes Q R' → Q ≤ Subgroup.normalizer (A : Set G) := by
    intro A R' hA hR'A hR'Ω hc y hy
    have hAy : conjSub y A ∈ Ω := hΩ.conjInvariant y A hA
    have hR'y : R' ≤ conjSub y A := by
      intro x hx
      rw [mem_conjSub_iff]
      have hxy : y⁻¹ * x * y = x := by
        have := hc y hy x hx
        calc y⁻¹ * x * y = y⁻¹ * (x * y) := by group
          _ = y⁻¹ * (y * x) := by rw [this]
          _ = x := by group
      rw [hxy]
      exact hR'A.1 hx
    have h4 : 4 ≤ Nat.card R' := by have := hΩ.eight_le_of_mem_RSet hR'Ω; omega
    exact mem_normalizer_iff_conjSub_eq.mpr (hΩ.eq_of_le_of_le hA hAy hR'A.2.1 h4 hR'A.1 hR'y).symm
  have hQK : Q ≤ Subgroup.normalizer (K : Set G) := hnorm hKΩ hax.syl₁ hR₁Ω hcomm₁
  have hQJ : Q ≤ Subgroup.normalizer (J : Set G) := hnorm hJΩ hax.syl₂ hR₂Ω hcomm₂
  have hMK : M ≠ K := by
    rintro rfl
    exact hQ₁ (eq_of_isSylow2In_of_le_sylow' hQM hax.syl₁ hQS h₁S)
  have hMJ : M ≠ J := by
    rintro rfl
    exact hQ₂ (eq_of_isSylow2In_of_le_sylow' hQM hax.syl₂ hQS h₂S)
  have hMK' : M ≠ K' := by
    rintro rfl
    exact hQ₃ (eq_of_isSylow2In_of_le_sylow' hQM hax.syl₃ hQS h₃S)
  have hMnK : M ∈ omegaNbr Ω K := ⟨hM, hMK, Q, hQ, hQM.1, hQK⟩
  have hMnJ : M ∈ omegaNbr Ω J := ⟨hM, hMJ, Q, hQ, hQM.1, hQJ⟩
  have hmul : m = z * t := hset.bad.eq_mul_of_nbr_nbr hMnK hMnJ hm
  exact hMK' (hnt K' hset.nbrK.1 M ⟨hM, z * t, hset.uniq_mul, hmul ▸ hm⟩)

end Axis

end CFSG.ClassicalInvolution.Q3.Q3AM
