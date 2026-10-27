module

public import CFSG.ClassicalInvolution.Asc77.AscT3TypedG2D4
public import CFSG.ClassicalInvolution.Asc77.AscE186CentA
public import CFSG.ClassicalInvolution.Balance.LayerGenerationPairG2

public section

namespace CFSG.ClassicalInvolution.Asc77.T3Typed

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3 CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.G2D4Models
open scoped commutatorElement

section Involution

variable {p : ℕ} [Fact p.Prime]

theorem involution_eq_of_commutes_aux {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {n e : ℕ}
    (hp : p ≠ 2) (he : 1 ≤ e) (ht : t = .G2 ∨ t = .trialityD4)
    {R₁ R₂ : Subgroup (modelUniv t n p e Fact.out).K} {c₁ c₂ : (modelUniv t n p e Fact.out).K}
    (hc₁ : IsUniqueInvolution R₁ c₁) (hc₂ : IsUniqueInvolution R₂ c₂)
    (hperf : ⁅R₂, R₂⁆ = R₂) (hcomm : Commutes R₁ R₂) : c₂ = c₁ := by
  rcases ht with rfl | rfl
  · have hodd : Odd (Nat.card (GaloisField p e)) := by
      rw [GaloisField.card p e (by omega)]
      exact ((Fact.out : p.Prime).odd_of_ne_two hp).pow
    rcases Balance.Bootstrap.g2_eq_one_or_eq_of_central_in_perfect (K := GaloisField p e) hodd
      hc₁.sq hc₁.ne_one (fun r hr => hcomm c₁ hc₁.mem r hr) hperf hc₂.mem
      (fun r hr => hc₂.commute_of_mem hr) with h | h
    · exact absurd h hc₂.ne_one
    · exact h
  · exact ModelFacts.trialityD4_eq_of_central_in_perfect p e hp he hperf hc₁.sq hc₁.ne_one
      hc₂.ne_one hc₂.mem (fun r hr => hc₂.commute_of_mem hr)
      (fun r hr => hcomm c₁ hc₁.mem r hr)

end Involution

section Component

variable {X : Type} [Group X] [Finite X] {p f : ℕ} [Fact p.Prime] {Φ : Set (Subgroup X)}

@[expose] def compMembers (D : OmegaLie p f Φ) (i : Fin D.card) : Set (Subgroup X) :=
  {M | ∃ R ∈ D.cls i, M = R.map (D.hom i)}

omit [Finite X] in
theorem compMembers_subset (D : OmegaLie p f Φ) (i : Fin D.card) : compMembers D i ⊆ Φ := by
  rintro _ ⟨R, hR, rfl⟩
  exact hR.2

omit [Finite X] in
theorem compMembers_unique (hΦ : HypOmegaMod p f Φ) (D : OmegaLie p f Φ) {i j : Fin D.card}
    {M : Subgroup X} (hi : M ∈ compMembers D i) (hj : M ∈ compMembers D j) : i = j := by
  by_contra hij
  obtain ⟨R, hR, rfl⟩ := hi
  obtain ⟨R', -, hR'⟩ := hj
  obtain ⟨z, hz⟩ := hΦ.classical _ hR.2
  obtain ⟨x, hx, y, hy, hxy⟩ := ih8_exists_noncomm hz
  have hx' : x ∈ D.comp i := Subgroup.map_le_range _ _ hx
  have hy' : y ∈ D.comp j := by
    rw [hR'] at hy
    exact Subgroup.map_le_range _ _ hy
  exact hxy (D.comp_commute hij x hx' y hy')

omit [Finite X] in
theorem exists_mem_compMembers (D : OmegaLie p f Φ) {M : Subgroup X} (hM : M ∈ Φ) :
    ∃ i, M ∈ compMembers D i := by
  obtain ⟨i, R, hR, hMR⟩ := D.fundamental M hM
  exact ⟨i, R, ⟨hR, hMR ▸ hM⟩, hMR⟩

omit [Finite X] in
theorem commutes_of_not_mem_compMembers (D : OmegaLie p f Φ) {i : Fin D.card} {M K : Subgroup X}
    (hM : M ∈ Φ) (hMi : M ∉ compMembers D i) (hK : K ∈ compMembers D i) : Commutes M K := by
  obtain ⟨j, hj⟩ := exists_mem_compMembers D hM
  have hji : j ≠ i := fun h => hMi (h ▸ hj)
  obtain ⟨R, -, rfl⟩ := hK
  obtain ⟨R', -, hMR'⟩ := hj
  rw [hMR']
  rintro _ ⟨x, -, rfl⟩ _ ⟨y, -, rfl⟩
  exact D.commute j i hji x y

theorem mem_omegaNbr_of_commutes {K M : Subgroup X} (hM : M ∈ Φ) (hMK : M ≠ K)
    (hc : Commutes M K) : M ∈ omegaNbr Φ K := by
  have hcomm : ⁅M, K⁆ ≤ K := Subgroup.commutator_le.mpr fun x hx y hy => by
    rw [commutatorElement_eq_one_iff_mul_comm.mpr (hc x hx y hy)]
    exact K.one_mem
  have hMN : M ≤ Subgroup.normalizer (K : Set X) := le_normalizer_of_commutator_le hcomm
  obtain ⟨R, hR, hRM, -⟩ := exists_mem_RSet_ge hM (isPGroup_two_bot' (G := X)) bot_le
  exact ⟨hM, hMK, R, hR, hRM.1, hRM.1.trans hMN⟩

variable (hp : p ≠ 2) (D : OmegaLie p f Φ) {i : Fin D.card}

include hp

omit [Finite X] in
theorem hom_injective_of_g2d4 (hi : D.tag i = .G2 ∨ D.tag i = .trialityD4) :
    Function.Injective (D.hom i) :=
  RouteD.G2D4.injective_of_ker_le_center hp hi (D.rank i) (D.admissible i).2.1 (D.hom i)
    (D.ker_le_center i)

omit [Finite X] in
theorem twin_mem_compMembers (hi : D.tag i = .G2 ∨ D.tag i = .trialityD4) {K J : Subgroup X}
    (hK : K ∈ compMembers D i) (hJ : J ∈ twinSet Φ K) : J ∈ compMembers D i := by
  obtain ⟨hJΦ, z, hzK, hzJ⟩ := hJ
  obtain ⟨j, hj⟩ := exists_mem_compMembers D hJΦ
  by_cases hji : j = i
  · exact hji ▸ hj
  · exfalso
    have hinj := hom_injective_of_g2d4 hp D hi
    obtain ⟨R, -, rfl⟩ := hK
    obtain ⟨R', -, hJR'⟩ := hj
    have hzi : z ∈ (D.hom i).range := Subgroup.map_le_range _ _ hzK.mem
    have hzj : z ∈ D.comp j := by
      rw [hJR'] at hzJ
      exact Subgroup.map_le_range _ _ hzJ.mem
    obtain ⟨c, hc⟩ := hzi
    have hcen : c ∈ Subgroup.center (D.model i).K := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply hinj
      rw [map_mul, map_mul, hc]
      exact (D.comp_commute hji z hzj _ ⟨y, rfl⟩).symm
    have hbot := RouteD.G2D4.center_modelUniv_g2d4_eq_bot hp hi (D.rank i) (D.admissible i).2.1
    rw [hbot, Subgroup.mem_bot] at hcen
    exact hzK.ne_one (by rw [← hc, hcen, map_one])

omit [Finite X] in
theorem cls_perfect_of_g2d4 (hΦ : HypOmegaMod p f Φ) (hi : D.tag i = .G2 ∨ D.tag i = .trialityD4)
    {R : Subgroup (D.model i).K} (hR : R ∈ D.cls i) : ⁅R, R⁆ = R := by
  have hinj := hom_injective_of_g2d4 hp D hi
  have hinjR : ∀ x ∈ R, D.hom i x = 1 → x = 1 := fun x _ h => hinj (h.trans (map_one _).symm)
  exact Subgroup.isPerfect_iff.mp (isPerfect_of_map (D.hom i) hinjR (hΦ.isPerfect hR.2))

omit [Finite X] in
theorem cls_involution_eq_of_commutes (hΦ : HypOmegaMod p f Φ)
    (hi : D.tag i = .G2 ∨ D.tag i = .trialityD4) {R₁ R₂ : Subgroup (D.model i).K}
    (hR₂ : R₂ ∈ D.cls i) {c₁ c₂ : (D.model i).K}
    (hc₁ : IsUniqueInvolution R₁ c₁) (hc₂ : IsUniqueInvolution R₂ c₂) (hcomm : Commutes R₁ R₂) :
    c₂ = c₁ :=
  involution_eq_of_commutes_aux hp (D.admissible i).2.1 hi hc₁ hc₂
    (cls_perfect_of_g2d4 hp D hΦ hi hR₂) hcomm

theorem mem_omegaOfSet_twinSet_iff (hq : 5 ≤ p ^ f) (hΦ : HypOmegaMod p f Φ)
    (hi : D.tag i = .G2 ∨ D.tag i = .trialityD4) {J : Subgroup X} (hJ : J ∈ compMembers D i)
    {M : Subgroup X} : M ∈ omegaOfSet Φ (twinSet Φ J) ↔ M ∈ Φ ∧ M ∉ compMembers D i := by
  constructor
  · rintro ⟨hMΦ, hall⟩
    refine ⟨hMΦ, fun hMi => ?_⟩
    have hJΦ : J ∈ Φ := compMembers_subset D i hJ
    obtain ⟨z, hz⟩ := hΦ.exists_uniqueInvolution hp hq hJΦ
    obtain ⟨zM, hzM⟩ := hΦ.exists_uniqueInvolution hp hq hMΦ
    have hexact := hΦ.toExact (D.exactMembers hp hq hΦ)
    have hcomm : Commutes J M :=
      AscE186.commutes_of_mem_omegaNbr hp hq hexact hJΦ (hall J ⟨hJΦ, z, hz, hz⟩)
    have hinj := hom_injective_of_g2d4 hp D hi
    obtain ⟨R₁, hR₁, rfl⟩ := hJ
    obtain ⟨R₂, hR₂, rfl⟩ := hMi
    obtain ⟨c₁, hc₁z, hc₁⟩ := isUniqueInvolution_of_map hinj hz
    obtain ⟨c₂, hc₂z, hc₂⟩ := isUniqueInvolution_of_map hinj hzM
    have hcomm' : Commutes R₁ R₂ := fun x hx y hy => hinj (by
      rw [map_mul, map_mul]
      exact hcomm _ (Subgroup.mem_map_of_mem _ hx) _ (Subgroup.mem_map_of_mem _ hy))
    have hcc : c₂ = c₁ := cls_involution_eq_of_commutes hp D hΦ hi hR₂ hc₁ hc₂ hcomm'
    have hzz : zM = z := by rw [← hc₂z, ← hc₁z, hcc]
    have hMt : R₂.map (D.hom i) ∈ twinSet Φ (R₁.map (D.hom i)) := ⟨hMΦ, z, hz, hzz ▸ hzM⟩
    exact (hall _ hMt).2.1 rfl
  · rintro ⟨hMΦ, hMi⟩
    refine ⟨hMΦ, fun K' hK' => ?_⟩
    have hK'i := twin_mem_compMembers hp D hi hJ hK'
    exact mem_omegaNbr_of_commutes hMΦ (fun h => hMi (h ▸ hK'i))
      (commutes_of_not_mem_compMembers D hMΦ hMi hK'i)

theorem vStar_eq_compMembers (hq : 5 ≤ p ^ f) (hΦ : HypOmegaMod p f Φ)
    (hi : D.tag i = .G2 ∨ D.tag i = .trialityD4) {K : Subgroup X} (hK : K ∈ compMembers D i) :
    vStar Φ K = compMembers D i := by
  ext J
  constructor
  · rintro ⟨hJΦ, heq⟩
    by_contra hJi
    have h1 : J ∈ omegaOfSet Φ (twinSet Φ K) :=
      (mem_omegaOfSet_twinSet_iff hp D hq hΦ hi hK).mpr ⟨hJΦ, hJi⟩
    rw [heq] at h1
    obtain ⟨z, hz⟩ := hΦ.exists_uniqueInvolution hp hq hJΦ
    exact (h1.2 J ⟨hJΦ, z, hz, hz⟩).2.1 rfl
  · intro hJ
    refine ⟨compMembers_subset D i hJ, ?_⟩
    ext M
    rw [mem_omegaOfSet_twinSet_iff hp D hq hΦ hi hK, mem_omegaOfSet_twinSet_iff hp D hq hΦ hi hJ]

end Component

end CFSG.ClassicalInvolution.Asc77.T3Typed
