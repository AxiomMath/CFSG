module

public import CFSG.ClassicalInvolution.Uniform.U9G2
public import CFSG.ClassicalInvolution.Q3.Q3WAM11Comp

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3KB

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
open scoped MatrixGroups


section Model

variable {X : Type} [Group X]

theorem range_le_of_pair_model {c : CompData} (ψ : c.G →* X)
    (hker : ψ.ker ≤ Subgroup.center c.G) {t : StatedLieTag} {n : ℕ} (hfund : IsFundTag t)
    (hadm : StatedLieAdmissible t n 3 1) (hc : c = CompData.model t n) {R₁ R₂ : Subgroup c.G}
    (hR₁ : R₁ ∈ c.fund) (hR₂ : R₂ ∈ c.fund) {ζ ξ : X} (hζ : ζ ∈ R₁.map ψ) (hξ : ξ ∈ R₂.map ψ)
    (hζ2 : ζ * ζ = 1) (hξ2 : ξ * ξ = 1) (hζ1 : ζ ≠ 1) (hξ1 : ξ ≠ 1) (hζξ : ζ ≠ ξ)
    (hζR₁ : ∀ y ∈ R₁.map ψ, ζ * y = y * ζ) (hξR₂ : ∀ y ∈ R₂.map ψ, ξ * y = y * ξ)
    (hζR₂ : ∀ y ∈ R₂.map ψ, ζ * y = y * ζ) (hξR₁ : ∀ y ∈ R₁.map ψ, ξ * y = y * ξ) :
    ψ.range ≤ (Subgroup.centralizer ({ζ} : Set X) ⊓ ψ.range) ⊔
      (Subgroup.centralizer ({ξ} : Set X) ⊓ ψ.range) ⊔
      (Subgroup.centralizer ({ζ * ξ} : Set X) ⊓ ψ.range) := by
  subst hc
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  by_cases hG : t = .G2 ∨ t = .trialityD4
  ·
    have hinj : Function.Injective ψ :=
      RouteD.G2D4.injective_of_ker_le_center (p := 3) (by norm_num) hG n le_rfl ψ hker
    obtain ⟨u₀, -, hu₀⟩ := id hζ
    obtain ⟨v₀, -, hv₀⟩ := id hξ
    have hu2 : u₀ * u₀ = 1 := hinj (by rw [map_mul, hu₀, map_one, hζ2])
    have hv2 : v₀ * v₀ = 1 := hinj (by rw [map_mul, hv₀, map_one, hξ2])
    have hu1 : u₀ ≠ 1 := fun h => hζ1 (by rw [← hu₀, h, map_one])
    have hv1 : v₀ ≠ 1 := fun h => hξ1 (by rw [← hv₀, h, map_one])
    have huv : u₀ ≠ v₀ := fun h => hζξ (by rw [← hu₀, ← hv₀, h])
    have hcomm : u₀ * v₀ = v₀ * u₀ :=
      hinj (by rw [map_mul, map_mul, hu₀, hv₀]; exact hζR₂ ξ hξ)
    have hpair : Subgroup.centralizer ({u₀} : Set (CompData.model t n).G) ⊔
        Subgroup.centralizer ({v₀} : Set (CompData.model t n).G) = ⊤ := by
      rcases hG with rfl | rfl
      · obtain ⟨hk, -⟩ := hadm.2.2
        subst hk
        exact Uniform.g2_pairGen3_proved u₀ v₀ hu2 hv2 hu1 hv1 huv hcomm
      · have hk : n = 0 := hadm.2.2
        subst hk
        exact G2D4Models.sup_centralizer_eq_top_model_td4 hp2 hadm hu2 hv2 hu1 hv1 huv hcomm
    have hle : ∀ (w : X) (u : (CompData.model t n).G), ψ u = w →
        (Subgroup.centralizer ({u} : Set (CompData.model t n).G)).map ψ ≤
          Subgroup.centralizer ({w} : Set X) ⊓ ψ.range := by
      intro w u hu y hy
      obtain ⟨g, hg, rfl⟩ := hy
      refine ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_, ⟨g, rfl⟩⟩
      rw [← hu, ← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.mp hg]
    calc ψ.range = (⊤ : Subgroup (CompData.model t n).G).map ψ := MonoidHom.range_eq_map ψ
      _ ≤ _ := by
        rw [← hpair, Subgroup.map_sup]
        exact sup_le (le_sup_of_le_left (le_sup_of_le_left (hle ζ u₀ hu₀)))
          (le_sup_of_le_left (le_sup_of_le_right (hle ξ v₀ hv₀)))
  ·
    push Not at hG
    obtain ⟨hG2, hD4⟩ := hG
    have hComm : ModelFacts.CommutingFundamentalGeneration 3 t n 1 := by
      by_cases hE : t = .twistedE6
      · subst hE
        exact ModelFacts.commutingFundamentalGeneration3_twistedE6 (by norm_num) hadm
      · exact ModelFacts.commutingFundamentalGeneration3_nonTwisted hG2 hD4 hE hfund hadm
    have hk3 : ∀ x ∈ ψ.ker, x ^ 3 = 1 → x = 1 := fun x hx hx3 =>
      CFSG.ComponentClassification.RankTwoOddLie.modelCenterPPrime t n 3 1 Nat.prime_three hp2
        hfund hadm x (hker hx) hx3
    have hG3 : ∀ R ∈ (CompData.model t n).fund, ModelFacts.Gen3 R := fun R hR =>
      ModelFacts.gen3_of_mem_longestFundamental3 (p := 3) (e := 1) (by norm_num) hfund hadm hG2
        hD4 (ModelFacts.fundamentalSubgroups_subset_longest hG2 hD4 _ hR)
    have key := ModelFacts.range_le_iSup_of_commutingPair3 ψ hker hk3 hG3 hComm hR₁ hR₂ hζ hξ
      hζR₁ hξR₂ hξR₁ hζR₂
    refine key.trans (iSup₂_le fun R hR => iSup_le fun hP => ?_)
    have hbound : ∀ w : X, (∀ y ∈ R.map ψ, w * y = y * w) →
        R.map ψ ≤ Subgroup.centralizer ({w} : Set X) ⊓ ψ.range := by
      intro w hw y hy
      exact ⟨Subgroup.mem_centralizer_singleton_iff.mpr (hw y hy).symm,
        Subgroup.map_le_range ψ R hy⟩
    rcases hP with h | h | h
    · exact le_sup_of_le_left (le_sup_of_le_left (hbound ζ h))
    · exact le_sup_of_le_left (le_sup_of_le_right (hbound ξ h))
    · exact le_sup_of_le_right (hbound (ζ * ξ) h)

theorem false_of_pair_m11 {c : CompData} (ψ : c.G →* X) (hker : ψ.ker ≤ Subgroup.center c.G)
    (hc : c = CompData.m11) {R₁ R₂ : Subgroup c.G} (hR₁ : R₁ ∈ c.fund) (hR₂ : R₂ ∈ c.fund)
    (hcomm : ∀ y ∈ R₁.map ψ, ∀ y' ∈ R₂.map ψ, y * y' = y' * y) : False := by
  subst hc
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker.trans (center_m11_eq_bot m11Facts).le
  refine Q3W.not_commutes_of_mem_m11Class hR₁ hR₂ ?_
  intro x hx y hy
  exact hinj (by
    rw [map_mul, map_mul]
    exact hcomm _ (Subgroup.mem_map_of_mem ψ hx) _ (Subgroup.mem_map_of_mem ψ hy))

end Model

section Lie

variable {X : Type} [Group X] {ι : Type} {Φ : Set (Subgroup X)}

theorem range_le_of_pair (D : LieSystemData3 ι X Φ) {k : ι} (hk : D.kind k ≠ CompData.sl23)
    {K J : Subgroup X} (hK : K ∈ Φ) (hJ : J ∈ Φ) {ζ ξ : X} (hζK : ζ ∈ K) (hξJ : ξ ∈ J)
    (hζ2 : ζ * ζ = 1) (hξ2 : ξ * ξ = 1) (hζ1 : ζ ≠ 1) (hξ1 : ξ ≠ 1) (hζξ : ζ ≠ ξ)
    (hKJ : ∀ y ∈ K, ∀ y' ∈ J, y * y' = y' * y) (hζK' : ∀ y ∈ K, ζ * y = y * ζ)
    (hξJ' : ∀ y ∈ J, ξ * y = y * ξ) (hζnc : ¬ ∀ q ∈ (D.hom k).range, ζ * q = q * ζ)
    (hξnc : ¬ ∀ q ∈ (D.hom k).range, ξ * q = q * ξ) :
    (D.hom k).range ≤ (Subgroup.centralizer ({ζ} : Set X) ⊓ (D.hom k).range) ⊔
      (Subgroup.centralizer ({ξ} : Set X) ⊓ (D.hom k).range) ⊔
      (Subgroup.centralizer ({ζ * ξ} : Set X) ⊓ (D.hom k).range) := by
  obtain ⟨i, R, hR, hKR⟩ := D.fundamental K hK
  obtain ⟨j, R', hR', hJR⟩ := D.fundamental J hJ
  have hcommc : ∀ {c d : ι}, c ≠ d → ∀ {a b : X}, a ∈ (D.hom c).range → b ∈ (D.hom d).range →
      a * b = b * a := by
    rintro c d h _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact D.commute c d h x y
  have hik : i = k := by
    by_contra h
    refine hζnc fun q hq => hcommc h ?_ hq
    rw [hKR] at hζK
    exact Subgroup.map_le_range _ _ hζK
  have hjk : j = k := by
    by_contra h
    refine hξnc fun q hq => hcommc h ?_ hq
    rw [hJR] at hξJ
    exact Subgroup.map_le_range _ _ hξJ
  subst hik
  subst hjk
  subst hKR
  subst hJR
  rcases D.valid j with ⟨t, n, hfund, hadm, hc⟩ | hc | hc
  · exact range_le_of_pair_model (D.hom j) (D.ker_le_center j) hfund hadm hc hR hR' hζK hξJ hζ2
      hξ2 hζ1 hξ1 hζξ hζK' hξJ' (fun y hy => hKJ ζ hζK y hy) (fun y hy => (hKJ y hy ξ hξJ).symm)
  · exact absurd hc hk
  · exact (false_of_pair_m11 (D.hom j) (D.ker_le_center j) hc hR hR' hKJ).elim

end Lie

end CFSG.ClassicalInvolution.Q3.Q3KB
