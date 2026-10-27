module

public import CFSG.ClassicalInvolution.AschTight.S19GCore

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.NDB.G2S

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Disconnected.AschTight.S19G

theorem fg0Model_of_tag {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {t : StatedLieTag} {n e : ℕ}
    (he : 1 ≤ e) (ht : t = .G2 ∨ t = .trialityD4)
    {R : Subgroup (modelUniv t n p e Fact.out).K}
    (hR : R ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D) : FG0Model R := by
  rcases ht with rfl | rfl
  · exact fg0Model_g2 hp2 he hR
  · exact fg0Model_d4 hp2 he hR

theorem eq_of_card_dvd_two {Z : Type*} [Group Z] [Finite Z] (h : Nat.card Z ∣ 2) {x y : Z}
    (hx : x ≠ 1) (hy : y ≠ 1) : x = y := by
  by_contra hxy
  have : Fintype Z := Fintype.ofFinite Z
  classical
  have h3 : ({1, x, y} : Finset Z).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair hxy]
    simp [Ne.symm hx, Ne.symm hy]
  have h4 : ({1, x, y} : Finset Z).card ≤ Nat.card Z := by
    rw [Nat.card_eq_fintype_card]
    exact Finset.card_le_univ _
  have := Nat.le_of_dvd (by norm_num) h
  omega

theorem dichotomy_of_fg0 {K X : Type} [Group K] [Group X] [Finite X] (ψ : K →* X)
    (hψ : Function.Injective ψ) (hZ : ∀ g : K, (∀ x : K, g * x = x * g) → g = 1)
    {R : Subgroup K} (hR : FG0Model R) {r : K}
    (hZR : ∀ g ∈ R, (∀ y ∈ R, g * y = y * g) → g * g = 1 → g = 1 ∨ g = r)
    (φ : MulAut X) (hφ2 : ∀ x, φ (φ x) = x) (hφQ : ∀ g : K, ∃ g' : K, ψ g' = φ (ψ g))
    (hfix : ∀ y ∈ R, φ (ψ y) = ψ y) :
    (∀ g : K, φ (ψ g) = ψ g) ∨ (∀ g : K, φ (ψ g) = ψ r * ψ g * (ψ r)⁻¹) := by
  classical
  have : Finite K := Finite.of_injective ψ hψ
  choose α hα using hφQ
  have hαmul : ∀ g h, α (g * h) = α g * α h := fun g h => hψ (by simp only [hα, map_mul])
  have hα1 : α 1 = 1 := hψ (by simp [hα])
  let α₀ : K →* K := { toFun := α, map_one' := hα1, map_mul' := hαmul }
  have hαinj : Function.Injective α₀ := fun g h hgh => hψ (by
    have h1 : ψ (α g) = ψ (α h) := congrArg ψ hgh
    rw [hα, hα] at h1
    exact φ.injective h1)
  have hαbij : Function.Bijective α₀ := Finite.injective_iff_bijective.mp hαinj
  let αe : MulAut K := MulEquiv.ofBijective α₀ hαbij
  have hαe : ∀ g, αe g = α g := fun g => rfl
  have hαα : ∀ g, α (α g) = g := fun g => hψ (by rw [hα, hα, hφ2])
  have hfixR : ∀ x ∈ R, αe x = x := fun x hx => hψ (by rw [hαe, hα]; exact hfix x hx)
  have hsq : ∃ n : ℕ, αe ^ (2 ^ n) = 1 := ⟨1, by
    ext g
    simp only [pow_one, pow_two, MulAut.mul_apply, MulAut.one_apply, hαe]
    exact hαα g⟩
  obtain ⟨g, hg⟩ := hR.2.2 αe hsq hfixR
  have hgx : ∀ x, α x = g * x * g⁻¹ := fun x => by
    have := DFunLike.congr_fun hg x
    rw [hαe, MulAut.conj_apply] at this
    exact this
  have hgc : ∀ y ∈ R, g * y = y * g := fun y hy => by
    have h1 := hfixR y hy
    rw [hαe, hgx] at h1
    calc g * y = g * y * g⁻¹ * g := by group
      _ = y * g := by rw [h1]
  have hgg : g * g = 1 := by
    refine hZ (g * g) fun x => ?_
    have h1 := hαα x
    rw [hgx, hgx] at h1
    calc g * g * x = g * (g * x * g⁻¹) * g⁻¹ * (g * g) := by group
      _ = x * (g * g) := by rw [h1]
  have hgcent : g ∈ Subgroup.centralizer (R : Set K) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact (hgc h hh).symm
  rcases hR.1 g hgcent hgg with h1 | h1
  · left
    intro x
    rw [← hα, hgx, h1]
    simp
  · rcases hZR g h1 hgc hgg with h2 | h2
    · left
      intro x
      rw [← hα, hgx, h2]
      simp
    · right
      intro x
      rw [← hα, hgx, h2, map_mul, map_mul, map_inv]

end CFSG.ClassicalInvolution.NDB.G2S
