module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.Swap.Structure

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Swap

open Module CFSG.EvenSporadicStandard.HNRecog.Fpf

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
variable {σ : A5 × A5 →* (V ≃ₗ[ZMod 2] V)} {c : ℕ} {Fp Fm : Submodule (ZMod 2) V}

private lemma pow_fst (n : ℕ) :
    σ (a₀, 1) ^ n = σ (a₀ ^ n, 1) := by
  have h1 : (a₀, (1 : A5)) ^ n = (a₀ ^ n, 1) := by
    rw [Prod.pow_mk, one_pow]
  rw [← h1, map_pow]

private lemma pow_mem_fm (hE : EigenData σ c Fp Fm) (m : ℕ) :
    ∀ v ∈ Fm, ((σ (a₀, 1)) ^ m) v ∈ Fm := by
  induction m with
  | zero =>
      intro v hv
      simpa using hv
  | succ m ih =>
      intro v hv
      rw [pow_succ', LinearEquiv.mul_apply]
      exact hE.alpha_mem.2 _ (ih v hv)

theorem EigenData.bilin_plus_minus (hS : StdHyp σ) (hE : EigenData σ c Fp Fm)
    (B : LinearMap.BilinForm (ZMod 2) V) (hBσ : ∀ g x y, B (σ g x) (σ g y) = B x y) :
    ∀ x ∈ Fp, ∀ y ∈ Fm, B x y = 0 := by
  intro x hx y hy
  have ha5 : a₀ ^ 5 = 1 := by
    simpa only [orderOf_a₀] using pow_orderOf_eq_one a₀
  have hα5 : (σ (a₀, 1)) ^ 5 = 1 := by
    rw [pow_fst 5, ha5]
    exact map_one σ
  have hn : ¬ 5 ∣ 10 - 2 * c := by
    rintro ⟨k, hk⟩
    have h1 : 1 ≤ c := hE.one_le
    have h4 : c ≤ 4 := hE.le_four
    omega
  have hstep : ∀ y ∈ Fm, B x y = B x (((σ (a₀, 1)) ^ (10 - 2 * c)) y) := by
    intro y hy
    have e1 : B x y = B (((σ (a₀, 1)) ^ c) x) (((σ (a₀, 1)) ^ (5 - c)) y) := by
      rw [(hBσ (1, a₀) x y).symm, hE.beta_eq.1 x hx, hE.beta_eq.2 y hy]
    have e2 : B (((σ (a₀, 1)) ^ c) x) (((σ (a₀, 1)) ^ (5 - c)) y)
        = B x (((σ (a₀, 1)) ^ (10 - 2 * c)) y) := by
      have hg := (hBσ (a₀ ^ (5 - c), 1)
        (((σ (a₀, 1)) ^ c) x) (((σ (a₀, 1)) ^ (5 - c)) y)).symm
      rw [hg, ← pow_fst (5 - c)]
      have hc1 : 5 - c + c = 5 := by omega
      have harg1 : ((σ (a₀, 1)) ^ (5 - c)) (((σ (a₀, 1)) ^ c) x) = x := by
        rw [← LinearEquiv.mul_apply, ← pow_add, hc1, hα5]
        simp
      have hc2 : 5 - c + (5 - c) = 10 - 2 * c := by omega
      have harg2 : ((σ (a₀, 1)) ^ (5 - c)) (((σ (a₀, 1)) ^ (5 - c)) y)
          = ((σ (a₀, 1)) ^ (10 - 2 * c)) y := by
        rw [← LinearEquiv.mul_apply, ← pow_add, hc2]
      rw [harg1, harg2]
    rw [e1, e2]
  haveI : FiniteDimensional (ZMod 2) V :=
    FiniteDimensional.of_finrank_pos (by rw [hS.finrank_eq]; norm_num)
  let g : Fm →ₗ[ZMod 2] Fm :=
    ((((σ (a₀ ^ (10 - 2 * c), 1) : V →ₗ[ZMod 2] V)).comp Fm.subtype)).codRestrict Fm
      (fun v => by
        have hv := pow_mem_fm hE (10 - 2 * c) (v : V) v.2
        simpa [pow_fst] using hv)
  let h : Fm →ₗ[ZMod 2] Fm := g - LinearMap.id
  have hinj : Function.Injective h := by
    intro y y' hyy'
    have h1 : h (y - y') = 0 := by rw [map_sub, hyy', sub_self]
    have hcoe : ((h (y - y') : Fm) : V) = 0 := by rw [h1]; rfl
    have hzV : σ (a₀ ^ (10 - 2 * c), 1) ((y - y' : Fm) : V) = ((y - y' : Fm) : V) := by
      have hsub : σ (a₀ ^ (10 - 2 * c), 1) ((y - y' : Fm) : V)
          - ((y - y' : Fm) : V) = 0 := by
        simpa [h, g, LinearMap.codRestrict_apply] using hcoe
      exact sub_eq_zero.mp hsub
    have hz0 : ((y - y' : Fm) : V) = 0 :=
      hS.fixedFree_left_pow hn ((y - y' : Fm) : V) hzV
    exact sub_eq_zero.mp (Subtype.ext hz0)
  have hsurj : Function.Surjective h := LinearMap.injective_iff_surjective.mp hinj
  obtain ⟨y0, hy0⟩ := hsurj ⟨y, hy⟩
  have hy0V : σ (a₀ ^ (10 - 2 * c), 1) (y0 : V) - (y0 : V) = (y : V) := by
    have hcoe : ((h y0 : Fm) : V) = (y : V) := by rw [hy0]
    simpa [h, g, LinearMap.codRestrict_apply] using hcoe
  calc
    B x y = B x (σ (a₀ ^ (10 - 2 * c), 1) (y0 : V) - (y0 : V)) := by rw [← hy0V]
    _ = B x (σ (a₀ ^ (10 - 2 * c), 1) (y0 : V)) - B x (y0 : V) := by rw [map_sub]
    _ = 0 := by
      rw [← pow_fst (10 - 2 * c), hstep y0 y0.2, sub_self]

theorem EigenData.bilin_minus_plus (hS : StdHyp σ) (hE : EigenData σ c Fp Fm)
    (B : LinearMap.BilinForm (ZMod 2) V) (hBσ : ∀ g x y, B (σ g x) (σ g y) = B x y) :
    ∀ x ∈ Fm, ∀ y ∈ Fp, B x y = 0 := by
  intro x hx y hy
  have hflip : ∀ g x y, B.flip (σ g x) (σ g y) = B.flip x y := by
    intro g u v
    simp only [LinearMap.BilinForm.flip_apply]
    exact hBσ g v u
  have := EigenData.bilin_plus_minus hS hE B.flip hflip y hy x hx
  simpa only [LinearMap.BilinForm.flip_apply] using this

theorem EigenData.bilin_right_nondegenerate_plus (hS : StdHyp σ) (hE : EigenData σ c Fp Fm)
    (B : LinearMap.BilinForm (ZMod 2) V) (hB : B.Nondegenerate)
    (hBσ : ∀ g x y, B (σ g x) (σ g y) = B x y) :
    ∀ y ∈ Fp, (∀ x ∈ Fp, B x y = 0) → y = 0 := by
  intro y hy horth
  apply hB.2 y
  intro v
  have hv : v ∈ Fp ⊔ Fm := by rw [hE.isCompl.sup_eq_top]; trivial
  obtain ⟨p, hp, m, hm, hpm⟩ := Submodule.mem_sup.mp hv
  rw [← hpm]
  have hadd : B (p + m) y = B p y + B m y := by
    rw [map_add, LinearMap.add_apply]
  rw [hadd, horth p hp,
    EigenData.bilin_minus_plus hS hE B hBσ m hm y hy, add_zero]

end CFSG.EvenSporadicStandard.HNRecog.Swap