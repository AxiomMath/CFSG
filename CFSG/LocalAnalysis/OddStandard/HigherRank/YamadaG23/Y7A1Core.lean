module

public import Mathlib.Tactic.Group
public import Mathlib.Algebra.Group.Subgroup.Defs

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

variable {G : Type} [Group G]

private lemma y7a_aux {H : Type*} [Group H] [IsMulCommutative H] (a b c : H)
    (ha : a * a = 1) (hb : b * b = 1) (hc : c * c = 1) :
    (a * b * c) * (b * a⁻¹) * (c * a⁻¹) = a := by
  rw [inv_eq_of_mul_eq_one_right ha]
  calc (a * b * c) * (b * a) * (c * a)
      = (b * b) * (c * c) * (a * a) * a := by ac_rfl
    _ = a := by rw [hb, hc, ha]; simp

private lemma y7a_cancel {H : Type*} [Group H] [IsMulCommutative H] (a b c e : H)
    (h : a * b * c = e) : a⁻¹ * b⁻¹ * c⁻¹ * e = 1 := by
  rw [← h]
  calc a⁻¹ * b⁻¹ * c⁻¹ * (a * b * c)
      = (a * a⁻¹) * (b * b⁻¹) * (c * c⁻¹) := by ac_rfl
    _ = 1 := by simp

theorem y7a_core {W D F Z : Subgroup G} {φ : G → G} {k d : G} (hk3 : k ^ 3 = 1)
    (hW : ∀ w ∈ W, k * w * k⁻¹ ∈ W) (hD : ∀ w ∈ D, k * w * k⁻¹ ∈ D)
    (hφF : ∀ w ∈ W, φ w ∈ F) (hφmul : ∀ w ∈ W, ∀ w' ∈ W, φ (w * w') = φ w * φ w')
    (hφk : ∀ w, φ (k * w * k⁻¹) = k * φ w * k⁻¹)
    (hFsq : ∀ f ∈ F, f ^ 2 = 1) (hFcomm : ∀ f ∈ F, ∀ f' ∈ F, f * f' = f' * f)
    (hkF : ∀ f ∈ F, k * f * k⁻¹ ∈ F) (hfpf : ∀ f ∈ F, k * f * k⁻¹ * f⁻¹ ∈ Z → f ∈ Z)
    (hZ : ∀ x ∈ Z, x = 1 ∨ x = φ d) (hdD : d ∈ D) (hdW : d ∈ W)
    (hker : ∀ w ∈ W, φ w = 1 → w ∈ D) (hcomm : ∀ w ∈ W, k * w * k⁻¹ * w⁻¹ ∈ D) :
    W ≤ D := by
  intro w hw
  have h1W : (1 : G) ∈ W := W.one_mem
  have hphi1 : φ 1 = 1 := by
    have h : φ 1 = φ 1 * φ 1 := by simpa using hφmul 1 h1W 1 h1W
    exact (mul_left_cancel (a := φ 1) (by rw [mul_one]; exact h)).symm
  have hphiinv : ∀ x ∈ W, φ x⁻¹ = (φ x)⁻¹ := by
    intro x hx
    have h : φ x * φ x⁻¹ = 1 := by
      have hh := hφmul x hx x⁻¹ (W.inv_mem hx)
      rw [mul_inv_cancel, hphi1] at hh
      exact hh.symm
    exact eq_inv_of_mul_eq_one_right h
  let f : G := φ w
  have hfF : f ∈ F := hφF w hw
  have hfinv : f⁻¹ = f := by
    have h2 : f * f = 1 := by simpa [pow_two] using hFsq f hfF
    exact inv_eq_of_mul_eq_one_right h2
  let b : G := k * f * k⁻¹
  have hbF : b ∈ F := hkF f hfF
  let c : G := k * b * k⁻¹
  have hcF : c ∈ F := hkF b hbF
  let w₁ : G := k * w * k⁻¹ * w⁻¹
  let w₂ : G := (k * w₁ * k⁻¹) * w₁
  have hw1W : w₁ ∈ W := W.mul_mem (hW w hw) (W.inv_mem hw)
  have hw1D : w₁ ∈ D := hcomm w hw
  have hw2W : w₂ ∈ W := W.mul_mem (hW w₁ hw1W) hw1W
  have hw2D : w₂ ∈ D := D.mul_mem (hD w₁ hw1D) hw1D
  have hφw1 : φ w₁ = b * f⁻¹ := by
    have h := hφmul (k * w * k⁻¹) (hW w hw) w⁻¹ (W.inv_mem hw)
    rw [hφk w, hphiinv w hw] at h
    change φ (k * w * k⁻¹ * w⁻¹) = (k * f * k⁻¹) * f⁻¹
    exact h
  have hb2 : b * b = 1 := by simpa [pow_two] using hFsq b hbF
  have hφw2 : φ w₂ = c * f⁻¹ := by
    have h := hφmul (k * w₁ * k⁻¹) (hW w₁ hw1W) w₁ hw1W
    rw [hφk w₁, hφw1] at h
    have hkb : k * (b * f⁻¹) * k⁻¹ = c * b := by
      calc k * (b * f⁻¹) * k⁻¹
          = (k * b * k⁻¹) * (k * f⁻¹ * k⁻¹) := by group
        _ = c * (k * f * k⁻¹) := by rw [hfinv]
        _ = c * b := rfl
    rw [hkb] at h
    have hcb : (c * b) * (b * f⁻¹) = c * f⁻¹ := by
      calc (c * b) * (b * f⁻¹) = c * (b * b) * f⁻¹ := by group
        _ = c * f⁻¹ := by rw [hb2]; group
    rw [hcb] at h
    change φ ((k * w₁ * k⁻¹) * w₁) = c * f⁻¹
    exact h
  let n : G := f * b * c
  have hnF : n ∈ F := F.mul_mem (F.mul_mem hfF hbF) hcF
  haveI : IsMulCommutative F :=
    IsMulCommutative.of_comm (fun x y => Subtype.ext (hFcomm x x.2 y y.2))
  let fF : F := ⟨f, hfF⟩
  let bF : F := ⟨b, hbF⟩
  let cF : F := ⟨c, hcF⟩
  have hfF2 : fF * fF = 1 := Subtype.ext (by simpa [fF, pow_two] using hFsq f hfF)
  have hbF2 : bF * bF = 1 := Subtype.ext (by simpa [bF, pow_two] using hFsq b hbF)
  have hcF2 : cF * cF = 1 := Subtype.ext (by simpa [cF, pow_two] using hFsq c hcF)
  have hmainF : (fF * bF * cF) * (bF * fF⁻¹) * (cF * fF⁻¹) = fF :=
    y7a_aux fF bF cF hfF2 hbF2 hcF2
  have hnf : n * φ w₁ * φ w₂ = f := by
    have h := congrArg (fun x : F => (x : G)) hmainF
    rw [show n = f * b * c from rfl, hφw1, hφw2]
    simpa [fF, bF, cF] using h
  have hk3' : (k⁻¹) ^ 3 = 1 := by rw [inv_pow, hk3, inv_one]
  have hkn : k * n * k⁻¹ = n := by
    have hk3'' : k * k * k = 1 := by rw [← pow_two, ← pow_succ, hk3]
    have hk3inv : k⁻¹ * k⁻¹ * k⁻¹ = 1 := by
      rw [← pow_two, ← pow_succ]
      exact hk3'
    have hkc : k * c * k⁻¹ = f := by
      change k * (k * (k * f * k⁻¹) * k⁻¹) * k⁻¹ = f
      calc k * (k * (k * f * k⁻¹) * k⁻¹) * k⁻¹
          = (k * k * k) * f * (k⁻¹ * k⁻¹ * k⁻¹) := by group
        _ = f := by rw [hk3'', hk3inv, one_mul, mul_one]
    have hbc : b * c * f = f * b * c := by
      calc b * c * f = (b * c) * f := rfl
        _ = f * (b * c) := hFcomm (b * c) (F.mul_mem hbF hcF) f hfF
        _ = f * b * c := (mul_assoc f b c).symm
    calc k * n * k⁻¹
        = (k * f * k⁻¹) * (k * b * k⁻¹) * (k * c * k⁻¹) := by
            change k * (f * b * c) * k⁻¹ = (k * f * k⁻¹) * (k * b * k⁻¹) * (k * c * k⁻¹)
            group
      _ = b * c * f := by rw [hkc]
      _ = f * b * c := hbc
      _ = n := rfl
  have hnZ : n ∈ Z := hfpf n hnF (by rw [hkn, mul_inv_cancel]; exact Z.one_mem)
  obtain ⟨w₀, hw0D, hw0W, hφw0⟩ : ∃ w₀ : G, w₀ ∈ D ∧ w₀ ∈ W ∧ φ w₀ = n := by
    rcases hZ n hnZ with h1 | h1
    · exact ⟨1, D.one_mem, W.one_mem, by rw [hphi1, h1]⟩
    · exact ⟨d, hdD, hdW, by rw [h1]⟩
  let u : G := w₀⁻¹ * w₁⁻¹ * w₂⁻¹ * w
  have huW : u ∈ W :=
    W.mul_mem (W.mul_mem (W.mul_mem (W.inv_mem hw0W) (W.inv_mem hw1W))
      (W.inv_mem hw2W)) hw
  have h01 : φ (w₀⁻¹ * w₁⁻¹) = (φ w₀)⁻¹ * (φ w₁)⁻¹ := by
    have h := hφmul w₀⁻¹ (W.inv_mem hw0W) w₁⁻¹ (W.inv_mem hw1W)
    rw [hphiinv w₀ hw0W, hphiinv w₁ hw1W] at h
    exact h
  have h012 : φ (w₀⁻¹ * w₁⁻¹ * w₂⁻¹) = (φ w₀)⁻¹ * (φ w₁)⁻¹ * (φ w₂)⁻¹ := by
    have h := hφmul (w₀⁻¹ * w₁⁻¹)
      (W.mul_mem (W.inv_mem hw0W) (W.inv_mem hw1W)) w₂⁻¹ (W.inv_mem hw2W)
    rw [h01, hphiinv w₂ hw2W] at h
    exact h
  have hu : φ u = (φ w₀)⁻¹ * (φ w₁)⁻¹ * (φ w₂)⁻¹ * f := by
    have h := hφmul (w₀⁻¹ * w₁⁻¹ * w₂⁻¹)
      (W.mul_mem (W.mul_mem (W.inv_mem hw0W) (W.inv_mem hw1W)) (W.inv_mem hw2W)) w hw
    rw [h012] at h
    change φ ((w₀⁻¹ * w₁⁻¹ * w₂⁻¹) * w) = (φ w₀)⁻¹ * (φ w₁)⁻¹ * (φ w₂)⁻¹ * f
    exact h
  let nF : F := ⟨n, hnF⟩
  let p1F : F := ⟨φ w₁, hφF w₁ hw1W⟩
  let p2F : F := ⟨φ w₂, hφF w₂ hw2W⟩
  have hnfF : nF * p1F * p2F = fF := Subtype.ext (by simpa [nF, p1F, p2F, fF] using hnf)
  have hucF : nF⁻¹ * p1F⁻¹ * p2F⁻¹ * fF = 1 := y7a_cancel nF p1F p2F fF hnfF
  have hφu : φ u = 1 := by
    have h := congrArg (fun x : F => (x : G)) hucF
    rw [hu, hφw0]
    simpa [nF, p1F, p2F, fF] using h
  have huD : u ∈ D := hker u huW hφu
  have hw_eq : w = w₂ * w₁ * w₀ * u := by
    rw [show u = w₀⁻¹ * w₁⁻¹ * w₂⁻¹ * w from rfl]
    group
  rw [hw_eq]
  exact D.mul_mem (D.mul_mem (D.mul_mem hw2D hw1D) hw0D) huD

end CFSG.OddStandard.HigherRank.YamadaG23