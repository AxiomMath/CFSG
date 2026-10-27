module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S13

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup Wreath

section Diag

variable {G : Type} [Group G] [Finite G] {P K : Subgroup G} {t : G}

@[expose] def DiagForm {A : Type*} [Group A] (d : A) (w : Wr2 A) : Prop :=
  w = base d d ∨ w = base d d * tau

theorem DiagForm.unique {A : Type*} [Group A] {d f : A} {w : Wr2 A} (h : DiagForm d w)
    (h' : DiagForm f w) : d = f := by
  rcases h with h | h <;> rcases h' with h' | h'
  · exact (base_injective.1 (h.symm.trans h')).1
  · exact absurd (h.symm.trans h') (base_ne_base_mul_tau _ _ _ _)
  · exact absurd (h'.symm.trans h) (base_ne_base_mul_tau _ _ _ _)
  · exact (base_mul_tau_inj.1 (h.symm.trans h')).1

theorem DiagForm.mul {A : Type*} [Group A] {d e : A} {w w' : Wr2 A} (h : DiagForm d w)
    (h' : DiagForm e w') : DiagForm (d * e) (w * w') := by
  have hc : ∀ x : A, (tau : Wr2 A) * base x x = base x x * tau := fun x => by
    rw [tau_mul_base]
  rcases h with rfl | rfl <;> rcases h' with rfl | rfl
  · left; rw [base_mul_base]
  · right; rw [← mul_assoc, base_mul_base]
  · right
    rw [mul_assoc, hc, ← mul_assoc, base_mul_base]
  · left
    rw [mul_assoc, ← mul_assoc tau, hc, mul_assoc (base e e), tau_mul_tau, mul_one, base_mul_base]

theorem rho_diag_iso (pd : PairData P K t) (Ab J : Subgroup G)
    (hAbP : Ab ≤ P) (hAbt : ∀ x ∈ Ab, x * t = t * x) (hJAb : J ≤ Ab)
    (hJH : J ≤ K ⊔ conjSub t K)
    (hCJ : ∀ x ∈ Ab, (∀ j ∈ J, x * j = j * x) → x = 1)
    (hAb : Nat.card Ab = 1440) (hA : Nat.card (MulAut ↥K) ≤ 1440) :
    ∃ θ : ↥Ab ≃* MulAut ↥K, ∀ x : ↥Ab, DiagForm (θ x) (pd.rho ⟨x, hAbP x.2⟩) := by
  let φ : ↥Ab →* Wr2 (MulAut ↥K) := pd.rho.comp (Subgroup.inclusion hAbP)
  have hφ : ∀ x : ↥Ab, φ x = pd.rho ⟨x, hAbP x.2⟩ := fun x => rfl
  have htau : (tau : Wr2 (MulAut ↥K)) ≠ 1 := by
    intro h
    have := base_ne_base_mul_tau (1 : MulAut ↥K) 1 1 1
    rw [base_one, one_mul] at this
    exact this h.symm
  have hone : ∀ x : ↥Ab, φ x = 1 → x = 1 := by
    intro x hx
    have := commute_of_rho_eq_one pd hJH ⟨x, hAbP x.2⟩ hx
    have h1 : (x : G) = 1 := hCJ x x.2 (fun j hj => this j hj)
    exact Subtype.ext h1
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    exact hone
  have htauR : ∀ x : ↥Ab, φ x ≠ tau := by
    intro x hx
    let w : ↥P := ⟨(x : G) * t, mul_mem (hAbP x.2) pd.t_mem⟩
    have hw : pd.rho w = 1 := by
      have : w = ⟨x, hAbP x.2⟩ * ⟨t, pd.t_mem⟩ := rfl
      rw [this, map_mul, pd.rho_t, ← hφ, hx, tau_mul_tau]
    have hc := commute_of_rho_eq_one pd hJH w hw
    have hx1 : (x : G) = 1 := by
      refine hCJ x x.2 (fun j hj => ?_)
      have e := hc j hj
      have hjt := hAbt j (hJAb hj)
      show (x : G) * j = j * x
      apply mul_right_cancel (b := t)
      calc (x : G) * j * t = x * (j * t) := mul_assoc _ _ _
        _ = x * (t * j) := by rw [hjt]
        _ = x * t * j := (mul_assoc _ _ _).symm
        _ = j * (x * t) := e
        _ = j * x * t := (mul_assoc _ _ _).symm
    have : x = 1 := Subtype.ext hx1
    rw [this, map_one] at hx
    exact htau hx.symm
  have hRcard : Nat.card φ.range = 1440 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv, hAb]
  have hRc : φ.range ≤ centralizer ({tau} : Set (Wr2 (MulAut ↥K))) := by
    rintro _ ⟨x, rfl⟩
    rw [mem_centralizer_singleton_iff, ← pd.rho_t, hφ, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hAbt x x.2)
  have hτ : (tau : Wr2 (MulAut ↥K)) ∉ φ.range := by
    rintro ⟨x, hx⟩
    exact htauR x hx
  obtain ⟨hAeq, hcov⟩ := diag_cover hA φ.range hRcard hRc hτ
  have hex : ∀ x : ↥Ab, ∃ d : MulAut ↥K, DiagForm d (φ x) := by
    intro x
    have hxc : φ x ∈ centralizer ({tau} : Set (Wr2 (MulAut ↥K))) := hRc ⟨x, rfl⟩
    rcases eq_base_or_eq_base_mul_tau (φ x) with ⟨c, d, h⟩ | ⟨c, d, h⟩
    · rw [h] at hxc
      have := (mem_centralizer_tau_iff c d).1 hxc
      exact ⟨c, Or.inl (by rw [h, this])⟩
    · rw [h] at hxc
      have hτc : (tau : Wr2 (MulAut ↥K)) ∈ centralizer ({tau} : Set (Wr2 (MulAut ↥K))) :=
        mem_centralizer_singleton_iff.2 rfl
      have h2 : base c d ∈ centralizer ({tau} : Set (Wr2 (MulAut ↥K))) := by
        have := mul_mem hxc (inv_mem hτc)
        rwa [mul_assoc, mul_inv_cancel, mul_one] at this
      have := (mem_centralizer_tau_iff c d).1 h2
      exact ⟨c, Or.inr (by rw [h, this])⟩
  choose d hd using hex
  have hmul : ∀ x y : ↥Ab, d (x * y) = d x * d y := by
    intro x y
    have h1 : DiagForm (d x * d y) (φ (x * y)) := by
      rw [map_mul]
      exact (hd x).mul (hd y)
    exact (hd (x * y)).unique h1
  let θ0 : ↥Ab →* MulAut ↥K := MonoidHom.mk' d hmul
  have hθinj : Function.Injective θ0 := by
    intro x y hxy
    have hxy' : d x = d y := hxy
    have hdx := hd x
    have hdy := hd y
    rw [hxy'] at hdx
    by_cases hxe : φ x = φ y
    · exact hφinj hxe
    exfalso
    apply hτ
    rcases hdx with h1 | h1 <;> rcases hdy with h2 | h2
    · exact absurd (h1.trans h2.symm) hxe
    · refine ⟨x⁻¹ * y, ?_⟩
      rw [map_mul, map_inv, h1, h2, base_inv]
      rw [show base (d y)⁻¹ (d y)⁻¹ * (base (d y) (d y) * tau) = tau by
        rw [← mul_assoc, base_mul_base, inv_mul_cancel, base_one, one_mul]]
    · refine ⟨y⁻¹ * x, ?_⟩
      rw [map_mul, map_inv, h1, h2, base_inv]
      rw [show base (d y)⁻¹ (d y)⁻¹ * (base (d y) (d y) * tau) = tau by
        rw [← mul_assoc, base_mul_base, inv_mul_cancel, base_one, one_mul]]
    · exact absurd (h1.trans h2.symm) hxe
  have hθbij : Function.Bijective θ0 :=
    hθinj.bijective_of_nat_card_le (by rw [hAb, hAeq])
  exact ⟨MulEquiv.ofBijective θ0 hθbij, fun x => hd x⟩

end Diag

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
