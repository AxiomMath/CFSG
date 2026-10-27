module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L128SplB

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

namespace Sec128Spl

variable {M : Type} [Group M] {ρ : Sec128A5 × Sec128A5 →* MulAut M} {V1 V2 : Subgroup M}
  {φ1 φ2 : (Fin 5 → ZMod 2) → M}

theorem equiv_comap (h : Sec128Spl ρ V1 V2 φ1 φ2) {Xt : Subgroup (MulAut M)}
    (hXt : ∀ x ∈ Xt, ∃ p, ρ p = x) : Nonempty (↥(Xt.comap ρ) ≃* ↥Xt) := by
  let f : ↥(Xt.comap ρ) →* ↥Xt := (ρ.comp (Xt.comap ρ).subtype).codRestrict Xt fun d => d.2
  have hinj : Function.Injective f := by
    intro d d' hdd
    exact Subtype.ext (h.inj (congrArg Subtype.val hdd))
  have hsurj : Function.Surjective f := by
    rintro ⟨x, hx⟩
    obtain ⟨p, rfl⟩ := hXt x hx
    exact ⟨⟨p, hx⟩, rfl⟩
  exact ⟨MulEquiv.ofBijective f ⟨hinj, hsurj⟩⟩

theorem swap (h : Sec128Spl ρ V1 V2 φ1 φ2) {τ : MulAut M} (hτ1 : τ ≠ 1)
    (hZn : ∀ p, ∃ p', τ * ρ p * τ⁻¹ = ρ p') {Xt : Subgroup (MulAut M)}
    (hXt : ∀ x ∈ Xt, ∃ p, ρ p = x) (hXA : Nonempty (↥Xt ≃* Sec128A5))
    (hXc : ∀ x ∈ Xt, τ * x = x * τ) (hfix : ∀ u : M, (∀ x ∈ Xt, x u = u) → u = 1) :
    (∀ a, ∃ b, τ * ρ (a, 1) * τ⁻¹ = ρ (1, b)) ∧ (∀ b, ∃ a, τ * ρ (1, b) * τ⁻¹ = ρ (a, 1)) ∧
      ∀ p, τ ≠ ρ p := by
  classical
  obtain ⟨eD⟩ := h.equiv_comap hXt
  let D : Subgroup (Sec128A5 × Sec128A5) := Xt.comap ρ
  have hDA : Nonempty (↥D ≃* Sec128A5) := hXA.map fun e => eD.trans e
  have hne2 : ∃ d ∈ D, d.2 ≠ 1 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨u, hu, hu1⟩ := h.exists_ne_one2
    apply hu1
    refine hfix u fun x hx => ?_
    obtain ⟨p, rfl⟩ := hXt x hx
    have hp2 : p.2 = 1 := hcon p hx
    have hpe : p = (p.1, 1) := Prod.ext rfl hp2
    rw [hpe]
    exact h.fixed1 hu p.1
  have hne1 : ∃ d ∈ D, d.1 ≠ 1 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨u, hu, hu1⟩ := h.exists_ne_one1
    apply hu1
    refine hfix u fun x hx => ?_
    obtain ⟨p, rfl⟩ := hXt x hx
    have hp1 : p.1 = 1 := hcon p hx
    have hpe : p = (1, p.2) := Prod.ext hp1 rfl
    rw [hpe]
    exact h.fixed2 hu p.2
  have hD2 := sec128_proj2_onto hDA hne2
  have hD1 := sec128_proj1_onto hDA hne1
  choose κf hκf using hZn
  have hκ1 : κf 1 = 1 := by
    apply h.inj
    rw [← hκf 1, map_one]
    group
  have hκm : ∀ p q, κf (p * q) = κf p * κf q := by
    intro p q
    apply h.inj
    calc ρ (κf (p * q)) = τ * ρ (p * q) * τ⁻¹ := (hκf _).symm
      _ = (τ * ρ p * τ⁻¹) * (τ * ρ q * τ⁻¹) := by rw [map_mul]; group
      _ = ρ (κf p) * ρ (κf q) := by rw [hκf, hκf]
      _ = ρ (κf p * κf q) := (map_mul ρ _ _).symm
  let κ : Sec128A5 × Sec128A5 →* Sec128A5 × Sec128A5 :=
    { toFun := κf, map_one' := hκ1, map_mul' := hκm }
  have hκinj : Function.Injective κ := by
    intro p q hpq
    have h1 : ρ (κf p) = ρ (κf q) := congrArg ρ hpq
    rw [← hκf, ← hκf] at h1
    apply h.inj
    have h2 : τ * ρ p = τ * ρ q := mul_right_cancel h1
    exact mul_left_cancel h2
  have hκD : ∀ d ∈ D, κ d = d := by
    intro d hd
    apply h.inj
    show ρ (κf d) = ρ d
    rw [← hκf, hXc _ hd]
    group
  rcases sec128_aut_dich κ hκinj D hD1 hD2 hκD with hid | ⟨hsw1, hsw2⟩
  · exfalso
    apply hτ1
    refine h.cent_one fun p => ?_
    have h1 : τ * ρ p * τ⁻¹ = ρ p := by
      rw [hκf p]
      exact congrArg ρ (hid p)
    calc τ * ρ p = (τ * ρ p * τ⁻¹) * τ := by group
      _ = ρ p * τ := by rw [h1]
  · refine ⟨fun a => ⟨(κf (a, 1)).2, ?_⟩, fun b => ⟨(κf (1, b)).1, ?_⟩, ?_⟩
    · rw [hκf (a, 1)]
      exact congrArg ρ (Prod.ext (hsw1 a) rfl)
    · rw [hκf (1, b)]
      exact congrArg ρ (Prod.ext rfl (hsw2 b))
    · intro p hp
      have hcomm : ∀ d ∈ D, p * d = d * p := by
        intro d hd
        apply h.inj
        rw [map_mul, map_mul, ← hp]
        exact hXc _ hd
      have hp1 : p.1 = 1 := by
        refine sec128_A5_central fun a => ?_
        obtain ⟨b, hb⟩ := hD1 a
        exact congrArg Prod.fst (hcomm _ hb)
      have hp2 : p.2 = 1 := by
        refine sec128_A5_central fun b => ?_
        obtain ⟨a, ha⟩ := hD2 b
        exact congrArg Prod.snd (hcomm _ ha)
      apply hτ1
      rw [hp, show p = 1 from Prod.ext hp1 hp2, map_one]

theorem swap_sub (h : Sec128Spl ρ V1 V2 φ1 φ2) {τ : MulAut M} (hτ2 : τ * τ = 1)
    (hA : ∀ a, ∃ b, τ * ρ (a, 1) * τ⁻¹ = ρ (1, b))
    (hB : ∀ b, ∃ a, τ * ρ (1, b) * τ⁻¹ = ρ (a, 1)) :
    V1.map (τ : M ≃* M).toMonoidHom = V2 := by
  have hτinv : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right hτ2
  have hττ : ∀ u, τ (τ u) = u := fun u => congrArg (fun f : MulAut M => f u) hτ2
  have hconj : ∀ X : MulAut M, τ * (τ * X * τ) * τ = X := fun X => by
    rw [show τ * (τ * X * τ) * τ = (τ * τ) * X * (τ * τ) by group, hτ2]
    group
  have hto : ∀ u ∈ V1, τ u ∈ V2 := by
    intro u hu
    refine h.fix1 fun a => ?_
    obtain ⟨b, hb⟩ := hA a
    rw [hτinv] at hb
    have h1 : ρ (a, 1) = τ * ρ (1, b) * τ := by rw [← hb, hconj]
    rw [h1]
    show τ (ρ (1, b) (τ (τ u))) = τ u
    rw [hττ, h.fixed2 hu b]
  have hto' : ∀ u ∈ V2, τ u ∈ V1 := by
    intro u hu
    refine h.fix2 fun b => ?_
    obtain ⟨a, ha⟩ := hB b
    rw [hτinv] at ha
    have h1 : ρ (1, b) = τ * ρ (a, 1) * τ := by rw [← ha, hconj]
    rw [h1]
    show τ (ρ (a, 1) (τ (τ u))) = τ u
    rw [hττ, h.fixed1 hu a]
  ext w
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact hto u hu
  · intro hw
    exact ⟨τ w, hto' w hw, hττ w⟩

end Sec128Spl

end CFSG.OddStandard.SmallF3.Omega
