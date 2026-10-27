module

public import CFSG.CGT.PushingUpLit.BHS.ThreeFiveB

public section

namespace CFSG.CGT.PushingUpLit.BHS

open CFSG.Quasithin CFSG.CGT.PushingUpLit.BHS.Glauberman

local macro "comm_group" : tactic =>
  `(tactic| (apply Additive.ofMul.injective
             simp only [ofMul_mul, ofMul_inv, ofMul_div, ofMul_one]
             abel))

variable {V : Type} [CommGroup V] {Γ : Type} [Group Γ]

theorem mem_fixV_of_mod_fixV (ρ : Γ →* MulAut V) {A₁ B₁ : Subgroup Γ} (hgen : A₁ ⊔ B₁ = ⊤)
    (hconj : ∃ y : Γ, A₁ = B₁.map (MulAut.conj y).toMonoidHom) {w : V}
    (hA : ∀ a ∈ A₁, ρ a w * w⁻¹ ∈ fixV ρ.range) (hB : ∀ b ∈ B₁, ρ b w = w) :
    w ∈ fixV ρ.range := by
  set Y := fixV ρ.range with hY
  have hYfix : ∀ (g : Γ), ∀ y ∈ Y, ρ g y = y := fun g y hy => hy _ ⟨g, rfl⟩
  set c : Γ → V := fun g => ρ g w * w⁻¹ with hc
  have hcg : ∀ g : Γ, ρ g w = c g * w := fun g => by simp [hc]
  have hmul : ∀ g h : Γ, c h ∈ Y → c (g * h) = c h * c g := by
    intro g h hh
    have : ρ (g * h) w = ρ g (c h * w) := by rw [map_mul, MulAut.mul_apply, hcg h]
    show ρ (g * h) w * w⁻¹ = c h * (ρ g w * w⁻¹)
    rw [this, map_mul, hYfix g _ hh, hcg g]
    comm_group
  have hinv : ∀ g : Γ, c g ∈ Y → c g⁻¹ = (c g)⁻¹ := by
    intro g hg
    have e : ρ g⁻¹ w = (c g)⁻¹ * w := by
      have h1 : w = (c g)⁻¹ * ρ g w := by rw [hcg g]; comm_group
      calc ρ g⁻¹ w = ρ g⁻¹ ((c g)⁻¹ * ρ g w) := by rw [← h1]
        _ = (c g)⁻¹ * w := by
          rw [map_mul, hYfix g⁻¹ _ (Y.inv_mem hg)]
          simp
    show ρ g⁻¹ w * w⁻¹ = (c g)⁻¹
    rw [e]
    comm_group
  let Ω : Subgroup Γ :=
    { carrier := {g | c g ∈ Y}
      one_mem' := by
        show c 1 ∈ Y
        simp [hc, Y.one_mem]
      mul_mem' := by
        intro g h hg hh
        show c (g * h) ∈ Y
        rw [hmul g h hh]
        exact Y.mul_mem hh hg
      inv_mem' := by
        intro g hg
        show c g⁻¹ ∈ Y
        rw [hinv g hg]
        exact Y.inv_mem hg }
  have hAΩ : A₁ ≤ Ω := fun a ha => hA a ha
  have hBΩ : B₁ ≤ Ω := fun b hb => by
    show c b ∈ Y
    simp [hc, hB b hb, Y.one_mem]
  have hΩ : ∀ g : Γ, c g ∈ Y := by
    have : (⊤ : Subgroup Γ) ≤ Ω := by
      rw [← hgen]
      exact sup_le hAΩ hBΩ
    exact fun g => this (Subgroup.mem_top g)
  have hmult : ∀ g h : Γ, c (g * h) = c g * c h := fun g h => by
    rw [hmul g h (hΩ h), mul_comm]
  have hc1 : c 1 = 1 := by simp [hc]
  have hB1 : ∀ b ∈ B₁, ∀ g : Γ, c (g * b * g⁻¹) = 1 := by
    intro b hb g
    have hcb : c b = 1 := by simp [hc, hB b hb]
    calc c (g * b * g⁻¹) = c g * c b * c g⁻¹ := by rw [hmult, hmult]
      _ = c g * c g⁻¹ := by rw [hcb, mul_one]
      _ = c (g * g⁻¹) := (hmult g g⁻¹).symm
      _ = 1 := by rw [mul_inv_cancel, hc1]
  have hA1 : ∀ a ∈ A₁, c a = 1 := by
    intro a ha
    obtain ⟨y, hy⟩ := hconj
    rw [hy] at ha
    obtain ⟨b, hb, rfl⟩ := ha
    exact hB1 b hb y
  let Ω₁ : Subgroup Γ := (MulAction.stabilizer (MulAut V) w).comap ρ
  have hΩ₁ : ∀ g : Γ, g ∈ Ω₁ ↔ ρ g w = w := fun g => by
    show ρ g ∈ MulAction.stabilizer (MulAut V) w ↔ _
    rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]
  have hAΩ₁ : A₁ ≤ Ω₁ := fun a ha => (hΩ₁ a).2 (by
    have := hA1 a ha
    simp only [hc, mul_inv_eq_one] at this
    exact this)
  have hBΩ₁ : B₁ ≤ Ω₁ := fun b hb => (hΩ₁ b).2 (hB b hb)
  have htop : (⊤ : Subgroup Γ) ≤ Ω₁ := by
    rw [← hgen]
    exact sup_le hAΩ₁ hBΩ₁
  intro φ hφ
  obtain ⟨g, rfl⟩ := hφ
  exact (hΩ₁ g).1 (htop (Subgroup.mem_top g))

theorem mem_fixV_of_mod_sup (ρ : Γ →* MulAut V) (W : Subgroup V) {A₁ B₁ : Subgroup Γ}
    (hgen : A₁ ⊔ B₁ = ⊤) (hconj : ∃ y : Γ, A₁ = B₁.map (MulAut.conj y).toMonoidHom)
    (hdec : W ≤ (W ⊓ fixV (A₁.map ρ)) ⊔ (W ⊓ fixV (B₁.map ρ))) {w : V}
    (hw : w ∈ W) (hA : ∀ a ∈ A₁, ρ a w * w⁻¹ ∈ fixV ρ.range) : w ∈ fixV (A₁.map ρ) := by
  obtain ⟨wa, hwa, wb, hwb, rfl⟩ := Subgroup.mem_sup.1 (hdec hw)
  have hYA : fixV ρ.range ≤ fixV (A₁.map ρ) := fun v hv x hx => by
    obtain ⟨a, -, rfl⟩ := hx
    exact hv _ ⟨a, rfl⟩
  have hwb' : wb ∈ fixV ρ.range := by
    refine mem_fixV_of_mod_fixV ρ hgen hconj (w := wb) (fun a ha => ?_) (fun b hb => ?_)
    · have h1 : ρ a wa = wa := mem_fixV.1 hwa.2 _ (Subgroup.mem_map_of_mem ρ ha)
      have h2 := hA a ha
      rw [map_mul, h1] at h2
      have : ρ a wb * wb⁻¹ = wa * ρ a wb * (wa * wb)⁻¹ := by comm_group
      rw [this]
      exact h2
    · exact mem_fixV.1 hwb.2 _ (Subgroup.mem_map_of_mem ρ hb)
  exact (fixV (A₁.map ρ)).mul_mem hwa.2 (hYA hwb')

namespace ThreeFiveHyp

variable {ρ : Γ →* MulAut V} {T M A : Subgroup Γ} (h : ThreeFiveHyp ρ T M A)

include h

theorem mem_fixV_A_of_mod [Finite V] {x : Γ} (hx : x ∉ M) {w : V} (hw : w ∈ wMod ρ T)
    (hA : ∀ a ∈ A, ρ a w * w⁻¹ ∈ fixV ρ.range) : w ∈ fixV (A.map ρ) := by
  exact mem_fixV_of_mod_sup ρ (wMod ρ T) (h.gen x hx) ⟨x⁻¹, (map_conj_inv_map_conj x A).symm⟩
    (h.wMod_le_sup hx) hw hA

theorem mem_fixV_B_of_mod [Finite V] {x : Γ} (hx : x ∉ M) {w : V} (hw : w ∈ wMod ρ T)
    (hB : ∀ b ∈ A.map (MulAut.conj x).toMonoidHom, ρ b w * w⁻¹ ∈ fixV ρ.range) :
    w ∈ fixV ((A.map (MulAut.conj x).toMonoidHom).map ρ) := by
  refine mem_fixV_of_mod_sup ρ (wMod ρ T) (by rw [sup_comm]; exact h.gen x hx) ⟨x, rfl⟩ ?_
    hw hB
  rw [sup_comm]
  exact h.wMod_le_sup hx

theorem mem_fixV_range_of_mod [Finite V] {w : V} (hw : w ∈ wMod ρ T)
    (hΓ : ∀ g : Γ, ρ g w * w⁻¹ ∈ fixV ρ.range) : w ∈ fixV ρ.range := by
  obtain ⟨x, hx⟩ := h.exists_not_mem
  have h1 := h.mem_fixV_A_of_mod hx hw (fun a _ => hΓ a)
  have h2 := h.mem_fixV_B_of_mod hx hw (fun b _ => hΓ b)
  rw [← h.fixV_inf_fixV hx]
  exact ⟨h1, h2⟩

end ThreeFiveHyp

end CFSG.CGT.PushingUpLit.BHS
