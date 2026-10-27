module

public import CFSG.CGT.PushingUpLit.BHS.ThreeFiveA

public section

namespace CFSG.CGT.PushingUpLit.BHS

open CFSG.Quasithin CFSG.CGT.PushingUpLit.BHS.Glauberman

local macro "comm_group" : tactic =>
  `(tactic| (apply Additive.ofMul.injective
             simp only [ofMul_mul, ofMul_inv, ofMul_div, ofMul_one]
             abel))

variable {V : Type} [CommGroup V] {Γ : Type} [Group Γ]

@[expose] def cenMod (ρ : Γ →* MulAut V) (U : Subgroup V) : Subgroup Γ :=
  (centSub U).comap ρ

theorem mem_cenMod {ρ : Γ →* MulAut V} {U : Subgroup V} {g : Γ} :
    g ∈ cenMod ρ U ↔ ∀ u ∈ U, ρ g u = u := Iff.rfl

theorem conj_mem_cenMod {ρ : Γ →* MulAut V} {U : Subgroup V} (hU : ∀ g : Γ, ∀ u ∈ U, ρ g u ∈ U)
    {g : Γ} (hg : g ∈ cenMod ρ U) (x : Γ) : x * g * x⁻¹ ∈ cenMod ρ U := by
  rw [mem_cenMod] at hg ⊢
  intro u hu
  have h1 : ρ x⁻¹ u ∈ U := hU x⁻¹ u hu
  have h2 : ρ g (ρ x⁻¹ u) = ρ x⁻¹ u := hg _ h1
  have h3 : ρ (x * g * x⁻¹) u = ρ x (ρ g (ρ x⁻¹ u)) := by
    rw [map_mul, map_mul]
    rfl
  rw [h3, h2, ← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]

namespace ThreeFiveHyp

variable {ρ : Γ →* MulAut V} {T M A : Subgroup Γ} (h : ThreeFiveHyp ρ T M A)

include h

theorem not_le_cenW : ¬ A ≤ cenMod ρ (wMod ρ T) := by
  intro hA
  obtain ⟨x, hx⟩ := h.exists_not_mem
  have hB : A.map (MulAut.conj x).toMonoidHom ≤ cenMod ρ (wMod ρ T) := by
    rintro _ ⟨a, ha, rfl⟩
    exact conj_mem_cenMod (wMod_inv ρ T) (hA ha) x
  have htop : (⊤ : Subgroup Γ) ≤ cenMod ρ (wMod ρ T) := by
    rw [← h.gen x hx]
    exact sup_le hA hB
  obtain ⟨g, z, hz, hgz⟩ := h.nontriv
  exact hgz ((mem_cenMod.1 (htop (Subgroup.mem_top g))) z (fixV_le_wMod ρ T hz))

theorem wMod_le_sup [Finite V] {x : Γ} (hx : x ∉ M) :
    wMod ρ T ≤ (wMod ρ T ⊓ fixV (A.map ρ)) ⊔
      (wMod ρ T ⊓ fixV ((A.map (MulAut.conj x).toMonoidHom).map ρ)) := by
  set W := wMod ρ T with hW
  set B := A.map (MulAut.conj x).toMonoidHom with hB
  have hAq : IsQuadratic (A.map ρ) := h.quadratic
  have hBq : IsQuadratic (B.map ρ) := by
    rw [hB, map_map_conj]
    exact isQuadratic_map_conj hAq _
  set U₁ := (W ⊓ fixV (A.map ρ)) ⊔ (W ⊓ fixV (B.map ρ)) with hU₁
  have hAinv : ∀ a ∈ A, ∀ u ∈ U₁, ρ a u ∈ U₁ := by
    intro a ha u hu
    obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := Subgroup.mem_sup.1 hu
    have hρa : ρ a ∈ A.map ρ := Subgroup.mem_map_of_mem ρ ha
    have hc : ρ a u₂ * u₂⁻¹ ∈ W ⊓ fixV (A.map ρ) :=
      ⟨Subgroup.mul_mem _ (wMod_inv ρ T a hu₂.1) (Subgroup.inv_mem _ hu₂.1),
        hAq (G6.mem_commV_of_mem hρa u₂)⟩
    rw [map_mul, mem_fixV.1 hu₁.2 _ hρa]
    have : u₁ * ρ a u₂ = (u₁ * (ρ a u₂ * u₂⁻¹)) * u₂ := by
      rw [mul_assoc, inv_mul_cancel_right]
    rw [this]
    exact Subgroup.mul_mem_sup (Subgroup.mul_mem _ hu₁ hc) hu₂
  have hBinv : ∀ b ∈ B, ∀ u ∈ U₁, ρ b u ∈ U₁ := by
    intro b hb u hu
    obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := Subgroup.mem_sup.1 hu
    have hρb : ρ b ∈ B.map ρ := Subgroup.mem_map_of_mem ρ hb
    have hc : ρ b u₁ * u₁⁻¹ ∈ W ⊓ fixV (B.map ρ) :=
      ⟨Subgroup.mul_mem _ (wMod_inv ρ T b hu₁.1) (Subgroup.inv_mem _ hu₁.1),
        hBq (G6.mem_commV_of_mem hρb u₁)⟩
    rw [map_mul, mem_fixV.1 hu₂.2 _ hρb]
    have : ρ b u₁ * u₂ = u₁ * ((ρ b u₁ * u₁⁻¹) * u₂) := by comm_group
    rw [this]
    exact Subgroup.mul_mem_sup hu₁ (Subgroup.mul_mem _ hc hu₂)
  have hAI : A ≤ (stabSub U₁).comap ρ := fun a ha => by
    refine fun u => ⟨fun hu => ?_, fun hu => hAinv a ha u hu⟩
    have := hAinv a⁻¹ (A.inv_mem ha) _ hu
    simpa using this
  have hBI : B ≤ (stabSub U₁).comap ρ := fun b hb => by
    refine fun u => ⟨fun hu => ?_, fun hu => hBinv b hb u hu⟩
    have := hBinv b⁻¹ (B.inv_mem hb) _ hu
    simpa using this
  have hI : (⊤ : Subgroup Γ) ≤ (stabSub U₁).comap ρ := by
    rw [← h.gen x hx]
    exact sup_le hAI hBI
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨g, z, hz, rfl⟩
  have hzU : z ∈ U₁ := by
    refine Subgroup.mem_sup_left ⟨fixV_le_wMod ρ T hz, ?_⟩
    exact fun a ha => hz a (Subgroup.map_mono h.le_T ha)
  exact ((hI (Subgroup.mem_top g)) z).2 hzU

theorem fixV_inf_fixV {x : Γ} (hx : x ∉ M) :
    fixV (A.map ρ) ⊓ fixV ((A.map (MulAut.conj x).toMonoidHom).map ρ) = fixV ρ.range := by
  rw [← fixV_sup, ← Subgroup.map_sup, h.gen x hx, ← MonoidHom.range_eq_map]

end ThreeFiveHyp

end CFSG.CGT.PushingUpLit.BHS
