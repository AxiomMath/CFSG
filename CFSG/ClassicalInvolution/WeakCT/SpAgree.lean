module

public import CFSG.ClassicalInvolution.WeakCT.SpTorus
public import CFSG.ClassicalInvolution.WeakCT.Sides

public section

namespace CFSG.ClassicalInvolution.WeakCT

open CFSG.Assembly.LowTwoRank (StatedSp)
open scoped MatrixGroups

section Aux

variable {G X : Type*} [Group G] [Group X]

theorem commute_of_map_commute' (θ : G →* X) (B : Subgroup G) (hB : ∀ b ∈ B, θ b = 1 → b = 1)
    {x d : G} (hx : x ∈ B) (hd : d * x * d⁻¹ ∈ B) (h : θ x * θ d = θ d * θ x) :
    x * d = d * x := by
  have hmem : x * d * x⁻¹ * d⁻¹ ∈ B := by
    have : x * d * x⁻¹ * d⁻¹ = x * (d * x * d⁻¹)⁻¹ := by group
    rw [this]
    exact mul_mem hx (inv_mem hd)
  have hz : θ (x * d * x⁻¹ * d⁻¹) = 1 := by
    simp only [map_mul, map_inv]
    rw [h]
    group
  have hz1 : x * d * x⁻¹ * d⁻¹ = 1 := hB _ hmem hz
  calc x * d = (x * d * x⁻¹ * d⁻¹) * (d * x) := by group
    _ = d * x := by rw [hz1, one_mul]

end Aux

section SpSide

variable {F : Type} [Field F] [Finite F] {X : Type} [Group X]

theorem sp_centralizer (hF : 4 ≤ Nat.card F) (u : Fin 2) {θ₁ : StatedSp 2 F →* X}
    (hf : ∀ v : Fin 2, Function.Injective (θ₁.comp (spBlock F v))) {m : X}
    (hm : m ∈ (θ₁.comp (spBlock F u)).range)
    (hc : ∀ a ∈ (diagTorus2 F).map (θ₁.comp (spBlock F u.rev)), a * m = m * a) :
    m ∈ (diagTorus2 F).map (θ₁.comp (spBlock F u)) := by
  obtain ⟨B, rfl⟩ := hm
  have hB : ∀ v : Fin 2, ∀ b ∈ (spBlock F v).range, θ₁ b = 1 → b = 1 := by
    rintro v _ ⟨B', rfl⟩ h
    have : B' = 1 := hf v (by simpa using h)
    rw [this, map_one]
  fin_cases u
  ·
    obtain ⟨s₀, hs₀⟩ := exists_unit_ne_one (K := F) (by omega)
    have h1 := hc (θ₁ (spBlock F 1 (torusHom F s₀))) ⟨_, ⟨s₀, rfl⟩, rfl⟩
    have hx : spBlock F 0 B ∈ (spBlock F 0).range := ⟨B, rfl⟩
    have hd : spBlock F 1 (torusHom F s₀) * spBlock F 0 B * (spBlock F 1 (torusHom F s₀))⁻¹ ∈
        (spBlock F 0).range := by
      rw [sp_torus1_conj]
      exact ⟨_, rfl⟩
    have hcomm := commute_of_map_commute' θ₁ (spBlock F 0).range (hB 0) hx hd
      (by simpa using h1.symm)
    have hB' := mem_diagTorus2_of_commute_sp_short hs₀ (A := B) (Commute.symm hcomm)
    exact ⟨B, hB', rfl⟩
  ·
    obtain ⟨s₀, hs₀⟩ := exists_unit_sq_ne_one hF
    have h1 := hc (θ₁ (spBlock F 0 (torusHom F s₀))) ⟨_, ⟨s₀, rfl⟩, rfl⟩
    have hx : spBlock F 1 B ∈ (spBlock F 1).range := ⟨B, rfl⟩
    have hd : spBlock F 0 (torusHom F s₀) * spBlock F 1 B * (spBlock F 0 (torusHom F s₀))⁻¹ ∈
        (spBlock F 1).range := by
      rw [sp_torus0_conj]
      exact ⟨_, rfl⟩
    have hcomm := commute_of_map_commute' θ₁ (spBlock F 1).range (hB 1) hx hd
      (by simpa using h1.symm)
    have hB' := mem_diagTorus2_of_commute_sp_long hs₀ (A := B) (Commute.symm hcomm)
    exact ⟨B, hB', rfl⟩

end SpSide

section Agree

variable {F : Type} [Field F] [Finite F] {X : Type} [Group X]

theorem torus_agree_sp_one (hF : 4 ≤ Nat.card F) (u : Fin 2) {θ₁ : StatedSp 2 F →* X}
    {θ₂ : SL(3, F) →* X} (hf : ∀ v : Fin 2, Function.Injective (θ₁.comp (spBlock F v)))
    (h₂ : θ₂.ker ≤ Subgroup.center SL(3, F))
    (hM : (θ₁.comp (spBlock F u)).range = (B23 F).map θ₂)
    (hcomm : ∀ x ∈ (θ₁.comp (spBlock F u.rev)).range, ∀ y ∈ (B12 F).map θ₂, x * y = y * x) :
    (diagTorus2 F).map (θ₁.comp (spBlock F u)) = (D23 F).map θ₂ := by
  have hTfin : Finite ((diagTorus2 F).map (θ₁.comp (spBlock F u))) := finite_map_subgroup _ _
  have hcyc : IsCyclic ((diagTorus2 F).map (θ₁.comp (spBlock F u))) :=
    (MulEquiv.isCyclic (Subgroup.equivMapOfInjective _ _ (hf u))).1 isCyclic_diagTorus2
  have hcard₁ : Nat.card ((diagTorus2 F).map (θ₁.comp (spBlock F u))) =
      Nat.card (diagTorus2 F) := Subgroup.card_map_of_injective (hf u)
  have hcard₂ : Nat.card ((D12 F).map θ₂) = Nat.card (diagTorus2 F) := by
    rw [map_D12]
    exact Subgroup.card_map_of_injective (comp_blockSL_injective h₂ _ (by omega))
  have hcard₃ : Nat.card ((D23 F).map θ₂) = Nat.card (diagTorus2 F) := by
    rw [map_D23]
    exact Subgroup.card_map_of_injective (comp_blockSL_injective h₂ _ (by omega))
  have hle : (diagTorus2 F).map (θ₁.comp (spBlock F u)) ≤ (D23 F).map θ₂ := by
    refine le_of_centralizer_of_card_lt (M := (B23 F).map θ₂)
      (A := (diagTorus2 F).map (θ₁.comp (spBlock F u.rev))) (C := (D12 F).map θ₂) ?_ ?_ ?_ ?_ ?_
      ?_ ?_
    · rw [← hM]
      exact Subgroup.map_le_range _ _
    · rintro _ ⟨a, ⟨s, rfl⟩, rfl⟩ _ ⟨t, ⟨r, rfl⟩, rfl⟩
      fin_cases u
      · simp only [MonoidHom.comp_apply, ← map_mul]
        exact congrArg θ₁ (spTorus_comm r s).symm.eq
      · simp only [MonoidHom.comp_apply, ← map_mul]
        exact congrArg θ₁ (spTorus_comm s r).eq
    · intro a ha c hc
      exact hcomm a (Subgroup.map_le_range _ _ ha) c (Subgroup.map_mono D12_le_B12 hc)
    · rintro _ ⟨c, hc, rfl⟩ _ ⟨m, hm, rfl⟩
      exact ⟨c * m * c⁻¹, D12_conj_mem_B23 hc hm, by simp⟩
    · intro m hm hcentral
      exact sp_centralizer hF u hf (hM ▸ hm) hcentral
    · rw [hcard₂]
      calc Nat.card (MulAut ((diagTorus2 F).map (θ₁.comp (spBlock F u))))
          < Nat.card ((diagTorus2 F).map (θ₁.comp (spBlock F u))) :=
            card_mulAut_lt _ (by rw [hcard₁]; exact one_lt_card_diagTorus2 (by omega))
        _ = Nat.card (diagTorus2 F) := hcard₁
    · rintro _ ⟨d, hd, rfl⟩ hd1 _ ⟨m, ⟨A', rfl⟩, rfl⟩ hdm
      obtain ⟨t, rfl⟩ := mem_D12_iff.mp hd
      have ht : t ≠ 1 := fun h => by
        subst h
        exact hd1 (by simp)
      have hA := mem_diagTorus2_of_map_commute_one h₂ ht (A := A') hdm.symm
      exact ⟨_, ⟨A', hA, rfl⟩, rfl⟩
  have : Finite ((D23 F).map θ₂) := finite_map_subgroup _ _
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcard₃, hcard₁])

theorem torus_agree_sp_sl3 (hF : 4 ≤ Nat.card F) (u t : Fin 2) {θ₁ : StatedSp 2 F →* X}
    {θ₂ : SL(3, F) →* X} (hf : ∀ v : Fin 2, Function.Injective (θ₁.comp (spBlock F v)))
    (h₂ : θ₂.ker ≤ Subgroup.center SL(3, F))
    (hM : (θ₁.comp (spBlock F u)).range = (Bs F t).map θ₂)
    (hcomm : ∀ x ∈ (θ₁.comp (spBlock F u.rev)).range, ∀ y ∈ (Bs F t.rev).map θ₂,
      x * y = y * x) :
    (diagTorus2 F).map (θ₁.comp (spBlock F u)) = (Ds F t).map θ₂ := by
  fin_cases t
  ·
    have hker := ker_comp_mulEquiv_le_center h₂ (MulAut.conj (swapSL : SL(3, F)))
    have := torus_agree_sp_one hF u hf hker
      (by rw [show B23 F = Bs F 1 from rfl, map_flip_Bs]; exact hM)
      (by
        intro x hx y hy
        rw [show B12 F = Bs F 0 from rfl, map_flip_Bs] at hy
        exact hcomm x hx y hy)
    rw [show D23 F = Ds F 1 from rfl, map_flip_Ds] at this
    exact this
  · exact torus_agree_sp_one hF u hf h₂ hM hcomm

end Agree

section Adjust

variable {F : Type} [Field F] [Finite F] {X : Type} [Group X]

theorem exists_adjust_sp_long (hF : 4 ≤ Nat.card F) {θ₀ : StatedSp 2 F →* X}
    (hθ₀ : θ₀.ker ≤ Subgroup.center (StatedSp 2 F))
    (hf1 : Function.Injective (θ₀.comp (spBlock F 1)))
    (hf0 : Function.Injective (θ₀.comp (spBlock F 0))) {ρ : SL(2, F) →* X}
    (hρ : Function.Injective ρ) (hrange : ρ.range = (θ₀.comp (spBlock F 1)).range)
    (htor : (diagTorus2 F).map ρ = (diagTorus2 F).map (θ₀.comp (spBlock F 1))) :
    ∃ θ' : StatedSp 2 F →* X, θ'.ker ≤ Subgroup.center (StatedSp 2 F) ∧
      θ'.comp (spBlock F 1) = ρ ∧ Function.Injective (θ'.comp (spBlock F 0)) ∧
      (θ'.comp (spBlock F 0)).range = (θ₀.comp (spBlock F 0)).range ∧
      (diagTorus2 F).map (θ'.comp (spBlock F 0)) = (diagTorus2 F).map (θ₀.comp (spBlock F 0)) := by
  let α : SL(2, F) ≃* SL(2, F) :=
    (MonoidHom.ofInjective hρ).trans
      ((MulEquiv.subgroupCongr hrange).trans (MonoidHom.ofInjective hf1).symm)
  have hα : ∀ A, θ₀ (spBlock F 1 (α A)) = ρ A := by
    intro A
    have h := congrArg Subtype.val ((MonoidHom.ofInjective hf1).apply_symm_apply
      (MulEquiv.subgroupCongr hrange (MonoidHom.ofInjective hρ A)))
    exact h
  have hαD : (diagTorus2 F).map α.toMonoidHom ≤ diagTorus2 F := by
    rintro _ ⟨d, hd, rfl⟩
    have hmem : ρ d ∈ (diagTorus2 F).map (θ₀.comp (spBlock F 1)) := by
      rw [← htor]
      exact ⟨d, hd, rfl⟩
    obtain ⟨d', hd', hd'eq⟩ := hmem
    have hαd : α d = d' := hf1 ((hα d).trans hd'eq.symm)
    simpa [hαd] using hd'
  obtain ⟨β, α', hβ1, hβ0, hα'D⟩ := exists_extend_sp hF α hαD
  refine ⟨θ₀.comp β.toMonoidHom, ker_comp_mulEquiv_le_center hθ₀ β, ?_, ?_, ?_, ?_⟩
  · refine MonoidHom.ext fun A => ?_
    show θ₀ (β (spBlock F 1 A)) = ρ A
    rw [hβ1, hα]
  · have h : (θ₀.comp β.toMonoidHom).comp (spBlock F 0) =
        (θ₀.comp (spBlock F 0)).comp α'.toMonoidHom :=
      MonoidHom.ext fun A => by
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
        rw [hβ0]
    rw [h]
    exact hf0.comp α'.injective
  · have h : (θ₀.comp β.toMonoidHom).comp (spBlock F 0) =
        (θ₀.comp (spBlock F 0)).comp α'.toMonoidHom :=
      MonoidHom.ext fun A => by
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
        rw [hβ0]
    rw [h]
    exact range_comp_mulEquiv _ α'
  · have h : (θ₀.comp β.toMonoidHom).comp (spBlock F 0) =
        (θ₀.comp (spBlock F 0)).comp α'.toMonoidHom :=
      MonoidHom.ext fun A => by
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
        rw [hβ0]
    rw [h, ← Subgroup.map_map]
    congr 1
    exact Subgroup.eq_of_le_of_card_ge hα'D (by rw [Subgroup.card_map_of_injective α'.injective])

end Adjust

end CFSG.ClassicalInvolution.WeakCT
