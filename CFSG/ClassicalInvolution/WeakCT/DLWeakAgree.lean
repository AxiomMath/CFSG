module

public import CFSG.ClassicalInvolution.WeakCT.SpAgree
public import CFSG.ClassicalInvolution.WeakCT.SpPair

public section

namespace CFSG.ClassicalInvolution.Models.SymplecticPairs

open CFSG.Assembly.LowTwoRank (StatedSp)

variable (K : Type) [Field K]

@[expose] def SymplecticBlockPair {X : Type} [Group X] (W U V : Subgroup X) : Prop :=
  ∃ (θ : StatedSp 2 K →* X) (c : StatedSp 2 K), θ.range = W ∧
    θ.ker ≤ Subgroup.center (StatedSp 2 K) ∧
    Function.Injective (θ.comp ((MulAut.conj c⁻¹).toMonoidHom.comp (longBlock K 2 1))) ∧
    ((longBlock K 2 1).range.map (MulAut.conj c⁻¹).toMonoidHom).map θ = U ∧
      ((shortBlock K (zero_ne_one : (0 : Fin 2) ≠ 1)).range.map
        (MulAut.conj c⁻¹).toMonoidHom).map θ = V

variable {K}

theorem SymplecticBlockStandardPair.pair {X : Type} [Group X] {W U V : Subgroup X}
    (h : SymplecticBlockStandardPair K W U V) : SymplecticBlockPair K W U V := by
  obtain ⟨θ, c, hrange, hker, hinj1, -, hU, hV⟩ := h
  exact ⟨θ, c, hrange, hker, hinj1, hU, hV⟩

end CFSG.ClassicalInvolution.Models.SymplecticPairs

namespace CFSG.ClassicalInvolution.WeakCT

open CFSG.Timmesfeld.LevisExtras
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (SymplecticBlockPair)
open scoped MatrixGroups

section Normalize

variable {F : Type} [Field F] {X : Type} [Group X]

theorem pair_normalize_sp' {W U V : Subgroup X} (h : SymplecticBlockPair F W U V) :
    ∃ θ : StatedSp 2 F →* X, θ.range = W ∧ θ.ker ≤ Subgroup.center (StatedSp 2 F) ∧
      Function.Injective (θ.comp (spBlock F 1)) ∧
      (θ.comp (spBlock F 1)).range = U ∧ (θ.comp (spBlock F 0)).range = V := by
  obtain ⟨θ, c, hrange, hker, hinj1, hU, hV⟩ := h
  rw [← spBlock_one_eq_longBlock] at hinj1 hU
  rw [← spBlock_zero_eq_shortBlock] at hV
  refine ⟨θ.comp (MulAut.conj c⁻¹).toMonoidHom, ?_, ker_comp_mulEquiv_le_center hker _, hinj1,
    ?_, ?_⟩
  · rw [range_comp_mulEquiv, hrange]
  · rw [MonoidHom.range_comp, ← Subgroup.map_map]
    exact hU
  · rw [MonoidHom.range_comp, ← Subgroup.map_map]
    exact hV

end Normalize

section SpSide

variable {F : Type} [Field F] [Finite F] {X : Type} [Group X]

theorem sp_centralizer' (hF : 4 ≤ Nat.card F) (u : Fin 2) {θ₁ : StatedSp 2 F →* X}
    (hf : Function.Injective (θ₁.comp (spBlock F u))) {m : X}
    (hm : m ∈ (θ₁.comp (spBlock F u)).range)
    (hc : ∀ a ∈ (diagTorus2 F).map (θ₁.comp (spBlock F u.rev)), a * m = m * a) :
    m ∈ (diagTorus2 F).map (θ₁.comp (spBlock F u)) := by
  obtain ⟨B, rfl⟩ := hm
  have hB : ∀ b ∈ (spBlock F u).range, θ₁ b = 1 → b = 1 := by
    rintro _ ⟨B', rfl⟩ h
    have : B' = 1 := hf (by simpa using h)
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
    have hcomm := commute_of_map_commute' θ₁ (spBlock F 0).range hB hx hd
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
    have hcomm := commute_of_map_commute' θ₁ (spBlock F 1).range hB hx hd
      (by simpa using h1.symm)
    have hB' := mem_diagTorus2_of_commute_sp_long hs₀ (A := B) (Commute.symm hcomm)
    exact ⟨B, hB', rfl⟩

end SpSide

section Agree

variable {F : Type} [Field F] [Finite F] {X : Type} [Group X]

theorem torus_agree_sp_one' (hF : 4 ≤ Nat.card F) (u : Fin 2) {θ₁ : StatedSp 2 F →* X}
    {θ₂ : SL(3, F) →* X} (hf : Function.Injective (θ₁.comp (spBlock F u)))
    (h₂ : θ₂.ker ≤ Subgroup.center SL(3, F))
    (hM : (θ₁.comp (spBlock F u)).range = (B23 F).map θ₂)
    (hcomm : ∀ x ∈ (θ₁.comp (spBlock F u.rev)).range, ∀ y ∈ (B12 F).map θ₂, x * y = y * x) :
    (diagTorus2 F).map (θ₁.comp (spBlock F u)) = (D23 F).map θ₂ := by
  have hTfin : Finite ((diagTorus2 F).map (θ₁.comp (spBlock F u))) := finite_map_subgroup _ _
  have hcyc : IsCyclic ((diagTorus2 F).map (θ₁.comp (spBlock F u))) :=
    (MulEquiv.isCyclic (Subgroup.equivMapOfInjective _ _ hf)).1 isCyclic_diagTorus2
  have hcard₁ : Nat.card ((diagTorus2 F).map (θ₁.comp (spBlock F u))) =
      Nat.card (diagTorus2 F) := Subgroup.card_map_of_injective hf
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
      exact sp_centralizer' hF u hf (hM ▸ hm) hcentral
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

theorem torus_agree_sp_sl3' (hF : 4 ≤ Nat.card F) (u t : Fin 2) {θ₁ : StatedSp 2 F →* X}
    {θ₂ : SL(3, F) →* X} (hf : Function.Injective (θ₁.comp (spBlock F u)))
    (h₂ : θ₂.ker ≤ Subgroup.center SL(3, F))
    (hM : (θ₁.comp (spBlock F u)).range = (Bs F t).map θ₂)
    (hcomm : ∀ x ∈ (θ₁.comp (spBlock F u.rev)).range, ∀ y ∈ (Bs F t.rev).map θ₂,
      x * y = y * x) :
    (diagTorus2 F).map (θ₁.comp (spBlock F u)) = (Ds F t).map θ₂ := by
  fin_cases t
  ·
    have hker := ker_comp_mulEquiv_le_center h₂ (MulAut.conj (swapSL : SL(3, F)))
    have := torus_agree_sp_one' hF u hf hker
      (by rw [show B23 F = Bs F 1 from rfl, map_flip_Bs]; exact hM)
      (by
        intro x hx y hy
        rw [show B12 F = Bs F 0 from rfl, map_flip_Bs] at hy
        exact hcomm x hx y hy)
    rw [show D23 F = Ds F 1 from rfl, map_flip_Ds] at this
    exact this
  · exact torus_agree_sp_one' hF u hf h₂ hM hcomm

end Agree

section Adjust

variable {F : Type} [Field F] [Finite F] {X : Type} [Group X]

theorem exists_adjust_sp_long' (hF : 4 ≤ Nat.card F) {θ₀ : StatedSp 2 F →* X}
    (hθ₀ : θ₀.ker ≤ Subgroup.center (StatedSp 2 F))
    (hf1 : Function.Injective (θ₀.comp (spBlock F 1))) {ρ : SL(2, F) →* X}
    (hρ : Function.Injective ρ) (hrange : ρ.range = (θ₀.comp (spBlock F 1)).range)
    (htor : (diagTorus2 F).map ρ = (diagTorus2 F).map (θ₀.comp (spBlock F 1))) :
    ∃ θ' : StatedSp 2 F →* X, θ'.ker ≤ Subgroup.center (StatedSp 2 F) ∧
      θ'.comp (spBlock F 1) = ρ ∧
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
  refine ⟨θ₀.comp β.toMonoidHom, ker_comp_mulEquiv_le_center hθ₀ β, ?_, ?_, ?_⟩
  · refine MonoidHom.ext fun A => ?_
    show θ₀ (β (spBlock F 1 A)) = ρ A
    rw [hβ1, hα]
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
