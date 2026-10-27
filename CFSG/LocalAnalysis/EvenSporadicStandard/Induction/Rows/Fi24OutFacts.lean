module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Out1SlimEquiv

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.EvenSporadicStandard.Solomon78

structure Fi24OutFacts (Y : Type) [Group Y] (ν : MulAut Y) : Prop where
  sq : ν * ν = 1
  fusion : ∀ σ : MulAut Y, σ * σ = 1 → ∃ h : Y,
    (MulAut.conj h * ν * (MulAut.conj h)⁻¹) * σ = σ * (MulAut.conj h * ν * (MulAut.conj h)⁻¹)
  pair : ∃ h : Y, ν h * h⁻¹ ≠ 1 ∧ ν (ν h * h⁻¹) = ν h * h⁻¹ ∧
    twoAdic (fixSubgroup ν ⊓ centralizer ({ν h * h⁻¹} : Set Y)) = twoAdic (fixSubgroup ν)
  cent : ∀ α : MulAut Y, α * ν = ν * α →
    ∃ m ∈ fixSubgroup ν, α = MulAut.conj m ∨ α = ν * MulAut.conj m
  coatom : IsCoatom (fixSubgroup ν)
  allInner : AllInner ↥(fixSubgroup ν)
  center_bot : center ↥(fixSubgroup ν) = ⊥
  card_le : Nat.card ↥(fixSubgroup ν) ≤ 4089470473293004800

section Transport

variable {Y Y' : Type} [Group Y] [Group Y']

theorem fi24out_fixSubgroup_congr (e : Y ≃* Y') (ν : MulAut Y) :
    fixSubgroup (MulAut.congr e ν) = (fixSubgroup ν).map e.toMonoidHom := by
  ext y
  constructor
  · intro hy
    have h1 : e (ν (e.symm y)) = y := hy
    have h2 : ν (e.symm y) = e.symm y := by
      have := congrArg e.symm h1
      rwa [e.symm_apply_apply] at this
    exact ⟨e.symm y, h2, e.apply_symm_apply y⟩
  · rintro ⟨x, hx, rfl⟩
    have hx' : ν x = x := hx
    show e (ν (e.symm (e x))) = e x
    rw [e.symm_apply_apply, hx']

theorem fi24out_twoAdic_map_mulEquiv (e : Y ≃* Y') (S : Subgroup Y) :
    twoAdic (S.map e.toMonoidHom) = twoAdic S := by
  unfold twoAdic
  rw [Subgroup.card_map_of_injective e.injective]

theorem fi24out_map_centralizer_singleton (e : Y ≃* Y') (m : Y) :
    (centralizer ({m} : Set Y)).map e.toMonoidHom = centralizer ({e m} : Set Y') := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine mem_centralizer_singleton_iff.2 ?_
    have := mem_centralizer_singleton_iff.1 hx
    show e x * e m = e m * e x
    rw [← map_mul, ← map_mul, this]
  · intro hy
    refine ⟨e.symm y, mem_centralizer_singleton_iff.2 ?_, e.apply_symm_apply y⟩
    have h := mem_centralizer_singleton_iff.1 hy
    apply e.injective
    rw [map_mul, map_mul, e.apply_symm_apply]
    exact h

theorem fi24out_congr_conj (e : Y ≃* Y') (h : Y) :
    MulAut.congr e (MulAut.conj h) = MulAut.conj (e h) := by
  ext y
  simp [MulAut.conj_apply]

noncomputable def fi24out_fixEquiv (e : Y ≃* Y') (ν : MulAut Y) :
    ↥(fixSubgroup ν) ≃* ↥(fixSubgroup (MulAut.congr e ν)) :=
  (e.subgroupMap (fixSubgroup ν)).trans
    (MulEquiv.subgroupCongr (fi24out_fixSubgroup_congr e ν).symm)

theorem fi24out_center_eq_bot_of_equiv {A B : Type} [Group A] [Group B] (φ : A ≃* B)
    (h : center A = ⊥) : center B = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have h1 : φ.symm z ∈ center A := by
    rw [mem_center_iff]
    intro g
    have := mem_center_iff.1 hz (φ g)
    apply φ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact this
  rw [h, mem_bot] at h1
  rw [mem_bot]
  calc z = φ (φ.symm z) := (φ.apply_symm_apply z).symm
    _ = 1 := by rw [h1, map_one]

theorem Fi24OutFacts.of_mulEquiv (e : Y ≃* Y') {ν : MulAut Y} (h : Fi24OutFacts Y ν) :
    Fi24OutFacts Y' (MulAut.congr e ν) := by
  set F : MulAut Y ≃* MulAut Y' := MulAut.congr e with hF
  have hfix : fixSubgroup (F ν) = (fixSubgroup ν).map e.toMonoidHom := fi24out_fixSubgroup_congr e ν
  have happ : ∀ y : Y, F ν (e y) = e (ν y) := fun y => by
    show e (ν (e.symm (e y))) = e (ν y)
    rw [e.symm_apply_apply]
  have hcj : ∀ x : Y, F (MulAut.conj x) = MulAut.conj (e x) := fun x => fi24out_congr_conj e x
  refine ⟨by rw [← map_mul, h.sq, map_one], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro σ' hσ'
    have hσ : F.symm σ' * F.symm σ' = 1 := by rw [← map_mul, hσ', map_one]
    obtain ⟨x, hx⟩ := h.fusion _ hσ
    refine ⟨e x, ?_⟩
    have hx' := congrArg F hx
    simp only [map_mul, map_inv, MulEquiv.apply_symm_apply, hcj] at hx'
    exact hx'
  · obtain ⟨x, hx1, hx2, hx3⟩ := h.pair
    have hm : F ν (e x) * (e x)⁻¹ = e (ν x * x⁻¹) := by
      rw [happ, map_mul, map_inv]
    refine ⟨e x, ?_, ?_, ?_⟩
    · rw [hm]
      intro h'
      exact hx1 (e.injective (by rw [h', map_one]))
    · rw [hm, happ, hx2]
    · rw [hm, hfix, ← fi24out_map_centralizer_singleton, ← Subgroup.map_inf _ _ _ e.injective,
        fi24out_twoAdic_map_mulEquiv, fi24out_twoAdic_map_mulEquiv]
      exact hx3
  · intro α' hα'
    have hα : F.symm α' * ν = ν * F.symm α' := by
      have := congrArg F.symm hα'
      simpa only [map_mul, MulEquiv.symm_apply_apply] using this
    obtain ⟨m, hm, hm'⟩ := h.cent _ hα
    refine ⟨e m, ?_, ?_⟩
    · rw [hfix]
      exact ⟨m, hm, rfl⟩
    · have hα'F : α' = F (F.symm α') := (F.apply_symm_apply α').symm
      rcases hm' with hm' | hm'
      · left
        rw [hα'F, hm', hcj]
      · right
        rw [hα'F, hm', map_mul, hcj]
  · rw [hfix]
    exact (OrderIso.isCoatom_iff (e.mapSubgroup) (fixSubgroup ν)).2 h.coatom
  · exact AllInner.of_mulEquiv (fi24out_fixEquiv e ν) h.allInner
  · exact fi24out_center_eq_bot_of_equiv (fi24out_fixEquiv e ν) h.center_bot
  · rw [← Nat.card_congr (fi24out_fixEquiv e ν).toEquiv]
    exact h.card_le

theorem Fi24OutFacts.conj {Y : Type} [Group Y] {ν : MulAut Y} (h : Fi24OutFacts Y ν) (g : Y) :
    Fi24OutFacts Y (MulAut.conj g * ν * (MulAut.conj g)⁻¹) := by
  have e := Fi24OutFacts.of_mulEquiv (MulAut.conj g) h
  have hν : MulAut.congr (MulAut.conj g) ν = MulAut.conj g * ν * (MulAut.conj g)⁻¹ := by
    ext y
    simp [MulAut.conj_apply, MulAut.mul_apply]
  rwa [hν] at e

end Transport

end CFSG.EvenSporadicStandard.Induction
