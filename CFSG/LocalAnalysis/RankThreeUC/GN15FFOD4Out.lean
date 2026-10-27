module

public import Mathlib.Data.Fintype.Perm
public import CFSG.RankThree.PartOne.KLC.ThreePoint

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.D4

open Subgroup
open scoped commutatorElement Pointwise

section Abstract

variable {A X : Type*} [Group A] [MulAction A X]

private lemma fin3_cube_fixed_is_one : ∀ u : Equiv.Perm (Fin 3), u ^ 3 = 1 →
    (∃ i, u i = i) → u = 1 := by
  decide

private lemma fin3_cycle_cover : ∀ u : Equiv.Perm (Fin 3), u ^ 3 = 1 →
    (∀ i, u i ≠ i) → ∀ i j : Fin 3, j = i ∨ j = u i ∨ j = u (u i) := by
  decide

private lemma fin3_cycle_distinct : ∀ u : Equiv.Perm (Fin 3), u ^ 3 = 1 →
    (∀ i, u i ≠ i) → ∀ i : Fin 3,
      i ≠ u i ∧ u i ≠ u (u i) ∧ i ≠ u (u i) := by
  decide

private lemma fin3_inv_of_threeCycle : ∀ u v : Equiv.Perm (Fin 3), u ^ 3 = 1 →
    (∀ i, u i ≠ i) → v * u * v⁻¹ = u⁻¹ →
    ∃ i, v i = i ∧ ∀ j, v j = j → j = i := by
  decide


private lemma fin3_cube_apply : ∀ u : Equiv.Perm (Fin 3), u ^ 3 = 1 →
    ∀ i : Fin 3, u (u (u i)) = i := by
  decide

private lemma fin3_mul_transposition_fixed : ∀ v w : Equiv.Perm (Fin 3),
    (∀ i, v i ≠ i) → w * w = 1 → w ≠ 1 → ∃ i, (v * w) i = i := by
  decide

private lemma fin3_fixed_index_transposition : ∀ (t : Equiv.Perm (Fin 3)) (i0 i1 i2 : Fin 3),
    i0 ≠ i1 → i0 ≠ i2 → i1 ≠ i2 →
    (∀ j : Fin 3, j = i0 ∨ j = i1 ∨ j = i2) → t i0 = i0 →
    (t i1 = i1 ∧ t i2 = i2) ∨ (t i1 = i2 ∧ t i2 = i1) := by
  decide

theorem threeCycle_of_inverted (N : Subgroup A) [N.Normal] {F y z : X}
    (hO : ∀ g : A, g • F = F ∨ g • F = y ∨ g • F = z)
    {κ : A} (hκF : κ • F = F) (hκy : κ • y = z) (hκz : κ • z = y) (hyz : y ≠ z)
    (hN : ∀ n ∈ N, n • F = F)
    (hE : ∀ g h : A, g • F = F → h • F = F → ⁅g, h⁆ ∈ N)
    {α β : A} (hα : α ^ 3 ∈ N) (hαN : α ∉ N) (hβ : β * α * β⁻¹ = α⁻¹) :
    ∃ P Q R : X, ({P, Q, R} : Set X) = {F, y, z} ∧ P ≠ Q ∧ Q ≠ R ∧ P ≠ R ∧
      β • P = P ∧ β • Q = R ∧ β • R = Q ∧
      ((α • P = Q ∧ α • Q = R ∧ α • R = P) ∨ (α • P = R ∧ α • R = Q ∧ α • Q = P)) ∧
      ∀ γ : A, γ * β = β * γ →
        (γ • P = P ∧ γ • Q = Q ∧ γ • R = R) ∨ (γ • P = P ∧ γ • Q = R ∧ γ • R = Q) := by
  classical
  let S : Finset X := {F, y, z}
  have hFy : F ≠ y := by
    intro h
    apply hyz
    have h1 : κ • y = y := by rw [← h, hκF]
    rw [← h1, hκy]
  have hFz : F ≠ z := by
    intro h
    apply hyz
    have h1 : κ • z = z := by rw [← h, hκF]
    rw [← hκz, h1]
  have hS_card : S.card = 3 := by
    simp [S, hFy, hFz, hyz]
  have hcomm_ab : ⁅β, α⁆ ∉ N := by
    intro h
    have e : ⁅β, α⁆ = (α ^ 2)⁻¹ := by
      simp only [commutatorElement_def]
      rw [hβ]
      group
    rw [e] at h
    have h2 : α ^ 2 ∈ N := by
      simpa using N.inv_mem h
    have h3 : (α ^ 2)⁻¹ ∈ N := N.inv_mem h2
    have hαmem : α ∈ N := by
      have e2 : α = α ^ 3 * (α ^ 2)⁻¹ := by group
      rw [e2]
      exact N.mul_mem hα h3
    exact hαN hαmem
  have hex : ∃ g : A, g • F ≠ F := by
    by_contra h
    push Not at h
    exact hcomm_ab (hE β α (h β) (h α))
  obtain ⟨g, hg⟩ := hex
  have hy_orb : ∃ c : A, c • F = y := by
    rcases hO g with h | h | h
    · exact absurd h hg
    · exact ⟨g, h⟩
    · exact ⟨κ * g, by rw [mul_smul, h, hκz]⟩
  have hz_orb : ∃ c : A, c • F = z := by
    rcases hO g with h | h | h
    · exact absurd h hg
    · exact ⟨κ * g, by rw [mul_smul, h, hκy]⟩
    · exact ⟨g, h⟩
  have hrep : ∀ P ∈ S, ∃ c : A, c • F = P := by
    intro P hP
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hP
    rcases hP with rfl | rfl | rfl
    · exact ⟨1, by simp⟩
    · exact hy_orb
    · exact hz_orb
  have hNfix : ∀ n ∈ N, ∀ P ∈ S, n • P = P := by
    intro n hn P hP
    obtain ⟨c, hc⟩ := hrep P hP
    rw [← hc]
    exact CFSG.RankThree.PartOne.KLC.smul_orbit_of_normal hN hn c
  have hSmap : ∀ a : A, ∀ P ∈ S, a • P ∈ S := by
    intro a P hP
    obtain ⟨c, hc⟩ := hrep P hP
    rw [← hc]
    have h := hO (a * c)
    simpa [S, Finset.mem_insert, Finset.mem_singleton, smul_smul] using h
  have hcomm_of_fix : ∀ g h : A, ∀ P ∈ S, g • P = P → h • P = P → ⁅g, h⁆ ∈ N := by
    intro g h P hP hgP hhP
    obtain ⟨c, hc⟩ := hrep P hP
    have hgF : (c⁻¹ * g * c) • F = F := by
      calc (c⁻¹ * g * c) • F = c⁻¹ • (g • (c • F)) := by simp [mul_smul]
        _ = c⁻¹ • (g • P) := by rw [hc]
        _ = c⁻¹ • P := by rw [hgP]
        _ = F := by rw [← hc, inv_smul_smul]
    have hhF : (c⁻¹ * h * c) • F = F := by
      calc (c⁻¹ * h * c) • F = c⁻¹ • (h • (c • F)) := by simp [mul_smul]
        _ = c⁻¹ • (h • P) := by rw [hc]
        _ = c⁻¹ • P := by rw [hhP]
        _ = F := by rw [← hc, inv_smul_smul]
    have hcomm := hE _ _ hgF hhF
    have e : ⁅c⁻¹ * g * c, c⁻¹ * h * c⁆ = c⁻¹ * ⁅g, h⁆ * c := by
      simp only [commutatorElement_def]
      group
    rw [e] at hcomm
    have hconj := Subgroup.Normal.conj_mem ‹N.Normal› _ hcomm c
    have e2 : c * (c⁻¹ * ⁅g, h⁆ * c) * c⁻¹ = ⁅g, h⁆ := by group
    rwa [e2] at hconj
  let φ : A →* Equiv.Perm ↥S :=
    { toFun := fun a =>
        { toFun := fun x => ⟨a • (x : X), hSmap a x x.2⟩
          invFun := fun x => ⟨a⁻¹ • (x : X), hSmap a⁻¹ x x.2⟩
          left_inv := by
            intro x
            apply Subtype.ext
            simp
          right_inv := by
            intro x
            apply Subtype.ext
            simp }
      map_one' := by
        ext x
        simp
      map_mul' := by
        intro a b
        ext x
        simp [Equiv.Perm.mul_apply, mul_smul] }
  have hφ_apply : ∀ (a : A) (x : ↥S), ((φ a) x : X) = a • (x : X) := by
    intro a x
    rfl
  let e : ↥S ≃ Fin 3 := Fintype.equivFinOfCardEq (by
    rw [Fintype.card_coe]
    exact hS_card)
  let u : Equiv.Perm (Fin 3) := e.permCongrHom (φ α)
  let v : Equiv.Perm (Fin 3) := e.permCongrHom (φ β)
  let w : Equiv.Perm (Fin 3) := e.permCongrHom (φ κ)
  have hu3 : u ^ 3 = 1 := by
    have hα3S : ∀ x : ↥S, φ (α ^ 3) x = x := by
      intro x
      apply Subtype.ext
      rw [hφ_apply]
      exact hNfix (α ^ 3) hα x x.2
    have hφα3 : φ (α ^ 3) = 1 := Equiv.ext hα3S
    calc u ^ 3 = (e.permCongrHom (φ α)) ^ 3 := rfl
      _ = e.permCongrHom ((φ α) ^ 3) := (map_pow _ _ _).symm
      _ = e.permCongrHom (φ (α ^ 3)) := by
            rw [show (φ α) ^ 3 = φ (α ^ 3) from (map_pow φ α 3).symm]
      _ = 1 := by rw [hφα3, map_one]
  have hv : v * u * v⁻¹ = u⁻¹ := by
    have h := congrArg (fun a : A => e.permCongrHom (φ a)) hβ
    simpa [v, u, map_mul, map_inv] using h
  have hw2 : w * w = 1 := by
    have hκ2S : ∀ x : ↥S, φ (κ * κ) x = x := by
      intro x
      apply Subtype.ext
      rw [hφ_apply, mul_smul]
      have hx := x.2
      simp only [S, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with hx | hx | hx
      · rw [hx, hκF, hκF]
      · rw [hx, hκy, hκz]
      · rw [hx, hκz, hκy]
    have hφκ2 : φ (κ * κ) = 1 := Equiv.ext hκ2S
    calc w * w = e.permCongrHom (φ κ * φ κ) := (map_mul _ _ _).symm
      _ = e.permCongrHom (φ (κ * κ)) := by
            rw [show φ κ * φ κ = φ (κ * κ) from (map_mul φ κ κ).symm]
      _ = 1 := by rw [hφκ2, map_one]
  have hw1 : w ≠ 1 := by
    intro h
    have hφy : (φ κ) ⟨y, by simp [S]⟩ = ⟨z, by simp [S]⟩ := by
      apply Subtype.ext
      rw [hφ_apply, hκy]
    have hzy : e ⟨z, by simp [S]⟩ = e ⟨y, by simp [S]⟩ := by
      have h1 : w (e ⟨y, by simp [S]⟩) = e ⟨z, by simp [S]⟩ := by
        change e ((φ κ) (e.symm (e ⟨y, by simp [S]⟩))) = e ⟨z, by simp [S]⟩
        rw [e.symm_apply_apply, hφy]
      have h2 : w (e ⟨y, by simp [S]⟩) = e ⟨y, by simp [S]⟩ := by
        rw [h]
        rfl
      rw [← h1, h2]
    exact hyz (congrArg Subtype.val (e.injective hzy)).symm
  have hα_no_fix : ∀ P ∈ S, α • P ≠ P := by
    intro P hP hfixP
    let xP : ↥S := ⟨P, hP⟩
    have hfixu : ∃ i : Fin 3, u i = i := by
      refine ⟨e xP, ?_⟩
      change e ((φ α) (e.symm (e xP))) = e xP
      rw [e.symm_apply_apply]
      have hφfix : (φ α) xP = xP := by
        apply Subtype.ext
        rw [hφ_apply]
        exact hfixP
      rw [hφfix]
    have hu1 : u = 1 := fin3_cube_fixed_is_one u hu3 hfixu
    have hαfix : ∀ Q ∈ S, α • Q = Q := by
      intro Q hQ
      let xQ : ↥S := ⟨Q, hQ⟩
      have hφfix : (φ α) xQ = xQ := by
        apply e.injective
        have h := congrArg (fun p : Equiv.Perm (Fin 3) => p (e xQ)) hu1
        have h' : e ((φ α) xQ) = e xQ := by
          simpa [u, Equiv.permCongr_apply] using h
        exact h'
      calc α • Q = (((φ α) xQ : X)) := (hφ_apply α xQ).symm
        _ = Q := congrArg Subtype.val hφfix
    by_cases hβfix : ∃ Q ∈ S, β • Q = Q
    · obtain ⟨Q, hQ, hβQ⟩ := hβfix
      exact hcomm_ab (hcomm_of_fix β α Q hQ hβQ (hαfix Q hQ))
    · push Not at hβfix
      have hv_nofix : ∀ i : Fin 3, v i ≠ i := by
        intro i hi
        let x : ↥S := e.symm i
        have hφfix : (φ β) x = x := by
          apply e.injective
          have h' : e ((φ β) x) = e x := by
            simpa [v, Equiv.permCongr_apply, x] using hi
          exact h'
        have hβx : β • (x : X) = (x : X) := by
          calc β • (x : X) = ((φ β) x : X) := (hφ_apply β x).symm
            _ = (x : X) := congrArg Subtype.val hφfix
        exact hβfix x.val x.2 hβx
      obtain ⟨i, hi⟩ := fin3_mul_transposition_fixed v w hv_nofix hw2 hw1
      let xR : ↥S := e.symm i
      have hβκR : (β * κ) • (xR : X) = (xR : X) := by
        have hvw : v * w = e.permCongrHom (φ (β * κ)) := by
          simp [v, w, map_mul]
        have hi' : e ((φ (β * κ)) xR) = e xR := by
          have h := hi
          rw [hvw] at h
          simpa [Equiv.permCongr_apply, xR] using h
        have hφfix : (φ (β * κ)) xR = xR := e.injective hi'
        calc (β * κ) • (xR : X) = ((φ (β * κ)) xR : X) := (hφ_apply (β * κ) xR).symm
          _ = (xR : X) := congrArg Subtype.val hφfix
      have hαR : α • (xR : X) = (xR : X) := hαfix xR.val xR.2
      have h1 : ⁅β * κ, α⁆ ∈ N := hcomm_of_fix (β * κ) α xR.val xR.2 hβκR hαR
      have h2 : ⁅κ, α⁆ ∈ N := hcomm_of_fix κ α F (by simp [S]) hκF (hαfix F (by simp [S]))
      have hwN : κ⁻¹ * α * κ * α⁻¹ ∈ N := by
        have hc := Subgroup.Normal.conj_mem ‹N.Normal› (κ * α * κ⁻¹ * α⁻¹) h2 κ⁻¹
        have e1 : κ⁻¹ * (κ * α * κ⁻¹ * α⁻¹) * (κ⁻¹)⁻¹ = (κ⁻¹ * α * κ * α⁻¹)⁻¹ := by
          group
        rw [e1] at hc
        simpa using N.inv_mem hc
      have hfirst : (β * κ) * (κ⁻¹ * α * κ * α⁻¹) * (β * κ)⁻¹ ∈ N :=
        Subgroup.Normal.conj_mem ‹N.Normal› _ hwN (β * κ)
      have hprod : (β * κ) * (κ⁻¹ * α * κ * α⁻¹) * (β * κ)⁻¹ * ⁅β * κ, α⁆ ∈ N :=
        N.mul_mem hfirst h1
      have eid : ⁅β, α⁆ = (β * κ) * (κ⁻¹ * α * κ * α⁻¹) * (β * κ)⁻¹ * ⁅β * κ, α⁆ := by
        simp only [commutatorElement_def]
        group
      rw [← eid] at hprod
      exact hcomm_ab hprod
  have huf : ∀ i : Fin 3, u i ≠ i := by
    intro i hi
    let x : ↥S := e.symm i
    have hφfix : (φ α) x = x := by
      apply e.injective
      have h' : e ((φ α) x) = e x := by
        simpa [u, Equiv.permCongr_apply, x] using hi
      exact h'
    have hαx : α • (x : X) = (x : X) := by
      calc α • (x : X) = ((φ α) x : X) := (hφ_apply α x).symm
        _ = (x : X) := congrArg Subtype.val hφfix
    exact hα_no_fix x.val x.2 hαx
  obtain ⟨i0, hi0, hi0uniq⟩ := fin3_inv_of_threeCycle u v hu3 huf hv
  let i1 : Fin 3 := u i0
  let i2 : Fin 3 := u i1
  have hi01 : i0 ≠ i1 := (fin3_cycle_distinct u hu3 huf i0).1
  have hi12 : i1 ≠ i2 := (fin3_cycle_distinct u hu3 huf i0).2.1
  have hi02 : i0 ≠ i2 := (fin3_cycle_distinct u hu3 huf i0).2.2
  have hcover : ∀ j : Fin 3, j = i0 ∨ j = i1 ∨ j = i2 := fun j =>
    fin3_cycle_cover u hu3 huf i0 j
  have hv' : v * u = u⁻¹ * v := by
    calc v * u = (v * u * v⁻¹) * v := by group
      _ = u⁻¹ * v := by rw [hv]
  have hu_inv : u⁻¹ = u ^ 2 := by
    calc u⁻¹ = u⁻¹ * 1 := by simp
      _ = u⁻¹ * u ^ 3 := by rw [hu3]
      _ = u ^ 2 := by group
  have hv_i1 : v i1 = i2 := by
    have h := congrArg (fun p : Equiv.Perm (Fin 3) => p i0) hv'
    have h1 : v i1 = u⁻¹ i0 := by
      simpa [i1, Equiv.Perm.mul_apply, hi0] using h
    rw [hu_inv] at h1
    simpa [i2, i1, pow_two, Equiv.Perm.mul_apply] using h1
  have hv_i2 : v i2 = i1 := by
    have h := congrArg (fun p : Equiv.Perm (Fin 3) => p i1) hv'
    have h1 : v i2 = u⁻¹ i2 := by
      simpa [i2, Equiv.Perm.mul_apply, hv_i1] using h
    rw [hu_inv] at h1
    have h2 : (u ^ 2) i2 = i1 := by
      simpa [i2, pow_two, Equiv.Perm.mul_apply] using fin3_cube_apply u hu3 i1
    rw [h2] at h1
    exact h1
  let p : ↥S := e.symm i0
  let q : ↥S := e.symm i1
  let r : ↥S := e.symm i2
  have hu_apply : ∀ x : ↥S, u (e x) = e ((φ α) x) := by
    intro x
    simp [u, Equiv.permCongr_apply]
  have hv_apply : ∀ x : ↥S, v (e x) = e ((φ β) x) := by
    intro x
    simp [v, Equiv.permCongr_apply]
  have hφ_of_perm : ∀ (a : A) (x y : ↥S), e ((φ a) x) = e y → a • (x : X) = (y : X) := by
    intro a x y h
    calc a • (x : X) = ((φ a) x : X) := (hφ_apply a x).symm
      _ = (y : X) := congrArg Subtype.val (e.injective h)
  have hαp : α • (p : X) = (q : X) := by
    apply hφ_of_perm
    calc e ((φ α) p) = u (e p) := (hu_apply p).symm
      _ = u i0 := by rw [e.apply_symm_apply]
      _ = i1 := rfl
      _ = e q := by rw [e.apply_symm_apply]
  have hαq : α • (q : X) = (r : X) := by
    apply hφ_of_perm
    calc e ((φ α) q) = u (e q) := (hu_apply q).symm
      _ = u i1 := by rw [e.apply_symm_apply]
      _ = i2 := rfl
      _ = e r := by rw [e.apply_symm_apply]
  have hαr : α • (r : X) = (p : X) := by
    apply hφ_of_perm
    calc e ((φ α) r) = u (e r) := (hu_apply r).symm
      _ = u i2 := by rw [e.apply_symm_apply]
      _ = u (u (u i0)) := rfl
      _ = i0 := fin3_cube_apply u hu3 i0
      _ = e p := by rw [e.apply_symm_apply]
  have hβp : β • (p : X) = (p : X) := by
    apply hφ_of_perm
    calc e ((φ β) p) = v (e p) := (hv_apply p).symm
      _ = v i0 := by rw [e.apply_symm_apply]
      _ = i0 := hi0
      _ = e p := by rw [e.apply_symm_apply]
  have hβq : β • (q : X) = (r : X) := by
    apply hφ_of_perm
    calc e ((φ β) q) = v (e q) := (hv_apply q).symm
      _ = v i1 := by rw [e.apply_symm_apply]
      _ = i2 := hv_i1
      _ = e r := by rw [e.apply_symm_apply]
  have hβr : β • (r : X) = (q : X) := by
    apply hφ_of_perm
    calc e ((φ β) r) = v (e r) := (hv_apply r).symm
      _ = v i2 := by rw [e.apply_symm_apply]
      _ = i1 := hv_i2
      _ = e q := by rw [e.apply_symm_apply]
  have hp_ne_q : (p : X) ≠ (q : X) := by
    intro h
    have h' : p = q := Subtype.ext h
    have h'' : i0 = i1 := by
      calc i0 = e p := (e.apply_symm_apply i0).symm
        _ = e q := congrArg e h'
        _ = i1 := e.apply_symm_apply i1
    exact hi01 h''
  have hq_ne_r : (q : X) ≠ (r : X) := by
    intro h
    have h' : q = r := Subtype.ext h
    have h'' : i1 = i2 := by
      calc i1 = e q := (e.apply_symm_apply i1).symm
        _ = e r := congrArg e h'
        _ = i2 := e.apply_symm_apply i2
    exact hi12 h''
  have hp_ne_r : (p : X) ≠ (r : X) := by
    intro h
    have h' : p = r := Subtype.ext h
    have h'' : i0 = i2 := by
      calc i0 = e p := (e.apply_symm_apply i0).symm
        _ = e r := congrArg e h'
        _ = i2 := e.apply_symm_apply i2
    exact hi02 h''
  have hpqr_sub : ({(p : X), (q : X), (r : X)} : Set X) ⊆ (S : Set X) := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact p.2
    · exact q.2
    · exact r.2
  have hS_sub : (S : Set X) ⊆ ({(p : X), (q : X), (r : X)} : Set X) := by
    intro x hx
    have hx' := hcover (e ⟨x, hx⟩)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases hx' with h | h | h
    · left
      have h' : (⟨x, hx⟩ : ↥S) = p := e.injective (by rw [h]; exact (e.apply_symm_apply i0).symm)
      exact congrArg Subtype.val h'
    · right; left
      have h' : (⟨x, hx⟩ : ↥S) = q := e.injective (by rw [h]; exact (e.apply_symm_apply i1).symm)
      exact congrArg Subtype.val h'
    · right; right
      have h' : (⟨x, hx⟩ : ↥S) = r := e.injective (by rw [h]; exact (e.apply_symm_apply i2).symm)
      exact congrArg Subtype.val h'
  have hset : ({(p : X), (q : X), (r : X)} : Set X) = {F, y, z} := by
    have hS_set : (S : Set X) = ({F, y, z} : Set X) := by
      ext x
      simp [S]
    rw [← hS_set]
    exact Set.Subset.antisymm hpqr_sub hS_sub
  refine ⟨p, q, r, hset, hp_ne_q, hq_ne_r, hp_ne_r, hβp, hβq, hβr, ?_, ?_⟩
  · left
    exact ⟨hαp, hαq, hαr⟩
  · intro γ hγ
    let t : Equiv.Perm (Fin 3) := e.permCongrHom (φ γ)
    have ht_apply : ∀ x : ↥S, t (e x) = e ((φ γ) x) := by
      intro x
      simp [t, Equiv.permCongr_apply]
    have hcomm : t * v = v * t := by
      have h := congrArg (fun a : A => e.permCongrHom (φ a)) hγ
      simpa [t, v, map_mul] using h
    have ht0 : t i0 = i0 := by
      have h := congrArg (fun s : Equiv.Perm (Fin 3) => s i0) hcomm
      have hfix : v (t i0) = t i0 := by
        simpa [Equiv.Perm.mul_apply, hi0] using h.symm
      exact hi0uniq (t i0) hfix
    have hγ_smul_of_index : ∀ (x y : ↥S) (i j : Fin 3),
        e x = i → e y = j → t i = j → γ • (x : X) = (y : X) := by
      intro x y i j hx hy hij
      apply hφ_of_perm
      calc e ((φ γ) x) = t (e x) := (ht_apply x).symm
        _ = t i := by rw [hx]
        _ = j := hij
        _ = e y := by rw [hy]
    have hγp : γ • (p : X) = (p : X) :=
      hγ_smul_of_index p p i0 i0 (e.apply_symm_apply i0) (e.apply_symm_apply i0) ht0
    obtain ⟨ht1, ht2⟩ | ⟨ht1, ht2⟩ :=
      fin3_fixed_index_transposition t i0 i1 i2 hi01 hi02 hi12 hcover ht0
    · left
      exact ⟨hγp,
        hγ_smul_of_index q q i1 i1 (e.apply_symm_apply i1) (e.apply_symm_apply i1) ht1,
        hγ_smul_of_index r r i2 i2 (e.apply_symm_apply i2) (e.apply_symm_apply i2) ht2⟩
    · right
      exact ⟨hγp,
        hγ_smul_of_index q r i1 i2 (e.apply_symm_apply i1) (e.apply_symm_apply i2) ht1,
        hγ_smul_of_index r q i2 i1 (e.apply_symm_apply i2) (e.apply_symm_apply i1) ht2⟩

end Abstract

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.D4
