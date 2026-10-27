module

public import CFSG.GH74.GLS.Stage2.Local.P34OneAut
public import CFSG.LocalAnalysis.QuasithinUnique.CompNormSylow
public import CFSG.GH74.GLS.Stage2.Final.ModelSPMain

public section

namespace CFSG.GH74.GLS.Stage2.Local.P34

open Subgroup CFSG.GH74.L5U5 CFSG.GH74.GLS.Stage2.Final.ModelSp CFSG.GH74.GLS.LU.Local
  CFSG.Assembly.LowTwoRank
open CFSG.GH74.GLS.Stage2.Final.ModelBlock (PG mkP yP K1 K2 spSyl_PG luComps_PG exists_equiv_sylow
  orderOf_yP)

section Act

variable {X : Type} [Group X] {J : Subgroup X} [J.Normal] {N : Type} [Group N] (Φ : ↥J ≃* N)

@[expose] noncomputable def actHom : X →* MulAut N :=
  (MulAut.congr Φ).toMonoidHom.comp MulAut.conjNormal

theorem actHom_apply (x : X) (n : N) :
    actHom Φ x n = Φ (MulAut.conjNormal x (Φ.symm n)) := by
  simp [actHom, MulAut.congr_apply]

theorem actHom_apply_Φ (x : X) (j : ↥J) : actHom Φ x (Φ j) = Φ (MulAut.conjNormal x j) := by
  rw [actHom_apply, Φ.symm_apply_apply]

theorem actHom_of_mem (j : ↥J) : actHom Φ (j : X) = MulAut.conj (Φ j) := by
  ext n
  rw [actHom_apply, MulAut.conj_apply, ← Φ.apply_symm_apply n, Φ.symm_apply_apply, ← map_inv,
    ← map_mul, ← map_mul]
  congr 1

end Act

theorem center_psp4_trivial {F : Type} [Field F] [Finite F] (h4 : 4 ≤ Nat.card F) {J : Type}
    [Group J] (e : J ≃* StatedProj (StatedSp 2 F)) {x : J} (hx : ∀ y : J, x * y = y * x) :
    x = 1 := by
  obtain ⟨-, hs, a, b, hab⟩ := CFSG.LieType.Universal.Symplectic.isQuasisimple (n := 2) (F := F)
    (by norm_num) (Or.inl (Or.inr h4))
  have := hs
  let c := CFSG.LieType.Universal.Symplectic.centerQuotientEquiv 2 F
  set x' := c.symm (e x) with hx'
  have hcen : x' ∈ Subgroup.center (StatedSp 2 F ⧸ Subgroup.center (StatedSp 2 F)) := by
    rw [Subgroup.mem_center_iff]
    intro y
    have h1 := hx (e.symm (c y))
    have h2 := congrArg (fun w => c.symm (e w)) h1
    simp only [map_mul, MulEquiv.apply_symm_apply, MulEquiv.symm_apply_apply] at h2
    exact h2.symm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (Subgroup.center (StatedSp 2 F ⧸ Subgroup.center (StatedSp 2 F))) with h | h
  · rw [h, Subgroup.mem_bot] at hcen
    have : e x = 1 := by
      have h3 := congrArg c hcen
      simpa [hx'] using h3
    exact e.injective (by rw [this, map_one])
  · exfalso
    have ha : a ∈ Subgroup.center (StatedSp 2 F ⧸ Subgroup.center (StatedSp 2 F)) := h ▸ Subgroup.mem_top a
    exact hab (Subgroup.mem_center_iff.1 ha b).symm

theorem exists_outer_involution
    {X : Type} [Group X] [Finite X] {J : Subgroup X} [J.Normal]
    {F : Type} [Field F] [Finite F]
    (hq8 : Nat.card F % 8 = 3 ∨ Nat.card F % 8 = 5) (h5 : 5 ≤ Nat.card F)
    (e : ↥J ≃* StatedProj (StatedSp 2 F))
    (hCJ : ∀ x : X, (∀ j ∈ J, x * j = j * x) → x ∈ J)
    (T : Sylow 2 X) {z' : X} (hzJ : z' ∈ J) (hz2 : orderOf z' = 2)
    (hzT : z' ∈ (T : Subgroup X)) (hzc : ∀ t ∈ (T : Subgroup X), t * z' = z' * t)
    (hTJ : ¬ (T : Subgroup X) ≤ J) :
    ∃ (E₁ E₂ : Subgroup ↥J) (u : X),
      LUComps ↥J (Nat.card F) ⟨z', hzJ⟩ E₁ E₂ ∧
      u * u = 1 ∧ u ∉ J ∧ u * z' = z' * u ∧
      (∀ x ∈ E₁, MulAut.conjNormal u x ∈ E₁) ∧ (∀ x ∈ E₂, MulAut.conjNormal u x ∈ E₂) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : Odd (Nat.card F) := by rcases hq8 with h | h <;> exact Nat.odd_iff.2 (by omega)
  have h2 : (2 : F) ≠ 0 := CFSG.GH74.GLS.Stage2.Final.ModelBlock.two_ne_zero_of_odd_card hodd
  have h4 : 4 ≤ Nat.card F := by omega
  have hG := CFSG.GH74.GLS.Stage2.Final.ModelBlock.goodModel_sp h2 h5
  obtain ⟨S₀, hS₀⟩ := spSyl_PG h2 h5
  have hLU := luComps_PG hG (Nat.card F)
    (CFSG.GH74.GLS.Stage2.Final.ModelBlock.hasSL2Model_H2_sp F)
  obtain ⟨T₀, hT₀⟩ := CFSG.QuasithinUnique.exists_sylow_eq_subgroupOf_of_normal T J
  let e' : ↥J ≃* PG (ModelData.sp F) := e.trans (spEquiv F)
  obtain ⟨Φ, hΦ⟩ := exists_equiv_sylow e' S₀ T₀
  set z₀ : ↥J := ⟨z', hzJ⟩ with hz₀
  have hz₀T : z₀ ∈ (T₀ : Subgroup ↥J) := by
    rw [hT₀]; exact Subgroup.mem_subgroupOf.2 hzT
  have hz₀c : ∀ t ∈ (T₀ : Subgroup ↥J), t * z₀ = z₀ * t := by
    intro t ht
    rw [hT₀] at ht
    exact Subtype.ext (hzc (t : X) (Subgroup.mem_subgroupOf.1 ht))
  have hz₀2 : orderOf z₀ = 2 := by
    rw [← Subgroup.orderOf_coe]; exact hz2
  have hcen := (CFSG.GH74.GLS.Stage2.Final.ModelBlock.centerIs_iff _ _).1 hS₀.z_cen
  have hΦz : Φ z₀ = yP (ModelData.sp F) := by
    have hmem : Φ z₀ ∈ (S₀ : Subgroup (PG (ModelData.sp F))) := by
      rw [← hΦ]; exact Subgroup.mem_map_of_mem _ hz₀T
    have hcomm : ∀ s ∈ (S₀ : Subgroup (PG (ModelData.sp F))), s * Φ z₀ = Φ z₀ * s := by
      intro s hs
      rw [← hΦ] at hs
      obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 hs
      show Φ t * Φ z₀ = Φ z₀ * Φ t
      rw [← map_mul, ← map_mul, hz₀c t ht]
    have h1 := (hcen (Φ z₀)).1 ⟨hmem, hcomm⟩
    have hord : orderOf (Φ z₀) = 2 := by rw [MulEquiv.orderOf_eq]; exact hz₀2
    exact CFSG.GH74.GLS.Stage2.Final.ModelBlock.eq_of_mem_zpowers_of_orderOf_two
      (CFSG.GH74.GLS.Stage2.Final.ModelBlock.orderOf_yP _ h2) hord h1
  have hΘker : ∀ x : X, actHom Φ x = 1 → x = 1 := by
    intro x hx
    have hxn : ∀ n, actHom Φ x n = n := fun n => by rw [hx]; rfl
    have hxJ : x ∈ J := by
      refine hCJ x fun j hj => ?_
      have h1 := hxn (Φ ⟨j, hj⟩)
      rw [actHom_apply_Φ] at h1
      have h2 := congrArg (fun w : ↥J => (w : X)) (Φ.injective h1)
      simp only [MulAut.conjNormal_apply] at h2
      calc x * j = x * j * x⁻¹ * x := by group
        _ = j * x := by rw [h2]
    have hx1 : (⟨x, hxJ⟩ : ↥J) = 1 := by
      refine center_psp4_trivial h4 e fun y => ?_
      have h1 := hxn (Φ y)
      rw [actHom_apply_Φ] at h1
      have h2 := Φ.injective h1
      apply Subtype.ext
      have h5 := congrArg (fun w : ↥J => (w : X)) h2
      simp only [MulAut.conjNormal_apply] at h5
      calc x * (y : X) = x * y * x⁻¹ * x := by group
        _ = (y : X) * x := by rw [h5]
    exact congrArg Subtype.val hx1
  have hΘinj : Function.Injective (actHom Φ) := (injective_iff_map_eq_one _).2 hΘker
  have hnotInner : ∀ x : X, x ∉ J → actHom Φ x ∉
      (MulAut.conj : PG (ModelData.sp F) →* MulAut (PG (ModelData.sp F))).range := by
    rintro x hx ⟨n, hn⟩
    apply hx
    have : actHom Φ x = actHom Φ ((Φ.symm n : ↥J) : X) := by
      rw [actHom_of_mem, Φ.apply_symm_apply, hn]
    rw [hΘinj this]
    exact (Φ.symm n).2
  obtain ⟨s, hsT, hsJ⟩ : ∃ s ∈ (T : Subgroup X), s ∉ J := by
    by_contra hcon
    push Not at hcon
    exact hTJ hcon
  obtain ⟨m, hm⟩ : ∃ m : ℕ, s ^ 2 ^ m = 1 := by
    obtain ⟨k, hk⟩ := T.isPGroup' ⟨s, hsT⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hinn : (MulAut.conj : PG (ModelData.sp F) →* MulAut (PG (ModelData.sp F))).range ≤
      (actHom Φ).range := by
    rintro _ ⟨n, rfl⟩
    refine ⟨((Φ.symm n : ↥J) : X), ?_⟩
    rw [actHom_of_mem, Φ.apply_symm_apply]
  obtain ⟨τ₀, hτ₀Γ, hτ₀n, hτ₀sq, hτ₀y, hτ₀K1, hτ₀K2⟩ := exists_outer_involution_aut hq8
    (actHom Φ).range hinn ⟨s, rfl⟩ (m := m) (by rw [← map_pow, hm, map_one]) (hnotInner s hsJ)
  obtain ⟨u, rfl⟩ := hτ₀Γ
  have hLU' := CFSG.GH74.GLS.Stage2.Final.ModelLUT.luComps_map Φ.symm hLU
  rw [show Φ.symm (yP (ModelData.sp F)) = z₀ by rw [← hΦz, Φ.symm_apply_apply]] at hLU'
  have hnorm : ∀ K : Subgroup (PG (ModelData.sp F)), (∀ x ∈ K, actHom Φ u x ∈ K) →
      ∀ x ∈ K.map Φ.symm.toMonoidHom, MulAut.conjNormal u x ∈ K.map Φ.symm.toMonoidHom := by
    intro K hK x hx
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hx
    refine Subgroup.mem_map.2 ⟨actHom Φ u k, hK k hk, ?_⟩
    rw [actHom_apply]
    exact Φ.symm_apply_apply _
  refine ⟨_, _, u, hLU', ?_, ?_, ?_, hnorm _ hτ₀K1, hnorm _ hτ₀K2⟩
  · exact hΘinj (by rw [map_mul, map_one]; exact hτ₀sq)
  · intro huJ
    apply hτ₀n
    refine ⟨Φ ⟨u, huJ⟩, ?_⟩
    rw [← actHom_of_mem Φ ⟨u, huJ⟩]
  · have h1 := hτ₀y
    rw [← hΦz, actHom_apply_Φ] at h1
    have h2 := congrArg (fun w : ↥J => (w : X)) (Φ.injective h1)
    simp only [MulAut.conjNormal_apply, hz₀] at h2
    calc u * z' = u * z' * u⁻¹ * u := by group
      _ = z' * u := by rw [h2]

end CFSG.GH74.GLS.Stage2.Local.P34
