module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx3

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
open scoped commutatorElement Pointwise

theorem conjugate_eq_comap {G : Type} [Group G] (H : Subgroup G) (g : G) :
    conjugate H g = H.comap (MulAut.conj g).toMonoidHom := (cj_eq_conjugate H g).symm

theorem mem_conjugate_iff {G : Type} [Group G] {H : Subgroup G} {g x : G} :
    x ∈ conjugate H g ↔ g * x * g⁻¹ ∈ H := by
  rw [conjugate_eq_comap]; exact Iff.rfl

namespace Setup8

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ W₁ W₂ U : Subgroup G} {u h : G}

theorem hz_mem_U (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) : h * z * h⁻¹ ∈ U :=
  ((Subgroup.mem_normalizer_iff.1 hs.h_norm) z).1 hs.z_mem

theorem hz_inv_mem_U (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) : h⁻¹ * z * h ∈ U := by
  have := ((Subgroup.mem_normalizer_iff.1 (inv_mem hs.h_norm)) z).1 hs.z_mem
  simpa using this

theorem V₁h_le_W (hII : II4_4_4_center) (hq : II4_4_quat) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) :
    conjugate (Vof S K₁ W₂) h ≤ Wsub S U := by
  intro x hx
  have hx' : h * x * h⁻¹ ∈ Vof S K₁ W₂ := mem_conjugate_iff.1 hx
  exact ((Subgroup.mem_normalizer_iff.1 hs.h_W) x).2 (hs.V₁_le_W hII hq hx')

theorem V₁h_le_S1 (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) : conjugate (Vof S K₁ W₂) h ≤ S1 S K₁ := by
  intro x hx
  have hx' : h * x * h⁻¹ ∈ Vof S K₁ W₂ := mem_conjugate_iff.1 hx
  have hxW : x ∈ Wsub S U := hs.V₁h_le_W hII hq hx
  refine ⟨hxW.1, ?_⟩
  have hvW : h * x * h⁻¹ ∈ Wsub S U := hs.V₁_le_W hII hq hx'
  have hxe : x = h⁻¹ * (h * x * h⁻¹) * h := by group
  by_cases hvz : h * x * h⁻¹ ∈ zpowers z
  · rcases (M.mem_zpowers_of_sq hs.z_sq).1 hvz with h1 | h1
    · rw [hxe, h1]
      simp
    · rw [hxe, h1]
      exact (hs.U_le_S1 hII hs.hz_inv_mem_U).2
  · have htU : h * z * h⁻¹ ∈ U := hs.hz_mem_U
    have htC : h * z * h⁻¹ ∈ centralizer ({z} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact hs.four_comm z hs.z_mem _ htU
    have htN : h * z * h⁻¹ ∈ normalizer (K₁ : Set G) := (hs.U_le_S1 hII htU).2
    have hxK : h * x * h⁻¹ ∈ K₁ := hx'.2.2
    have hxp : IsPGroup 2 ↥(zpowers (h * x * h⁻¹)) :=
      (hs.S_pgroup hII).to_le (zpowers_le.2 hx'.2.1)
    have hcomm : (h * x * h⁻¹) * (h * z * h⁻¹) = (h * z * h⁻¹) * (h * x * h⁻¹) :=
      ((Subgroup.mem_centralizer_iff.1 hvW.2) _ htU).symm
    have key := rec1b_of_std hII hrec hs.fused.std (h * z * h⁻¹) h⁻¹ (by simp) htC K₁ K₁
      (Or.inl rfl) (Or.inl rfl) htN _ hxK hxp hvz hcomm
    have := M.mem_normalizer_cj key
    rw [hxe]
    simpa [mul_assoc] using this

theorem P_le_norm_K₁h (hII : II4_4_4_center) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {K X : Subgroup G} (hK : K = K₁ ∨ K = K₂)
    (hXP : X ≤ Pof S K) (hXW : X ≤ Wsub S U) :
    ∀ c ∈ X, c ∈ normalizer (conjugate K₁ h : Set G) ∨ c ∈ zpowers z := by
  intro c hc
  by_cases hcz : c ∈ zpowers z
  · exact Or.inr hcz
  left
  have htU : h⁻¹ * z * h ∈ U := hs.hz_inv_mem_U
  have htC : h⁻¹ * z * h ∈ centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact hs.four_comm z hs.z_mem _ htU
  have htN : h⁻¹ * z * h ∈ normalizer (K : Set G) := by
    have := (hs.U_le_S1 hII htU).2
    rcases hK with rfl | rfl
    · exact this
    · exact (hs.norm_iff hII (hs.U_le_S hII htU)).1 this
  have hcK : c ∈ K := (hXP hc).2
  have hcp : IsPGroup 2 ↥(zpowers c) := (hs.S_pgroup hII).to_le (zpowers_le.2 (hXP hc).1)
  have hcomm : c * (h⁻¹ * z * h) = (h⁻¹ * z * h) * c :=
    ((Subgroup.mem_centralizer_iff.1 (hXW hc).2) _ htU).symm
  have key := rec1b_of_std hII hrec hs.fused.std (h⁻¹ * z * h) h rfl htC K K₁ hK (Or.inl rfl) htN c
    hcK hcp hcz hcomm
  rw [← cj_eq_conjugate]
  exact key

theorem comm_V (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {K X : Subgroup G} (hK : K = K₁ ∨ K = K₂)
    (hXP : X ≤ Pof S K) (hXW : X ≤ Wsub S U)
    (hXn : ∀ x ∈ S1 S K₁, ∀ y ∈ X, x * y * x⁻¹ ∈ X) :
    ∀ c ∈ X, ∀ v ∈ conjugate (Vof S K₁ W₂) h, c * v = v * c := by
  have hM := hs.m4 hII
  have hVS := hs.V₁h_le_S1 hII hq hrec
  intro c hc v hv
  rcases hs.P_le_norm_K₁h hII hrec hK hXP hXW c hc with hcn | hcz
  ·
    have hvK : v ∈ conjugate K₁ h := by
      rw [mem_conjugate_iff]
      have : h * v * h⁻¹ ∈ Vof S K₁ W₂ := mem_conjugate_iff.1 hv
      exact this.2.2
    have h1 : c * v * c⁻¹ ∈ conjugate K₁ h := by
      have := (Subgroup.mem_normalizer_iff.1 hcn) v
      exact this.1 hvK
    have h2 : c * v * c⁻¹ * v⁻¹ ∈ conjugate K₁ h := mul_mem h1 (inv_mem hvK)
    have h3 : c * v * c⁻¹ * v⁻¹ ∈ X := by
      have : c * (v * c⁻¹ * v⁻¹) ∈ X :=
        mul_mem hc (hXn v (hVS hv) c⁻¹ (inv_mem hc))
      simpa [mul_assoc] using this
    have hinf : conjugate K₁ h ⊓ X = ⊥ := by
      refine Basic.conj_inf_bot (z := z) (h := h) (P := K₁) (Q := X) (V₁ := K₁) ?_ ?_ le_rfl
        hs.h_move ?_ ?_
      · intro x hx hx2; exact hM.inv_comp (Or.inl rfl) hx hx2
      · intro x hx hx2; exact hM.inv_comp hK ((hXP hx).2) hx2
      · intro x
        exact mem_conjugate_iff
      · exact (hs.S_pgroup hII).to_le ((inf_le_right : conjugate K₁ h ⊓ X ≤ X).trans
          ((hXP.trans inf_le_left)))
    have h4 : c * v * c⁻¹ * v⁻¹ ∈ conjugate K₁ h ⊓ X := ⟨h2, h3⟩
    rw [hinf, Subgroup.mem_bot] at h4
    calc c * v = (c * v * c⁻¹ * v⁻¹) * (v * c) := by group
      _ = v * c := by rw [h4, one_mul]
  ·
    have hvW : v ∈ Wsub S U := hs.V₁h_le_W hII hq hv
    have hzv : z * v = v * z := (Subgroup.mem_centralizer_iff.1 hvW.2) z hs.z_mem
    rcases (M.mem_zpowers_of_sq hs.z_sq).1 hcz with rfl | rfl
    · simp
    · exact hzv

end Setup8

end CFSG.GH74.GLS.Stage1.Thm3.Sec8
