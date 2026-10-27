module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec8BCase

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace Sec8

open Sec7

namespace MB

@[expose] def zkList : List MB := [1, z, k, z * k]

@[expose] def w₁' (c : MB) : MB := w₁ * y * c * (z * u)⁻¹

@[expose] def e3gens (c : MB) : List MB := [z, z * u, z * k, t * w₁' c]

theorem e3_fact : ∀ c ∈ zkList, InSpan (e3gens c) (w₂ * z * w₂⁻¹) ∧
    InSpan (e3gens c) (w₂ * (y * w₁' c) * w₂⁻¹) ∧ InSpan (e3gens c) (w₂ * (z * u * t) * w₂⁻¹) ∧
    InSpan (e3gens c) (w₂ * (z * k) * w₂⁻¹) := by
  decide +kernel

end MB

variable {X : Type} [Group X] [Finite X] {S : A7Base X} {F : S.Frame} {T₁ : Subgroup X}

@[expose] noncomputable def E0t (F : S.Frame) (a : X) : Subgroup X :=
  S.E0 F.yF F.kF ⊔ zpowers (S.t * a)

namespace BData

variable (A : BData S F T₁)

@[expose] noncomputable def P₂ : IPair S F T₁ where
  V := A.V₂
  W := A.V₁
  hyy := Or.inr (by
    change F.yF = S.z * (F.xF * (F.xF * F.yF))
    rw [xF_mul_xyF, ← mul_assoc, z_mul_z, one_mul])
  hkk := by
    change F.kF = S.z * (S.z * F.kF)
    rw [← mul_assoc, z_mul_z, one_mul]
  h4 := A.h4

noncomputable def ι₂ : MB →* X := A.P₂.ιB A.hq₂

theorem ι₂_w₂ : A.ι₂ MB.w₂ = A.D₂.w₂ := (IPair.ιB_spec (P := A.P₂) A.hq₂).1
theorem ι₂_u : A.ι₂ MB.u = A.D₂.u := (IPair.ιB_spec (P := A.P₂) A.hq₂).2.1
theorem ι₂_w₁ : A.ι₂ MB.w₁ = A.V₂.w₁N := (IPair.ιB_spec (P := A.P₂) A.hq₂).2.2.1
theorem ι₂_z : A.ι₂ MB.z = S.z := (IPair.ιB_spec (P := A.P₂) A.hq₂).2.2.2.2.1
theorem ι₂_y : A.ι₂ MB.y = F.xF * F.yF := (IPair.ιB_spec (P := A.P₂) A.hq₂).2.2.2.2.2.1
theorem ι₂_t : A.ι₂ MB.t = S.t := (IPair.ιB_spec (P := A.P₂) A.hq₂).2.2.2.2.2.2.1
theorem ι₂_k : A.ι₂ MB.k = S.z * F.kF := (IPair.ιB_spec (P := A.P₂) A.hq₂).2.2.2.2.2.2.2

theorem ι₂_zu : A.ι₂ (MB.z * MB.u) = F.yF := by
  rw [map_mul, A.ι₂_z, A.ι₂_u, A.hu₂, ← mul_assoc, z_mul_z, one_mul]

theorem ι₂_zk : A.ι₂ (MB.z * MB.k) = F.kF := by
  rw [map_mul, A.ι₂_z, A.ι₂_k, ← mul_assoc, z_mul_z, one_mul]

theorem exists_w₁_ι₂ : ∃ c ∈ MB.zkList, A.V₁.w₁N = A.ι₂ (MB.w₁' c) := by
  obtain ⟨c, hc, hw⟩ := A.P₁.exists_w₁W_same (A.hq₁.trans A.hq₂.symm)
  have e1 : A.P₁.V.w₁c = A.V₁.w₁N * F.yF := ISide.w₁c_of_homoc _ A.hq₁
  have e2 : A.P₁.W.w₁c = A.V₂.w₁N * (F.xF * F.yF) := ISide.w₁c_of_homoc _ A.hq₂
  rw [e1, e2] at hw
  have hw' : A.V₁.w₁N = A.V₂.w₁N * (F.xF * F.yF) * c * F.yF⁻¹ := by
    rw [← hw]; group
  change c ∈ (zpowers S.z ⊔ zpowers A.V₂.ki : Subgroup X) at hc
  have hk2 : A.V₂.ki = S.z * F.kF := rfl
  have key : ∀ c' : MB, A.ι₂ c' = c → A.V₁.w₁N = A.ι₂ (MB.w₁' c') := by
    intro c' hc'
    rw [hw', MB.w₁', map_mul, map_mul, map_mul, map_inv, A.ι₂_w₁, A.ι₂_y, A.ι₂_zu, hc']
  rcases A.V₂.eq_of_mem_zk hc with rfl | rfl | rfl | rfl
  · exact ⟨1, by simp [MB.zkList], key 1 (map_one _)⟩
  · exact ⟨MB.z, by simp [MB.zkList], key MB.z A.ι₂_z⟩
  · exact ⟨MB.k, by simp [MB.zkList], key MB.k (by rw [A.ι₂_k]; rfl)⟩
  · exact ⟨MB.z * MB.k, by simp [MB.zkList], key _ (by rw [map_mul, A.ι₂_z, A.ι₂_k]; rfl)⟩

theorem conj_E₂_le :
    F.E₂.map (MulAut.conj (A.D₂.w₂ * A.D₁.w₂)).toMonoidHom ≤ E0t F A.V₁.w₁N := by
  obtain ⟨c, hc, hw⟩ := A.exists_w₁_ι₂
  obtain ⟨h1, h2, h3, h4⟩ := MB.e3_fact c hc
  have hgens : ∀ g ∈ MB.e3gens c, A.ι₂ g ∈ E0t F A.V₁.w₁N := by
    intro g hg
    simp only [MB.e3gens, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · rw [A.ι₂_z]; exact mem_sup_left (z_mem_E0 _ _)
    · rw [A.ι₂_zu]; exact mem_sup_left (yi_mem_E0 _ _)
    · rw [A.ι₂_zk]; exact mem_sup_left (ki_mem_E0 _ _)
    · rw [map_mul, A.ι₂_t, ← hw]; exact mem_sup_right (mem_zpowers _)
  have hconj : ∀ x : MB, A.D₂.w₂ * A.ι₂ x * A.D₂.w₂⁻¹ = A.ι₂ (MB.w₂ * x * MB.w₂⁻¹) := by
    intro x; rw [map_mul, map_mul, map_inv, A.ι₂_w₂]
  rw [A7Base.Frame.E₂, A7Base.E, MonoidHom.map_closure, closure_le]
  rintro _ ⟨e, he, rfl⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, SetLike.mem_coe]
  have hw₂₁ : ∀ e : X, (A.D₂.w₂ * A.D₁.w₂) * e * (A.D₂.w₂ * A.D₁.w₂)⁻¹ =
      A.D₂.w₂ * (A.D₁.w₂ * e * A.D₁.w₂⁻¹) * A.D₂.w₂⁻¹ := fun e => by group
  have e_z : A.D₁.w₂ * S.z * A.D₁.w₂⁻¹ = A.ι₂ MB.z := by
    rw [A.ι₂_z]; exact A.V₁.w₂_conj_E0 (z_mem_E0 _ _)
  have e_k : A.D₁.w₂ * F.kF * A.D₁.w₂⁻¹ = A.ι₂ (MB.z * MB.k) := by
    rw [A.ι₂_zk]; exact A.V₁.w₂_conj_E0 (ki_mem_E0 _ _)
  have e_t : A.D₁.w₂ * S.t * A.D₁.w₂⁻¹ = A.ι₂ (MB.z * MB.u * MB.t) := by
    rw [map_mul, A.ι₂_zu, A.ι₂_t]; exact A.V₁.w₂_conj_t'
  have e_u : A.D₁.w₂ * (F.xF * F.yF) * A.D₁.w₂⁻¹ = A.ι₂ (MB.y * MB.w₁' c) := by
    have h := A.V₁.w₂_conj_u
    change A.D₁.w₂ * A.D₁.u * A.D₁.w₂⁻¹ = A.D₁.u * A.V₁.w₁N at h
    rw [A.hu₁] at h
    rw [h, map_mul, A.ι₂_y, hw]
  have m_z : (A.D₂.w₂ * A.D₁.w₂) * S.z * (A.D₂.w₂ * A.D₁.w₂)⁻¹ ∈ E0t F A.V₁.w₁N := by
    rw [hw₂₁, e_z, hconj]; exact map_mem_of_inSpan _ h1 hgens
  have m_u : (A.D₂.w₂ * A.D₁.w₂) * (F.xF * F.yF) * (A.D₂.w₂ * A.D₁.w₂)⁻¹ ∈
      E0t F A.V₁.w₁N := by
    rw [hw₂₁, e_u, hconj]; exact map_mem_of_inSpan _ h2 hgens
  have m_t : (A.D₂.w₂ * A.D₁.w₂) * S.t * (A.D₂.w₂ * A.D₁.w₂)⁻¹ ∈ E0t F A.V₁.w₁N := by
    rw [hw₂₁, e_t, hconj]; exact map_mem_of_inSpan _ h3 hgens
  have m_k : (A.D₂.w₂ * A.D₁.w₂) * F.kF * (A.D₂.w₂ * A.D₁.w₂)⁻¹ ∈ E0t F A.V₁.w₁N := by
    rw [hw₂₁, e_k, hconj]; exact map_mem_of_inSpan _ h4 hgens
  have hB : S.B ≤ (E0t F A.V₁.w₁N).comap (MulAut.conj (A.D₂.w₂ * A.D₁.w₂)).toMonoidHom := by
    rw [A.V₁.B_eq]
    refine sup_le (sup_le (zpowers_le.mpr ?_) (zpowers_le.mpr ?_)) (zpowers_le.mpr ?_)
    · exact m_z
    · exact m_k
    · exact m_t
  rcases he with rfl | rfl | rfl | rfl
  · exact m_z
  · exact m_u
  · exact m_t
  · exact hB k_mem_B

theorem not_conj_E₃ (hnc : ¬ SubConj F.E₁ F.E₂) {g : X}
    (hg : F.E₁.map (MulAut.conj g).toMonoidHom = E0t F A.V₁.w₁N) : False := by
  set h := A.D₂.w₂ * A.D₁.w₂ with hh
  have hle := A.conj_E₂_le
  rw [← hg] at hle
  have hcard : Nat.card (F.E₂.map (MulAut.conj h).toMonoidHom) =
      Nat.card (F.E₁.map (MulAut.conj g).toMonoidHom) := by
    have hE₁ : Nat.card F.E₁ = 16 := (isRefl_yF F).card_E
    have hE₂ : Nat.card F.E₂ = 16 := (isRefl_xyF F).card_E
    rw [card_map_of_injective (MulAut.conj h).injective,
      card_map_of_injective (MulAut.conj g).injective, hE₁, hE₂]
  have heq := Subgroup.eq_of_le_of_card_ge hle hcard.ge
  apply hnc
  refine ⟨h⁻¹ * g, ?_⟩
  rw [show (MulAut.conj (h⁻¹ * g)).toMonoidHom =
    (MulAut.conj h⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom by
      ext x; simp [mul_assoc], ← map_map, ← heq, map_map]
  rw [show (MulAut.conj h⁻¹).toMonoidHom.comp (MulAut.conj h).toMonoidHom = MonoidHom.id X by
    ext x; simp [mul_assoc], map_id]

end BData

end Sec8

end CFSG.ComponentClassification.HSFLit
