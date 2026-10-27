module

public import CFSG.LargeExtraspecial.S3Basic
public import CFSG.LargeExtraspecial.Types

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.Literature.FSmith
  CFSG.RankThree.OrthogonalInvolutions

section TypeTransport

variable {V V' : Type*} [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup V']
  [Module (ZMod 2) V'] {q : QuadraticForm (ZMod 2) V} {q' : QuadraticForm (ZMod 2) V'}

theorem commSpace_eq_map_of_intertwine (φ : V ≃ₗ[ZMod 2] V') {t : V ≃ₗ[ZMod 2] V}
    {t' : V' ≃ₗ[ZMod 2] V'} (ht : ∀ v, t' (φ v) = φ (t v)) :
    commSpace t' = (commSpace t).map (φ : V →ₗ[ZMod 2] V') := by
  ext x
  rw [mem_commSpace, Submodule.mem_map]
  constructor
  · rintro ⟨v', rfl⟩
    refine ⟨t (φ.symm v') - φ.symm v', sub_mem_commSpace t _, ?_⟩
    rw [LinearEquiv.coe_coe, map_sub, ← ht, LinearEquiv.apply_symm_apply]
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨v, rfl⟩ := mem_commSpace.mp hy
    exact ⟨φ v, by rw [ht, LinearEquiv.coe_coe, map_sub]⟩

theorem iso_of_intertwine (φ : V ≃ₗ[ZMod 2] V') (hφ : ∀ v, q' (φ v) = q v)
    {t : V ≃ₗ[ZMod 2] V} {t' : V' ≃ₗ[ZMod 2] V'} (ht : ∀ v, t' (φ v) = φ (t v))
    (h : ∀ v, q (t v) = q v) : ∀ v', q' (t' v') = q' v' := fun v' => by
  obtain ⟨v, rfl⟩ := φ.surjective v'
  rw [ht, hφ, hφ, h]

theorem ne_one_of_intertwine (φ : V ≃ₗ[ZMod 2] V') {t : V ≃ₗ[ZMod 2] V}
    {t' : V' ≃ₗ[ZMod 2] V'} (ht : ∀ v, t' (φ v) = φ (t v)) (h : t ≠ 1) : t' ≠ 1 := by
  intro h1
  refine h (LinearEquiv.ext fun v => φ.injective ?_)
  rw [← ht, h1]
  rfl

theorem mul_self_of_intertwine (φ : V ≃ₗ[ZMod 2] V') {t : V ≃ₗ[ZMod 2] V}
    {t' : V' ≃ₗ[ZMod 2] V'} (ht : ∀ v, t' (φ v) = φ (t v)) (h : t * t = 1) : t' * t' = 1 := by
  refine LinearEquiv.ext fun v' => ?_
  obtain ⟨v, rfl⟩ := φ.surjective v'
  rw [LinearEquiv.mul_apply, ht, ht, ← LinearEquiv.mul_apply, h]
  rfl

theorem finrank_commSpace_of_intertwine (φ : V ≃ₗ[ZMod 2] V') {t : V ≃ₗ[ZMod 2] V}
    {t' : V' ≃ₗ[ZMod 2] V'} (ht : ∀ v, t' (φ v) = φ (t v)) :
    finrank (ZMod 2) (commSpace t') = finrank (ZMod 2) (commSpace t) := by
  rw [commSpace_eq_map_of_intertwine φ ht, LinearEquiv.finrank_map_eq]

theorem isTypeA_of_intertwine (φ : V ≃ₗ[ZMod 2] V') (hφ : ∀ v, q' (φ v) = q v)
    {t : V ≃ₗ[ZMod 2] V} {t' : V' ≃ₗ[ZMod 2] V'} (ht : ∀ v, t' (φ v) = φ (t v)) {l : ℕ}
    (h : IsTypeA q t l) : IsTypeA q' t' l := by
  obtain ⟨hiso, hne, htt, hdim, hsing⟩ := h
  refine ⟨iso_of_intertwine φ hφ ht hiso, ne_one_of_intertwine φ ht hne,
    mul_self_of_intertwine φ ht htt, by rw [finrank_commSpace_of_intertwine φ ht, hdim],
    fun x hx => ?_⟩
  rw [commSpace_eq_map_of_intertwine φ ht] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  rw [LinearEquiv.coe_coe, hφ]
  exact hsing y hy

theorem isTypeC_of_intertwine (φ : V ≃ₗ[ZMod 2] V') (hφ : ∀ v, q' (φ v) = q v)
    {t : V ≃ₗ[ZMod 2] V} {t' : V' ≃ₗ[ZMod 2] V'} (ht : ∀ v, t' (φ v) = φ (t v)) {l : ℕ}
    (h : IsTypeC q t l) : IsTypeC q' t' l := by
  obtain ⟨hiso, hne, htt, hdim, hev, x, hx, hqx⟩ := h
  refine ⟨iso_of_intertwine φ hφ ht hiso, ne_one_of_intertwine φ ht hne,
    mul_self_of_intertwine φ ht htt, by rw [finrank_commSpace_of_intertwine φ ht, hdim], hev,
    φ x, ?_, by rw [hφ]; exact hqx⟩
  rw [commSpace_eq_map_of_intertwine φ ht]
  exact ⟨x, hx, rfl⟩

theorem isTypeB_of_intertwine (φ : V ≃ₗ[ZMod 2] V') (hφ : ∀ v, q' (φ v) = q v)
    {t : V ≃ₗ[ZMod 2] V} {t' : V' ≃ₗ[ZMod 2] V'} (ht : ∀ v, t' (φ v) = φ (t v)) {l : ℕ}
    (h : IsTypeB q t l) : IsTypeB q' t' l := by
  obtain ⟨hiso, htt, hdim, hodd⟩ := h
  exact ⟨iso_of_intertwine φ hφ ht hiso, mul_self_of_intertwine φ ht htt,
    by rw [finrank_commSpace_of_intertwine φ ht, hdim], hodd⟩

end TypeTransport

namespace Setting

variable {G : Type*} [Group G]

theorem conj_mem_M_of_conj_eq (S S' : Setting G) {k : G} (hk : k * S.z * k⁻¹ = S'.z) {m : G}
    (hm : m ∈ S.M) : k * m * k⁻¹ ∈ S'.M := by
  rw [S'.mem_M_iff, ← hk]
  calc k * m * k⁻¹ * (k * S.z * k⁻¹) = k * (m * S.z) * k⁻¹ := by group
    _ = k * (S.z * m) * k⁻¹ := by rw [S.z_comm hm]
    _ = k * S.z * k⁻¹ * (k * m * k⁻¹) := by group

noncomputable def transportFun (S S' : Setting G) (k : G) (v : S.Qt) : S'.Qt :=
  S'.cl (k * (S.exists_cl v).choose * k⁻¹)

theorem inv_conj_eq_of_conj_eq (S S' : Setting G) {k : G} (hk : k * S.z * k⁻¹ = S'.z) :
    k⁻¹ * S'.z * k⁻¹⁻¹ = S.z := by
  rw [← hk]
  group

variable [Finite G]

theorem conj_mem_QG_of_conj_eq (S S' : Setting G) {k : G} (hk : k * S.z * k⁻¹ = S'.z) {x : G}
    (hx : x ∈ S.QG) : k * x * k⁻¹ ∈ S'.QG := by
  have h1 : (S.conjBy k).QG = S'.QG := QG_eq_of_z_eq _ _ hk
  rw [← h1]
  change k * x * k⁻¹ ∈ S.Qa k
  rw [S.Qa_eq_map]
  exact ⟨x, hx, by simp⟩

theorem cl_conj_eq_of_cl_eq (S S' : Setting G) {k : G} (hk : k * S.z * k⁻¹ = S'.z) {x y : G}
    (hx : x ∈ S.QG) (hy : y ∈ S.QG) (hxy : S.cl x = S.cl y) :
    S'.cl (k * x * k⁻¹) = S'.cl (k * y * k⁻¹) := by
  rcases (S.cl_eq_cl_iff hx hy).mp hxy with rfl | rfl
  · rfl
  · rw [show k * (x * S.z) * k⁻¹ = k * x * k⁻¹ * (k * S.z * k⁻¹) by group, hk,
      S'.cl_mul_z (S.conj_mem_QG_of_conj_eq S' hk hx)]

theorem transportFun_cl (S S' : Setting G) {k : G} (hk : k * S.z * k⁻¹ = S'.z) {x : G}
    (hx : x ∈ S.QG) : transportFun S S' k (S.cl x) = S'.cl (k * x * k⁻¹) :=
  cl_conj_eq_of_cl_eq S S' hk (S.exists_cl (S.cl x)).choose_spec.1 hx
    (S.exists_cl (S.cl x)).choose_spec.2

theorem transportFun_add (S S' : Setting G) {k : G} (hk : k * S.z * k⁻¹ = S'.z) (v w : S.Qt) :
    transportFun S S' k (v + w) = transportFun S S' k v + transportFun S S' k w := by
  obtain ⟨x, hx, rfl⟩ := S.exists_cl v
  obtain ⟨y, hy, rfl⟩ := S.exists_cl w
  rw [← S.cl_mul hx hy, transportFun_cl S S' hk (S.QG.mul_mem hx hy), transportFun_cl S S' hk hx,
    transportFun_cl S S' hk hy, show k * (x * y) * k⁻¹ = k * x * k⁻¹ * (k * y * k⁻¹) by group,
    S'.cl_mul (S.conj_mem_QG_of_conj_eq S' hk hx) (S.conj_mem_QG_of_conj_eq S' hk hy)]

noncomputable def transportQt (S S' : Setting G) {k : G} (hk : k * S.z * k⁻¹ = S'.z) :
    S.Qt ≃ₗ[ZMod 2] S'.Qt :=
  { (AddMonoidHom.mk' (transportFun S S' k) (transportFun_add S S' hk)).toZModLinearMap 2 with
    invFun := transportFun S' S k⁻¹
    left_inv := fun v => by
      obtain ⟨x, hx, rfl⟩ := S.exists_cl v
      change transportFun S' S k⁻¹ (transportFun S S' k (S.cl x)) = S.cl x
      rw [transportFun_cl S S' hk hx, transportFun_cl S' S (inv_conj_eq_of_conj_eq S S' hk)
        (S.conj_mem_QG_of_conj_eq S' hk hx)]
      congr 1
      group
    right_inv := fun v => by
      obtain ⟨x, hx, rfl⟩ := S'.exists_cl v
      change transportFun S S' k (transportFun S' S k⁻¹ (S'.cl x)) = S'.cl x
      rw [transportFun_cl S' S (inv_conj_eq_of_conj_eq S S' hk) hx, transportFun_cl S S' hk
        (S'.conj_mem_QG_of_conj_eq S (inv_conj_eq_of_conj_eq S S' hk) hx)]
      congr 1
      group }

theorem transportQt_cl (S S' : Setting G) {k : G} (hk : k * S.z * k⁻¹ = S'.z) {x : G}
    (hx : x ∈ S.QG) : transportQt S S' hk (S.cl x) = S'.cl (k * x * k⁻¹) :=
  transportFun_cl S S' hk hx

theorem q_cl_conj_of_conj_eq (S S' : Setting G) {k : G} (hk : k * S.z * k⁻¹ = S'.z) {x : G}
    (hx : x ∈ S.QG) : S'.q (S'.cl (k * x * k⁻¹)) = S.q (S.cl x) := by
  have hx' := S.conj_mem_QG_of_conj_eq S' hk hx
  have key : S'.q (S'.cl (k * x * k⁻¹)) = 0 ↔ S.q (S.cl x) = 0 := by
    rw [S'.q_cl_eq_zero_iff hx', S.q_cl_eq_zero_iff hx, conj_pow]
    constructor
    · intro h
      have e : x ^ 2 = k⁻¹ * (k * x ^ 2 * k⁻¹) * k := by group
      rw [e, h]
      group
    · intro h
      rw [h]
      group
  rcases zmod2_cases (S.q (S.cl x)) with h | h
  · rw [h]
    exact key.mpr h
  · rw [h]
    rcases zmod2_cases (S'.q (S'.cl (k * x * k⁻¹))) with h' | h'
    · exact absurd (key.mp h') (by rw [h]; decide)
    · exact h'

theorem q_transportQt (S S' : Setting G) {k : G} (hk : k * S.z * k⁻¹ = S'.z) (v : S.Qt) :
    S'.q (transportQt S S' hk v) = S.q v := by
  obtain ⟨x, hx, rfl⟩ := S.exists_cl v
  rw [transportQt_cl S S' hk hx, q_cl_conj_of_conj_eq S S' hk hx]

theorem transportQt_ρ (S S' : Setting G) {k : G} (hk : k * S.z * k⁻¹ = S'.z) (m : S.M)
    (v : S.Qt) :
    (S'.ρ ⟨k * m * k⁻¹, conj_mem_M_of_conj_eq S S' hk m.2⟩ : S'.Qt ≃ₗ[ZMod 2] S'.Qt)
        (transportQt S S' hk v) =
      transportQt S S' hk ((S.ρ m : S.Qt ≃ₗ[ZMod 2] S.Qt) v) := by
  obtain ⟨x, hx, rfl⟩ := S.exists_cl v
  rw [transportQt_cl S S' hk hx, S'.ρ_cl _ (S.conj_mem_QG_of_conj_eq S' hk hx), S.ρ_cl m hx,
    transportQt_cl S S' hk (S.conj_mem_QG m.2 hx)]
  change S'.cl (k * m * k⁻¹ * (k * x * k⁻¹) * (k * m * k⁻¹)⁻¹) =
    S'.cl (k * ((m : G) * x * (m : G)⁻¹) * k⁻¹)
  congr 1
  group

theorem isTypeAOn_transport (S S' : Setting G) {k : G} (hk : k * S.z * k⁻¹ = S'.z) {m : S.M}
    {l : ℕ} (h : S.IsTypeAOn m l) :
    S'.IsTypeAOn ⟨k * m * k⁻¹, conj_mem_M_of_conj_eq S S' hk m.2⟩ l :=
  isTypeA_of_intertwine (transportQt S S' hk) (q_transportQt S S' hk) (transportQt_ρ S S' hk m) h

theorem isTypeCOn_transport (S S' : Setting G) {k : G} (hk : k * S.z * k⁻¹ = S'.z) {m : S.M}
    {l : ℕ} (h : S.IsTypeCOn m l) :
    S'.IsTypeCOn ⟨k * m * k⁻¹, conj_mem_M_of_conj_eq S S' hk m.2⟩ l :=
  isTypeC_of_intertwine (transportQt S S' hk) (q_transportQt S S' hk) (transportQt_ρ S S' hk m) h

theorem isTypeBOn_transport (S S' : Setting G) {k : G} (hk : k * S.z * k⁻¹ = S'.z) {m : S.M}
    {l : ℕ} (h : S.IsTypeBOn m l) :
    S'.IsTypeBOn ⟨k * m * k⁻¹, conj_mem_M_of_conj_eq S S' hk m.2⟩ l :=
  isTypeB_of_intertwine (transportQt S S' hk) (q_transportQt S S' hk) (transportQt_ρ S S' hk m) h

variable (S : Setting G)

omit [Finite G] in
theorem conj_z_of_mem_M {h : G} (hh : h ∈ S.M) : h * S.z * h⁻¹ = S.z := by
  rw [S.z_comm hh]
  group

theorem isTypeAOn_conj {h : G} (hh : h ∈ S.M) {m : S.M} {l : ℕ} (hm : S.IsTypeAOn m l) :
    S.IsTypeAOn ⟨h * m * h⁻¹, S.M.mul_mem (S.M.mul_mem hh m.2) (S.M.inv_mem hh)⟩ l :=
  isTypeAOn_transport S S (S.conj_z_of_mem_M hh) hm

end Setting

end CFSG.LargeExtraspecial
