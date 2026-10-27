module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec7S2h

public noncomputable section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace Sec7

variable {X : Type} [Group X] [Finite X]

namespace Setup

variable {S : A7Base X} (C : Setup S)

theorem Zz_cases {c : X} (hc : c ∈ C.Zz) : c = 1 ∨ c = S.z ∨ c = C.F.kF ∨ c = S.z * C.F.kF := by
  have hkN : C.F.kF ∈ normalizer ((zpowers S.z : Subgroup X) : Set X) :=
    mem_normalizer_of_map_le (by
      rintro _ ⟨a, ha, rfl⟩
      show C.F.kF * a * C.F.kF⁻¹ ∈ zpowers S.z
      rw [conj_eq_of_comm (commute_of_mem_B (kF_mem_B C.F) (zpowers_le.mpr z_mem_B ha))]
      exact ha)
  rcases mem_or_of_mem_sup_zpowers hkN (by rw [C.F.kF_sq]; exact one_mem _) hc with h | h
  · rcases eq_one_or_eq_of_mem_zpowers z_sq h with h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')
  · rcases eq_one_or_eq_of_mem_zpowers z_sq h with h' | h'
    · right; right; left
      calc c = c * C.F.kF⁻¹ * C.F.kF := by group
        _ = C.F.kF := by rw [h', one_mul]
    · right; right; right
      calc c = c * C.F.kF⁻¹ * C.F.kF := by group
        _ = S.z * C.F.kF := by rw [h']

theorem z_ne_k : S.z ≠ C.F.kF := fun h => C.k_not_mem_zpowers_z (h ▸ mem_zpowers _)

theorem zk_ne_k : S.z * C.F.kF ≠ C.F.kF := fun h => S.z_ne_one (by simpa using h)

theorem zk_ne_z : S.z * C.F.kF ≠ S.z := fun h => C.ne_one_k (by simpa using h)

theorem z_not_mem_zpowers_k : S.z ∉ zpowers C.F.kF := fun h => by
  rcases eq_one_or_eq_of_mem_zpowers C.F.kF_sq h with h' | h'
  · exact S.z_ne_one h'
  · exact C.z_ne_k h'

theorem k_not_mem_zpowers_zk : C.F.kF ∉ zpowers (S.z * C.F.kF) := fun h => by
  rcases eq_one_or_eq_of_mem_zpowers (isK_zkF C.F).sq h with h' | h'
  · exact C.ne_one_k h'
  · exact C.zk_ne_k h'.symm

theorem S₂_E0 {s : X} (hs : s ∈ C.S₂) {e : X} (he : e ∈ C.E₀) :
    s * e * s⁻¹ = e ∨ s * e * s⁻¹ = S.z * e := by
  have hel := C.isRefl_y.elemAbelianTwo_E0 C.isK_k
  have he2 : e * e = 1 := by rw [← pow_two]; exact hel.sq_eq_one e he
  have hu : C.D₁.u * e * C.D₁.u⁻¹ = e ∨ C.D₁.u * e * C.D₁.u⁻¹ = S.z * e := by
    rcases C.mul_u_conj_mem he with h | h
    · left
      calc C.D₁.u * e * C.D₁.u⁻¹ = e * e * (C.D₁.u * e * C.D₁.u⁻¹) := by rw [he2, one_mul]
        _ = e := by rw [mul_assoc, h, mul_one]
    · right
      calc C.D₁.u * e * C.D₁.u⁻¹ = e * e * (C.D₁.u * e * C.D₁.u⁻¹) := by rw [he2, one_mul]
        _ = e * S.z := by rw [mul_assoc, h]
        _ = S.z * e := C.comm_E0 he C.z_mem_E0
  have hzeE : S.z * e ∈ C.E₀ := mul_mem C.z_mem_E0 he
  obtain ⟨w, a, hw, ha, rfl | rfl⟩ := C.S₂_decomp hs
  · left
    rw [show w * a * e * (w * a)⁻¹ = w * (a * e * a⁻¹) * w⁻¹ by group, C.conj_eq_of_mem_Q₁ ha he,
      hw e (mem_sup_left he)]
  · rw [show w * a * C.D₁.u * e * (w * a * C.D₁.u)⁻¹ =
      w * (a * (C.D₁.u * e * C.D₁.u⁻¹) * a⁻¹) * w⁻¹ by group]
    rcases hu with h | h <;> rw [h]
    · left; rw [C.conj_eq_of_mem_Q₁ ha he, hw e (mem_sup_left he)]
    · right; rw [C.conj_eq_of_mem_Q₁ ha hzeE, hw _ (mem_sup_left hzeE)]

theorem Fv_cases {f : X} (hf : f ∈ C.Fv) : f ∈ C.E₀ ∨ ∃ e ∈ C.E₀, f = e * C.v' := by
  rcases mem_or_of_mem_sup_zpowers (C.normalizes_E0_of_mem_Q₁ C.v'_mem_Q₁) C.v'_sq_mem_E0 hf with
    h | h
  · exact Or.inl h
  · exact Or.inr ⟨_, h, by group⟩

theorem comm_ev' {s e : X} (hse : s * e * s⁻¹ = e) :
    s * (e * C.v') * s⁻¹ * (e * C.v')⁻¹ = e * (s * C.v' * s⁻¹ * C.v'⁻¹) * e⁻¹ := by
  rw [show s * (e * C.v') * s⁻¹ * (e * C.v')⁻¹ = (s * e * s⁻¹) * (s * C.v' * s⁻¹ * C.v'⁻¹) * e⁻¹
    by group, hse]

theorem fixY_iff {s : X} (hs : s ∈ C.S₂) :
    s * C.F.yF * s⁻¹ = C.F.yF ↔ ∀ f ∈ C.Fv, s * f * s⁻¹ * f⁻¹ ∈ zpowers C.F.kF := by
  constructor
  · intro hy f hf
    have hE := C.conj_E0_of_gens (C.S₂_z hs) hy (C.S₂_k hs)
    rcases C.Fv_cases hf with he | ⟨e, he, rfl⟩
    · rw [hE f he, mul_inv_cancel]; exact one_mem _
    · rw [C.comm_ev' (hE e he)]
      rcases C.S₂_v' hs with h | h <;> rw [h]
      · rw [mul_inv_cancel, mul_one, mul_inv_cancel]; exact one_mem _
      · rw [mul_inv_cancel_right, C.comm_E0 he C.k_mem_E0, mul_inv_cancel_right]
        exact mem_zpowers _
  · intro h
    rcases C.S₂_y hs with hy | hy
    · exact hy
    · exfalso
      have := h _ (mem_sup_left C.y_mem_E0)
      rw [hy, mul_inv_cancel_right] at this
      exact C.z_not_mem_zpowers_k this

theorem fixV_iff {s : X} (hs : s ∈ C.S₂) :
    s * C.v' * s⁻¹ = C.v' ↔ ∀ f ∈ C.Fv, s * f * s⁻¹ * f⁻¹ ∈ zpowers S.z := by
  constructor
  · intro hv f hf
    rcases C.Fv_cases hf with he | ⟨e, he, rfl⟩
    · rcases C.S₂_E0 hs he with h | h <;> rw [h]
      · rw [mul_inv_cancel]; exact one_mem _
      · rw [mul_inv_cancel_right]; exact mem_zpowers _
    · rw [show s * (e * C.v') * s⁻¹ * (e * C.v')⁻¹ =
        (s * e * s⁻¹) * (s * C.v' * s⁻¹) * C.v'⁻¹ * e⁻¹ by group, hv, mul_inv_cancel_right]
      rcases C.S₂_E0 hs he with h | h <;> rw [h]
      · rw [mul_inv_cancel]; exact one_mem _
      · rw [mul_inv_cancel_right]; exact mem_zpowers _
  · intro h
    rcases C.S₂_v' hs with hv | hv
    · exact hv
    · exfalso
      have := h _ (mem_sup_right (mem_zpowers _))
      rw [hv, mul_inv_cancel_right] at this
      exact C.k_not_mem_zpowers_z this

theorem Q₁_comm_Fv {c : X} (hc : c ∈ C.D₁.Q₁) {f : X} (hf : f ∈ C.Fv) :
    c * f * c⁻¹ * f⁻¹ ∈ zpowers C.F.kF :=
  (C.fixY_iff (C.Q₁_le_S₂ hc)).mp (C.conj_eq_of_mem_Q₁ hc C.y_mem_E0) f hf

theorem Fv_conj_inv {h : X} (hh : h ∈ normalizer (C.S₂ : Set X)) {f : X} (hf : f ∈ C.Fv) :
    h⁻¹ * f * h ∈ C.Fv := by
  have := C.conj_Fv' (inv_mem hh) hf
  rwa [inv_inv] at this

theorem comm_conj_zpowers {h x c : X} (hh : h ∈ normalizer (C.S₂ : Set X))
    (hx : ∀ f ∈ C.Fv, x * f * x⁻¹ * f⁻¹ ∈ zpowers c) :
    ∀ f ∈ C.Fv, (h * x * h⁻¹) * f * (h * x * h⁻¹)⁻¹ * f⁻¹ ∈ zpowers (h * c * h⁻¹) := by
  intro f hf
  obtain ⟨n, hn⟩ := mem_zpowers_iff.mp (hx _ (C.Fv_conj_inv hh hf))
  refine mem_zpowers_iff.mpr ⟨n, ?_⟩
  rw [conj_zpow, hn]
  group

theorem conj_k_cases {h : X} (hh : h ∈ normalizer (C.S₂ : Set X)) :
    h * C.F.kF * h⁻¹ = C.F.kF ∨ h * C.F.kF * h⁻¹ = S.z := by
  have hkZ : C.F.kF ∈ C.Zz := mem_sup_right (mem_zpowers _)
  rcases C.Zz_cases (C.conj_Zz hh hkZ) with h1 | h1 | h1 | h1
  · exfalso
    exact C.ne_one_k (by
      calc C.F.kF = h⁻¹ * (h * C.F.kF * h⁻¹) * h := by group
        _ = 1 := by rw [h1]; group)
  · exact Or.inr h1
  · exact Or.inl h1
  · exfalso
    have htS : h * S.t * h⁻¹ ∈ C.S₂ := (mem_normalizer_iff.mp hh _).mp C.t_mem_S₂
    have hc := C.comm_conj_zpowers hh (fun f hf => C.Q₁_comm_Fv C.t_mem_Q₁ hf)
    rw [h1] at hc
    have hy : (h * S.t * h⁻¹) * C.F.yF * (h * S.t * h⁻¹)⁻¹ = C.F.yF := by
      rcases C.S₂_y htS with hy | hy
      · exact hy
      · exfalso
        have := hc _ (mem_sup_left C.y_mem_E0)
        rw [hy, mul_inv_cancel_right] at this
        exact C.z_not_mem_zpowers_zk this
    have hv : (h * S.t * h⁻¹) * C.v' * (h * S.t * h⁻¹)⁻¹ = C.v' := by
      rcases C.S₂_v' htS with hv | hv
      · exact hv
      · exfalso
        have := hc _ (mem_sup_right (mem_zpowers _))
        rw [hv, mul_inv_cancel_right] at this
        exact C.k_not_mem_zpowers_zk this
    exact C.not_conjTo_of_mem_Q₂₀ (C.mem_Q₂₀_of htS hy hv) ⟨h, rfl⟩

theorem mem_S₂_of_fix_k {P : Subgroup X} (hP2 : IsPGroup 2 P) (hSP : C.S₂ ≤ P) {h : X}
    (hhP : h ∈ P) (hh : h ∈ normalizer (C.S₂ : Set X)) (hk : h * C.F.kF * h⁻¹ = C.F.kF) :
    h ∈ C.S₂ := by
  have hQ : C.D₁.Q₁ ≤ C.D₁.Q₁.comap (MulAut.conj h).toMonoidHom := by
    refine C.Q₁_le_of_conjTo fun c hc hct => ?_
    show h * c * h⁻¹ ∈ C.D₁.Q₁
    have hcS : h * c * h⁻¹ ∈ C.S₂ := (mem_normalizer_iff.mp hh _).mp (C.Q₁_le_S₂ hc)
    have hcc := C.comm_conj_zpowers hh (fun f hf => C.Q₁_comm_Fv hc hf)
    rw [hk] at hcc
    have hy := (C.fixY_iff hcS).mpr hcc
    have hct' : ConjTo S.t (h * c * h⁻¹) := conjTo_conj hct
    rcases C.inv_cases_Q₂ hcS hy (sq_of_conjTo hct') with h1 | h1
    · exact h1
    · exact absurd hct' (C.not_conjTo_of_mem_Q₂₀ h1)
  have hN : h ∈ normalizer (C.D₁.Q₁ : Set X) :=
    mem_normalizer_of_map_le (map_le_iff_le_comap.mpr hQ)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : C.S₂ ⊔ zpowers h ≤ normalizer (C.D₁.Q₁ : Set X) :=
    sup_le C.S₂_le (zpowers_le.mpr hN)
  have heq := C.S₂_sylow.eq_of_le le_sup_left hle (isPGroup_sup_zpowers hP2 hSP hhP)
  rw [← heq]
  exact mem_sup_right (mem_zpowers h)

end Setup

end Sec7

end CFSG.ComponentClassification.HSFLit
