module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD8cQ

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace KD8c

open KD7 KD8ab Sec8

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : L2Data t L}
  {C : A.CaseKD} {S : KDBase A C} {T₁ : Subgroup X}

theorem MC_hom_ext {Y : Type*} [Group Y] {f g : MC →* Y} (h : ∀ x ∈ MC.gens, f x = g x)
    (x : MC) : f x = g x := by
  rw [MC.nf_spec x, map_nfProd, map_nfProd, List.map_congr_left h]

namespace Conf

variable (K : Conf S T₁)

theorem ι_mem_S1 (b : MC) : K.ι b ∈ K.D₁.S₁ := by
  rw [← K.range_ι]; exact ⟨b, rfl⟩

namespace T2

variable {K} (T : K.T2)

theorem q_NR : T.q ∈ K.NR := T.le_NR T.q_mem

theorem pN_q_3 : K.pN T.q_NR 3 = 0 := T.pN_q 3

theorem pN_q_0 : K.pN T.q_NR 0 = 3 := T.pN_q 0

theorem pN_qinv_0 : K.pN (inv_mem T.q_NR) 0 = 3 := by
  have := K.pN_inv T.q_NR 3
  rwa [T.pN_q_3] at this

theorem q_not_mem : T.q ∉ K.D₁.S₁ := fun h => by
  have := K.pN_S1 h T.q_NR
  rw [T.pN_q_0] at this
  exact absurd this (by decide)

theorem mem_S1_of {g : X} (hg : g ∈ T.P) (h0 : K.pN (T.le_NR hg) 0 = 0) : g ∈ K.D₁.S₁ :=
  K.mem_S1_of T.isPGroup T.S1_le T.le_NR hg h0

theorem conj_S1 {s : X} (hs : s ∈ K.D₁.S₁) : T.q * s * T.q⁻¹ ∈ K.D₁.S₁ := by
  have hsP := T.S1_le hs
  refine T.mem_S1_of (mul_mem (mul_mem T.q_mem hsP) (inv_mem T.q_mem)) ?_
  refine (K.pN_mul (mul_mem T.q_NR (T.le_NR hsP)) (inv_mem T.q_NR) 0).trans ?_
  rw [K.pN_mul T.q_NR (T.le_NR hsP), T.pN_qinv_0, K.pN_S1_3 hs, T.pN_q_3]

theorem sq_mem : T.q * T.q ∈ K.D₁.S₁ := by
  refine T.mem_S1_of (mul_mem T.q_mem T.q_mem) ?_
  refine (K.pN_mul T.q_NR T.q_NR 0).trans ?_
  rw [T.pN_q_0, T.pN_q_3]

theorem cases {g : X} (hg : g ∈ T.P) : g ∈ K.D₁.S₁ ∨ g * T.q⁻¹ ∈ K.D₁.S₁ := by
  rcases K.pN_cases T.isPGroup (T.S1_le K.w₂_mem_S1) T.le_NR hg with h0 | ha | hsa
  · exact Or.inl (T.mem_S1_of hg h0)
  · refine Or.inr (T.mem_S1_of (mul_mem hg (inv_mem T.q_mem)) ?_)
    refine (K.pN_mul (T.le_NR hg) (inv_mem T.q_NR) 0).trans ?_
    rw [T.pN_qinv_0, ha]
    rfl
  · refine Or.inr (T.mem_S1_of (mul_mem hg (inv_mem T.q_mem)) ?_)
    refine (K.pN_mul (T.le_NR hg) (inv_mem T.q_NR) 0).trans ?_
    rw [T.pN_qinv_0, hsa]
    rfl

noncomputable def phi (b : MC) : MC := Function.invFun K.ι (T.q * K.ι b * T.q⁻¹)

theorem ι_phi (b : MC) : K.ι (T.phi b) = T.q * K.ι b * T.q⁻¹ := by
  apply Function.invFun_eq
  have h : T.q * K.ι b * T.q⁻¹ ∈ K.D₁.S₁ := T.conj_S1 (K.ι_mem_S1 b)
  rw [← K.range_ι] at h
  exact h

theorem antipodal : Antipodal T.phi where
  map_mul a b := K.ι_injective (by rw [map_mul, T.ι_phi, T.ι_phi, T.ι_phi, map_mul]; group)
  injective a b h := K.ι_injective (by
    have := congrArg K.ι h
    rw [T.ι_phi, T.ι_phi] at this
    simpa using this)
  ant i x hx := by
    have h := K.conj_mem_pN T.q_NR (K.ι_mem_Ex hx)
    rw [T.pN_q, ← T.ι_phi] at h
    obtain ⟨y, hy, hyx⟩ := K.mem_Ex.mp h
    rw [K.ι_injective hyx] at hy
    exact hy

theorem exists_j : ∃ m : MC, inR1 m = true ∧ ∃ j : Fin 8, ∀ b : MC,
    K.ι m * T.q * K.ι b * (K.ι m * T.q)⁻¹ = K.ι (phiR j b) := by
  obtain ⟨m, hm, j, hj⟩ := exists_norm T.antipodal
  refine ⟨m, hm, j, fun b => ?_⟩
  let F₁ : MC →* X := (MulAut.conj (K.ι m * T.q)).toMonoidHom.comp K.ι
  let F₂ : MC →* X := K.ι.comp (MonoidHom.mk' (phiR j) (phiR_mul j))
  have := MC_hom_ext (f := F₁) (g := F₂) (fun g hg => by
    simp only [F₁, F₂, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      MonoidHom.mk'_apply]
    rw [← hj g hg, map_mul, map_mul, map_inv, T.ι_phi]
    group) b
  exact this

structure Lift (T : K.T2) where
  j : Fin 8
  i : Fin 2
  hj3 : j ≠ 3
  hj4 : j ≠ 4
  Q : X
  hQ : ∀ b, Q * K.ι b * Q⁻¹ = K.ι (phiR j b)
  hs : Q * Q = K.ι (sR j i)
  Q_mem : Q ∈ T.P
  Q_not_mem : Q ∉ K.D₁.S₁
  cases : ∀ g ∈ T.P, g ∈ K.D₁.S₁ ∨ g * Q⁻¹ ∈ K.D₁.S₁

theorem nonempty_lift : Nonempty T.Lift := by
  obtain ⟨m, -, j, hj⟩ := T.exists_j
  set Q := K.ι m * T.q with hQdef
  have hmS := K.ι_mem_S1 m
  have hQQ : Q * Q ∈ K.D₁.S₁ := by
    rw [hQdef, show K.ι m * T.q * (K.ι m * T.q) = K.ι m * (T.q * K.ι m * T.q⁻¹) * (T.q * T.q)
      by group]
    exact mul_mem (mul_mem hmS (T.conj_S1 hmS)) T.sq_mem
  rw [← K.range_ι] at hQQ
  obtain ⟨s, hs⟩ := hQQ
  have hφs : phiR j s = s := K.ι_injective (by
    rw [← hj, hs]
    group)
  have hvalid : ValidS (phiR j) s := by
    refine ⟨hφs, fun g _ => K.ι_injective ?_⟩
    rw [← hj, ← hj, map_mul, map_mul, map_inv, hs]
    group
  obtain ⟨hj3, hj4, hsi⟩ := validS_iff j s hvalid
  have hQP : Q ∈ T.P := mul_mem (T.S1_le hmS) T.q_mem
  have hQS : Q ∉ K.D₁.S₁ := fun h => T.q_not_mem (by
    rw [show T.q = (K.ι m)⁻¹ * Q by rw [hQdef]; group]
    exact mul_mem (inv_mem hmS) h)
  have hcases : ∀ g ∈ T.P, g ∈ K.D₁.S₁ ∨ g * Q⁻¹ ∈ K.D₁.S₁ := by
    intro g hg
    rcases T.cases hg with h | h
    · exact Or.inl h
    · refine Or.inr ?_
      rw [hQdef, show g * (K.ι m * T.q)⁻¹ = g * T.q⁻¹ * (K.ι m)⁻¹ by group]
      exact mul_mem h (inv_mem hmS)
  have hQ : ∀ b, Q * K.ι b * Q⁻¹ = K.ι (phiR j b) := hj
  rcases hsi with h0 | h1
  · exact ⟨⟨j, 0, hj3, hj4, Q, hQ, by rw [← h0, hs], hQP, hQS, hcases⟩⟩
  · exact ⟨⟨j, 1, hj3, hj4, Q, hQ, by rw [← h1, hs], hQP, hQS, hcases⟩⟩

namespace Lift

variable {T} (W : T.Lift)

abbrev D' : ExtData MC := D W.j W.hj3 W.hj4 W.i

@[expose] noncomputable def ψ : Ext W.D' →* X := Ext.lift K.ι W.Q W.hQ W.hs

theorem ψ_apply (x : Ext W.D') : W.ψ x = K.ι x.a * bif x.e then W.Q else 1 := rfl

theorem ψ_injective : Function.Injective W.ψ := by
  refine Ext.lift_injective _ _ _ _ K.ι_injective fun h => W.Q_not_mem ?_
  rw [← K.range_ι]
  exact h

theorem ψ_incl (a : MC) : W.ψ (Ext.incl W.D' a) = K.ι a := by
  rw [ψ_apply]
  simp [Ext.incl]

theorem range_ψ : W.ψ.range = T.P := by
  apply le_antisymm
  · rintro _ ⟨⟨a, e⟩, rfl⟩
    rw [ψ_apply]
    cases e
    · simpa using T.S1_le (K.ι_mem_S1 a)
    · simpa using mul_mem (T.S1_le (K.ι_mem_S1 a)) W.Q_mem
  · intro g hg
    rcases W.cases g hg with h | h
    · rw [← K.range_ι] at h
      obtain ⟨a, rfl⟩ := h
      exact ⟨⟨a, false⟩, by simp [ψ_apply]⟩
    · rw [← K.range_ι] at h
      obtain ⟨a, ha⟩ := h
      refine ⟨⟨a, true⟩, ?_⟩
      rw [ψ_apply]
      simp only [Bool.cond_true]
      rw [ha]
      group

include W in
theorem card_P : Nat.card T.P = 512 := by
  rw [← W.range_ψ, MonoidHom.range_eq_map, card_map_of_injective W.ψ_injective, card_top,
    Ext.card_eq, MC.card_eq]
  norm_num

end Lift

end T2

end Conf

end KD8c

end CFSG.ComponentClassification.HSFLit
