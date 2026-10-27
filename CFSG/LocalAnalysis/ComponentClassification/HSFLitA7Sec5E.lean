module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec5EInv
public import CFSG.Quasithin.Background.A1cTransferVariants

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace Sec5E

open Sec7 Sec8 T2M

variable {X : Type} [Group X] [Finite X] {S : A7Base X} {F : S.Frame} {T₁ : Subgroup X}

namespace R2D

variable {C : Ctx S F T₁} (B : R2D C)

@[expose] def SigZ (p : SigD) : Prop := p.sig z = z

instance (p : SigD) : Decidable (SigZ p) := by unfold SigZ; infer_instance

theorem sig_z : ∀ p ∈ repList, SigZ p := by decide +kernel

@[expose] noncomputable def ws : X := C.ι B.G.p.ws

@[expose] noncomputable def Stab : Subgroup X where
  carrier := {r | r * S.z * r⁻¹ = S.z ∧ (r * B.ws * r⁻¹ = B.ws ∨ r * B.ws * r⁻¹ = B.ws * S.z)}
  mul_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    have hz : ∀ c : X, a * (c * S.z) * a⁻¹ = (a * c * a⁻¹) * S.z := fun c => by
      calc a * (c * S.z) * a⁻¹ = (a * c * a⁻¹) * (a * S.z * a⁻¹) := by group
        _ = (a * c * a⁻¹) * S.z := by rw [ha1]
    refine ⟨?_, ?_⟩
    · rw [show a * b * S.z * (a * b)⁻¹ = a * (b * S.z * b⁻¹) * a⁻¹ by group, hb1, ha1]
    · rw [show a * b * B.ws * (a * b)⁻¹ = a * (b * B.ws * b⁻¹) * a⁻¹ by group]
      rcases hb2 with h | h <;> rw [h]
      · exact ha2
      · rw [hz]
        rcases ha2 with h' | h' <;> rw [h']
        · exact Or.inr rfl
        · left; rw [mul_assoc, z_mul_z, mul_one]
  one_mem' := ⟨by group, Or.inl (by group)⟩
  inv_mem' := by
    rintro a ⟨ha1, ha2⟩
    have hz : a⁻¹ * S.z * a = S.z := by
      calc a⁻¹ * S.z * a = a⁻¹ * (a * S.z * a⁻¹) * a := by rw [ha1]
        _ = S.z := by group
    refine ⟨by rw [inv_inv]; exact hz, ?_⟩
    rw [inv_inv]
    rcases ha2 with h | h
    · left
      calc a⁻¹ * B.ws * a = a⁻¹ * (a * B.ws * a⁻¹) * a := by rw [h]
        _ = B.ws := by group
    · right
      have h1 : B.ws = (a⁻¹ * B.ws * a) * S.z := by
        calc B.ws = a⁻¹ * (a * B.ws * a⁻¹) * a := by group
          _ = a⁻¹ * (B.ws * S.z) * a := by rw [h]
          _ = (a⁻¹ * B.ws * a) * (a⁻¹ * S.z * a) := by group
          _ = (a⁻¹ * B.ws * a) * S.z := by rw [hz]
      calc a⁻¹ * B.ws * a = (a⁻¹ * B.ws * a) * S.z * S.z := by
            rw [mul_assoc _ S.z S.z, z_mul_z, mul_one]
        _ = B.ws * S.z := by rw [← h1]

theorem ws_mem_N : B.G.p.InN B.G.p.ws := B.ws_ok.1

theorem ws_comm_z : B.ws * S.z = S.z * B.ws := by
  rw [ws, ← C.ι_z, ← map_mul, ← map_mul, central_of_mem_Zl z (by decide +kernel)]

theorem T₂_le_Stab : C.D.T₂ ≤ B.Stab := by
  intro r hr
  obtain ⟨τ, rfl⟩ := C.exists_ι hr
  refine ⟨?_, ?_⟩
  · rw [← C.ι_z, ← map_inv, ← map_mul, ← map_mul,
      ← central_of_mem_Zl z (by decide +kernel) τ, mul_inv_cancel_right]
  · rcases comm_cases τ B.G.p.ws with h | h
    · left
      have : τ * B.G.p.ws * τ⁻¹ = B.G.p.ws := by
        calc τ * B.G.p.ws * τ⁻¹ = τ * B.G.p.ws * τ⁻¹ * (B.G.p.ws)⁻¹ * B.G.p.ws := by group
          _ = B.G.p.ws := by rw [h, one_mul]
      rw [ws, ← map_inv, ← map_mul, ← map_mul, this]
    · right
      have : τ * B.G.p.ws * τ⁻¹ = z * B.G.p.ws := by
        calc τ * B.G.p.ws * τ⁻¹ = τ * B.G.p.ws * τ⁻¹ * (B.G.p.ws)⁻¹ * B.G.p.ws := by group
          _ = z * B.G.p.ws := by rw [h]
      rw [ws, ← map_inv, ← map_mul, ← map_mul, this, map_mul, C.ι_z, ← ws, ← B.ws_comm_z]

theorem w₂_mem_Stab : C.D.w₂ ∈ B.Stab := by
  refine ⟨?_, Or.inl ?_⟩
  · rw [← C.ι_z, C.w₂_conj, sw2_E3 _ (by decide +kernel)]
  · rw [ws, C.w₂_conj, sw2_E3 _ B.ws_mem_N.1]

theorem g_mem_Stab : B.g ∈ B.Stab := by
  refine ⟨?_, ?_⟩
  · rw [← C.ι_z, B.hσ, sig_z B.G.p B.G.hp]
  · rcases B.ws_ok.2.2.1 with h | h
    · left; rw [ws, B.hσ, h]
    · right; rw [ws, B.hσ, h, map_mul, C.ι_z]


theorem R_le_Stab : C.D.R ≤ B.Stab := by
  rw [C.D.R_eq]; exact sup_le B.T₂_le_Stab (zpowers_le.mpr B.w₂_mem_Stab)

theorem R₂_le_Stab : B.R₂ ≤ B.Stab := by
  intro r hr
  have hg := B.g_mem_Stab
  have hw := B.w₂_mem_Stab
  rcases B.mem_cases hr with h | h | h | h
  · exact B.R_le_Stab h
  · rw [show r = B.g * (B.g⁻¹ * r) by group]; exact mul_mem hg (B.R_le_Stab h)
  · rw [show r = C.D.w₂ * B.g * ((C.D.w₂ * B.g)⁻¹ * r) by group]
    exact mul_mem (mul_mem hw hg) (B.R_le_Stab h)
  · rw [show r = B.g * C.D.w₂ * B.g * ((B.g * C.D.w₂ * B.g)⁻¹ * r) by group]
    exact mul_mem (mul_mem (mul_mem hg hw) hg) (B.R_le_Stab h)

@[expose] noncomputable def Q' : Subgroup X := B.R₂ ⊓ centralizer ({B.ws} : Set X)

theorem t_mem_R₂ : S.t ∈ B.R₂ :=
  B.R_le (C.T₂_le_R (C.T_le_T₂ S.data.t_mem_T))

theorem t_mem_S16 : T2M.t ∈ B.G.p.S16 := by
  simp only [SigD.S16, List.mem_append]; exact Or.inl (Or.inl (Or.inl t_mem_tEl))

theorem not_comm_of_S16 {a : T2M} (ha : a ∈ B.G.p.S16) : C.ι a * B.ws ≠ B.ws * C.ι a := by
  intro h
  apply (SigD.m0Ok B.G.p B.hp').1 a ha
  apply C.ι_injective
  rw [map_mul, map_mul]; exact h

theorem t_conj_ws : S.t * B.ws * S.t⁻¹ = B.ws * S.z := by
  have h := (B.T₂_le_Stab (C.T_le_T₂ S.data.t_mem_T)).2
  rcases h with h | h
  · exfalso
    apply B.not_comm_of_S16 B.t_mem_S16
    rw [C.ι_t]
    calc S.t * B.ws = (S.t * B.ws * S.t⁻¹) * S.t := by group
      _ = B.ws * S.t := by rw [h]
  · exact h

theorem t_not_mem_Q' : S.t ∉ B.Q' := by
  intro h
  apply B.not_comm_of_S16 B.t_mem_S16
  rw [C.ι_t]
  exact mem_centralizer_singleton_iff.mp h.2

theorem relIndex_Q' : B.Q'.relIndex B.R₂ = 2 := by
  rw [Subgroup.relIndex_eq_two_iff]
  refine ⟨S.t, B.t_mem_R₂, fun r hr => ?_⟩
  have hS := B.R₂_le_Stab hr
  have hmem : ∀ x ∈ B.R₂, x * B.ws * x⁻¹ = B.ws → x ∈ B.Q' := fun x hx hxw =>
    ⟨hx, mem_centralizer_singleton_iff.mpr (by
      calc x * B.ws = (x * B.ws * x⁻¹) * x := by group
        _ = B.ws * x := by rw [hxw])⟩
  have hnot : ∀ x ∈ B.Q', x * B.ws * x⁻¹ = B.ws := fun x hx => by
    rw [mem_centralizer_singleton_iff.mp hx.2, mul_inv_cancel_right]
  rcases hS.2 with h | h
  · refine Or.inr ⟨hmem r hr h, fun hrt => B.t_not_mem_Q' ?_⟩
    have := mul_mem (inv_mem (hmem r hr h)) hrt
    rwa [inv_mul_cancel_left] at this
  · refine Or.inl ⟨hmem _ (mul_mem hr B.t_mem_R₂) ?_, fun hrQ => ?_⟩
    · rw [show r * S.t * B.ws * (r * S.t)⁻¹ = r * (S.t * B.ws * S.t⁻¹) * r⁻¹ by group,
        B.t_conj_ws]
      calc r * (B.ws * S.z) * r⁻¹ = (r * B.ws * r⁻¹) * (r * S.z * r⁻¹) := by group
        _ = B.ws := by rw [h, hS.1, mul_assoc, z_mul_z, mul_one]
    · have h1 := hnot r hrQ
      rw [h1] at h
      have : S.z = 1 := by
        calc S.z = B.ws⁻¹ * (B.ws * S.z) := by group
          _ = 1 := by rw [← h]; group
      exact S.z_ne_one this

@[expose] noncomputable def J : Subgroup X := closure {s | s ∈ B.R₂ ∧ ConjTo S.t s}

theorem conj_mem_R₂ {s : X} (hs : s ∈ B.R₂) (hc : ConjTo S.t s) :
    ∃ a ∈ B.G.p.S16, C.ι a = s := by
  have hs2 : s * s = 1 := by
    obtain ⟨c, rfl⟩ := hc
    rw [show c * S.t * c⁻¹ * (c * S.t * c⁻¹) = c * (S.t * S.t) * c⁻¹ by group, t_mul_t]; group
  rcases B.inv_cases hs hs2 with h | h
  · exact h
  · exact absurd hc h

theorem J_eq : B.J = C.D.T₂ := by
  apply le_antisymm
  · rw [J, closure_le]
    rintro s ⟨hs, hc⟩
    obtain ⟨a, -, rfl⟩ := B.conj_mem_R₂ hs hc
    exact C.ι_mem_T₂ a
  · intro b hb
    obtain ⟨a, rfl⟩ := C.exists_ι hb
    have hmemJ : ∀ c ∈ B.G.p.S16, C.ι c ∈ B.J := fun c hc =>
      subset_closure ⟨B.R_le (C.T₂_le_R (C.ι_mem_T₂ c)), B.G.conj_S16 hc⟩
    have hrep : ∀ i, B.G.p.reps i ∈ B.G.p.S16 := fun i => by
      have := SigD.reps_mem B.G.p B.G.hp i 1 (by decide +kernel)
      rwa [mul_one] at this
    have htz : T2M.t * T2M.z ∈ B.G.p.S16 := by
      simp only [SigD.S16, List.mem_append]; exact Or.inl (Or.inl (Or.inl (by decide +kernel)))
    have htk : T2M.t * T2M.k ∈ B.G.p.S16 := by
      simp only [SigD.S16, List.mem_append]; exact Or.inl (Or.inl (Or.inl (by decide +kernel)))
    obtain ⟨bs, hbs, rfl⟩ := SigD.reps_gen B.G.p B.G.hp a
    refine map_mem_of_inSpan C.ι ⟨bs, hbs, rfl⟩ fun g hg => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hmemJ _ (hrep 0)
    · exact hmemJ _ (hrep 1)
    · exact hmemJ _ (hrep 2)
    · exact hmemJ _ (hrep 3)
    · have : T2M.z = T2M.t⁻¹ * (T2M.t * T2M.z) := by group
      rw [this, map_mul, map_inv]
      exact mul_mem (inv_mem (hmemJ _ B.t_mem_S16)) (hmemJ _ htz)
    · have : T2M.k = T2M.t⁻¹ * (T2M.t * T2M.k) := by group
      rw [this, map_mul, map_inv]
      exact mul_mem (inv_mem (hmemJ _ B.t_mem_S16)) (hmemJ _ htk)


theorem conj_J_le {w : X} (hw : w ∈ normalizer (B.R₂ : Set X)) {x : X} (hx : x ∈ B.J) :
    w * x * w⁻¹ ∈ B.J := by
  have hle : B.J.map (MulAut.conj w).toMonoidHom ≤ B.J := by
    rw [J, MonoidHom.map_closure, closure_le]
    rintro _ ⟨s, ⟨hs, hc⟩, rfl⟩
    exact subset_closure ⟨conj_mem_of_mem_normalizer hw hs, conjTo_conj hc w⟩
  exact hle ⟨x, hx, rfl⟩

theorem exists_sylow : ∃ P : Sylow 2 X, (P : Subgroup X) = B.R₂ := by
  by_contra hne
  push Not at hne
  obtain ⟨w, hwN, hwR, hwp⟩ := exists_mem_normalizer_not_mem B.isPGroup hne
  have hwT : w ∈ normalizer (C.D.T₂ : Set X) := by
    rw [← B.J_eq]
    exact mem_normalizer_of_conj_le' fun x hx => B.conj_J_le hwN hx
  have h := B.maximal (B.R₂ ⊔ zpowers w) hwp le_sup_left (sup_le B.le_N (zpowers_le.mpr hwT))
  exact hwR (h ▸ mem_sup_right (mem_zpowers w))

theorem not_conj_mem_Q' (x : X) : x⁻¹ * S.t * x ∉ B.Q' := by
  intro h
  have hc : ConjTo S.t (x⁻¹ * S.t * x) := ⟨x⁻¹, by group⟩
  obtain ⟨a, ha, hax⟩ := B.conj_mem_R₂ h.1 hc
  apply B.not_comm_of_S16 ha
  rw [hax]
  exact mem_centralizer_singleton_iff.mp h.2

include B in
theorem false_of [IsSimpleGroup X] (hX : ∃ a b : X, a * b ≠ b * a) : False := by
  obtain ⟨P, hP⟩ := B.exists_sylow
  have hQP : B.Q' ≤ (P : Subgroup X) := hP ▸ inf_le_left
  have hidx : B.Q'.relIndex (P : Subgroup X) = 2 := hP ▸ B.relIndex_Q'
  obtain ⟨N, hN, hsq, htN⟩ := CFSG.Quasithin.thompson_transfer_exists_normal P hQP hidx
    S.data.orderOf_t B.not_conj_mem_Q'
  have := hN
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  · obtain ⟨a, b, hab⟩ := hX
    have hsq' : ∀ y : X, y * y = 1 := fun y => by
      have := hsq y
      rwa [h, mem_bot, pow_two] at this
    apply hab
    calc a * b = a * (a * b * (a * b)) * b := by rw [hsq', mul_one]
      _ = (a * a) * b * (a * (b * b)) := by group
      _ = b * a := by rw [hsq', hsq', one_mul, mul_one]
  · exact htN (h ▸ mem_top _)

end R2D

end Sec5E

theorem fritzA7Section5E : FritzA7Section5E := by
  intro _ X _ _ _ hX _ S F T₁ h4 hF D hE
  obtain ⟨B⟩ := (⟨h4, hF, D, hE⟩ : Sec5E.Ctx S F T₁).exists_r2D
  exact B.false_of hX

end CFSG.ComponentClassification.HSFLit
