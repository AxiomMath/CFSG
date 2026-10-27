module

public import CFSG.GF2Type.Smith1979.CaseIIBAlt
public import CFSG.GF2Type.Smith1979.CaseIIBCtx
public import Mathlib.FieldTheory.Finiteness

public section

namespace CFSG.GF2Type.Smith1979.Case2

namespace PhaseB

open Module QuadraticMap

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  {q : QuadraticForm (ZMod 2) V} {a : V} {E : Submodule (ZMod 2) V}
  {L : Subgroup (V ≃ₗ[ZMod 2] V)}

structure Aux (q : QuadraticForm (ZMod 2) V) (a : V) (E : Submodule (ZMod 2) V) where
  P : V →ₗ[ZMod 2] V
  b : V
  P_E : ∀ e ∈ E, P e = 0
  sub_P : ∀ u, u - P u ∈ E
  polar_b : polar q a b = 1

theorem Ctx.nonempty_aux (C : Ctx q a E L) : Nonempty (Aux q a E) := by
  obtain ⟨F, hF⟩ := Submodule.exists_isCompl E
  obtain ⟨b, hb⟩ := C.exists_partner
  exact ⟨⟨F.projection E hF.symm, b, fun e he => Submodule.projection_apply_of_mem_right _ he,
    Submodule.sub_projection_mem hF.symm, hb⟩⟩

private theorem zmod2_cases' (c : ZMod 2) : c = 0 ∨ c = 1 := by
  revert c
  decide

namespace Aux

variable (X : Aux q a E)

@[expose] def vec (s : V ≃ₗ[ZMod 2] V) : V := X.P (s X.b - X.b)

theorem sub_b_mem_A (C : Ctx q a E L) {s : V ≃ₗ[ZMod 2] V} (hs : s ∈ L) :
    s X.b - X.b ∈ Asp q a := by
  rw [mem_Asp, ← C.polar_sub_swap hs a X.b, C.apply_a s hs, sub_self, polar_zero_left]

theorem vec_mem_A (C : Ctx q a E L) {s : V ≃ₗ[ZMod 2] V} (hs : s ∈ L) : X.vec s ∈ Asp q a := by
  have h2 : X.P (s X.b - X.b) = (s X.b - X.b) - ((s X.b - X.b) - X.P (s X.b - X.b)) := by abel
  rw [vec, h2]
  exact sub_mem (X.sub_b_mem_A C hs) (C.E_le_A (X.sub_P _))

theorem sub_apply_vec (C : Ctx q a E L) {s : V ≃ₗ[ZMod 2] V} (hs : s ∈ L) {e : V} (he : e ∈ E) :
    s e - e = polar q e (X.vec s) • a := by
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (C.sub_E s hs e he)
  have h1 : polar q e (X.vec s) = c := by
    have h2 : X.vec s = (s X.b - X.b) - ((s X.b - X.b) - X.P (s X.b - X.b)) := by
      rw [vec]
      abel
    rw [h2, polar_sub_right, C.polar_E he (X.sub_P _), sub_zero, ← C.polar_sub_swap hs e X.b,
      ← hc, polar_smul_left, X.polar_b, smul_eq_mul, mul_one]
  rw [h1, hc]

theorem vec_mul (C : Ctx q a E L) {s s' : V ≃ₗ[ZMod 2] V} (hs : s ∈ L) (hs' : s' ∈ L) :
    X.vec (s * s') = X.vec s + X.vec s' := by
  have hE : s (s' X.b - X.b) - (s' X.b - X.b) ∈ E :=
    C.sub_A s hs _ (mem_Asp.mp (X.sub_b_mem_A C hs'))
  have h : (s * s') X.b - X.b = (s X.b - X.b) + (s' X.b - X.b) +
      (s (s' X.b - X.b) - (s' X.b - X.b)) := by
    simp only [LinearEquiv.mul_apply, map_sub]
    abel
  rw [vec, h, map_add, map_add, X.P_E _ hE, add_zero]
  rfl

theorem vec_one : X.vec 1 = 0 := by
  simp [vec]

theorem eq_one_of_vec_mem_E (C : Ctx q a E L) {s : V ≃ₗ[ZMod 2] V} (hs : s ∈ L)
    (h : X.vec s ∈ E) : s = 1 := by
  refine C.faithful s hs fun e he => ?_
  have := X.sub_apply_vec C hs he
  rw [C.polar_E he h, zero_smul] at this
  exact sub_eq_zero.mp this

theorem eq_of_vec_eq (C : Ctx q a E L) {s s' : V ≃ₗ[ZMod 2] V} (hs : s ∈ L) (hs' : s' ∈ L)
    (h : X.vec s = X.vec s') : s = s' := by
  have h1 : X.vec (s * s') = 0 := by rw [X.vec_mul C hs hs', h, ZModModule.add_self]
  have h2 : s * s' = 1 := X.eq_one_of_vec_mem_E C (mul_mem hs hs') (h1 ▸ zero_mem E)
  exact (mul_left_cancel (h2.trans (C.mul_self s hs).symm : s * s' = s * s)).symm

end Aux

@[expose] def Wsp (C : Ctx q a E L) (X : Aux q a E) : Submodule (ZMod 2) V where
  carrier := {w | ∃ s ∈ L, X.vec s = w}
  add_mem' := by
    rintro _ _ ⟨s, hs, rfl⟩ ⟨s', hs', rfl⟩
    exact ⟨s * s', mul_mem hs hs', X.vec_mul C hs hs'⟩
  zero_mem' := ⟨1, one_mem L, X.vec_one⟩
  smul_mem' := by
    rintro c _ ⟨s, hs, rfl⟩
    rcases zmod2_cases' c with rfl | rfl
    · exact ⟨1, one_mem L, by rw [zero_smul]; exact X.vec_one⟩
    · exact ⟨s, hs, by rw [one_smul]⟩

theorem Wsp_le_A (C : Ctx q a E L) (X : Aux q a E) : Wsp C X ≤ Asp q a := by
  rintro _ ⟨s, hs, rfl⟩
  exact X.vec_mem_A C hs

theorem Wsp_inf_E (C : Ctx q a E L) (X : Aux q a E) : Wsp C X ⊓ E = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨⟨s, hs, rfl⟩, hwE⟩
  rw [Submodule.mem_bot, X.eq_one_of_vec_mem_E C hs hwE]
  exact X.vec_one

@[expose] noncomputable def eqv (C : Ctx q a E L) (X : Aux q a E) : L ≃ Wsp C X :=
  Equiv.ofBijective (fun s => ⟨X.vec s, s, s.2, rfl⟩)
    ⟨fun s s' h => Subtype.ext (X.eq_of_vec_eq C s.2 s'.2 (congrArg Subtype.val h)),
      fun ⟨_, s, hs, h⟩ => ⟨⟨s, hs⟩, Subtype.ext h⟩⟩

variable [FiniteDimensional (ZMod 2) V]

theorem finrank_Wsp (C : Ctx q a E L) (X : Aux q a E) : finrank (ZMod 2) (Wsp C X) = 5 := by
  have h1 : Nat.card (Wsp C X) = 32 := by
    rw [← Nat.card_congr (eqv C X)]
    exact C.card_L
  have h2 : Nat.card (Wsp C X) = 2 ^ finrank (ZMod 2) (Wsp C X) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have h3 : (2 : ℕ) ^ finrank (ZMod 2) (Wsp C X) = 2 ^ 5 := by
    rw [← h2, h1]
    norm_num
  exact Nat.pow_right_injective le_rfl h3

theorem A_eq_sup (C : Ctx q a E L) (X : Aux q a E) : Asp q a = E ⊔ Wsp C X := by
  symm
  refine Submodule.eq_of_le_of_finrank_eq (sup_le C.E_le_A (Wsp_le_A C X)) ?_
  have h := Submodule.finrank_sup_add_finrank_inf_eq E (Wsp C X)
  rw [inf_comm, Wsp_inf_E C X, finrank_bot, C.finrank_E, finrank_Wsp C X] at h
  rw [C.finrank_A]
  omega

@[expose] noncomputable def Sv (C : Ctx q a E L) (X : Aux q a E) (w : Wsp C X) :
    V ≃ₗ[ZMod 2] V :=
  ((eqv C X).symm w : L)

theorem Sv_mem (C : Ctx q a E L) (X : Aux q a E) (w : Wsp C X) : Sv C X w ∈ L :=
  ((eqv C X).symm w).2

theorem vec_Sv (C : Ctx q a E L) (X : Aux q a E) (w : Wsp C X) : X.vec (Sv C X w) = w :=
  congrArg Subtype.val ((eqv C X).apply_symm_apply w)

theorem Sv_vec (C : Ctx q a E L) (X : Aux q a E) {s : V ≃ₗ[ZMod 2] V} (hs : s ∈ L)
    (h : X.vec s ∈ Wsp C X) : Sv C X ⟨X.vec s, h⟩ = s :=
  X.eq_of_vec_eq C (Sv_mem C X _) hs (vec_Sv C X _)

theorem Sv_add (C : Ctx q a E L) (X : Aux q a E) (w w' : Wsp C X) :
    Sv C X (w + w') = Sv C X w * Sv C X w' :=
  X.eq_of_vec_eq C (Sv_mem C X _) (mul_mem (Sv_mem C X w) (Sv_mem C X w'))
    (by rw [vec_Sv, X.vec_mul C (Sv_mem C X w) (Sv_mem C X w'), vec_Sv, vec_Sv]; rfl)

theorem Sv_zero (C : Ctx q a E L) (X : Aux q a E) : Sv C X 0 = 1 :=
  X.eq_of_vec_eq C (Sv_mem C X _) (one_mem L) (by rw [vec_Sv, X.vec_one]; rfl)

theorem eq_zero_of_Sv_eq_one (C : Ctx q a E L) (X : Aux q a E) {w : Wsp C X}
    (h : Sv C X w = 1) : w = 0 := by
  have := vec_Sv C X w
  rw [h, X.vec_one] at this
  exact Subtype.ext this.symm

@[expose] noncomputable def Tfun (C : Ctx q a E L) (X : Aux q a E) (w₁ w₂ w₃ : Wsp C X) :
    ZMod 2 :=
  polar q (w₂ : V) (Sv C X w₁ (w₃ : V) - w₃)

theorem Tfun_add₁ (C : Ctx q a E L) (X : Aux q a E) (w₁ w₁' w₂ w₃ : Wsp C X) :
    Tfun C X (w₁ + w₁') w₂ w₃ = Tfun C X w₁ w₂ w₃ + Tfun C X w₁' w₂ w₃ := by
  have hs := Sv_mem C X w₁
  have hs' := Sv_mem C X w₁'
  have hx := Wsp_le_A C X w₂.2
  have hy := Wsp_le_A C X w₃.2
  have hE : Sv C X w₁' (w₃ : V) - w₃ ∈ E := C.sub_A _ hs' _ (mem_Asp.mp hy)
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (C.sub_E _ hs _ hE)
  have h : (Sv C X w₁ * Sv C X w₁') (w₃ : V) - w₃ =
      (Sv C X w₁ w₃ - w₃) + (Sv C X w₁' w₃ - w₃) +
        (Sv C X w₁ (Sv C X w₁' w₃ - w₃) - (Sv C X w₁' w₃ - w₃)) := by
    simp only [LinearEquiv.mul_apply, map_sub]
    abel
  have hxa : polar q (w₂ : V) a = 0 := by
    rw [polar_comm]
    exact mem_Asp.mp hx
  unfold Tfun
  rw [Sv_add, h, polar_add_right, polar_add_right, ← hc, polar_smul_right, hxa, smul_zero,
    add_zero]

theorem Tfun_smul₁ (C : Ctx q a E L) (X : Aux q a E) (c : ZMod 2) (w₁ w₂ w₃ : Wsp C X) :
    Tfun C X (c • w₁) w₂ w₃ = c • Tfun C X w₁ w₂ w₃ := by
  rcases zmod2_cases' c with rfl | rfl
  · simp [Tfun, Sv_zero]
  · simp

theorem Tfun_add₂ (C : Ctx q a E L) (X : Aux q a E) (w₁ w₂ w₂' w₃ : Wsp C X) :
    Tfun C X w₁ (w₂ + w₂') w₃ = Tfun C X w₁ w₂ w₃ + Tfun C X w₁ w₂' w₃ := by
  unfold Tfun
  rw [Submodule.coe_add, polar_add_left]

theorem Tfun_smul₂ (C : Ctx q a E L) (X : Aux q a E) (c : ZMod 2) (w₁ w₂ w₃ : Wsp C X) :
    Tfun C X w₁ (c • w₂) w₃ = c • Tfun C X w₁ w₂ w₃ := by
  unfold Tfun
  rw [Submodule.coe_smul, polar_smul_left]

theorem Tfun_add₃ (C : Ctx q a E L) (X : Aux q a E) (w₁ w₂ w₃ w₃' : Wsp C X) :
    Tfun C X w₁ w₂ (w₃ + w₃') = Tfun C X w₁ w₂ w₃ + Tfun C X w₁ w₂ w₃' := by
  unfold Tfun
  rw [← polar_add_right]
  congr 1
  simp only [Submodule.coe_add, map_add]
  abel

theorem Tfun_smul₃ (C : Ctx q a E L) (X : Aux q a E) (c : ZMod 2) (w₁ w₂ w₃ : Wsp C X) :
    Tfun C X w₁ w₂ (c • w₃) = c • Tfun C X w₁ w₂ w₃ := by
  unfold Tfun
  have h : Sv C X w₁ ((c • w₃ : Wsp C X) : V) - ((c • w₃ : Wsp C X) : V) =
      c • (Sv C X w₁ (w₃ : V) - w₃) := by
    simp only [Submodule.coe_smul, map_smul, smul_sub]
  rw [h, polar_smul_right]

@[expose] noncomputable def Tform (C : Ctx q a E L) (X : Aux q a E) :
    Wsp C X →ₗ[ZMod 2] Wsp C X →ₗ[ZMod 2] Wsp C X →ₗ[ZMod 2] ZMod 2 where
  toFun w₁ := LinearMap.mk₂ (ZMod 2) (Tfun C X w₁) (Tfun_add₂ C X w₁) (Tfun_smul₂ C X · w₁)
    (Tfun_add₃ C X w₁) (Tfun_smul₃ C X · w₁)
  map_add' w₁ w₁' := LinearMap.ext₂ fun w₂ w₃ => Tfun_add₁ C X w₁ w₁' w₂ w₃
  map_smul' c w₁ := LinearMap.ext₂ fun w₂ w₃ => Tfun_smul₁ C X c w₁ w₂ w₃

theorem Tform_apply (C : Ctx q a E L) (X : Aux q a E) (w₁ w₂ w₃ : Wsp C X) :
    Tform C X w₁ w₂ w₃ = polar q (w₂ : V) (Sv C X w₁ (w₃ : V) - w₃) := rfl

theorem Tform_self₁ (C : Ctx q a E L) (X : Aux q a E) (x z : Wsp C X) : Tform C X x x z = 0 := by
  rw [Tform_apply]
  have hs := Sv_mem C X x
  have hv := vec_Sv C X x
  generalize Sv C X x = s at hs hv ⊢
  have hz : (z : V) ∈ Asp q a := Wsp_le_A C X z.2
  have he : s z - z ∈ E := C.sub_A s hs z (mem_Asp.mp hz)
  have h1 := X.sub_apply_vec C hs he
  rw [C.sub_sq hs, sub_self, hv] at h1
  have h2 : polar q (s z - z) (x : V) = 0 := (smul_eq_zero.mp h1.symm).resolve_right C.a_ne
  rw [polar_comm]
  exact h2

theorem Tform_self₂ (C : Ctx q a E L) (X : Aux q a E) (x y : Wsp C X) : Tform C X x y y = 0 := by
  rw [Tform_apply]
  have hs := Sv_mem C X x
  generalize Sv C X x = s at hs ⊢
  have hy : (y : V) ∈ Asp q a := Wsp_le_A C X y.2
  have hE : s y - y ∈ E := C.sub_A s hs y (mem_Asp.mp hy)
  have h1 : q (s y - y) = polar q (y : V) (s y - y) := by
    rw [polar_sub_right, polar_self_eq_zero, sub_zero, polar_comm q (y : V) (s y),
      ZModModule.sub_eq_add, QuadraticMap.map_add q (s y) y, C.q_apply s hs y,
      ZModModule.add_self, zero_add]
  rw [← h1]
  exact C.q_E _ hE

theorem Tform_swap₁₂ (C : Ctx q a E L) (X : Aux q a E) (x y z : Wsp C X) :
    Tform C X x y z = Tform C X y x z := by
  rw [Tform_apply, Tform_apply]
  have hs := Sv_mem C X x
  have hs' := Sv_mem C X y
  have hvx := vec_Sv C X x
  have hvy := vec_Sv C X y
  have hcomm := C.comm _ hs _ hs'
  generalize Sv C X x = s at hs hvx hcomm ⊢
  generalize Sv C X y = s' at hs' hvy hcomm ⊢
  have hz : (z : V) ∈ Asp q a := Wsp_le_A C X z.2
  have hex : s z - z ∈ E := C.sub_A s hs z (mem_Asp.mp hz)
  have hey : s' z - z ∈ E := C.sub_A s' hs' z (mem_Asp.mp hz)
  have e1 := X.sub_apply_vec C hs' hex
  have e2 := X.sub_apply_vec C hs hey
  rw [hvy] at e1
  rw [hvx] at e2
  have hz2 : s' (s z) = s (s' z) := by
    have := congrArg (fun f : V ≃ₗ[ZMod 2] V => f z) hcomm
    simpa using this.symm
  have h : polar q (y : V) (s z - z) • a = polar q (x : V) (s' z - z) • a := by
    rw [polar_comm q (y : V), polar_comm q (x : V), ← e1, ← e2]
    simp only [map_sub, hz2]
    abel
  exact smul_left_injective (ZMod 2) C.a_ne h

theorem Rsp_eq (C : Ctx q a E L) (X : Aux q a E) (w : Wsp C X) :
    Rsp q a (Sv C X w) = E ⊔ (rad (Tform C X) w).map (Wsp C X).subtype := by
  have hs := Sv_mem C X w
  have hA := A_eq_sup C X
  refine le_antisymm (fun x hx => ?_) (sup_le (fun e he => ?_) ?_)
  · obtain ⟨hxA, -⟩ := mem_Rsp.mp hx
    rw [hA] at hxA
    obtain ⟨e, he, z, hz, rfl⟩ := Submodule.mem_sup.mp hxA
    have hER : e ∈ Rsp q a (Sv C X w) := mem_Rsp.mpr ⟨C.E_le_A he, C.sub_E _ hs e he⟩
    have hzR := mem_Rsp.mp (sub_mem hx hER)
    rw [add_sub_cancel_left] at hzR
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hzR.2
    refine Submodule.mem_sup.mpr ⟨e, he, z, ⟨⟨z, hz⟩, ?_, rfl⟩, rfl⟩
    rw [SetLike.mem_coe, mem_rad]
    intro z'
    rw [trilinear_swap_right _ (Tform_self₂ C X), Tform_apply, ← hc, polar_smul_right,
      polar_comm, mem_Asp.mp (Wsp_le_A C X z'.2), smul_zero]
  · exact mem_Rsp.mpr ⟨C.E_le_A he, C.sub_E _ hs e he⟩
  · rintro _ ⟨y, hy, rfl⟩
    have hy : y ∈ rad (Tform C X) w := hy
    show (y : V) ∈ Rsp q a (Sv C X w)
    refine mem_Rsp.mpr ⟨Wsp_le_A C X y.2, ?_⟩
    have hyA : (y : V) ∈ Asp q a := Wsp_le_A C X y.2
    have hE : Sv C X w y - y ∈ E := C.sub_A _ hs _ (mem_Asp.mp hyA)
    refine C.perp_A fun x hx => ?_
    rw [A_eq_sup C X] at hx
    obtain ⟨e, he, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    rw [polar_add_left, C.polar_E he hE, zero_add]
    have := mem_rad.mp hy ⟨z, hz⟩
    rw [trilinear_swap_right _ (Tform_self₂ C X), Tform_apply] at this
    exact this

theorem finrank_Rsp [FiniteDimensional (ZMod 2) V] (C : Ctx q a E L) (X : Aux q a E)
    (w : Wsp C X) :
    finrank (ZMod 2) (Rsp q a (Sv C X w)) = 6 + finrank (ZMod 2) (rad (Tform C X) w) := by
  rw [Rsp_eq C X w]
  have h := Submodule.finrank_sup_add_finrank_inf_eq E
    ((rad (Tform C X) w).map (Wsp C X).subtype)
  have hdisj : E ⊓ (rad (Tform C X) w).map (Wsp C X).subtype = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨hvE, y, -, rfl⟩
    have : (y : V) ∈ Wsp C X ⊓ E := ⟨y.2, hvE⟩
    rwa [Wsp_inf_E C X] at this
  rw [hdisj, finrank_bot, Submodule.finrank_map_subtype_eq, C.finrank_E] at h
  omega

theorem finrank_range_add_finrank_rad [FiniteDimensional (ZMod 2) V] (C : Ctx q a E L)
    (X : Aux q a E) {w : Wsp C X} (hw : w ≠ 0) :
    finrank (ZMod 2) (LinearMap.range ((Sv C X w : V →ₗ[ZMod 2] V) - 1)) +
      finrank (ZMod 2) (rad (Tform C X) w) = 7 := by
  have h1 : Sv C X w ≠ 1 := fun h => hw (eq_zero_of_Sv_eq_one C X h)
  have := C.finrank_range_add_finrank_Rsp (Sv_mem C X w) h1
  rw [finrank_Rsp C X w] at this
  omega

theorem Ctx.exists_model [FiniteDimensional (ZMod 2) V] (C : Ctx q a E L) :
    ∃ (W : Submodule (ZMod 2) V) (T : W →ₗ[ZMod 2] W →ₗ[ZMod 2] W →ₗ[ZMod 2] ZMod 2)
      (S : W → V ≃ₗ[ZMod 2] V),
      finrank (ZMod 2) W = 5 ∧ (∀ x z, T x x z = 0) ∧ (∀ x y, T x y y = 0) ∧
      (∀ x y z, T x y z = T y x z) ∧ (∀ w, S w ∈ L) ∧ (∀ s ∈ L, ∃ w, S w = s) ∧
      (∀ w w', S (w + w') = S w * S w') ∧ S 0 = 1 ∧ (∀ w, S w = 1 → w = 0) ∧
      ∀ w, w ≠ 0 → finrank (ZMod 2) (LinearMap.range ((S w : V →ₗ[ZMod 2] V) - 1)) +
        finrank (ZMod 2) (rad T w) = 7 := by
  obtain ⟨X⟩ := C.nonempty_aux
  exact ⟨Wsp C X, Tform C X, Sv C X, finrank_Wsp C X, Tform_self₁ C X, Tform_self₂ C X,
    Tform_swap₁₂ C X, Sv_mem C X, fun s hs => ⟨⟨X.vec s, s, hs, rfl⟩, Sv_vec C X hs _⟩,
    Sv_add C X, Sv_zero C X, fun w => eq_zero_of_Sv_eq_one C X,
    fun w hw => finrank_range_add_finrank_rad C X hw⟩

end PhaseB

end CFSG.GF2Type.Smith1979.Case2
