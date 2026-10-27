module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec5ESigma
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec5EKeyA

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace Sec5E

open Sec7 Sec8 T2M

variable {X : Type} [Group X] [Finite X] {S : A7Base X} {F : S.Frame} {T₁ : Subgroup X}

@[expose] def E3sub : Subgroup T2M where
  carrier := {a | a ∈ E3l}
  mul_mem' := fun {a b} ha hb =>
    (by decide +kernel : ∀ a ∈ E3l, ∀ b ∈ E3l, a * b ∈ E3l) a ha b hb
  one_mem' := by decide +kernel
  inv_mem' := fun {a} ha => (by decide +kernel : ∀ a ∈ E3l, a⁻¹ ∈ E3l) a ha

theorem card_E3sub : Nat.card E3sub = 16 := by
  change Nat.card {a : T2M // a ∈ E3l} = 16
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

theorem E3l_comm : ∀ a ∈ E3l, ∀ b ∈ E3l, a * b = b * a := by decide +kernel

theorem E3l_sq : ∀ a ∈ E3l, a * a = 1 := by decide +kernel

namespace Ctx

variable (C : Ctx S F T₁)

@[expose] noncomputable def E₃ : Subgroup X := E3sub.map C.ι

@[expose] noncomputable def A : Subgroup X := C.E₃ ⊔ zpowers C.D.w₂

theorem mem_E₃ {a : T2M} (ha : a ∈ E3l) : C.ι a ∈ C.E₃ := ⟨a, ha, rfl⟩

theorem elemAbelianTwo_E₃ : ElemAbelianTwo C.E₃ := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, E3l_comm a ha b hb]
  · rintro _ ⟨a, ha, rfl⟩
    rw [pow_two, ← map_mul, E3l_sq a ha, map_one]

theorem card_E₃ : Nat.card C.E₃ = 16 := by
  rw [E₃, card_map_of_injective C.ι_injective, card_E3sub]

theorem E₃_le_T₂ : C.E₃ ≤ C.D.T₂ := by
  rintro _ ⟨a, -, rfl⟩; exact C.ι_mem_T₂ a

theorem w₂_not_mem_T₂ : C.D.w₂ ∉ C.D.T₂ := by
  intro h
  have hR : C.D.R = C.D.T₂ := by
    rw [C.D.R_eq]; exact sup_eq_left.mpr (zpowers_le.mpr h)
  have := C.D.card_R
  rw [hR, C.D.card_T₂] at this
  norm_num at this

theorem w₂_comm_E₃ : ∀ a ∈ C.E₃, C.D.w₂ * a = a * C.D.w₂ := by
  rintro _ ⟨a, ha, rfl⟩
  have h := C.w₂_conj a
  rw [T2M.sw2_E3 a ha] at h
  calc C.D.w₂ * C.ι a = C.D.w₂ * C.ι a * C.D.w₂⁻¹ * C.D.w₂ := by group
    _ = C.ι a * C.D.w₂ := by rw [h]

theorem w₂_sq : C.D.w₂ ^ 2 = 1 := by rw [pow_two, C.w₂_mul_w₂]

theorem elemAbelianTwo_A : ElemAbelianTwo C.A :=
  elemAbelianTwo_sup C.elemAbelianTwo_E₃ C.w₂_sq C.w₂_comm_E₃

theorem card_A : Nat.card C.A = 32 := by
  rw [A, card_sup_of_not_mem C.elemAbelianTwo_E₃ C.w₂_sq
    (fun h => C.w₂_not_mem_T₂ (C.E₃_le_T₂ h)) C.w₂_comm_E₃, C.card_E₃]

theorem w₂_mem_A : C.D.w₂ ∈ C.A := mem_sup_right (mem_zpowers _)

theorem E₃_le_A : C.E₃ ≤ C.A := le_sup_left

theorem not_conjTo_of_mem_elem {B : Subgroup X} (hB : ElemAbelianTwo B) (hcard : Nat.card B = 32)
    {a : X} (ha : a ∈ B) : ¬ ConjTo S.t a :=
  not_conjTo_of_elem hB (fun b hb => mem_centralizer_singleton_iff.mpr (hB.comm b hb a ha))
    hcard.symm.le

theorem not_conjTo_of_mem_A {a : X} (ha : a ∈ C.A) : ¬ ConjTo S.t a :=
  not_conjTo_of_mem_elem C.elemAbelianTwo_A C.card_A ha

omit [Finite X] in
theorem elemAbelianTwo_map {B : Subgroup X} (hB : ElemAbelianTwo B) (n : X) :
    ElemAbelianTwo (B.map (MulAut.conj n).toMonoidHom) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hB.comm a ha b hb]
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hB.sq_eq_one a ha, map_one]

theorem not_conjTo_of_conj_mem_A {n a : X} (ha : n⁻¹ * a * n ∈ C.A) : ¬ ConjTo S.t a := by
  refine not_conjTo_of_mem_elem (elemAbelianTwo_map C.elemAbelianTwo_A n)
    (by rw [card_map_of_injective (MulAut.conj n).injective, C.card_A]) ⟨_, ha, ?_⟩
  simp [MulAut.conj_apply, mul_assoc]

end Ctx

theorem tEl_cases : ∀ e ∈ tEl, e = t ∨ e = t * z ∨ e = t * y ∨ e = t * z * y ∨ e = t * k ∨
    e = t * z * k ∨ e = t * y * k ∨ e = t * z * y * k := by decide +kernel

@[expose] def S16Inv (p : SigD) : Prop := ∀ a ∈ p.S16, a * a = 1 ∧ a ≠ 1

instance (p : SigD) : Decidable (S16Inv p) := by unfold S16Inv; infer_instance

theorem s16Inv : ∀ p ∈ repList, S16Inv p := by decide +kernel

theorem conjTo_conj {a : X} (h : ConjTo S.t a) (n : X) : ConjTo S.t (n * a * n⁻¹) := by
  obtain ⟨c, hc⟩ := h
  exact ⟨n * c, by rw [← hc]; group⟩

namespace Ctx

variable (C : Ctx S F T₁)

noncomputable def conjM (n : X) (hn : n ∈ normalizer (C.D.T₂ : Set X)) : T2M →* T2M where
  toFun a := C.ιinv (n * C.ι a * n⁻¹)
  map_one' := by
    apply C.ι_injective
    rw [C.ι_ιinv (conj_mem_of_mem_normalizer hn (C.ι_mem_T₂ 1)), map_one]; group
  map_mul' a b := by
    apply C.ι_injective
    have h : ∀ c : T2M, C.ι (C.ιinv (n * C.ι c * n⁻¹)) = n * C.ι c * n⁻¹ := fun c =>
      C.ι_ιinv (conj_mem_of_mem_normalizer hn (C.ι_mem_T₂ c))
    rw [show C.ι (C.ιinv (n * C.ι a * n⁻¹) * C.ιinv (n * C.ι b * n⁻¹)) =
      C.ι (C.ιinv (n * C.ι a * n⁻¹)) * C.ι (C.ιinv (n * C.ι b * n⁻¹)) from map_mul _ _ _,
      h, h, h, map_mul]
    group

theorem ι_conjM {n : X} (hn : n ∈ normalizer (C.D.T₂ : Set X)) (a : T2M) :
    C.ι (C.conjM n hn a) = n * C.ι a * n⁻¹ :=
  C.ι_ιinv (conj_mem_of_mem_normalizer hn (C.ι_mem_T₂ a))

end Ctx

namespace GD

variable {C : Ctx S F T₁} (G : GD C)

theorem g_t : G.g * S.t * G.g⁻¹ = S.t * F.kF := by
  rw [← C.ι_t, G.hσ, SigD.sig, homOf_t, map_mul, C.ι_t, C.ι_k]

include G in
theorem orbit_t {b : X} (hbE : b ∈ F.E₁)
    (hb : b = S.t ∨ b = S.t * S.z ∨ b = S.t * F.yF ∨ b = S.t * S.z * F.yF) :
    ConjTo S.t b ∧ ConjTo S.t (b * F.kF) := by
  obtain ⟨n, hn, hnb⟩ := (C.D.orbit b hbE).mpr hb
  refine ⟨⟨n, hnb⟩, ⟨n * G.g, ?_⟩⟩
  calc n * G.g * S.t * (n * G.g)⁻¹ = n * (G.g * S.t * G.g⁻¹) * n⁻¹ := by group
    _ = (n * S.t * n⁻¹) * (n * F.kF * n⁻¹) := by rw [G.g_t]; group
    _ = b * F.kF := by rw [hnb, C.D.k_fixed n hn]

include G in
theorem conj_tE {e : T2M} (he : e ∈ tEl) : ConjTo S.t (C.ι e) := by
  have hmem : ∀ c : T2M, InE1 c → C.ι c ∈ F.E₁ := fun c hc => (C.ι_mem_E₁_iff c).mpr hc
  have h1 : C.ι t = S.t := C.ι_t
  have h2 : C.ι (t * z) = S.t * S.z := by rw [map_mul, C.ι_t, C.ι_z]
  have h3 : C.ι (t * y) = S.t * F.yF := by rw [map_mul, C.ι_t, C.ι_y]
  have h4 : C.ι (t * z * y) = S.t * S.z * F.yF := by rw [map_mul, map_mul, C.ι_t, C.ι_z, C.ι_y]
  have o1 := G.orbit_t (h1 ▸ hmem t (by decide +kernel)) (Or.inl rfl)
  have o2 := G.orbit_t (h2 ▸ hmem (t * z) (by decide +kernel)) (Or.inr (Or.inl rfl))
  have o3 := G.orbit_t (h3 ▸ hmem (t * y) (by decide +kernel)) (Or.inr (Or.inr (Or.inl rfl)))
  have o4 := G.orbit_t (h4 ▸ hmem (t * z * y) (by decide +kernel)) (Or.inr (Or.inr (Or.inr rfl)))
  rcases tEl_cases e he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h1]; exact o1.1
  · rw [h2]; exact o2.1
  · rw [h3]; exact o3.1
  · rw [h4]; exact o4.1
  · rw [map_mul, h1, C.ι_k]; exact o1.2
  · rw [map_mul, h2, C.ι_k]; exact o2.2
  · rw [map_mul, h3, C.ι_k]; exact o3.2
  · rw [map_mul, h4, C.ι_k]; exact o4.2

theorem conj_S16 {s : T2M} (hs : s ∈ G.p.S16) : ConjTo S.t (C.ι s) := by
  simp only [SigD.S16, List.mem_append, List.mem_map] at hs
  rcases hs with ((hs | ⟨e, he, rfl⟩) | ⟨e, he, rfl⟩) | ⟨e, he, rfl⟩
  · exact G.conj_tE hs
  · rw [← G.hσ]; exact conjTo_conj (G.conj_tE he) _
  · rw [← C.w₂_conj, ← G.hσ]; exact conjTo_conj (conjTo_conj (G.conj_tE he) _) _
  · rw [← G.hσ, ← C.w₂_conj, ← G.hσ]
    exact conjTo_conj (conjTo_conj (conjTo_conj (G.conj_tE he) _) _) _

theorem conjTo_iff {a : T2M} (ha2 : a * a = 1) (ha1 : a ≠ 1) :
    ConjTo S.t (C.ι a) ↔ a ∈ G.p.S16 := by
  refine ⟨fun h => ?_, G.conj_S16⟩
  rcases SigD.involution_cases G.p G.hp a ha2 ha1 with h1 | h1 | h1
  · exact h1
  · exact absurd h (C.not_conjTo_of_mem_A (C.E₃_le_A (C.mem_E₃ h1)))
  · exfalso
    simp only [SigD.E3'l, List.mem_map] at h1
    obtain ⟨e, he, rfl⟩ := h1
    refine C.not_conjTo_of_conj_mem_A (n := G.g) ?_ h
    rw [← G.hσ]
    have : G.g⁻¹ * (G.g * C.ι e * G.g⁻¹) * G.g = C.ι e := by group
    rw [this]
    exact C.E₃_le_A (C.mem_E₃ he)

include G in
theorem centralizes_of_odd {n : X} (hn : n ∈ normalizer (C.D.T₂ : Set X)) {m : ℕ} (hm : Odd m)
    (hnm : n ^ m = 1) {b : X} (hb : b ∈ C.D.T₂) : n * b * n⁻¹ = b := by
  set ν := C.conjM n hn with hν
  have hinj : Function.Injective ν := by
    intro a b hab
    have := congrArg C.ι hab
    rw [C.ι_conjM, C.ι_conjM] at this
    exact C.ι_injective (by simpa using this)
  have hS : ∀ a ∈ G.p.S16, ν a ∈ G.p.S16 := by
    intro a ha
    obtain ⟨ha2, ha1⟩ := s16Inv G.p G.hp a ha
    have hc := conjTo_conj (G.conj_S16 ha) n
    rw [← C.ι_conjM hn] at hc
    refine (G.conjTo_iff (by rw [← map_mul, ha2, map_one]) (fun h => ha1 ?_)).mp hc
    exact hinj (h.trans (map_one ν).symm)
  have hiter : ∀ j : ℕ, ∀ a, C.ι (ν^[j] a) = n ^ j * C.ι a * (n ^ j)⁻¹ := by
    intro j
    induction j with
    | zero => intro a; simp
    | succ j ih =>
      intro a
      rw [Function.iterate_succ_apply', C.ι_conjM, ih, pow_succ']
      group
  have hνm : ∀ a, ν^[m] a = a := by
    intro a
    apply C.ι_injective
    rw [hiter, hnm]; group
  obtain ⟨a, rfl⟩ := C.exists_ι hb
  rw [← C.ι_conjM hn, SigD.eq_self_of_odd G.hp ν hinj hS hm hνm a]

end GD

end Sec5E

end CFSG.ComponentClassification.HSFLit
