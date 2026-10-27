module

public import CFSG.LargeExtraspecial.Timmesfeld.FStar

public section

namespace CFSG.LargeExtraspecial.RepresentationSupport

namespace ExtraspecialInvolutionDoubleCentralizer

theorem dual_lemma_aux {K V : Type} [Field K] [AddCommGroup V] [Module K V] [Finite V]
    (B : V →ₗ[K] V →ₗ[K] K) (hnd : ∀ x, B x = 0 → x = 0) (N : Submodule K V) (c : V)
    (hc : c ∉ N) : ∃ x, (∀ n ∈ N, B x n = 0) ∧ B x c ≠ 0 := by
  haveI : Module.Finite K V := Module.Finite.of_finite
  obtain ⟨f, hfc, hfN⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hc inferInstance
  have hinj : Function.Injective B := by
    rw [injective_iff_map_eq_zero]
    exact fun x hx => hnd x hx
  have hsurj : Function.Surjective B :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (Subspace.dual_finrank_eq (K := K) (V := V)).symm).1 hinj
  obtain ⟨x, hx⟩ := hsurj f
  have hB : ∀ y, B x y = f y := fun y => by rw [hx]
  refine ⟨x, fun n hn => ?_, by rw [hB]; exact hfc⟩
  rw [hB]
  have : f n ∈ N.map f := Submodule.mem_map_of_mem hn
  rw [hfN] at this
  simpa using this

theorem dual_lemma (V : Type) [AddCommGroup V] [Finite V] (h2 : ∀ v : V, 2 • v = 0)
    (B : V →+ V →+ ZMod 2) (hnd : ∀ x, B x = 0 → x = 0) (N : AddSubgroup V) (c : V)
    (hc : c ∉ N) : ∃ x, (∀ n ∈ N, B x n = 0) ∧ B x c ≠ 0 := by
  letI : Module (ZMod 2) V := AddCommGroup.zmodModule h2
  have hz : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  let Ψ : V → Module.Dual (ZMod 2) V := fun x =>
    { toFun := B x, map_add' := map_add _, map_smul' := by
        intro c y
        rcases hz c with rfl | rfl <;> simp }
  let Φ : V →ₗ[ZMod 2] Module.Dual (ZMod 2) V :=
    { toFun := Ψ
      map_add' := by intro x y; ext z; simp [Ψ]
      map_smul' := by
        intro c x; ext z
        rcases hz c with rfl | rfl <;> simp [Ψ] }
  have hc' : c ∉ AddSubgroup.toZModSubmodule (2:ℕ) N := hc
  obtain ⟨x, hx1, hx2⟩ := dual_lemma_aux Φ (fun x hx => hnd x (by
    ext y; have := congrArg (fun g => g y) hx; simpa [Φ, Ψ] using this)) _ c hc'
  exact ⟨x, fun n hn => hx1 n hn, hx2⟩

open Subgroup

open scoped commutatorElement

variable {E : Type} [Group E]

structure Setup (E : Type) [Group E] : Prop where
  card_center : Nat.card (center E) = 2
  comm_mem : ∀ x y : E, ⁅x, y⁆ ∈ center E

variable (hE : Setup E)

include hE

theorem sq_center [Finite E] {z : E} (hz : z ∈ center E) : z * z = 1 := by
  have h := pow_card_eq_one' (G := center E) (x := (⟨z, hz⟩ : center E))
  rw [hE.card_center] at h
  have := congrArg Subtype.val h
  simpa [pow_two] using this

theorem center_eq [Finite E] {a b : E} (ha : a ∈ center E) (hb : b ∈ center E) (ha1 : a ≠ 1)
    (hb1 : b ≠ 1) : a = b := by
  obtain ⟨y, hy, huniq⟩ := (Nat.card_eq_two_iff' (1 : center E)).1 hE.card_center
  have h1 := huniq ⟨a, ha⟩ (fun h => ha1 (by simpa using congrArg Subtype.val h))
  have h2 := huniq ⟨b, hb⟩ (fun h => hb1 (by simpa using congrArg Subtype.val h))
  have := h1.trans h2.symm
  simpa using congrArg Subtype.val this

theorem comm_mul_left (x y z : E) : ⁅x * y, z⁆ = ⁅x, z⁆ * ⁅y, z⁆ := by
  have hc := hE.comm_mem y z
  have h : x * ⁅y, z⁆ * x⁻¹ = ⁅y, z⁆ := by
    rw [mul_inv_eq_iff_eq_mul]; exact mem_center_iff.1 hc x
  calc ⁅x * y, z⁆ = x * ⁅y, z⁆ * x⁻¹ * ⁅x, z⁆ := by
        simp only [commutatorElement_def]; group
    _ = _ := by rw [h]; exact mem_center_iff.1 (hE.comm_mem x z) _

theorem comm_mul_right (x y z : E) : ⁅x, y * z⁆ = ⁅x, y⁆ * ⁅x, z⁆ := by
  have hc := hE.comm_mem x z
  have h : y * ⁅x, z⁆ * y⁻¹ = ⁅x, z⁆ := by
    rw [mul_inv_eq_iff_eq_mul]; exact mem_center_iff.1 hc y
  calc ⁅x, y * z⁆ = ⁅x, y⁆ * (y * ⁅x, z⁆ * y⁻¹) := by
        simp only [commutatorElement_def]; group
    _ = _ := by rw [h]

open Classical in
noncomputable def eps (z : E) : ZMod 2 := if z = 1 then 0 else 1

omit hE in
theorem eps_one : eps (1 : E) = 0 := by simp [eps]

theorem eps_mul [Finite E] {a b : E} (ha : a ∈ center E) (hb : b ∈ center E) :
    eps (a * b) = eps a + eps b := by
  by_cases ha1 : a = 1
  · subst ha1; rw [one_mul, eps_one, zero_add]
  by_cases hb1 : b = 1
  · subst hb1; rw [mul_one, eps_one, add_zero]
  have := center_eq hE ha hb ha1 hb1
  subst this
  have h1 := sq_center hE ha
  simp [eps, h1, ha1]
  decide

omit hE in
theorem eps_eq_zero {a : E} : eps a = 0 ↔ a = 1 := by
  unfold eps; split_ifs with h <;> simp [h]

noncomputable def om (x y : E) : ZMod 2 := eps ⁅x, y⁆

theorem om_mul_left [Finite E] (x y z : E) : om (x * y) z = om x z + om y z := by
  unfold om
  rw [comm_mul_left hE]
  exact eps_mul hE (hE.comm_mem _ _) (hE.comm_mem _ _)

theorem om_mul_right [Finite E] (x y z : E) : om x (y * z) = om x y + om x z := by
  unfold om
  rw [comm_mul_right hE]
  exact eps_mul hE (hE.comm_mem _ _) (hE.comm_mem _ _)

omit hE in
theorem om_eq_zero {x y : E} : om x y = 0 ↔ x * y = y * x := by
  unfold om; rw [eps_eq_zero, commutatorElement_eq_one_iff_mul_comm]

theorem om_center_left [Finite E] (x : E) {z : E} (hz : z ∈ center E) (y : E) :
    om (x * z) y = om x y := by
  rw [om_mul_left hE, (om_eq_zero).2 (mem_center_iff.1 hz y).symm, add_zero]

theorem om_center_right [Finite E] (x y : E) {z : E} (hz : z ∈ center E) :
    om x (y * z) = om x y := by
  rw [om_mul_right hE, (om_eq_zero).2 (mem_center_iff.1 hz x), add_zero]

theorem sq_mem_center [Finite E] (e : E) : e * e ∈ center E := by
  rw [mem_center_iff]
  intro g
  have : om (e * e) g = 0 := by
    rw [om_mul_left hE]
    simp only [← two_mul]
    have : (2 : ZMod 2) = 0 := by decide
    rw [this, zero_mul]
  have := (om_eq_zero).1 this
  exact this.symm

@[reducible] def qcg : CommGroup (E ⧸ center E) :=
  { (inferInstance : Group (E ⧸ center E)) with
    mul_comm := by
      intro a b
      induction a using QuotientGroup.induction_on with | _ x
      induction b using QuotientGroup.induction_on with | _ y
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
      have := hE.comm_mem y⁻¹ x⁻¹
      convert this using 1
      simp [commutatorElement_def, mul_assoc] }

theorem om_wd [Finite E] (a₁ b₁ a₂ b₂ : E)
    (ha : QuotientGroup.leftRel (center E) a₁ a₂) (hb : QuotientGroup.leftRel (center E) b₁ b₂) :
    om a₁ b₁ = om a₂ b₂ := by
  rw [QuotientGroup.leftRel_apply] at ha hb
  have h1 : a₂ = a₁ * (a₁⁻¹ * a₂) := by group
  have h2 : b₂ = b₁ * (b₁⁻¹ * b₂) := by group
  rw [h1, h2, om_center_left hE _ ha, om_center_right hE _ _ hb]

@[expose] noncomputable def bq [Finite E] : E ⧸ center E → E ⧸ center E → ZMod 2 :=
  Quotient.lift₂ (om : E → E → ZMod 2) (om_wd hE)

theorem key [Finite E] (S : Subgroup E) (hS : center E ≤ S) (c : E) (hc : c ∉ S) :
    ∃ x : E, (∀ s ∈ S, ⁅x, s⁆ = 1) ∧ ⁅x, c⁆ ≠ 1 := by
  letI : CommGroup (E ⧸ center E) := qcg hE
  have hmul_l : ∀ p q r : E ⧸ center E, bq hE (p * q) r = bq hE p r + bq hE q r := by
    intro p q r
    induction p using QuotientGroup.induction_on with | _ x
    induction q using QuotientGroup.induction_on with | _ y
    induction r using QuotientGroup.induction_on with | _ z
    rw [← QuotientGroup.mk_mul]
    exact om_mul_left hE x y z
  have hmul_r : ∀ p q r : E ⧸ center E, bq hE p (q * r) = bq hE p q + bq hE p r := by
    intro p q r
    induction p using QuotientGroup.induction_on with | _ x
    induction q using QuotientGroup.induction_on with | _ y
    induction r using QuotientGroup.induction_on with | _ z
    rw [← QuotientGroup.mk_mul]
    exact om_mul_right hE x y z
  let B1 : Additive (E ⧸ center E) → Additive (E ⧸ center E) →+ ZMod 2 := fun v =>
    AddMonoidHom.mk' (fun w => bq hE (Additive.toMul v) (Additive.toMul w))
      (fun w w' => hmul_r _ _ _)
  let B : Additive (E ⧸ center E) →+ Additive (E ⧸ center E) →+ ZMod 2 :=
    { toFun := B1
      map_zero' := by
        refine AddMonoidHom.ext fun w => ?_
        show bq hE 1 (Additive.toMul w) = 0
        have := hmul_l 1 1 (Additive.toMul w)
        simpa using this
      map_add' := fun v v' => by
        refine AddMonoidHom.ext fun w => ?_
        exact hmul_l _ _ _ }
  let N : AddSubgroup (Additive (E ⧸ center E)) :=
    Subgroup.toAddSubgroup (S.map (QuotientGroup.mk' (center E)))
  have hmemN : ∀ e : E, Additive.ofMul (e : E ⧸ center E) ∈ N ↔ e ∈ S := by
    intro e
    show (e : E ⧸ center E) ∈ S.map (QuotientGroup.mk' (center E)) ↔ _
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨s, hs, hse⟩
      have : (s : E ⧸ center E) = e := hse
      rw [QuotientGroup.eq] at this
      have h3 : s⁻¹ * e ∈ S := hS this
      have := S.mul_mem hs h3
      simpa using this
    · intro h; exact ⟨e, h, rfl⟩
  have h2 : ∀ v : Additive (E ⧸ center E), 2 • v = 0 := by
    intro v
    obtain ⟨e, he⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
    have : v = Additive.ofMul (e : E ⧸ center E) := by rw [he]; rfl
    subst this
    show Additive.ofMul ((e : E ⧸ center E) ^ 2) = 0
    rw [pow_two, ← QuotientGroup.mk_mul]
    show ((e * e : E) : E ⧸ center E) = 1
    exact (QuotientGroup.eq_one_iff _).2 (sq_mem_center hE e)
  have hnd : ∀ x, B x = 0 → x = 0 := by
    intro x hx
    obtain ⟨e, he⟩ := QuotientGroup.mk_surjective (Additive.toMul x)
    have : x = Additive.ofMul (e : E ⧸ center E) := by rw [he]; rfl
    subst this
    show Additive.ofMul (e : E ⧸ center E) = Additive.ofMul 1
    congr 1
    apply (QuotientGroup.eq_one_iff _).2
    rw [mem_center_iff]
    intro g
    have := congrArg (fun f => f (Additive.ofMul (g : E ⧸ center E))) hx
    have h0 : om e g = 0 := this
    exact (om_eq_zero.1 h0).symm
  obtain ⟨c', hc'⟩ := QuotientGroup.mk_surjective (Additive.toMul (Additive.ofMul (c : E ⧸ center E)))
  obtain ⟨x, hx1, hx2⟩ := dual_lemma _ h2 B hnd N (Additive.ofMul (c : E ⧸ center E))
    (fun h => hc ((hmemN c).1 h))
  obtain ⟨e, he⟩ := QuotientGroup.mk_surjective (Additive.toMul x)
  have hxe : x = Additive.ofMul (e : E ⧸ center E) := by rw [he]; rfl
  subst hxe
  refine ⟨e, fun s hs => ?_, fun h => hx2 ?_⟩
  · have := hx1 _ ((hmemN s).2 hs)
    have h0 : om e s = 0 := this
    rw [om_eq_zero] at h0
    exact commutatorElement_eq_one_iff_mul_comm.2 h0
  · show om e c = 0
    unfold om; rw [h, eps_one]

end ExtraspecialInvolutionDoubleCentralizer

open CFSG.LargeExtraspecial.Timmesfeld Subgroup

open scoped commutatorElement

end CFSG.LargeExtraspecial.RepresentationSupport
