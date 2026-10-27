module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6EModel

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6E

section PlaneFacts
variable {M : Type*} [AddCommGroup M] [Module (ZMod 3) M] [Finite M]

theorem plane_comm_fixed (hM : Nat.card M = 9) (U : Subgroup (M ≃ₗ[ZMod 3] M)) (hU : IsPGroup 3 U) :
    ∀ x ∈ commSub U, ∀ u ∈ U, u x = x := by
  intro x hx
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨u', hu', m, rfl⟩ := hx
    intro u hu
    exact plane_three_nil hM U hU u' hu' u hu m
  | zero => intro u hu; exact map_zero u
  | add x y _ _ hx hy => intro u hu; rw [map_add, hx u hu, hy u hu]
  | neg x _ hx => intro u hu; rw [map_neg, hx u hu]

theorem plane_numeric (hM : Nat.card M = 9) (U : Subgroup (M ≃ₗ[ZMod 3] M)) (hU : IsPGroup 3 U) :
    (Nat.card U = 1 ∧ commSub U = ⊥ ∧ fixSub U = ⊤ ∧ Nat.card (commSub U) = 1 ∧
        Nat.card (fixSub U) = 9) ∨
      (Nat.card U = 3 ∧ Nat.card (commSub U) = 3 ∧ Nat.card (fixSub U) = 3) := by
  rcases plane_three_dichotomy hM U hU with ⟨h1, h2, h3⟩ | h
  · left
    refine ⟨?_, h2, h3, ?_, ?_⟩
    · rw [h1]; exact Subgroup.card_bot
    · rw [h2]; exact AddSubgroup.card_bot
    · rw [h3, AddSubgroup.card_top, hM]
  · exact Or.inr h

end PlaneFacts

section Restriction
variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Finite V]
  (M : Submodule (ZMod 3) V) (P : Subgroup (V ≃ₗ[ZMod 3] V))
  (hM : ∀ p ∈ P, ∀ m ∈ M, p m ∈ M)

@[expose] def resRange : Subgroup (M ≃ₗ[ZMod 3] M) := (resHom M P hM).range

include hM

theorem mem_fixSub_resRange (m : M) :
    (m : V) ∈ fixSub P ↔ m ∈ fixSub (resRange M P hM) := by
  constructor
  · intro h u hu
    obtain ⟨p, rfl⟩ := hu
    exact Subtype.ext (h p p.2)
  · intro h p hp
    have := h (resHom M P hM ⟨p, hp⟩) ⟨_, rfl⟩
    exact congrArg Subtype.val this

theorem mem_commSub_of_resRange (m : M) (h : m ∈ commSub (resRange M P hM)) :
    (m : V) ∈ commSub P := by
  induction h using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨u, ⟨p, rfl⟩, m, rfl⟩ := hx
    exact AddSubgroup.subset_closure ⟨p, p.2, m, rfl⟩
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | neg x _ hx => exact neg_mem hx

theorem isPGroup_resRange (hP : IsPGroup 3 P) : IsPGroup 3 (resRange M P hM) :=
  hP.of_surjective (resHom M P hM).rangeRestrict (resHom M P hM).rangeRestrict_surjective

end Restriction


namespace Datum
variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Finite V] (D : Datum V)

theorem ext_AF {g h : V ≃ₗ[ZMod 3] V} (hA : ∀ a ∈ D.A, g a = h a) (hF : ∀ f ∈ D.F, g f = h f) :
    g = h := by
  ext v
  obtain ⟨a, ha, f, hf, rfl⟩ := D.exists_decomp v
  rw [map_add, map_add, hA a ha, hF f hf]

theorem eq_one_of_fix_AF {g : V ≃ₗ[ZMod 3] V} (hA : ∀ a ∈ D.A, g a = a)
    (hF : ∀ f ∈ D.F, g f = f) : g = 1 :=
  D.ext_AF (fun a ha => by simpa using hA a ha) (fun f hf => by simpa using hF f hf)

variable {D} {P : Subgroup (V ≃ₗ[ZMod 3] V)}

theorem pres_A (hc : ∀ p ∈ P, p * D.t = D.t * p) : ∀ p ∈ P, ∀ a ∈ D.A, p a ∈ D.A :=
  fun p hp => (D.t_comm_preserves (hc p hp)).1

theorem pres_F (hc : ∀ p ∈ P, p * D.t = D.t * p) : ∀ p ∈ P, ∀ f ∈ D.F, p f ∈ D.F :=
  fun p hp => (D.t_comm_preserves (hc p hp)).2

theorem t_comm_apply {p : V ≃ₗ[ZMod 3] V} (hp : p * D.t = D.t * p) (v : V) :
    p (D.t v) = D.t (p v) := by
  have := congrArg (fun e : V ≃ₗ[ZMod 3] V => e v) hp
  simpa using this

theorem fixSub_t_closed (hc : ∀ p ∈ P, p * D.t = D.t * p) : ∀ y ∈ fixSub P, D.t y ∈ fixSub P := by
  intro y hy p hp
  rw [t_comm_apply (hc p hp), hy p hp]

theorem commSub_t_closed (hc : ∀ p ∈ P, p * D.t = D.t * p) :
    ∀ y ∈ commSub P, D.t y ∈ commSub P := by
  intro y hy
  induction hy using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨p, hp, v, rfl⟩ := hx
    refine AddSubgroup.subset_closure ⟨p, hp, D.t v, ?_⟩
    rw [map_sub, t_comm_apply (hc p hp)]
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx

theorem card_split (Y : AddSubgroup V) (hY : ∀ y ∈ Y, D.t y ∈ Y) :
    Nat.card Y = Nat.card {a : D.A // (a : V) ∈ Y} * Nat.card {f : D.F // (f : V) ∈ Y} := by
  rw [← Nat.card_prod]
  symm
  refine Nat.card_eq_of_bijective
    (fun x => (⟨(x.1.1 : V) + x.2.1, Y.add_mem x.1.2 x.2.2⟩ : Y)) ⟨?_, ?_⟩
  · rintro ⟨⟨a, ha⟩, ⟨f, hf⟩⟩ ⟨⟨a', ha'⟩, ⟨f', hf'⟩⟩ h
    have h1 : (a : V) + f = a' + f' := congrArg Subtype.val h
    have h2 : (a : V) - a' = f' - f := by
      rw [show (a : V) - a' = ((a : V) + f) - (a' + f') + (f' - f) by abel, h1, sub_self, zero_add]
    have h4 : (a : V) - a' = 0 :=
      D.inter_eq_zero (D.A.sub_mem a.2 a'.2) (h2 ▸ D.F.sub_mem f'.2 f.2)
    have h5 : (f' : V) - f = 0 := h2 ▸ h4
    have e1 : a = a' := Subtype.ext (sub_eq_zero.1 h4)
    have e2 : f = f' := Subtype.ext (sub_eq_zero.1 h5).symm
    subst e1; subst e2; rfl
  · rintro ⟨y, hy⟩
    obtain ⟨a, haY, haA, f, hfY, hfF, rfl⟩ := D.split_of_t_closed Y hY hy
    exact ⟨(⟨⟨a, haA⟩, haY⟩, ⟨⟨f, hfF⟩, hfY⟩), rfl⟩


@[expose] def rangeA (hc : ∀ p ∈ P, p * D.t = D.t * p) : Subgroup (D.A ≃ₗ[ZMod 3] D.A) :=
  resRange D.A P (pres_A hc)

@[expose] def rangeF (hc : ∀ p ∈ P, p * D.t = D.t * p) : Subgroup (D.F ≃ₗ[ZMod 3] D.F) :=
  resRange D.F P (pres_F hc)

theorem isPGroup_rangeA (hP : IsPGroup 3 P) (hc : ∀ p ∈ P, p * D.t = D.t * p) :
    IsPGroup 3 (rangeA hc) := isPGroup_resRange _ _ _ hP

theorem isPGroup_rangeF (hP : IsPGroup 3 P) (hc : ∀ p ∈ P, p * D.t = D.t * p) :
    IsPGroup 3 (rangeF hc) := isPGroup_resRange _ _ _ hP

theorem comm_decomp (hc : ∀ p ∈ P, p * D.t = D.t * p) {y : V} (hy : y ∈ commSub P) :
    ∃ a : D.A, a ∈ commSub (rangeA hc) ∧
      ∃ f : D.F, f ∈ commSub (rangeF hc) ∧ y = (a : V) + f := by
  induction hy using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨p, hp, v, rfl⟩ := hx
    obtain ⟨a, ha, f, hf, rfl⟩ := D.exists_decomp v
    have hpa : p a ∈ D.A := pres_A hc p hp a ha
    have hpf : p f ∈ D.F := pres_F hc p hp f hf
    refine ⟨⟨p a - a, D.A.sub_mem hpa ha⟩, ?_, ⟨p f - f, D.F.sub_mem hpf hf⟩, ?_, ?_⟩
    · exact AddSubgroup.subset_closure
        ⟨resHom D.A P (pres_A hc) ⟨p, hp⟩, ⟨_, rfl⟩, ⟨a, ha⟩, rfl⟩
    · exact AddSubgroup.subset_closure
        ⟨resHom D.F P (pres_F hc) ⟨p, hp⟩, ⟨_, rfl⟩, ⟨f, hf⟩, rfl⟩
    · simp only [map_add]; abel
  | zero => exact ⟨0, zero_mem _, 0, zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a1, h1, f1, h1', rfl⟩ := hx
    obtain ⟨a2, h2, f2, h2', rfl⟩ := hy
    refine ⟨a1 + a2, add_mem h1 h2, f1 + f2, add_mem h1' h2', ?_⟩
    push_cast; abel
  | neg x _ hx =>
    obtain ⟨a1, h1, f1, h1', rfl⟩ := hx
    refine ⟨-a1, neg_mem h1, -f1, neg_mem h1', ?_⟩
    push_cast; abel

theorem mem_commSub_A_iff (hc : ∀ p ∈ P, p * D.t = D.t * p) (a : D.A) :
    (a : V) ∈ commSub P ↔ a ∈ commSub (rangeA hc) := by
  constructor
  · intro h
    obtain ⟨a', ha', f', hf', he⟩ := comm_decomp hc h
    have h0 : (f' : V) = 0 := D.inter_eq_zero
      (by rw [show (f' : V) = a - a' by rw [he]; abel]; exact D.A.sub_mem a.2 a'.2) f'.2
    have : a = a' := Subtype.ext (by rw [he, h0, add_zero])
    rwa [this]
  · exact mem_commSub_of_resRange D.A P _ a

theorem mem_commSub_F_iff (hc : ∀ p ∈ P, p * D.t = D.t * p) (f : D.F) :
    (f : V) ∈ commSub P ↔ f ∈ commSub (rangeF hc) := by
  constructor
  · intro h
    obtain ⟨a', ha', f', hf', he⟩ := comm_decomp hc h
    have h0 : (a' : V) = 0 := D.inter_eq_zero a'.2
      (by rw [show (a' : V) = f - f' by rw [he]; abel]; exact D.F.sub_mem f.2 f'.2)
    have : f = f' := Subtype.ext (by rw [he, h0, zero_add])
    rwa [this]
  · exact mem_commSub_of_resRange D.F P _ f

theorem card_comm (hc : ∀ p ∈ P, p * D.t = D.t * p) :
    Nat.card (commSub P) =
      Nat.card (commSub (rangeA hc)) * Nat.card (commSub (rangeF hc)) := by
  rw [D.card_split (commSub P) (commSub_t_closed hc)]
  congr 1
  · exact Nat.card_congr (Equiv.subtypeEquivRight (fun a => mem_commSub_A_iff hc a))
  · exact Nat.card_congr (Equiv.subtypeEquivRight (fun f => mem_commSub_F_iff hc f))

theorem card_fix (hc : ∀ p ∈ P, p * D.t = D.t * p) :
    Nat.card (fixSub P) =
      Nat.card (fixSub (rangeA hc)) * Nat.card (fixSub (rangeF hc)) := by
  rw [D.card_split (fixSub P) (fixSub_t_closed hc)]
  congr 1
  · exact Nat.card_congr (Equiv.subtypeEquivRight (fun a => mem_fixSub_resRange D.A P (pres_A hc) a))
  · exact Nat.card_congr (Equiv.subtypeEquivRight (fun f => mem_fixSub_resRange D.F P (pres_F hc) f))


@[expose] noncomputable def psi (hc : ∀ p ∈ P, p * D.t = D.t * p) :
    P →* (rangeA hc) × (rangeF hc) :=
  (resHom D.A P (pres_A hc)).rangeRestrict.prod (resHom D.F P (pres_F hc)).rangeRestrict

theorem psi_injective (hc : ∀ p ∈ P, p * D.t = D.t * p) : Function.Injective (psi hc) := by
  rw [injective_iff_map_eq_one]
  intro p hp
  have h1 : resHom D.A P (pres_A hc) p = 1 :=
    congrArg (fun x => (x.1 : D.A ≃ₗ[ZMod 3] D.A)) hp
  have h2 : resHom D.F P (pres_F hc) p = 1 :=
    congrArg (fun x => (x.2 : D.F ≃ₗ[ZMod 3] D.F)) hp
  refine Subtype.ext (D.eq_one_of_fix_AF (fun a ha => ?_) (fun f hf => ?_))
  · have := congrArg (fun e : D.A ≃ₗ[ZMod 3] D.A => (e ⟨a, ha⟩ : V)) h1
    simpa using this
  · have := congrArg (fun e : D.F ≃ₗ[ZMod 3] D.F => (e ⟨f, hf⟩ : V)) h2
    simpa using this

theorem card_le_planes (hc : ∀ p ∈ P, p * D.t = D.t * p) :
    Nat.card P ≤ Nat.card (rangeA hc) * Nat.card (rangeF hc) := by
  rw [← Nat.card_prod]
  exact Nat.card_le_card_of_injective _ (psi_injective hc)

theorem left_case (hc : ∀ p ∈ P, p * D.t = D.t * p) (hcA : commSub (rangeA hc) = ⊥)
    (hfA : fixSub (rangeA hc) = ⊤) :
    (∀ y ∈ commSub P, y ∈ D.F) ∧ ∀ a ∈ D.A, a ∈ fixSub P := by
  refine ⟨fun y hy => ?_, fun a ha => ?_⟩
  · obtain ⟨a, ha, f, hf, rfl⟩ := comm_decomp hc hy
    rw [hcA, AddSubgroup.mem_bot] at ha
    rw [ha]
    simp
  · exact (mem_fixSub_resRange D.A P (pres_A hc) ⟨a, ha⟩).2 (by show (⟨a, ha⟩ : D.A) ∈ fixSub (rangeA hc); rw [hfA]; trivial)

theorem right_case (hc : ∀ p ∈ P, p * D.t = D.t * p) (hcF : commSub (rangeF hc) = ⊥)
    (hfF : fixSub (rangeF hc) = ⊤) :
    (∀ y ∈ commSub P, y ∈ D.A) ∧ ∀ f ∈ D.F, f ∈ fixSub P := by
  refine ⟨fun y hy => ?_, fun f hf => ?_⟩
  · obtain ⟨a, ha, f, hf, rfl⟩ := comm_decomp hc hy
    rw [hcF, AddSubgroup.mem_bot] at hf
    rw [hf]
    simp
  · exact (mem_fixSub_resRange D.F P (pres_F hc) ⟨f, hf⟩).2 (by show (⟨f, hf⟩ : D.F) ∈ fixSub (rangeF hc); rw [hfF]; trivial)

theorem comm_fixed (hP : IsPGroup 3 P) (hc : ∀ p ∈ P, p * D.t = D.t * p) :
    ∀ y ∈ commSub P, ∀ p ∈ P, p y = y := by
  intro y hy p hp
  obtain ⟨a, ha, f, hf, rfl⟩ := comm_decomp hc hy
  have h1 := plane_comm_fixed D.card_A (rangeA hc) (isPGroup_rangeA hP hc) a ha
    (resHom D.A P (pres_A hc) ⟨p, hp⟩) ⟨_, rfl⟩
  have h2 := plane_comm_fixed D.card_F (rangeF hc) (isPGroup_rangeF hP hc) f hf
    (resHom D.F P (pres_F hc) ⟨p, hp⟩) ⟨_, rfl⟩
  rw [map_add]
  have h1' := congrArg Subtype.val h1
  have h2' := congrArg Subtype.val h2
  simp only [resHom_apply] at h1' h2'
  rw [h1', h2']


theorem psi_pow (hP : IsPGroup 3 P) (hc : ∀ p ∈ P, p * D.t = D.t * p) (x : (rangeA hc) × (rangeF hc)) :
    x ^ 3 = 1 := by
  obtain ⟨h1, -⟩ := plane_three_exp D.card_A (rangeA hc) (isPGroup_rangeA hP hc)
  obtain ⟨h2, -⟩ := plane_three_exp D.card_F (rangeF hc) (isPGroup_rangeF hP hc)
  refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
  · exact h1 _ x.1.2
  · exact h2 _ x.2.2

theorem psi_comm (hP : IsPGroup 3 P) (hc : ∀ p ∈ P, p * D.t = D.t * p)
    (x y : (rangeA hc) × (rangeF hc)) : x * y = y * x := by
  obtain ⟨-, h1⟩ := plane_three_exp D.card_A (rangeA hc) (isPGroup_rangeA hP hc)
  obtain ⟨-, h2⟩ := plane_three_exp D.card_F (rangeF hc) (isPGroup_rangeF hP hc)
  refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
  · exact h1 _ x.1.2 _ y.1.2
  · exact h2 _ x.2.2 _ y.2.2

theorem core66 (hP : IsPGroup 3 P) (hc : ∀ p ∈ P, p * D.t = D.t * p) :
    (Nat.card P ≤ 9 ∧ (∀ p ∈ P, p ^ 3 = 1) ∧ ∀ p ∈ P, ∀ p' ∈ P, p * p' = p' * p) ∧
    (∀ y ∈ commSub P, ∀ p ∈ P, p y = y) ∧
    (Nat.card (commSub P) * Nat.card (fixSub P) = 81 ∧
      (Nat.card P = 9 → Nat.card (commSub P) = 9)) ∧
    (Nat.card (commSub P) = 3 →
      ((∀ y ∈ commSub P, y ∈ D.F) ∧ (∀ a ∈ D.A, a ∈ fixSub P) ∨
        (∀ y ∈ commSub P, y ∈ D.A) ∧ (∀ f ∈ D.F, f ∈ fixSub P))) := by
  have hnA := plane_numeric D.card_A (rangeA hc) (isPGroup_rangeA hP hc)
  have hnF := plane_numeric D.card_F (rangeF hc) (isPGroup_rangeF hP hc)
  have hle := card_le_planes (D := D) hc
  have hcomm := card_comm (D := D) hc
  have hfix := card_fix (D := D) hc
  refine ⟨⟨?_, ?_, ?_⟩, comm_fixed hP hc, ⟨?_, ?_⟩, ?_⟩
  · rcases hnA with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rcases hnF with ⟨h2, -⟩ | ⟨h2, -⟩ <;>
      rw [h1, h2] at hle <;> omega
  · intro p hp
    have := psi_injective hc (a₁ := (⟨p, hp⟩ : P) ^ 3) (a₂ := 1)
      (by rw [map_pow, map_one]; exact psi_pow hP hc _)
    simpa using congrArg Subtype.val this
  · intro p hp p' hp'
    have := psi_injective hc (a₁ := (⟨p, hp⟩ : P) * ⟨p', hp'⟩) (a₂ := ⟨p', hp'⟩ * ⟨p, hp⟩)
      (by rw [map_mul, map_mul]; exact psi_comm hP hc _ _)
    simpa using congrArg Subtype.val this
  · rw [hcomm, hfix]
    rcases hnA with ⟨-, -, -, h1, h2⟩ | ⟨-, h1, h2⟩ <;>
      rcases hnF with ⟨-, -, -, h3, h4⟩ | ⟨-, h3, h4⟩ <;> rw [h1, h2, h3, h4]
  · intro h9
    rw [hcomm]
    rcases hnA with ⟨h1, -, -, h1', -⟩ | ⟨h1, h1', -⟩ <;>
      rcases hnF with ⟨h2, -, -, h2', -⟩ | ⟨h2, h2', -⟩ <;>
      rw [h1, h2] at hle <;> rw [h1', h2'] <;> omega
  · intro h3
    rw [hcomm] at h3
    rcases hnA with ⟨-, hcA, hfA, h1, -⟩ | ⟨-, h1, -⟩ <;>
      rcases hnF with ⟨-, hcF, hfF, h2, -⟩ | ⟨-, h2, -⟩
    · rw [h1, h2] at h3; omega
    · exact Or.inl (left_case hc hcA hfA)
    · exact Or.inr (right_case hc hcF hfF)
    · rw [h1, h2] at h3; omega

end Datum

end CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6E
