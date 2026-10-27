module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6EPlane

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6E

section Basic
variable {V : Type*} [AddCommGroup V] [Module (ZMod 3) V]

instance finite_aut [Finite V] : Finite (V ≃ₗ[ZMod 3] V) :=
  Finite.of_injective (fun g : V ≃ₗ[ZMod 3] V => (g : V → V)) DFunLike.coe_injective

theorem three_add (x : V) : x + x + x = 0 := by
  have h : (3 : ZMod 3) • x = 0 := by
    have : (3 : ZMod 3) = 0 := by decide
    rw [this, zero_smul]
  rw [← h]
  rw [show (3 : ZMod 3) = 1 + 1 + 1 from by decide]
  simp [add_smul]

theorem eq_zero_of_eq_neg {x : V} (h : x = -x) : x = 0 := by
  have h3 := three_add x
  have : x + x = 0 := by
    nth_rewrite 1 [h]; simp
  rw [this, zero_add] at h3
  exact h3

end Basic

section Restrict
variable {V : Type*} [AddCommGroup V] [Module (ZMod 3) V]

@[expose] def restr (M : Submodule (ZMod 3) V) (g : V ≃ₗ[ZMod 3] V) (h : ∀ m ∈ M, g m ∈ M)
    (h' : ∀ m ∈ M, g.symm m ∈ M) : M ≃ₗ[ZMod 3] M where
  toFun m := ⟨g m, h m m.2⟩
  map_add' x y := by ext; simp
  map_smul' c x := by ext; simp
  invFun m := ⟨g.symm m, h' m m.2⟩
  left_inv x := by ext; simp
  right_inv x := by ext; simp

@[simp] theorem restr_apply (M : Submodule (ZMod 3) V) (g : V ≃ₗ[ZMod 3] V) (h h') (m : M) :
    ((restr M g h h' m : M) : V) = g m := rfl

@[expose] def resHom (M : Submodule (ZMod 3) V) (S : Subgroup (V ≃ₗ[ZMod 3] V))
    (h : ∀ s ∈ S, ∀ m ∈ M, s m ∈ M) : S →* (M ≃ₗ[ZMod 3] M) where
  toFun s := restr M s (h s s.2) (h s⁻¹ (inv_mem s.2))
  map_one' := by ext; simp [restr]
  map_mul' x y := by ext; simp [restr]

@[simp] theorem resHom_apply (M : Submodule (ZMod 3) V) (S : Subgroup (V ≃ₗ[ZMod 3] V))
    (h : ∀ s ∈ S, ∀ m ∈ M, s m ∈ M) (s : S) (m : M) :
    ((resHom M S h s m : M) : V) = (s : V ≃ₗ[ZMod 3] V) m := rfl

@[simp] theorem resHom_symm_apply (M : Submodule (ZMod 3) V) (S : Subgroup (V ≃ₗ[ZMod 3] V))
    (h : ∀ s ∈ S, ∀ m ∈ M, s m ∈ M) (s : S) (m : M) :
    (((resHom M S h s).symm m : M) : V) = (s : V ≃ₗ[ZMod 3] V).symm m := rfl

end Restrict

section PlaneQ
variable {V : Type*} [AddCommGroup V] [Module (ZMod 3) V] [Finite V]

structure PlaneQ (Q : Subgroup (V ≃ₗ[ZMod 3] V)) (F : Submodule (ZMod 3) V) : Prop where
  card_F : Nat.card F = 9
  quat : Nonempty (Q ≃* QuaternionGroup 2)
  mem : ∀ q ∈ Q, ∀ f ∈ F, q f ∈ F
  faith : ∀ q ∈ Q, (∀ f ∈ F, q f = f) → q = 1

variable {Q : Subgroup (V ≃ₗ[ZMod 3] V)} {F : Submodule (ZMod 3) V}

theorem resHom_injective_of_faith (S : Subgroup (V ≃ₗ[ZMod 3] V)) (h : ∀ s ∈ S, ∀ m ∈ F, s m ∈ F)
    (hf : ∀ s ∈ S, (∀ m ∈ F, s m = m) → s = 1) : Function.Injective (resHom F S h) := by
  rw [injective_iff_map_eq_one]
  intro s hs
  have : ∀ m ∈ F, (s : V ≃ₗ[ZMod 3] V) m = m := by
    intro m hm
    have := congrArg (fun e : F ≃ₗ[ZMod 3] F => ((e ⟨m, hm⟩ : F) : V)) hs
    simpa using this
  exact Subtype.ext (hf s s.2 this)

namespace PlaneQ
variable (h : PlaneQ Q F)

@[expose] noncomputable def emb : QuaternionGroup 2 →* (F ≃ₗ[ZMod 3] F) :=
  (resHom F Q h.mem).comp (h.quat.some.symm : QuaternionGroup 2 ≃* Q).toMonoidHom

theorem emb_injective : Function.Injective h.emb := by
  have h1 := resHom_injective_of_faith (F := F) Q h.mem h.faith
  exact h1.comp h.quat.some.symm.injective

theorem mem_range_emb {x : F ≃ₗ[ZMod 3] F} : x ∈ h.emb.range ↔ ∃ q : Q, resHom F Q h.mem q = x := by
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨_, rfl⟩
  · rintro ⟨q, rfl⟩
    exact ⟨h.quat.some q, by simp [emb]⟩

theorem finite_F : Finite F := inferInstance

theorem exists_ne_zero (h : PlaneQ Q F) : ∃ f ∈ F, f ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have : Nat.card F ≤ 1 := by
    rw [Finite.card_le_one_iff_subsingleton]
    refine ⟨fun a b => Subtype.ext ?_⟩
    rw [hcon a a.2, hcon b b.2]
  have := h.card_F
  omega

theorem resHom_inj (h : PlaneQ Q F) : Function.Injective (resHom F Q h.mem) :=
  resHom_injective_of_faith (F := F) Q h.mem h.faith

theorem resHom_apply' (h : PlaneQ Q F) (q : Q) (f : F) :
    ((resHom F Q h.mem q f : F) : V) = (q : V ≃ₗ[ZMod 3] V) f := rfl

theorem exists_t (h : PlaneQ Q F) : ∃ t ∈ Q, t ≠ 1 ∧ (∀ f ∈ F, t f = -f) ∧
    ∀ q ∈ Q, q * q = 1 → q = 1 ∨ q = t := by
  obtain ⟨t', ht'mem, ht'neg, ht'inv⟩ := plane_q8_neg h.card_F h.emb h.emb_injective
  obtain ⟨t, rfl⟩ := (h.mem_range_emb).1 ht'mem
  have htneg : ∀ f ∈ F, (t : V ≃ₗ[ZMod 3] V) f = -f := by
    intro f hf
    have := congrArg (fun x : F => (x : V)) (ht'neg ⟨f, hf⟩)
    simpa using this
  refine ⟨t, t.2, ?_, htneg, ?_⟩
  · intro h1
    obtain ⟨f, hf, hf0⟩ := h.exists_ne_zero
    have h2 := htneg f hf
    rw [h1] at h2
    exact hf0 (eq_zero_of_eq_neg h2)
  · intro q hq hq2
    have hq' : resHom F Q h.mem ⟨q, hq⟩ * resHom F Q h.mem ⟨q, hq⟩ = 1 := by
      rw [← map_mul, ← map_one (resHom F Q h.mem)]
      congr 1
      exact Subtype.ext hq2
    rcases ht'inv _ ((h.mem_range_emb).2 ⟨⟨q, hq⟩, rfl⟩) hq' with h3 | h3
    · left
      have := h.resHom_inj (h3.trans (map_one _).symm)
      exact congrArg Subtype.val this
    · right
      have := h.resHom_inj h3
      exact congrArg Subtype.val this

theorem free (h : PlaneQ Q F) : ∀ q ∈ Q, q ≠ 1 → ∀ f ∈ F, q f = f → f = 0 := by
  intro q hq hq1 f hf hqf
  have hne : resHom F Q h.mem ⟨q, hq⟩ ≠ 1 := by
    intro h1
    apply hq1
    have := h.resHom_inj (h1.trans (map_one _).symm)
    exact congrArg Subtype.val this
  have hfix : resHom F Q h.mem ⟨q, hq⟩ ⟨f, hf⟩ = ⟨f, hf⟩ := Subtype.ext hqf
  have := plane_q8_free h.card_F h.emb h.emb_injective _ ((h.mem_range_emb).2 ⟨_, rfl⟩) hne ⟨f, hf⟩ hfix
  exact congrArg Subtype.val this

theorem trans (h : PlaneQ Q F) : ∀ f ∈ F, ∀ g ∈ F, f ≠ 0 → g ≠ 0 → ∃ q ∈ Q, q f = g := by
  intro f hf g hg hf0 hg0
  obtain ⟨q', hq', hq'fg⟩ := plane_q8_trans h.card_F h.emb h.emb_injective ⟨f, hf⟩ ⟨g, hg⟩
    (fun h0 => hf0 (congrArg Subtype.val h0)) (fun h0 => hg0 (congrArg Subtype.val h0))
  obtain ⟨q, rfl⟩ := (h.mem_range_emb).1 hq'
  exact ⟨q, q.2, by simpa using congrArg Subtype.val hq'fg⟩

theorem zd (h : PlaneQ Q F) : ∃ q1 ∈ Q, ∃ q2 ∈ Q, (∃ f ∈ F, f ≠ 0 ∧ f + q1 f + q2 f = 0) ∧
    ∃ f ∈ F, f + q1 f + q2 f ≠ 0 := by
  obtain ⟨q1', h1, q2', h2, ⟨m, hm0, hm⟩, ⟨m', hm'⟩⟩ :=
    plane_q8_zd h.card_F h.emb h.emb_injective
  obtain ⟨q1, rfl⟩ := (h.mem_range_emb).1 h1
  obtain ⟨q2, rfl⟩ := (h.mem_range_emb).1 h2
  refine ⟨q1, q1.2, q2, q2.2, ⟨m, m.2, fun h0 => hm0 (Subtype.ext h0), ?_⟩, ⟨m', m'.2, ?_⟩⟩
  · simpa using congrArg Subtype.val hm
  · intro h0
    apply hm'
    apply Subtype.ext
    simpa using h0

theorem resHom_congr (S T : Subgroup (V ≃ₗ[ZMod 3] V)) (hS : ∀ s ∈ S, ∀ f ∈ F, s f ∈ F)
    (hT : ∀ s ∈ T, ∀ f ∈ F, s f ∈ F) (s : S) (t : T)
    (hst : (s : V ≃ₗ[ZMod 3] V) = t) : resHom F S hS s = resHom F T hT t := by
  ext f
  simp [hst]

theorem odd_normalized (h : PlaneQ Q F) (Z : Subgroup (V ≃ₗ[ZMod 3] V))
    (hZ : ∀ z ∈ Z, ∀ f ∈ F, z f ∈ F) (hZf : ∀ z ∈ Z, (∀ f ∈ F, z f = f) → z = 1)
    (hodd : Odd (Nat.card Z)) (hn : ∀ q ∈ Q, ∀ z ∈ Z, q * z * q⁻¹ ∈ Z) : Z = ⊥ := by
  have hinj : Function.Injective (resHom F Z hZ) := resHom_injective_of_faith Z hZ hZf
  have hcard : Nat.card (resHom F Z hZ).range = Nat.card Z :=
    Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm
  have key := plane_q8_odd h.card_F h.emb h.emb_injective (resHom F Z hZ).range
    (hcard ▸ hodd) (by
      intro q' hq' z' hz'
      obtain ⟨q, rfl⟩ := (h.mem_range_emb).1 hq'
      obtain ⟨z, rfl⟩ := hz'
      refine ⟨⟨q * z * q⁻¹, hn q q.2 z z.2⟩, ?_⟩
      ext f
      simp)
  rw [Subgroup.eq_bot_iff_forall]
  intro z hz
  have : resHom F Z hZ ⟨z, hz⟩ ∈ (resHom F Z hZ).range := ⟨_, rfl⟩
  rw [key, Subgroup.mem_bot] at this
  have := hinj (this.trans (map_one _).symm)
  exact congrArg Subtype.val this

theorem normal_of_faithful (h : PlaneQ Q F) (S : Subgroup (V ≃ₗ[ZMod 3] V)) (hQS : Q ≤ S)
    (hS : ∀ s ∈ S, ∀ f ∈ F, s f ∈ F) (hSf : ∀ s ∈ S, (∀ f ∈ F, s f = f) → s = 1) :
    ∀ s ∈ S, ∀ q ∈ Q, s * q * s⁻¹ ∈ Q := by
  intro s hs q hq
  have hinjS : Function.Injective (resHom F S hS) := resHom_injective_of_faith S hS hSf
  set σ : F ≃ₗ[ZMod 3] F := resHom F S hS ⟨s, hs⟩ with hσ
  let emb' : QuaternionGroup 2 →* (F ≃ₗ[ZMod 3] F) :=
    (MulAut.conj σ).toMonoidHom.comp h.emb
  have hinj' : Function.Injective emb' := (MulAut.conj σ).injective.comp h.emb_injective
  have hr := plane_q8_unique h.card_F h.emb h.emb_injective emb' hinj'
  have hx : σ * resHom F Q h.mem ⟨q, hq⟩ * σ⁻¹ ∈ emb'.range := by
    obtain ⟨g, hg⟩ := (h.mem_range_emb).2 ⟨⟨q, hq⟩, rfl⟩
    exact ⟨g, by simp [emb', hg]⟩
  rw [hr] at hx
  obtain ⟨q', hq'⟩ := (h.mem_range_emb).1 hx
  have hqq : q'.1 = s * q * s⁻¹ := by
    have h1 : resHom F S hS ⟨q'.1, hQS q'.2⟩ = resHom F S hS ⟨s * q * s⁻¹, S.mul_mem (S.mul_mem hs (hQS hq)) (S.inv_mem hs)⟩ := by
      rw [← resHom_congr (F := F) Q S h.mem hS q' ⟨q'.1, hQS q'.2⟩ rfl] 
      rw [hq']
      ext f
      simp [hσ]
    have := hinjS h1
    exact congrArg Subtype.val this
  rw [← hqq]
  exact q'.2

end PlaneQ
end PlaneQ

section Datum
variable {V : Type*} [AddCommGroup V] [Module (ZMod 3) V] [Finite V]

structure Datum (V : Type*) [AddCommGroup V] [Module (ZMod 3) V] [Finite V] where
  W : Subgroup (V ≃ₗ[ZMod 3] V)
  Q : Subgroup (V ≃ₗ[ZMod 3] V)
  A : Submodule (ZMod 3) V
  F : Submodule (ZMod 3) V
  card_A : Nat.card A = 9
  isCompl : IsCompl A F
  Q_le_W : Q ≤ W
  Q_fix_A : ∀ q ∈ Q, ∀ a ∈ A, q a = a
  planeQ : PlaneQ Q F

namespace Datum
variable (D : Datum V)

theorem card_F : Nat.card D.F = 9 := D.planeQ.card_F

theorem exists_decomp (v : V) : ∃ a ∈ D.A, ∃ f ∈ D.F, v = a + f := by
  have : v ∈ D.A ⊔ D.F := by rw [D.isCompl.sup_eq_top]; trivial
  obtain ⟨a, ha, f, hf, rfl⟩ := Submodule.mem_sup.1 this
  exact ⟨a, ha, f, hf, rfl⟩

theorem inter_eq_zero {v : V} (hA : v ∈ D.A) (hF : v ∈ D.F) : v = 0 := by
  have : v ∈ D.A ⊓ D.F := ⟨hA, hF⟩
  rw [D.isCompl.inf_eq_bot] at this
  simpa using this

@[expose] noncomputable def t : V ≃ₗ[ZMod 3] V := (PlaneQ.exists_t D.planeQ).choose

theorem t_mem : D.t ∈ D.Q := (PlaneQ.exists_t D.planeQ).choose_spec.1
theorem t_ne_one : D.t ≠ 1 := (PlaneQ.exists_t D.planeQ).choose_spec.2.1
theorem t_neg_F : ∀ f ∈ D.F, D.t f = -f := (PlaneQ.exists_t D.planeQ).choose_spec.2.2.1
theorem t_unique : ∀ q ∈ D.Q, q * q = 1 → q = 1 ∨ q = D.t := (PlaneQ.exists_t D.planeQ).choose_spec.2.2.2
theorem t_fix_A : ∀ a ∈ D.A, D.t a = a := fun a ha => D.Q_fix_A _ D.t_mem a ha

theorem t_apply {a f : V} (ha : a ∈ D.A) (hf : f ∈ D.F) : D.t (a + f) = a - f := by
  rw [map_add, D.t_fix_A a ha, D.t_neg_F f hf]; abel

theorem card_V (D : Datum V) : Nat.card V = 81 := by
  have := Nat.card_congr (Submodule.prodEquivOfIsCompl D.A D.F D.isCompl).toEquiv
  rw [Nat.card_prod, D.card_A, D.card_F] at this
  omega

theorem t_t (v : V) : D.t (D.t v) = v := by
  obtain ⟨a, ha, f, hf, rfl⟩ := D.exists_decomp v
  rw [D.t_apply ha hf, sub_eq_add_neg, D.t_apply ha (D.F.neg_mem hf)]
  abel

theorem t_mul_self : D.t * D.t = 1 := by
  ext v; simpa using D.t_t v

theorem mem_A_of_t_fix {v : V} (h : D.t v = v) : v ∈ D.A := by
  obtain ⟨a, ha, f, hf, rfl⟩ := D.exists_decomp v
  rw [D.t_apply ha hf] at h
  have h2 : f = -f := by
    rw [sub_eq_add_neg] at h
    exact (add_left_cancel h).symm
  have : f = 0 := eq_zero_of_eq_neg h2
  simp [this, ha]

theorem mem_F_of_t_neg {v : V} (h : D.t v = -v) : v ∈ D.F := by
  obtain ⟨a, ha, f, hf, rfl⟩ := D.exists_decomp v
  rw [D.t_apply ha hf] at h
  have h2 : a = -a := by
    rw [sub_eq_add_neg, neg_add] at h
    exact add_right_cancel h
  have : a = 0 := eq_zero_of_eq_neg h2
  simp [this, hf]

theorem t_comm_preserves {g : V ≃ₗ[ZMod 3] V} (hg : g * D.t = D.t * g) :
    (∀ a ∈ D.A, g a ∈ D.A) ∧ ∀ f ∈ D.F, g f ∈ D.F := by
  have key : ∀ v, g (D.t v) = D.t (g v) := fun v => by
    have := congrArg (fun e : V ≃ₗ[ZMod 3] V => e v) hg
    simpa using this
  constructor
  · intro a ha
    exact D.mem_A_of_t_fix (by rw [← key, D.t_fix_A a ha])
  · intro f hf
    exact D.mem_F_of_t_neg (by rw [← key, D.t_neg_F f hf, map_neg])

theorem fixed_Q_mem_A {v : V} (h : ∀ q ∈ D.Q, q v = v) : v ∈ D.A :=
  D.mem_A_of_t_fix (h _ D.t_mem)

theorem split_of_t_closed (Y : AddSubgroup V) (hY : ∀ y ∈ Y, D.t y ∈ Y) {y : V} (hy : y ∈ Y) :
    ∃ a ∈ Y, a ∈ D.A ∧ ∃ f ∈ Y, f ∈ D.F ∧ y = a + f := by
  obtain ⟨a, ha, f, hf, rfl⟩ := D.exists_decomp y
  have h1 : a = -((a + f) + D.t (a + f)) := by
    rw [D.t_apply ha hf]
    have : (a + f) + (a - f) = a + a := by abel
    rw [this]
    have h3 := three_add a
    have : a + a = -a := by
      have : a + a + a = 0 := h3
      exact eq_neg_of_add_eq_zero_left this
    rw [this, neg_neg]
  refine ⟨a, ?_, ha, f, ?_, hf, rfl⟩
  · rw [h1]; exact Y.neg_mem (Y.add_mem hy (hY _ hy))
  · have : f = (a + f) - a := by abel
    rw [this]
    refine Y.sub_mem hy ?_
    rw [h1]; exact Y.neg_mem (Y.add_mem hy (hY _ hy))

theorem F_le_of_Q_closed (Y : AddSubgroup V) (hY : ∀ q ∈ D.Q, ∀ y ∈ Y, q y ∈ Y) {f : V}
    (hfY : f ∈ Y) (hfF : f ∈ D.F) (hf0 : f ≠ 0) : ∀ g ∈ D.F, g ∈ Y := by
  intro g hg
  by_cases hg0 : g = 0
  · simp [hg0]
  · obtain ⟨q, hq, hqf⟩ := D.planeQ.trans f hfF g hg hf0 hg0
    rw [← hqf]; exact hY q hq f hfY

theorem t_central {q : V ≃ₗ[ZMod 3] V} (hq : q ∈ D.Q) : q * D.t = D.t * q := by
  have hq' : q⁻¹ ∈ D.Q := D.Q.inv_mem hq
  have hmem : q * D.t * q⁻¹ ∈ D.Q := D.Q.mul_mem (D.Q.mul_mem hq D.t_mem) hq'
  have hinv : (q * D.t * q⁻¹) * (q * D.t * q⁻¹) = 1 := by
    have : (q * D.t * q⁻¹) * (q * D.t * q⁻¹) = q * (D.t * D.t) * q⁻¹ := by group
    rw [this, D.t_mul_self]; group
  rcases D.t_unique _ hmem hinv with h | h
  · exact absurd (by simpa using h) D.t_ne_one
  · calc q * D.t = (q * D.t * q⁻¹) * q := by group
      _ = D.t * q := by rw [h]

theorem exists_ij : ∃ i ∈ D.Q, ∃ j ∈ D.Q, i * j = D.t * (j * i) := by
  let φ : QuaternionGroup 2 ≃* D.Q := D.planeQ.quat.some.symm
  have h2 : (φ (QuaternionGroup.a 2) : V ≃ₗ[ZMod 3] V) = D.t := by
    have hsq : (φ (QuaternionGroup.a 2) : V ≃ₗ[ZMod 3] V) * φ (QuaternionGroup.a 2) = 1 := by
      have h0 : (QuaternionGroup.a 2 : QuaternionGroup 2) * QuaternionGroup.a 2 = 1 := by decide
      have h1 : φ (QuaternionGroup.a 2) * φ (QuaternionGroup.a 2) = 1 := by
        rw [← map_mul, h0, map_one]
      exact congrArg Subtype.val h1
    rcases D.t_unique _ (φ _).2 hsq with h | h
    · exfalso
      have h1 : φ (QuaternionGroup.a 2) = 1 := Subtype.ext h
      have : (QuaternionGroup.a 2 : QuaternionGroup 2) = 1 := φ.injective (by rw [h1, map_one])
      exact absurd this (by decide)
    · exact h
  refine ⟨φ (QuaternionGroup.a 1), (φ _).2, φ (QuaternionGroup.xa 0), (φ _).2, ?_⟩
  have key : (QuaternionGroup.a 1 : QuaternionGroup 2) * QuaternionGroup.xa 0 =
      QuaternionGroup.a 2 * (QuaternionGroup.xa 0 * QuaternionGroup.a 1) := by decide
  have := congrArg (fun g => ((φ g : D.Q) : V ≃ₗ[ZMod 3] V)) key
  simp only [map_mul, Subgroup.coe_mul] at this
  rw [this, h2]

structure FaithfulOver (S : Subgroup (V ≃ₗ[ZMod 3] V)) : Prop where
  le_W : S ≤ D.W
  Q_le : D.Q ≤ S
  mem_F : ∀ s ∈ S, ∀ f ∈ D.F, s f ∈ D.F
  faith : ∀ s ∈ S, (∀ f ∈ D.F, s f = f) → s = 1

@[expose] def HasKa : Prop :=
  ∀ a ∈ D.A, a ≠ 0 → ∃ S : Subgroup (V ≃ₗ[ZMod 3] V), D.FaithfulOver S ∧
    ∀ w ∈ D.W, (w a = a ∨ w a = -a) → ∀ s ∈ S, w * s * w⁻¹ ∈ S

@[expose] def HasJ : Prop :=
  ∃ S : Subgroup (V ≃ₗ[ZMod 3] V), D.FaithfulOver S ∧
    ∀ w ∈ D.W, (∀ a ∈ D.A, w a ∈ D.A) → ∀ s ∈ S, w * s * w⁻¹ ∈ S

@[expose] def img (g : V ≃ₗ[ZMod 3] V) (S : Submodule (ZMod 3) V) : Submodule (ZMod 3) V :=
  S.map (g : V →ₗ[ZMod 3] V)

theorem mem_img {g : V ≃ₗ[ZMod 3] V} {S : Submodule (ZMod 3) V} {v : V} :
    v ∈ img g S ↔ ∃ s ∈ S, g s = v := Submodule.mem_map

@[expose] def NWQ2 : Set (Subgroup (V ≃ₗ[ZMod 3] V)) :=
  {X | X ≤ D.W ∧ Odd (Nat.card X) ∧ ∀ q ∈ D.Q, ∀ x ∈ X, q * x * q⁻¹ ∈ X}

@[expose] def T : Subgroup (V ≃ₗ[ZMod 3] V) := (Subgroup.center D.Q).map D.Q.subtype

@[expose] def conjSub (x : V ≃ₗ[ZMod 3] V) (H : Subgroup (V ≃ₗ[ZMod 3] V)) : Subgroup (V ≃ₗ[ZMod 3] V) :=
  H.map (MulAut.conj x⁻¹).toMonoidHom

@[expose] def NW (H : Subgroup (V ≃ₗ[ZMod 3] V)) : Subgroup (V ≃ₗ[ZMod 3] V) :=
  D.W ⊓ Subgroup.normalizer (H : Set (V ≃ₗ[ZMod 3] V))

@[expose] def PermutesAF (g : V ≃ₗ[ZMod 3] V) : Prop :=
  (img g D.A = D.A ∧ img g D.F = D.F) ∨ (img g D.A = D.F ∧ img g D.F = D.A)

@[expose] def Lemma64Concl : Prop :=
  D.Q ≤ Subgroup.centralizer ((sSup D.NWQ2 : Subgroup (V ≃ₗ[ZMod 3] V)) : Set (V ≃ₗ[ZMod 3] V))

@[expose] def Lemma65Concl : Prop :=
  (∀ w ∈ D.W, ∀ q ∈ D.Q, w * q * w⁻¹ ∈ D.Q) ∨
  ∃ x ∈ D.W,
    (D.Q ⊓ conjSub x D.Q = ⊥ ∧ ∀ q ∈ D.Q, ∀ q' ∈ conjSub x D.Q, q * q' = q' * q) ∧
    x * x ∈ Subgroup.normalizer (D.Q : Set (V ≃ₗ[ZMod 3] V)) ∧
    (img x⁻¹ D.A = D.F ∧ img x⁻¹ D.F = D.A) ∧
    (∀ g ∈ D.NW (D.Q ⊔ conjSub x D.Q), D.PermutesAF g) ∧
    (D.W ≤ Subgroup.normalizer ((D.Q ⊔ conjSub x D.Q : Subgroup (V ≃ₗ[ZMod 3] V)) : Set _) ∨
      ((D.NW (D.Q ⊔ conjSub x D.Q)).relIndex D.W = 5 ∧
        ∀ u v : V, u ≠ 0 → v ≠ 0 → ∃ w ∈ D.W, w u = v))

@[expose] def Lemma66Concl (P : Subgroup (V ≃ₗ[ZMod 3] V)) : Prop :=
  (∃ w ∈ D.W, ∀ τ ∈ D.T, ∀ p ∈ P, (w⁻¹ * p * w) * τ = τ * (w⁻¹ * p * w)) ∧
  (Nat.card P ≤ 9 ∧ (∀ p ∈ P, p ^ 3 = 1) ∧ ∀ p ∈ P, ∀ p' ∈ P, p * p' = p' * p) ∧
  (∀ y ∈ commSub P, ∀ p ∈ P, p y = y) ∧
  ((fixSub P).index = Nat.card (commSub P) ∧ (Nat.card P = 9 → Nat.card (commSub P) = 9)) ∧
  ((∀ τ ∈ D.T, ∀ p ∈ P, p * τ = τ * p) → Nat.card (commSub P) = 3 →
    ((∀ y ∈ commSub P, y ∈ D.F) ∧ (∀ a ∈ D.A, a ∈ fixSub P) ∨
      (∀ y ∈ commSub P, y ∈ D.A) ∧ (∀ f ∈ D.F, f ∈ fixSub P)))


end Datum
end Datum
end CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6E
