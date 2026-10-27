module

public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C5Conj

public section

namespace CFSG.QuasithinUnique.C5

open CFSG.Quasithin Subgroup

variable {G : Type*} [Group G]

@[expose] def sqSub (D : Subgroup G) : Subgroup G := Subgroup.closure {y | ∃ d ∈ D, y = d ^ 2}

theorem sqSub_mono {A B : Subgroup G} (h : A ≤ B) : sqSub A ≤ sqSub B := by
  rw [sqSub, Subgroup.closure_le]
  rintro _ ⟨d, hd, rfl⟩
  exact Subgroup.subset_closure ⟨d, h hd, rfl⟩

theorem sqSub_le_of_forall {D N : Subgroup G} (h : ∀ d ∈ D, d ^ 2 ∈ N) : sqSub D ≤ N := by
  rw [sqSub, Subgroup.closure_le]
  rintro _ ⟨d, hd, rfl⟩
  exact h d hd

theorem sq_mem_sqSub {D : Subgroup G} {d : G} (hd : d ∈ D) : d ^ 2 ∈ sqSub D :=
  Subgroup.subset_closure ⟨d, hd, rfl⟩

theorem sqSub_le_self {D : Subgroup G} : sqSub D ≤ D :=
  sqSub_le_of_forall fun _ hd => D.pow_mem hd 2

theorem sqSub_eq_bot_iff {D : Subgroup G} : sqSub D = ⊥ ↔ ∀ d ∈ D, d ^ 2 = 1 := by
  constructor
  · intro h d hd
    have := sq_mem_sqSub hd
    rw [h] at this
    simpa using this
  · intro h
    refine eq_bot_iff.mpr (sqSub_le_of_forall fun d hd => ?_)
    rw [h d hd]; exact Subgroup.one_mem _

theorem comm_of_sq_eq_one {D : Subgroup G} (h : ∀ d ∈ D, d ^ 2 = 1) :
    ∀ a ∈ D, ∀ b ∈ D, a * b = b * a := by
  intro a ha b hb
  have h1 : (a * b) ^ 2 = 1 := h _ (D.mul_mem ha hb)
  have h2 : a ^ 2 = 1 := h a ha
  have h3 : b ^ 2 = 1 := h b hb
  have ha' : a⁻¹ = a := by
    rw [inv_eq_iff_mul_eq_one, ← pow_two]; exact h2
  have hb' : b⁻¹ = b := by
    rw [inv_eq_iff_mul_eq_one, ← pow_two]; exact h3
  have hab : (a * b)⁻¹ = a * b := by
    rw [inv_eq_iff_mul_eq_one, ← pow_two]; exact h1
  rw [mul_inv_rev, ha', hb'] at hab
  exact hab.symm

theorem le_normalizer_of_commute {U D : Subgroup G} (hc : ∀ u ∈ U, ∀ a ∈ D, u * a = a * u) :
    U ≤ normalizer (D : Set G) := by
  intro u hu
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    have : u * y * u⁻¹ = y := by rw [hc u hu y hy]; simp
    rw [this]; exact hy
  · intro hy
    have h1 := hc u⁻¹ (inv_mem hu) _ hy
    have h2 : y = u * y * u⁻¹ := by
      have h3 : y * u⁻¹ = (u * y * u⁻¹) * u⁻¹ := by
        have : u⁻¹ * (u * y * u⁻¹) = y * u⁻¹ := by simp [mul_assoc]
        rw [← this]; exact h1
      exact mul_right_cancel h3
    rw [← h2] at hy; exact hy

theorem sqSub_sup_eq {U D : Subgroup G} (hU2 : ∀ u ∈ U, u ^ 2 = 1)
    (hc : ∀ u ∈ U, ∀ a ∈ D, u * a = a * u) : sqSub (U ⊔ D) = sqSub D := by
  refine le_antisymm ?_ (sqSub_mono le_sup_right)
  refine sqSub_le_of_forall fun d hd => ?_
  have hN := le_normalizer_of_commute hc
  have hd' : d ∈ ((U ⊔ D : Subgroup G) : Set G) := hd
  rw [Subgroup.coe_mul_of_left_le_normalizer_right U D hN] at hd'
  obtain ⟨u, hu, a, ha, rfl⟩ := hd'
  have e : (u * a) ^ 2 = a ^ 2 := by
    have h1 : a * u = u * a := (hc u hu a ha).symm
    have h2 := hU2 u hu
    calc (u * a) ^ 2 = u * (a * u) * a := by simp [pow_two, mul_assoc]
      _ = u * (u * a) * a := by rw [h1]
      _ = (u * u) * (a * a) := by simp [mul_assoc]
      _ = a ^ 2 := by rw [← pow_two, h2, one_mul, pow_two]
  show (fun x1 x2 => x1 * x2) u a ^ 2 ∈ _
  simp only
  rw [e]
  exact sq_mem_sqSub ha

theorem conjSubgroup_sqSub (D : Subgroup G) (g : G) :
    conjSubgroup (sqSub D) g = sqSub (conjSubgroup D g) := by
  apply le_antisymm
  · rw [conjSubgroup_def, sqSub, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨y, ⟨d, hd, rfl⟩, rfl⟩
    refine Subgroup.subset_closure ⟨(MulAut.conj g⁻¹).toMonoidHom d, ⟨d, hd, rfl⟩, ?_⟩
    simp [pow_two, mul_assoc]
  · refine sqSub_le_of_forall fun d hd => ?_
    rw [mem_conjSubgroup_iff] at hd ⊢
    have : g * d ^ 2 * g⁻¹ = (g * d * g⁻¹) ^ 2 := by
      simp [pow_two, mul_assoc]
    rw [this]
    exact sq_mem_sqSub hd

theorem conjSubgroup_sqSub_of_mem_normalizer {D : Subgroup G} {g : G}
    (hg : g ∈ normalizer (D : Set G)) : conjSubgroup (sqSub D) g = sqSub D := by
  rw [conjSubgroup_sqSub, conjSubgroup_eq_self hg]

theorem mem_normalizer_centralizer {K : Subgroup G} {g : G} (hg : g ∈ normalizer (K : Set G)) :
    g ∈ normalizer ((centralizer (K : Set G) : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hg ⊢
  intro y
  simp only [Subgroup.mem_centralizer_iff]
  constructor
  · intro hy k hk
    have hk' : g⁻¹ * k * g ∈ K := by
      have := (hg (g⁻¹ * k * g)).mpr (by simpa [mul_assoc] using hk)
      exact this
    have h := hy _ hk'
    calc k * (g * y * g⁻¹) = g * ((g⁻¹ * k * g) * y) * g⁻¹ := by group
      _ = g * (y * (g⁻¹ * k * g)) * g⁻¹ := by rw [h]
      _ = (g * y * g⁻¹) * k := by group
  · intro hy k hk
    have hk' : g * k * g⁻¹ ∈ K := (hg k).mp hk
    have h := hy _ hk'
    calc k * y = g⁻¹ * ((g * k * g⁻¹) * (g * y * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * y * g⁻¹) * (g * k * g⁻¹)) * g := by rw [h]
      _ = y * k := by group

@[expose] def ElemAb2 (E : Subgroup G) : Prop :=
  (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) ∧ ∀ a ∈ E, a ^ 2 = 1

theorem isElemAbelian_two_iff {E : Subgroup G} : CFSG.Open.IsElemAbelian 2 E ↔ ElemAb2 E := by
  constructor
  · rintro ⟨hc, h⟩
    refine ⟨fun a ha b hb => ?_, h⟩
    have := hc.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
    exact congrArg Subtype.val this
  · rintro ⟨hc, h⟩
    exact ⟨⟨⟨fun a b => Subtype.ext (hc a a.2 b b.2)⟩⟩, h⟩

theorem ElemAb2.mono {A A' : Subgroup G} (h : ElemAb2 A) (hle : A' ≤ A) : ElemAb2 A' :=
  ⟨fun a ha b hb => h.1 a (hle ha) b (hle hb), fun a ha => h.2 a (hle ha)⟩

theorem ElemAb2.sq_eq_one {A : Subgroup G} (h : ElemAb2 A) {a : G} (ha : a ∈ A) : a ^ 2 = 1 :=
  h.2 a ha

theorem ElemAb2.conjSubgroup {A : Subgroup G} (h : ElemAb2 A) (g : G) :
    ElemAb2 (CFSG.Quasithin.conjSubgroup A g) := by
  refine ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
  · rw [mem_conjSubgroup_iff] at ha hb
    have := h.1 _ ha _ hb
    have h2 : g * (a * b) * g⁻¹ = g * (b * a) * g⁻¹ := by
      calc g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
        _ = (g * b * g⁻¹) * (g * a * g⁻¹) := this
        _ = g * (b * a) * g⁻¹ := by group
    simpa using h2
  · rw [mem_conjSubgroup_iff] at ha
    have := h.2 _ ha
    have h2 : g * a ^ 2 * g⁻¹ = (g * a * g⁻¹) ^ 2 := by simp [pow_two, mul_assoc]
    have h3 : g * a ^ 2 * g⁻¹ = 1 := by rw [h2]; exact this
    simpa using h3

theorem mem_sup_of_commute {A B : Subgroup G} (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : G}
    (hx : x ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  have hN := le_normalizer_of_commute hAB
  have hx' : x ∈ ((A ⊔ B : Subgroup G) : Set G) := hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right A B hN] at hx'
  obtain ⟨a, ha, b, hb, rfl⟩ := hx'
  exact ⟨a, ha, b, hb, rfl⟩

theorem mem_sup_of_le_normalizer {A B : Subgroup G} (hAB : A ≤ normalizer (B : Set G)) {x : G}
    (hx : x ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  have hx' : x ∈ ((A ⊔ B : Subgroup G) : Set G) := hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right A B hAB] at hx'
  obtain ⟨a, ha, b, hb, rfl⟩ := hx'
  exact ⟨a, ha, b, hb, rfl⟩

theorem ElemAb2.sup {A B : Subgroup G} (hA : ElemAb2 A) (hB : ElemAb2 B)
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) : ElemAb2 (A ⊔ B) := by
  have hxy : ∀ x ∈ A ⊔ B, ∀ y ∈ A ⊔ B, x * y = y * x := by
    intro x hx y hy
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute hAB hx
    obtain ⟨a', ha', b', hb', rfl⟩ := mem_sup_of_commute hAB hy
    have h1 := hA.1 a ha a' ha'
    have h2 := hB.1 b hb b' hb'
    have h3 := hAB a ha b' hb'
    have h4 := hAB a' ha' b hb
    calc a * b * (a' * b') = a * (b * a') * b' := by simp [mul_assoc]
      _ = a * (a' * b) * b' := by rw [← h4]
      _ = (a * a') * (b * b') := by simp [mul_assoc]
      _ = (a' * a) * (b' * b) := by rw [h1, h2]
      _ = a' * (a * b') * b := by simp [mul_assoc]
      _ = a' * (b' * a) * b := by rw [h3]
      _ = a' * b' * (a * b) := by simp [mul_assoc]
  refine ⟨hxy, fun x hx => ?_⟩
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute hAB hx
  have e : (a * b) ^ 2 = a ^ 2 * b ^ 2 := by
    have h1 : b * a = a * b := (hAB a ha b hb).symm
    calc (a * b) ^ 2 = a * (b * a) * b := by simp [pow_two, mul_assoc]
      _ = a * (a * b) * b := by rw [h1]
      _ = a ^ 2 * b ^ 2 := by simp [pow_two, mul_assoc]
  rw [e, hA.2 a ha, hB.2 b hb, one_mul]

end CFSG.QuasithinUnique.C5
