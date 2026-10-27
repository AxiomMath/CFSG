module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBHyp

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup
open scoped commutatorElement

theorem exists_mem_upperCentralSeries_succ_not_mem {G : Type*} [Group G] [Group.IsNilpotent G]
    (N : Subgroup G) [N.Normal] (k : ℕ) (hN : ¬ N ≤ Subgroup.upperCentralSeries G k) :
    ∃ y ∈ N, y ∈ Subgroup.upperCentralSeries G (k + 1) ∧ y ∉ Subgroup.upperCentralSeries G k := by
  classical
  set C : ℕ → Subgroup G := fun j => (fun M : Subgroup G => ⁅M, ⊤⁆)^[j] N with hC
  have hCsucc : ∀ j, C (j + 1) = ⁅C j, ⊤⁆ := fun j => Function.iterate_succ_apply' _ _ _
  have hC0 : C 0 = N := rfl
  have hCnormal : ∀ j, (C j).Normal := by
    intro j
    induction j with
    | zero => rw [hC0]; infer_instance
    | succ j ih => rw [hCsucc]; exact commutator_normal _ _
  have hCle : ∀ j, C j ≤ N := by
    intro j
    induction j with
    | zero => rw [hC0]
    | succ j ih =>
      rw [hCsucc]
      have := hCnormal j
      exact (commutator_le_left _ _).trans ih
  have hClow : ∀ j, C j ≤ (⊤ : Subgroup G).lowerCentralSeries j := by
    intro j
    induction j with
    | zero => rw [hC0, Subgroup.lowerCentralSeries_zero]; exact le_top
    | succ j ih =>
      rw [hCsucc, Subgroup.lowerCentralSeries_succ]
      exact commutator_mono ih le_rfl
  obtain ⟨m, hm⟩ := Subgroup.nilpotent_iff_lowerCentralSeries.mp
    (inferInstance : Group.IsNilpotent G)
  have hex : ∃ j, C j ≤ Subgroup.upperCentralSeries G k :=
    ⟨m, (hClow m).trans (by rw [hm]; exact bot_le)⟩
  have hj₁ : Nat.find hex ≠ 0 := by
    intro h0
    have := Nat.find_spec hex
    rw [h0, hC0] at this
    exact hN this
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hj₁
  have hjnot : ¬ C j ≤ Subgroup.upperCentralSeries G k := Nat.find_min hex (by omega)
  have hj1 : C (j + 1) ≤ Subgroup.upperCentralSeries G k := by
    have := Nat.find_spec hex
    rw [hj] at this
    exact this
  obtain ⟨y, hyC, hyZ⟩ := Set.not_subset.mp hjnot
  refine ⟨y, hCle j hyC, ?_, hyZ⟩
  rw [Subgroup.mem_upperCentralSeries_succ_iff]
  intro g
  apply hj1
  rw [hCsucc]
  exact commutator_mem_commutator hyC (mem_top g)

variable {H : Type} [Group H] [Finite H]

namespace Hyp52

variable (h : Hyp52 H)

@[expose] def upperS (i : ℕ) : Subgroup H :=
  (Subgroup.upperCentralSeries h.S i).map h.S.subtype

@[expose] def upperP (i : ℕ) : Subgroup H :=
  h.upperS i ⊓ h.P

theorem upperS_le_S (i : ℕ) : h.upperS i ≤ h.S := by
  rintro _ ⟨y, -, rfl⟩
  exact y.2

theorem upperS_zero : h.upperS 0 = ⊥ := by
  rw [upperS, Subgroup.upperCentralSeries_zero, Subgroup.map_bot]

theorem upperS_mono {i j : ℕ} (hij : i ≤ j) : h.upperS i ≤ h.upperS j :=
  map_mono (Subgroup.upperCentralSeries_mono _ hij)

theorem mem_upperS_succ {i : ℕ} {y : H} :
    y ∈ h.upperS (i + 1) ↔ y ∈ h.S ∧ ∀ s ∈ h.S, ⁅y, s⁆ ∈ h.upperS i := by
  constructor
  · rintro ⟨y', hy', rfl⟩
    refine ⟨y'.2, fun s hs => ?_⟩
    exact ⟨_, Subgroup.mem_upperCentralSeries_succ_iff.mp hy' ⟨s, hs⟩, rfl⟩
  · rintro ⟨hyS, hy⟩
    refine ⟨⟨y, hyS⟩, Subgroup.mem_upperCentralSeries_succ_iff.mpr fun s => ?_, rfl⟩
    obtain ⟨c, hc, hce⟩ := hy s s.2
    have : c = ⁅(⟨y, hyS⟩ : h.S), s⁆ := Subtype.ext hce
    rwa [← this]

theorem mem_upperS_one {y : H} :
    y ∈ h.upperS 1 ↔ y ∈ h.S ∧ ∀ s ∈ h.S, y * s = s * y := by
  rw [mem_upperS_succ, upperS_zero]
  simp only [mem_bot, commutatorElement_eq_one_iff_mul_comm]

theorem commutator_mem_upperS {i : ℕ} {u s : H} (hu : u ∈ h.upperS (i + 1)) (hs : s ∈ h.S) :
    ⁅u, s⁆ ∈ h.upperS i ∧ ⁅s, u⁆ ∈ h.upperS i := by
  have h1 := (h.mem_upperS_succ.mp hu).2 s hs
  refine ⟨h1, ?_⟩
  rw [← commutatorElement_inv]
  exact inv_mem h1

private theorem isPGroup_S_aux : IsPGroup 2 h.S := by
  obtain ⟨R, hR⟩ := h.S_sylow
  have h1 : IsPGroup 2 (h.S.subgroupOf (centralizer ({h.a} : Set H) ⊓
      normalizer (h.J : Set H))) := hR ▸ R.isPGroup'
  have h2 := h1.map (centralizer ({h.a} : Set H) ⊓ normalizer (h.J : Set H)).subtype
  rwa [map_subgroupOf_eq_of_le h.S_le] at h2

private theorem conj_mem_P_aux {s y : H} (hs : s ∈ h.S) (hy : y ∈ h.P) : s * y * s⁻¹ ∈ h.P := by
  obtain ⟨hyS, hyC⟩ := mem_inf.mp hy
  have hsJ : s⁻¹ ∈ normalizer (h.J : Set H) := (mem_inf.mp (h.S_le (inv_mem hs))).2
  have h1 := conj_mem_coreActionKernel hsJ hyC
  rw [inv_inv] at h1
  exact mem_inf.mpr ⟨mul_mem (mul_mem hs hyS) (inv_mem hs), h1⟩

theorem commutator_mem_P {u s : H} (hu : u ∈ h.P) (hs : s ∈ h.S) : ⁅u, s⁆ ∈ h.P ∧ ⁅s, u⁆ ∈ h.P := by
  have h1 : ⁅s, u⁆ ∈ h.P := by
    rw [commutatorElement_def]
    exact mul_mem (h.conj_mem_P_aux hs hu) (inv_mem hu)
  refine ⟨?_, h1⟩
  rw [← commutatorElement_inv]
  exact inv_mem h1

theorem exists_mem_upperP_succ (i : ℕ) (hP : ¬ h.P ≤ h.upperS i) :
    ∃ y ∈ h.P, y ∈ h.upperS (i + 1) ∧ y ∉ h.upperS i := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent h.S := h.isPGroup_S_aux.isNilpotent
  have hPS : h.P ≤ h.S := inf_le_left
  have hN : (h.P.subgroupOf h.S).Normal :=
    (normal_subgroupOf_iff hPS).mpr fun y s hy hs => h.conj_mem_P_aux hs hy
  have hN' : ¬ h.P.subgroupOf h.S ≤ Subgroup.upperCentralSeries h.S i := by
    intro hle
    apply hP
    intro y hy
    exact ⟨⟨y, hPS hy⟩, hle (mem_subgroupOf.mpr hy), rfl⟩
  obtain ⟨y, hyN, hy1, hy2⟩ := exists_mem_upperCentralSeries_succ_not_mem _ i hN'
  refine ⟨y, mem_subgroupOf.mp hyN, ⟨y, hy1, rfl⟩, ?_⟩
  rintro ⟨z, hz, hzy⟩
  exact hy2 ((Subtype.ext hzy : z = y) ▸ hz)

theorem exists_upperP_not_le (hBP : ¬ h.P ≤ normalizer (h.B : Set H)) :
    ∃ n, ¬ h.upperP n ≤ h.T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent h.S := h.isPGroup_S_aux.isNilpotent
  refine ⟨Group.nilpotencyClass h.S, fun hle => hBP fun y hy => ?_⟩
  have hyT : y ∈ h.T := hle (mem_inf.mpr ⟨?_, hy⟩)
  · exact (mem_inf.mp (mem_inf.mp hyT).1).2
  · rw [upperS, Subgroup.upperCentralSeries_nilpotencyClass]
    exact ⟨⟨y, (mem_inf.mp hy).1⟩, mem_top _, rfl⟩

open Classical in
noncomputable def x0Index : ℕ :=
  if hB : ∃ n, ¬ h.upperP n ≤ h.T then Nat.find hB else 0

@[expose] def IsX0Min (y : H) : Prop :=
  y ∈ h.upperP h.x0Index ∧ y ∉ h.T ∧ y ^ 2 ∈ h.T

theorem x0Index_spec (hB : ∃ n, ¬ h.upperP n ≤ h.T) :
    ¬ h.upperP h.x0Index ≤ h.T ∧ ∀ n < h.x0Index, h.upperP n ≤ h.T := by
  classical
  have he : h.x0Index = Nat.find hB := by
    unfold x0Index
    split
    · rfl
    · contradiction
  rw [he]
  refine ⟨Nat.find_spec hB, fun n hn => ?_⟩
  have := Nat.find_min hB hn
  push Not at this
  exact this

theorem exists_isX0Min (hBP : ¬ h.P ≤ normalizer (h.B : Set H)) : ∃ y, h.IsX0Min y := by
  classical
  obtain ⟨hnot, -⟩ := h.x0Index_spec (h.exists_upperP_not_le hBP)
  obtain ⟨y, hyY, hyT⟩ := Set.not_subset.mp hnot
  obtain ⟨m, hm⟩ := (h.isPGroup_S_aux.to_le (inf_le_left : h.P ≤ h.S)) ⟨y, (mem_inf.mp hyY).2⟩
  have hm' : y ^ 2 ^ m = 1 := congrArg Subtype.val hm
  have hex : ∃ k, y ^ 2 ^ (k + 1) ∈ h.T := ⟨m, by
    rw [pow_succ, pow_mul, hm', one_pow]
    exact one_mem _⟩
  have hkT : y ^ 2 ^ (Nat.find hex + 1) ∈ h.T := Nat.find_spec hex
  have hkT' : y ^ 2 ^ Nat.find hex ∉ h.T := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with hk0 | hk0
    · rw [hk0, pow_zero, pow_one]
      exact hyT
    · obtain ⟨l, hl⟩ := Nat.exists_eq_succ_of_ne_zero hk0.ne'
      have := Nat.find_min hex (show l < Nat.find hex by omega)
      rw [hl]
      exact this
  refine ⟨y ^ 2 ^ Nat.find hex, pow_mem hyY _, hkT', ?_⟩
  rw [← pow_mul, ← pow_succ]
  exact hkT

@[expose] def Lemma61Conclusion (y : H) : Prop :=
  (y ∈ h.upperP 2 ∧ ⁅h.B, zpowers y⁆ = zpowers h.a) ∨
    (y ∈ h.upperP 3 ∧ ∃ b : H, orderOf b = 2 ∧ h.x⁻¹ * b * h.x = h.a * b ∧
      h.upperP 2 = closure {h.a, b} ∧ b ∈ h.B ⊓ conjugate h.B y ∧ y * b = b * y ∧
      ⁅h.B, zpowers y⁆ ≤ closure {h.a, b} ∧
      ((centralizer ({b} : Set H)).subgroupOf h.S).index = 2)

@[expose] def Lemma61Shape (y : H) : Prop :=
  ⁅h.B, zpowers y⁆ = zpowers h.a ∨
    ∃ b : H, orderOf b = 2 ∧ h.x⁻¹ * b * h.x = h.a * b ∧ h.upperP 2 = closure {h.a, b} ∧
      b ∈ h.B ⊓ conjugate h.B y ∧ y * b = b * y ∧ ⁅h.B, zpowers y⁆ ≤ closure {h.a, b} ∧
      ((centralizer ({b} : Set H)).subgroupOf h.S).index = 2

theorem Lemma61Conclusion.shape {y : H} (hy : h.Lemma61Conclusion y) : h.Lemma61Shape y := by
  rcases hy with ⟨-, h1⟩ | ⟨-, h2⟩
  · exact Or.inl h1
  · exact Or.inr h2


section Lemma61

variable {h}
variable (hT : h.T = h.B ⊔ zpowers h.a)
  (hC : h.P ⊓ centralizer (h.S : Set H) = zpowers h.a)

omit [Finite H] in
private theorem mem_conjugate_iff_aux {X : Subgroup H} {g y : H} :
    y ∈ conjugate X g ↔ g * y * g⁻¹ ∈ X := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa [mul_assoc] using hx
  · intro hy
    exact ⟨g * y * g⁻¹, hy, by simp [mul_assoc]⟩

omit [Finite H] in
private theorem mem_zpowers_of_sq {a y : H} (ha : a * a = 1) (hy : y ∈ zpowers a) :
    y = 1 ∨ y = a := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
  have h2 : a ^ (2 : ℤ) = 1 := by rw [zpow_two, ha]
  obtain ⟨r, hr | hr⟩ := Int.even_or_odd' k
  · left
    rw [hr, zpow_mul, h2, one_zpow]
  · right
    rw [hr, zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]

include hC in
private theorem a_mem_P : h.a ∈ h.P :=
  (mem_inf.mp (hC.symm ▸ mem_zpowers h.a : h.a ∈ h.P ⊓ centralizer (h.S : Set H))).1

include hC in
private theorem a_comm {s : H} (hs : s ∈ h.S) : s * h.a = h.a * s :=
  mem_centralizer_iff.mp
    (mem_inf.mp (hC.symm ▸ mem_zpowers h.a : h.a ∈ h.P ⊓ centralizer (h.S : Set H))).2 s hs

private theorem a_mul_a (h : Hyp52 H) : h.a * h.a = 1 := by
  rw [← pow_two, ← h.orderOf_a, pow_orderOf_eq_one]

include hC in
private theorem a_mem_T : h.a ∈ h.T := by
  have haP := a_mem_P hC
  exact mem_inf.mpr ⟨mem_inf.mpr ⟨(mem_inf.mp haP).1, h.a_mem_normalizer⟩, haP⟩

include hC in
private theorem a_not_mem_B : h.a ∉ h.B := by
  intro haB
  have hax : h.x * h.a * h.x⁻¹ = h.a := by
    rw [a_comm hC h.x_mem, mul_inv_cancel_right]
  have hmem : h.a ∈ h.B ⊓ conjugate h.B h.x :=
    mem_inf.mpr ⟨haB, mem_conjugate_iff_aux.mpr (hax.symm ▸ haB)⟩
  rw [h.inf_conjugate_x, mem_bot] at hmem
  have := h.orderOf_a
  rw [hmem, orderOf_one] at this
  exact absurd this (by norm_num)

include hC in
private theorem upperP_one : h.upperP 1 = zpowers h.a := by
  rw [← hC, upperP, inf_comm]
  ext y
  simp only [mem_inf, h.mem_upperS_one, mem_centralizer_iff]
  constructor
  · rintro ⟨hyP, -, hy⟩
    exact ⟨hyP, fun s hs => (hy s hs).symm⟩
  · rintro ⟨hyP, hy⟩
    exact ⟨hyP, (mem_inf.mp hyP).1, fun s hs => (hy s hs).symm⟩

include hT hC in
private theorem mem_T_cases {y : H} (hy : y ∈ h.T) : ∃ β ∈ h.B, y = β ∨ y = β * h.a := by
  have hB2 : ∀ β ∈ h.B, β * h.a = h.a * β := fun β hβ =>
    a_comm hC ((h.B_le.trans inf_le_left) hβ)
  let K : Subgroup H :=
    { carrier := {y | ∃ β ∈ h.B, y = β ∨ y = β * h.a}
      mul_mem' := by
        rintro y z ⟨β, hβ, hy⟩ ⟨γ, hγ, hz⟩
        refine ⟨β * γ, mul_mem hβ hγ, ?_⟩
        rcases hy with hy | hy <;> rcases hz with hz | hz <;> rw [hy, hz]
        · exact Or.inl rfl
        · exact Or.inr (by group)
        · refine Or.inr ?_
          rw [mul_assoc, ← hB2 γ hγ, ← mul_assoc]
        · refine Or.inl ?_
          rw [show β * h.a * (γ * h.a) = β * (h.a * γ) * h.a by group, ← hB2 γ hγ,
            show β * (γ * h.a) * h.a = β * γ * (h.a * h.a) by group, a_mul_a h, mul_one]
      one_mem' := ⟨1, one_mem _, Or.inl rfl⟩
      inv_mem' := by
        rintro y ⟨β, hβ, hy⟩
        refine ⟨β⁻¹, inv_mem hβ, ?_⟩
        rcases hy with hy | hy <;> rw [hy]
        · exact Or.inl rfl
        · refine Or.inr ?_
          have ha' : h.a⁻¹ = h.a := inv_eq_of_mul_eq_one_right (a_mul_a h)
          rw [mul_inv_rev, ha', eq_comm, inv_mul_eq_iff_eq_mul, ← mul_assoc, hB2 β hβ,
            mul_assoc, mul_inv_cancel, mul_one] }
  have hle : h.B ⊔ zpowers h.a ≤ K := by
    refine sup_le (fun β hβ => ⟨β, hβ, Or.inl rfl⟩) ?_
    rw [zpowers_le]
    exact ⟨1, one_mem _, Or.inr (one_mul _).symm⟩
  rw [hT] at hy
  exact hle hy

private theorem conj_x_of_comm_mem {β : H} (hβ : β ∈ h.B) (hβ1 : β ≠ 1)
    (hc : ⁅β, h.x⁆ ∈ zpowers h.a) : h.x * β * h.x⁻¹ = h.a * β := by
  rcases mem_zpowers_of_sq (a_mul_a h) hc with hc | hc
  · exfalso
    apply hβ1
    have hcomm : β * h.x = h.x * β := commutatorElement_eq_one_iff_mul_comm.mp hc
    have hmem : β ∈ h.B ⊓ conjugate h.B h.x := by
      refine mem_inf.mpr ⟨hβ, mem_conjugate_iff_aux.mpr ?_⟩
      rw [← hcomm, mul_inv_cancel_right]
      exact hβ
    rwa [h.inf_conjugate_x, mem_bot] at hmem
  · rw [commutatorElement_def] at hc
    have ha' : h.a⁻¹ = h.a := inv_eq_of_mul_eq_one_right (a_mul_a h)
    calc h.x * β * h.x⁻¹ = (β * h.x * β⁻¹ * h.x⁻¹)⁻¹ * β := by group
      _ = h.a * β := by rw [hc, ha']

include hC in
private theorem mul_eq_one_of_conj_x {β γ : H} (hβ : β ∈ h.B) (hγ : γ ∈ h.B)
    (hβx : h.x * β * h.x⁻¹ = h.a * β) (hγx : h.x * γ * h.x⁻¹ = h.a * γ) : β * γ = 1 := by
  have hβa : β * h.a = h.a * β := a_comm hC ((h.B_le.trans inf_le_left) hβ)
  have hconj : h.x * (β * γ) * h.x⁻¹ = β * γ := by
    calc h.x * (β * γ) * h.x⁻¹ = (h.x * β * h.x⁻¹) * (h.x * γ * h.x⁻¹) := by group
      _ = h.a * β * (h.a * γ) := by rw [hβx, hγx]
      _ = β * γ := by
        rw [← hβa, show β * h.a * (h.a * γ) = β * (h.a * h.a) * γ by group, a_mul_a h, mul_one]
  have hmem : β * γ ∈ h.B ⊓ conjugate h.B h.x :=
    mem_inf.mpr ⟨mul_mem hβ hγ, mem_conjugate_iff_aux.mpr (hconj.symm ▸ mul_mem hβ hγ)⟩
  rwa [h.inf_conjugate_x, mem_bot] at hmem

private theorem x_sq_normalizes {β : H} (hβ : β ∈ h.B) :
    h.x ^ 2 * β * (h.x ^ 2)⁻¹ ∈ h.B :=
  (mem_normalizer_iff.mp (mem_inf.mp h.x_sq_mem).2 β).mp hβ

private theorem T_le_normalizer (h : Hyp52 H) : h.T ≤ normalizer (h.B : Set H) :=
  inf_le_left.trans inf_le_right

private theorem P_le_S (h : Hyp52 H) : h.P ≤ h.S := inf_le_left

include hT hC in
theorem lemma61 (hBP : ¬ h.P ≤ normalizer (h.B : Set H)) {y : H} (hy : h.IsX0Min y) :
    h.Lemma61Conclusion y := by
  classical
  unfold Lemma61Conclusion
  obtain ⟨hyU, hyT, hy2⟩ := hy
  obtain ⟨hnot, hmin⟩ := h.x0Index_spec ⟨_, fun hle => hyT (hle hyU)⟩
  have haT := a_mem_T hC
  have haP := a_mem_P hC
  have haS : h.a ∈ h.S := h.P_le_S haP
  have haB := a_not_mem_B hC
  have hP1 := upperP_one hC
  have haa := a_mul_a h
  have ha' : h.a⁻¹ = h.a := inv_eq_of_mul_eq_one_right haa
  have ha1 : h.a ≠ 1 := by
    intro h1
    have := h.orderOf_a
    rw [h1, orderOf_one] at this
    exact absurd this (by norm_num)
  have haU1 : h.a ∈ h.upperS 1 := (mem_inf.mp (hP1.symm ▸ mem_zpowers h.a :
    h.a ∈ h.upperP 1)).1
  have hBS : ∀ {β}, β ∈ h.B → β ∈ h.S := fun hβ => (h.B_le.trans inf_le_left) hβ
  have hBP' : ∀ {β}, β ∈ h.B → β ∈ h.P := fun hβ => h.B_le hβ
  have hPT : ¬ h.P ≤ h.T := fun hle => hBP (hle.trans (T_le_normalizer h))
  have hi2 : 2 ≤ h.x0Index := by
    by_contra hlt
    push Not at hlt
    apply hnot
    interval_cases hi : h.x0Index
    · rw [upperP, upperS_zero, bot_inf_eq]
      exact bot_le
    · rw [hP1, zpowers_le]
      exact haT
  have hcommB : ∀ {i : ℕ} {β g : H}, β ∈ h.B → g ∈ h.upperP (i + 1) → ⁅β, g⁆ ∈ h.upperP i := by
    intro i β g hβ hg
    exact mem_inf.mpr ⟨(h.commutator_mem_upperS (mem_inf.mp hg).1 (hBS hβ)).2,
      (h.commutator_mem_P (mem_inf.mp hg).2 (hBS hβ)).2⟩
  rcases Nat.lt_or_ge h.x0Index 3 with hi3 | hi3
  ·
    have hi : h.x0Index = 2 := by omega
    rw [hi] at hyU
    left
    refine ⟨hyU, le_antisymm ?_ ?_⟩
    · rw [commutator_le]
      intro β hβ g hg
      have hgU : g ∈ h.upperP 2 := (zpowers_le.mpr hyU) hg
      rw [← hP1]
      exact hcommB hβ hgU
    · rw [zpowers_le]
      by_contra hna
      apply hyT
      have hcomm : ∀ β ∈ h.B, β * y = y * β := by
        intro β hβ
        have h1 : ⁅β, y⁆ ∈ zpowers h.a := hP1 ▸ hcommB hβ hyU
        rcases mem_zpowers_of_sq haa h1 with h1 | h1
        · exact commutatorElement_eq_one_iff_mul_comm.mp h1
        · exact absurd (h1 ▸ commutator_mem_commutator hβ (mem_zpowers y)) hna
      have hyN : y ∈ normalizer (h.B : Set H) := by
        rw [mem_normalizer_iff]
        intro β
        constructor
        · intro hβ
          rw [← hcomm β hβ, mul_inv_cancel_right]
          exact hβ
        · intro hβ
          have hβ' : y⁻¹ * (y * β * y⁻¹) * y ∈ h.B := by
            have hm := hcomm _ hβ
            rw [show y⁻¹ * (y * β * y⁻¹) * y = y⁻¹ * ((y * β * y⁻¹) * y) by group, hm,
              inv_mul_cancel_left]
            exact hβ
          rwa [show y⁻¹ * (y * β * y⁻¹) * y = β by group] at hβ'
      have hyP := (mem_inf.mp hyU).2
      exact mem_inf.mpr ⟨mem_inf.mpr ⟨(mem_inf.mp hyP).1, hyN⟩, hyP⟩
  ·
    have hU2T : h.upperP 2 ≤ h.T := hmin 2 (by omega)
    have hP1' : ¬ h.P ≤ h.upperS 1 := by
      intro hle
      apply hPT
      intro w hw
      have : w ∈ h.upperP 1 := mem_inf.mpr ⟨hle hw, hw⟩
      rw [hP1] at this
      exact (zpowers_le.mpr haT) this
    obtain ⟨w, hwP, hw2, hw1⟩ := h.exists_mem_upperP_succ 1 hP1'
    obtain ⟨b, hbB, hwb⟩ := mem_T_cases hT hC (hU2T (mem_inf.mpr ⟨hw2, hwP⟩))
    have haU2 : h.a ∈ h.upperS 2 := h.upperS_mono (by norm_num) haU1
    have hbU2 : b ∈ h.upperS 2 := by
      rcases hwb with rfl | rfl
      · exact hw2
      · have := mul_mem hw2 (inv_mem haU2)
        rwa [mul_inv_cancel_right] at this
    have hbU1 : b ∉ h.upperS 1 := by
      intro hb1
      apply hw1
      rcases hwb with rfl | rfl
      · exact hb1
      · exact mul_mem hb1 haU1
    have hb1 : b ≠ 1 := fun h1 => hbU1 (h1 ▸ one_mem _)
    have hbx : h.x * b * h.x⁻¹ = h.a * b := by
      refine conj_x_of_comm_mem hbB hb1 ?_
      rw [← hP1]
      exact mem_inf.mpr ⟨(h.commutator_mem_upperS hbU2 h.x_mem).1,
        (h.commutator_mem_P (hBP' hbB) h.x_mem).1⟩
    have hbb : b * b = 1 := mul_eq_one_of_conj_x hC hbB hbB hbx hbx
    have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right hbb
    have hab : b * h.a = h.a * b := a_comm hC (hBS hbB)
    have hU2cases : ∀ w ∈ h.upperP 2, w = 1 ∨ w = h.a ∨ w = b ∨ w = b * h.a := by
      intro w hw
      obtain ⟨β, hβB, hwβ⟩ := mem_T_cases hT hC (hU2T hw)
      have hβU2 : β ∈ h.upperP 2 := by
        rcases hwβ with rfl | rfl
        · exact hw
        · have := mul_mem hw (inv_mem (mem_inf.mpr ⟨haU2, haP⟩))
          rwa [mul_inv_cancel_right] at this
      have hβ : β = 1 ∨ β = b := by
        by_cases hβ1 : β = 1
        · exact Or.inl hβ1
        · right
          have hβx : h.x * β * h.x⁻¹ = h.a * β := by
            refine conj_x_of_comm_mem hβB hβ1 ?_
            rw [← hP1]
            exact mem_inf.mpr ⟨(h.commutator_mem_upperS (mem_inf.mp hβU2).1 h.x_mem).1,
              (h.commutator_mem_P (hBP' hβB) h.x_mem).1⟩
          have := mul_eq_one_of_conj_x hC hbB hβB hbx hβx
          rw [← hb', ← mul_eq_one_iff_inv_eq.mp this]
      rcases hβ with rfl | rfl <;> rcases hwβ with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl (one_mul _))
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr rfl))
    have hU2eq : h.upperP 2 = closure {h.a, b} := by
      apply le_antisymm
      · intro w hw
        have ha : h.a ∈ closure ({h.a, b} : Set H) := subset_closure (by simp)
        have hb : b ∈ closure ({h.a, b} : Set H) := subset_closure (by simp)
        rcases hU2cases w hw with rfl | rfl | rfl | rfl
        · exact one_mem _
        · exact ha
        · exact hb
        · exact mul_mem hb ha
      · rw [closure_le]
        intro w hw
        rcases hw with rfl | rfl
        · exact mem_inf.mpr ⟨haU2, haP⟩
        · exact mem_inf.mpr ⟨hbU2, hBP' hbB⟩
    have hU3T : ∀ w ∈ h.upperS 3, w ∈ h.T → w ∈ h.upperP 2 := by
      intro w hw3 hwT
      obtain ⟨β, hβB, hwβ⟩ := mem_T_cases hT hC hwT
      have haU3 : h.a ∈ h.upperS 3 := h.upperS_mono (by norm_num) haU1
      have hβU3 : β ∈ h.upperS 3 := by
        rcases hwβ with rfl | rfl
        · exact hw3
        · have := mul_mem hw3 (inv_mem haU3)
          rwa [mul_inv_cancel_right] at this
      have hc : ⁅β, h.x⁆ ∈ h.upperP 2 :=
        mem_inf.mpr ⟨(h.commutator_mem_upperS hβU3 h.x_mem).1,
          (h.commutator_mem_P (hBP' hβB) h.x_mem).1⟩
      have hxa : h.x * h.a * h.x⁻¹ = h.a := by rw [a_comm hC h.x_mem, mul_inv_cancel_right]
      have hkey : ⁅β, h.x⁆ = b ∨ ⁅β, h.x⁆ = b * h.a → h.a ∈ h.B := by
        intro hc'
        have hcc : ⁅β, h.x⁆ * ⁅β, h.x⁆ = 1 := by
          rcases hc' with hc' | hc'
          · rw [hc', hbb]
          · rw [hc']
            calc b * h.a * (b * h.a) = b * (h.a * b) * h.a := by group
              _ = b * (b * h.a) * h.a := by rw [hab]
              _ = (b * b) * (h.a * h.a) := by group
              _ = 1 := by rw [hbb, haa, one_mul]
        have hinv : ⁅β, h.x⁆⁻¹ = ⁅β, h.x⁆ := inv_eq_of_mul_eq_one_right hcc
        have hβx : h.x * β * h.x⁻¹ = ⁅β, h.x⁆ * β := by
          calc h.x * β * h.x⁻¹ = ⁅β, h.x⁆⁻¹ * β := by rw [commutatorElement_def]; group
            _ = ⁅β, h.x⁆ * β := by rw [hinv]
        have hxc : h.x * ⁅β, h.x⁆ * h.x⁻¹ * ⁅β, h.x⁆ = h.a := by
          rcases hc' with hc' | hc'
          · rw [hc', hbx, mul_assoc, hbb, mul_one]
          · rw [hc']
            calc h.x * (b * h.a) * h.x⁻¹ * (b * h.a)
                = (h.x * b * h.x⁻¹) * (h.x * h.a * h.x⁻¹) * (b * h.a) := by group
              _ = h.a * b * h.a * (b * h.a) := by rw [hbx, hxa]
              _ = h.a * (b * h.a) * (b * h.a) := by group
              _ = h.a * (h.a * b) * (h.a * b) := by rw [hab]
              _ = (h.a * h.a) * b * (h.a * b) := by group
              _ = b * (h.a * b) := by rw [haa, one_mul]
              _ = b * (b * h.a) := by rw [hab]
              _ = (b * b) * h.a := by group
              _ = h.a := by rw [hbb, one_mul]
        have hx2 : h.x ^ 2 * β * (h.x ^ 2)⁻¹ = h.a * β := by
          calc h.x ^ 2 * β * (h.x ^ 2)⁻¹ = h.x * (h.x * β * h.x⁻¹) * h.x⁻¹ := by
                rw [pow_two]; group
            _ = h.x * (⁅β, h.x⁆ * β) * h.x⁻¹ := by rw [hβx]
            _ = (h.x * ⁅β, h.x⁆ * h.x⁻¹) * (h.x * β * h.x⁻¹) := by group
            _ = (h.x * ⁅β, h.x⁆ * h.x⁻¹) * (⁅β, h.x⁆ * β) := by rw [hβx]
            _ = (h.x * ⁅β, h.x⁆ * h.x⁻¹ * ⁅β, h.x⁆) * β := by group
            _ = h.a * β := by rw [hxc]
        have hmem := x_sq_normalizes hβB
        rw [hx2] at hmem
        have := mul_mem hmem (inv_mem hβB)
        rwa [mul_inv_cancel_right] at this
      have hβ : β = 1 ∨ β = b := by
        by_cases hβ1 : β = 1
        · exact Or.inl hβ1
        · right
          rcases hU2cases _ hc with hc' | hc' | hc' | hc'
          · have hβx := conj_x_of_comm_mem hβB hβ1 (hc' ▸ one_mem _)
            have := mul_eq_one_of_conj_x hC hbB hβB hbx hβx
            rw [← hb', ← mul_eq_one_iff_inv_eq.mp this]
          · have hβx := conj_x_of_comm_mem hβB hβ1 (hc' ▸ mem_zpowers _)
            have := mul_eq_one_of_conj_x hC hbB hβB hbx hβx
            rw [← hb', ← mul_eq_one_iff_inv_eq.mp this]
          · exact absurd (hkey (Or.inl hc')) haB
          · exact absurd (hkey (Or.inr hc')) haB
      rcases hβ with rfl | rfl <;> rcases hwβ with rfl | rfl
      · exact one_mem _
      · rw [one_mul]
        exact mem_inf.mpr ⟨haU2, haP⟩
      · exact mem_inf.mpr ⟨hbU2, hBP' hbB⟩
      · exact mul_mem (mem_inf.mpr ⟨hbU2, hBP' hbB⟩) (mem_inf.mpr ⟨haU2, haP⟩)
    have hU3 : ¬ h.upperP 3 ≤ h.T := by
      intro hle
      have hP2 : ¬ h.P ≤ h.upperS 2 := by
        intro hle2
        exact hPT fun w hw => hU2T (mem_inf.mpr ⟨hle2 hw, hw⟩)
      obtain ⟨w, hwP, hw3, hw2'⟩ := h.exists_mem_upperP_succ 2 hP2
      exact hw2' (mem_inf.mp (hU3T w hw3 (hle (mem_inf.mpr ⟨hw3, hwP⟩)))).1
    have hi : h.x0Index = 3 := by
      have hle3 : h.x0Index ≤ 3 := by
        by_contra hgt
        push Not at hgt
        exact hU3 (hmin 3 hgt)
      omega
    rw [hi] at hyU
    right
    have hcommU : ⁅h.B, zpowers y⁆ ≤ closure {h.a, b} := by
      rw [commutator_le, ← hU2eq]
      intro β hβ g hg
      exact hcommB hβ ((zpowers_le.mpr hyU) hg)
    have hyS : y ∈ h.S := h.P_le_S (mem_inf.mp hyU).2
    have hby : b * y = y * b := by
      have h1 : ⁅b, y⁆ ∈ zpowers h.a := by
        rw [← hP1]
        exact mem_inf.mpr ⟨(h.commutator_mem_upperS hbU2 hyS).1,
          (h.commutator_mem_P (hBP' hbB) hyS).1⟩
      rcases mem_zpowers_of_sq haa h1 with h1 | h1
      · exact commutatorElement_eq_one_iff_mul_comm.mp h1
      · exfalso
        rw [commutatorElement_def] at h1
        have hyb : y * b * y⁻¹ = h.a * b := by
          calc y * b * y⁻¹ = (b * y * b⁻¹ * y⁻¹)⁻¹ * b := by group
            _ = h.a * b := by rw [h1, ha']
        have hy2U : y ^ 2 ∈ h.upperP 2 :=
          hU3T _ (pow_mem (mem_inf.mp hyU).1 _) hy2
        have hy2c : y * y ^ 2 * y⁻¹ = y ^ 2 := by group
        have hy2a : y ^ 2 = 1 ∨ y ^ 2 = h.a := by
          rcases hU2cases _ hy2U with h2 | h2 | h2 | h2
          · exact Or.inl h2
          · exact Or.inr h2
          · exfalso
            rw [h2, hyb] at hy2c
            apply ha1
            have := congrArg (· * b⁻¹) hy2c
            simpa using this
          · exfalso
            rw [h2, show y * (b * h.a) * y⁻¹ = (y * b * y⁻¹) * (y * h.a * y⁻¹) by group, hyb,
              a_comm hC hyS, mul_inv_cancel_right, ← hab,
              show b * h.a * h.a = b * (h.a * h.a) by group, haa, mul_one] at hy2c
            apply ha1
            have := congrArg (b⁻¹ * ·) hy2c
            simpa using this.symm
        have hy2S : ∀ s ∈ h.S, s * y ^ 2 * s⁻¹ = y ^ 2 := by
          intro s hs
          rcases hy2a with h2 | h2
          · rw [h2]
            group
          · rw [h2, a_comm hC hs, mul_inv_cancel_right]
        apply hyT
        apply hU2T
        refine mem_inf.mpr ⟨h.mem_upperS_succ.mpr ⟨hyS, fun s hs => ?_⟩, (mem_inf.mp hyU).2⟩
        rw [← commutatorElement_inv]
        refine inv_mem ?_
        have hcU : ⁅s, y⁆ ∈ h.upperP 2 :=
          mem_inf.mpr ⟨(h.commutator_mem_upperS (mem_inf.mp hyU).1 hs).2,
            (h.commutator_mem_P (mem_inf.mp hyU).2 hs).2⟩
        have hsy : s * y * s⁻¹ = ⁅s, y⁆ * y := by
          rw [commutatorElement_def]
          group
        have hsq : ⁅s, y⁆ * y * (⁅s, y⁆ * y) = y ^ 2 := by
          rw [← hsy, show s * y * s⁻¹ * (s * y * s⁻¹) = s * y ^ 2 * s⁻¹ by rw [pow_two]; group,
            hy2S s hs]
        rcases hU2cases _ hcU with hc | hc | hc | hc
        · rw [hc]
          exact one_mem _
        · rw [hc]
          exact haU1
        · exfalso
          rw [hc, show b * y * (b * y) = b * (y * b * y⁻¹) * y ^ 2 by group, hyb,
            show b * (h.a * b) * y ^ 2 = (b * h.a) * b * y ^ 2 by group, hab,
            show h.a * b * b * y ^ 2 = h.a * (b * b) * y ^ 2 by group, hbb, mul_one] at hsq
          apply ha1
          have := congrArg (· * (y ^ 2)⁻¹) hsq
          simpa using this
        · exfalso
          rw [hc, show b * h.a * y * (b * h.a * y) = b * h.a * (y * b * y⁻¹) *
              (y * h.a * y⁻¹) * y ^ 2 by group, hyb, a_comm hC hyS, mul_inv_cancel_right,
            show b * h.a * (h.a * b) * h.a * y ^ 2 = b * (h.a * h.a) * b * h.a * y ^ 2 by group,
            haa, mul_one, hbb, one_mul] at hsq
          apply ha1
          have := congrArg (· * (y ^ 2)⁻¹) hsq
          simpa using this
    have hbB0 : b ∈ h.B ⊓ conjugate h.B y := by
      refine mem_inf.mpr ⟨hbB, mem_conjugate_iff_aux.mpr ?_⟩
      rw [← hby, mul_inv_cancel_right]
      exact hbB
    have hindex : ((centralizer ({b} : Set H)).subgroupOf h.S).index = 2 := by
      have hbs : ∀ s ∈ h.S, ⁅b, s⁆ = 1 ∨ ⁅b, s⁆ = h.a := by
        intro s hs
        refine mem_zpowers_of_sq haa ?_
        rw [← hP1]
        exact mem_inf.mpr ⟨(h.commutator_mem_upperS hbU2 hs).1,
          (h.commutator_mem_P (hBP' hbB) hs).1⟩
      obtain ⟨s₀, hs₀, hbs₀⟩ : ∃ s₀ ∈ h.S, ⁅b, s₀⁆ = h.a := by
        by_contra hno
        push Not at hno
        apply hbU1
        refine h.mem_upperS_one.mpr ⟨hBS hbB, fun s hs => ?_⟩
        rcases hbs s hs with h1 | h1
        · exact commutatorElement_eq_one_iff_mul_comm.mp h1
        · exact absurd h1 (hno s hs)
      have hmemC : ∀ t : h.S,
          t ∈ (centralizer ({b} : Set H)).subgroupOf h.S ↔ ⁅b, (t : H)⁆ = 1 := by
        intro t
        rw [mem_subgroupOf, mem_centralizer_singleton_iff, commutatorElement_eq_one_iff_mul_comm]
        exact eq_comm
      refine index_eq_two_iff.mpr ⟨⟨s₀, hs₀⟩, fun t => ?_⟩
      rw [hmemC, hmemC]
      have hts : ⁅b, (t : H) * s₀⁆ = ⁅b, (t : H)⁆ * h.a := by
        rw [show ⁅b, (t : H) * s₀⁆ = ⁅b, (t : H)⁆ * ((t : H) * ⁅b, s₀⁆ * (t : H)⁻¹) by
          simp only [commutatorElement_def]; group, hbs₀, a_comm hC t.2, mul_inv_cancel_right]
      simp only [Subgroup.coe_mul]
      rw [hts]
      rcases hbs t t.2 with h1 | h1
      · rw [h1, one_mul]
        simp [ha1]
      · rw [h1, haa]
        simp [ha1]
    refine ⟨hyU, b, orderOf_eq_prime (by rw [pow_two, hbb]) hb1, ?_, hU2eq, hbB0, hby.symm,
      hcommU, hindex⟩
    have hxa' : h.x⁻¹ * h.a * h.x = h.a := by
      rw [mul_assoc, ← a_comm hC h.x_mem, inv_mul_cancel_left]
    calc h.x⁻¹ * b * h.x = h.x⁻¹ * (h.a * (h.a * b)) * h.x := by
          rw [show h.a * (h.a * b) = b by rw [← mul_assoc, haa, one_mul]]
      _ = h.x⁻¹ * (h.a * (h.x * b * h.x⁻¹)) * h.x := by rw [hbx]
      _ = (h.x⁻¹ * h.a * h.x) * b := by group
      _ = h.a * b := by rw [hxa']

end Lemma61

end Hyp52

namespace Six

variable {h : Hyp52 H}

theorem a_mul_a_self (h : Hyp52 H) : h.a * h.a = 1 := Hyp52.a_mul_a h

theorem eq_one_or_eq_a {y : H} (hy : y ∈ zpowers h.a) : y = 1 ∨ y = h.a :=
  Hyp52.mem_zpowers_of_sq (Hyp52.a_mul_a h) hy

theorem conj_mem_P (h : Hyp52 H) {s y : H} (hs : s ∈ h.S) (hy : y ∈ h.P) : s * y * s⁻¹ ∈ h.P :=
  h.conj_mem_P_aux hs hy

theorem isPGroup_S (h : Hyp52 H) : IsPGroup 2 h.S := h.isPGroup_S_aux

variable (hC : h.P ⊓ centralizer (h.S : Set H) = zpowers h.a)
include hC

theorem a_mem_P : h.a ∈ h.P := Hyp52.a_mem_P hC

theorem comm_a {s : H} (hs : s ∈ h.S) : s * h.a = h.a * s := Hyp52.a_comm hC hs

theorem a_not_mem_B : h.a ∉ h.B := Hyp52.a_not_mem_B hC

theorem upperP_one_eq : h.upperP 1 = zpowers h.a := Hyp52.upperP_one hC

end Six

end CFSG.ComponentClassification.GSThmB
