module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GrpDefs

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup
open scoped commutatorElement

section ClassTwo

variable {A : Type} [Group A] {W : Subgroup A}

private lemma comm_mem_W {a b : A} (ha : a ∈ W) (hb : b ∈ W) : ⁅a, b⁆ ∈ W := by
  rw [commutatorElement_def]
  exact W.mul_mem (W.mul_mem (W.mul_mem ha hb) (W.inv_mem ha)) (W.inv_mem hb)

private lemma mem_Z_iff {u : A} :
    u ∈ W ⊓ centralizer (W : Set A) ↔ u ∈ W ∧ ∀ w ∈ W, w * u = u * w := by
  simp [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]

private lemma comm_central
    (hW2 : ∀ a ∈ W, ∀ b ∈ W, ∀ c ∈ W, ⁅⁅a, b⁆, c⁆ = 1)
    {a b c : A} (ha : a ∈ W) (hb : b ∈ W) (hc : c ∈ W) : c * ⁅a, b⁆ = ⁅a, b⁆ * c :=
  (commutatorElement_eq_one_iff_mul_comm.mp (hW2 a ha b hb c hc)).symm

private lemma comm_mem_Z
    (hW2 : ∀ a ∈ W, ∀ b ∈ W, ∀ c ∈ W, ⁅⁅a, b⁆, c⁆ = 1)
    {a b : A} (ha : a ∈ W) (hb : b ∈ W) : ⁅a, b⁆ ∈ W ⊓ centralizer (W : Set A) :=
  mem_Z_iff.mpr ⟨comm_mem_W ha hb, fun _ hc => comm_central hW2 ha hb hc⟩

private lemma derived_le_Z
    (hW2 : ∀ a ∈ W, ∀ b ∈ W, ∀ c ∈ W, ⁅⁅a, b⁆, c⁆ = 1) :
    ⁅W, W⁆ ≤ W ⊓ centralizer (W : Set A) := by
  rw [Subgroup.commutator_def, Subgroup.closure_le]
  rintro _ ⟨a, ha, b, hb, rfl⟩
  exact comm_mem_Z hW2 ha hb

private lemma Z_comm {u w : A} (hu : u ∈ W ⊓ centralizer (W : Set A)) (hw : w ∈ W) :
    w * u = u * w :=
  (mem_Z_iff.mp hu).2 w hw

private lemma comm_mul_left
    (hW2 : ∀ a ∈ W, ∀ b ∈ W, ∀ c ∈ W, ⁅⁅a, b⁆, c⁆ = 1)
    {x x' y : A} (hx : x ∈ W) (hx' : x' ∈ W) (hy : y ∈ W) :
    ⁅x * x', y⁆ = ⁅x', y⁆ * ⁅x, y⁆ := by
  have h1 : ⁅x', y⁆ * x = x * ⁅x', y⁆ := (comm_central hW2 hx' hy hx).symm
  have e : ⁅x * x', y⁆ = x * ⁅x', y⁆ * y * x⁻¹ * y⁻¹ := by
    simp only [commutatorElement_def]; group
  rw [e, ← h1]
  simp only [commutatorElement_def]; group

private lemma comm_mul_right
    (hW2 : ∀ a ∈ W, ∀ b ∈ W, ∀ c ∈ W, ⁅⁅a, b⁆, c⁆ = 1)
    {x y y' : A} (hx : x ∈ W) (hy : y ∈ W) (hy' : y' ∈ W) :
    ⁅x, y * y'⁆ = ⁅x, y⁆ * ⁅x, y'⁆ := by
  have h1 : y * ⁅x, y'⁆ = ⁅x, y'⁆ * y := comm_central hW2 hx hy' hy
  have e : ⁅x, y * y'⁆ = ⁅x, y⁆ * (y * ⁅x, y'⁆ * y⁻¹) := by
    simp only [commutatorElement_def]; group
  rw [e, h1]
  group

private lemma comm_inv_left
    (hW2 : ∀ a ∈ W, ∀ b ∈ W, ∀ c ∈ W, ⁅⁅a, b⁆, c⁆ = 1)
    {x y : A} (hx : x ∈ W) (hy : y ∈ W) : ⁅x⁻¹, y⁆ = ⁅x, y⁆⁻¹ := by
  have h := comm_mul_left hW2 hx (W.inv_mem hx) hy
  rw [mul_inv_cancel, commutatorElement_one_left] at h
  exact eq_inv_of_mul_eq_one_left h.symm

private lemma comm_inv_right
    (hW2 : ∀ a ∈ W, ∀ b ∈ W, ∀ c ∈ W, ⁅⁅a, b⁆, c⁆ = 1)
    {x y : A} (hx : x ∈ W) (hy : y ∈ W) : ⁅x, y⁻¹⁆ = ⁅x, y⁆⁻¹ := by
  have h := comm_mul_right hW2 hx hy (W.inv_mem hy)
  rw [mul_inv_cancel, commutatorElement_one_right] at h
  exact eq_inv_of_mul_eq_one_right h.symm

private lemma mul_self_mul
    (hW2 : ∀ a ∈ W, ∀ b ∈ W, ∀ c ∈ W, ⁅⁅a, b⁆, c⁆ = 1)
    {x y : A} (hx : x ∈ W) (hy : y ∈ W) :
    (x * y) * (x * y) = ⁅y, x⁆ * (x * x) * (y * y) := by
  have h1 : x * ⁅y, x⁆ = ⁅y, x⁆ * x := comm_central hW2 hy hx hx
  have e : (x * y) * (x * y) = x * ⁅y, x⁆ * x * y * y := by
    simp only [commutatorElement_def]; group
  rw [e, h1]
  group

end ClassTwo

section Squares

variable {A : Type} [Group A] {W : Subgroup A}

private lemma conj_mem_Z {g u : A} (hg : g ∈ normalizer (W : Set A))
    (hu : u ∈ W ⊓ centralizer (W : Set A)) : g * u * g⁻¹ ∈ W ⊓ centralizer (W : Set A) := by
  rw [mem_Z_iff] at hu ⊢
  refine ⟨(mem_set_normalizer_iff.mp hg u).mp hu.1, fun w hw => ?_⟩
  have hw' : g⁻¹ * w * g ∈ W := ((mem_set_normalizer_iff''.mp hg) w).mp hw
  have h1 := hu.2 _ hw'
  calc w * (g * u * g⁻¹) = g * ((g⁻¹ * w * g) * u) * g⁻¹ := by group
    _ = g * (u * (g⁻¹ * w * g)) * g⁻¹ := by rw [h1]
    _ = (g * u * g⁻¹) * w := by group

private lemma sq_comm_of_sq_central
    (hW2 : ∀ a ∈ W, ∀ b ∈ W, ∀ c ∈ W, ⁅⁅a, b⁆, c⁆ = 1)
    {w b : A} (hw : w ∈ W) (hb : b ∈ W) (hb2 : b * b ∈ W ⊓ centralizer (W : Set A)) :
    (w * w) * b = b * (w * w) := by
  have h1 : ⁅w, b * b⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr (Z_comm hb2 hw)
  rw [comm_mul_right hW2 hw hb hb] at h1
  have h2 : ⁅w * w, b⁆ = 1 := by rw [comm_mul_left hW2 hw hw hb]; exact h1
  exact commutatorElement_eq_one_iff_mul_comm.mp h2

private lemma exists_T (hW2 : ∀ a ∈ W, ∀ b ∈ W, ∀ c ∈ W, ⁅⁅a, b⁆, c⁆ = 1) :
    ∃ T : Subgroup A, ∀ u, u ∈ T ↔ u ∈ W ∧ u * u ∈ W ⊓ centralizer (W : Set A) := by
  refine ⟨{ carrier := {u | u ∈ W ∧ u * u ∈ W ⊓ centralizer (W : Set A)}
            mul_mem' := ?_, one_mem' := ?_, inv_mem' := ?_ }, fun u => Iff.rfl⟩
  · rintro a b ⟨ha, ha2⟩ ⟨hb, hb2⟩
    refine ⟨W.mul_mem ha hb, ?_⟩
    rw [mul_self_mul hW2 ha hb]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (comm_mem_Z hW2 hb ha) ha2) hb2
  · exact ⟨W.one_mem, by simp⟩
  · rintro a ⟨ha, ha2⟩
    refine ⟨W.inv_mem ha, ?_⟩
    have e : a⁻¹ * a⁻¹ = (a * a)⁻¹ := by group
    rw [e]; exact Subgroup.inv_mem _ ha2

private lemma sq_closure_comm
    (hW2 : ∀ a ∈ W, ∀ b ∈ W, ∀ c ∈ W, ⁅⁅a, b⁆, c⁆ = 1)
    {b : A} (hb : b ∈ W) (hb2 : b * b ∈ W ⊓ centralizer (W : Set A))
    {s : A} (hs : s ∈ closure {u : A | ∃ w ∈ W, u = w * w}) : s * b = b * s := by
  induction hs using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    exact sq_comm_of_sq_central hW2 hw hb hb2
  | one => simp
  | mul x y hx hy ihx ihy =>
    calc x * y * b = x * (y * b) := mul_assoc _ _ _
      _ = x * (b * y) := by rw [ihy]
      _ = (x * b) * y := (mul_assoc _ _ _).symm
      _ = (b * x) * y := by rw [ihx]
      _ = b * (x * y) := mul_assoc _ _ _
  | inv x hx ih =>
    have : Commute x b := ih
    exact this.inv_left

private lemma sq_closure_conj {g : A} (hg : g ∈ normalizer (W : Set A))
    {u : A} (hu : u ∈ closure {u : A | ∃ w ∈ W, u = w * w}) :
    g * u * g⁻¹ ∈ closure {u : A | ∃ w ∈ W, u = w * w} := by
  induction hu using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    apply Subgroup.subset_closure
    refine ⟨g * w * g⁻¹, (mem_set_normalizer_iff.mp hg w).mp hw, ?_⟩
    group
  | one => simp
  | mul x y hx hy ihx ihy =>
    have : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
    rw [this]; exact mul_mem ihx ihy
  | inv x hx ih =>
    have : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
    rw [this]; exact inv_mem ih

private lemma le_normalizer_of_conj {N U : Subgroup A}
    (hN : ∀ g ∈ N, ∀ u ∈ U, g * u * g⁻¹ ∈ U) : N ≤ normalizer (U : Set A) := by
  intro g hg
  rw [mem_set_normalizer_iff]
  intro u
  refine ⟨hN g hg u, fun hu => ?_⟩
  have h1 := hN g⁻¹ (N.inv_mem hg) _ hu
  have e : g⁻¹ * (g * u * g⁻¹) * g⁻¹⁻¹ = u := by group
  rwa [e] at h1

end Squares

section SqCentral

variable {A : Type} [Group A] {p : ℕ} {W X : Subgroup A} {z : A}

private theorem sq_central_of_part1 (h : Part1 p W X z) :
    ∀ w ∈ W, w * w ∈ W ⊓ centralizer (W : Set A) := by
  have hW2 := h.class_two
  obtain ⟨T, hT⟩ := exists_T hW2
  have hSqW : closure {u : A | ∃ w ∈ W, u = w * w} ≤ W := by
    rw [Subgroup.closure_le]
    rintro _ ⟨w, hw, rfl⟩
    exact W.mul_mem hw hw
  have hTinv : ∀ g ∈ normalizer (W : Set A), ∀ u ∈ T, g * u * g⁻¹ ∈ T := by
    intro g hg u hu
    rw [hT] at hu ⊢
    refine ⟨(mem_set_normalizer_iff.mp hg u).mp hu.1, ?_⟩
    have e : g * u * g⁻¹ * (g * u * g⁻¹) = g * (u * u) * g⁻¹ := by group
    rw [e]; exact conj_mem_Z hg hu.2
  have hinv : ∀ g ∈ normalizer (W : Set A), ∀ u ∈ closure {u : A | ∃ w ∈ W, u = w * w} ⊓ T,
      g * u * g⁻¹ ∈ closure {u : A | ∃ w ∈ W, u = w * w} ⊓ T := fun g hg u hu =>
    Subgroup.mem_inf.mpr ⟨sq_closure_conj hg (Subgroup.mem_inf.mp hu).1,
      hTinv g hg u (Subgroup.mem_inf.mp hu).2⟩
  have hnorm := le_normalizer_of_conj hinv
  have hab : ∀ a ∈ closure {u : A | ∃ w ∈ W, u = w * w} ⊓ T,
      ∀ b ∈ closure {u : A | ∃ w ∈ W, u = w * w} ⊓ T, a * b = b * a := by
    intro a ha b hb
    obtain ⟨ha1, ha2⟩ := Subgroup.mem_inf.mp ha
    obtain ⟨hb1, hb2⟩ := Subgroup.mem_inf.mp hb
    rw [hT] at hb2
    exact sq_closure_comm hW2 hb2.1 hb2.2 ha1
  have hcent : closure {u : A | ∃ w ∈ W, u = w * w} ⊓ T ≤ centralizer (W : Set A) :=
    h.abel_central _ (inf_le_left.trans hSqW)
      (fun w hw u hu => hinv w (Subgroup.le_normalizer hw) u hu)
      (h.setup.XW.trans hnorm) (hnorm h.setup.zW) hab
  have key : ∀ k : ℕ, ∀ s ∈ closure {u : A | ∃ w ∈ W, u = w * w},
      s ^ (2 ^ k) ∈ W ⊓ centralizer (W : Set A) → s ∈ W ⊓ centralizer (W : Set A) := by
    intro k
    induction k with
    | zero => intro s hs h0; simpa using h0
    | succ k ih =>
      intro s hs hk
      have hk' : (s ^ 2) ^ (2 ^ k) ∈ W ⊓ centralizer (W : Set A) := by
        rw [← pow_mul, ← pow_succ']; exact hk
      have hz2 : s ^ 2 ∈ W ⊓ centralizer (W : Set A) := ih _ (pow_mem hs 2) hk'
      have hsW : s ∈ W := hSqW hs
      have hsT : s ∈ T := by rw [hT]; exact ⟨hsW, by rwa [← pow_two]⟩
      exact Subgroup.mem_inf.mpr ⟨hsW, hcent (Subgroup.mem_inf.mpr ⟨hs, hsT⟩)⟩
  intro w hw
  have hmem : w * w ∈ closure {u : A | ∃ w ∈ W, u = w * w} := Subgroup.subset_closure ⟨w, hw, rfl⟩
  obtain ⟨k, hk⟩ := h.setup.W2 ⟨w * w, W.mul_mem hw hw⟩
  have h1 : (w * w) ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  exact key k _ hmem (by rw [h1]; exact one_mem _)

end SqCentral

section Exp2

variable {A : Type} [Group A] {W : Subgroup A}

private lemma comm_mul_self_eq_one
    (hW2 : ∀ a ∈ W, ∀ b ∈ W, ∀ c ∈ W, ⁅⁅a, b⁆, c⁆ = 1)
    (hsq : ∀ w ∈ W, w * w ∈ W ⊓ centralizer (W : Set A))
    {a b : A} (ha : a ∈ W) (hb : b ∈ W) : ⁅a, b⁆ * ⁅a, b⁆ = 1 := by
  rw [← comm_mul_left hW2 ha ha hb]
  exact commutatorElement_eq_one_iff_mul_comm.mpr (Z_comm (hsq a ha) hb).symm

private lemma derived_sq_eq_one
    (hW2 : ∀ a ∈ W, ∀ b ∈ W, ∀ c ∈ W, ⁅⁅a, b⁆, c⁆ = 1)
    (hsq : ∀ w ∈ W, w * w ∈ W ⊓ centralizer (W : Set A)) :
    ∀ g ∈ ⁅W, W⁆, g * g = 1 := by
  intro g hg
  rw [Subgroup.commutator_def] at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    exact comm_mul_self_eq_one hW2 hsq ha hb
  | one => simp
  | mul x y hx hy ihx ihy =>
    have hxZ : x ∈ W ⊓ centralizer (W : Set A) :=
      derived_le_Z hW2 (by rw [Subgroup.commutator_def]; exact hx)
    have hyW : y ∈ W := (mem_Z_iff.mp (derived_le_Z hW2
      (by rw [Subgroup.commutator_def]; exact hy))).1
    have hxy : y * x = x * y := Z_comm hxZ hyW
    calc x * y * (x * y) = x * (y * x) * y := by group
      _ = x * (x * y) * y := by rw [hxy]
      _ = (x * x) * (y * y) := by group
      _ = 1 := by rw [ihx, ihy, mul_one]
  | inv x hx ih =>
    calc x⁻¹ * x⁻¹ = (x * x)⁻¹ := by group
      _ = 1 := by rw [ih, inv_one]

end Exp2

section Orbit

variable {A : Type} [Group A] [Finite A]

private lemma card_le_orbit (H S : Subgroup A) (z : A) (hS : ∀ h ∈ H, ⁅h, z⁆ ∈ S) :
    Nat.card H ≤ Nat.card ↥(H ⊓ centralizer ({z} : Set A)) * Nat.card S := by
  classical
  set K : Subgroup H := (H ⊓ centralizer ({z} : Set A)).subgroupOf H with hK
  have e1 : Nat.card K * K.index = Nat.card H := Subgroup.card_mul_index K
  have e2 : Nat.card K = Nat.card ↥(H ⊓ centralizer ({z} : Set A)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have key : ∀ a b : H, a⁻¹ * b ∈ K ↔ ⁅(a : A), z⁆ = ⁅(b : A), z⁆ := by
    intro a b
    rw [hK, Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv, Set.mem_singleton_iff, forall_eq]
    constructor
    · rintro ⟨_, hc⟩
      have h3 : (b : A) * z * (b : A)⁻¹ = (a : A) * z * (a : A)⁻¹ := by
        calc (b : A) * z * (b : A)⁻¹
            = (a : A) * ((a : A)⁻¹ * (b : A) * z) * (b : A)⁻¹ := by group
          _ = (a : A) * (z * ((a : A)⁻¹ * (b : A))) * (b : A)⁻¹ := by rw [← hc]
          _ = (a : A) * z * (a : A)⁻¹ := by group
      simp only [commutatorElement_def]
      rw [h3]
    · intro he
      refine ⟨H.mul_mem (H.inv_mem a.2) b.2, ?_⟩
      have h3 : (a : A) * z * (a : A)⁻¹ = (b : A) * z * (b : A)⁻¹ := by
        have h4 := he
        simp only [commutatorElement_def] at h4
        exact mul_right_cancel h4
      calc z * ((a : A)⁻¹ * (b : A)) = (a : A)⁻¹ * ((a : A) * z * (a : A)⁻¹) * (b : A) := by group
        _ = (a : A)⁻¹ * ((b : A) * z * (b : A)⁻¹) * (b : A) := by rw [h3]
        _ = ((a : A)⁻¹ * (b : A)) * z := by group
  have e3 : K.index ≤ Nat.card S := by
    rw [Subgroup.index_eq_card]
    let F : H ⧸ K → S := Quotient.lift (s := QuotientGroup.leftRel K)
      (fun g => (⟨⁅(g : A), z⁆, hS g g.2⟩ : S)) (by
        intro a b hab
        have hab' : a⁻¹ * b ∈ K := QuotientGroup.leftRel_apply.mp hab
        apply Subtype.ext
        exact (key a b).mp hab')
    have hF : Function.Injective F := by
      intro u v huv
      induction u using QuotientGroup.induction_on with
      | _ a =>
        induction v using QuotientGroup.induction_on with
        | _ b =>
          have h' : ⁅(a : A), z⁆ = ⁅(b : A), z⁆ := congrArg Subtype.val huv
          exact QuotientGroup.eq.mpr ((key a b).mpr h')
    exact Nat.card_le_card_of_injective F hF
  calc Nat.card H = Nat.card K * K.index := e1.symm
    _ ≤ Nat.card ↥(H ⊓ centralizer ({z} : Set A)) * Nat.card S := by
      rw [e2]; exact Nat.mul_le_mul_left _ e3

end Orbit

section Dsub

variable {A : Type} [Group A]

private lemma exists_Dsub (W : Subgroup A) (z : A) :
    ∃ D : Subgroup A, ∀ u, u ∈ D ↔ u ∈ W ∧ ⁅u, z⁆ ∈ W ⊓ centralizer (W : Set A) := by
  refine ⟨{ carrier := {u | u ∈ W ∧ ⁅u, z⁆ ∈ W ⊓ centralizer (W : Set A)}
            mul_mem' := ?_, one_mem' := ?_, inv_mem' := ?_ }, fun u => Iff.rfl⟩
  · rintro a b ⟨ha, ha2⟩ ⟨hb, hb2⟩
    refine ⟨W.mul_mem ha hb, ?_⟩
    have e : ⁅a * b, z⁆ = (a * ⁅b, z⁆ * a⁻¹) * ⁅a, z⁆ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact Subgroup.mul_mem _ (conj_mem_Z (Subgroup.le_normalizer ha) hb2) ha2
  · exact ⟨W.one_mem, by simp⟩
  · rintro a ⟨ha, ha2⟩
    refine ⟨W.inv_mem ha, ?_⟩
    have e : ⁅a⁻¹, z⁆ = a⁻¹ * ⁅a, z⁆⁻¹ * a⁻¹⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact conj_mem_Z (Subgroup.le_normalizer (W.inv_mem ha)) (Subgroup.inv_mem _ ha2)

end Dsub

section Part1Facts

variable {A : Type} [Group A] {p : ℕ} {W X : Subgroup A} {z : A}

private lemma Z_eq_derived_of_part1 (h : Part1 p W X z) :
    W ⊓ centralizer (W : Set A) = ⁅W, W⁆ :=
  le_antisymm (le_trans (le_inf inf_le_left h.X_cent_Z) h.CX_le_derived)
    (derived_le_Z h.class_two)

private lemma Z_eq_fix_of_part1 (h : Part1 p W X z) :
    W ⊓ centralizer (W : Set A) = W ⊓ centralizer (X : Set A) :=
  le_antisymm (le_inf inf_le_left h.X_cent_Z)
    (h.CX_le_derived.trans (derived_le_Z h.class_two))

private lemma Cz_le_Z (h : Part1 p W X z) :
    W ⊓ centralizer ({z} : Set A) ≤ W ⊓ centralizer (W : Set A) := by
  intro c hc
  obtain ⟨hcW, hcz⟩ := Subgroup.mem_inf.mp hc
  have hcz' : c * z = z * c := (Subgroup.mem_centralizer_iff.mp hcz z (Set.mem_singleton z)).symm
  have hcX := h.setup.Cz c hcW hcz'
  have hdisj : W ⊓ X = ⊥ := by
    have : Fact p.Prime := ⟨h.setup.prime⟩
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact disjoint_iff.mp (IsPGroup.disjoint_of_ne 2 p (Ne.symm h.setup.odd) W X h.setup.W2
      h.setup.Xp)
  have hcent : c ∈ centralizer (X : Set A) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hxn := h.setup.XW hx
    have d1 : c * x * c⁻¹ * x⁻¹ ∈ X :=
      X.mul_mem ((mem_set_normalizer_iff.mp hcX x).mp hx) (X.inv_mem hx)
    have d2 : c * x * c⁻¹ * x⁻¹ ∈ W := by
      have h1 : x * c⁻¹ * x⁻¹ ∈ W := (mem_set_normalizer_iff.mp hxn c⁻¹).mp (W.inv_mem hcW)
      have e : c * x * c⁻¹ * x⁻¹ = c * (x * c⁻¹ * x⁻¹) := by group
      rw [e]; exact W.mul_mem hcW h1
    have d3 : c * x * c⁻¹ * x⁻¹ = 1 := by
      have h2 : c * x * c⁻¹ * x⁻¹ ∈ W ⊓ X := Subgroup.mem_inf.mpr ⟨d2, d1⟩
      rw [hdisj] at h2
      exact Subgroup.mem_bot.mp h2
    have d4 : ⁅c, x⁆ = 1 := by rw [commutatorElement_def]; exact d3
    exact (commutatorElement_eq_one_iff_mul_comm.mp d4).symm
  rw [Z_eq_fix_of_part1 h]
  exact Subgroup.mem_inf.mpr ⟨hcW, hcent⟩

private lemma comm_z_mem_D (h : Part1 p W X z)
    (hsq : ∀ w ∈ W, w * w ∈ W ⊓ centralizer (W : Set A))
    {w : A} (hw : w ∈ W) : ⁅w, z⁆ ∈ W ∧ ⁅⁅w, z⁆, z⁆ ∈ W ⊓ centralizer (W : Set A) := by
  have hz2 := h.setup.z2
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have hzW : z ∈ normalizer (W : Set A) := h.setup.zW
  have he : ⁅w, z⁆ ∈ W := by
    have h1 : z * w⁻¹ * z⁻¹ ∈ W := (mem_set_normalizer_iff.mp hzW w⁻¹).mp (W.inv_mem hw)
    have e : ⁅w, z⁆ = w * (z * w⁻¹ * z⁻¹) := by simp only [commutatorElement_def]; group
    rw [e]; exact W.mul_mem hw h1
  refine ⟨he, ?_⟩
  have e1 : z * ⁅w, z⁆⁻¹ * z⁻¹ = ⁅w, z⁆ := by
    have e : z * ⁅w, z⁆⁻¹ * z⁻¹ = (z * z) * w * z⁻¹ * w⁻¹ * z⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e, hz2, one_mul, commutatorElement_def, hzi]
  have e2 : ⁅⁅w, z⁆, z⁆ = ⁅w, z⁆ * ⁅w, z⁆ := by
    calc ⁅⁅w, z⁆, z⁆ = ⁅w, z⁆ * (z * ⁅w, z⁆⁻¹ * z⁻¹) := by
          rw [commutatorElement_def ⁅w, z⁆ z]; group
      _ = ⁅w, z⁆ * ⁅w, z⁆ := by rw [e1]
  rw [e2]
  exact hsq _ he

end Part1Facts

section CardLe

variable {A : Type} [Group A] [Finite A] {p : ℕ} {W X : Subgroup A} {z : A}

private theorem card_le_of_part1 (h : Part1 p W X z) :
    Nat.card ↥W ≤ Nat.card ↥(W ⊓ centralizer (W : Set A)) *
      Nat.card ↥(W ⊓ centralizer (W : Set A) ⊓ centralizer ({z} : Set A)) ^ 2 := by
  have hsq := sq_central_of_part1 h
  obtain ⟨D, hD⟩ := exists_Dsub W z
  have h1 : Nat.card ↥W ≤ Nat.card ↥(W ⊓ centralizer ({z} : Set A)) * Nat.card ↥D :=
    card_le_orbit W D z (fun w hw => (hD _).mpr ⟨(comm_z_mem_D h hsq hw).1,
      (comm_z_mem_D h hsq hw).2⟩)
  have h2 : Nat.card ↥D ≤ Nat.card ↥(D ⊓ centralizer ({z} : Set A)) *
      Nat.card ↥(W ⊓ centralizer (W : Set A)) :=
    card_le_orbit D _ z (fun u hu => ((hD u).mp hu).2)
  have hDW : D ≤ W := fun u hu => ((hD u).mp hu).1
  have h3 : Nat.card ↥(D ⊓ centralizer ({z} : Set A)) ≤
      Nat.card ↥(W ⊓ centralizer ({z} : Set A)) :=
    Subgroup.card_le_of_le (inf_le_inf_right _ hDW)
  have h4 : W ⊓ centralizer (W : Set A) ⊓ centralizer ({z} : Set A) =
      W ⊓ centralizer ({z} : Set A) :=
    le_antisymm (inf_le_inf_right _ inf_le_left) (le_inf (Cz_le_Z h) inf_le_right)
  rw [h4]
  calc Nat.card ↥W ≤ Nat.card ↥(W ⊓ centralizer ({z} : Set A)) * Nat.card ↥D := h1
    _ ≤ Nat.card ↥(W ⊓ centralizer ({z} : Set A)) *
        (Nat.card ↥(W ⊓ centralizer ({z} : Set A)) * Nat.card ↥(W ⊓ centralizer (W : Set A))) :=
      Nat.mul_le_mul_left _ (h2.trans (Nat.mul_le_mul_right _ h3))
    _ = Nat.card ↥(W ⊓ centralizer (W : Set A)) *
        Nat.card ↥(W ⊓ centralizer ({z} : Set A)) ^ 2 := by ring

end CardLe

section Eight

variable {A : Type} [Group A]

private lemma closure_comm {S : Set A} (hS : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) :
    ∀ x ∈ closure S, ∀ y ∈ closure S, x * y = y * x := by
  have h1 : closure S ≤ centralizer S := by
    rw [Subgroup.closure_le]
    intro x hx
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro y hy
    exact hS y hy x hx
  intro x hx y hy
  have h2 : closure S ≤ centralizer ({x} : Set A) := by
    rw [Subgroup.closure_le]
    intro s hs
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro t ht
    rw [Set.mem_singleton_iff] at ht
    subst ht
    exact (Subgroup.mem_centralizer_iff.mp (h1 hx) s hs).symm
  exact Subgroup.mem_centralizer_iff.mp (h2 hy) x (Set.mem_singleton x)

private lemma derived_le_of_gen {W : Subgroup A}
    (hW2 : ∀ a ∈ W, ∀ b ∈ W, ∀ c ∈ W, ⁅⁅a, b⁆, c⁆ = 1)
    {S : Set A} (hS : closure S = W) (E : Subgroup A)
    (hE : ∀ g ∈ S, ∀ h ∈ S, ⁅g, h⁆ ∈ E) : ⁅W, W⁆ ≤ E := by
  have key : ∀ x y : A, x ∈ closure S → y ∈ closure S → ⁅x, y⁆ ∈ E := by
    intro x y hx hy
    induction hx, hy using Subgroup.closure_induction₂ with
    | mem x y hx hy => exact hE x hx y hy
    | one_left x hx => simp [E.one_mem]
    | one_right x hx => simp [E.one_mem]
    | mul_left x y z hx hy hz hxz hyz =>
      rw [comm_mul_left hW2 (hS ▸ hx) (hS ▸ hy) (hS ▸ hz)]
      exact E.mul_mem hyz hxz
    | mul_right y z x hy hz hx hxy hxz =>
      rw [comm_mul_right hW2 (hS ▸ hx) (hS ▸ hy) (hS ▸ hz)]
      exact E.mul_mem hxy hxz
    | inv_left x y hx hy h =>
      rw [comm_inv_left hW2 (hS ▸ hx) (hS ▸ hy)]
      exact E.inv_mem h
    | inv_right x y hx hy h =>
      rw [comm_inv_right hW2 (hS ▸ hx) (hS ▸ hy)]
      exact E.inv_mem h
  rw [Subgroup.commutator_def, Subgroup.closure_le]
  rintro _ ⟨x, hx, y, hy, rfl⟩
  exact key x y (hS ▸ hx) (hS ▸ hy)

private lemma two_mul_card_le {H K : Subgroup A} [Finite A] (hHK : H ≤ K) (hne : H ≠ K) :
    2 * Nat.card H ≤ Nat.card K := by
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hHK
  have hpos : 0 < Nat.card K := Nat.card_pos
  have hHpos : 0 < Nat.card H := Nat.card_pos
  have hk1 : k ≠ 1 := by
    rintro rfl
    exact hne (Subgroup.eq_of_le_of_card_ge hHK (by rw [hk, mul_one]))
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hk
    omega
  have hk2 : 2 ≤ k := by omega
  calc 2 * Nat.card H ≤ k * Nat.card H := Nat.mul_le_mul_right _ hk2
    _ = Nat.card K := by rw [hk]; ring

private theorem card_eq_eight [Finite A] {W Z : Subgroup A}
    (hW2 : ∀ a ∈ W, ∀ b ∈ W, ∀ c ∈ W, ⁅⁅a, b⁆, c⁆ = 1)
    (hZW : Z ≤ W) (hZc : ∀ u ∈ Z, ∀ w ∈ W, w * u = u * w)
    (hder : ⁅W, W⁆ = Z) (hexp : ∀ g ∈ Z, g * g = 1)
    (hnonab : ¬ ∀ a ∈ W, ∀ b ∈ W, a * b = b * a)
    (hcard : Nat.card W ≤ 4 * Nat.card Z) : Nat.card W = 8 := by
  obtain ⟨a, haW, haZ⟩ : ∃ a ∈ W, a ∉ Z := by
    by_contra hcon
    push Not at hcon
    exact hnonab fun x hx y hy => (hZc x (hcon x hx) y hy).symm
  have hU1W : closure (insert a (Z : Set A)) ≤ W := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with hxa | hx
    · rw [hxa]; exact haW
    · exact hZW hx
  have hZU1 : Z ≤ closure (insert a (Z : Set A)) := fun u hu =>
    Subgroup.subset_closure (Set.mem_insert_of_mem _ hu)
  have haU1 : a ∈ closure (insert a (Z : Set A)) := Subgroup.subset_closure (Set.mem_insert _ _)
  have hU1ab : ∀ x ∈ closure (insert a (Z : Set A)), ∀ y ∈ closure (insert a (Z : Set A)),
      x * y = y * x := by
    apply closure_comm
    intro x hx y hy
    rcases hx with hxa | hx <;> rcases hy with hya | hy
    · rw [hxa, hya]
    · rw [hxa]; exact hZc y hy a haW
    · rw [hya]; exact (hZc x hx a haW).symm
    · exact (hZc x hx y (hZW hy)).symm
  obtain ⟨b, hbW, hbU1⟩ : ∃ b ∈ W, b ∉ closure (insert a (Z : Set A)) := by
    by_contra hcon
    push Not at hcon
    exact hnonab fun x hx y hy => hU1ab x (hcon x hx) y (hcon y hy)
  have hU2W : closure (insert a (insert b (Z : Set A))) ≤ W := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with hxa | hxb | hx
    · rw [hxa]; exact haW
    · rw [hxb]; exact hbW
    · exact hZW hx
  have hU12 : closure (insert a (Z : Set A)) ≤ closure (insert a (insert b (Z : Set A))) :=
    Subgroup.closure_mono (Set.insert_subset_insert (Set.subset_insert _ _))
  have hbU2 : b ∈ closure (insert a (insert b (Z : Set A))) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have h1ne : Z ≠ closure (insert a (Z : Set A)) := fun h => haZ (h ▸ haU1)
  have h2ne : closure (insert a (Z : Set A)) ≠ closure (insert a (insert b (Z : Set A))) :=
    fun h => hbU1 (h ▸ hbU2)
  have c1 := two_mul_card_le hZU1 h1ne
  have c2 := two_mul_card_le hU12 h2ne
  have c3 := Subgroup.card_le_of_le hU2W
  have hS : closure (insert a (insert b (Z : Set A))) = W :=
    Subgroup.eq_of_le_of_card_ge hU2W (by omega)
  have hc : ⁅a, b⁆ ∈ Z := hder ▸ Subgroup.commutator_mem_commutator haW hbW
  have hone : ∀ g ∈ W, ∀ g' ∈ W, (g ∈ Z ∨ g' ∈ Z) → ⁅g, g'⁆ = 1 := by
    intro g hg g' hg' hor
    rw [commutatorElement_eq_one_iff_mul_comm]
    rcases hor with h | h
    · exact (hZc g h g' hg').symm
    · exact hZc g' h g hg
  have hZle : Z ≤ zpowers ⁅a, b⁆ := by
    rw [← hder]
    apply derived_le_of_gen hW2 hS
    intro g hg g' hg'
    have hSW : ∀ x ∈ insert a (insert b (Z : Set A)), x ∈ W := fun x hx =>
      hU2W (Subgroup.subset_closure hx)
    have hgW := hSW g hg
    have hg'W := hSW g' hg'
    rcases hg with hga | hgb | hgZ <;> rcases hg' with hga' | hgb' | hgZ'
    · rw [hga, hga', commutatorElement_self]; exact one_mem _
    · rw [hga, hgb']; exact Subgroup.mem_zpowers _
    · rw [hone g hgW g' hg'W (Or.inr hgZ')]; exact one_mem _
    · rw [hgb, hga', ← commutatorElement_inv a b]
      exact (zpowers ⁅a, b⁆).inv_mem (Subgroup.mem_zpowers _)
    · rw [hgb, hgb', commutatorElement_self]; exact one_mem _
    · rw [hone g hgW g' hg'W (Or.inr hgZ')]; exact one_mem _
    · rw [hone g hgW g' hg'W (Or.inl hgZ)]; exact one_mem _
    · rw [hone g hgW g' hg'W (Or.inl hgZ)]; exact one_mem _
    · rw [hone g hgW g' hg'W (Or.inl hgZ)]; exact one_mem _
  have hcZ2 := hexp _ hc
  have hord : orderOf ⁅a, b⁆ ≤ 2 :=
    Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hcZ2))
  have hZ2 : Nat.card Z ≤ 2 := by
    calc Nat.card Z ≤ Nat.card (zpowers ⁅a, b⁆) := Subgroup.card_le_of_le hZle
      _ = orderOf ⁅a, b⁆ := Nat.card_zpowers _
      _ ≤ 2 := hord
  have hZ1 : Nat.card Z ≠ 1 := by
    intro h1
    have hbot : Z = ⊥ := Subgroup.card_eq_one.mp h1
    apply hnonab
    intro x hx y hy
    have hxy : ⁅x, y⁆ ∈ Z := hder ▸ Subgroup.commutator_mem_commutator hx hy
    rw [hbot, Subgroup.mem_bot] at hxy
    exact commutatorElement_eq_one_iff_mul_comm.mp hxy
  have hZpos : 0 < Nat.card Z := Nat.card_pos
  omega

end Eight

section Main

variable {A : Type} [Group A] [Finite A] {p : ℕ} {W X : Subgroup A} {z : A}

private theorem card8_of_part1 (h : Part1 p W X z)
    (h2 : Nat.card ↥(W ⊓ centralizer (W : Set A) ⊓ centralizer ({z} : Set A)) = 2) :
    Nat.card ↥W = 8 := by
  have hle := card_le_of_part1 h
  rw [h2] at hle
  have hder := Z_eq_derived_of_part1 h
  refine card_eq_eight (Z := W ⊓ centralizer (W : Set A)) h.class_two inf_le_left
    (fun u hu w hw => Z_comm hu hw) hder.symm
    (fun g hg => derived_sq_eq_one h.class_two (sq_central_of_part1 h) g (by rw [← hder]; exact hg))
    h.nonab ?_
  omega

theorem core412_of_part1 {p : ℕ} {W X : Subgroup A} {z : A} (h : Part1 p W X z) :
    Core412 W X z where
  nonab := h.nonab
  Z_eq_derived := Z_eq_derived_of_part1 h
  Z_eq_fix := Z_eq_fix_of_part1 h
  X_cent_Z := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact (Subgroup.mem_centralizer_iff.mp (h.X_cent_Z hu) x hx).symm
  sq_central := sq_central_of_part1 h
  Z_exp2 := fun g hg => derived_sq_eq_one h.class_two (sq_central_of_part1 h) g
    (by rw [← Z_eq_derived_of_part1 h]; exact hg)
  card_le := card_le_of_part1 h
  card8 := card8_of_part1 h

end Main

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
