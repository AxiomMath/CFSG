module

public import CFSG.GH74.GLS.Stage2.Signalizer.L53Clifford

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.L53

open Subgroup
open scoped commutatorElement

variable {M : Type*} [Group M]

@[expose] def Target (A S : Subgroup M) : Prop :=
  ∃ g ∈ S, ∃ X Y : Subgroup M, IsChiefPair X Y ∧ X ≤ A ∧ (∀ x ∈ X, ⁅⁅x, g⁆, g⁆ ∈ Y) ∧
    ∃ x ∈ X, ⁅x, g⁆ ∉ Y

theorem target_of_quad [Finite M] {p : ℕ} [Fact p.Prime] {T A S : Subgroup M} (hS : Setup p T A)
    {g : M} (hgS : g ∈ S) (hgT : g ∉ T)
    (hq : ∀ X Y : Subgroup M, IsChiefPair X Y → X ≤ A → ∀ x ∈ X, ⁅⁅x, g⁆, g⁆ ∈ Y) :
    Target A S := by
  have h : g ∉ stabAll A := fun h => hgT (hS.stabAll_le h)
  rw [mem_stabAll] at h
  push Not at h
  obtain ⟨X, Y, hc, hXA, x, hx, hxY⟩ := h
  exact ⟨g, hgS, X, Y, hc, hXA, hq X Y hc hXA, x, hx, hxY⟩

theorem comm_Z_eq_bot (A : Subgroup M) : ⁅A ⊓ centralizer (A : Set M), A ⊓ centralizer (A : Set M)⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro z hz
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  exact (Subgroup.mem_centralizer_iff.mp hw.2 z hz.1).symm

theorem mul_comm_of_mem_centralizer {B : Subgroup M} {w g : M} (hw : w ∈ centralizer (B : Set M))
    (hg : g ∈ B) : ⁅w, g⁆ = 1 := by
  rw [commutatorElement_eq_one_iff_mul_comm]
  exact (Subgroup.mem_centralizer_iff.mp hw g hg).symm

theorem quad_of_up {A B : Subgroup M} {g : M} (hg : g ∈ B)
    (h : ⁅A, B⁆ ≤ B ⊓ centralizer (B : Set M)) : ∀ x ∈ A, ⁅⁅x, g⁆, g⁆ = 1 := by
  intro x hx
  have h1 : ⁅x, g⁆ ∈ B ⊓ centralizer (B : Set M) := h (Subgroup.commutator_mem_commutator hx hg)
  exact mul_comm_of_mem_centralizer h1.2 hg

theorem quad_of_zB {A B : Subgroup M} {g : M} (hAB : A ≤ normalizer (B : Set M))
    (hg : g ∈ B ⊓ centralizer (B : Set M)) : ∀ x ∈ A, ⁅⁅x, g⁆, g⁆ = 1 := by
  intro x hx
  have h1 : ⁅x, g⁆ ∈ B := by
    have e : ⁅x, g⁆ = (x * g * x⁻¹) * g⁻¹ := by simp only [commutatorElement_def]
    rw [e]
    exact B.mul_mem ((Subgroup.mem_normalizer_iff.mp (hAB hx) g).mp hg.1) (B.inv_mem hg.1)
  have : ⁅⁅x, g⁆, g⁆ = 1 := by
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_centralizer_iff.mp hg.2 _ h1)
  exact this

theorem quad_mul_normal {Y : Subgroup M} (hY : Y.Normal) {a g y : M} (hy : y ∈ Y)
    (ha : ⁅⁅a, g⁆, g⁆ ∈ Y) : ⁅⁅a * y, g⁆, g⁆ ∈ Y := by
  have e : ⁅a * y, g⁆ = (a * ⁅y, g⁆ * a⁻¹) * ⁅a, g⁆ := by
    simp only [commutatorElement_def]; group
  have h1 : a * ⁅y, g⁆ * a⁻¹ ∈ Y := nconj hY (by
    have e2 : ⁅y, g⁆ = y * (g * y⁻¹ * g⁻¹) := by simp only [commutatorElement_def]; group
    rw [e2]; exact Y.mul_mem hy (nconj hY (Y.inv_mem hy) g)) a
  show ⁅a * y, g⁆ ∈ phiSub Y hY g
  rw [e]
  exact (phiSub Y hY g).mul_mem (le_phiSub hY g h1) ha

theorem lowfail_branch [Finite M] {p : ℕ} [Fact p.Prime] {T A S A₂ : Subgroup M}
    (hS : Setup p T A) (hA₂S : A₂ ≤ S) (hAA₂ : A ≤ normalizer (A₂ : Set M))
    (h1 : ⁅A, ⁅A₂, A₂⁆⁆ = ⊥)
    (h2 : ⁅⁅A ⊓ centralizer (A : Set M), A₂⁆, A₂⁆ = ⊥)
    (h3 : ¬ ⁅A, A₂⁆ ≤ A ⊓ centralizer (A : Set M)) : Target A S := by
  have hAn := hS.normalA
  have hZn := hS.normal_Z
  rw [Subgroup.commutator_le] at h3
  push Not at h3
  obtain ⟨a, ha, g, hg, hag⟩ := h3
  have hgS : g ∈ S := hA₂S hg
  have hgT : g ∉ T := by
    intro hgT
    apply hag
    have : ⁅g, a⁆ ∈ A ⊓ centralizer (A : Set M) :=
      hS.commTA (Subgroup.commutator_mem_commutator hgT ha)
    have e : ⁅a, g⁆ = ⁅g, a⁆⁻¹ := (commutatorElement_inv g a).symm
    rw [e]
    exact (A ⊓ centralizer (A : Set M)).inv_mem this
  have hA1 : ∀ x ∈ A, ⁅⁅x, g⁆, g⁆ ∈ A ⊓ centralizer (A : Set M) := by
    intro x hx
    have hxg : ⁅x, g⁆ ∈ A₂ := by
      have e : ⁅x, g⁆ = (x * g * x⁻¹) * g⁻¹ := by simp only [commutatorElement_def]
      rw [e]
      exact A₂.mul_mem ((Subgroup.mem_normalizer_iff.mp (hAA₂ hx) g).mp hg) (A₂.inv_mem hg)
    have hxgA : ⁅x, g⁆ ∈ A := comm_mem_normal hAn hx g
    refine ⟨comm_mem_normal hAn hxgA g, ?_⟩
    have hc : ⁅A₂, A₂⁆ ≤ centralizer (A : Set M) := by
      have : ⁅⁅A₂, A₂⁆, A⁆ = ⊥ := by rw [Subgroup.commutator_comm]; exact h1
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp this
    exact hc (Subgroup.commutator_mem_commutator hxg hg)
  have hA2 : ∀ z ∈ A ⊓ centralizer (A : Set M), ⁅⁅z, g⁆, g⁆ = 1 := by
    intro z hz
    have : ⁅⁅z, g⁆, g⁆ ∈ ⁅⁅A ⊓ centralizer (A : Set M), A₂⁆, A₂⁆ :=
      Subgroup.commutator_mem_commutator (Subgroup.commutator_mem_commutator hz hg) hg
    rw [h2] at this
    exact Subgroup.mem_bot.mp this
  refine target_of_quad hS hgS hgT fun X Y hc hXA x hx => ?_
  have hXn := hc.1
  have hYn := hc.2.1
  obtain ⟨W, hW⟩ : ∃ W : Subgroup M, W = (X ⊓ (A ⊓ centralizer (A : Set M))) ⊔ Y := ⟨_, rfl⟩
  have hWn : W.Normal := by
    rw [hW]
    have : (X ⊓ (A ⊓ centralizer (A : Set M))).Normal := inferInstance
    infer_instance
  have hWX : W ≤ X := by rw [hW]; exact sup_le inf_le_left hc.2.2.1.le
  have hYW : Y ≤ W := by rw [hW]; exact le_sup_right
  rcases hc.2.2.2 W hWn hYW hWX with hWY | hWX'
  · have h4 : ⁅⁅x, g⁆, g⁆ ∈ X ⊓ (A ⊓ centralizer (A : Set M)) :=
      ⟨comm_mem_normal hXn (comm_mem_normal hXn hx g) g, hA1 x (hXA hx)⟩
    have : ⁅⁅x, g⁆, g⁆ ∈ W := by rw [hW]; exact Subgroup.mem_sup_left h4
    rw [hWY] at this
    exact this
  · have hxW : x ∈ W := by rw [hWX']; exact hx
    rw [hW, Subgroup.mem_sup_of_normal_right] at hxW
    obtain ⟨z, hz, y, hy, rfl⟩ := hxW
    refine quad_mul_normal hYn hy ?_
    rw [hA2 z hz.2]
    exact Y.one_mem

@[expose] def Abar (A W : Subgroup M) (hW : W ≤ centralizer (A : Set M)) : Subgroup M where
  carrier := {a | a ∈ A ∧ ∀ x ∈ A, ⁅a, x⁆ ∈ W}
  mul_mem' := by
    rintro a b ⟨haA, ha⟩ ⟨hbA, hb⟩
    refine ⟨A.mul_mem haA hbA, fun x hx => ?_⟩
    have e : ⁅a * b, x⁆ = (a * ⁅b, x⁆ * a⁻¹) * ⁅a, x⁆ := by
      simp only [commutatorElement_def]; group
    have hc : a * ⁅b, x⁆ * a⁻¹ = ⁅b, x⁆ := by
      have := Subgroup.mem_centralizer_iff.mp (hW (hb x hx)) a haA
      calc a * ⁅b, x⁆ * a⁻¹ = ⁅b, x⁆ * a * a⁻¹ := by rw [this]
        _ = ⁅b, x⁆ := by group
    rw [e, hc]
    exact W.mul_mem (hb x hx) (ha x hx)
  one_mem' := ⟨A.one_mem, fun x _ => by simp⟩
  inv_mem' := by
    rintro a ⟨haA, ha⟩
    refine ⟨A.inv_mem haA, fun x hx => ?_⟩
    have e : ⁅a⁻¹, x⁆ = a⁻¹ * ⁅a, x⁆⁻¹ * a := by
      simp only [commutatorElement_def]; group
    have hc : a⁻¹ * ⁅a, x⁆⁻¹ * a = ⁅a, x⁆⁻¹ := by
      have := Subgroup.mem_centralizer_iff.mp (hW (W.inv_mem (ha x hx))) a⁻¹ (A.inv_mem haA)
      calc a⁻¹ * ⁅a, x⁆⁻¹ * a = ⁅a, x⁆⁻¹ * a⁻¹ * a := by rw [this]
        _ = ⁅a, x⁆⁻¹ := by group
    rw [e, hc]
    exact W.inv_mem (ha x hx)

theorem Abar_le {A W : Subgroup M} (hW : W ≤ centralizer (A : Set M)) : Abar A W hW ≤ A :=
  fun _ h => h.1

theorem comm_Abar_le {A W : Subgroup M} (hW : W ≤ centralizer (A : Set M)) :
    ⁅Abar A W hW, Abar A W hW⁆ ≤ W := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  exact ha.2 b hb.1

theorem Abar_normalized {A W : Subgroup M} (hAn : A.Normal) (hW : W ≤ centralizer (A : Set M))
    {r : M} (hr : ∀ w ∈ W, r * w * r⁻¹ = w) : r ∈ normalizer (Abar A W hW : Set M) := by
  have fwd : ∀ r : M, (∀ w ∈ W, r * w * r⁻¹ = w) → ∀ a ∈ Abar A W hW,
      r * a * r⁻¹ ∈ Abar A W hW := by
    intro r hr a ha
    refine ⟨nconj hAn ha.1 r, fun x hx => ?_⟩
    have e : ⁅r * a * r⁻¹, x⁆ = r * ⁅a, r⁻¹ * x * r⁆ * r⁻¹ := by
      simp only [commutatorElement_def]; group
    have hw := ha.2 _ (nconj_inv hAn hx r)
    rw [e, hr _ hw]
    exact hw
  have hr' : ∀ w ∈ W, r⁻¹ * w * r⁻¹⁻¹ = w := by
    intro w hw
    rw [inv_inv]
    have h := hr w hw
    calc r⁻¹ * w * r = r⁻¹ * (r * w * r⁻¹) * r := by rw [h]
      _ = w := by group
  rw [Subgroup.mem_normalizer_iff]
  intro a
  constructor
  · intro ha; exact fwd r hr a ha
  · intro ha
    have := fwd r⁻¹ hr' _ ha
    have e : r⁻¹ * (r * a * r⁻¹) * r⁻¹⁻¹ = a := by group
    rwa [e] at this

theorem conj_eq_of_comm {x c : M} (h : x * c = c * x) : c * x * c⁻¹ = x :=
  mul_inv_eq_iff_eq_mul.mpr h.symm

theorem conj_mem_center {B : Subgroup M} {x z : M} (hx : x ∈ normalizer (B : Set M))
    (hz : z ∈ B ⊓ centralizer (B : Set M)) : x * z * x⁻¹ ∈ B ⊓ centralizer (B : Set M) := by
  refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp hx z).mp hz.1, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  have hb' : x⁻¹ * b * x ∈ B := by
    refine (Subgroup.mem_normalizer_iff.mp hx _).mpr ?_
    have e : x * (x⁻¹ * b * x) * x⁻¹ = b := by group
    rw [e]; exact hb
  have h1 := Subgroup.mem_centralizer_iff.mp hz.2 _ hb'
  have e1 : b * (x * z * x⁻¹) = x * ((x⁻¹ * b * x) * z) * x⁻¹ := by group
  have e2 : x * z * x⁻¹ * b = x * (z * (x⁻¹ * b * x)) * x⁻¹ := by group
  rw [e1, e2, h1]

theorem mem_normalizer_sup_normal {R U Y : Subgroup M} (hY : Y.Normal)
    (hU : R ≤ normalizer (U : Set M)) : R ≤ normalizer ((U ⊔ Y : Subgroup M) : Set M) := by
  have fwd : ∀ r ∈ R, ∀ h ∈ U ⊔ Y, r * h * r⁻¹ ∈ U ⊔ Y := by
    intro r hr h hh
    rw [Subgroup.mem_sup_of_normal_right] at hh
    obtain ⟨a, ha, y, hy, rfl⟩ := hh
    have e : r * (a * y) * r⁻¹ = (r * a * r⁻¹) * (r * y * r⁻¹) := by group
    rw [e]
    exact (U ⊔ Y).mul_mem (Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp (hU hr) a).mp ha))
      (Subgroup.mem_sup_right (nconj hY hy r))
  intro r hr
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fwd r hr h, fun hh => ?_⟩
  have := fwd r⁻¹ (R.inv_mem hr) _ hh
  have e : r⁻¹ * (r * h * r⁻¹) * r⁻¹⁻¹ = h := by group
  rwa [e] at this

theorem even_branch [Finite M] {p : ℕ} [Fact p.Prime] {T A S B : Subgroup M}
    (hS : Setup p T A) {g : M} (hgB : g ∈ B) (hgT : g ∉ T) (hgS : g ∈ S)
    (hAB : A ≤ normalizer (B : Set M))
    (hBcl : ⁅B, B⁆ ≤ B ⊓ centralizer (B : Set M))
    (hBZ : B ⊓ centralizer (B : Set M) ≤ T)
    (hK : ∀ A' : Subgroup M, A' ≤ A → B ≤ normalizer (A' : Set M) → ⁅B, ⁅A', A'⁆⁆ = ⊥ →
      ⁅⁅B ⊓ centralizer (B : Set M), A'⁆, A'⁆ = ⊥ → ⁅B, A'⁆ ≤ B ⊓ centralizer (B : Set M)) :
    Target A S := by
  have hAn := hS.normalA
  have hTn := hS.normalT
  have hZn : (A ⊓ centralizer (A : Set M)).Normal := hS.normal_Z
  have hZA : A ⊓ centralizer (A : Set M) ≤ A := inf_le_left
  have hZT : A ⊓ centralizer (A : Set M) ≤ T := hZA.trans hS.leT
  have hZc : A ⊓ centralizer (A : Set M) ≤ centralizer (A : Set M) := inf_le_right
  have hBZA : ⁅B, A ⊓ centralizer (A : Set M)⁆ ≤ B ⊓ centralizer (B : Set M) := by
    refine hK _ hZA ((le_top).trans (normalizer_top_of_normal hZn)) ?_ ?_
    · rw [comm_Z_eq_bot A]; exact Subgroup.commutator_bot_right B
    · have h1 : ⁅B ⊓ centralizer (B : Set M), A ⊓ centralizer (A : Set M)⁆ ≤
          A ⊓ centralizer (A : Set M) := Subgroup.commutator_le_right _ _
      exact le_bot_iff.mp ((Subgroup.commutator_mono_left h1).trans (comm_Z_eq_bot A).le)
  have hq0 : ∀ z ∈ A ⊓ centralizer (A : Set M), ⁅⁅z, g⁆, g⁆ = 1 := by
    intro z hz
    have : ⁅z, g⁆ ∈ B ⊓ centralizer (B : Set M) := by
      rw [← commutatorElement_inv]
      exact (B ⊓ centralizer (B : Set M)).inv_mem
        (hBZA (Subgroup.commutator_mem_commutator hgB hz))
    exact mul_comm_of_mem_centralizer this.2 hgB
  by_cases hα : ∃ X Y : Subgroup M, IsChiefPair X Y ∧ X ≤ A ⊓ centralizer (A : Set M) ∧
      ∃ x ∈ X, ⁅x, g⁆ ∉ Y
  · obtain ⟨X, Y, hc, hXZ, x, hx, hxY⟩ := hα
    refine ⟨g, hgS, X, Y, hc, hXZ.trans hZA, fun x hx => ?_, x, hx, hxY⟩
    rw [hq0 x (hXZ hx)]; exact Y.one_mem
  push Not at hα
  have hgZ : g ∈ stabAll (A ⊓ centralizer (A : Set M)) := hα
  have hWc : (A ⊓ centralizer (A : Set M)) ⊓ (B ⊓ centralizer (B : Set M)) ≤
      centralizer (A : Set M) := inf_le_left.trans hZc
  have hWZ : (A ⊓ centralizer (A : Set M)) ⊓ (B ⊓ centralizer (B : Set M)) ≤
      A ⊓ centralizer (A : Set M) := inf_le_left
  have hWB : (A ⊓ centralizer (A : Set M)) ⊓ (B ⊓ centralizer (B : Set M)) ≤
      B ⊓ centralizer (B : Set M) := inf_le_right
  have hCW : ∀ c ∈ centralizer ((A ⊓ centralizer (A : Set M) : Subgroup M) : Set M),
      ∀ w ∈ (A ⊓ centralizer (A : Set M)) ⊓ (B ⊓ centralizer (B : Set M)), c * w * c⁻¹ = w := by
    intro c hc w hw
    exact conj_eq_of_comm (Subgroup.mem_centralizer_iff.mp hc w (hWZ hw))
  have hBW : ∀ b ∈ B, ∀ w ∈ (A ⊓ centralizer (A : Set M)) ⊓ (B ⊓ centralizer (B : Set M)),
      b * w * b⁻¹ = w := by
    intro b hb w hw
    exact conj_eq_of_comm (Subgroup.mem_centralizer_iff.mp (hWB hw).2 b hb).symm
  have hBnorm : B ≤ normalizer (Abar A _ hWc : Set M) := fun b hb =>
    Abar_normalized hAn hWc (hBW b hb)
  have hCnorm : centralizer ((A ⊓ centralizer (A : Set M) : Subgroup M) : Set M) ≤
      normalizer (Abar A _ hWc : Set M) := fun c hc => Abar_normalized hAn hWc (hCW c hc)
  have hLnorm : centralizer ((A ⊓ centralizer (A : Set M) : Subgroup M) : Set M) ⊔ zpowers g ≤
      normalizer (Abar A _ hWc : Set M) :=
    sup_le hCnorm ((Subgroup.zpowers_le).mpr (hBnorm hgB))
  have hBAb : ⁅B, Abar A _ hWc⁆ ≤ B ⊓ centralizer (B : Set M) := by
    refine hK _ (Abar_le hWc) hBnorm ?_ ?_
    · rw [Subgroup.commutator_comm]
      refine Subgroup.commutator_eq_bot_iff_le_centralizer.mpr ?_
      exact (comm_Abar_le hWc).trans (hWB.trans (inf_le_right))
    · have h1 : ⁅B ⊓ centralizer (B : Set M), Abar A _ hWc⁆ ≤
          A ⊓ centralizer (A : Set M) :=
        (Subgroup.commutator_mono hBZ (Abar_le hWc)).trans hS.commTA
      have h2 : ⁅A ⊓ centralizer (A : Set M), Abar A _ hWc⁆ = ⊥ := by
        refine Subgroup.commutator_eq_bot_iff_le_centralizer.mpr ?_
        exact hZc.trans (Subgroup.centralizer_le (Abar_le hWc))
      exact le_bot_iff.mp ((Subgroup.commutator_mono_left h1).trans h2.le)
  have hq1 : ∀ b ∈ Abar A _ hWc, ⁅⁅b, g⁆, g⁆ = 1 := by
    intro b hb
    have : ⁅b, g⁆ ∈ B ⊓ centralizer (B : Set M) := by
      rw [← commutatorElement_inv]
      exact (B ⊓ centralizer (B : Set M)).inv_mem
        (hBAb (Subgroup.commutator_mem_commutator hgB hb))
    exact mul_comm_of_mem_centralizer this.2 hgB
  have hq2 : ∀ a ∈ A, ⁅⁅a, g⁆, g⁆ ∈ Abar A _ hWc := by
    intro a ha
    have hu : ⁅a, g⁆ ∈ B := by
      have e : ⁅a, g⁆ = (a * g * a⁻¹) * g⁻¹ := by simp only [commutatorElement_def]
      rw [e]
      exact B.mul_mem ((Subgroup.mem_normalizer_iff.mp (hAB ha) g).mp hgB) (B.inv_mem hgB)
    have hd : ⁅⁅a, g⁆, g⁆ ∈ B ⊓ centralizer (B : Set M) :=
      hBcl (Subgroup.commutator_mem_commutator hu hgB)
    have hdA : ⁅⁅a, g⁆, g⁆ ∈ A := comm_mem_normal hAn (comm_mem_normal hAn ha g) g
    refine ⟨hdA, fun x hx => Subgroup.mem_inf.mpr ⟨?_, ?_⟩⟩
    · exact hS.commTA (Subgroup.commutator_mem_commutator (hS.leT hdA) hx)
    · have e : ⁅⁅⁅a, g⁆, g⁆, x⁆ = ⁅⁅a, g⁆, g⁆ * (x * ⁅⁅a, g⁆, g⁆⁻¹ * x⁻¹) := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact (B ⊓ centralizer (B : Set M)).mul_mem hd
        (conj_mem_center (hAB hx) ((B ⊓ centralizer (B : Set M)).inv_mem hd))
  have hq : ∀ X Y : Subgroup M, IsChiefPair X Y → X ≤ A → ∀ x ∈ X, ⁅⁅x, g⁆, g⁆ ∈ Y := by
    intro X Y hc hXA
    refine quad_of_chief hTn hS.pT hZn hZT (hXA.trans hS.leT) hc hgZ ?_
    intro V hV u hu
    obtain ⟨hYV, hVX, hLV, hmin⟩ := hV
    have hYn := hc.2.1
    have hinfnorm : centralizer ((A ⊓ centralizer (A : Set M) : Subgroup M) : Set M) ⊔ zpowers g ≤
        normalizer ((V ⊓ Abar A _ hWc : Subgroup M) : Set M) := by
      intro r hr
      rw [Subgroup.mem_normalizer_iff]
      intro h
      have h1 := Subgroup.mem_normalizer_iff.mp (hLV hr) h
      have h2 := Subgroup.mem_normalizer_iff.mp (hLnorm hr) h
      rw [Subgroup.mem_inf, Subgroup.mem_inf, h1, h2]
    have hV'norm := mem_normalizer_sup_normal hYn hinfnorm
    have hYV' : Y ≤ (V ⊓ Abar A _ hWc) ⊔ Y := le_sup_right
    have hV'V : (V ⊓ Abar A _ hWc) ⊔ Y ≤ V := sup_le inf_le_left hYV.le
    rcases hmin _ hYV' hV'V hV'norm with h | h
    ·
      have hgnorm : g ∈ normalizer (V : Set M) := hLV (Subgroup.mem_sup_right (Subgroup.mem_zpowers g))
      have hVg : ∀ v ∈ V, ⁅v, g⁆ ∈ V := by
        intro v hv
        have e : ⁅v, g⁆ = v * (g * v⁻¹ * g⁻¹) := by simp only [commutatorElement_def]; group
        rw [e]
        exact V.mul_mem hv ((Subgroup.mem_normalizer_iff.mp hgnorm v⁻¹).mp (V.inv_mem hv))
      have hd : ⁅⁅u, g⁆, g⁆ ∈ V ⊓ Abar A _ hWc :=
        Subgroup.mem_inf.mpr ⟨hVg _ (hVg u hu), hq2 u (hXA (hVX hu))⟩
      have : ⁅⁅u, g⁆, g⁆ ∈ (V ⊓ Abar A _ hWc) ⊔ Y := Subgroup.mem_sup_left hd
      rw [h] at this
      exact this
    · have hu' : u ∈ (V ⊓ Abar A _ hWc) ⊔ Y := by rw [h]; exact hu
      rw [Subgroup.mem_sup_of_normal_right] at hu'
      obtain ⟨a, ha, y, hy, rfl⟩ := hu'
      refine quad_mul_normal hYn hy ?_
      rw [hq1 a ha.2]
      exact Y.one_mem
  exact target_of_quad hS hgS hgT hq

end CFSG.GH74.GLS.Stage2.Signalizer.L53
