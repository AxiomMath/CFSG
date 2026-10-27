
module

public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneKillSignBase

public import Certificates.Certificate3360

public section

namespace CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOne

open Subgroup

theorem sgnOK_of_mem {u : Bool} {σ : Equiv.Perm (Fin 64)}
    (hσ : σ ∈ Gq u) : sgnOK u (tupleOf σ) = true :=
  (Certificates.certificate3360 u).2.1 σ hσ

theorem pres_false_spec {σ : Equiv.Perm (Fin 64)}
    (hσ : σ ∈ Gq false) :
    (Pres false σ → ∀ v, v < 64 → wpart v = xpart v → wpart (fn σ v) = xpart (fn σ v)) ∧
    (Pres false σ → ∀ v, v < 64 → wpart v = 0 → wpart (fn σ v) = 0) ∧
    (¬ Pres false σ → ∀ v, v < 64 → wpart v = 0 → wpart (fn σ v) = xpart (fn σ v)) ∧
    (¬ Pres false σ → ∀ v, v < 64 → wpart v = xpart v → wpart (fn σ v) = 0) := by
  have hs := sgnOK_of_mem hσ
  simp only [sgnOK, Bool.false_eq_true, ite_false, Bool.or_eq_true, Bool.and_eq_true,
    imNl_tupleOf hσ.1, imNr_tupleOf hσ.1, List.all_cons, List.all_nil, Bool.and_true,
    beq_iff_eq] at hs
  have hP : Pres false σ ↔ wpart (fn σ (mkv 0 1)) = 0 ∧ wpart (fn σ (mkv 0 2)) = 0 ∧
      wpart (fn σ (mkv 0 4)) = 0 := by
    simp only [Pres, presT, Bool.false_eq_true, ite_false, imNl_tupleOf hσ.1, List.all_cons,
      List.all_nil, Bool.and_true, Bool.and_eq_true, beq_iff_eq]
  have hne : fn σ (mkv 0 1) ≠ 0 := fun h0 => absurd (fn_eq_zero hσ.1 (by decide) h0) (by decide)
  have hlt := fn_lt σ (mkv 0 1)
  refine ⟨fun hp => ?_, fun hp => ?_, fun hp => ?_, fun hp => ?_⟩
  · rcases hs with ⟨-, hr⟩ | ⟨hl, -⟩
    · exact maps_nr hσ.1 (p := fun v => wpart v = xpart v) wr_zero' wr_xor' hr.1 hr.2.1 hr.2.2
    · exact absurd (nl_nr_zero _ hlt ((hP.1 hp).1) hl.1) hne
  · rcases hs with ⟨hl, -⟩ | ⟨hl, -⟩
    · exact maps_nl hσ.1 (p := fun v => wpart v = 0) rfl wl_xor' hl.1 hl.2.1 hl.2.2
    · exact absurd (nl_nr_zero _ hlt ((hP.1 hp).1) hl.1) hne
  · rcases hs with ⟨hl, -⟩ | ⟨hl, -⟩
    · exact absurd (hP.2 hl) hp
    · exact maps_nl hσ.1 (p := fun v => wpart v = xpart v) wr_zero' wr_xor' hl.1 hl.2.1 hl.2.2
  · rcases hs with ⟨hl, -⟩ | ⟨-, hr⟩
    · exact absurd (hP.2 hl) hp
    · exact maps_nr hσ.1 (p := fun v => wpart v = 0) rfl wl_xor' hr.1 hr.2.1 hr.2.2

theorem pres_false_iff {σ : Equiv.Perm (Fin 64)}
    (hσ : σ ∈ Gq false) {y : ℕ} (hy : y < 64) (hy0 : y ≠ 0) :
    (wpart y = 0 → (Pres false σ ↔ wpart (fn σ y) = 0)) ∧
    (wpart y = xpart y → (Pres false σ ↔ wpart (fn σ y) ≠ 0)) := by
  obtain ⟨h1, h2, h3, h4⟩ := pres_false_spec hσ
  have hne : fn σ y ≠ 0 := fun h0 => hy0 (fn_eq_zero hσ.1 hy h0)
  have hlt := fn_lt σ y
  constructor
  · intro hw
    constructor
    · intro hp
      exact h2 hp y hy hw
    · intro hz
      by_contra hp
      exact hne (nl_nr_zero _ hlt hz (h3 hp y hy hw))
  · intro hw
    constructor
    · intro hp hz
      exact hne (nl_nr_zero _ hlt hz (h1 hp y hy hw))
    · intro hz
      by_contra hp
      exact hz (h4 hp y hy hw)

theorem pres_mul_false {σ τ : Equiv.Perm (Fin 64)}
    (hσ : σ ∈ Gq false) (hτ : τ ∈ Gq false) :
    Pres false (σ * τ) ↔ (Pres false σ ↔ Pres false τ) := by
  have hst := mul_mem hσ hτ
  have hy := fn_lt τ 2
  have hy0 : fn τ 2 ≠ 0 := fun h0 => absurd (fn_eq_zero hτ.1 (by norm_num) h0) (by norm_num)
  rw [((pres_false_iff (y := 2) hst (by norm_num) (by norm_num)).1 (by decide)),
    fn_mul σ τ (by norm_num)]
  by_cases hτp : Pres false τ
  · have hw : wpart (fn τ 2) = 0 :=
      (((pres_false_iff (y := 2) hτ (by norm_num) (by norm_num)).1 (by decide)).1 hτp)
    rw [← ((pres_false_iff hσ hy hy0).1 hw)]
    exact ⟨fun h => ⟨fun _ => hτp, fun _ => h⟩, fun h => h.2 hτp⟩
  · have hr : wpart (fn τ 2) = xpart (fn τ 2) :=
      (pres_false_spec hτ).2.2.1 hτp 2 (by norm_num) (by decide)
    have hσi := (pres_false_iff hσ hy hy0).2 hr
    constructor
    · intro hz
      exact ⟨fun hp => absurd hz (hσi.1 hp), fun h => absurd h hτp⟩
    · intro hiff
      by_contra hz
      exact hτp (hiff.1 (hσi.2 hz))

section UnitarySign

variable {ω : Equiv.Perm (Fin 64)} (hω : ω ∈ Gq true) (hωt : tupleOf ω = omT)
include hω hωt

theorem sgn_true_spec {σ : Equiv.Perm (Fin 64)} (hσ : σ ∈ Gq true) :
    σ * ω = ω * σ ∨ σ * ω = ω * ω * σ :=
  (sgn_true_iff hω hωt hσ).1 (sgnOK_of_mem hσ)

theorem pres_mul_true {σ τ : Equiv.Perm (Fin 64)}
    (hσ : σ ∈ Gq true) (hτ : τ ∈ Gq true) :
    Pres true (σ * τ) ↔ (Pres true σ ↔ Pres true τ) := by
  rw [pres_true_iff hω hωt (mul_mem hσ hτ), pres_true_iff hω hωt hσ, pres_true_iff hω hωt hτ]
  have h1 := omega_ne_one hωt
  have h3 := omega_cube hω hωt
  have hcancel : ∀ x : Equiv.Perm (Fin 64), ω * ω * x ≠ ω * x := fun x h =>
    h1 (mul_left_cancel (a := ω) (by rw [mul_one]; exact mul_right_cancel h))
  rcases sgn_true_spec hω hωt hσ with hA | hA <;> rcases sgn_true_spec hω hωt hτ with hB | hB
  · have : σ * τ * ω = ω * (σ * τ) := by
      calc σ * τ * ω = σ * (τ * ω) := by group
        _ = σ * (ω * τ) := by rw [hB]
        _ = (σ * ω) * τ := by group
        _ = ω * (σ * τ) := by rw [hA]; group
    exact ⟨fun _ => ⟨fun _ => hB, fun _ => hA⟩, fun _ => this⟩
  · have : σ * τ * ω = ω * ω * (σ * τ) := by
      calc σ * τ * ω = σ * (τ * ω) := by group
        _ = σ * (ω * ω * τ) := by rw [hB]
        _ = (σ * ω) * ω * τ := by group
        _ = (ω * σ) * ω * τ := by rw [hA]
        _ = ω * (σ * ω) * τ := by group
        _ = ω * (ω * σ) * τ := by rw [hA]
        _ = ω * ω * (σ * τ) := by group
    have hnB : ¬ τ * ω = ω * τ := fun h => hcancel τ (hB.symm.trans h)
    rw [this]
    exact ⟨fun h => absurd h (hcancel _), fun h => absurd (h.1 hA) hnB⟩
  · have : σ * τ * ω = ω * ω * (σ * τ) := by
      calc σ * τ * ω = σ * (τ * ω) := by group
        _ = σ * (ω * τ) := by rw [hB]
        _ = (σ * ω) * τ := by group
        _ = ω * ω * (σ * τ) := by rw [hA]; group
    have hnA : ¬ σ * ω = ω * σ := fun h => hcancel σ (hA.symm.trans h)
    rw [this]
    exact ⟨fun h => absurd h (hcancel _), fun h => absurd (h.2 hB) hnA⟩
  · have : σ * τ * ω = ω * (σ * τ) := by
      calc σ * τ * ω = σ * (τ * ω) := by group
        _ = σ * (ω * ω * τ) := by rw [hB]
        _ = (σ * ω) * ω * τ := by group
        _ = (ω * ω * σ) * ω * τ := by rw [hA]
        _ = ω * ω * (σ * ω) * τ := by group
        _ = ω * ω * (ω * ω * σ) * τ := by rw [hA]
        _ = (ω * (ω * ω)) * ω * σ * τ := by group
        _ = ω * (σ * τ) := by rw [h3]; group
    have hnA : ¬ σ * ω = ω * σ := fun h => hcancel σ (hA.symm.trans h)
    have hnB : ¬ τ * ω = ω * τ := fun h => hcancel τ (hB.symm.trans h)
    exact ⟨fun _ => ⟨fun h => absurd h hnA, fun h => absurd h hnB⟩, fun _ => this⟩

end UnitarySign

end CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOne
