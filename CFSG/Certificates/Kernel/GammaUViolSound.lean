
module

public import Certificates.Data.Kernel.GammaUViolK
public import CFSG.Certificates.Kernel.IdxFourChainSound
public import CFSG.GF2Type.Smith1979.GammaU.Violation

public section

namespace CFSG.KC.GUV

open CFSG.KC.IF4C CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA

local notation "GL" => V12 ≃ₗ[ZMod 2] V12

theorem subQ_cons (p : Nat) (P : List Nat) (m : Nat) :
    subQ (p :: P) m = mulP (subQ P (m / 2)) (bif Nat.beq (m % 2) 1 then p else idP) := rfl

theorem subQ_nil (m : Nat) : subQ [] m = idP := rfl

theorem exists_row_subQ {P : List Nat} {gs : List (Array ℕ)}
    (h : List.Forall₂ (fun p g => ∀ v, linP p v = linOfRows g v) P gs) :
    ∀ (acc : List (Array ℕ)) (y : Array ℕ), y ∈ acc → ∀ m, ∃ x ∈
      gs.foldl (fun acc g => acc ++ acc.map (mulR g)) acc,
        ∀ v, linOfRows x v = linP (subQ P m) (linOfRows y v) := by
  induction h with
  | nil => exact fun acc y hy m => ⟨y, hy, fun v => by rw [subQ_nil, linP_idP]⟩
  | @cons p g P gs hpg _ ih =>
    intro acc y hy m
    rw [List.foldl_cons]
    cases hb : Nat.beq (m % 2) 1
    · obtain ⟨x, hx, hxv⟩ := ih (acc ++ acc.map (mulR g)) y (List.mem_append_left _ hy) (m / 2)
      refine ⟨x, hx, fun v => ?_⟩
      rw [subQ_cons, hb, cond_false, linP_mulP, linP_idP, hxv]
    · obtain ⟨x, hx, hxv⟩ := ih (acc ++ acc.map (mulR g)) (mulR g y)
        (List.mem_append_right _ (List.mem_map.2 ⟨y, hy, rfl⟩)) (m / 2)
      refine ⟨x, hx, fun v => ?_⟩
      rw [subQ_cons, hb, cond_true, linP_mulP, hxv, linOfRows_mulR, hpg]

theorem exists_subQ_of_mem {P : List Nat} {gs : List (Array ℕ)}
    (h : List.Forall₂ (fun p g => ∀ v, linP p v = linOfRows g v) P gs) :
    ∀ (acc : List (Array ℕ)) (x : Array ℕ), x ∈ gs.foldl (fun acc g => acc ++ acc.map (mulR g)) acc →
      ∃ y ∈ acc, ∃ m < 2 ^ gs.length, ∀ v, linOfRows x v = linP (subQ P m) (linOfRows y v) := by
  induction h with
  | nil => exact fun acc x hx => ⟨x, hx, 0, by simp, fun v => by rw [subQ_nil, linP_idP]⟩
  | @cons p g P gs hpg _ ih =>
    intro acc x hx
    rw [List.foldl_cons] at hx
    obtain ⟨y', hy', m, hm, hxv⟩ := ih _ x hx
    have hlt : 2 * m + 1 < 2 ^ (g :: gs).length := by
      rw [List.length_cons, pow_succ]
      generalize 2 ^ gs.length = K at hm ⊢
      omega
    rcases List.mem_append.1 hy' with hy | hy
    · refine ⟨y', hy, 2 * m, by omega, fun v => ?_⟩
      have h2 : Nat.beq (2 * m % 2) 1 = false := by
        rw [Nat.mul_mod_right]
        rfl
      rw [subQ_cons, h2, cond_false, linP_mulP, linP_idP, hxv, Nat.mul_div_cancel_left _ (by omega)]
    · obtain ⟨y, hy0, rfl⟩ := List.mem_map.1 hy
      refine ⟨y, hy0, 2 * m + 1, hlt, fun v => ?_⟩
      have h2 : Nat.beq ((2 * m + 1) % 2) 1 = true := by
        rw [Nat.add_mod, Nat.mul_mod_right]
        rfl
      have h3 : (2 * m + 1) / 2 = m := by omega
      rw [subQ_cons, h2, cond_true, linP_mulP, h3, hxv, linOfRows_mulR, hpg]

theorem mem_subsetProducts_iff {P : List Nat} {gs : List (Array ℕ)}
    (h : List.Forall₂ (fun p g => ∀ v, linP p v = linOfRows g v) P gs) :
    (∀ m, ∃ x ∈ subsetProducts gs, ∀ v, linOfRows x v = linP (subQ P m) v) ∧
      ∀ x ∈ subsetProducts gs, ∃ m < 2 ^ gs.length, ∀ v, linOfRows x v = linP (subQ P m) v := by
  refine ⟨fun m => ?_, fun x hx => ?_⟩
  · obtain ⟨x, hx, hxv⟩ := exists_row_subQ h [idR] idR (List.mem_singleton_self _) m
    exact ⟨x, hx, fun v => by rw [hxv, linOfRows_idR]⟩
  · obtain ⟨y, hy, m, hm, hxv⟩ := exists_subQ_of_mem h [idR] x hx
    rw [List.mem_singleton] at hy
    subst hy
    exact ⟨m, hm, fun v => by rw [hxv, linOfRows_idR]⟩

theorem ltAll_iff (n : Nat) (w : List Nat) : ltAll n w = true ↔ ∀ e ∈ w, e < n := by
  induction w with
  | nil => simp [ltAll]
  | cons e w ih =>
    change (Nat.blt e n && ltAll n w) = true ↔ _
    rw [Bool.and_eq_true, Nat.blt_eq, ih, List.forall_mem_cons]

theorem isP_wordF {K : Subgroup GL} {f : Nat → Nat} {n : Nat}
    (hf : ∀ e < n, ∃ U ∈ K, IsP U (f e)) :
    ∀ w : List Nat, ltAll n w = true → ∃ U ∈ K, IsP U (wordF f w)
  | [], _ => ⟨1, K.one_mem, IsP.one⟩
  | e :: w, hw => by
    rw [ltAll_iff, List.forall_mem_cons] at hw
    obtain ⟨U, hU, hUP⟩ := hf e hw.1
    obtain ⟨V, hV, hVP⟩ := isP_wordF hf w ((ltAll_iff n w).2 hw.2)
    exact ⟨U * V, K.mul_mem hU hV, hUP.mul hVP⟩

theorem not_beq_eq (a b : Nat) : (!(Nat.beq a b)) = (a != b) := by
  cases h : Nat.beq a b
  · simp [bne_iff_ne, Nat.ne_of_beq_eq_false h]
  · simp [Nat.eq_of_beq_eq_true h]

theorem f2I3_spec {x y w : Nat} (h : f2I3 x y w = true) : Viol.f2Indep3 x y w = true := by
  unfold f2I3 at h
  simp only [not_beq_eq] at h
  exact h

theorem antiP_spec {TH A : Nat} (hTH : ∀ v, linP TH v = theta0 v) (h : antiP TH A = true) (v : V12) :
    linP A (theta0 v) = theta0 (theta0 (linP A v)) := by
  unfold antiP at h
  rw [Nat.beq_eq] at h
  have := congrArg (fun m => linP m v) h
  simp only [linP_mulP, hTH] at this
  exact this

theorem frOK_spec {L : List Nat} {A u m : Nat} (h : frOK L A u m = true) {U : GL} (hU : IsP U u) :
    m < 32 ∧ ∀ v, U⁻¹ (linP A (U v)) = linP (subQ L m) v := by
  unfold frOK at h
  rw [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  refine ⟨h.1, fun v => ?_⟩
  have h2 := congrArg (fun m => linP m v) h.2
  simp only [linP_mulP] at h2
  rw [← hU, ← hU] at h2
  rw [h2, inv_apply_apply]

theorem d2aOK_spec {L : List Nat} {TH : Nat} {f : Nat → Nat} {n : Nat} {rec : List (List Nat)}
    (h : d2aOK L TH f n rec = true) {K : Subgroup GL} (hf : ∀ e < n, ∃ U ∈ K, IsP U (f e))
    (hTH : ∀ v, linP TH v = theta0 v) {Lc H : List (Array ℕ)}
    (hL : ∀ m, ∃ x ∈ Lc, ∀ v, linOfRows x v = linP (subQ L m) v) :
    Viol.Violation K Lc H := by
  unfold d2aOK d2aAt at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨-, hA⟩, ⟨⟨⟨⟨⟨⟨hw₁, hw₂⟩, hw₃⟩, hf₁⟩, hf₂⟩, hf₃⟩, hI⟩⟩ := h
  set A := subQ L (nthD 0 (nthD [] rec 0) 0)
  obtain ⟨U₁, hU₁, hP₁⟩ := isP_wordF hf _ hw₁
  obtain ⟨U₂, hU₂, hP₂⟩ := isP_wordF hf _ hw₂
  obtain ⟨U₃, hU₃, hP₃⟩ := isP_wordF hf _ hw₃
  obtain ⟨r, hr, hrv⟩ := hL (nthD 0 (nthD [] rec 0) 0)
  have hfr : ∀ (U : GL) (u m : Nat), IsP U u → frOK L A u m = true → Viol.InFrame Lc U r := by
    intro U u m hU hfm
    obtain ⟨x, hx, hxv⟩ := hL m
    refine ⟨x, hx, fun v => ?_⟩
    rw [hrv, hxv]
    exact (frOK_spec hfm hU).2 v
  have ha0 : vecOf a0 = vecOf 3072 := rfl
  refine Or.inr (Or.inr ⟨r, hr, fun v => ?_, U₁, hU₁, U₂, hU₂, U₃, hU₃, hfr _ _ _ hP₁ hf₁,
    hfr _ _ _ hP₂ hf₂, hfr _ _ _ hP₃ hf₃, ?_⟩)
  · rw [hrv, hrv]
    exact antiP_spec hTH hA v
  · rw [ha0, hP₁.apply_code, hP₂.apply_code, hP₃.apply_code]
    exact Viol.f2Indep3_spec (ap12_lt _ _) (ap12_lt _ _) (ap12_lt _ _) (f2I3_spec hI)

end CFSG.KC.GUV

end
