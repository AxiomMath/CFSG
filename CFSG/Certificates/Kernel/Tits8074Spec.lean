module

public import CFSG.Certificates.Kernel.Tits8074Sound
public import CFSG.Certificates.Kernel.Asc82Syl.Codes
public import Certificates.Data.Kernel.Tits8074Grp

public section

namespace CFSG.KC.Tits8074

variable {L : Nat → Nat}

theorem allL_iff {α : Type} {f : α → Bool} : ∀ {l : List α}, allL l f = true ↔ ∀ a ∈ l, f a = true
  | [] => by simp [allL]
  | b :: l => by
    have e : allL (b :: l) f = bAnd(f b, allL l f) := rfl
    rw [e, band_true, allL_iff]
    simp

theorem fixes_spec {pre : List Nat} {c : Nat} (h : fixes L pre c = true) :
    ∀ p ∈ pre, ap L c p = p :=
  fun p hp => Nat.eq_of_beq_eq_true (allL_spec h p hp)

theorem fixes_of {pre : List Nat} {c : Nat} (h : ∀ p ∈ pre, ap L c p = p) :
    fixes L pre c = true :=
  allL_iff.2 fun p hp => Nat.beq_eq_true_eq _ _ ▸ h p hp

theorem bif_imp {c t : Bool} (h : bIf(c, t, true) = true) (hc : c = true) : t = true := by
  subst hc
  exact h

theorem cenZ_spec {z : Nat} (h : cenZ L z = true) :
    ∀ c ∈ codes, fixes L [0] c = true → ∀ p ∈ bs, ap L z (ap L c p) = ap L c (ap L z p) :=
  fun c hc hf => commF_spec (bif_imp (allL_spec h c hc) hf)

theorem orbK_spec {R : List (List Nat)} {pre : List Nat} {b : Nat} (h : orbK L R pre b = true) :
    (∀ u ∈ R, ∀ c ∈ u, ∀ p ∈ pre, ap L c p = p) ∧
      ∀ u ∈ R, ∀ c ∈ codes, (∀ p ∈ pre, ap L c p = p) →
        ∃ v ∈ R, ev L v b = ap L c (ev L u b) := by
  have e : orbK L R pre b = bAnd(allL R fun u => allL u fun c => fixes L pre c,
      allL R fun u => allL codes fun c => bIf(fixes L pre c,
        anyL R fun v => Nat.beq (ev L v b) (ap L c (ev L u b)), true)) := rfl
  rw [e, band_true] at h
  refine ⟨fun u hu c hc => fixes_spec (allL_spec (allL_spec h.1 u hu) c hc), ?_⟩
  intro u hu c hc hf
  have ha := bif_imp (allL_spec (allL_spec h.2 u hu) c hc) (fixes_of hf)
  have any_spec : ∀ {l : List (List Nat)}, (anyL l fun v => Nat.beq (ev L v b)
      (ap L c (ev L u b))) = true → ∃ v ∈ l, ev L v b = ap L c (ev L u b) := by
    intro l
    induction l with
    | nil => intro h0; exact absurd h0 Bool.false_ne_true
    | cons v l ih =>
      intro h1
      have e1 : (anyL (v :: l) fun v => Nat.beq (ev L v b) (ap L c (ev L u b))) =
          bIf(Nat.beq (ev L v b) (ap L c (ev L u b)), true,
            anyL l fun v => Nat.beq (ev L v b) (ap L c (ev L u b))) := rfl
      rw [e1, bif_true] at h1
      rcases h1 with ⟨hv, -⟩ | ⟨-, hl⟩
      · exact ⟨v, List.mem_cons_self .., Nat.eq_of_beq_eq_true hv⟩
      · obtain ⟨w, hw, ew⟩ := ih hl
        exact ⟨w, List.mem_cons_of_mem v hw, ew⟩
  exact any_spec ha

theorem pairK_spec {s : Nat} (h : pairK L s = true) :
    (∀ c ∈ codes, (∀ p ∈ [0, 3], ap L c p = p) → ap L c 4 = 4) ∧
      ap L s 0 = 0 ∧ ap L s 3 = 4 ∧ ap L s 4 = 3 := by
  have e : pairK L s = bAnd(allL codes fun c => bIf(fixes L [0, 3] c, Nat.beq (ap L c 4) 4, true),
      bAnd(Nat.beq (ap L s 0) 0, bAnd(Nat.beq (ap L s 3) 4, Nat.beq (ap L s 4) 3))) := rfl
  rw [e, band_true, band_true, band_true] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨fun c hc hf => Nat.eq_of_beq_eq_true (bif_imp (allL_spec h1 c hc) (fixes_of hf)),
    Nat.eq_of_beq_eq_true h2, Nat.eq_of_beq_eq_true h3, Nat.eq_of_beq_eq_true h4⟩

theorem zOne_spec {z s : Nat} {f : Nat → Nat} (h : zOne L z s f = true)
    (hs : ∀ p ∈ bs, f (ap L s p) = ap L s (f p))
    (hc : ∀ c ∈ codes, (∀ p ∈ [0, 3], ap L c p = p) → ∀ p ∈ bs, f (ap L c p) = ap L c (f p)) :
    (∀ p ∈ bs, f p = p) ∨ (∀ p ∈ bs, f p = ap L z p) := by
  have hs' : commF f (ap L s) = true :=
    allL_iff.2 fun p hp => Nat.beq_eq_true_eq _ _ ▸ hs p hp
  have hc' : (allL codes fun c => bIf(fixes L [0, 3] c, commF f (ap L c), true)) = true := by
    refine allL_iff.2 fun c hcm => ?_
    cases hfx : fixes L [0, 3] c
    · rfl
    · exact allL_iff.2 fun p hp => Nat.beq_eq_true_eq _ _ ▸ hc c hcm (fixes_spec hfx) p hp
  have e : zOne L z s f = bIf(commF f (ap L s),
      bIf(allL codes fun c => bIf(fixes L [0, 3] c, commF f (ap L c), true),
        bIf(allL bs fun p => Nat.beq (f p) p, true, allL bs fun p => Nat.beq (f p) (ap L z p)),
        true), true) := rfl
  rw [e, hs', hc'] at h
  change bIf(allL bs fun p => Nat.beq (f p) p, true,
    allL bs fun p => Nat.beq (f p) (ap L z p)) = true at h
  cases h1 : (allL bs fun p => Nat.beq (f p) p)
  · rw [h1] at h
    exact Or.inr fun p hp => Nat.eq_of_beq_eq_true (allL_spec h p hp)
  · exact Or.inl fun p hp => Nat.eq_of_beq_eq_true (allL_spec h1 p hp)

theorem zsK_spec {z s : Nat} {e : Bool} {R₂ R₃ R₄ R₅ R₆ : List (List Nat)}
    (h : zsK L z s e R₂ R₃ R₄ R₅ R₆ = true) :
    ∀ u₂ ∈ R₂, ∀ u₃ ∈ R₃, ∀ u₄ ∈ R₄, ∀ u₅ ∈ R₅, ∀ u₆ ∈ R₆, zOne L z s (fun p =>
      (fun y => nIf(e, ap L s y, y)) (ev L u₂ (ev L u₃ (ev L u₄ (ev L u₅ (ev L u₆ p)))))) =
        true :=
  fun u₂ h₂ u₃ h₃ u₄ h₄ u₅ h₅ u₆ h₆ =>
    allL_spec (allL_spec (allL_spec (allL_spec (allL_spec h u₂ h₂) u₃ h₃) u₄ h₄) u₅ h₅) u₆ h₆

theorem genEq_spec {G : Nat → Nat} : ∀ {W : List (List Nat)} {k₀ : Nat}, genEq L G W k₀ = true →
    ∀ (j : Nat) (hj : j < W.length), ∀ p < 1755, pgf (G (k₀ + j)) p = ev L W[j] p
  | [], _, _, j, hj => absurd hj (Nat.not_lt_zero j)
  | w :: W, k₀, h, j, hj => by
    have e : genEq L G (w :: W) k₀ = bAnd(CFSG.KC.Loop.allBelow 1755 28 fun p =>
        Nat.beq (pgf (G k₀) p) (ev L w p), genEq L G W (Nat.succ k₀)) := rfl
    rw [e, band_true] at h
    intro p hp
    cases j with
    | zero =>
      exact Nat.eq_of_beq_eq_true (CFSG.KS.Asc82Syl.allBelow_a82 h.1 (by decide) p hp)
    | succ j =>
      have r := genEq_spec h.2 j (by simpa using hj) p hp
      rw [show k₀ + (j + 1) = Nat.succ k₀ + j by omega]
      simpa using r

theorem commG_spec {G : Nat → Nat} {c : Nat} : ∀ {n : Nat}, commG L G n c = true →
    ∀ k < n, ∀ p ∈ bs, pgf (G k) (ap L c p) = ap L c (pgf (G k) p)
  | 0, _, k, hk => absurd hk (Nat.not_lt_zero k)
  | n + 1, h, k, hk => by
    have e : commG L G (n + 1) c = bAnd(commF (pgf (G n)) (ap L c), commG L G n c) := rfl
    rw [e, band_true] at h
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · exact commG_spec h.2 k hk
    · exact commF_spec h.1

theorem conjK_spec {T : Nat → Nat} : ∀ {W : List (List Nat)} {i₀ : Nat}, conjK L T W i₀ = true →
    ∀ (j : Nat) (hj : j < W.length), i₀ + j ≠ 0 →
      ∀ p ∈ bs, ev L W[j] (pgf (T (i₀ + j)) p) = ap L 2 (ev L W[j] p)
  | [], _, _, j, hj => absurd hj (Nat.not_lt_zero j)
  | w :: W, i₀, h, j, hj => by
    have e : conjK L T (w :: W) i₀ = bAnd(bIf(Nat.beq i₀ 0, true,
        allL bs fun p => Nat.beq (ev L w (pgf (T i₀) p)) (ap L 2 (ev L w p))),
        conjK L T W (Nat.succ i₀)) := rfl
    rw [e, band_true] at h
    intro h0 p hp
    cases j with
    | zero =>
      have hne : Nat.beq i₀ 0 = false :=
        Bool.eq_false_iff.2 fun hb => h0 (by rw [Nat.eq_of_beq_eq_true hb])
      rw [hne] at h
      exact Nat.eq_of_beq_eq_true (allL_spec h.1 p hp)
    | succ j =>
      have r := conjK_spec h.2 j (by simpa using hj) (by omega) p hp
      rw [show i₀ + (j + 1) = Nat.succ i₀ + j by omega]
      simpa using r

theorem nGood_eq : ∀ E : List (List Nat × Nat), nGood E = (E.filter fun e => e.2 == 2047).length
  | [] => rfl
  | e :: E => by
    have h : nGood (e :: E) = nIf(Nat.beq e.2 2047, Nat.succ (nGood E), nGood E) := rfl
    rw [h, nGood_eq E, List.filter_cons]
    cases hb : Nat.beq e.2 2047
    · have : ¬ e.2 = 2047 := fun h' => by
        rw [h'] at hb
        exact absurd hb (by decide)
      simp [this]
    · have : e.2 = 2047 := Nat.eq_of_beq_eq_true hb
      simp [this]

end CFSG.KC.Tits8074

end
