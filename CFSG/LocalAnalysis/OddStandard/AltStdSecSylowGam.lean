module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecSylowBlock

public section

namespace CFSG.OddStandard.AltStdSec.SylowSn

@[expose] def Gam : List ℕ → Type
  | [] => PUnit
  | a :: l => W a × Gam l

instance instGroupGam : (l : List ℕ) → Group (Gam l)
  | [] => inferInstanceAs (Group PUnit)
  | a :: l => haveI := instGroupGam l; inferInstanceAs (Group (W a × Gam l))

instance instFiniteGam : (l : List ℕ) → Finite (Gam l)
  | [] => inferInstanceAs (Finite PUnit)
  | a :: l => haveI := instFiniteGam l; inferInstanceAs (Finite (W a × Gam l))

instance instSubsingletonGamNil : Subsingleton (Gam []) := inferInstanceAs (Subsingleton PUnit)

abbrev Gam.cons {a : ℕ} {l : List ℕ} (y₁ : W a) (y₂ : Gam l) : Gam (a :: l) := (y₁, y₂)

noncomputable def sgG : (l : List ℕ) → Gam l →* ℤˣ
  | [] => 1
  | a :: l => (sgW a).comp (MonoidHom.fst (W a) (Gam l)) *
      (sgG l).comp (MonoidHom.snd (W a) (Gam l))

theorem sgG_nil (γ : Gam []) : sgG [] γ = 1 := by
  rfl

theorem sgG_cons (a : ℕ) (l : List ℕ) (x : W a) (γ : Gam l) :
    sgG (a :: l) (Gam.cons x γ) = sgW a x * sgG l γ := by
  rfl

@[expose] noncomputable def EV (l : List ℕ) (y : Gam l) : ℕ := rootCount (sgG l) 1 y

@[expose] noncomputable def OD (l : List ℕ) (y : Gam l) : ℕ := rootCount (sgG l) (-1) y

theorem EV_cons (a : ℕ) (l : List ℕ) (y₁ : W a) (y₂ : Gam l) :
    EV (a :: l) (Gam.cons y₁ y₂) = ev a y₁ * EV l y₂ + od a y₁ * OD l y₂ := by
  have h := rootCount_prod (sgW a) (sgG l) (sgG (a :: l)) (fun p => rfl) 1 y₁ y₂
  rw [sum_units] at h
  simp only [mul_one, one_mul] at h
  exact h

theorem OD_cons (a : ℕ) (l : List ℕ) (y₁ : W a) (y₂ : Gam l) :
    OD (a :: l) (Gam.cons y₁ y₂) = ev a y₁ * OD l y₂ + od a y₁ * EV l y₂ := by
  have h := rootCount_prod (sgW a) (sgG l) (sgG (a :: l)) (fun p => rfl) (-1) y₁ y₂
  rw [sum_units] at h
  simp only [mul_one, one_mul, neg_mul, neg_neg] at h
  exact h

theorem one_le_EV_one (l : List ℕ) : 1 ≤ EV l 1 := by
  unfold EV rootCount
  have : Nonempty {a : Gam l // sgG l a = 1 ∧ a * a = 1} := ⟨⟨1, map_one _, one_mul _⟩⟩
  exact Nat.card_pos

theorem central_cons {a : ℕ} {l : List ℕ} {y₁ : W a} {y₂ : Gam l}
    (hc : ∀ x : Gam (a :: l), x * Gam.cons y₁ y₂ = Gam.cons y₁ y₂ * x) :
    (∀ x : W a, x * y₁ = y₁ * x) ∧ (∀ x : Gam l, x * y₂ = y₂ * x) := by
  constructor
  · intro x
    have h := hc (Gam.cons x 1)
    exact (Prod.ext_iff.1 h).1
  · intro x
    have h := hc (Gam.cons 1 x)
    exact (Prod.ext_iff.1 h).2

theorem sq_cons {a : ℕ} {l : List ℕ} {y₁ : W a} {y₂ : Gam l}
    (h : Gam.cons y₁ y₂ * Gam.cons y₁ y₂ = 1) : y₁ * y₁ = 1 ∧ y₂ * y₂ = 1 :=
  Prod.ext_iff.1 h

theorem central_inv_W (a : ℕ) (y : W a) (hc : ∀ x : W a, x * y = y * x) (hs : y * y = 1) :
    y = 1 ∨ (1 ≤ a ∧ y = cc a) := by
  by_cases ha : 1 ≤ a
  · rcases eq_one_or_cc a ha y hc hs with h | h
    · exact Or.inl h
    · exact Or.inr ⟨ha, h⟩
  · obtain rfl : a = 0 := by omega
    exact Or.inl (Subsingleton.elim _ _)

theorem mono_gam (l : List ℕ) : ∀ y : Gam l, (∀ x : Gam l, x * y = y * x) → y * y = 1 → y ≠ 1 →
    EV l y ≤ EV l 1 ∧ OD l y ≤ OD l 1 ∧ (EV l y < EV l 1 ∨ OD l y < OD l 1) := by
  induction l with
  | nil => intro y _ _ hy; exact absurd (Subsingleton.elim _ _) hy
  | cons a l ih =>
    rintro ⟨y₁, y₂⟩ hc hsq hne
    obtain ⟨hc₁, hc₂⟩ := central_cons hc
    obtain ⟨hs₁, hs₂⟩ := sq_cons hsq
    have htail : EV l y₂ ≤ EV l 1 ∧ OD l y₂ ≤ OD l 1 := by
      by_cases h2 : y₂ = 1
      · subst h2
        exact ⟨le_rfl, le_rfl⟩
      · exact ⟨(ih y₂ hc₂ hs₂ h2).1, (ih y₂ hc₂ hs₂ h2).2.1⟩
    have h1 : EV (a :: l) (1 : Gam (a :: l)) = ev a 1 * EV l 1 + od a 1 * OD l 1 :=
      EV_cons a l 1 1
    have h2 : OD (a :: l) (1 : Gam (a :: l)) = ev a 1 * OD l 1 + od a 1 * EV l 1 :=
      OD_cons a l 1 1
    rw [EV_cons, OD_cons, h1, h2]
    have hE : 1 ≤ ev a 1 := one_le_ev_one a
    have hx0 : 1 ≤ EV l 1 := one_le_EV_one l
    rcases central_inv_W a y₁ hc₁ hs₁ with rfl | ⟨ha, rfl⟩
    · have hy₂ : y₂ ≠ 1 := fun h => hne (by subst h; rfl)
      obtain ⟨hx, hu, hxu⟩ := ih y₂ hc₂ hs₂ hy₂
      refine ⟨Nat.add_le_add (Nat.mul_le_mul le_rfl hx) (Nat.mul_le_mul le_rfl hu),
        Nat.add_le_add (Nat.mul_le_mul le_rfl hu) (Nat.mul_le_mul le_rfl hx), ?_⟩
      rcases hxu with h | h
      · left
        have := Nat.mul_lt_mul_of_pos_left h hE
        have := Nat.mul_le_mul (le_refl (od a 1)) hu
        omega
      · right
        have := Nat.mul_lt_mul_of_pos_left h hE
        have := Nat.mul_le_mul (le_refl (od a 1)) hx
        omega
    · obtain ⟨hlt, hle, hO⟩ := block_facts a ha
      refine ⟨Nat.add_le_add (Nat.mul_le_mul hlt.le htail.1) (Nat.mul_le_mul hle htail.2),
        Nat.add_le_add (Nat.mul_le_mul hlt.le htail.2) (Nat.mul_le_mul hle htail.1), Or.inl ?_⟩
      have h3 := Nat.mul_lt_mul_of_pos_right hlt hx0
      have h4 := Nat.mul_le_mul (le_refl (ev a (cc a))) htail.1
      have h5 := Nat.mul_le_mul hle htail.2
      have h6 := Nat.mul_le_mul (le_refl (od a (cc a))) htail.2
      omega

theorem one_le_OD_one (l : List ℕ) (hl : ∃ b ∈ l, 1 ≤ b) : 1 ≤ OD l 1 := by
  induction l with
  | nil => simp at hl
  | cons b l ih =>
    have h : OD (b :: l) (1 : Gam (b :: l)) = ev b 1 * OD l 1 + od b 1 * EV l 1 :=
      OD_cons b l 1 1
    rw [h]
    by_cases hb : 1 ≤ b
    · have h1 := (block_facts b hb).2.2
      have h2 := one_le_EV_one l
      have := Nat.mul_le_mul h1 h2
      omega
    · obtain rfl : b = 0 := by omega
      have hl' : ∃ c ∈ l, 1 ≤ c := by
        obtain ⟨c, hc, hc1⟩ := hl
        rcases List.mem_cons.1 hc with rfl | hc
        · omega
        · exact ⟨c, hc, hc1⟩
      have := ih hl'
      rw [ev_zero, od_zero]
      omega

theorem strict_gam (l : List ℕ) (hl : ∃ a ∈ l, 3 ≤ a) :
    ∀ y : Gam l, (∀ x : Gam l, x * y = y * x) → y * y = 1 → y ≠ 1 → OD l y < OD l 1 := by
  induction l with
  | nil => simp at hl
  | cons a l ih =>
    rintro ⟨y₁, y₂⟩ hc hsq hne
    obtain ⟨hc₁, hc₂⟩ := central_cons hc
    obtain ⟨hs₁, hs₂⟩ := sq_cons hsq
    have htail : EV l y₂ ≤ EV l 1 ∧ OD l y₂ ≤ OD l 1 := by
      by_cases h2 : y₂ = 1
      · subst h2
        exact ⟨le_rfl, le_rfl⟩
      · exact ⟨(mono_gam l y₂ hc₂ hs₂ h2).1, (mono_gam l y₂ hc₂ hs₂ h2).2.1⟩
    have h2 : OD (a :: l) (1 : Gam (a :: l)) = ev a 1 * OD l 1 + od a 1 * EV l 1 :=
      OD_cons a l 1 1
    rw [OD_cons, h2]
    have hE : 1 ≤ ev a 1 := one_le_ev_one a
    have hx0 : 1 ≤ EV l 1 := one_le_EV_one l
    have hbig : 3 ≤ a ∨ ∃ b ∈ l, 3 ≤ b := by
      obtain ⟨b, hb, hb3⟩ := hl
      rcases List.mem_cons.1 hb with rfl | hb
      · exact Or.inl hb3
      · exact Or.inr ⟨b, hb, hb3⟩
    rcases central_inv_W a y₁ hc₁ hs₁ with rfl | ⟨ha, rfl⟩
    · have hy₂ : y₂ ≠ 1 := fun h => hne (by subst h; rfl)
      rcases hbig with h3 | hl'
      · obtain ⟨hx, hu, hxu⟩ := mono_gam l y₂ hc₂ hs₂ hy₂
        have hO : 1 ≤ od a 1 := (block_facts a (by omega)).2.2
        rcases hxu with h | h
        · have := Nat.mul_lt_mul_of_pos_left h hO
          have := Nat.mul_le_mul (le_refl (ev a 1)) hu
          omega
        · have := Nat.mul_lt_mul_of_pos_left h hE
          have := Nat.mul_le_mul (le_refl (od a 1)) hx
          omega
      · have h := ih hl' y₂ hc₂ hs₂ hy₂
        have := Nat.mul_lt_mul_of_pos_left h hE
        have := Nat.mul_le_mul (le_refl (od a 1)) htail.1
        omega
    · obtain ⟨hlt, hle, hO⟩ := block_facts a ha
      rcases hbig with h3 | hl'
      · have hO' : od a (cc a) = 0 := od_cc_eq_zero a h3
        rw [hO']
        have h4 := Nat.mul_le_mul hlt.le htail.2
        have h5 := Nat.mul_le_mul (le_refl (ev a 1)) htail.2
        have h6 := Nat.mul_le_mul hO hx0
        have h7 := Nat.mul_le_mul (le_refl (ev a (cc a))) htail.2
        have h8 := Nat.mul_le_mul hlt.le (le_refl (OD l 1))
        omega
      · by_cases hy₂ : y₂ = 1
        · subst hy₂
          have hu0 : 1 ≤ OD l 1 := by
            obtain ⟨b, hb, hb3⟩ := hl'
            exact one_le_OD_one l ⟨b, hb, by omega⟩
          have h3 := Nat.mul_lt_mul_of_pos_right hlt hu0
          have h4 := Nat.mul_le_mul hle (le_refl (EV l 1))
          omega
        · have h := ih hl' y₂ hc₂ hs₂ hy₂
          have hE' : 1 ≤ ev a 1 := by omega
          have h3 := Nat.mul_le_mul hlt.le (le_refl (OD l y₂))
          have h4 := Nat.mul_lt_mul_of_pos_left h hE'
          have h5 := Nat.mul_le_mul hle htail.1
          omega

end CFSG.OddStandard.AltStdSec.SylowSn
