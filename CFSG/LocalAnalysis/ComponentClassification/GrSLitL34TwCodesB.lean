module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34TwCodes
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34TwRAB
public import Certificates.Certificate33102
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourAutomorphisms

public section

namespace CFSG.ComponentClassification.GrSLit.L34Tw

open CFSG Subgroup CFSG.ComponentClassification.PSL3Four

@[expose] def codeSet (X : Subgroup WrE) : Set (Fin 4 × Fin 4 × Bool) := {c | ∃ x ∈ X, cc x = c}

theorem N0w_le_Pw : N0w ≤ Pw := fun x hx =>
  ⟨T0_le_RA (mem_N0w_iff.1 hx).2.1, T0_le_RA (mem_N0w_iff.1 hx).2.2⟩

theorem g₅_mem_RA : g₅ ∈ RA := Subgroup.subset_closure (Or.inr (by simp))

theorem g₆_mem_RA : g₆ ∈ RA := Subgroup.subset_closure (Or.inr (by simp))

theorem s1_mem_Pw : (⟨1, g₅ * g₆, true⟩ : WrE) ∈ Pw :=
  ⟨RA.one_mem, RA.mul_mem g₅_mem_RA g₆_mem_RA⟩

theorem s2_mem_Pw : (⟨g₅, g₆, true⟩ : WrE) ∈ Pw := ⟨g₅_mem_RA, g₆_mem_RA⟩

theorem cosRA_eq_zero_iff (r : Equiv.Perm (Fin 42)) : cosRA r = 0 ↔ r ∈ L34Facts.T0 := by
  unfold cosRA
  by_cases h0 : r ∈ L34Facts.T0
  · rw [if_pos h0]
    exact iff_of_true rfl h0
  · rw [if_neg h0]
    refine iff_of_false ?_ h0
    split_ifs <;> decide

theorem cosRA_one : cosRA 1 = 0 := (cosRA_eq_zero_iff 1).2 L34Facts.T0.one_mem

theorem cc_one : cc (1 : WrE) = (0, 0, false) := by
  change (cosRA 1, cosRA 1, false) = _
  rw [cosRA_one]

theorem mem_N0w_iff_cc {x : WrE} (_ : x ∈ Pw) : x ∈ N0w ↔ cc x = (0, 0, false) := by
  rw [mem_N0w_iff]
  change _ ↔ (cosRA x.a, cosRA x.b, x.e) = _
  rw [Prod.mk.injEq, Prod.mk.injEq, cosRA_eq_zero_iff, cosRA_eq_zero_iff]
  tauto

theorem cc_mul {x y : WrE} (hx : x ∈ Pw) (hy : y ∈ Pw) : cc (x * y) = qmulC (cc x) (cc y) := by
  have h := Certificates.certificate33102
  obtain ⟨a, b, e⟩ := x
  obtain ⟨c, d, f⟩ := y
  obtain ⟨ha, hb⟩ := mem_Pw_iff.1 hx
  obtain ⟨hc, hd⟩ := mem_Pw_iff.1 hy
  cases f
  · change (cosRA (a * c), cosRA (b * d), xor e false) =
      (cosXor (cosRA a) (cosRA c), cosXor (cosRA b) (cosRA d), xor e false)
    rw [h a ha c hc, h b hb d hd]
  · change (cosRA (b * c), cosRA (a * d), xor e true) =
      (cosXor (cosRA b) (cosRA c), cosXor (cosRA a) (cosRA d), xor e true)
    rw [h b hb c hc, h a ha d hd]

theorem inv_mul_mem_N0w {x y : WrE} (hx : x ∈ Pw) (hy : y ∈ Pw) (h : cc x = cc y) :
    x⁻¹ * y ∈ N0w := by
  have hxi : x⁻¹ ∈ Pw := Pw.inv_mem hx
  rw [mem_N0w_iff_cc (Pw.mul_mem hxi hy), cc_mul hxi hy, ← h, ← cc_mul hxi hx, inv_mul_cancel,
    cc_one]

theorem mem_of_cc_eq {X : Subgroup WrE} (hN : N0w ≤ X) {x y : WrE} (hx : x ∈ Pw) (hy : y ∈ X)
    (hyP : y ∈ Pw) (h : cc x = cc y) : x ∈ X := by
  have h1 : y⁻¹ * x ∈ N0w := inv_mul_mem_N0w hyP hx h.symm
  have := X.mul_mem hy (hN h1)
  rwa [mul_inv_cancel_left] at this

theorem mem_iff_cc {X : Subgroup WrE} (hXP : X ≤ Pw) (hN : N0w ≤ X) (x : WrE) :
    x ∈ X ↔ x ∈ Pw ∧ cc x ∈ codeSet X := by
  constructor
  · intro hx
    exact ⟨hXP hx, x, hx, rfl⟩
  · rintro ⟨hxP, y, hy, hyc⟩
    exact mem_of_cc_eq hN hxP hy (hXP hy) hyc.symm

theorem codeSet_zero {X : Subgroup WrE} : ((0 : Fin 4), (0 : Fin 4), false) ∈ codeSet X :=
  ⟨1, X.one_mem, cc_one⟩

theorem codeSet_mul {X : Subgroup WrE} (hXP : X ≤ Pw) {c d : Fin 4 × Fin 4 × Bool}
    (hc : c ∈ codeSet X) (hd : d ∈ codeSet X) : qmulC c d ∈ codeSet X := by
  obtain ⟨x, hx, rfl⟩ := hc
  obtain ⟨y, hy, rfl⟩ := hd
  exact ⟨x * y, X.mul_mem hx hy, cc_mul (hXP hx) (hXP hy)⟩

theorem not_mem_T0_five : g₅ ∉ L34Facts.T0 := fun h =>
  not_mem_S_r₂ (by simpa [r₂] using L34Facts.T0_le_S h)

theorem not_mem_T0_six : g₆ ∉ L34Facts.T0 := fun h =>
  not_mem_S_r₃ (by simpa [r₃] using L34Facts.T0_le_S h)

theorem not_mem_T0_g56 : g₅ * g₆ ∉ L34Facts.T0 := fun h =>
  not_mem_S_r₄ (by simpa [r₄] using L34Facts.T0_le_S h)

theorem cosRA_g5 : cosRA g₅ = 1 := by
  unfold cosRA
  rw [if_neg not_mem_T0_five, if_pos (by rw [inv_mul_cancel]; exact L34Facts.T0.one_mem)]

theorem cosRA_g6 : cosRA g₆ = 2 := by
  unfold cosRA
  have h1 : g₅⁻¹ * g₆ = g₅ * g₆ := by rw [inv_eq_of_mul_eq_one_right PSL3Four.g₅_mul_g₅]
  rw [if_neg not_mem_T0_six, if_neg (by rw [h1]; exact not_mem_T0_g56),
    if_pos (by rw [inv_mul_cancel]; exact L34Facts.T0.one_mem)]

theorem cosRA_g56 : cosRA (g₅ * g₆) = 3 := by
  rw [Certificates.certificate33102 g₅ g₅_mem_RA g₆ g₆_mem_RA, cosRA_g5, cosRA_g6]
  decide

theorem cc_s1 : cc (⟨1, g₅ * g₆, true⟩ : WrE) = (0, 3, true) := by
  show (cosRA 1, cosRA (g₅ * g₆), true) = _
  rw [cosRA_one, cosRA_g56]

theorem cc_s2 : cc (⟨g₅, g₆, true⟩ : WrE) = (1, 2, true) := by
  show (cosRA g₅, cosRA g₆, true) = _
  rw [cosRA_g5, cosRA_g6]

@[expose] def preimg (U : Set (Fin 4 × Fin 4 × Bool)) (h0 : ((0 : Fin 4), (0 : Fin 4), false) ∈ U)
    (hmul : ∀ c ∈ U, ∀ d ∈ U, qmulC c d ∈ U)
    (hinv : ∀ c ∈ U, ∀ d, qmulC c d = (0, 0, false) → d ∈ U) : Subgroup WrE where
  carrier := {x | x ∈ Pw ∧ cc x ∈ U}
  one_mem' := ⟨Pw.one_mem, by rw [cc_one]; exact h0⟩
  mul_mem' := by
    rintro x y ⟨hx, hxU⟩ ⟨hy, hyU⟩
    exact ⟨Pw.mul_mem hx hy, by rw [cc_mul hx hy]; exact hmul _ hxU _ hyU⟩
  inv_mem' := by
    rintro x ⟨hx, hxU⟩
    refine ⟨Pw.inv_mem hx, hinv _ hxU _ ?_⟩
    rw [← cc_mul hx (Pw.inv_mem hx), mul_inv_cancel, cc_one]

theorem mem_preimg {U : Set (Fin 4 × Fin 4 × Bool)}
    {h0 : ((0 : Fin 4), (0 : Fin 4), false) ∈ U} {hmul : ∀ c ∈ U, ∀ d ∈ U, qmulC c d ∈ U}
    {hinv : ∀ c ∈ U, ∀ d, qmulC c d = (0, 0, false) → d ∈ U} {x : WrE} :
    x ∈ preimg U h0 hmul hinv ↔ x ∈ Pw ∧ cc x ∈ U := Iff.rfl

private theorem U1_zero : ((0 : Fin 4), (0 : Fin 4), false) ∈ U1 := by simp [U1]

private theorem U1_mul : ∀ c ∈ U1, ∀ d ∈ U1, qmulC c d ∈ U1 := by
  intro c hc d hd
  simp only [U1, Set.mem_insert_iff, Set.mem_singleton_iff] at hc hd ⊢
  rcases hc with rfl | rfl | rfl | rfl <;> rcases hd with rfl | rfl | rfl | rfl <;> decide

private theorem U1_inv : ∀ c ∈ U1, ∀ d, qmulC c d = (0, 0, false) → d ∈ U1 := by
  intro c hc d hd
  simp only [U1, Set.mem_insert_iff, Set.mem_singleton_iff] at hc ⊢
  rcases hc with rfl | rfl | rfl | rfl <;> revert d <;> decide

private theorem U2_zero : ((0 : Fin 4), (0 : Fin 4), false) ∈ U2 := by simp [U2]

private theorem U2_mul : ∀ c ∈ U2, ∀ d ∈ U2, qmulC c d ∈ U2 := by
  intro c hc d hd
  simp only [U2, Set.mem_insert_iff, Set.mem_singleton_iff] at hc hd ⊢
  rcases hc with rfl | rfl | rfl | rfl <;> rcases hd with rfl | rfl | rfl | rfl <;> decide

private theorem U2_inv : ∀ c ∈ U2, ∀ d, qmulC c d = (0, 0, false) → d ∈ U2 := by
  intro c hc d hd
  simp only [U2, Set.mem_insert_iff, Set.mem_singleton_iff] at hc ⊢
  rcases hc with rfl | rfl | rfl | rfl <;> revert d <;> decide

theorem mem_X1_iff (x : WrE) : x ∈ X1 ↔ x ∈ Pw ∧ cc x ∈ U1 := by
  have hs : (⟨1, g₅ * g₆, true⟩ : WrE) ∈ X1 := Subgroup.subset_closure (Or.inr rfl)
  have hN : N0w ≤ X1 := fun y hy => Subgroup.subset_closure (Or.inl hy)
  have hs2 : cc ((⟨1, g₅ * g₆, true⟩ : WrE) * ⟨1, g₅ * g₆, true⟩) = (3, 3, false) := by
    rw [cc_mul s1_mem_Pw s1_mem_Pw, cc_s1]; decide
  have hs3 : cc ((⟨1, g₅ * g₆, true⟩ : WrE) * ⟨1, g₅ * g₆, true⟩ * ⟨1, g₅ * g₆, true⟩) =
      (3, 0, true) := by
    rw [cc_mul (Pw.mul_mem s1_mem_Pw s1_mem_Pw) s1_mem_Pw, hs2, cc_s1]; decide
  constructor
  · intro hx
    have hle : X1 ≤ preimg U1 U1_zero U1_mul U1_inv := by
      rw [X1, Subgroup.closure_le]
      rintro y (hy | rfl)
      · refine ⟨N0w_le_Pw hy, ?_⟩
        rw [(mem_N0w_iff_cc (N0w_le_Pw hy)).1 hy]
        exact U1_zero
      · exact ⟨s1_mem_Pw, by rw [cc_s1]; simp [U1]⟩
    exact hle hx
  · rintro ⟨hxP, hxU⟩
    simp only [U1, Set.mem_insert_iff, Set.mem_singleton_iff] at hxU
    rcases hxU with h | h | h | h
    · exact hN ((mem_N0w_iff_cc hxP).2 h)
    · exact mem_of_cc_eq hN hxP (X1.mul_mem hs hs) (Pw.mul_mem s1_mem_Pw s1_mem_Pw)
        (h.trans hs2.symm)
    · exact mem_of_cc_eq hN hxP hs s1_mem_Pw (h.trans cc_s1.symm)
    · exact mem_of_cc_eq hN hxP (X1.mul_mem (X1.mul_mem hs hs) hs)
        (Pw.mul_mem (Pw.mul_mem s1_mem_Pw s1_mem_Pw) s1_mem_Pw) (h.trans hs3.symm)

theorem mem_X2_iff (x : WrE) : x ∈ X2 ↔ x ∈ Pw ∧ cc x ∈ U2 := by
  have hs : (⟨g₅, g₆, true⟩ : WrE) ∈ X2 := Subgroup.subset_closure (Or.inr rfl)
  have hN : N0w ≤ X2 := fun y hy => Subgroup.subset_closure (Or.inl hy)
  have hs2 : cc ((⟨g₅, g₆, true⟩ : WrE) * ⟨g₅, g₆, true⟩) = (3, 3, false) := by
    rw [cc_mul s2_mem_Pw s2_mem_Pw, cc_s2]; decide
  have hs3 : cc ((⟨g₅, g₆, true⟩ : WrE) * ⟨g₅, g₆, true⟩ * ⟨g₅, g₆, true⟩) = (2, 1, true) := by
    rw [cc_mul (Pw.mul_mem s2_mem_Pw s2_mem_Pw) s2_mem_Pw, hs2, cc_s2]; decide
  constructor
  · intro hx
    have hle : X2 ≤ preimg U2 U2_zero U2_mul U2_inv := by
      rw [X2, Subgroup.closure_le]
      rintro y (hy | rfl)
      · refine ⟨N0w_le_Pw hy, ?_⟩
        rw [(mem_N0w_iff_cc (N0w_le_Pw hy)).1 hy]
        exact U2_zero
      · exact ⟨s2_mem_Pw, by rw [cc_s2]; simp [U2]⟩
    exact hle hx
  · rintro ⟨hxP, hxU⟩
    simp only [U2, Set.mem_insert_iff, Set.mem_singleton_iff] at hxU
    rcases hxU with h | h | h | h
    · exact hN ((mem_N0w_iff_cc hxP).2 h)
    · exact mem_of_cc_eq hN hxP (X2.mul_mem hs hs) (Pw.mul_mem s2_mem_Pw s2_mem_Pw)
        (h.trans hs2.symm)
    · exact mem_of_cc_eq hN hxP hs s2_mem_Pw (h.trans cc_s2.symm)
    · exact mem_of_cc_eq hN hxP (X2.mul_mem (X2.mul_mem hs hs) hs)
        (Pw.mul_mem (Pw.mul_mem s2_mem_Pw s2_mem_Pw) s2_mem_Pw) (h.trans hs3.symm)

theorem classify_of_codes {X : Subgroup WrE} (hXP : X ≤ Pw) (hN : N0w ≤ X)
    (hsw : ∃ g ∈ X, g.e = true) (h4 : ∀ x ∈ X, x.e = true → IsC4 (cc x))
    (hUC : codeSet X ≠ UC) : X = X1 ∨ X = X2 := by
  have hcl := codes_classify (codeSet X) codeSet_zero
    (fun c hc d hd => codeSet_mul hXP hc hd)
    (by obtain ⟨g, hg, he⟩ := hsw; exact ⟨cc g, ⟨g, hg, rfl⟩, he⟩)
    (by rintro c ⟨x, hx, rfl⟩ hc; exact h4 x hx hc)
  rcases hcl with h | h | h
  · left
    ext x
    rw [mem_iff_cc hXP hN, h, mem_X1_iff]
  · right
    ext x
    rw [mem_iff_cc hXP hN, h, mem_X2_iff]
  · exact absurd h hUC

end CFSG.ComponentClassification.GrSLit.L34Tw
