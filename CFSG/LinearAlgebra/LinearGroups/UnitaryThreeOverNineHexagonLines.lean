module

public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutionsOrthogonal

public section

namespace CFSG.LinearGroups.UnitaryThreeOverNine

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.Assembly.LowTwoRank

variable {F : Type} [Field F]

@[expose] def Orth (a b : NonisoLine F) : Prop :=
  ∀ x ∈ a.1, ∀ y ∈ b.1, ∑ j, x j ^ 3 * y j = 0

abbrev HexLine (F : Type) [Field F] : Type :=
  {T : Finset (NonisoLine F) // T.card = 3 ∧ ∀ a ∈ T, ∀ b ∈ T, a ≠ b → Orth a b}

theorem orth_iff (h : UnitaryFieldData 3 1 F) (a b : NonisoLine F) :
    Orth a b ↔ ∀ x ∈ a.1, ∀ y ∈ b.1, gramForm h (1 : Matrix (Fin 3) (Fin 3) F) x y = 0 := by
  simp only [Orth, gramForm_one_apply]

theorem Orth.symm (h : UnitaryFieldData 3 1 F) {a b : NonisoLine F} (hab : Orth a b) :
    Orth b a := by
  rw [orth_iff h] at hab ⊢
  intro x hx y hy
  rw [← bar_gramForm, hab y hy x hx, map_zero]

theorem not_orth_self (a : NonisoLine F) : ¬ Orth a a := fun hO =>
  a.gen_norm (hO _ a.gen_mem _ a.gen_mem)

theorem Orth.ne {a b : NonisoLine F} (hab : Orth a b) : a ≠ b := by
  rintro rfl
  exact not_orth_self a hab

theorem orth_of_mem (T : HexLine F) {a b : NonisoLine F} (ha : a ∈ T.1) (hb : b ∈ T.1)
    (hab : a ≠ b) : Orth a b :=
  T.2.2 a ha b hb hab

theorem existsUnique_orth (hF : Nat.card F = 9) {a b : NonisoLine F} (hab : a ≠ b)
    (horth : Orth a b) : ∃! c : NonisoLine F, Orth a c ∧ Orth b c := by
  have h := unitaryFieldData_of_card hF
  obtain ⟨T, hT, -⟩ := exists_tauLine_mul_eq (h := h) (hF := hF) hab ((orth_iff h a b).mp horth)
  have hmemT : ∀ y, y ∈ T.1 ↔
      ∀ x ∈ a.1 ⊔ b.1, gramForm h (1 : Matrix (Fin 3) (Fin 3) F) x y = 0 := fun y => by
    rw [← SetLike.mem_coe, hT, Set.mem_ofPred_eq]
  refine ⟨T, ⟨?_, ?_⟩, fun d ⟨had, hbd⟩ => ?_⟩
  · rw [orth_iff h]
    intro x hx y hy
    exact (hmemT y).mp hy x (Submodule.mem_sup_left hx)
  · rw [orth_iff h]
    intro x hx y hy
    exact (hmemT y).mp hy x (Submodule.mem_sup_right hx)
  · have hle : d.1 ≤ T.1 := by
      intro y hy
      rw [hmemT]
      intro x hx
      obtain ⟨xa, hxa, xb, hxb, rfl⟩ := Submodule.mem_sup.mp hx
      rw [map_add, LinearMap.add_apply, (orth_iff h a d).mp had xa hxa y hy,
        (orth_iff h b d).mp hbd xb hxb y hy, add_zero]
    exact Subtype.ext (Submodule.eq_of_le_of_finrank_eq hle (by rw [d.2.1, T.2.1]))

theorem exists_mem_ne_ne (T : HexLine F) (a b : NonisoLine F) :
    ∃ y ∈ T.1, y ≠ a ∧ y ≠ b := by
  classical
  by_contra hne
  push Not at hne
  have hsub : T.1 ⊆ {a, b} := fun y hy => by
    rcases eq_or_ne y a with rfl | hya
    · exact Finset.mem_insert_self _ _
    · rw [hne y hy hya]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self b)
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_le_two (a := a) (b := b)
  rw [T.2.1] at h1
  omega

theorem mem_line_iff (hF : Nat.card F = 9) {T : HexLine F} {a b : NonisoLine F} (hab : a ≠ b)
    (ha : a ∈ T.1) (hb : b ∈ T.1) (x : NonisoLine F) :
    x ∈ T.1 ↔ x = a ∨ x = b ∨ (Orth a x ∧ Orth b x) := by
  constructor
  · intro hx
    by_cases hxa : x = a
    · exact Or.inl hxa
    by_cases hxb : x = b
    · exact Or.inr (Or.inl hxb)
    exact Or.inr (Or.inr ⟨orth_of_mem T ha hx (Ne.symm hxa), orth_of_mem T hb hx (Ne.symm hxb)⟩)
  · rintro (rfl | rfl | ⟨hax, hbx⟩)
    · exact ha
    · exact hb
    · obtain ⟨y, hy, hya, hyb⟩ := exists_mem_ne_ne T a b
      obtain ⟨c, -, hc⟩ := existsUnique_orth hF hab (orth_of_mem T ha hb hab)
      have hyc := hc y ⟨orth_of_mem T ha hy (Ne.symm hya), orth_of_mem T hb hy (Ne.symm hyb)⟩
      have hxc := hc x ⟨hax, hbx⟩
      rw [hxc, ← hyc]
      exact hy

theorem eq_of_mem_of_mem (hF : Nat.card F = 9) {a b : NonisoLine F} (hab : a ≠ b)
    {T T' : HexLine F} (ha : a ∈ T.1) (hb : b ∈ T.1) (ha' : a ∈ T'.1) (hb' : b ∈ T'.1) :
    T = T' :=
  Subtype.ext (Finset.ext fun x => by
    rw [mem_line_iff hF hab ha hb, mem_line_iff hF hab ha' hb'])

theorem exists_line (hF : Nat.card F = 9) {a b : NonisoLine F} (horth : Orth a b) :
    ∃ T : HexLine F, a ∈ T.1 ∧ b ∈ T.1 := by
  classical
  have h := unitaryFieldData_of_card hF
  obtain ⟨c, ⟨hac, hbc⟩, -⟩ := existsUnique_orth hF horth.ne horth
  refine ⟨⟨{a, b, c}, ?_, ?_⟩, by simp, by simp⟩
  · rw [Finset.card_eq_three]
    exact ⟨a, b, c, horth.ne, hac.ne, hbc.ne, rfl⟩
  · intro x hx y hy hxy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
    all_goals first
      | exact absurd rfl hxy
      | exact horth
      | exact horth.symm h
      | exact hac
      | exact hac.symm h
      | exact hbc
      | exact hbc.symm h

theorem eq_of_orth (hF : Nat.card F = 9) {a b c : NonisoLine F} {T T' : HexLine F}
    (hab : a ≠ b) (hbc : b ≠ c) (ha : a ∈ T.1) (hb : b ∈ T.1) (hb' : b ∈ T'.1) (hc : c ∈ T'.1)
    (hac : Orth a c) : T = T' := by
  have hcT : c ∈ T.1 :=
    (mem_line_iff hF hab ha hb c).mpr (Or.inr (Or.inr ⟨hac, orth_of_mem T' hb' hc hbc⟩))
  exact eq_of_mem_of_mem hF hbc hb hcT hb' hc

theorem orth_lineAct_iff (hF : Nat.card F = 9) (g : StatedSU 3 3 F) (a b : NonisoLine F) :
    Orth (lineAct hF g a) (lineAct hF g b) ↔ Orth a b := by
  have h := unitaryFieldData_of_card hF
  rw [orth_iff h, orth_iff h, lineAct_val, lineAct_val]
  constructor
  · intro hO x hx y hy
    have := hO _ (Submodule.mem_map_of_mem hx) _ (Submodule.mem_map_of_mem hy)
    rwa [Matrix.toLin'_apply, Matrix.toLin'_apply, isometry_of_mem hF h] at this
  · intro hO x hx y hy
    obtain ⟨x', hx', rfl⟩ := Submodule.mem_map.mp hx
    obtain ⟨y', hy', rfl⟩ := Submodule.mem_map.mp hy
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, isometry_of_mem hF h]
    exact hO x' hx' y' hy'

theorem lineAct_injective (hF : Nat.card F = 9) (g : StatedSU 3 3 F) :
    Function.Injective (lineAct hF g) := fun L M hLM => by
  have := congrArg (lineAct hF g⁻¹) hLM
  rwa [← lineAct_mul, ← lineAct_mul, inv_mul_cancel, lineAct_one, lineAct_one] at this

@[expose] noncomputable def lineActLin (hF : Nat.card F = 9) (g : StatedSU 3 3 F)
    (T : HexLine F) : HexLine F := by
  classical
  exact ⟨T.1.image (lineAct hF g), by
    rw [Finset.card_image_of_injective _ (lineAct_injective hF g), T.2.1], fun x hx y hy hxy => by
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    exact (orth_lineAct_iff hF g a b).mpr (T.2.2 a ha b hb fun hab => hxy (by rw [hab]))⟩

theorem mem_lineActLin (hF : Nat.card F = 9) (g : StatedSU 3 3 F) (T : HexLine F)
    (x : NonisoLine F) : x ∈ (lineActLin hF g T).1 ↔ ∃ a ∈ T.1, lineAct hF g a = x := by
  classical
  exact Finset.mem_image

theorem lineAct_mem_lineActLin (hF : Nat.card F = 9) (g : StatedSU 3 3 F) (T : HexLine F)
    (a : NonisoLine F) : lineAct hF g a ∈ (lineActLin hF g T).1 ↔ a ∈ T.1 := by
  rw [mem_lineActLin]
  constructor
  · rintro ⟨b, hb, hba⟩
    rwa [← lineAct_injective hF g hba]
  · intro ha
    exact ⟨a, ha, rfl⟩

theorem lineActLin_one (hF : Nat.card F = 9) (T : HexLine F) : lineActLin hF 1 T = T :=
  Subtype.ext (Finset.ext fun x => by simp only [mem_lineActLin, lineAct_one, exists_eq_right])

theorem lineActLin_mul (hF : Nat.card F = 9) (g g' : StatedSU 3 3 F) (T : HexLine F) :
    lineActLin hF (g * g') T = lineActLin hF g (lineActLin hF g' T) :=
  Subtype.ext (Finset.ext fun x => by
    simp only [mem_lineActLin, lineAct_mul]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨lineAct hF g' a, ⟨a, ha, rfl⟩, rfl⟩
    · rintro ⟨b, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨a, ha, rfl⟩)

end CFSG.LinearGroups.UnitaryThreeOverNine
