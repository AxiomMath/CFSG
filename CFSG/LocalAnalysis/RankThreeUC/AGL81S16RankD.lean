module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16RankC

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.ClassicalGroups.Unitary Matrix
open CFSG.LieType.Universal.Unitary (SUid)

section Struct2

variable {F : Type} [Field F] [Finite F] {σ : F ≃+* F}

theorem card_le_two_pow_four (hσ : IsUnitaryInvolution σ) {E : Subgroup (SUid σ 4)}
    (hE2 : ∀ a ∈ E, a * a = 1) (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) {n : ℕ} (hn : 1 ≤ n)
    (hF : Nat.card F = (2 ^ n) ^ 2) : Nat.card ↥E ≤ 2 ^ (4 * n) := by
  rcases card_cases hσ hE2 hEc hn hF with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩
  · exact h.trans Nat.one_le_two_pow
  · exact h.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
  · exact h
  · exact h.trans (Nat.pow_le_pow_right (by norm_num) (by omega))

theorem finrank_commSp_eq_two_of_card_eq (hσ : IsUnitaryInvolution σ) {E : Subgroup (SUid σ 4)}
    (hE2 : ∀ a ∈ E, a * a = 1) (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) {n : ℕ} (hn : 1 ≤ n)
    (hF : Nat.card F = (2 ^ n) ^ 2) (hcard : Nat.card ↥E = 2 ^ (4 * n)) :
    Module.finrank F ↥(commSp E) = 2 := by
  have h1 : 2 ^ (4 * n) > 1 := Nat.one_lt_two_pow (by omega)
  have hlt1 : 2 ^ n < 2 ^ (4 * n) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hlt3 : 2 ^ (3 * n) < 2 ^ (4 * n) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  rcases card_cases hσ hE2 hEc hn hF with ⟨_, h⟩ | ⟨_, h⟩ | ⟨hu, _⟩ | ⟨_, h⟩
  · omega
  · omega
  · exact hu
  · omega

theorem two_le_finrank_commSp_of_card_ge (hσ : IsUnitaryInvolution σ) {E : Subgroup (SUid σ 4)}
    (hE2 : ∀ a ∈ E, a * a = 1) (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) {n : ℕ} (hn : 1 ≤ n)
    (hF : Nat.card F = (2 ^ n) ^ 2) (hcard : 2 ^ (2 * n) ≤ Nat.card ↥E) :
    2 ≤ Module.finrank F ↥(commSp E) := by
  have h1 : 1 < 2 ^ (2 * n) := Nat.one_lt_two_pow (by omega)
  have hlt1 : 2 ^ n < 2 ^ (2 * n) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  rcases card_cases hσ hE2 hEc hn hF with ⟨_, h⟩ | ⟨_, h⟩ | ⟨hu, _⟩ | ⟨hu, _⟩
  · omega
  · omega
  · omega
  · omega

theorem herm_eq_zero_of_span {G : Set (Fin 4 → F)} (hG : ∀ g ∈ G, ∀ g' ∈ G, herm σ g g' = 0) :
    ∀ u ∈ Submodule.span F G, ∀ u' ∈ Submodule.span F G, herm σ u u' = 0 := by
  intro u hu u' hu'
  induction hu using Submodule.span_induction with
  | mem g hg =>
    induction hu' using Submodule.span_induction with
    | mem g' hg' => exact hG g hg g' hg'
    | zero => exact herm_zero_right σ g
    | add v v' _ _ h1 h2 => rw [herm_add_right, h1, h2, add_zero]
    | smul c v _ h1 => rw [herm_smul_right, h1, mul_zero]
  | zero => exact herm_zero_left σ u'
  | add v v' _ _ h1 h2 => rw [herm_add_left, h1, h2, add_zero]
  | smul c v _ h1 => rw [herm_smul_left, h1, mul_zero]

theorem commSp_le_fixSp_of_finrank_eq_two (hσ : IsUnitaryInvolution σ) (h2 : (2 : F) = 0)
    {E : Subgroup (SUid σ 4)} (hE2 : ∀ a ∈ E, a * a = 1)
    (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hu : Module.finrank F ↥(commSp E) = 2) :
    commSp E ≤ fixSp E := by
  by_contra hnle
  obtain ⟨b, hb, x, hy⟩ : ∃ b ∈ E, ∃ x, b • x - x ∉ fixSp E := by
    by_contra hcon
    push_neg at hcon
    apply hnle
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨b, hb, x, rfl⟩
    exact hcon b hb x
  obtain ⟨a, ha, hay⟩ : ∃ a ∈ E, a • (b • x - x) ≠ b • x - x := by
    by_contra hcon
    push_neg at hcon
    exact hy (mem_fixSp.mpr hcon)
  set y := b • x - x with hydef
  set z := a • y - y with hzdef
  have hz0 : z ≠ 0 := fun h => hay (sub_eq_zero.mp h)
  have hby : b • y = y := smul_nil (hE2 b hb) h2 x
  have haz : a • z = z := smul_nil (hE2 a ha) h2 y
  have hbz : b • z = z := by
    have : b • (a • y) = a • y := by
      rw [← mul_smul, hEc b hb a ha, mul_smul, hby]
    simp only [hzdef, smul_sub, this, hby]
  have hyy : herm σ y y = 0 := by
    have := herm_nil (hE2 b hb) x y
    rw [sub_eq_zero.mpr hby, herm_zero_right] at this
    exact this
  have hzz : herm σ z z = 0 := by
    have := herm_nil (hE2 a ha) y z
    rw [sub_eq_zero.mpr haz, herm_zero_right] at this
    exact this
  have hyz : herm σ y z = 0 := by
    have := herm_nil (hE2 b hb) x z
    rw [sub_eq_zero.mpr hbz, herm_zero_right] at this
    exact this
  have hzy : herm σ z y = 0 := by rw [herm_conj σ hσ.invol y z, hyz, map_zero]
  have hli : LinearIndependent F ![y, z] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 : a • (s • y + t • z) - (s • y + t • z) = s • z := by
      have hay' : a • y = z + y := by rw [hzdef]; abel
      rw [smul_add, smul_comm a s y, smul_comm a t z, haz, hay', smul_add]
      abel
    rw [hst, smul_zero, sub_zero] at h1
    have hs : s = 0 := by
      rcases smul_eq_zero.mp h1.symm with h | h
      · exact h
      · exact absurd h hz0
    subst hs
    rw [zero_smul, zero_add] at hst
    exact ⟨rfl, by
      rcases smul_eq_zero.mp hst with h | h
      · exact h
      · exact absurd h hz0⟩
  have hspan : Submodule.span F (Set.range ![y, z]) = commSp E := by
    apply Submodule.eq_of_le_of_finrank_eq
    · refine Submodule.span_le.mpr ?_
      rintro _ ⟨i, rfl⟩
      fin_cases i
      · exact sub_mem_commSp hb x
      · exact sub_mem_commSp ha y
    · rw [hu, finrank_span_eq_card hli]
      simp
  have hti : ∀ u ∈ commSp E, ∀ u' ∈ commSp E, herm σ u u' = 0 := by
    rw [← hspan]
    refine herm_eq_zero_of_span ?_
    rintro g ⟨i, rfl⟩ g' ⟨j, rfl⟩
    fin_cases i <;> fin_cases j <;> simpa [hyy, hyz, hzy, hzz]
  have hyfix : y ∈ fixSp E := by
    rw [fixSp_eq_horth hσ hE2]
    exact mem_horth.mpr fun u hu => hti u hu y (sub_mem_commSp hb x)
  exact hy hyfix

def PW (W : Submodule F (Fin 4 → F)) : Subgroup (SUid σ 4) where
  carrier := {g | (∀ x, g • x - x ∈ W) ∧ ∀ w ∈ W, g • w = w}
  mul_mem' := fun {g g'} hg hg' => by
    refine ⟨fun x => ?_, fun w hw => ?_⟩
    · have h1 := hg.1 (g' • x)
      have h2 := hg'.1 x
      have := W.add_mem h1 h2
      rw [mul_smul]
      simpa using this
    · rw [mul_smul, hg'.2 w hw, hg.2 w hw]
  one_mem' := ⟨fun x => by simp, fun w _ => one_smul _ _⟩
  inv_mem' := fun {g} hg => by
    refine ⟨fun x => ?_, fun w hw => ?_⟩
    · have h1 := hg.1 (g⁻¹ • x)
      rw [smul_inv_smul] at h1
      have := W.neg_mem h1
      simpa using this
    · have := hg.2 w hw
      rw [inv_smul_eq_iff]
      exact this.symm

theorem mem_PW {W : Submodule F (Fin 4 → F)} {g : SUid σ 4} :
    g ∈ PW W ↔ (∀ x, g • x - x ∈ W) ∧ ∀ w ∈ W, g • w = w := Iff.rfl

theorem PW_sq (h2 : (2 : F) = 0) {W : Submodule F (Fin 4 → F)} {g : SUid σ 4}
    (hg : g ∈ PW W) : g * g = 1 := by
  refine ext_smul σ fun x => ?_
  have hw : g • x - x ∈ W := hg.1 x
  have hfix := hg.2 _ hw
  have h3 : g • g • x = g • x + (g • x - x) := by
    have : g • x = x + (g • x - x) := by abel
    conv_lhs => rw [this]
    rw [smul_add, hfix]
  rw [mul_smul, h3, one_smul]
  have := neg_eq_self_vec h2 (g • x - x)
  rw [← sub_eq_zero]
  calc g • x + (g • x - x) - x = (g • x - x) + (g • x - x) := by abel
    _ = 0 := by rw [← two_smul F, h2, zero_smul]

theorem PW_comm {W : Submodule F (Fin 4 → F)} {g g' : SUid σ 4}
    (hg : g ∈ PW W) (hg' : g' ∈ PW W) : g * g' = g' * g := by
  refine ext_smul σ fun x => ?_
  have h1 : g • x - x ∈ W := hg.1 x
  have h2 : g' • x - x ∈ W := hg'.1 x
  have e1 : g • g' • x = x + (g' • x - x) + (g • x - x) := by
    have : g' • x = x + (g' • x - x) := by abel
    conv_lhs => rw [this]
    rw [smul_add, hg.2 _ h2]
    abel
  have e2 : g' • g • x = x + (g • x - x) + (g' • x - x) := by
    have : g • x = x + (g • x - x) := by abel
    conv_lhs => rw [this]
    rw [smul_add, hg'.2 _ h1]
    abel
  rw [mul_smul, mul_smul, e1, e2]
  abel

theorem eq_PW_of_card_eq (hσ : IsUnitaryInvolution σ) (h2 : (2 : F) = 0)
    {E : Subgroup (SUid σ 4)} (hE2 : ∀ a ∈ E, a * a = 1)
    (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) {n : ℕ} (hn : 1 ≤ n)
    (hF : Nat.card F = (2 ^ n) ^ 2) (hcard : Nat.card ↥E = 2 ^ (4 * n)) :
    Module.finrank F ↥(commSp E) = 2 ∧ commSp E = fixSp E ∧ E = PW (commSp E) := by
  have hu := finrank_commSp_eq_two_of_card_eq hσ hE2 hEc hn hF hcard
  have hle := commSp_le_fixSp_of_finrank_eq_two hσ h2 hE2 hEc hu
  have hsum := finrank_commSp_add_finrank_fixSp hσ hE2
  have heq : commSp E = fixSp E :=
    Submodule.eq_of_le_of_finrank_eq hle (by omega)
  refine ⟨hu, heq, ?_⟩
  have hEP : E ≤ PW (commSp E) := fun a ha =>
    ⟨fun x => sub_mem_commSp ha x, fun w hw => mem_fixSp.mp (heq ▸ hw) a ha⟩
  have hPcard : Nat.card ↥(PW (commSp E)) ≤ 2 ^ (4 * n) :=
    card_le_two_pow_four hσ (fun g hg => PW_sq h2 hg) (fun g hg g' hg' => PW_comm hg hg') hn hF
  exact Subgroup.eq_of_le_of_card_ge hEP (by rw [hcard]; exact hPcard)

end Struct2

end CFSG.LocalAnalysis.RankThreeUC
