module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.SingleA3.ZTwo.SetupS

public section

namespace CFSG.QuasithinUnique

open CFSG.Quasithin Subgroup ZTwoAux

namespace ZTwoConfig

variable {G : Type} [Group G] [Finite G] {T S U R : Subgroup G} {y x c : G}
  (h : ZTwoConfig T S U R y x c) {z : G}

include h

theorem U_le_S' : U ≤ S := h.U_le

theorem zpowers_y_le_S : zpowers y ≤ S := zpowers_le.mpr h.y_mem

theorem y_not_mem_U : y ∉ U := fun hy => h.y_not_mem_R (h.U_le_R hy)

theorem y_not_mem_U' : y ∉ conjSubgroup U x := fun hy => h.y_not_mem_R (h.U'_le_R hy)

theorem card_zpowers_y : Nat.card (zpowers y) = 2 := by
  rw [Nat.card_zpowers, h.y_order]

theorem mem_zpowers_y {g : G} : g ∈ zpowers y ↔ g = 1 ∨ g = y :=
  mem_zpowers_iff_of_sq_eq_one h.y_sq

theorem card_sup_zpowers_y {A : Subgroup G} (hAS : A ≤ S) (hy : y ∉ A) :
    Nat.card ↥(A ⊔ zpowers y) = 2 * Nat.card A := by
  have hle : A ≤ normalizer ((zpowers y : Subgroup G) : Set G) := fun a ha =>
    mem_normalizer_zpowers_of_comm (h.y_comm a (hAS ha))
  have hinf : A ⊓ zpowers y = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_bot]
    rcases h.mem_zpowers_y.mp hg.2 with e | e
    · exact e
    · exact absurd (e ▸ hg.1) hy
  have hh := A3Gen.card_sup_mul_card_inf_of_le_normalizer' hle
  rw [hinf, Subgroup.card_bot, h.card_zpowers_y] at hh
  omega

theorem card_Q : Nat.card ↥(U ⊔ zpowers y) = 8 := by
  rw [h.card_sup_zpowers_y h.U_le h.y_not_mem_U, h.card_U]

theorem card_Q' : Nat.card ↥(conjSubgroup U x ⊔ zpowers y) = 8 := by
  rw [h.card_sup_zpowers_y h.U'_le h.y_not_mem_U', h.card_U']

theorem mem_sup_zpowers_y {A : Subgroup G} (hAS : A ≤ S) {g : G} :
    g ∈ A ⊔ zpowers y ↔ ∃ a ∈ A, g = a ∨ g = a * y := by
  have hle : A ≤ normalizer ((zpowers y : Subgroup G) : Set G) := fun a ha =>
    mem_normalizer_zpowers_of_comm (h.y_comm a (hAS ha))
  rw [A3Dich.mem_sup_iff_of_le_normalizer hle]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    rcases h.mem_zpowers_y.mp hb with rfl | rfl
    · exact ⟨a, ha, Or.inl (by simp)⟩
    · exact ⟨a, ha, Or.inr rfl⟩
  · rintro ⟨a, ha, h1 | h1⟩ <;> rw [h1]
    · exact ⟨a, ha, 1, one_mem _, by simp⟩
    · exact ⟨a, ha, y, mem_zpowers y, rfl⟩

theorem exp_sup_zpowers_y {A : Subgroup G} (hAS : A ≤ S) (hA : ∀ a ∈ A, a ^ 2 = 1) :
    ∀ g ∈ A ⊔ zpowers y, g ^ 2 = 1 := by
  intro g hg
  obtain ⟨a, ha, h1 | h1⟩ := (h.mem_sup_zpowers_y hAS).mp hg
  · rw [h1]
    exact hA a ha
  · rw [h1]
    have hc : y * a = a * y := (h.y_comm a (hAS ha)).symm
    have hy : y * y = 1 := by simpa [pow_two] using h.y_sq
    have ha2 : a * a = 1 := by simpa [pow_two] using hA a ha
    rw [pow_two]
    calc a * y * (a * y) = a * (y * a) * y := by group
      _ = a * (a * y) * y := by rw [hc]
      _ = (a * a) * (y * y) := by group
      _ = 1 := by rw [ha2, hy, one_mul]

variable (hd : D8Data R U (conjSubgroup U x) z)

include hd

theorem eq_Q_or_Q' {E : Subgroup G} (hES : E ≤ S) (hE8 : Nat.card E = 8)
    (hEexp : ∀ g ∈ E, g ^ 2 = 1) :
    E = U ⊔ zpowers y ∨ E = conjSubgroup U x ⊔ zpowers y := by
  have hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb => comm_of_exp_two hEexp ha hb
  have hyE : y ∈ E := by
    by_contra hyE
    have hy_norm : y ∈ normalizer (E : Set G) :=
      A3Dich.mem_normalizer_of_forall_comm fun b hb => (h.y_comm b (hES hb)).symm
    have hle : zpowers y ≤ normalizer (E : Set G) := zpowers_le.mpr hy_norm
    have hinf : zpowers y ⊓ E = ⊥ := by
      rw [eq_bot_iff]
      intro g hg
      rw [Subgroup.mem_bot]
      rcases h.mem_zpowers_y.mp hg.1 with e | e
      · exact e
      · exact absurd (e ▸ hg.2) hyE
    have hprod := A3Gen.card_sup_mul_card_inf_of_le_normalizer' hle
    rw [hinf, Subgroup.card_bot, h.card_zpowers_y, hE8] at hprod
    have hSE : zpowers y ⊔ E = S := by
      refine Subgroup.eq_of_le_of_card_ge (sup_le h.zpowers_y_le_S hES) ?_
      have := h.card_S
      omega
    have hRS : ∀ r ∈ R, ∃ b ∈ E, r = b ∨ r = y * b := by
      intro r hr
      have hr' : r ∈ zpowers y ⊔ E := hSE ▸ h.R_le hr
      obtain ⟨a, ha, b, hb, rfl⟩ := (A3Dich.mem_sup_iff_of_le_normalizer hle).mp hr'
      rcases h.mem_zpowers_y.mp ha with rfl | rfl
      · exact ⟨b, hb, Or.inl (by simp)⟩
      · exact ⟨b, hb, Or.inr rfl⟩
    obtain ⟨r, hr, s, hs, hrs⟩ := h.R_nonabelian
    obtain ⟨b, hb, hrb⟩ := hRS r hr
    obtain ⟨b', hb', hsb⟩ := hRS s hs
    apply hrs
    have hyb : y * b = b * y := (h.y_comm b (hES hb)).symm
    have hyb' : y * b' = b' * y := (h.y_comm b' (hES hb')).symm
    have hbb := hEc b hb b' hb'
    rcases hrb with rfl | rfl <;> rcases hsb with rfl | rfl
    · exact hbb
    · calc r * (y * b') = (r * y) * b' := by rw [mul_assoc]
        _ = (y * r) * b' := by rw [← hyb]
        _ = y * (r * b') := by rw [mul_assoc]
        _ = y * (b' * r) := by rw [hbb]
        _ = (y * b') * r := by rw [mul_assoc]
    · calc y * b * s = y * (b * s) := by rw [mul_assoc]
        _ = y * (s * b) := by rw [hbb]
        _ = (y * s) * b := by rw [mul_assoc]
        _ = (s * y) * b := by rw [← hyb']
        _ = s * (y * b) := by rw [mul_assoc]
    · calc y * b * (y * b') = y * (b * (y * b')) := by rw [mul_assoc]
        _ = y * ((b * y) * b') := by rw [mul_assoc]
        _ = y * ((y * b) * b') := by rw [hyb]
        _ = y * (y * (b * b')) := by rw [mul_assoc]
        _ = y * (y * (b' * b)) := by rw [hbb]
        _ = y * ((y * b') * b) := by rw [mul_assoc]
        _ = y * ((b' * y) * b) := by rw [hyb']
        _ = y * (b' * (y * b)) := by rw [mul_assoc]
        _ = (y * b') * (y * b) := by rw [mul_assoc]
  have hER : ∀ r ∈ E, r ∈ R → r ∈ U ∨ r ∈ conjSubgroup U x := fun r hr hrR =>
    hd.mem_U_or_V_of_sq hrR (hEexp r hr)
  have hdec : ∀ g ∈ E, ∃ r ∈ E, r ∈ R ∧ (g = r ∨ g = r * y) := by
    intro g hg
    obtain ⟨r, hr, h1 | h1⟩ := (h.mem_S_iff).mp (hES hg)
    · exact ⟨r, h1 ▸ hg, hr, Or.inl h1⟩
    · refine ⟨r, ?_, hr, Or.inr h1⟩
      have hy : y * y = 1 := by simpa [pow_two] using h.y_sq
      have : r = g * y := by rw [h1, mul_assoc, hy, mul_one]
      rw [this]
      exact E.mul_mem hg hyE
  by_cases hEU : ∀ r ∈ E, r ∈ R → r ∈ U
  · left
    have hEQ : E ≤ U ⊔ zpowers y := by
      intro g hg
      obtain ⟨r, hrE, hrR, hgr⟩ := hdec g hg
      refine (h.mem_sup_zpowers_y h.U_le).mpr ⟨r, hEU r hrE hrR, hgr⟩
    exact Subgroup.eq_of_le_of_card_ge hEQ (by rw [h.card_Q, hE8])
  · right
    by_cases hEV : ∀ r ∈ E, r ∈ R → r ∈ conjSubgroup U x
    · have hEQ : E ≤ conjSubgroup U x ⊔ zpowers y := by
        intro g hg
        obtain ⟨r, hrE, hrR, hgr⟩ := hdec g hg
        refine (h.mem_sup_zpowers_y h.U'_le).mpr ⟨r, hEV r hrE hrR, hgr⟩
      exact Subgroup.eq_of_le_of_card_ge hEQ (by rw [h.card_Q', hE8])
    · exfalso
      push Not at hEU hEV
      obtain ⟨r, hrE, hrR, hrU⟩ := hEU
      obtain ⟨q, hqE, hqR, hqV⟩ := hEV
      have hrV : r ∈ conjSubgroup U x := (hER r hrE hrR).resolve_left hrU
      have hqU : q ∈ U := (hER q hqE hqR).resolve_right hqV
      have hrZ : r ∉ zpowers z := fun hz => hrU (hd.zpowers_le_U hz)
      have hqZ : q ∉ zpowers z := fun hz => hqV (hd.zpowers_le_V hz)
      exact hd.noncomm hqU hqZ hrV hrZ (hEc q hqE r hrE)

end ZTwoConfig

end CFSG.QuasithinUnique
