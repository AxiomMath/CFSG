module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84G3BW
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84G3AB
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84G3AG

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G}
  {E Y1 Y2 T T1 T2 V1 V2 F1 F2 : Subgroup G}

private lemma sec8t84g_gu_map_cent (c : G ≃* G) (y : G) :
    (centralizer ({y} : Set G)).map c.toMonoidHom = centralizer ({c y} : Set G) := by
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff,
    MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨a, ha, rfl⟩
    rw [← map_mul, ← map_mul, ha]
  · intro hx
    refine ⟨c.symm x, ?_, c.apply_symm_apply x⟩
    apply c.injective
    rw [map_mul, map_mul, c.apply_symm_apply]
    exact hx

theorem sec8t84g_gamma_U (hP : Sec8T84FactP) (hS4 : Sec8T84FactS4)
    (h : Sec8T84GSet G t E Y1 Y2 T T1 T2 V1 V2 F1 F2) {γ : G}
    (hE : E.map (MulAut.conj γ).toMonoidHom = F1 ⊔ F2)
    (hE0 : (F1 ⊔ F2).map (MulAut.conj γ).toMonoidHom = E)
    (hE1 : (V1 ⊔ F2).map (MulAut.conj γ).toMonoidHom = F1 ⊔ V2) :
    (V1 ⊔ F1).map (MulAut.conj γ).toMonoidHom = V1 ⊔ F1 ∧
      (V2 ⊔ F2).map (MulAut.conj γ).toMonoidHom = V2 ⊔ F2 ∧
      V1.map (MulAut.conj γ).toMonoidHom = F1 ∧ F1.map (MulAut.conj γ).toMonoidHom = V1 ∧
      V2.map (MulAut.conj γ).toMonoidHom = F2 ∧ F2.map (MulAut.conj γ).toMonoidHom = V2 := by
  set c : G ≃* G := MulAut.conj γ with hc
  have hinj : Function.Injective c.toMonoidHom := c.injective
  have hmapinj : Function.Injective (Subgroup.map c.toMonoidHom) :=
    Subgroup.map_injective hinj
  obtain ⟨hQn, hOn, hWn⟩ := sec8t84g3a_gamma_Q hE hE0
  have hQ : (sec8t84g_Q E (F1 ⊔ F2)).map c.toMonoidHom = sec8t84g_Q E (F1 ⊔ F2) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hQn
  have hO : (oddCoreIn (sec8t84g_Q E (F1 ⊔ F2))).map c.toMonoidHom =
      oddCoreIn (sec8t84g_Q E (F1 ⊔ F2)) := Subgroup.mem_normalizer_iff_map_conj_eq.mp hOn
  have hW : (E ⊔ (F1 ⊔ F2)).map c.toMonoidHom = E ⊔ (F1 ⊔ F2) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hWn
  obtain ⟨hc1, hc2⟩ := sec8t84g3a_U_card h.D
  have hUinf := sec8t84g3a_U_inf h.D
  have hWeq := sec8t84g3a_W_eq h.D
  obtain ⟨hU1E, hU1E0, hU1E1⟩ := sec8t84g3a_U1_inf h.D
  obtain ⟨hU2E, hU2E0, hU2E2⟩ := sec8t84g3a_U2_inf h.D
  have hne := sec8t84g3a_F2_ne_V2 h.D
  have hU12 : V1 ⊔ F1 ≠ V2 ⊔ F2 := by
    intro heq
    rw [heq, inf_idem] at hUinf
    rw [hUinf, Subgroup.card_bot] at hc2
    omega
  have key : ∀ y ∈ sec8t84g_Q E (F1 ⊔ F2),
      (∃ k : ℕ, y ^ (3 ^ k) ∈ oddCoreIn (sec8t84g_Q E (F1 ⊔ F2))) →
      ((E ⊔ (F1 ⊔ F2)) ⊓ centralizer ({y} : Set G)).map c.toMonoidHom = ⊥ ∨
        ((E ⊔ (F1 ⊔ F2)) ⊓ centralizer ({y} : Set G)).map c.toMonoidHom = V1 ⊔ F1 ∨
        ((E ⊔ (F1 ⊔ F2)) ⊓ centralizer ({y} : Set G)).map c.toMonoidHom = V2 ⊔ F2 ∨
        ((E ⊔ (F1 ⊔ F2)) ⊓ centralizer ({y} : Set G)).map c.toMonoidHom = E ⊔ (F1 ⊔ F2) := by
    rintro y hy ⟨k, hk⟩
    have hy' : c y ∈ sec8t84g_Q E (F1 ⊔ F2) := by
      rw [← hQ]
      exact Subgroup.mem_map_of_mem c.toMonoidHom hy
    have hk' : (c y) ^ (3 ^ k) ∈ oddCoreIn (sec8t84g_Q E (F1 ⊔ F2)) := by
      rw [← map_pow, ← hO]
      exact Subgroup.mem_map_of_mem c.toMonoidHom hk
    have := sec8t84g3b_cent_W hP hS4 h hy' ⟨k, hk'⟩
    rwa [Subgroup.map_inf _ _ _ hinj, hW, sec8t84g_gu_map_cent]
  have cls : ∀ X : Subgroup G, Nat.card X = 64 →
      (X = ⊥ ∨ X = V1 ⊔ F1 ∨ X = V2 ⊔ F2 ∨ X = E ⊔ (F1 ⊔ F2)) →
      X = V1 ⊔ F1 ∨ X = V2 ⊔ F2 := by
    intro X hX hmem
    rcases hmem with rfl | rfl | rfl | rfl
    · rw [Subgroup.card_bot] at hX
      omega
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exfalso
      have h1 : V1 ⊔ F1 = E ⊔ (F1 ⊔ F2) :=
        Subgroup.eq_of_le_of_card_ge (hWeq ▸ le_sup_left) (by rw [hX, hc1])
      have h2 : V2 ⊔ F2 = E ⊔ (F1 ⊔ F2) :=
        Subgroup.eq_of_le_of_card_ge (hWeq ▸ le_sup_right) (by rw [hX, hc2])
      exact hU12 (h1.trans h2.symm)
  obtain ⟨⟨y2, hy2Q, hy2k, hy2⟩, ⟨y1, hy1Q, hy1k, hy1⟩⟩ := sec8t84g3b_exists_U hP hS4 h
  have hk2 : ∃ k : ℕ, y2 ^ (3 ^ k) ∈ oddCoreIn (sec8t84g_Q E (F1 ⊔ F2)) := ⟨1, by simpa using hy2k⟩
  have hk1 : ∃ k : ℕ, y1 ^ (3 ^ k) ∈ oddCoreIn (sec8t84g_Q E (F1 ⊔ F2)) := ⟨1, by simpa using hy1k⟩
  have hU2c : (V2 ⊔ F2).map c.toMonoidHom = V1 ⊔ F1 ∨ (V2 ⊔ F2).map c.toMonoidHom = V2 ⊔ F2 := by
    have := key y2 hy2Q hk2
    rw [hy2] at this
    exact cls _ (by rw [Subgroup.card_map_of_injective hinj, hc2]) this
  have hU1c : (V1 ⊔ F1).map c.toMonoidHom = V1 ⊔ F1 ∨ (V1 ⊔ F1).map c.toMonoidHom = V2 ⊔ F2 := by
    have := key y1 hy1Q hk1
    rw [hy1] at this
    exact cls _ (by rw [Subgroup.card_map_of_injective hinj, hc1]) this
  have hfix1 : (V1 ⊔ F1).map c.toMonoidHom = V1 ⊔ F1 := by
    rcases hU1c with h1 | h1
    · exact h1
    · exfalso
      apply hne
      have e1 : V1.map c.toMonoidHom = V2 := by
        rw [← hU1E1, Subgroup.map_inf _ _ _ hinj, h1, hE1, hU2E2]
      have e2 : V1.map c.toMonoidHom = F2 := by
        rw [← hU1E, Subgroup.map_inf _ _ _ hinj, h1, hE, hU2E0]
      rw [← e2, e1]
  have hfix2 : (V2 ⊔ F2).map c.toMonoidHom = V2 ⊔ F2 := by
    rcases hU2c with h2 | h2
    · exfalso
      apply hU12
      apply hmapinj
      rw [h2, hfix1]
    · exact h2
  refine ⟨hfix1, hfix2, ?_, ?_, ?_, ?_⟩
  · rw [← hU1E, Subgroup.map_inf _ _ _ hinj, hfix1, hE, hU1E0]
  · rw [← hU1E0, Subgroup.map_inf _ _ _ hinj, hfix1, hE0, hU1E]
  · rw [← hU2E, Subgroup.map_inf _ _ _ hinj, hfix2, hE, hU2E0]
  · rw [← hU2E0, Subgroup.map_inf _ _ _ hinj, hfix2, hE0, hU2E]

end CFSG.OddStandard.SmallF3.Omega
