module

public import CFSG.Quasithin.H13.L32NLem14332l
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem14332k

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open scoped commutatorElement

namespace L14332

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V V₂ : Subgroup G} {g a : G}
  {D : HatModelU (fsuU T V)} {K : Subgroup G}

theorem eq_of_le_centerOf_F4 (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) (h1222 : Stmt12_2_2_F4)
    (C : Ctx14332 G T L V V₂ g a D) (hii : Case14323ii T V g D)
    (hd : Module.finrank (ZMod 2) D.V = 4) (h4 : Nat.card ↥(centerOf (fsuU T V)) = 4)
    (hQ : pCoreOf 2 (l32nH T V) = l32nCHat T V) (hK : K ∈ cComp (l32nH T V))
    {A B : Subgroup G} (hA : fsuV1 T V ≤ A) (hB : fsuV1 T V ≤ B) (hBU : B ≤ fsuU T V)
    (hKB : K ≤ Subgroup.normalizer (B : Set G)) (hAB : A ⊓ B = fsuV1 T V)
    (hABU : A ⊔ B = fsuU T V) (hAZ : A ≤ centerOf (fsuU T V)) : A = fsuV1 T V := by
  by_contra hAV
  have hKH : K ≤ l32nH T V := le_of_mem_cComp hK

  have hAZeq : A = centerOf (fsuU T V) := by
    refine Subgroup.eq_of_le_of_card_ge hAZ ?_
    have h1 := Subgroup.card_dvd_of_le hAZ
    have h2 := Subgroup.card_dvd_of_le hA
    rw [h4] at h1
    rw [C.card_V1] at h2
    rw [h4]
    have hne : Nat.card ↥A ≠ 2 := fun h => hAV (Subgroup.eq_of_le_of_card_ge hA
      (by rw [h, C.card_V1])).symm
    have h0 : 0 < Nat.card ↥A := Nat.card_pos
    have h3 : Nat.card ↥A ≤ 4 := Nat.le_of_dvd (by norm_num) h1
    obtain ⟨m, hm⟩ := h2
    interval_cases hc : Nat.card ↥A <;> omega

  have hZB : centerOf (fsuU T V) ⊔ B = fsuU T V := by rw [← hAZeq]; exact hABU
  have hcl : centerOf (fsuU T V) ⊔ B =
      Subgroup.closure ((centerOf (fsuU T V) : Set G) ∪ (B : Set G)) := by
    rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]
  have hcomm : ∀ u ∈ fsuU T V, ∀ k ∈ K, ⁅u, k⁆ ∈ B := by
    intro u hu
    rw [← hZB, hcl] at hu
    refine Subgroup.closure_induction (p := fun u _ => ∀ k ∈ K, ⁅u, k⁆ ∈ B) ?_ ?_ ?_ ?_ hu
    · rintro u (hu | hu) k hk
      · have h1 := C.conj_zU_mem h4 k (hKH hk) u hu
        have e : ⁅u, k⁆ = (k * u * k⁻¹ * u⁻¹)⁻¹ := by rw [commutatorElement_def]; group
        rw [e]
        exact hB (inv_mem h1)
      · have h1 : k * u⁻¹ * k⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp (hKB hk) _).mp (inv_mem hu)
        rw [commutatorElement_def, mul_assoc, mul_assoc, ← mul_assoc k]
        exact mul_mem hu h1
    · intro k _
      rw [commutatorElement_def, one_mul, inv_one, mul_one, mul_inv_cancel]
      exact B.one_mem
    · intro x y hx hy ihx ihy k hk
      have hxU : x ∈ fsuU T V := by
        rw [← hcl, hZB] at hx
        exact hx
      have h1 : x * ⁅y, k⁆ * x⁻¹ ∈ B :=
        (Subgroup.mem_normalizer_iff.mp (le_normalizer_of_V1_le C hB hBU hxU) _).mp (ihy k hk)
      have e : ⁅x * y, k⁆ = x * ⁅y, k⁆ * x⁻¹ * ⁅x, k⁆ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact mul_mem h1 (ihx k hk)
    · intro x hx ihx k hk
      have hxU : x ∈ fsuU T V := by
        rw [← hcl, hZB] at hx
        exact hx
      have h1 : x⁻¹ * ⁅x, k⁆⁻¹ * x⁻¹⁻¹ ∈ B :=
        (Subgroup.mem_normalizer_iff.mp (le_normalizer_of_V1_le C hB hBU (inv_mem hxU)) _).mp
          (inv_mem (ihx k hk))
      have e : ⁅x⁻¹, k⁆ = x⁻¹ * ⁅x, k⁆⁻¹ * x⁻¹⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact h1
  have hUB : fsuU T V ≤ B :=
    (fsuU_le_commutator_F4 h1332 h1334 h1222 C hii hQ hK).trans
      (Subgroup.commutator_le.mpr hcomm)

  have hcard := L32NSet14.card_sup_mul_card_inf (X := A) (N := B)
    (hAZ.trans inf_le_left |>.trans (le_normalizer_of_V1_le C hB hBU))
  rw [hABU, hAB, card_fsuU h4 hd, C.card_V1, hAZeq, h4] at hcard
  have hle := Subgroup.card_le_of_le hUB
  rw [card_fsuU h4 hd] at hle
  omega

theorem isIndecOnSection_F4 (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) (h1222 : Stmt12_2_2_F4)
    (C : Ctx14332 G T L V V₂ g a D) (hii : Case14323ii T V g D)
    (hd : Module.finrank (ZMod 2) D.V = 4) (h4 : Nat.card ↥(centerOf (fsuU T V)) = 4)
    (hQ : pCoreOf 2 (l32nH T V) = l32nCHat T V) (hK : K ∈ cComp (l32nH T V)) :
    IsIndecOnSection K (fsuU T V) (fsuV1 T V) := by
  intro A B hA hB hAU hBU hKA hKB hAB hABU
  have hKH : K ≤ l32nH T V := le_of_mem_cComp hK
  have hirr : ∀ X : Subgroup G, K ≤ Subgroup.normalizer (X : Set G) →
      (D.hat X).toAddSubgroup = ⊥ ∨ (D.hat X).toAddSubgroup = ⊤ := fun X hKX =>
    eq_bot_or_eq_top_of_invariant hii hQ hK _ (hat_invariant hKH hKX)
  rcases hirr A hKA with hA0 | hAt
  · exact Or.inl (eq_of_le_centerOf_F4 h1332 h1334 h1222 C hii hd h4 hQ hK hA hB hBU hKB hAB hABU
      (le_centerOf_of_hat_eq_bot hAU hA0))
  rcases hirr B hKB with hB0 | hBt
  · exact Or.inr (eq_of_le_centerOf_F4 h1332 h1334 h1222 C hii hd h4 hQ hK hB hA hAU hKA
      (by rw [inf_comm]; exact hAB) (by rw [sup_comm]; exact hABU)
      (le_centerOf_of_hat_eq_bot hBU hB0))
  exfalso
  have hA32 := card_ge_of_sup_eq C h4 hd hA hAU (sup_centerOf_eq hAU hAt)
  have hB32 := card_ge_of_sup_eq C h4 hd hB hBU (sup_centerOf_eq hBU hBt)
  have hcard := L32NSet14.card_sup_mul_card_inf (X := A) (N := B)
    (hAU.trans (le_normalizer_of_V1_le C hB hBU))
  rw [hABU, hAB, card_fsuU h4 hd, C.card_V1] at hcard
  nlinarith

theorem comp_of_case_ii_F4 (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) (h1222 : Stmt12_2_2_F4)
    (h12213 : Stmt12_2_13_F4) (h14323 : Lemma14323Rest_F4) (C : Ctx14332 G T L V V₂ g a D)
    (hii : Case14323ii T V g D) (hd : Module.finrank (ZMod 2) D.V = 4)
    (h4 : Nat.card ↥(centerOf (fsuU T V)) = 4) (hQ : pCoreOf 2 (l32nH T V) = l32nCHat T V)
    (hQT : pCoreOf 2 (l32nH T V) ≤ T) :
    ∃ K : Subgroup G, quasithinIsCComponent K (l32nH T V) ∧ l32nH T V = K ⊔ T ∧
      fsuU T V = ⁅pCoreOf 2 K, K⁆ ∧ IsIndecOnSection K (fsuU T V) (fsuV1 T V) := by
  obtain ⟨K, hK⟩ := exists_mem_cComp hii
  exact ⟨K, hK, eq_sup_T C hii hQ hQT hK,
    fsuU_eq_commutator_F4 h1332 h1334 h1222 h12213 h14323 C hii hd hQ hQT hK,
    isIndecOnSection_F4 h1332 h1334 h1222 C hii hd h4 hQ hK⟩

end L14332

end CFSG.Quasithin.H13
