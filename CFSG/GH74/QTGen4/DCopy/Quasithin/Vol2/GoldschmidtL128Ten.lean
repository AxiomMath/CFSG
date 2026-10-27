module

public import CFSG.Quasithin.Vol2.GoldschmidtL128Ten
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec8OneModel
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec8OneThirteenZ

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

namespace L128P

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

theorem commutator_eq_bot_centerOf_i128_F4 (h1222 : Stmt12_2_2_F4) (h12213 : Stmt12_2_13_F4)
    {T L V : Subgroup G} {n : ℕ} {V₁ V₂ : Subgroup G} (hs : Setting1282One G T L V n V₁ V₂)
    {k : G} (hk : k ∈ oTwoUpper (p128 T L V)) (hkN : k ∉ Subgroup.normalizer (V₁ : Set G))
    (hkZ : ∀ z ∈ zU128 V V₁, k⁻¹ * z * k ∈ u128 V V₁) :
    ⁅L, centerOf (i128 T L V V₁)⁆ = ⊥ := by
  obtain ⟨hZ, -, hKC, hLTN⟩ := sup_le_normalizer_centerOf_i128_F4 h1222 h12213 hs hk hkN hkZ
  set J := centerOf (i128 T L V V₁) with hJdef
  have hJZ : J ≤ zU128 V V₁ := le_sup_left.trans hZ.ge
  have hL₁J : lOne L V₁ ≤ Subgroup.centralizer (J : Set G) :=
    (lOne_le_centralizer_centerOf_F4 h1222 h12213 hs hk hkN hkZ).trans (Subgroup.centralizer_le hJZ)
  have hKL : oTwoUpper (p128 T L V) ≤ L := oTwoUpper_p128_le hs.hyp
  have hL₁L : lOne L V₁ ≤ L := (oTwoUpper_le _).trans inf_le_left
  have hKLT : oTwoUpper (p128 T L V) ≤ L ⊔ T := hKL.trans le_sup_left
  have hL₁LT : lOne L V₁ ≤ L ⊔ T := hL₁L.trans le_sup_left

  have hX := L1297.sup_le_of_not_le_normalizer_F4 h1222 hs.hyp hs.v1
    (X := oTwoUpper (p128 T L V) ⊔ lOne L V₁ ⊔ T) (sup_le_sup_right le_sup_right T)
    (sup_le (sup_le hKLT hL₁LT) le_sup_right)
    (fun hle' => hkN (hle' (Subgroup.mem_sup_left (Subgroup.mem_sup_left hk))))
  set C : Subgroup G := L ⊓ Subgroup.centralizer (J : Set G) with hCdef
  have hKC' : oTwoUpper (p128 T L V) ≤ C := le_inf hKL hKC
  have hL₁C : lOne L V₁ ≤ C := le_inf hL₁L hL₁J
  have hTJ : T ≤ Subgroup.normalizer (J : Set G) := le_sup_right.trans hLTN
  have hTC : T ≤ Subgroup.normalizer (C : Set G) := fun t ht =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hs.hyp.hyp.normalizes ht,
      normalizer_le_normalizer_centralizer'' J (hTJ ht)⟩
  have hLC : L ≤ C ⊔ T :=
    (le_sup_left.trans hX).trans (sup_le_sup_right (sup_le hKC' hL₁C) T)
  have hCL : (C.subgroupOf L).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left]
    intro l hl
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hl,
      normalizer_le_normalizer_centralizer'' J (hLTN (Subgroup.mem_sup_left hl))⟩
  have hCeq : C = L := hs.hyp.hyp.faithful.2.1 C inf_le_left hCL fun x hx =>
    exists_two_pow_mem_of_le_sup hs.hyp.hyp.sylow.1 hTC hLC hx
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (hCeq.ge.trans inf_le_right)

end L128P

open L128P

theorem lemma12_8_10_of_four_F4 (h1222 : Stmt12_2_2_F4) (h12213 : Stmt12_2_13_F4)
    (h84 : Lemma12_8_4_four_F4) : Lemma12_8_10_F4 := by
  intro G _ _ T L V n V₁ V₂ hs g hg hgN
  have S := setting128A_F4 h1222 h12213 hs
  have hUeq := uA_eq_F4 h1222 hs
  have hA := hs.almostSpecial_F4 h1222 h12213
  have hI := i128_eq_sup_F4 h1222 h12213 hs
  obtain ⟨k, hk, hkN, hkY⟩ := exists_conjugate_eq hs.hyp hs.v1 hg hgN
  obtain ⟨-, hTZ⟩ := T_le_normalizer_w128_F4 h1222 h12213 hs
  have hTU : T ≤ Subgroup.normalizer (u128 V V₁ : Set G) := hA.G22_three.2
  rw [hkY _ hTU, hkY _ hTZ, hkY _ hs.v1.2.2]
  have hgood : L128A.Good V₁ (oTwoUpper (p128 T L V)) k := ⟨hk, hkN⟩
  refine ⟨?_, ?_, ?_, ⟨?_, ?_⟩, ?_, ?_⟩
  · have h := S.ten_one hgood
    rw [hUeq] at h
    exact h
  · have h := S.ten_two hgood
    rw [hUeq, ← hI] at h
    exact h
  · intro hlt
    have h := S.ten_three hgood (by rw [hUeq]; exact hlt)
    rw [hUeq, ← hI] at h
    exact h
  · have h := S.ten_four hgood
    simp only [L128A.wA, hUeq] at h
    exact h
  · intro x hx
    obtain ⟨D⟩ := hs.exists_hatModelU_F4 h1222 h12213
    exact L128A.Setting.ten_four_relIndex S hgood hUeq D hx
  · intro hle
    have hkZ : ∀ z ∈ zU128 V V₁, k⁻¹ * z * k ∈ u128 V V₁ := fun z hz =>
      hle (mem_rconj.mpr (by rw [show k * (k⁻¹ * z * k) * k⁻¹ = z by group]; exact hz))
    obtain ⟨hZ, hdisj, -, -⟩ := sup_le_normalizer_centerOf_i128_F4 h1222 h12213 hs hk hkN hkZ
    exact ⟨hZ, disjoint_iff.mp hdisj,
      commutator_eq_bot_centerOf_i128_F4 h1222 h12213 hs hk hkN hkZ⟩
  · have h84' : centralizerMod V₁ (Subgroup.normalizer (V₁ : Set G)) (L128A.uA V₂ V₁) =
        pCoreOf 2 (Subgroup.normalizer (V₁ : Set G)) := by
      rw [hUeq]
      exact h84 G T L V n hs.hyp V₁ _ hs.v1 (isHzOne_normalizer_F4 h12213 hs.hyp hs.v1)
    have h6 := S.ten_six hgood h84'
    rw [hUeq, ← hI] at h6
    obtain ⟨h61, h62, h63, h64, h65, h66⟩ := h6
    have hZT : CFSG.conjugate (zU128 V V₁) k ≤ T := by
      have h := (L128A.Setting.rconj_centerOf_le_rconj_wA V₂ V₁ k).trans
        (S.rconj_wA_le_T hgood)
      rw [hUeq] at h
      exact h
    have hZk : CFSG.conjugate (zU128 V V₁) k ≤ Subgroup.normalizer (V₁ : Set G) :=
      hZT.trans hs.v1.2.2
    refine ⟨?_, ?_, h63, ?_, ?_, h66⟩
    · rw [inf_centralizerMod_eq hZk, inf_centralizerMod_eq hZk]
      exact h61
    · rw [inf_centralizerMod_eq hZk]
      exact h62
    · rw [inf_comm (CFSG.conjugate (zU128 V V₁) k) (zU128 V V₁)]
      exact h64
    · rw [inf_comm (CFSG.conjugate (zU128 V V₁) k) (zU128 V V₁)]
      exact h65

end CFSG.Quasithin.H13
