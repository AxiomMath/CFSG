module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Sp62FrameTab
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Sp62LocalMax
public import Certificates.Certificate9453

public section

namespace CFSG.AGLEmbedding.KFactProofs.Sp62Local

open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two
open CFSG.Quasithin.H13 CFSG.KGroups.Sp6 CFSG.Quasithin.G2U CFSG.Open

theorem exists_dc
    (x : H6) :
    ∃ r ∈ dcReps, ∃ a ∈ N0, ∃ b ∈ N0, x = a * elt r * b :=
  Certificates.certificate9453.1 x

theorem eq_oneC_or_mem_dcPairs {r : List ℕ} (hr : r ∈ dcReps) :
    r = oneC ∨ r ∈ dcPairs.map Prod.fst := by
  simpa [dcReps] using hr

theorem normalizer_B0_eq :
    Subgroup.normalizer (B0 : Set H6) = N0 := by
  refine le_antisymm ?_ N0_le_normalizer_B0
  intro x hx
  obtain ⟨r, hr, a, ha, b, hb, rfl⟩ := exists_dc x
  rcases eq_oneC_or_mem_dcPairs hr with rfl | hr'
  · rw [← one_eq_elt_oneC, mul_one]
    exact mul_mem ha hb
  · exfalso
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr'
    have hgp : genB p.1 = true := wordsX_spec.2.2.2.2.2 p hp
    have hnot := sp62_frame_tables.2.2.2.1
    simp only [chkWordsX, Bool.and_eq_true, List.all_eq_true] at hnot
    have h1 := (hnot.2 p hp).2
    simp only [Bool.not_eq_true', List.all_eq_false, ne_eq] at h1
    obtain ⟨g, hg, hgn⟩ := h1
    have hN : ∀ {u : H6}, u ∈ N0 → u ∈ Subgroup.normalizer (B0 : Set H6) := fun hu =>
      N0_le_normalizer_B0 hu
    have hrN : elt p.1 ∈ Subgroup.normalizer (B0 : Set H6) := by
      have h1 : a⁻¹ * (a * elt p.1 * b) * b⁻¹ ∈ Subgroup.normalizer (B0 : Set H6) :=
        mul_mem (mul_mem (inv_mem (hN ha)) hx) (inv_mem (hN hb))
      simpa [mul_assoc] using h1
    have hgB : elt g ∈ B0 := elt_mem_Hgen hg
    have hconj := (Subgroup.mem_normalizer_iff.1 hrN (elt g)).1 hgB
    obtain ⟨t, ht, htr⟩ := Hgen_rep tabCheck_B hconj
    have hgg : genB g = true := (tabCheck_spec tabCheck_B).2.2.2.2 g hg
    have hrep := (rep_elt (genB_isoB hgp)).conj hgp (rep_elt (genB_isoB hgg))
    have : conjC p.1 g = t := (hrep.eq_iff htr).1 rfl
    exact hgn (by rw [this]; exact inTab_iff.2 ht)

theorem centralizer_B0_le :
    Subgroup.centralizer (B0 : Set H6) ≤ B0 := by
  intro x hx
  have hxN : x ∈ N0 := by
    rw [← normalizer_B0_eq]
    exact Subgroup.centralizer_le_normalizer (B0 : Set H6) hx
  exact centralizer_N0_le (Subgroup.mem_inf.2 ⟨hxN, hx⟩)

theorem W0_le_of_ne_N0
    {X : Subgroup H6}
    (hN : N0 ≤ X) (hne : X ≠ N0) : W0 ≤ X := by
  obtain ⟨x, hxX, hxN⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hN (Ne.symm hne))
  obtain ⟨r, hr, a, ha, b, hb, rfl⟩ := exists_dc x
  rcases eq_oneC_or_mem_dcPairs hr with rfl | hr'
  · exfalso
    apply hxN
    rw [← one_eq_elt_oneC, mul_one]
    exact mul_mem ha hb
  · have hrX : elt r ∈ X := by
      have h1 : a⁻¹ * (a * elt r * b) * b⁻¹ ∈ X :=
        mul_mem (mul_mem (inv_mem (hN ha)) hxX) (inv_mem (hN hb))
      simpa [mul_assoc] using h1
    have hgD := gD_mem_of_rep hN hr' hrX
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨c, hc, rfl⟩
    have hWD : gensWD = gensN ++ [cGD] := rfl
    rw [hWD, List.mem_append, List.mem_singleton] at hc
    rcases hc with hc | rfl
    · exact hN (elt_mem_Hgen hc)
    · exact hgD

theorem eq_N0_or_W0
    {X : Subgroup H6} (hN : N0 ≤ X) (hne : X ≠ ⊤) : X = N0 ∨ X = W0 := by
  by_cases h : X = N0
  · exact Or.inl h
  · exact Or.inr (eq_W0_of_ne_top (W0_le_of_ne_N0 hN h) hne)

theorem centralizer_z0_le_W0 :
    Subgroup.centralizer ({z0} : Set H6) ≤ W0 :=
  Certificates.certificate9453.2

theorem not_hasKlingenData_W0
    [Fact (Nat.Prime 3)] :
    ¬ HasKlingenData 3 T0S W0 := by
  rintro ⟨E, D, L, hET, hEc, hEexp, hZE, hDE, hDel, hDc, hDC, hDN, hLC, hLW, e, hSL⟩
  rw [coe_T0S] at hET
  have hZle : (Subgroup.center E).map E.subtype ≤ Subgroup.zpowers z0 := by
    rintro _ ⟨c, hc, rfl⟩
    by_contra hcz
    have hcomm : ∀ y ∈ E, (c : H6) * y = y * (c : H6) := fun y hy => by
      have := Subgroup.mem_center_iff.1 hc ⟨y, hy⟩
      exact (congrArg Subtype.val this).symm
    by_cases hcB : (c : H6) ∈ B0
    · have hEB : E ≤ B0 := fun y hy => mem_B0_of_comm hcB hcz (hET hy) (hcomm y hy)
      have hEeq : E = B0 := Subgroup.eq_of_le_of_card_ge hEB (by rw [hEc, card_B0])
      rw [hEeq] at hZE
      have htop : Subgroup.center B0 = ⊤ := by
        refine (Subgroup.eq_top_iff' _).2 fun g => Subgroup.mem_center_iff.2 fun h => ?_
        exact B0_elemAbelian.1.is_comm.comm h g
      rw [htop, Subgroup.card_top, card_B0] at hZE
      omega
    · have h9 := nine_le_card_inf_B0 hET hEc
      have hF : E ⊓ B0 ≤ Subgroup.zpowers z0 := by
        intro f hf
        by_contra hfz
        exact hcB (mem_B0_of_comm hf.2 hfz (hET c.2) (hcomm f hf.1).symm)
      have h3 := Subgroup.card_le_of_le hF
      rw [Nat.card_zpowers, orderOf_z0] at h3
      omega
  have hZeq : (Subgroup.center E).map E.subtype = Subgroup.zpowers z0 := by
    refine Subgroup.eq_of_le_of_card_ge hZle ?_
    rw [Nat.card_zpowers, orderOf_z0, Subgroup.card_map_of_injective E.subtype_injective, hZE]
  rw [hZeq] at hLC
  have hLC' : L ≤ Subgroup.centralizer ({z0} : Set H6) :=
    hLC.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.2 (Subgroup.mem_zpowers z0)))
  exact hLW (hLC'.trans centralizer_z0_le_W0)

end CFSG.AGLEmbedding.KFactProofs.Sp62Local
