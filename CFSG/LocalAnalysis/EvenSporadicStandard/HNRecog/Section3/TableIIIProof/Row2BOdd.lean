module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.TableIIIProof.CenterX
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.TableIIIProof.FiveType

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G]

private theorem t3_sq_eq_one_of_isConj {x y : G} (hx : orderOf x = 2) (hy : IsConj x y) :
    y ^ 2 = 1 := by
  obtain ⟨g, rfl⟩ := isConj_iff.1 hy
  rw [conj_pow, ← hx, pow_orderOf_eq_one, mul_one, mul_inv_cancel]

theorem tableIII_orderOf_ne_three_2B (hI : TwoHSInterface) [Finite G] {a z a' c σ : G}
    (h : IsF5Type a z) (hF2 : Vert Fusion2Facts a z) (hX : XStruct a z a') (ha'Q : a' ∈ Qz z)
    (ha' : IsConj a a') (hc : c ∈ tab3Set a z a' 1) (hσ : σ ∈ Gxyz a' z c) :
    orderOf σ ≠ 3 := by
  intro hσ3
  obtain ⟨hσa', hσz, hσc⟩ := mem_Gxyz.1 hσ
  obtain ⟨c₀, -, -, hcent⟩ := hX.three_cent σ (mem_Gxy.2 ⟨hσa', hσz⟩) hσ3
  have hcO := tableIII_mem_pCore_2B hI h hF2 hX ha'Q ha' hc
  have hcσ : c ∈ Gx σ := mem_Gx.2 (mem_Gx.1 hσc).symm
  have hmem : c ∈ CFSG.Open.pCoreOf 2 (derivedOf (Gxy a' z)) ⊓ Gx σ := ⟨hcO, hcσ⟩
  rw [hcent] at hmem
  exact tableIII_not_mem_center_2B hI h hF2 hX ha'Q ha' hc hmem

theorem tableIII_orderOf_ne_five_2B (hI : TwoHSInterface) [Finite G] {a z a' c ρ : G}
    (h : IsF5Type a z) (hSGz : StructGzFacts a z) (ha'Q : a' ∈ Qz z) (ha' : IsConj a a')
    (hc : c ∈ tab3Set a z a' 1) (hρ : ρ ∈ Gxyz a' z c) : orderOf ρ ≠ 5 := by
  intro hρ5
  obtain ⟨⟨hcQ, hcA, hca', hca'z⟩, hcB⟩ := hc
  obtain ⟨ha'2, ha'1, ha'z, ha'zc, hz2, hz1, -, -⟩ := tableIII_basic hI h ha'Q ha'
  obtain ⟨hρa', hρz, hρc⟩ := mem_Gxyz.1 hρ
  have hc2 : c ^ 2 = 1 := t3_sq_eq_one_of_isConj h.orderOf_a hcA
  have ha'c : a' * c = c * a' :=
    comm_of_sq_mul ha'2 hc2 (t3_sq_eq_one_of_isConj h.orderOf_z hcB)
  have hzc : z * c = c * z := mem_Gx.1 (tableIII_Qz_le z hcQ)
  have hnz : ¬ IsConj a z := not_isConj_of_isF5Type hI h
  have hc1 : c ≠ 1 := by
    rintro rfl
    have h1 := h.orderOf_a
    rw [isConj_one_left.1 hcA, orderOf_one] at h1
    exact absurd h1 (by norm_num)
  have hcz : c ≠ z := fun h' => hnz (h' ▸ hcA)
  obtain ⟨-, hE⟩ := tableIII_five_type h hSGz (ρ := ⟨ρ, hρz⟩)
    (by rw [Subgroup.orderOf_mk, hρ5]) ha'Q ha'1 ha'z (mem_Gx.1 hρa').symm
  obtain ⟨-, -, hno⟩ := hE
  apply hno
  refine ⟨Subgroup.closure ({a', z, c} : Set G), ?_, ?_⟩
  · rw [Subgroup.closure_le]
    rintro x (rfl | rfl | rfl)
    · exact ⟨ha'Q, mem_Gx.2 (mem_Gx.1 hρa').symm⟩
    · exact ⟨self_mem_Qz hz2, mem_Gx.2 (mem_Gx.1 hρz).symm⟩
    · exact ⟨hcQ, mem_Gx.2 (mem_Gx.1 hρc).symm⟩
  · exact tableIII_isElemAbelian_closure_three ha'2 hz2 hc2 ha'zc ha'c hzc ha'1 hz1 ha'z hc1
      hca' hcz hca'z

end CFSG.EvenSporadicStandard.HNRecog.Section3
