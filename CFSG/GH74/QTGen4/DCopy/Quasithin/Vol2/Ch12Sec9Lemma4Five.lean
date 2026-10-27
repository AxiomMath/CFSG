module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4Five
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec8OneThirteen
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec9Lemma4FiveFinal
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec9Lemma4Red
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem8Rank
public import CFSG.Quasithin.Vol2.Ch12Sec8OneSix
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4E9

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin

open L1294 L128P in

theorem case1294Five_of_F4 (h1222 : Stmt12_2_2_F4) (h12213 : Stmt12_2_13_F4)
    (hFinal : Case1294FiveFinal_F4) : Case1294Five_F4 := by
  intro G _ _ T L V hcx V₁ V₂ K₁ hs hLK hK hK4 D h5 himg
  classical
  have hV₁2 : Nat.card V₁ = 2 := by simpa using hs.v1.2.1
  have hV₂4 : Nat.card V₂ = 4 := by simpa using hs.v2.2.1
  obtain ⟨-, -, -, a, haV₂, haV₁⟩ := exists_gens hV₁2 hV₂4
  have haV := hs.v2.1 haV₂
  have haU : a ∈ u128 V V₁ := le_conjClosure V _ haV

  have hπa : D.π a ≠ 0 := by
    intro h0
    rw [L128A.HatU.π_eq_zero_iff D haU] at h0
    have h1 : a ∈ V ⊓ zU128 V V₁ := ⟨haV, h0⟩
    rw [lemma12_8_8_three_F4 h1222 h12213 hs] at h1
    exact haV₁ h1

  obtain ⟨x, hxΓ, y, hyΓ, hx3, hy3, hxy, hx1, hy1, hxy1, hxy2, hxa, hya⟩ :=
    L1294E.exists_e9 (L128A.HatU.B_nondegenerate D) h5 hπa

  set C := centralizerMod V₁ (Subgroup.normalizer (V₁ : Set G)) V₂ with hCdef
  have hCN : C ≤ Subgroup.normalizer (u128 V V₁ : Set G) := fun g hg =>
    le_normalizer_conjClosure V _ hg.1
  have hK₁G₁ : K₁ ≤ Subgroup.normalizer (V₁ : Set G) :=
    le_of_mem_cComp (show K₁ ∈ cComp _ from hK)
  have hmemC : ∀ γ ∈ D.img K₁, γ (D.π a) = D.π a → γ ∈ D.img C := by
    intro γ hγ hγa
    obtain ⟨h, hhK, hhN, rfl⟩ := (L128A.HatU.mem_img D).1 hγ
    have hh₂ := hFinal G T L V hcx V₁ V₂ K₁ hs hLK hK hK4 D h5 himg a haV₂ haV₁ ⟨h, hhN⟩ hhK hγa
    exact (L128A.HatU.mem_img D).2
      ⟨h, mem_centralizerMod_of_mem_normalizer hs (hK₁G₁ hhK) hh₂, hhN, rfl⟩
  have hxC := hmemC x (L1294E.mem_of_relIndex_le_two himg hxΓ hx3) hxa
  have hyC := hmemC y (L1294E.mem_of_relIndex_le_two himg hyΓ hy3) hya
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

  have hpr : 2 ≤ CFSG.Open.pRank 3 (D.img C) := by
    rw [← pRank_top_subtype (p := 3)]
    refine Rank8.two_le_pRank_three_of (x := ⟨x, hxC⟩) (y := ⟨y, hyC⟩) ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · exact Subtype.ext (by simpa using hx3)
    · exact Subtype.ext (by simpa using hy3)
    · exact Subtype.ext (by simpa using hxy)
    · exact fun h => hx1 (by simpa using congrArg Subtype.val h)
    · exact fun h => hy1 (by simpa using congrArg Subtype.val h)
    · exact fun h => hxy1 (by simpa using congrArg Subtype.val h)
    · exact fun h => hxy2 (by simpa using congrArg Subtype.val h)

  rw [L1294.img_eq_range D hCN, ← pRank_top_subtype (p := 3)] at hpr
  have h2 := two_le_pRank_of_surjective' Nat.prime_three (by norm_num)
    (D.ρ.comp (Subgroup.inclusion hCN)).rangeRestrict
    (MonoidHom.rangeRestrict_surjective _) hpr
  rw [pRank_top_subtype (p := 3)] at h2
  have h3 : CFSG.Open.pRank 3 C ≤ 1 := thirteen_eight_F4 h1222 h12213 hs
  omega

end CFSG.Quasithin.H13
