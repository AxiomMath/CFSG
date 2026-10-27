module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165OmFam
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Split
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011I61
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165OmDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.SectionRank CFSG.RankThree.Classical2

section Certificate

theorem i165On_famTwD_of_engine (hE : Om165Engine) : I165On i165FamTwD := by
  refine i165On_of_model ?_
  intro K _ _ lab p q hK hfam hp hp2 hq hq2 hqp hns he hm4 A hAe hmax hA3
  obtain ⟨t, ℓ, n⟩ := lab
  obtain ⟨ht, hm0⟩ := hfam
  subst ht
  obtain ⟨hQ, hlab, hM⟩ := rk2_model_of_isLabel hK
  have hn1 : 1 ≤ n := hlab.1
  have hℓ2 : 2 ≤ ℓ := hlab.2
  by_cases hℓeq2 : ℓ = 2
  · subst hℓeq2
    have hle := rk2Mult_bcd_le (lab := (⟨.twD, 2, n⟩ : GLALabel))
      (Or.inr (Or.inr (Or.inr rfl))) hm0
    have hle' : rk2Mult (⟨.twD, 2, n⟩ : GLALabel) (rk2Ord p n) ≤ 1 := by
      simpa using hle
    have hKrank := rk2KRank K (⟨.twD, 2, n⟩ : GLALabel) p hK hp hp2
    have hKrank' : CFSG.Open.pRank p (⊤ : Subgroup K) ≤
        rk2Mult (⟨.twD, 2, n⟩ : GLALabel) (rk2Ord p n) := by
      simpa using hKrank
    have htop3 : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup K) :=
      le_trans hA3 (pRank_mono hp.one_lt le_top)
    omega
  by_cases hℓeq3 : ℓ = 3
  · subst hℓeq3
    have hle := rk2Mult_bcd_le (lab := (⟨.twD, 3, n⟩ : GLALabel))
      (Or.inr (Or.inr (Or.inr rfl))) hm0
    have hle' : rk2Mult (⟨.twD, 3, n⟩ : GLALabel) (rk2Ord p n) ≤ 1 := by
      simpa using hle
    have hKrank := rk2KRank K (⟨.twD, 3, n⟩ : GLALabel) p hK hp hp2
    have hKrank' : CFSG.Open.pRank p (⊤ : Subgroup K) ≤
        rk2Mult (⟨.twD, 3, n⟩ : GLALabel) (rk2Ord p n) := by
      simpa using hKrank
    have htop3 : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup K) :=
      le_trans hA3 (pRank_mono hp.one_lt le_top)
    omega
  have hℓ4 : 4 ≤ ℓ := by
    rcases Nat.lt_or_ge ℓ 4 with hlt | hge
    · interval_cases ℓ
      · exact absurd rfl hℓeq2
      · exact absurd rfl hℓeq3
    · exact hge
  have hqdiv : q ∣ 2 ^ n - 1 ∨ q ∣ 2 ^ n + 1 := by
    have h3 : 3 ≤ GLATwoLocalRank q K := by omega
    obtain ⟨lab', hlab', hs⟩ :=
      rk2_split16_of_tables_holds hq hq2 (hasLabel_mono (fun _ _ => trivial) hK) h3 he.symm
    exact dvd_two_pow_sub_one_or_add_one_of_hasLabel_of_exists_split16 hm4 hK
      ⟨lab', hlab', hs⟩ (by simp [CFSG.Assembly.LargeEvenUntwisted])
  have hZ : Subgroup.center K = ⊥ := by
    have hℓ2' : ℓ ≠ 2 := by omega
    have hℓ3' : ℓ ≠ 3 := by omega
    have hM' : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .POmegaMinus ℓ 2 n := by
      simpa [CFSG.StandardType.MarkedModel, CFSG.StandardType.markTag,
        CFSG.StandardType.markRank, CFSG.StandardType.markChar,
        CFSG.StandardType.markDeg, if_neg hℓ2', if_neg hℓ3'] using hM
    exact i61_center_eq_bot_of_model hQ hM'
      (OmFam.genericOrders_pomegaMinus_eq_one hn1 (by omega)) rfl
  obtain ⟨F, hfield, hfinite, hchar, b, c, hcard, hirr, ⟨eΩ⟩⟩ :=
    exists_mulEquiv_statedOmega_minus_of_hasLabel hℓ4 hK hZ
  letI : Field F := hfield
  letI : Finite F := hfinite
  letI : CharP F 2 := hchar
  let Q : QuadraticForm F (Fin (ℓ - 1) ⊕ Fin (ℓ - 1) ⊕ Fin 2 → F) :=
    CFSG.LieType.Universal.Spin.quadMinus ℓ F b c
  let e : K ≃* ↥(orthDerived Q) :=
    eΩ.trans (CFSG.RankThree.PartOne.statedOmegaOrthEquiv
      (Q := Q) (Q₀ := StatedQuadMinus ℓ F b c)
      (CFSG.LieType.Universal.Spin.coe_quadMinus ℓ F b c))
  have hQnd : (QuadraticMap.polarBilin Q).Nondegenerate :=
    CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite
      (K := F) (n := ℓ) hirr
  let Ã : Subgroup ↥(orthDerived Q) := A.map e.toMonoidHom
  have hÃe : IsElemAbelian p Ã := CFSG.SectionRank.isElemAbelian_map hAe e.toMonoidHom
  have hÃrank : CFSG.Open.pRank p Ã = CFSG.Open.pRank p A := by
    have htop : (⊤ : Subgroup A).map (e.toMonoidHom.comp A.subtype) = Ã := by
      rw [Subgroup.map_top, MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← htop, pRank_eq_pRank_top_subgroup A]
    exact CFSG.LocalAnalysis.GLTheoremB.pRank_map_eq_of_injective hp.one_lt
      (e.toMonoidHom.comp A.subtype) (fun x y h => Subtype.ext (e.injective h)) ⊤
  have hÃmax : CFSG.Open.pRank p (⊤ : Subgroup ↥(orthDerived Q)) ≤
      CFSG.Open.pRank p Ã := by
    rw [← pRank_top_eq_of_mulEquiv hp.one_lt e, hÃrank]
    exact hmax
  have hÃ3 : 3 ≤ CFSG.Open.pRank p Ã := by
    rw [hÃrank]
    exact hA3
  have hreg' : 3 ≤ rk2Ord p n ∨ (rk2Ord p n = 2 ∧ ∃ ℓ' : ℕ,
      Module.finrank F (Fin (ℓ - 1) ⊕ Fin (ℓ - 1) ⊕ Fin 2 → F) = 2 * ℓ' ∧
        Odd ℓ' ∧ 5 ≤ ℓ' ∧ ℓ' - 1 ≤ CFSG.Open.pRank p Ã) := Or.inl hm0
  have hmodel := hE F (Fin (ℓ - 1) ⊕ Fin (ℓ - 1) ⊕ Fin 2 → F) Q hQnd n p q hcard
    hp hp2 hq hq2 hqp hqdiv Ã hÃe hÃmax hÃ3 hreg'
  exact concl165_of_mulEquiv hp hq e hmodel

end Certificate

end CFSG.LocalAnalysis.GLTheoremA.Y10F
