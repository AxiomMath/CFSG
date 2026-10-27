module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165OmFam
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Split
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011I61
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165OmDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.SectionRank CFSG.RankThree.Classical2

section Certificate

theorem i165On_famD_of_engine (hE : Om165Engine) (hR : OmHypRankLower) :
    I165On i165FamD := by
  refine i165On_of_model ?_
  intro K _ _ lab p q hK hfam hp hp2 hq hq2 hqp hns he hm4 A hAe hmax hA3
  obtain ⟨t, ℓ, n⟩ := lab
  obtain ⟨ht, hreg⟩ := hfam
  subst ht
  obtain ⟨hQ, hlab, hM⟩ := rk2_model_of_isLabel hK
  have hreg_c : 3 ≤ rk2Ord p n ∨ (rk2Ord p n = 2 ∧ Odd ℓ ∧ 5 ≤ ℓ) := by
    simpa using hreg
  have hn1 : 1 ≤ n := by simpa using hlab.1
  have hℓ3 : 3 ≤ ℓ := by simpa using hlab.2
  by_cases hℓeq3 : ℓ = 3
  · subst hℓeq3
    have hm0 : 3 ≤ rk2Ord p n := by
      rcases hreg_c with h | ⟨h2, -, h5⟩
      · exact h
      · omega
    have hle := rk2Mult_bcd_le (lab := (⟨.D, 3, n⟩ : GLALabel))
      (Or.inr (Or.inr (Or.inl rfl))) hm0
    have hle' : rk2Mult (⟨.D, 3, n⟩ : GLALabel) (rk2Ord p n) ≤ 1 := by
      simpa using hle
    have hKrank := rk2KRank K (⟨.D, 3, n⟩ : GLALabel) p hK hp hp2
    have hKrank' : CFSG.Open.pRank p (⊤ : Subgroup K) ≤
        rk2Mult (⟨.D, 3, n⟩ : GLALabel) (rk2Ord p n) := by
      simpa using hKrank
    have htop3 : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup K) :=
      le_trans hA3 (pRank_mono hp.one_lt le_top)
    omega
  have hℓ4 : 4 ≤ ℓ := by
    rcases Nat.lt_or_ge 3 ℓ with h | h
    · omega
    · have h3 : ℓ = 3 := by omega
      exact absurd h3 hℓeq3
  have hqdiv : q ∣ 2 ^ n - 1 ∨ q ∣ 2 ^ n + 1 := by
    have h3 : 3 ≤ GLATwoLocalRank q K := by omega
    obtain ⟨lab', hlab', hs⟩ :=
      rk2_split16_of_tables_holds hq hq2 (hasLabel_mono (fun _ _ => trivial) hK) h3 he.symm
    rcases dvd_two_pow_sub_one_or_eq_three_of_hasLabel_of_exists_split16 hm4 hK
      ⟨lab', hlab', hs⟩ (by simp [CFSG.Assembly.LargeEvenUntwisted])
      with h | ⟨hn1, hq3⟩
    · exact Or.inl h
    · exact Or.inr (by rw [show n = 1 from hn1, hq3]; norm_num)
  have hZ : Subgroup.center K = ⊥ := by
    by_cases hn2 : 2 ≤ n
    · exact rk2_center_eq_bot_of_large hK (Or.inr (Or.inl rfl)) hn2
    · have hn : n = 1 := by
        have hlt : n < 2 := Nat.lt_of_not_le hn2
        omega
      subst hn
      by_cases hℓeq4 : ℓ = 4
      ·
        exfalso
        subst hℓeq4
        have hm0 : 3 ≤ rk2Ord p 1 := by
          rcases hreg_c with h | ⟨h2, -, h5⟩
          · exact h
          · omega
        have hle := rk2Mult_bcd_le (lab := (⟨.D, 4, 1⟩ : GLALabel))
          (Or.inr (Or.inr (Or.inl rfl))) hm0
        have hle' : rk2Mult (⟨.D, 4, 1⟩ : GLALabel) (rk2Ord p 1) ≤ 2 := by
          simpa using hle
        have hKrank := rk2KRank K (⟨.D, 4, 1⟩ : GLALabel) p hK hp hp2
        have hKrank' : CFSG.Open.pRank p (⊤ : Subgroup K) ≤
            rk2Mult (⟨.D, 4, 1⟩ : GLALabel) (rk2Ord p 1) := by
          simpa using hKrank
        have htop3 : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup K) :=
          le_trans hA3 (pRank_mono hp.one_lt le_top)
        omega
      · have hℓ5 : 5 ≤ ℓ := by
          rcases Nat.lt_or_ge 4 ℓ with h | h
          · omega
          · have h4 : ℓ = 4 := by omega
            exact absurd h4 hℓeq4
        refine i61_center_eq_bot_of_model hQ (i61_model_D hM rfl (by omega))
          (i61_gen_POmegaPlus le_rfl) ?_
        unfold CFSG.Blueprint.Multiplier.exceptionalOrders
        split <;> simp_all
  obtain ⟨F, hfield, hfinite, hchar, hcard, ⟨eΩ⟩⟩ :=
    exists_mulEquiv_statedOmega_plus_of_hasLabel hℓ4 hK hZ
  letI : Field F := hfield
  letI : Finite F := hfinite
  letI : CharP F 2 := hchar
  let Q : QuadraticForm F (Fin ℓ ⊕ Fin ℓ → F) := CFSG.LieType.Universal.Spin.quadPlus ℓ F
  let e : K ≃* ↥(orthDerived Q) :=
    eΩ.trans (CFSG.RankThree.PartOne.statedOmegaOrthEquiv
      (Q := Q) (Q₀ := StatedQuadPlus ℓ F) (CFSG.LieType.Universal.Spin.coe_quadPlus ℓ F))
  have hQnd : (QuadraticMap.polarBilin Q).Nondegenerate :=
    CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus ℓ F
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
      Module.finrank F (Fin ℓ ⊕ Fin ℓ → F) = 2 * ℓ' ∧ Odd ℓ' ∧ 5 ≤ ℓ' ∧
        ℓ' - 1 ≤ CFSG.Open.pRank p Ã) := by
    rcases hreg_c with h3 | ⟨hm2, hodd, h5⟩
    · exact Or.inl h3
    · obtain ⟨m, hm⟩ := hodd
      have h2m : 2 * m = ℓ - 1 := by
        rw [hm]
        simp
      refine Or.inr ⟨hm2, ℓ, ?_, ⟨m, hm⟩, h5, ?_⟩
      · exact CFSG.GroupTheory.WeirSylow.finrank_quadPlus_space (K := F) (m := ℓ)
      · have hpdvd : p ∣ Nat.card F + 1 := by
          rw [hcard]
          exact (rk2Ord_eq_two_iff hp hp2).1 hm2
        let P : Fin (2 * m) → CFSG.ClassicalGroups.Orthogonal.HypPair Q := fun i =>
          CFSG.ClassicalGroups.Orthogonal.plusPair F ⟨i.val, by
            have hi := i.isLt
            omega⟩
        have hPorth : ∀ i j, i ≠ j → (P i).Orth (P j) := by
          intro i j hij
          exact CFSG.ClassicalGroups.Orthogonal.plusPair_orth (fun h =>
            hij (Fin.ext (by simpa using congrArg Fin.val h)))
        have hle := hR F (Fin ℓ ⊕ Fin ℓ → F) Q m P hPorth p hp hp2 hpdvd
        have htop_le : ℓ - 1 ≤
            CFSG.Open.pRank p (⊤ : Subgroup ↥(orthDerived Q)) := by
          rw [← h2m]
          exact hle
        exact le_trans htop_le hÃmax
  have hmodel := hE F (Fin ℓ ⊕ Fin ℓ → F) Q hQnd n p q hcard hp hp2 hq hq2 hqp hqdiv
    Ã hÃe hÃmax hÃ3 hreg'
  exact concl165_of_mulEquiv hp hq e hmodel

end Certificate

end CFSG.LocalAnalysis.GLTheoremA.Y10F
