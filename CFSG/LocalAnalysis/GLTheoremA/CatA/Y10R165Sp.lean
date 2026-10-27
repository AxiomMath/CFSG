module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Concl
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Split
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166FamB
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011I61

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.SectionRank

@[expose] def SpModel165At : Prop :=
  ∀ (ℓ n p q : ℕ) (F : Type) [Field F] [Finite F] [CharP F 2],
    Nat.card F = 2 ^ n → 3 ≤ rk2Ord p n → 3 * rk2Ord p n ≤ 2 * ℓ →
    p.Prime → p ≠ 2 → q.Prime → q ≠ 2 → q ≠ p →
    (q ∣ 2 ^ n - 1 ∨ n = 1 ∧ q = 3) →
    ∀ A : Subgroup (StatedSp ℓ F), IsElemAbelian p A →
      CFSG.Open.pRank p (⊤ : Subgroup (StatedSp ℓ F)) ≤ CFSG.Open.pRank p A →
      3 ≤ CFSG.Open.pRank p A → Concl165 (StatedSp ℓ F) p q A

private theorem exc_PSp_one {ℓ : ℕ} (h : ℓ ≠ 3) :
    CFSG.Blueprint.Multiplier.exceptionalOrders .PSp ℓ 2 1 = (1, 1) := by
  unfold CFSG.Blueprint.Multiplier.exceptionalOrders
  split <;> simp_all

theorem i165On_famBC_of_engine (hengine : SpModel165At) : I165On i165FamBC := by
  refine i165On_of_model ?_
  intro K _ _ lab p q hK hfam hp hp2 hq hq2 hqp hns he hm4 A hAe hmax hA3
  obtain ⟨htag, hm0⟩ := hfam
  let labB : GLALabel := ⟨.B, lab.rank, lab.n⟩
  have hBeq : rk2Norm lab = labB := by
    obtain ⟨t, l, n⟩ := lab
    rcases htag with htag | htag
    · subst htag; simp [rk2Norm, labB]
    · subst htag; simp [rk2Norm, labB]
  have hKB : HasLabel K (fun l : GLALabel => l = labB) :=
    hBeq ▸ CFSG.LocalAnalysis.GLTheoremA.rk2_isLabel_norm hK
  have hBn : labB.n = lab.n := rfl
  have hBrank : labB.rank = lab.rank := rfl
  have hmlt : 3 ≤ rk2Mult labB (rk2Ord p labB.n) := by
    have h1 : CFSG.Open.pRank p (⊤ : Subgroup K) ≤ rk2Mult labB (rk2Ord p labB.n) :=
      CFSG.LocalAnalysis.GLTheoremA.rk2KRank K labB p hKB hp hp2
    have h2 : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup K) :=
      le_trans hA3 (pRank_mono hp.one_lt le_top)
    exact le_trans h2 h1
  have h2l : 3 * rk2Ord p lab.n ≤ 2 * lab.rank := by
    have hpos : 0 < rk2Ord p labB.n := by
      have := CFSG.LocalAnalysis.GLTheoremA.rk2Ord_pos hp hp2 labB.n
      exact this
    have hm : rk2Mult labB (rk2Ord p labB.n) =
        if (rk2Ord p labB.n) % 2 = 0 then 2 * labB.rank / (rk2Ord p labB.n)
          else labB.rank / (rk2Ord p labB.n) := rfl
    rw [hm] at hmlt
    split at hmlt
    · rename_i heven
      have h3 : 3 * rk2Ord p labB.n ≤ 2 * labB.rank := by
        rw [Nat.le_div_iff_mul_le hpos] at hmlt
        omega
      simpa using h3
    · have h3 : 3 * rk2Ord p labB.n ≤ labB.rank := by
        rw [Nat.le_div_iff_mul_le hpos] at hmlt
        omega
      simpa using (show 3 * rk2Ord p labB.n ≤ 2 * labB.rank by omega)
  have hZ : Subgroup.center K = ⊥ := by
    obtain ⟨hQo, hlam, hMo⟩ := CFSG.LocalAnalysis.GLTheoremA.rk2_model_of_isLabel hKB
    rcases eq_or_ne lab.n 1 with hn1 | hn1
    ·
      have hne3 : labB.rank ≠ 3 := by
        intro h3
        rw [h3] at h2l
        have : rk2Ord p lab.n ≤ 2 := by omega
        omega
      refine CFSG.LocalAnalysis.GLTheoremA.i61_center_eq_bot_of_model hQo
        (CFSG.LocalAnalysis.GLTheoremA.i61_model_B hMo rfl) ?_ ?_
      · simpa using CFSG.LocalAnalysis.GLTheoremA.i61_gen_PSp
          (ℓ := labB.rank) (n := labB.n) hlam.1
      · simpa [hBn, hn1] using exc_PSp_one (ℓ := labB.rank) hne3
    · refine CFSG.LocalAnalysis.GLTheoremA.rk2_center_eq_bot_of_large hKB (Or.inl rfl) ?_
      have := hlam.1
      omega
  obtain ⟨F, hfield, hfinite, hchar, hcard, ⟨e⟩⟩ :=
    exists_mulEquiv_statedSp_of_isLabel (N := lab.rank) (n := lab.n) hKB hZ
  letI : Field F := hfield
  letI : Finite F := hfinite
  letI : CharP F 2 := hchar
  have hqdiv : q ∣ 2 ^ lab.n - 1 ∨ lab.n = 1 ∧ q = 3 := by
    have h3 : 3 ≤ GLATwoLocalRank q K := by omega
    obtain ⟨lab', hlab', hs⟩ :=
      rk2_split16_of_tables_holds hq hq2 (hasLabel_mono (fun _ _ => trivial) hK) h3 he.symm
    exact dvd_two_pow_sub_one_or_eq_three_of_hasLabel_of_exists_split16 hm4 hK
      ⟨lab', hlab', hs⟩ (by rcases htag with htag | htag <;> rw [htag] <;> trivial)
  let Ã : Subgroup (StatedSp lab.rank F) := A.map e.toMonoidHom
  have hÃe : IsElemAbelian p Ã := CFSG.SectionRank.isElemAbelian_map hAe e.toMonoidHom
  have hÃrank : CFSG.Open.pRank p Ã = CFSG.Open.pRank p A := by
    have htop : (⊤ : Subgroup A).map (e.toMonoidHom.comp A.subtype) = Ã := by
      rw [Subgroup.map_top, MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← htop, pRank_eq_pRank_top_subgroup A]
    exact CFSG.LocalAnalysis.GLTheoremB.pRank_map_eq_of_injective hp.one_lt
      (e.toMonoidHom.comp A.subtype) (fun x y h => Subtype.ext (e.injective h)) ⊤
  have hÃmax : CFSG.Open.pRank p (⊤ : Subgroup (StatedSp lab.rank F)) ≤
      CFSG.Open.pRank p Ã := by
    rw [← pRank_top_eq_of_mulEquiv hp.one_lt e, hÃrank]
    exact hmax
  have hÃ3 : 3 ≤ CFSG.Open.pRank p Ã := by
    rw [hÃrank]
    exact hA3
  have hmodel : Concl165 (StatedSp lab.rank F) p q Ã :=
    hengine lab.rank lab.n p q F hcard hm0 h2l hp hp2 hq hq2 hqp hqdiv Ã hÃe hÃmax hÃ3
  exact concl165_of_mulEquiv hp hq e hmodel

end CFSG.LocalAnalysis.GLTheoremA.Y10F
