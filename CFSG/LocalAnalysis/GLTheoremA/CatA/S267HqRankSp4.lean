module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267HqRankCrit
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267HqRankLift

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.HqRank

open CFSG.Open Subgroup Matrix

theorem le_pRank_PSp4 {K : Type} [Field K] [Finite K] {q f : ℕ} (hq : q.Prime)
    (hK : Nat.card K = q ^ f) :
    3 * f ≤ CFSG.Open.pRank q (⊤ : Subgroup (StatedProj (StatedSp 2 K))) := by
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨hR, hRc⟩ := CFSG.RankThree.Classical.siegel_radical_sp hq hK 2
  set R := CFSG.RankThree.Classical.siegelRadicalSp 2 K with hRdef
  set π : StatedSp 2 K →* StatedProj (StatedSp 2 K) := QuotientGroup.mk' _ with hπ
  have hinj : Function.Injective (π.comp R.subtype) := by
    rw [injective_iff_map_eq_one]
    rintro ⟨g, hg⟩ h1
    have hmem : g ∈ (StatedScalars (Fin 2 ⊕ Fin 2) K).subgroupOf (StatedSp 2 K) :=
      (QuotientGroup.eq_one_iff g).1 h1
    obtain ⟨B, -, hgB⟩ := CFSG.RankThree.Classical.mem_siegelRadicalSp.1 hg
    rw [mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at hmem
    obtain ⟨c, hc⟩ := hmem
    have h' : (Matrix.fromBlocks 1 B 0 1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
        Matrix.scalar (Fin 2 ⊕ Fin 2) (c : K) := by
      rw [← hgB, ← hc, Matrix.GeneralLinearGroup.coe_scalar]
    have hB : B = 0 := by
      ext i j
      have := congrFun (congrFun h' (Sum.inl i)) (Sum.inr j)
      simpa [Matrix.scalar_apply] using this
    refine Subtype.ext (Subtype.ext (Units.ext ?_))
    change ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = 1
    rw [hgB, hB, Matrix.fromBlocks_one]
  have hmap : R.map π = (π.comp R.subtype).range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hE : IsElemAbelian q (R.map π) := CFSG.SectionRank.isElemAbelian_map hR π
  have hEc : Nat.card (R.map π) = q ^ (3 * f) := by
    rw [hmap, MonoidHom.range_eq_map, Subgroup.card_map_of_injective hinj, Subgroup.card_top,
      hRc, ← pow_mul]
    congr 1
    ring
  exact CFSG.SectionRank.le_pRank hq.one_lt le_top hE hEc

theorem six_le_pRank_of_surj_PSp4 {K : Type} [Field K] [Finite K] {q f : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) (hK : Nat.card K = q ^ f) (hf : 3 ≤ f) {X : Type} [Group X] [Finite X]
    (φ : X →* StatedProj (StatedSp 2 K)) (hφ : Function.Surjective φ) :
    6 ≤ CFSG.Open.pRank q (⊤ : Subgroup X) := by
  have : Fact q.Prime := ⟨hq⟩
  have hq3 : 3 ≤ q := by have := hq.two_le; omega
  have hK27 : 27 ≤ Nat.card K := by
    rw [hK]
    calc 27 = 3 ^ 3 := by norm_num
      _ ≤ q ^ 3 := Nat.pow_le_pow_left hq3 3
      _ ≤ q ^ f := Nat.pow_le_pow_right hq.pos hf
  haveI : IsSimpleGroup (StatedProj (StatedSp 2 K)) :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp K 2 (by norm_num)
      (Or.inl (Or.inr (by omega)))
  obtain ⟨hperf, ⟨eM⟩⟩ :=
    CFSG.LieType.Steinberg.CentralExt.SpClosed.psp_hopfMultiplier (K := K) (n := 2) le_rfl
      (by omega)
  have hnc : ∃ a b : StatedProj (StatedSp 2 K), a * b ≠ b * a := by
    by_contra h
    push Not at h
    have hbot : commutator (StatedProj (StatedSp 2 K)) = ⊥ := by
      rw [commutator_eq_bot_iff_center_eq_top, eq_top_iff]
      intro x _
      rw [mem_center_iff]
      intro y
      exact h y x
    rw [hbot] at hperf
    obtain ⟨x, hx⟩ := exists_ne (1 : StatedProj (StatedSp 2 K))
    have hxb : x ∈ (⊥ : Subgroup (StatedProj (StatedSp 2 K))) := hperf.symm ▸ mem_top x
    exact hx (mem_bot.1 hxb)
  have hM : ¬ q ∣ Nat.card (CFSG.Open.griessHopfMultiplier (StatedProj (StatedSp 2 K))) := by
    rw [Nat.card_congr eM.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
    intro h
    have := Nat.le_of_dvd two_pos (h.trans (Nat.gcd_dvd_left 2 _))
    omega
  have hcen := pRank_cover_of_multiplier hnc hq hM
    ((show 6 ≤ 3 * f by omega).trans (le_pRank_PSp4 hq hK))
  obtain ⟨ℓ, hℓ, hℓd, hprim⟩ :=
    CFSG.SL2MinimalFaithful.exists_primitive_prime_dvd_pow_sub_one hq3 (show 3 ≤ 4 * f by omega)
  have hℓq : ℓ ≠ q := by
    rintro rfl
    have h1 : ℓ ∣ ℓ ^ (4 * f) := dvd_pow_self ℓ (by omega)
    have h2 := Nat.dvd_sub h1 hℓd
    rw [Nat.sub_sub_self (Nat.one_le_pow _ _ hℓ.pos)] at h2
    exact hℓ.one_lt.ne' (Nat.dvd_one.mp h2)
  have hℓ2 : ℓ ≠ 2 := by
    rintro rfl
    exact hprim 1 one_pos (by omega) (by simpa using (hq.even_sub_one hq2).two_dvd)
  have hℓF : ℓ ∣ Nat.card (StatedProj (StatedSp 2 K)) := by
    have hSp : ℓ ∣ Nat.card (StatedSp 2 K) := by
      rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp_two, hK, ← pow_mul,
        mul_comm f 4]
      exact Dvd.dvd.mul_left (Dvd.dvd.mul_left hℓd _) _
    have hsplit : Nat.card (StatedSp 2 K) = Nat.card (StatedProj (StatedSp 2 K)) *
        Nat.card (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.spScalars 2 K) :=
      card_eq_card_quotient_mul_card_subgroup _
    have hZ :
        Nat.card (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.spScalars 2 K) ≤ 2 := by
      rw [CFSG.LocalAnalysis.ComponentInitial.card_spScalars_eq_gcd K (by norm_num)]
      exact Nat.le_of_dvd two_pos (Nat.gcd_dvd_left 2 _)
    rw [hsplit] at hSp
    rcases (Nat.Prime.dvd_mul hℓ).1 hSp with h | h
    · exact h
    · have := Nat.le_of_dvd Nat.card_pos h
      have := hℓ.two_le
      omega
  have hinv := not_dvd_card_GL_of_prime (F := StatedProj (StatedSp 2 K)) (k := 6 ^ 2 / 4) hq hℓ
    hℓq hℓF (fun i hi1 hi2 => hprim i (by omega) (by norm_num at hi2; omega))
  exact le_pRank_of_surj_crit hnc hq hq2 hcen hinv φ hφ

end CFSG.LocalAnalysis.GLTheoremA.S267.HqRank
