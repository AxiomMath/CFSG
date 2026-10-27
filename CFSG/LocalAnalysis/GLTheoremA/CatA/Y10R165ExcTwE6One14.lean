module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcTwE6One13
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcTwE6One9

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcTwE6

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.Minuscule CFSG.SeitzReduction
  CFSG.StandardType CFSG.LieType.Steinberg.Exceptional CFSG.SectionRank
  CFSG.SeitzReduction.F4Pilot CFSG.LieType.SeitzGeneration
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcTwE6One

theorem not_three_dvd_two_pow_add_one_of_rk2Ord_one {f : ℕ}
    (hrk : CFSG.LocalAnalysis.GLTheoremA.rk2Ord 3 f = 1) : ¬ 3 ∣ 2 ^ f + 1 := by
  intro h3
  have h1 : 3 ∣ 2 ^ f - 1 :=
    (CFSG.LocalAnalysis.GLTheoremA.rk2Ord_eq_one_iff).mp hrk
  have h2 : 3 ∣ 2 ^ f + 1 - (2 ^ f - 1) := Nat.dvd_sub h3 h1
  have h4 : 2 ^ f + 1 - (2 ^ f - 1) = 2 := by
    have := Nat.one_le_pow f 2 (by norm_num)
    omega
  rw [h4] at h2
  exact absurd h2 (by norm_num)

theorem exists_conj_eq_threeFrame_lift_of_maximal_rank {f : ℕ} (hf : 1 ≤ f)
    (h3 : ¬ 3 ∣ 2 ^ f + 1)
    {A : Subgroup ↥(fixedGroup (GaloisField 2 (2 * f)) (frobQ 2 f))}
    (hA : IsElemAbelian 3 A)
    (hmax : CFSG.Open.pRank 3
        (⊤ : Subgroup ↥(fixedGroup (GaloisField 2 (2 * f)) (frobQ 2 f))) ≤
      CFSG.Open.pRank 3 A)
    (hSC : ∀ c ∈ Subgroup.centralizer
        (A : Set ↥(fixedGroup (GaloisField 2 (2 * f)) (frobQ 2 f))), c ^ 3 = 1 → c ∈ A) :
    ∃ (ζ : (GaloisField 2 (2 * f))ˣ) (hζ : ζ ^ 3 = 1) (hζo : orderOf ζ = 3)
      (g : ↥(fixedGroup (GaloisField 2 (2 * f)) (frobQ 2 f))),
      IsElemAbelian 3 (CFSG.Quasithin.A1b.conjSub g A) ∧
      (CFSG.Quasithin.A1b.conjSub g A).map
        (twistedIsogenyC hf (TwE6Toral.card_galoisField_two_mul f hf) (frobQ 2 f)
          (fun c => frobQ_apply 2 f c)) =
        (ExcFrames.twE6ThreeFrameHom hf h3 ζ hζ).range := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hK : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 :=
    TwE6Toral.card_galoisField_two_mul f hf
  obtain ⟨ζ, hζ, ι, hζo, hinj, happly, hmem, hlast⟩ := ExcFrames.exists_threeFrame hf h3
  have hFrameEl : IsElemAbelian 3 ι.range :=
    CFSG.HardMathSupport.Timmesfeld.FieldBonus.isElemAbelian_range_of_comm_pow
      (fun a b => mul_comm a b) (fun a => by
        apply Multiplicative.toAdd.injective
        rw [toAdd_pow, toAdd_one]
        funext i
        rw [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul]) ι
  have hFrameCard : Nat.card ↥ι.range = 3 ^ 4 := by
    rw [show Nat.card ↥ι.range =
        Nat.card (Multiplicative (Fin Tag.F4.rank → ZMod 3)) from
      Nat.card_range_of_injective hinj]
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_pi]
    simp only [Nat.card_zmod, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have h4 : Tag.F4.rank = 4 := by decide
    exact h4 ▸ rfl
  have heq : CFSG.Open.pRank 3
        (⊤ : Subgroup ↥(fixedGroup (GaloisField 2 (2 * f)) (frobQ 2 f))) =
      CFSG.Open.pRank 3 (⊤ : Subgroup ↥(C0 f)) :=
    CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num)
      (twistedIsogenyCMulEquiv hf hK h3)
  have h4top : 4 ≤ CFSG.Open.pRank 3
      (⊤ : Subgroup ↥(fixedGroup (GaloisField 2 (2 * f)) (frobQ 2 f))) := by
    rw [heq]
    exact CFSG.SectionRank.le_pRank (by norm_num) le_top hFrameEl hFrameCard
  have hAcard : 3 ^ 4 ≤ Nat.card A := by
    obtain ⟨E, hEA, hE, hEcard⟩ :=
      CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank
        (p := 3) (H := A) (k := 4) (le_trans h4top hmax)
    rw [← hEcard]
    exact Subgroup.card_le_of_le hEA
  set π : ↥(fixedGroup (GaloisField 2 (2 * f)) (frobQ 2 f)) →* ↥(C0 f) :=
    twistedIsogenyC hf hK (frobQ 2 f) (fun c => frobQ_apply 2 f c) with hπdef
  have hsurj : Function.Surjective π :=
    twistedIsogenyC_surjective hf hK (frobQ 2 f) (fun c => frobQ_apply 2 f c)
  have hker : π.ker =
      Subgroup.center ↥(fixedGroup (GaloisField 2 (2 * f)) (frobQ 2 f)) :=
    ker_twistedIsogenyC hf hK (frobQ 2 f) (fun c => frobQ_apply 2 f c)
  have hZc : Subgroup.center ↥(fixedGroup (GaloisField 2 (2 * f)) (frobQ 2 f)) = ⊥ :=
    center_fixedGroup_eq_bot_of_not_three_dvd (frobQ 2 f) hK
      (fun c => frobQ_apply 2 f c) h3
  have hinjπ : Function.Injective π := by
    rw [← MonoidHom.ker_eq_bot_iff, hker, hZc]
  have hA'el : IsElemAbelian 3 (A.map π) := CFSG.SectionRank.isElemAbelian_map hA π
  have hA'card : 3 ^ 4 ≤ Nat.card ↥(A.map π) := by
    rw [Subgroup.card_map_of_injective hinjπ]
    exact hAcard
  have hSC' : ∀ c ∈ Subgroup.centralizer ((A.map π : Subgroup ↥(C0 f)) : Set ↥(C0 f)),
      c ^ 3 = 1 → c ∈ A.map π := by
    intro c hc hc3
    obtain ⟨d, rfl⟩ := hsurj c
    have hd3 : d ^ 3 = 1 := by
      apply hinjπ
      simpa using hc3
    have hd : d ∈ Subgroup.centralizer (A : Set
        ↥(fixedGroup (GaloisField 2 (2 * f)) (frobQ 2 f))) := by
      rw [Subgroup.mem_centralizer_iff] at hc ⊢
      intro a ha
      have h := hc (π a) (Subgroup.mem_map_of_mem π ha)
      apply hinjπ
      rw [map_mul, map_mul]
      exact h
    exact Subgroup.mem_map_of_mem π (hSC d hd hd3)
  obtain ⟨c0, hc0⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcTwE6One.exists_conj_eq_threeFrame_of_sc
      hf h3 hζo hζ hA'el hA'card hSC'
  obtain ⟨g, hg⟩ : ∃ g : ↥(fixedGroup (GaloisField 2 (2 * f)) (frobQ 2 f)), π g = c0 :=
    hsurj c0
  refine ⟨ζ, hζ, hζo, g⁻¹, CFSG.SectionRank.isElemAbelian_map hA _, ?_⟩
  have hgc : π g⁻¹ = c0⁻¹ := by rw [map_inv, hg]
  have hcA : CFSG.Quasithin.A1b.conjSub c0⁻¹ (A.map π) =
      (ExcFrames.twE6ThreeFrameHom hf h3 ζ hζ).range := by
    rw [hc0]
    change CFSG.Quasithin.A1b.conjSub c0⁻¹ (CFSG.Quasithin.A1b.conjSub c0
      (ExcFrames.twE6ThreeFrameHom hf h3 ζ hζ).range) = _
    rw [← CFSG.Quasithin.A1b.conjSub_mul, inv_mul_cancel, CFSG.Quasithin.A1b.conjSub_one]
  rw [CFSG.Quasithin.A1b.conjSub] at hcA
  exact map_conjSub_map_eq π hgc hcA

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcTwE6
