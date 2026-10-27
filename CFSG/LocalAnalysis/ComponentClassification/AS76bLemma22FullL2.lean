module

public import CFSG.Milestones.CTGMS_Bender_1971_even_rank_one_model_and_strong_embedding_input
public import CFSG.LocalAnalysis.SectionRank.EvenCover.SLTwo
public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma22Basic

public section

namespace CFSG.ComponentClassification.AS76b

namespace Lemma22Full

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open Lemma34 Lemma22
open scoped commutatorElement MatrixGroups

section SL2

theorem center_sl_two_eq_bot (K : Type*) [Field K] [CharP K 2] :
    center (SL(2, K)) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨r, hr, hA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  rw [Fintype.card_fin] at hr
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hsq : (r - 1) ^ 2 = 0 := by linear_combination hr + (1 - r) * h2
  have hr1 : r = 1 := sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hsq)
  rw [mem_bot]
  apply Subtype.ext
  rw [← hA, hr1, map_one, Matrix.SpecialLinearGroup.coe_one]

noncomputable def pslTwoEquivSlTwo (K : Type*) [Field K] [CharP K 2] :
    Matrix.ProjectiveSpecialLinearGroup (Fin 2) K ≃* SL(2, K) :=
  (QuotientGroup.quotientMulEquivOfEq (center_sl_two_eq_bot K)).trans QuotientGroup.quotientBot

end SL2

section Commutator

variable {G : Type*} [Group G]

theorem commutatorElement_mul_mem_center (a b : G) {z w : G} (hz : z ∈ center G)
    (hw : w ∈ center G) : ⁅a * z, b * w⁆ = ⁅a, b⁆ := by
  have hz' : ∀ g, g * z = z * g := mem_center_iff.mp hz
  have hw' : ∀ g, g * w = w * g := mem_center_iff.mp hw
  calc ⁅a * z, b * w⁆ = a * (z * (b * w) * z⁻¹) * a⁻¹ * (b * w)⁻¹ := by
          simp only [commutatorElement_def]
          group
    _ = a * b * (w * a⁻¹ * w⁻¹) * b⁻¹ := by
          rw [← hz' (b * w), mul_inv_cancel_right]
          group
    _ = ⁅a, b⁆ := by
          rw [← hw' a⁻¹, mul_inv_cancel_right, commutatorElement_def]

end Commutator

section Recognition

variable {L : Type} [Group L] [Finite L]

theorem card_map_sylow_of_odd_center (hZ : Odd (Nat.card (center L))) (S : Sylow 2 L) :
    Nat.card ((S : Subgroup L).map (QuotientGroup.mk' (center L))) = Nat.card (S : Subgroup L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set f := (QuotientGroup.mk' (center L)).comp (S : Subgroup L).subtype with hf
  have hinj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro s hs
    rw [MonoidHom.mem_ker, hf, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hs
    have hS2 : IsPGroup 2 ↥((S : Subgroup L) ⊓ center L) := S.isPGroup'.to_inf_left
    have hbot : (S : Subgroup L) ⊓ center L = ⊥ :=
      two_subgroup_of_odd_eq_bot _ (center L) hS2 hZ inf_le_right
    have hs' : (s : L) ∈ (S : Subgroup L) ⊓ center L := mem_inf.mpr ⟨s.2, hs⟩
    rw [hbot, mem_bot] at hs'
    exact (mem_bot).mpr (Subtype.ext hs')
  have hrange : f.range = (S : Subgroup L).map (QuotientGroup.mk' (center L)) := by
    rw [hf, MonoidHom.range_comp, range_subtype]
  rw [← hrange]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

theorem exists_mulEquiv_sl_two
    (hL : CFSG.Open.IsQuasisimple L) (hZ : Odd (Nat.card (center L)))
    (hB : fusionIsBenderGroup (L ⧸ center L)) (S : Sylow 2 L)
    (hS : ∀ a ∈ (S : Subgroup L), ∀ b ∈ (S : Subgroup L), a * b = b * a) :
    ∃ n : ℕ, 2 ≤ n ∧ 2 ^ n = Nat.card (S : Subgroup L) ∧
      Nonempty (L ≃* SL(2, GaloisField 2 n)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π₀ := QuotientGroup.mk' (center L) with hπ₀
  set Sb : Sylow 2 (L ⧸ center L) := S.mapSurjective (QuotientGroup.mk'_surjective (center L))
    with hSb
  have hSbcoe : (Sb : Subgroup (L ⧸ center L)) = (S : Subgroup L).map π₀ := rfl
  have hcardSb : Nat.card (Sb : Subgroup (L ⧸ center L)) = Nat.card (S : Subgroup L) := by
    rw [hSbcoe]
    exact card_map_sylow_of_odd_center hZ S
  have hcenSb : Nat.card (center (Sb : Subgroup (L ⧸ center L))) =
      Nat.card (Sb : Subgroup (L ⧸ center L)) := by
    have htop : center (Sb : Subgroup (L ⧸ center L)) = ⊤ := by
      rw [eq_top_iff]
      intro x _
      rw [mem_center_iff]
      intro y
      have hx : (x : L ⧸ center L) ∈ (S : Subgroup L).map π₀ := x.2
      have hy : (y : L ⧸ center L) ∈ (S : Subgroup L).map π₀ := y.2
      obtain ⟨a, ha, hax⟩ := hx
      obtain ⟨b, hb, hby⟩ := hy
      apply Subtype.ext
      simp only [coe_mul]
      rw [← hax, ← hby, ← map_mul, ← map_mul, hS b hb a ha]
    rw [htop, card_top]
  rcases hB with ⟨f, hf, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ | ⟨a, ha, ⟨e⟩⟩
  ·
    have : Finite (PSL(2, GaloisField 2 f)) := Finite.of_surjective e e.surjective
    have hBB := (CFSG.Milestones.ctgms_bender_1971_even_rank_one_model_and_strong_embedding_input_1
      f hf).map_mulEquiv e.symm
    obtain ⟨-, -, -, -, hcard⟩ := hBB Sb
    refine ⟨f, hf, by rw [← hcardSb, hcard, pow_one], ?_⟩
    set π : L →* SL(2, GaloisField 2 f) :=
      ((pslTwoEquivSlTwo (GaloisField 2 f)).toMonoidHom.comp e.toMonoidHom).comp π₀ with hπ
    have hπsurj : Function.Surjective π :=
      ((pslTwoEquivSlTwo _).surjective.comp e.surjective).comp (QuotientGroup.mk'_surjective _)
    have hker : π.ker = center L := by
      ext x
      rw [MonoidHom.mem_ker, hπ, MonoidHom.comp_apply, MonoidHom.comp_apply,
        MulEquiv.coe_toMonoidHom, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
        MulEquiv.map_eq_one_iff, hπ₀, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    have hcen : π.ker ≤ center L := hker.le
    have hC : ¬ 2 ∣ Nat.card π.ker := by
      rw [hker]
      exact fun h => (Nat.not_even_iff_odd.mpr hZ) (even_iff_two_dvd.mpr h)
    obtain ⟨σ, hσ, -⟩ := CFSG.SectionRank.EvenCover.sl2_existsUnique_section hπsurj hcen hC
    have hσsurj : Function.Surjective σ := by
      have hle : commutator L ≤ σ.range := by
        rw [_root_.commutator_def, commutator_le]
        intro x _ y _
        have hx : (σ (π x))⁻¹ * x ∈ center L := by
          rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hσ, inv_mul_cancel]
        have hy : (σ (π y))⁻¹ * y ∈ center L := by
          rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hσ, inv_mul_cancel]
        have hxy : ⁅x, y⁆ = ⁅σ (π x), σ (π y)⁆ := by
          rw [← commutatorElement_mul_mem_center (σ (π x)) (σ (π y)) hx hy,
            mul_inv_cancel_left, mul_inv_cancel_left]
        rw [hxy, ← map_commutatorElement]
        exact ⟨_, rfl⟩
      rw [hL.1] at hle
      intro x
      exact hle (mem_top x)
    have hσinj : Function.Injective σ := Function.LeftInverse.injective hσ
    exact ⟨(MulEquiv.ofBijective σ ⟨hσinj, hσsurj⟩).symm⟩
  ·
    exfalso
    have : Finite (PSU3 2 f) := Finite.of_surjective e e.surjective
    have hBB := (CFSG.Milestones.ctgms_bender_1971_even_rank_one_model_and_strong_embedding_input_2
      f hf).map_mulEquiv e.symm
    obtain ⟨-, -, -, hZc, hcard⟩ := hBB Sb
    rw [hcenSb, hcard] at hZc
    have h1 : 1 < 2 ^ f := Nat.one_lt_two_pow (by omega)
    have : (2 ^ f) ^ 3 > 2 ^ f := by
      calc (2 ^ f) ^ 3 = 2 ^ f * (2 ^ f) ^ 2 := by ring
        _ > 2 ^ f * 1 := by
          apply Nat.mul_lt_mul_of_pos_left _ (by positivity)
          exact Nat.one_lt_pow (by norm_num) h1
        _ = 2 ^ f := mul_one _
    omega
  ·
    exfalso
    have : Finite (Sz a) := Finite.of_surjective e e.surjective
    have hBB := (CFSG.Milestones.ctgms_bender_1971_even_rank_one_model_and_strong_embedding_input_4
      a ha).map_mulEquiv e.symm
    obtain ⟨-, -, -, hZc, hcard⟩ := hBB Sb
    rw [hcenSb, hcard] at hZc
    have h1 : 1 < 2 ^ (2 * a + 1) := Nat.one_lt_two_pow (by omega)
    have : (2 ^ (2 * a + 1)) ^ 2 > 2 ^ (2 * a + 1) := by
      calc (2 ^ (2 * a + 1)) ^ 2 = 2 ^ (2 * a + 1) * 2 ^ (2 * a + 1) := by ring
        _ > 2 ^ (2 * a + 1) * 1 := Nat.mul_lt_mul_of_pos_left h1 (by positivity)
        _ = 2 ^ (2 * a + 1) := mul_one _
    omega

end Recognition

end Lemma22Full

end CFSG.ComponentClassification.AS76b
