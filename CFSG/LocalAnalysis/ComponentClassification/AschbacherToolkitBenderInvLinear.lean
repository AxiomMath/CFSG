module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderInvField
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderInvLinearModel
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderInvBasic
public import CFSG.LocalAnalysis.QuasithinUnique.RankOneRecognitionCover
public import CFSG.Milestones.CTGMS_Bender_1971_even_rank_one_model_and_strong_embedding_input
public import CFSG.Walter.PSL2Facts.Even

public section

namespace CFSG.ComponentClassification.AschbacherToolkit

namespace Bender

namespace LinearInv

open CFSG.Open
open scoped MatrixGroups

variable {K : Type*} [Field K] [Finite K] [CharP K 2]

theorem invDichotomyAt_upSub [IsSimpleGroup SL(2, K)] (R R₀ : Sylow 2 SL(2, K))
    (hR : (R : Subgroup SL(2, K)) = upSub) (hR₀ : (R₀ : Subgroup SL(2, K)) = loSub)
    (hSE : fusionStronglyEmbedded
      (Subgroup.normalizer ((R : Subgroup SL(2, K)) : Set SL(2, K))))
    (hcard : Nat.card (Sylow 2 SL(2, K)) = Nat.card (R : Subgroup SL(2, K)) + 1) :
    InvDichotomyAt (R : Subgroup SL(2, K)) := by
  classical
  have hne : R₀ ≠ R := by
    intro h
    apply upSub_ne_loSub (K := K)
    rw [← hR, ← hR₀, h]
  apply invDichotomyAt_of_twisted hSE hcard hne
  intro α' hα'α' hα'R hα'R₀ r hr hα'r
  have hex : ∀ b : K, ∃ b', α' (up b) = up b' := by
    intro b
    have h := InvInner.apply_mem_of_smul_eq hα'R
      (show up b ∈ (R : Subgroup SL(2, K)) by rw [hR]; exact up_mem b)
    rw [hR] at h
    exact mem_upSub.mp h
  choose L hL using hex
  have hLadd : ∀ b b', L (b + b') = L b + L b' := by
    intro b b'
    apply up_injective
    rw [← hL, ← up_mul, map_mul, hL, hL, up_mul]
  have hLL : ∀ b, L (L b) = b := fun b => up_injective (by rw [← hL, ← hL, hα'α'])
  have hL0 : L 0 = 0 := by
    have h := hLadd 0 0
    rw [add_zero] at h
    linear_combination -h
  have hex' : ∀ t : Kˣ, ∃ t', α' (dg t) = dg t' := by
    intro t
    have h1 := Omega.mem_normalizer_smul (α := α') (S := R) (g := dg t)
      (by rw [hR]; exact dg_mem_normalizer_up t)
    have h2 := Omega.mem_normalizer_smul (α := α') (S := R₀) (g := dg t)
      (by rw [hR₀]; exact dg_mem_normalizer_lo t)
    rw [hα'R, hR] at h1
    rw [hα'R₀, hR₀] at h2
    exact eq_dg_of_mem_normalizer h1 h2
  choose φ hφ using hex'
  have hLsq : ∀ (t : Kˣ) (b : K), L ((t : K) ^ 2 * b) = (φ t : K) ^ 2 * L b := by
    intro t b
    apply up_injective
    rw [← hL, ← dg_conj_up, map_mul, map_mul, map_inv, hφ, hL, dg_conj_up]
  obtain ⟨lam, hlamdef⟩ : ∃ lam, L 1 = lam := ⟨_, rfl⟩
  have hlam0 : lam ≠ 0 := by
    intro h
    have h1 := hLL 1
    rw [hlamdef, h, hL0] at h1
    exact zero_ne_one h1
  have hLmul : ∀ s b, L (s * b) * lam = L s * L b := by
    intro s b
    by_cases hs : s = 0
    · rw [hs, zero_mul, hL0, zero_mul, zero_mul]
    · obtain ⟨t, ht⟩ := isSquare_of_charTwo' s
      have ht0 : t ≠ 0 := by
        rintro rfl
        exact hs (by rw [ht, mul_zero])
      have h1 := hLsq (Units.mk0 t ht0) b
      have h2 := hLsq (Units.mk0 t ht0) 1
      rw [mul_one, hlamdef] at h2
      simp only [Units.val_mk0] at h1 h2
      rw [ht, ← sq, h1, h2]
      ring
  set θ : K → K := fun a => L a * lam⁻¹ with hθdef
  have hLθ : ∀ a, L a = lam * θ a := fun a => by
    simp only [hθdef]
    field_simp
  have hθ1 : θ 1 = 1 := by
    simp only [hθdef, hlamdef]
    exact mul_inv_cancel₀ hlam0
  have hθ0 : θ 0 = 0 := by simp only [hθdef, hL0, zero_mul]
  have hθadd : ∀ a a', θ (a + a') = θ a + θ a' := fun a a' => by
    simp only [hθdef, hLadd]
    ring
  have hθmul : ∀ a a', θ (a * a') = θ a * θ a' := by
    intro a a'
    have h := hLmul a a'
    calc θ (a * a') = (L (a * a') * lam) * lam⁻¹ * lam⁻¹ := by
          simp only [hθdef]
          field_simp
      _ = θ a * θ a' := by
          rw [h]
          simp only [hθdef]
          ring
  let θr : K →+* K :=
    { toFun := θ
      map_one' := hθ1
      map_mul' := hθmul
      map_zero' := hθ0
      map_add' := hθadd }
  have hlamθ : lam * θ lam = 1 := by
    have h := hLL 1
    rw [hlamdef, hLθ] at h
    exact h
  have hθθ : ∀ a, θr (θr a) = a := by
    intro a
    have h := hLL a
    rw [hLθ a, hLθ, hθmul] at h
    change θ (θ a) = a
    calc θ (θ a) = (lam * θ lam) * θ (θ a) := by rw [hlamθ, one_mul]
      _ = a := by linear_combination h
  by_cases hid : ∀ x, θ x = x
  ·
    left
    have hlam1 : lam = 1 := by
      have h := hlamθ
      rw [hid] at h
      exact CharTwo.sq_injective (show lam ^ 2 = 1 ^ 2 by rw [sq, h, one_pow])
    intro s hs
    rw [hR] at hs
    obtain ⟨b, rfl⟩ := mem_upSub.mp hs
    rw [hL, hLθ, hid, hlam1, one_mul]
  ·
    right
    push Not at hid
    obtain ⟨e, he⟩ := hid
    obtain ⟨w, hw⟩ := InvField.exists_add_apply_eq_one θr hθθ he
    have hrU : r ∈ (upSub : Subgroup SL(2, K)) := by
      rw [← hR]
      exact hr
    obtain ⟨c, rfl⟩ := mem_upSub.mp hrU
    have hLc : L c = c := by
      apply up_injective
      rw [← hL, hα'r, up_inv, CharTwo.neg_eq]
    refine ⟨up (w * c), by rw [hR]; exact up_mem _, ?_⟩
    rw [hL, up_inv, up_mul, CharTwo.neg_eq]
    congr 1
    have h1 : L (w * c) = θ w * c := by
      rw [hLθ, hθmul]
      rw [hLθ] at hLc
      linear_combination θ w * hLc
    have hw' : w + θ w = 1 := hw
    rw [h1]
    linear_combination -c * hw'

end LinearInv

open LinearInv CFSG.Open in
open scoped MatrixGroups in
theorem invDichotomyAt_of_mulEquiv_psl2 {X : Type*} [Group X] [Finite X] {f : ℕ} (hf : 2 ≤ f)
    (e : X ≃* PSL(2, GaloisField 2 f)) (T : Sylow 2 X) : InvDichotomyAt (T : Subgroup X) := by
  have : Finite PSL(2, GaloisField 2 f) := Finite.of_surjective e e.surjective
  let eS : PSL(2, GaloisField 2 f) ≃* SL(2, GaloisField 2 f) :=
    CFSG.Walter.psl2MulEquivSL2OfCharTwo
  have : Finite SL(2, GaloisField 2 f) := Finite.of_surjective eS eS.surjective
  have hB : fusionBenderBorel SL(2, GaloisField 2 f) (2 ^ f) 1 :=
    (CFSG.Milestones.ctgms_bender_1971_even_rank_one_model_and_strong_embedding_input_1 f
      hf).map_mulEquiv eS
  have : IsSimpleGroup SL(2, GaloisField 2 f) :=
    CFSG.QuasithinUnique.RankOneRecog.isSimpleGroup_of_fusionIsBenderGroup
      (Or.inl ⟨f, hf, ⟨eS.symm⟩⟩)
  have hKcard : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hsyl : ∀ H : Subgroup SL(2, GaloisField 2 f), Nat.card H = 2 ^ f →
      ∃ S : Sylow 2 SL(2, GaloisField 2 f), (S : Subgroup SL(2, GaloisField 2 f)) = H := by
    intro H hH
    obtain ⟨S, hS⟩ := (IsPGroup.of_card hH).exists_le_sylow
    refine ⟨S, (Subgroup.eq_of_le_of_card_ge hS ?_).symm⟩
    obtain ⟨-, -, -, hScard⟩ := benderBorel_sylowCenter hB S
    rw [hScard, hH, pow_one]
  obtain ⟨R, hR⟩ := hsyl upSub (by rw [card_upSub, hKcard])
  obtain ⟨R₀, hR₀⟩ := hsyl loSub (by rw [card_loSub, hKcard])
  obtain ⟨hSE, -, -, hRcard⟩ := benderBorel_sylowCenter hB R
  have hcard : Nat.card (Sylow 2 SL(2, GaloisField 2 f)) =
      Nat.card (R : Subgroup SL(2, GaloisField 2 f)) + 1 := by
    rw [← card_sylow_eq_of_mulEquiv eS 2, CFSG.Walter.psl2_even_card_sylow (by omega), hRcard,
      pow_one]
  exact invDichotomyAt_of_mulEquiv (e.trans eS)
    (invDichotomyAt_of_one_sylow R (invDichotomyAt_upSub R R₀ hR hR₀ hSE hcard)) T

end Bender

end CFSG.ComponentClassification.AschbacherToolkit
