module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoBenderAutE4Basic
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderAutUnitaryField
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderInvField
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderInvLinearModel
public import CFSG.LocalAnalysis.QuasithinUnique.RankOneRecognitionCover
public import CFSG.Milestones.CTGMS_Bender_1971_even_rank_one_model_and_strong_embedding_input
public import CFSG.Walter.PSL2Facts.Even

public section

namespace CFSG.ComponentClassification.RankTwoBender

open Subgroup CFSG.Open CFSG.ComponentClassification.AschbacherToolkit
open CFSG.ComponentClassification.AschbacherToolkit.Bender
open CFSG.ComponentClassification.AschbacherToolkit.Bender.LinearInv
open scoped MatrixGroups

section Field

variable {K : Type*} [Field K] [Finite K] [CharP K 2]

theorem eq_of_involutive (θ₁ θ₂ : K →+* K) (h₁ : ∀ x, θ₁ (θ₁ x) = x) (h₂ : ∀ x, θ₂ (θ₂ x) = x)
    {e₁ : K} (he₁ : θ₁ e₁ ≠ e₁) {e₂ : K} (he₂ : θ₂ e₂ ≠ e₂) : ∀ x, θ₂ x = θ₁ x := by
  let σ : K ≃+* K := RingEquiv.ofBijective θ₁ ⟨θ₁.injective, fun y => ⟨θ₁ y, h₁ y⟩⟩
  have hσ : ∀ x, σ x = θ₁ x := fun _ => rfl
  have hinv : Function.Involutive σ := fun x => by rw [hσ, hσ, h₁]
  set q := Nat.card {x : K // σ x = x} with hq
  have hcard : Nat.card K = q ^ 2 := by
    rw [hq]
    exact (InvField.card_fix_sq θ₁ h₁ he₁).symm
  have hq2 : 2 ≤ q := by
    rw [hq]
    have h0 : σ 0 = 0 := map_zero σ
    have h1 : σ 1 = 1 := map_one σ
    have : Finite {x : K // σ x = x} := Subtype.finite
    exact Finite.one_lt_card_iff_nontrivial.mpr
      ⟨⟨⟨0, h0⟩, ⟨1, h1⟩, fun h => zero_ne_one (congrArg Subtype.val h)⟩⟩
  have hfix : ∀ t : K, σ t = t → θ₂ t = t := fun t ht =>
    InvField.apply_eq_self_of_involutive σ θ₂ q hq2 hcard rfl h₂ ht
  rcases UnitaryField.eq_id_or_eq_conj_of_fix σ hinv θ₂ hfix with hid | hconj
  · exact absurd (hid e₂) he₂
  · exact hconj

end Field

section Model

variable {K : Type*} [Field K] [Finite K] [CharP K 2]

theorem linear_coord (R R₀ : Sylow 2 SL(2, K)) (hR : (R : Subgroup SL(2, K)) = upSub)
    (hR₀ : (R₀ : Subgroup SL(2, K)) = loSub) (γ : MulAut SL(2, K)) (hγγ : γ * γ = 1)
    (hγR : γ • R = R) (hγR₀ : γ • R₀ = R₀) :
    ∃ (θ : K →+* K) (lam : K), (∀ x, θ (θ x) = x) ∧ lam * θ lam = 1 ∧
      ∀ b, γ (up b) = up (lam * θ b) := by
  classical
  have hex : ∀ b : K, ∃ b', γ (up b) = up b' := by
    intro b
    have h := InvInner.apply_mem_of_smul_eq hγR
      (show up b ∈ (R : Subgroup SL(2, K)) by rw [hR]; exact up_mem b)
    rw [hR] at h
    exact mem_upSub.mp h
  choose L hL using hex
  have hLadd : ∀ b b', L (b + b') = L b + L b' := by
    intro b b'
    apply up_injective
    rw [← hL, ← up_mul, map_mul, hL, hL, up_mul]
  have hLL : ∀ b, L (L b) = b := fun b => up_injective (by
    rw [← hL, ← hL]
    change (γ * γ) (up b) = up b
    rw [hγγ, MulAut.one_apply])
  have hL0 : L 0 = 0 := by
    have h := hLadd 0 0
    rw [add_zero] at h
    linear_combination -h
  have hex' : ∀ t : Kˣ, ∃ t', γ (dg t) = dg t' := by
    intro t
    have h1 := Omega.mem_normalizer_smul (α := γ) (S := R) (g := dg t)
      (by rw [hR]; exact dg_mem_normalizer_up t)
    have h2 := Omega.mem_normalizer_smul (α := γ) (S := R₀) (g := dg t)
      (by rw [hR₀]; exact dg_mem_normalizer_lo t)
    rw [hγR, hR] at h1
    rw [hγR₀, hR₀] at h2
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
  exact ⟨θr, lam, hθθ, hlamθ, fun b => by rw [hL, hLθ]; rfl⟩

@[expose] def LinearTwisted (γ : MulAut SL(2, K)) : Prop :=
  ∃ (θ : K →+* K) (lam : K), (∃ e, θ e ≠ e) ∧ (∀ x, θ (θ x) = x) ∧
    ∀ b, γ (up b) = up (lam * θ b)

theorem linear_form [IsSimpleGroup SL(2, K)] (R R₀ : Sylow 2 SL(2, K))
    (hR : (R : Subgroup SL(2, K)) = upSub) (hR₀ : (R₀ : Subgroup SL(2, K)) = loSub)
    (hSE : fusionStronglyEmbedded (normalizer ((R : Subgroup SL(2, K)) : Set SL(2, K))))
    (hcard : Nat.card (Sylow 2 SL(2, K)) = Nat.card (R : Subgroup SL(2, K)) + 1)
    (γ : MulAut SL(2, K)) (hγγ : γ * γ = 1) (hγR : γ • R = R) (hγR₀ : γ • R₀ = R₀) :
    γ = 1 ∨ LinearTwisted γ := by
  classical
  obtain ⟨θ, lam, hθθ, hlamθ, hγ⟩ := linear_coord R R₀ hR hR₀ γ hγγ hγR hγR₀
  by_cases hid : ∀ x, θ x = x
  · left
    have hne : R₀ ≠ R := by
      intro h
      apply upSub_ne_loSub (K := K)
      rw [← hR, ← hR₀, h]
    have hlam1 : lam = 1 := by
      have h := hlamθ
      rw [hid] at h
      exact CharTwo.sq_injective (show lam ^ 2 = 1 ^ 2 by rw [sq, h, one_pow])
    refine Omega.eq_one_of_centralizes hSE hcard hne γ hγR hγR₀ fun s hs => ?_
    rw [hR] at hs
    obtain ⟨b, rfl⟩ := mem_upSub.mp hs
    rw [hγ, hid, hlam1, one_mul]
  · right
    push Not at hid
    obtain ⟨e, he⟩ := hid
    exact ⟨θ, lam, ⟨e, he⟩, hθθ, hγ⟩

theorem linear_not_twisted_mul {γ₁ γ₂ : MulAut SL(2, K)} (h₁ : LinearTwisted γ₁)
    (h₂ : LinearTwisted γ₂) : ¬ LinearTwisted (γ₁ * γ₂) := by
  rintro ⟨θ', l', ⟨e', he'⟩, hθ', h'⟩
  obtain ⟨θ₁, l₁, ⟨e₁, he₁⟩, hθ₁, hγ₁⟩ := h₁
  obtain ⟨θ₂, l₂, ⟨e₂, he₂⟩, hθ₂, hγ₂⟩ := h₂
  have hcomp : ∀ b, l' * θ' b = l₁ * θ₁ l₂ * θ₁ (θ₂ b) := by
    intro b
    apply up_injective
    rw [← h', MulAut.mul_apply, hγ₂, hγ₁, map_mul, mul_assoc]
  have hl : l' = l₁ * θ₁ l₂ := by
    have h := hcomp 1
    simp only [map_one, mul_one] at h
    exact h
  have hl0 : l' ≠ 0 := by
    intro h0
    have h := h' 1
    rw [h0, zero_mul] at h
    have h1 : (γ₁ * γ₂) (up 1) = (γ₁ * γ₂) 1 := by rw [h, up_zero, map_one]
    exact one_ne_zero (up_injective (((γ₁ * γ₂).injective h1).trans up_zero.symm))
  have h21 := eq_of_involutive θ₁ θ₂ hθ₁ hθ₂ he₁ he₂
  have h'1 := eq_of_involutive θ₁ θ' hθ₁ hθ' he₁ he'
  apply he'
  have h := hcomp e'
  rw [← hl, h21, hθ₁] at h
  exact mul_left_cancel₀ hl0 h

end Model

theorem e4Inner_sl2 (f : ℕ) (hf : 2 ≤ f) : E4Inner SL(2, GaloisField 2 f) := by
  have : Finite (GaloisField 2 f) := inferInstance
  let eS : PSL(2, GaloisField 2 f) ≃* SL(2, GaloisField 2 f) :=
    CFSG.Walter.psl2MulEquivSL2OfCharTwo
  have : Finite PSL(2, GaloisField 2 f) := Finite.of_injective eS eS.injective
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
  have hne : R₀ ≠ R := by
    intro h
    apply upSub_ne_loSub (K := GaloisField 2 f)
    rw [← hR, ← hR₀, h]
  intro α β hα hβ hαβ
  exact exists_inner_of_commute_of_form hSE hcard hne LinearTwisted
    (fun γ hγ hγR hγR₀ => linear_form R R₀ hR hR₀ hSE hcard γ hγ hγR hγR₀)
    (fun _ _ _ _ _ _ _ _ h₁ h₂ => linear_not_twisted_mul h₁ h₂) α β hα hβ hαβ

theorem e4Inner_of_mulEquiv_psl2 {X : Type*} [Group X] {f : ℕ} (hf : 2 ≤ f)
    (e : X ≃* PSL(2, GaloisField 2 f)) : E4Inner X :=
  (e4Inner_sl2 f hf).of_mulEquiv (e.trans CFSG.Walter.psl2MulEquivSL2OfCharTwo)

end CFSG.ComponentClassification.RankTwoBender
