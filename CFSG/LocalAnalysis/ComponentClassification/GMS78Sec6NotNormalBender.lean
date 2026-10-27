module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Aut

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open
open CFSG.ComponentClassification.AschbacherToolkit.Bender
open CFSG.ComponentClassification.RankTwoStandard
open scoped MatrixGroups commutatorElement

theorem eq_one_of_odd_of_centralizes_sl2 {f : ℕ} (hf : 2 ≤ f)
    (α : MulAut SL(2, GaloisField 2 f)) {m : ℕ} (hm : Odd m) (hαm : α ^ m = 1)
    {A : Subgroup SL(2, GaloisField 2 f)} (hA : Nat.card A = 2 ^ f)
    (hc : ∀ a ∈ A, α a = a) : α = 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := GaloisField 2 f
  let eS : PSL(2, K) ≃* SL(2, K) := CFSG.Walter.psl2MulEquivSL2OfCharTwo
  have : Finite PSL(2, K) := Finite.of_injective eS eS.injective
  have hB : fusionBenderBorel SL(2, K) (2 ^ f) 1 :=
    (CFSG.Milestones.ctgms_bender_1971_even_rank_one_model_and_strong_embedding_input_1 f
      hf).map_mulEquiv eS
  have : IsSimpleGroup SL(2, K) :=
    CFSG.QuasithinUnique.RankOneRecog.isSimpleGroup_of_fusionIsBenderGroup
      (Or.inl ⟨f, hf, ⟨eS.symm⟩⟩)
  obtain ⟨R, hR⟩ : ∃ R : Sylow 2 SL(2, K), (R : Subgroup SL(2, K)) = A := by
    obtain ⟨P, hP⟩ := (IsPGroup.of_card hA).exists_le_sylow
    refine ⟨P, (Subgroup.eq_of_le_of_card_ge hP ?_).symm⟩
    obtain ⟨-, -, -, hPcard⟩ := benderBorel_sylowCenter hB P
    rw [hPcard, hA, pow_one]
  obtain ⟨hSE, -, hZcard, hRcard⟩ := benderBorel_sylowCenter hB R
  have hcard : Nat.card (Sylow 2 SL(2, K)) = Nat.card (R : Subgroup SL(2, K)) + 1 := by
    rw [← card_sylow_eq_of_mulEquiv eS 2, CFSG.Walter.psl2_even_card_sylow (by omega), hRcard,
      pow_one]
  have hZR : sylowCenter (R : Subgroup SL(2, K)) = R :=
    Subgroup.eq_of_le_of_card_ge (fun z hz => (mem_sylowCenter.mp hz).1)
      (by rw [hZcard, hRcard, pow_one])
  have hab : ∀ x ∈ (R : Subgroup SL(2, K)), ∀ y ∈ (R : Subgroup SL(2, K)), x * y = y * x := by
    intro x hx y hy
    rw [← hZR] at hy
    exact (mem_sylowCenter.mp hy).2 x hx
  obtain ⟨r, hr, hαr⟩ := Omega.exists_eq_conj_of_abelian hSE hcard hab α
    (fun x hx => hc x (hR ▸ hx))
  obtain ⟨j, hj⟩ := R.isPGroup' ⟨r, hr⟩
  have hrj : r ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
  have hα2 : α ^ 2 ^ j = 1 := by rw [hαr, ← map_pow, hrj, map_one]
  have h1 : orderOf α ∣ 2 ^ j := orderOf_dvd_of_pow_eq_one hα2
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  have h2 : orderOf α ∣ m := orderOf_dvd_of_pow_eq_one hαm
  rcases i with _ | i
  · rw [pow_zero, orderOf_eq_one_iff] at hi
    exact hi
  · rw [hi, pow_succ] at h2
    exact absurd (even_iff_two_dvd.mpr (dvd_trans (dvd_mul_left 2 _) h2))
      (Nat.not_even_iff_odd.mpr hm)

theorem commutator_le_centralizer_of_odd {G : Type} [Group G]
    [Finite G] {f : ℕ} (hf : 2 ≤ f) {X H A : Subgroup G}
    (e : rankTwoQuot X ≃* SL(2, GaloisField 2 f)) (hZ : Odd (Nat.card (center X)))
    (hHN : H ≤ normalizer (X : Set G)) (hHo : Odd (Nat.card H)) (hAX : A ≤ X)
    (hA : Nat.card A = 2 ^ f) (hHA : H ≤ centralizer (A : Set G)) :
    ⁅X, X⁆ ≤ centralizer (H : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set φ : H →* MulAut SL(2, GaloisField 2 f) :=
    (MulAut.congr e).toMonoidHom.comp ((quotAutHom X).comp (Subgroup.inclusion hHN))
  set A' : Subgroup X := A.subgroupOf X
  set ι : A' →* rankTwoQuot X := (QuotientGroup.mk' (center X)).comp A'.subtype
  have hA' : Nat.card A' = 2 ^ f := by
    rw [← hA]
    exact Nat.card_congr (subgroupOfEquivOfLe hAX).toEquiv
  have hι : Function.Injective ι := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxZ : (x : X) ∈ center X := by
      rw [← QuotientGroup.eq_one_iff]
      exact hx
    have hbot : A' ⊓ center X = ⊥ :=
      AschbacherTightEmbedding.two_subgroup_of_odd_eq_bot _ _
        (IsPGroup.of_card (n := f) hA').to_inf_left hZ inf_le_right
    have h3 : (x : X) ∈ A' ⊓ center X := mem_inf.mpr ⟨x.2, hxZ⟩
    rw [hbot, mem_bot] at h3
    exact Subtype.ext h3
  set B : Subgroup SL(2, GaloisField 2 f) := ι.range.map e.toMonoidHom
  have hB : Nat.card B = 2 ^ f := by
    rw [Subgroup.card_map_of_injective e.injective,
      ← Nat.card_congr (MonoidHom.ofInjective hι).toEquiv, hA']
  have htriv : ∀ h : H, quotAutHom X ⟨(h : G), hHN h.2⟩ = 1 := by
    intro h
    have hpow : φ h ^ Nat.card H = 1 := by rw [← map_pow, pow_card_eq_one', map_one]
    have hfix : ∀ b ∈ B, φ h b = b := by
      rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
      simp only [φ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.congr_apply,
        MulEquiv.trans_apply, MulEquiv.symm_apply_apply, ι]
      congr 1
      show quotAutHom X ⟨(h : G), hHN h.2⟩ (QuotientGroup.mk' (center X) (a : X)) =
        QuotientGroup.mk' (center X) (a : X)
      rw [quotAutHom_apply_mk]
      congr 1
      apply Subtype.ext
      rw [normalizerMonoidHom_apply_apply_coe]
      have hac : (h : G) * ((a : X) : G) = ((a : X) : G) * h :=
        (mem_centralizer_iff.mp (hHA h.2) ((a : X) : G) a.2).symm
      rw [hac, mul_inv_cancel_right]
    have h1 := eq_one_of_odd_of_centralizes_sl2 hf (φ h) hHo hpow hB hfix
    have h2 : (MulAut.congr e) (quotAutHom X ⟨(h : G), hHN h.2⟩) = 1 := h1
    rw [← map_one (MulAut.congr e)] at h2
    exact (MulAut.congr e).injective h2
  have hcen : ∀ h ∈ H, ∀ x ∈ X, ∃ z ∈ center X, h * x * h⁻¹ = x * (z : G) := by
    intro h hh x hx
    have h1 := congrArg (fun α => α (QuotientGroup.mk' (center X) ⟨x, hx⟩)) (htriv ⟨h, hh⟩)
    simp only [MulAut.one_apply] at h1
    rw [quotAutHom_apply_mk, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq] at h1
    refine ⟨_, inv_mem h1, ?_⟩
    simp only [InvMemClass.coe_inv, MulMemClass.coe_mul, normalizerMonoidHom_apply_apply_coe]
    group
  rw [commutator_le]
  intro x hx y hy
  rw [mem_centralizer_iff]
  intro h hh
  obtain ⟨z₁, hz₁, e₁⟩ := hcen h hh x hx
  obtain ⟨z₂, hz₂, e₂⟩ := hcen h hh y hy
  have c₁ : ∀ w ∈ X, w * (z₁ : G) = (z₁ : G) * w := fun w hw =>
    congrArg Subtype.val ((mem_center_iff.mp hz₁) ⟨w, hw⟩)
  have c₂ : ∀ w ∈ X, w * (z₂ : G) = (z₂ : G) * w := fun w hw =>
    congrArg Subtype.val ((mem_center_iff.mp hz₂) ⟨w, hw⟩)
  have hz21 : (z₂ : G) * (z₁ : G)⁻¹ = (z₁ : G)⁻¹ * z₂ := by
    rw [mul_inv_eq_iff_eq_mul, mul_assoc, c₁ (z₂ : G) z₂.2, inv_mul_cancel_left]
  have hconj : h * ⁅x, y⁆ * h⁻¹ = ⁅x, y⁆ := by
    rw [commutatorElement_def]
    calc h * (x * y * x⁻¹ * y⁻¹) * h⁻¹ =
          (h * x * h⁻¹) * (h * y * h⁻¹) * (h * x * h⁻¹)⁻¹ * (h * y * h⁻¹)⁻¹ := by group
      _ = x * z₁ * (y * z₂) * (x * z₁)⁻¹ * (y * z₂)⁻¹ := by rw [e₁, e₂]
      _ = x * ((z₁ : G) * y) * ((z₂ : G) * (z₁ : G)⁻¹) * x⁻¹ * (z₂ : G)⁻¹ * y⁻¹ := by group
      _ = x * (y * z₁) * ((z₁ : G)⁻¹ * z₂) * x⁻¹ * (z₂ : G)⁻¹ * y⁻¹ := by
          rw [← c₁ y hy, hz21]
      _ = x * y * ((z₂ : G) * x⁻¹) * (z₂ : G)⁻¹ * y⁻¹ := by group
      _ = x * y * (x⁻¹ * z₂) * (z₂ : G)⁻¹ * y⁻¹ := by rw [← c₂ x⁻¹ (inv_mem hx)]
      _ = x * y * x⁻¹ * y⁻¹ := by group
  calc h * ⁅x, y⁆ = h * ⁅x, y⁆ * h⁻¹ * h := by group
    _ = ⁅x, y⁆ * h := by rw [hconj]

end CFSG.ComponentClassification.GMS78
