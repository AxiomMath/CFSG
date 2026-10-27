module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Push28Torus
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherGoldschmidtFour

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {L T R : Subgroup G} {f : ℕ}

namespace Sec3.IsR

theorem rightConjugate_eq_of_psl2
    (hR : Sec3.IsR L T R) (h : Sec3 G L T) (hF : Foundation) (hf : 3 ≤ f)
    (e : rankTwoQuot L ≃* PSL(2, GaloisField 2 f)) (hX : Sec3.Facts L T (2 ^ f))
    (hinv : ∀ x ∈ R, x * x = 1 → x ∈ gmsV L T) {g : G}
    (hg : rightConjugate (gmsV L T) g ≤ R ⊔ T) : rightConjugate (gmsV L T) g = gmsV L T := by
  have hFr := hR.sec4Frame_of_psl2 h hf e
  obtain ⟨-, hVel, -, -, -⟩ := hX.vFacts h hF
  set E := rightConjugate (gmsV L T) g with hEdef
  have hEel : IsElemAbelian 2 E := isElemAbelian_map _ hVel
  have hE2 : ∀ x ∈ E, x * x = 1 := fun x hx => by rw [← sq]; exact hEel.2 x hx
  have hER : E ⊓ R ≤ gmsV L T := fun x hx => hinv x (mem_inf.mp hx).2 (hE2 x (mem_inf.mp hx).1)
  by_cases hEle : E ≤ R
  · have hEV : E ≤ gmsV L T := fun x hx => hER (mem_inf.mpr ⟨hx, hEle hx⟩)
    exact Subgroup.eq_of_le_of_card_ge hEV (by rw [hEdef, rightConjugate_card])
  · exfalso
    obtain ⟨x, hxE, hxR⟩ := IsConcreteLE.not_le_iff_exists.mp hEle
    have hcard := hFr.card_le_two_mul h hf e hg hE2
    have hDC : E ⊓ R ≤ centralizer ({x} : Set G) := fun z hz =>
      mem_centralizer_singleton_iff.mpr (congrArg Subtype.val
        (hEel.1.is_comm.comm ⟨z, (mem_inf.mp hz).1⟩ ⟨x, hxE⟩))
    have hlt := hFr.two_mul_card_lt h hf e hX (hg hxE) (hE2 x hxE) hxR hER hDC
    have hcE : Nat.card E = Nat.card (gmsV L T) := by rw [hEdef, rightConjugate_card]
    omega

theorem isSylowOf_top_of_psl2
    (hR : Sec3.IsR L T R) (h : Sec3 G L T) (hF : Foundation)
    (hf : 3 ≤ f) (e : rankTwoQuot L ≃* PSL(2, GaloisField 2 f)) (hX : Sec3.Facts L T (2 ^ f))
    (htr : ∀ Q ∈ gmsDelta L T, ∃ u ∈ gmsTrans L T,
      rightConjugate (T ⊓ centralizer (L : Set G)) u⁻¹ = Q)
    (hinv : ∀ x ∈ R, x * x = 1 → x ∈ gmsV L T) : IsSylowOf 2 (R ⊔ T) ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS₀ := hR.isSylowOf_sup_of_psl2 h hX htr
  have hVS₀ : gmsV L T ≤ R ⊔ T := (hR.gmsV_le_of_psl2 h hf e).trans le_sup_left
  by_contra hns
  obtain ⟨S, hS₀S, z, hzS, hzN, hzS₀⟩ :=
    exists_mem_normalizer_of_not_isSylowOf hS₀.isPGroup hns
  have hle : rightConjugate (gmsV L T) z⁻¹ ≤ R ⊔ T := by
    intro x hx
    rw [mem_rightConjugate_iff, inv_inv] at hx
    have h1 := (mem_normalizer_iff.mp hzN _).mp (hVS₀ hx)
    simpa [mul_assoc] using h1
  have hzV : z ∈ normalizer (gmsV L T : Set G) := by
    have h1 := (rightConjugate_eq_self_iff _ _).mp
      (hR.rightConjugate_eq_of_psl2 h hF hf e hX hinv hle)
    simpa using inv_mem h1
  have hp : IsPGroup 2 (R ⊔ T ⊔ zpowers z : Subgroup G) :=
    S.isPGroup'.to_le (sup_le hS₀S (zpowers_le.mpr hzS))
  have heq := hS₀.eq_of_le le_sup_left (sup_le hS₀.le (zpowers_le.mpr hzV)) hp
  exact hzS₀ (heq ▸ mem_sup_right (mem_zpowers z))

theorem false_of_psl2
    (hR : Sec3.IsR L T R) (h : Sec3 G L T) (hF : Foundation)
    (hf : 3 ≤ f) (e : rankTwoQuot L ≃* PSL(2, GaloisField 2 f)) (hX : Sec3.Facts L T (2 ^ f))
    (htr : ∀ Q ∈ gmsDelta L T, ∃ u ∈ gmsTrans L T,
      rightConjugate (T ⊓ centralizer (L : Set G)) u⁻¹ = Q)
    (hinv : ∀ x ∈ R, x * x = 1 → x ∈ gmsV L T) : False := by
  have hFr := hR.sec4Frame_of_psl2 h hf e
  obtain ⟨hVc, hVel, -, -, -⟩ := hX.vFacts h hF
  have hsyl := hR.isSylowOf_top_of_psl2 h hF hf e hX htr hinv
  obtain ⟨-, hS₀p, hS₀idx⟩ := isSylowOf_iff.mp hsyl
  rw [relIndex_top_right] at hS₀idx
  let S : Sylow 2 G := hS₀p.toSylow hS₀idx
  have hSc : (S : Subgroup G) = R ⊔ T := IsPGroup.toSylow_coe hS₀p hS₀idx
  have hVS : gmsV L T ≤ S := hSc ▸ (hR.gmsV_le_of_psl2 h hf e).trans le_sup_left
  have hV1 : gmsV L T ≠ ⊥ := by
    intro hb
    have h1 : Nat.card (gmsV L T) = 1 := by rw [hb, card_bot]
    rw [hVc] at h1
    have : 1 < 2 ^ f := Nat.one_lt_two_pow (by omega)
    have h2 := Nat.card_pos (α := (T ⊓ centralizer (L : Set G) : Subgroup G))
    nlinarith
  have hwc : ∀ g : G, rightConjugate (gmsV L T) g ≤ S → rightConjugate (gmsV L T) g = gmsV L T :=
    fun g hg => hR.rightConjugate_eq_of_psl2 h hF hf e hX hinv (hSc ▸ hg)
  by_cases hsc : ∃ v ∈ gmsV L T, ∃ g : G, g⁻¹ * v * g ∈ (S : Subgroup G) ∧ g⁻¹ * v * g ∉ gmsV L T
  · obtain ⟨U, hUV, g, hUg, hUgV, hbound⟩ :=
      GoldschmidtFour.goldschmidt_theorem_four_holds G S (gmsV L T) hVS hVel hwc hsc
    set U' := rightConjugate U g with hU'def
    have hU'S : U' ≤ R ⊔ T := hSc ▸ hUg
    have hU'el : IsElemAbelian 2 U' := isElemAbelian_map _ (isElemAbelian_of_le hVel hUV)
    have hU'2 : ∀ x ∈ U', x * x = 1 := fun x hx => by rw [← sq]; exact hU'el.2 x hx
    have hU'R : U' ⊓ R ≤ gmsV L T := fun x hx => hinv x (mem_inf.mp hx).2 (hU'2 x (mem_inf.mp hx).1)
    have hU'Rle : ¬ U' ≤ R := fun h1 => hUgV fun x hx => hU'R (mem_inf.mpr ⟨hx, h1 hx⟩)
    obtain ⟨w, hwU', hwR⟩ := IsConcreteLE.not_le_iff_exists.mp hU'Rle
    have hcard := hFr.card_le_two_mul h hf e hU'S hU'2
    have hinf : gmsV L T ⊓ U' = U' ⊓ R := by
      apply le_antisymm
      · exact le_inf inf_le_right (inf_le_left.trans (hR.gmsV_le_of_psl2 h hf e))
      · exact le_inf hU'R inf_le_left
    have hidx := relIndex_mul_card (gmsV L T) U'
    rw [hinf] at hidx
    have hpos : 0 < Nat.card (U' ⊓ R : Subgroup G) := Nat.card_pos
    have hidx2 : (gmsV L T).relIndex U' ≤ 2 := by nlinarith
    have hb := hbound w hwU'
    have hwN : w ∈ normalizer (gmsV L T : Set G) :=
      (hR.isSylowOf_sup_of_psl2 h hX htr).le (hU'S hwU')
    have hc := card_le_card_inf_centralizer_mul hVel.1 hwN
    have hlt := hFr.two_mul_card_lt h hf e hX (hU'S hwU') (hU'2 w hwU') hwR
      (inf_le_left : gmsV L T ⊓ centralizer ({w} : Set G) ≤ gmsV L T) inf_le_right
    have : Nat.card (gmsV L T) ≤ Nat.card (gmsV L T ⊓ centralizer ({w} : Set G) : Subgroup G) * 2 :=
      hc.trans (Nat.mul_le_mul_left _ (hb.trans hidx2))
    omega
  · push Not at hsc
    exact h.hyp.lemma34 S hVS hVel.1 hV1 hsc

end Sec3.IsR

namespace Push28Torus

variable {y d : G}

theorem sq_mem_of_exists
    (hd : Push28Torus L T R y d) (hR : Sec3.IsR L T R) (hy : Sec3.IsTorus L T y)
    (h313 : Lemma313 L T (2 ^ f)) (h : Sec3 G L T) (hF : Foundation) (hf : 3 ≤ f)
    (e : rankTwoQuot L ≃* PSL(2, GaloisField 2 f)) (hX : Sec3.Facts L T (2 ^ f)) {x₀ : G}
    (hx₀ : x₀ ∈ R) (hx₀V : x₀ ∉ gmsV L T) (hx₀A : x₀ * x₀ ∈ gmsA L T) :
    ∀ x ∈ R, x * x ∈ gmsA L T := by
  obtain ⟨-, hVel, -, -, -⟩ := hX.vFacts h hF
  intro x hx
  by_cases hxV : x ∈ gmsV L T
  · have : x * x = 1 := by rw [← sq]; exact hVel.2 x hxV
    rw [this]
    exact one_mem _
  obtain ⟨k, hk⟩ := hd.exists_conj_mem hR hy h313 h hF hf e hX hx hxV hx₀ hx₀V
  set a := (d ^ k)⁻¹ * x₀ * d ^ k with ha
  have haR : a ∈ R := by
    have := (mem_normalizer_iff.mp (inv_mem (pow_mem hd.mem_normalizer k)) x₀).mp hx₀
    simpa [ha] using this
  have haA : a * a ∈ gmsA L T := by
    have hdA : (d ^ k)⁻¹ ∈ normalizer (gmsA L T : Set G) :=
      inv_mem (pow_mem (h313.normalizer_le hd.mem_normalizer_V) k)
    have := (mem_normalizer_iff.mp hdA _).mp hx₀A
    have e1 : a * a = (d ^ k)⁻¹ * (x₀ * x₀) * (d ^ k)⁻¹⁻¹ := by rw [ha]; group
    rw [e1]
    exact this
  set v := x⁻¹ * a with hv
  have hvV : v⁻¹ ∈ gmsV L T := inv_mem hk
  have hxe : x = a * v⁻¹ := by rw [hv]; group
  have hc : a⁻¹ * v⁻¹ * a⁻¹⁻¹ * v⁻¹⁻¹ ∈ gmsA L T :=
    Sec3.conj_mul_inv_mem (hR.le_gmsTrans (inv_mem haR)) hvV
  have hvv : v⁻¹ * v⁻¹ = 1 := by rw [← sq]; exact hVel.2 _ hvV
  rw [hxe]
  have e2 : a * v⁻¹ * (a * v⁻¹) = (a * a) * (a⁻¹ * v⁻¹ * a⁻¹⁻¹ * v⁻¹⁻¹) * (v⁻¹ * v⁻¹) := by
    group
  rw [e2, hvv, mul_one]
  exact mul_mem haA hc

theorem sq_mem_gmsA
    (hd : Push28Torus L T R y d) (hR : Sec3.IsR L T R) (hy : Sec3.IsTorus L T y)
    (h313 : Lemma313 L T (2 ^ f)) (h : Sec3 G L T) (hF : Foundation) (hf : 3 ≤ f)
    (e : rankTwoQuot L ≃* PSL(2, GaloisField 2 f)) (hX : Sec3.Facts L T (2 ^ f))
    (htr : ∀ Q ∈ gmsDelta L T, ∃ u ∈ gmsTrans L T,
      rightConjugate (T ⊓ centralizer (L : Set G)) u⁻¹ = Q) :
    ∀ x ∈ R, x * x ∈ gmsA L T := by
  by_cases hex : ∃ x₀ ∈ R, x₀ ∉ gmsV L T ∧ x₀ * x₀ ∈ gmsA L T
  · obtain ⟨x₀, hx₀, hx₀V, hx₀A⟩ := hex
    exact hd.sq_mem_of_exists hR hy h313 h hF hf e hX hx₀ hx₀V hx₀A
  · push Not at hex
    exfalso
    refine hR.false_of_psl2 h hF hf e hX htr fun x hx hxx => ?_
    by_contra hxV
    apply hex x hx hxV
    rw [hxx]
    exact one_mem _

end Push28Torus

omit [Finite G] in
theorem commutator_mem_of_sq_mem' {R A : Subgroup G} (hRA : ∀ r ∈ R, ∀ a ∈ A, r * a = a * r)
    (hsq : ∀ x ∈ R, x * x ∈ A) {x y : G} (hx : x ∈ R) (hy : y ∈ R) :
    x * y * x⁻¹ * y⁻¹ ∈ A := by
  have e1 : x * y * x⁻¹ * y⁻¹ = (x * y * (x * y)) * (y⁻¹ * (x * x)⁻¹ * y) * (y * y)⁻¹ := by group
  have h1 : y⁻¹ * (x * x)⁻¹ * y = (x * x)⁻¹ := by
    rw [mul_assoc, ← hRA y hy _ (inv_mem (hsq x hx)), ← mul_assoc, inv_mul_cancel, one_mul]
  rw [e1, h1]
  exact mul_mem (mul_mem (hsq _ (mul_mem hx hy)) (inv_mem (hsq x hx))) (inv_mem (hsq y hy))

end CFSG.ComponentClassification.GMS78
