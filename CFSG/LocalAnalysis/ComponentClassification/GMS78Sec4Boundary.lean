module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec4SwapComm
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec4TorusFix
public import CFSG.LocalAnalysis.ComponentClassification.GMS78GapBoundaryFusion
public import CFSG.LocalAnalysis.ComponentClassification.GMS78GapBoundarySwap
public import CFSG.LocalAnalysis.ComponentClassification.GMS78GapHKS
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Lemma313L2
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Push28Fink
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Push29Defs
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec4Elem
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec4Homo

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

private theorem exists_ne_one_mem_center {P X : Subgroup G} (hP : IsPGroup 2 P) (hXP : X ≤ P)
    (hPX : P ≤ normalizer (X : Set G)) (hX : X ≠ ⊥) :
    ∃ x ∈ X, x ≠ 1 ∧ ∀ s ∈ P, s * x = x * s := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnil : Group.IsNilpotent P := hP.isNilpotent
  let X' : Subgroup P := X.subgroupOf P
  have hX'n : X'.Normal := ⟨fun x hx t => by
    show ((t * x * t⁻¹ : P) : G) ∈ X
    exact (mem_normalizer_iff.mp (hPX t.2) (x : G)).mp hx⟩
  have hX'ne : X' ≠ ⊥ := by
    intro h0
    apply hX
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hXP hx⟩ : P) ∈ X' := hx
    rw [h0, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.2 (congrArg Subtype.val this)
  obtain ⟨z, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hX'ne)
  have hzX : ((z : P) : G) ∈ X := (Subgroup.mem_inf.1 z.2).1
  have hzc := Subgroup.mem_center_iff.1 (Subgroup.mem_inf.1 z.2).2
  refine ⟨((z : P) : G), hzX, fun h => hz1 (Subtype.ext (Subtype.ext h)), fun s hs => ?_⟩
  exact congrArg Subtype.val (hzc ⟨s, hs⟩)

omit [Finite G] in
theorem card_fixed_normalizerMonoidHom (H : Subgroup G) {s : G}
    (hs : s ∈ normalizer (H : Set G)) :
    Nat.card {a : H // H.normalizerMonoidHom ⟨s, hs⟩ a = a} =
      Nat.card (H ⊓ centralizer ({s} : Set G) : Subgroup G) := by
  have key : ∀ a : H, H.normalizerMonoidHom ⟨s, hs⟩ a = a ↔ (a : G) * s = s * a := by
    intro a
    rw [← Subtype.coe_inj, normalizerMonoidHom_apply_apply_coe]
    change s * (a : G) * s⁻¹ = a ↔ _
    constructor
    · intro h1
      calc (a : G) * s = s * a * s⁻¹ * s := by rw [h1]
        _ = s * a := by group
    · intro h1
      calc s * (a : G) * s⁻¹ = a * s * s⁻¹ := by rw [h1]
        _ = a := by group
  exact Nat.card_congr
    { toFun := fun a => ⟨a.1, mem_inf.mpr ⟨a.1.2,
        mem_centralizer_singleton_iff.mpr ((key a.1).mp a.2)⟩⟩
      invFun := fun b => ⟨⟨b, (mem_inf.mp b.2).1⟩,
        (key _).mpr (mem_centralizer_singleton_iff.mp (mem_inf.mp b.2).2)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

omit [Finite G] in
theorem card_inf_centralizer_conj {K B : Subgroup G} {m w : G} (hm : rightConjugate K m = B) :
    Nat.card (K ⊓ centralizer ({m * w * m⁻¹} : Set G) : Subgroup G) =
      Nat.card (B ⊓ centralizer ({w} : Set G) : Subgroup G) := by
  have heq : rightConjugate (K ⊓ centralizer ({m * w * m⁻¹} : Set G)) m =
      B ⊓ centralizer ({w} : Set G) := by
    ext z
    rw [mem_rightConjugate_iff, mem_inf, mem_inf, ← hm, mem_rightConjugate_iff,
      mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
    refine and_congr_right fun _ => ⟨fun h1 => ?_, fun h1 => ?_⟩
    · have : m * (z * w) * m⁻¹ = m * (w * z) * m⁻¹ := by
        calc m * (z * w) * m⁻¹ = m * z * m⁻¹ * (m * w * m⁻¹) := by group
          _ = m * w * m⁻¹ * (m * z * m⁻¹) := h1
          _ = m * (w * z) * m⁻¹ := by group
      simpa using this
    · calc m * z * m⁻¹ * (m * w * m⁻¹) = m * (z * w) * m⁻¹ := by group
        _ = m * (w * z) * m⁻¹ := by rw [h1]
        _ = m * w * m⁻¹ * (m * z * m⁻¹) := by group
  rw [← heq, rightConjugate_card]

theorem two_mul_card_le_of_lt {H K : Subgroup G} (h : H < K) :
    2 * Nat.card H ≤ Nat.card K := by
  obtain ⟨m, hm⟩ := card_dvd_of_le h.le
  have hK : 0 < Nat.card K := Nat.card_pos
  have hm0 : m ≠ 0 := by rintro rfl; omega
  have hm1 : m ≠ 1 := by
    rintro rfl
    exact h.ne (eq_of_le_of_card_ge h.le (by omega))
  rw [hm]
  have : 2 ≤ m := by omega
  nlinarith [Nat.card_pos (α := H)]

theorem eq_of_sub_one_dvd {f c : ℕ} (hf : 3 ≤ f) (hc : c ∣ 2 ^ f) (h4 : 2 ^ f ≤ 4 * c)
    (hdvd : c - 1 ∣ 2 ^ f - 1) : c = 2 ^ f ∨ (f = 4 ∧ c = 4) ∨ (f = 3 ∧ c = 2) := by
  obtain ⟨j, hj, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hc
  have hpos : 0 < 2 ^ j := Nat.pos_of_ne_zero (by positivity)
  have hjf : j = f ∨ j + 1 = f ∨ j + 2 = f := by
    by_contra hne
    have h3 : j + 3 ≤ f := by omega
    have := Nat.pow_le_pow_right (by norm_num : 0 < 2) h3
    rw [pow_add] at this
    omega
  rcases hjf with rfl | rfl | rfl
  · exact Or.inl rfl
  · exfalso
    have hN : 4 ≤ 2 ^ j := by
      have := Nat.pow_le_pow_right (by norm_num : 0 < 2) (show 2 ≤ j by omega)
      simpa using this
    rw [pow_succ] at hdvd
    have h1 : 2 ^ j * 2 - 1 = 2 * (2 ^ j - 1) + 1 := by omega
    rw [h1] at hdvd
    have h2 := Nat.le_of_dvd one_pos ((Nat.dvd_add_right (dvd_mul_left _ 2)).mp hdvd)
    omega
  · have h1 : 2 ^ (j + 2) - 1 = 4 * (2 ^ j - 1) + 3 := by rw [pow_add]; omega
    rw [h1] at hdvd
    have h2 := Nat.le_of_dvd (by norm_num) ((Nat.dvd_add_right (dvd_mul_left _ 4)).mp hdvd)
    have hj2 : j ≤ 2 := by
      by_contra hj3
      have := Nat.pow_le_pow_right (by norm_num : 0 < 2) (show 3 ≤ j by omega)
      omega
    have hj1 : 1 ≤ j := by omega
    interval_cases j <;> norm_num

namespace Sec4Elem

variable {L T U₁ : Subgroup G} {f : ℕ} {y d : G}

theorem normalizer_W_le_normalizer_gmsA
    (hE : Sec4Elem L T U₁ (2 ^ f)) (h : Sec3 G L T) (hF : Foundation) (hf : 3 ≤ f)
    (e : rankTwoQuot L ≃* PSL(2, GaloisField 2 f)) (hX : Sec3.Facts L T (2 ^ f))
    (h313 : Lemma313 L T (2 ^ f))
    (hq : Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 2 ^ f) :
    normalizer ((U₁ ⊔ (T ⊓ centralizer (L : Set G)) : Subgroup G) : Set G) ≤
      normalizer (gmsA L T : Set G) := by
  intro n hn
  by_cases hnV : n ∈ normalizer (gmsV L T : Set G)
  · exact h313.normalizer_le hnV
  obtain ⟨hV₁, hU₁⟩ := hE.swap_of_not_mem h hF hf e hX hq hn hnV
  rw [← rightConjugate_eq_self_iff]
  ext x
  have h1 := SetLike.ext_iff.mp hU₁ x
  have h2 := SetLike.ext_iff.mp hV₁ x
  rw [mem_rightConjugate_iff] at h1 h2 ⊢
  rw [← hE.inf_V, mem_inf, mem_inf, h1, h2]
  exact and_comm

theorem inf_normalizer_V_eq
    (hE : Sec4Elem L T U₁ (2 ^ f)) (h : Sec3 G L T) (hF : Foundation) (hf : 3 ≤ f)
    (e : rankTwoQuot L ≃* PSL(2, GaloisField 2 f)) {P : Subgroup G} (hP : IsPGroup 2 P)
    (hS₀P : U₁ ⊔ T ≤ P) : P ⊓ normalizer (gmsV L T : Set G) = U₁ ⊔ T :=
  hE.sylow.eq_of_le (le_inf hS₀P (hE.S₀_le_normalizer_V h hF hf e)) inf_le_right
    (hP.to_le inf_le_left)

theorem card_le_four_mul
    (hE : Sec4Elem L T U₁ (2 ^ f)) (h : Sec3 G L T) (hF : Foundation) (hf : 3 ≤ f)
    (e : rankTwoQuot L ≃* PSL(2, GaloisField 2 f)) (hX : Sec3.Facts L T (2 ^ f))
    (hq : Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 2 ^ f) {P : Subgroup G}
    (hP : IsPGroup 2 P) (hS₀P : U₁ ⊔ T ≤ P) {X : Subgroup G} (hXP : X ≤ P)
    (hX2 : ∀ x ∈ X, x * x = 1) (hXW : X ⊓ (U₁ ⊔ (T ⊓ centralizer (L : Set G))) ≤ gmsA L T) :
    Nat.card X ≤ 4 * Nat.card (X ⊓ gmsA L T : Subgroup G) ∧
      (f = 3 → Nat.card X ≤ 2 * Nat.card (X ⊓ gmsA L T : Subgroup G)) := by
  have hPW := hE.le_normalizer_W h hF hf e hX hq hP hS₀P
  have hPV := hE.inf_normalizer_V_eq h hF hf e hP hS₀P
  have hf3 : f = 3 → U₁ ⊔ T ≤ U₁ ⊔ (T ⊓ centralizer (L : Set G)) := fun hf3 =>
    sup_le le_sup_left ((h.le_V_of_odd hf ⟨1, by omega⟩ e).trans hE.V_le)
  have h1 := hE.card_le_two_mul_inf_normalizer h hF hf e hX hq (hXP.trans hPW)
  have h2 : X ⊓ normalizer (gmsV L T : Set G) ≤ X ⊓ (U₁ ⊔ T) :=
    le_inf inf_le_left ((inf_le_inf_right _ hXP).trans_eq hPV)
  have h3 := hE.card_le_two_mul h hf e (inf_le_right : X ⊓ (U₁ ⊔ T) ≤ U₁ ⊔ T)
    (fun y hy => hX2 y (mem_inf.mp hy).1)
  have h4 : X ⊓ (U₁ ⊔ T) ⊓ (U₁ ⊔ (T ⊓ centralizer (L : Set G))) ≤ X ⊓ gmsA L T :=
    fun y hy => mem_inf.mpr ⟨(mem_inf.mp (mem_inf.mp hy).1).1,
      hXW (mem_inf.mpr ⟨(mem_inf.mp (mem_inf.mp hy).1).1, (mem_inf.mp hy).2⟩)⟩
  have h5 := card_le_of_le h4
  have h6 := card_le_of_le h2
  refine ⟨by omega, fun h3' => ?_⟩
  have h7 : X ⊓ (U₁ ⊔ T) ≤ X ⊓ gmsA L T := fun y hy =>
    mem_inf.mpr ⟨(mem_inf.mp hy).1,
      hXW (mem_inf.mpr ⟨(mem_inf.mp hy).1, hf3 h3' (mem_inf.mp hy).2⟩)⟩
  have h8 := card_le_of_le h7
  omega

theorem conj_mem_zpowers
    (hE : Sec4Elem L T U₁ (2 ^ f)) (h : Sec3 G L T) (hF : Foundation) (hf : 3 ≤ f)
    (e : rankTwoQuot L ≃* PSL(2, GaloisField 2 f)) (hX : Sec3.Facts L T (2 ^ f))
    (hq : Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 2 ^ f)
    (hO : Push28Out L T U₁ (2 ^ f) y d) (hy : Sec3.IsTorus L T y) {P : Subgroup G}
    (hP : IsPGroup 2 P) (hS₀P : U₁ ⊔ T ≤ P) {s : G} (hs : s ∈ P)
    (hsA : s ∈ normalizer (gmsA L T : Set G)) :
    (gmsA L T).normalizerMonoidHom ⟨s, hsA⟩ *
        (gmsA L T).normalizerMonoidHom ⟨d, hO.mem_normalizer_gmsA hy⟩ *
        ((gmsA L T).normalizerMonoidHom ⟨s, hsA⟩)⁻¹ ∈
      zpowers ((gmsA L T).normalizerMonoidHom ⟨d, hO.mem_normalizer_gmsA hy⟩) := by
  have hcard : Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = Nat.card (gmsA L T) := by
    rw [hq, (hX.sylow h).1]
  by_cases hsV : s ∈ normalizer (gmsV L T : Set G)
  · have hsS : s ∈ U₁ ⊔ T := by
      rw [← hE.inf_normalizer_V_eq h hF hf e hP hS₀P]
      exact mem_inf.mpr ⟨hs, hsV⟩
    obtain ⟨u, hu, t, ht, rfl⟩ := hE.exists_mul_eq_S₀ hsS
    have htA := h.le_normalizer_gmsA ht
    have hua : ∀ a ∈ gmsA L T, u * a * u⁻¹ = a := fun a ha => by
      rw [hE.comm hu (hE.A_le ha), mul_inv_cancel_right]
    have huA : u ∈ normalizer (gmsA L T : Set G) :=
      mem_normalizer_of_conj_mem_of_finite' fun a ha => by rw [hua a ha]; exact ha
    have hρu : (gmsA L T).normalizerMonoidHom ⟨u, huA⟩ = 1 :=
      MulEquiv.ext fun a => Subtype.ext (by
        rw [normalizerMonoidHom_apply_apply_coe]
        exact hua a a.2)
    have heq : (⟨u * t, hsA⟩ : normalizer (gmsA L T : Set G)) = ⟨u, huA⟩ * ⟨t, htA⟩ :=
      Subtype.ext rfl
    rw [heq, map_mul, hρu, one_mul]
    exact hO.conj_mem_zpowers_of_mem_T hy h ht
  · obtain ⟨hV₁, hU₁⟩ := hE.swap_of_not_mem h hF hf e hX hq
      (hE.le_normalizer_W h hF hf e hX hq hP hS₀P hs) hsV
    exact hO.conj_mem_zpowers_of_swap hy hE.toSec4Base hcard hE.lt hsA hV₁ hU₁

theorem card_sub_one_dvd_of_mem
    (hE : Sec4Elem L T U₁ (2 ^ f)) (h : Sec3 G L T) (hF : Foundation) (hf : 3 ≤ f)
    (e : rankTwoQuot L ≃* PSL(2, GaloisField 2 f)) (hX : Sec3.Facts L T (2 ^ f))
    (h313 : Lemma313 L T (2 ^ f))
    (hq : Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 2 ^ f)
    (hO : Push28Out L T U₁ (2 ^ f) y d) (hy : Sec3.IsTorus L T y) {P : Subgroup G}
    (hP : IsPGroup 2 P) (hS₀P : U₁ ⊔ T ≤ P) {s : G} (hs : s ∈ P) {a₀ : G}
    (ha₀ : a₀ ∈ gmsA L T) (ha₀1 : a₀ ≠ 1) (hsa₀ : s * a₀ = a₀ * s) :
    Nat.card (gmsA L T ⊓ centralizer ({s} : Set G) : Subgroup G) - 1 ∣ 2 ^ f - 1 := by
  have hsA : s ∈ normalizer (gmsA L T : Set G) :=
    hE.normalizer_W_le_normalizer_gmsA h hF hf e hX h313 hq
      (hE.le_normalizer_W h hF hf e hX hq hP hS₀P hs)
  have hfix : (gmsA L T).normalizerMonoidHom ⟨s, hsA⟩ ⟨a₀, ha₀⟩ = ⟨a₀, ha₀⟩ :=
    Subtype.ext (by
      rw [normalizerMonoidHom_apply_apply_coe]
      change s * a₀ * s⁻¹ = a₀
      rw [hsa₀, mul_inv_cancel_right])
  have hdvd := TorusFix.card_sub_one_dvd (hO.exists_apply_eq hy)
    (hE.conj_mem_zpowers h hF hf e hX hq hO hy hP hS₀P hs hsA)
    (fun h1 => ha₀1 (congrArg Subtype.val h1)) hfix
  rwa [card_fixed_normalizerMonoidHom, (hX.sylow h).1] at hdvd

theorem card_inf_centralizer_eq
    (hE : Sec4Elem L T U₁ (2 ^ f)) (h : Sec3 G L T) (hF : Foundation) (hf : 3 ≤ f)
    (e : rankTwoQuot L ≃* PSL(2, GaloisField 2 f)) (hX : Sec3.Facts L T (2 ^ f))
    (h313 : Lemma313 L T (2 ^ f))
    (hq : Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 2 ^ f)
    (hO : Push28Out L T U₁ (2 ^ f) y d) (hy : Sec3.IsTorus L T y) {P : Subgroup G}
    (hP : IsPGroup 2 P) (hS₀P : U₁ ⊔ T ≤ P) {s : G} (hs : s ∈ P) {a₀ : G}
    (ha₀ : a₀ ∈ gmsA L T) (ha₀1 : a₀ ≠ 1) (hsa₀ : s * a₀ = a₀ * s)
    (h4 : 2 ^ f ≤ 4 * Nat.card (gmsA L T ⊓ centralizer ({s} : Set G) : Subgroup G)) :
    Nat.card (gmsA L T ⊓ centralizer ({s} : Set G) : Subgroup G) = 2 ^ f ∨
      (f = 4 ∧ Nat.card (gmsA L T ⊓ centralizer ({s} : Set G) : Subgroup G) = 4) ∨
      (f = 3 ∧ Nat.card (gmsA L T ⊓ centralizer ({s} : Set G) : Subgroup G) = 2) :=
  eq_of_sub_one_dvd hf (by rw [← (hX.sylow h).1]; exact card_dvd_of_le inf_le_left) h4
    (hE.card_sub_one_dvd_of_mem h hF hf e hX h313 hq hO hy hP hS₀P hs ha₀ ha₀1 hsa₀)

theorem card_inf_centralizer_mul_eq
    (hE : Sec4Elem L T U₁ (2 ^ f)) (h : Sec3 G L T) (hF : Foundation) (hf : 3 ≤ f)
    (e : rankTwoQuot L ≃* PSL(2, GaloisField 2 f)) (hX : Sec3.Facts L T (2 ^ f))
    (h313 : Lemma313 L T (2 ^ f))
    (hq : Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 2 ^ f)
    (hO : Push28Out L T U₁ (2 ^ f) y d) (hy : Sec3.IsTorus L T y) {P : Subgroup G}
    (hP : IsPGroup 2 P) (hS₀P : U₁ ⊔ T ≤ P) (hf4 : f = 4) {s₁ s₂ : G} (h₁ : s₁ ∈ P)
    (h₂ : s₂ ∈ P) (h₁₁ : s₁ * s₁ = 1) (h₂₂ : s₂ * s₂ = 1)
    (hc₁ : Nat.card (gmsA L T ⊓ centralizer ({s₁} : Set G) : Subgroup G) = 4)
    (hc₂ : Nat.card (gmsA L T ⊓ centralizer ({s₂} : Set G) : Subgroup G) = 4) {a₀ : G}
    (ha₀ : a₀ ∈ gmsA L T) (ha₀1 : a₀ ≠ 1) (ha₀P : ∀ s ∈ P, s * a₀ = a₀ * s) :
    Nat.card (gmsA L T ⊓ centralizer ({s₁ * s₂} : Set G) : Subgroup G) = 2 ^ f := by
  have hPA : P ≤ normalizer (gmsA L T : Set G) :=
    (hE.le_normalizer_W h hF hf e hX hq hP hS₀P).trans
      (hE.normalizer_W_le_normalizer_gmsA h hF hf e hX h313 hq)
  set ρ := (gmsA L T).normalizerMonoidHom
  set δ := ρ ⟨d, hO.mem_normalizer_gmsA hy⟩
  have htr := hO.exists_apply_eq hy
  have ha₀' : (⟨a₀, ha₀⟩ : gmsA L T) ≠ 1 := fun h1 => ha₀1 (congrArg Subtype.val h1)
  have hfix : ∀ {s : G} (hs : s ∈ P), ρ ⟨s, hPA hs⟩ ⟨a₀, ha₀⟩ = ⟨a₀, ha₀⟩ := fun {s} hs =>
    Subtype.ext (by
      rw [normalizerMonoidHom_apply_apply_coe]
      change s * a₀ * s⁻¹ = a₀
      rw [ha₀P s hs, mul_inv_cancel_right])
  have hinv : ∀ {s : G} (hs : s ∈ P), s * s = 1 → ρ ⟨s, hPA hs⟩ * ρ ⟨s, hPA hs⟩ = 1 :=
    fun {s} hs hss => by
      rw [← map_mul]
      have : (⟨s, hPA hs⟩ * ⟨s, hPA hs⟩ : normalizer (gmsA L T : Set G)) = 1 := Subtype.ext hss
      rw [this, map_one]
  have hA16 : Nat.card (gmsA L T) = 16 := by rw [(hX.sylow h).1, hf4]; norm_num
  have hcomm := TorusFix.commute_mul_of_card_eq_four hA16 htr
    (hE.conj_mem_zpowers h hF hf e hX hq hO hy hP hS₀P h₁ (hPA h₁))
    (hE.conj_mem_zpowers h hF hf e hX hq hO hy hP hS₀P h₂ (hPA h₂)) (hinv h₁ h₁₁) (hinv h₂ h₂₂)
    ha₀' ha₀' (hfix h₁) (hfix h₂) (by rw [card_fixed_normalizerMonoidHom]; exact hc₁)
    (by rw [card_fixed_normalizerMonoidHom]; exact hc₂)
  have h₁₂ : s₁ * s₂ ∈ P := mul_mem h₁ h₂
  have hmul : ρ ⟨s₁, hPA h₁⟩ * ρ ⟨s₂, hPA h₂⟩ = ρ ⟨s₁ * s₂, hPA h₁₂⟩ := by
    rw [← map_mul]; rfl
  rw [hmul] at hcomm
  have hn : ρ ⟨s₁ * s₂, hPA h₁₂⟩ * δ * (ρ ⟨s₁ * s₂, hPA h₁₂⟩)⁻¹ ∈ zpowers δ := by
    rw [hcomm.eq, mul_inv_cancel_right]
    exact mem_zpowers δ
  have h1 := TorusFix.card_inf_centralizer_add_one htr hn ha₀' (hfix h₁₂)
  have h2 : (zpowers δ ⊓ centralizer {ρ ⟨s₁ * s₂, hPA h₁₂⟩} : Subgroup (MulAut (gmsA L T))) =
      zpowers δ :=
    inf_eq_left.mpr (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hcomm.eq.symm))
  rw [h2, card_fixed_normalizerMonoidHom] at h1
  have h3 : Nat.card (zpowers δ) + 1 = 2 ^ f := by
    rw [← (hX.sylow h).1]
    exact TorusFix.card_zpowers_add_one htr ha₀'
  omega

theorem false_of_rightConjugate_le
    (hE : Sec4Elem L T U₁ (2 ^ f)) (h : Sec3 G L T) (hF : Foundation) (hf : 3 ≤ f)
    (e : rankTwoQuot L ≃* PSL(2, GaloisField 2 f)) (hX : Sec3.Facts L T (2 ^ f))
    (h313 : Lemma313 L T (2 ^ f))
    (hq : Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 2 ^ f)
    (hfus : ∃ t ∈ T ⊓ centralizer (L : Set G), t ≠ 1 ∧ ∃ g : G, g * t * g⁻¹ ∈ U₁)
    (hO : Push28Out L T U₁ (2 ^ f) y d) (hy : Sec3.IsTorus L T y) (P : Sylow 2 G)
    (hS₀P : U₁ ⊔ T ≤ P) {k : G} (hkP : rightConjugate (gmsA L T) k ≤ P) {a₀ : G}
    (ha₀ : a₀ ∈ gmsA L T) (ha₀1 : a₀ ≠ 1) (ha₀P : ∀ s ∈ (P : Subgroup G), s * a₀ = a₀ * s)
    (ha₀k : k * a₀ * k⁻¹ ∉ gmsA L T) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP := P.isPGroup'
  have hPW := hE.le_normalizer_W h hF hf e hX hq hP hS₀P
  have hPA : (P : Subgroup G) ≤ normalizer (gmsA L T : Set G) :=
    hPW.trans (hE.normalizer_W_le_normalizer_gmsA h hF hf e hX h313 hq)
  obtain ⟨-, hVel, -, -, -⟩ := hX.vFacts h hF
  have hAel : IsElemAbelian 2 (gmsA L T) := isElemAbelian_of_le hVel le_sup_left
  have hAc : Nat.card (gmsA L T) = 2 ^ f := (hX.sylow h).1
  have hcard : Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = Nat.card (gmsA L T) := by
    rw [hq, hAc]
  have h8 : 8 ≤ 2 ^ f := by
    have := Nat.pow_le_pow_right (by norm_num : 0 < 2) hf
    simpa using this
  set B := rightConjugate (gmsA L T) k with hBdef
  have hBel : IsElemAbelian 2 B := isElemAbelian_map _ hAel
  have hB2 : ∀ x ∈ B, x * x = 1 := fun x hx => by rw [← sq]; exact hBel.2 x hx
  have hBc : Nat.card B = 2 ^ f := by rw [hBdef, rightConjugate_card, hAc]
  have hBW : B ⊓ (U₁ ⊔ (T ⊓ centralizer (L : Set G))) ≤ gmsA L T := fun x hx =>
    hE.mem_A_of_conj_mem h hF hf e hX h313 hq hfus (mem_inf.mp hx).2 (hB2 x (mem_inf.mp hx).1)
      ((mem_rightConjugate_iff _ _ _).mp (mem_inf.mp hx).1)
  obtain ⟨hi4, -⟩ := hE.card_le_four_mul h hF hf e hX hq hP hS₀P hkP hB2 hBW
  have ha₀B : a₀ ∉ B := fun h1 => ha₀k ((mem_rightConjugate_iff _ _ _).mp h1)
  have hcent : ∀ b ∈ B, ∀ a ∈ gmsA L T, b * a = a * b := by
    intro b hb
    have hle : B ⊓ gmsA L T ≤ gmsA L T ⊓ centralizer ({b} : Set G) := fun z hz =>
      mem_inf.mpr ⟨(mem_inf.mp hz).2, mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (hBel.1.is_comm.comm ⟨z, (mem_inf.mp hz).1⟩ ⟨b, hb⟩))⟩
    have ha₀C : a₀ ∈ gmsA L T ⊓ centralizer ({b} : Set G) :=
      mem_inf.mpr ⟨ha₀, mem_centralizer_singleton_iff.mpr (ha₀P b (hkP hb)).symm⟩
    have hlt : B ⊓ gmsA L T < gmsA L T ⊓ centralizer ({b} : Set G) := by
      refine lt_of_le_of_ne hle fun heq => ha₀B ?_
      rw [← heq] at ha₀C
      exact (mem_inf.mp ha₀C).1
    have h2 := two_mul_card_le_of_lt hlt
    have h2' : 2 ^ f ≤ 2 * Nat.card (gmsA L T ⊓ centralizer ({b} : Set G) : Subgroup G) := by
      omega
    rcases hE.card_inf_centralizer_eq h hF hf e hX h313 hq hO hy hP hS₀P (hkP hb) ha₀ ha₀1
        (ha₀P b (hkP hb)) (by omega) with hC | ⟨hf4, hC⟩ | ⟨hf3, hC⟩
    · have hAC : gmsA L T ⊓ centralizer ({b} : Set G) = gmsA L T :=
        eq_of_le_of_card_ge inf_le_left (by rw [hC, hAc])
      intro a ha
      rw [← hAC] at ha
      exact (mem_centralizer_singleton_iff.mp (mem_inf.mp ha).2).symm
    · rw [hf4, hC] at h2'
      norm_num at h2'
    · rw [hf3, hC] at h2'
      norm_num at h2'
  have hBN : B ⊓ normalizer (gmsV L T : Set G) ≤ B ⊓ gmsA L T := by
    intro z hz
    have hzS : z ∈ U₁ ⊔ T := by
      rw [← hE.inf_normalizer_V_eq h hF hf e hP hS₀P]
      exact mem_inf.mpr ⟨hkP (mem_inf.mp hz).1, (mem_inf.mp hz).2⟩
    exact mem_inf.mpr ⟨(mem_inf.mp hz).1, hBW (mem_inf.mpr ⟨(mem_inf.mp hz).1,
      hE.mem_W_of_commute h hf e hzS (hcent z (mem_inf.mp hz).1)⟩)⟩
  have h2B : Nat.card B ≤ 2 * Nat.card (B ⊓ gmsA L T : Subgroup G) := by
    have h1 := hE.card_le_two_mul_inf_normalizer h hF hf e hX hq (hkP.trans hPW)
    have h3 := card_le_of_le hBN
    omega
  have hBA : ¬ B ≤ gmsA L T := fun hle => ha₀B (by
    rw [eq_of_le_of_card_ge hle (by rw [hBc, hAc])]
    exact ha₀)
  obtain ⟨b₁, hb₁B, hb₁A⟩ := IsConcreteLE.not_le_iff_exists.mp hBA
  have hb₁V : b₁ ∉ normalizer (gmsV L T : Set G) := fun h1 =>
    hb₁A (mem_inf.mp (hBN (mem_inf.mpr ⟨hb₁B, h1⟩))).2
  obtain ⟨-, hU₁⟩ := hE.swap_of_not_mem h hF hf e hX hq (hPW (hkP hb₁B)) hb₁V
  have hxT : ∀ t ∈ T ⊓ centralizer (L : Set G), b₁ * t * b₁⁻¹ ∈ U₁ := fun t ht =>
    (mem_rightConjugate_iff _ _ _).mp (by rw [hU₁]; exact mem_sup_right ht)
  have hBAlt : B ⊓ gmsA L T < B := lt_of_le_of_ne inf_le_left fun heq => hb₁A (by
    rw [← heq] at hb₁B
    exact (mem_inf.mp hb₁B).2)
  have hBAc : 2 * Nat.card (B ⊓ gmsA L T : Subgroup G) = 2 ^ f := by
    have := two_mul_card_le_of_lt hBAlt
    omega
  obtain ⟨d₁, hd₁, hd₁1⟩ : ∃ d₁ ∈ B ⊓ gmsA L T, d₁ ≠ 1 := by
    by_contra hne
    push Not at hne
    have := (eq_bot_iff_forall _).mpr hne
    rw [this, card_bot] at hBAc
    omega
  obtain ⟨w, hwW, hw⟩ := hE.toSec4Base.exists_conj_eq_mul_of_swap hcard (hB2 b₁ hb₁B) hxT
    (hcent b₁ hb₁B) (mem_inf.mp hd₁).2
  have hwA : ∀ a ∈ gmsA L T, w * a = a * w := by
    intro a ha
    obtain ⟨u, hu, t, ht, rfl⟩ := hE.exists_mul_eq hwW
    have h1 : u * a = a * u := hE.comm hu (hE.A_le ha)
    have h2 : t * a = a * t :=
      (mem_centralizer_iff.mp (mem_inf.mp ht).2 a (mem_inf.mp (mem_inf.mp ha).1).2).symm
    calc u * t * a = u * (t * a) := by group
      _ = u * (a * t) := by rw [h2]
      _ = u * a * t := by group
      _ = a * u * t := by rw [h1]
      _ = a * (u * t) := by group
  have hBsup : (B ⊓ gmsA L T) ⊔ zpowers b₁ = B := by
    have hle : (B ⊓ gmsA L T) ⊔ zpowers b₁ ≤ B := sup_le inf_le_left (zpowers_le.mpr hb₁B)
    have hlt : B ⊓ gmsA L T < (B ⊓ gmsA L T) ⊔ zpowers b₁ := by
      refine lt_of_le_of_ne le_sup_left fun heq => hb₁A ?_
      have : b₁ ∈ (B ⊓ gmsA L T) ⊔ zpowers b₁ := mem_sup_right (mem_zpowers b₁)
      rw [← heq] at this
      exact (mem_inf.mp this).2
    exact eq_of_le_of_card_ge hle (by have := two_mul_card_le_of_lt hlt; omega)
  have hwB : ∀ z ∈ B, w * z * w⁻¹ ∈ B := by
    have hle : (B ⊓ gmsA L T) ⊔ zpowers b₁ ≤ B.comap (MulAut.conj w).toMonoidHom := by
      refine sup_le (fun z hz => ?_) (zpowers_le.mpr ?_)
      · rw [mem_comap]
        show w * z * w⁻¹ ∈ B
        rw [hwA z (mem_inf.mp hz).2, mul_inv_cancel_right]
        exact (mem_inf.mp hz).1
      · rw [mem_comap]
        show w * b₁ * w⁻¹ ∈ B
        rw [hw]
        exact mul_mem hb₁B (mem_inf.mp hd₁).1
    intro z hz
    exact hle (by rw [hBsup]; exact hz)
  have hCw : 2 * Nat.card (B ⊓ centralizer ({w} : Set G) : Subgroup G) = 2 ^ f := by
    have hle : B ⊓ gmsA L T ≤ B ⊓ centralizer ({w} : Set G) := fun z hz =>
      mem_inf.mpr ⟨(mem_inf.mp hz).1,
        mem_centralizer_singleton_iff.mpr (hwA z (mem_inf.mp hz).2).symm⟩
    have hlt : B ⊓ centralizer ({w} : Set G) < B := by
      refine lt_of_le_of_ne inf_le_left fun heq => hd₁1 ?_
      have hb : b₁ ∈ B ⊓ centralizer ({w} : Set G) := by rw [heq]; exact hb₁B
      have h1 := mem_centralizer_singleton_iff.mp (mem_inf.mp hb).2
      have h2 : w * b₁ * w⁻¹ = b₁ := by rw [← h1]; group
      rw [hw] at h2
      simpa using h2
    have h1 := card_le_of_le hle
    have h2 := two_mul_card_le_of_lt hlt
    omega
  have hw'A : k * w * k⁻¹ ∈ normalizer (gmsA L T : Set G) := by
    refine mem_normalizer_of_conj_mem_of_finite' fun a ha => ?_
    have hz : k⁻¹ * a * k ∈ B := by
      rw [hBdef, mem_rightConjugate_iff, show k * (k⁻¹ * a * k) * k⁻¹ = a by group]
      exact ha
    have h1 := hwB _ hz
    rw [hBdef, mem_rightConjugate_iff] at h1
    rw [show k * w * k⁻¹ * a * (k * w * k⁻¹)⁻¹ = k * (w * (k⁻¹ * a * k) * w⁻¹) * k⁻¹ by group]
    exact h1
  have hwP : w ∈ (P : Subgroup G) :=
    hS₀P (sup_le_sup_left (inf_le_left : T ⊓ centralizer (L : Set G) ≤ T) U₁ hwW)
  have hw'2 : IsPGroup 2 (zpowers (k * w * k⁻¹)) := by
    have := (hP.to_le (zpowers_le.mpr hwP)).map (MulAut.conj k).toMonoidHom
    rwa [MonoidHom.map_zpowers] at this
  have hPsyl : IsSylowOf 2 (P : Subgroup G) (normalizer (gmsA L T : Set G)) :=
    (isSylowOf_of_card le_top (by rw [card_top]; exact P.card_eq_multiplicity)).of_le hPA le_top
  obtain ⟨n, hnA, hn⟩ := exists_conj_le_of_isSylowOf hPsyl (zpowers_le.mpr hw'A) hw'2
  have hs : n * (k * w * k⁻¹) * n⁻¹ ∈ (P : Subgroup G) := hn _ (mem_zpowers _)
  have hm : rightConjugate (gmsA L T) (n * k) = B := by
    ext z
    rw [hBdef, mem_rightConjugate_iff, mem_rightConjugate_iff,
      show n * k * z * (n * k)⁻¹ = n * (k * z * k⁻¹) * n⁻¹ by group]
    exact (mem_normalizer_iff.mp hnA _).symm
  have hsc : Nat.card (gmsA L T ⊓ centralizer ({n * (k * w * k⁻¹) * n⁻¹} : Set G) :
      Subgroup G) = Nat.card (B ⊓ centralizer ({w} : Set G) : Subgroup G) := by
    rw [show n * (k * w * k⁻¹) * n⁻¹ = n * k * w * (n * k)⁻¹ by group]
    exact card_inf_centralizer_conj hm
  rcases hE.card_inf_centralizer_eq h hF hf e hX h313 hq hO hy hP hS₀P hs ha₀ ha₀1 (ha₀P _ hs)
      (by omega) with hC | ⟨hf4, hC⟩ | ⟨hf3, hC⟩
  · omega
  · rw [hf4] at hCw
    omega
  · rw [hf3] at hCw
    omega

theorem false_of_conj_mem_of_commute
    (hE : Sec4Elem L T U₁ (2 ^ f)) (h : Sec3 G L T) (hF : Foundation) (hf : 3 ≤ f)
    (e : rankTwoQuot L ≃* PSL(2, GaloisField 2 f)) (hX : Sec3.Facts L T (2 ^ f))
    (h313 : Lemma313 L T (2 ^ f))
    (hq : Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 2 ^ f)
    (hfus : ∃ t ∈ T ⊓ centralizer (L : Set G), t ≠ 1 ∧ ∃ g : G, g * t * g⁻¹ ∈ U₁)
    (hO : Push28Out L T U₁ (2 ^ f) y d) (hy : Sec3.IsTorus L T y) (P : Sylow 2 G)
    (hS₀P : U₁ ⊔ T ≤ P) {x : G} (hxA' : x ∉ gmsA L T) (hxA : ∀ a ∈ gmsA L T, x * a = a * x)
    {g : G} (hg : g * x * g⁻¹ ∈ gmsA L T) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP := P.isPGroup'
  have hPA : (P : Subgroup G) ≤ normalizer (gmsA L T : Set G) :=
    (hE.le_normalizer_W h hF hf e hX hq hP hS₀P).trans
      (hE.normalizer_W_le_normalizer_gmsA h hF hf e hX h313 hq)
  have hAP : gmsA L T ≤ (P : Subgroup G) := hE.A_le.trans (le_sup_left.trans hS₀P)
  have hAne : gmsA L T ≠ ⊥ := by
    intro hb
    have hAc := (hX.sylow h).1
    rw [hb, card_bot] at hAc
    have : 1 < 2 ^ f := Nat.one_lt_two_pow (by omega)
    omega
  obtain ⟨a₀, ha₀, ha₀1, ha₀P⟩ := exists_ne_one_mem_center hP hAP hPA hAne
  have hgx1 : g * x * g⁻¹ ≠ 1 := fun h1 => hxA' (by
    have : x = 1 := by
      have := congrArg (fun z => g⁻¹ * z * g) h1
      simpa [mul_assoc] using this
    rw [this]
    exact one_mem _)
  obtain ⟨m, hm⟩ := hy.trans _ hg a₀ ha₀ hgx1 ha₀1
  set c := (y ^ m)⁻¹ * g with hcdef
  have hcx : c * x * c⁻¹ = a₀ := by rw [← hm, hcdef]; group
  have hPC : IsSylowOf 2 (P : Subgroup G) (centralizer ({a₀} : Set G)) :=
    (isSylowOf_of_card le_top (by rw [card_top]; exact P.card_eq_multiplicity)).of_le
      (fun s hs => mem_centralizer_singleton_iff.mpr (ha₀P s hs)) le_top
  set Q := ((P : Subgroup G) ⊓ centralizer ({x} : Set G)).map (MulAut.conj c).toMonoidHom
    with hQdef
  have hQC : Q ≤ centralizer ({a₀} : Set G) := by
    rintro _ ⟨z, hz, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have hzx : z * x = x * z := mem_centralizer_singleton_iff.mp (mem_inf.mp hz).2
    show c * z * c⁻¹ * a₀ = a₀ * (c * z * c⁻¹)
    rw [← hcx]
    calc c * z * c⁻¹ * (c * x * c⁻¹) = c * (z * x) * c⁻¹ := by group
      _ = c * (x * z) * c⁻¹ := by rw [hzx]
      _ = c * x * c⁻¹ * (c * z * c⁻¹) := by group
  have hQp : IsPGroup 2 Q := (hP.to_le inf_le_left).map _
  obtain ⟨n, hn, hnQ⟩ := exists_conj_le_of_isSylowOf hPC hQC hQp
  have hna : n * a₀ = a₀ * n := mem_centralizer_singleton_iff.mp hn
  have hk : (n * c)⁻¹ * a₀ * ((n * c)⁻¹)⁻¹ = x := by
    have hna' : n⁻¹ * a₀ * n = a₀ := by
      calc n⁻¹ * a₀ * n = n⁻¹ * (a₀ * n) := by group
        _ = n⁻¹ * (n * a₀) := by rw [hna]
        _ = a₀ := by group
    calc (n * c)⁻¹ * a₀ * ((n * c)⁻¹)⁻¹ = c⁻¹ * (n⁻¹ * a₀ * n) * c := by group
      _ = c⁻¹ * (c * x * c⁻¹) * c := by rw [hna', hcx]
      _ = x := by group
  have hkP : rightConjugate (gmsA L T) (n * c)⁻¹ ≤ P := by
    intro z hz
    rw [mem_rightConjugate_iff] at hz
    have haC : (n * c)⁻¹ * z * ((n * c)⁻¹)⁻¹ ∈ (P : Subgroup G) ⊓ centralizer ({x} : Set G) :=
      mem_inf.mpr ⟨hAP hz, mem_centralizer_singleton_iff.mpr (hxA _ hz).symm⟩
    have h1 := hnQ _ (mem_map.mpr ⟨_, haC, rfl⟩)
    have heq : n * ((MulAut.conj c).toMonoidHom ((n * c)⁻¹ * z * ((n * c)⁻¹)⁻¹)) * n⁻¹ = z := by
      show n * (c * ((n * c)⁻¹ * z * ((n * c)⁻¹)⁻¹) * c⁻¹) * n⁻¹ = z
      group
    rwa [heq] at h1
  exact hE.false_of_rightConjugate_le h hF hf e hX h313 hq hfus hO hy P hS₀P hkP ha₀ ha₀1 ha₀P
    (by rw [hk]; exact hxA')

theorem false_of_root
    (hE : Sec4Elem L T U₁ (2 ^ f)) (h : Sec3 G L T) (hF : Foundation) (hf : 3 ≤ f)
    (e : rankTwoQuot L ≃* PSL(2, GaloisField 2 f)) (hX : Sec3.Facts L T (2 ^ f))
    (h313 : Lemma313 L T (2 ^ f))
    (hq : Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 2 ^ f)
    (hfus : ∃ t ∈ T ⊓ centralizer (L : Set G), t ≠ 1 ∧ ∃ g : G, g * t * g⁻¹ ∈ U₁)
    (hO : Push28Out L T U₁ (2 ^ f) y d) (hy : Sec3.IsTorus L T y) (P : Sylow 2 G)
    (hS₀P : U₁ ⊔ T ≤ P) {X : Subgroup G} (hXP : X ≤ P) (hXel : IsElemAbelian 2 X)
    (hXr : ∀ z ∈ X, ∃ g : G, g * z * g⁻¹ ∈ gmsA L T) (hXA : ¬ X ≤ gmsA L T)
    (hXc : ∀ z ∈ X, z ∉ gmsA L T → 2 ^ f ≤
      (gmsA L T).relIndex X * Nat.card (gmsA L T ⊓ centralizer ({z} : Set G) : Subgroup G)) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP := P.isPGroup'
  have hPA : (P : Subgroup G) ≤ normalizer (gmsA L T : Set G) :=
    (hE.le_normalizer_W h hF hf e hX hq hP hS₀P).trans
      (hE.normalizer_W_le_normalizer_gmsA h hF hf e hX h313 hq)
  have hAP : gmsA L T ≤ (P : Subgroup G) := hE.A_le.trans (le_sup_left.trans hS₀P)
  have hAc := (hX.sylow h).1
  have hAne : gmsA L T ≠ ⊥ := by
    intro hb
    rw [hb, card_bot] at hAc
    have : 1 < 2 ^ f := Nat.one_lt_two_pow (by omega)
    omega
  obtain ⟨a₀, ha₀, ha₀1, ha₀P⟩ := exists_ne_one_mem_center hP hAP hPA hAne
  have hX2 : ∀ z ∈ X, z * z = 1 := fun z hz => by rw [← sq]; exact hXel.2 z hz
  have hXW : X ⊓ (U₁ ⊔ (T ⊓ centralizer (L : Set G))) ≤ gmsA L T := fun z hz => by
    obtain ⟨g, hg⟩ := hXr z (mem_inf.mp hz).1
    exact hE.mem_A_of_conj_mem h hF hf e hX h313 hq hfus (mem_inf.mp hz).2
      (hX2 z (mem_inf.mp hz).1) hg
  obtain ⟨hi4, hi2⟩ := hE.card_le_four_mul h hF hf e hX hq hP hS₀P hXP hX2 hXW
  have hidx := relIndex_mul_card (gmsA L T) X
  rw [inf_comm (gmsA L T) X] at hidx
  have hpos : 0 < Nat.card (X ⊓ gmsA L T : Subgroup G) := Nat.card_pos
  have hr4 : (gmsA L T).relIndex X ≤ 4 := Nat.le_of_mul_le_mul_right (hidx.le.trans hi4) hpos
  have hr2 : f = 3 → (gmsA L T).relIndex X ≤ 2 := fun h3 =>
    Nat.le_of_mul_le_mul_right (hidx.le.trans (hi2 h3)) hpos
  have hz : ∀ z ∈ X, z ∉ gmsA L T →
      f = 4 ∧ Nat.card (gmsA L T ⊓ centralizer ({z} : Set G) : Subgroup G) = 4 := by
    intro z hzX hzA
    have hc := hXc z hzX hzA
    have h4 : 2 ^ f ≤ 4 * Nat.card (gmsA L T ⊓ centralizer ({z} : Set G) : Subgroup G) :=
      hc.trans (Nat.mul_le_mul_right _ hr4)
    rcases hE.card_inf_centralizer_eq h hF hf e hX h313 hq hO hy hP hS₀P (hXP hzX) ha₀ ha₀1
        (ha₀P z (hXP hzX)) h4 with hC | hC | ⟨hf3, hC⟩
    · exfalso
      have hAC : gmsA L T ⊓ centralizer ({z} : Set G) = gmsA L T :=
        eq_of_le_of_card_ge inf_le_left (by rw [hC, hAc])
      have hzC : ∀ a ∈ gmsA L T, z * a = a * z := fun a ha => by
        rw [← hAC] at ha
        exact (mem_centralizer_singleton_iff.mp (mem_inf.mp ha).2).symm
      obtain ⟨g, hg⟩ := hXr z hzX
      exact hE.false_of_conj_mem_of_commute h hF hf e hX h313 hq hfus hO hy P hS₀P hzA hzC hg
    · exact hC
    · exfalso
      have h2 := hr2 hf3
      rw [hC, hf3] at hc
      have : (gmsA L T).relIndex X * 2 ≤ 4 := by omega
      norm_num at hc
      omega
  obtain ⟨z₁, hz₁X, hz₁A⟩ := IsConcreteLE.not_le_iff_exists.mp hXA
  obtain ⟨hf4, hc₁⟩ := hz z₁ hz₁X hz₁A
  have hr : (gmsA L T).relIndex X = 4 := by
    have := hXc z₁ hz₁X hz₁A
    rw [hc₁, hf4] at this
    norm_num at this
    omega
  by_cases hall : ∀ x₁ ∈ X, ∀ x₂ ∈ X, x₁ ∉ X ⊓ gmsA L T → x₂ ∉ X ⊓ gmsA L T →
      x₁ * x₂ ∈ X ⊓ gmsA L T
  · have := card_le_two_mul_of_mul_mem hall
    rw [hr] at hidx
    omega
  · push Not at hall
    obtain ⟨x₁, hx₁, x₂, hx₂, hx₁A, hx₂A, hx₁₂⟩ := hall
    have h1 : x₁ ∉ gmsA L T := fun h0 => hx₁A (mem_inf.mpr ⟨hx₁, h0⟩)
    have h2 : x₂ ∉ gmsA L T := fun h0 => hx₂A (mem_inf.mpr ⟨hx₂, h0⟩)
    have h12 : x₁ * x₂ ∉ gmsA L T := fun h0 => hx₁₂ (mem_inf.mpr ⟨mul_mem hx₁ hx₂, h0⟩)
    obtain ⟨-, hc₁'⟩ := hz x₁ hx₁ h1
    obtain ⟨-, hc₂'⟩ := hz x₂ hx₂ h2
    obtain ⟨-, hc₁₂⟩ := hz _ (mul_mem hx₁ hx₂) h12
    have := hE.card_inf_centralizer_mul_eq h hF hf e hX h313 hq hO hy hP hS₀P hf4 (hXP hx₁)
      (hXP hx₂) (hX2 _ hx₁) (hX2 _ hx₂) hc₁' hc₂' ha₀ ha₀1 ha₀P
    rw [hc₁₂, hf4] at this
    norm_num at this

theorem false_of_push28Out
    (hE : Sec4Elem L T U₁ (2 ^ f)) (h : Sec3 G L T) (hF : Foundation) (hf : 3 ≤ f)
    (e : rankTwoQuot L ≃* PSL(2, GaloisField 2 f)) (hX : Sec3.Facts L T (2 ^ f))
    (h313 : Lemma313 L T (2 ^ f))
    (hq : Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 2 ^ f)
    (hfus : ∃ t ∈ T ⊓ centralizer (L : Set G), t ≠ 1 ∧ ∃ g : G, g * t * g⁻¹ ∈ U₁)
    (hO : Push28Out L T U₁ (2 ^ f) y d) (hy : Sec3.IsTorus L T y) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hVel, -, -, -⟩ := hX.vFacts h hF
  have hAel : IsElemAbelian 2 (gmsA L T) := isElemAbelian_of_le hVel le_sup_left
  have hAc := (hX.sylow h).1
  obtain ⟨P, hS₀P⟩ := hE.sylow.isPGroup.exists_le_sylow
  have hNA : (P : Subgroup G) ≤ normalizer (gmsA L T : Set G) :=
    (hE.le_normalizer_W h hF hf e hX hq P.isPGroup' hS₀P).trans
      (hE.normalizer_W_le_normalizer_gmsA h hF hf e hX h313 hq)
  have hwc : ∀ g : G, rightConjugate (gmsA L T) g ≤ (P : Subgroup G) →
      rightConjugate (gmsA L T) g = gmsA L T := by
    intro g hg
    have hEel : IsElemAbelian 2 (rightConjugate (gmsA L T) g) := isElemAbelian_map _ hAel
    by_contra hne
    have hEA : ¬ rightConjugate (gmsA L T) g ≤ gmsA L T := fun h1 =>
      hne (Subgroup.eq_of_le_of_card_ge h1 (by rw [rightConjugate_card]))
    refine hE.false_of_root h hF hf e hX h313 hq hfus hO hy P hS₀P hg hEel
      (fun z hz => ⟨g, (mem_rightConjugate_iff _ _ _).mp hz⟩) hEA fun z hz _ => ?_
    have hidx := relIndex_mul_card (gmsA L T) (rightConjugate (gmsA L T) g)
    rw [rightConjugate_card, hAc] at hidx
    have hle : Nat.card (gmsA L T ⊓ rightConjugate (gmsA L T) g : Subgroup G) ≤
        Nat.card (gmsA L T ⊓ centralizer ({z} : Set G) : Subgroup G) := by
      refine card_le_of_le (le_inf inf_le_left fun y hy => mem_centralizer_singleton_iff.mpr ?_)
      exact congrArg Subtype.val (hEel.1.is_comm.comm ⟨y, (mem_inf.mp hy).2⟩ ⟨z, hz⟩)
    calc 2 ^ f = (gmsA L T).relIndex (rightConjugate (gmsA L T) g) *
          Nat.card (gmsA L T ⊓ rightConjugate (gmsA L T) g : Subgroup G) := hidx.symm
      _ ≤ _ := Nat.mul_le_mul_left _ hle
  have hAS : gmsA L T ≤ (P : Subgroup G) := hE.A_le.trans (le_sup_left.trans hS₀P)
  have hA1 : gmsA L T ≠ ⊥ := by
    intro hb
    rw [hb, card_bot] at hAc
    have : 1 < 2 ^ f := Nat.one_lt_two_pow (by omega)
    omega
  by_cases hsc : ∃ v ∈ gmsA L T, ∃ g : G, g⁻¹ * v * g ∈ (P : Subgroup G) ∧
      g⁻¹ * v * g ∉ gmsA L T
  · obtain ⟨U, hUA, g, hUg, hUgA, hbound⟩ :=
      GoldschmidtFour.goldschmidt_theorem_four_holds G P (gmsA L T) hAS hAel hwc hsc
    have hU'el : IsElemAbelian 2 (rightConjugate U g) :=
      isElemAbelian_map _ (isElemAbelian_of_le hAel hUA)
    refine hE.false_of_root h hF hf e hX h313 hq hfus hO hy P hS₀P hUg hU'el
      (fun z hz => ⟨g, hUA ((mem_rightConjugate_iff _ _ _).mp hz)⟩) hUgA fun w hw _ => ?_
    have hc := card_le_card_inf_centralizer_mul hAel.1 (hNA (hUg hw))
    rw [hAc] at hc
    calc 2 ^ f ≤ Nat.card (gmsA L T ⊓ centralizer ({w} : Set G) : Subgroup G) *
          Nat.card (⁅gmsA L T, zpowers w⁆ : Subgroup G) := hc
      _ ≤ Nat.card (gmsA L T ⊓ centralizer ({w} : Set G) : Subgroup G) *
          (gmsA L T).relIndex (rightConjugate U g) := Nat.mul_le_mul_left _ (hbound w hw)
      _ = _ := mul_comm _ _
  · push Not at hsc
    exact h.hyp.lemma34 P hAS hAel.1 hA1 hsc

end Sec4Elem

theorem l2Res_of_gms42ResidualU
    (hF : Foundation) (hHKS : HKSRegularNormalAffine) (hR : GMS42ResidualU) : L2Res := by
  intro G _ _ L hL f hf ⟨e⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT⟩ := exists_isSylowOf 2 (normalizer (L : Set G))
  have h : Sec3 G L T := ⟨hL, hT⟩
  have hX := h.facts_of_psl2 hF hf e
  have h313 := h.lemma313_of_psl2 hF hf e
  obtain ⟨y, hy⟩ := hX.exists_isTorus h
  have htr := hy.exists_translation_of_affine h313 hX h hF hHKS
  obtain ⟨R, hRR⟩ := Sec3.exists_isR h313 hX h hF
  obtain ⟨d, hd⟩ := hRR.exists_push28Torus h313 h hF hf e hX hy
  have hsq := hd.sq_mem_gmsA hRR hy h313 h hF hf e hX htr
  obtain ⟨U₁, -, hO⟩ := hd.exists_push28Out hRR hy h313 h hF hf e hX htr hsq
  rcases hO.sec4 hy hX h hF hf with hE | hE
  · exact hE.false_of_homo h hF hf e hX h313 hR
  · have hle := (hE.card_T₀_le hE.lt).trans (hX.sylow h).1.le
    rcases lt_or_eq_of_le hle with hlt' | heq
    · exact hE.false_of_lt h hF hf e hX h313 hlt'
    · exact hE.false_of_noFusion h hF hf e hX h313 fun t ht ht1 g hg =>
        hE.false_of_push28Out h hF hf e hX h313 heq ⟨t, ht, ht1, g, hg⟩ hO hy

end CFSG.ComponentClassification.GMS78
