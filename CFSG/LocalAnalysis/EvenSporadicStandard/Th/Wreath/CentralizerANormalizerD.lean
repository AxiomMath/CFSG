module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Wreath.NormalizerDAction
import CFSG.LinearAlgebra.GLInvariantEndSubgroup

public section

namespace CFSG.EvenSporadicStandard.ThStd

open scoped IsMulCommutative

open Subgroup SylowEnd

private def ThP {G : Type} [Group G] (A D : Subgroup G) : Subgroup G :=
  normalizer (D : Set G) ⊓ centralizer (A : Set G)

private theorem ThCyc.conj_eq_of_mem_centralizer {G : Type} [Group G] {A : Subgroup G} {c : G}
    (hc : c ∈ centralizer (A : Set G)) : ∀ a ∈ A, c * a * c⁻¹ = a := fun a ha => by
  have h : a * c = c * a := mem_centralizer_iff.1 hc a ha
  calc c * a * c⁻¹ = (a * c) * c⁻¹ := by rw [← h]
    _ = a := by group

private theorem ThCyc.mem_centralizer_of_conj_eq {G : Type} [Group G] {A : Subgroup G} {c : G}
    (hc : ∀ a ∈ A, c * a * c⁻¹ = a) : c ∈ centralizer (A : Set G) :=
  mem_centralizer_iff.2 fun a ha => by
    calc a * c = (c * a * c⁻¹) * c := by rw [hc a ha]
      _ = c * a := by group

private theorem ThCyc.mem_ThP_conj {G : Type} [Group G] {A D : Subgroup G} {c : ↥(ThP A D)} {l : G}
    (hlD : l ∈ normalizer (D : Set G)) (hlAinv : ∀ a ∈ A, l⁻¹ * a * l ∈ A) :
    l * c.1 * l⁻¹ ∈ ThP A D := by
  refine ⟨?_, ?_⟩
  · exact (normalizer (D : Set G)).mul_mem ((normalizer (D : Set G)).mul_mem hlD c.2.1)
      ((normalizer (D : Set G)).inv_mem hlD)
  · refine ThCyc.mem_centralizer_of_conj_eq fun a ha => ?_
    have hca : c.1 * (l⁻¹ * a * l) * c.1⁻¹ = l⁻¹ * a * l :=
      ThCyc.conj_eq_of_mem_centralizer c.2.2 _ (hlAinv a ha)
    calc (l * c.1 * l⁻¹) * a * (l * c.1 * l⁻¹)⁻¹
        = l * (c.1 * (l⁻¹ * a * l) * c.1⁻¹) * l⁻¹ := by group
      _ = l * (l⁻¹ * a * l) * l⁻¹ := by rw [hca]
      _ = a := by group

variable {G : Type} [Group G] [Finite G] {L R : Subgroup G} {t : G} {S A B Aa D : Subgroup G}
  {z b : G}

private theorem ThCyc.t_mem_ThP (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) : t ∈ ThP A D := by
  refine ⟨?_, ?_⟩
  · exact le_normalizer_of_conj_mem hD.norm (H.t_mem_normalizer W W2 hD)
  · exact mem_centralizer_iff.2 fun a ha =>
      (H.comm_of_mem_L (le_trans (fun x hx => ((W.mem_A_iff x).1 hx).1) W.S_le ha)).symm

theorem ThCyc.normalizer_D_inf_centralizer_A_inf_centralizer_t_le (H : ThCyc G L R t)
    (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) {c : G}
    (hcD : c ∈ normalizer (D : Set G)) (hcA : c ∈ centralizer (A : Set G)) (hct : c * t = t * c) :
    c ∈ B ⊔ zpowers t := by
  have hxN : c ∈ normalizer (D : Set G) ⊓ centralizer ({t} : Set G) :=
    ⟨hcD, mem_centralizer_singleton_iff.2 hct⟩
  rw [H.normalizer_D_inf_centralizer_t W W2 hD] at hxN
  have hcomm : zpowers t ≤ centralizer ((L ⊓ normalizer (A : Set G) : Subgroup G) : Set G) := by
    intro r hr
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hr
    exact mem_centralizer_iff.2 fun l hl =>
      (((show Commute l t from (H.comm_of_mem_L hl.1).symm).zpow_right k).eq)
  obtain ⟨l, hl, r, hr, hclr⟩ := exists_mul_of_mem_sup hcomm hxN
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hr
  have hA_le_L : A ≤ L := fun a ha => W.S_le ((W.mem_A_iff a).1 ha).1
  have htA : t ∈ centralizer (A : Set G) :=
    mem_centralizer_iff.2 fun a ha => (H.comm_of_mem_L (hA_le_L ha)).symm
  have hrA : t ^ k ∈ centralizer (A : Set G) := (centralizer (A : Set G)).zpow_mem htA k
  have hriA : (t ^ k)⁻¹ ∈ centralizer (A : Set G) :=
    (centralizer (A : Set G)).inv_mem hrA
  have hl_eq : l = c * (t ^ k)⁻¹ := by
    rw [hclr]
    group
  have hcla : ∀ a ∈ A, l * a = a * l := by
    intro a ha
    have hca : a * c = c * a := mem_centralizer_iff.1 hcA a ha
    have hrai : a * (t ^ k)⁻¹ = (t ^ k)⁻¹ * a := mem_centralizer_iff.1 hriA a ha
    calc l * a = (c * (t ^ k)⁻¹) * a := by rw [hl_eq]
      _ = c * ((t ^ k)⁻¹ * a) := by group
      _ = c * (a * (t ^ k)⁻¹) := by rw [← hrai]
      _ = (c * a) * (t ^ k)⁻¹ := by group
      _ = (a * c) * (t ^ k)⁻¹ := by rw [← hca]
      _ = a * (c * (t ^ k)⁻¹) := by group
      _ = a * l := by rw [← hl_eq]
  have hlB : l ∈ B := (W.mem_B_iff l hl.1).2 hcla
  rw [hclr]
  exact mul_mem_sup hlB (zpow_mem (mem_zpowers t) k)

theorem ThCyc.natCard_B_sup_t (H : ThCyc G L R t) (W : ThLocalIn L S A B z) :
    Nat.card ↥(B ⊔ zpowers t) = 2 ^ 10 := by
  have hcomm : ∀ b ∈ B, ∀ r ∈ zpowers t, b * r = r * b := by
    intro b hb r hr
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hr
    exact (((show Commute b t from (H.comm_of_mem_L (W.B_le hb)).symm).zpow_right k).eq)
  have hdisj : B ⊓ zpowers t = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    obtain ⟨hxB, hxt⟩ := hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hxt
    rcases zpow_eq_one_or_self H.sq_t k with h | h
    · rw [h]; exact one_mem _
    · rw [h] at hxB
      exact absurd (W.B_le hxB) H.t_not_mem_L
  rw [natCard_sup_of_commute hcomm hdisj, Nat.card_zpowers, H.order_two, W.B_card]
  norm_num

private noncomputable def lambda (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D)
    (hV : ∀ c ∈ normalizer (D : Set G), (∀ a ∈ A, c * a * c⁻¹ = a) → ∀ v ∈ omega1 D hD.comm,
      v⁻¹ * (c * v * c⁻¹) ∈ A) (c : ↥(ThP A D)) : ↥(omega1 D hD.comm) →* ↥A where
  toFun v :=
    ⟨v.1⁻¹ * (c.1 * v.1 * c.1⁻¹),
      hV c.1 c.2.1 (ThCyc.conj_eq_of_mem_centralizer c.2.2) v.1 v.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' v w := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subtype.coe_mk]
    have hcv : c.1 * v.1 * c.1⁻¹ ∈ omega1 D hD.comm :=
      (mem_normalizer_iff.1 (ThCyc.normalizer_D_le_normalizer_omega1 hD c.2.1) v.1).1 v.2
    have hcw : c.1 * w.1 * c.1⁻¹ ∈ omega1 D hD.comm :=
      (mem_normalizer_iff.1 (ThCyc.normalizer_D_le_normalizer_omega1 hD c.2.1) w.1).1 w.2
    have hwv : w.1⁻¹ * v.1⁻¹ = v.1⁻¹ * w.1⁻¹ :=
      H.omega1_comm W W2 hD ((omega1 D hD.comm).inv_mem w.2)
        ((omega1 D hD.comm).inv_mem v.2)
    have hwcv : w.1⁻¹ * (c.1 * v.1 * c.1⁻¹) = (c.1 * v.1 * c.1⁻¹) * w.1⁻¹ :=
      H.omega1_comm W W2 hD ((omega1 D hD.comm).inv_mem w.2) hcv
    calc (v.1 * w.1)⁻¹ * (c.1 * (v.1 * w.1) * c.1⁻¹)
        = w.1⁻¹ * v.1⁻¹ * (c.1 * v.1 * c.1⁻¹) * (c.1 * w.1 * c.1⁻¹) := by group
      _ = (v.1⁻¹ * (c.1 * v.1 * c.1⁻¹)) * (w.1⁻¹ * (c.1 * w.1 * c.1⁻¹)) := by
          rw [hwv]
          calc v.1⁻¹ * w.1⁻¹ * (c.1 * v.1 * c.1⁻¹) * (c.1 * w.1 * c.1⁻¹)
              = v.1⁻¹ * (w.1⁻¹ * (c.1 * v.1 * c.1⁻¹)) * (c.1 * w.1 * c.1⁻¹) := by group
            _ = v.1⁻¹ * ((c.1 * v.1 * c.1⁻¹) * w.1⁻¹) * (c.1 * w.1 * c.1⁻¹) := by rw [hwcv]
            _ = v.1⁻¹ * (c.1 * v.1 * c.1⁻¹) * (w.1⁻¹ * (c.1 * w.1 * c.1⁻¹)) := by group

private theorem ThCyc.lambda_apply_mem_A_eq_one (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D)
    (hV : ∀ c ∈ normalizer (D : Set G), (∀ a ∈ A, c * a * c⁻¹ = a) → ∀ v ∈ omega1 D hD.comm,
      v⁻¹ * (c * v * c⁻¹) ∈ A) {c : ↥(ThP A D)} {a : G} (ha : a ∈ A) :
    lambda H W W2 hD hV c ⟨a, H.A_le_omega1 W W2 hD ha⟩ = 1 := by
  apply Subtype.ext
  change a⁻¹ * (c.1 * a * c.1⁻¹) = 1
  rw [ThCyc.conj_eq_of_mem_centralizer c.2.2 a ha, inv_mul_cancel]

private noncomputable def thVHom (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) : ↥(omega1 D hD.comm) →* ↥A where
  toFun v := ⟨thV t v.1, H.thV_mem_A W W2 hD v.2⟩
  map_one' := Subtype.ext (by simp [thV])
  map_mul' v w := Subtype.ext (H.thV_mul W W2 hD v.2 w.2)

private theorem ThCyc.thVHom_surj (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (hsq : ∀ d ∈ D, d ^ 2 ∈ A) :
    Function.Surjective (thVHom H W W2 hD) := by
  intro a
  obtain ⟨v, hv, hva⟩ := H.thV_surj W W2 hD hsq a.1 a.2
  exact ⟨⟨v, hv⟩, Subtype.ext hva⟩

private theorem ThCyc.lambda_eq_of_thV_eq (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D)
    (hV : ∀ c ∈ normalizer (D : Set G), (∀ a ∈ A, c * a * c⁻¹ = a) → ∀ v ∈ omega1 D hD.comm,
      v⁻¹ * (c * v * c⁻¹) ∈ A) {c : ↥(ThP A D)} {v w : ↥(omega1 D hD.comm)}
    (h : thVHom H W W2 hD v = thVHom H W W2 hD w) :
    lambda H W W2 hD hV c v = lambda H W W2 hD hV c w := by
  have h1 : thVHom H W W2 hD (v * w⁻¹) = 1 := by
    rw [map_mul, map_inv, h, mul_inv_cancel]
  have h2 : thV t (v * w⁻¹).1 = 1 := congrArg Subtype.val h1
  have h3 : (v * w⁻¹).1 ∈ A :=
    (H.thV_eq_one_iff W W2 hD (v * w⁻¹).2).1 h2
  have h4 : lambda H W W2 hD hV c (v * w⁻¹) = 1 := by
    have hkill := H.lambda_apply_mem_A_eq_one W W2 hD hV (c := c) h3
    rwa [show (⟨(v * w⁻¹).1, H.A_le_omega1 W W2 hD h3⟩ : ↥(omega1 D hD.comm)) =
      v * w⁻¹ from Subtype.ext rfl] at hkill
  have h5 : lambda H W W2 hD hV c v * (lambda H W W2 hD hV c w)⁻¹ = 1 := by
    calc lambda H W W2 hD hV c v * (lambda H W W2 hD hV c w)⁻¹
        = lambda H W W2 hD hV c (v * w⁻¹) := by rw [map_mul, map_inv]
      _ = 1 := h4
  exact mul_inv_eq_one.1 h5

private theorem ThCyc.lambda_eq_one_of_thVHom_eq_one (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D)
    (hV : ∀ c ∈ normalizer (D : Set G), (∀ a ∈ A, c * a * c⁻¹ = a) → ∀ v ∈ omega1 D hD.comm,
      v⁻¹ * (c * v * c⁻¹) ∈ A) {c : ↥(ThP A D)} {v : ↥(omega1 D hD.comm)}
    (h : thVHom H W W2 hD v = 1) : lambda H W W2 hD hV c v = 1 := by
  have h2 : thV t v.1 = 1 := congrArg Subtype.val h
  have h3 : v.1 ∈ A := (H.thV_eq_one_iff W W2 hD v.2).1 h2
  have hkill := H.lambda_apply_mem_A_eq_one W W2 hD hV (c := c) h3
  rwa [show (⟨v.1, H.A_le_omega1 W W2 hD h3⟩ : ↥(omega1 D hD.comm)) = v from
    Subtype.ext rfl] at hkill

section CommutativeA

variable [hAcomm : Fact (∀ a b : ↥A, a * b = b * a)]

local instance : IsMulCommutative ↥A :=
  IsMulCommutative.of_comm (Fact.out : ∀ a b : ↥A, a * b = b * a)

private theorem ThCyc.lambda_mul (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D)
    (hV : ∀ c ∈ normalizer (D : Set G), (∀ a ∈ A, c * a * c⁻¹ = a) → ∀ v ∈ omega1 D hD.comm,
      v⁻¹ * (c * v * c⁻¹) ∈ A) (c c' : ↥(ThP A D)) :
    lambda H W W2 hD hV (c * c') =
      lambda H W W2 hD hV c * lambda H W W2 hD hV c' := by
  ext v
  rw [MonoidHom.mul_apply]
  set y := v.1⁻¹ * (c.1 * v.1 * c.1⁻¹) with hy
  set y' := v.1⁻¹ * (c'.1 * v.1 * c'.1⁻¹) with hy'
  have hA' : y' ∈ A := by
    rw [hy']
    exact hV c'.1 c'.2.1 (ThCyc.conj_eq_of_mem_centralizer c'.2.2) v.1 v.2
  have hcomm : y' * c.1 = c.1 * y' := mem_centralizer_iff.1 c.2.2 y' hA'
  have hcv : c.1 * v.1 * c.1⁻¹ = v.1 * y := by rw [hy]; group
  have hcv' : c'.1 * v.1 * c'.1⁻¹ = v.1 * y' := by rw [hy']; group
  have hcentral : c.1 * y' * c.1⁻¹ = y' := by
    calc c.1 * y' * c.1⁻¹ = (y' * c.1) * c.1⁻¹ := by rw [← hcomm]
      _ = y' := by group
  calc v.1⁻¹ * ((c.1 * c'.1) * v.1 * (c.1 * c'.1)⁻¹)
      = v.1⁻¹ * (c.1 * (c'.1 * v.1 * c'.1⁻¹) * c.1⁻¹) := by group
    _ = v.1⁻¹ * (c.1 * (v.1 * y') * c.1⁻¹) := by rw [hcv']
    _ = v.1⁻¹ * ((c.1 * v.1 * c.1⁻¹) * (c.1 * y' * c.1⁻¹)) := by group
    _ = v.1⁻¹ * ((v.1 * y) * y') := by rw [hcv, hcentral]
    _ = y * y' := by group
    _ = (v.1⁻¹ * (c.1 * v.1 * c.1⁻¹)) * (v.1⁻¹ * (c'.1 * v.1 * c'.1⁻¹)) := by
        rw [hy, hy']

private noncomputable def lambdaHom (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D)
    (hV : ∀ c ∈ normalizer (D : Set G), (∀ a ∈ A, c * a * c⁻¹ = a) → ∀ v ∈ omega1 D hD.comm,
      v⁻¹ * (c * v * c⁻¹) ∈ A) : ↥(ThP A D) →* (↥(omega1 D hD.comm) →* ↥A) where
  toFun c := lambda H W W2 hD hV c
  map_one' := MonoidHom.ext fun v => by
    rw [MonoidHom.one_apply]
    apply Subtype.ext
    change v.1⁻¹ * ((1 : G) * v.1 * (1 : G)⁻¹) = 1
    group
  map_mul' c c' := H.lambda_mul W W2 hD hV c c'

private noncomputable def mu (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D)
    (hV : ∀ c ∈ normalizer (D : Set G), (∀ a ∈ A, c * a * c⁻¹ = a) → ∀ v ∈ omega1 D hD.comm,
      v⁻¹ * (c * v * c⁻¹) ∈ A) (hsq : ∀ d ∈ D, d ^ 2 ∈ A) (c : ↥(ThP A D)) : ↥A →* ↥A where
  toFun a := lambda H W W2 hD hV c (Classical.choose (H.thVHom_surj W W2 hD hsq a))
  map_one' := H.lambda_eq_one_of_thVHom_eq_one W W2 hD hV
    (Classical.choose_spec (H.thVHom_surj W W2 hD hsq 1))
  map_mul' a b := by
    have h1 : thVHom H W W2 hD
          (Classical.choose (H.thVHom_surj W W2 hD hsq (a * b))) =
        thVHom H W W2 hD
          (Classical.choose (H.thVHom_surj W W2 hD hsq a) *
            Classical.choose (H.thVHom_surj W W2 hD hsq b)) := by
      rw [map_mul, Classical.choose_spec (H.thVHom_surj W W2 hD hsq (a * b)),
        Classical.choose_spec (H.thVHom_surj W W2 hD hsq a),
        Classical.choose_spec (H.thVHom_surj W W2 hD hsq b)]
    have h2 : lambda H W W2 hD hV c
          (Classical.choose (H.thVHom_surj W W2 hD hsq (a * b))) =
        lambda H W W2 hD hV c
          (Classical.choose (H.thVHom_surj W W2 hD hsq a) *
            Classical.choose (H.thVHom_surj W W2 hD hsq b)) :=
      H.lambda_eq_of_thV_eq W W2 hD hV h1
    rw [h2, map_mul]

end CommutativeA

private theorem ThCyc.mu_apply_thV (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D)
    (hV : ∀ c ∈ normalizer (D : Set G), (∀ a ∈ A, c * a * c⁻¹ = a) → ∀ v ∈ omega1 D hD.comm,
      v⁻¹ * (c * v * c⁻¹) ∈ A) (hsq : ∀ d ∈ D, d ^ 2 ∈ A) (c : ↥(ThP A D))
    (v : ↥(omega1 D hD.comm)) :
    mu H W W2 hD hV hsq c (thVHom H W W2 hD v) =
      lambda H W W2 hD hV c v :=
  H.lambda_eq_of_thV_eq W W2 hD hV
    (Classical.choose_spec (H.thVHom_surj W W2 hD hsq (thVHom H W W2 hD v)))

section CommutativeA

variable [hAcomm : Fact (∀ a b : ↥A, a * b = b * a)]

local instance : IsMulCommutative ↥A :=
  IsMulCommutative.of_comm (Fact.out : ∀ a b : ↥A, a * b = b * a)

private noncomputable def muHom (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D)
    (hV : ∀ c ∈ normalizer (D : Set G), (∀ a ∈ A, c * a * c⁻¹ = a) → ∀ v ∈ omega1 D hD.comm,
      v⁻¹ * (c * v * c⁻¹) ∈ A) (hsq : ∀ d ∈ D, d ^ 2 ∈ A) : ↥(ThP A D) →* (↥A →* ↥A) where
  toFun c := mu H W W2 hD hV hsq c
  map_one' := MonoidHom.ext fun a => by
    obtain ⟨v, rfl⟩ := H.thVHom_surj W W2 hD hsq a
    change mu H W W2 hD hV hsq 1 (thVHom H W W2 hD v) = 1
    rw [H.mu_apply_thV W W2 hD hV hsq]
    apply Subtype.ext
    change v.1⁻¹ * ((1 : G) * v.1 * (1 : G)⁻¹) = 1
    group
  map_mul' c c' := MonoidHom.ext fun a => by
    obtain ⟨v, rfl⟩ := H.thVHom_surj W W2 hD hsq a
    change mu H W W2 hD hV hsq (c * c') (thVHom H W W2 hD v) =
      (mu H W W2 hD hV hsq c * mu H W W2 hD hV hsq c') (thVHom H W W2 hD v)
    rw [H.mu_apply_thV W W2 hD hV hsq, MonoidHom.mul_apply,
      H.mu_apply_thV W W2 hD hV hsq, H.mu_apply_thV W W2 hD hV hsq]
    rw [H.lambda_mul W W2 hD hV c c']
    rfl

private theorem ThCyc.muHom_ker (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D)
    (hV : ∀ c ∈ normalizer (D : Set G), (∀ a ∈ A, c * a * c⁻¹ = a) → ∀ v ∈ omega1 D hD.comm,
      v⁻¹ * (c * v * c⁻¹) ∈ A) (hsq : ∀ d ∈ D, d ^ 2 ∈ A) :
    (muHom H W W2 hD hV hsq).ker = (lambdaHom H W W2 hD hV).ker := by
  ext c
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
  constructor
  · intro h
    rw [MonoidHom.ext_iff] at h
    apply MonoidHom.ext
    intro v
    apply Subtype.ext
    have h1 : mu H W W2 hD hV hsq c (thVHom H W W2 hD v) = 1 := by
      have := h (thVHom H W W2 hD v)
      rw [show ((muHom H W W2 hD hV hsq) c) (thVHom H W W2 hD v) =
          mu H W W2 hD hV hsq c (thVHom H W W2 hD v) from rfl,
        show (1 : ↥A →* ↥A) (thVHom H W W2 hD v) = 1 from rfl] at this
      exact this
    rw [H.mu_apply_thV W W2 hD hV hsq] at h1
    simpa [lambdaHom] using congrArg Subtype.val h1
  · intro h
    rw [MonoidHom.ext_iff] at h ⊢
    intro a
    obtain ⟨v, rfl⟩ := H.thVHom_surj W W2 hD hsq a
    have hh : muHom H W W2 hD hV hsq c (thVHom H W W2 hD v) =
        mu H W W2 hD hV hsq c (thVHom H W W2 hD v) := rfl
    rw [hh, H.mu_apply_thV W W2 hD hV hsq]
    simpa [lambdaHom, MonoidHom.one_apply] using h v

end CommutativeA

private theorem ThCyc.lambda_t_eq_thV (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D)
    (hV : ∀ c ∈ normalizer (D : Set G), (∀ a ∈ A, c * a * c⁻¹ = a) → ∀ v ∈ omega1 D hD.comm,
      v⁻¹ * (c * v * c⁻¹) ∈ A) (v : ↥(omega1 D hD.comm)) :
    lambda H W W2 hD hV ⟨t, H.t_mem_ThP W W2 hD⟩ v =
      thVHom H W W2 hD v := by
  apply Subtype.ext
  have hv2 : v.1 * v.1 = 1 := H.omega1_mul_self W W2 hD v.2
  have hvi : v.1⁻¹ = v.1 := inv_eq_of_mul_eq_one_right hv2
  change v.1⁻¹ * (t * v.1 * t⁻¹) = thV t v.1
  rw [hvi]
  rfl

section CommutativeA

variable [hAcomm : Fact (∀ a b : ↥A, a * b = b * a)]

local instance : IsMulCommutative ↥A :=
  IsMulCommutative.of_comm (Fact.out : ∀ a b : ↥A, a * b = b * a)

private theorem ThCyc.muHom_t (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D)
    (hV : ∀ c ∈ normalizer (D : Set G), (∀ a ∈ A, c * a * c⁻¹ = a) → ∀ v ∈ omega1 D hD.comm,
      v⁻¹ * (c * v * c⁻¹) ∈ A) (hsq : ∀ d ∈ D, d ^ 2 ∈ A) :
    muHom H W W2 hD hV hsq ⟨t, H.t_mem_ThP W W2 hD⟩ = MonoidHom.id ↥A := by
  apply MonoidHom.ext
  intro a
  obtain ⟨v, rfl⟩ := H.thVHom_surj W W2 hD hsq a
  apply Subtype.ext
  rw [show (((muHom H W W2 hD hV hsq) ⟨t, H.t_mem_ThP W W2 hD⟩)
        (thVHom H W W2 hD v) : ↥A) =
      mu H W W2 hD hV hsq ⟨t, H.t_mem_ThP W W2 hD⟩
        (thVHom H W W2 hD v) from rfl]
  rw [H.mu_apply_thV W W2 hD hV hsq, H.lambda_t_eq_thV W W2 hD hV v]
  rfl

private theorem ThCyc.commutator_t_mem_ker (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D)
    (hV : ∀ c ∈ normalizer (D : Set G), (∀ a ∈ A, c * a * c⁻¹ = a) → ∀ v ∈ omega1 D hD.comm,
      v⁻¹ * (c * v * c⁻¹) ∈ A) (c : ↥(ThP A D)) :
    c * ⟨t, H.t_mem_ThP W W2 hD⟩ * c⁻¹ * ⟨t, H.t_mem_ThP W W2 hD⟩⁻¹ ∈
      (lambdaHom H W W2 hD hV).ker := by
  rw [MonoidHom.mem_ker]
  apply MonoidHom.ext
  intro v
  rw [MonoidHom.one_apply]
  rw [map_mul, map_mul, map_mul, map_inv, map_inv]
  simp only [MonoidHom.mul_apply, MonoidHom.one_apply]
  change lambda H W W2 hD hV c v * lambda H W W2 hD hV ⟨t, H.t_mem_ThP W W2 hD⟩ v *
      (lambda H W W2 hD hV c v)⁻¹ *
        (lambda H W W2 hD hV ⟨t, H.t_mem_ThP W W2 hD⟩ v)⁻¹ = (1 : ↥A)
  have hb : lambda H W W2 hD hV ⟨t, H.t_mem_ThP W W2 hD⟩ v *
        (lambda H W W2 hD hV c v)⁻¹ =
      (lambda H W W2 hD hV c v)⁻¹ *
        lambda H W W2 hD hV ⟨t, H.t_mem_ThP W W2 hD⟩ v := by
    apply Subtype.ext
    exact W.A_comm _ (lambda H W W2 hD hV ⟨t, H.t_mem_ThP W W2 hD⟩ v).2 _
      ((lambda H W W2 hD hV c v)⁻¹).2
  calc lambda H W W2 hD hV c v * lambda H W W2 hD hV ⟨t, H.t_mem_ThP W W2 hD⟩ v *
        (lambda H W W2 hD hV c v)⁻¹ *
          (lambda H W W2 hD hV ⟨t, H.t_mem_ThP W W2 hD⟩ v)⁻¹
      = lambda H W W2 hD hV c v *
          (lambda H W W2 hD hV ⟨t, H.t_mem_ThP W W2 hD⟩ v *
            (lambda H W W2 hD hV c v)⁻¹) *
          (lambda H W W2 hD hV ⟨t, H.t_mem_ThP W W2 hD⟩ v)⁻¹ := by group
    _ = lambda H W W2 hD hV c v *
          ((lambda H W W2 hD hV c v)⁻¹ *
            lambda H W W2 hD hV ⟨t, H.t_mem_ThP W W2 hD⟩ v) *
          (lambda H W W2 hD hV ⟨t, H.t_mem_ThP W W2 hD⟩ v)⁻¹ := by rw [hb]
    _ = 1 := by group

end CommutativeA

private theorem ThCyc.card_CPt_le (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) :
    Nat.card ↥(Subgroup.centralizer ({⟨t, H.t_mem_ThP W W2 hD⟩} : Set ↥(ThP A D))) ≤
      2 ^ 10 := by
  have hinj : Function.Injective
      (fun c : ↥(Subgroup.centralizer ({⟨t, H.t_mem_ThP W W2 hD⟩} : Set ↥(ThP A D))) =>
        (⟨c.1.1, H.normalizer_D_inf_centralizer_A_inf_centralizer_t_le W W2 hD
            c.1.2.1 c.1.2.2 (by
              have h := congrArg (fun x : ↥(ThP A D) => (x : G))
                (mem_centralizer_iff.1 c.2 ⟨t, H.t_mem_ThP W W2 hD⟩ (by simp))
              exact h.symm)⟩ : ↥(B ⊔ zpowers t))) := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : ↥(B ⊔ zpowers t) => (z : G)) h
  have h := Nat.card_le_card_of_injective _ hinj
  rwa [H.natCard_B_sup_t W] at h

section CommutativeA

variable [hAcomm : Fact (∀ a b : ↥A, a * b = b * a)]

local instance : IsMulCommutative ↥A :=
  IsMulCommutative.of_comm (Fact.out : ∀ a b : ↥A, a * b = b * a)

private theorem ThCyc.index_CPt_le_ker (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D)
    (hV : ∀ c ∈ normalizer (D : Set G), (∀ a ∈ A, c * a * c⁻¹ = a) → ∀ v ∈ omega1 D hD.comm,
      v⁻¹ * (c * v * c⁻¹) ∈ A) :
    (Subgroup.centralizer ({⟨t, H.t_mem_ThP W W2 hD⟩} : Set ↥(ThP A D))).index ≤
      Nat.card ↥(lambdaHom H W W2 hD hV).ker := by
  rw [Subgroup.index_centralizer_eq_ncard]
  rw [← Nat.card_coe_set_eq]
  let f : ↥(conjugatesOf (⟨t, H.t_mem_ThP W W2 hD⟩ : ↥(ThP A D))) →
      ↥(lambdaHom H W W2 hD hV).ker := fun x =>
    ⟨x.1 * (⟨t, H.t_mem_ThP W W2 hD⟩ : ↥(ThP A D))⁻¹, by
      obtain ⟨c, hc⟩ := isConj_iff.1 x.2
      rw [← hc]
      exact H.commutator_t_mem_ker W W2 hD hV c⟩
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    have h := congrArg (fun z : ↥(lambdaHom H W W2 hD hV).ker => (z : ↥(ThP A D))) hxy
    exact mul_right_cancel h
  exact Nat.card_le_card_of_injective f hf

private theorem ThCyc.index_ker_le (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D)
    (hV : ∀ c ∈ normalizer (D : Set G), (∀ a ∈ A, c * a * c⁻¹ = a) → ∀ v ∈ omega1 D hD.comm,
      v⁻¹ * (c * v * c⁻¹) ∈ A) : (lambdaHom H W W2 hD hV).ker.index ≤ 2 ^ 10 := by
  let CPt := Subgroup.centralizer ({⟨t, H.t_mem_ThP W W2 hD⟩} : Set ↥(ThP A D))
  let K := (lambdaHom H W W2 hD hV).ker
  have h1 : CPt.index ≤ Nat.card ↥K := H.index_CPt_le_ker W W2 hD hV
  have h2 : Nat.card ↥CPt ≤ 2 ^ 10 := H.card_CPt_le W W2 hD
  have h3 : CPt.index * Nat.card ↥CPt = Nat.card ↥(ThP A D) := Subgroup.index_mul_card CPt
  have h4 : K.index * Nat.card ↥K = Nat.card ↥(ThP A D) := Subgroup.index_mul_card K
  have h5 : Nat.card ↥(ThP A D) ≤ Nat.card ↥K * 2 ^ 10 := by
    rw [← h3]
    exact Nat.mul_le_mul h1 h2
  have h6 : K.index * Nat.card ↥K ≤ 2 ^ 10 * Nat.card ↥K := by
    rw [h4]
    exact h5.trans (le_of_eq (Nat.mul_comm _ _))
  exact Nat.le_of_mul_le_mul_right h6 Nat.card_pos

private theorem ThCyc.card_range_mu_le (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D)
    (hV : ∀ c ∈ normalizer (D : Set G), (∀ a ∈ A, c * a * c⁻¹ = a) → ∀ v ∈ omega1 D hD.comm,
      v⁻¹ * (c * v * c⁻¹) ∈ A) (hsq : ∀ d ∈ D, d ^ 2 ∈ A) :
    Nat.card ↥(muHom H W W2 hD hV hsq).range ≤ 2 ^ 10 := by
  rw [← Subgroup.index_ker (muHom H W W2 hD hV hsq)]
  rw [H.muHom_ker W W2 hD hV hsq]
  exact H.index_ker_le W W2 hD hV

end CommutativeA

private theorem ThCyc.mu_conj_apply (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D)
    (hV : ∀ c ∈ normalizer (D : Set G), (∀ a ∈ A, c * a * c⁻¹ = a) → ∀ v ∈ omega1 D hD.comm,
      v⁻¹ * (c * v * c⁻¹) ∈ A) (hsq : ∀ d ∈ D, d ^ 2 ∈ A) {c : ↥(ThP A D)} {l : G} (hlL : l ∈ L)
    (hlA : ∀ a ∈ A, l * a * l⁻¹ ∈ A) (hlAinv : ∀ a ∈ A, l⁻¹ * a * l ∈ A) (v : ↥(omega1 D hD.comm)) :
    mu H W W2 hD hV hsq
        ⟨l * c.1 * l⁻¹,
          ThCyc.mem_ThP_conj (by
            refine mem_normalizer_iff.2 fun x => ⟨fun hx => ?_, fun hx => ?_⟩
            · exact hD.norm l (H.mem_normalizer_W5_of_L W hlL hlA) x hx
            · have h := hD.norm l⁻¹
                ((normalizer ((W5 A t : Subgroup G) : Set G)).inv_mem
                  (H.mem_normalizer_W5_of_L W hlL hlA)) (l * x * l⁻¹) hx
              have h' : l⁻¹ * (l * x * l⁻¹) * l = x := by group
              simpa [h'] using h) hlAinv⟩
        (thVHom H W W2 hD v) =
      (actA H W l (H.mem_normalizer_W5_of_L W hlL hlA))
        (mu H W W2 hD hV hsq c
          ((actA H W l (H.mem_normalizer_W5_of_L W hlL hlA)).symm
            (thVHom H W W2 hD v))) := by
  have hlW : l ∈ normalizer ((W5 A t : Subgroup G) : Set G) :=
    H.mem_normalizer_W5_of_L W hlL hlA
  have hlV : l ∈ normalizer (omega1 D hD.comm : Set G) :=
    H.normalizer_le_normalizer_omega1 W W2 hD hlW
  have hv' : l⁻¹ * v.1 * l ∈ omega1 D hD.comm := by
    have h := (mem_normalizer_iff.1 ((normalizer (omega1 D hD.comm : Set G)).inv_mem hlV)
      v.1).1 v.2
    simpa using h
  have hsymm : (actA H W l hlW).symm (thVHom H W W2 hD v) =
      thVHom H W W2 hD ⟨l⁻¹ * v.1 * l, hv'⟩ := by
    apply Subtype.ext
    change l⁻¹ * thV t v.1 * l = thV t (l⁻¹ * v.1 * l)
    simpa using (H.thV_conj W W2 hD (n := l⁻¹) (L.inv_mem hlL)).symm
  rw [hsymm, H.mu_apply_thV W W2 hD hV hsq, H.mu_apply_thV W W2 hD hV hsq]
  apply Subtype.ext
  change v.1⁻¹ * ((l * c.1 * l⁻¹) * v.1 * (l * c.1 * l⁻¹)⁻¹) =
    l * ((l⁻¹ * v.1 * l)⁻¹ * (c.1 * (l⁻¹ * v.1 * l) * c.1⁻¹)) * l⁻¹
  group

section CommutativeA

variable [hAcomm : Fact (∀ a b : ↥A, a * b = b * a)]

local instance : IsMulCommutative ↥A :=
  IsMulCommutative.of_comm (Fact.out : ∀ a b : ↥A, a * b = b * a)

private theorem ThCyc.mem_range_mu_conj (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D)
    (hV : ∀ c ∈ normalizer (D : Set G), (∀ a ∈ A, c * a * c⁻¹ = a) → ∀ v ∈ omega1 D hD.comm,
      v⁻¹ * (c * v * c⁻¹) ∈ A) (hsq : ∀ d ∈ D, d ^ 2 ∈ A) {σ : ↥A ≃* ↥A} {f : ↥A →* ↥A}
    (hf : f ∈ (muHom H W W2 hD hV hsq).range) :
    (σ : ↥A →* ↥A).comp (f.comp (σ.symm : ↥A →* ↥A)) ∈
      (muHom H W W2 hD hV hsq).range := by
  obtain ⟨c, rfl⟩ := hf
  classical
  obtain ⟨l, hlL, hl⟩ := W.surj
    (fun a => if h : a ∈ A then ((σ ⟨a, h⟩ : ↥A) : G) else 1)
    (fun a ha => by simp [ha])
    (fun a ha b hb => by
      simp only [ha, hb, mul_mem ha hb, dite_true]
      exact congrArg Subtype.val (σ.map_mul ⟨a, ha⟩ ⟨b, hb⟩))
    (fun a ha b hb hab => by
      simp only [ha, hb, dite_true] at hab
      exact congrArg Subtype.val (σ.injective (Subtype.ext hab)))
  have hlσ : ∀ a (ha : a ∈ A), l * a * l⁻¹ = ((σ ⟨a, ha⟩ : ↥A) : G) := by
    intro a ha
    have h := hl a ha
    simpa only [dif_pos ha] using h
  have hlA : ∀ a ∈ A, l * a * l⁻¹ ∈ A := fun a ha => by
    rw [hlσ a ha]
    exact (σ ⟨a, ha⟩).2
  have hlAinv : ∀ a ∈ A, l⁻¹ * a * l ∈ A := by
    intro a ha
    obtain ⟨b, hb⟩ := σ.surjective ⟨a, ha⟩
    have hlb : l * b * l⁻¹ = a := by
      have h := hlσ b b.2
      rw [hb] at h
      exact h
    have hb' : l⁻¹ * a * l = b := by
      calc l⁻¹ * a * l = l⁻¹ * (l * b * l⁻¹) * l := by rw [hlb]
        _ = b := by group
    rw [hb']
    exact b.2
  have hlW : l ∈ normalizer ((W5 A t : Subgroup G) : Set G) :=
    H.mem_normalizer_W5_of_L W hlL hlA
  have hlD : l ∈ normalizer (D : Set G) := by
    refine mem_normalizer_iff.2 fun x => ⟨fun hx => hD.norm l hlW x hx, fun hx => ?_⟩
    have h := hD.norm l⁻¹ ((normalizer _).inv_mem hlW) (l * x * l⁻¹) hx
    have h' : l⁻¹ * (l * x * l⁻¹) * l = x := by group
    simpa [h'] using h
  have hmem : l * c.1 * l⁻¹ ∈ ThP A D :=
    ThCyc.mem_ThP_conj hlD hlAinv
  have hact : actA H W l hlW = σ := by
    apply MulEquiv.ext
    intro a
    apply Subtype.ext
    exact hlσ a.1 a.2
  refine ⟨⟨l * c.1 * l⁻¹, hmem⟩, ?_⟩
  apply MonoidHom.ext
  intro a
  obtain ⟨v, rfl⟩ := H.thVHom_surj W W2 hD hsq a
  rw [show ((σ : ↥A →* ↥A).comp
        ((muHom H W W2 hD hV hsq c).comp (σ.symm : ↥A →* ↥A)))
        (thVHom H W W2 hD v) =
      σ (mu H W W2 hD hV hsq c (σ.symm (thVHom H W W2 hD v))) from rfl]
  rw [← hact]
  have h : mu H W W2 hD hV hsq ⟨l * c.1 * l⁻¹, hmem⟩
        (thVHom H W W2 hD v) =
      actA H W l hlW (mu H W W2 hD hV hsq c
        ((actA H W l hlW).symm (thVHom H W W2 hD v))) :=
    H.mu_conj_apply W W2 hD hV hsq hlL hlA hlAinv v
  simpa [muHom] using h

private theorem ThCyc.conj_omega1_eq_or_of_mem_normalizer_D_aux (H : ThCyc G L R t)
    (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D)
    (hV : ∀ c ∈ normalizer (D : Set G), (∀ a ∈ A, c * a * c⁻¹ = a) → ∀ v ∈ omega1 D hD.comm,
      v⁻¹ * (c * v * c⁻¹) ∈ A) (h4 : ∀ d ∈ D, d ^ 4 = 1)
    (hEnd : ∀ {K : Type} [CommGroup K], (∀ x : K, x ^ 2 = 1) → Nat.card K = 16 →
      ∀ W : Subgroup (K →* K), (∀ σ : K ≃* K, ∀ f ∈ W,
      (σ : K →* K).comp (f.comp (σ.symm : K →* K)) ∈ W) → MonoidHom.id K ∈ W → Nat.card W ≤
      2 ^ 10 → ∀ f ∈ W, f = 1 ∨ f = MonoidHom.id K) {c : G} (hcD : c ∈ normalizer (D : Set G))
    (hcA : ∀ a ∈ A, c * a * c⁻¹ = a) :
    (∀ v ∈ omega1 D hD.comm, c * v * c⁻¹ = v) ∨
      (∀ v ∈ omega1 D hD.comm, c * v * c⁻¹ = t * v * t⁻¹) := by
  classical
  have hsq : ∀ d ∈ D, d ^ 2 ∈ A := fun d hd => H.D_sq_mem_A_of_fourth W W2 hD h4 hd
  let c' : ↥(ThP A D) := ⟨c, hcD, ThCyc.mem_centralizer_of_conj_eq hcA⟩
  have hmem : muHom H W W2 hD hV hsq c' ∈ (muHom H W W2 hD hV hsq).range :=
    ⟨c', rfl⟩
  have hid : MonoidHom.id ↥A ∈ (muHom H W W2 hD hV hsq).range :=
    ⟨⟨t, H.t_mem_ThP W W2 hD⟩, H.muHom_t W W2 hD hV hsq⟩
  have hconj : ∀ σ : ↥A ≃* ↥A, ∀ f ∈ (muHom H W W2 hD hV hsq).range,
      (σ : ↥A →* ↥A).comp (f.comp (σ.symm : ↥A →* ↥A)) ∈
        (muHom H W W2 hD hV hsq).range :=
    fun σ f hf => H.mem_range_mu_conj W W2 hD hV hsq hf
  have hcases := hEnd (K := ↥A) (fun x => Subtype.ext (W.A_sq x x.2)) W.A_card
    (muHom H W W2 hD hV hsq).range hconj hid
    (H.card_range_mu_le W W2 hD hV hsq) (muHom H W W2 hD hV hsq c') hmem
  have hthV : ∀ v : ↥(omega1 D hD.comm),
      (thVHom H W W2 hD v : ↥A) =
        ⟨v.1 * (t * v.1 * t⁻¹), H.thV_mem_A W W2 hD v.2⟩ := fun v => rfl
  rcases hcases with h1 | hid'
  · left
    intro v hv
    have h := congrArg
      (fun f : ↥A →* ↥A => f (thVHom H W W2 hD ⟨v, hv⟩)) h1
    rw [show ((muHom H W W2 hD hV hsq) c') (thVHom H W W2 hD ⟨v, hv⟩) =
        mu H W W2 hD hV hsq c' (thVHom H W W2 hD ⟨v, hv⟩) from rfl,
      show (1 : ↥A →* ↥A) (thVHom H W W2 hD ⟨v, hv⟩) = 1 from rfl] at h
    rw [H.mu_apply_thV W W2 hD hV hsq] at h
    have hval : v⁻¹ * (c * v * c⁻¹) = 1 := congrArg Subtype.val h
    calc c * v * c⁻¹ = v * (v⁻¹ * (c * v * c⁻¹)) := by group
      _ = v * 1 := by rw [hval]
      _ = v := by group
  · right
    intro v hv
    have h := congrArg
      (fun f : ↥A →* ↥A => f (thVHom H W W2 hD ⟨v, hv⟩)) hid'
    rw [show ((muHom H W W2 hD hV hsq) c') (thVHom H W W2 hD ⟨v, hv⟩) =
        mu H W W2 hD hV hsq c' (thVHom H W W2 hD ⟨v, hv⟩) from rfl,
      show (MonoidHom.id ↥A) (thVHom H W W2 hD ⟨v, hv⟩) =
        thVHom H W W2 hD ⟨v, hv⟩ from rfl] at h
    rw [H.mu_apply_thV W W2 hD hV hsq] at h
    have hval : v⁻¹ * (c * v * c⁻¹) = thV t v := congrArg Subtype.val h
    have hv2 : v * v = 1 := H.omega1_mul_self W W2 hD hv
    calc c * v * c⁻¹ = v * (v⁻¹ * (c * v * c⁻¹)) := by group
      _ = v * thV t v := by rw [hval]
      _ = v * (v * (t * v * t⁻¹)) := by rw [thV]
      _ = (v * v) * (t * v * t⁻¹) := by group
      _ = t * v * t⁻¹ := by rw [hv2]; group

end CommutativeA

theorem ThCyc.conj_omega1_eq_or_of_mem_normalizer_D (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1)
    (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹) {c : G} (hcD : c ∈ normalizer (D : Set G))
    (hcA : ∀ a ∈ A, c * a * c⁻¹ = a) : (∀ v ∈ omega1 D hD.comm, c * v * c⁻¹ = v) ∨
      (∀ v ∈ omega1 D hD.comm, c * v * c⁻¹ = t * v * t⁻¹) := by
  have hV : ∀ x ∈ normalizer (D : Set G), (∀ a ∈ A, x * a * x⁻¹ = a) →
      ∀ v ∈ omega1 D hD.comm, v⁻¹ * (x * v * x⁻¹) ∈ A :=
    fun x hx hxA v hv =>
      H.conj_mul_inv_mem_A_of_mem_normalizer_D W W2 hD h4 hb hx hxA hv
  haveI : Fact (∀ a b : ↥A, a * b = b * a) :=
    ⟨fun a b => Subtype.ext (W.A_comm a.1 a.2 b.1 b.2)⟩
  exact ThCyc.conj_omega1_eq_or_of_mem_normalizer_D_aux H W W2 hD hV h4
    (fun hsq hcard W hconj hid hcardW =>
      CFSG.LinearAlgebra.monoidHom_eq_one_or_id_of_conj_invariant_of_card_le hsq hcard
        (fun σ _ hf => hconj σ _ hf) hid hcardW) hcD hcA

end CFSG.EvenSporadicStandard.ThStd
