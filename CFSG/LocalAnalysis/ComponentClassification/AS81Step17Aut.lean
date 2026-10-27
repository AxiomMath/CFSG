module

public import CFSG.LocalAnalysis.ComponentClassification.AS81AutRadSub
public import CFSG.LocalAnalysis.ComponentClassification.AS81Step15Cent

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.FieldFourCover LinearFlag

variable {G : Type} [Group G] [Finite G]

theorem card_map_mul_card_inf_ker {X Y : Type*} [Group X] [Group Y] (φ : X →* Y)
    (H : Subgroup X) : Nat.card (H.map φ) * Nat.card (H ⊓ φ.ker : Subgroup X) = Nat.card H := by
  have h := Subgroup.card_ker_mul_card_range (φ.comp H.subtype)
  have hrange : (φ.comp H.subtype).range = H.map φ := by
    rw [MonoidHom.range_comp, range_subtype]
  have hker : Nat.card (φ.comp H.subtype).ker = Nat.card (H ⊓ φ.ker : Subgroup X) := by
    have : (φ.comp H.subtype).ker = (φ.ker).subgroupOf H := by
      ext x
      simp [mem_subgroupOf]
    rw [this, inf_comm, ← subgroupOf_map_subtype, card_map_of_injective H.subtype_injective]
  rw [hrange, hker, mul_comm] at h
  exact h

omit [Finite G] in
theorem map_inf_center_eq {A X : Subgroup G} (hXA : X ≤ A) :
    (X.subgroupOf A ⊓ center ↥A).map A.subtype = X ⊓ centralizer (A : Set G) := by
  ext g
  constructor
  · rintro ⟨a, ⟨haX, haZ⟩, rfl⟩
    refine ⟨haX, mem_centralizer_iff.mpr fun b hb => ?_⟩
    exact congrArg Subtype.val (mem_center_iff.mp haZ ⟨b, hb⟩)
  · rintro ⟨hgX, hgC⟩
    refine ⟨⟨g, hXA hgX⟩, ⟨hgX, mem_center_iff.mpr fun b => Subtype.ext ?_⟩, rfl⟩
    exact mem_centralizer_iff.mp hgC b b.2

theorem mem_centralizer_of_odd_of_fix {A H B : Subgroup G} (hq : CFSG.Open.IsQuasisimple ↥A)
    (hL : TypeL34 (rankTwoQuot A))
    (hZ : ∀ z ∈ center ↥A, IsPGroup 2 (zpowers z) → z ^ 2 = 1)
    (hHA : H ≤ A) (hH : IsElemAbelian 2 H)
    (hH16 : Nat.card H = 16 * Nat.card (H ⊓ centralizer (A : Set G) : Subgroup G))
    (hBH : B ≤ H) (hB8 : 8 * Nat.card (B ⊓ centralizer (A : Set G) : Subgroup G) ≤ Nat.card B)
    {y : G} (hyA : y ∈ normalizer (A : Set G)) (hy : Odd (orderOf y))
    (hyB : ∀ b ∈ B, y * b * y⁻¹ = b) : y ∈ centralizer (A : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨cv⟩ := exists_l34Cover hq.1 hL hq.2 hZ
  have hO := oddCore_le_center hq.1 hq.2
  have : Finite cv.k := Nat.finite_of_card_ne_zero (by rw [cv.card_k]; omega)
  have : CharP cv.k 2 := charP_two_of_card cv.card_k
  have hH₀ : IsPGroup 2 (H.subgroupOf A) := (isPGroup_two_of_isElemAbelian hH).comap_subtype
  obtain ⟨T, hT⟩ := hH₀.exists_le_sylow
  obtain ⟨φ, hφs, hφk, hφT⟩ := cv.exists_std hO T
  have hkerA : ∀ X : Subgroup G, X ≤ A → Nat.card (X.subgroupOf A ⊓ φ.ker : Subgroup ↥A) =
      Nat.card (X ⊓ centralizer (A : Set G) : Subgroup G) := fun X hXA => by
    rw [hφk, ← map_inf_center_eq hXA, card_map_of_injective A.subtype_injective]
  have hcardA : ∀ X : Subgroup G, X ≤ A → Nat.card (X.subgroupOf A) = Nat.card X :=
    fun X hXA => Nat.card_congr (subgroupOfEquivOfLe hXA).toEquiv
  have hH₀2 : ∀ x ∈ (H.subgroupOf A).map φ, x ^ 2 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, show x ^ 2 = 1 from Subtype.ext (by simpa using hH.2 _ (mem_subgroupOf.mp hx)),
      map_one]
  have hH₀16 : Nat.card ((H.subgroupOf A).map φ) = 16 := by
    have h := card_map_mul_card_inf_ker φ (H.subgroupOf A)
    rw [hkerA H hHA, hcardA H hHA, hH16] at h
    have hpos : 0 < Nat.card (H ⊓ centralizer (A : Set G) : Subgroup G) := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hpos h
  have hH₀U : (H.subgroupOf A).map φ ≤ projUnip cv.k := hφT ▸ map_mono hT
  obtain ⟨i, hi⟩ : ∃ i : Fin 2, (H.subgroupOf A).map φ = projRad cv.k i := by
    rcases eq_projRad_of_le_projUnip cv.card_k hH₀U hH₀2 hH₀16 with h0 | h1
    · exact ⟨0, h0⟩
    · exact ⟨1, h1⟩
  have hB₀ : (B.subgroupOf A).map φ ≤ projRad cv.k i := by
    rw [← hi]
    exact map_mono fun x hx => hBH hx
  have hB₀8 : 8 ≤ Nat.card ((B.subgroupOf A).map φ) := by
    have h := card_map_mul_card_inf_ker φ (B.subgroupOf A)
    have hBA : B ≤ A := hBH.trans hHA
    rw [hkerA B hBA, hcardA B hBA] at h
    have hpos : 0 < Nat.card (B ⊓ centralizer (A : Set G) : Subgroup G) := Nat.card_pos
    exact Nat.le_of_mul_le_mul_right (h ▸ hB8 : 8 * _ ≤ _ * _) hpos
  set σ := normalizerConj hyA with hσdef
  have hσ : φ.ker.map (σ : ↥A →* ↥A) = φ.ker := by
    rw [hφk]
    exact Subgroup.map_center_eq σ
  set α := descendAut φ hφs σ hσ with hαdef
  have hαB : ∀ x ∈ (B.subgroupOf A).map φ, α x = x := by
    rintro _ ⟨b, hb, rfl⟩
    rw [hαdef, descendAut_apply]
    congr 1
    apply Subtype.ext
    rw [hσdef, coe_normalizerConj_apply]
    exact hyB _ (mem_subgroupOf.mp hb)
  have hσa : ∀ a : ↥A, ((σ a : ↥A) : G) = y * a * y⁻¹ := fun a => by
    rw [hσdef, coe_normalizerConj_apply]
  have hσpow : ∀ n : ℕ, ∀ a : ↥A, (((σ ^ n) a : ↥A) : G) = y ^ n * a * (y ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro a; simp
    | succ n ih =>
      intro a
      rw [pow_succ σ n, MulAut.mul_apply, ih, hσa]
      group
  have hαa : ∀ a : ↥A, α (φ a) = φ (σ a) := fun a => descendAut_apply φ hφs σ hσ a
  have hαpow : ∀ n : ℕ, ∀ a : ↥A, (α ^ n) (φ a) = φ ((σ ^ n) a) := by
    intro n
    induction n with
    | zero => intro a; simp
    | succ n ih =>
      intro a
      rw [pow_succ α n, MulAut.mul_apply, hαa, ih, pow_succ σ n, MulAut.mul_apply]
  have hαn : α ^ orderOf y = 1 := by
    ext x
    obtain ⟨a, rfl⟩ := hφs x
    rw [hαpow, MulAut.one_apply]
    congr 1
    apply Subtype.ext
    rw [hσpow, pow_orderOf_eq_one, one_mul, inv_one, mul_one]
  have hαodd : Odd (orderOf α) := hy.of_dvd_nat (orderOf_dvd_of_pow_eq_one hαn)
  have hα1 : α = 1 := eq_one_of_fix_of_odd cv.card_k i hB₀ hB₀8 hαodd hαB
  refine mem_centralizer_of_conj_mem_center hq.1 fun a ha => ?_
  set z : ↥A := σ ⟨a, ha⟩ * (⟨a, ha⟩ : ↥A)⁻¹ with hz
  have hzk : z ∈ φ.ker := by
    rw [MonoidHom.mem_ker, hz, map_mul, map_inv, ← hαa, hα1, MulAut.one_apply, mul_inv_cancel]
  rw [hφk] at hzk
  refine ⟨z, z.2, fun b hb => congrArg Subtype.val (mem_center_iff.mp hzk ⟨b, hb⟩).symm, ?_⟩
  have hza : ((σ ⟨a, ha⟩ : ↥A) : G) = z * a := by
    rw [hz]
    simp only [coe_mul, coe_inv]
    group
  rw [← hza, hσa]

end CFSG.ComponentClassification.AS81
