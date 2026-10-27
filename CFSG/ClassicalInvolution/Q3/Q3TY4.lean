module

public import CFSG.ClassicalInvolution.Q3.Q3TY2
public import CFSG.ClassicalInvolution.Q3.Q3WStd
public import CFSG.ClassicalInvolution.Q3.Q3WL65
public import CFSG.ClassicalInvolution.WeakCT.SU4SpinMinusBridge
public import CFSG.ClassicalInvolution.RouteD.TypeF4Lift
public import CFSG.ClassicalInvolution.RouteD.TypeTwistedDRecognition

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TY

open CFSG.ClassicalInvolution.ModelFacts.OddCover CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted
open CFSG.ClassicalInvolution.Models.TwistedPairs (TwistedB2BlockPair spinMinusModel)
open scoped MatrixGroups

theorem sl2_gf3_pow_twelve (x : SL(2, GaloisField 3 1)) : x ^ 12 = 1 := by
  have hK : Nat.card (GaloisField 3 1) = 3 := by
    rw [GaloisField.card 3 1 one_ne_zero]
    norm_num
  obtain ⟨ε⟩ := Q3W.nonempty_ringEquiv_zmod_three hK
  apply (Q3W.slEquiv ε 2).injective
  rw [map_pow, map_one]
  exact Q3W.sl2_pow_twelve _


theorem isPerfect_spinMinus6_three {b c : GaloisField 3 1}
    (hirr : ∀ s : GaloisField 3 1, s ^ 2 + b * s + c ≠ 0) :
    Group.IsPerfect (spinGroup (quadMinus 3 (GaloisField 3 1) b c)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e, -⟩ := WeakCT.SU4.su4SpinMinus_exists (p := 3) (f := 1) (by norm_num) one_ne_zero hirr
  have hK : Nat.card (GaloisField 3 (2 * 1)) = (3 ^ 1) ^ 2 := by
    rw [GaloisField.card 3 (2 * 1) (by norm_num)]
    norm_num
  have hperf : Group.IsPerfect (CFSG.ClassicalInvolution.Phan.Su (GaloisField 3 (2 * 1)) 3 1 4) :=
    CFSG.ClassicalGroups.Unitary.isPerfect_SUid
      (CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution hK) (by norm_num)
      fun h3 => absurd h3 (by norm_num)
  have := hperf
  exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective


theorem twistedB2BlockPair_lift3 {b c : GaloisField 3 1}
    (hirr : ∀ s : GaloisField 3 1, s ^ 2 + b * s + c ≠ 0)
    (hg6 : RouteD.SpinMinus6Generated hirr)
    {Y : Type} [Group Y] [Finite Y] {O : Subgroup Y} [O.Normal] (hOc : O ≤ Subgroup.center Y)
    (hOodd : Odd (Nat.card O)) (hO3 : ¬ 3 ∣ Nat.card O) {A B : Subgroup Y}
    (hA : ∀ a ∈ A, a ^ 12 = 1) (hB : B ≤ ⁅B, B⁆) {W : Subgroup (Y ⧸ O)}
    (h : TwistedB2BlockPair hirr W (A.map (QuotientGroup.mk' O))
      (B.map (QuotientGroup.mk' O))) :
    ∃ W' : Subgroup Y, TwistedB2BlockPair hirr W' A B := by
  have := fact_shortField hirr
  have := finite_shortField (b := b) (c := c)
  have hfin6 : Finite (spinGroup (quadMinus 3 (GaloisField 3 1) b c)) :=
    RouteD.finite_spinGroup_quadMinus 3 b c
  have hperf6 := isPerfect_spinMinus6_three hirr
  let π := QuotientGroup.mk' O
  let P : Subgroup Y := A ⊔ B
  let π' : ↥P →* Y ⧸ O := π.comp P.subtype
  have hW : W ≤ A.map π ⊔ B.map π := RouteD.twistedB2BlockPair_le_sup hirr hg6 h
  obtain ⟨θb, hrange, hker, hinjL, hU, hV⟩ := h
  have hrange' : π'.range = A.map π ⊔ B.map π := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, Subgroup.map_sup]
  have hAle : A.map π ≤ θb.range := hU ▸ Subgroup.map_le_range θb _
  have hBle : B.map π ≤ θb.range := hV ▸ Subgroup.map_le_range θb _
  have hθ : ∀ s, θb s ∈ π'.range := fun s => by
    rw [hrange']
    exact hW (hrange ▸ ⟨s, rfl⟩)
  have hZc : π'.ker ≤ Subgroup.center ↥P := by
    intro y hy
    rw [Subgroup.mem_center_iff]
    intro r
    have : (y : Y) ∈ O := (QuotientGroup.eq_one_iff _).mp (MonoidHom.mem_ker.mp hy)
    exact Subtype.ext (Subgroup.mem_center_iff.mp (hOc this) (r : Y))
  have hdvd : Nat.card π'.ker ∣ Nat.card O := by
    let g : π'.ker →* O :=
      { toFun := fun y => ⟨(y.1 : Y), (QuotientGroup.eq_one_iff _).mp (MonoidHom.mem_ker.mp y.2)⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    exact Subgroup.card_dvd_of_injective g fun y₁ y₂ h =>
      Subtype.ext (Subtype.ext (congrArg (fun x : O => (x : Y)) h))
  have hQ : Odd (Nat.card π'.ker) ∧ ¬ 3 ∣ Nat.card π'.ker :=
    ⟨hOodd.of_dvd_nat hdvd, fun h3 => hO3 (h3.trans hdvd)⟩
  let θc : spinGroup (quadMinus 3 (GaloisField 3 1) b c) →* π'.range :=
    θb.codRestrict π'.range hθ
  have hdivQ : ∀ m n : ℕ, m ∣ n → (Odd n ∧ ¬ 3 ∣ n) → (Odd m ∧ ¬ 3 ∣ m) :=
    fun m n hmn ⟨ho, hn⟩ => ⟨ho.of_dvd_nat hmn, fun h => hn (h.trans hmn)⟩
  obtain ⟨β, hβ⟩ := exists_lift_of_noCover (Q := fun n => Odd n ∧ ¬ 3 ∣ n) hdivQ
    (spinMinus6_three_noCover hirr) π'.rangeRestrict π'.rangeRestrict_surjective
    (by rw [MonoidHom.ker_rangeRestrict]; exact hZc) (by rw [MonoidHom.ker_rangeRestrict]; exact hQ)
    θc
  let θY : spinGroup (quadMinus 3 (GaloisField 3 1) b c) →* Y := P.subtype.comp β
  have hπθ : ∀ x, π (θY x) = θb x := by
    intro x
    have h1 : π'.rangeRestrict (β x) = θc x := DFunLike.congr_fun hβ x
    have h2 : ((π'.rangeRestrict (β x) : π'.range) : Y ⧸ O) = θb x := by
      rw [h1]
      rfl
    exact h2
  have hπθY : π.comp θY = θb := MonoidHom.ext hπθ
  have hker0 : π.ker ≤ Subgroup.center Y := by
    rw [QuotientGroup.ker_mk']
    exact hOc
  have hcop : ∀ n ∈ π.ker, Nat.Coprime (orderOf n) 6 := by
    intro n hn
    rw [QuotientGroup.ker_mk'] at hn
    exact Q3W.orderOf_coprime_six hOodd hO3 hn
  refine ⟨θY.range, θY, rfl, ?_, ?_, ?_, ?_⟩
  · intro x hx
    apply hker
    rw [MonoidHom.mem_ker, ← hπθ, MonoidHom.mem_ker.mp hx, map_one]
  · intro a b hab
    apply hinjL
    simp only [MonoidHom.comp_apply] at hab ⊢
    rw [← hπθ, ← hπθ]
    exact congrArg π hab
  · set S := (spinMinusModel hirr).lb.range.map θY with hSdef
    have hS12 : ∀ y ∈ S, y ^ 12 = 1 := by
      rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
      rw [← map_pow, ← map_pow, sl2_gf3_pow_twelve a, map_one, map_one]
    have hmap : S.map π = A.map π := by
      rw [hSdef, Subgroup.map_map, hπθY, hU]
    refine le_antisymm ?_ ?_
    · refine Q3W.le_of_map_le_of_exponent π hker0 hcop hS12 hA fun l hl => ?_
      rw [← hmap]
      exact ⟨l, hl, rfl⟩
    · refine Q3W.le_of_map_le_of_exponent π hker0 hcop hA hS12 fun l hl => ?_
      rw [hmap]
      exact ⟨l, hl, rfl⟩
  · have hperfS : (θY.comp (spinMinusModel hirr).sb).range ≤
        ⁅(θY.comp (spinMinusModel hirr).sb).range, (θY.comp (spinMinusModel hirr).sb).range⁆ :=
      RouteD.range_perfect_of_sl2
        (CFSG.ClassicalInvolution.Models.TwistedPairs.four_le_card_shortField' (b := b) (c := c)) _
    have hrS : (θY.comp (spinMinusModel hirr).sb).range = (spinMinusModel hirr).sb.range.map θY :=
      MonoidHom.range_comp _ _ |>.trans rfl
    rw [hrS] at hperfS
    refine RouteD.eq_of_map_mk_eq_of_central hOc hperfS hB ?_
    rw [Subgroup.map_map, hπθY, hV]

end CFSG.ClassicalInvolution.Q3.Q3TY
