module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.RuRowFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.RuSzEightModel
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.RowFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Thm24Gen

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard
  CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.Induction.Hyp
  CFSG.Assembly.LowTwoRank CFSG.EvenSporadicStandard.RuStd

open scoped Pointwise

theorem szEight_sylow_nonabelian' (hSz : SzEightModel) {Q : Type} [Group Q] [Finite Q]
    (hQm : SuzukiModel Q 2 3) (hs : IsSimpleGroup Q) (hc : Nat.card Q = 29120) (R : Subgroup Q)
    (hR : Nat.card ↥R = 2 ^ 6) : ∃ x ∈ R, ∃ y ∈ R, x * y ≠ y * x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hna : ∃ a b : Q, a * b ≠ b * a := not_comm_of_simple_not_prime (by rw [hc]; norm_num)
  have hZ : center Q = ⊥ := center_eq_bot_of_simple_nonabelian hna
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := Q) 2 (by rw [hc]; norm_num)
  have ha2 : a * a = 1 := by rw [← pow_two, ← ha]; exact pow_orderOf_eq_one a
  have ha1 : a ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ha
    omega
  have hα1 : (MulAut.conj a : MulAut Q) ≠ 1 := by
    intro h
    apply ha1
    have : a ∈ center Q := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h3 := congrArg (fun f : MulAut Q => f g) h
      simp only [MulAut.conj_apply, MulAut.one_apply] at h3
      calc g * a = (a * g * a⁻¹) * a := by rw [h3]
        _ = a * g := by group
    rw [hZ, Subgroup.mem_bot] at this
    exact this
  have hα2 : (MulAut.conj a : MulAut Q) * MulAut.conj a = 1 := by
    rw [← map_mul, ha2, map_one]
  have hnab := (hSz Q hQm).2 _ hα1 hα2
  unfold TwoSubgroupsAbelian at hnab
  push Not at hnab
  obtain ⟨P, hP2, x, hx, y, hy, hxy⟩ := hnab
  have hP₁ : IsPGroup 2 ↥(P.map (fixSubgroup (MulAut.conj a : MulAut Q)).subtype) :=
    hP2.map _
  obtain ⟨S₁, hS₁⟩ := hP₁.exists_le_sylow
  let SR : Sylow 2 Q := Sylow.ofCard R (by rw [hR, hc, factorization_two_29120])
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Q SR S₁
  have hmem : ∀ z ∈ P.map (fixSubgroup (MulAut.conj a : MulAut Q)).subtype,
      ∃ r ∈ R, g * r * g⁻¹ = z := by
    intro z hz
    have hz' : z ∈ (S₁ : Subgroup Q) := hS₁ hz
    rw [← hg, Sylow.coe_subgroup_smul, Sylow.coe_ofCard,
      Subgroup.mem_smul_pointwise_iff_exists] at hz'
    obtain ⟨r, hr, hrz⟩ := hz'
    exact ⟨r, hr, by simpa [MulAut.smul_def] using hrz⟩
  obtain ⟨r, hr, hrx⟩ := hmem _ ⟨x, hx, rfl⟩
  obtain ⟨r', hr', hry⟩ := hmem _ ⟨y, hy, rfl⟩
  refine ⟨r, hr, r', hr', fun hcomm => hxy ?_⟩
  apply Subtype.ext
  show (x : Q) * y = y * x
  have hrx' : g * r * g⁻¹ = (x : Q) := hrx
  have hry' : g * r' * g⁻¹ = (y : Q) := hry
  rw [← hrx', ← hry']
  calc g * r * g⁻¹ * (g * r' * g⁻¹) = g * (r * r') * g⁻¹ := by group
    _ = g * (r' * r) * g⁻¹ := by rw [hcomm]
    _ = g * r' * g⁻¹ * (g * r * g⁻¹) := by group

section RuRowFacts


attribute [local irreducible] CFSG.Blueprint.NativeSporadic.carrierGroup

theorem ru_hsec' (hf : RuLocalFacts) (hS : RuSuzukiModel) (hSz : SzEightModel) {G : Type}
    [Group G] [Finite G] (K₁ N₀ : Subgroup G) (hK : CFSG.IsQuasisimple ↥K₁)
    (hIsK : IsKRu (↥K₁ ⧸ CFSG.oddCore ↥K₁)) (hcan : CanLoc K₁ N₀) :
    ¬ (Group.IsSolvable ↥((N₀.subgroupOf K₁).map (QuotientGroup.mk' (center ↥K₁))) ∧
      (True → TwoSubgroupsAbelian ↥((N₀.subgroupOf K₁).map
        (QuotientGroup.mk' (center ↥K₁))))) := by
  rintro ⟨-, hab⟩
  have hab := hab trivial
  have : Group.IsPerfect ↥K₁ := hK.1
  obtain ⟨hsX, hcX, hXm, hXq⟩ := isKRu_data hf hS hIsK
  have hker : (QuotientGroup.mk' (CFSG.oddCore ↥K₁)).ker ≤ center ↥K₁ := by
    rw [QuotientGroup.ker_mk']
    exact oddCore_le_center hK
  have hsurjO := QuotientGroup.mk'_surjective (CFSG.oddCore ↥K₁)
  have hZX : center (↥K₁ ⧸ CFSG.oddCore ↥K₁) = ⊥ := center_eq_bot_of_simple_isQuasisimple_row hXq
  have hZc := card_center_eq_of_cover (QuotientGroup.mk' (CFSG.oddCore ↥K₁)) hsurjO hker
  rw [hZX, Subgroup.card_bot, mul_one, QuotientGroup.ker_mk'] at hZc
  have hZodd : Odd (Nat.card ↥(center ↥K₁)) := by
    rw [hZc]
    exact odd_card_oddCore' ↥K₁
  rcases hcan with ⟨hev, -⟩ | ⟨-, R, -, hRle, hRcard, hN₀⟩
  · exact absurd hev (Nat.not_even_iff_odd.2 hZodd)
  · obtain ⟨e⟩ := cqEquiv_of_cover (QuotientGroup.mk' (CFSG.oddCore ↥K₁)) hsurjO hker
    have hQs : IsSimpleGroup (↥K₁ ⧸ center ↥K₁) := hK.2.1
    have hQc : Nat.card (↥K₁ ⧸ center ↥K₁) = 29120 := by
      rw [Nat.card_congr e.toEquiv, card_quotient_center_of_simple hXq]
      exact hcX
    have hQm : SuzukiModel (↥K₁ ⧸ center ↥K₁) 2 3 :=
      suzukiModel_of_mulEquiv'
        (e.trans ((QuotientGroup.quotientMulEquivOfEq hZX).trans QuotientGroup.quotientBot)).symm
        hXm
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    let SR₁ : Sylow 2 ↥K₁ := Sylow.ofCard (R.subgroupOf K₁) (by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRle).toEquiv]
      exact hRcard)
    let Sb : Sylow 2 (↥K₁ ⧸ center ↥K₁) :=
      SR₁.mapSurjective (f := QuotientGroup.mk' (center ↥K₁)) (QuotientGroup.mk'_surjective _)
    have hSbcard : Nat.card ↥(Sb : Subgroup (↥K₁ ⧸ center ↥K₁)) = 2 ^ 6 :=
      (Sylow.card_eq_multiplicity Sb).trans (by rw [hQc, factorization_two_29120])
    obtain ⟨x, hx, y, hy, hxy⟩ :=
      szEight_sylow_nonabelian' hSz hQm hQs hQc (Sb : Subgroup _) hSbcard
    have hle : (Sb : Subgroup (↥K₁ ⧸ center ↥K₁)) ≤
        (N₀.subgroupOf K₁).map (QuotientGroup.mk' (center ↥K₁)) := by
      show (SR₁ : Subgroup ↥K₁).map (QuotientGroup.mk' (center ↥K₁)) ≤ _
      refine Subgroup.map_mono ?_
      show R.subgroupOf K₁ ≤ N₀.subgroupOf K₁
      intro k hk
      rw [Subgroup.mem_subgroupOf] at hk ⊢
      rw [hN₀]
      exact ⟨Subgroup.le_normalizer hk, k.2⟩
    have h2 : IsPGroup 2 ↥((Sb : Subgroup (↥K₁ ⧸ center ↥K₁)).subgroupOf
        ((N₀.subgroupOf K₁).map (QuotientGroup.mk' (center ↥K₁)))) :=
      Sb.isPGroup'.of_surjective (Subgroup.subgroupOfEquivOfLe hle).symm.toMonoidHom
        (MulEquiv.surjective _)
    have := hab _ h2 ⟨x, hle hx⟩ (Subgroup.mem_subgroupOf.2 hx) ⟨y, hle hy⟩
      (Subgroup.mem_subgroupOf.2 hy)
    exact hxy (congrArg Subtype.val this)

theorem hyp31RowFacts_ru' (hf : RuLocalFacts) (hSz : SzEightModel) (hmult : OddMultTrivial .Ru)
    (lo : LieModelOrders) (inp : RuHyp31Inputs) : Hyp31RowFacts IsKRu [.Ru] [] [] where
  reach := ⟨RuKnown, ruReachRow hf inp⟩
  evenOut := fun s hs => by
    rcases List.mem_singleton.1 hs with rfl
    exact inp.even
  up :=
    { fi23 := fun s hs => absurd hs List.not_mem_nil
      not_exc := fun s hs => absurd hs List.not_mem_nil
      odd := fun s hs => absurd hs List.not_mem_nil
      rank := fun s hs => absurd hs List.not_mem_nil }
  thm24 := fun s hs => by
    rcases List.mem_singleton.1 hs with rfl
    refine Or.inr ⟨by decide, fun X _ hq hodd hX => thm24Hex_of_card lo ru_pinned_card
      (by norm_num) (factorial_div_two_ne_of_between (n₀ := 14) (by norm_num [Nat.factorial])
        (by norm_num [Nat.factorial])) X hq hodd hX⟩
  std_row := fun G _ _ L K₁ T s hL _ hdata hq hK =>
    ru_std_row hf inp.suzuki hmult L K₁ T s hL hdata hq hK
  four_a := fourAFacts_of_lamProfile True 2 4 le_rfl
    (fun G _ _ L K₁ N₀ T s hL _ hdata hq hK hcan =>
      ru_hautC hf inp.suzuki hmult inp.normalizer L K₁ N₀ T s hL hdata hq hK hcan)
    (fun K₂ _ _ hperf ⟨X, _, hX, ⟨e⟩⟩ =>
      ru_hfix inp.szCover hperf
        (suzukiModel_of_mulEquiv' e.symm (isKRu_suzuki_cq hf inp.suzuki hX)))
    (fun G _ _ K₁ N₀ hq hK hcan => ru_hsec' hf inp.suzuki hSz K₁ N₀ hq hK hcan)

end RuRowFacts

end CFSG.EvenSporadicStandard.Induction
