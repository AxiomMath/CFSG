module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanG2QTor
public import CFSG.Timmesfeld.Orders.ExceptionalUntwisted
public import CFSG.RankThree.PartOne.BRANCH.RankArith
public import CFSG.LieType.Chevalley.CoordinateFieldBaseChange

public section

namespace CFSG.AGLEmbedding.KFactProofs.G2Q

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Timmesfeld.ExceptionalOrders

set_option linter.unusedSectionVars false


theorem card_le_nine_of_mod_three {K : Type} [Field K] [Finite K] (h3 : Nat.card K % 3 = 1)
    {E : Subgroup (adjointGroup .G2 K)} (hc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (h : ∀ x ∈ E, x ^ 3 = 1) : Nat.card E ≤ 9 := by
  classical
  have hQ : 2 ≤ Nat.card K := Finite.one_lt_card
  have hnt : Nontrivial Kˣ := by
    rw [← Finite.one_lt_card_iff_nontrivial, Nat.card_units]
    omega
  obtain ⟨g, hg⟩ := exists_ne (1 : Kˣ)
  have hExt := ext3_torusSub (K := K) hg
  have hTcard : Nat.card (torusSub K) = (Nat.card K - 1) ^ 2 := by
    rw [torusSub, Nat.card_congr (Subgroup.subgroupOfEquivOfLe torusGroup_le_adjoint).toEquiv]
    exact card_torusGroup_G2
  have hGcard : Nat.card (adjointGroup .G2 K) =
      Nat.card K ^ 6 * (Nat.card K ^ 6 - 1) * (Nat.card K ^ 2 - 1) := card_adjointGroup_G2
  have hTidx : (torusSub K).index * Nat.card (torusSub K) = Nat.card (adjointGroup .G2 K) :=
    Subgroup.index_mul_card _
  have h9 : ¬ 9 ∣ (torusSub K).index := by
    refine CFSG.RankThree.PartOne.BRANCH.not_nine_dvd_g2_split (Q := Nat.card K) hQ h3 ?_
    rw [← hGcard, ← hTidx, hTcard]
    ring
  have hH := card_extSub hExt
  have hHidx : (extSub hExt).index * Nat.card (extSub hExt) = Nat.card (adjointGroup .G2 K) :=
    Subgroup.index_mul_card _
  have hidx : (torusSub K).index = 3 * (extSub hExt).index := by
    have hpos : 0 < Nat.card (torusSub K) := Nat.card_pos
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [hTidx, ← hHidx, hH]
    ring
  have h3H : ¬ 3 ∣ (extSub hExt).index := by
    rintro ⟨c, hcc⟩
    exact h9 ⟨c, by rw [hidx, hcc]; ring⟩
  have hE : IsPGroup 3 E := fun x => ⟨1, Subtype.ext (by simpa using h x.1 x.2)⟩
  obtain ⟨g', E₁, hE₁, hcard, hmem⟩ :=
    CFSG.RankThree.PartOne.BRANCH.exists_conj_le_of_not_dvd_index (extSub hExt) Nat.prime_three
      (a := 0) (by simpa using h3H) hE
  set E₂ : Subgroup (adjointGroup .G2 K) := E₁.map (MulAut.conj g'⁻¹).toMonoidHom with hE₂def
  have hE₂ : E₂ ≤ extSub hExt := by
    rintro _ ⟨e, he, rfl⟩
    simpa [MulAut.conj_apply] using hmem e he
  have hE₂c : ∀ a ∈ E₂, ∀ b ∈ E₂, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hc a (hE₁ ha) b (hE₁ hb)]
  have hE₂3 : ∀ x ∈ E₂, x ^ 3 = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, h a (hE₁ ha), map_one]
  have hE₂card : Nat.card E₂ = Nat.card E₁ :=
    Subgroup.card_map_of_injective (MulAut.conj g'⁻¹).injective
  have hb := card_le_nine hExt (fun a ha b hb => torusSub_comm ha hb)
    (fun F hF h3 => card_le_nine_of_le_torus hF h3)
    (fun F hF h3 => card_le_three_of_fixed hF h3) hE₂ hE₂c hE₂3
  calc Nat.card E ≤ 3 ^ 0 * Nat.card E₁ := hcard
    _ = Nat.card E₂ := by rw [hE₂card]; ring
    _ ≤ 9 := hb

noncomputable def baseChangeAdjoint {K K' : Type} [Field K] [Field K'] (f : K →+* K') :
    adjointGroup .G2 K →* adjointGroup .G2 K' :=
  ((baseChangeGL f).comp (adjointGroup .G2 K).subtype).codRestrict (adjointGroup .G2 K') (by
    intro g
    have h1 : baseChangeGL f (g : ModGL .G2 K) ∈
        (adjointGroup .G2 K).map (baseChangeGL (τ := .G2) f) := ⟨g, g.2, rfl⟩
    rw [map_baseChangeGL_adjointGroup] at h1
    refine (Subgroup.closure_le _).2 ?_ h1
    rintro _ ⟨i, c, rfl | rfl⟩
    · exact Subgroup.subset_closure ⟨i, f c, Or.inl rfl⟩
    · exact Subgroup.subset_closure ⟨i, f c, Or.inr rfl⟩)

theorem baseChangeAdjoint_injective {K K' : Type} [Field K] [Field K'] (f : K →+* K') :
    Function.Injective (baseChangeAdjoint f) := by
  intro a b h
  apply Subtype.ext
  exact baseChangeGL_injective f (congrArg Subtype.val h)

theorem card_le_nine_of_not_dvd {K : Type} [Field K] [Finite K] (h3 : ¬ 3 ∣ Nat.card K)
    {E : Subgroup (adjointGroup .G2 K)} (hc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (h : ∀ x ∈ E, x ^ 3 = 1) : Nat.card E ≤ 9 := by
  by_cases hmod : Nat.card K % 3 = 1
  · exact card_le_nine_of_mod_three hmod hc h
  have hmod2 : Nat.card K % 3 = 2 := by omega
  have hp : (ringChar K).Prime := CharP.char_is_prime K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hp⟩
  let K' := FiniteField.Extension K (ringChar K) 2
  have hK' : Nat.card K' % 3 = 1 := by
    rw [show Nat.card K' = Nat.card K ^ 2 from FiniteField.natCard_extension K (ringChar K) 2,
      Nat.pow_mod, hmod2]
  let f : K →+* K' := algebraMap K K'
  let E' : Subgroup (adjointGroup .G2 K') := E.map (baseChangeAdjoint f)
  have hE'c : ∀ a ∈ E', ∀ b ∈ E', a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hc a ha b hb]
  have hE'3 : ∀ x ∈ E', x ^ 3 = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, h a ha, map_one]
  have hcard : Nat.card E' = Nat.card E :=
    Subgroup.card_map_of_injective (baseChangeAdjoint_injective f)
  rw [← hcard]
  exact card_le_nine_of_mod_three hK' hE'c hE'3

end CFSG.AGLEmbedding.KFactProofs.G2Q
