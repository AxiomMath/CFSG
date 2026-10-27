module

public import CFSG.LieType.SeitzGeneration.ExcPlaneSzTits
public import CFSG.LieType.SeitzGeneration.ExcPlaneG2
public import CFSG.LieType.SeitzGeneration.HyperEx
public import CFSG.LieType.Simplicity.Finiteness

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open CFSG.AGLEmbedding
  TauCeti CFSG.LieType.Ree

theorem false_of_rankLE2_of_card {G : Type*} [Group G] {p : ℕ} (hp : p.Prime) (h : RankLE2 p G)
    {E : Subgroup G} (hE : IsElemAbelian p E) (hc : Nat.card E = p ^ 3) : False := by
  have h1 := h E hE
  rw [hc] at h1
  exact absurd h1 (not_le.2 (Nat.pow_lt_pow_right hp.one_lt (by norm_num)))

@[expose] def HyperExReeTypeThree : Prop :=
  SeitzHyperLieEx fun d p _ => (IsReeF4Index d.1 ∨ IsTitsIndex d.1) ∧ p = 3

section Suzuki


theorem rankLE2_cat_suzuki {m : ℕ} (hv : (LieTypeIndex.suzuki m).Valid) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) : RankLE2 p (Cat ⟨.suzuki m, hv⟩) := by
  have hmodel : SuzukiModel (Cat ⟨.suzuki m, hv⟩) 2 (2 * m + 1) :=
    CFSG.SectionRank.suzukiModel_of_mulEquiv (MulEquiv.refl _)
      (CFSG.RankThree.PartTwo.Sec4.Census.suzukiModel_of_index m hv)
  obtain ⟨-, a, ha, F, _, _, hfa, hF, ⟨e⟩⟩ := hmodel
  have hF' : Nat.card F = 2 ^ (2 * a + 1) := by rw [hF, hfa]
  have e' : Cat ⟨.suzuki m, hv⟩ ≃* CFSG.Open.GLASzGroup a F :=
    e.trans (MulEquiv.subgroupCongr (CFSG.LieType.BorelTits.suzukiGroup_eq_glaSzGroup a F))
  have : Finite (Cat ⟨.suzuki m, hv⟩) := Finite.of_equiv _ e.symm.toEquiv
  exact rankLE2_of_oddSylow_cyclic hp hp2
    (CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator.suzuki_model_oddSylow_cyclic a ha
      hF' e')

end Suzuki

section Ree


theorem rankLE2_cat_reeG2 {m : ℕ} (hv : (LieTypeIndex.reeG2 m).Valid) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) : RankLE2 p (Cat ⟨.reeG2 m, hv⟩) := by
  obtain ⟨X, _, _, _, hX, ⟨e⟩⟩ := exists_reeGamma_equiv_cat_G2 hv
  have hp5 : 5 ≤ p := (eq_three_or_five_le hp hp2).resolve_left hp3
  have hpq : ¬ p ∣ Nat.card X := by
    rw [hX]
    exact fun h => hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h))
  let f : ReeTag.G2.reeGamma X m →* adjointGroup ReeTag.G2.tag X :=
    { toFun := fun g => ⟨g, (ReeTag.mem_reeGamma.1 g.2).1⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hf : Function.Injective f := fun g₁ g₂ h => by
    have h' := congrArg Subtype.val h
    exact Subtype.ext h'
  exact RankLE2.of_injective (f.comp e.toMonoidHom) (hf.comp e.injective)
    (rankLE2_adjointGroup_G2 X hp hp5 hpq)

end Ree

section ReeF4


theorem rankLE2_cat_reeF4_five {m : ℕ} (hv : (LieTypeIndex.reeF4 m).Valid) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) : RankLE2 p (Cat ⟨.reeF4 m, hv⟩) := by
  have hmodel := reeTitsModel_cat_reeF4 hv
  have := CFSG.LieType.Simplicity.fam_ree_tits_finiteness _ _ _ _ hmodel
  exact rankLE2_of_noPowThree hp fun _ hE hc =>
    CFSG.RankThree.PartOne.Q1327C.false_of_pow_three_ree_five hmodel hp hp5 hE hc

end ReeF4

section Tits


theorem false_of_cube_tits (hv : LieTypeIndex.tits.Valid) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hp3 : p ≠ 3) {E : Subgroup (Cat ⟨.tits, hv⟩)} (hc : Nat.card E = p ^ 3) : False := by
  have hT := card_cat_tits hv
  have : Finite (Cat ⟨.tits, hv⟩) := Nat.finite_of_card_ne_zero (by rw [hT]; norm_num)
  have hdvd : p ^ 3 ∣ 17971200 := by
    rw [← hT, ← hc]
    exact Subgroup.card_subgroup_dvd_card E
  by_cases hp5 : p = 5
  · subst hp5
    norm_num at hdvd
  · exact not_sq_dvd_card_tits hp hp2 hp3 hp5 ((pow_dvd_pow p (by norm_num)).trans hdvd)

end Tits

section All


theorem hyperExFor_reeType (h3 : HyperExReeTypeThree) :
    HyperExFor fun d => IsReeTypeIndex d.1 := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hl ⟨E₀, hE₀, hc₀, hd⟩
  by_cases h3p : p = 3 ∧ (IsReeF4Index d ∨ IsTitsIndex d)
  · exact h3 ⟨d, hv⟩ p hp hp2 hpd hl ⟨E₀, hE₀, hc₀, h3p.2, h3p.1⟩
  exfalso
  rcases hd with ⟨m, rfl⟩ | ⟨m, rfl⟩ | ⟨m, rfl⟩ | rfl
  · exact false_of_rankLE2_of_card hp (rankLE2_cat_suzuki hv hp hp2) hE₀ hc₀
  · have hp3 : p ≠ 3 := by simpa using hpd
    exact false_of_rankLE2_of_card hp (rankLE2_cat_reeG2 hv hp hp2 hp3) hE₀ hc₀
  · have hp3 : p ≠ 3 := fun h => h3p ⟨h, Or.inl ⟨m, rfl⟩⟩
    have hp5 : 5 ≤ p := (eq_three_or_five_le hp hp2).resolve_left hp3
    exact false_of_rankLE2_of_card hp (rankLE2_cat_reeF4_five hv hp hp5) hE₀ hc₀
  · have hp3 : p ≠ 3 := fun h => h3p ⟨h, Or.inr rfl⟩
    exact false_of_cube_tits hv hp hp2 hp3 hc₀

end All

end CFSG.LieType.SeitzGeneration
