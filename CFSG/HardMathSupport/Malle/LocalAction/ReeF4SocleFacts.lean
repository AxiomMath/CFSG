module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ReeF4Target
public import CFSG.RankThree.PartOne.K128.ReeShape
public import CFSG.RankThree.PartOne.K128.LangStep
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.JStarTargetTwoData

public section

namespace CFSG.HardMathSupport.Malle.LocalAction

open CFSG.AGLEmbedding CFSG.Blueprint CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.K1214 CFSG.RankThree.PartOne.K128
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)


theorem exists_reeGamma_model {K : Type} [Group K]
    {d : TauCeti.ValidLieTypeIndex} (hd : IsReeFFourFiveIndex d)
    (e : Nonempty (K ≃* CatGroup d)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F F4.prime),
      Nat.card F = 2 ^ (2 * 2 + 1) ∧ Nonempty (K ≃* F4.reeGamma F 2) := by
  obtain ⟨e₀⟩ := e
  have hmodel := reeTitsModel_of_catGroup_reeF4 (d := d) (m := 2) hd
  have hS := large_Ree_model_Schreier (CatGroup d) 2 (2 * 2 + 1) hmodel
  obtain ⟨-, a, hfa, F, _, _, hF, ⟨e'⟩⟩ := hmodel
  have ha : a = 2 := by omega
  subst ha
  have hKc : Nat.card F = 2 ^ (2 * 2 + 1) := hF
  have : CharP F F4.prime :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by norm_num) hF
  obtain ⟨eΓ⟩ := hS.2.2.2.2.2 2 F rfl hF ⟨e'⟩
  exact ⟨F, inferInstance, inferInstance, this, hKc, ⟨e₀.trans eΓ⟩⟩

theorem sylowShape_five_of_catGroup {K : Type}
    [Group K] {d : TauCeti.ValidLieTypeIndex} (hd : IsReeFFourFiveIndex d)
    (e : Nonempty (K ≃* CatGroup d)) : SylowShape 5 2 2 K := by
  obtain ⟨F, _, _, _, hF, ⟨eΓ⟩⟩ := exists_reeGamma_model hd e
  have h := sylowShape_ree_phi4 (a := 2) (K := F) hF (p := 5) Nat.prime_five (by norm_num)
    (by norm_num)
  have hfac : ((2 ^ (2 * 2 + 1)) ^ 2 + 1).factorization 5 = 2 := by
    have h : (2 ^ (2 * 2 + 1)) ^ 2 + 1 = 5 ^ 2 * 41 := by norm_num
    rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_five, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 5 ∣ 41)]
  rw [hfac] at h
  exact SylowShape.of_mulEquiv eΓ h

theorem pRank_le_two_of_isPGroup {K : Type}
    [Group K] [Finite K] {d : TauCeti.ValidLieTypeIndex} (hd : IsReeFFourFiveIndex d)
    (e : Nonempty (K ≃* CatGroup d)) (P : Subgroup K) (hP : IsPGroup 5 P) :
    CFSG.Open.pRank 5 P ≤ 2 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hsh := sylowShape_five_of_catGroup hd e
  unfold CFSG.Open.pRank
  refine csSup_le ⟨0, ⊥, bot_le, ⟨inferInstance, fun x hx => ?_⟩, by simp⟩ ?_
  · rw [Subgroup.mem_bot] at hx; subst hx; simp
  · rintro k ⟨E, hEP, hE, hk⟩
    have hEp : IsPGroup 5 E := hP.to_le hEP
    obtain ⟨S, hES⟩ := hEp.exists_le_sylow
    obtain ⟨f⟩ := hsh (S : Subgroup K) S.isPGroup' S.not_dvd_index
    have hcard : Nat.card E ≤ 5 ^ 2 := by
      let g : E → {v : Fin 2 → Multiplicative (ZMod (5 ^ 2)) // v ^ 5 = 1} := fun x =>
        ⟨f ⟨x, hES x.2⟩, by
          have := hE.2 x x.2
          rw [← map_pow]
          have h1 : (⟨(x : K), hES x.2⟩ : (S : Subgroup K)) ^ 5 = 1 :=
            Subtype.ext (by simpa using this)
          rw [h1, map_one]⟩
      have hg : Function.Injective g := by
        intro x y hxy
        have := congrArg Subtype.val hxy
        have h2 := f.injective this
        exact Subtype.ext (Subtype.mk.inj h2)
      calc Nat.card E ≤ Nat.card {v : Fin 2 → Multiplicative (ZMod (5 ^ 2)) // v ^ 5 = 1} :=
          Nat.card_le_card_of_injective g hg
        _ ≤ 5 ^ 2 := card_pow_eq_one_le Nat.prime_five 2
    rw [hk] at hcard
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 5)).1 hcard

theorem card_mulAut_dvd_five_mul {K : Type}
    [Group K] [Finite K] {d : TauCeti.ValidLieTypeIndex} (hd : IsReeFFourFiveIndex d)
    (e : Nonempty (K ≃* CatGroup d)) : Nat.card (MulAut K) ∣ 5 * Nat.card K := by
  obtain ⟨F, _, _, _, hF, ⟨eΓ⟩⟩ := exists_reeGamma_model hd e
  obtain ⟨-, hOutn⟩ := outer_reeGamma (a := 2) (K := F) (by norm_num) hF
  let eO := CFSG.ComponentClassification.OuterAutomorphisms.equivalence eΓ
  have h5 : Nat.card (Outer K) ∣ 5 := by
    rw [Nat.card_congr eO.toEquiv]
    simpa using hOutn
  exact (KFactProofs.TargetTwo.card_mulAut_dvd (L := K)).trans (Nat.mul_dvd_mul_right h5 _)

end CFSG.HardMathSupport.Malle.LocalAction
