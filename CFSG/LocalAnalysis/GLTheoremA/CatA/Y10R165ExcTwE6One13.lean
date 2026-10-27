module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcTwE6One8
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcTwE6One3
public import CFSG.RankThree.SubgroupLists.ExtraspecialCore

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcTwE6

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.Minuscule CFSG.SeitzReduction
  CFSG.StandardType CFSG.LieType.Steinberg.Exceptional CFSG.SectionRank
  CFSG.SeitzReduction.F4Pilot CFSG.LieType.SeitzGeneration
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcTwE6One

theorem map_conjSub_map_eq {H K : Type*} [Group H] [Group K]
    (π : H →* K) {A : Subgroup H} {A₀ : Subgroup K} {c : K} {g : H}
    (hg : π g = c) (hc : (A.map π).map (MulAut.conj c).toMonoidHom = A₀) :
    (CFSG.Quasithin.A1b.conjSub g A).map π = A₀ := by
  rw [← hc, CFSG.Quasithin.A1b.conjSub]
  ext y
  constructor
  · rintro ⟨y, hx, rfl⟩
    obtain ⟨z, hz, rfl⟩ := hx
    refine ⟨π z, Subgroup.mem_map_of_mem _ hz, ?_⟩
    change c * π z * c⁻¹ = π (g * z * g⁻¹)
    rw [map_mul, map_mul, map_inv, hg]
  · rintro ⟨y, ⟨z, hz, rfl⟩, hy⟩
    refine ⟨(MulAut.conj g) z, Subgroup.mem_map_of_mem _ hz, ?_⟩
    change π (g * z * g⁻¹) = y
    rw [map_mul, map_mul, map_inv, hg]
    change c * π z * c⁻¹ = y at hy
    exact hy

theorem exists_conj_eq_model_lift {f p : ℕ} (hf : 1 ≤ f) (hp : p.Prime)
    (hp5 : 5 ≤ p) [NeZero p] (hrk : CFSG.LocalAnalysis.GLTheoremA.rk2Ord p f = 1)
    {A : Subgroup ↥(fixedGroup (GaloisField 2 (2 * f)) (frobQ 2 f))}
    {A₀ : Subgroup ↥(C0 f)}
    (hA : IsElemAbelian p A)
    (hmax : CFSG.Open.pRank p
        (⊤ : Subgroup ↥(fixedGroup (GaloisField 2 (2 * f)) (frobQ 2 f))) ≤
      CFSG.Open.pRank p A)
    (hA₀ : IsElemAbelian p A₀) (hA₀card : Nat.card ↥A₀ = p ^ 4) :
    ∃ A₁ : Subgroup ↥(fixedGroup (GaloisField 2 (2 * f)) (frobQ 2 f)),
      ∃ g : ↥(fixedGroup (GaloisField 2 (2 * f)) (frobQ 2 f)),
      IsElemAbelian p A₁ ∧
      A₁ = CFSG.Quasithin.A1b.conjSub g A ∧
      A₁.map (twistedIsogenyC hf (TwE6Toral.card_galoisField_two_mul f hf) (frobQ 2 f)
        (fun c => frobQ_apply 2 f c)) = A₀ ∧
      A₁ ⊓ Subgroup.center ↥(fixedGroup (GaloisField 2 (2 * f)) (frobQ 2 f)) = ⊥ := by
  classical
  have hp2 : p ≠ 2 := by omega
  have hK : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 :=
    TwE6Toral.card_galoisField_two_mul f hf
  have he : orderOf (((2 ^ f : ℕ)) : ZMod p) = 1 := by
    rw [CFSG.LocalAnalysis.GLTheoremA.rk2Ord] at hrk
    rw [Nat.cast_pow]
    exact hrk
  set π : ↥(fixedGroup (GaloisField 2 (2 * f)) (frobQ 2 f)) →* ↥(C0 f) :=
    twistedIsogenyC hf hK (frobQ 2 f) (fun c => frobQ_apply 2 f c) with hπdef
  have hAcard : Nat.card A = p ^ 4 :=
    card_eq_pow_four_of_maximal_rank hf hp hp5 he hA hmax
  have hsurj : Function.Surjective π :=
    twistedIsogenyC_surjective hf hK (frobQ 2 f) (fun c => frobQ_apply 2 f c)
  have hker : π.ker =
      Subgroup.center ↥(fixedGroup (GaloisField 2 (2 * f)) (frobQ 2 f)) :=
    ker_twistedIsogenyC hf hK (frobQ 2 f) (fun c => frobQ_apply 2 f c)
  have hpZ : ¬ p ∣ Nat.card ↥(Subgroup.center
      ↥(fixedGroup (GaloisField 2 (2 * f)) (frobQ 2 f))) :=
    not_dvd_card_center_of_rk2Ord_one (frobQ 2 f) hK (fun c => frobQ_apply 2 f c) hp hp2 hrk
  have hAinf : A ⊓ π.ker = ⊥ := by
    rw [hker]
    exact Subgroup.inf_eq_bot_of_coprime (by
      rw [hAcard]
      exact ((hp.coprime_iff_not_dvd).2 hpZ).pow_left 4)
  have hAmapcard : Nat.card (A.map π) = p ^ 4 := by
    have h := CFSG.RankThree.SubgroupLists.card_eq_card_map_mul_card_inf_ker π A
    rw [hAinf, Subgroup.card_bot, mul_one, hAcard] at h
    exact h.symm
  have hmain : ∃ c : ↥(C0 f),
      (A.map π).map (MulAut.conj c).toMonoidHom = A₀ :=
    exists_conj_eq_of_card_eq hf hp hp5 he
      (CFSG.SectionRank.isElemAbelian_map hA π) hAmapcard hA₀ hA₀card
  obtain ⟨c, hc⟩ := hmain
  obtain ⟨g, hg⟩ : ∃ g : ↥(fixedGroup (GaloisField 2 (2 * f)) (frobQ 2 f)), π g = c :=
    hsurj c
  have hcard : Nat.card ↥(CFSG.Quasithin.A1b.conjSub g A) = p ^ 4 := by
    rw [CFSG.Quasithin.A1b.conjSub, Subgroup.card_map_of_injective (MulAut.conj g).injective,
      hAcard]
  have hZ : CFSG.Quasithin.A1b.conjSub g A ⊓
      Subgroup.center ↥(fixedGroup (GaloisField 2 (2 * f)) (frobQ 2 f)) = ⊥ :=
    Subgroup.inf_eq_bot_of_coprime (by
      rw [hcard]
      exact ((hp.coprime_iff_not_dvd).2 hpZ).pow_left 4)
  exact ⟨CFSG.Quasithin.A1b.conjSub g A, g,
    CFSG.SectionRank.isElemAbelian_map hA _, rfl, map_conjSub_map_eq π hg hc, hZ⟩

theorem exists_conj_eq_model_lift_of_maximal_rank {f p : ℕ} (hf : 1 ≤ f) (hp : p.Prime)
    (hp5 : 5 ≤ p) [NeZero p] (hrk : CFSG.LocalAnalysis.GLTheoremA.rk2Ord p f = 1)
    {k : Type} [Field k] [Finite k] [Algebra k (GaloisField 2 (2 * f))]
    (hkk : Nat.card k = 2 ^ f)
    (h : UnitaryFieldData 2 f (GaloisField 2 (2 * f)))
    {ζ : (GaloisField 2 (2 * f))ˣ} (hζ : orderOf ζ = p)
    (hζbar : h.bar (ζ : GaloisField 2 (2 * f)) = ζ)
    {t : kˣ} (ht : orderOf t = p)
    (hσ : ∀ c, frobQ 2 f c = c ^ 2 ^ f)
    {A : Subgroup ↥(fixedGroup (GaloisField 2 (2 * f)) (frobQ 2 f))}
    (hA : IsElemAbelian p A)
    (hmax : CFSG.Open.pRank p
        (⊤ : Subgroup ↥(fixedGroup (GaloisField 2 (2 * f)) (frobQ 2 f))) ≤
      CFSG.Open.pRank p A) :
    ∃ A₁ : Subgroup ↥(fixedGroup (GaloisField 2 (2 * f)) (frobQ 2 f)),
      ∃ g : ↥(fixedGroup (GaloisField 2 (2 * f)) (frobQ 2 f)),
      IsElemAbelian p A₁ ∧
      A₁ = CFSG.Quasithin.A1b.conjSub g A ∧
      A₁.map (twistedIsogenyC hf (TwE6Toral.card_galoisField_two_mul f hf) (frobQ 2 f)
        (fun c => frobQ_apply 2 f c)) =
        thetaTorusP (f := f) t ⊔
          (R3Levi h p hp (by omega) ζ hζ hζbar hσ).subgroupOf (C0 f) ∧
      A₁ ⊓ Subgroup.center ↥(fixedGroup (GaloisField 2 (2 * f)) (frobQ 2 f)) = ⊥ :=
  exists_conj_eq_model_lift hf hp hp5 hrk hA hmax
    (isElemAbelian_thetaTorusP_sup_R3Levi hf hkk h hp (by omega) hζ hζbar ht hσ)
    (card_thetaTorusP_sup_R3Levi hf hkk h hp (by omega) hζ hζbar ht hσ)

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcTwE6
