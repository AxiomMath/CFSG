module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitL219C
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aOddQuotIso
public import CFSG.LocalAnalysis.ComponentInitial.SwappedQuasisimple
public import CFSG.GH74.GLS.Defs
public import CFSG.GH74.GLS.Pattern
public import CFSG.GH74.GLS.TwoThin.Basic
public import CFSG.GH74.GLS.TwoThin.Pumpup
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma45c
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82

public section

namespace CFSG.OddStandard.HigherRank.F3

open Subgroup CFSG CFSG.Open CFSG.ComponentClassification.HarrisLit
open CFSG.GH74.GLS.TwoThin CFSG.LocalAnalysis.ComponentInitial

variable {H : Type} [Group H] [Finite H]

theorem nonempty_bar_equiv_map_barMk {K₀ : Subgroup H} (hK₀ : IsTwoComponent K₀) :
    Nonempty (↥K₀ ⧸ pPrimeCore 2 ↥K₀ ≃*
      ↥(K₀.map (barMk H)) ⧸ pPrimeCore 2 ↥(K₀.map (barMk H))) := by
  set f := (barMk H).subgroupMap K₀
  have hf : Function.Surjective f := (barMk H).subgroupMap_surjective K₀
  have hker : ¬ 2 ∣ Nat.card f.ker := by
    have hle : f.ker.map K₀.subtype ≤ pPrimeCore 2 H := by
      rintro _ ⟨x, hx, rfl⟩
      have h1 : barMk H (x : H) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have hdvd : Nat.card f.ker ∣ Nat.card ↥(pPrimeCore 2 H) := by
      rw [← Subgroup.card_map_of_injective K₀.subtype_injective]
      exact Subgroup.card_dvd_of_le hle
    exact fun h2 =>
      (Nat.prime_two.coprime_iff_not_dvd.mp pPrimeCore_coprime_card) (h2.trans hdvd)
  exact CFSG.ComponentClassification.GSThmB.OddQuot.nonempty_pPrimeCore_equiv_of_surjective
    f hf hker

theorem card_map_barMk {K₀ : Subgroup H} (hK₀ : IsTwoComponent K₀) :
    Nat.card ↥(K₀.map (barMk H)) = Nat.card (↥K₀ ⧸ pPrimeCore 2 ↥K₀) := by
  obtain ⟨e⟩ := nonempty_bar_equiv_map_barMk hK₀
  have hc : IsComponent (K₀.map (barMk H)) :=
    isComponent_map_barMk ((L219.isTwoComponent_iff_twoComponents K₀).mp hK₀)
  have hO : pPrimeCore 2 ↥(K₀.map (barMk H)) = ⊥ :=
    pPrimeCore_eq_bot_of_isSubnormal (pPrimeCore_quotient_pPrimeCore_eq_bot 2) hc.2
  have e' : ↥(K₀.map (barMk H)) ≃* ↥K₀ ⧸ pPrimeCore 2 ↥K₀ :=
    (QuotientGroup.quotientBot.symm.trans
      (QuotientGroup.quotientMulEquivOfEq hO.symm)).trans e.symm
  exact Nat.card_congr e'.toEquiv

theorem card_quotient_le_card_map_barMk (R : Subgroup H) :
    Nat.card (↥R ⧸ pPrimeCore 2 ↥R) ≤ Nat.card ↥(R.map (barMk H)) := by
  set ρ := (barMk H).subgroupMap R with hρ
  have hρs : Function.Surjective ρ := (barMk H).subgroupMap_surjective R
  have hkerO : ρ.ker.map R.subtype ≤ pPrimeCore 2 H := by
    rintro _ ⟨r, hr, rfl⟩
    rw [← ker_barMk, MonoidHom.mem_ker]
    exact congrArg Subtype.val (MonoidHom.mem_ker.mp hr)
  have hker : ρ.ker ≤ pPrimeCore 2 ↥R := by
    refine le_sSup ⟨ρ.normal_ker, ?_⟩
    have h := Subgroup.card_dvd_of_le hkerO
    rw [Subgroup.card_map_of_injective R.subtype_injective] at h
    exact Nat.Coprime.coprime_dvd_right h pPrimeCore_coprime_card
  let q : ↥R ⧸ ρ.ker →* ↥R ⧸ pPrimeCore 2 ↥R := QuotientGroup.map _ _ (MonoidHom.id _) hker
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨r, rfl⟩ := QuotientGroup.mk_surjective y
    exact ⟨QuotientGroup.mk r, rfl⟩
  let e := QuotientGroup.quotientKerEquivOfSurjective ρ hρs
  calc Nat.card (↥R ⧸ pPrimeCore 2 ↥R) ≤ Nat.card (↥R ⧸ ρ.ker) :=
        Nat.card_le_card_of_surjective q hq
    _ = Nat.card ↥(R.map (barMk H)) := Nat.card_congr e.toEquiv

theorem inf_conjSub_eq_bot {X : Type} [Group X] [Finite X] {t : X} (ht : t * t = 1)
    {A : Subgroup X} (hA : pPrimeCore 2 ↥A = ⊥) (hAB : ⁅A, conjSub t⁻¹ A⁆ = ⊥)
    (hinj : Function.Injective (swapDiag hAB)) : A ⊓ conjSub t⁻¹ A = ⊥ := by
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have htinv : t⁻¹ * t⁻¹ = 1 := by rw [ht', ht]
  have hconj : ∀ a : X, t⁻¹ * (t⁻¹ * a * t) * t = a := by
    intro a
    have h2 : t⁻¹ * (t⁻¹ * a * t) * t = (t⁻¹ * t⁻¹) * a * (t * t) := by group
    rw [h2, htinv, ht, one_mul, mul_one]
  have hmemA : ∀ y ∈ A ⊓ conjSub t⁻¹ A, t⁻¹ * y * t ∈ A := by
    intro y hy
    obtain ⟨a, ha, hay⟩ := hy.2
    rw [← hay]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [hconj a]
    exact ha
  have hfix : ∀ y ∈ A ⊓ conjSub t⁻¹ A, t⁻¹ * y * t = y := by
    intro y hy
    have hy' : t⁻¹ * y * t ∈ A ⊓ conjSub t⁻¹ A :=
      Subgroup.mem_inf.2 ⟨hmemA y hy, conj_mem_conjSub hy.1⟩
    have hδ : swapDiag hAB ⟨y, hy.1⟩ = swapDiag hAB ⟨t⁻¹ * y * t, hy'.1⟩ := by
      rw [swapDiag_apply, swapDiag_apply, hconj y]
      exact commute_of_commutator_conj_eq_bot hAB hy.1 hy'.2
    exact (congrArg Subtype.val (hinj hδ)).symm
  have hnoTwo : ∀ y ∈ A ⊓ conjSub t⁻¹ A, y * y = 1 → y = 1 := by
    intro y hy hyy
    have hδy : swapDiag hAB ⟨y, hy.1⟩ = 1 := by rw [swapDiag_apply, hfix y hy, hyy]
    have hδ1 : swapDiag hAB ⟨1, one_mem A⟩ = 1 := map_one (swapDiag hAB)
    have h1 : (⟨y, hy.1⟩ : A) = ⟨1, one_mem A⟩ := hinj (hδy.trans hδ1.symm)
    exact Subtype.ext_iff.mp h1
  have hIleCenter : (A ⊓ conjSub t⁻¹ A).subgroupOf A ≤ Subgroup.center A := by
    intro y hy
    rw [Subgroup.mem_center_iff]
    intro a
    exact Subtype.ext (commute_of_commutator_conj_eq_bot hAB a.2
      (Subgroup.mem_subgroupOf.mp hy).2)
  have hIodd : Odd (Nat.card ↥((A ⊓ conjSub t⁻¹ A).subgroupOf A)) := by
    rw [← Nat.not_even_iff_odd]
    intro heven
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card'
      (G := ↥((A ⊓ conjSub t⁻¹ A).subgroupOf A)) 2 (even_iff_two_dvd.mp heven)
    have hzz : z * z = 1 := by
      have := pow_orderOf_eq_one z
      rw [hz, pow_two] at this
      exact this
    have hzX : ((z : A) : X) * ((z : A) : X) = 1 := by
      have := congrArg (fun w : ↥((A ⊓ conjSub t⁻¹ A).subgroupOf A) => (((w : A) : X))) hzz
      simpa using this
    have hzI : ((z : A) : X) ∈ A ⊓ conjSub t⁻¹ A := Subgroup.mem_subgroupOf.mp z.2
    have hz1 : ((z : A) : X) = 1 := hnoTwo _ hzI hzX
    have hzA : (z : A) = 1 := Subtype.ext hz1
    have hzz1 : z = 1 := Subtype.ext hzA
    rw [hzz1] at hz
    simp at hz
  rw [eq_bot_iff]
  intro y hy
  rw [Subgroup.mem_bot]
  have hyJ : (⟨y, hy.1⟩ : A) ∈ (A ⊓ conjSub t⁻¹ A).subgroupOf A := by
    rw [Subgroup.mem_subgroupOf]; exact hy
  have hbot : (A ⊓ conjSub t⁻¹ A).subgroupOf A = ⊥ :=
    (pPrimeCore_eq_bot_iff.mp hA) _ (Subgroup.normal_of_le_center hIleCenter)
      (Nat.coprime_two_left.mpr hIodd)
  rw [hbot, Subgroup.mem_bot] at hyJ
  exact Subtype.ext_iff.mp hyJ

theorem inf_map_barMk_eq_bot {t : H} (ht : orderOf t = 2) {K₀ K₁ R : Subgroup H}
    (hK₀ : IsTwoComponent K₀) (hK₁ : K₁ = K₀.map (MulAut.conj t).toMonoidHom) (hne : K₁ ≠ K₀)
    (hR : R = centralizerResidual (K₀ ⊔ K₁) t)
    (hφ : Nonempty (↥K₀ ⧸ pPrimeCore 2 ↥K₀ ≃* ↥R ⧸ pPrimeCore 2 ↥R)) :
    K₀.map (barMk H) ⊓ K₁.map (barMk H) = ⊥ := by
  subst hK₁ hR
  have hK₀' := (L219.isTwoComponent_iff_twoComponents K₀).mp hK₀
  obtain ⟨hY₀c, hY₁eq, -⟩ := L219.diag_setup ht hK₀' hne
  obtain ⟨hAB, hmap⟩ := (L219.part_b1 ht hK₀' hne).2
  set R' := centralizerResidual (K₀ ⊔ K₀.map (MulAut.conj t).toMonoidHom) t with hR'
  have hle : Nat.card ↥(K₀.map (barMk H)) ≤ Nat.card ↥(swapDiag hAB).range := by
    calc Nat.card ↥(K₀.map (barMk H)) = Nat.card (↥K₀ ⧸ pPrimeCore 2 ↥K₀) :=
          card_map_barMk hK₀
      _ = Nat.card (↥R' ⧸ pPrimeCore 2 ↥R') := Nat.card_congr hφ.some.toEquiv
      _ ≤ Nat.card ↥(R'.map (barMk H)) := card_quotient_le_card_map_barMk R'
      _ = Nat.card ↥(swapDiag hAB).range := by rw [hmap]
  have hmul := Subgroup.card_ker_mul_card_range (swapDiag hAB)
  have hkerle : Nat.card (swapDiag hAB).ker ≤ 1 := by
    have hb : 0 < Nat.card ↥(swapDiag hAB).range := Nat.card_pos
    refine Nat.le_of_mul_le_mul_right ?_ hb
    rw [one_mul, hmul]
    exact hle
  have hkerbot : (swapDiag hAB).ker = ⊥ := (Subgroup.card_le_one_iff_eq_bot _).mp hkerle
  have hinj : Function.Injective (swapDiag hAB) := (MonoidHom.ker_eq_bot_iff _).mp hkerbot
  have ht' : barMk H t * barMk H t = 1 := by
    have := pow_orderOf_eq_one (barMk H t)
    rw [orderOf_barMk ht, pow_two] at this
    exact this
  have hA : pPrimeCore 2 ↥(K₀.map (barMk H)) = ⊥ :=
    pPrimeCore_eq_bot_of_isSubnormal (pPrimeCore_quotient_pPrimeCore_eq_bot 2) hY₀c.2
  rw [hY₁eq]
  exact inf_conjSub_eq_bot (X := barQ H) ht' hA hAB hinj

end CFSG.OddStandard.HigherRank.F3
