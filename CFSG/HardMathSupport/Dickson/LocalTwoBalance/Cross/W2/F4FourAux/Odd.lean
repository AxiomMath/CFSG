module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.F4FourAux.Assembly
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.Chevalley.F4Weyl CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.E6 CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupEvenCanonical SteinbergBN
open scoped Pointwise commutatorElement

set_option linter.unusedSectionVars false

theorem p_dvd_card_f4Sp {K : Type} [Field K] [Finite K] {p : ℕ} (hpd : p ∣ Nat.card K ^ 2 + 1) :
    p ∣ Nat.card (matrixIsometryGroup (f4J0 K)) := by
  rw [Nat.card_congr (f4SpEquiv K).toEquiv,
    CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp_two]
  refine Dvd.dvd.mul_left ?_ _
  refine Dvd.dvd.mul_left ?_ _
  have h1 : Nat.card K ^ 4 - 1 = (Nat.card K ^ 2 + 1) * (Nat.card K ^ 2 - 1) := by
    have : 1 ≤ Nat.card K ^ 2 := Nat.one_le_pow _ _ Nat.card_pos
    zify [this, Nat.one_le_pow _ _ Nat.card_pos]
    ring
  rw [h1]
  exact Dvd.dvd.mul_right hpd _

section Actor


variable (K : Type) [Field K] [Finite K] (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
  (F : Ω →+* Ω)

theorem f4FourActor_odd {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) (hF : ∀ c, F c = c ^ Nat.card K) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hpd : p ∣ Nat.card K ^ 2 + 1) {g : ModGL Tag.F4 Ω}
    (hg : g ∈ adjointGroup Tag.F4 Ω)
    (hgn : g⁻¹ * Units.map (entrywiseHom F) g =
      canonicalRep (coxeterSystem Tag.F4) Ω (f4Coxeter ^ 3))
    {x : ModGL Tag.F4 Ω} (hx : x ∈ torusGroup Tag.F4 Ω ⊓ conjEntrywiseImage K g⁻¹)
    (hxp : orderOf x = p) (hne : {α | IsRoot Tag.F4 α ∧ torusRootChar x α = 1}.Nonempty)
    {x₁ : adjointGroup Tag.F4 K}
    (hx₁ : baseChangeGL (algebraMap K Ω) (x₁ : ModGL Tag.F4 K) = g * x * g⁻¹) :
    F4FourActorAt K Ω p g x x₁ := by
  classical
  set n := canonicalRep (coxeterSystem Tag.F4) Ω (f4Coxeter ^ 3) with hn
  set Γ := conjEntrywiseImage K g⁻¹ with hΓ
  set T₀ := torusGroup Tag.F4 Ω ⊓ Γ with hT₀
  obtain ⟨-, -, -, hpr, -⟩ := (F4_cyclotomic_four_torus_and_regular_prime_centralizers K Ω F hF n
    rfl).2 g hg hgn Γ T₀ (T₀.map (MulAut.conj g).toMonoidHom) rfl rfl rfl
  obtain ⟨-, -, -, hcls⟩ := hpr p hp hp3 hpd
  obtain ⟨hcase, -, -⟩ := hcls x hx hxp _ rfl
  obtain ⟨u, ε, hε, hu, huw⟩ := hcase.resolve_left hne.ne_empty
  set h := canonicalRep (coxeterSystem Tag.F4) Ω u with hh
  set Γ₁ := Γ.map (MulAut.conj h).toMonoidHom with hΓ₁
  set D := Γ₁ ⊓ centralizer {h * x * h⁻¹} with hD
  set R := ⁅D, D⁆ with hR
  obtain ⟨-, ⟨-, -, -, -, e, -, -⟩, hRq, -, -, -, -, ⟨-, hCDR, -, -⟩,
      ⟨x₀, hx₀, hD₀, hR₀', R₀, hR₀le, M, -, kM, -, hkeq⟩, hroot⟩ :=
    odd_F4_cyclotomic_four_nonregular_derived_centralizers hℓ hℓ2 hf K hK Ω F hF hp hp3 n g rfl hg
      hgn Γ T₀ rfl rfl x hx hxp u ε hε hu huw h (h * x * h⁻¹) rfl rfl Γ₁ D R rfl rfl rfl
  have hx₀₁ : x₀ = x₁ :=
    Subtype.ext (baseChangeGL_injective (τ := Tag.F4) (algebraMap K Ω) (hx₀.trans hx₁.symm))
  subst hx₀₁
  set ι' : adjointGroup Tag.F4 K →* ModGL Tag.F4 Ω :=
    (baseChangeGL (algebraMap K Ω)).comp (adjointGroup Tag.F4 K).subtype with hι'
  have hι'inj : Function.Injective ι' :=
    (baseChangeGL_injective (τ := Tag.F4) (algebraMap K Ω)).comp Subtype.val_injective
  have eR : (⁅centralizer ({x₀} : Set (adjointGroup Tag.F4 K)),
      centralizer ({x₀} : Set (adjointGroup Tag.F4 K))⁆ : Subgroup (adjointGroup Tag.F4 K)) ≃* R :=
    (Subgroup.equivMapOfInjective _ ι' hι'inj).trans ((MulEquiv.subgroupCongr hR₀').trans
      (Subgroup.equivMapOfInjective R _ (MulAut.conj (g * h⁻¹)).injective).symm)
  have hq₀ := CFSG.LocalCores.isQuasisimple_of_mulEquiv eR.symm hRq
  have hpR : ¬ Nat.Coprime p (Nat.card (⁅centralizer ({x₀} : Set (adjointGroup Tag.F4 K)),
      centralizer ({x₀} : Set (adjointGroup Tag.F4 K))⁆ : Subgroup (adjointGroup Tag.F4 K))) := by
    rw [Nat.card_congr (eR.toEquiv.trans e.toEquiv)]
    exact fun hc => hp.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hc dvd_rfl
      (p_dvd_card_f4Sp hpd))
  have hconj1 : ((Matrix.SpecialLinearGroup.map (algebraMap K M)).range.map
      (CFSG.RankThree.Classical.conjSL (1 : GL (Fin 2) M))) =
        (Matrix.SpecialLinearGroup.map (algebraMap K M)).range := by
    have h1 : CFSG.RankThree.Classical.conjSL (1 : GL (Fin 2) M) = MonoidHom.id _ :=
      MonoidHom.ext fun A => Subtype.ext (by
        simp only [CFSG.RankThree.Classical.conjSL, Units.val_one, inv_one, Matrix.one_mul,
          Matrix.mul_one]
        rfl)
    rw [h1, Subgroup.map_id]
  have hinner := (odd_F4_descended_A2_root_SL2_pointwise_automorphisms_inner hℓ hℓ2 hf K hK M
    (algebraMap K M) .short R₀ (kM : ModGL Tag.F4 M) 1 (by rw [hconj1]; exact hkeq)).1
  have hcen : ∀ η : MulAut (adjointGroup Tag.F4 K), η x₀ = x₀ →
      (∀ r ∈ (⁅centralizer ({x₀} : Set (adjointGroup Tag.F4 K)),
        centralizer ({x₀} : Set (adjointGroup Tag.F4 K))⁆ : Subgroup (adjointGroup Tag.F4 K)),
          η r = r) →
      ∃ c ∈ centralizer ({x₀} : Set (adjointGroup Tag.F4 K)) ⊓
        centralizer ((⁅centralizer ({x₀} : Set (adjointGroup Tag.F4 K)),
          centralizer ({x₀} : Set (adjointGroup Tag.F4 K))⁆ : Subgroup (adjointGroup Tag.F4 K)) :
            Set (adjointGroup Tag.F4 K)), η = MulAut.conj c := by
    intro η hηx hηR
    obtain ⟨c, hc⟩ := hinner η fun r hr => hηR r (hR₀le hr)
    refine ⟨c, Subgroup.mem_inf.2 ⟨mem_centralizer_singleton_iff.2 ?_,
      Subgroup.mem_centralizer_iff.2 fun r hr => ?_⟩, hc.symm⟩
    · have h1 := hηx
      rw [← hc, MulAut.conj_apply] at h1
      exact mul_inv_eq_iff_eq_mul.1 h1
    · have h1 := hηR r hr
      rw [← hc, MulAut.conj_apply] at h1
      exact (mul_inv_eq_iff_eq_mul.1 h1).symm
  refine ⟨hq₀, hpR, hcen, fun y hy => ?_⟩
  obtain ⟨hyC, hyR⟩ := hy
  have h1 : ι' y ∈ (centralizer ({x₀} : Set (adjointGroup Tag.F4 K))).map ι' := ⟨y, hyC, rfl⟩
  rw [hD₀] at h1
  obtain ⟨d, hdD, hdy⟩ := h1
  have hdR : d ∈ centralizer (R : Set (ModGL Tag.F4 Ω)) := by
    rw [mem_centralizer_iff]
    intro r hr
    have hr' : (MulAut.conj (g * h⁻¹)).toMonoidHom r ∈
        (⁅centralizer ({x₀} : Set (adjointGroup Tag.F4 K)),
          centralizer ({x₀} : Set (adjointGroup Tag.F4 K))⁆ :
            Subgroup (adjointGroup Tag.F4 K)).map ι' := by
      rw [hR₀']
      exact ⟨r, hr, rfl⟩
    obtain ⟨r', hr'R, hr'e⟩ := hr'
    have hc := mem_centralizer_iff.1 hyR r' hr'R
    have hdy' : (MulAut.conj (g * h⁻¹)) d = ι' y := hdy
    have hr'e' : ι' r' = (MulAut.conj (g * h⁻¹)) r := hr'e
    apply (MulAut.conj (g * h⁻¹)).injective
    rw [map_mul (MulAut.conj (g * h⁻¹)) r d, map_mul (MulAut.conj (g * h⁻¹)) d r, hdy', ← hr'e',
      ← map_mul ι', ← map_mul ι', hc]
  have hdDR : d ∈ D ⊓ centralizer (R : Set (ModGL Tag.F4 Ω)) := ⟨hdD, hdR⟩
  have hkey : g⁻¹ * baseChangeGL (algebraMap K Ω) (y : ModGL Tag.F4 K) * g =
      h⁻¹ * d * h⁻¹⁻¹ := by
    change g⁻¹ * ι' y * g = _
    rw [← hdy]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  obtain ⟨⟨t₀, ht₀, ht₀d⟩, -, -⟩ := (hCDR d).1 hdDR
  refine ⟨?_, fun α hα => ?_⟩
  · rw [hkey, ← ht₀d]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [show h⁻¹ * (h * t₀ * h⁻¹) * h⁻¹⁻¹ = t₀ by group]
    exact ht₀.1
  · rw [hkey]
    exact hroot α hα _ ⟨d, hdDR, rfl⟩

end Actor

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2
