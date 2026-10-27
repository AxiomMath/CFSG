module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.F4FourAux.Assembly
public import CFSG.RankThree.Chevalley.SteinbergCAF4CyclotomicThreeSixActors
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Arith
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MnSyl

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo.SeitzRows

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.Chevalley.F4Weyl CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.E6 CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupEvenCanonical SteinbergBN
  CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2 CFSG.RankThree.Chevalley.EvenF4QPlus
open scoped Pointwise commutatorElement MatrixGroups

set_option linter.unusedSectionVars false

theorem p_dvd_card_SL3 {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpd : p ∣ Nat.card K ^ 2 + Nat.card K + 1) :
    p ∣ Nat.card SL(3, K) := by
  have : Fintype K := Fintype.ofFinite K
  have : Fact p.Prime := ⟨hp⟩
  have hq1 : 1 < Nat.card K := Finite.one_lt_card
  have hqc : Nat.card K = Fintype.card K := Nat.card_eq_fintype_card
  have h3 : ((Fintype.card K : ℕ) : ZMod p) ^ 2 + ((Fintype.card K : ℕ) : ZMod p) + 1 = 0 := by
    have := (ZMod.natCast_eq_zero_iff _ _).2 hpd
    rw [hqc] at this
    push_cast at this
    exact this
  have hq3 : ((Fintype.card K : ℕ) : ZMod p) ^ 3 = 1 := by
    linear_combination (((Fintype.card K : ℕ) : ZMod p) - 1) * h3
  have hq1' : ((Fintype.card K : ℕ) : ZMod p) ≠ 1 := fun h => by
    rw [h] at h3
    have h3' : ((3 : ℕ) : ZMod p) = 0 := by
      push_cast
      linear_combination h3
    have := (ZMod.natCast_eq_zero_iff _ _).1 h3'
    have := Nat.le_of_dvd (by norm_num) this
    omega
  have hord : orderOf ((Fintype.card K : ℕ) : ZMod p) = 3 := by
    have hdvd : orderOf ((Fintype.card K : ℕ) : ZMod p) ∣ 3 := orderOf_dvd_of_pow_eq_one hq3
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hq1'
    · exact h
  have hval := CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.padicValNat_card_SL_of_orderOf_eq
    K hp (by norm_num) hord
  have hdvd3 : p ∣ Fintype.card K ^ 3 - 1 := by
    have h1 : (((Fintype.card K ^ 3 - 1 : ℕ)) : ZMod p) = 0 := by
      have hle : 1 ≤ Fintype.card K ^ 3 := Nat.one_le_pow _ _ (by omega)
      rw [Nat.cast_sub hle, Nat.cast_pow, hq3]
      simp
    exact (ZMod.natCast_eq_zero_iff _ _).1 h1
  have hpos : 0 < padicValNat p (Fintype.card K ^ 3 - 1) := by
    have hne : Fintype.card K ^ 3 - 1 ≠ 0 :=
      Nat.sub_ne_zero_of_lt (one_lt_pow₀ (by omega) (by omega))
    exact (one_le_padicValNat_of_dvd hne hdvd3)
  rw [← hval] at hpos
  have hne : Nat.card SL(3, K) ≠ 0 := Nat.card_pos.ne'
  exact dvd_of_one_le_padicValNat hpos

theorem dvd_card_SU3_of_dvd {p q : ℕ} (hpd : p ∣ q ^ 2 - q + 1) :
    p ∣ q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1) := by
  have h : q ^ 3 + 1 = (q ^ 2 - q + 1) * (q + 1) := by
    have : q ≤ q ^ 2 := by nlinarith
    zify [this]
    ring
  exact Dvd.dvd.mul_left (h ▸ Dvd.dvd.mul_right hpd _) _

theorem rootChar_eq_one_of_mem_parabolicRoots_of_forall {L : Type} [Field L] {τ : Tag}
    {J : Set (Fin τ.rank)} {b : Fin τ.rank → Lˣ} (hb : ∀ j ∈ J, b j = 1)
    {β : Fin τ.rank → ℤ} (hβ : β ∈ parabolicRoots τ J) : rootChar b β = 1 := by
  rw [rootChar]
  refine Finset.prod_eq_one fun j _ => ?_
  by_cases hj : j ∈ J
  · rw [hb j hj, one_zpow]
  · rw [hβ.2 j hj, zpow_zero]

section Actor


theorem torusRootChar_conj_eq_one_of_forall {Ω : Type} [Field Ω] (u : WeylGroup Tag.F4)
    (κ : F4A2Kind) {x d : ModGL Tag.F4 Ω}
    (hu : (fun α => u • α) '' {α | IsRoot Tag.F4 α ∧ torusRootChar x α = 1} =
      parabolicRoots Tag.F4 {κ.i, κ.j})
    (hdT : d ∈ torusGroup Tag.F4 Ω) (h1 : torusRootChar d (Pi.single κ.i 1) = 1)
    (h2 : torusRootChar d (Pi.single κ.j 1) = 1) :
    (canonicalRep (coxeterSystem Tag.F4) Ω u)⁻¹ * d *
        (canonicalRep (coxeterSystem Tag.F4) Ω u)⁻¹⁻¹ ∈ torusGroup Tag.F4 Ω ∧
      ∀ α ∈ {α | IsRoot Tag.F4 α ∧ torusRootChar x α = 1},
        torusRootChar ((canonicalRep (coxeterSystem Tag.F4) Ω u)⁻¹ * d *
          (canonicalRep (coxeterSystem Tag.F4) Ω u)⁻¹⁻¹) α = 1 := by
  obtain ⟨h, hh⟩ : ∃ h, h = canonicalRep (coxeterSystem Tag.F4) Ω u := ⟨_, rfl⟩
  rw [← hh]
  have hhN : h ∈ Subgroup.normalizer (torusGroup Tag.F4 Ω : Set (ModGL Tag.F4 Ω)) :=
    hh ▸ canonicalRep_mem_normalizer u
  have hzH : h⁻¹ * d * h⁻¹⁻¹ ∈ torusGroup Tag.F4 Ω :=
    (Subgroup.mem_normalizer_iff.1 (inv_mem hhN) d).1 hdT
  refine ⟨hzH, fun α hα => ?_⟩
  obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hdT
  have hbi : b κ.i = 1 := by
    rw [hb, torusRootChar_rootDiagUnit b (isRoot_single Tag.F4 κ.i), rootChar_pi_single] at h1
    exact Units.val_eq_one.1 h1
  have hbj : b κ.j = 1 := by
    rw [hb, torusRootChar_rootDiagUnit b (isRoot_single Tag.F4 κ.j), rootChar_pi_single] at h2
    exact Units.val_eq_one.1 h2
  obtain ⟨a', ha''⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hzH
  have hconj : rootDiagUnit Tag.F4 b = canonicalRep (coxeterSystem Tag.F4) Ω u *
      rootDiagUnit Tag.F4 a' * (canonicalRep (coxeterSystem Tag.F4) Ω u)⁻¹ := by
    rw [← hb, ← ha'', ← hh]
    group
  have hchar := (rootDiagUnit_eq_conj_canonicalRep_iff b a' u).1 hconj
  have huα : u • α ∈ parabolicRoots Tag.F4 ({κ.i, κ.j} : Set (Fin Tag.F4.rank)) := by
    rw [← hu]
    exact ⟨α, hα, rfl⟩
  rw [ha'', torusRootChar_rootDiagUnit a' hα.1, ← hchar,
    rootChar_eq_one_of_mem_parabolicRoots_of_forall (J := {κ.i, κ.j}) (b := b) (fun j hj => by
      rcases hj with rfl | hj
      · exact hbi
      · rw [Set.mem_singleton_iff.1 hj]; exact hbj) huα, Units.val_one]

variable (K : Type) [Field K] [Finite K] (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
  (F : Ω →+* Ω)

theorem f4ThreeSixActor_odd {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) (hF : ∀ c, F c = c ^ Nat.card K) {ε : ℤ} {w : WeylGroup Tag.F4}
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hεw : (ε = 1 ∧ w = f4Coxeter ^ 4 ∧ p ∣ Nat.card K ^ 2 + Nat.card K + 1) ∨
      (ε = -1 ∧ w = f4PhiSix ∧ p ∣ Nat.card K ^ 2 - Nat.card K + 1))
    {g : ModGL Tag.F4 Ω} (hg : g ∈ adjointGroup Tag.F4 Ω)
    (hgn : g⁻¹ * Units.map (entrywiseHom F) g = canonicalRep (coxeterSystem Tag.F4) Ω w)
    {x : ModGL Tag.F4 Ω} (hx : x ∈ torusGroup Tag.F4 Ω ⊓ conjEntrywiseImage K g⁻¹)
    (hxp : orderOf x = p) (hne : {α | IsRoot Tag.F4 α ∧ torusRootChar x α = 1}.Nonempty)
    {x₁ : adjointGroup Tag.F4 K}
    (hx₁ : baseChangeGL (algebraMap K Ω) (x₁ : ModGL Tag.F4 K) = g * x * g⁻¹) :
    F4FourActorAt K Ω p g x x₁ := by
  classical
  set n := canonicalRep (coxeterSystem Tag.F4) Ω w with hn
  set Γ := conjEntrywiseImage K g⁻¹ with hΓ
  set T₀ := torusGroup Tag.F4 Ω ⊓ Γ with hT₀
  obtain ⟨-, -, hcls⟩ := (F4_three_six_torus_data K Ω F hF hεw hp hp3).2 g hg hgn
  obtain ⟨u, κ, δ, hδ, hu, huw⟩ := ((hcls x hx hxp).1).resolve_left hne.ne_empty
  set h := canonicalRep (coxeterSystem Tag.F4) Ω u with hh
  set Γ₁ := Γ.map (MulAut.conj h).toMonoidHom with hΓ₁
  set D := Γ₁ ⊓ centralizer {h * x * h⁻¹} with hD
  set R := ⁅D, D⁆ with hR
  obtain ⟨-, ⟨a, ha, hRQ, hsplit, hsplit'⟩, hRq, -, -, -, -, -, ⟨-, -, hCDR⟩,
      ⟨x₀, hx₀, hD₀, hR₀', R₀, hR₀le, M, -, kM, -, hkeq⟩⟩ :=
    odd_F4_cyclotomic_three_six_nonregular_derived_centralizers hℓ hℓ2 hf K hK Ω F hF ε w
      (hεw.imp (fun h => ⟨h.1, h.2.1⟩) (fun h => ⟨h.1, h.2.1⟩)) hp hp3 n g rfl hg hgn Γ T₀ rfl rfl
      x hx hxp u κ δ hδ hu huw h (h * x * h⁻¹) rfl rfl Γ₁ D R rfl rfl rfl
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
  have hpRR : p ∣ Nat.card R := by
    rcases hεw with ⟨hε, -, hpd⟩ | ⟨hε, -, hpd⟩
    · let φ : SL(3, K) →* ModGL Tag.F4 Ω :=
        (MulAut.conj a).toMonoidHom.comp ((subsystemGroup Tag.F4 Ω {κ.i, κ.j}).subtype.comp
          ((f4A2Equiv Ω κ).symm.toMonoidHom.comp (Matrix.SpecialLinearGroup.map (algebraMap K Ω))))
      have hφinj : Function.Injective φ := by
        refine (MulAut.conj a).injective.comp (Subtype.val_injective.comp
          ((f4A2Equiv Ω κ).symm.injective.comp ?_))
        exact CFSG.RankThree.Classical2.specialLinearGroup_map_injective
          (algebraMap K Ω).injective
      have hRφ : R = φ.range := by
        ext z
        rw [hsplit hε z]
        constructor
        · rintro ⟨Y, rfl⟩
          exact ⟨Y, by simp [φ, MulAut.conj_apply]⟩
        · rintro ⟨Y, rfl⟩
          exact ⟨Y, by simp [φ, MulAut.conj_apply]⟩
      rw [hRφ, ← Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv]
      exact p_dvd_card_SL3 hp hp3 hpd
    · have : Fact ℓ.Prime := ⟨hℓ⟩
      have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
      have : CharP K ℓ := finite_field_prime_power_characteristic hℓ hf hK
      have : CharP Ω ℓ := charP_of_injective_algebraMap (algebraMap K Ω).injective ℓ
      have hS := CFSG.GH74.GLS.Stage2.Bender.Thm1.mnSyl_card_unitarySet_three (Ω := Ω) (ℓ := ℓ) hf
      rw [← hK] at hS
      let ψ : SL(3, Ω) →* ModGL Tag.F4 Ω :=
        (MulAut.conj a).toMonoidHom.comp ((subsystemGroup Tag.F4 Ω {κ.i, κ.j}).subtype.comp
          (f4A2Equiv Ω κ).symm.toMonoidHom)
      have hψinj : Function.Injective ψ :=
        (MulAut.conj a).injective.comp (Subtype.val_injective.comp (f4A2Equiv Ω κ).symm.injective)
      have e1 : Nat.card {X : SL(3, Ω) // Matrix.SpecialLinearGroup.toGL X ∈
          CFSG.RankThree.Classical2.unitarySet (Nat.card K) 3} = Nat.card R := by
        refine Nat.card_eq_of_bijective (fun X => ⟨ψ X.1, (hsplit' hε _).2 ⟨X.1, X.2, rfl⟩⟩)
          ⟨fun X Y hXY => Subtype.ext (hψinj (congrArg Subtype.val hXY)), fun z => ?_⟩
        obtain ⟨X, hX, hz⟩ := (hsplit' hε z.1).1 z.2
        exact ⟨⟨X, hX⟩, Subtype.ext hz.symm⟩
      have e2 : Nat.card {X : SL(3, Ω) // Matrix.SpecialLinearGroup.toGL X ∈
          CFSG.RankThree.Classical2.unitarySet (Nat.card K) 3} =
          Nat.card (CFSG.RankThree.Classical2.unitarySet (Nat.card K) 3 :
            Set (GL (Fin 3) Ω)) :=
        Nat.card_congr
          { toFun := fun X => ⟨Matrix.SpecialLinearGroup.toGL X.1, X.2⟩
            invFun := fun Y => ⟨⟨(Y.1 : Matrix (Fin 3) (Fin 3) Ω), Y.2.2.1⟩, by
              have h1 : Matrix.SpecialLinearGroup.toGL
                  (⟨(Y.1 : Matrix (Fin 3) (Fin 3) Ω), Y.2.2.1⟩ : SL(3, Ω)) = Y.1 :=
                Units.ext rfl
              rw [h1]
              exact Y.2⟩
            left_inv := fun X => rfl
            right_inv := fun Y => Subtype.ext (Units.ext rfl) }
      rw [← e1, e2, hS]
      exact dvd_card_SU3_of_dvd hpd
  have hpR : ¬ Nat.Coprime p (Nat.card (⁅centralizer ({x₀} : Set (adjointGroup Tag.F4 K)),
      centralizer ({x₀} : Set (adjointGroup Tag.F4 K))⁆ : Subgroup (adjointGroup Tag.F4 K))) := by
    have hcard : Nat.card (⁅centralizer ({x₀} : Set (adjointGroup Tag.F4 K)),
        centralizer ({x₀} : Set (adjointGroup Tag.F4 K))⁆ : Subgroup (adjointGroup Tag.F4 K)) =
        Nat.card R := Nat.card_congr eR.toEquiv
    rw [hcard]
    exact fun hc' => hp.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hc' dvd_rfl hpRR)
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
    (algebraMap K M) κ R₀ (kM : ModGL Tag.F4 M) 1 (by rw [hconj1]; exact hkeq)).1
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
  obtain ⟨⟨t₀, ht₀, ht₀d⟩, hχi, hχj⟩ := (hCDR d).1 hdDR
  have ht₀e : h⁻¹ * d * h⁻¹⁻¹ = t₀ := by
    rw [← ht₀d]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hdH : d ∈ torusGroup Tag.F4 Ω := by
    have hhN : h ∈ Subgroup.normalizer (torusGroup Tag.F4 Ω : Set (ModGL Tag.F4 Ω)) :=
      hh ▸ canonicalRep_mem_normalizer u
    rw [← ht₀d]
    simpa [MulAut.conj_apply] using (Subgroup.mem_normalizer_iff.1 hhN t₀).1 ht₀.1
  refine ⟨by rw [hkey, ht₀e]; exact ht₀.1, fun α hα => ?_⟩
  rw [hkey, ht₀e]
  obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hdH
  obtain ⟨a', ha'⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht₀.1
  have hbi : b κ.i = 1 := by
    rw [hb, torusRootChar_rootDiagUnit b (isRoot_single Tag.F4 κ.i), rootChar_pi_single] at hχi
    exact Units.val_eq_one.1 hχi
  have hbj : b κ.j = 1 := by
    rw [hb, torusRootChar_rootDiagUnit b (isRoot_single Tag.F4 κ.j), rootChar_pi_single] at hχj
    exact Units.val_eq_one.1 hχj
  have hconj : rootDiagUnit Tag.F4 b = canonicalRep (coxeterSystem Tag.F4) Ω u *
      rootDiagUnit Tag.F4 a' * (canonicalRep (coxeterSystem Tag.F4) Ω u)⁻¹ := by
    rw [← hb, ← ha', ← hh]
    rw [← ht₀d]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  have hchar := (rootDiagUnit_eq_conj_canonicalRep_iff b a' u).1 hconj
  have huα : u • α ∈ parabolicRoots Tag.F4 ({κ.i, κ.j} : Set (Fin Tag.F4.rank)) := by
    rw [← hu]
    exact ⟨α, hα, rfl⟩
  rw [ha', torusRootChar_rootDiagUnit a' hα.1, ← hchar,
    rootChar_eq_one_of_mem_parabolicRoots_of_forall (J := {κ.i, κ.j}) (b := b) (fun j hj => by
      rcases hj with rfl | hj
      · exact hbi
      · rw [Set.mem_singleton_iff.1 hj]; exact hbj) huα, Units.val_one]

theorem f4ThreeActor_odd {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) (hF : ∀ c, F c = c ^ Nat.card K) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hpd : p ∣ Nat.card K ^ 2 + Nat.card K + 1) {g : ModGL Tag.F4 Ω}
    (hg : g ∈ adjointGroup Tag.F4 Ω)
    (hgn : g⁻¹ * Units.map (entrywiseHom F) g =
      canonicalRep (coxeterSystem Tag.F4) Ω (f4Coxeter ^ 4))
    {x : ModGL Tag.F4 Ω} (hx : x ∈ torusGroup Tag.F4 Ω ⊓ conjEntrywiseImage K g⁻¹)
    (hxp : orderOf x = p) (hne : {α | IsRoot Tag.F4 α ∧ torusRootChar x α = 1}.Nonempty)
    {x₁ : adjointGroup Tag.F4 K}
    (hx₁ : baseChangeGL (algebraMap K Ω) (x₁ : ModGL Tag.F4 K) = g * x * g⁻¹) :
    F4FourActorAt K Ω p g x x₁ :=
  f4ThreeSixActor_odd K Ω F hℓ hℓ2 hf hK hF hp hp3 (Or.inl ⟨rfl, rfl, hpd⟩) hg hgn hx hxp hne hx₁

theorem f4SixActor_odd {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) (hF : ∀ c, F c = c ^ Nat.card K) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hpd : p ∣ Nat.card K ^ 2 - Nat.card K + 1) {g : ModGL Tag.F4 Ω}
    (hg : g ∈ adjointGroup Tag.F4 Ω)
    (hgn : g⁻¹ * Units.map (entrywiseHom F) g =
      canonicalRep (coxeterSystem Tag.F4) Ω f4PhiSix)
    {x : ModGL Tag.F4 Ω} (hx : x ∈ torusGroup Tag.F4 Ω ⊓ conjEntrywiseImage K g⁻¹)
    (hxp : orderOf x = p) (hne : {α | IsRoot Tag.F4 α ∧ torusRootChar x α = 1}.Nonempty)
    {x₁ : adjointGroup Tag.F4 K}
    (hx₁ : baseChangeGL (algebraMap K Ω) (x₁ : ModGL Tag.F4 K) = g * x * g⁻¹) :
    F4FourActorAt K Ω p g x x₁ :=
  f4ThreeSixActor_odd K Ω F hℓ hℓ2 hf hK hF hp hp3 (Or.inr ⟨rfl, rfl, hpd⟩) hg hgn hx hxp hne hx₁

end Actor

end CFSG.HardMathSupport.Timmesfeld.LocalTwo.SeitzRows
