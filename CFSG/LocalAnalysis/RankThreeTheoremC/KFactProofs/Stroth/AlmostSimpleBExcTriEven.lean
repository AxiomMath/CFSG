module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBExcTriLevi
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBExcTriEvenNe
public import CFSG.RankThree.PartTwo.Sec21.Item219LieProofD4Cent
public import CFSG.RankThree.PartTwo.Sec21.Item219LieProofD4Arith

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open CFSG CFSG.Open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Chevalley.TrialitySplitInner CFSG.RankThree.PartOne.FOC
  CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec4.Res417Seven
  CFSG.RankThree.PartTwo.Sec21.Item219LieProof
open CFSG.RankThree.PartOne
open scoped commutatorElement Pointwise

section Abstract

theorem comm_of_centralizes_conj_of_sylow_comm {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) (x g₀ : G) (C : Subgroup G) (hC : ∀ c, c ∈ C ↔ c * x = x * c)
    (P : Sylow p C) (hPab : ∀ a ∈ (P : Subgroup C), ∀ b ∈ (P : Subgroup C), a * b = b * a)
    (P' : Subgroup G) (hP' : IsPGroup p P')
    (hP'x : ∀ q ∈ P', q * (g₀ * x * g₀⁻¹) = (g₀ * x * g₀⁻¹) * q) :
    ∀ q₁ ∈ P', ∀ q₂ ∈ P', q₁ * q₂ = q₂ * q₁ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set Q'' : Subgroup G := P'.map (MulAut.conj g₀⁻¹).toMonoidHom with hQ''
  have hQ''C : Q'' ≤ C := by
    rintro _ ⟨q, hq, rfl⟩
    rw [hC]
    have h := hP'x q hq
    show g₀⁻¹ * q * g₀⁻¹⁻¹ * x = x * (g₀⁻¹ * q * g₀⁻¹⁻¹)
    calc g₀⁻¹ * q * g₀⁻¹⁻¹ * x = g₀⁻¹ * (q * (g₀ * x * g₀⁻¹)) * g₀⁻¹⁻¹ := by group
      _ = g₀⁻¹ * ((g₀ * x * g₀⁻¹) * q) * g₀⁻¹⁻¹ := by rw [h]
      _ = x * (g₀⁻¹ * q * g₀⁻¹⁻¹) := by group
  have hQ''p : IsPGroup p Q'' := hP'.map _
  set Q' : Subgroup C := Q''.comap C.subtype with hQ'
  have hQ'p : IsPGroup p Q' := hQ''p.comap_subtype
  obtain ⟨S, hS⟩ := hQ'p.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq C P S
  have hQ'P : ∀ a ∈ Q', c⁻¹ * a * c ∈ (P : Subgroup C) := by
    intro a ha
    have haS : a ∈ (S : Subgroup C) := hS ha
    rw [← hc, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      ← map_inv, MulAut.smul_def, MulAut.conj_apply] at haS
    simpa using haS
  intro q₁ hq₁ q₂ hq₂
  have hmem : ∀ q ∈ P', g₀⁻¹ * q * g₀⁻¹⁻¹ ∈ C := fun q hq => hQ''C ⟨q, hq, rfl⟩
  set a₁ : C := ⟨g₀⁻¹ * q₁ * g₀⁻¹⁻¹, hmem q₁ hq₁⟩ with ha₁
  set a₂ : C := ⟨g₀⁻¹ * q₂ * g₀⁻¹⁻¹, hmem q₂ hq₂⟩ with ha₂
  have ha₁Q : a₁ ∈ Q' := ⟨q₁, hq₁, rfl⟩
  have ha₂Q : a₂ ∈ Q' := ⟨q₂, hq₂, rfl⟩
  have hcomm : (c⁻¹ * a₁ * c) * (c⁻¹ * a₂ * c) = (c⁻¹ * a₂ * c) * (c⁻¹ * a₁ * c) :=
    hPab _ (hQ'P a₁ ha₁Q) _ (hQ'P a₂ ha₂Q)
  have hcomm' : a₁ * a₂ = a₂ * a₁ := by
    have h1 : c⁻¹ * (a₁ * a₂) * c = c⁻¹ * (a₂ * a₁) * c := by
      calc c⁻¹ * (a₁ * a₂) * c = (c⁻¹ * a₁ * c) * (c⁻¹ * a₂ * c) := by group
        _ = (c⁻¹ * a₂ * c) * (c⁻¹ * a₁ * c) := hcomm
        _ = c⁻¹ * (a₂ * a₁) * c := by group
    exact mul_left_cancel (mul_right_cancel h1)
  have hG : g₀⁻¹ * q₁ * g₀⁻¹⁻¹ * (g₀⁻¹ * q₂ * g₀⁻¹⁻¹) =
      g₀⁻¹ * q₂ * g₀⁻¹⁻¹ * (g₀⁻¹ * q₁ * g₀⁻¹⁻¹) := congrArg Subtype.val hcomm'
  calc q₁ * q₂ = g₀ * ((g₀⁻¹ * q₁ * g₀⁻¹⁻¹) * (g₀⁻¹ * q₂ * g₀⁻¹⁻¹)) * g₀⁻¹ := by group
    _ = g₀ * ((g₀⁻¹ * q₂ * g₀⁻¹⁻¹) * (g₀⁻¹ * q₁ * g₀⁻¹⁻¹)) * g₀⁻¹ := by rw [hG]
    _ = q₂ * q₁ := by group

end Abstract

section Outer


theorem exists_noncomm_pGroup_centralizing_outer {K : Type} [Field K] [Finite K] {f : ℕ}
    (hf : 1 ≤ f) (hfeven : Even f) (hK : Nat.card K = (2 ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ 2 ^ f) {ζ : (trialityFixedField K σ.toRingHom)ˣ}
    (hζ : orderOf (trialityFixedUnit K σ ζ) = 3)
    (d : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) {u : ℕ}
    (hd : (d : ModGL TwistTag.D4.tag K) =
      trialityOuterTorus K σ (trialityFixedUnit K σ ζ ^ u)) (hd1 : d ≠ 1) :
    ∃ P' : Subgroup ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom), IsPGroup 3 P' ∧
      (∀ q ∈ P', q * d = d * q) ∧ ¬ (∀ q₁ ∈ P', ∀ q₂ ∈ P', q₁ * q₂ = q₂ * q₁) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  haveI : Finite ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := Subtype.finite
  have h3 : ∀ c : K, σ (σ (σ c)) = c := fun c => by
    have : Fintype K := Fintype.ofFinite K
    rw [hσ, hσ, hσ, ← pow_mul, ← pow_mul,
      show 2 ^ f * (2 ^ f * 2 ^ f) = (2 ^ f) ^ 3 by ring, ← hK, Nat.card_eq_fintype_card,
      FiniteField.pow_card]
  have hσ3 : σ ^ 3 = 1 := RingEquiv.ext fun c => h3 c
  have hq : 2 ^ f % 3 = 1 := two_pow_mod_three hfeven
  have hkcard : Nat.card (trialityFixedField K σ.toRingHom) = 2 ^ f :=
    card_trialityFixedField Nat.prime_two hf hK σ hσ
  obtain ⟨P', hcard, hcen⟩ := exists_sylow_center (K := K) (σ := σ) (n := f) (by omega) hfeven hK
    hσ hζ
  obtain ⟨z, hz⟩ : ∃ z : Kˣ, z = trialityFixedUnit K σ ζ := ⟨_, rfl⟩
  rw [← hz] at hζ hd
  rw [← hz] at hcen
  obtain ⟨y₀, hy₀⟩ : ∃ y₀ : ModGL TwistTag.D4.tag K, y₀ = trialityOuterTorus K σ z := ⟨_, rfl⟩
  rw [← hy₀] at hcen
  have hz3 : z ^ 3 = 1 := by rw [← hζ]; exact pow_orderOf_eq_one z
  have hTy₀ : ∀ n : ℕ, trialityOuterTorus K σ (z ^ n) = y₀ ^ n := fun n => by
    have h1 : trialityTorusHom σ (z ^ n, 1) = (trialityTorusHom σ (z, 1)) ^ n := by
      have hp : ((z, (1 : (trialityFixedField K σ.toRingHom)ˣ)) ^ n :
          Kˣ × (trialityFixedField K σ.toRingHom)ˣ) = (z ^ n, 1) := Prod.ext rfl (one_pow n)
      rw [← map_pow, hp]
    rw [trialityTorusHom_one_right, trialityTorusHom_one_right] at h1
    rw [hy₀]
    exact h1
  have hy₀3 : y₀ ^ 3 = 1 := by
    rw [← hTy₀, hz3, ← trialityTorusHom_one_right (σ := σ)]
    exact map_one _
  obtain ⟨-, ⟨eT, heT⟩, -, -, -⟩ := triality_all_characteristic_faithful_torus_coordinates K σ hσ3
  have hH1card : Nat.card (graphFixedRootTorus TwistTag.D4 K σ.toRingHom) =
      ((2 ^ f) ^ 3 - 1) * (2 ^ f - 1) := by
    rw [← Nat.card_congr eT.toEquiv, Nat.card_prod, Nat.card_units, Nat.card_units, hK, hkcard]
  have h9 : 3 ^ 2 ∣ Nat.card ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
    have h1 : 3 ∣ 2 ^ f - 1 := by omega
    have h2 : 3 ∣ (2 ^ f) ^ 3 - 1 := by
      have : (2 ^ f) ^ 3 % 3 = 1 := by rw [Nat.pow_mod, hq]
      omega
    have h12 : 3 ^ 2 ∣ ((2 ^ f) ^ 3 - 1) * (2 ^ f - 1) := by
      rw [pow_two]
      exact Nat.mul_dvd_mul h2 h1
    rw [← hH1card] at h12
    exact h12.trans (Subgroup.card_dvd_of_le (graphFixedRootTorus_le _ _ _))
  have hfac : 2 ≤ (Nat.card ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).factorization 3 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three Nat.card_pos.ne').1 h9
  have hP'9 : 9 ≤ Nat.card P' := by
    rw [hcard]
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ (Nat.card ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).factorization 3 :=
        Nat.pow_le_pow_right (by norm_num) hfac
  have hP'p : IsPGroup 3 P' := IsPGroup.of_card hcard
  have hnab : ¬ (∀ q₁ ∈ P', ∀ q₂ ∈ P', q₁ * q₂ = q₂ * q₁) := by
    intro habel
    have hle : P'.map (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype ≤
        Subgroup.zpowers y₀ := by
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨j, hj⟩ := hcen y hy (fun p hp => habel p hp y hy)
      show (y : ModGL TwistTag.D4.tag K) ∈ Subgroup.zpowers y₀
      rw [hj]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers y₀) j
    have h1 := Subgroup.card_le_of_le hle
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), Nat.card_zpowers] at h1
    have h2 : orderOf y₀ ≤ 3 := orderOf_le_of_pow_eq_one (by norm_num) hy₀3
    omega
  refine ⟨P', hP'p, ?_, hnab⟩
  haveI : Nontrivial P' := Finite.one_lt_card_iff_nontrivial.1 (by omega)
  haveI : Nontrivial (Subgroup.center P') := hP'p.center_nontrivial
  obtain ⟨⟨y, hyc⟩, hy1⟩ := exists_ne (1 : Subgroup.center P')
  have hycomm : ∀ q ∈ P', q * (y : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) =
      (y : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) * q := fun q hq => by
    have := Subgroup.mem_center_iff.1 hyc ⟨q, hq⟩
    exact congrArg Subtype.val this
  obtain ⟨j, hj⟩ := hcen y y.2 (fun p hp => hycomm p hp)
  have hj3 : ¬ 3 ∣ j := by
    rintro ⟨k, rfl⟩
    apply hy1
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    rw [hj, pow_mul, hy₀3, one_pow]
    rfl
  have hu3 : ¬ 3 ∣ u := by
    rintro ⟨k, rfl⟩
    apply hd1
    apply Subtype.ext
    rw [hd, hTy₀, pow_mul, hy₀3, one_pow]
    rfl
  have hd' : (d : ModGL TwistTag.D4.tag K) = ((y : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
      ModGL TwistTag.D4.tag K) ^ (j * u) := by
    rw [hd, hTy₀, hj, ← pow_mul]
    have hjj : (j * j * u) % 3 = u % 3 := by
      have : j % 3 = 1 ∨ j % 3 = 2 := by omega
      rcases this with h | h <;> simp [Nat.mul_mod, h]
    rw [show j * (j * u) = j * j * u by ring, pow_eq_pow_mod (j * j * u) hy₀3, hjj,
      ← pow_eq_pow_mod u hy₀3]
  intro q hq
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, hd']
  have hc : Commute (q : ModGL TwistTag.D4.tag K)
      (((y : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) : ModGL TwistTag.D4.tag K)) :=
    congrArg Subtype.val (hycomm q hq)
  exact (hc.pow_right (j * u)).eq

end Outer

section Main


theorem oddPCoreInClosure_triality_three_even_aux {K : Type} [Field K] [Finite K] [CharP K 2]
    {f : ℕ} (hf : 1 ≤ f) (hfeven : Even f) (hK : Nat.card K = (2 ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ 2 ^ f) {x : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)}
    (hx : orderOf x = 3) (C : Subgroup ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hC : ∀ c, c ∈ C ↔ c * x = x * c) : OddPCoreInClosure 3 ↥C := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  haveI : Finite ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := Subtype.finite
  haveI : Finite C := Subtype.finite
  have h3 : ∀ c : K, σ (σ (σ c)) = c := fun c => by
    have : Fintype K := Fintype.ofFinite K
    rw [hσ, hσ, hσ, ← pow_mul, ← pow_mul,
      show 2 ^ f * (2 ^ f * 2 ^ f) = (2 ^ f) ^ 3 by ring, ← hK, Nat.card_eq_fintype_card,
      FiniteField.pow_card]
  have hσ3 : σ ^ 3 = 1 := RingEquiv.ext fun c => h3 c
  have hq : 2 ^ f % 3 = 1 := two_pow_mod_three hfeven
  have hpq : 3 ∣ 2 ^ f - 1 := by omega
  obtain ⟨-, ⟨eT, heT⟩, -, -, hMa, -⟩ := triality_all_characteristic_faithful_torus_coordinates K σ
    hσ3
  have h3a : ∀ b : Fin TwistTag.D4.foldedTag.rank,
      3 ∣ Nat.card (orbitField TwistTag.D4 K σ.toRingHom b) - 1 := by
    intro b
    rw [card_orbitField_D4_orientation Nat.prime_two hf hK (r := 1) (Or.inl rfl)
      (σ := σ.toRingHom) (by simpa using hσ) b]
    have : ((2 ^ f) ^ (TwistTag.D4.orbit b).card) % 3 = 1 := by
      rw [Nat.pow_mod, hq]
      simp
    omega
  intro N hN hle hcop
  by_contra hodd
  have hxC : x ∈ C := (hC x).2 rfl
  obtain ⟨P, hxP⟩ : ∃ P : Sylow 3 C, (⟨x, hxC⟩ : C) ∈ (P : Subgroup C) := by
    have hpg : IsPGroup 3 (Subgroup.zpowers (⟨x, hxC⟩ : C)) := by
      refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, pow_one, ← Subgroup.orderOf_coe]
      exact hx
    obtain ⟨P, hP⟩ := hpg.exists_le_sylow
    exact ⟨P, hP (Subgroup.mem_zpowers _)⟩
  obtain ⟨R, hRne, hR2, hPR⟩ := exists_normalized_two_group Nat.prime_three C N hodd hcop P
  set φ : C →* ModGL TwistTag.D4.tag K :=
    (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype.comp C.subtype with hφdef
  have hφ : Function.Injective φ :=
    (Subgroup.subtype_injective _).comp (Subgroup.subtype_injective C)
  set A : Subgroup (ModGL TwistTag.D4.tag K) := (P : Subgroup C).map φ with hA
  set R' : Subgroup (ModGL TwistTag.D4.tag K) :=
    R.map (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype with hR'
  have hAX : A ≤ graphFixedRootGroup TwistTag.D4 K σ.toRingHom := by
    rintro _ ⟨c, -, rfl⟩
    exact c.1.2
  have hRX : R' ≤ graphFixedRootGroup TwistTag.D4 K σ.toRingHom := by
    rintro _ ⟨r, -, rfl⟩
    exact r.2
  have hR2' : IsPGroup 2 R' := hR2.map _
  have hR'ne : R' ≠ ⊥ := fun h0 =>
    hRne ((Subgroup.map_eq_bot_iff_of_injective R (Subgroup.subtype_injective _)).1 h0)
  have hAR : A ≤ Subgroup.normalizer (R' : Set (ModGL TwistTag.D4.tag K)) := by
    have : A = ((P : Subgroup C).map C.subtype).map
        (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype := by
      rw [hA, Subgroup.map_map]
    rw [this]
    exact (Subgroup.map_mono hPR).trans (Subgroup.le_normalizer_map _)
  have hAp : IsPGroup 3 A := P.isPGroup'.map φ
  obtain ⟨x₀, hx₀, J, hJ, hAJ⟩ := exists_conj_le_graphFixedParabolicLevi TwistTag.D4 (r := 2)
    (p := 3) (by norm_num) σ hσ3 hAX hAp hRX hR2' hR'ne hAR
  obtain ⟨ia, haJ⟩ := exists_subset_singleton_of_ne_univ hJ
  have hAL : A.map (MulAut.conj x₀).toMonoidHom ≤
      graphFixedParabolicLevi TwistTag.D4 K σ.toRingHom {ia} :=
    hAJ.trans (graphFixedParabolicLevi_mono _ haJ)
  have hAab : ∀ s ∈ A, ∀ t ∈ A, s * t = t * s := by
    intro s hs t ht
    have h1 := levi_threeGroup_comm σ hσ3 ia hAL (hAp.map _) _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩
    have h2 : (MulAut.conj x₀) (s * t) = (MulAut.conj x₀) (t * s) := by
      rw [map_mul, map_mul]
      exact h1
    exact (MulAut.conj x₀).injective h2
  have hPab : ∀ a ∈ (P : Subgroup C), ∀ b ∈ (P : Subgroup C), a * b = b * a := by
    intro a ha b hb
    apply hφ
    rw [map_mul, map_mul]
    exact hAab _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  have hxA : ((x : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
      ModGL TwistTag.D4.tag K) ∈ A := ⟨⟨x, hxC⟩, hxP, rfl⟩
  have hy3 : ((x : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
      ModGL TwistTag.D4.tag K) ^ 3 = 1 := by
    have h := pow_orderOf_eq_one x
    rw [hx] at h
    exact congrArg Subtype.val h
  obtain ⟨y', hy'⟩ : ∃ y' : ModGL TwistTag.D4.tag K,
      y' = x₀ * ((x : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
        ModGL TwistTag.D4.tag K) * x₀⁻¹ := ⟨_, rfl⟩
  have hy'L : y' ∈ graphFixedParabolicLevi TwistTag.D4 K σ.toRingHom {ia} := by
    rw [hy']
    exact hAL ⟨_, hxA, rfl⟩
  have hy'3 : y' ^ 3 = 1 := by
    have h := map_pow (MulAut.conj x₀) ((x : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
      ModGL TwistTag.D4.tag K) 3
    rw [hy3, map_one, MulAut.conj_apply] at h
    rw [hy']
    exact h.symm
  have hEL : Subgroup.zpowers y' ≤ graphFixedParabolicLevi TwistTag.D4 K σ.toRingHom {ia} :=
    (Subgroup.zpowers_le).2 hy'L
  have hE3 : ∀ z ∈ Subgroup.zpowers y', z ^ 3 = 1 := by
    rintro _ ⟨k, rfl⟩
    rw [← _root_.zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, _root_.zpow_natCast,
      hy'3, _root_.one_zpow]
  obtain ⟨y₁, hy₁M, hEtor⟩ := exists_conj_le_graphFixedRootTorus σ hσ3 ia (h3a ia) hEL hE3
  have hdT : y₁ * y' * y₁⁻¹ ∈ graphFixedRootTorus TwistTag.D4 K σ.toRingHom :=
    hEtor ⟨y', Subgroup.mem_zpowers y', rfl⟩
  have hd3 : (y₁ * y' * y₁⁻¹) ^ 3 = 1 := by
    have h := map_pow (MulAut.conj y₁) y' 3
    rw [hy'3, map_one, MulAut.conj_apply] at h
    exact h.symm
  have hy₁C : y₁ ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom := (hMa ia).1 hy₁M
  obtain ⟨g₀, hg₀⟩ : ∃ g₀ : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      (g₀ : ModGL TwistTag.D4.tag K) = y₁ * x₀ := ⟨⟨y₁ * x₀, mul_mem hy₁C hx₀⟩, rfl⟩
  have hd'coe : ((g₀ * x * g₀⁻¹ : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
      ModGL TwistTag.D4.tag K) = y₁ * y' * y₁⁻¹ := by
    rw [hy']
    show (g₀ : ModGL TwistTag.D4.tag K) * (x : ModGL TwistTag.D4.tag K) *
      (g₀ : ModGL TwistTag.D4.tag K)⁻¹ = _
    rw [hg₀]
    group
  obtain ⟨ζ, hζ, hζ'⟩ := exists_fixedUnit_orderOf_eq Nat.prime_two hf hK σ hσ Nat.prime_three hpq
  obtain ⟨u, v, huv⟩ := exists_torus_coords_of_pow_eq_one Nat.prime_three eT heT hζ hζ' hdT hd3
  have hmix := trialityOuter_mul_middle_pow_eq σ ζ u v
  obtain ⟨z, hz⟩ : ∃ z : Kˣ, z = trialityFixedUnit K σ ζ := ⟨_, rfl⟩
  have hζ'z : orderOf z = 3 := by rw [hz]; exact hζ'
  have hz3 : z ^ 3 = 1 := by rw [← hζ'z]; exact pow_orderOf_eq_one z
  have hpow : ∀ m : ℕ, (z ^ m) ^ 3 = 1 := fun m => by
    rw [← pow_mul, mul_comm, pow_mul, hz3, one_pow]
  rw [← hz] at hmix huv
  obtain ⟨A₀, hA₀⟩ : ∃ A₀ : Kˣ, A₀ = (z ^ u) ^ 2 * (z ^ v)⁻¹ := ⟨_, rfl⟩
  obtain ⟨B₀, hB₀⟩ : ∃ B₀ : Kˣ, B₀ = (z ^ u * z ^ u * z ^ u)⁻¹ * (z ^ v) ^ 2 := ⟨_, rfl⟩
  rw [← hA₀, ← hB₀] at hmix
  have hA3 : A₀ ^ 3 = 1 := by
    rw [hA₀, mul_pow, inv_pow, ← pow_mul, mul_comm 2 3, pow_mul, hpow, hpow]
    simp
  have hB3 : B₀ ^ 3 = 1 := by
    rw [hB₀, mul_pow, inv_pow, mul_pow, mul_pow, hpow, ← pow_mul, mul_comm 2 3, pow_mul, hpow]
    simp
  have hxa : ((g₀ * x * g₀⁻¹ : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
      ModGL TwistTag.D4.tag K) = rootDiagUnit TwistTag.D4.tag (d4Tuple A₀ A₀ B₀ A₀) := by
    rw [hd'coe, huv, hmix]
  by_cases hB1 : B₀ = 1
  ·
    exfalso
    have hzu : z ^ u * z ^ u * z ^ u = 1 := by
      calc z ^ u * z ^ u * z ^ u = (z ^ u) ^ 3 := by group
        _ = 1 := hpow u
    have hzv2 : (z ^ v) ^ 2 = 1 := by
      rw [hB₀, hzu, inv_one, one_mul] at hB1
      exact hB1
    have hzv : z ^ v = 1 := by
      calc z ^ v = (z ^ v) ^ 3 * ((z ^ v) ^ 2)⁻¹ := by group
        _ = 1 := by rw [hpow v, hzv2]; simp
    have h3v : 3 ∣ v := by
      have := orderOf_dvd_of_pow_eq_one hzv
      rwa [hζ'z] at this
    have hζv : ζ ^ v = 1 := orderOf_dvd_iff_pow_eq_one.1 (by rw [hζ]; exact h3v)
    have hm1 : trialityMiddleTorus K σ 1 = 1 := by
      rw [trialityMiddleTorus, map_one, torusElt_one]
    have hdOut : ((g₀ * x * g₀⁻¹ : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
        ModGL TwistTag.D4.tag K) =
        trialityOuterTorus K σ (trialityFixedUnit K σ ζ ^ u) := by
      rw [hd'coe, huv, hζv, hm1, mul_one, hz]
    have hd1 : g₀ * x * g₀⁻¹ ≠ 1 := by
      intro h
      have hx1 : x = 1 := by
        calc x = g₀⁻¹ * (g₀ * x * g₀⁻¹) * g₀ := by group
          _ = 1 := by rw [h]; group
      rw [hx1, orderOf_one] at hx
      omega
    obtain ⟨P', hP'p, hP'd, hnab⟩ := exists_noncomm_pGroup_centralizing_outer hf hfeven hK σ hσ hζ'
      (g₀ * x * g₀⁻¹) hdOut hd1
    exact hnab (comm_of_centralizes_conj_of_sylow_comm Nat.prime_three x g₀ C hC P hPab P' hP'p
      hP'd)
  ·
    exact hodd (oddPCoreInClosure_triality_three_ne hf hK σ hσ hq (x := x) g₀ hA3 hB3 hB1 hxa C hC
      N hN hle hcop)

end Main

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
