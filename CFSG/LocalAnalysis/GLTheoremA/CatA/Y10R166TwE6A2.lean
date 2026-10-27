module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166TwE6A
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27TwistedE6Core
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeDiagTwisted

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Lang.E6Descent CFSG.RankThree.Classical2
  CFSG.HardMathSupport.Lang.E6Descent.TwistedDiag CFSG.HardMathSupport.Timmesfeld.CrossChar

section Certs

variable {ℓ f : ℕ} [Fact ℓ.Prime] {K : Type} [Field K] [Finite K]
  {σ : K →+* K} {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] [CharP Ω ℓ]
  {Fr : Ω →+* Ω}

theorem twE6EnnolaConj (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hK : Nat.card K = (ℓ ^ f) ^ 2)
    (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) :
    ∃ g ∈ adjointGroup Tag.E6 Ω, g⁻¹ * twistE6 Ω Fr g = n0 Ω := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have hmem : canonicalRep (coxeterSystem Tag.E6) Ω twE6W0 ∈ adjointGroup Tag.E6 Ω :=
    canonicalRep_mem_adjointGroup (coxeterSystem Tag.E6) Ω twE6W0
  exact exists_inv_mul_twistE6_eq hf hFr hmem

theorem thetaFixed_eq_map_Rgrp {g : ModGL Tag.E6 Ω} (hg : g ∈ adjointGroup Tag.E6 Ω)
    (hgn : g⁻¹ * twistE6 Ω Fr g = n0 Ω) :
    thetaFixed Fr = (Rgrp Ω Fr).map (MulAut.conj g⁻¹).toMonoidHom := by
  ext x
  rw [Subgroup.mem_map, mem_thetaFixed_iff_conj Fr hg hgn]
  constructor
  · intro hx
    exact ⟨g * x * g⁻¹, hx, by
      change g⁻¹ * (g * x * g⁻¹) * (g⁻¹)⁻¹ = x
      group⟩
  · rintro ⟨y, hy, hxy⟩
    rw [← hxy]
    have h : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
    rw [show (MulAut.conj g⁻¹).toMonoidHom y = g⁻¹ * y * g from rfl, h]
    exact hy

theorem rgrp_derived_eq_map_cgrp (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) {g : ModGL Tag.E6 Ω} (hg : g ∈ adjointGroup Tag.E6 Ω)
    (hgn : g⁻¹ * twistE6 Ω Fr g = n0 Ω) :
    ⁅thetaFixed Fr, thetaFixed Fr⁆ = (Cgrp K σ Ω).map (MulAut.conj g⁻¹).toMonoidHom := by
  have hder : ⁅Rgrp Ω Fr, Rgrp Ω Fr⁆ = Cgrp K σ Ω :=
    (twisted_E6_full_rational_fixed_group_order hℓ hf K hK σ hσ Ω Fr hFr).2.2.1
  rw [thetaFixed_eq_map_Rgrp hg hgn, ← Subgroup.map_commutator, hder]

theorem rgrp_derived_relIndex_eq_gcd (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) {g : ModGL Tag.E6 Ω} (hg : g ∈ adjointGroup Tag.E6 Ω)
    (hgn : g⁻¹ * twistE6 Ω Fr g = n0 Ω) :
    (⁅thetaFixed Fr, thetaFixed Fr⁆).relIndex (thetaFixed Fr) = Nat.gcd 3 (ℓ ^ f + 1) := by
  have hRcard : Nat.card (Rgrp Ω Fr) = SeitzReduction.E6Pilot.numTwistedE6 (ℓ ^ f) :=
    (twisted_E6_full_rational_fixed_group_order hℓ hf K hK σ hσ Ω Fr hFr).2.2.2.2.2.1
  have hCR : Cgrp K σ Ω ≤ Rgrp Ω Fr :=
    (exceptional_ambient_twisted_Frobenius_fixed_normalizer TwistTag.E6 hℓ hf K hK σ hσ Ω Fr hFr).2.1
  have hfinR : Finite (Rgrp Ω Fr) :=
    (twisted_E6_full_rational_fixed_group_order hℓ hf K hK σ hσ Ω Fr hFr).1
  haveI : Finite (Rgrp Ω Fr) := hfinR
  haveI : Finite (Cgrp K σ Ω) :=
    Finite.of_injective (Subgroup.inclusion hCR) (Subgroup.inclusion_injective hCR)
  have hCg : Nat.card (Cgrp K σ Ω) * Nat.gcd 3 (ℓ ^ f + 1) = Nat.card (Rgrp Ω Fr) := by
    rw [hRcard]
    change Nat.card ((graphFixedRootGroup TwistTag.E6 K σ).map
      (baseChangeGL (algebraMap K Ω))) * Nat.gcd 3 (ℓ ^ f + 1) =
        SeitzReduction.E6Pilot.numTwistedE6 (ℓ ^ f)
    rw [Subgroup.card_map_of_injective (baseChangeGL_injective _),
      CFSG.HardMathSupport.Lang.Coordinator.card_graphFixedRootGroup_E6_mul_gcd hℓ hf hK hσ]
  have hrel := Subgroup.relIndex_mul_card (Cgrp K σ Ω) (Rgrp Ω Fr)
  rw [inf_of_le_left hCR] at hrel
  have hidx : (Cgrp K σ Ω).relIndex (Rgrp Ω Fr) = Nat.gcd 3 (ℓ ^ f + 1) := by
    have h1 : (Cgrp K σ Ω).relIndex (Rgrp Ω Fr) * Nat.card (Cgrp K σ Ω) =
        Nat.gcd 3 (ℓ ^ f + 1) * Nat.card (Cgrp K σ Ω) := by
      rw [hrel, ← hCg, mul_comm]
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
  rw [rgrp_derived_eq_map_cgrp hℓ hf hK hσ hFr hg hgn, thetaFixed_eq_map_Rgrp hg hgn,
    Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective]
  exact hidx

theorem rgrp_pow_three_mem_derived (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) {g : ModGL Tag.E6 Ω} (hg : g ∈ adjointGroup Tag.E6 Ω)
    (hgn : g⁻¹ * twistE6 Ω Fr g = n0 Ω) {x : ModGL Tag.E6 Ω} (hx : x ∈ thetaFixed Fr) :
    x ^ 3 ∈ ⁅thetaFixed Fr, thetaFixed Fr⁆ := by
  have hidx : (⁅thetaFixed Fr, thetaFixed Fr⁆.subgroupOf (thetaFixed Fr)).index =
      Nat.gcd 3 (ℓ ^ f + 1) :=
    rgrp_derived_relIndex_eq_gcd hℓ hf hK hσ hFr hg hgn
  haveI hN : (⁅thetaFixed Fr, thetaFixed Fr⁆.subgroupOf (thetaFixed Fr)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hg : (g : ModGL Tag.E6 Ω) ∈ thetaFixed Fr := g.2
    have hginv : (g : ModGL Tag.E6 Ω)⁻¹ ∈ thetaFixed Fr := (thetaFixed Fr).inv_mem hg
    have hRmap : (thetaFixed Fr).map (MulAut.conj (g : ModGL Tag.E6 Ω)).toMonoidHom =
        thetaFixed Fr := by
      refine le_antisymm ?_ ?_
      · rintro _ ⟨y, hy, rfl⟩
        exact (thetaFixed Fr).mul_mem ((thetaFixed Fr).mul_mem hg hy) ((thetaFixed Fr).inv_mem hg)
      · intro x hx
        refine ⟨(g : ModGL Tag.E6 Ω)⁻¹ * x * (g : ModGL Tag.E6 Ω), ?_, ?_⟩
        · exact (thetaFixed Fr).mul_mem ((thetaFixed Fr).mul_mem hginv hx)
            ((thetaFixed Fr).inv_mem hginv)
        · show (g : ModGL Tag.E6 Ω) * ((g : ModGL Tag.E6 Ω)⁻¹ * x * (g : ModGL Tag.E6 Ω)) *
            (g : ModGL Tag.E6 Ω)⁻¹ = x
          group
    have hCmap : (⁅thetaFixed Fr, thetaFixed Fr⁆).map
        (MulAut.conj (g : ModGL Tag.E6 Ω)).toMonoidHom = ⁅thetaFixed Fr, thetaFixed Fr⁆ := by
      rw [Subgroup.map_commutator, hRmap]
    have hmap := Subgroup.mem_map_of_mem (MulAut.conj (g : ModGL Tag.E6 Ω)).toMonoidHom hn
    rw [hCmap] at hmap
    show (g : ModGL Tag.E6 Ω) * (n : ModGL Tag.E6 Ω) * (g : ModGL Tag.E6 Ω)⁻¹ ∈
      ⁅thetaFixed Fr, thetaFixed Fr⁆
    exact hmap
  have h := Subgroup.pow_index_mem (⁅thetaFixed Fr, thetaFixed Fr⁆.subgroupOf (thetaFixed Fr))
    (⟨x, hx⟩ : ↥(thetaFixed Fr))
  rw [hidx] at h
  have hx3 : x ^ Nat.gcd 3 (ℓ ^ f + 1) ∈ ⁅thetaFixed Fr, thetaFixed Fr⁆ := h
  obtain ⟨k, hk⟩ := Nat.gcd_dvd_left 3 (ℓ ^ f + 1)
  rw [hk, pow_mul]
  exact Subgroup.pow_mem _ hx3 k

theorem rootDiagUnit_mem_thetaFixed (hK : Nat.card K = (ℓ ^ f) ^ 2) {q : ℕ}
    (hFr : ∀ c, Fr c = c ^ q) {a : Fin Tag.E6.rank → Ωˣ} (ha : ∀ i, a i ^ (q + 1) = 1) :
    rootDiagUnit Tag.E6 a ∈ thetaFixed Fr := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  rw [mem_thetaFixed]
  exact ⟨rootDiagUnit_mem_adjointGroup_of_isAlgClosed a,
    (theta_rootDiagUnit_eq_iff Fr hFr a).2 ha⟩

theorem twE6_rootDiagUnit_mem_cgrp (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hqdvd : q ∣ ℓ ^ f + 1) (hq3 : q ≠ 3 ∨ 9 ∣ ℓ ^ f + 1)
    {a : Fin Tag.E6.rank → Ωˣ} (ha : ∀ i, a i ^ q = 1) :
    rootDiagUnit Tag.E6 a ∈ ⁅thetaFixed Fr, thetaFixed Fr⁆ := by
  classical
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  obtain ⟨g, hg, hgn⟩ := twE6EnnolaConj hℓ hf hK hFr
  have hQ : ∀ i, a i ^ (ℓ ^ f + 1) = 1 := by
    intro i
    obtain ⟨m, hm⟩ := hqdvd
    rw [hm, pow_mul, ha i, one_pow]
  have hR : rootDiagUnit Tag.E6 a ∈ thetaFixed Fr := rootDiagUnit_mem_thetaFixed hK hFr hQ
  have hd3 : (rootDiagUnit Tag.E6 a) ^ 3 ∈ ⁅thetaFixed Fr, thetaFixed Fr⁆ :=
    rgrp_pow_three_mem_derived hℓ hf hK hσ hFr hg hgn hR
  have hdq : (rootDiagUnit Tag.E6 a) ^ q = 1 := by
    have h : a ^ q = 1 := funext ha
    calc (rootDiagUnit Tag.E6 a) ^ q = rootDiagUnitHom Tag.E6 Ω (a ^ q) :=
          (map_pow (rootDiagUnitHom Tag.E6 Ω) a q).symm
      _ = 1 := by rw [h, map_one]
  by_cases hq3' : q = 3
  ·
    subst hq3'
    have h9 : 9 ∣ ℓ ^ f + 1 := by
      rcases hq3 with h | h
      · exact absurd rfl h
      · exact h
    have h3 : 3 ∣ ℓ ^ f + 1 := dvd_trans (by norm_num : 3 ∣ 9) h9
    have hℓ3 : ℓ ≠ 3 := by
      intro hℓ3'
      subst hℓ3'
      have hpow : (3 : ℕ) ∣ 3 ^ f := dvd_pow_self 3 (by omega)
      have h1 : (3 : ℕ) ∣ 1 := by
        have := Nat.dvd_sub h3 hpow
        simpa using this
      exact absurd (Nat.dvd_one.1 h1) (by norm_num)
    have h9ne : (9 : Ω) ≠ 0 := by
      have h3ne : (3 : Ω) ≠ 0 := by
        intro h0
        have hdvd : ℓ ∣ 3 := (CharP.cast_eq_zero_iff Ω ℓ 3).1 h0
        exact hℓ3 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).1 hdvd)
      have h9eq : (9 : Ω) = 3 * 3 := by norm_num
      rw [h9eq]
      exact mul_ne_zero h3ne h3ne
    haveI : NeZero (9 : Ω) := ⟨h9ne⟩
    haveI : HasEnoughRootsOfUnity Ω 9 := IsSepClosed.hasEnoughRootsOfUnity Ω 9
    obtain ⟨η, hη⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω 9
    have hη0 : η ≠ 0 := hη.ne_zero (by norm_num)
    have hω : IsPrimitiveRoot (η ^ 3) 3 := hη.pow_of_dvd (p := 3) (by norm_num) (by norm_num)
    have hex : ∀ i, ∃ kk : ℕ, kk < 3 ∧ η ^ (3 * kk) = (a i : Ω) := by
      intro i
      have h3i : (a i : Ω) ^ 3 = 1 := by
        rw [← Units.val_pow_eq_pow_val, ha i, Units.val_one]
      obtain ⟨kk, hk3, hk⟩ := hω.eq_pow_of_pow_eq_one h3i
      exact ⟨kk, hk3, by rw [← hk, pow_mul]⟩
    choose k hk using hex
    have hk3 : ∀ i, k i < 3 := fun i => (hk i).1
    have hkpow : ∀ i, η ^ (3 * k i) = (a i : Ω) := fun i => (hk i).2
    let b : Fin Tag.E6.rank → Ωˣ := fun i => Units.mk0 (η ^ k i) (pow_ne_zero _ hη0)
    have hbval : ∀ i, (b i : Ω) = η ^ k i := fun i => rfl
    have hb3 : b ^ 3 = a := by
      funext i
      refine Units.ext ?_
      show ((η ^ k i : Ω)) ^ 3 = (a i : Ω)
      rw [← pow_mul, mul_comm, hkpow i]
    have hb9 : ∀ i, (η ^ k i) ^ 9 = 1 := by
      intro i
      rw [← pow_mul, mul_comm, pow_mul, hη.pow_eq_one, one_pow]
    have hbQ : ∀ i, b i ^ (ℓ ^ f + 1) = 1 := by
      intro i
      obtain ⟨m, hm⟩ := h9
      refine Units.ext ?_
      show ((η ^ k i : Ω)) ^ (ℓ ^ f + 1) = 1
      rw [hm, pow_mul, hb9 i, one_pow]
    have hbR : rootDiagUnit Tag.E6 b ∈ thetaFixed Fr := rootDiagUnit_mem_thetaFixed hK hFr hbQ
    have hda : rootDiagUnit Tag.E6 a = (rootDiagUnit Tag.E6 b) ^ 3 := by
      have h : (rootDiagUnit Tag.E6 b) ^ 3 = rootDiagUnitHom Tag.E6 Ω (b ^ 3) :=
        (map_pow (rootDiagUnitHom Tag.E6 Ω) b 3).symm
      rw [h, hb3]
      rfl
    rw [hda]
    exact rgrp_pow_three_mem_derived hℓ hf hK hσ hFr hg hgn hbR
  ·
    have hcop : Nat.Coprime 3 q :=
      (Nat.coprime_primes Nat.prime_three hq).2 (Ne.symm hq3')
    have hbez : (3 : ℤ) * (Nat.gcdA 3 q) + (q : ℤ) * (Nat.gcdB 3 q) = 1 := by
      have h := Nat.gcd_eq_gcd_ab 3 q
      rw [show Nat.gcd 3 q = 1 from hcop] at h
      simpa using h.symm
    have hd : rootDiagUnit Tag.E6 a = ((rootDiagUnit Tag.E6 a) ^ 3) ^ (Nat.gcdA 3 q) := by
      have h1 : ((rootDiagUnit Tag.E6 a) ^ 3) ^ (Nat.gcdA 3 q) *
          ((rootDiagUnit Tag.E6 a) ^ q) ^ (Nat.gcdB 3 q) = rootDiagUnit Tag.E6 a := by
        have e : ((rootDiagUnit Tag.E6 a) ^ (3 : ℤ)) ^ (Nat.gcdA 3 q) *
            ((rootDiagUnit Tag.E6 a) ^ (q : ℤ)) ^ (Nat.gcdB 3 q) =
            rootDiagUnit Tag.E6 a := by
          rw [← zpow_mul, ← zpow_mul, ← zpow_add, hbez, zpow_one]
        simpa using e
      rw [hdq, one_zpow, mul_one] at h1
      exact h1.symm
    rw [hd]
    exact Subgroup.zpow_mem _ hd3 _

@[expose] noncomputable def twE6xStar (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hqdvd : q ∣ ℓ ^ f + 1) (hq3 : q ≠ 3 ∨ 9 ∣ ℓ ^ f + 1) {ζ : Ωˣ} (hζq : ζ ^ q = 1)
    (hζ1 : ζ ≠ 1) : ↥(⁅thetaFixed Fr, thetaFixed Fr⁆) :=
  ⟨rootDiagUnit Tag.E6 (twE6omega1Tuple ζ),
    twE6_rootDiagUnit_mem_cgrp hℓ hf hK hσ hFr hq hq2 hqdvd hq3 (fun i => by
      simp only [twE6omega1Tuple]
      split_ifs with hi
      · exact hζq
      · exact one_pow q)⟩

theorem twE6xStar_pow_eq_one (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hqdvd : q ∣ ℓ ^ f + 1) (hq3 : q ≠ 3 ∨ 9 ∣ ℓ ^ f + 1) {ζ : Ωˣ} (hζq : ζ ^ q = 1)
    (hζ1 : ζ ≠ 1) : twE6xStar hℓ hf hK hσ hFr hq hq2 hqdvd hq3 hζq hζ1 ^ q = 1 := by
  refine Subtype.ext ?_
  show (rootDiagUnit Tag.E6 (twE6omega1Tuple ζ)) ^ q = 1
  have haq : (twE6omega1Tuple ζ) ^ q = 1 := by
    funext i
    simp only [twE6omega1Tuple, Pi.pow_apply]
    split_ifs with hi
    · exact hζq
    · exact one_pow q
  calc (rootDiagUnit Tag.E6 (twE6omega1Tuple ζ)) ^ q =
        rootDiagUnitHom Tag.E6 Ω ((twE6omega1Tuple ζ) ^ q) :=
        (map_pow (rootDiagUnitHom Tag.E6 Ω) _ q).symm
    _ = 1 := by rw [haq, map_one]

theorem twE6xStar_ne_one (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hqdvd : q ∣ ℓ ^ f + 1) (hq3 : q ≠ 3 ∨ 9 ∣ ℓ ^ f + 1) {ζ : Ωˣ} (hζq : ζ ^ q = 1)
    (hζ1 : ζ ≠ 1) : twE6xStar hℓ hf hK hσ hFr hq hq2 hqdvd hq3 hζq hζ1 ≠ 1 := by
  intro h
  have h1 : rootDiagUnit Tag.E6 (twE6omega1Tuple ζ) = 1 := congrArg Subtype.val h
  have h2 : rootDiagUnit Tag.E6 (twE6omega1Tuple ζ) =
      rootDiagUnit Tag.E6 (1 : Fin Tag.E6.rank → Ωˣ) :=
    h1.trans (map_one (rootDiagUnitHom Tag.E6 Ω)).symm
  have h3' : twE6omega1Tuple ζ = 1 :=
    CFSG.LieType.Chevalley.rootDiagUnit_injective h2
  have h4 := congrFun h3' (0 : Fin Tag.E6.rank)
  simp only [twE6omega1Tuple, Pi.one_apply, if_pos rfl] at h4
  exact hζ1 h4

end Certs

end CFSG.LocalAnalysis.GLTheoremA.Y10F
