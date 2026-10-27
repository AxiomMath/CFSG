module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcTwE6ConcCent
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264Co13Gen
public import CFSG.LocalAnalysis.GLTheoremA.CatA.H81A3UniAut
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcTwE6ConcSU

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.BadExc.TwE6Conc

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.E6A5Cube CFSG.LieType.SeitzGeneration.ExcWideThree
  CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary CFSG.SeitzReduction
  CFSG.SeitzReduction.EPilot CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply)
open CFSG.RankThree.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open scoped commutatorElement

section SL2

@[expose] def compSL2 {F : Type*} [Field F] (t : F) : SL2 F :=
  ⟨!![0, -1; 1, t], by simp [det_fin_two]⟩

variable {K : Type} [Field K]

@[expose] noncomputable def eigSL2 (c : Kˣ) (hd : (c : K) - ((c⁻¹ : Kˣ) : K) ≠ 0) : SL2 K :=
  ⟨!![((c : K) - ((c⁻¹ : Kˣ) : K))⁻¹, 1; -(c : K) * ((c : K) - ((c⁻¹ : Kˣ) : K))⁻¹,
    -((c⁻¹ : Kˣ) : K)], by
    rw [det_fin_two_of]
    field_simp
    ring⟩

theorem compSL2_mul_eigSL2 (c : Kˣ) (hd : (c : K) - ((c⁻¹ : Kˣ) : K) ≠ 0) :
    compSL2 ((c : K) + ((c⁻¹ : Kˣ) : K)) * eigSL2 c hd = eigSL2 c hd * HSL c := by
  have hc : (c : K) * ((c⁻¹ : Kˣ) : K) = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hc' : ((c⁻¹ : Kˣ) : K) = (c : K)⁻¹ := Units.val_inv_eq_inv_val c
  have hc0 : (c : K) ≠ 0 := c.ne_zero
  have hd' : (c : K) - (c : K)⁻¹ ≠ 0 := by rwa [hc'] at hd
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  change !![0, -1; 1, (c : K) + ((c⁻¹ : Kˣ) : K)] *
      !![((c : K) - ((c⁻¹ : Kˣ) : K))⁻¹, 1; -(c : K) * ((c : K) - ((c⁻¹ : Kˣ) : K))⁻¹,
        -((c⁻¹ : Kˣ) : K)] =
    !![((c : K) - ((c⁻¹ : Kˣ) : K))⁻¹, 1; -(c : K) * ((c : K) - ((c⁻¹ : Kˣ) : K))⁻¹,
        -((c⁻¹ : Kˣ) : K)] * !![(c : K), 0; 0, ((c⁻¹ : Kˣ) : K)]
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two, hc']
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> field_simp <;> ring

theorem eigSL2_inv_mul_compSL2 (c : Kˣ) (hd : (c : K) - ((c⁻¹ : Kˣ) : K) ≠ 0) :
    (eigSL2 c hd)⁻¹ * compSL2 ((c : K) + ((c⁻¹ : Kˣ) : K)) * eigSL2 c hd = HSL c := by
  rw [mul_assoc, compSL2_mul_eigSL2, ← mul_assoc, inv_mul_cancel, one_mul]

theorem orderOf_compSL2 {p : ℕ} (hp : p.Prime) {c : Kˣ} (hc : orderOf c = p)
    (hd : (c : K) - ((c⁻¹ : Kˣ) : K) ≠ 0) :
    orderOf (compSL2 ((c : K) + ((c⁻¹ : Kˣ) : K))) = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have he := eigSL2_inv_mul_compSL2 c hd
  refine orderOf_eq_prime ?_ ?_
  · have h1 : ((eigSL2 c hd)⁻¹ * compSL2 ((c : K) + ((c⁻¹ : Kˣ) : K)) * eigSL2 c hd) ^ p = 1 := by
      rw [he, HSL_pow, ← hc, pow_orderOf_eq_one, HSL_one]
    rw [inv_mul_mul_pow_eq] at h1
    have h2 := congrArg (fun g => eigSL2 c hd * g * (eigSL2 c hd)⁻¹) h1
    simpa [mul_assoc] using h2
  · intro h1
    have h2 := congrArg (fun g : SL2 K => (g : Matrix (Fin 2) (Fin 2) K) 0 0) h1
    simp [compSL2] at h2

end SL2

section Data

variable {K : Type} [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
  (hK : Nat.card K = (ℓ ^ f) ^ 2) (hf : 1 ≤ f)
  {ζ : K} (hζ : ζ ≠ 0) (hσζ : unitaryInvolution K ℓ f ζ = -ζ)
  (P : GL (Fin 6) K) (hP : conjTr (unitaryInvolution K ℓ f) (P : Matrix (Fin 6) (Fin 6) K) *
    (P : Matrix (Fin 6) (Fin 6) K) = antidiag 6)

variable (K ℓ f) in
noncomputable abbrev leviJ : Subgroup (ModGL TwistTag.E6.tag K) := twE6LeviSA K (unitaryInvolution K ℓ f)

include hK hf in
theorem leviAnti_mem_twistedE6RootGroup (x : SU (unitaryInvolution K ℓ f) 6) :
    leviAnti hζ hσζ x ∈ twistedE6RootGroup K (unitaryInvolution K ℓ f) :=
  twE6LeviSA_le_twistedE6RootGroup hK hf (by rw [← range_leviAnti hζ hσζ hK]; exact ⟨x, rfl⟩)

@[expose] noncomputable def leviSU : Su K ℓ f 6 →* ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f)) :=
  ((leviAnti hζ hσζ).comp (conjEquiv P hP).symm.toMonoidHom).codRestrict _ fun y =>
    leviAnti_mem_twistedE6RootGroup hK hf hζ hσζ _

theorem coe_leviSU (y : Su K ℓ f 6) :
    (leviSU hK hf hζ hσζ P hP y : ModGL TwistTag.E6.tag K) =
      leviAnti hζ hσζ ((conjEquiv P hP).symm y) := rfl

theorem range_leviSU :
    (leviSU hK hf hζ hσζ P hP).range =
      (leviJ K ℓ f).subgroupOf (twistedE6RootGroup K (unitaryInvolution K ℓ f)) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    show (leviSU hK hf hζ hσζ P hP y : ModGL TwistTag.E6.tag K) ∈ leviJ K ℓ f
    rw [coe_leviSU]
    have h := range_leviAnti hζ hσζ hK
    have hmem : leviAnti hζ hσζ ((conjEquiv P hP).symm y) ∈ (leviAnti hζ hσζ).range := ⟨_, rfl⟩
    rw [h] at hmem
    exact hmem
  · intro hx
    have hx' : (x : ModGL TwistTag.E6.tag K) ∈ (leviAnti hζ hσζ).range := by
      rw [range_leviAnti hζ hσζ hK]
      exact hx
    obtain ⟨z, hz⟩ := hx'
    refine ⟨conjEquiv P hP z, Subtype.ext ?_⟩
    rw [coe_leviSU, MulEquiv.symm_apply_apply, hz]

theorem exists_smul_of_leviSU_eq_one {y : Su K ℓ f 6} (hy : leviSU hK hf hζ hσζ P hP y = 1) :
    ∃ l : K, ((y : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = l • (1 : Matrix (Fin 6) (Fin 6) K) := by
  have h1 : leviAnti hζ hσζ ((conjEquiv P hP).symm y) = 1 := by
    have := congrArg Subtype.val hy
    rwa [coe_leviSU] at this
  obtain ⟨l, hl⟩ := exists_smul_of_leviAnti_eq_one hζ hσζ h1
  refine ⟨l, ?_⟩
  have e := coe_conjEquiv P hP ((conjEquiv P hP).symm y)
  rw [MulEquiv.apply_symm_apply] at e
  have e' := congrArg (fun g : GL (Fin 6) K => (g : Matrix (Fin 6) (Fin 6) K)) e
  simp only [Units.val_mul] at e'
  rw [e', hl, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, ← Units.val_mul, mul_inv_cancel,
    Units.val_one]

theorem leviSU_mem_leviJ (y : Su K ℓ f 6) :
    (leviSU hK hf hζ hσζ P hP y : ModGL TwistTag.E6.tag K) ∈ leviJ K ℓ f := by
  have h := range_leviSU hK hf hζ hσζ P hP
  have hy : leviSU hK hf hζ hσζ P hP y ∈ (leviSU hK hf hζ hσζ P hP).range := ⟨y, rfl⟩
  rw [h] at hy
  exact hy

theorem exists_leviSU_eq {x : ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f))}
    (hx : (x : ModGL TwistTag.E6.tag K) ∈ leviJ K ℓ f) : ∃ y, leviSU hK hf hζ hσζ P hP y = x := by
  have h := range_leviSU hK hf hζ hσζ P hP
  have hx' : x ∈ (leviSU hK hf hζ hσζ P hP).range := by rw [h]; exact hx
  exact hx'

theorem eq_one_of_leviSU_eq_one {p : ℕ} (hcop : Nat.Coprime p (Nat.gcd 6 (ℓ ^ f + 1)))
    {y : Su K ℓ f 6} (hyp : y ^ p = 1) (hy : leviSU hK hf hζ hσζ P hP y = 1) : y = 1 := by
  obtain ⟨l, hl⟩ := exists_smul_of_leviSU_eq_one hK hf hζ hσζ P hP hy
  exact eq_one_of_smul_one hcop hyp hl

theorem commute_of_leviSU_commute {p : ℕ} (hcop : Nat.Coprime p (Nat.gcd 6 (ℓ ^ f + 1)))
    {y h : Su K ℓ f 6} (hhp : h ^ p = 1)
    (hc : leviSU hK hf hζ hσζ P hP y * leviSU hK hf hζ hσζ P hP h =
      leviSU hK hf hζ hσζ P hP h * leviSU hK hf hζ hσζ P hP y) : y * h = h * y := by
  have h1 : leviSU hK hf hζ hσζ P hP (y * h * y⁻¹ * h⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hc]
    group
  obtain ⟨l, hl⟩ := exists_smul_of_leviSU_eq_one hK hf hζ hσζ P hP h1
  have hl' : (((y * h * y⁻¹ : Su K ℓ f 6) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      l • (((h : Su K ℓ f 6) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) := by
    have e : y * h * y⁻¹ = (y * h * y⁻¹ * h⁻¹) * h := by group
    rw [e, Subgroup.coe_mul, Units.val_mul, hl, Matrix.smul_mul, Matrix.one_mul]
  have hl1 := eq_one_of_conj_eq_smul (by norm_num) hcop hhp hl'
  rw [hl1, one_smul] at hl'
  have e : y * h * y⁻¹ = h := Subtype.ext (Units.ext hl')
  calc y * h = y * h * y⁻¹ * y := by group
    _ = h * y := by rw [e]

include hK hζ hσζ in
theorem mul_self_eq_one_of_mem_center_leviJ {z : ↥(leviJ K ℓ f)}
    (hz : z ∈ Subgroup.center ↥(leviJ K ℓ f)) : z * z = 1 :=
  (isQuasisimple_twE6LeviSA hζ hσζ hK).2 z hz

end Data

section Main

variable {K : Type} [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ]

@[expose] def splitHom (G : Type*) [Group G] (m : ℕ) : (Fin (m + 1) → G) →* G × (Fin m → G) :=
  (Pi.evalMonoidHom (fun _ => G) 0).prod (Pi.monoidHom fun i : Fin m => Pi.evalMonoidHom _ i.succ)

@[expose] def consHom (G : Type*) [CommGroup G] (m : ℕ) : G × (Fin m → G) →* (Fin (m + 1) → G) where
  toFun sy := Fin.cons sy.1 sy.2
  map_one' := by
    funext j
    refine Fin.cases ?_ (fun i => ?_) j <;> simp
  map_mul' a b := by
    funext j
    refine Fin.cases ?_ (fun i => ?_) j <;> simp

theorem splitHom_consHom (G : Type*) [CommGroup G] (m : ℕ) (sy : G × (Fin m → G)) :
    splitHom G m (consHom G m sy) = sy := by
  refine Prod.ext rfl (funext fun i => ?_)
  show (Fin.cons sy.1 sy.2 : Fin (m + 1) → G) i.succ = sy.2 i
  rw [Fin.cons_succ]

theorem map_compSL2_fixQ (c : Kˣ)
    (hct : unitaryInvolution K ℓ f ((c : K) + ((c⁻¹ : Kˣ) : K)) = (c : K) + ((c⁻¹ : Kˣ) : K)) :
    Matrix.SpecialLinearGroup.map (fixQ K ℓ f).subtype
        (compSL2 (⟨(c : K) + ((c⁻¹ : Kˣ) : K), hct⟩ : fixQ K ℓ f)) =
      compSL2 ((c : K) + ((c⁻¹ : Kˣ) : K)) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [compSL2]

theorem map_neg_one_fixQ :
    Matrix.SpecialLinearGroup.map (fixQ K ℓ f).subtype (-1) = (-1 : SL2 K) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

@[expose] noncomputable def twE6R0 (c : Kˣ)
    (hct : unitaryInvolution K ℓ f ((c : K) + ((c⁻¹ : Kˣ) : K)) = (c : K) + ((c⁻¹ : Kˣ) : K)) :
    ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f)) :=
  ⟨rootSL2 TwistTag.E6.tag K e6HighestRoot (compSL2 ((c : K) + ((c⁻¹ : Kˣ) : K))),
    map_compSL2_fixQ c hct ▸ rootSL2_highRoot_mem _⟩

theorem coe_twE6R0 (c : Kˣ)
    (hct : unitaryInvolution K ℓ f ((c : K) + ((c⁻¹ : Kˣ) : K)) = (c : K) + ((c⁻¹ : Kˣ) : K)) :
    (twE6R0 c hct : ModGL TwistTag.E6.tag K) =
      rootSL2 TwistTag.E6.tag K e6HighestRoot (compSL2 ((c : K) + ((c⁻¹ : Kˣ) : K))) := rfl

omit [Finite K] [Fact ℓ.Prime] [CharP K ℓ] in
theorem sub_inv_ne_zero_of_orderOf {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {c : Kˣ}
    (hc : orderOf c = p) : (c : K) - ((c⁻¹ : Kˣ) : K) ≠ 0 := by
  have hc2 : c ^ 2 ≠ 1 := fun h => by
    have h1 := orderOf_dvd_of_pow_eq_one h
    rw [hc] at h1
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h1)
  have hcc : (c : K) * ((c⁻¹ : Kˣ) : K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  intro h
  apply hc2
  have h1 : ((c⁻¹ : Kˣ) : K) = c := (sub_eq_zero.1 h).symm
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, sq, Units.val_one]
  calc (c : K) * c = (c : K) * ((c⁻¹ : Kˣ) : K) := by rw [h1]
    _ = 1 := hcc

theorem orderOf_twE6R0 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {c : Kˣ} (hc : orderOf c = p)
    (hct : unitaryInvolution K ℓ f ((c : K) + ((c⁻¹ : Kˣ) : K)) = (c : K) + ((c⁻¹ : Kˣ) : K)) :
    orderOf (twE6R0 c hct) = p := by
  rw [twE6R0, Subgroup.orderOf_mk, orderOf_injective _ (rootSL2_injective_of_field _),
    orderOf_compSL2 hp hc (sub_inv_ne_zero_of_orderOf hp hp2 hc)]

variable (K ℓ f) in
@[expose] noncomputable def twE6T : ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f)) :=
  ⟨rootSL2 TwistTag.E6.tag K e6HighestRoot (-1),
    map_neg_one_fixQ (K := K) (ℓ := ℓ) (f := f) ▸
      rootSL2_highRoot_mem (K := K) (ℓ := ℓ) (f := f) (-1)⟩

variable (K ℓ f) in
theorem coe_twE6T :
    ((twE6T K ℓ f : ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f))) :
      ModGL TwistTag.E6.tag K) = rootSL2 TwistTag.E6.tag K e6HighestRoot (-1) := rfl

theorem rootSL2_commute_of_mem_leviJ (B : SL2 K) {x : ModGL TwistTag.E6.tag K}
    (hx : x ∈ leviJ K ℓ f) :
    rootSL2 TwistTag.E6.tag K e6HighestRoot B * x = x * rootSL2 TwistTag.E6.tag K e6HighestRoot B :=
  rootSL2_highRoot_commute_of_mem_groupA B hx.1

theorem twE6R0_pow_commute (c : Kˣ)
    (hct : unitaryInvolution K ℓ f ((c : K) + ((c⁻¹ : Kˣ) : K)) = (c : K) + ((c⁻¹ : Kˣ) : K))
    (n : ℕ) {x : ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f))}
    (hx : (x : ModGL TwistTag.E6.tag K) ∈ leviJ K ℓ f) :
    twE6R0 c hct ^ n * x = x * twE6R0 c hct ^ n := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, SubgroupClass.coe_pow, coe_twE6R0]
  rw [← map_pow]
  exact rootSL2_commute_of_mem_leviJ _ hx

theorem twE6T_commute {x : ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f))}
    (hx : (x : ModGL TwistTag.E6.tag K) ∈ leviJ K ℓ f) : twE6T K ℓ f * x = x * twE6T K ℓ f :=
  Subtype.ext (rootSL2_commute_of_mem_leviJ _ hx)

theorem twE6R0_mul_twE6T (c : Kˣ)
    (hct : unitaryInvolution K ℓ f ((c : K) + ((c⁻¹ : Kˣ) : K)) = (c : K) + ((c⁻¹ : Kˣ) : K)) :
    twE6R0 c hct * twE6T K ℓ f = twE6T K ℓ f * twE6R0 c hct := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_twE6R0, coe_twE6T, ← map_mul, ← map_mul,
    mul_neg_one, neg_one_mul]

theorem twE6T_ne_one (hℓ2 : ℓ ≠ 2) : twE6T K ℓ f ≠ 1 := by
  have hK2 : (2 : K) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff K ℓ] at h'
    exact hℓ2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 h')
  intro h1
  have h2 : rootSL2 TwistTag.E6.tag K e6HighestRoot (-1) = 1 := by
    have h := Subtype.ext_iff.1 h1
    exact h
  have h3 : (-1 : SL2 K) = 1 := rootSL2_injective_of_field _ (h2.trans (map_one _).symm)
  have h4 := congrArg (fun g : SL2 K => (g : Matrix (Fin 2) (Fin 2) K) 0 0) h3
  simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one,
    Matrix.neg_apply, Matrix.one_apply_eq] at h4
  exact hK2 (by linear_combination -h4)

variable (K ℓ f) in
theorem twE6T_sq : twE6T K ℓ f ^ 2 = 1 := by
  apply Subtype.ext
  show rootSL2 TwistTag.E6.tag K e6HighestRoot (-1) ^ 2 = 1
  rw [← map_pow, neg_one_sq, map_one]

variable (hK : Nat.card K = (ℓ ^ f) ^ 2) (hf : 1 ≤ f)
  {ζ : K} (hζ : ζ ≠ 0) (hσζ : unitaryInvolution K ℓ f ζ = -ζ)
  (P : GL (Fin 6) K) (hP : conjTr (unitaryInvolution K ℓ f) (P : Matrix (Fin 6) (Fin 6) K) *
    (P : Matrix (Fin 6) (Fin 6) K) = antidiag 6)

theorem leviSU_eq_one_of_commute {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {y : Su K ℓ f 6}
    (hyp : y ^ p = 1)
    (hyc : ∀ x : ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f)),
      (x : ModGL TwistTag.E6.tag K) ∈ leviJ K ℓ f →
        leviSU hK hf hζ hσζ P hP y * x = x * leviSU hK hf hζ hσζ P hP y) :
    leviSU hK hf hζ hσζ P hP y = 1 := by
  set w : ↥(leviJ K ℓ f) := ⟨leviSU hK hf hζ hσζ P hP y, leviSU_mem_leviJ hK hf hζ hσζ P hP y⟩
    with hw
  have hwc : w ∈ Subgroup.center ↥(leviJ K ℓ f) := by
    rw [Subgroup.mem_center_iff]
    intro j
    apply Subtype.ext
    have hjC : (j : ModGL TwistTag.E6.tag K) ∈ twistedE6RootGroup K (unitaryInvolution K ℓ f) :=
      twE6LeviSA_le_twistedE6RootGroup hK hf j.2
    have h1 := hyc ⟨j, hjC⟩ j.2
    have h2 := congrArg Subtype.val h1
    exact h2.symm
  have hw2 : w * w = 1 := mul_self_eq_one_of_mem_center_leviJ hK hζ hσζ hwc
  have hwp : w ^ p = 1 := by
    apply Subtype.ext
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one, hw]
    show ((leviSU hK hf hζ hσζ P hP y : ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f))) :
      ModGL TwistTag.E6.tag K) ^ p = 1
    rw [← SubgroupClass.coe_pow, ← map_pow, hyp, map_one, OneMemClass.coe_one]
  have hw1 : w = 1 := by
    have h2 : w ^ 2 = 1 := by rw [sq]; exact hw2
    have hg : w ^ Nat.gcd p 2 = 1 := pow_gcd_eq_one.mpr ⟨hwp, h2⟩
    rwa [(Nat.coprime_primes hp Nat.prime_two).2 hp2, pow_one] at hg
  apply Subtype.ext
  have := congrArg Subtype.val hw1
  exact this

@[expose] noncomputable def twE6Phi {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {c : Kˣ}
    (hc : orderOf c = p)
    (hct : unitaryInvolution K ℓ f ((c : K) + ((c⁻¹ : Kˣ) : K)) = (c : K) + ((c⁻¹ : Kˣ) : K))
    {m : ℕ} (φ : (Fin m → Multiplicative (ZMod p)) →* Su K ℓ f 6) :
    (Fin (m + 1) → Multiplicative (ZMod p)) →* ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f)) :=
  (MonoidHom.noncommCoprod (powHom (twE6R0 c hct) (orderOf_twE6R0 Fact.out hp2 hc hct))
    ((leviSU hK hf hζ hσζ P hP).comp φ) fun _ _ =>
      twE6R0_pow_commute c hct _ (leviSU_mem_leviJ hK hf hζ hσζ P hP _)).comp
    (splitHom (Multiplicative (ZMod p)) m)

theorem twE6Phi_apply {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {c : Kˣ} (hc : orderOf c = p)
    (hct : unitaryInvolution K ℓ f ((c : K) + ((c⁻¹ : Kˣ) : K)) = (c : K) + ((c⁻¹ : Kˣ) : K))
    {m : ℕ} (φ : (Fin m → Multiplicative (ZMod p)) →* Su K ℓ f 6)
    (x : Fin (m + 1) → Multiplicative (ZMod p)) :
    twE6Phi hK hf hζ hσζ P hP hp2 hc hct φ x =
      twE6R0 c hct ^ (Multiplicative.toAdd (x 0)).val *
        leviSU hK hf hζ hσζ P hP (φ (fun i : Fin m => x i.succ)) := rfl

theorem pow_eq_one_of_fin {p m : ℕ} (x : Fin m → Multiplicative (ZMod p)) : x ^ p = 1 := by
  funext j
  rw [Pi.pow_apply, Pi.one_apply]
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one, nsmul_eq_mul, ZMod.natCast_self, zero_mul]

theorem leviSU_comp_injective {p : ℕ} (hcop : Nat.Coprime p (Nat.gcd 6 (ℓ ^ f + 1))) {m : ℕ}
    {φ : (Fin m → Multiplicative (ZMod p)) →* Su K ℓ f 6} (hφ : Function.Injective φ) :
    Function.Injective ((leviSU hK hf hζ hσζ P hP).comp φ) := by
  rw [injective_iff_map_eq_one]
  intro y hy
  have hyp : φ y ^ p = 1 := by rw [← map_pow, pow_eq_one_of_fin, map_one]
  exact hφ ((eq_one_of_leviSU_eq_one hK hf hζ hσζ P hP hcop hyp hy).trans (map_one φ).symm)

theorem twE6Phi_injective_of_inj {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {c : Kˣ}
    (hc : orderOf c = p)
    (hct : unitaryInvolution K ℓ f ((c : K) + ((c⁻¹ : Kˣ) : K)) = (c : K) + ((c⁻¹ : Kˣ) : K))
    {m : ℕ} {φ : (Fin m → Multiplicative (ZMod p)) →* Su K ℓ f 6}
    (hιφ : Function.Injective ((leviSU hK hf hζ hσζ P hP).comp φ)) :
    Function.Injective (twE6Phi hK hf hζ hσζ P hP hp2 hc hct φ) := by
  have hp : p.Prime := Fact.out
  rw [injective_iff_map_eq_one]
  intro x hx
  rw [twE6Phi_apply] at hx
  have hφp : ∀ y, φ y ^ p = 1 := fun y => by rw [← map_pow, pow_eq_one_of_fin, map_one]
  have e : leviSU hK hf hζ hσζ P hP (φ (fun i : Fin m => x i.succ)) =
      (twE6R0 c hct ^ (Multiplicative.toAdd (x 0)).val)⁻¹ := eq_inv_of_mul_eq_one_right hx
  have hιy : leviSU hK hf hζ hσζ P hP (φ (fun i : Fin m => x i.succ)) = 1 := by
    refine leviSU_eq_one_of_commute hK hf hζ hσζ P hP hp hp2 (hφp _) fun z hz => ?_
    rw [e]
    exact (show Commute (twE6R0 c hct ^ (Multiplicative.toAdd (x 0)).val) z from
      twE6R0_pow_commute c hct _ hz).inv_left.eq
  rw [hιy, mul_one] at hx
  have hx0 : x 0 = 1 := powHom_injective (orderOf_twE6R0 hp hp2 hc hct)
    (show powHom (twE6R0 c hct) (orderOf_twE6R0 hp hp2 hc hct) (x 0) = powHom _ _ 1 by
      rw [map_one]; exact hx)
  have hy1 : (fun i : Fin m => x i.succ) = 1 :=
    hιφ ((show ((leviSU hK hf hζ hσζ P hP).comp φ) (fun i : Fin m => x i.succ) = 1 from
      hιy).trans (map_one _).symm)
  funext j
  refine Fin.cases ?_ (fun i => ?_) j
  · exact hx0
  · exact congrFun hy1 i

theorem modelAGen_twistedE6_spec_of_inj (hℓ2 : ℓ ≠ 2) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {c : Kˣ} (hc : orderOf c = p)
    (hct : unitaryInvolution K ℓ f ((c : K) + ((c⁻¹ : Kˣ) : K)) = (c : K) + ((c⁻¹ : Kˣ) : K))
    {m : ℕ} (hm : 0 < m) {φ : (Fin m → Multiplicative (ZMod p)) →* Su K ℓ f 6}
    (hιφ : Function.Injective ((leviSU hK hf hζ hσζ P hP).comp φ)) :
    IsElemAbelian p (twE6Phi hK hf hζ hσζ P hP hp2 hc hct φ).range ∧
      Nat.card (twE6Phi hK hf hζ hσζ P hP hp2 hc hct φ).range = p ^ (m + 1) ∧
      Subgroup.zpowers (twE6R0 c hct) ≤ (twE6Phi hK hf hζ hσζ P hP hp2 hc hct φ).range ∧
      Nat.card (Subgroup.zpowers (twE6R0 c hct)) = p ∧
      GLAPComponent p (Subgroup.centralizer
          ((Subgroup.zpowers (twE6R0 c hct) : Subgroup _) :
            Set ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f))))
        ((leviJ K ℓ f).subgroupOf (twistedE6RootGroup K (unitaryInvolution K ℓ f))) ∧
      (twE6Phi hK hf hζ hσζ P hP hp2 hc hct φ).range ≤
        Subgroup.normalizer (((leviJ K ℓ f).subgroupOf
          (twistedE6RootGroup K (unitaryInvolution K ℓ f)) : Subgroup _) :
            Set ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f))) ∧
      (∀ x ∈ (twE6Phi hK hf hζ hσζ P hP hp2 hc hct φ).range,
        CentMod p ((leviJ K ℓ f).subgroupOf (twistedE6RootGroup K (unitaryInvolution K ℓ f))) x →
          x ∈ Subgroup.zpowers (twE6R0 c hct)) ∧
      twE6T K ℓ f ≠ 1 ∧ twE6T K ℓ f ^ 2 = 1 ∧
      (leviJ K ℓ f).subgroupOf (twistedE6RootGroup K (unitaryInvolution K ℓ f)) ≤
        Subgroup.centralizer ({twE6T K ℓ f} : Set ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f))) ∧
      (twE6Phi hK hf hζ hσζ P hP hp2 hc hct φ).range ≤
        Subgroup.centralizer ({twE6T K ℓ f} : Set ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f))) := by
  classical
  have hp : p.Prime := Fact.out
  set C₀ := twistedE6RootGroup K (unitaryInvolution K ℓ f) with hC₀
  set ι := leviSU hK hf hζ hσζ P hP with hιdef
  set r₀ := twE6R0 c hct with hr₀def
  set Φ := twE6Phi hK hf hζ hσζ P hP hp2 hc hct φ with hΦdef
  have hr₀o : orderOf r₀ = p := orderOf_twE6R0 hp hp2 hc hct
  have hd := sub_inv_ne_zero_of_orderOf hp hp2 hc
  have hc2 : c ^ 2 ≠ 1 := fun h => by
    have h1 := orderOf_dvd_of_pow_eq_one h
    rw [hc] at h1
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h1)
  have hc1 : c ≠ 1 := fun h => hc2 (by rw [h, one_pow])
  have hPA := eigSL2_inv_mul_compSL2 c hd
  have hιJ : ∀ y, (ι y : ModGL TwistTag.E6.tag K) ∈ leviJ K ℓ f :=
    leviSU_mem_leviJ hK hf hζ hσζ P hP
  have hφp : ∀ x, φ x ^ p = 1 := fun x => by rw [← map_pow, pow_eq_one_of_fin, map_one]
  have hΦinj := twE6Phi_injective_of_inj hK hf hζ hσζ P hP hp2 hc hct hιφ
  obtain ⟨hAe, hAc⟩ := isElemAbelian_range_of_injective hΦinj
  set e₀ : Fin (m + 1) → Multiplicative (ZMod p) := Pi.mulSingle 0 (Multiplicative.ofAdd 1)
    with he₀
  have hΦe₀ : Φ e₀ = r₀ := by
    rw [hΦdef, twE6Phi_apply]
    have h1 : (fun i : Fin m => e₀ i.succ) = 1 := funext fun i => by
      rw [he₀, Pi.mulSingle_eq_of_ne (Fin.succ_ne_zero i)]
      rfl
    rw [h1, map_one, map_one, mul_one, he₀, Pi.mulSingle_eq_same, toAdd_ofAdd, ZMod.val_one,
      pow_one]
  have hr₀A : r₀ ∈ Φ.range := ⟨e₀, hΦe₀⟩
  have hA₁A : Subgroup.zpowers r₀ ≤ Φ.range := (Subgroup.zpowers_le).2 hr₀A
  have hA₁c : Nat.card (Subgroup.zpowers r₀) = p := by rw [Nat.card_zpowers, hr₀o]
  have hJC₀ : leviJ K ℓ f ≤ C₀ := twE6LeviSA_le_twistedE6RootGroup hK hf
  have hJq : CFSG.Open.IsQuasisimple ↥(leviJ K ℓ f) := (isQuasisimple_twE6LeviSA hζ hσζ hK).1
  set x₁ : Fin m → Multiplicative (ZMod p) := Pi.mulSingle ⟨0, hm⟩ (Multiplicative.ofAdd 1)
    with hx₁def
  have hx₁1 : x₁ ≠ 1 := fun h => one_ne_zero (Multiplicative.ofAdd.injective
    ((congrFun h ⟨0, hm⟩).symm.trans (Pi.mulSingle_eq_same _ _)).symm)
  have hιh₁1 : ι (φ x₁) ≠ 1 := fun h => hx₁1 (hιφ
    ((show ((leviSU hK hf hζ hσζ P hP).comp φ) x₁ = 1 from h).trans (map_one _).symm))
  have hιh₁o : orderOf (⟨ι (φ x₁), hιJ _⟩ : ↥(leviJ K ℓ f)) = p := by
    refine orderOf_eq_prime ?_ fun h => hιh₁1 (Subtype.ext (by
      have h' := congrArg Subtype.val h
      exact h'))
    apply Subtype.ext
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
    show ((ι (φ x₁) : ↥C₀) : ModGL TwistTag.E6.tag K) ^ p = 1
    rw [← SubgroupClass.coe_pow, ← map_pow, hφp, map_one, OneMemClass.coe_one]
  have hpJ : p ∣ Nat.card ↥(leviJ K ℓ f) := hιh₁o ▸ orderOf_dvd_natCard _
  have hgA : ∀ g : ↥C₀, g * r₀ = r₀ * g →
      ∀ l ∈ leviJ K ℓ f, (g : ModGL TwistTag.E6.tag K) * l * (g : ModGL TwistTag.E6.tag K)⁻¹ ∈
        leviJ K ℓ f := by
    intro g hg l hl
    have hgΓ : (g : ModGL TwistTag.E6.tag K) ∈
        twistedFixedGroup TwistTag.E6 K (unitaryInvolution K ℓ f).toRingHom :=
      graphFixedRootGroup_le _ _ _ g.2
    have hgr : (g : ModGL TwistTag.E6.tag K) *
        rootSL2 TwistTag.E6.tag K e6HighestRoot (compSL2 ((c : K) + ((c⁻¹ : Kˣ) : K))) =
        rootSL2 TwistTag.E6.tag K e6HighestRoot (compSL2 ((c : K) + ((c⁻¹ : Kˣ) : K))) * g := by
      have h := congrArg Subtype.val hg
      rw [Subgroup.coe_mul, Subgroup.coe_mul] at h
      exact h
    have key : ∀ x : ModGL Tag.E6 K, x ∈ adjointGroup Tag.E6 K →
        x * rootSL2 Tag.E6 K (highRoot Tag.E6) (compSL2 ((c : K) + ((c⁻¹ : Kˣ) : K))) =
          rootSL2 Tag.E6 K (highRoot Tag.E6) (compSL2 ((c : K) + ((c⁻¹ : Kˣ) : K))) * x →
        x ∈ Subgroup.normalizer (groupA K : Set (ModGL Tag.E6 K)) := fun x hx h =>
      mem_normalizer_groupA_of_commute hc1 hc2 hPA hx h
    have hgN := key (g : ModGL TwistTag.E6.tag K) hgΓ.1 hgr
    have hlΓ : l ∈ twistedFixedGroup TwistTag.E6 K (unitaryInvolution K ℓ f).toRingHom := hl.2
    have hΓ' : (g : ModGL TwistTag.E6.tag K) * l * (g : ModGL TwistTag.E6.tag K)⁻¹ ∈
        twistedFixedGroup TwistTag.E6 K (unitaryInvolution K ℓ f).toRingHom :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hgΓ hlΓ) (Subgroup.inv_mem _ hgΓ)
    exact ⟨(Subgroup.mem_normalizer_iff.1 hgN l).1 hl.1, hΓ'⟩
  have hJcomp : GLAPComponent p (Subgroup.centralizer ((Subgroup.zpowers r₀ : Subgroup ↥C₀) :
      Set ↥C₀)) ((leviJ K ℓ f).subgroupOf C₀) := by
    refine CFSG.LocalAnalysis.GLTheoremA.KD264Gen.Co15.glaPComponent_subgroupOf C₀ hp _ hJC₀
      ?_ ?_ hJq hpJ
    · rintro l hl s hs
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hs
      have h := (show Commute r₀ ⟨l, hJC₀ hl⟩ from by
        have := twE6R0_pow_commute c hct 1 (x := ⟨l, hJC₀ hl⟩) hl
        rwa [pow_one] at this).zpow_left k
      exact (congrArg Subtype.val h.eq).symm
    · intro g hg hgc l hl
      exact hgA ⟨g, hg⟩ (Subtype.ext (hgc r₀ (Subgroup.mem_zpowers r₀))) l hl
  have hJqX : CFSG.Open.IsQuasisimple ↥((leviJ K ℓ f).subgroupOf C₀) :=
    CFSG.LocalAnalysis.GLTheoremA.KD264Gen.Co15.isQuasisimple_of_equiv
      (Subgroup.subgroupOfEquivOfLe hJC₀).symm hJq
  have hpJX : p ∣ Nat.card ↥((leviJ K ℓ f).subgroupOf C₀) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJC₀).toEquiv]
    exact hpJ
  have hAcomm : ∀ a ∈ Φ.range, a * r₀ = r₀ * a := fun a ha =>
    hAe.1.is_comm.comm ⟨a, ha⟩ ⟨r₀, hr₀A⟩ |> congrArg Subtype.val
  have hAN : Φ.range ≤
      Subgroup.normalizer (((leviJ K ℓ f).subgroupOf C₀ : Subgroup ↥C₀) : Set ↥C₀) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      exact hgA a (hAcomm a ha) _ hh
    · intro hh
      have ha' : a⁻¹ * r₀ = r₀ * a⁻¹ := (show Commute a r₀ from hAcomm a ha).inv_left.eq
      have h1 := hgA a⁻¹ ha' _ hh
      have e : ((a⁻¹ : ↥C₀) : ModGL TwistTag.E6.tag K) * C₀.subtype (a * h * a⁻¹) *
          ((a⁻¹ : ↥C₀) : ModGL TwistTag.E6.tag K)⁻¹ = C₀.subtype h := by
        simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [e] at h1
      exact h1
  refine ⟨hAe, hAc, hA₁A, hA₁c, hJcomp, hAN, ?_, twE6T_ne_one hℓ2, twE6T_sq K ℓ f, ?_, ?_⟩
  ·
    rintro _ ⟨x, rfl⟩ hx
    obtain ⟨-, hcm⟩ := hx
    have hfix := CFSG.LocalAnalysis.GLTheoremA.H81.UniA3.eq_of_mul_inv_mem_glaPPrimeCoreOf hp
      hJqX hpJX (MulAut.conj (Φ x)).toMonoidHom fun j hj => by
        have h1 := hcm (Subgroup.commutator_mem_commutator hj (Subgroup.mem_zpowers (Φ x)))
        have h2 := (GLAPPrimeCoreOf p ((leviJ K ℓ f).subgroupOf C₀)).inv_mem h1
        rw [commutatorElement_inv, commutatorElement_def] at h2
        exact h2
    set n := (Multiplicative.toAdd (x 0)).val with hn
    set w := ι (φ (fun i : Fin m => x i.succ)) with hw
    have hιy : w = 1 := by
      refine leviSU_eq_one_of_commute hK hf hζ hσζ P hP hp hp2 (hφp _) fun z hz => ?_
      have h1 := hfix z hz
      simp only [MonoidHom.coe_coe, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h1
      rw [hΦdef, twE6Phi_apply] at h1
      have h2 := twE6R0_pow_commute c hct n hz
      have h3 : w * z * w⁻¹ = z := by
        calc w * z * w⁻¹ = (r₀ ^ n)⁻¹ * (r₀ ^ n * w * z * (r₀ ^ n * w)⁻¹) * r₀ ^ n := by group
          _ = (r₀ ^ n)⁻¹ * z * r₀ ^ n := by rw [h1]
          _ = z := by rw [mul_assoc, ← h2, ← mul_assoc, inv_mul_cancel, one_mul]
      calc w * z = w * z * w⁻¹ * w := by group
        _ = z * w := by rw [h3]
    rw [hΦdef, twE6Phi_apply, ← hw, hιy, mul_one]
    exact Subgroup.npow_mem_zpowers _ _
  ·
    intro j hj
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (twE6T_commute hj).symm
  ·
    rintro _ ⟨x, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, hΦdef, twE6Phi_apply]
    have h1 : r₀ ^ (Multiplicative.toAdd (x 0)).val * twE6T K ℓ f =
        twE6T K ℓ f * r₀ ^ (Multiplicative.toAdd (x 0)).val :=
      ((show Commute r₀ (twE6T K ℓ f) from twE6R0_mul_twE6T c hct).pow_left _).eq
    have h2 := twE6T_commute (K := K) (ℓ := ℓ) (f := f) (hιJ (φ (fun i : Fin m => x i.succ)))
    calc r₀ ^ (Multiplicative.toAdd (x 0)).val * ι (φ (fun i : Fin m => x i.succ)) * twE6T K ℓ f
        = r₀ ^ (Multiplicative.toAdd (x 0)).val *
            (twE6T K ℓ f * ι (φ (fun i : Fin m => x i.succ))) := by
          rw [mul_assoc, h2]
      _ = twE6T K ℓ f *
            (r₀ ^ (Multiplicative.toAdd (x 0)).val * ι (φ (fun i : Fin m => x i.succ))) := by
          rw [← mul_assoc, h1, mul_assoc]

theorem glaPLayer_inf_centralizer_A12_ne_bot (hℓ2 : ℓ ≠ 2) (hq5 : 5 ≤ ℓ ^ f) {p : ℕ} [Fact p.Prime]
    (hp : p.Prime)
    (hp2 : p ≠ 2) (hpK : (p : K) ≠ 0) (hpSU : p ∣ Nat.card (Su K ℓ f 2)) {c : Kˣ}
    (hc : orderOf c = p)
    (hct : unitaryInvolution K ℓ f ((c : K) + ((c⁻¹ : Kˣ) : K)) = (c : K) + ((c⁻¹ : Kˣ) : K))
    {m : ℕ} {φ : (Fin m → Multiplicative (ZMod p)) →* Su K ℓ f 6}
    (hιφ : Function.Injective ((leviSU hK hf hζ hσζ P hP).comp φ))
    {x₁ : Fin m → Multiplicative (ZMod p)} (hx₁ : φ x₁ ∈ coordBlockSU K ℓ f blk01)
    (hx₁1 : x₁ ≠ 1)
    (hcomm₁ : ∀ y : Su K ℓ f 6,
      leviSU hK hf hζ hσζ P hP y * leviSU hK hf hζ hσζ P hP (φ x₁) =
        leviSU hK hf hζ hσζ P hP (φ x₁) * leviSU hK hf hζ hσζ P hP y → y * φ x₁ = φ x₁ * y) :
    (Subgroup.zpowers (twE6R0 c hct) ⊔ Subgroup.zpowers (leviSU hK hf hζ hσζ P hP (φ x₁))) ≤
        (twE6Phi hK hf hζ hσζ P hP hp2 hc hct φ).range ∧
      Nat.card ↥(Subgroup.zpowers (twE6R0 c hct) ⊔
        Subgroup.zpowers (leviSU hK hf hζ hσζ P hP (φ x₁))) = p ^ 2 ∧
      GLAPLayer p ((leviJ K ℓ f).subgroupOf (twistedE6RootGroup K (unitaryInvolution K ℓ f)) ⊓
        Subgroup.centralizer ((Subgroup.zpowers (twE6R0 c hct) ⊔
          Subgroup.zpowers (leviSU hK hf hζ hσζ P hP (φ x₁)) :
            Subgroup ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f))) :
              Set ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f)))) ≠ ⊥ := by
  classical
  set C₀ := twistedE6RootGroup K (unitaryInvolution K ℓ f) with hC₀
  set ι := leviSU hK hf hζ hσζ P hP with hιdef
  set r₀ := twE6R0 c hct with hr₀def
  set Φ := twE6Phi hK hf hζ hσζ P hP hp2 hc hct φ with hΦdef
  have hr₀o : orderOf r₀ = p := orderOf_twE6R0 hp hp2 hc hct
  have hιJ : ∀ y, (ι y : ModGL TwistTag.E6.tag K) ∈ leviJ K ℓ f :=
    leviSU_mem_leviJ hK hf hζ hσζ P hP
  have hφp : ∀ x, φ x ^ p = 1 := fun x => by rw [← map_pow, pow_eq_one_of_fin, map_one]
  have hx₁o : orderOf x₁ = p := orderOf_eq_prime (pow_eq_one_of_fin x₁) hx₁1
  have hh₁1 : φ x₁ ≠ 1 := fun h => hx₁1 (hιφ
    ((show (ι.comp φ) x₁ = 1 by rw [MonoidHom.comp_apply, h, map_one]).trans (map_one _).symm))
  have hΦinj := twE6Phi_injective_of_inj hK hf hζ hσζ P hP hp2 hc hct hιφ
  set ψ : Multiplicative (ZMod p) × Multiplicative (ZMod p) →*
      (Fin (m + 1) → Multiplicative (ZMod p)) :=
    (consHom (Multiplicative (ZMod p)) m).comp ((MonoidHom.id _).prodMap (powHom x₁ hx₁o)) with hψ
  have hcons : Function.Injective (consHom (Multiplicative (ZMod p)) m) :=
    Function.LeftInverse.injective (splitHom_consHom _ m)
  have hpm : Function.Injective
      ((MonoidHom.id (Multiplicative (ZMod p))).prodMap (powHom x₁ hx₁o)) := by
    rw [MonoidHom.coe_prodMap]
    exact Function.injective_id.prodMap (powHom_injective hx₁o)
  have hψinj : Function.Injective ψ := by
    rw [hψ, MonoidHom.coe_comp]
    exact hcons.comp hpm
  have hΦψ : ∀ su, Φ (ψ su) =
      r₀ ^ (Multiplicative.toAdd su.1).val * ι (φ (powHom x₁ hx₁o su.2)) := by
    intro su
    rw [hΦdef, twE6Phi_apply]
    have h1 : ψ su 0 = su.1 := by
      show (Fin.cons su.1 (powHom x₁ hx₁o su.2) : Fin (m + 1) → _) 0 = su.1
      rfl
    have h2 : (fun i : Fin m => ψ su i.succ) = powHom x₁ hx₁o su.2 := funext fun i => by
      show (Fin.cons su.1 (powHom x₁ hx₁o su.2) : Fin (m + 1) → _) i.succ = _
      rw [Fin.cons_succ]
    rw [h1, h2]
  have hΦ1 : Φ (ψ (1, Multiplicative.ofAdd 1)) = ι (φ x₁) := by
    rw [hΦψ]
    simp only [toAdd_one, ZMod.val_zero, pow_zero, one_mul]
    rw [powHom_apply, toAdd_ofAdd, ZMod.val_one, pow_one]
  have hA₁₂c : Nat.card (Φ.comp ψ).range = p ^ 2 := by
    rw [card_range_of_injective' (by rw [MonoidHom.coe_comp]; exact hΦinj.comp hψinj),
      Nat.card_prod, card_multiplicative_zmod, sq]
  have hr₀A₁₂ : r₀ ∈ (Φ.comp ψ).range := ⟨(Multiplicative.ofAdd 1, 1), by
    rw [MonoidHom.comp_apply, hΦψ, map_one (powHom x₁ hx₁o), map_one φ, map_one ι, mul_one,
      toAdd_ofAdd, ZMod.val_one, pow_one]⟩
  have hA₁A₁₂ : Subgroup.zpowers r₀ ≤ (Φ.comp ψ).range := (Subgroup.zpowers_le).2 hr₀A₁₂
  have hA₁₂A : (Φ.comp ψ).range ≤ Φ.range := by
    rintro _ ⟨su, rfl⟩
    exact ⟨ψ su, rfl⟩
  have hA₁₂eq : (Φ.comp ψ).range = Subgroup.zpowers r₀ ⊔ Subgroup.zpowers (ι (φ x₁)) := by
    apply le_antisymm
    · rintro _ ⟨su, rfl⟩
      rw [MonoidHom.comp_apply, hΦψ, powHom_apply, map_pow, map_pow]
      exact mul_mem (Subgroup.mem_sup_left (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _))
        (Subgroup.mem_sup_right (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _))
    · exact sup_le hA₁A₁₂ ((Subgroup.zpowers_le).2 ⟨(1, Multiplicative.ofAdd 1), hΦ1⟩)
  rw [← hA₁₂eq]
  refine ⟨hA₁₂A, hA₁₂c, ?_⟩
  set N0 := coordBlockSU K ℓ f blk01ᶜ with hN0
  set N := N0.map ι with hN
  have hN0inj : Function.Injective (ι.comp N0.subtype) := by
    rw [injective_iff_map_eq_one]
    intro y hy
    obtain ⟨l, hl⟩ := exists_smul_of_leviSU_eq_one hK hf hζ hσζ P hP hy
    simp only [Subgroup.coe_subtype] at hl
    have h00 := (mem_coordBlockSU_iff.1 y.2) 0 0 (Or.inl (by decide))
    rw [hl] at h00
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one, if_pos] at h00
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    rw [hl, h00, one_smul]
    rfl
  have hrange : (ι.comp N0.subtype).range = N := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have heN : ↥N0 ≃* ↥N :=
    (MonoidHom.ofInjective hN0inj).trans (MulEquiv.subgroupCongr hrange)
  have hNq : CFSG.Open.IsQuasisimple ↥N :=
    CFSG.LocalAnalysis.GLTheoremA.KD264Gen.Co15.isQuasisimple_of_equiv heN
      (isQuasisimple_coordBlockSU hK hq5 (by decide))
  have hpN : p ∣ Nat.card ↥N := by
    rw [← Nat.card_congr heN.toEquiv]
    exact dvd_card_coordBlockSU_compl hpSU
  have hNJ : N ≤ (leviJ K ℓ f).subgroupOf C₀ := by
    rintro _ ⟨y, -, rfl⟩
    exact hιJ y
  have hNC : N ≤ Subgroup.centralizer ((Φ.comp ψ).range : Set ↥C₀) := by
    rintro _ ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨su, rfl⟩
    rw [MonoidHom.comp_apply, hΦψ]
    have hy1 : y * φ x₁ = φ x₁ * y :=
      Subgroup.mem_centralizer_singleton_iff.1 (coordBlockSU_compl_le_centralizer hx₁ hy)
    have hyu : Commute y (φ (powHom x₁ hx₁o su.2)) := by
      rw [powHom_apply, map_pow]
      exact (show Commute y (φ x₁) from hy1).pow_right _
    have h1 : ι (φ (powHom x₁ hx₁o su.2)) * ι y = ι y * ι (φ (powHom x₁ hx₁o su.2)) := by
      rw [← map_mul, ← map_mul, hyu.eq]
    have h2 := twE6R0_pow_commute c hct (Multiplicative.toAdd su.1).val (hιJ y)
    calc r₀ ^ (Multiplicative.toAdd su.1).val * ι (φ (powHom x₁ hx₁o su.2)) * ι y
        = r₀ ^ (Multiplicative.toAdd su.1).val * ι y * ι (φ (powHom x₁ hx₁o su.2)) := by
          rw [mul_assoc, h1, ← mul_assoc]
      _ = ι y * (r₀ ^ (Multiplicative.toAdd su.1).val * ι (φ (powHom x₁ hx₁o su.2))) := by
          rw [h2, mul_assoc]
  have hNn : (N.subgroupOf ((leviJ K ℓ f).subgroupOf C₀ ⊓
      Subgroup.centralizer ((Φ.comp ψ).range : Set ↥C₀))).Normal := by
    refine CFSG.HardMathSupport.Dickson.I271.normal_subgroupOf_of_conj fun g hg l hl => ?_
    obtain ⟨hgJ, hgC⟩ := Subgroup.mem_inf.1 hg
    obtain ⟨y', rfl⟩ := exists_leviSU_eq hK hf hζ hσζ P hP hgJ
    have hcomm1 : ι y' * ι (φ x₁) = ι (φ x₁) * ι y' :=
      (Subgroup.mem_centralizer_iff.1 hgC (ι (φ x₁)) ⟨(1, Multiplicative.ofAdd 1), hΦ1⟩).symm
    have hy'c : y' * φ x₁ = φ x₁ * y' := hcomm₁ y' hcomm1
    obtain ⟨y, hy, rfl⟩ := hl
    refine ⟨y' * y * y'⁻¹, conj_mem_coordBlockSU_of_commute hpK hx₁ (hφp x₁) hh₁1 hy'c hy, ?_⟩
    rw [map_mul, map_mul, map_inv]
  have hNc := CFSG.HardMathSupport.Dickson.I271.glaPComponent_of_normal hp hNq hpN
    (le_inf hNJ hNC) hNn
  intro hbot
  have hle : N ≤ GLAPLayer p ((leviJ K ℓ f).subgroupOf C₀ ⊓
      Subgroup.centralizer ((Φ.comp ψ).range : Set ↥C₀)) := le_sSup hNc
  rw [hbot, le_bot_iff] at hle
  exact CFSG.LocalAnalysis.GLTheoremA.glaPComponent_ne_bot' hNc hle

theorem modelAGen_twistedE6_of_inj (hℓ2 : ℓ ≠ 2) (hq5 : 5 ≤ ℓ ^ f) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpK : (p : K) ≠ 0) (hpSU : p ∣ Nat.card (Su K ℓ f 2)) {c : Kˣ}
    (hc : orderOf c = p)
    (hct : unitaryInvolution K ℓ f ((c : K) + ((c⁻¹ : Kˣ) : K)) = (c : K) + ((c⁻¹ : Kˣ) : K))
    {m : ℕ} {φ : (Fin m → Multiplicative (ZMod p)) →* Su K ℓ f 6}
    (hιφ : Function.Injective ((leviSU hK hf hζ hσζ P hP).comp φ))
    {x₁ : Fin m → Multiplicative (ZMod p)} (hx₁ : φ x₁ ∈ coordBlockSU K ℓ f blk01)
    (hx₁1 : x₁ ≠ 1)
    (hcomm₁ : ∀ y : Su K ℓ f 6,
      leviSU hK hf hζ hσζ P hP y * leviSU hK hf hζ hσζ P hP (φ x₁) =
        leviSU hK hf hζ hσζ P hP (φ x₁) * leviSU hK hf hζ hσζ P hP y → y * φ x₁ = φ x₁ * y) :
    ModelGen.ModelAGen p (m + 1) ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · subst h0
      exact absurd (Subsingleton.elim x₁ 1) hx₁1
    · exact h0
  obtain ⟨hAe, hAc, hA₁A, hA₁c, hJcomp, hAN, hcent, ht1, ht2, hJt, hAt⟩ :=
    modelAGen_twistedE6_spec_of_inj hK hf hζ hσζ P hP hℓ2 hp2 hc hct hm hιφ
  obtain ⟨h12A, h12c, h12L⟩ := glaPLayer_inf_centralizer_A12_ne_bot hK hf hζ hσζ P hP hℓ2 hq5 hp hp2
    hpK hpSU hc hct hιφ hx₁ hx₁1 hcomm₁
  exact ⟨_, _, _, _, twE6T K ℓ f, hAe, hAc, le_sup_left, h12A, hA₁c, h12c, hJcomp, hAN, hcent,
    h12L, ht1, ht2, hJt, hAt⟩

include hK hf hζ hσζ hP in
theorem modelAGen_twistedE6 (hℓ2 : ℓ ≠ 2) (hq5 : 5 ≤ ℓ ^ f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpK : (p : K) ≠ 0) (hcop : Nat.Coprime p (Nat.gcd 6 (ℓ ^ f + 1)))
    (hpSU : p ∣ Nat.card (Su K ℓ f 2)) {c : Kˣ} (hc : orderOf c = p)
    (hct : unitaryInvolution K ℓ f ((c : K) + ((c⁻¹ : Kˣ) : K)) = (c : K) + ((c⁻¹ : Kˣ) : K))
    {m : ℕ} {φ : (Fin m → Multiplicative (ZMod p)) →* Su K ℓ f 6} (hφ : Function.Injective φ)
    {x₁ : Fin m → Multiplicative (ZMod p)} (hx₁ : φ x₁ ∈ coordBlockSU K ℓ f blk01)
    (hx₁1 : x₁ ≠ 1) :
    ModelGen.ModelAGen p (m + 1) ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f)) :=
  modelAGen_twistedE6_of_inj hK hf hζ hσζ P hP hℓ2 hq5 hp hp2 hpK hpSU hc hct
    (leviSU_comp_injective hK hf hζ hσζ P hP hcop hφ) hx₁ hx₁1 fun _ h =>
      commute_of_leviSU_commute hK hf hζ hσζ P hP hcop
        (by rw [← map_pow, pow_eq_one_of_fin, map_one]) h

end Main

end CFSG.LocalAnalysis.GLTheoremA.S267.BadExc.TwE6Conc

end
