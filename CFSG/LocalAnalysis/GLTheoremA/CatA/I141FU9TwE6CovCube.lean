module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeTwE6TwoFusion
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E6HeisenbergAux.PairAuxSc

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I141F

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
  CFSG.LieType.Steinberg.CentralExt.MinusculeClosed
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.KE CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.TwistedE6 CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3

section Cube

set_option linter.unusedSectionVars false


private theorem twE6Cov_innerParam_pow_three {k : Type} [Field k] {ω : kˣ} (hω : ω ^ 3 = 1)
    (y : Fin 5 → ZMod 3) (l : Fin Tag.E6.rank) : e6InnerParam ω y l ^ 3 = 1 := by
  have h : e6InnerParam ω y ^ 3 = 1 := by
    unfold e6InnerParam
    rw [← powMonoidHom_apply, map_list_prod, List.map_map]
    refine List.prod_eq_one fun x hx => ?_
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    simp only [Function.comp_apply, powMonoidHom_apply]
    rw [← pow_mul, mul_comm, pow_mul]
    have : (Pi.mulSingle (⟨i.val, lt_of_lt_of_le i.2 (by decide)⟩ : Fin Tag.E6.rank) ω :
        Fin Tag.E6.rank → kˣ) ^ 3 = 1 := by
      rw [← Pi.mulSingle_pow, hω, Pi.mulSingle_one]
    rw [this, one_pow]
  have := congrFun h l
  simpa using this

private theorem twE6Cov_descent {K : Type} [Field K] [Finite K]
    (ω : (AlgebraicClosure K)ˣ) {h : ModGL Tag.E6 (AlgebraicClosure K)}
    (hh : h ∈ adjointGroup Tag.E6 (AlgebraicClosure K)) :
    ∃ k : Subfield (AlgebraicClosure K), Finite k ∧ ((ω : AlgebraicClosure K) ∈ k) ∧
      (∀ c : K, algebraMap K (AlgebraicClosure K) c ∈ k) ∧
      ∃ h₃ ∈ adjointGroup Tag.E6 k, baseChangeGL k.subtype h₃ = h := by
  classical
  obtain ⟨E, hE⟩ := exists_finset_descent hh
  obtain ⟨k, hk, hEk, hιk⟩ :=
    exists_finite_subfield_of_finset (K := K) (insert (ω : AlgebraicClosure K) E)
  have hmem : ∀ x ∈ insert (ω : AlgebraicClosure K) E, x ∈ k :=
    fun x hx => hEk (Finset.mem_coe.2 hx)
  refine ⟨k, hk, hmem _ (Finset.mem_insert_self _ _), fun c => hιk ⟨c, rfl⟩, ?_⟩
  exact hE k fun x hx => hmem x (Finset.mem_insert_of_mem (Finset.mem_coe.1 hx))

theorem twE6Cov_cube_eq_one {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 4)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2) (g : ↥(fixedGroup K σ.toRingHom))
    (hg : (e6IsogenyFixed σ.toRingHom g) ^ 3 = 1) : g ^ 3 = 1 := by
  classical
  set L := AlgebraicClosure K with hL
  haveI hcL : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK2 : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
  have hσ2 : ∀ c, σ c = c ^ (2 ^ 1) := fun c => by rw [hσ]; norm_num
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hder, -, -, -⟩ :=
    CFSG.LieType.Chevalley.twisted_E6_all_characteristic_exact_automorphism_normal_form
      Nat.prime_two le_rfl K hK2 σ hσ2
  have hθθ : ∀ c, σ.toRingHom (σ.toRingHom c) = c := fun c => by
    have : Fintype K := Fintype.ofFinite K
    have h := FiniteField.pow_card c
    rw [← Nat.card_eq_fintype_card, hK] at h
    simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hσ, ← pow_mul]
    exact h
  obtain ⟨t, ht_def⟩ : ∃ t : ModGL Tag.E6 K, t = e6IsogenyFixed σ.toRingHom g := ⟨_, rfl⟩
  have ht : t ∈ twistedE6RootGroup K σ := by
    have h1 : e6IsogenyFixed σ.toRingHom g ∈ (e6IsogenyFixed σ.toRingHom).range := ⟨g, rfl⟩
    rw [range_e6IsogenyFixed σ.toRingHom hθθ hK.ge, hder] at h1
    rw [ht_def]
    exact h1
  have ht3 : t ^ 3 = 1 := by rw [ht_def]; exact hg
  obtain ⟨g0', hg0C', hg0'⟩ := exists_twE6Two_lang K
  obtain ⟨G0, hG0⟩ : ∃ G0 : ModGL Tag.E6 L, G0 = g0' := ⟨g0', rfl⟩
  have hG0C : G0 ∈ adjointGroup Tag.E6 L := by rw [hG0]; exact hg0C'
  obtain ⟨s, hs_def⟩ : ∃ s, s = twE6TwoEquiv hK σ hσ hg0C' hg0' ⟨t, ht⟩ := ⟨_, rfl⟩
  have hsmat : (s : ModGL Tag.E6 L) = G0⁻¹ * baseChangeGL (algebraMap K L) t * G0 := by
    rw [hs_def, hG0]
    exact coe_twE6TwoEquiv hK σ hσ hg0C' hg0' ⟨t, ht⟩
  have hs3 : (s : ModGL Tag.E6 L) ^ 3 = 1 := by
    have h1 : (⟨t, ht⟩ : twistedE6RootGroup K σ) ^ 3 = 1 :=
      Subtype.ext (by show t ^ 3 = 1; exact ht3)
    have h2 : s ^ 3 = 1 := by rw [hs_def, ← map_pow, h1, map_one]
    simpa using congrArg Subtype.val h2
  obtain ⟨ω, hω⟩ : ∃ ω : Lˣ, orderOf ω = 3 := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3
      (by rw [Nat.card_units, hK] <;> norm_num)
    refine ⟨Units.map (algebraMap K L).toMonoidHom ζ, ?_⟩
    rw [← hζ]
    exact orderOf_injective _ (Units.map_injective (algebraMap K L).injective) ζ
  have hω3 : ω ^ 3 = 1 := pow_three_of_orderOf hω
  obtain ⟨m, hmM, y, hm⟩ := twE6TwoFusion_holds K hK σ hσ g0' hg0C' hg0' ω hω
    (s : ModGL Tag.E6 L) s.2 hs3
  have hrel : (m * G0⁻¹) * baseChangeGL (algebraMap K L) t * (m * G0⁻¹)⁻¹ =
      dV (τ := .E6) ω (subLin (τ := .E6) e6InnerVec y) := by
    rw [← hm, hsmat]
    group
  have hh : m * G0⁻¹ ∈ adjointGroup Tag.E6 L := mul_mem hmM.1 (inv_mem hG0C)
  obtain ⟨k, hk, hωk, hKk, h₃, hh₃G, hh₃⟩ := twE6Cov_descent ω hh
  haveI : Finite k := hk
  haveI : CharP k 2 := Subfield.charP k 2
  obtain ⟨ι₃, hι₃⟩ : ∃ ι₃ : K →+* k, k.subtype.comp ι₃ = algebraMap K L :=
    ⟨(algebraMap K L).codRestrict k hKk, RingHom.ext fun _ => rfl⟩
  obtain ⟨ω₃, hω₃⟩ : ∃ ω₃ : kˣ, Units.map k.subtype.toMonoidHom ω₃ = ω :=
    ⟨Units.mk0 ⟨(ω : L), hωk⟩ (fun h0 => ω.ne_zero (congrArg Subtype.val h0)), Units.ext rfl⟩
  have hinj : Function.Injective (Units.map k.subtype.toMonoidHom) :=
    units_map_subtype_injective k
  have hω₃3 : ω₃ ^ 3 = 1 := hinj (by rw [map_pow, hω₃, hω3, map_one])
  obtain ⟨u₃, hu₃⟩ : ∃ u₃ : Fin Tag.E6.rank → kˣ, u₃ = e6InnerParam ω₃ y := ⟨_, rfl⟩
  have hu₃3 : ∀ l, u₃ l ^ 3 = 1 := fun l => by
    rw [hu₃]
    exact twE6Cov_innerParam_pow_three hω₃3 y l
  have hconj : h₃ * baseChangeGL ι₃ t * h₃⁻¹ = rootDiagUnit Tag.E6 (e6RootParams u₃) := by
    apply baseChangeGL_injective k.subtype
    rw [map_mul, map_mul, map_inv, hh₃, baseChangeGL_baseChangeGL, hι₃, hrel, hu₃,
      e6RootParams_e6InnerParam hω₃3, baseChangeGL_rootDiagUnit]
    change rootDiagUnit Tag.E6 (torV ω (subLin (τ := .E6) e6InnerVec y)) = _
    congr 1
    funext j
    simp only [torV, map_pow, hω₃]
  obtain ⟨xl, hxl⟩ : ∃ xl : e6Data_valid.minGroup k, xl = minBC e6Data_valid ι₃ g.1 := ⟨_, rfl⟩
  obtain ⟨hl, hhl⟩ := e6Isogeny_surjective k ⟨h₃, hh₃G⟩
  obtain ⟨T, hT⟩ : ∃ T, T = minTorus e6Data_valid k u₃ := ⟨_, rfl⟩
  have hxπ : ((e6Isogeny k xl : adjointGroup Tag.E6 k) : ModGL Tag.E6 k) =
      baseChangeGL ι₃ t := by
    rw [hxl, e6Isogeny_minBC, ht_def]
    rfl
  have hhπ : ((e6Isogeny k hl : adjointGroup Tag.E6 k) : ModGL Tag.E6 k) = h₃ := by
    rw [hhl]
  have hTπ : ((e6Isogeny k T : adjointGroup Tag.E6 k) : ModGL Tag.E6 k) =
      rootDiagUnit Tag.E6 (e6RootParams u₃) := by
    rw [hT]
    exact e6Isogeny_minTorus u₃
  have hz : T⁻¹ * (hl * xl * hl⁻¹) ∈ Subgroup.center (e6Data_valid.minGroup k) := by
    refine mem_center_of_isogeny_eq_one ?_
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inv, hxπ, hhπ, hTπ, ← hconj]
    group
  obtain ⟨v, hv, hv3⟩ := exists_minTorus_of_mem_center_E6 hz
  have hz3 : (T⁻¹ * (hl * xl * hl⁻¹)) ^ 3 = 1 := by
    rw [hv, ← map_pow]
    have : v ^ 3 = 1 := funext fun j => by simpa using hv3 j
    rw [this, map_one]
  have hT3 : T ^ 3 = 1 := by
    rw [hT, ← map_pow]
    have : u₃ ^ 3 = 1 := funext fun l => by simpa using hu₃3 l
    rw [this, map_one]
  have hcomm : Commute T (T⁻¹ * (hl * xl * hl⁻¹)) :=
    Subgroup.mem_center_iff.1 hz T
  have ha3 : (hl * xl * hl⁻¹) ^ 3 = 1 := by
    have h1 : hl * xl * hl⁻¹ = T * (T⁻¹ * (hl * xl * hl⁻¹)) := by group
    rw [h1, hcomm.mul_pow, hT3, hz3, one_mul]
  have hx3 : xl ^ 3 = 1 := by
    rw [conj_pow] at ha3
    calc xl ^ 3 = hl⁻¹ * (hl * xl ^ 3 * hl⁻¹) * hl := by group
      _ = 1 := by rw [ha3]; group
  have hg3 : minBC e6Data_valid ι₃ (g.1 ^ 3) = minBC e6Data_valid ι₃ 1 := by
    rw [map_pow, ← hxl, hx3, map_one]
  exact Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.E6Heis.PairAux.minBC_injective
      e6Data_valid ι₃ hg3)

theorem twE6Cov_cube_eq_one_of_frob {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 4) (θ : K →+* K) (hθ : ∀ c, θ c = c ^ 2) (g : ↥(fixedGroup K θ))
    (hg : (e6IsogenyFixed θ g) ^ 3 = 1) : g ^ 3 = 1 := by
  obtain ⟨σ, rfl⟩ : ∃ σ : K ≃+* K, σ.toRingHom = θ :=
    ⟨RingEquiv.ofBijective θ ⟨θ.injective, Finite.surjective_of_injective θ.injective⟩, rfl⟩
  exact twE6Cov_cube_eq_one hK σ (fun c => hθ c) g hg

end Cube

end CFSG.LocalAnalysis.GLTheoremA.I141F
