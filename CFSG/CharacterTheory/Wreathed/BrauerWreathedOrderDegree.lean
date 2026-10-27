module

public import CFSG.CharacterTheory.Wreathed.BrauerWongSylowCentralizer
public import CFSG.CharacterTheory.PSL2Table.BlocksDefect
public import CFSG.CharacterTheory.Wreathed.ConditionalFourierParityCharacters
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public noncomputable section

open scoped Classical

namespace CFSG.Wreathed.BrauerWreathedOrder

open CFSG CFSG.TwoRankLowerBound.Helpers CFSG.BrauerThirdMainTheorem.Helpers
  CFSG.Wreathed.ConditionalFourier

theorem eq_one_of_pow_eq_one_of_sub_one_mem (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    (h2 : (2 : BlocksAlgInt) ∈ m) {ζ : ℂ} {r : ℕ} (hr : Odd r) (hζ : ζ ^ r = 1)
    (hM : ζ - 1 ∈ BlocksLocalMaxIdeal m) : ζ = 1 := by
  by_contra hne
  have hzInt : IsIntegral ℤ ζ :=
    IsIntegral.of_pow hr.pos (by rw [hζ]; exact isIntegral_one)
  have hzR := CFSG.PSL2Table.integral_mem_localRing m hm hzInt
  have hterm : ∀ i : ℕ, ζ ^ i - 1 ∈ BlocksLocalMaxIdeal m := by
    intro i
    rw [← geom_sum_mul, mul_comm]
    exact localMaxIdeal_mul_localRing m hm hM (localRing_sum m hm _ _
      (fun l _ => CFSG.PSL2Table.pow_mem_localRing m hm hzR l))
  have hsum : ∑ i ∈ Finset.range r, ζ ^ i = 0 := by
    have h := geom_sum_mul ζ r
    rw [hζ, sub_self] at h
    exact (mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr hne)
  have hall := localMaxIdeal_sum m hm (Finset.range r) (fun i => ζ ^ i - 1) (fun i _ => hterm i)
  rw [Finset.sum_sub_distrib, hsum, Finset.sum_const, Finset.card_range] at hall
  apply CFSG.PSL2Table.intCast_not_mem_localMaxIdeal m hm h2 (n := r) ((Int.odd_coe_nat r).mpr hr)
  have := localMaxIdeal_neg m hall
  simpa using this

theorem representation_eq_character_smul {G : Type} [Group G] (V : FiniteComplexRepresentation G)
    (hV : Module.finrank ℂ V.vector = 1) (g : G) :
    V.representation g = V.character g • LinearMap.id := by
  let _ := V.addCommGroup
  let _ := V.module
  obtain ⟨c, hc, -⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hV (V.representation g)
  have : V.character g = c := by
    change LinearMap.trace ℂ _ (V.representation g) = c
    rw [hc, map_smul, LinearMap.trace_id, hV]
    simp
  rw [this]
  exact hc

theorem character_mul_of_finrank_eq_one {G : Type} [Group G] (V : FiniteComplexRepresentation G)
    (hV : Module.finrank ℂ V.vector = 1) (g h : G) :
    V.character (g * h) = V.character g * V.character h := by
  let _ := V.addCommGroup
  let _ := V.module
  have hgh := representation_eq_character_smul V hV (g * h)
  rw [map_mul, representation_eq_character_smul V hV g,
    representation_eq_character_smul V hV h, smul_mul_smul_comm, Module.End.mul_eq_comp,
    LinearMap.id_comp] at hgh
  have htr := congrArg (LinearMap.trace ℂ V.vector) hgh
  simp only [map_smul, LinearMap.trace_id, hV, Nat.cast_one, smul_eq_mul, mul_one] at htr
  exact htr.symm

theorem character_one_of_finrank_eq_one {G : Type} [Group G] (V : FiniteComplexRepresentation G)
    (hV : Module.finrank ℂ V.vector = 1) : V.character 1 = 1 := by
  rw [FiniteComplexRepresentation.character, Representation.char_one, hV, Nat.cast_one]

@[expose] def linearCharacterHom {G : Type} [Group G] (V : FiniteComplexRepresentation G)
    (hV : Module.finrank ℂ V.vector = 1) : G →* ℂˣ where
  toFun g := Units.mk0 (V.character g) (by
    intro h0
    have h := character_mul_of_finrank_eq_one V hV g g⁻¹
    rw [mul_inv_cancel, character_one_of_finrank_eq_one V hV, h0, zero_mul] at h
    exact one_ne_zero h)
  map_one' := Units.ext (character_one_of_finrank_eq_one V hV)
  map_mul' g h := Units.ext (character_mul_of_finrank_eq_one V hV g h)

theorem linearCharacterHom_apply {G : Type} [Group G] (V : FiniteComplexRepresentation G)
    (hV : Module.finrank ℂ V.vector = 1) (g : G) :
    (linearCharacterHom V hV g : ℂ) = V.character g := rfl

theorem exists_normal_index_two_of_even {X : Type} [Group X] [Finite X] (f : X →* ℂˣ)
    (heven : Even (Nat.card f.range)) : ∃ H : Subgroup X, H.Normal ∧ H.index = 2 := by
  have : Finite f.range := Finite.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  obtain ⟨ζ, hζ⟩ := IsCyclic.exists_generator (α := f.range)
  have htop : Subgroup.zpowers ζ = ⊤ := eq_top_iff.mpr fun x _ => hζ x
  refine ⟨(Subgroup.zpowers (ζ ^ (2 : ℤ))).comap f.rangeRestrict,
    Subgroup.Normal.comap (Subgroup.normal_of_isMulCommutative _) _, ?_⟩
  rw [Subgroup.index_comap_of_surjective _ f.rangeRestrict_surjective,
    Subgroup.index_zpowers_zpow htop, orderOf_eq_card_of_forall_mem_zpowers hζ]
  obtain ⟨k, hk⟩ := heven
  rw [hk, show k + k = k * 2 by ring]
  change Int.gcd ((2 : ℕ) : ℤ) ((k * 2 : ℕ) : ℤ) = 2
  rw [Int.gcd_natCast_natCast]
  exact Nat.gcd_mul_left_right k 2

theorem odd_card_carrier_of_sylow_le {G : Type} [Group G] [Finite G] (S : Sylow 2 G) {c : G}
    (hc : (S : Subgroup G) ≤ Subgroup.centralizer ({c} : Set G)) :
    Odd (Nat.card (ConjClasses.mk c).carrier) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := CFSG.PSL2Table.card_carrier_mul_card_centralizer c
  have h2 := (Subgroup.centralizer ({c} : Set G)).card_mul_index
  have hpos : 0 < Nat.card (Subgroup.centralizer ({c} : Set G)) := Nat.card_pos
  have heq : Nat.card (ConjClasses.mk c).carrier = (Subgroup.centralizer ({c} : Set G)).index := by
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [h1, mul_comm, h2]
  rw [heq]
  have hdvd := Subgroup.index_dvd_of_le hc
  rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
  exact fun h => S.not_dvd_index (dvd_trans h hdvd)

theorem two_le_basisDegree_of_principal {G : Type} [Group G] [Fintype G] (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hno2 : ¬ ∃ H : Subgroup G, H.Normal ∧ H.index = 2)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (basis : FiniteIrreducibleCharacterBasis G)
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    (ψ : basis.index)
    (hψ : ψ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal)
    (hψp : ψ ≠ principal) : 2 ≤ basisDegree basis ψ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hm : ideal.IsMaximal := inferInstance
  have h2 : (2 : BlocksAlgInt) ∈ ideal := CFSG.BlockBasics.prime_mem_of_charP 2 ideal
  have hpos := basisDegree_pos basis ψ
  by_contra hlt
  have hdeg : Module.finrank ℂ (basis.representation ψ).vector = 1 := by
    rw [basisDegree] at hpos hlt
    omega
  apply hψp
  set V := basis.representation ψ
  set lam := linearCharacterHom V hdeg
  have hodd : Odd (Nat.card lam.range) := by
    by_contra hev
    rw [Nat.not_odd_iff_even] at hev
    exact hno2 (exists_normal_index_two_of_even lam hev)
  have hSK : (S : Subgroup G) ≤ lam.ker := by
    intro s hs
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp S.isPGroup') ⟨s, hs⟩
    rw [Subgroup.orderOf_mk] at hk
    have h1 : orderOf (lam s) ∣ 2 ^ k := hk ▸ orderOf_map_dvd lam s
    have h2' : orderOf (lam s) ∣ Nat.card lam.range := by
      rw [← Subgroup.orderOf_mk (lam s) (MonoidHom.mem_range.mpr ⟨s, rfl⟩)]
      exact orderOf_dvd_natCard _
    have hcop : Nat.Coprime (orderOf (lam s)) (Nat.card lam.range) :=
      Nat.Coprime.coprime_dvd_left h1 (Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd))
    exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop h2')
  have hψB : V.character ∈ BlocksPrincipalBlock ideal G := by
    have hmem : V.character ∈ (fun l => (basis.representation l).character) ''
        ((coefficientBlock basis (localizedComplexIntegerRing ideal) principal : Finset _) :
          Set basis.index) := ⟨ψ, hψ, rfl⟩
    rw [CFSG.BlockBasics.coefficientBlock_image basis ideal principal, hprincipal] at hmem
    exact hmem
  have hEK : CFSG.Wreathed.BrauerWong.sylowCentralizerCore S ≤ lam.ker := by
    intro c hc
    have hcS := CFSG.Wreathed.BrauerWong.sylowCentralizerCore_le S hc
    have hco : Odd (orderOf c) := by
      rw [← Subgroup.orderOf_mk c hc]
      exact (Nat.coprime_two_left.mp
        (CFSG.Wreathed.BrauerWong.sylowCentralizerCore_coprime S)).of_dvd_nat
          (orderOf_dvd_natCard _)
    have hSc : (S : Subgroup G) ≤ Subgroup.centralizer ({c} : Set G) := by
      intro s hs
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp hcS s hs
    have hK := odd_card_carrier_of_sylow_le S hSc
    have hcong := principal_centralChar_congr ideal hm G hψB
      (classCoefficients_central ideal hm (ConjClasses.mk c))
    have hVcl : BlocksIsClassFunction V.character :=
      blocksVChar_isClassFunction (AddSubgroup.subset_closure
        (CFSG.BlockBasics.basis_character_mem_irr basis ψ))
    have h1cl : BlocksIsClassFunction (fun _ : G => (1 : ℂ)) := fun _ _ => rfl
    rw [CFSG.PSL2Table.centralChar_classCoefficients hVcl c,
      CFSG.PSL2Table.centralChar_classCoefficients h1cl c,
      character_one_of_finrank_eq_one V hdeg] at hcong
    have hmul : ((Nat.card (ConjClasses.mk c).carrier : ℤ) : ℂ) * (V.character c - 1) ∈
        BlocksLocalMaxIdeal ideal := by
      convert hcong using 1
      push_cast
      ring
    have hsub := CFSG.PSL2Table.mem_of_odd_mul_mem ideal hm h2 ((Int.odd_coe_nat _).mpr hK) hmul
    have hpow : V.character c ^ orderOf c = 1 := by
      rw [← linearCharacterHom_apply V hdeg, ← Units.val_pow_eq_pow_val, ← map_pow,
        pow_orderOf_eq_one, map_one, Units.val_one]
    have hc1 := eq_one_of_pow_eq_one_of_sub_one_mem ideal hm h2 hco hpow hsub
    rw [MonoidHom.mem_ker]
    exact Units.ext hc1
  have hNK : Subgroup.normalizer ((S : Subgroup G) : Set G) ≤ lam.ker := by
    obtain ⟨Φ, hΦ⟩ := CFSG.Wreathed.BrauerWong.normalizer_eq_sylow_prod_core n hn S e
    intro g hg
    obtain ⟨⟨x, y⟩, hxy⟩ := Φ.surjective ⟨g, hg⟩
    have hg' : g = x * y := by
      rw [← hΦ x y, hxy]
    rw [hg']
    exact lam.ker.mul_mem (hSK x.2) (hEK y.2)
  have htop : lam.ker = ⊤ := by
    have h := Sylow.normalizer_sup_eq_top' (N := lam.ker) S hSK
    apply eq_top_iff.mpr
    rw [← h]
    exact sup_le hNK le_rfl
  apply basis.distinct
  show (basis.representation ψ).character = (basis.representation principal).character
  rw [hprincipal]
  funext g
  have hg : g ∈ lam.ker := by rw [htop]; trivial
  rw [MonoidHom.mem_ker] at hg
  have := congrArg Units.val hg
  rw [linearCharacterHom_apply] at this
  exact this

end CFSG.Wreathed.BrauerWreathedOrder
