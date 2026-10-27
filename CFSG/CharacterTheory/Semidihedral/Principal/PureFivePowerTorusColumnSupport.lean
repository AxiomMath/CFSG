module

public import CFSG.CharacterTheory.Semidihedral.Principal.CyclicInversionAlternatingFive
public import CFSG.CharacterTheory.Semidihedral.Principal.DegreeQOddRestriction
public import CFSG.CharacterTheory.Semidihedral.Principal.CyclicFivePowerDefectColumnSupport
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2FixedPointBound

public section

open scoped Classical Pointwise

namespace CFSG.Semidihedral.Principal

open CFSG.GorensteinWalter in
theorem card_sylow_normalized_of_five_power {L : Type} [Group L] [Finite L] {p f : ℕ}
    (hp : p.Prime) (hf : 1 ≤ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel L .PSL 2 p f)
    {a : ℕ} (ha : 1 ≤ a) {e : ℤ} (he : e = 1 ∨ e = -1)
    (hqa : ((p ^ f : ℕ) : ℤ) + e = 2 * 5 ^ a) (g : L) (hg : orderOf g = 5 ^ a) :
    (Nat.card {P : Sylow p L // g ∈ Subgroup.normalizer ((P : Subgroup L) : Set L)} : ℤ) =
      1 - e := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, K, hK, hKfin, hKcard, ⟨iso⟩⟩ := hmodel
  let iso' : L ≃* PSL2 K :=
    iso.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm
  set g' : PSL2 K := iso' g with hg'def
  have hg' : orderOf g' = 5 ^ a := by rw [hg'def, MulEquiv.orderOf_eq, hg]
  have hinj : Function.Injective (fun P : Sylow p L =>
      Sylow.mapSurjective (f := iso'.toMonoidHom) iso'.surjective P) := by
    intro P Q h
    apply Sylow.ext
    have h' := congrArg (fun S : Sylow p (PSL2 K) => (S : Subgroup (PSL2 K))) h
    exact Subgroup.map_injective iso'.injective h'
  have hcount : Nat.card {P : Sylow p L // g ∈ Subgroup.normalizer ((P : Subgroup L) : Set L)} =
      Nat.card {S : Sylow p (PSL2 K) //
        g' ∈ Subgroup.normalizer ((S : Subgroup (PSL2 K)) : Set (PSL2 K))} := by
    refine Nat.card_congr (Equiv.subtypeEquiv (Equiv.ofBijective _
      ⟨hinj, Sylow.mapSurjective_surjective (f := iso'.toMonoidHom) iso'.surjective p⟩)
      fun P => ?_)
    change _ ↔ g' ∈ Subgroup.normalizer (((P : Subgroup L).map iso'.toMonoidHom : Subgroup _) :
      Set (PSL2 K))
    rw [← Subgroup.map_equiv_normalizer_eq, Subgroup.mem_map_equiv, hg'def,
      MulEquiv.symm_apply_apply]
  have hpts : Nat.card {S : Sylow p (PSL2 K) //
      g' ∈ Subgroup.normalizer ((S : Subgroup (PSL2 K)) : Set (PSL2 K))} =
      Nat.card {x : PSL2ProjectiveLine K // g' • x = x} := by
    symm
    refine Nat.card_congr (Equiv.subtypeEquiv (psl2ProjectiveLineEquivSylow K hKcard)
      fun x => ?_)
    rw [← psl2ProjectiveLineEquivSylow_stabilizer K hKcard x, MulAction.mem_stabilizer_iff]
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hZ : IsPGroup 5 (Subgroup.zpowers g') := IsPGroup.of_card (n := a) (by
    rw [Nat.card_zpowers, hg'])
  have hmod := hZ.card_modEq_card_fixedPoints (α := PSL2ProjectiveLine K)
  have hfixed : Nat.card (MulAction.fixedPoints (Subgroup.zpowers g') (PSL2ProjectiveLine K)) =
      Nat.card {x : PSL2ProjectiveLine K // g' • x = x} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
    constructor
    · intro hx
      exact hx ⟨g', Subgroup.mem_zpowers g'⟩
    · intro hx z
      have hle : Subgroup.zpowers g' ≤ MulAction.stabilizer (PSL2 K) x :=
        Subgroup.zpowers_le.mpr hx
      exact hle z.2
  have hline : Nat.card (PSL2ProjectiveLine K) = p ^ f + 1 := by
    have h := Projectivization.card' (k := K) (V := Fin 2 → K)
    rw [Nat.card_fun, Nat.card_fin, hKcard] at h
    have hq1 : 1 < p ^ f := Nat.one_lt_pow (by omega) hp.one_lt
    have hz : ((Nat.card (PSL2ProjectiveLine K) : ℤ) - (p ^ f + 1)) * ((p ^ f : ℤ) - 1) = 0 := by
      have h' : ((p ^ f : ℕ) : ℤ) ^ 2 = (Nat.card (PSL2ProjectiveLine K) : ℤ) *
          (((p ^ f : ℕ) : ℤ) - 1) + 1 := by
        have := congrArg (fun x : ℕ => (x : ℤ)) h
        push_cast [Nat.cast_sub hq1.le] at this ⊢
        linarith
      push_cast at h'
      linear_combination -h'
    have hne : ((p ^ f : ℤ) - 1) ≠ 0 := by
      have : (1 : ℤ) < (p ^ f : ℕ) := by exact_mod_cast hq1
      push_cast at this
      linarith
    have h0 := (mul_eq_zero.mp hz).resolve_right hne
    have : (Nat.card (PSL2ProjectiveLine K) : ℤ) = ((p ^ f + 1 : ℕ) : ℤ) := by
      push_cast
      linarith
    exact_mod_cast this
  have hle2 : Nat.card {x : PSL2ProjectiveLine K // g' • x = x} ≤ 2 :=
    psl2_fixedPoint_card_le_two K g' (by
      intro h1
      rw [h1, orderOf_one] at hg'
      have : 1 < 5 ^ a := Nat.one_lt_pow (by omega) (by norm_num)
      omega)
  rw [hcount, hpts]
  have hmod5 : (p ^ f + 1) % 5 = Nat.card {x : PSL2ProjectiveLine K // g' • x = x} % 5 := by
    have h := hmod
    rw [hline, hfixed] at h
    exact h
  obtain ⟨k, hk⟩ : 5 ∣ 5 ^ a := dvd_pow_self 5 (by omega)
  rcases he with rfl | rfl
  · have hq : p ^ f + 1 = 2 * 5 ^ a := by
      have : ((p ^ f : ℕ) : ℤ) + 1 = 2 * 5 ^ a := hqa
      exact_mod_cast this
    omega
  · have hq : p ^ f = 2 * 5 ^ a + 1 := by
      have : ((p ^ f : ℕ) : ℤ) - 1 = 2 * 5 ^ a := by rw [← hqa]; ring
      have hq1 : 1 ≤ p ^ f := Nat.one_le_pow _ _ hp.pos
      zify [hq1] at this ⊢
      linarith
    omega

theorem card_map_conj_eq_card_normalizer {Γ : Type*} [Group Γ] (L : Subgroup Γ) [L.Normal]
    {p : ℕ} (γ : Γ) (hγ : γ ∈ L) :
    Nat.card {P : Sylow p L // ((P : Subgroup L).map L.subtype).map
        (MulAut.conj γ).toMonoidHom = (P : Subgroup L).map L.subtype} =
      Nat.card {P : Sylow p L //
        (⟨γ, hγ⟩ : L) ∈ Subgroup.normalizer ((P : Subgroup L) : Set L)} := by
  refine Nat.card_congr (Equiv.subtypeEquivRight fun P => ?_)
  have h : MulAut.conjNormal (H := L) γ = MulAut.conj (⟨γ, hγ⟩ : L) := by
    ext x
    simp [MulAut.conjNormal_apply]
  rw [← conjNormal_smul_eq_iff_map_conj_eq L γ P, h]
  exact Sylow.smul_eq_iff_mem_normalizer

open CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.ActualSimpleLayerLocalPackage CFSG.Open in
theorem local_degree_q_value_of_five_power {G : Type} [Group G] [Fintype G]
    (n : ℕ) (hn : 4 ≤ n) (S0 : Sylow 2 G) (f0 : SemidihedralGroup n ≃* S0)
    (hG : ∀ U : Subgroup G, U.index ≠ 2) (t : G) (ht : orderOf t = 2)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (hN : N t = ⊥) {a : ℕ} (ha : 1 ≤ a) {e : ℤ} (he : e = 1 ∨ e = -1)
    (hqa : ((p ^ f : ℕ) : ℤ) + e = 2 * 5 ^ a)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (basis : FiniteIrreducibleCharacterBasis (C t)) (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) (α : basis.index)
    (hαB : α ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal)
    (hαdeg : Module.finrank ℂ (basis.representation α).vector = p ^ f)
    (hαker : MonoidHom.ker (basis.representation α).representation = NZ t)
    (y : C t) (hy : orderOf y = 5 ^ a) (hyL : kappa t y ∈ CFSG.generalizedFitting (Gamma t)) :
    (basis.representation α).character y = -e := by
  have hyodd : Odd (orderOf y) := by
    rw [hy]
    exact Odd.pow (by decide)
  have hval := local_degree_q_principal_odd_restriction_rigidity n hn S0 f0 hG t ht hnonab
    hcentral hnc p f hp hpodd hf hmodel ideal basis principal hprincipal α hαB hαdeg hαker y hyodd
  set L := CFSG.generalizedFitting (Gamma t) with hLdef
  have : L.Normal := (CFSG.LocalCores.generalized_fitting_characteristic (G := Gamma t)).2
  rw [hval, card_map_conj_eq_card_normalizer L _ hyL]
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hord : orderOf (⟨kappa t y, hyL⟩ : L) = 5 ^ a := by
    rw [Subgroup.orderOf_mk]
    obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
    apply orderOf_eq_prime_pow
    · intro h
      rw [← map_pow] at h
      have hker : y ^ 5 ^ b ∈ (kappa t).ker := h
      rw [QuotientGroup.ker_mk', NZ, hN, bot_sup_eq] at hker
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hker
      have ht2 : orderOf (tInC t) = 2 := by rw [← Subgroup.orderOf_coe]; exact ht
      have hsq : (y ^ 5 ^ b) ^ 2 = 1 := by
        rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← ht2,
          pow_orderOf_eq_one, one_zpow]
      have h5 : orderOf (y ^ 5 ^ b) = 5 := by
        rw [orderOf_pow' y (pow_ne_zero _ (by norm_num)), hy, pow_succ,
          Nat.gcd_eq_right (dvd_mul_right _ _), Nat.mul_div_cancel_left _ (pow_pos (by norm_num) _)]
      have := orderOf_dvd_of_pow_eq_one hsq
      rw [h5] at this
      norm_num at this
    · rw [← map_pow, ← hy, pow_orderOf_eq_one, map_one]
  have hcount := card_sylow_normalized_of_five_power hp hf hmodel ha he hqa _ hord
  rw [show (Nat.card {P : Sylow p L // (⟨kappa t y, hyL⟩ : L) ∈
      Subgroup.normalizer ((P : Subgroup L) : Set L)} : ℂ) =
      ((Nat.card {P : Sylow p L // (⟨kappa t y, hyL⟩ : L) ∈
        Subgroup.normalizer ((P : Subgroup L) : Set L)} : ℤ) : ℂ) by push_cast; rfl, hcount]
  push_cast
  ring

open CFSG.TwoRankLowerBound.Helpers in
theorem exists_localized_unit_eq_int_div (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    (p : ℕ) [CharP (ComplexAlgebraicIntegers ⧸ ideal) p] (x y : ℤ) (hx : ¬ (p : ℤ) ∣ x)
    (hy : ¬ (p : ℤ) ∣ y) :
    ∃ u : (localizedComplexIntegerRing ideal)ˣ, (u : ℂ) = x / y := by
  have hnot : ∀ z : ℤ, ¬ (p : ℤ) ∣ z → (z : ComplexAlgebraicIntegers) ∉ ideal := by
    intro z hz hmem
    apply hz
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_intCast] at hmem
    exact (CharP.intCast_eq_zero_iff (ComplexAlgebraicIntegers ⧸ ideal) p z).mp hmem
  have hcoe : ∀ z : ℤ, ((z : ComplexAlgebraicIntegers) : ℂ) = (z : ℂ) := fun z => by
    push_cast
    rfl
  have hx0 : (x : ℂ) ≠ 0 := by
    intro h
    apply hx
    rw [Int.cast_eq_zero.mp h]
    exact dvd_zero _
  have hy0 : (y : ℂ) ≠ 0 := by
    intro h
    apply hy
    rw [Int.cast_eq_zero.mp h]
    exact dvd_zero _
  have hmem : ∀ z w : ℤ, ¬ (p : ℤ) ∣ w → (z : ℂ) / w ∈ localizedComplexIntegerRing ideal := by
    intro z w hw
    rw [localizedComplexIntegerRing_mem_iff_fraction]
    exact ⟨z, w, hnot w hw, by rw [hcoe, hcoe]⟩
  refine ⟨⟨⟨(x : ℂ) / y, hmem x y hy⟩, ⟨(y : ℂ) / x, hmem y x hx⟩, ?_, ?_⟩, rfl⟩
  · apply Subtype.ext
    change (x : ℂ) / y * ((y : ℂ) / x) = 1
    field_simp
  · apply Subtype.ext
    change (y : ℂ) / x * ((x : ℂ) / y) = 1
    field_simp

open CFSG.TwoRankLowerBound.Helpers in
theorem exists_localized_unit_of_padicValNat_eq (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (p : ℕ) [hp : Fact p.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) p]
    {I f : ℕ} (hI : I ≠ 0) (hf : f ≠ 0) (hv : padicValNat p I = padicValNat p f) (c : ℤ)
    (hc : ¬ (p : ℤ) ∣ c) :
    ∃ u : (localizedComplexIntegerRing ideal)ˣ, (u : ℂ) = (I : ℂ) * c / f := by
  set k := padicValNat p I with hk
  have hIdec := Nat.ordProj_mul_ordCompl_eq_self I p
  have hfdec := Nat.ordProj_mul_ordCompl_eq_self f p
  rw [Nat.factorization_def I hp.out] at hIdec
  rw [Nat.factorization_def f hp.out] at hfdec
  have hI' := Nat.not_dvd_ordCompl hp.out hI
  have hf' := Nat.not_dvd_ordCompl hp.out hf
  rw [Nat.factorization_def I hp.out] at hI'
  rw [Nat.factorization_def f hp.out] at hf'
  rw [← hv] at hfdec hf'
  set I' := I / p ^ k with hI'def
  set f' := f / p ^ k with hf'def
  have hcI : ¬ (p : ℤ) ∣ (I' : ℤ) * c := by
    intro h
    rcases (Int.Prime.dvd_mul' hp.out h) with h1 | h1
    · exact hI' (Int.natCast_dvd_natCast.mp h1)
    · exact hc h1
  have hf'' : ¬ (p : ℤ) ∣ (f' : ℤ) := fun h => hf' (Int.natCast_dvd_natCast.mp h)
  obtain ⟨u, hu⟩ := exists_localized_unit_eq_int_div ideal p _ _ hcI hf''
  refine ⟨u, ?_⟩
  rw [hu]
  have hpk : ((p ^ k : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast pow_ne_zero k hp.out.ne_zero
  have hf0 : ((f' : ℕ) : ℂ) ≠ 0 := by
    intro h
    apply hf
    rw [← hfdec, Nat.cast_eq_zero.mp h, mul_zero]
  have hpk' : (p : ℂ) ^ k ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hp.out.ne_zero)
  conv_rhs => rw [← hIdec, ← hfdec]
  rw [← hk]
  push_cast
  field_simp

theorem generator_column_coefficient {G : Type*} [Group G] [Fintype G] (W : Subgroup G)
    [IsCyclic W] (a : ℕ) (hWcard : Nat.card W = 5 ^ a) (lam : W →* ℂˣ) (hlam : orderOf lam = 5)
    (F : W → ℂ) (c₀ : ℂ) (hF : ∀ w : W, Subgroup.zpowers (w : G) = W → F w = c₀) :
    ((5 : ℂ) ^ a)⁻¹ * ∑ w : W, F w * (starRingEnd ℂ (lam w : ℂ) - 1) = -c₀ := by
  have hlam5 : lam ^ 5 = 1 := hlam ▸ pow_orderOf_eq_one lam
  have hlam1 : lam ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hlam
    norm_num at hlam
  have hterm : ∀ w : W, F w * (starRingEnd ℂ (lam w : ℂ) - 1) =
      c₀ * (((lam w⁻¹ : ℂˣ) : ℂ) - 1) := by
    intro w
    rw [FivePowerColumn.conj_eq_inv W lam hlam5 w]
    by_cases hw : lam w = 1
    · have h1 : lam w⁻¹ = 1 := by rw [map_inv, hw, inv_one]
      rw [h1, Units.val_one, sub_self, mul_zero, mul_zero]
    · rw [hF w (FivePowerColumn.zpowers_eq_of_ne_one W a hWcard lam hlam5 w hw)]
  rw [Finset.sum_congr rfl (fun w _ => hterm w), ← Finset.mul_sum, Finset.sum_sub_distrib]
  have hsum : ∑ w : W, ((lam w⁻¹ : ℂˣ) : ℂ) = 0 := by
    rw [Fintype.sum_equiv (Equiv.inv W) (fun w => ((lam w⁻¹ : ℂˣ) : ℂ))
      (fun w => ((lam w : ℂˣ) : ℂ)) (fun w => rfl),
      FivePowerColumn.sum_linear W lam, ite_eq_right hlam1]
  rw [hsum, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, hWcard]
  have h5 : (5 : ℂ) ^ a ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp
  ring

theorem cyclic_torus_alternating_five_structure {G : Type*} [Group G] [Finite G] (W : Subgroup G)
    [IsCyclic W] (hodd : Odd (Nat.card W))
    (hKH : (Subgroup.centralizer (W : Set G)).relIndex (Subgroup.normalizer (W : Set G)) = 2)
    (hinv : ∀ h ∈ Subgroup.normalizer (W : Set G), h ∉ Subgroup.centralizer (W : Set G) →
      ∀ w ∈ W, h * w * h⁻¹ = w⁻¹)
    (hR : (CFSG.pPrimeCore 2 (Subgroup.centralizer (W : Set G))).map
      (Subgroup.centralizer (W : Set G)).subtype = W)
    (hK5 : Nonempty ((Subgroup.centralizer (W : Set G) ⧸
      CFSG.pPrimeCore 2 (Subgroup.centralizer (W : Set G))) ≃* alternatingGroup (Fin 5)))
    (hdih : ∃ P : Sylow 2 (Subgroup.normalizer (W : Set G)),
      Nonempty ((P : Subgroup (Subgroup.normalizer (W : Set G))) ≃* DihedralGroup 4)) :
    let H : Subgroup G := Subgroup.normalizer (W : Set G)
    let K : Subgroup G := Subgroup.centralizer (W : Set G)
    let J : Subgroup G := ⁅K, K⁆
    W ⊔ J = K ∧ W ⊓ J = ⊥ ∧ (∀ w ∈ W, ∀ j ∈ J, w * j = j * w) ∧
      (∀ h ∈ H, ∀ j ∈ J, h * j * h⁻¹ ∈ J) ∧ Nonempty (J ≃* alternatingGroup (Fin 5)) ∧
      (∃ (E : Subgroup G) (σ : E ≃* Equiv.Perm (Fin 5)), E ≤ H ∧ J ≤ E ∧ W ⊔ E = H ∧ W ⊓ E = ⊥ ∧
        (∀ x : E, (x : G) ∈ J ↔ σ x ∈ alternatingGroup (Fin 5)) ∧
        ∀ x : E, ∀ w ∈ W, (x : G) * w * (x : G)⁻¹ = w ^ ((Equiv.Perm.sign (σ x) : ℤˣ) : ℤ)) ∧
      Nat.card H = 120 * Nat.card W := by
  intro H K J
  have hWH : W ≤ H := Subgroup.le_normalizer
  have hKH' : K ≤ H := Subgroup.centralizer_le_normalizer _
  set W' : Subgroup H := W.subgroupOf H with hW'def
  have hW'n : W'.Normal := Subgroup.normal_in_normalizer
  have hW'card : Nat.card W' = Nat.card W :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWH).toEquiv
  have : IsCyclic W' :=
    isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hWH).symm.toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hWH).symm.surjective
  have hcent : Subgroup.centralizer (W' : Set H) = K.subgroupOf H := by
    ext h
    rw [Subgroup.mem_centralizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
    constructor
    · intro hh w hw
      exact congrArg Subtype.val (hh ⟨w, hWH hw⟩ hw)
    · intro hh w hw
      exact Subtype.ext (hh w hw)
  have hindex' : (Subgroup.centralizer (W' : Set H)).index = 2 := by
    rw [hcent]
    exact hKH
  have hinv' : ∀ h : H, h ∉ Subgroup.centralizer (W' : Set H) → ∀ w ∈ W', h * w * h⁻¹ = w⁻¹ := by
    intro h hh w hw
    rw [hcent, Subgroup.mem_subgroupOf] at hh
    exact Subtype.ext (hinv h h.2 hh w hw)
  let hKsub : K.subgroupOf H ≃* K := Subgroup.subgroupOfEquivOfLe hKH'
  let φ : Subgroup.centralizer (W' : Set H) ≃* K :=
    (MulEquiv.subgroupCongr hcent).trans hKsub
  have hφval : ∀ x : Subgroup.centralizer (W' : Set H), ((φ x : K) : G) = ((x : H) : G) :=
    fun x => rfl
  have hmapN : (W'.subgroupOf (Subgroup.centralizer (W' : Set H))).map φ.toMonoidHom =
      CFSG.pPrimeCore 2 K := by
    ext k
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hxW : ((x : H) : G) ∈ W := hx
      rw [← hR] at hxW
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hxW
      have : y = φ.toMonoidHom x := Subtype.ext (by
        change (y : G) = ((φ x : K) : G)
        rw [hφval]
        exact hyx)
      rw [← this]
      exact hy
    · intro hk
      refine ⟨φ.symm k, ?_, by simp⟩
      change (((φ.symm k : Subgroup.centralizer (W' : Set H)) : H) : G) ∈ W
      have h1 : (((φ.symm k : Subgroup.centralizer (W' : Set H)) : H) : G) = (k : G) := by
        rw [← hφval, MulEquiv.apply_symm_apply]
      rw [h1, ← hR]
      exact ⟨k, hk, rfl⟩
  obtain ⟨ψ⟩ := hK5
  have hquot : Nonempty (Subgroup.centralizer (W' : Set H) ⧸
      W'.subgroupOf (Subgroup.centralizer (W' : Set H)) ≃* alternatingGroup (Fin 5)) :=
    ⟨(QuotientGroup.congr _ _ φ hmapN).trans ψ⟩
  have hdih' : ∃ P : Sylow 2 H, Nonempty ((P : Subgroup H) ≃* DihedralGroup 4) := hdih
  obtain ⟨J', x, E', σ', hJ'def, hWJ', hWJ'inf, -, hJ'n, ⟨eJ'⟩, -, -, hE'def, hWE', hWE'inf, hσJ,
      hσact, -, hHcard, -⟩ :=
    odd_cyclic_inversion_normalizer_alternating_five_centralizer_splits_by_sign W'
      (hW'card ▸ hodd) hindex' hinv' hquot hdih'
  have hmapW : W'.map H.subtype = W := by
    rw [hW'def, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hWH]
  have hmapC : (Subgroup.centralizer (W' : Set H)).map H.subtype = K := by
    rw [hcent, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hKH']
  have hmapJ : J'.map H.subtype = J := by
    rw [hJ'def, Subgroup.map_subtype_commutator, Subgroup.map_commutator, hmapC]
  have hinj := H.subtype_injective
  have hWJ : W ⊔ J = K := by
    rw [← hmapW, ← hmapJ, ← Subgroup.map_sup, hWJ', hmapC]
  have hWJinf : W ⊓ J = ⊥ := by
    rw [← hmapW, ← hmapJ, ← Subgroup.map_inf_eq _ _ _ hinj, hWJ'inf, Subgroup.map_bot]
  have hJK : J ≤ K := Subgroup.commutator_le_self K
  have hcomm : ∀ w ∈ W, ∀ j ∈ J, w * j = j * w := fun w hw j hj =>
    Subgroup.mem_centralizer_iff.mp (hJK hj) w hw
  have hJnorm : ∀ h ∈ H, ∀ j ∈ J, h * j * h⁻¹ ∈ J := by
    intro h hh j hj
    rw [← hmapJ] at hj ⊢
    obtain ⟨j', hj', rfl⟩ := Subgroup.mem_map.mp hj
    exact ⟨⟨h, hh⟩ * j' * ⟨h, hh⟩⁻¹, hJ'n.conj_mem j' hj' _, rfl⟩
  have hJiso : Nonempty (J ≃* alternatingGroup (Fin 5)) :=
    ⟨(MulEquiv.subgroupCongr hmapJ).symm.trans
      ((Subgroup.equivMapOfInjective J' H.subtype hinj).symm.trans eJ')⟩
  let E : Subgroup G := E'.map H.subtype
  let σ : E ≃* Equiv.Perm (Fin 5) := (Subgroup.equivMapOfInjective E' H.subtype hinj).symm.trans σ'
  have hσval : ∀ y : E', σ (Subgroup.equivMapOfInjective E' H.subtype hinj y) = σ' y := by
    intro y
    simp [σ]
  have hEH : E ≤ H := Subgroup.map_subtype_le _
  have hWE : W ⊔ E = H := by
    rw [← hmapW, ← Subgroup.map_sup, hWE', ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hWEinf : W ⊓ E = ⊥ := by
    rw [← hmapW, ← Subgroup.map_inf_eq _ _ _ hinj, hWE'inf, Subgroup.map_bot]
  have hJE : J ≤ E := by
    rw [← hmapJ]
    exact Subgroup.map_mono (hE'def ▸ le_sup_left)
  refine ⟨hWJ, hWJinf, hcomm, hJnorm, hJiso,
    ⟨E, σ, hEH, hJE, hWE, hWEinf, fun y => ?_, fun y w hw => ?_⟩, ?_⟩
  · obtain ⟨y', rfl⟩ := (Subgroup.equivMapOfInjective E' H.subtype hinj).surjective y
    rw [hσval, ← hσJ y', ← hmapJ]
    change ((y' : H) : G) ∈ J'.map H.subtype ↔ _
    exact Subgroup.mem_map_iff_mem hinj
  · obtain ⟨y', rfl⟩ := (Subgroup.equivMapOfInjective E' H.subtype hinj).surjective y
    rw [hσval]
    have hw' : (⟨w, hWH hw⟩ : H) ∈ W' := hw
    have h := congrArg Subtype.val (hσact y' ⟨w, hWH hw⟩ hw')
    simpa using h
  · rw [hHcard, hW'card]

theorem mem_zpowers_mul_of_commute_of_coprime {G : Type*} [Group G] {a b : G} (hab : Commute a b)
    (hcop : Nat.Coprime (orderOf a) (orderOf b)) : a ∈ Subgroup.zpowers (a * b) := by
  have hpow : (a * b) ^ orderOf b = a ^ orderOf b := by
    rw [hab.mul_pow, pow_orderOf_eq_one, mul_one]
  have hamem : a ∈ Subgroup.zpowers (a ^ orderOf b) := by
    rw [mem_zpowers_pow_iff]
    simpa [Nat.gcd_comm] using hcop.gcd_eq_one
  have hle : Subgroup.zpowers (a ^ orderOf b) ≤ Subgroup.zpowers (a * b) := by
    rw [Subgroup.zpowers_le, ← hpow]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
  exact hle hamem

theorem centralizer_mul_eq_inf_of_coprime {G : Type*} [Group G] {a b : G} (hab : Commute a b)
    (hcop : Nat.Coprime (orderOf a) (orderOf b)) :
    Subgroup.centralizer {a * b} = Subgroup.centralizer {a} ⊓ Subgroup.centralizer {b} := by
  have ha := mem_zpowers_mul_of_commute_of_coprime hab hcop
  have hb : b ∈ Subgroup.zpowers (a * b) := by
    have h := mem_zpowers_mul_of_commute_of_coprime hab.symm (Nat.Coprime.symm hcop)
    rwa [hab.symm.eq] at h
  apply le_antisymm
  · intro c hc
    have hle : Subgroup.zpowers (a * b) ≤ Subgroup.centralizer {c} := by
      rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_singleton_iff.mp hc).symm
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_singleton_iff.mp (hle ha)).symm
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hb)).symm
  · intro c hc
    obtain ⟨hca, hcb⟩ := Subgroup.mem_inf.mp hc
    rw [Subgroup.mem_centralizer_singleton_iff] at hca hcb ⊢
    rw [← mul_assoc, hca, mul_assoc, hcb, mul_assoc]

theorem five_adic_degree_of_order_formula {Gc q f₂ f₄ a : ℕ} {e δ₂ : ℤ} (ha : 1 ≤ a)
    (he : e = 1 ∨ e = -1) (hδ : δ₂ = 1 ∨ δ₂ = -1) (hqa : (q : ℤ) + e = 2 * 5 ^ a)
    (hf₄ : (f₄ : ℤ) = f₂ + δ₂) (hf₂ : 1 < f₂) (hGpos : 0 < Gc)
    (hX : (f₂ : ℚ) + e * δ₂ * q ≠ 0)
    (hOF : (Gc : ℚ) = ((2 * q * (q ^ 2 - 1) : ℕ) : ℚ) ^ 3 / ((4 * 5 ^ a : ℕ) : ℚ) ^ 2 *
      ((f₂ : ℚ) * (f₂ + δ₂) / (f₂ + e * δ₂ * q) ^ 2) * ((q - e) / q))
    (hGa : 5 ^ (a + 1) ∣ Gc) :
    (5 ∣ f₂ ∧ ¬ 5 ∣ f₄ ∧ padicValNat 5 Gc = a + padicValNat 5 f₂) ∨
      (5 ∣ f₄ ∧ ¬ 5 ∣ f₂ ∧ padicValNat 5 Gc = a + padicValNat 5 f₄) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hq1 : 1 ≤ q := by
    rcases he with rfl | rfl
    · have : (2 : ℤ) ≤ 2 * 5 ^ a := by
        have : (1 : ℤ) ≤ 5 ^ a := one_le_pow₀ (by norm_num)
        linarith
      omega
    · have : (2 : ℤ) ≤ 2 * 5 ^ a := by
        have : (1 : ℤ) ≤ 5 ^ a := one_le_pow₀ (by norm_num)
        linarith
      omega
  have hint : (Gc : ℤ) * ((f₂ : ℤ) + e * δ₂ * q) ^ 2 =
      4 * (q : ℤ) ^ 2 * ((q : ℤ) - e) ^ 4 * 5 ^ a * (f₂ * f₄) := by
    have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
    have h5 : (5 : ℚ) ^ a ≠ 0 := pow_ne_zero _ (by norm_num)
    have hsq : ((q ^ 2 - 1 : ℕ) : ℚ) = ((q : ℚ) - e) * (2 * 5 ^ a) := by
      have h1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
      have hqa' : (q : ℚ) + e = 2 * 5 ^ a := by exact_mod_cast hqa
      rw [Nat.cast_sub h1, ← hqa']
      push_cast
      rcases he with rfl | rfl <;> push_cast <;> ring
    have hOF' := hOF
    push_cast [Nat.cast_sub (Nat.one_le_pow 2 q (by omega))] at hOF'
    have hsq' : ((q : ℚ) ^ 2 - 1) = ((q : ℚ) - e) * (2 * 5 ^ a) := by
      have := hsq
      push_cast [Nat.cast_sub (Nat.one_le_pow 2 q (by omega))] at this
      exact this
    rw [hsq'] at hOF'
    have hX2 : ((f₂ : ℚ) + e * δ₂ * q) ^ 2 ≠ 0 := pow_ne_zero _ hX
    have hfinal : (Gc : ℚ) * ((f₂ : ℚ) + e * δ₂ * q) ^ 2 =
        4 * (q : ℚ) ^ 2 * ((q : ℚ) - e) ^ 4 * 5 ^ a * (f₂ * (f₂ + δ₂)) := by
      rw [hOF']
      set X := (f₂ : ℚ) + e * δ₂ * q with hXdef
      set F := (f₂ : ℚ) * (f₂ + δ₂) with hFdef
      rw [show (2 * (q : ℚ) * (((q : ℚ) - e) * (2 * 5 ^ a))) ^ 3 / (4 * 5 ^ a) ^ 2 * (F / X ^ 2) *
          (((q : ℚ) - e) / q) * X ^ 2 =
          (2 * (q : ℚ) * (((q : ℚ) - e) * (2 * 5 ^ a))) ^ 3 / (4 * 5 ^ a) ^ 2 * F *
            (((q : ℚ) - e) / q) * (X ^ 2 / X ^ 2) by ring, div_self hX2, mul_one]
      field_simp
      ring
    have hf4q : ((f₄ : ℤ) : ℚ) = (f₂ : ℚ) + δ₂ := by exact_mod_cast hf₄
    have : ((Gc : ℤ) * ((f₂ : ℤ) + e * δ₂ * q) ^ 2 : ℚ) =
        (4 * (q : ℤ) ^ 2 * ((q : ℤ) - e) ^ 4 * 5 ^ a * (f₂ * f₄) : ℚ) := by
      push_cast
      rw [hfinal]
      push_cast at hf4q
      rw [hf4q]
    exact_mod_cast this
  set N := ((f₂ : ℤ) + e * δ₂ * q).natAbs with hNdef
  set Y := ((q : ℤ) - e).natAbs with hYdef
  have hnat : Gc * N ^ 2 = 4 * q ^ 2 * Y ^ 4 * 5 ^ a * (f₂ * f₄) := by
    have h := congrArg Int.natAbs hint
    simp only [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast] at h
    rw [← hNdef, ← hYdef] at h
    have h4 : Int.natAbs 4 = 4 := rfl
    have h5 : Int.natAbs 5 = 5 := rfl
    rw [h4, h5] at h
    exact h
  obtain ⟨k, hk⟩ : (5 : ℤ) ∣ 5 ^ a := dvd_pow_self 5 (by omega)
  have hqk : (q : ℤ) = 2 * (5 * k) - e := by rw [← hk]; linarith
  have hq5 : ¬ 5 ∣ q := by
    intro h
    obtain ⟨j, hj⟩ := h
    have hj' : (q : ℤ) = 5 * j := by exact_mod_cast hj
    rcases he with rfl | rfl <;> omega
  have hY5 : ¬ 5 ∣ Y := by
    intro h
    have h' : (5 : ℤ) ∣ (q : ℤ) - e := Int.natAbs_dvd_natAbs.mp (by simpa using h)
    obtain ⟨j, hj⟩ := h'
    rcases he with rfl | rfl <;> omega
  have hN0 : N ≠ 0 := by
    intro h
    apply hX
    have h' : (f₂ : ℤ) + e * δ₂ * q = 0 := Int.natAbs_eq_zero.mp h
    exact_mod_cast h'
  have hf₂0 : f₂ ≠ 0 := by omega
  have hf₄0 : f₄ ≠ 0 := by
    intro h
    rw [h] at hf₄
    rcases hδ with rfl | rfl <;> omega
  have hq0 : q ≠ 0 := by omega
  have hY0 : Y ≠ 0 := fun h => hY5 (h ▸ dvd_zero 5)
  have hGc0 : Gc ≠ 0 := by omega
  have hZ : ¬ 5 ∣ 4 * q ^ 2 * Y ^ 4 := by
    have h5p : Nat.Prime 5 := by norm_num
    have hc : Nat.Coprime 5 (4 * q ^ 2 * Y ^ 4) :=
      Nat.Coprime.mul_right (Nat.Coprime.mul_right (by norm_num)
        (((Nat.Prime.coprime_iff_not_dvd h5p).mpr hq5).pow_right 2))
        (((Nat.Prime.coprime_iff_not_dvd h5p).mpr hY5).pow_right 4)
    exact (Nat.Prime.coprime_iff_not_dvd h5p).mp hc
  have hZ0 : 4 * q ^ 2 * Y ^ 4 ≠ 0 := by positivity
  have hv := congrArg (padicValNat 5) hnat
  rw [show 4 * q ^ 2 * Y ^ 4 * 5 ^ a * (f₂ * f₄) = 5 ^ a * (f₂ * (f₄ * (4 * q ^ 2 * Y ^ 4))) by
    ring] at hv
  rw [padicValNat.mul hGc0 (pow_ne_zero _ hN0), padicValNat.pow N 2,
    padicValNat.mul (pow_ne_zero _ (by norm_num)) (by positivity), padicValNat.prime_pow,
    padicValNat.mul hf₂0 (by positivity), padicValNat.mul hf₄0 hZ0,
    padicValNat.eq_zero_of_not_dvd hZ] at hv
  have hGv : a + 1 ≤ padicValNat 5 Gc := (padicValNat_dvd_iff_le hGc0).mp hGa
  have hXnot : ∀ j : ℕ, (f₂ = 5 * j ∨ (f₄ : ℤ) = 5 * j) → ¬ 5 ∣ N := by
    intro j hj h
    have h' : (5 : ℤ) ∣ (f₂ : ℤ) + e * δ₂ * q := Int.natAbs_dvd_natAbs.mp (by simpa using h)
    obtain ⟨i, hi⟩ := h'
    rcases hj with hj | hj
    · have hj' : (f₂ : ℤ) = 5 * j := by exact_mod_cast hj
      rcases he with rfl | rfl <;> rcases hδ with rfl | rfl <;> simp only [hqk] at hi <;> omega
    · rcases he with rfl | rfl <;> rcases hδ with rfl | rfl <;> simp only [hqk] at hi <;> omega
  by_cases h2 : 5 ∣ f₂
  · left
    obtain ⟨j, hj⟩ := h2
    have h4 : ¬ 5 ∣ f₄ := by
      rintro ⟨i, hi⟩
      have hi' : (f₄ : ℤ) = 5 * i := by exact_mod_cast hi
      have hj' : (f₂ : ℤ) = 5 * j := by exact_mod_cast hj
      rcases hδ with rfl | rfl <;> omega
    have hN5 := hXnot j (Or.inl hj)
    rw [padicValNat.eq_zero_of_not_dvd hN5, padicValNat.eq_zero_of_not_dvd h4] at hv
    exact ⟨⟨j, hj⟩, h4, by omega⟩
  · right
    have hpos : 1 ≤ padicValNat 5 f₄ := by
      rw [padicValNat.eq_zero_of_not_dvd h2] at hv
      omega
    have h4 : 5 ∣ f₄ := by
      have := pow_padicValNat_dvd (p := 5) (n := f₄)
      exact (pow_dvd_pow 5 hpos).trans (by simpa using this)
    obtain ⟨j, hj⟩ := h4
    have hN5 := hXnot j (Or.inr (by exact_mod_cast hj))
    rw [padicValNat.eq_zero_of_not_dvd hN5, padicValNat.eq_zero_of_not_dvd h2] at hv
    exact ⟨⟨j, hj⟩, h2, by omega⟩

open CFSG.TwoRankLowerBound.Helpers in
theorem coefficientBlockDefect_of_torus_generator {G : Type} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 5] (χ : basis.index) {t w : G}
    (W D : Subgroup G) {a : ℕ} (hw : Subgroup.zpowers w = W) (htw : Commute t w)
    (ht2 : orderOf t = 2) (hWcard : Nat.card W = 5 ^ a)
    (hD : Subgroup.centralizer {t * w} = D) (hWD : W ≤ D) (hDcard : Nat.card D = 4 * 5 ^ a)
    (c : ℤ) (hc : ¬ (5 : ℤ) ∣ c) (hχ : (basis.representation χ).character (t * w) = c)
    (hv : padicValNat 5 D.index =
      padicValNat 5 (Module.finrank ℂ (basis.representation χ).vector)) :
    coefficientBlockDefect basis ideal 5 χ W := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hwo : orderOf w = 5 ^ a := by rw [← Nat.card_zpowers, hw, hWcard]
  have hWC : W ≤ Subgroup.centralizer {t * w} := hD ▸ hWD
  have hCcard : Nat.card (Subgroup.centralizer {t * w}) = 4 * 5 ^ a := by rw [hD, hDcard]
  have hPcard : Nat.card (W.subgroupOf (Subgroup.centralizer {t * w})) = 5 ^ a := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWC).toEquiv, hWcard]
  have hPp : IsPGroup 5 (W.subgroupOf (Subgroup.centralizer {t * w})) := IsPGroup.of_card hPcard
  have hidx : (W.subgroupOf (Subgroup.centralizer {t * w})).index = 4 := by
    have h := Subgroup.card_mul_index (W.subgroupOf (Subgroup.centralizer {t * w}))
    rw [hPcard, hCcard, mul_comm 4] at h
    exact Nat.eq_of_mul_eq_mul_left (pow_pos (by norm_num) a) h
  have hsylow : ∃ S : Sylow 5 (Subgroup.centralizer ({t * w} : Set G)),
      (S : Subgroup (Subgroup.centralizer ({t * w} : Set G))).map
        (Subgroup.centralizer ({t * w} : Set G)).subtype = Subgroup.zpowers w := by
    refine ⟨hPp.toSylow (by rw [hidx]; norm_num), ?_⟩
    rw [hw]
    change (W.subgroupOf _).map _ = W
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hWC]
  have hf0 : Module.finrank ℂ (basis.representation χ).vector ≠ 0 :=
    (basis_character_one basis χ).2.ne'
  have hI0 : D.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  obtain ⟨u, hu⟩ := exists_localized_unit_of_padicValNat_eq ideal 5 hI0 hf0 hv c hc
  have hunit : ∃ y : (localizedComplexIntegerRing ideal)ˣ,
      ((y : localizedComplexIntegerRing ideal) : ℂ) =
        ((Subgroup.centralizer ({t * w} : Set G)).index : ℂ) *
          (basis.representation χ).character (t * w) / (basis.representation χ).character 1 := by
    refine ⟨u, ?_⟩
    rw [hu, hD, hχ, (basis_character_one basis χ).1]
  have h := unit_class_scalar_force_exact_block_defect basis ideal 5 χ (t * w) w t htw.eq htw.symm
    ⟨a, hwo⟩ (by rw [ht2]; norm_num) hsylow hunit
  rwa [hw] at h

theorem exists_linear_character_orderOf_five {G : Type*} [Group G] (W : Subgroup G)
    [IsCyclic W] {a : ℕ} (ha : 1 ≤ a) (hWcard : Nat.card W = 5 ^ a) :
    ∃ lam : W →* ℂˣ, orderOf lam = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hcard : Nat.card (W →* ℂˣ) = 5 ^ a := by
    let : CommGroup W := IsCyclic.commGroup
    have : Finite W := Nat.finite_of_card_ne_zero (by rw [hWcard]; positivity)
    have : NeZero ((Nat.card W : ℕ) : ℂ) := ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
    obtain ⟨e⟩ := IsCyclic.monoidHom_equiv_self W ℂ
    exact (Nat.card_congr e.toEquiv).trans hWcard
  have : Finite (W →* ℂˣ) := Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  exact exists_prime_orderOf_dvd_card' 5 (by rw [hcard]; exact dvd_pow_self 5 (by omega))

theorem mem_of_index_eq_two_of_odd_orderOf {G : Type*} [Group G] {Y : Subgroup G}
    (hY : Y.index = 2) {y : G} (hy : Odd (orderOf y)) : y ∈ Y := by
  by_contra hyY
  have hpow : ∀ k : ℕ, y ^ k ∈ Y ↔ Even k := by
    intro k
    induction k with
    | zero => simp [Y.one_mem]
    | succ k ih =>
      rw [pow_succ, Subgroup.mul_mem_iff_of_index_two hY, ih, Nat.even_add_one]
      exact ⟨fun h hk => hyY (h.mp hk), fun h => ⟨fun hk => absurd hk h, fun h' => absurd h' hyY⟩⟩
  have h1 := (hpow (orderOf y)).mp (by rw [pow_orderOf_eq_one]; exact Y.one_mem)
  exact (Nat.not_even_iff_odd.mpr hy) h1

end CFSG.Semidihedral.Principal
