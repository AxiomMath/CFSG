module

public import CFSG.CharacterTheory.Semidihedral.AllPrimeLayerFacts
public import CFSG.CharacterTheory.Semidihedral.CentralKernelTorusSplitModel
public import CFSG.CharacterTheory.Semidihedral.FixedTorusDerived

public noncomputable section

namespace CFSG.Semidihedral.AllPrime

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.Semidihedral.EscapingLocalEigensubgroups
open CFSG.ABGTheoremB CFSG.ABGLocalTools CFSG.QuasiDihedralFusion
open scoped Pointwise

section Semidirect

variable {N Q : Type*} [Group N] [Group Q] [Finite N] [Finite Q] {φ : Q →* MulAut N}
  {r : ℕ} [Fact r.Prime]

private theorem finite_semidirect : Finite (N ⋊[φ] Q) :=
  Finite.of_equiv _ SemidirectProduct.equivProd.symm

private theorem exists_sylow_comap_inl (P : Sylow r (N ⋊[φ] Q)) :
    ∃ S : Sylow r N, ∀ n : N, n ∈ (S : Subgroup N) ↔
      (SemidirectProduct.inl n : N ⋊[φ] Q) ∈ (P : Subgroup (N ⋊[φ] Q)) := by
  have := finite_semidirect (N := N) (Q := Q) (φ := φ)
  let W' : Subgroup (N ⋊[φ] Q) := (SemidirectProduct.inl : N →* N ⋊[φ] Q).range
  have hW' : W'.Normal := by
    have h : W' = (SemidirectProduct.rightHom : N ⋊[φ] Q →* Q).ker :=
      SemidirectProduct.range_inl_eq_ker_rightHom
    rw [h]
    infer_instance
  have hPsyl : IsSylowOf r (P : Subgroup (N ⋊[φ] Q)) ⊤ := by
    rw [isSylowOf_iff, Subgroup.relIndex_top_right]
    exact ⟨le_top, P.isPGroup', P.not_dvd_index⟩
  have hPW := hPsyl.inf_of_le_normalizer le_top (Subgroup.normalizer_eq_top_iff.mpr hW').ge
  have hcardW : Nat.card W' = Nat.card N := by
    change Nat.card (SemidirectProduct.inl : N →* N ⋊[φ] Q).range = _
    rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective SemidirectProduct.inl_injective,
      Subgroup.card_top]
  have hmap : ((P : Subgroup (N ⋊[φ] Q)).comap SemidirectProduct.inl).map
      (SemidirectProduct.inl : N →* N ⋊[φ] Q) = (P : Subgroup (N ⋊[φ] Q)) ⊓ W' := by
    rw [Subgroup.map_comap_eq, inf_comm]
  have hcard : Nat.card ((P : Subgroup (N ⋊[φ] Q)).comap SemidirectProduct.inl) =
      r ^ (Nat.card N).factorization r := by
    rw [← Subgroup.card_map_of_injective (f := (SemidirectProduct.inl : N →* N ⋊[φ] Q))
      SemidirectProduct.inl_injective, hmap, hPW.card_eq, hcardW]
  exact ⟨Sylow.ofCard _ hcard, fun n => Iff.rfl⟩

private theorem semidirect_sylow_dichotomy (hN : ∀ a b : N, a * b = b * a)
    (hfaith : ∀ q : Q, orderOf q = r → ∀ S : Sylow r N,
      (∀ n ∈ (S : Subgroup N), φ q n = n) → (S : Subgroup N) = ⊥)
    (P : Sylow r (N ⋊[φ] Q)) :
    (∀ x ∈ (P : Subgroup (N ⋊[φ] Q)), (∀ y ∈ (P : Subgroup (N ⋊[φ] Q)), x * y = y * x) →
      x.right = 1) ∨
    (∀ y ∈ (P : Subgroup (N ⋊[φ] Q)), y.right = 1 → y = 1) := by
  have := finite_semidirect (N := N) (Q := Q) (φ := φ)
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨x, hxP, hxc, hxr⟩, ⟨y, hyP, hyr, hy1⟩⟩ := hcon
  obtain ⟨SN, hSN⟩ := exists_sylow_comap_inl P
  have hfix : ∀ n ∈ (SN : Subgroup N), φ x.right n = n := by
    intro n hn
    have h := hxc _ ((hSN n).mp hn)
    have hl := congrArg SemidirectProduct.left h
    simp only [SemidirectProduct.mul_left, SemidirectProduct.left_inl,
      SemidirectProduct.right_inl, map_one, MulAut.one_apply] at hl
    rw [hN n x.left] at hl
    exact mul_left_cancel hl
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp P.isPGroup' ⟨x, hxP⟩
  rw [Subgroup.orderOf_mk] at hk
  have hdvd : orderOf x.right ∣ r ^ k := by
    rw [← hk]
    exact orderOf_map_dvd (SemidirectProduct.rightHom : N ⋊[φ] Q →* Q) x
  obtain ⟨j, hjk, hj⟩ := (Nat.dvd_prime_pow (Fact.out : r.Prime)).mp hdvd
  have hj0 : j ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hj
    exact hxr hj
  have hq₁ : orderOf (x.right ^ r ^ (j - 1)) = r := by
    rw [orderOf_pow_of_dvd (pow_ne_zero _ (Fact.out : r.Prime).ne_zero)
      (by rw [hj]; exact pow_dvd_pow r (Nat.sub_le j 1)), hj,
      Nat.pow_div (Nat.sub_le j 1) (Fact.out : r.Prime).pos]
    rw [show j - (j - 1) = 1 by omega, pow_one]
  have hfix₁ : ∀ n ∈ (SN : Subgroup N), φ (x.right ^ r ^ (j - 1)) n = n := by
    intro n hn
    rw [map_pow]
    induction (r ^ (j - 1)) with
    | zero => rfl
    | succ m ih => rw [pow_succ, MulAut.mul_apply, hfix n hn, ih]
  have hbot := hfaith _ hq₁ SN hfix₁
  apply hy1
  have hy : y = SemidirectProduct.inl y.left := by
    apply SemidirectProduct.ext
    · rfl
    · exact hyr
  have hmem : y.left ∈ (SN : Subgroup N) := by
    rw [hSN, ← hy]
    exact hyP
  rw [hbot, Subgroup.mem_bot] at hmem
  rw [hy, hmem, map_one]

private theorem semidirect_sylow_conj (P : Sylow r (N ⋊[φ] Q))
    (hP : ∀ y ∈ (P : Subgroup (N ⋊[φ] Q)), y.right = 1 → y = 1) :
    ∃ (k : N ⋊[φ] Q) (Qr : Sylow r Q),
      (P : Subgroup (N ⋊[φ] Q)) =
        ((Qr : Subgroup Q).map SemidirectProduct.inr).map (MulAut.conj k).toMonoidHom := by
  have := finite_semidirect (N := N) (Q := Q) (φ := φ)
  obtain ⟨SN, hSN⟩ := exists_sylow_comap_inl P
  have hSN1 : (SN : Subgroup N) = ⊥ := by
    rw [eq_bot_iff]
    intro n hn
    have h := hP _ ((hSN n).mp hn) rfl
    rw [Subgroup.mem_bot]
    exact SemidirectProduct.inl_injective (h.trans (map_one _).symm)
  have hN0 : (Nat.card N).factorization r = 0 := by
    have h := SN.card_eq_multiplicity
    rw [hSN1, Subgroup.card_bot] at h
    exact (Nat.pow_eq_one.mp h.symm).resolve_left (Fact.out : r.Prime).one_lt.ne'
  obtain ⟨Qr⟩ : Nonempty (Sylow r Q) := inferInstance
  have hcardK : Nat.card (N ⋊[φ] Q) = Nat.card N * Nat.card Q := SemidirectProduct.card
  have hcard : Nat.card ((Qr : Subgroup Q).map (SemidirectProduct.inr : Q →* N ⋊[φ] Q)) =
      r ^ (Nat.card (N ⋊[φ] Q)).factorization r := by
    rw [Subgroup.card_map_of_injective SemidirectProduct.inr_injective, Qr.card_eq_multiplicity,
      hcardK, Nat.factorization_mul (Nat.card_pos (α := N)).ne' (Nat.card_pos (α := Q)).ne',
      Finsupp.add_apply, hN0, zero_add]
  let P₀ : Sylow r (N ⋊[φ] Q) := Sylow.ofCard _ hcard
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq (N ⋊[φ] Q) P₀ P
  refine ⟨k, Qr, ?_⟩
  rw [← hk, Sylow.coe_subgroup_smul]
  rfl

end Semidirect

private theorem isSylowOf_map_hom {X Y : Type*} [Group X] [Group Y] [Finite X] {r : ℕ}
    [Fact r.Prime] (ψ : X →* Y) {P K : Subgroup X} (h : IsSylowOf r P K) :
    IsSylowOf r (P.map ψ) (K.map ψ) := by
  obtain ⟨Q, rfl⟩ := h
  refine ⟨Q.mapSurjective (ψ.subgroupMap_surjective K), ?_⟩
  rw [Sylow.coe_mapSurjective, Subgroup.map_map, Subgroup.map_map]
  rfl

section Arithmetic

private theorem pow_mod_four_of_odd {x r : ℕ} (hx : Odd x) (hr : Odd r) : x ^ r % 4 = x % 4 := by
  obtain ⟨k, rfl⟩ := hr
  have h2 : x ^ 2 % 4 = 1 := by
    obtain ⟨m, rfl⟩ := hx
    have : (2 * m + 1) ^ 2 = 4 * (m * m + m) + 1 := by ring
    rw [this]
    omega
  rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod, h2, one_pow]
  omega

private theorem padicValNat_half {r m : ℕ} [Fact r.Prime] (hr2 : r ≠ 2) (hm : m % 4 = 2) :
    padicValNat r (m / 2) = padicValNat r m := by
  have hm2 : m = 2 * (m / 2) := by omega
  have hne : m / 2 ≠ 0 := by omega
  have h2 : padicValNat r 2 = 0 := padicValNat.eq_zero_of_not_dvd fun h =>
    hr2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : r.Prime) Nat.prime_two).mp h)
  conv_rhs => rw [hm2]
  rw [padicValNat.mul two_ne_zero hne, h2, zero_add]

private theorem factorization_torusSize_pow {r x : ℕ} [Fact r.Prime] (hr2 : r ≠ 2) (hx : Odd x)
    (hx3 : 3 ≤ x)
    (h : r ^ (MatrixTorus.torusSize (x ^ r) / 2).factorization r ∣
      MatrixTorus.torusSize x / 2) :
    (MatrixTorus.torusSize (x ^ r) / 2).factorization r = 0 := by
  have hr : r.Prime := Fact.out
  have hrodd : Odd r := hr.eq_two_or_odd'.resolve_left hr2
  have hmod := pow_mod_four_of_odd hx hrodd
  have hxr1 : 1 ≤ x ^ r := Nat.one_le_pow _ _ (by omega)
  have hT := MatrixTorus.torusSize_mod_four (hx.pow (n := r))
  have hT₀ := MatrixTorus.torusSize_mod_four hx
  rw [Nat.factorization_def _ hr] at h ⊢
  rw [padicValNat_half hr2 hT] at h ⊢
  by_contra hv
  have hT0 : MatrixTorus.torusSize x / 2 ≠ 0 := by omega
  have hle := (padicValNat_dvd_iff_le hT0).mp h
  rw [padicValNat_half hr2 hT₀] at hle
  have hdvdT : r ∣ MatrixTorus.torusSize (x ^ r) := dvd_of_one_le_padicValNat (by omega)
  unfold MatrixTorus.torusSize at hdvdT hle hv
  by_cases h1 : x % 4 = 1
  · rw [ite_eq_left (hmod.trans h1)] at hdvdT hle hv
    rw [ite_eq_left h1] at hle
    have hx1 : r ∣ x + 1 := by
      have hz : ((x ^ r + 1 : ℕ) : ZMod r) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdvdT
      push_cast at hz
      rw [ZMod.pow_card] at hz
      exact (ZMod.natCast_eq_zero_iff _ _).mp (by push_cast; exact hz)
    have hnx : ¬ r ∣ x := fun hx' =>
      hr.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right hx').mp hx1))
    have hlte := padicValNat.pow_add_pow (x := x) (y := 1) hrodd (by simpa using hx1) hnx hrodd
    rw [one_pow, padicValNat_self] at hlte
    omega
  · have h3 : x % 4 = 3 := by
      have := Nat.odd_iff.mp hx
      omega
    rw [ite_eq_right (show ¬ x ^ r % 4 = 1 by omega)] at hdvdT hle hv
    rw [ite_eq_right h1] at hle
    have hx1 : r ∣ x - 1 := by
      have hz : ((x ^ r - 1 : ℕ) : ZMod r) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdvdT
      rw [Nat.cast_sub hxr1] at hz
      push_cast at hz
      rw [ZMod.pow_card] at hz
      exact (ZMod.natCast_eq_zero_iff _ _).mp (by rw [Nat.cast_sub (by omega)]; push_cast; exact hz)
    have hnx : ¬ r ∣ x := by
      intro hx'
      have h' : r ∣ x - (x - 1) := Nat.dvd_sub hx' hx1
      rw [show x - (x - 1) = 1 by omega] at h'
      exact hr.one_lt.ne' (Nat.dvd_one.mp h')
    have hlte := padicValNat.pow_sub_pow (x := x) (y := 1) hrodd (by omega) hx1 hnx hr.ne_zero
    rw [one_pow, padicValNat_self] at hlte
    omega

end Arithmetic

section Torus

variable (F : Type) [Field F] [Finite F] (A : Subgroup (F ≃+* F)) (b : Fˣ)
  (hfix : ∀ sigma : A, (sigma : F ≃+* F) (b : F) = b)

private theorem torus_sylow_eq_bot_of_fixed {p f : ℕ} (hp : p.Prime) (hpodd : Odd p)
    (hf : 1 ≤ f) (hcard : Nat.card F = p ^ f) (hA : Odd (Nat.card A)) (hb : ¬IsSquare b)
    {r : ℕ} [Fact r.Prime] (hr2 : r ≠ 2) (σ : A) (hσ : orderOf σ = r)
    (S : Sylow r (MatrixTorus.W F b))
    (hS : ∀ X ∈ (S : Subgroup (MatrixTorus.W F b)),
      ActualFourGroupCentralizer.originalWAction F A b hfix σ X = X) :
    (S : Subgroup (MatrixTorus.W F b)) = ⊥ := by
  obtain ⟨-, -, -, hWcard, -, -, hsig, -⟩ :=
    FixedTorusDerived.odd_field_fixed_torus_derived_subgroup_has_exact_torus_centralizer F hp hpodd
      hf hcard A hA b hb hfix
  obtain ⟨hdvd, -, hpow, hfixcard, -⟩ := hsig σ
  rw [hσ] at hdvd hpow hfixcard
  set x := p ^ (f / r) with hx
  have hr : r.Prime := Fact.out
  have hrodd : Odd r := hr.eq_two_or_odd'.resolve_left hr2
  have hxodd : Odd x := hpodd.pow
  have hx3 : 3 ≤ x := by
    have hp3 : 3 ≤ p := by
      have := hp.two_le
      have := Nat.odd_iff.mp hpodd
      omega
    have hfr : 1 ≤ f / r := Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) hr.pos
    calc 3 ≤ p := hp3
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ x := Nat.pow_le_pow_right (by omega) hfr
  let Fix : Subgroup (MatrixTorus.W F b) :=
    { carrier := {X | ActualFourGroupCentralizer.originalWAction F A b hfix σ X = X}
      mul_mem' := fun {X Y} hX hY => by
        simp only [Set.mem_ofPred_eq] at hX hY ⊢
        rw [map_mul, hX, hY]
      one_mem' := map_one _
      inv_mem' := fun {X} hX => by
        simp only [Set.mem_ofPred_eq] at hX ⊢
        rw [map_inv, hX] }
  have hFix : Nat.card Fix = MatrixTorus.torusSize x / 2 := by
    have h : Nat.card Fix = Nat.card {X : MatrixTorus.W F b //
        FixedTorusDerived.torusFieldAction F b A hfix σ X = X} := rfl
    rw [h, hfixcard, hpow, pow_mod_four_of_odd hxodd hrodd]
    rfl
  have hle : (S : Subgroup (MatrixTorus.W F b)) ≤ Fix := fun X hX => hS X hX
  have hSdvd := Subgroup.card_dvd_of_le hle
  rw [hFix, S.card_eq_multiplicity, hWcard, hpow] at hSdvd
  have h0 := factorization_torusSize_pow hr2 hxodd hx3 hSdvd
  have hS1 : Nat.card (S : Subgroup (MatrixTorus.W F b)) = 1 := by
    rw [S.card_eq_multiplicity, hWcard, hpow, h0, pow_zero]
  exact Subgroup.eq_bot_of_card_eq _ hS1

end Torus

section Model

variable {G : Type} [Group G]

private theorem frontierSetting_C_eq {n : ℕ} (S : Sylow 2 G)
    (fS : SemidihedralGroup n ≃* (S : Subgroup G)) (t : G) (p f : ℕ) (sC : C t)
    (hsC : (sC : G) = (fS (s n) : G)) :
    (frontierSetting S fS t p f).C =
      (Subgroup.centralizer ({sC} : Set (C t))).map (C t).subtype := by
  ext g
  change g ∈ Subgroup.centralizer (Subgroup.closure ({t, (fS (s n) : G)} : Set G) : Set G) ↔ _
  rw [Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
  constructor
  · intro h
    have hgt : g ∈ C t :=
      Subgroup.mem_centralizer_singleton_iff.mpr (h t (Set.mem_insert _ _)).symm
    refine ⟨⟨g, hgt⟩, Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext ?_), rfl⟩
    change g * (sC : G) = (sC : G) * g
    rw [hsC]
    exact (h _ (Set.mem_insert_of_mem _ rfl)).symm
  · rintro ⟨c, hc, rfl⟩ x hx
    rcases hx with rfl | rfl
    · exact (Subgroup.mem_centralizer_singleton_iff.mp c.2).symm
    · rw [← hsC]
      exact (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hc)).symm

private theorem frontier_torus_model [Finite G] [IsSimpleGroup G]
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    {n : ℕ} (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    {p f : ℕ} (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (sC : C t) (hsC : (sC : G) = (fS (s n) : G)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (A : Subgroup (F ≃+* F)) (b : Fˣ)
      (hfix : ∀ σ : A, (σ : F ≃+* F) (b : F) = b)
      (Psi : MatrixTorus.OriginalH F b A hfix ≃* H t),
      Nat.card F = p ^ f ∧ Odd (Nat.card A) ∧ ¬IsSquare b ∧
      (CFSG.generalizedFitting (Gamma t)).comap (barKappa t) =
        (MatrixTorus.originalSlInH F b A hfix).range.map Psi.toMonoidHom ∧
      (Psi.toMonoidHom.comp (ActualFourGroupCentralizer.originalOddInclusion F A b hfix)).range =
        ((KleinFourOddKernel.oddKernel sC).map
          (KleinFourOddKernel.centralizer sC).subtype).map (nu t) ∧
      ∀ x ∈ KleinFourOddKernel.centralizer sC, Odd (orderOf x) →
        x ∈ (KleinFourOddKernel.oddKernel sC).map (KleinFourOddKernel.centralizer sC).subtype := by
  obtain ⟨-, ht2, -, -, hs2, hst⟩ := CFSG.Semidihedral.Principal.supplied_t_s_facts hn fS ht
  have hG := CFSG.Semidihedral.Principal.index_ne_two_of_isSimpleGroup hGnonab
  have hsC2 : orderOf sC = 2 := by rw [← Subgroup.orderOf_coe, hsC]; exact hs2
  have hsCt : sC ≠ tInC t := fun h => hst (by rw [← hsC, h]; rfl)
  obtain ⟨-, F, hF, hFfin, A, a, hFcard, hAodd, -, -, -, -, -, haF, -, -, -, hall⟩ :=
    ActualFourGroupCentralizer.actual_simple_layer_four_group_centralizer_odd_core n hn S fS hG t
      ht2 hnonab hcentral hnc p f hp hpodd hf hmodel
  obtain ⟨Psi, -, -, hdata, -, -, -, -⟩ := hall sC hsC2 hsCt
  set b := MatrixCover.fixedUnit F A a with hbdef
  have hfix : ∀ σ : A, (σ : F ≃+* F) (b : F) = b :=
    ActualFourGroupCentralizer.fixed_coefficient_action F A a
  refine ⟨F, hF, hFfin, A, b, hfix, Psi, hFcard, hAodd, haF, ?_, ?_, ?_⟩
  ·
    obtain ⟨-, -, -, hAutcyc, -, -⟩ :=
      SemilinearOuterQuotient.odd_field_projective_semilinear_exact_outer_quotient F hp hpodd hf
        hFcard
    have : IsCyclic (F ≃+* F) := hAutcyc
    have hAcyc : IsCyclic A := Subgroup.isCyclic A
    have hAcomm : ∀ σ τ : A, σ * τ = τ * σ := by
      obtain ⟨g, hg⟩ := hAcyc.exists_generator
      intro σ τ
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg σ)
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg τ)
      exact (Commute.zpow_zpow_self g i j).eq
    obtain ⟨F', hF', hF'fin, _A', _rho', data'⟩ :=
      actual_simple_layer_matrix_data n hn S fS hG t ht2 hnonab hcentral hnc p f hp hpodd hf
        hmodel
    obtain ⟨eta', -, -, -⟩ := data'.compatible_layer
    set T₀ := (CFSG.generalizedFitting (Gamma t)).comap (barKappa t) with hT₀def
    have hT₀perf : Group.IsPerfect T₀ := by
      have : Fintype F' := Fintype.ofFinite F'
      have h4 : ∃ u : Finset F', u.card = 4 := by
        obtain ⟨u, -, hu⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset F'))
          (n := 4) (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card, data'.field_card]; omega)
        exact ⟨u, hu⟩
      have := CFSG.LinearGroups.special_linear_dimension_two_perfect h4
      exact Group.IsPerfect.ofSurjective (f := eta'.symm.toMonoidHom) eta'.symm.surjective
    have hcommH : commutator (H t) =
        (commutator (MatrixTorus.OriginalH F b A hfix)).map Psi.toMonoidHom := by
      rw [commutator_def, commutator_def, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective _ Psi.surjective]
    have hT₀le : T₀ ≤ (MatrixTorus.originalSlInH F b A hfix).range.map Psi.toMonoidHom :=
      calc T₀ = ⁅T₀, T₀⁆ := (Subgroup.isPerfect_iff.mp hT₀perf).symm
        _ ≤ commutator (H t) := Subgroup.commutator_mono le_top le_top
        _ = (commutator (MatrixTorus.OriginalH F b A hfix)).map Psi.toMonoidHom := hcommH
        _ ≤ (MatrixTorus.originalSlInH F b A hfix).range.map Psi.toMonoidHom :=
          Subgroup.map_mono
            (CentralKernelTorusSplit.commutator_le_originalSlInH_range F b A hfix hAcomm)
    have hcardT₀ : Nat.card ((MatrixTorus.originalSlInH F b A hfix).range.map
        Psi.toMonoidHom) ≤ Nat.card T₀ := by
      rw [Subgroup.card_map_of_injective Psi.injective, Nat.card_congr eta'.toEquiv,
        ← Nat.card_congr (MonoidHom.ofInjective
          (MatrixFourGroupNormalizer.originalSlInH_injective F b A hfix)).toEquiv]
      exact (CentralKernelTorusSplit.card_SL_two_congr
        (hFcard.trans data'.field_card.symm)).le
    exact Subgroup.eq_of_le_of_card_ge hT₀le hcardT₀
  ·
    obtain ⟨g, hgsurj, -, hgval⟩ := hdata.lifted.restricted_quotient
    rw [← hdata.odd_factor_range]
    apply le_antisymm
    · intro y hy
      obtain ⟨ρ, hρ⟩ := hgsurj ⟨y, hy⟩
      have hy' : (g ρ : H t) = y := congrArg Subtype.val hρ
      refine ⟨_, ⟨ρ, ρ.2, rfl⟩, ?_⟩
      rw [← hy', hgval]
      rfl
    · rintro _ ⟨_, ⟨ρ, hρ, rfl⟩, rfl⟩
      have h := (g ⟨ρ, hρ⟩).2
      rw [hgval] at h
      exact h
  ·
    intro x hx hodd
    obtain ⟨e, he⟩ := hdata.lifted.direct_equiv
    have hK := hdata.lifted.klein_four
    set x' : KleinFourOddKernel.centralizer sC := ⟨x, hx⟩ with hx'def
    set y := e.symm x' with hydef
    have hord : orderOf y = orderOf x := by
      rw [hydef, MulEquiv.orderOf_eq, hx'def, Subgroup.orderOf_mk]
    have hpow : y.1 ^ orderOf x = 1 := by
      have h := congrArg Prod.fst (pow_orderOf_eq_one y)
      rwa [Prod.pow_fst, hord, Prod.fst_one] at h
    have hv2 : y.1 ^ 2 = 1 := by
      rw [← hK.exponent_two]
      exact Monoid.pow_exponent_eq_one _
    have hv1 : y.1 = 1 := by
      have h := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hpow) (orderOf_dvd_of_pow_eq_one hv2)
      rw [Nat.Coprime.gcd_eq_one hodd.coprime_two_right] at h
      exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h)
    have hxval : x = ((y.2 : KleinFourOddKernel.centralizer sC) : C t) := by
      have h := he y.1 y.2
      rw [Prod.mk.eta, hydef, MulEquiv.apply_symm_apply, hv1, OneMemClass.coe_one,
        one_mul] at h
      exact h
    exact ⟨y.2, y.2.2, hxval.symm⟩

private theorem frontier_sylow_model [Finite G] [IsSimpleGroup G]
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    {n : ℕ} (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    {p f : ℕ} (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2) (P : Subgroup G)
    (hP : IsSylowOf ℓ P (frontierSetting S fS t p f).C) :
    P ≤ C t ∧
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (A : Subgroup (F ≃+* F)) (b : Fˣ)
      (hfix : ∀ σ : A, (σ : F ≃+* F) (b : F) = b)
      (Psi : MatrixTorus.OriginalH F b A hfix ≃* H t)
      (Q : Sylow ℓ (ActualFourGroupCentralizer.OriginalWProduct F A b hfix)),
      Nat.card F = p ^ f ∧ Odd (Nat.card A) ∧ ¬IsSquare b ∧
      (CFSG.generalizedFitting (Gamma t)).comap (barKappa t) =
        (MatrixTorus.originalSlInH F b A hfix).range.map Psi.toMonoidHom ∧
      (P.subgroupOf (C t)).map (nu t) ≤
        (Psi.toMonoidHom.comp (ActualFourGroupCentralizer.originalOddInclusion F A b hfix)).range ∧
      ∀ x, x ∈ (Q : Subgroup (ActualFourGroupCentralizer.OriginalWProduct F A b hfix)) ↔
        Psi (ActualFourGroupCentralizer.originalOddInclusion F A b hfix x) ∈
          (P.subgroupOf (C t)).map (nu t) := by
  obtain ⟨-, -, -, hsC, -, -⟩ := CFSG.Semidihedral.Principal.supplied_t_s_facts hn fS ht
  set sC : C t := ⟨(fS (s n) : G), hsC⟩ with hsCdef
  have hCeq := frontierSetting_C_eq S fS t p f sC rfl
  have hPC : P ≤ C t := by
    intro g hg
    have h := hP.le hg
    rw [hCeq] at h
    obtain ⟨c, -, rfl⟩ := h
    exact c.2
  refine ⟨hPC, ?_⟩
  obtain ⟨F, hF, hFfin, A, b, hfix, Psi, hFcard, hAodd, hb, hlayer, hrange, hodd⟩ :=
    frontier_torus_model hGnonab hn S fS t ht hnonab hcentral hnc hp hpodd hf hq hmodel sC rfl
  have hPCmap : (P.subgroupOf (C t)).map (C t).subtype = P := map_subgroupOf_C_subtype t hPC
  have hPD : IsSylowOf ℓ (P.subgroupOf (C t)) (KleinFourOddKernel.centralizer sC) := by
    rw [← isSylowOf_map_subtype_iff (C t), hPCmap]
    change IsSylowOf ℓ P ((Subgroup.centralizer ({sC} : Set (C t))).map (C t).subtype)
    rw [← hCeq]
    exact hP
  have hPR : P.subgroupOf (C t) ≤
      (KleinFourOddKernel.oddKernel sC).map (KleinFourOddKernel.centralizer sC).subtype := by
    intro x hx
    apply hodd x (hPD.le hx)
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hPD.isPGroup ⟨x, hx⟩
    rw [Subgroup.orderOf_mk] at hk
    rw [hk]
    exact ((Fact.out : ℓ.Prime).eq_two_or_odd'.resolve_left hℓ2).pow
  have hPB := isSylowOf_map_hom (nu t) (hPD.of_le hPR (Subgroup.map_subtype_le _))
  rw [← hrange] at hPB
  have hPBle := hPB.le
  set ι := Psi.toMonoidHom.comp (ActualFourGroupCentralizer.originalOddInclusion F A b hfix)
    with hιdef
  have hι : Function.Injective ι :=
    Psi.injective.comp (ActualFourGroupCentralizer.originalOddInclusion_injective F A b hfix)
  obtain ⟨QB, hQB⟩ := hPB
  let e : ActualFourGroupCentralizer.OriginalWProduct F A b hfix ≃* ι.range :=
    MonoidHom.ofInjective hι
  have hesurj : Function.Surjective e.symm.toMonoidHom := e.symm.surjective
  refine ⟨F, hF, hFfin, A, b, hfix, Psi, QB.mapSurjective hesurj, hFcard, hAodd, hb,
    hlayer, hPBle, fun x => ?_⟩
  rw [Sylow.coe_mapSurjective, Subgroup.mem_map_equiv, MulEquiv.symm_symm, ← hQB]
  exact (Subgroup.mem_map_iff_mem ι.range.subtype_injective).symm

private theorem inr_conj_originalSlInH (F : Type) [Field F] (A : Subgroup (F ≃+* F)) (b : Fˣ)
    (hfix : ∀ σ : A, (σ : F ≃+* F) (b : F) = b) (q : A) (X : MatrixCoverData.SL F) :
    (SemidirectProduct.inr q : MatrixTorus.OriginalH F b A hfix) *
        MatrixTorus.originalSlInH F b A hfix X * (SemidirectProduct.inr q)⁻¹ =
      MatrixTorus.originalSlInH F b A hfix
        (Matrix.SpecialLinearGroup.map (q : F ≃+* F).toRingHom X) := by
  change (SemidirectProduct.inr q : MatrixTorus.OriginalH F b A hfix) *
      SemidirectProduct.inl (MatrixCoverData.inclusion F b X) * (SemidirectProduct.inr q)⁻¹ =
    SemidirectProduct.inl (MatrixCoverData.inclusion F b
      (Matrix.SpecialLinearGroup.map (q : F ≃+* F).toRingHom X))
  rw [← map_inv, ← SemidirectProduct.inl_aut]
  rfl

private theorem originalSlInH_commute_inr_iff (F : Type) [Field F] (A : Subgroup (F ≃+* F))
    (b : Fˣ) (hfix : ∀ σ : A, (σ : F ≃+* F) (b : F) = b) (q : A) (X : MatrixCoverData.SL F) :
    MatrixTorus.originalSlInH F b A hfix X * SemidirectProduct.inr q =
        SemidirectProduct.inr q * MatrixTorus.originalSlInH F b A hfix X ↔
      Matrix.SpecialLinearGroup.map (q : F ≃+* F).toRingHom X = X := by
  rw [← (MatrixFourGroupNormalizer.originalSlInH_injective F b A hfix).eq_iff,
    ← inr_conj_originalSlInH, mul_inv_eq_iff_eq_mul, eq_comm]

private theorem frontier_mem_layer_of_odd {n : ℕ} (hn : 4 ≤ n) (S : Sylow 2 G)
    (fS : SemidihedralGroup n ≃* (S : Subgroup G)) (t : G)
    (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2)) (p f : ℕ) (c : C t)
    (hcL : (c : G) ∈ (frontierSetting S fS t p f).L) (hodd : Odd (orderOf c)) :
    c ∈ localLayerPreimage t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := localLayerPreimage_normal t
  have hSC := frontier_S_le_C hn S fS t ht p f
  have hL : (frontierSetting S fS t p f).L =
      (localLayerPreimage t ⊔ (S : Subgroup G).subgroupOf (C t)).map (C t).subtype := by
    rw [Subgroup.map_sup, map_subgroupOf_C_subtype t hSC]
    rfl
  rw [hL] at hcL
  replace hcL := (Subgroup.mem_map_iff_mem (C t).subtype_injective).mp hcL
  let π := QuotientGroup.mk' (localLayerPreimage t)
  have hmap : (localLayerPreimage t ⊔ (S : Subgroup G).subgroupOf (C t)).map π =
      ((S : Subgroup G).subgroupOf (C t)).map π := by
    rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq]
  have hπc : π c ∈ ((S : Subgroup G).subgroupOf (C t)).map π := hmap ▸ ⟨c, hcL, rfl⟩
  have h2 : IsPGroup 2 (((S : Subgroup G).subgroupOf (C t)).map π) :=
    (S.isPGroup'.comap_subtype (K := C t)).map π
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp h2 ⟨π c, hπc⟩
  rw [Subgroup.orderOf_mk] at hk
  have hdvd : orderOf (π c) ∣ orderOf c := orderOf_map_dvd π c
  have h1 : orderOf (π c) = 1 := by
    rw [hk] at hdvd ⊢
    rcases k with _ | k
    · rfl
    · exact absurd (even_iff_two_dvd.mpr ((dvd_pow_self 2 (Nat.succ_ne_zero k)).trans hdvd))
        (Nat.not_even_iff_odd.mpr hodd)
  rwa [orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1

end Model

theorem frontier_II42v {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f) :
    ∀ r : ℕ, r.Prime → r ∣ Nat.card (frontierSetting S fS t p f).ON → ∀ P : Subgroup G,
      IsSylowOf r P (frontierSetting S fS t p f).C →
      (frontierSetting S fS t p f).D ≤ Subgroup.normalizer (P : Set G) →
      centerOf P ≤ (frontierSetting S fS t p f).L ∨
        P ⊓ (frontierSetting S fS t p f).L ≤ (frontierSetting S fS t p f).ON := by
  intro ℓ hℓ hℓON P hP _
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hℓ2 : ℓ ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr (frontierSetting S fS t p f).odd_card_ON)
      (even_iff_two_dvd.mpr hℓON)
  obtain ⟨hPC, F, hF, hFfin, A, b, hfix, Psi, Q, hFcard, hAodd, hb, hlayer, hPle, hQ⟩ :=
    frontier_sylow_model hGnonab hn S fS t ht hnonab hcentral hnc hp hpodd hf hq hmodel hℓ2 P hP
  set ι := Psi.toMonoidHom.comp (ActualFourGroupCentralizer.originalOddInclusion F A b hfix)
    with hιdef
  have hι : Function.Injective ι :=
    Psi.injective.comp (ActualFourGroupCentralizer.originalOddInclusion_injective F A b hfix)
  have hlay : ∀ x, ι x ∈ (CFSG.generalizedFitting (Gamma t)).comap (barKappa t) ↔
      x.right = 1 := by
    intro x
    rw [hlayer]
    exact (Subgroup.mem_map_iff_mem (f := Psi.toMonoidHom) Psi.injective).trans
      (CentralKernelTorusSplit.originalOddInclusion_mem_range_iff F b A hfix x)
  have hQ' : ∀ x, x ∈ (Q : Subgroup _) ↔ ι x ∈ (P.subgroupOf (C t)).map (nu t) := hQ
  have hcodd : ∀ c : C t, (c : G) ∈ P → Odd (orderOf c) := by
    intro c hc
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hP.isPGroup ⟨c, hc⟩
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe] at hk
    rw [hk]
    exact (hℓ.eq_two_or_odd'.resolve_left hℓ2).pow
  rcases semidirect_sylow_dichotomy (FixedTorusDerived.W_mul_comm F b)
      (fun σ hσ S' hS' => torus_sylow_eq_bot_of_fixed F A b hfix hp hpodd hf hFcard hAodd hb hℓ2
        σ hσ S' hS') Q with hZ | hW
  · left
    rintro g ⟨hgP, hgcent⟩
    have hgC : g ∈ C t := hPC hgP
    have hbar : nu t ⟨g, hgC⟩ ∈ (P.subgroupOf (C t)).map (nu t) := ⟨⟨g, hgC⟩, hgP, rfl⟩
    obtain ⟨x, hx⟩ := hPle hbar
    have hxQ : x ∈ (Q : Subgroup _) := (hQ' x).mpr (hx ▸ hbar)
    have hxc : ∀ y ∈ (Q : Subgroup _), x * y = y * x := by
      intro y hy
      obtain ⟨c', hc', hc'y⟩ := (hQ' y).mp hy
      apply hι
      rw [map_mul, map_mul, hx, ← hc'y, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hgcent _ hc').symm
    have hmem : nu t ⟨g, hgC⟩ ∈ (CFSG.generalizedFitting (Gamma t)).comap (barKappa t) := by
      rw [← hx]
      exact (hlay x).mpr (hZ x hxQ hxc)
    exact Subgroup.mem_sup_left ⟨⟨g, hgC⟩, hmem, rfl⟩
  · right
    rintro g ⟨hgP, hgL⟩
    have hgC : g ∈ C t := hPC hgP
    have hcY := frontier_mem_layer_of_odd hn S fS t ht p f ⟨g, hgC⟩ hgL (hcodd ⟨g, hgC⟩ hgP)
    have hbar : nu t ⟨g, hgC⟩ ∈ (P.subgroupOf (C t)).map (nu t) := ⟨⟨g, hgC⟩, hgP, rfl⟩
    obtain ⟨x, hx⟩ := hPle hbar
    have hxQ : x ∈ (Q : Subgroup _) := (hQ' x).mpr (hx ▸ hbar)
    have hr1 : x.right = 1 := (hlay x).mp (by rw [hx]; exact hcY)
    have hc1 : nu t ⟨g, hgC⟩ = 1 := by rw [← hx, hW x hxQ hr1, map_one]
    rw [frontierSetting_ON]
    exact ⟨⟨g, hgC⟩, (QuotientGroup.eq_one_iff _).mp hc1, rfl⟩

theorem frontier_II42vi {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f) :
    ∀ r : ℕ, r.Prime → r ∣ Nat.card (frontierSetting S fS t p f).ON → ∀ P : Subgroup G,
      IsSylowOf r P (frontierSetting S fS t p f).C →
      (frontierSetting S fS t p f).D ≤ Subgroup.normalizer (P : Set G) →
      ¬ centerOf P ≤ (frontierSetting S fS t p f).L₀ →
      P ⊓ (frontierSetting S fS t p f).L ≤ (frontierSetting S fS t p f).ON →
        ∃ Λ : Subgroup G, (∀ l : G, l ∈ Λ ↔ l ∈ (frontierSetting S fS t p f).L₀ ∧
            ∀ g ∈ P, g * l * g⁻¹ * l⁻¹ ∈ (frontierSetting S fS t p f).ON) ∧
          ∃ (F₀ : Type) (_ : Field F₀) (_ : Finite F₀) (m : ℕ), 1 < m ∧ Odd m ∧
            (frontierSetting S fS t p f).q = Nat.card F₀ ^ m ∧
            ∃ φ : Λ →* Matrix.SpecialLinearGroup (Fin 2) F₀,
              Function.Surjective φ ∧ φ.ker = (frontierSetting S fS t p f).ON.subgroupOf Λ := by
  intro ℓ hℓ hℓON P hP _ hZ hPL
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hℓ2 : ℓ ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr (frontierSetting S fS t p f).odd_card_ON)
      (even_iff_two_dvd.mpr hℓON)
  obtain ⟨hPC, F, hF, hFfin, A, b, hfix, Psi, Q, hFcard, hAodd, hb, hlayer, hPle, hQ⟩ :=
    frontier_sylow_model hGnonab hn S fS t ht hnonab hcentral hnc hp hpodd hf hq hmodel hℓ2 P hP
  set ι := Psi.toMonoidHom.comp (ActualFourGroupCentralizer.originalOddInclusion F A b hfix)
    with hιdef
  have hι : Function.Injective ι :=
    Psi.injective.comp (ActualFourGroupCentralizer.originalOddInclusion_injective F A b hfix)
  have hlay : ∀ x, ι x ∈ (CFSG.generalizedFitting (Gamma t)).comap (barKappa t) ↔
      x.right = 1 := by
    intro x
    rw [hlayer]
    exact (Subgroup.mem_map_iff_mem (f := Psi.toMonoidHom) Psi.injective).trans
      (CentralKernelTorusSplit.originalOddInclusion_mem_range_iff F b A hfix x)
  have hQ' : ∀ x, x ∈ (Q : Subgroup _) ↔ ι x ∈ (P.subgroupOf (C t)).map (nu t) := hQ
  have hW : ∀ y ∈ (Q : Subgroup (ActualFourGroupCentralizer.OriginalWProduct F A b hfix)),
      y.right = 1 → y = 1 := by
    intro y hy hy1
    obtain ⟨c, hc, hcy⟩ := (hQ' y).mp hy
    have hcY : nu t c ∈ (CFSG.generalizedFitting (Gamma t)).comap (barKappa t) := by
      rw [hcy]
      exact (hlay y).mpr hy1
    have hcON := hPL ⟨hc, Subgroup.mem_sup_left ⟨c, hcY, rfl⟩⟩
    rw [frontierSetting_ON] at hcON
    have hcN : c ∈ N t := (Subgroup.mem_map_iff_mem (C t).subtype_injective).mp hcON
    apply hι
    rw [map_one, ← hcy]
    exact (QuotientGroup.eq_one_iff c).mpr hcN
  obtain ⟨k, Qr, hQr⟩ := semidirect_sylow_conj Q hW
  set c₀ : H t := ι k with hc₀
  have hPbar : ∀ y, y ∈ (P.subgroupOf (C t)).map (nu t) ↔
      ∃ q ∈ (Qr : Subgroup A), y = c₀ * Psi (SemidirectProduct.inr q) * c₀⁻¹ := by
    intro y
    constructor
    · intro hy
      obtain ⟨x, rfl⟩ := hPle hy
      have hxQ : x ∈ (Q : Subgroup _) := (hQ' x).mpr hy
      rw [hQr] at hxQ
      obtain ⟨_, ⟨q, hq, rfl⟩, rfl⟩ := hxQ
      refine ⟨q, hq, ?_⟩
      change ι (k * SemidirectProduct.inr q * k⁻¹) = _
      rw [map_mul, map_mul, map_inv]
      rfl
    · rintro ⟨q, hq, rfl⟩
      have hx : k * SemidirectProduct.inr q * k⁻¹ ∈ (Q : Subgroup _) := by
        rw [hQr]
        exact ⟨_, ⟨q, hq, rfl⟩, rfl⟩
      have h := (hQ' _).mp hx
      rw [map_mul, map_mul, map_inv] at h
      exact h
  set Qr₀ : Subgroup (F ≃+* F) := (Qr : Subgroup A).map A.subtype with hQr₀def
  have hQr₀mem : ∀ q : A, q ∈ (Qr : Subgroup A) → (q : F ≃+* F) ∈ Qr₀ :=
    fun q hq => ⟨q, hq, rfl⟩
  have hmodd : Odd (Nat.card Qr₀) :=
    hAodd.of_dvd_nat (Subgroup.card_dvd_of_le (Subgroup.map_subtype_le _))
  set Y := (CFSG.generalizedFitting (Gamma t)).comap (barKappa t) with hYdef
  have hYn : Y.Normal := by
    have := SemilinearLayerModel.generalizedFitting_normal (Gamma t)
    exact Subgroup.Normal.comap inferInstance _
  set Pbar := (P.subgroupOf (C t)).map (nu t) with hPbardef
  let j : Matrix.SpecialLinearGroup (Fin 2) (FixedPoints.subfield Qr₀ F) →* H t :=
    (MulAut.conj c₀).toMonoidHom.comp (Psi.toMonoidHom.comp
      ((MatrixTorus.originalSlInH F b A hfix).comp (OddFieldLift.fixedSL2Inclusion F Qr₀)))
  have hj : Function.Injective j :=
    (MulAut.conj c₀).injective.comp (Psi.injective.comp
      ((MatrixFourGroupNormalizer.originalSlInH_injective F b A hfix).comp
        (OddFieldLift.fixedSL2Inclusion_injective F Qr₀)))
  have hjrange : j.range = Y ⊓ Subgroup.centralizer (Pbar : Set (H t)) := by
    apply le_antisymm
    · rintro _ ⟨X₀, rfl⟩
      set X := OddFieldLift.fixedSL2Inclusion F Qr₀ X₀ with hXdef
      have hXfix : ∀ q ∈ (Qr : Subgroup A),
          Matrix.SpecialLinearGroup.map (q : F ≃+* F).toRingHom X = X := by
        intro q hq
        have hXmem : X ∈ OddFieldLift.fixedEntrySL2 F Qr₀ := ⟨X₀, rfl⟩
        exact (OddFieldLift.mem_fixedEntrySL2 F Qr₀ X).mp hXmem ⟨q, hQr₀mem q hq⟩
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · change c₀ * Psi (MatrixTorus.originalSlInH F b A hfix X) * c₀⁻¹ ∈ Y
        apply hYn.conj_mem
        rw [hlayer]
        exact ⟨_, ⟨X, rfl⟩, rfl⟩
      · rw [Subgroup.mem_centralizer_iff]
        intro y hy
        obtain ⟨q, hq, rfl⟩ := (hPbar y).mp hy
        have h := (originalSlInH_commute_inr_iff F A b hfix q X).mpr (hXfix q hq)
        have h' : Psi (MatrixTorus.originalSlInH F b A hfix X) * Psi (SemidirectProduct.inr q) =
            Psi (SemidirectProduct.inr q) * Psi (MatrixTorus.originalSlInH F b A hfix X) := by
          rw [← map_mul, ← map_mul, h]
        change c₀ * Psi (SemidirectProduct.inr q) * c₀⁻¹ *
            (c₀ * Psi (MatrixTorus.originalSlInH F b A hfix X) * c₀⁻¹) =
          c₀ * Psi (MatrixTorus.originalSlInH F b A hfix X) * c₀⁻¹ *
            (c₀ * Psi (SemidirectProduct.inr q) * c₀⁻¹)
        calc c₀ * Psi (SemidirectProduct.inr q) * c₀⁻¹ *
              (c₀ * Psi (MatrixTorus.originalSlInH F b A hfix X) * c₀⁻¹)
            = c₀ * (Psi (SemidirectProduct.inr q) *
                Psi (MatrixTorus.originalSlInH F b A hfix X)) * c₀⁻¹ := by group
          _ = c₀ * (Psi (MatrixTorus.originalSlInH F b A hfix X) *
                Psi (SemidirectProduct.inr q)) * c₀⁻¹ := by rw [h']
          _ = c₀ * Psi (MatrixTorus.originalSlInH F b A hfix X) * c₀⁻¹ *
              (c₀ * Psi (SemidirectProduct.inr q) * c₀⁻¹) := by group
    · rintro y ⟨hyY, hyc⟩
      have hy' : c₀⁻¹ * y * c₀ ∈ Y := by
        have h := hYn.conj_mem y hyY c₀⁻¹
        rwa [inv_inv] at h
      rw [hlayer] at hy'
      obtain ⟨_, ⟨X, rfl⟩, hX⟩ := hy'
      have hX' : Psi (MatrixTorus.originalSlInH F b A hfix X) = c₀⁻¹ * y * c₀ := hX
      have hXfix : X ∈ OddFieldLift.fixedEntrySL2 F Qr₀ := by
        rw [OddFieldLift.mem_fixedEntrySL2]
        rintro ⟨_, ⟨q, hq, rfl⟩⟩
        apply (originalSlInH_commute_inr_iff F A b hfix q X).mp
        apply Psi.injective
        rw [map_mul, map_mul, hX']
        have h := Subgroup.mem_centralizer_iff.mp hyc _ ((hPbar _).mpr ⟨q, hq, rfl⟩)
        calc c₀⁻¹ * y * c₀ * Psi (SemidirectProduct.inr q)
            = c₀⁻¹ * (y * (c₀ * Psi (SemidirectProduct.inr q) * c₀⁻¹)) * c₀ := by group
          _ = c₀⁻¹ * (c₀ * Psi (SemidirectProduct.inr q) * c₀⁻¹ * y) * c₀ := by rw [h]
          _ = Psi (SemidirectProduct.inr q) * (c₀⁻¹ * y * c₀) := by group
      obtain ⟨X₀, hX₀⟩ := hXfix
      refine ⟨X₀, ?_⟩
      change c₀ * Psi (MatrixTorus.originalSlInH F b A hfix
        (OddFieldLift.fixedSL2Inclusion F Qr₀ X₀)) * c₀⁻¹ = y
      rw [hX₀, hX']
      group
  set Λbar := Y ⊓ Subgroup.centralizer (Pbar : Set (H t)) with hΛbardef
  let eΛ : Λbar ≃* Matrix.SpecialLinearGroup (Fin 2) (FixedPoints.subfield Qr₀ F) :=
    ((MonoidHom.ofInjective hj).trans (MulEquiv.subgroupCongr hjrange)).symm
  set ΛC := Λbar.comap (nu t) with hΛCdef
  let eC := ΛC.equivMapOfInjective (C t).subtype (C t).subtype_injective
  let φ : ΛC.map (C t).subtype →* Matrix.SpecialLinearGroup (Fin 2) (FixedPoints.subfield Qr₀ F) :=
    eΛ.toMonoidHom.comp (((nu t).subgroupComap Λbar).comp eC.symm.toMonoidHom)
  refine ⟨ΛC.map (C t).subtype, ?_, FixedPoints.subfield Qr₀ F, inferInstance, inferInstance,
    Nat.card Qr₀, ?_, hmodd, ?_, φ, ?_, ?_⟩
  ·
    intro l
    constructor
    · rintro ⟨c, hc, rfl⟩
      refine ⟨⟨c, hc.1, rfl⟩, fun g hg => ?_⟩
      have hgC := hPC hg
      have hcomm : nu t ⟨g, hgC⟩ * nu t c = nu t c * nu t ⟨g, hgC⟩ :=
        Subgroup.mem_centralizer_iff.mp hc.2 _ ⟨⟨g, hgC⟩, hg, rfl⟩
      rw [frontierSetting_ON]
      refine ⟨⟨g, hgC⟩ * c * ⟨g, hgC⟩⁻¹ * c⁻¹, ?_, rfl⟩
      apply (QuotientGroup.eq_one_iff _).mp
      change nu t (⟨g, hgC⟩ * c * ⟨g, hgC⟩⁻¹ * c⁻¹) = 1
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
      group
    · rintro ⟨⟨c, hc, rfl⟩, hcomm⟩
      refine ⟨c, (Subgroup.mem_inf.mpr ⟨hc, ?_⟩ : nu t c ∈ Λbar), rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨c', hc', rfl⟩
      have h := hcomm _ hc'
      rw [frontierSetting_ON] at h
      have hN : c' * c * c'⁻¹ * c⁻¹ ∈ N t :=
        (Subgroup.mem_map_iff_mem (x := c' * c * c'⁻¹ * c⁻¹) (C t).subtype_injective).mp h
      have h1 : nu t (c' * c * c'⁻¹ * c⁻¹) = 1 := (QuotientGroup.eq_one_iff _).mpr hN
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, mul_inv_eq_one,
        mul_inv_eq_iff_eq_mul] at h1
      exact h1
  ·
    by_contra hm
    apply hZ
    have hm1 : Nat.card Qr₀ = 1 := by
      have := Nat.card_pos (α := Qr₀)
      omega
    have hQr1 : ∀ q ∈ (Qr : Subgroup A), q = 1 := by
      intro q hq
      have hq0 : (q : F ≃+* F) ∈ Qr₀ := hQr₀mem q hq
      rw [Subgroup.card_eq_one.mp hm1, Subgroup.mem_bot] at hq0
      exact Subtype.ext hq0
    rintro g ⟨hgP, -⟩
    have hgC := hPC hgP
    obtain ⟨q, hq, hqeq⟩ := (hPbar _).mp ⟨⟨g, hgC⟩, hgP, rfl⟩
    rw [hQr1 q hq, map_one, map_one, mul_one, mul_inv_cancel] at hqeq
    exact ⟨⟨g, hgC⟩, N_le_localLayerPreimage t ((QuotientGroup.eq_one_iff _).mp hqeq), rfl⟩
  ·
    obtain ⟨-, -, -, -, -, hF0card, hpow, -⟩ :=
      FixedFieldData.odd_fixed_field_data p f hp hpodd hf F hFcard Qr₀ hmodd
    change p ^ f = _
    rw [hF0card, ← hpow, hFcard]
  ·
    exact eΛ.surjective.comp (((nu t).subgroupComap_surjective Λbar
      (QuotientGroup.mk'_surjective _)).comp eC.symm.surjective)
  ·
    ext l
    have hcl : (((eC.symm l : ΛC) : C t) : G) = (l : G) := by
      have h := congrArg Subtype.val (eC.apply_symm_apply l)
      rwa [Subgroup.coe_equivMapOfInjective_apply] at h
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, frontierSetting_ON, ← hcl]
    refine Iff.trans ?_ (Subgroup.mem_map_iff_mem (C t).subtype_injective).symm
    change eΛ ((nu t).subgroupComap Λbar (eC.symm l)) = 1 ↔ _
    rw [map_eq_one_iff _ eΛ.injective, ← Subtype.coe_inj]
    exact QuotientGroup.eq_one_iff _

end CFSG.Semidihedral.AllPrime
