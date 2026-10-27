module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Q81FBar
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitSL25
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aSecData
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2Leaf

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools
open scoped MatrixGroups

namespace Q81

theorem sl2_mul_self_eq_one {F : Type*} [Field F] (h2 : (2 : F) ≠ 0)
    {A : Matrix.SpecialLinearGroup (Fin 2) F} (hA : A * A = 1) :
    (A : Matrix (Fin 2) (Fin 2) F) = 1 ∨ (A : Matrix (Fin 2) (Fin 2) F) = -1 := by
  have hdet : (A : Matrix (Fin 2) (Fin 2) F).det = 1 := A.2
  have hsq : (A : Matrix (Fin 2) (Fin 2) F) * A = 1 := congrArg Subtype.val hA
  rw [Matrix.det_fin_two] at hdet
  have e00 := congrFun (congrFun hsq 0) 0
  have e01 := congrFun (congrFun hsq 0) 1
  have e10 := congrFun (congrFun hsq 1) 0
  have e11 := congrFun (congrFun hsq 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq,
    Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)] at e00 e01 e10 e11
  set a := (A : Matrix (Fin 2) (Fin 2) F) 0 0
  set b := (A : Matrix (Fin 2) (Fin 2) F) 0 1
  set c := (A : Matrix (Fin 2) (Fin 2) F) 1 0
  set d := (A : Matrix (Fin 2) (Fin 2) F) 1 1
  by_cases had : a + d = 0
  · exfalso
    apply h2
    have hd : d = -a := by linear_combination had
    rw [hd] at hdet e11
    linear_combination -e00 - hdet
  · have hb : b = 0 := by
      have : b * (a + d) = 0 := by linear_combination e01
      exact (mul_eq_zero.mp this).resolve_right had
    have hc : c = 0 := by
      have : c * (a + d) = 0 := by linear_combination e10
      exact (mul_eq_zero.mp this).resolve_right had
    rw [hb] at e00 e11 hdet
    rw [hc] at e00 e11 hdet
    have ha2 : a * a = 1 := by linear_combination e00
    have had1 : a * d = 1 := by linear_combination hdet
    have hda : d = a := by
      have h1 : a * (d - a) = 0 := by linear_combination had1 - ha2
      have ha0 : a ≠ 0 := fun h => by rw [h, zero_mul] at ha2; exact one_ne_zero ha2.symm
      linear_combination (mul_eq_zero.mp h1).resolve_left ha0
    have hd1 : d = a := hda
    rcases mul_self_eq_one_iff.mp ha2 with h1 | h1
    · left
      ext i j
      fin_cases i <;> fin_cases j
      · simpa using h1
      · simpa using hb
      · simpa using hc
      · exact (hd1.trans h1).trans (by simp)
    · right
      ext i j
      fin_cases i <;> fin_cases j
      · simpa using h1
      · simpa using hb
      · simpa using hc
      · exact (hd1.trans h1).trans (by simp)

theorem psl_two_double_cover (hGO : TBLit.GriessMultipliersOdd)
    (hGC : TBLit.GriessMultipliersCentralCovers) {Q : Type} [Group Q] [Finite Q]
    (hQ : IsQuasisimple Q) (hZ : IsPGroup 2 (center Q)) (hZ1 : center Q ≠ ⊥) {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hm : Blueprint.LieModel (Q ⧸ center Q) .PSL 2 p f) :
    ∃ _ : Fact p.Prime, Nonempty (Q ≃* SL(2, GaloisField p f)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfact : Fact p.Prime := ⟨hp⟩
  have hm' := TBLit.models_lieModel_of_lieModel_psl_two hm
  obtain ⟨hf, h5⟩ := TBLit.lieModel_psl_two_params hm hp2
  obtain ⟨-, -, K, hK, hKf, hcardK, ⟨eK⟩⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ := hm
  rotate_left
  · exact absurd h0 (by norm_num)
  · exact absurd h0 (by norm_num)
  · exact absurd h0 (by norm_num)
  refine ⟨hfact, ?_⟩
  have hS2 := TBLit.sylow_two_card_griessHopfMultiplier_psl_two hGO hp hp2 hm'
  obtain ⟨hcov1, hcov2⟩ := hGC (Q ⧸ center Q) .PSL 2 p f hm'
  have hcardZ : Nat.card (center Q) = 2 := by
    obtain ⟨S⟩ : Nonempty (Sylow 2 (center Q)) := inferInstance
    have hle := hcov1 (fun S => (hS2 S).le) Q hQ ⟨MulEquiv.refl _⟩ S
    have hSZ : Nat.card S = Nat.card (center Q) := by
      obtain ⟨k, hk⟩ := (IsPGroup.iff_card.mp hZ)
      rw [Sylow.card_eq_multiplicity, hk, Nat.Prime.factorization_pow Nat.prime_two,
        Finsupp.single_eq_same]
    have h1 : 1 < Nat.card (center Q) := by
      rw [Subgroup.one_lt_card_iff_ne_bot]
      exact hZ1
    rw [hSZ] at hle
    omega
  have hKodd : Odd (Nat.card K) := by
    rw [hcardK]
    exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  have hSLq : IsQuasisimple (Matrix.SpecialLinearGroup (Fin 2) K) :=
    CatalogueBHigherLinearInner.sl_quasisimple 2 K le_rfl (.inr (by rw [hcardK]; exact h5))
  have hcardSL := ABGLocalTools.card_center_sl2 (F := K) hKodd
  obtain ⟨eQ⟩ := hcov2 (fun S => hS2 S) Q (Matrix.SpecialLinearGroup (Fin 2) K) hQ hSLq hcardZ
    hcardSL ⟨MulEquiv.refl _⟩ ⟨(SectionRank.OddCover.pslEquiv K).trans eK.symm⟩
  let _ : Fintype K := Fintype.ofFinite K
  let _ : Fintype (GaloisField p f) := Fintype.ofFinite (GaloisField p f)
  have hcardGF : Fintype.card K = Fintype.card (GaloisField p f) := by
    rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, hcardK,
      GaloisField.card p f (by omega)]
  exact ⟨eQ.trans (TBLit.specialLinearTwoRingEquiv (FiniteField.ringEquivOfCardEq hcardGF))⟩

theorem unique_involution_of_double_cover (hGO : TBLit.GriessMultipliersOdd)
    (hGC : TBLit.GriessMultipliersCentralCovers) {Q : Type} [Group Q] [Finite Q]
    (hQ : IsQuasisimple Q) (hZ : IsPGroup 2 (center Q)) (hZ1 : center Q ≠ ⊥) {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hm : Blueprint.LieModel (Q ⧸ center Q) .PSL 2 p f) :
    ∃ c : Q, ∀ x : Q, x * x = 1 → x = 1 ∨ x = c := by
  obtain ⟨_, ⟨e⟩⟩ := psl_two_double_cover hGO hGC hQ hZ hZ1 hp hp2 hm
  have h2 : (2 : GaloisField p f) ≠ 0 := by
    intro h
    have hchar : ringChar (GaloisField p f) = p := ringChar.eq (GaloisField p f) p
    have h2' : ((2 : ℕ) : GaloisField p f) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff (GaloisField p f) p] at h2'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2')
  have hneg : ∃ m : Matrix.SpecialLinearGroup (Fin 2) (GaloisField p f),
      (m : Matrix (Fin 2) (Fin 2) (GaloisField p f)) = -1 :=
    ⟨⟨-1, by simp [Matrix.det_neg]⟩, rfl⟩
  obtain ⟨m, hm1⟩ := hneg
  refine ⟨e.symm m, fun x hx => ?_⟩
  have hx' : e x * e x = 1 := by rw [← map_mul, hx, map_one]
  rcases sl2_mul_self_eq_one h2 hx' with h1 | h1
  · left
    apply e.injective
    rw [map_one]
    exact Subtype.ext h1
  · right
    apply e.injective
    rw [MulEquiv.apply_symm_apply]
    exact Subtype.ext (h1.trans hm1.symm)

variable {X : Type} [Group X] [Finite X] {z t : X}

theorem component_psl_two (h219 : Harris82Lemma219Input) (hP2 : Harris81Lemma33Simple)
    (hGO : TBLit.GriessMultipliersOdd) (htz : t ∈ centralizer ({z} : Set X))
    (ht : orderOf t = 2)
    (hC : IsPGroup 2 (↥(centralizer ({t} : Set X) ⊓ centralizer {z}) ⧸
      pPrimeCore 2 ↥(centralizer ({t} : Set X) ⊓ centralizer {z})))
    {A : Subgroup (MBar z)} (hA : IsComponent A) (hAt : IsOfType (HarrisF 3) ↥A)
    (hZ1 : center ↥A ≠ ⊥) :
    ∃ m : ℕ, 2 ≤ m ∧ Blueprint.LieModel (↥A ⧸ center ↥A) .PSL 2 3 m ∧
      IsPGroup 2 ↥(center ↥A) ∧ Nat.card ↥(center ↥A) ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO : pPrimeCore 2 (MBar z) = ⊥ := pPrimeCore_quotient_pPrimeCore_eq_bot 2
  have hOA := pPrimeCore_eq_bot_of_isSubnormal hO hA.2
  obtain ⟨hN, hP⟩ := component_tBar h219 htz ht hC hA
  have ht2 : (QuotientGroup.mk ⟨t, htz⟩ : MBar z) * QuotientGroup.mk ⟨t, htz⟩ = 1 := by
    rw [← QuotientGroup.mk_mul]
    have : (⟨t, htz⟩ : ↥(centralizer ({z} : Set X))) * ⟨t, htz⟩ = 1 :=
      Subtype.ext (by change t * t = 1; rw [← sq, ← ht, pow_orderOf_eq_one])
    rw [this, QuotientGroup.mk_one]
  obtain ⟨m, hm2, hm⟩ := harris81Lemma33Step_of_simple hP2 _ A hAt hOA hZ1 _ hN ht2 hP
  have hm' := GSThmB.OddQuot.lieModel_of_equiv
    (QuotientGroup.quotientMulEquivOfEq (fusionZStar_eq_center_of_pPrimeCore_eq_bot hOA)) hm
  have hZ := isPGroup_center_of_pPrimeCore_eq_bot hOA
  refine ⟨m, hm2, hm', hZ, ?_⟩
  have hdvd := Center47.card_center_dvd_card_griessHopfMultiplier hA.1
  obtain ⟨e⟩ := (hGO _ .PSL 2 3 m (TBLit.models_lieModel_of_lieModel_psl_two hm')
    (by norm_num) (Or.inl rfl)).2
  obtain ⟨k, hk, hcard⟩ := TBLit.card_psl_two_multiplier_table Nat.prime_three (by norm_num)
    (f := m)
  rw [Nat.card_congr e.toEquiv, hcard] at hdvd
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hZ
  rw [hn] at hdvd ⊢
  have hn1 : n ≤ 1 := by
    by_contra hn1
    have h4 : 4 ∣ 2 * k := (pow_dvd_pow 2 (by omega : 2 ≤ n)).trans hdvd
    obtain ⟨j, hj⟩ := hk
    omega
  calc 2 ^ n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hn1
    _ = 2 := pow_one 2

theorem zBar_not_mem_component
    [IsSimpleGroup X] (hnonab : ∃ a b : X, a * b ≠ b * a) (hcat : ¬ Blueprint.Catalog X)
    (hCI : GSLit.ClassicalInvolutionInput) (h219 : Harris82Lemma219Input)
    (hP2 : Harris81Lemma33Simple) (hGO : TBLit.GriessMultipliersOdd)
    (hGC : TBLit.GriessMultipliersCentralCovers) (hz : orderOf z = 2)
    (htz : t ∈ centralizer ({z} : Set X)) (ht : orderOf t = 2)
    (hC : IsPGroup 2 (↥(centralizer ({t} : Set X) ⊓ centralizer {z}) ⧸
      pPrimeCore 2 ↥(centralizer ({t} : Set X) ⊓ centralizer {z})))
    {A : Subgroup (MBar z)} (hA : IsComponent A) (hAt : IsOfType (HarrisF 3) ↥A) :
    (QuotientGroup.mk ⟨z, mem_centralizer_singleton_iff.mpr rfl⟩ : MBar z) ∉ A := by
  intro hzA
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO : pPrimeCore 2 (MBar z) = ⊥ := pPrimeCore_quotient_pPrimeCore_eq_bot 2
  have hzc := mk_center z
  have hz2 := orderOf_mk_self hz
  have hzZ : (⟨_, hzA⟩ : ↥A) ∈ center ↥A :=
    mem_center_iff.mpr fun g => Subtype.ext (mem_center_iff.mp hzc g)
  have hzA1 : (⟨_, hzA⟩ : ↥A) ≠ 1 := by
    intro h1
    have h2 := congrArg Subtype.val h1
    change (QuotientGroup.mk ⟨z, mem_centralizer_singleton_iff.mpr rfl⟩ : MBar z) = 1 at h2
    rw [h2, orderOf_one] at hz2
    exact absurd hz2 (by decide)
  have hZ1 : center ↥A ≠ ⊥ := by
    intro h1
    rw [h1, mem_bot] at hzZ
    exact hzA1 hzZ
  obtain ⟨m, -, hm, hZ, -⟩ := component_psl_two h219 hP2 hGO htz ht hC hA hAt hZ1
  obtain ⟨c, hc⟩ := unique_involution_of_double_cover hGO hGC hA.1 hZ hZ1 Nat.prime_three
    (by norm_num) hm
  have hCzb : centralizer ({(QuotientGroup.mk ⟨z, mem_centralizer_singleton_iff.mpr rfl⟩ :
      MBar z)} : Set (MBar z)) = ⊤ := by
    rw [eq_top_iff]
    intro g _
    exact mem_centralizer_singleton_iff.mpr (mem_center_iff.mp hzc g)
  have hAp : IsPComponent 2 A :=
    (isTwoComponent_iff_isPComponent A).mp ((isTwoComponent_iff_isComponent hO A).mpr hA)
  have hY : IsPComponent 2 (A.subgroupOf (centralizer {(QuotientGroup.mk
      ⟨z, mem_centralizer_singleton_iff.mpr rfl⟩ : MBar z)})) := by
    rw [hCzb]
    exact GSThmB.B5a.isPComponent_subgroupOf_top_iff.mpr hAp
  obtain ⟨J, hJle, hJ, hzJ, -, g, hg, hgk⟩ := Lemma47.exists_lift_two_component
    (mem_centralizer_singleton_iff.mpr rfl) hz (hCzb ▸ le_top) hY hzA
  rw [inf_idem] at hJle hJ
  have hgi : ∀ x : ↥J, orderOf x = 2 → g x = c := by
    intro x hx
    have hx' : x * x = 1 := by rw [← sq]; exact hx ▸ pow_orderOf_eq_one x
    have h1 : g x * g x = 1 := by rw [← map_mul, hx', map_one]
    rcases hc (g x) h1 with h2 | h2
    · exfalso
      have h3 : x ∈ g.ker := h2
      have h4 : orderOf x ∣ Nat.card g.ker := Subgroup.orderOf_dvd_natCard g.ker h3
      rw [hx] at h4
      exact hgk h4
    · exact h2
  have hzJ2 : orderOf (⟨z, hzJ⟩ : ↥J) = 2 := by rw [Subgroup.orderOf_mk, hz]
  have hrank : CFSG.pRank 2 ↥J ≤ 1 := by
    refine FooteLit.pRank_le_one_of_forall_sq_eq_one ⟨z, hzJ⟩ fun x hx => ?_
    by_cases hx1 : x = 1
    · exact Or.inl hx1
    right
    have hx2 : orderOf x = 2 := orderOf_eq_prime hx hx1
    have h1 : x⁻¹ * ⟨z, hzJ⟩ ∈ g.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hgi x hx2, hgi _ hzJ2, inv_mul_cancel]
    have hxz : x * ⟨z, hzJ⟩ = ⟨z, hzJ⟩ * x :=
      Subtype.ext (mem_centralizer_singleton_iff.mp (hJle x.2))
    have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_left (by rw [← sq]; exact hx)
    have h2 : (x⁻¹ * ⟨z, hzJ⟩) ^ 2 = 1 := by
      rw [hxi, sq, show x * ⟨z, hzJ⟩ * (x * ⟨z, hzJ⟩) = x * (⟨z, hzJ⟩ * x) * ⟨z, hzJ⟩ by group,
        ← hxz, show x * (x * ⟨z, hzJ⟩) * ⟨z, hzJ⟩ = (x * x) * (⟨z, hzJ⟩ * ⟨z, hzJ⟩) by group,
        ← sq, hx, ← sq, ← hzJ2, pow_orderOf_eq_one, one_mul]
    have h3 : orderOf (⟨x⁻¹ * ⟨z, hzJ⟩, h1⟩ : ↥g.ker) ∣ Nat.card ↥g.ker :=
      orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h3
    have h4 : orderOf (x⁻¹ * ⟨z, hzJ⟩) ∣ 2 := orderOf_dvd_of_pow_eq_one h2
    have h5 : orderOf (x⁻¹ * ⟨z, hzJ⟩) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp h4 with h6 | h6
      · exact h6
      · rw [h6] at h3
        exact absurd h3 hgk
    rw [orderOf_eq_one_iff, inv_mul_eq_one] at h5
    exact h5
  exact hcat (catalog_of_oddLieType (FooteLit.oddLieType_of_classical_twoComponent hCI hnonab hz
    hJle hJ hzJ hrank))

end Q81

end CFSG.ComponentClassification.HarrisLit
