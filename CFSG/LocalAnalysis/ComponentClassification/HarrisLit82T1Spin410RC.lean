module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1Spin410RO
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1Spin410b
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1SpinCover

public section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup QuadraticMap CliffordAlgebra CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.Models.OrthogonalPairs
open scoped MatrixGroups

theorem gwIsQuasisimple_of_isQuasisimple {Q : Type*} [Group Q] (h : IsQuasisimple Q) :
    GorensteinWalter.IsQuasisimple Q :=
  ⟨LocalCores.isQuasisimple_nontrivial h, h.1.commutator_eq_top, h.2.1⟩

theorem gwIsComponentOf_subgroupOf {G : Type*} [Group G] {C A : Subgroup G} (hAC : A ≤ C)
    (hsn : (A.subgroupOf C).IsSubnormal) (hq : IsQuasisimple ↥A) :
    GorensteinWalter.IsComponentOf (A.subgroupOf C) ⊤ :=
  ⟨le_top, hsn.subgroupOf, gwIsQuasisimple_of_isQuasisimple
    (LocalCores.isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe hAC).symm hq)⟩

theorem le_or_commutator_eq_bot_of_subgroupOf {G : Type*} [Group G] [Finite G]
    {C A B : Subgroup G} (hAC : A ≤ C) (hBC : B ≤ C)
    (hA : GorensteinWalter.IsComponentOf (A.subgroupOf C) ⊤)
    (hB : (B.subgroupOf C).IsSubnormal) : A ≤ B ∨ ⁅A, B⁆ = ⊥ := by
  rcases GorensteinWalter.component_le_or_commutator_eq_bot hA hB with h | h
  · left
    intro x hx
    exact h (show (⟨x, hAC hx⟩ : ↥C) ∈ A.subgroupOf C from hx)
  · right
    have h' := congrArg (Subgroup.map C.subtype) h
    rwa [map_commutator, subgroupOf_map_subtype, subgroupOf_map_subtype, inf_of_le_left hAC,
      inf_of_le_left hBC, Subgroup.map_bot] at h'

theorem not_le_centralizer_self {G : Type*} [Group G] {J : Subgroup G}
    (hJ : Group.IsPerfect ↥J) (hnt : Nontrivial ↥J) : ¬ J ≤ centralizer J := by
  intro h
  have h1 : ⁅J, J⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr h
  rw [Subgroup.isPerfect_iff.mp hJ] at h1
  exact (nontrivial_iff_ne_bot J).mp hnt h1

theorem pPrimeCore_eq_bot_of_isTwoComponentIn {G : Type*} [Group G] [Finite G]
    {C J : Subgroup G} (hJ : IsTwoComponentIn J C) (hC : pPrimeCore 2 ↥C = ⊥) :
    pPrimeCore 2 ↥J = ⊥ := by
  have h := CFSG.Walter.map_pPrimeCore_le_of_isSubnormal hJ.2.1
  rw [hC, le_bot_iff, map_eq_bot_iff_of_injective _ (subtype_injective _)] at h
  rw [← pPrimeCore_map_iso 2 (subgroupOfEquivOfLe hJ.1), h, Subgroup.map_bot]

theorem isQuasisimple_of_isTwoComponentIn {G : Type*} [Group G] [Finite G] {C J : Subgroup G}
    (hJ : IsTwoComponentIn J C) (hC : pPrimeCore 2 ↥C = ⊥) : IsQuasisimple ↥J :=
  LocalCores.isQuasisimple_of_mulEquiv ((QuotientGroup.quotientMulEquivOfEq
    (pPrimeCore_eq_bot_of_isTwoComponentIn hJ hC)).trans QuotientGroup.quotientBot) hJ.2.2.2

theorem isSLTwoOver_quotient_of_pPrimeCore_eq_bot {q : ℕ} {Y : Type} [Group Y]
    (hO : pPrimeCore 2 Y = ⊥) (hY : IsSLTwoOver q Y) : IsSLTwoOver q (Y ⧸ pPrimeCore 2 Y) := by
  obtain ⟨F, i1, i2, hF, ⟨e⟩⟩ := hY
  exact ⟨F, i1, i2, hF,
    ⟨((QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot).trans e⟩⟩

theorem isSLTwoOver_quotient_of_mulEquiv {q : ℕ} {Y Y' : Type} [Group Y] [Group Y']
    (φ : Y ≃* Y') (h : IsSLTwoOver q (Y' ⧸ pPrimeCore 2 Y')) :
    IsSLTwoOver q (Y ⧸ pPrimeCore 2 Y) := by
  obtain ⟨F, i1, i2, hF, ⟨eF⟩⟩ := h
  exact ⟨F, i1, i2, hF, ⟨(QuotientGroup.congr _ _ φ (pPrimeCore_map_iso 2 φ)).trans eF⟩⟩

section Model

variable {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
  (hK : Nat.card K = p ^ f) (h5 : 5 ≤ p ^ f)
include hp hp2 hK h5

theorem spinJ_props {J : Subgroup (spinGroup (quadOdd 3 K))}
    (hJ : J = spinJ₁ K ∨ J = spinJ₂ K ∨ J = spinJ₃ K) :
    J ≤ centralizer {tSeven K} ∧ (J.subgroupOf (centralizer {tSeven K})).Normal ∧
      IsSLTwoOver (p ^ f) ↥J ∧ pPrimeCore 2 ↥J = ⊥ ∧ IsQuasisimple ↥J := by
  have := finite_spinSeven (two_ne_zero_spin hp hp2 hK)
  obtain ⟨l1, l2, l3⟩ := spinJ_le_centralizer (K := K) hp hp2 hK
  obtain ⟨n1, n2, n3⟩ := normal_spinJ (K := K) hp hp2 hK h5
  obtain ⟨s1, s2, s3⟩ := isSLTwoOver_spinJ (K := K) hK
  rcases hJ with rfl | rfl | rfl
  · obtain ⟨hq, -, hO⟩ := sl2_facts_spin hp hp2 h5 s1
    exact ⟨l1, n1, s1, hO, hq⟩
  · obtain ⟨hq, -, hO⟩ := sl2_facts_spin hp hp2 h5 s2
    exact ⟨l2, n2, s2, hO, hq⟩
  · obtain ⟨hq, -, hO⟩ := sl2_facts_spin hp hp2 h5 s3
    exact ⟨l3, n3, s3, hO, hq⟩

theorem eq_spinJ_of_isTwoComponentIn {J : Subgroup (spinGroup (quadOdd 3 K))}
    (hJ : IsTwoComponentIn J (centralizer {tSeven K})) :
    J = spinJ₁ K ∨ J = spinJ₂ K ∨ J = spinJ₃ K := by
  have := finite_spinSeven (two_ne_zero_spin hp hp2 hK)
  have hO := pPrimeCore_centralizer_tSeven hp hp2 hK h5
  have hJq := isQuasisimple_of_isTwoComponentIn hJ hO
  have hJperf : Group.IsPerfect ↥J := hJ.2.2.1
  have hJnt : Nontrivial ↥J := LocalCores.isQuasisimple_nontrivial hJq
  have hJE : J ≤ spinE K := le_spinE_of_isPerfect hp hp2 hK h5 hJ.1 hJperf
  have hJc := gwIsComponentOf_subgroupOf hJ.1 hJ.2.1 hJq
  have key : ∀ J' : Subgroup (spinGroup (quadOdd 3 K)),
      (J' = spinJ₁ K ∨ J' = spinJ₂ K ∨ J' = spinJ₃ K) → J = J' ∨ ⁅J, J'⁆ = ⊥ := by
    intro J' hJ'
    obtain ⟨hJ'C, hJ'n, -, -, hJ'q⟩ := spinJ_props hp hp2 hK h5 hJ'
    have hJ'c := gwIsComponentOf_subgroupOf hJ'C hJ'n.isSubnormal hJ'q
    rcases le_or_commutator_eq_bot_of_subgroupOf hJ.1 hJ'C hJc hJ'n.isSubnormal with h | h
    · rcases le_or_commutator_eq_bot_of_subgroupOf hJ'C hJ.1 hJ'c hJ.2.1 with h' | h'
      · exact Or.inl (le_antisymm h h')
      · exact (not_le_centralizer_self hJperf hJnt
          (fun x hx => commutator_eq_bot_iff_le_centralizer.mp h' (h hx))).elim
    · exact Or.inr h
  rcases key _ (Or.inl rfl) with h1 | h1
  · exact Or.inl h1
  rcases key _ (Or.inr (Or.inl rfl)) with h2 | h2
  · exact Or.inr (Or.inl h2)
  rcases key _ (Or.inr (Or.inr rfl)) with h3 | h3
  · exact Or.inr (Or.inr h3)
  exfalso
  refine not_le_centralizer_self hJperf hJnt (hJE.trans (sup_le (sup_le ?_ ?_) ?_))
  · exact commutator_eq_bot_iff_le_centralizer.mp ((commutator_comm _ _).trans h1)
  · exact commutator_eq_bot_iff_le_centralizer.mp ((commutator_comm _ _).trans h2)
  · exact commutator_eq_bot_iff_le_centralizer.mp ((commutator_comm _ _).trans h3)

theorem eq_one_of_mem_spinJ₁_of_mem_spinJ₂ {x : spinGroup (quadOdd 3 K)} (h1 : x ∈ spinJ₁ K)
    (h2 : x ∈ spinJ₂ K) : x = 1 := by
  obtain ⟨hzz, -, hzc, htt, -, htc, -, -, -, -⟩ := spinZ_facts hp hp2 hK
  rcases eq_one_or_eq_of_mem_zpowers_of_mul_self hzz (mem_zpowers_of_commute_spinJ₁ hp hp2 hK h5
    h1 fun a ha => (commute_spinJ₁_spinJ₂ ha h2).symm) with ha | ha
  · exact ha
  rcases eq_one_or_eq_of_mem_zpowers_of_mul_self htt (mem_zpowers_of_commute_spinJ₂ hp hp2 hK h5
    h2 fun b hb => commute_spinJ₁_spinJ₂ h1 hb) with hb | hb
  · exact hb
  exact absurd (by rw [← hb, ha]; exact hzc) htc

theorem eq_one_of_mem_spinJ₁_of_mem_spinJ₃ {x : spinGroup (quadOdd 3 K)} (h1 : x ∈ spinJ₁ K)
    (h3 : x ∈ spinJ₃ K) : x = 1 := by
  obtain ⟨hzz, -, hzc, htt, ht1, -, -, -, -, h3eq⟩ := spinZ_facts hp hp2 hK
  have h4 := four_le_card_spin hK h5
  have hzcomm : ∀ g : spinGroup (quadOdd 3 K), spinZ K * g = g * spinZ K := fun g =>
    (mem_center_iff.mp hzc g).symm
  have hztzt : spinZ K * tSeven K * (spinZ K * tSeven K) = 1 := by
    rw [mul_assoc, ← mul_assoc (tSeven K), ← hzcomm, mul_assoc, htt, mul_one, hzz]
  rcases eq_one_or_eq_of_mem_zpowers_of_mul_self hzz (mem_zpowers_of_commute_spinJ₁ hp hp2 hK h5
    h1 fun a ha => (commute_spinJ₁_spinJ₃ ha h3).symm) with ha | ha
  · exact ha
  rcases eq_one_or_eq_of_mem_zpowers_of_mul_self hztzt (h3eq ▸ mem_zpowers_of_commute_spinJ₃ hp
    hp2 hK h5 h3 fun c hc => commute_spinJ₁_spinJ₃ h1 hc) with hc | hc
  · exact hc
  exact absurd (mul_left_cancel ((hc.symm.trans ha).trans (mul_one _).symm)) ht1

theorem eq_one_of_mem_spinJ₂_of_mem_spinJ₃ {x : spinGroup (quadOdd 3 K)} (h2 : x ∈ spinJ₂ K)
    (h3 : x ∈ spinJ₃ K) : x = 1 := by
  obtain ⟨hzz, hz1, hzc, htt, -, -, -, -, -, h3eq⟩ := spinZ_facts hp hp2 hK
  have h4 := four_le_card_spin hK h5
  have hzcomm : ∀ g : spinGroup (quadOdd 3 K), spinZ K * g = g * spinZ K := fun g =>
    (mem_center_iff.mp hzc g).symm
  have hztzt : spinZ K * tSeven K * (spinZ K * tSeven K) = 1 := by
    rw [mul_assoc, ← mul_assoc (tSeven K), ← hzcomm, mul_assoc, htt, mul_one, hzz]
  rcases eq_one_or_eq_of_mem_zpowers_of_mul_self htt (mem_zpowers_of_commute_spinJ₂ hp hp2 hK h5
    h2 fun b hb => (commute_spinJ₂_spinJ₃ h4 hb h3).symm) with hb | hb
  · exact hb
  rcases eq_one_or_eq_of_mem_zpowers_of_mul_self hztzt (h3eq ▸ mem_zpowers_of_commute_spinJ₃ hp
    hp2 hK h5 h3 fun c hc => commute_spinJ₂_spinJ₃ h4 h2 hc) with hc | hc
  · exact hc
  exact absurd (mul_right_cancel ((hc.symm.trans hb).trans (one_mul _).symm)) hz1

theorem spinSeven_lemma410c_components :
    (∀ J : Subgroup (spinGroup (quadOdd 3 K)), IsTwoComponentIn J (centralizer {tSeven K}) →
      IsSLTwoOver (p ^ f) (↥J ⧸ pPrimeCore 2 ↥J) ∧
        (spinZ K ∈ J ∨ tSeven K ∈ J ∨ spinZ K * tSeven K ∈ J)) ∧
    ∀ J J' : Subgroup (spinGroup (quadOdd 3 K)), IsTwoComponentIn J (centralizer {tSeven K}) →
      IsTwoComponentIn J' (centralizer {tSeven K}) →
        ∀ e ∈ ({spinZ K, tSeven K, spinZ K * tSeven K} : Set (spinGroup (quadOdd 3 K))),
          e ∈ J → e ∈ J' → J = J' := by
  obtain ⟨hzz, hz1, hzc, -, ht1, htc, hz1', ht2', hzt3, -⟩ := spinZ_facts hp hp2 hK
  have hzt1 : spinZ K * tSeven K ≠ 1 := fun h => htc (by
    rw [(eq_inv_of_mul_eq_one_right h).trans (inv_eq_of_mul_eq_one_right hzz)]
    exact hzc)
  refine ⟨fun J hJ => ?_, fun J J' hJ hJ' e he heJ heJ' => ?_⟩
  · obtain ⟨-, -, hs, hO, -⟩ :=
      spinJ_props hp hp2 hK h5 (eq_spinJ_of_isTwoComponentIn hp hp2 hK h5 hJ)
    refine ⟨isSLTwoOver_quotient_of_pPrimeCore_eq_bot hO hs, ?_⟩
    rcases eq_spinJ_of_isTwoComponentIn hp hp2 hK h5 hJ with rfl | rfl | rfl
    · exact Or.inl hz1'
    · exact Or.inr (Or.inl ht2')
    · exact Or.inr (Or.inr hzt3)
  · have he1 : e ≠ 1 := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he
      rcases he with rfl | rfl | rfl
      · exact hz1
      · exact ht1
      · exact hzt1
    rcases eq_spinJ_of_isTwoComponentIn hp hp2 hK h5 hJ with rfl | rfl | rfl <;>
      rcases eq_spinJ_of_isTwoComponentIn hp hp2 hK h5 hJ' with rfl | rfl | rfl
    · rfl
    · exact absurd (eq_one_of_mem_spinJ₁_of_mem_spinJ₂ hp hp2 hK h5 heJ heJ') he1
    · exact absurd (eq_one_of_mem_spinJ₁_of_mem_spinJ₃ hp hp2 hK h5 heJ heJ') he1
    · exact absurd (eq_one_of_mem_spinJ₁_of_mem_spinJ₂ hp hp2 hK h5 heJ' heJ) he1
    · rfl
    · exact absurd (eq_one_of_mem_spinJ₂_of_mem_spinJ₃ hp hp2 hK h5 heJ heJ') he1
    · exact absurd (eq_one_of_mem_spinJ₁_of_mem_spinJ₃ hp hp2 hK h5 heJ' heJ) he1
    · exact absurd (eq_one_of_mem_spinJ₂_of_mem_spinJ₃ hp hp2 hK h5 heJ' heJ) he1
    · rfl

end Model

theorem exists_mulEquiv_spinSeven {X : Type} [Group X] [Finite X] {p f : ℕ} (h5 : 5 ≤ p ^ f)
    (hX : IsCoverOf .POmegaOdd 3 p f 2 X) {t : X} (ht : orderOf t = 2) (htZ : t ∉ center X) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (e : X ≃* spinGroup (quadOdd 3 K)),
      Nat.card K = p ^ f ∧ p.Prime ∧ p ≠ 2 ∧ e t = tSeven K := by
  obtain ⟨K, _, _, hK, -, hp, hp2, ⟨e⟩⟩ := nonempty_mulEquiv_spinOdd h5 hX
  have hodd : Odd (Nat.card K) := hK ▸ (hp.odd_of_ne_two hp2).pow
  obtain ⟨g, hg⟩ := spinSeven_lemma410b hodd (four_le_card_spin hK h5) (x := e t)
    (by rw [MulEquiv.orderOf_eq, ht]) (fun h => htZ ((mem_center_mulEquiv_iff e t).mp h))
  refine ⟨K, inferInstance, inferInstance, e.trans (MulAut.conj g⁻¹), hK, hp, hp2, ?_⟩
  show g⁻¹ * e t * g⁻¹⁻¹ = tSeven K
  rw [← hg]
  group

theorem eq_spinZ_of_mem_center {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) {x : spinGroup (quadOdd 3 K)}
    (hx : x ∈ center (spinGroup (quadOdd 3 K))) (hx1 : x ≠ 1) : x = spinZ K := by
  have h2 := two_ne_zero_spin hp hp2 hK
  have : Invertible (2 : K) := invertibleOfNonzero h2
  obtain ⟨hzz, -⟩ := spinZ_facts hp hp2 hK
  rw [center_spinGroup_quadOdd h2 (le_refl 3)] at hx
  exact (eq_one_or_eq_of_mem_zpowers_of_mul_self hzz hx).resolve_left hx1

theorem lemma410c_of_isCoverOf {X : Type} [Group X] [Finite X] {p f : ℕ} (h5 : 5 ≤ p ^ f)
    (hX : IsCoverOf .POmegaOdd 3 p f 2 X) {z : X} (hz : z ∈ center X) (hz1 : z ≠ 1) {t : X}
    (ht : orderOf t = 2) (htZ : t ∉ center X) :
    (∀ J : Subgroup X, IsTwoComponentIn J (centralizer {t}) →
        IsSLTwoOver (p ^ f) (↥J ⧸ pPrimeCore 2 ↥J) ∧ (z ∈ J ∨ t ∈ J ∨ z * t ∈ J)) ∧
      ∀ J J' : Subgroup X, IsTwoComponentIn J (centralizer {t}) →
        IsTwoComponentIn J' (centralizer {t}) → ∀ e ∈ ({z, t, z * t} : Set X), e ∈ J →
          e ∈ J' → J = J' := by
  obtain ⟨K, _, _, e, hK, hp, hp2, het⟩ := exists_mulEquiv_spinSeven h5 hX ht htZ
  have hez : e z = spinZ K := eq_spinZ_of_mem_center hp hp2 hK
    ((mem_center_mulEquiv_iff e z).mpr hz) (fun h => hz1 (e.injective (h.trans (map_one e).symm)))
  obtain ⟨hc1, hc2⟩ := spinSeven_lemma410c_components hp hp2 hK h5
  have hmap : ∀ J : Subgroup X, IsTwoComponentIn J (centralizer {t}) →
      IsTwoComponentIn (J.map e.toMonoidHom) (centralizer {tSeven K}) := by
    intro J hJ
    rw [← het, ← map_centralizer_singleton_mulEquiv e t]
    exact L35.isTwoComponentIn_map_of_injective e.toMonoidHom e.injective hJ
  have hmem : ∀ (J : Subgroup X) (x : X), e x ∈ J.map e.toMonoidHom → x ∈ J := by
    intro J x h
    rw [mem_map_equiv, MulEquiv.symm_apply_apply] at h
    exact h
  refine ⟨fun J hJ => ?_, fun J J' hJ hJ' x hx hxJ hxJ' => ?_⟩
  · obtain ⟨hs, hm⟩ := hc1 _ (hmap J hJ)
    refine ⟨isSLTwoOver_quotient_of_mulEquiv (J.equivMapOfInjective e.toMonoidHom e.injective)
      hs, ?_⟩
    rw [← hez, ← het, ← map_mul] at hm
    rcases hm with h | h | h
    · exact Or.inl (hmem J _ h)
    · exact Or.inr (Or.inl (hmem J _ h))
    · exact Or.inr (Or.inr (hmem J _ h))
  · have hx' : e x ∈ ({spinZ K, tSeven K, spinZ K * tSeven K} :
        Set (spinGroup (quadOdd 3 K))) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
      rcases hx with rfl | rfl | rfl
      · exact Or.inl hez
      · exact Or.inr (Or.inl het)
      · exact Or.inr (Or.inr (by rw [map_mul, hez, het]))
    exact map_injective e.injective (hc2 _ _ (hmap J hJ) (hmap J' hJ') (e x) hx'
      (mem_map_of_mem e.toMonoidHom hxJ) (mem_map_of_mem e.toMonoidHom hxJ'))

theorem pPrimeCore_centralizer_of_isCoverOf {X : Type} [Group X] [Finite X] {p f : ℕ}
    (h5 : 5 ≤ p ^ f) (hX : IsCoverOf .POmegaOdd 3 p f 2 X) {t : X} (ht : orderOf t = 2)
    (htZ : t ∉ center X) : pPrimeCore 2 ↥(centralizer ({t} : Set X)) = ⊥ := by
  obtain ⟨K, _, _, e, hK, hp, hp2, het⟩ := exists_mulEquiv_spinSeven h5 hX ht htZ
  have hmapC : (centralizer ({t} : Set X)).map e.toMonoidHom = centralizer {tSeven K} := by
    rw [← het, map_centralizer_singleton_mulEquiv e t]
  have φ := ((centralizer ({t} : Set X)).equivMapOfInjective e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr hmapC)
  have h := pPrimeCore_map_iso 2 φ
  rw [pPrimeCore_centralizer_tSeven hp hp2 hK h5] at h
  exact (map_eq_bot_iff_of_injective _ φ.injective).mp h

end CFSG.ComponentClassification.HarrisLit.T1
