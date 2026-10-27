module

public import CFSG.LocalAnalysis.GLTheoremA.S3.KData
public import CFSG.LocalAnalysis.SectionRank.OddCover.PSL2
public import CFSG.Adapters.LinearCatalog
public import CFSG.RankThree.PartTwo.KFacts.KS10L27Aut
public import CFSG.RankThree.PartTwo.KFacts.AutPSLOrderThree

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

private theorem kdL227_prime_pow_27 {p f : ℕ} (hp : p.Prime) (hf : 0 < f) (h : p ^ f = 27) :
    p = 3 ∧ f = 3 := by
  have hp3 : p = 3 := by
    have hd : p ∣ 3 := hp.dvd_of_dvd_pow (show p ∣ 3 ^ 3 by
      rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← h]
      exact dvd_pow_self p hf.ne')
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hd
  subst hp3
  exact ⟨rfl, Nat.pow_right_injective (by norm_num : 2 ≤ 3)
    (show 3 ^ f = 3 ^ 3 by norm_num [h])⟩

private theorem kdL227_isL2_elim {n : ℕ} {ℓ : TauCeti.LieTypeIndex} (h : isL2 n ℓ) :
    ∃ q : TauCeti.PrimePower, ℓ = .A 1 q ∧ q.card = n := by
  cases ℓ
  case A r q =>
    rcases r with _ | _ | r
    · exact False.elim h
    · exact ⟨q, rfl, h⟩
    · exact False.elim h
  all_goals exact False.elim h

private theorem kdL227_catalog_iso {S : Type} [Group S]
    (h : catalogIs S (onLie (isL2 27))) :
    Nonempty (S ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 3 3)) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic p hp => exact False.elim hi
  | alternating n hn => exact False.elim hi
  | lie d =>
    obtain ⟨ℓ, hv⟩ := d
    have hℓ : isL2 27 ℓ := hi
    obtain ⟨q, rfl, hq⟩ := kdL227_isL2_elim hℓ
    obtain ⟨p, f, hpp, hff⟩ := q
    have hpf : p ^ f = 27 := (TauCeti.PrimePower.card_def _).symm.trans hq
    obtain ⟨rfl, rfl⟩ := kdL227_prime_pow_27 hpp hff hpf
    haveI : Fact (Nat.Prime 3) := ⟨hpp⟩
    exact ⟨e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 ⟨3, 3, hpp, hff⟩ hv)⟩
  | sporadic name => exact False.elim hi

private theorem kdL227_center_eq_bot (E : Type) [Group E] [Finite E]
    (hq : CFSG.Open.IsQuasisimple E) (hZ : IsPGroup 3 (Subgroup.center E))
    (hcat : catalogIs (E ⧸ Subgroup.center E) (onLie (isL2 27))) :
    Subgroup.center E = ⊥ := by
  obtain ⟨e⟩ := kdL227_catalog_iso hcat
  haveI : Group.IsPerfect E := ⟨hq.1⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let π : E →* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 3 3) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center E))
  have hπs : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = Subgroup.center E := by
    ext x
    rw [MonoidHom.mem_ker]
    change e (QuotientGroup.mk x) = 1 ↔ x ∈ Subgroup.center E
    rw [map_eq_one_iff e e.injective, QuotientGroup.eq_one_iff]
  have hodd : Odd (Nat.card π.ker) := by
    obtain ⟨n, hn⟩ := hZ.exists_card_eq
    rw [hker, hn]
    exact Odd.pow (by decide)
  have hK : Nat.card (GaloisField 3 3) = 3 ^ 3 := GaloisField.card 3 3 (by norm_num)
  have h := (CFSG.SectionRank.OddCover.psl_two_perfect_odd_cover_kernel (p := 3) (f := 3)
    (by norm_num) hK π hπs hker.le hodd).1 (by norm_num)
  rw [hker] at h
  exact h

private theorem kdL227_root_exists {S : Type} [Group S] [Finite S]
    (e : S ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 3 3)) :
    ∃ P : Subgroup S, IsElemAbelian 3 P ∧ Nat.card P = 27 := by
  refine ⟨(CFSG.GorensteinWalter.psl2UpperUnipotentSubgroup (GaloisField 3 3)).map
    e.symm.toMonoidHom, ?_, ?_⟩
  · apply CFSG.SectionRank.isElemAbelian_map _ e.symm.toMonoidHom
    exact ⟨⟨⟨fun x y => Subtype.ext (CFSG.RankThree.PartTwo.KFacts.psl2Upper_mul_comm x.2 y.2)⟩⟩,
      fun x hx => CFSG.RankThree.PartTwo.KFacts.psl2Upper_pow_three hx⟩
  · rw [Subgroup.card_map_of_injective e.symm.injective,
      CFSG.GorensteinWalter.psl2UpperUnipotentSubgroup_card, GaloisField.card 3 3 (by norm_num)]
    norm_num


private theorem kdL227_cube_eq_iff {K : Type} [Field K] (x : K) :
    x ^ 3 = x ↔ x = 0 ∨ x = 1 ∨ x = -1 := by
  have h : x ^ 3 - x = x * (x - 1) * (x + 1) := by ring
  constructor
  · intro hx
    have h0 : x * (x - 1) * (x + 1) = 0 := by rw [← h, hx, sub_self]
    rcases mul_eq_zero.mp h0 with h1 | h1
    · rcases mul_eq_zero.mp h1 with h2 | h2
      · exact Or.inl h2
      · exact Or.inr (Or.inl (sub_eq_zero.mp h2))
    · exact Or.inr (Or.inr (eq_neg_of_add_eq_zero_left h1))
  · rintro (rfl | rfl | rfl) <;> norm_num

private theorem kdL227_two_ne_zero {K : Type} [Field K] [CharP K 3] : (2 : K) ≠ 0 := by
  intro h2
  have h3 : (3 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 3
  exact one_ne_zero (by linear_combination h3 - h2)

private theorem kdL227_fix_iff {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
    (hK : Nat.card K = 3 ^ 3) (hσ : orderOf σ = 3) (x : K) :
    σ x = x ↔ x ^ 3 = x := by
  have h := (CFSG.RankThree.PartTwo.KFacts.eq_frobenius_pow_of_orderOf_eq_three
    Nat.prime_three (by norm_num) hK hσ).2
  norm_num at h
  rcases h with h | h
  · rw [h x]
  · rw [h x]
    constructor
    · intro hx9
      haveI : Fintype K := Fintype.ofFinite K
      have hc : Fintype.card K = 27 := (Fintype.card_eq_nat_card).trans (hK.trans (by norm_num))
      have h27 : x ^ 27 = x := by rw [← hc]; exact FiniteField.pow_card x
      have h3 : x ^ 3 = x ^ 27 := by rw [show x ^ 27 = (x ^ 9) ^ 3 by ring, hx9]
      exact h3.trans h27
    · intro hx3
      rw [show x ^ 9 = (x ^ 3) ^ 3 by ring, hx3, hx3]

private theorem kdL227_card_fix {K : Type} [Field K] [Finite K] [CharP K 3] {σ : K ≃+* K}
    (hK : Nat.card K = 3 ^ 3) (hσ : orderOf σ = 3) {K₀ : Subfield K}
    (hK₀ : ∀ x, x ∈ K₀ ↔ σ x = x) : Nat.card K₀ = 3 := by
  have hset : (K₀ : Set K) = {0, 1, -1} := by
    ext x
    rw [SetLike.mem_coe, hK₀ x, kdL227_fix_iff hK hσ x, kdL227_cube_eq_iff x]
    simp
  have h1m1 : (1 : K) ≠ -1 := by
    intro h
    exact kdL227_two_ne_zero (by linear_combination h)
  have h0m1 : (0 : K) ≠ -1 := by
    intro h
    exact one_ne_zero (by linear_combination h)
  show Nat.card (K₀ : Set K) = 3
  rw [Nat.card_coe_set_eq, hset]
  exact Set.ncard_eq_three.mpr ⟨0, 1, -1, zero_ne_one, h0m1, h1m1, rfl⟩

private def kdL227Incl {K : Type} [Field K] (K₀ : Subfield K) :
    Matrix.ProjectiveSpecialLinearGroup (Fin 2) K₀ →*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) K :=
  QuotientGroup.map (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K₀))
    (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K))
    (Matrix.SpecialLinearGroup.map K₀.subtype) (by
      intro A hA
      rw [Matrix.SpecialLinearGroup.mem_center_iff] at hA
      rw [Subgroup.mem_comap, Matrix.SpecialLinearGroup.mem_center_iff]
      obtain ⟨r, hr, hA⟩ := hA
      refine ⟨K₀.subtype r, ?_, ?_⟩
      · rw [← map_pow, hr, map_one]
      · ext i j
        have hij := congrFun (congrFun hA i) j
        show Matrix.scalar (Fin 2) (K₀.subtype r) i j =
          K₀.subtype.mapMatrix (A : Matrix (Fin 2) (Fin 2) K₀) i j
        rw [RingHom.mapMatrix_apply, Matrix.map_apply, ← hij]
        by_cases h : i = j <;> simp [Matrix.scalar_apply, Matrix.diagonal_apply, h])

private theorem kdL227_no_neg {K : Type} [Field K] [CharP K 3] {σ : K ≃+* K}
    (hσ3 : σ ^ 3 = 1) (a : K) (h : σ a = -a) : a = 0 := by
  have h3 : ∀ x, σ (σ (σ x)) = x := fun x => by
    have := CFSG.RankThree.PartTwo.KFacts.iterate_three_apply_of_pow hσ3 x
    simpa [Function.iterate_succ_apply] using this
  have h2 : σ (σ a) = a := by rw [h, map_neg, h, neg_neg]
  have h1 : σ a = a := by
    have := h3 a
    rwa [h2] at this
  have h4 : a = -a := h1.symm.trans h
  have h5 : (2 : K) * a = 0 := by linear_combination h4
  exact (mul_eq_zero.mp h5).resolve_left kdL227_two_ne_zero

private theorem kdL227_hard {K : Type} [Field K] [Finite K] [CharP K 3] {σ : K ≃+* K}
    (hσ3 : σ ^ 3 = 1) {K₀ : Subfield K} (hK₀ : ∀ x, x ∈ K₀ ↔ σ x = x)
    (t : Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)
    (ht : CFSG.GorensteinWalter.psl2FieldAut K σ t = t) :
    t ∈ (kdL227Incl K₀).range := by
  obtain ⟨A, rfl⟩ := QuotientGroup.mk_surjective t
  rw [CFSG.GorensteinWalter.psl2FieldAut_apply] at ht
  have e1 : CFSG.GorensteinWalter.psl2RingEquiv σ (QuotientGroup.mk A) =
      QuotientGroup.mk (Matrix.SpecialLinearGroup.map σ.toRingHom A) :=
    CFSG.GorensteinWalter.psl2RingEquiv_mk σ A
  rw [e1] at ht
  have hz := QuotientGroup.eq.mp ht
  set z := (Matrix.SpecialLinearGroup.map σ.toRingHom A)⁻¹ * A with hzdef
  obtain ⟨r, hr, hzr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hz
  have hr2 : r * r = 1 := by
    rw [Fintype.card_fin] at hr
    simpa [sq] using hr
  have key : Matrix.SpecialLinearGroup.map σ.toRingHom A * z = A := mul_inv_cancel_left _ _
  have hM : (Matrix.SpecialLinearGroup.map σ.toRingHom A : Matrix (Fin 2) (Fin 2) K) *
      Matrix.scalar (Fin 2) r = (A : Matrix (Fin 2) (Fin 2) K) := by
    rw [hzr, ← Matrix.SpecialLinearGroup.coe_mul, key]
  have hent : ∀ i j, σ (A i j) * r = A i j := by
    intro i j
    have h1 := congrFun (congrFun hM i) j
    have h2 : (Matrix.SpecialLinearGroup.map σ.toRingHom A : Matrix (Fin 2) (Fin 2) K) i j =
        σ (A i j) := rfl
    simpa [Matrix.scalar_apply, Matrix.mul_diagonal, h2] using h1
  have hA' : ∀ i j, σ (A i j) = A i j * r := by
    intro i j
    calc σ (A i j) = σ (A i j) * r * r := by rw [mul_assoc, hr2, mul_one]
      _ = A i j * r := by rw [hent i j]
  have hdetA : (A : Matrix (Fin 2) (Fin 2) K).det = 1 := Matrix.SpecialLinearGroup.det_coe A
  rcases mul_self_eq_one_iff.mp hr2 with h1 | h1
  ·
    have hK0 : ∀ i j, A i j ∈ K₀ := fun i j => (hK₀ _).mpr (by rw [hA' i j, h1, mul_one])
    let N : Matrix (Fin 2) (Fin 2) K₀ := fun i j => ⟨A i j, hK0 i j⟩
    have hNmap : K₀.subtype.mapMatrix N = (A : Matrix (Fin 2) (Fin 2) K) := by
      ext i j
      rfl
    have hdetN : N.det = 1 := by
      apply K₀.subtype.injective
      rw [RingHom.map_det, hNmap, hdetA, map_one]
    refine ⟨QuotientGroup.mk ⟨N, hdetN⟩, ?_⟩
    show QuotientGroup.mk (Matrix.SpecialLinearGroup.map K₀.subtype ⟨N, hdetN⟩) =
      QuotientGroup.mk A
    congr 1
  ·
    exfalso
    have hzero : ∀ i j, A i j = 0 := fun i j =>
      kdL227_no_neg hσ3 (A i j) (by rw [hA' i j, h1, mul_neg_one])
    have hd := hdetA
    rw [Matrix.det_fin_two, hzero 0 0, hzero 0 1, hzero 1 0, hzero 1 1] at hd
    norm_num at hd

private theorem kdL227_fix_card_le {K : Type} [Field K] [Finite K] [CharP K 3]
    (hK : Nat.card K = 3 ^ 3) {σ : K ≃+* K} (hσ : orderOf σ = 3)
    (T : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K))
    (hT : IsPGroup 3 T) (hfix : ∀ t ∈ T, CFSG.GorensteinWalter.psl2FieldAut K σ t = t) :
    Nat.card T ≤ 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hσ3 : σ ^ 3 = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
  let K₀ : Subfield K := σ.toRingHom.eqLocusField (RingHom.id K)
  have hK₀ : ∀ x, x ∈ K₀ ↔ σ x = x := fun x => RingHom.mem_eqLocusField
  have hcard : Nat.card K₀ = 3 := kdL227_card_fix hK hσ hK₀
  have hPSL : Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K₀) = 12 :=
    CFSG.RankThree.PartTwo.KFacts.card_psl2_of_card_three hcard
  have hle : T ≤ (kdL227Incl K₀).range := fun t ht => kdL227_hard hσ3 hK₀ t (hfix t ht)
  have hdvd2 : Nat.card (kdL227Incl K₀).range ∣ 12 := by
    rw [← hPSL, CFSG.RankThree.PartTwo.KFacts.card_eq_card_ker_mul_card_range (kdL227Incl K₀)]
    exact Dvd.intro_left _ rfl
  have hdvd : Nat.card T ∣ 12 := (Subgroup.card_dvd_of_le hle).trans hdvd2
  obtain ⟨n, hn⟩ := hT.exists_card_eq
  rw [hn] at hdvd ⊢
  rcases n with _ | _ | n
  · norm_num
  · norm_num
  · exfalso
    have h9 : 9 ∣ 3 ^ (n + 1 + 1) := ⟨3 ^ n, by ring⟩
    have := h9.trans hdvd
    norm_num at this

private instance kdL227_finite_mulAut (G : Type) [Group G] [Finite G] : Finite (MulAut G) :=
  Finite.of_injective (fun f : MulAut G => f.toEquiv)
    (fun f g h => MulEquiv.ext fun x => congrArg (fun e : G ≃ G => e x) h)

private theorem kdL227_aut_card_le_nine {K : Type} [Field K] [Finite K] [CharP K 3]
    (hK : Nat.card K = 3 ^ 3)
    (D : Subgroup (MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)))
    (hD : IsElemAbelian 3 D)
    (hnot : ¬ D ≤ inner (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)) :
    Nat.card D ≤ 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set G := Matrix.ProjectiveSpecialLinearGroup (Fin 2) K with hGdef
  have hDpg : IsPGroup 3 D := fun x => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (hD.2 x.1 x.2)⟩
  have hcomm : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hD.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  obtain ⟨α, hαD, hαn⟩ : ∃ α ∈ D, α ∉ inner G := by
    by_contra h
    apply hnot
    intro α hα
    by_contra hα'
    exact h ⟨α, hα, hα'⟩
  have hα3 : α ^ 3 = 1 := hD.2 α hαD
  have hα1 : α ≠ 1 := fun h => hαn (by rw [h]; exact (inner G).one_mem)
  have hαord : orderOf α = 3 := orderOf_eq_prime hα3 hα1
  have hαpgl : α ∉ (CFSG.ComponentClassification.CatalogueSchreierLinearTwo.pglAction K).range := by
    rintro ⟨g, rfl⟩
    have hg3 : g ^ 3 = 1 := CFSG.RankThree.PartTwo.KFacts.pglAction_injective (K := K)
      (by rw [map_pow, hα3, map_one])
    obtain ⟨x, rfl⟩ := CFSG.RankThree.PartTwo.KFacts.exists_toPGL_eq_of_pow_three hg3
    exact hαn ⟨x, (CFSG.ComponentClassification.CatalogueSchreierLinearTwo.pglAction_toPGL K x).symm⟩
  obtain ⟨σ, hσord, g, hαeq⟩ :=
    CFSG.RankThree.PartTwo.KFacts.linear_two_prime_order_field_descent Nat.prime_three α hαord hαpgl
  let D₀ : Subgroup (MulAut G) := D ⊓ inner G
  have hcover : ∀ τ ∈ D, ∃ i : ℕ, α ^ i * τ ∈ D₀ := fun τ hτ => by
    obtain ⟨i, hi⟩ := CFSG.RankThree.PartTwo.KFacts.exists_pow_mul_isInnerAut_psl2 hDpg hαD hτ
      hα3 hαn (hD.2 τ hτ)
    exact ⟨i, Subgroup.mem_inf.mpr ⟨D.mul_mem (D.pow_mem hαD i) hτ, hi⟩⟩
  have hzD : Subgroup.zpowers α ≤ D := Subgroup.zpowers_le.mpr hαD
  let f : (Subgroup.zpowers α) × D₀ → D := fun p =>
    ⟨p.1.1 * p.2.1, D.mul_mem (hzD p.1.2) (Subgroup.mem_inf.mp p.2.2).1⟩
  have hf : Function.Surjective f := by
    intro τ
    obtain ⟨i, hi⟩ := hcover τ.1 τ.2
    refine ⟨(⟨(α ^ i)⁻¹, (Subgroup.zpowers α).inv_mem
      (Subgroup.pow_mem _ (Subgroup.mem_zpowers α) i)⟩, ⟨α ^ i * τ.1, hi⟩), Subtype.ext ?_⟩
    simp [f]
  have hcardD : Nat.card D ≤ 3 * Nat.card D₀ := by
    have h1 := Nat.card_le_card_of_surjective f hf
    rw [Nat.card_prod, Nat.card_zpowers, hαord] at h1
    exact h1
  have hinj : Function.Injective (MulAut.conj : G →* MulAut G) := by
    intro x y hxy
    have hz : x⁻¹ * y ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro h'
      have h := DFunLike.congr_fun hxy h'
      simp only [MulAut.conj_apply] at h
      calc h' * (x⁻¹ * y) = x⁻¹ * (x * h' * x⁻¹) * y := by group
        _ = x⁻¹ * (y * h' * y⁻¹) * y := by rw [h]
        _ = x⁻¹ * y * h' := by group
    rw [CFSG.GorensteinWalter.psl2_center_eq_bot K, Subgroup.mem_bot] at hz
    exact inv_mul_eq_one.mp hz
  set T : Subgroup G := D₀.comap (MulAut.conj : G →* MulAut G) with hTdef
  have hTmap : T.map (MulAut.conj : G →* MulAut G) = D₀ := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ht
    · intro hx
      obtain ⟨t, rfl⟩ := (Subgroup.mem_inf.mp hx).2
      exact ⟨t, hx, rfl⟩
  have hTcard : Nat.card D₀ = Nat.card T := by
    rw [← hTmap, Subgroup.card_map_of_injective hinj]
  have hTpg : IsPGroup 3 T := (hDpg.to_inf_left (K := inner G)).comap_of_injective _ hinj
  have hTfix : ∀ t ∈ T, α t = t := by
    intro t ht
    have ht' : MulAut.conj t ∈ D₀ := ht
    have hct : MulAut.conj t ∈ D := (Subgroup.mem_inf.mp ht').1
    have h1 : MulAut.conj (α t) = MulAut.conj t := by
      rw [← CFSG.RankThree.PartTwo.KFacts.mul_mulAutConj_mul_inv, hcomm α hαD _ hct]
      group
    exact hinj h1
  have hφα : (CFSG.ComponentClassification.CatalogueSchreierLinearTwo.pglAction K g)⁻¹ * α =
      CFSG.GorensteinWalter.psl2FieldAut K σ *
        (CFSG.ComponentClassification.CatalogueSchreierLinearTwo.pglAction K g)⁻¹ := by
    rw [hαeq]
    group
  have hT'card : Nat.card (T.map
      ((CFSG.ComponentClassification.CatalogueSchreierLinearTwo.pglAction K g)⁻¹ :
        MulAut G).toMonoidHom) = Nat.card T :=
    Subgroup.card_map_of_injective ((CFSG.ComponentClassification.CatalogueSchreierLinearTwo.pglAction
      K g)⁻¹).injective
  have hT'pg : IsPGroup 3 (T.map
      ((CFSG.ComponentClassification.CatalogueSchreierLinearTwo.pglAction K g)⁻¹ :
        MulAut G).toMonoidHom) := hTpg.map _
  have hT'fix : ∀ t' ∈ T.map
      ((CFSG.ComponentClassification.CatalogueSchreierLinearTwo.pglAction K g)⁻¹ :
        MulAut G).toMonoidHom,
      CFSG.GorensteinWalter.psl2FieldAut K σ t' = t' := by
    rintro _ ⟨t, ht, rfl⟩
    have h2 := congrArg (fun F : MulAut G => F t) hφα
    simp only [MulAut.mul_apply] at h2
    rw [hTfix t ht] at h2
    exact h2.symm
  have h3T : Nat.card T ≤ 3 := by
    rw [← hT'card]
    exact kdL227_fix_card_le hK hσord _ hT'pg hT'fix
  omega

private theorem kdL227_aut_bound {S : Type} [Group S] [Finite S]
    (e : S ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 3 3))
    (D : Subgroup (MulAut S)) (hD : IsElemAbelian 3 D) (hnot : ¬ D ≤ inner S) :
    Nat.card D ≤ 9 := by
  let D' : Subgroup (MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 3 3))) :=
    D.map (MulAut.congr e).toMonoidHom
  have hD' : IsElemAbelian 3 D' := CFSG.SectionRank.isElemAbelian_map hD _
  have hcard : Nat.card D' = Nat.card D :=
    Subgroup.card_map_of_injective (MulAut.congr e).injective
  have hnot' : ¬ D' ≤ inner (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 3 3)) := by
    intro h
    apply hnot
    intro τ hτ
    have hmem : MulAut.congr e τ ∈ D' := Subgroup.mem_map_of_mem _ hτ
    exact (CFSG.RankThree.PartTwo.KFacts.isInnerAut_congr e τ).mp (h hmem)
  have h := kdL227_aut_card_le_nine (K := GaloisField 3 3)
    (GaloisField.card 3 3 (by norm_num)) D' hD' hnot'
  rw [hcard] at h
  exact h

theorem kdL227_holds : KDL227 := by
  unfold KDL227
  refine ⟨?_, ?_⟩
  · intro E _ _ hq hZ hcat
    exact kdL227_center_eq_bot E hq hZ hcat
  · intro S _ _ hcat
    obtain ⟨e⟩ := kdL227_catalog_iso hcat
    refine ⟨kdL227_root_exists e, ?_⟩
    intro D hD hnot
    exact kdL227_aut_bound e D hD hnot

end CFSG.LocalAnalysis.GLTheoremA
