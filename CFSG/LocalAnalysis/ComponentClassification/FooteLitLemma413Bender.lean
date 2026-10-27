module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingInvolutionClass
public import CFSG.LieType.Suzuki.SuzukiOuterCyclic
public import CFSG.GH74.Bender.Suzuki
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma49Tools
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitSzEightSylow
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bAction
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ABGLocalTools

theorem isPGroup_two_zpowers_of_sq_eq_one {Y : Type*} [Group Y] {y : Y} (hy : y ^ 2 = 1) :
    IsPGroup 2 (zpowers y) := by
  rintro ⟨g, hg⟩
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hg
  refine ⟨1, Subtype.ext ?_⟩
  simp only [pow_one, SubgroupClass.coe_pow, OneMemClass.coe_one]
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy, one_zpow]

private theorem eq_one_of_mk_eq_one {G : Type*} [Group G] [Finite G] {K : Subgroup G}
    {Q : Subgroup ↥K} (hQ : IsPGroup 2 Q) {a : ↥K} (ha : a ∈ Q)
    (h1 : QuotientGroup.mk' (pPrimeCore 2 ↥K) a = 1) : a = 1 := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  obtain ⟨k, hk⟩ := hQ ⟨a, ha⟩
  have h2 : orderOf a ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one (by
    have := congrArg Subtype.val hk
    simpa using this)
  have h3 : orderOf a ∣ Nat.card (pPrimeCore 2 ↥K) := Subgroup.orderOf_dvd_natCard _ h1
  have hcop : Nat.Coprime (2 ^ k) (Nat.card (pPrimeCore 2 ↥K)) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr (odd_card_pPrimeCore_two ↥K))
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h2 h3)

theorem exists_mem_normalizer_conj_of_isBender {X : Type*} [Group X]
    [Finite X] (hX : Open.fusionIsBenderGroup X) (Q : Sylow 2 X) {x y : X}
    (hxQ : x ∈ (Q : Subgroup X)) (hyQ : y ∈ (Q : Subgroup X)) (hx : orderOf x = 2)
    (hy : orderOf y = 2) : ∃ n ∈ normalizer ((Q : Subgroup X) : Set X), n * x * n⁻¹ = y := by
  obtain ⟨q, k, -, hB⟩ := (AschbacherToolkit.BenderExt.benderData_of_isBenderGroup hX).borel
  have hse := (hB Q).1
  obtain ⟨c, hc⟩ := isConj_iff.mp (AschbacherStrongEmbedding.isConj_of_stronglyEmbedded hse hx hy)
  refine ⟨c, ?_, hc⟩
  by_contra hcN
  set B := normalizer ((Q : Subgroup X) : Set X) with hBdef
  have hcN' : c⁻¹ ∉ B := fun h => hcN (by simpa using inv_mem h)
  have hodd := hse.2.2 c⁻¹ hcN'
  have hmem : y ∈ B ⊓ B.map (MulAut.conj c⁻¹⁻¹).toMonoidHom := by
    refine mem_inf.mpr ⟨le_normalizer hyQ, x, le_normalizer hxQ, ?_⟩
    change c⁻¹⁻¹ * x * c⁻¹⁻¹⁻¹ = y
    simp only [inv_inv]
    exact hc
  have h1 := Subgroup.orderOf_dvd_natCard _ hmem
  rw [hy] at h1
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h1)

theorem exists_mem_normalizer_conj_of_isBender_quotient {G : Type*}
    [Group G] [Finite G] {K R : Subgroup G} (hRK : IsSylowOf 2 R K)
    (hX : Open.fusionIsBenderGroup (K ⧸ pPrimeCore 2 K)) {x y : G} (hxR : x ∈ R) (hyR : y ∈ R)
    (hx : orderOf x = 2) (hy : orderOf y = 2) :
    ∃ m ∈ K, m ∈ normalizer (R : Set G) ∧ m * x * m⁻¹ = y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := hRK
  set ρ := QuotientGroup.mk' (pPrimeCore 2 ↥K) with hρ
  have hQO : ∀ a ∈ (Q : Subgroup ↥K), ρ a = 1 → a = 1 := fun a ha h1 =>
    eq_one_of_mk_eq_one Q.isPGroup' ha h1
  rw [← hQ] at hxR hyR
  obtain ⟨x', hx'Q, rfl⟩ := mem_map.mp hxR
  obtain ⟨y', hy'Q, rfl⟩ := mem_map.mp hyR
  have hord : ∀ a ∈ (Q : Subgroup ↥K), orderOf (a : G) = 2 → orderOf (ρ a) = 2 := by
    intro a ha ha2
    have ha2' : a ^ 2 = 1 := Subtype.ext (by
      rw [SubgroupClass.coe_pow, OneMemClass.coe_one, ← ha2]
      exact pow_orderOf_eq_one _)
    apply orderOf_eq_prime
    · rw [← map_pow, ha2', map_one]
    · intro h1
      rw [hQO a ha h1, OneMemClass.coe_one, orderOf_one] at ha2
      omega
  set Q' : Sylow 2 (↥K ⧸ pPrimeCore 2 ↥K) := Q.mapSurjective (QuotientGroup.mk'_surjective _)
    with hQ'
  have hQ'c : (Q' : Subgroup _) = (Q : Subgroup ↥K).map ρ := Sylow.coe_mapSurjective _ _
  obtain ⟨n', hn', hn'x⟩ := exists_mem_normalizer_conj_of_isBender hX Q'
    (by rw [hQ'c]; exact mem_map_of_mem ρ hx'Q) (by rw [hQ'c]; exact mem_map_of_mem ρ hy'Q)
    (hord x' hx'Q hx) (hord y' hy'Q hy)
  have : Fact (IsPGroup 2 ↥(Q : Subgroup ↥K)) := ⟨Q.isPGroup'⟩
  have hnorm := CFSG.normalizer_map_quotient_eq_map_normalizer 2 (Q : Subgroup ↥K)
    (pPrimeCore 2 ↥K) inferInstance (Nat.coprime_two_left.mpr (odd_card_pPrimeCore_two ↥K))
  have hn'' : n' ∈ (normalizer ((Q : Subgroup ↥K) : Set ↥K)).map ρ := by
    rw [hQ'c] at hn'
    rw [← hnorm]
    exact hn'
  obtain ⟨n, hnN, rfl⟩ := mem_map.mp hn''
  have h1 : n * x' * n⁻¹ ∈ (Q : Subgroup ↥K) := (mem_normalizer_iff.mp hnN x').mp hx'Q
  have hnx : n * x' * n⁻¹ = y' := by
    have h2 : ρ ((n * x' * n⁻¹)⁻¹ * y') = 1 := by
      rw [map_mul, map_inv, map_mul, map_mul, map_inv, hn'x, inv_mul_cancel]
    have h3 := hQO _ (mul_mem (inv_mem h1) hy'Q) h2
    rwa [inv_mul_eq_one] at h3
  refine ⟨n, n.2, ?_, ?_⟩
  · rw [← hQ]
    exact le_normalizer_map K.subtype (mem_map_of_mem K.subtype hnN)
  · rw [← hnx]
    simp

theorem apply_eq_of_isCoverOverTwo_sz {Y : Type} [Group Y]
    [Finite Y] (h : IsCoverOverTwo Y (Open.Sz 1)) (T : Sylow 2 Y) (σ : MulAut Y)
    (hσ : σ * σ = 1) (hσT : ∀ t ∈ (T : Subgroup Y), σ t ∈ (T : Subgroup Y)) {x : Y}
    (hxT : x ∈ (T : Subgroup Y)) (hx : x ^ 2 = 1) : σ x = x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨π, hπs, hKZ, hKC, hK2⟩ := id h
  have : Finite (Open.Sz 1) := Finite.of_surjective π hπs
  obtain ⟨hsimp, hna⟩ := sz_one_simple_nonabelian
  obtain ⟨hq, hker⟩ := isQuasisimple_of_isCoverOverTwo (hX := hsimp) hna hπs hKZ hKC
  have : Group.IsPerfect Y := hq.1
  have e : Y ⧸ center Y ≃* Open.Sz 1 :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective π hπs)
  have hmodel := GH74.Bender.suzukiModel_of_mulEquiv_sz (G := ↥(Open.Sz 1)) le_rfl
    (MulEquiv.refl _)
  obtain ⟨-, -, hodd⟩ :=
    (LieType.Suzuki.Suzuki_model_and_perfect_cover_outer_cyclicity.{0} _ 2 _ hmodel).2 Y ⟨e⟩
  have hσin : σ ∈ OuterAutomorphisms.inner Y := by
    have h1 : orderOf (σ : OuterAutomorphisms.Outer Y) ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (by rw [← QuotientGroup.mk_pow, sq, hσ, QuotientGroup.mk_one])
    have h2 : orderOf (σ : OuterAutomorphisms.Outer Y) ∣
        Nat.card (OuterAutomorphisms.Outer Y) := orderOf_dvd_natCard _
    have h3 : orderOf (σ : OuterAutomorphisms.Outer Y) = 1 :=
      Nat.eq_one_of_dvd_coprimes (Nat.coprime_two_left.mpr hodd) h1 h2
    rw [orderOf_eq_one_iff] at h3
    exact (QuotientGroup.eq_one_iff σ).mp h3
  obtain ⟨y, rfl⟩ := hσin
  have hy2c : y ^ 2 ∈ center Y := by
    rw [mem_center_iff]
    intro g
    have h1 : (MulAut.conj y * MulAut.conj y) g = g := by rw [hσ]; rfl
    rw [MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_apply] at h1
    calc g * y ^ 2 = y * (y * g * y⁻¹) * y⁻¹ * y ^ 2 := by rw [h1]
      _ = y ^ 2 * g := by rw [sq]; group
  have hy2 := sq_eq_one_of_sq_mem_center_sz h hy2c
  have hyy : y * y = 1 := by rw [← sq]; exact hy2
  have hyT' : ∀ t ∈ (T : Subgroup Y), y * t * y⁻¹ ∈ (T : Subgroup Y) := fun t ht => by
    have h1 := hσT t ht
    rwa [MulAut.conj_apply] at h1
  have hyN : y ∈ normalizer ((T : Subgroup Y) : Set Y) := by
    rw [mem_normalizer_iff]
    intro t
    refine ⟨hyT' t, fun ht => ?_⟩
    have h1 := hyT' _ ht
    have h2 : y * (y * t * y⁻¹) * y⁻¹ = t := by
      calc y * (y * t * y⁻¹) * y⁻¹ = (y * y) * t * (y * y)⁻¹ := by group
        _ = t := by rw [hyy]; group
    rwa [h2] at h1
  have hyT : y ∈ (T : Subgroup Y) := by
    have hp : IsPGroup 2 ↥((T : Subgroup Y) ⊔ zpowers y) :=
      T.isPGroup'.to_sup_of_normal_left' (isPGroup_two_zpowers_of_sq_eq_one hy2)
        (zpowers_le.mpr hyN)
    have h1 := T.3 hp le_sup_left
    rw [← h1]
    exact mem_sup_right (mem_zpowers y)
  obtain ⟨A, -, -, hA2, hAinv⟩ := exists_omega_of_isCoverOverTwo_sz h T
  have hc : y * x = x * y := commute_of_sq_eq_one hA2 (hAinv y hyT hy2) (hAinv x hxT hx)
  rw [MulAut.conj_apply, hc, mul_inv_cancel_right]

theorem conj_eq_of_isCoverOverTwo_sz {G : Type} [Group G]
    [Finite G] {K R : Subgroup G} (hRK : IsSylowOf 2 R K)
    (hcov : IsCoverOverTwo (K ⧸ pPrimeCore 2 K) (Open.Sz 1)) {y : G}
    (hyK : y ∈ normalizer (K : Set G)) (hyR : y ∈ normalizer (R : Set G)) (hy : y ^ 2 = 1)
    {x : G} (hxR : x ∈ R) (hx : x ^ 2 = 1) : y * x * y⁻¹ = x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := hRK
  set ρ := QuotientGroup.mk' (pPrimeCore 2 ↥K) with hρ
  have hQO : ∀ a ∈ (Q : Subgroup ↥K), ρ a = 1 → a = 1 := fun a ha h1 =>
    eq_one_of_mk_eq_one Q.isPGroup' ha h1
  set σ := GSThmB.oddBarConj K ⟨y, hyK⟩ with hσdef
  have hσ : σ * σ = 1 := by
    rw [hσdef, ← map_mul]
    have h1 : (⟨y, hyK⟩ : ↥(normalizer (K : Set G))) * ⟨y, hyK⟩ = 1 :=
      Subtype.ext (by rw [Subgroup.coe_mul, OneMemClass.coe_one, ← sq]; exact hy)
    rw [h1, map_one]
  set T : Sylow 2 (↥K ⧸ pPrimeCore 2 ↥K) := Q.mapSurjective (QuotientGroup.mk'_surjective _)
    with hT
  have hTc : (T : Subgroup _) = (Q : Subgroup ↥K).map ρ := Sylow.coe_mapSurjective _ _
  have hyQ : ∀ q ∈ (Q : Subgroup ↥K),
      (⟨y * q * y⁻¹, (mem_normalizer_iff.mp hyK q).mp q.2⟩ : ↥K) ∈ (Q : Subgroup ↥K) := by
    intro q hq
    have h1 : (q : G) ∈ R := hQ ▸ mem_map_of_mem K.subtype hq
    have h2 : y * q * y⁻¹ ∈ R := (mem_normalizer_iff.mp hyR q).mp h1
    rw [← hQ] at h2
    obtain ⟨q', hq', hq'e⟩ := mem_map.mp h2
    have h3 : q' = ⟨y * q * y⁻¹, (mem_normalizer_iff.mp hyK q).mp q.2⟩ := Subtype.ext hq'e
    rw [← h3]
    exact hq'
  have hσT : ∀ t ∈ (T : Subgroup _), σ t ∈ (T : Subgroup _) := by
    intro t ht
    rw [hTc] at ht ⊢
    obtain ⟨q, hq, rfl⟩ := mem_map.mp ht
    rw [hσdef, hρ, QuotientGroup.mk'_apply, GSThmB.oddBarConj_apply_mk]
    exact mem_map_of_mem (QuotientGroup.mk' (pPrimeCore 2 ↥K)) (hyQ q hq)
  rw [← hQ] at hxR
  obtain ⟨x', hx'Q, rfl⟩ := mem_map.mp hxR
  have hx'2 : x' ^ 2 = 1 := Subtype.ext (by
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
    exact hx)
  have h1 := apply_eq_of_isCoverOverTwo_sz hcov T σ hσ hσT
    (by rw [hTc]; exact mem_map_of_mem ρ hx'Q) (by rw [← map_pow, hx'2, map_one])
  rw [hσdef, hρ, QuotientGroup.mk'_apply, GSThmB.oddBarConj_apply_mk] at h1
  have h2 : ρ ((⟨y * x' * y⁻¹, (mem_normalizer_iff.mp hyK x').mp x'.2⟩ : ↥K)⁻¹ * x') = 1 := by
    rw [map_mul, map_inv, hρ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, h1,
      inv_mul_cancel]
  have h3 := hQO _ (mul_mem (inv_mem (hyQ x' hx'Q)) hx'Q) h2
  rw [inv_mul_eq_one] at h3
  exact congrArg Subtype.val h3

end CFSG.ComponentClassification.FooteLit
