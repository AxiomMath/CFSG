module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma413Two

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherToolkit.Bender (sylowCenter mem_sylowCenter)

@[expose] def IsOmegaOneOf {G : Type*} [Group G] (A T : Subgroup G) : Prop :=
  A ≤ T ∧ (∀ x ∈ A, x ^ 2 = 1) ∧ ∀ x ∈ T, x ^ 2 = 1 → x ∈ A

theorem IsOmegaOneOf.eq {G : Type*} [Group G] {A A' T : Subgroup G} (h : IsOmegaOneOf A T)
    (h' : IsOmegaOneOf A' T) : A = A' :=
  le_antisymm (fun x hx => h'.2.2 x (h.1 hx) (h.2.1 x hx))
    (fun x hx => h.2.2 x (h'.1 hx) (h'.2.1 x hx))

private theorem eq_one_of_mk_eq_one' {G : Type*} [Group G] [Finite G] {K : Subgroup G}
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

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem exists_omega_of_isBender_quotient {K R : Subgroup G}
    (hRK : IsSylowOf 2 R K) (hX : Open.fusionIsBenderGroup (K ⧸ pPrimeCore 2 K)) :
    ∃ F : Subgroup G, IsOmegaOneOf F R ∧ 4 ≤ Nat.card F := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := hRK
  set ρ := QuotientGroup.mk' (pPrimeCore 2 ↥K) with hρ
  have hQO : ∀ a ∈ (Q : Subgroup ↥K), ρ a = 1 → a = 1 := fun a ha h1 =>
    eq_one_of_mk_eq_one' Q.isPGroup' ha h1
  set Q' : Sylow 2 (↥K ⧸ pPrimeCore 2 ↥K) := Q.mapSurjective (QuotientGroup.mk'_surjective _)
    with hQ'
  have hQ'c : (Q' : Subgroup _) = (Q : Subgroup ↥K).map ρ := Sylow.coe_mapSurjective _ _
  obtain ⟨q, k, hq4, hB⟩ := (AschbacherToolkit.BenderExt.benderData_of_isBenderGroup hX).borel
  obtain ⟨-, hZ2, hZcard, -⟩ := AschbacherToolkit.Bender.benderBorel_sylowCenter hB Q'
  set Z := sylowCenter (Q' : Subgroup (↥K ⧸ pPrimeCore 2 ↥K)) with hZ
  set F' := Z.comap ρ ⊓ (Q : Subgroup ↥K) with hF'
  have hinj : Function.Injective (ρ.comp F'.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [mem_bot]
    exact Subtype.ext (hQO x (mem_inf.mp x.2).2 hx)
  have hrange : (ρ.comp F'.subtype).range = Z := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      exact (mem_inf.mp x.2).1
    · intro y hy
      have hyQ : y ∈ (Q : Subgroup ↥K).map ρ := hQ'c ▸ (mem_sylowCenter.mp hy).1
      obtain ⟨x, hxQ, rfl⟩ := mem_map.mp hyQ
      exact ⟨⟨x, mem_inf.mpr ⟨hy, hxQ⟩⟩, rfl⟩
  refine ⟨F'.map K.subtype, ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [← hQ]
    exact map_mono inf_le_right
  · rintro _ ⟨x, hx, rfl⟩
    have h1 : ρ (x ^ 2) = 1 := by rw [map_pow]; exact hZ2 _ (mem_inf.mp hx).1
    have h2 := hQO (x ^ 2) (pow_mem (mem_inf.mp hx).2 2) h1
    rw [subtype_apply, ← SubgroupClass.coe_pow, h2, OneMemClass.coe_one]
  · intro x hxR hx2
    rw [← hQ] at hxR
    obtain ⟨y, hyQ, rfl⟩ := mem_map.mp hxR
    refine ⟨y, mem_inf.mpr ⟨?_, hyQ⟩, rfl⟩
    have hy2 : y ^ 2 = 1 := Subtype.ext (by simpa using hx2)
    exact AschbacherToolkit.Goldschmidt.mem_sylowCenter_of_sq_eq_one hB (by omega) Q'
      (hQ'c ▸ mem_map_of_mem ρ hyQ) (by rw [← map_pow, hy2, map_one])
  · rw [card_map_of_injective K.subtype_injective, Nat.card_congr
      (MonoidHom.ofInjective hinj).toEquiv, hrange, hZcard]
    exact hq4

theorem exists_mem_normalizer_conj_of_quotient {K R : Subgroup G} (Q : Sylow 2 ↥K)
    (hQ : (Q : Subgroup ↥K).map K.subtype = R) {x' y' : ↥K} (hx' : x' ∈ (Q : Subgroup ↥K))
    (hy' : y' ∈ (Q : Subgroup ↥K)) {n' : ↥K ⧸ pPrimeCore 2 ↥K}
    (hn' : n' ∈ normalizer (((Q : Subgroup ↥K).map (QuotientGroup.mk' (pPrimeCore 2 ↥K)) :
      Subgroup (↥K ⧸ pPrimeCore 2 ↥K)) : Set (↥K ⧸ pPrimeCore 2 ↥K)))
    (hn'x : n' * QuotientGroup.mk' (pPrimeCore 2 ↥K) x' * n'⁻¹ =
      QuotientGroup.mk' (pPrimeCore 2 ↥K) y') :
    ∃ m ∈ K, m ∈ normalizer (R : Set G) ∧ m * (x' : G) * m⁻¹ = y' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ρ := QuotientGroup.mk' (pPrimeCore 2 ↥K) with hρ
  have hQO : ∀ a ∈ (Q : Subgroup ↥K), ρ a = 1 → a = 1 := fun a ha h1 =>
    eq_one_of_mk_eq_one' Q.isPGroup' ha h1
  have : Fact (IsPGroup 2 ↥(Q : Subgroup ↥K)) := ⟨Q.isPGroup'⟩
  have hnorm := CFSG.normalizer_map_quotient_eq_map_normalizer 2 (Q : Subgroup ↥K)
    (pPrimeCore 2 ↥K) inferInstance (Nat.coprime_two_left.mpr (odd_card_pPrimeCore_two ↥K))
  have hn'' : n' ∈ (normalizer ((Q : Subgroup ↥K) : Set ↥K)).map ρ := by
    rw [← hnorm]
    exact hn'
  obtain ⟨n, hnN, rfl⟩ := mem_map.mp hn''
  have h1 : n * x' * n⁻¹ ∈ (Q : Subgroup ↥K) := (mem_normalizer_iff.mp hnN x').mp hx'
  have hnx : n * x' * n⁻¹ = y' := by
    have h2 : ρ ((n * x' * n⁻¹)⁻¹ * y') = 1 := by
      rw [map_mul, map_inv, map_mul, map_mul, map_inv, hn'x, inv_mul_cancel]
    have h3 := hQO _ (mul_mem (inv_mem h1) hy') h2
    rwa [inv_mul_eq_one] at h3
  refine ⟨n, n.2, ?_, ?_⟩
  · rw [← hQ]
    exact le_normalizer_map K.subtype (mem_map_of_mem K.subtype hnN)
  · rw [← hnx]
    simp

theorem exists_mem_normalizer_conj_of_isCoverOverTwo_sz
    {Y : Type} [Group Y] [Finite Y] (h : IsCoverOverTwo Y (Open.Sz 1)) (T : Sylow 2 Y) {x y : Y}
    (hxT : x ∈ (T : Subgroup Y)) (hyT : y ∈ (T : Subgroup Y)) (hx2 : x ^ 2 = 1) (hy2 : y ^ 2 = 1)
    (hxZ : x ∉ center Y) (hyZ : y ∉ center Y) :
    ∃ n ∈ normalizer ((T : Subgroup Y) : Set Y), n * x * n⁻¹ = y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨π, hπs, hKZ, hKC, hK2⟩ := id h
  have : Finite (Open.Sz 1) := Finite.of_surjective π hπs
  obtain ⟨hsimp, hna⟩ := sz_one_simple_nonabelian
  obtain ⟨hq, hker⟩ := isQuasisimple_of_isCoverOverTwo (hX := hsimp) hna hπs hKZ hKC
  have : Group.IsPerfect Y := hq.1
  have hZ2 : ∀ z ∈ center Y, z ^ 2 = 1 := by
    intro z hz
    rw [← hker] at hz
    have h1 := Subgroup.orderOf_dvd_natCard π.ker hz
    rw [hK2] at h1
    exact orderOf_dvd_iff_pow_eq_one.mp h1
  have hB := Open.bender_suzuki_borel_full 1 le_rfl
  have hBen : Open.fusionIsBenderGroup (Open.Sz 1) :=
    Or.inr (Or.inr ⟨1, le_rfl, ⟨MulEquiv.refl _⟩⟩)
  set Q : Sylow 2 (Open.Sz 1) := T.mapSurjective hπs with hQ
  have hQc : (Q : Subgroup (Open.Sz 1)) = (T : Subgroup Y).map π := Sylow.coe_mapSurjective _ _
  have hkerp : IsPGroup 2 π.ker := IsPGroup.of_card (n := 1) (by rw [hK2, pow_one])
  have hkerT : π.ker ≤ (T : Subgroup Y) := by
    have hp : IsPGroup 2 ↥((T : Subgroup Y) ⊔ π.ker) :=
      T.isPGroup'.to_sup_of_normal_right hkerp
    rw [← T.3 hp le_sup_left]
    exact le_sup_right
  have hpre : ∀ w : Y, π w ∈ (Q : Subgroup (Open.Sz 1)) → w ∈ (T : Subgroup Y) := by
    intro w hw
    rw [hQc] at hw
    obtain ⟨t, ht, htw⟩ := mem_map.mp hw
    have h1 : t⁻¹ * w ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, htw, inv_mul_cancel]
    rw [show w = t * (t⁻¹ * w) by group]
    exact mul_mem ht (hkerT h1)
  have hπQ : ∀ w ∈ (T : Subgroup Y), π w ∈ (Q : Subgroup (Open.Sz 1)) := fun w hw =>
    hQc ▸ mem_map_of_mem π hw
  have hord : ∀ w ∈ (T : Subgroup Y), w ^ 2 = 1 → w ∉ center Y → orderOf (π w) = 2 :=
    fun w hw hw2 hwZ => orderOf_eq_prime (by rw [← map_pow, hw2, map_one]) (fun h1 =>
      hwZ (hker ▸ (MonoidHom.mem_ker.mpr h1)))
  obtain ⟨n', hn', hn'x⟩ := exists_mem_normalizer_conj_of_isBender hBen Q (hπQ x hxT)
    (hπQ y hyT) (hord x hxT hx2 hxZ) (hord y hyT hy2 hyZ)
  obtain ⟨n₀, rfl⟩ := hπs n'
  have hn₀T : ∀ w ∈ (T : Subgroup Y), n₀ * w * n₀⁻¹ ∈ (T : Subgroup Y) := fun w hw => by
    apply hpre
    rw [map_mul, map_mul, map_inv]
    exact (mem_normalizer_iff.mp hn' _).mp (hπQ w hw)
  have hn₀T' : ∀ w ∈ (T : Subgroup Y), n₀⁻¹ * w * n₀⁻¹⁻¹ ∈ (T : Subgroup Y) := fun w hw => by
    apply hpre
    rw [inv_inv, map_mul, map_mul, map_inv]
    have h1 := (mem_normalizer_iff.mp (inv_mem hn') _).mp (hπQ w hw)
    rwa [inv_inv] at h1
  have hn₀N : n₀ ∈ normalizer ((T : Subgroup Y) : Set Y) := by
    rw [mem_normalizer_iff]
    intro w
    refine ⟨hn₀T w, fun hw => ?_⟩
    have h1 := hn₀T' _ hw
    rwa [show n₀⁻¹ * (n₀ * w * n₀⁻¹) * n₀⁻¹⁻¹ = w by group] at h1
  set w := n₀ * x * n₀⁻¹ with hw
  have hc : w * y⁻¹ ∈ center Y := by
    rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hw, map_mul, map_mul, map_inv, hn'x,
      mul_inv_cancel]
  by_cases hc1 : w * y⁻¹ = 1
  · exact ⟨n₀, hn₀N, mul_inv_eq_one.mp hc1⟩
  have hyc : ∀ t ∈ (T : Subgroup Y), y * t * y⁻¹ * t⁻¹ ∈ center Y := by
    intro t ht
    have hyZQ := AschbacherToolkit.Goldschmidt.mem_sylowCenter_of_sq_eq_one hB (by norm_num) Q
      (hπQ y hyT) (by rw [← map_pow, hy2, map_one])
    rw [← hker, MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv,
      ((mem_sylowCenter.mp hyZQ).2 (π t) (hπQ t ht)).symm]
    group
  obtain ⟨r, hrT, hr⟩ := Goldschmidt.MFSz8.exists_commutator_eq le_rfl π hπs hker hZ2 T hyc hyZ hc
  refine ⟨r⁻¹ * n₀, mul_mem (inv_mem (le_normalizer hrT)) hn₀N, ?_⟩
  have hwr : w = r * y * r⁻¹ := by
    have h1 : r * y * r⁻¹ = w * y⁻¹ * y := by rw [← hr]; group
    rw [h1]
    group
  calc r⁻¹ * n₀ * x * (r⁻¹ * n₀)⁻¹ = r⁻¹ * w * r := by rw [hw]; group
    _ = y := by rw [hwr]; group

theorem exists_mem_normalizer_conj_of_isCoverOverTwo_sz_quotient
    {K R : Subgroup G} (hRK : IsSylowOf 2 R K)
    (hcov : IsCoverOverTwo (K ⧸ pPrimeCore 2 K) (Open.Sz 1)) {s x y : G} (hsR : s ∈ R)
    (hs1 : s ≠ 1) (hsc : ∀ k ∈ K, k * s = s * k) (hxR : x ∈ R) (hyR : y ∈ R)
    (hx2 : x ^ 2 = 1) (hy2 : y ^ 2 = 1) (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hxs : x ≠ s)
    (hys : y ≠ s) : ∃ m ∈ K, m ∈ normalizer (R : Set G) ∧ m * x * m⁻¹ = y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRK' := hRK
  obtain ⟨Q, hQ⟩ := hRK'
  set ρ := QuotientGroup.mk' (pPrimeCore 2 ↥K) with hρ
  have hQO : ∀ a ∈ (Q : Subgroup ↥K), ρ a = 1 → a = 1 := fun a ha h1 =>
    eq_one_of_mk_eq_one' Q.isPGroup' ha h1
  set Q' : Sylow 2 (↥K ⧸ pPrimeCore 2 ↥K) := Q.mapSurjective (QuotientGroup.mk'_surjective _)
    with hQ'
  have hQ'c : (Q' : Subgroup _) = (Q : Subgroup ↥K).map ρ := Sylow.coe_mapSurjective _ _
  rw [← hQ] at hxR hyR hsR
  obtain ⟨x', hx'Q, rfl⟩ := mem_map.mp hxR
  obtain ⟨y', hy'Q, rfl⟩ := mem_map.mp hyR
  obtain ⟨s', hs'Q, rfl⟩ := mem_map.mp hsR
  obtain ⟨π, hπs, hKZ, hKC, hK2⟩ := id hcov
  have : Finite (Open.Sz 1) := Finite.of_surjective π hπs
  obtain ⟨hsimp, hna⟩ := sz_one_simple_nonabelian
  obtain ⟨-, hker⟩ := isQuasisimple_of_isCoverOverTwo (hX := hsimp) hna hπs hKZ hKC
  have hsZ : ρ s' ∈ center (↥K ⧸ pPrimeCore 2 ↥K) := by
    rw [mem_center_iff]
    intro g
    obtain ⟨g', rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥K) g
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hsc _ g'.2)
  have hs'1 : ρ s' ≠ 1 := fun h1 => hs1 (by rw [hQO s' hs'Q h1]; rfl)
  have hZ : ∀ w : ↥K, w ∈ (Q : Subgroup ↥K) → ρ w ∈ center (↥K ⧸ pPrimeCore 2 ↥K) →
      w = 1 ∨ w = s' := by
    intro w hwQ hwZ
    rw [← hker] at hwZ hsZ
    have hcard := hK2
    by_contra hne
    push Not at hne
    have h1 : ρ w ≠ 1 := fun h1 => hne.1 (hQO w hwQ h1)
    have h2 : ρ w ≠ ρ s' := fun h2 => hne.2 (by
      have h3 := hQO _ (mul_mem (inv_mem hwQ) hs'Q)
        (by rw [map_mul, map_inv, h2, inv_mul_cancel])
      rw [inv_mul_eq_one] at h3
      exact h3)
    have hsub : ({1, ρ w, ρ s'} : Set _) ⊆ (π.ker : Set _) := by
      intro u hu
      rcases hu with rfl | rfl | rfl
      · exact one_mem _
      · exact hwZ
      · exact hsZ
    have h3 := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_eq_three.mpr ⟨1, ρ w, ρ s', h1.symm, hs'1.symm, h2, rfl⟩,
      ← Nat.card_coe_set_eq, SetLike.coe_sort_coe] at h3
    omega
  have hx2' : (ρ x') ^ 2 = 1 := by
    rw [← map_pow, show x' ^ 2 = 1 from Subtype.ext (by simpa using hx2), map_one]
  have hy2' : (ρ y') ^ 2 = 1 := by
    rw [← map_pow, show y' ^ 2 = 1 from Subtype.ext (by simpa using hy2), map_one]
  have hxZ : ρ x' ∉ center (↥K ⧸ pPrimeCore 2 ↥K) := fun h1 => by
    rcases hZ x' hx'Q h1 with h2 | h2
    · exact hx1 (by rw [h2]; rfl)
    · exact hxs (by rw [h2])
  have hyZ : ρ y' ∉ center (↥K ⧸ pPrimeCore 2 ↥K) := fun h1 => by
    rcases hZ y' hy'Q h1 with h2 | h2
    · exact hy1 (by rw [h2]; rfl)
    · exact hys (by rw [h2])
  obtain ⟨n', hn', hn'x⟩ := exists_mem_normalizer_conj_of_isCoverOverTwo_sz hcov Q'
    (hQ'c ▸ mem_map_of_mem ρ hx'Q) (hQ'c ▸ mem_map_of_mem ρ hy'Q) hx2' hy2' hxZ hyZ
  rw [hQ'c] at hn'
  exact exists_mem_normalizer_conj_of_quotient Q hQ hx'Q hy'Q hn' hn'x

omit [Finite G] in
theorem IsOmegaOneOf.mem_normalizer {A R : Subgroup G} (h : IsOmegaOneOf A R) {m : G}
    (hm : m ∈ normalizer (R : Set G)) : m ∈ normalizer (A : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact h.2.2 _ ((mem_normalizer_iff.mp hm x).mp (h.1 hx))
      (by rw [conj_pow, h.2.1 x hx, mul_one, mul_inv_cancel])
  · intro hx
    have hxR : x ∈ R := (mem_normalizer_iff.mp hm x).mpr (h.1 hx)
    have h1 := h.2.1 _ hx
    rw [conj_pow, mul_inv_eq_one, mul_eq_left] at h1
    exact h.2.2 x hxR h1

theorem exists_omega_of_footeInCC
    (h : FooteSec4 G L) (h47 : FooteThm47Statement)
    (hST : GSThmB.SuzukiTausskyInput) (hAsc : Foote5.AschbacherCentralCoreInput)
    (h2An : GSThmB.Solomon2AnInput) {M : Subgroup G} (hM : IsFooteM L M) {s : G}
    (hs : FooteInCC M s) {T : Subgroup G}
    (hT : IsSylowOf 2 T (coreActionKernel M ⊓ centralizer ({s} : Set G))) :
    ∃ A : Subgroup G, IsOmegaOneOf A T ∧ s ∈ A ∧ 8 ≤ Nat.card A ∧
      (s ∉ footeK L s → (∀ x ∈ A, x ∈ footeK L s ∨ x * s ∈ footeK L s) ∧
        4 ≤ Nat.card ↥(A ⊓ footeK L s)) ∧
      (s ∈ footeK L s → A ≤ footeK L s) ∧
      ∀ x ∈ A, ∀ y ∈ A, x ≠ 1 → y ≠ 1 → x ≠ s → y ≠ s →
        (x ∈ footeK L s ↔ y ∈ footeK L s) →
        ∃ m ∈ normalizer (M : Set G), m ∈ normalizer (A : Set G) ∧ m * s = s * m ∧
          m * x * m⁻¹ = y := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hs' := hs
  obtain ⟨hs2, hsC, hCs⟩ := hs'
  obtain ⟨hBN, -, hBs, -⟩ := foote_lemma_4_9_core h h47 hST hM hs2 hsC hCs
  obtain ⟨hKB, -, -, -, htype, -⟩ := foote_lemma_4_9 h h47 hST hAsc h2An hM hs2 hsC hCs
  obtain ⟨R₀, hR₀, hR₀C⟩ := exists_isSylowOf_footeK_le h h47 hST hAsc h2An hM hs
  set K := footeK L s with hK
  set C := coreActionKernel M with hC
  set N := normalizer (M : Set G) with hN
  have hss : s * s = 1 := by rw [← sq, ← hs2, pow_orderOf_eq_one]
  have hs2' : s ^ 2 = 1 := by rw [sq]; exact hss
  have hs1 : s ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hs2; omega
  have hKs : K ≤ centralizer ({s} : Set G) := hKB.trans hBs
  set D := C ⊓ centralizer ({s} : Set G) with hD
  have hTD : T ≤ D := hT.le
  have hTC : T ≤ C := hTD.trans inf_le_left
  have hTs : T ≤ centralizer ({s} : Set G) := hTD.trans inf_le_right
  have hKCD : K ⊓ C ≤ D := fun x hx =>
    mem_inf.mpr ⟨(mem_inf.mp hx).2, hKs (mem_inf.mp hx).1⟩
  have hDKC : D ≤ normalizer ((K ⊓ C : Subgroup G) : Set G) := fun d hd =>
    mem_normalizer_inf_of_mem (mem_normalizer_footeK (hBN (mem_inf.mp hd).2))
      (le_normalizer (mem_inf.mp hd).1)
  have hTKC := hT.inf_of_le_normalizer hKCD hDKC
  have hTKC' : T ⊓ (K ⊓ C) = T ⊓ K := by
    ext x
    simp only [mem_inf]
    exact ⟨fun hx => ⟨hx.1, hx.2.1⟩, fun hx => ⟨hx.1, hx.2, hTC hx.1⟩⟩
  rw [hTKC'] at hTKC
  have hR₀KC : IsSylowOf 2 R₀ (K ⊓ C) := hR₀.of_le (le_inf hR₀.le hR₀C) inf_le_left
  set R := T ⊓ K with hR
  have hRK : IsSylowOf 2 R K := by
    apply isSylowOf_of_card (hTKC.le.trans inf_le_left)
    rw [hTKC.card_eq, ← hR₀KC.card_eq, hR₀.card_eq]
  have hRC : R ≤ C := inf_le_left.trans hTC
  have hsT : s ∈ T := by
    have hsN : zpowers s ≤ normalizer (T : Set G) := zpowers_le.mpr
      (mem_normalizer_of_forall_commute fun u hu => mem_centralizer_singleton_iff.mp (hTs hu))
    have hp : IsPGroup 2 ↥(T ⊔ zpowers s) :=
      hT.isPGroup.to_sup_of_normal_left' (isPGroup_two_zpowers_of_sq_eq_one hs2') hsN
    have hle : T ⊔ zpowers s ≤ D :=
      sup_le hTD (zpowers_le.mpr (mem_inf.mpr ⟨hsC, mem_centralizer_singleton_iff.mpr rfl⟩))
    have h1 := hT.eq_of_le le_sup_left hle hp
    rw [← h1]
    exact mem_sup_right (mem_zpowers s)
  have hsc : ∀ k ∈ K, k * s = s * k := fun k hk => mem_centralizer_singleton_iff.mp (hKs hk)
  have hzs : ∀ m ∈ K, m ∈ normalizer (zpowers s : Set G) := fun m hm =>
    mem_normalizer_of_forall_commute fun w hw => by
      obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hw
      exact ((Commute.zpow_left (Commute.symm (hsc m hm)) i)).eq
  rcases htype with ⟨hBen, hsK⟩ | ⟨hcov, hsK⟩
  ·
    obtain ⟨F, hF, hF4⟩ := exists_omega_of_isBender_quotient hRK hBen
    set A := F ⊔ zpowers s with hA
    have hFR : F ≤ R := hF.1
    have hFs : F ≤ centralizer ({s} : Set G) := hFR.trans (inf_le_right.trans hKs)
    have hmemA : ∀ a ∈ A, a ∈ F ∨ a * s ∈ F := fun a ha =>
      mem_or_mul_mem_of_mem_sup_zpowers hFs hss ha
    have hsq : ∀ a : G, a * s = s * a → (a * s) ^ 2 = 1 → a ^ 2 = 1 := by
      intro a has ha2
      rw [sq] at ha2 ⊢
      calc a * a = a * s * (a * s) * (s * s) := by
            rw [hss, mul_one]
            calc a * a = a * (s * s) * a := by rw [hss, mul_one]
              _ = a * s * (s * a) := by group
              _ = a * s * (a * s) := by rw [← has]
        _ = 1 := by rw [ha2, hss, one_mul]
    have hsq' : ∀ a : G, a * s = s * a → a ^ 2 = 1 → (a * s) ^ 2 = 1 := by
      intro a has ha2
      rw [sq] at ha2 ⊢
      calc a * s * (a * s) = a * (s * a) * s := by group
        _ = a * (a * s) * s := by rw [has]
        _ = 1 := by rw [← mul_assoc, ha2, one_mul, hss]
    have hA2 : ∀ a ∈ A, a ^ 2 = 1 := by
      intro a ha
      rcases hmemA a ha with h1 | h1
      · exact hF.2.1 a h1
      · refine hsq a ?_ (hF.2.1 _ h1)
        have h2 : a * s * s = s * (a * s) := mem_centralizer_singleton_iff.mp (hFs h1)
        calc a * s = a * s * s * s := by rw [mul_assoc (a * s), hss, mul_one]
          _ = s * (a * s) * s := by rw [h2]
          _ = s * a := by rw [mul_assoc, mul_assoc, hss, mul_one]
    have hAT : A ≤ T := sup_le (hFR.trans inf_le_left) (zpowers_le.mpr hsT)
    have hAinv : ∀ x ∈ T, x ^ 2 = 1 → x ∈ A := by
      intro x hxT hx2
      by_cases hx1 : x = 1
      · rw [hx1]
        exact one_mem A
      have hxo : orderOf x = 2 := orderOf_eq_prime hx2 hx1
      have hxs : x * s = s * x := mem_centralizer_singleton_iff.mp (hTs hxT)
      rcases mem_or_mul_mem_footeK h h47 hST hAsc h2An hM hs (hTC hxT) hxs hxo with hxK | hxsK
      · exact mem_sup_left (hF.2.2 x (mem_inf.mpr ⟨hxT, hxK⟩) hx2)
      · have h1 := hF.2.2 (x * s) (mem_inf.mpr ⟨mul_mem hxT hsT, hxsK⟩) (hsq' x hxs hx2)
        rw [show x = x * s * s by rw [mul_assoc, hss, mul_one]]
        exact mul_mem (mem_sup_left h1) (mem_sup_right (mem_zpowers s))
    have hsA : s ∈ A := mem_sup_right (mem_zpowers s)
    have hFK : F ≤ A ⊓ K := le_inf le_sup_left (hFR.trans inf_le_right)
    have h8 : 8 ≤ Nat.card A := by
      have hsF : s ∉ F := fun h1 => hsK (hFR h1).2
      have hdvd := card_dvd_of_le (le_sup_left : F ≤ A)
      obtain ⟨k, hk⟩ := hdvd
      have hk1 : k ≠ 1 := by
        rintro rfl
        rw [mul_one] at hk
        exact hsF ((eq_of_le_of_card_ge (le_sup_left : F ≤ A) hk.le) ▸ hsA)
      have hk0 : k ≠ 0 := by
        rintro rfl
        rw [mul_zero] at hk
        exact Nat.card_pos.ne' hk
      rw [hk]
      calc 8 = 4 * 2 := by norm_num
        _ ≤ Nat.card F * k := Nat.mul_le_mul hF4 (by omega)
    have hBorel : ∀ u ∈ F, ∀ v ∈ F, u ≠ 1 → v ≠ 1 → ∃ m ∈ N, m ∈ normalizer (A : Set G) ∧
        m * s = s * m ∧ m * u * m⁻¹ = v := by
      intro u hu v hv hu1 hv1
      obtain ⟨m, hmK, hmR, hmuv⟩ := exists_mem_normalizer_conj_of_isBender_quotient hRK hBen
        (hFR hu) (hFR hv) (orderOf_eq_prime (hF.2.1 u hu) hu1) (orderOf_eq_prime (hF.2.1 v hv) hv1)
      have hms : m * s = s * m := hsc m hmK
      have hmN : m ∈ N := by
        have hTC' : R ⊔ zpowers s ≤ C := sup_le hRC (zpowers_le.mpr hsC)
        have hus : s ≠ u := fun h1 => hsK (h1 ▸ (hFR hu).2)
        have hW := isKleinFour_sup_zpowers (hF.2.1 u hu) hs2' hu1 hs1 hus
          (mem_centralizer_singleton_iff.mp (hFs hu))
        have hWT : zpowers u ⊔ zpowers s ≤ R ⊔ zpowers s :=
          sup_le_sup_right (zpowers_le.mpr (hFR hu)) _
        exact foote_cor_4_8_iv h h47 hST hM hTC' hW hWT
          (inf_normalizer_le_normalizer_sup R (zpowers s) (mem_inf.mpr ⟨hmR, hzs m hmK⟩))
      have hmA : m ∈ normalizer (A : Set G) :=
        inf_normalizer_le_normalizer_sup F (zpowers s)
          (mem_inf.mpr ⟨hF.mem_normalizer hmR, hzs m hmK⟩)
      exact ⟨m, hmN, hmA, hms, hmuv⟩
    refine ⟨A, ⟨hAT, hA2, hAinv⟩, hsA, h8, fun _ => ⟨fun x hx => ?_,
      hF4.trans (card_le_of_le hFK)⟩, fun h1 => absurd h1 hsK, ?_⟩
    · rcases hmemA x hx with h1 | h1
      · exact Or.inl (hFR h1).2
      · exact Or.inr (hFR h1).2
    · intro x hxA y hyA hx1 hy1 hxs hys hxy
      by_cases hxK : x ∈ K
      · have hyK := hxy.mp hxK
        exact hBorel x (hF.2.2 x (mem_inf.mpr ⟨hAT hxA, hxK⟩) (hA2 x hxA))
          y (hF.2.2 y (mem_inf.mpr ⟨hAT hyA, hyK⟩) (hA2 y hyA)) hx1 hy1
      · have hyK : y ∉ K := fun h1 => hxK (hxy.mpr h1)
        have hxsF : x * s ∈ F := (hmemA x hxA).resolve_left fun h1 => hxK (hFR h1).2
        have hysF : y * s ∈ F := (hmemA y hyA).resolve_left fun h1 => hyK (hFR h1).2
        have hxs1 : x * s ≠ 1 := fun h1 => hxs (by
          calc x = x * s * s := by rw [mul_assoc, hss, mul_one]
            _ = s := by rw [h1, one_mul])
        have hys1 : y * s ≠ 1 := fun h1 => hys (by
          calc y = y * s * s := by rw [mul_assoc, hss, mul_one]
            _ = s := by rw [h1, one_mul])
        obtain ⟨m, hmN, hmA, hms, hm⟩ := hBorel (x * s) hxsF (y * s) hysF hxs1 hys1
        refine ⟨m, hmN, hmA, hms, ?_⟩
        have hmsm : m * s * m⁻¹ = s := by rw [hms, mul_inv_cancel_right]
        calc m * x * m⁻¹ = m * (x * s) * m⁻¹ * (m * s * m⁻¹) := by
              rw [show m * (x * s) * m⁻¹ * (m * s * m⁻¹) = m * x * (s * s) * m⁻¹ by group,
                hss, mul_one]
          _ = y * s * s := by rw [hm, hmsm]
          _ = y := by rw [mul_assoc, hss, mul_one]
  ·
    obtain ⟨A, hAR, hA16, hA2, hAinv⟩ := exists_omega_of_isCoverOverTwo_sz_quotient hRK hcov
    have hAo : IsOmegaOneOf A R := ⟨hAR, hA2, hAinv⟩
    have hsR : s ∈ R := mem_inf.mpr ⟨hsT, hsK⟩
    have hAT : A ≤ T := hAR.trans inf_le_left
    have hAK : A ≤ K := hAR.trans inf_le_right
    have hTA : ∀ x ∈ T, x ^ 2 = 1 → x ∈ A := by
      intro x hxT hx2
      by_cases hx1 : x = 1
      · rw [hx1]
        exact one_mem A
      have hxo : orderOf x = 2 := orderOf_eq_prime hx2 hx1
      have hxs : x * s = s * x := mem_centralizer_singleton_iff.mp (hTs hxT)
      rcases mem_or_mul_mem_footeK h h47 hST hAsc h2An hM hs (hTC hxT) hxs hxo with hxK | hxsK
      · exact hAinv x (mem_inf.mpr ⟨hxT, hxK⟩) hx2
      · have hxK : x ∈ K := by
          have h1 := mul_mem hxsK (inv_mem hsK)
          rwa [mul_inv_cancel_right] at h1
        exact hAinv x (mem_inf.mpr ⟨hxT, hxK⟩) hx2
    have hsA : s ∈ A := hAinv s hsR hs2'
    refine ⟨A, ⟨hAT, hA2, hTA⟩, hsA, by omega, fun h1 => absurd hsK h1, fun _ => hAK, ?_⟩
    intro x hxA y hyA hx1 hy1 hxs hys _
    obtain ⟨m, hmK, hmR, hm⟩ := exists_mem_normalizer_conj_of_isCoverOverTwo_sz_quotient hRK
      hcov hsR hs1 hsc (hAR hxA) (hAR hyA) (hA2 x hxA) (hA2 y hyA) hx1 hy1 hxs hys
    have hmN : m ∈ N := by
      obtain ⟨W, hW, hWA⟩ := exists_isKleinFour_le hA2 (by omega)
      exact foote_cor_4_8_iv h h47 hST hM hRC hW (hWA.trans hAR) hmR
    exact ⟨m, hmN, hAo.mem_normalizer hmR, hsc m hmK, hm⟩

end CFSG.ComponentClassification.FooteLit
