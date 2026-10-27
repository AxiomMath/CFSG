module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingOutsideSix
public import CFSG.Adapters.LinearSmallCatalog
public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma21L2
public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma21Simple

public section

namespace CFSG.ComponentClassification.AS76b

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.OuterAutomorphisms
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem isKleinFour_of_card_four {R : Subgroup G} (hRe : IsElemAbelian 2 R)
    (hR4 : Nat.card R = 4) : IsKleinFour R := by
  have : Nontrivial R := by
    rw [← Finite.one_lt_card_iff_nontrivial, hR4]
    norm_num
  refine ⟨hR4, (Monoid.exponent_eq_prime_iff Nat.prime_two).mpr fun g hg => ?_⟩
  refine orderOf_eq_prime ?_ hg
  exact Subtype.ext (by simpa using hRe.2 g g.2)

theorem conj_eq_of_card_four {R : Subgroup G} (hRe : IsElemAbelian 2 R) (hR4 : Nat.card R = 4)
    {r y : G} (hrR : r ∈ R) (hr1 : r ≠ 1) (hyR : ∀ s ∈ R, y * s * y⁻¹ ∈ R)
    (hyr : y * r * y⁻¹ = r) (hy : Odd (orderOf y)) {s : G} (hs : s ∈ R) :
    y * s * y⁻¹ = s := by
  by_contra hne
  have := isKleinFour_of_card_four hRe hR4
  have hs1 : s ≠ 1 := by
    rintro rfl
    exact hne (by group)
  have hsr : s ≠ r := by
    rintro rfl
    exact hne hyr
  have hs'1 : y * s * y⁻¹ ≠ 1 := fun h => hs1 (by
    have : s = y⁻¹ * (y * s * y⁻¹) * y := by group
    rw [this, h]
    group)
  have hs'r : y * s * y⁻¹ ≠ r := fun h => hsr (by
    have h' : y * s * y⁻¹ = y * r * y⁻¹ := by rw [h, hyr]
    simpa using h')
  have hs' : y * s * y⁻¹ = r * s := by
    have h := IsKleinFour.eq_mul_of_ne_all (G := R) (x := ⟨r, hrR⟩) (y := ⟨s, hs⟩)
      (z := ⟨y * s * y⁻¹, hyR s hs⟩)
      (fun h => hr1 (congrArg Subtype.val h)) (fun h => hs1 (congrArg Subtype.val h))
      (fun h => hsr (congrArg Subtype.val h).symm) (fun h => hs'1 (congrArg Subtype.val h))
      (fun h => hs'r (congrArg Subtype.val h)) (fun h => hne (congrArg Subtype.val h))
    exact congrArg Subtype.val h
  have hrr : r * r = 1 := by
    have := hRe.2 r hrR
    rwa [sq] at this
  have hy2 : y * (y * s * y⁻¹) * y⁻¹ = s := by
    calc y * (y * s * y⁻¹) * y⁻¹ = y * (r * s) * y⁻¹ := by rw [hs']
      _ = (y * r * y⁻¹) * (y * s * y⁻¹) := by group
      _ = r * (r * s) := by rw [hyr, hs']
      _ = s := by rw [← mul_assoc, hrr, one_mul]
  have hpow : ∀ j : ℕ, y ^ (2 * j + 1) * s * (y ^ (2 * j + 1))⁻¹ = y * s * y⁻¹ := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      calc y ^ (2 * (j + 1) + 1) * s * (y ^ (2 * (j + 1) + 1))⁻¹
          = y * (y * (y ^ (2 * j + 1) * s * (y ^ (2 * j + 1))⁻¹) * y⁻¹) * y⁻¹ := by group
        _ = y * s * y⁻¹ := by rw [ih, hy2]
  obtain ⟨k, hk⟩ := hy
  have h := hpow k
  rw [← hk, pow_orderOf_eq_one, one_mul, inv_one, mul_one] at h
  exact hne h.symm




theorem sq_conj_eq_of_card_four {R : Subgroup G} (hRe : IsElemAbelian 2 R) (hR4 : Nat.card R = 4)
    {r x : G} (hrR : r ∈ R) (hr1 : r ≠ 1) (hxR : ∀ s ∈ R, x * s * x⁻¹ ∈ R)
    (hxr : x * r * x⁻¹ = r) {s : G} (hs : s ∈ R) : x ^ 2 * s * (x ^ 2)⁻¹ = s := by
  by_cases hfix : x * s * x⁻¹ = s
  · calc x ^ 2 * s * (x ^ 2)⁻¹ = x * (x * s * x⁻¹) * x⁻¹ := by rw [sq]; group
      _ = s := by rw [hfix, hfix]
  have := isKleinFour_of_card_four hRe hR4
  have hs1 : s ≠ 1 := by
    rintro rfl
    exact hfix (by group)
  have hsr : s ≠ r := by
    rintro rfl
    exact hfix hxr
  have hs'1 : x * s * x⁻¹ ≠ 1 := fun h => hs1 (by
    have : s = x⁻¹ * (x * s * x⁻¹) * x := by group
    rw [this, h]
    group)
  have hs'r : x * s * x⁻¹ ≠ r := fun h => hsr (by
    have h' : x * s * x⁻¹ = x * r * x⁻¹ := by rw [h, hxr]
    simpa using h')
  have hs' : x * s * x⁻¹ = r * s := by
    have h := IsKleinFour.eq_mul_of_ne_all (G := R) (x := ⟨r, hrR⟩) (y := ⟨s, hs⟩)
      (z := ⟨x * s * x⁻¹, hxR s hs⟩)
      (fun h => hr1 (congrArg Subtype.val h)) (fun h => hs1 (congrArg Subtype.val h))
      (fun h => hsr (congrArg Subtype.val h).symm) (fun h => hs'1 (congrArg Subtype.val h))
      (fun h => hs'r (congrArg Subtype.val h)) (fun h => hfix (congrArg Subtype.val h))
    exact congrArg Subtype.val h
  have hrr : r * r = 1 := by
    have := hRe.2 r hrR
    rwa [sq] at this
  calc x ^ 2 * s * (x ^ 2)⁻¹ = x * (x * s * x⁻¹) * x⁻¹ := by rw [sq]; group
    _ = x * (r * s) * x⁻¹ := by rw [hs']
    _ = (x * r * x⁻¹) * (x * s * x⁻¹) := by group
    _ = r * (r * s) := by rw [hxr, hs']
    _ = s := by rw [← mul_assoc, hrr, one_mul]

omit [Finite G] in
theorem le_oddCoreIn_of_le_normalizer {K X : Subgroup G} (hXK : X ≤ K)
    (hX : K ≤ normalizer (X : Set G)) (hodd : Odd (Nat.card X)) : X ≤ oddCoreIn K := by
  have hn : (X.subgroupOf K).Normal := (normal_subgroupOf_iff_le_normalizer hXK).mpr hX
  have hodd' : Odd (Nat.card (X.subgroupOf K)) := by
    rwa [Nat.card_congr (subgroupOfEquivOfLe hXK).toEquiv]
  have hle := le_assemblyOddCore hn hodd'
  intro x hx
  exact ⟨⟨x, hXK hx⟩, hle hx, rfl⟩

theorem eq_one_of_mem_isPGroup_of_odd_orderOf {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup 2 P) {x : P} {m : ℕ} (hm : Odd m) (hx : orderOf x ∣ m) : x = 1 := by
  obtain ⟨k, hk⟩ := hP.exists_orderOf_eq_pow x
  rcases k with _ | k
  · rwa [pow_zero, orderOf_eq_one_iff] at hk
  · exfalso
    rw [hk, pow_succ] at hx
    exact (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr ((dvd_mul_left 2 _).trans hx))

theorem inf_centralizer_eq_of_forall_prime {K R : Subgroup G} (hR : IsSylowOf 2 R K)
    (hRe : IsElemAbelian 2 R) {r : G} (hrR : r ∈ R)
    (hnoodd : ∀ y ∈ K ⊓ centralizer ({r} : Set G), ∀ p : ℕ, p.Prime → p ≠ 2 →
      orderOf y = p → False) :
    K ⊓ centralizer ({r} : Set G) = R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hH : IsPGroup 2 (K ⊓ centralizer ({r} : Set G) : Subgroup G) := by
    refine (isPGroup_iff_card_dvd_pow).mpr ⟨Nat.card (K ⊓ centralizer ({r} : Set G) :
      Subgroup G), ?_⟩
    have hpos : Nat.card (K ⊓ centralizer ({r} : Set G) : Subgroup G) ≠ 0 := Nat.card_pos.ne'
    refine (Nat.dvd_pow_self_iff hpos (by norm_num)).mpr fun q hq => ?_
    obtain ⟨hqp, hqdvd, -⟩ := Nat.mem_primeFactors.mp hq
    by_contra hq2
    have : Fact q.Prime := ⟨hqp⟩
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' q hqdvd
    have h2mem : (2 : ℕ) ∈ Nat.primeFactors 2 :=
      Nat.mem_primeFactors.mpr ⟨Nat.prime_two, dvd_refl 2, by norm_num⟩
    exact hnoodd y y.2 q hqp (fun h => hq2 (h ▸ h2mem)) (by rw [Subgroup.orderOf_coe, hy])
  have hRle : R ≤ K ⊓ centralizer ({r} : Set G) := fun s hs =>
    ⟨hR.le hs, mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hRe.1.is_comm.comm ⟨r, hrR⟩ ⟨s, hs⟩)).symm⟩
  exact hR.eq_of_le hRle inf_le_left hH

theorem inf_centralizer_eq_of_twoElements_le {K R : Subgroup G} (hR : IsSylowOf 2 R K)
    (hRe : IsElemAbelian 2 R) (hR4 : Nat.card R = 4) (hO : oddCoreIn K = ⊥)
    (h2 : ∀ k ∈ K, ∀ n : ℕ, k ^ 2 ^ n = 1 → k ∈ R) {r : G} (hrR : r ∈ R) (hr1 : r ≠ 1) :
    K ⊓ centralizer ({r} : Set G) = R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRK := hR.le
  have hRcomm : ∀ s ∈ R, ∀ t ∈ R, s * t = t * s := fun s hs t ht =>
    congrArg Subtype.val (hRe.1.is_comm.comm ⟨s, hs⟩ ⟨t, ht⟩)
  have hRn : ∀ k ∈ K, ∀ s ∈ R, k * s * k⁻¹ ∈ R := fun k hk s hs =>
    h2 _ (mul_mem (mul_mem hk (hRK hs)) (inv_mem hk)) 1 (by
      rw [pow_one, sq, show k * s * k⁻¹ * (k * s * k⁻¹) = k * (s * s) * k⁻¹ by group,
        ← sq, hRe.2 s hs]
      group)
  set C := K ⊓ centralizer (R : Set G) with hCdef
  have hCK : C ≤ K := inf_le_left
  have hKC : K ≤ normalizer (C : Set G) := by
    intro k hk
    rw [mem_normalizer_iff]
    intro x
    have key : ∀ k ∈ K, ∀ x ∈ C, k * x * k⁻¹ ∈ C := by
      intro k hk x hx
      refine Subgroup.mem_inf.mpr ⟨K.mul_mem (K.mul_mem hk (hCK hx)) (K.inv_mem hk),
        mem_centralizer_iff.mpr ?_⟩
      intro s hs
      have hs' : k⁻¹ * s * k ∈ R := by simpa using hRn k⁻¹ (inv_mem hk) s hs
      have h1 := mem_centralizer_iff.mp hx.2 _ hs'
      calc s * (k * x * k⁻¹) = k * ((k⁻¹ * s * k) * x) * k⁻¹ := by group
        _ = k * (x * (k⁻¹ * s * k)) * k⁻¹ := by rw [h1]
        _ = k * x * k⁻¹ * s := by group
    constructor
    · exact key k hk x
    · intro hx
      have := key k⁻¹ (inv_mem hk) _ hx
      simpa [mul_assoc] using this
  have hOC : oddCoreIn C = ⊥ := by
    have hle := le_oddCoreIn_of_le_normalizer ((oddCoreIn_le C).trans hCK)
      (hKC.trans (normalizer_le_normalizer_oddCoreIn C)) (odd_card_oddCoreIn C)
    rw [hO] at hle
    exact le_bot_iff.mp hle
  have hnoodd : ∀ y ∈ K ⊓ centralizer ({r} : Set G), ∀ p : ℕ, p.Prime → p ≠ 2 →
      orderOf y = p → False := by
    intro y hy p hp hp2 hyp
    have hyodd : Odd (orderOf y) := hyp ▸ hp.odd_of_ne_two hp2
    have hyr : y * r * y⁻¹ = r := by
      have := mem_centralizer_singleton_iff.mp hy.2
      rw [this, mul_inv_cancel_right]
    have hyR : ∀ s ∈ R, y * s * y⁻¹ = s := fun s hs =>
      conj_eq_of_card_four hRe hR4 hrR hr1 (hRn y hy.1) hyr hyodd hs
    have hyC : y ∈ C := ⟨hy.1, mem_centralizer_iff.mpr fun s hs => by
      have := hyR s hs
      calc s * y = y * s * y⁻¹ * y := by rw [this]
        _ = y * s := by group⟩
    have hRC : R ≤ C := fun s hs => ⟨hRK hs, mem_centralizer_iff.mpr fun t ht => hRcomm t ht s hs⟩
    have hRCs : IsSylowOf 2 R C := hR.of_le hRC hCK
    obtain ⟨P, hP⟩ := hRCs.exists_sylow_eq_subgroupOf
    have hPc : normalizer (P : Subgroup C) ≤ centralizer ((P : Subgroup C) : Set C) := by
      intro c _
      rw [mem_centralizer_iff]
      intro p hp
      rw [hP] at hp
      exact Subtype.ext (mem_centralizer_iff.mp c.2.2 _ hp)
    set τ := MonoidHom.transferSylow P hPc with hτ
    have hτy : τ ⟨y, hyC⟩ = 1 := by
      have hPp : IsPGroup 2 (P : Subgroup C) := P.isPGroup'
      refine eq_one_of_mem_isPGroup_of_odd_orderOf hPp hyodd ?_
      refine (orderOf_map_dvd τ _).trans ?_
      rw [Subgroup.orderOf_mk]
    have hN := MonoidHom.not_dvd_card_ker_transferSylow P hPc
    have hNodd : Odd (Nat.card τ.ker) := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hN)
    have hNle : τ.ker ≤ CFSG.Assembly.oddCore C :=
      le_assemblyOddCore (MonoidHom.normal_ker τ) hNodd
    have hyO : y ∈ oddCoreIn C := ⟨⟨y, hyC⟩, hNle hτy, rfl⟩
    rw [hOC, mem_bot] at hyO
    rw [hyO, orderOf_one] at hyp
    exact hp.one_lt.ne' hyp.symm
  exact inf_centralizer_eq_of_forall_prime hR hRe hrR hnoodd



theorem card_psl2_four : Nat.card PSL(2, GaloisField 2 2) = 60 := by
  rw [CFSG.Walter.psl2_even_card (by norm_num)]
  norm_num

theorem inf_centralizer_eq_of_caseD {K R T Y : Subgroup G} {g : G}
    (hK : TightlyEmbedded K) (hR : IsSylowOf 2 R K) (hRe : IsElemAbelian 2 R)
    (hR4 : Nat.card R = 4) (hO : oddCoreIn K = ⊥) (hg : g ∉ normalizer (K : Set G))
    (hT : IsSylowOf 2 T (rightConjugate K g)) (hTN : T ≤ normalizer (K : Set G))
    (hY : Y = oUpperTwoPrime (K ⊔ T)) {n : ℕ} (hn : 2 ≤ n)
    (φ : Y →* Multiplicative (Fin n → ZMod 2) ×
      Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n))
    (hφ : Function.Surjective φ) (hker : φ.ker = (oddCoreIn K).subgroupOf Y)
    {r : G} (hrR : r ∈ R) (hr1 : r ≠ 1) :
    K ⊓ centralizer ({r} : Set G) = R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn0 : n ≠ 0 := by omega
  set K₂ := oUpperTwoPrime K with hK₂
  set a := (Nat.card K).factorization 2 with ha
  have han : a ≤ n := factorization_le_of_caseD hK hg hT hTN hY hn0 φ hφ hker
  have hRa : Nat.card R = 2 ^ a := hR.card_eq
  have hK₂K : K₂ ≤ K := oUpperTwoPrime_le K
  have hK₂Y : K₂ ≤ Y := by
    rw [hY]
    exact closure_mono fun x ⟨hx, k, hk⟩ => ⟨mem_sup_left hx, k, hk⟩
  have hR2 : ∀ r ∈ R, r ^ 2 = 1 := fun r hr => hRe.2 r hr
  have hRK₂ : R ≤ K₂ := fun r hr => mem_oUpperTwoPrime (hR.le hr) (n := 1) (by simpa using hR2 r hr)
  have hφO : ∀ y : Y, φ y = 1 ↔ (y : G) ∈ oddCoreIn K := fun y => by
    rw [← MonoidHom.mem_ker, hker, mem_subgroupOf]
  let ψ : Y →* PSL(2, GaloisField 2 n) :=
    (CFSG.Walter.psl2MulEquivSL2OfCharTwo (K := GaloisField 2 n)).symm.toMonoidHom.comp
      ((MonoidHom.snd _ _).comp φ)
  have hψ : Function.Surjective ψ := by
    intro x
    obtain ⟨y, hy⟩ := hφ (1, CFSG.Walter.psl2MulEquivSL2OfCharTwo x)
    refine ⟨y, ?_⟩
    change (CFSG.Walter.psl2MulEquivSL2OfCharTwo (K := GaloisField 2 n)).symm (φ y).2 = x
    rw [hy]
    exact MulEquiv.symm_apply_apply _ _
  have hψφ : ∀ y : Y, ψ y = 1 → φ y ^ 2 = 1 := by
    intro y hy
    have h2 : (φ y).2 = 1 := by simpa [ψ] using hy
    ext1
    · exact sq_eq_one_multiplicative _
    · simp [h2]
  have hcardL : Nat.card PSL(2, GaloisField 2 n) = 2 ^ n * ((2 ^ n) ^ 2 - 1) :=
    CFSG.Walter.psl2_even_card hn0
  have hK₂n : (K₂.subgroupOf Y).Normal :=
    (normal_subgroupOf_iff_le_normalizer hK₂Y).mpr ((hY.le.trans (oUpperTwoPrime_le _)).trans
      ((sup_le le_normalizer hTN).trans (normalizer_le_normalizer_oUpperTwoPrime K)))
  have hL : IsSimpleGroup PSL(2, GaloisField 2 n) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by
      rw [GaloisField.card 2 n hn0]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn)
  have hJn : ((K₂.subgroupOf Y).map ψ).Normal := hK₂n.map ψ hψ
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((K₂.subgroupOf Y).map ψ) with hJ | hJ
  ·
    have hsq : ∀ k ∈ K₂, k ^ 2 ∈ oddCoreIn K := by
      intro k hk
      have hk1 : ψ ⟨k, hK₂Y hk⟩ = 1 := by
        have : ψ ⟨k, hK₂Y hk⟩ ∈ (K₂.subgroupOf Y).map ψ := ⟨⟨k, hK₂Y hk⟩, hk, rfl⟩
        rwa [hJ, mem_bot] at this
      have := (hφO (⟨k, hK₂Y hk⟩ ^ 2)).mp (by rw [map_pow]; exact hψφ _ hk1)
      simpa using this
    refine inf_centralizer_eq_of_twoElements_le hR hRe hR4 hO (fun k hk m hm => ?_) hrR hr1
    have := twoElements_le_of_sq_mem hR hsq k hk m hm
    rwa [hO, bot_sup_eq] at this
  let ψ₂ : K₂.subgroupOf Y →* PSL(2, GaloisField 2 n) := ψ.comp (K₂.subgroupOf Y).subtype
  have hψ₂r : ψ₂.range = ⊤ := by rw [MonoidHom.range_comp, range_subtype, hJ]
  have hcardK₂ : Nat.card ψ₂.ker * Nat.card PSL(2, GaloisField 2 n) = Nat.card K₂ := by
    have h := Subgroup.card_ker_mul_card_range ψ₂
    rw [hψ₂r, card_top, Nat.card_congr (subgroupOfEquivOfLe hK₂Y).toEquiv] at h
    exact h
  have hRK₂s : IsSylowOf 2 R K₂ := hR.of_le hRK₂ hK₂K
  have hdvdK₂ : ∀ j, 2 ^ j ∣ Nat.card K₂ → j ≤ a := fun j hj => by
    have := pow_dvd_card_of_isSylowOf hRK₂s hj
    rw [hRa] at this
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp this
  have hna : n ≤ a := hdvdK₂ n (by
    rw [← hcardK₂, hcardL]
    exact dvd_mul_of_dvd_right (dvd_mul_right _ _) _)
  have hkerodd : Odd (Nat.card ψ₂.ker) := by
    refine Nat.not_even_iff_odd.mp fun he => ?_
    obtain ⟨m, hm⟩ := even_iff_two_dvd.mp he
    have h := hdvdK₂ (n + 1) (by
      rw [← hcardK₂, hcardL, hm, pow_succ]
      exact ⟨m * ((2 ^ n) ^ 2 - 1), by ring⟩)
    omega
  have hkey : ∀ y : Y, (y : G) ∈ K₂ → ψ y = 1 → (y : G) = 1 := by
    intro y hyK hy
    have hx : (⟨y, hyK⟩ : K₂.subgroupOf Y) ∈ ψ₂.ker := hy
    have hdvd1 : orderOf (φ y) ∣ 2 := orderOf_dvd_of_pow_eq_one (hψφ y hy)
    have hdvd2 : orderOf (φ y) ∣ Nat.card ψ₂.ker := by
      let χ := φ.comp ((K₂.subgroupOf Y).subtype.comp ψ₂.ker.subtype)
      have h1 : χ ⟨_, hx⟩ = φ y := rfl
      rw [← h1]
      exact (orderOf_map_dvd χ _).trans (orderOf_dvd_natCard _)
    have h1 : orderOf (φ y) = 1 :=
      Nat.eq_one_of_dvd_coprimes (Nat.coprime_two_left.mpr hkerodd) hdvd1 hdvd2
    have := (hφO y).mp (orderOf_eq_one_iff.mp h1)
    rwa [hO, mem_bot] at this
  have hψ₂inj : Function.Injective ψ₂ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨⟨z, hzY⟩, hzK₂⟩ hz
    have h := hkey ⟨z, hzY⟩ (mem_subgroupOf.mp hzK₂) hz
    rw [mem_bot]
    exact Subtype.ext (Subtype.ext h)
  have hψ₂surj : Function.Surjective ψ₂ := MonoidHom.range_eq_top.mp hψ₂r
  have ha2 : a = 2 := by
    have h : 2 ^ a = 2 ^ 2 := by rw [← hRa, hR4]; norm_num
    exact Nat.pow_right_injective le_rfl h
  have hn2 : n = 2 := by omega
  subst hn2
  have h4 : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  obtain ⟨e4⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five
    (GaloisField 2 2) (Or.inl h4)
  let eA : K₂ ≃* alternatingGroup (Fin 5) :=
    ((subgroupOfEquivOfLe hK₂Y).symm.trans (MulEquiv.ofBijective ψ₂ ⟨hψ₂inj, hψ₂surj⟩)).trans
      ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2
        (GaloisField 2 2)).trans e4)
  have hOut : Nat.card (Outer K₂) ∣ 2 := by
    rw [Nat.card_congr (equivalence eA).toEquiv]
    exact CFSG.ComponentClassification.CatalogueSchreierAlternating.outer_card_dvd_two_outside_six
      (Or.inl rfl)
  have hrY : r ∈ Y := hK₂Y (hRK₂ hrR)
  have hψr : orderOf (ψ ⟨r, hrY⟩) = 2 := by
    refine orderOf_eq_prime ?_ fun h => hr1 (hkey ⟨r, hrY⟩ (hRK₂ hrR) h)
    rw [← map_pow]
    have : (⟨r, hrY⟩ : Y) ^ 2 = 1 := Subtype.ext (by simpa using hR2 r hrR)
    rw [this, map_one]
  have hC := CFSG.Walter.psl2_centralizer_isPGroup_of_charTwo hψr
  have hS2 : IsPGroup 2 (K₂ ⊓ centralizer ({r} : Set G) : Subgroup G) := by
    rintro ⟨z, hzK₂, hzr⟩
    have hzY : z ∈ Y := hK₂Y hzK₂
    have hzC : ψ ⟨z, hzY⟩ ∈ centralizer ({ψ ⟨r, hrY⟩} : Set PSL(2, GaloisField 2 2)) := by
      rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (mem_centralizer_singleton_iff.mp hzr)
    obtain ⟨k, hk⟩ := hC ⟨_, hzC⟩
    refine ⟨k, Subtype.ext ?_⟩
    have hk' : ψ (⟨z, hzY⟩ ^ 2 ^ k) = 1 := by
      rw [map_pow]
      exact congrArg Subtype.val hk
    have := hkey (⟨z, hzY⟩ ^ 2 ^ k) (by simpa using pow_mem hzK₂ (2 ^ k)) hk'
    simpa using this
  have hCK₂ : K₂ ⊓ centralizer ({r} : Set G) = R := by
    refine hR.eq_of_le (fun s hs => ⟨hRK₂ hs, mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hRe.1.is_comm.comm ⟨r, hrR⟩ ⟨s, hs⟩)).symm⟩)
      (inf_le_left.trans hK₂K) hS2
  set Cc := K ⊓ centralizer (K₂ : Set G) with hCc
  have hCcodd : Odd (Nat.card Cc) := by
    refine Nat.not_even_iff_odd.mp fun he => ?_
    obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp he)
    have ht2 : (t : G) ^ 2 = 1 := by
      rw [← Subgroup.coe_pow, ← ht, pow_orderOf_eq_one, Subgroup.coe_one]
    have htK₂ : (t : G) ∈ K₂ := mem_oUpperTwoPrime t.2.1 (n := 1) (by simpa using ht2)
    have htY : (t : G) ∈ Y := hK₂Y htK₂
    have ht1 : (t : G) ≠ 1 := by
      intro h
      rw [← Subgroup.orderOf_coe, h, orderOf_one] at ht
      omega
    have hψt : orderOf (ψ ⟨t, htY⟩) = 2 := by
      refine orderOf_eq_prime ?_ fun h => ht1 (hkey ⟨t, htY⟩ htK₂ h)
      rw [← map_pow]
      have : (⟨t, htY⟩ : Y) ^ 2 = 1 := Subtype.ext (by simpa using ht2)
      rw [this, map_one]
    have hCt := CFSG.Walter.psl2_centralizer_isPGroup_of_charTwo hψt
    have htop : centralizer ({ψ ⟨t, htY⟩} : Set PSL(2, GaloisField 2 2)) = ⊤ := by
      refine eq_top_iff.mpr fun x _ => ?_
      obtain ⟨⟨⟨w, hwY⟩, hwK₂⟩, rfl⟩ := hψ₂surj x
      rw [mem_centralizer_singleton_iff]
      change ψ ⟨w, hwY⟩ * ψ ⟨t, htY⟩ = ψ ⟨t, htY⟩ * ψ ⟨w, hwY⟩
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (mem_centralizer_iff.mp t.2.2 w (mem_subgroupOf.mp hwK₂))
    rw [htop] at hCt
    have h60 : IsPGroup 2 PSL(2, GaloisField 2 2) :=
      hCt.of_equiv Subgroup.topEquiv
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp h60
    rw [card_psl2_four] at hm
    have h3 : (3 : ℕ) ∣ 2 ^ m := hm ▸ (by norm_num : (3 : ℕ) ∣ 60)
    exact absurd ((Nat.prime_dvd_prime_iff_eq (by norm_num) Nat.prime_two).mp
      ((Nat.Prime.dvd_of_dvd_pow (by norm_num) h3))) (by norm_num)
  have hKCc : K ≤ normalizer (Cc : Set G) := by
    intro k hk
    have hkK₂ : k ∈ normalizer (K₂ : Set G) :=
      normalizer_le_normalizer_oUpperTwoPrime K (le_normalizer hk)
    have key : ∀ k ∈ K, k ∈ normalizer (K₂ : Set G) → ∀ x ∈ Cc, k * x * k⁻¹ ∈ Cc := by
      intro k hk hkN x hx
      refine Subgroup.mem_inf.mpr ⟨K.mul_mem (K.mul_mem hk hx.1) (K.inv_mem hk),
        mem_centralizer_iff.mpr fun z hz => ?_⟩
      have hz' : k⁻¹ * z * k ∈ K₂ := by
        have := (mem_normalizer_iff.mp (inv_mem hkN) z).mp hz
        simpa using this
      have h1 := mem_centralizer_iff.mp hx.2 _ hz'
      calc z * (k * x * k⁻¹) = k * ((k⁻¹ * z * k) * x) * k⁻¹ := by group
        _ = k * (x * (k⁻¹ * z * k)) * k⁻¹ := by rw [h1]
        _ = k * x * k⁻¹ * z := by group
    rw [mem_normalizer_iff]
    intro x
    refine ⟨key k hk hkK₂ x, fun hx => ?_⟩
    have := key k⁻¹ (inv_mem hk) (inv_mem hkK₂) _ hx
    simpa [mul_assoc] using this
  have hCc1 : Cc = ⊥ := by
    have := le_oddCoreIn_of_le_normalizer inf_le_left hKCc hCcodd
    rw [hO] at this
    exact le_bot_iff.mp this
  refine inf_centralizer_eq_of_forall_prime hR hRe hrR fun y hy p hp hp2 hyp => ?_
  have hyN : y ∈ normalizer (K₂ : Set G) :=
    normalizer_le_normalizer_oUpperTwoPrime K (le_normalizer hy.1)
  set β := K₂.normalizerMonoidHom ⟨y, hyN⟩ with hβ
  have hβp : orderOf β ∣ p := by
    rw [← hyp]
    refine (orderOf_map_dvd _ _).trans ?_
    rw [Subgroup.orderOf_mk]
  have hβin : β ∈ OuterAutomorphisms.inner K₂ := by
    have h1 : orderOf (QuotientGroup.mk' (OuterAutomorphisms.inner K₂) β) ∣ p :=
      (orderOf_map_dvd _ _).trans hβp
    have h2 : orderOf (QuotientGroup.mk' (OuterAutomorphisms.inner K₂) β) ∣ 2 :=
      (_root_.orderOf_dvd_natCard _).trans hOut
    have h3 : orderOf (QuotientGroup.mk' (OuterAutomorphisms.inner K₂) β) = 1 :=
      Nat.eq_one_of_dvd_coprimes ((Nat.coprime_primes hp Nat.prime_two).mpr hp2) h1 h2
    rw [orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h3
    exact h3
  obtain ⟨k₀, hk₀⟩ := hβin
  have hconj : ∀ z ∈ K₂, y * z * y⁻¹ = (k₀ : G) * z * (k₀ : G)⁻¹ := by
    intro z hz
    have h := congrArg (fun φ : MulAut K₂ => ((φ ⟨z, hz⟩ : K₂) : G)) hk₀
    simp only [MulAut.conj_apply, coe_mul, coe_inv, hβ,
      normalizerMonoidHom_apply_apply_coe] at h
    exact h.symm
  have hc : (k₀ : G)⁻¹ * y ∈ Cc := by
    refine ⟨K.mul_mem (K.inv_mem (hK₂K k₀.2)) hy.1, mem_centralizer_iff.mpr fun z hz => ?_⟩
    have h := hconj z hz
    calc z * ((k₀ : G)⁻¹ * y) = (k₀ : G)⁻¹ * ((k₀ : G) * z * (k₀ : G)⁻¹) * y := by group
      _ = (k₀ : G)⁻¹ * (y * z * y⁻¹) * y := by rw [h]
      _ = (k₀ : G)⁻¹ * y * z := by group
  rw [hCc1, mem_bot, inv_mul_eq_one] at hc
  have hyR : y ∈ R := by
    rw [← hCK₂]
    exact ⟨hc ▸ k₀.2, hy.2⟩
  have hy2 : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one (hR2 y hyR)
  rw [hyp] at hy2
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hy2)

theorem inf_centralizer_eq_of_oddCoreIn_eq_bot (h4 : Asc75Theorem4)
    {K R : Subgroup G} (hK : TightlyEmbedded K) (hR : IsSylowOf 2 R K) (hRe : IsElemAbelian 2 R)
    (hR4 : Nat.card R = 4) (hF : IsSimpleGroup (CFSG.generalizedFitting G)) (hKn : ¬ K.Normal)
    (hO : oddCoreIn K = ⊥) {r : G} (hrR : r ∈ R) (hr1 : r ≠ 1) :
    K ⊓ centralizer ({r} : Set G) = R := by
  by_cases hA : twoPrimeLayerIn K = oddCoreIn K
  · refine inf_centralizer_eq_of_twoElements_le hR hRe hR4 hO (fun k hk m hm => ?_) hrR hr1
    have := twoElements_le_of_layer_eq_bot hR hRe ((twoPrimeLayerIn_eq_oddCoreIn_iff K).mp hA) k
      hk m hm
    rwa [hO, bot_sup_eq] at this
  · rcases h4 G K hK hA with hB | ⟨h1, -⟩ | ⟨g, hg, T, hT, hTN, n, hn, φ, hφ, hker⟩
    · exact (false_of_normalIn_twoPrimeLayerIn_top hK hKn hF hA hB).elim
    · exact (false_of_pRank_twoPrimeLayerIn_eq_one hR hRe hA h1).elim
    · exact inf_centralizer_eq_of_caseD hK hR hRe hR4 hO hg hT hTN rfl hn φ hφ hker hrR hr1

end CFSG.ComponentClassification.AS76b
