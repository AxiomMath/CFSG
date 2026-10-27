module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Ctx
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Quot
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Setup2
public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x : G}

theorem gen49_isPGroup_T (hl : Gen5Local G p P M x) : IsPGroup 2 (pCoreOf 2 M) := by
  have _ := hl
  exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M

theorem gen49_normalizer_T (hl : Gen5Local G p P M x) :
    normalizer ((pCoreOf 2 M : Subgroup G) : Set G) = M := by
  obtain ⟨S, hS1, hS2, hSM⟩ := hl.core.1.1
  have hST : S ≤ pCoreOf 2 M := by
    have h := CFSG.LieType.BorelTits.le_pCoreOf_normalizer 2 S hS2
    rwa [← hSM] at h
  have hTne : pCoreOf 2 M ≠ ⊥ := fun h => hS1 (le_bot_iff.mp (h ▸ hST))
  exact hl.core.1.2 _ ⟨pCoreOf 2 M, hTne, CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M, rfl⟩
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M)

theorem gen49_fpf (hG : Gen5Global G) (hStr : GL83GenericStructure G)
    (hl : Gen5Local G p P M x) : ∀ t ∈ pCoreOf 2 M, t * x = x * t → t = 1 := by
  obtain ⟨-, -, -, X, -, -, -, -, -, -, -, hfpf⟩ :=
    hStr p hl.sigma P M hl.core hl.fail hl.larger x hl.generic
  exact fun t ht h => hfpf x (gen5_Z hG hl).1 hl.generic.2.1.2.1 t ht h

omit [Finite G] in
private theorem gen49t_two_elem_mem {W K V : Subgroup G} (h : rankThreeFrobeniusProduct W K V)
    (hV : ¬ 2 ∣ Nat.card V) {d : G} (hd : d ∈ W) {n : ℕ} (hdn : d ^ 2 ^ n = 1) : d ∈ K := by
  obtain ⟨X, h1, h2, -, -, hKX, hN, -, -⟩ := h
  have hdX : d ∈ X := (h1 d).2 ⟨d, hd, 1, V.one_mem, (mul_one d).symm⟩
  obtain ⟨t, ht, v, hv, rfl⟩ := (h2 d).1 hdX
  have hvX : v ∈ X := (h2 v).2 ⟨1, K.one_mem, v, hv, (one_mul v).symm⟩
  have htX : t ∈ X := hKX ht
  have hv' : v ∈ K := by
    set φ := QuotientGroup.mk' (K.subgroupOf X) with hφ
    have ht1 : φ ⟨t, htX⟩ = 1 := (QuotientGroup.eq_one_iff _).mpr ht
    have h1 : φ ⟨t * v, X.mul_mem htX hvX⟩ = φ ⟨v, hvX⟩ := by
      have e : (⟨t * v, X.mul_mem htX hvX⟩ : X) = ⟨t, htX⟩ * ⟨v, hvX⟩ := rfl
      rw [e, map_mul, ht1, one_mul]
    have h2 : φ ⟨v, hvX⟩ ^ 2 ^ n = 1 := by
      rw [← h1, ← map_pow]
      have e : (⟨t * v, X.mul_mem htX hvX⟩ : X) ^ 2 ^ n = 1 := Subtype.ext hdn
      rw [e, map_one]
    have h3 : orderOf (φ ⟨v, hvX⟩) ∣ Nat.card V :=
      (orderOf_map_dvd φ _).trans (by
        rw [Subgroup.orderOf_mk]
        exact Subgroup.orderOf_dvd_natCard V hv)
    have h4 : orderOf (φ ⟨v, hvX⟩) ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one h2
    have hcop : Nat.Coprime (Nat.card V) (2 ^ n) :=
      (((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hV).pow_left n).symm
    have h5 : orderOf (φ ⟨v, hvX⟩) = 1 := Nat.dvd_one.mp (hcop.gcd_eq_one ▸ Nat.dvd_gcd h3 h4)
    have h6 : φ ⟨v, hvX⟩ = 1 := orderOf_eq_one_iff.mp h5
    exact (QuotientGroup.eq_one_iff (N := K.subgroupOf X) _).mp h6
  exact K.mul_mem ht hv'

private theorem gen49t_eq_one_of_pow {A : Type*} [Group A] {w : A} {q k n : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) (h1 : w ^ q ^ k = 1) (h2 : w ^ 2 ^ n = 1) : w = 1 := by
  have hcop : Nat.Coprime (q ^ k) (2 ^ n) :=
    ((Nat.coprime_primes hq Nat.prime_two).mpr hq2).pow k n
  rw [← orderOf_eq_one_iff]
  exact Nat.dvd_one.mp (hcop.gcd_eq_one ▸
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one h2))

private theorem gen49t_mk_mem_pCore [Fact p.Prime] (hG : Gen5Global G) (hl : Gen5Local G p P M x)
    (hsolv : Group.IsSolvable M) {g : G} (hgP : g ∈ (P : Subgroup G)) (hgM : g ∈ M) :
    QuotientGroup.mk' (primeComplementCore (G := M) p) ⟨g, hgM⟩ ∈
      CFSG.Open.pCore p (M ⧸ primeComplementCore (G := M) p) := by
  set O := primeComplementCore (G := M) p with hO
  have hPM : (P : Subgroup G) ≤ M := (sylow_le_of_isCoreMaxLocal hG.setting hl.sigma hl.core).1
  let Sbar : Sylow p (M ⧸ O) := (P.subtype hPM).mapSurjective (QuotientGroup.mk'_surjective O)
  have hSbar : (Sbar : Subgroup (M ⧸ O)) =
      ((P : Subgroup G).subgroupOf M).map (QuotientGroup.mk' O) := by
    rw [Sylow.coe_mapSurjective, Sylow.coe_subtype]
  have hchar : centralizer (CFSG.Open.pCore p (M ⧸ O) : Set (M ⧸ O)) ≤
      CFSG.Open.pCore p (M ⧸ O) :=
    solvable_centralizer_pCore_le_of_primeComplementCore_eq_bot p Fact.out
      (primeComplementCore_quotient_eq_bot p) inferInstance
  have : (CFSG.Open.pCore p (M ⧸ O)).Normal :=
    CFSG.RankThreeCoreUniqueness.Helpers.pCore_normal p
  have hQS : CFSG.Open.pCore p (M ⧸ O) ≤ (Sbar : Subgroup (M ⧸ O)) :=
    (CFSG.LieType.BorelTits.pCore_isPGroup p).le_sylow_of_normal Sbar
  have : IsMulCommutative (Sbar : Subgroup (M ⧸ O)) :=
    isMulCommutative_sylow_quotient (fun Q hQ => (gen5_pgroup hG hl hQ).1) Sbar
  have hSQ : (Sbar : Subgroup (M ⧸ O)) ≤ CFSG.Open.pCore p (M ⧸ O) := by
    refine le_trans (fun s hs => ?_) hchar
    rw [mem_centralizer_iff]
    intro q hq
    exact setLike_mul_comm (hQS hq) hs
  refine hSQ ?_
  rw [hSbar]
  exact ⟨⟨g, hgM⟩, hgP, rfl⟩

private theorem gen49t_comm_mem_primeCore [Fact p.Prime] (hG : Gen5Global G)
    (hl : Gen5Local G p P M x) (hsolv : Group.IsSolvable M) {Y : Subgroup G}
    (hY : IsPGroup 2 Y) (hYM : Y ≤ M) (hxY : x ∈ normalizer (Y : Set G)) {y : G} (hy : y ∈ Y) :
    y * x * y⁻¹ * x⁻¹ ∈ rankThreePrimeCore p M ∧ ∃ n : ℕ, (y * x * y⁻¹ * x⁻¹) ^ 2 ^ n = 1 := by
  have hxM : x ∈ M := (sylow_le_of_isCoreMaxLocal hG.setting hl.sigma hl.core).1 hl.generic.1
  have hzY : y * x * y⁻¹ * x⁻¹ ∈ Y := by
    have h := (Subgroup.mem_normalizer_iff.mp hxY y⁻¹).mp (Y.inv_mem hy)
    simpa [mul_assoc] using Y.mul_mem hy h
  have hzM : y * x * y⁻¹ * x⁻¹ ∈ M := hYM hzY
  obtain ⟨n, hn⟩ := hY ⟨_, hzY⟩
  have hzn : (y * x * y⁻¹ * x⁻¹) ^ 2 ^ n = 1 := congrArg Subtype.val hn
  refine ⟨mem_rankThreePrimeCore_of_mk_eq_one hzM ?_, n, hzn⟩
  set O := primeComplementCore (G := M) p with hO
  have hyM : y ∈ M := hYM hy
  have hz : (⟨y * x * y⁻¹ * x⁻¹, hzM⟩ : M) = ⟨y, hyM⟩ * ⟨x, hxM⟩ * ⟨y, hyM⟩⁻¹ * ⟨x, hxM⟩⁻¹ := rfl
  have hxbar := gen49t_mk_mem_pCore hG hl hsolv hl.generic.1 hxM
  have hw : QuotientGroup.mk' O ⟨y * x * y⁻¹ * x⁻¹, hzM⟩ ∈ CFSG.Open.pCore p (M ⧸ O) := by
    rw [hz, map_mul, map_mul, map_mul, map_inv, map_inv]
    have hnorm : (CFSG.Open.pCore p (M ⧸ O)).Normal :=
      CFSG.RankThreeCoreUniqueness.Helpers.pCore_normal p
    exact (CFSG.Open.pCore p (M ⧸ O)).mul_mem (hnorm.conj_mem _ hxbar _)
      ((CFSG.Open.pCore p (M ⧸ O)).inv_mem hxbar)
  obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCore_isPGroup p ⟨_, hw⟩
  refine gen49t_eq_one_of_pow (n := n) (gen5_prime hl) (sigmaA_odd p hl.sigma)
    (congrArg Subtype.val hk) ?_
  have h2 : (⟨y * x * y⁻¹ * x⁻¹, hzM⟩ : M) ^ 2 ^ n = 1 := Subtype.ext hzn
  rw [← map_pow, h2, map_one]

theorem gen49_comm (hG : Gen5Global G) (hStr : GL83GenericStructure G)
    (hl : Gen5Local G p P M x) :
    ∀ Y : Subgroup G, IsPGroup 2 Y → Y ≤ M → x ∈ normalizer (Y : Set G) →
      ∀ y ∈ Y, y * x * y⁻¹ * x⁻¹ ∈ pCoreOf 2 M := by
  have : Fact p.Prime := ⟨gen5_prime hl⟩
  obtain ⟨-, -, hsolv, hfrob⟩ := hStr p hl.sigma P M hl.core hl.fail hl.larger x hl.generic
  intro Y hY hYM hxY y hy
  obtain ⟨hmem, n, hn⟩ := gen49t_comm_mem_primeCore hG hl hsolv hY hYM hxY hy
  exact gen49t_two_elem_mem hfrob (gen5_Z hG hl).2.1 hmem hn

end CFSG.LocalAnalysis.RankThreeTheoremC
