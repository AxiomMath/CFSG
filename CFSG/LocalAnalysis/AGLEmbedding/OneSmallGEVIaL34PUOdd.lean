module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIaL34PUMax
import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSmallPKFacts

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Abstract

variable {X : Type*} [Group X] [Finite X]

omit [Finite X] in
theorem mem_centralizer_of_stable {O N A : Subgroup X} [O.Normal]
    (hOodd : Nat.Coprime 2 (Nat.card O)) (hA : IsPGroup 2 A)
    (hAN : ∀ a ∈ A, ∀ n ∈ N, a * n = n * a)
    (hcomm : ∀ a ∈ A, ∀ o ∈ O, o⁻¹ * (a * o * a⁻¹) ∈ N) :
    O ≤ Subgroup.centralizer (A : Set X) := by
  intro o ho
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  set n := o⁻¹ * (a * o * a⁻¹) with hn
  have hnN : n ∈ N := hcomm a ha o ho
  have hnO : n ∈ O := O.mul_mem (O.inv_mem ho) (Subgroup.Normal.conj_mem ‹_› o ho a)
  have hcn : a * n = n * a := hAN a ha n hnN
  have hpow : ∀ k : ℕ, a ^ k * o * (a ^ k)⁻¹ = o * n ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hck : a * n ^ k = n ^ k * a := (Commute.pow_right hcn k).eq
      calc a ^ (k + 1) * o * (a ^ (k + 1))⁻¹ = a * (a ^ k * o * (a ^ k)⁻¹) * a⁻¹ := by group
        _ = a * (o * n ^ k) * a⁻¹ := by rw [ih]
        _ = (a * o * a⁻¹) * (a * n ^ k * a⁻¹) := by group
        _ = (o * n) * n ^ k := by
            rw [hck, show a * o * a⁻¹ = o * n by rw [hn]; group]; group
        _ = o * n ^ (k + 1) := by rw [pow_succ']; group
  obtain ⟨m, hm⟩ := hA ⟨a, ha⟩
  have ham : a ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
  have hn1 : n ^ 2 ^ m = 1 := by
    have h := hpow (2 ^ m)
    rw [ham, one_mul, inv_one, mul_one] at h
    have : o * n ^ 2 ^ m = o * 1 := by rw [← h, mul_one]
    exact mul_left_cancel this
  have hord : orderOf n ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hn1
  have hordO : orderOf n ∣ Nat.card O := by
    have h := orderOf_dvd_natCard (⟨n, hnO⟩ : O)
    rwa [Subgroup.orderOf_mk] at h
  have hcop : Nat.Coprime 2 (orderOf n) := hOodd.coprime_dvd_right hordO
  have h1 : orderOf n = 1 := by
    rcases (Nat.dvd_prime_pow Nat.prime_two).mp hord with ⟨i, hi, hni⟩
    rcases i with _ | i
    · simpa using hni
    · exfalso
      rw [hni] at hcop
      have := Nat.Coprime.coprime_dvd_right (dvd_pow_self 2 (Nat.succ_ne_zero i)) hcop
      norm_num at this
  have hn1' : n = 1 := orderOf_eq_one_iff.mp h1
  have : a * o * a⁻¹ = o := by
    have h := hn1'
    rw [hn] at h
    calc a * o * a⁻¹ = o * (o⁻¹ * (a * o * a⁻¹)) := by group
      _ = o := by rw [h, mul_one]
  calc a * o = a * o * a⁻¹ * a := by group
    _ = o * a := by rw [this]

end Abstract

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

omit [Finite G] in
theorem mem_pCore_two_iff_mem_pCoreOf {H : Subgroup G} (x : H) :
    x ∈ CFSG.pCore 2 ↥H ↔ (x : G) ∈ pCoreOf 2 H := (CFSG.mem_openPCoreOf_iff x).symm

theorem glbPrimeCore_subgroupOf_eq (p : ℕ) (H : Subgroup G) :
    (GLBPrimeCore p H).subgroupOf H = primeComplementCore (G := H) p := by
  ext x
  rw [Subgroup.mem_subgroupOf, mem_primeComplementCore_iff_mem_glbPrimeCore]

theorem commutator_mem_twoCore_of_primeCore_le (hN : GLBPrimeCore p H ≤ M) {w : H}
    (hw : w ∈ primeComplementCore (G := H) p) {u : H} (hu : (u : G) ∈ pCoreOf 2 (H ⊓ M)) :
    w * u * w⁻¹ * u⁻¹ ∈ CFSG.pCore 2 ↥H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W := GLBPrimeCore p H
  set U := pCoreOf 2 (H ⊓ M)
  have hwW : (w : G) ∈ W := (mem_primeComplementCore_iff_mem_glbPrimeCore p w).mp hw
  have hWHM : W ≤ H ⊓ M := _root_.le_inf (glbPrimeCore_le p H) hN
  have hHMU : H ⊓ M ≤ Subgroup.normalizer (U : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (H ⊓ M)
  have hcU : ((w * u * w⁻¹ * u⁻¹ : H) : G) ∈ U := by
    have h1 : (w : G) * u * (w : G)⁻¹ ∈ U :=
      (Subgroup.mem_normalizer_iff.mp (hHMU (hWHM hwW)) u).mp hu
    simpa using U.mul_mem h1 (U.inv_mem hu)
  have hcW : ((w * u * w⁻¹ * u⁻¹ : H) : G) ∈ W := by
    have hn : (primeComplementCore (G := H) p).Normal := inferInstance
    have h1 : w * u * w⁻¹ * u⁻¹ ∈ primeComplementCore (G := H) p := by
      have h2 : u * w⁻¹ * u⁻¹ ∈ primeComplementCore (G := H) p :=
        hn.conj_mem _ (Subgroup.inv_mem _ hw) u
      have h3 := Subgroup.mul_mem _ hw h2
      simpa [mul_assoc] using h3
    exact (mem_primeComplementCore_iff_mem_glbPrimeCore p _).mp h1
  have hD : W ⊓ U ≤ pCoreOf 2 W := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left ?_
      ((CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 (H ⊓ M)).to_le inf_le_right)
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hxU := Subgroup.mem_normalizer_iff.mp (hHMU (hWHM hx)) y
    constructor
    · rintro ⟨hy1, hy2⟩
      exact ⟨W.mul_mem (W.mul_mem hx hy1) (W.inv_mem hx), hxU.mp hy2⟩
    · rintro ⟨hy1, hy2⟩
      refine ⟨?_, hxU.mpr hy2⟩
      have := W.mul_mem (W.mul_mem (W.inv_mem hx) hy1) hx
      simpa [mul_assoc] using this
  have hWH : pCoreOf 2 W ≤ pCoreOf 2 H := by
    refine pCoreOf_le_of_normal_subgroupOf 2 W H (glbPrimeCore_le p H) ?_
    rw [glbPrimeCore_subgroupOf_eq]
    infer_instance
  exact (mem_pCore_two_iff_mem_pCoreOf _).mpr (hWH (hD ⟨hcW, hcU⟩))

theorem pCore_two_le_primeComplementCore {H : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    CFSG.pCore 2 ↥H ≤ primeComplementCore (G := H) p := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine normal_coprime_le_primeComplementCore p _ CFSG.pCore_normal ?_
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥H)).exists_card_eq
  rw [hk]
  exact Nat.Coprime.pow_right k ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)

@[expose] noncomputable def twoPrimeMap (H : Subgroup G) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    (↥H ⧸ CFSG.pCore 2 ↥H) →* (↥H ⧸ primeComplementCore (G := H) p) :=
  QuotientGroup.map _ _ (MonoidHom.id _) (pCore_two_le_primeComplementCore hp hp2)

theorem twoPrimeMap_mk {H : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (x : H) :
    twoPrimeMap H hp hp2 (QuotientGroup.mk' (CFSG.pCore 2 ↥H) x) =
      QuotientGroup.mk' (primeComplementCore (G := H) p) x := rfl

theorem twoPrimeMap_surjective {H : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    Function.Surjective (twoPrimeMap H hp hp2) := by
  intro y
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (primeComplementCore (G := H) p) y
  exact ⟨QuotientGroup.mk' _ x, twoPrimeMap_mk hp hp2 x⟩

theorem mem_map_of_twoPrimeMap_eq_one {H : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {y : ↥H ⧸ CFSG.pCore 2 ↥H} (hy : twoPrimeMap H hp hp2 y = 1) :
    y ∈ (primeComplementCore (G := H) p).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥H) y
  rw [twoPrimeMap_mk, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hy
  exact ⟨x, hy, rfl⟩

theorem primeCore_map_le_centralizer_of_primeCore_le (hN : GLBPrimeCore p H ≤ M) :
    (primeComplementCore (G := H) p).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) ≤
      Subgroup.centralizer (barM H (pCoreOf 2 (H ⊓ M)) : Set (↥H ⧸ CFSG.pCore 2 ↥H)) := by
  rintro _ ⟨w, hw, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨u, hu, rfl⟩
  have hc := commutator_mem_twoCore_of_primeCore_le hN hw (Subgroup.mem_subgroupOf.mp hu)
  have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥H) (w * u * w⁻¹ * u⁻¹) = 1 := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]; exact hc
  simp only [map_mul, map_inv] at h1
  have := congrArg (· * QuotientGroup.mk' (CFSG.pCore 2 ↥H) u) h1
  simp only [inv_mul_cancel_right, one_mul] at this
  have h2 := congrArg (· * QuotientGroup.mk' (CFSG.pCore 2 ↥H) w) this
  simp only [inv_mul_cancel_right] at h2
  exact h2.symm

theorem D1Escape.primeCore_map_le_centralizer (h : D1Escape p P M H R) :
    (primeComplementCore (G := H) p).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) ≤
      Subgroup.centralizer (barM H (pCoreOf 2 (H ⊓ M)) : Set (↥H ⧸ CFSG.pCore 2 ↥H)) :=
  primeCore_map_le_centralizer_of_primeCore_le h.primeCore_le

theorem D1OneSmallData.normalizer_le_d1X0 (hd : D1OneSmallData p P M H R Rbar K) :
    Subgroup.normalizer (((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
      Subgroup _) : Set (H ⧸ primeComplementCore (G := H) p)) ≤ d1X0 p M H := by
  have hp := hd.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨zb, hzbR, hzbK, hzbp, hzbc⟩ := hd.z
  have hRKp : IsPGroup p ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
      Subgroup _) := Rbar.isPGroup'.to_le inf_le_left
  have h2 : 2 ≤ Open.pRank p ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
      Subgroup _) :=
    CFSG.LocalAnalysis.RankThreeTheoremC.two_le_pRank_of_not_isCyclic hp hd.cfg.red.ne_two hRKp
      hd.noncyclic
  exact hd.cfg.red.normalizer_le_of_mem_centralizer hzbR (fun h => hzbK h.2) hzbp
    (Subgroup.centralizer_le inf_le_right hzbc) inf_le_left h2

theorem D1OneSmallData.commute_mk_of_odd_normal (hO : KFactSmallThreeOrders)
    (hd : D1OneSmallData p P M H R Rbar K) (hL : IsLinThreeFour K)
    {N : Subgroup (H ⧸ primeComplementCore (G := H) p)} [N.Normal]
    (hNodd : Nat.Coprime 2 (Nat.card N)) {x : H ⧸ primeComplementCore (G := H) p} (hx : x ∈ N)
    {u : H} (hu : (u : G) ∈ pCoreOf 2 (H ⊓ M)) :
    x * QuotientGroup.mk' (primeComplementCore (G := H) p) u =
      QuotientGroup.mk' (primeComplementCore (G := H) p) u * x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (primeComplementCore (G := H) p) with hπ
  have hKn : K.Normal := hd.cfg.red.normal_of_rankOne hd.comp hd.noncyclic
  obtain ⟨-, -, hsimple, -, -, -, -, -⟩ := hd.exists_sylow
  have hN : N.Normal := ‹_›
  have hNK : ∀ y ∈ N, y ∈ K → y = 1 := by
    have hn : (N.subgroupOf K).Normal := hN.subgroupOf K
    rcases hn.eq_bot_or_eq_top with h | h
    · intro y hyN hyK
      have : (⟨y, hyK⟩ : K) ∈ N.subgroupOf K := Subgroup.mem_subgroupOf.mpr hyN
      rw [h, Subgroup.mem_bot] at this
      exact congrArg Subtype.val this
    · exfalso
      have hKN : K ≤ N := fun k hk => by
        have : (⟨k, hk⟩ : K) ∈ N.subgroupOf K := h ▸ Subgroup.mem_top _
        exact Subgroup.mem_subgroupOf.mp this
      have hdvd := Subgroup.card_dvd_of_le hKN
      rw [(hO K).2.1 hL] at hdvd
      have h2 : 2 ∣ Nat.card N := dvd_trans (by norm_num) hdvd
      exact absurd (Nat.Coprime.coprime_dvd_right h2 hNodd) (by norm_num)
  have hxC : x ∈ Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have hc : x * k * x⁻¹ * k⁻¹ = 1 := by
      refine hNK _ ?_ ?_
      · have h1 : k * x⁻¹ * k⁻¹ ∈ N := hN.conj_mem _ (N.inv_mem hx) k
        have := N.mul_mem hx h1
        simpa [mul_assoc] using this
      · exact K.mul_mem (hKn.conj_mem k hk x) (K.inv_mem hk)
    have := congrArg (· * (k * x)) hc
    simp only [one_mul] at this
    calc k * x = x * k * x⁻¹ * k⁻¹ * (k * x) := this.symm
      _ = x * k := by group
  have hxX : x ∈ d1X0 p M H := by
    refine hd.normalizer_le_d1X0 ?_
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hxy : y ∈ K → x * y * x⁻¹ = y := fun hy => by
      rw [(Subgroup.mem_centralizer_iff.mp hxC y hy).symm]; group
    constructor
    · intro hy
      rw [hxy hy.2]; exact hy
    · intro hy
      have hyK : y ∈ K := by
        have := hKn.conj_mem _ hy.2 x⁻¹
        simpa [mul_assoc] using this
      rw [hxy hyK] at hy
      exact hy
  obtain ⟨h, hh, rfl⟩ := hxX
  have hhM : (h : G) ∈ H ⊓ M := Subgroup.mem_subgroupOf.mp hh
  set U := pCoreOf 2 (H ⊓ M)
  have hhU : (h : G) * u * (h : G)⁻¹ ∈ U :=
    (Subgroup.mem_normalizer_iff.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (H ⊓ M) hhM)
      u).mp hu
  set v : H := h * u * h⁻¹ * u⁻¹ with hv
  have hvU : (v : G) ∈ U := by
    simpa [hv] using U.mul_mem hhU (U.inv_mem hu)
  have hc : π h * π u * (π h)⁻¹ * (π u)⁻¹ = π v := by simp [hv]
  have hcN : π v ∈ N := by
    rw [← hc]
    have h1 : π u * (π h)⁻¹ * (π u)⁻¹ ∈ N := hN.conj_mem _ (N.inv_mem hx) _
    have h2 := N.mul_mem hx h1
    rw [← mul_assoc, ← mul_assoc] at h2
    exact h2
  obtain ⟨m, hm⟩ := (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 (H ⊓ M))
    ⟨(v : G), hvU⟩
  have hvm : v ^ 2 ^ m = 1 := by
    apply Subtype.ext
    simpa using congrArg Subtype.val hm
  have hord : orderOf (π v) ∣ 2 ^ m :=
    orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hvm, map_one])
  have hordN : orderOf (π v) ∣ Nat.card N := by
    have h1 := orderOf_dvd_natCard (⟨π v, hcN⟩ : N)
    rwa [Subgroup.orderOf_mk] at h1
  have hcop : Nat.Coprime 2 (orderOf (π v)) := hNodd.coprime_dvd_right hordN
  have h1 : orderOf (π v) = 1 := by
    rcases (Nat.dvd_prime_pow Nat.prime_two).mp hord with ⟨i, hi, hni⟩
    rcases i with _ | i
    · simpa using hni
    · exfalso
      rw [hni] at hcop
      have := Nat.Coprime.coprime_dvd_right (dvd_pow_self 2 (Nat.succ_ne_zero i)) hcop
      norm_num at this
  have hv1 : π v = 1 := orderOf_eq_one_iff.mp h1
  rw [← hc] at hv1
  have := congrArg (· * (π u * π h)) hv1
  simp only [one_mul] at this
  calc π h * π u = π h * π u * (π h)⁻¹ * (π u)⁻¹ * (π u * π h) := by group
    _ = π u * π h := this

theorem D1OneSmallData.oddCore_le_centralizer_barM (hO : KFactSmallThreeOrders)
    (hd : D1OneSmallData p P M H R Rbar K) (hL : IsLinThreeFour K) :
    CFSG.pPrimeCore 2 (↥H ⧸ CFSG.pCore 2 ↥H) ≤
      Subgroup.centralizer (barM H (pCoreOf 2 (H ⊓ M)) : Set (↥H ⧸ CFSG.pCore 2 ↥H)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp := hd.cfg.red.prime
  have hp2 := hd.cfg.red.ne_two
  set O := CFSG.pPrimeCore 2 (↥H ⧸ CFSG.pCore 2 ↥H) with hOdef
  have hOodd : Nat.Coprime 2 (Nat.card O) := CFSG.pPrimeCore_coprime_card
  have hNn : (O.map (twoPrimeMap H hp hp2)).Normal :=
    (CFSG.pPrimeCore_normal).map (twoPrimeMap H hp hp2) (twoPrimeMap_surjective hp hp2)
  have hNodd : Nat.Coprime 2 (Nat.card (O.map (twoPrimeMap H hp hp2))) :=
    hOodd.coprime_dvd_right (Subgroup.card_map_dvd O (twoPrimeMap H hp hp2))
  have hA : IsPGroup 2 (barM H (pCoreOf 2 (H ⊓ M))) :=
    ((CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 (H ⊓ M)).comap_subtype).map _
  refine mem_centralizer_of_stable
    (N := (primeComplementCore (G := H) p).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)))
    hOodd hA ?_ ?_
  · intro a ha n hn
    exact Subgroup.mem_centralizer_iff.mp (hd.cfg.ext.primeCore_map_le_centralizer hn) a ha
  · rintro _ ⟨u, hu, rfl⟩ o ho
    apply mem_map_of_twoPrimeMap_eq_one hp hp2
    have hc := hd.commute_mk_of_odd_normal hO hL (N := O.map (twoPrimeMap H hp hp2)) hNodd
      (Subgroup.mem_map_of_mem (twoPrimeMap H hp hp2) ho) (Subgroup.mem_subgroupOf.mp hu)
    rw [map_mul, map_inv, map_mul, map_mul, map_inv, twoPrimeMap_mk, ← hc]
    group

theorem exists_weakBlock_twoCore_inf_of_primeCore_le (hHM : pCoreOf 2 H ≤ M)
    (hN : GLBPrimeCore p H ≤ M)
    (hOc : CFSG.pPrimeCore 2 (↥H ⧸ CFSG.pCore 2 ↥H) ≤
      Subgroup.centralizer (barM H (pCoreOf 2 (H ⊓ M)) : Set (↥H ⧸ CFSG.pCore 2 ↥H)))
    (hS : pCoreOf 2 (H ⊓ M) ≠ pCoreOf 2 H) :
    ∃ L : Subgroup G, IsWeakSBlock H (pCoreOf 2 (H ⊓ M)) L ∧
      ¬ barM H L ≤ (primeComplementCore (G := H) p).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) := by
  have hU2 : IsPGroup 2 ((pCoreOf 2 (H ⊓ M)).subgroupOf H) :=
    (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 (H ⊓ M)).comap_subtype
  have hUQ : ¬ (pCoreOf 2 (H ⊓ M)).subgroupOf H ≤ CFSG.pCore 2 ↥H := by
    intro hle
    apply hS
    refine le_antisymm (fun u hu => ?_) (twoCore_le_twoCore_inf_of_le hHM)
    have huH : u ∈ H := (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 (H ⊓ M)).trans
      inf_le_left hu
    exact (mem_pCore_two_iff_mem_pCoreOf ⟨u, huH⟩).mp
      (hle (Subgroup.mem_subgroupOf.mpr hu))
  rcases exists_component_not_le_normalizer_or_not_le_centralizer hU2 hUQ with
    ⟨Lb, hLb, hnot⟩ | hodd
  · obtain ⟨L, hL', hbar⟩ := exists_isTwoPrimeComponent hLb
    refine ⟨L, ⟨hL', fun hLS => hnot ?_⟩, fun hle => hnot ?_⟩
    · rw [← hbar]
      exact barM_le_normalizer_barM hLS
    · rw [← hbar]
      exact (hle.trans (primeCore_map_le_centralizer_of_primeCore_le hN)).trans
        (Subgroup.centralizer_le_normalizer _)
  · exact absurd hOc hodd

theorem D1OneSmallData.exists_weakBlock_twoCore_inf (hO : KFactSmallThreeOrders)
    (hd : D1OneSmallData p P M H R Rbar K) (hL : IsLinThreeFour K)
    (hS : pCoreOf 2 (H ⊓ M) ≠ pCoreOf 2 H) :
    ∃ L : Subgroup G, IsWeakSBlock H (pCoreOf 2 (H ⊓ M)) L ∧
      ¬ barM H L ≤ (primeComplementCore (G := H) p).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) :=
  exists_weakBlock_twoCore_inf_of_primeCore_le hd.cfg.ext.twoCore_le hd.cfg.ext.primeCore_le
    (hd.oddCore_le_centralizer_barM hO hL) hS

end CFSG.AGLEmbedding
