module

public import CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977StandardCyclic
public import CFSG.LocalAnalysis.ComponentClassification.StandardSubgroupAPI
public import CFSG.GroupTheory.CyclicSylowNormalOddComplement
public import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup
open CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977
open scoped commutatorElement Pointwise

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem exists_mul_eq_mul_self_of_mem_normalizer {J : Subgroup G} (hJp : Group.IsPerfect ↥J)
    (hOut : ∀ α β : MulAut (↥J ⧸ center ↥J),
      α ∉ (MulAut.conj : (↥J ⧸ center ↥J) →* MulAut (↥J ⧸ center ↥J)).range →
      β ∉ (MulAut.conj : (↥J ⧸ center ↥J) →* MulAut (↥J ⧸ center ↥J)).range →
      α * β ∈ (MulAut.conj : (↥J ⧸ center ↥J) →* MulAut (↥J ⧸ center ↥J)).range)
    {n : G} (hn : n ∈ normalizer (J : Set G)) :
    ∃ j ∈ J, ∃ c ∈ centralizer (J : Set G), n * n = j * c := by
  classical
  have : Group.IsPerfect ↥J := hJp
  let N : Subgroup G := Subgroup.normalizer (J : Set G)
  let K : Subgroup (MulAut (↥J ⧸ center ↥J)) :=
    (MulAut.conj : (↥J ⧸ center ↥J) →* MulAut (↥J ⧸ center ↥J)).range
  let φ : MulAut (↥J ⧸ center ↥J) := automizer J ⟨n, hn⟩
  have hφφ : φ * φ ∈ K := by
    by_cases hφ : φ ∈ K
    · exact K.mul_mem hφ hφ
    · exact hOut φ φ hφ hφ
  obtain ⟨q, hq⟩ := hφφ
  obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective q
  have hjJ : (j : G) ∈ J := j.2
  have hjN : (j : G) ∈ N := Subgroup.le_normalizer hjJ
  have hautj : automizer J ⟨(j : G), hjN⟩ =
      (MulAut.conj : (↥J ⧸ center ↥J) →* MulAut (↥J ⧸ center ↥J))
        (QuotientGroup.mk j) := by
    ext x
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective x
    rw [automizer_apply_mk, MulAut.conj_apply]
    rfl
  let c : G := n * n * (j : G)⁻¹
  have hcN : c ∈ N := by
    have h1 : n * n ∈ N := N.mul_mem hn hn
    exact N.mul_mem h1 (N.inv_mem hjN)
  have hnn : automizer J ⟨c, hcN⟩ = 1 := by
    have hc_eq : (⟨c, hcN⟩ : N) = ⟨n, hn⟩ * ⟨n, hn⟩ * (⟨(j : G), hjN⟩ : N)⁻¹ := by
      ext
      simp [c]
    rw [hc_eq, map_mul, map_mul, map_inv, hautj]
    have hφn : automizer J ⟨n, hn⟩ = φ := rfl
    rw [hφn]
    rw [hq]
    simp only [mul_inv_cancel]
  have hcC : c ∈ centralizer (J : Set G) := (automizer_eq_one_iff J ⟨c, hcN⟩).mp hnn
  refine ⟨(j : G), hjJ, c, hcC, ?_⟩
  have hcj : (j : G) * c = c * (j : G) :=
    (Subgroup.mem_centralizer_iff.mp hcC) (j : G) hjJ
  have hcnn : n * n = c * (j : G) := by
    rw [show c * (j : G) = n * n by simp [c, mul_assoc]]
  calc n * n = c * (j : G) := hcnn
    _ = (j : G) * c := hcj.symm

private theorem odd_div_gcd_four_of_not_dvd_eight {m : ℕ} (hm : ¬ 8 ∣ m) :
    Odd (m / Nat.gcd m 4) := by
  have hgpos : 0 < Nat.gcd m 4 := Nat.gcd_pos_of_pos_right m (by norm_num)
  have hgdvd : Nat.gcd m 4 ∣ 4 := Nat.gcd_dvd_right m 4
  have hgle : Nat.gcd m 4 ≤ 4 := Nat.le_of_dvd (by norm_num) hgdvd
  have hgm : Nat.gcd m 4 ∣ m := Nat.gcd_dvd_left m 4
  have hmul : Nat.gcd m 4 * (m / Nat.gcd m 4) = m := Nat.mul_div_cancel' hgm
  have hg3 : Nat.gcd m 4 ≠ 3 := by
    intro h
    have h34 : ¬ (3 ∣ 4) := by norm_num
    exact h34 (h ▸ hgdvd)
  have hcases : Nat.gcd m 4 = 1 ∨ Nat.gcd m 4 = 2 ∨ Nat.gcd m 4 = 4 := by omega
  rw [← Nat.not_even_iff_odd]
  intro heven
  obtain ⟨k, hk⟩ := heven
  have hm_eq : m = Nat.gcd m 4 * (2 * k) := by
    calc m = Nat.gcd m 4 * (m / Nat.gcd m 4) := hmul.symm
      _ = Nat.gcd m 4 * (2 * k) := by rw [hk]; ring
  rcases hcases with h1 | h2 | h4
  · have h2m : 2 ∣ m := ⟨k, by rw [hm_eq, h1]; ring⟩
    have h2g : 2 ∣ Nat.gcd m 4 := Nat.dvd_gcd h2m (by norm_num)
    rw [h1] at h2g
    norm_num at h2g
  · have h4m : 4 ∣ m := ⟨k, by rw [hm_eq, h2]; ring⟩
    have h4g : 4 ∣ Nat.gcd m 4 := Nat.dvd_gcd h4m (by norm_num)
    rw [h2] at h4g
    norm_num at h4g
  · have h8m : 8 ∣ m := ⟨k, by rw [hm_eq, h4]; ring⟩
    exact hm h8m

theorem conj_not_mem_of_forall_pow_eight {J : Subgroup G} (hst : IsStandardSubgroup J)
    (hOut : ∀ α β : MulAut (↥J ⧸ center ↥J),
      α ∉ (MulAut.conj : (↥J ⧸ center ↥J) →* MulAut (↥J ⧸ center ↥J)).range →
      β ∉ (MulAut.conj : (↥J ⧸ center ↥J) →* MulAut (↥J ⧸ center ↥J)).range →
      α * β ∈ (MulAut.conj : (↥J ⧸ center ↥J) →* MulAut (↥J ⧸ center ↥J)).range)
    (hZ : Odd (Nat.card (center ↥J))) (hpow : ∀ a : ↥J, orderOf a = 2 → ∃ y : ↥J, y ^ 8 = a)
    (hC4 : ∀ P : Subgroup G, P ≤ centralizer (J : Set G) → IsPGroup 2 P → Nat.card P ≤ 4)
    {t : G} (ht : orderOf t = 2) (htJ : t ∈ centralizer (J : Set G)) (g : G) :
    g⁻¹ * t * g ∉ J := by
  classical
  have hst' : Assembly.ComponentType.IsStandardSubgroup J :=
    CFSG.StandardSubgroupAPI.isStandardSubgroup_iff_assembly.1 hst
  intro hsJ
  set s : G := g⁻¹ * t * g with hs_def
  have ht2 : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rw [ht] at this
    simpa [pow_two] using this
  have hs2 : s * s = 1 := by
    have : s * s = g⁻¹ * (t * t) * g := by dsimp [s]; group
    rw [this, ht2]
    group
  have hsne : s ≠ 1 := by
    intro h
    have h1 : g * s * g⁻¹ = t := by dsimp [s]; group
    rw [h] at h1
    have ht1 : t = 1 := by simpa using h1.symm
    rw [ht1, orderOf_one] at ht
    norm_num at ht
  have hs2' : (⟨s, hsJ⟩ : ↥J) ^ 2 = 1 := by
    apply Subtype.ext
    simpa [pow_two] using hs2
  have hsne' : (⟨s, hsJ⟩ : ↥J) ≠ 1 := by
    intro h
    exact hsne (congrArg Subtype.val h)
  have hsord : orderOf (⟨s, hsJ⟩ : ↥J) = 2 := orderOf_eq_prime hs2' hsne'
  obtain ⟨y, hy8⟩ := hpow ⟨s, hsJ⟩ hsord
  have hyG : (y : G) ^ 8 = s := by
    have := congrArg (Subtype.val) hy8
    simpa using this
  let v : G := g * (y : G) * g⁻¹
  have hv8 : v ^ 8 = t := by
    have hconj : v = MulAut.conj g (y : G) := by
      rw [MulAut.conj_apply]
    calc v ^ 8 = (MulAut.conj g (y : G)) ^ 8 := by rw [hconj]
      _ = MulAut.conj g ((y : G) ^ 8) := by rw [← map_pow]
      _ = g * s * g⁻¹ := by rw [hyG, MulAut.conj_apply]
      _ = t := by dsimp [s]; group
  have hvC : v ∈ centralizer ({t} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    rw [← hv8]
    group
  have hvN : v ∈ Subgroup.normalizer (J : Set G) :=
    (LocalAnalysis.ComponentInitial.standard_involution_centralizer_normality hst' htJ ht).1 hvC
  obtain ⟨j, hjJ, c, hcC, hvv⟩ :=
    exists_mul_eq_mul_self_of_mem_normalizer (J := J) hst.1.1 hOut hvN
  have hcommjc : Commute j c := (Subgroup.mem_centralizer_iff.mp hcC) j hjJ
  have ht_eq : t = j ^ 4 * c ^ 4 := by
    calc t = v ^ 8 := hv8.symm
      _ = (v * v) ^ 4 := by rw [← pow_two v, ← pow_mul]
      _ = (j * c) ^ 4 := by rw [hvv]
      _ = j ^ 4 * c ^ 4 := by rw [hcommjc.mul_pow]
  have hc4C : c ^ 4 ∈ centralizer (J : Set G) :=
    (Subgroup.centralizer (J : Set G)).pow_mem hcC 4
  have hj4J : j ^ 4 ∈ J := J.pow_mem hjJ 4
  have hj4C : j ^ 4 ∈ centralizer (J : Set G) := by
    have hjeq : j ^ 4 = t * (c ^ 4)⁻¹ := by
      rw [ht_eq]
      group
    rw [hjeq]
    exact Subgroup.mul_mem _ htJ (Subgroup.inv_mem _ hc4C)
  have hj4center : (⟨j ^ 4, hj4J⟩ : ↥J) ∈ center ↥J := by
    rw [Subgroup.mem_center_iff]
    intro x
    apply Subtype.ext
    change (x : G) * j ^ 4 = j ^ 4 * (x : G)
    exact (Subgroup.mem_centralizer_iff.mp hj4C) (x : G) x.2
  have hj4odd : Odd (orderOf (⟨j ^ 4, hj4J⟩ : ↥J)) :=
    Odd.of_dvd_nat hZ (Subgroup.orderOf_dvd_natCard (center ↥J) hj4center)
  have hj4oddG : Odd (orderOf (j ^ 4 : G)) := by
    have h := Subgroup.orderOf_coe (⟨j ^ 4, hj4J⟩ : ↥J)
    rw [h]
    exact hj4odd
  have h8 : ¬ 8 ∣ orderOf c := by
    intro hdvd
    have hmpos : 0 < orderOf c := orderOf_pos c
    let x : G := c ^ (orderOf c / 8)
    have hxord : orderOf x = 8 := by
      rw [orderOf_pow, Nat.gcd_eq_right (Nat.div_dvd_of_dvd hdvd)]
      have h8pos : 0 < orderOf c / 8 :=
        Nat.div_pos (Nat.le_of_dvd hmpos hdvd) (by norm_num)
      nth_rewrite 1 [← Nat.mul_div_cancel' hdvd]
      exact Nat.mul_div_left 8 h8pos
    have hxle : Subgroup.zpowers x ≤ centralizer (J : Set G) :=
      Subgroup.zpowers_le.mpr ((Subgroup.centralizer (J : Set G)).pow_mem hcC _)
    have hxp : IsPGroup 2 (Subgroup.zpowers x) :=
      IsPGroup.of_card (n := 3) (by rw [Nat.card_zpowers, hxord]; norm_num)
    have hcard := hC4 (Subgroup.zpowers x) hxle hxp
    rw [Nat.card_zpowers, hxord] at hcard
    omega
  have hc4odd : Odd (orderOf (c ^ 4)) := by
    rw [orderOf_pow]
    exact odd_div_gcd_four_of_not_dvd_eight h8
  have hcomm4 : Commute (j ^ 4 : G) (c ^ 4) :=
    (Subgroup.mem_centralizer_iff.mp hc4C) (j ^ 4) hj4J
  have htodd : Odd (orderOf t) := by
    rw [ht_eq]
    refine Odd.of_dvd_nat (hj4oddG.mul hc4odd) (orderOf_dvd_iff_pow_eq_one.mpr ?_)
    have hj1 : (j ^ 4 : G) ^ (orderOf (j ^ 4) * orderOf (c ^ 4)) = 1 := by
      rw [pow_mul, pow_orderOf_eq_one, one_pow]
    have hc1 : (c ^ 4 : G) ^ (orderOf (j ^ 4) * orderOf (c ^ 4)) = 1 := by
      rw [Nat.mul_comm, pow_mul, pow_orderOf_eq_one, one_pow]
    rw [hcomm4.mul_pow, hj1, hc1, mul_one]
  rw [ht] at htodd
  obtain ⟨k, hk⟩ := htodd
  omega

theorem le_of_perfect_le_centralizer {J : Subgroup G} (hst : IsStandardSubgroup J)
    (hOut : ∀ α β : MulAut (↥J ⧸ center ↥J),
      α ∉ (MulAut.conj : (↥J ⧸ center ↥J) →* MulAut (↥J ⧸ center ↥J)).range →
      β ∉ (MulAut.conj : (↥J ⧸ center ↥J) →* MulAut (↥J ⧸ center ↥J)).range →
      α * β ∈ (MulAut.conj : (↥J ⧸ center ↥J) →* MulAut (↥J ⧸ center ↥J)).range)
    (hcyc : ∀ P : Subgroup G, P ≤ centralizer (J : Set G) → IsPGroup 2 P → IsCyclic P)
    {t : G} (ht : orderOf t = 2) (htJ : t ∈ centralizer (J : Set G)) {L : Subgroup G}
    (hLt : L ≤ centralizer ({t} : Set G)) (hL : ⁅L, L⁆ = L) : L ≤ J := by
  classical
  have : Group.IsPerfect ↥J := hst.1.1
  have hst' : Assembly.ComponentType.IsStandardSubgroup J :=
    CFSG.StandardSubgroupAPI.isStandardSubgroup_iff_assembly.1 hst
  set T : Subgroup G := centralizer ({t} : Set G) with hT
  set C : Subgroup G := centralizer (J : Set G) with hC
  obtain ⟨hTN, hJT, hJn, -, -⟩ :=
    LocalAnalysis.ComponentInitial.standard_involution_centralizer_normality hst' htJ ht
  have hLT : L ≤ T := hLt
  let K : Subgroup (MulAut (↥J ⧸ center ↥J)) :=
    (MulAut.conj : (↥J ⧸ center ↥J) →* MulAut (↥J ⧸ center ↥J)).range
  let φ : T →* MulAut (↥J ⧸ center ↥J) :=
    (automizer J).comp (Subgroup.inclusion hTN)
  have hKnormal : K.Normal := by
    refine ⟨fun a ha g => ?_⟩
    obtain ⟨x, rfl⟩ := ha
    refine ⟨g x, ?_⟩
    ext y
    simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.inv_apply, map_mul, map_inv,
      MulEquiv.apply_symm_apply]
  have : K.Normal := hKnormal
  have hQcomm : ∀ a b : MulAut (↥J ⧸ center ↥J) ⧸ K, a * b = b * a := by
    intro a b
    obtain ⟨α, rfl⟩ := QuotientGroup.mk'_surjective K a
    obtain ⟨β, rfl⟩ := QuotientGroup.mk'_surjective K b
    by_cases hα : α ∈ K
    · rw [show QuotientGroup.mk' K α = 1 from (QuotientGroup.eq_one_iff α).mpr hα]
      simp
    by_cases hβ : β ∈ K
    · rw [show QuotientGroup.mk' K β = 1 from (QuotientGroup.eq_one_iff β).mpr hβ]
      simp
    · have hαβ : α * β ∈ K := hOut α β hα hβ
      have hβα : β * α ∈ K := hOut β α hβ hα
      rw [show QuotientGroup.mk' K α * QuotientGroup.mk' K β = 1 from by
            rw [← map_mul]
            exact (QuotientGroup.eq_one_iff (α * β)).mpr hαβ,
          show QuotientGroup.mk' K β * QuotientGroup.mk' K α = 1 from by
            rw [← map_mul]
            exact (QuotientGroup.eq_one_iff (β * α)).mpr hβα]
  have hInner : ∀ α β : MulAut (↥J ⧸ center ↥J), ⁅α, β⁆ ∈ K := by
    intro α β
    have hq1 : QuotientGroup.mk' K ⁅α, β⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm.mpr (hQcomm _ _)]
    exact (QuotientGroup.eq_one_iff ⁅α, β⁆).mp hq1
  have hLperf_sub : ⁅L.subgroupOf T, L.subgroupOf T⁆ = L.subgroupOf T := by
    apply (Subgroup.map_injective (f := T.subtype) T.subtype_injective)
    rw [commutator_subgroupOf_map_eq T L L hLT hLT, hL, Subgroup.map_subgroupOf_eq_of_le hLT]
  have hLgood : L.subgroupOf T ≤ K.comap φ := by
    rw [← hLperf_sub, Subgroup.commutator_le]
    intro x hx y hy
    rw [Subgroup.mem_comap, map_commutatorElement]
    exact hInner (φ x) (φ y)
  let B : Subgroup G := C ⊓ T
  have hBleT : B ≤ T := inf_le_right
  let q : T →* T ⧸ (J.subgroupOf T) := QuotientGroup.mk' (J.subgroupOf T)
  have hLmap_le : (L.subgroupOf T).map q ≤ (B.subgroupOf T).map q := by
    rintro y ⟨x, hx, rfl⟩
    have hxK : φ x ∈ K := Subgroup.mem_comap.mp (hLgood hx)
    obtain ⟨qx, hqx⟩ := hxK
    obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective qx
    let jT : T := ⟨(j : G), hJT j.2⟩
    have hφj : φ jT = MulAut.conj (QuotientGroup.mk j) := by
      have h : φ jT = automizer J ⟨(j : G), hTN (hJT j.2)⟩ := rfl
      rw [h]
      ext z
      obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective z
      rw [automizer_apply_mk, MulAut.conj_apply]
      rfl
    have hφ1 : φ (x * jT⁻¹) = 1 := by
      rw [map_mul, map_inv, hφj, ← hqx]
      simp
    have hbC : ((x * jT⁻¹ : T) : G) ∈ C := by
      have h1 : automizer J (Subgroup.inclusion hTN (x * jT⁻¹)) = 1 := hφ1
      have h2 := (automizer_eq_one_iff J (Subgroup.inclusion hTN (x * jT⁻¹))).mp h1
      simpa [Subgroup.coe_inclusion] using h2
    have hbB : ((x * jT⁻¹ : T) : G) ∈ B := ⟨hbC, (x * jT⁻¹).2⟩
    have hqeq : q (x * jT⁻¹) = q x := by
      apply (QuotientGroup.eq (s := J.subgroupOf T)).mpr
      change ((x * jT⁻¹)⁻¹ * x : T) ∈ J.subgroupOf T
      rw [Subgroup.mem_subgroupOf]
      have hjx : ((x * jT⁻¹)⁻¹ * x : T) = jT := by group
      rw [hjx]
      exact j.2
    rw [← hqeq]
    exact Subgroup.mem_map.mpr ⟨x * jT⁻¹, Subgroup.mem_subgroupOf.mpr hbB, rfl⟩
  let Ebar : Subgroup (T ⧸ (J.subgroupOf T)) := (L.subgroupOf T).map q
  have hEbar_perf : Group.IsPerfect Ebar := by
    have : Group.IsPerfect ↥(L.subgroupOf T) := Subgroup.isPerfect_iff.mpr hLperf_sub
    exact Group.IsPerfect.map q
  have hEbar_le : Ebar ≤ (B.subgroupOf T).map q := hLmap_le
  have hB_solv : Group.IsSolvable ↥B := by
    obtain ⟨Sb⟩ := Sylow.nonempty (p := 2) (G := ↥B)
    have hPle : (Sb : Subgroup ↥B).map B.subtype ≤ C := by
      rintro - ⟨b, hb, rfl⟩
      exact (Subgroup.mem_inf.mp b.2).1
    have hPpos : IsPGroup 2 ((Sb : Subgroup ↥B).map B.subtype) := Sb.isPGroup'.map B.subtype
    have hPcyc : IsCyclic ((Sb : Subgroup ↥B).map B.subtype) := hcyc _ hPle hPpos
    let e : ↥(Sb : Subgroup ↥B) ≃* ((Sb : Subgroup ↥B).map B.subtype) :=
      Subgroup.equivMapOfInjective (Sb : Subgroup ↥B) B.subtype B.subtype_injective
    have hSbcyc : IsCyclic ↥(Sb : Subgroup ↥B) := (MulEquiv.isCyclic e).mpr hPcyc
    let K2 : Subgroup ↥B := pPrimeCore 2 ↥B
    obtain ⟨-, hKS, -, ⟨hK2n, hK2odd, -, -⟩, -⟩ :=
      cyclic_sylow_normal_odd_complement Sb hSbcyc
    have : K2.Normal := hK2n
    have hK2solv : Group.IsSolvable ↥K2 := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hK2odd
    have hQcyc : IsCyclic (↥B ⧸ K2) := by
      let f : ↥(Sb : Subgroup ↥B) →* ↥B ⧸ K2 :=
        (QuotientGroup.mk' K2).comp (Sb : Subgroup ↥B).subtype
      have hf : Function.Surjective f := by
        intro y
        obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective K2 y
        have hb : (b : ↥B) ∈ (K2 : Set ↥B) * (Sb : Set ↥B) := by
          rw [hKS]
          trivial
        rcases hb with ⟨k, hk, s, hs, hks⟩
        refine ⟨⟨s, hs⟩, ?_⟩
        change QuotientGroup.mk' K2 s = QuotientGroup.mk' K2 b
        rw [← hks, map_mul]
        have hk1 : QuotientGroup.mk' K2 k = 1 := (QuotientGroup.eq_one_iff k).mpr hk
        rw [hk1, one_mul]
      exact isCyclic_of_surjective f hf
    have hQsolv : Group.IsSolvable (↥B ⧸ K2) := by
      let : CommGroup (↥B ⧸ K2) := IsCyclic.commGroup
      exact Group.isSolvable_of_comm (fun a b => mul_comm a b)
    have : Group.IsSolvable ↥K2 := hK2solv
    have : Group.IsSolvable (↥B ⧸ K2) := hQsolv
    exact Group.isSolvable_of_subgroup_quotient K2
  have hBmap_solv : Group.IsSolvable ((B.subgroupOf T).map q) := by
    have : Group.IsSolvable ↥B := hB_solv
    have hBsolv : Group.IsSolvable ↥(B.subgroupOf T) :=
      Group.isSolvable_of_isSolvable_injective
        (f := (Subgroup.subgroupOfEquivOfLe hBleT).toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hBleT).injective
    have : Group.IsSolvable ↥(B.subgroupOf T) := hBsolv
    let f : ↥(B.subgroupOf T) →* (B.subgroupOf T).map q :=
      (q.comp (B.subgroupOf T).subtype).codRestrict _
        (fun x => Subgroup.mem_map.mpr ⟨x, x.2, rfl⟩)
    exact Group.isSolvable_of_surjective (f := f) (by
      rintro ⟨y, hy⟩
      rcases hy with ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩)
  have hEbar_solv : Group.IsSolvable Ebar := by
    have : Group.IsSolvable ↥((B.subgroupOf T).map q) := hBmap_solv
    exact Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion hEbar_le) (Subgroup.inclusion_injective hEbar_le)
  have hEbar_bot : Ebar = ⊥ := by
    by_contra hne
    let : Nontrivial Ebar := (Subgroup.nontrivial_iff_ne_bot Ebar).2 hne
    let : Group.IsPerfect Ebar := hEbar_perf
    exact Group.IsPerfect.not_isSolvable Ebar hEbar_solv
  have hLleJ : L.subgroupOf T ≤ J.subgroupOf T := by
    have hker : L.subgroupOf T ≤ q.ker := (Subgroup.map_eq_bot_iff (L.subgroupOf T)).mp hEbar_bot
    rwa [QuotientGroup.ker_mk'] at hker
  intro x hx
  have hxT : x ∈ T := hLT hx
  have hx' : (⟨x, hxT⟩ : T) ∈ L.subgroupOf T := Subgroup.mem_subgroupOf.mpr hx
  exact Subgroup.mem_subgroupOf.mp (hLleJ hx')

omit [Finite G] in
theorem exists_mul_eq_mul_of_mem_normalizer {J : Subgroup G} (hJp : Group.IsPerfect ↥J)
    (hOut : ∀ α β : MulAut (↥J ⧸ center ↥J),
      α ∉ (MulAut.conj : (↥J ⧸ center ↥J) →* MulAut (↥J ⧸ center ↥J)).range →
      β ∉ (MulAut.conj : (↥J ⧸ center ↥J) →* MulAut (↥J ⧸ center ↥J)).range →
      α * β ∈ (MulAut.conj : (↥J ⧸ center ↥J) →* MulAut (↥J ⧸ center ↥J)).range)
    {n m : G} (hn : n ∈ normalizer (J : Set G)) (hm : m ∈ normalizer (J : Set G))
    (hn' : ¬ ∃ j ∈ J, ∃ c ∈ centralizer (J : Set G), n = j * c)
    (hm' : ¬ ∃ j ∈ J, ∃ c ∈ centralizer (J : Set G), m = j * c) :
    ∃ j ∈ J, ∃ c ∈ centralizer (J : Set G), n * m = j * c := by
  classical
  have : Group.IsPerfect ↥J := hJp
  let K : Subgroup (MulAut (↥J ⧸ center ↥J)) :=
    (MulAut.conj : (↥J ⧸ center ↥J) →* MulAut (↥J ⧸ center ↥J)).range
  have hautj : ∀ jj : ↥J,
      automizer J ⟨(jj : G), Subgroup.le_normalizer jj.2⟩ =
      (MulAut.conj : (↥J ⧸ center ↥J) →* MulAut (↥J ⧸ center ↥J))
        (QuotientGroup.mk jj) := by
    intro jj
    ext xx
    obtain ⟨ll, rfl⟩ := QuotientGroup.mk_surjective xx
    rw [automizer_apply_mk, MulAut.conj_apply]
    rfl
  have key : ∀ (g : G) (hg : g ∈ normalizer (J : Set G)),
      automizer J ⟨g, hg⟩ ∈ K → ∃ j ∈ J, ∃ c ∈ centralizer (J : Set G), g = j * c := by
    intro g hg hmem
    obtain ⟨q, hq⟩ := hmem
    obtain ⟨jj, rfl⟩ := QuotientGroup.mk_surjective q
    have hjN : (jj : G) ∈ normalizer (J : Set G) := Subgroup.le_normalizer jj.2
    let c : G := g * (jj : G)⁻¹
    have hcN : c ∈ normalizer (J : Set G) :=
      (Subgroup.normalizer (J : Set G)).mul_mem hg
        ((Subgroup.normalizer (J : Set G)).inv_mem hjN)
    have hc_eq : (⟨c, hcN⟩ : Subgroup.normalizer (J : Set G)) =
        ⟨g, hg⟩ * (⟨(jj : G), hjN⟩ : Subgroup.normalizer (J : Set G))⁻¹ := by
      ext
      simp [c]
    have haut : automizer J ⟨c, hcN⟩ = 1 := by
      rw [hc_eq, map_mul, map_inv, hautj jj, ← hq]
      simp
    have hcC : c ∈ centralizer (J : Set G) := (automizer_eq_one_iff J ⟨c, hcN⟩).mp haut
    refine ⟨jj, jj.2, c, hcC, ?_⟩
    have hgc : g = c * (jj : G) := by
      rw [show c = g * (jj : G)⁻¹ from rfl]
      group
    have hcomm : (jj : G) * c = c * (jj : G) :=
      (Subgroup.mem_centralizer_iff.mp hcC) (jj : G) jj.2
    rw [hgc]
    exact hcomm.symm
  have hnK : automizer J ⟨n, hn⟩ ∉ K := fun h => hn' (key n hn h)
  have hmK : automizer J ⟨m, hm⟩ ∉ K := fun h => hm' (key m hm h)
  have hnmK : automizer J ⟨n * m, Subgroup.mul_mem (Subgroup.normalizer (J : Set G)) hn hm⟩ ∈ K := by
    have hsplit : (⟨n * m, Subgroup.mul_mem (Subgroup.normalizer (J : Set G)) hn hm⟩ :
        Subgroup.normalizer (J : Set G)) = ⟨n, hn⟩ * ⟨m, hm⟩ := rfl
    rw [hsplit, map_mul]
    exact hOut _ _ hnK hmK
  exact key (n * m) (Subgroup.mul_mem (Subgroup.normalizer (J : Set G)) hn hm) hnmK

theorem mem_or_mul_mem_of_eq_mul {J : Subgroup G} (hZ : Odd (Nat.card (center ↥J)))
    (hC2 : ∀ P : Subgroup G, P ≤ centralizer (J : Set G) → IsPGroup 2 P → Nat.card P ≤ 2)
    {t : G} (ht : orderOf t = 2) (htJ : t ∈ centralizer (J : Set G))
    {b : G} (hb : ∃ k : ℕ, b ^ 2 ^ k = 1) (hbt : b * t = t * b)
    {j c : G} (hj : j ∈ J) (hc : c ∈ centralizer (J : Set G)) (hbjc : b = j * c) :
    b ∈ J ∨ b * t ∈ J := by
  classical
  obtain ⟨k, hk⟩ := hb
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  ·
    subst hk0
    have hb1 : b = 1 := by simpa using hk
    exact Or.inl (hb1 ▸ J.one_mem)
  have h2k1 : 1 < 2 ^ k := Nat.one_lt_pow (Nat.ne_of_gt hkpos) (by norm_num)
  have ht2 : t ^ 2 = 1 := by
    have h := pow_orderOf_eq_one t
    rw [ht] at h
    exact h
  have htt : t * t = 1 := by
    rw [← pow_two]
    exact ht2
  have hcomm : Commute j c := (Subgroup.mem_centralizer_iff.mp hc) j hj
  have hbN : j ^ 2 ^ k * c ^ 2 ^ k = 1 := by
    rw [← hcomm.mul_pow (2 ^ k), ← hbjc]
    exact hk
  have hinvC : c ^ 2 ^ k = (j ^ 2 ^ k)⁻¹ := eq_inv_of_mul_eq_one_right hbN
  have hinvJ : j ^ 2 ^ k = (c ^ 2 ^ k)⁻¹ := by rw [hinvC, inv_inv]
  have hjNC : j ^ 2 ^ k ∈ centralizer (J : Set G) := by
    rw [hinvJ]
    exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hc _)
  have hcen : (⟨j ^ 2 ^ k, J.pow_mem hj _⟩ : ↥J) ∈ center ↥J := by
    rw [Subgroup.mem_center_iff]
    intro xx
    apply Subtype.ext
    change (xx : G) * j ^ 2 ^ k = j ^ 2 ^ k * (xx : G)
    exact (Subgroup.mem_centralizer_iff.mp hjNC) (xx : G) xx.2
  have huN : (j ^ 2 ^ k) ^ Nat.card (center ↥J) = 1 := by
    have h2 : (⟨j ^ 2 ^ k, J.pow_mem hj _⟩ : ↥J) ^ Nat.card (center ↥J) = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard (center ↥J) hcen)
    have h3 := congrArg (Subtype.val) h2
    simpa [Subgroup.coe_pow] using h3
  have hcN_pow : (c ^ 2 ^ k) ^ Nat.card (center ↥J) = 1 := by
    rw [hinvC, inv_pow, huN, inv_one]
  have hcop : Nat.Coprime (Nat.card (center ↥J)) (2 ^ k) :=
    Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hZ)
  obtain ⟨x, -, hxmod⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop h2k1
  set e : ℕ := Nat.card (center ↥J) * x with he_def
  have he_mod : e % 2 ^ k = 1 := by
    rw [he_def]
    exact hxmod
  have he_dvd : Nat.card (center ↥J) ∣ e := ⟨x, by rw [he_def]⟩
  have hb_e : b ^ e = b := by
    have hdiv : e = 2 ^ k * (e / 2 ^ k) + 1 := by
      have h := Nat.div_add_mod e (2 ^ k)
      rw [he_mod] at h
      exact h.symm
    rw [hdiv, pow_add, pow_mul, hk, one_pow, one_mul, pow_one]
  have hbue : b = j ^ e * c ^ e := by
    rw [← hb_e, hbjc, hcomm.mul_pow e]
  have hc2pow : (c ^ e) ^ 2 ^ k = 1 := by
    have h1 : (c ^ e) ^ 2 ^ k = (c ^ 2 ^ k) ^ e := by
      calc (c ^ e) ^ 2 ^ k = c ^ (e * 2 ^ k) := (pow_mul c e (2 ^ k)).symm
        _ = c ^ (2 ^ k * e) := by rw [Nat.mul_comm e (2 ^ k)]
        _ = (c ^ 2 ^ k) ^ e := pow_mul c (2 ^ k) e
    rw [h1]
    exact orderOf_dvd_iff_pow_eq_one.mp (dvd_trans (orderOf_dvd_of_pow_eq_one hcN_pow) he_dvd)
  have hje_t : Commute (j ^ e) t :=
    (Subgroup.mem_centralizer_iff.mp htJ) (j ^ e) (J.pow_mem hj e)
  have hce_t : c ^ e * t = t * c ^ e := by
    have hceq : c ^ e = (j ^ e)⁻¹ * b := by
      rw [hbue]
      group
    rw [hceq]
    exact ((hje_t.inv_left).mul_left hbt).eq
  have hle : Subgroup.zpowers (c ^ e) ⊔ Subgroup.zpowers t ≤ centralizer (J : Set G) :=
    sup_le (Subgroup.zpowers_le.mpr ((Subgroup.centralizer (J : Set G)).pow_mem hc e))
      (Subgroup.zpowers_le.mpr htJ)
  have hp1 : IsPGroup 2 ↥(Subgroup.zpowers (c ^ e)) := by
    apply IsPGroup.of_card_dvd_pow (n := k)
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one hc2pow
  have hp2 : IsPGroup 2 ↥(Subgroup.zpowers t) := by
    apply IsPGroup.of_card_dvd_pow (n := 1)
    rw [Nat.card_zpowers, ht]
    norm_num
  have hnorm : Subgroup.zpowers (c ^ e) ≤ Subgroup.normalizer (Subgroup.zpowers t) := by
    have hce_comm : Commute (c ^ e) t := hce_t
    have hcent : c ^ e ∈ Subgroup.centralizer (Subgroup.zpowers t : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro hh hhh
      obtain ⟨ll, rfl⟩ := Subgroup.mem_zpowers_iff.mp hhh
      exact ((hce_comm.zpow_right ll).eq).symm
    exact le_trans (Subgroup.zpowers_le.mpr hcent) (Subgroup.centralizer_le_normalizer _)
  have hHp : IsPGroup 2 ↥(Subgroup.zpowers (c ^ e) ⊔ Subgroup.zpowers t) :=
    IsPGroup.to_sup_of_normal_right' hp1 hp2 hnorm
  have hHcard : Nat.card ↥(Subgroup.zpowers (c ^ e) ⊔ Subgroup.zpowers t) ≤ 2 := hC2 _ hle hHp
  have hzeq : Subgroup.zpowers t = Subgroup.zpowers (c ^ e) ⊔ Subgroup.zpowers t :=
    Subgroup.eq_of_le_of_card_ge le_sup_right (by rw [Nat.card_zpowers, ht]; exact hHcard)
  have hce_mem : c ^ e ∈ Subgroup.zpowers t := by
    rw [hzeq]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
  have hce_cases : c ^ e = 1 ∨ c ^ e = t := by
    obtain ⟨ll, hll⟩ := Subgroup.mem_zpowers_iff.mp hce_mem
    have ht2z : t ^ (2 : ℤ) = 1 := by
      rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, ht2]
    rw [← hll]
    obtain ⟨mm, rfl | rfl⟩ := Int.even_or_odd' ll
    · left
      rw [zpow_mul, ht2z, one_zpow]
    · right
      rw [zpow_add, zpow_mul, ht2z, one_zpow, one_mul, zpow_one]
  have huJ : j ^ e ∈ J := J.pow_mem hj e
  rcases hce_cases with h1 | h1
  · left
    rw [hbue, h1, mul_one]
    exact huJ
  · right
    rw [hbue, h1, mul_assoc, htt, mul_one]
    exact huJ

end CFSG.ComponentClassification.GrSLit.L34Sec5S

end
