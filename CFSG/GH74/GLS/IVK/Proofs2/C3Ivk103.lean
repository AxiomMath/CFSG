module

public import CFSG.GH74.GLS.IVK.Proofs2.C3Ivk103Bar
public import CFSG.GH74.GLS.Stage1.Thm2.Recip.Comp
public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.Equiv

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74.GLS
open scoped commutatorElement

theorem exists_lift_involution {H : Type*} [Group H] [Finite H] (N : Subgroup H) [N.Normal]
    (hN : Odd (Nat.card ↥N)) {ub : H ⧸ N} (hub : orderOf ub = 2) :
    ∃ u : H, orderOf u = 2 ∧ (u : H ⧸ N) = ub := by
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective ub
  have h2 : 2 ∣ orderOf k := by
    rw [← hub]
    exact orderOf_map_dvd (QuotientGroup.mk' N) k
  have hsq : ((k : H ⧸ N)) ^ 2 = 1 := by
    rw [← hub]
    exact pow_orderOf_eq_one _
  have hk2 : k ^ 2 ∈ N :=
    (QuotientGroup.eq_one_iff (k ^ 2)).1 (by rw [QuotientGroup.mk_pow]; exact hsq)
  have hodd2 : Odd (orderOf (k ^ 2)) :=
    Odd.of_dvd_nat hN (Subgroup.orderOf_dvd_natCard N hk2)
  obtain ⟨m, hm⟩ := h2
  have hpos : 0 < orderOf k := orderOf_pos k
  have hm0 : m ≠ 0 := by
    rintro rfl
    omega
  have hord2 : orderOf (k ^ 2) = m := by
    rw [orderOf_pow_of_dvd (by norm_num) ⟨m, hm⟩, hm]
    omega
  rw [hord2] at hodd2
  refine ⟨k ^ m, ?_, ?_⟩
  · rw [orderOf_pow_of_dvd hm0 ⟨2, by rw [hm]; ring⟩, hm]
    exact Nat.mul_div_cancel 2 (Nat.pos_of_ne_zero hm0)
  · obtain ⟨j, hj⟩ := hodd2
    rw [QuotientGroup.mk_pow, hj, pow_succ, pow_mul, hsq, one_pow, one_mul]

theorem le_pPrimeCoreOf_of_normalized' {H : Type*} [Group H] [Finite H] {C W : Subgroup H}
    (hWC : W ≤ C) (hnorm : ∀ c ∈ C, ∀ w ∈ W, c * w * c⁻¹ ∈ W) (hodd : Odd (Nat.card ↥W)) :
    W ≤ pPrimeCoreOf 2 C := by
  have hN : (W.subgroupOf C).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hnorm g g.2 n hn⟩
  have hodd' : Odd (Nat.card ↥(W.subgroupOf C)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWC).toEquiv]
    exact hodd
  have hle : W.subgroupOf C ≤ pPrimeCore 2 ↥C := Lemma118.le_pPrimeCore_of_normal _ hodd'
  rw [← Subgroup.map_subgroupOf_eq_of_le hWC]
  exact Subgroup.map_mono hle

theorem exists_mem_pPrimeCoreOf_centralizer {H : Type*} [Group H] [Finite H] (N : Subgroup H)
    [N.Normal] (hN : Odd (Nat.card ↥N)) {u : H} (hu : orderOf u = 2)
    (hne : pPrimeCoreOf 2 (Subgroup.centralizer ({(u : H ⧸ N)} : Set (H ⧸ N))) ≠ ⊥) :
    ∃ k ∈ pPrimeCoreOf 2 (Subgroup.centralizer ({u} : Set H)), (k : H ⧸ N) ≠ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA : IsPGroup 2 ↥(Subgroup.zpowers u) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hu]; norm_num)
  have hN2 : ¬ 2 ∣ Nat.card ↥N := by
    intro h
    exact (Nat.not_even_iff_odd.2 hN) (even_iff_two_dvd.2 h)
  obtain ⟨-, hcore, -, -⟩ :=
    CFSG.Semidihedral.Local.coprime_centralizer_prime_complement_core_quotient 2 N hN2
      (Subgroup.zpowers u) hA
  have hcA : (Subgroup.centralizer (↑(Subgroup.zpowers u) : Set H)) =
      Subgroup.centralizer ({u} : Set H) := by
    ext g
    simp only [Subgroup.mem_centralizer_iff, SetLike.mem_coe, Set.mem_singleton_iff,
      forall_eq]
    constructor
    · intro h
      exact h u (Subgroup.mem_zpowers u)
    · intro h a ha
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
      have h1 : Commute u g := h
      exact (h1.zpow_left n).eq
  have hcQ : (Subgroup.centralizer
      (↑((Subgroup.zpowers u).map (QuotientGroup.mk' N)) : Set (H ⧸ N))) =
      Subgroup.centralizer ({(u : H ⧸ N)} : Set (H ⧸ N)) := by
    ext g
    simp only [Subgroup.mem_centralizer_iff, SetLike.mem_coe, Set.mem_singleton_iff,
      forall_eq]
    constructor
    · intro h
      exact h _ ⟨u, Subgroup.mem_zpowers u, rfl⟩
    · intro h a ha
      obtain ⟨b, hb, rfl⟩ := ha
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
      have h1 : Commute (u : H ⧸ N) g := h
      have h2 := (h1.zpow_left n).eq
      simpa [map_zpow] using h2
  rw [hcA, hcQ] at hcore
  by_contra hcon
  have hcon' : ∀ k ∈ pPrimeCoreOf 2 (Subgroup.centralizer ({u} : Set H)), (k : H ⧸ N) = 1 :=
    fun k hk => by
      by_contra hk1
      exact hcon ⟨k, hk, hk1⟩
  apply hne
  have : (pPrimeCoreOf 2 (Subgroup.centralizer ({u} : Set H))).map (QuotientGroup.mk' N) = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨k, hk, rfl⟩
    exact hcon' k hk
  exact (show pPrimeCoreOf 2 (Subgroup.centralizer ({(u : H ⧸ N)} : Set (H ⧸ N))) =
    (pPrimeCoreOf 2 (Subgroup.centralizer ({u} : Set H))).map (QuotientGroup.mk' N) from
      hcore.symm).trans this

section GLevel

variable {G : Type} [Group G] [Finite G]

open CFSG.GH74.GLS.Stage1.Thm2.Recip CFSG.GH74.GLS.Stage1.Thm3.Sec4

omit [Finite G] in
theorem mk_mem_center_of_mem_centralizerSection {K : Subgroup G} {a : ↥K}
    (h : (a : G) ∈ centralizerSection K (pPrimeCoreOf 2 K)) :
    (QuotientGroup.mk a : kBar K) ∈ Subgroup.center (kBar K) := by
  rw [Subgroup.mem_center_iff]
  intro g
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective g
  have h1 : ⁅(l : G), (a : G)⁆ ∈ pPrimeCoreOf 2 K := h.2.2 (l : G) l.2
  have h2 : ⁅l, a⁆ ∈ pPrimeCore 2 ↥K := by
    obtain ⟨b, hb, hbe⟩ := h1
    have : b = ⁅l, a⁆ := Subtype.ext (hbe.trans (by simp [commutatorElement_def]))
    rw [← this]
    exact hb
  have h3 : ((⁅l, a⁆ : ↥K) : kBar K) = 1 := (QuotientGroup.eq_one_iff _).2 h2
  have h4 : ⁅(l : kBar K), (a : kBar K)⁆ = 1 := by
    have := map_commutatorElement (QuotientGroup.mk' (pPrimeCore 2 ↥K)) l a
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at this
    rw [← this]
    exact h3
  exact commutatorElement_eq_one_iff_mul_comm.1 h4

theorem b_ivk_10_3_of_gen4
    (hL34 : B_gen4_noL34_elem) : B_ivk_10_3 := by
  intro G _ _ hG x K hpair hU2 hnC2
  have hnL34 := hL34 G hG.gen4 x K hpair.1 hpair.2
  obtain ⟨hcen, ub, hub, hxu⟩ := exists_involution_oddcore hU2 hnC2 hnL34
  have hNodd : Odd (Nat.card ↥(pPrimeCore 2 ↥K)) :=
    Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := ↥K))
  obtain ⟨u, hu2, rfl⟩ := exists_lift_involution (pPrimeCore 2 ↥K) hNodd hub
  have hxu' : pPrimeCoreOf 2 (Subgroup.centralizer ({(u : kBar K)} : Set (kBar K))) ≠ ⊥ := by
    have e : xu (MulAut.conj (u : kBar K)) =
        pPrimeCoreOf 2 (fixedSubgroup (kBar K) (MulAut.conj (u : kBar K))) := rfl
    rw [e, Lemma118.fixedSubgroup_conj] at hxu
    exact hxu
  obtain ⟨k0, hk0, hk0ne⟩ := exists_mem_pPrimeCoreOf_centralizer (pPrimeCore 2 ↥K) hNodd hu2 hxu'
  set y : G := (u : G) with hy
  have hyK : y ∈ K := u.2
  have hy2 : orderOf y = 2 := by rw [hy, Subgroup.orderOf_coe]; exact hu2
  have hKX : K ≤ centralizer ({x} : Set G) := hpair.2.1
  have hyX : y ∈ centralizer ({x} : Set G) := hKX hyK
  refine ⟨y, hpair, hy2, hyX, le_normalizer hyK, ?_⟩
  intro hle
  set Z : Subgroup G := centralizer ({x, y} : Set G) with hZdef
  have hZmem : ∀ z, z ∈ Z ↔ z * x = x * z ∧ z * y = y * z := by
    intro z
    simp only [hZdef, Subgroup.mem_centralizer_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
      forall_eq_or_imp, forall_eq]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1.symm, h2.symm⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1.symm, h2.symm⟩
  have hZX : Z ≤ centralizer ({x} : Set G) := fun z hz => by
    rw [mem_centralizer_singleton_iff]
    exact ((hZmem z).1 hz).1
  have hZN : Z ≤ normalizer (K : Set G) := by
    intro z hz
    by_contra hzN
    have hzX : z ∈ centralizer ({x} : Set G) := hZX hz
    have hK' : cmap z K ≠ K := fun h =>
      hzN (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h)
    have hcX' : cmap z (centralizer ({x} : Set G)) = centralizer ({x} : Set G) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (le_normalizer hzX)
    have hK'c : IsPCompIn 2 (centralizer ({x} : Set G)) (cmap z K) := by
      have := isPCompIn_cmap hpair.2 z
      rwa [hcX'] at this
    have h1 : cmap z K ≤ cSec K := le_cSec_of_ne hK'c hpair.2 hK'
    have hyK' : y ∈ cmap z K := by
      rw [mem_cmap]
      have e : z⁻¹ * y * z = y := by
        have := ((hZmem z).1 hz).2
        rw [mul_assoc, ← this]
        group
      rw [e]
      exact hyK
    have hcen' := mk_mem_center_of_mem_centralizerSection (a := u) (h1 hyK')
    rw [hcen, Subgroup.mem_bot] at hcen'
    rw [hcen', orderOf_one] at hub
    omega
  set D : Subgroup G := K ⊓ centralizer ({y} : Set G) with hDdef
  have hDK : D ≤ K := inf_le_left
  have hDZ : D ≤ Z := fun d hd => by
    rw [hZmem]
    exact ⟨mem_centralizer_singleton_iff.1 (hKX hd.1), mem_centralizer_singleton_iff.1 hd.2⟩
  have hZY : ∀ z ∈ Z, z ∈ centralizer ({y} : Set G) := fun z hz => by
    rw [mem_centralizer_singleton_iff]
    exact ((hZmem z).1 hz).2
  have hDnorm : ∀ z ∈ Z, z ∈ normalizer (D : Set G) := fun z hz =>
    TwoThin.mem_normalizer_inf (hZN hz) (le_normalizer (hZY z hz))
  have hWD : pPrimeCoreOf 2 D ≤ pPrimeCoreOf 2 Z := by
    refine le_pPrimeCoreOf_of_normalized' ((TwoThin.pPrimeCoreOf_le D).trans hDZ) ?_
      (TwoThin.card_pPrimeCoreOf_odd D)
    intro c hc w hw
    exact TwoThin.mul_mem_pPrimeCoreOf_of_mem_normalizer (hDnorm c hc) hw
  have hDsub : D.subgroupOf K = Subgroup.centralizer ({u} : Set ↥K) := by
    ext a
    constructor
    · intro h
      rw [Subgroup.mem_subgroupOf] at h
      exact mem_centralizer_singleton_iff.2 (Subtype.ext (mem_centralizer_singleton_iff.1 h.2))
    · intro h
      rw [Subgroup.mem_subgroupOf]
      exact ⟨a.2, mem_centralizer_singleton_iff.2
        (congrArg Subtype.val (mem_centralizer_singleton_iff.1 h))⟩
  have hkD : (k0 : G) ∈ pPrimeCoreOf 2 D := by
    rw [TwoThin.pPrimeCoreOf_eq_map_subgroupOf hDK, hDsub]
    exact ⟨k0, hk0, rfl⟩
  have hkc : (k0 : G) ∈ centralizerSection K (pPrimeCoreOf 2 K) := hle (hWD hkD)
  have hk1 := mk_mem_center_of_mem_centralizerSection (a := k0) hkc
  rw [hcen, Subgroup.mem_bot] at hk1
  exact hk0ne hk1

end GLevel

end CFSG.GH74.GLS.IVK.Proofs2
