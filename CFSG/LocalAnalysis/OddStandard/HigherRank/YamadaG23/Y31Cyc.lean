module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTdict1

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} (s : Setting3 G L)

private theorem eq_of_orderOf_eq_two {C : Type*} [Group C] [Finite C] [IsCyclic C] {x y : C}
    (hx : orderOf x = 2) (hy : orderOf y = 2) : x = y := by
  classical
  have : Fintype C := Fintype.ofFinite C
  by_contra hxy
  have hx2 : x ^ 2 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hy2 : y ^ 2 = 1 := by rw [← hy]; exact pow_orderOf_eq_one y
  have hx1 : x ≠ 1 := by rintro rfl; rw [orderOf_one] at hx; norm_num at hx
  have hy1 : y ≠ 1 := by rintro rfl; rw [orderOf_one] at hy; norm_num at hy
  have hle := IsCyclic.card_pow_eq_one_le (α := C) (n := 2) (by norm_num)
  have hsub : ({1, x, y} : Finset C) ⊆ Finset.univ.filter (fun a : C => a ^ 2 = 1) := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases ha with rfl | rfl | rfl
    · exact one_pow 2
    · exact hx2
    · exact hy2
  have hcard : ({1, x, y} : Finset C).card = 3 := by
    rw [Finset.card_insert_of_notMem (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨Ne.symm hx1, Ne.symm hy1⟩), Finset.card_pair hxy]
  have := Finset.card_le_card hsub
  change _ ≤ (Finset.univ.filter (fun a : C => a ^ 2 = 1)).card at this
  have h2 : (Finset.univ.filter (fun a : C => a ^ 2 = 1)).card ≤ 2 := by
    convert hle using 2
  omega

theorem cyc_of_isPGroup_cent (hS : HRSetting G L) {P : Subgroup G} (hP : IsPGroup 2 P)
    (hPC : P ≤ centralizer (L : Set G)) : IsCyclic ↥P := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S₀, hS₀⟩ := hS.cyclic
  have hP' : IsPGroup 2 (P.subgroupOf (centralizer (L : Set G))) :=
    hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPC).symm
  obtain ⟨Q, hQ⟩ := hP'.exists_le_sylow
  haveI : Finite (Sylow 2 ↥(centralizer (L : Set G))) := Sylow.finite_of_finiteIndex Q
  haveI : IsCyclic ↥Q := (Sylow.equiv S₀ Q).isCyclic.mp hS₀
  have hP'cyc : IsCyclic ↥(P.subgroupOf (centralizer (L : Set G))) :=
    Subgroup.isCyclic_of_le hQ
  exact (Subgroup.subgroupOfEquivOfLe hPC).isCyclic.mp hP'cyc

theorem s3_invol_cenH (hS : HRSetting G L) {c : G} (hc : c ∈ centIn s.H L)
    (hc2 : orderOf c = 2) : c = s.t := by
  rcases Subgroup.mem_inf.mp hc with ⟨hcH, hcC⟩
  have hct : Commute c s.t := (Subgroup.mem_centralizer_iff.mp hcH s.t (by simp)).symm
  let K : Subgroup G := Subgroup.zpowers c ⊔ Subgroup.zpowers s.t
  have hcK : c ∈ K := Subgroup.mem_sup_left (Subgroup.mem_zpowers c)
  have htK : s.t ∈ K := Subgroup.mem_sup_right (Subgroup.mem_zpowers s.t)
  have hK2 : IsPGroup 2 K := by
    have hc_cent : c ∈ Subgroup.centralizer (Subgroup.zpowers s.t : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      exact (hct.zpow_right n).eq.symm
    have hcz : Subgroup.zpowers c ≤ Subgroup.normalizer (Subgroup.zpowers s.t : Set G) := by
      rw [Subgroup.zpowers_le]
      exact Subgroup.centralizer_le_normalizer _ hc_cent
    have hc2grp : IsPGroup 2 (Subgroup.zpowers c) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hc2]; norm_num)
    have ht2grp : IsPGroup 2 (Subgroup.zpowers s.t) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, s.t_order]; norm_num)
    exact IsPGroup.to_sup_of_normal_right' hc2grp ht2grp hcz
  have hKC : K ≤ centralizer (L : Set G) :=
    sup_le (Subgroup.zpowers_le.mpr hcC) (Subgroup.zpowers_le.mpr s.t_mem)
  haveI : IsCyclic ↥K := cyc_of_isPGroup_cent hS hK2 hKC
  have hordc : orderOf (⟨c, hcK⟩ : ↥K) = 2 := (Subgroup.orderOf_mk c hcK).trans hc2
  have hordt : orderOf (⟨s.t, htK⟩ : ↥K) = 2 := (Subgroup.orderOf_mk s.t htK).trans s.t_order
  simpa using Subtype.ext_iff.mp (eq_of_orderOf_eq_two hordc hordt)

theorem s3_Q_cyclic (hS : HRSetting G L) : IsCyclic ↥(s.T ⊓ centralizer (L : Set G)) :=
  cyc_of_isPGroup_cent hS s.sylow_T.2.1.to_inf_left inf_le_right

theorem s3_t_mem_Q : s.t ∈ s.T ⊓ centralizer (L : Set G) :=
  Subgroup.mem_inf.mpr ⟨s3_t_mem_T s, s.t_mem⟩

theorem s3_Q_invol (hS : HRSetting G L) {u : G} (hu : u ∈ s.T ⊓ centralizer (L : Set G))
    (hu2 : orderOf u = 2) : u = s.t := by
  haveI : IsCyclic ↥(s.T ⊓ centralizer (L : Set G)) := s3_Q_cyclic s hS
  have htQ : s.t ∈ s.T ⊓ centralizer (L : Set G) := s3_t_mem_Q s
  have huord : orderOf (⟨u, hu⟩ : ↥(s.T ⊓ centralizer (L : Set G))) = 2 :=
    (Subgroup.orderOf_mk u hu).trans hu2
  have htord : orderOf (⟨s.t, htQ⟩ : ↥(s.T ⊓ centralizer (L : Set G))) = 2 :=
    (Subgroup.orderOf_mk s.t htQ).trans s.t_order
  simpa using Subtype.ext_iff.mp (eq_of_orderOf_eq_two huord htord)

theorem s3_Q_sq_root (hS : HRSetting G L) {q₀ : G} (hq₀ : q₀ ∈ s.T ⊓ centralizer (L : Set G))
    (hq₀t : q₀ ∉ zpowers s.t) : ∃ q ∈ s.T ⊓ centralizer (L : Set G), q ^ 2 = s.t := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ2 : IsPGroup 2 ↥(s.T ⊓ centralizer (L : Set G)) := s.sylow_T.2.1.to_inf_left
  obtain ⟨k, hk⟩ := hQ2.exists_orderOf_eq_pow ⟨q₀, hq₀⟩
  have hord : orderOf q₀ = 2 ^ k := (Subgroup.orderOf_mk q₀ hq₀).symm.trans hk
  have hk2 : 2 ≤ k := by
    by_contra hk'
    have hk01 : k = 0 ∨ k = 1 := by omega
    rcases hk01 with rfl | rfl
    · have h1 : q₀ = 1 := by rw [← orderOf_eq_one_iff, hord]; norm_num
      rw [h1] at hq₀t
      exact hq₀t (Subgroup.one_mem _)
    · have hq : q₀ = s.t := s3_Q_invol s hS hq₀ (by rw [hord]; norm_num)
      rw [hq] at hq₀t
      exact hq₀t (Subgroup.mem_zpowers s.t)
  have hm_ne : orderOf q₀ ≠ 0 := by rw [hord]; exact pow_ne_zero _ (by norm_num)
  have h4dvd : 4 ∣ orderOf q₀ := by
    rw [hord, show (4 : ℕ) = 2 ^ 2 from by norm_num]
    exact pow_dvd_pow 2 hk2
  refine ⟨q₀ ^ (orderOf q₀ / 4), Subgroup.pow_mem _ hq₀ _, ?_⟩
  have hqord : orderOf (q₀ ^ (orderOf q₀ / 4)) = 4 := orderOf_pow_orderOf_div hm_ne h4dvd
  have hq2ord : orderOf ((q₀ ^ (orderOf q₀ / 4)) ^ 2) = 2 := by
    rw [orderOf_pow_of_dvd (n := 2) (by norm_num) (by rw [hqord]; norm_num), hqord]
  exact s3_Q_invol s hS (Subgroup.pow_mem _ (Subgroup.pow_mem _ hq₀ _) 2) hq2ord

theorem s3_Q_sq_unique (hS : HRSetting G L) {q q' : G} (hq : q ∈ s.T ⊓ centralizer (L : Set G))
    (hq' : q' ∈ s.T ⊓ centralizer (L : Set G)) (h : q ^ 2 = s.t) (h' : q' ^ 2 = s.t) :
    q' = q ∨ q' = q⁻¹ := by
  haveI : IsCyclic ↥(s.T ⊓ centralizer (L : Set G)) := s3_Q_cyclic s hS
  have hr2 : (q' * q⁻¹) ^ 2 = 1 := by
    rw [Commute.mul_pow (setLike_mul_comm hq' (Subgroup.inv_mem _ hq)), h', inv_pow, h]
    exact mul_inv_cancel s.t
  have hr_mem : q' * q⁻¹ ∈ s.T ⊓ centralizer (L : Set G) :=
    Subgroup.mul_mem _ hq' (Subgroup.inv_mem _ hq)
  have hr : q' * q⁻¹ = 1 ∨ q' * q⁻¹ = s.t := by
    have hdvd : orderOf (q' * q⁻¹) ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hr2
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
    · exact Or.inl (orderOf_eq_one_iff.mp h1)
    · exact Or.inr (s3_Q_invol s hS hr_mem h2)
  rcases hr with hr1 | hrt
  · exact Or.inl (mul_inv_eq_one.mp hr1)
  · have hq4 : q ^ 4 = 1 := by
      have h4 : q ^ 4 = (q ^ 2) ^ 2 := by rw [← pow_mul]
      rw [h4, h]
      simpa [s.t_order] using pow_orderOf_eq_one s.t
    have hq3 : q ^ 3 = q⁻¹ := eq_inv_of_mul_eq_one_left (by
      rw [← pow_succ, show (3 : ℕ) + 1 = 4 from rfl, hq4])
    have hq3eq : q' = q ^ 3 := by
      have h1 : (q' * q⁻¹) * q = q' := by group
      calc q' = (q' * q⁻¹) * q := h1.symm
        _ = s.t * q := by rw [hrt]
        _ = q ^ 3 := by rw [← h]; group
    exact Or.inr (hq3eq.trans hq3)

theorem s3_Q_normalized (hS : HRSetting G L) {y : G} (hy : y ∈ s.T) {q : G}
    (hq : q ∈ s.T ⊓ centralizer (L : Set G)) : y * q * y⁻¹ ∈ s.T ⊓ centralizer (L : Set G) := by
  rcases Subgroup.mem_inf.mp hq with ⟨hqT, hqC⟩
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · exact s.T.mul_mem (s.T.mul_mem hy hqT) (s.T.inv_mem hy)
  · rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have hconj : y⁻¹ * l * y ∈ L :=
      ((Subgroup.mem_normalizer_iff''.mp (s3_T_le_N s hS hy)) l).mp hl
    have hcomm : (y⁻¹ * l * y) * q = q * (y⁻¹ * l * y) :=
      Subgroup.mem_centralizer_iff.mp hqC (y⁻¹ * l * y) hconj
    calc l * (y * q * y⁻¹)
        = y * ((y⁻¹ * l * y) * q) * y⁻¹ := by group
      _ = y * (q * (y⁻¹ * l * y)) * y⁻¹ := by rw [hcomm]
      _ = (y * q * y⁻¹) * l := by group

theorem s3_t_not_mem_L_of_odd (hZ : Odd (Nat.card ↥(center ↥L))) : s.t ∉ L := by
  intro htL
  have hmem : (⟨s.t, htL⟩ : ↥L) ∈ center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro x
    apply Subtype.ext
    simpa using s3_comm_t_of_mem_L s x.2
  have hzord : orderOf (⟨⟨s.t, htL⟩, hmem⟩ : ↥(center ↥L)) = 2 := by
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk]
    exact s.t_order
  have hdvd : 2 ∣ Nat.card ↥(center ↥L) := by
    rw [← hzord]
    exact orderOf_dvd_natCard _
  exact (Nat.not_odd_iff_even.mpr (even_iff_two_dvd.mpr hdvd)) hZ

end CFSG.OddStandard.HigherRank.YamadaG23
