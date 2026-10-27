module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Out1L12Calc
public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.OddStandard.SmallF3.Omega

variable {S : Type} [Group S]

private theorem aor_l12_u2_comm_t {t u : S} (h : L12Coord S t u) : u ^ 2 * t = t * u ^ 2 :=
  (show Commute u t from h.comm).pow_left 2

private theorem aor_l12_conj_mem_R {t n x : S} (hn : n ∈ L12N t) (hx : x ∈ L12R t) :
    n * x * n⁻¹ ∈ L12R t :=
  (Subgroup.mem_set_normalizer_iff.mp hn x).mp hx

private theorem aor_l12_conj_z {t u : S} (h : L12Coord S t u) {n : S} (hn : n ∈ L12N t) :
    n * u ^ 2 * n⁻¹ = u ^ 2 := by
  have huR : u ∈ L12R t := Subgroup.mem_centralizer_singleton_iff.mpr h.comm
  have hyR : n * u * n⁻¹ ∈ L12R t := aor_l12_conj_mem_R hn huR
  have hyR' : (n * u * n⁻¹) * t = t * (n * u * n⁻¹) :=
    Subgroup.mem_centralizer_singleton_iff.mp hyR
  have hconj : (n * u * n⁻¹) ^ 2 = n * u ^ 2 * n⁻¹ := by rw [conj_pow]
  rcases h.R_sq hyR' with h1 | h1
  · rw [hconj] at h1
    exfalso
    have hz1 : u ^ 2 = 1 := by
      rw [show u ^ 2 = n⁻¹ * (n * u ^ 2 * n⁻¹) * n by group, h1]
      group
    exact h.z_ne_one hz1
  · rwa [hconj] at h1

private theorem aor_l12_conj_comm_iff {t u : S} (h : L12Coord S t u)
    (huz : ∀ y : S, y * u ^ 2 = u ^ 2 * y) {x r : S} (hx : x * t * x⁻¹ = u ^ 2 * t) :
    (x * r * x⁻¹) * t = t * (x * r * x⁻¹) ↔ r * t = t * r := by
  have hx' : x⁻¹ * t * x = u ^ 2 * t := by
    have h1 : t = x⁻¹ * (x * t * x⁻¹) * x := by group
    rw [hx] at h1
    have h3 : x⁻¹ * (u ^ 2 * t) * x = u ^ 2 * (x⁻¹ * t * x) := by
      rw [show x⁻¹ * (u ^ 2 * t) * x = (x⁻¹ * u ^ 2) * (t * x) by group, huz x⁻¹]
      group
    rw [h3] at h1
    have h4 : u ^ 2 * t = x⁻¹ * t * x := by
      have := congrArg (fun z => u ^ 2 * z) h1
      rwa [← mul_assoc, ← pow_two, h.z_sq, one_mul] at this
    exact h4.symm
  have hstep : r * (u ^ 2 * t) = u ^ 2 * (r * t) := by
    rw [← mul_assoc, huz r, mul_assoc]
  constructor
  · intro hh
    have h1 : r * (x⁻¹ * t * x) = (x⁻¹ * t * x) * r := by
      calc r * (x⁻¹ * t * x)
          = x⁻¹ * ((x * r * x⁻¹) * t) * x := by group
        _ = x⁻¹ * (t * (x * r * x⁻¹)) * x := by rw [hh]
        _ = (x⁻¹ * t * x) * r := by group
    rw [hx'] at h1
    have h2 : u ^ 2 * (r * t) = u ^ 2 * (t * r) := by
      calc u ^ 2 * (r * t) = r * (u ^ 2 * t) := by rw [← mul_assoc, (huz r).symm, mul_assoc]
        _ = (u ^ 2 * t) * r := h1
        _ = u ^ 2 * (t * r) := by rw [mul_assoc]
    exact mul_left_cancel h2
  · intro hr
    have h1 : r * (x⁻¹ * t * x) = (x⁻¹ * t * x) * r := by
      rw [hx']
      calc r * (u ^ 2 * t) = u ^ 2 * (r * t) := hstep
        _ = u ^ 2 * (t * r) := by rw [hr]
        _ = (u ^ 2 * t) * r := by rw [mul_assoc]
    calc (x * r * x⁻¹) * t
        = x * (r * (x⁻¹ * t * x)) * x⁻¹ := by group
      _ = x * ((x⁻¹ * t * x) * r) * x⁻¹ := by rw [h1]
      _ = t * (x * r * x⁻¹) := by group

theorem aor_l12_z_central [Finite S] (hS : IsPGroup 2 S) {t u : S} (h : L12Coord S t u)
    (hnc : ¬ ∀ x : S, x * t = t * x) : ∀ x : S, x * u ^ 2 = u ^ 2 * x := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Nontrivial S := ⟨t, 1, h.t_ne_one⟩
  haveI : Group.IsNilpotent S := IsPGroup.isNilpotent hS
  obtain ⟨n, hn0, hncard⟩ := hS.nontrivial_iff_card.mp inferInstance
  have hdvd : 2 ∣ Nat.card S := hncard.symm ▸ dvd_pow_self 2 hn0.ne'
  have hcdvd : 2 ∣ Nat.card (Subgroup.center S) :=
    Group.IsNilpotent.prime_dvd_card_center (p := 2) hdvd
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center S) 2 hcdvd
  have hwne : w ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hw
    exact absurd hw (by decide)
  have hw2 : (w : S) ^ 2 = 1 := by
    have h1 := pow_orderOf_eq_one w
    rw [hw] at h1
    simpa using congrArg (fun z : Subgroup.center S => (z : S)) h1
  have hwR : (w : S) ∈ L12R t :=
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_center_iff.mp w.2 t).symm
  rcases h.R_inv (Subgroup.mem_centralizer_singleton_iff.mp hwR) hw2 with h1 | h1 | h1 | h1
  · exfalso
    exact hwne (Subtype.ext h1)
  · intro x
    rw [← h1]
    exact Subgroup.mem_center_iff.mp w.2 x
  · exfalso
    apply hnc
    intro x
    have hc := Subgroup.mem_center_iff.mp w.2 x
    rw [h1] at hc
    exact hc
  · exfalso
    have hu2 : u ^ 2 = (w : S) * t := by
      rw [h1, mul_assoc, ← pow_two, h.t_sq, mul_one]
    have hNR : L12N t ≤ L12R t := by
      intro n hn
      have hcu : n * u ^ 2 = u ^ 2 * n :=
        calc n * u ^ 2 = (n * u ^ 2 * n⁻¹) * n := by group
          _ = u ^ 2 * n := by rw [aor_l12_conj_z h hn]
      have hW := Subgroup.mem_center_iff.mp w.2 n
      have hnt : n * t = t * n := by
        have key := hcu
        rw [hu2] at key
        have hleft : n * ((w : S) * t) = (w : S) * (n * t) := by
          rw [← mul_assoc, hW, mul_assoc]
        have hright : ((w : S) * t) * n = (w : S) * (t * n) := by
          rw [mul_assoc]
        have h2 : (w : S) * (n * t) = (w : S) * (t * n) := by
          rw [← hleft, ← hright]
          exact key
        exact mul_left_cancel h2
      exact Subgroup.mem_centralizer_singleton_iff.mpr hnt
    have hRlt : L12R t < ⊤ := by
      rw [lt_top_iff_ne_top]
      intro htop
      apply hnc
      intro x
      have hxR : x ∈ L12R t := by rw [htop]; trivial
      exact Subgroup.mem_centralizer_singleton_iff.mp hxR
    have hlt : L12R t < L12N t :=
      Group.normalizerCondition_of_isNilpotent (G := S) (L12R t) hRlt
    exact (lt_irrefl _) (lt_of_lt_of_le hlt hNR)

theorem aor_l12_N_conj [Finite S] (hS : IsPGroup 2 S) {t u : S} (h : L12Coord S t u)
    (hnc : ¬ ∀ x : S, x * t = t * x) {n : S} (hn : n ∈ L12N t) :
    n * t * n⁻¹ = t ∨ n * t * n⁻¹ = t * u ^ 2 := by
  have hz := aor_l12_z_central hS h hnc
  have htR : t ∈ L12R t := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hyR : n * t * n⁻¹ ∈ L12R t := aor_l12_conj_mem_R hn htR
  have hyR' : (n * t * n⁻¹) * t = t * (n * t * n⁻¹) :=
    Subgroup.mem_centralizer_singleton_iff.mp hyR
  have hy2 : (n * t * n⁻¹) ^ 2 = 1 := by
    rw [conj_pow, h.t_sq, mul_one, mul_inv_cancel]
  rcases h.R_inv hyR' hy2 with h1 | h1 | h1 | h1
  · exfalso
    have ht1 : t = 1 := by
      have hc := congrArg (fun z => n⁻¹ * z * n) h1
      rwa [show n⁻¹ * (n * t * n⁻¹) * n = t by group,
        show n⁻¹ * (1 : S) * n = 1 by group] at hc
    exact h.t_ne_one ht1
  · exfalso
    have ht2 : t = u ^ 2 := by
      have hc := congrArg (fun z => n⁻¹ * z * n) h1
      rw [show n⁻¹ * (n * t * n⁻¹) * n = t by group] at hc
      rwa [show n⁻¹ * u ^ 2 * n = u ^ 2 by rw [hz n⁻¹]; group] at hc
    exact h.t_ne_z ht2
  · exact Or.inl h1
  · exact Or.inr (by rw [h1]; exact aor_l12_u2_comm_t h)

theorem aor_l12_exists_N [Finite S] (hS : IsPGroup 2 S) {t u : S} (h : L12Coord S t u)
    (hnc : ¬ ∀ x : S, x * t = t * x) : ∃ n ∈ L12N t, n * t ≠ t * n := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsNilpotent S := IsPGroup.isNilpotent hS
  have hRlt : L12R t < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    apply hnc
    intro x
    have hxR : x ∈ L12R t := by rw [htop]; trivial
    exact Subgroup.mem_centralizer_singleton_iff.mp hxR
  have hnormal := Group.normalizerCondition_of_isNilpotent (G := S) (L12R t) hRlt
  obtain ⟨-, n, hnN, hnR⟩ := SetLike.lt_iff_le_and_exists.mp hnormal
  refine ⟨n, hnN, ?_⟩
  intro hcomm
  exact hnR (Subgroup.mem_centralizer_singleton_iff.mpr hcomm)

theorem aor_l12_N_card [Finite S] (hS : IsPGroup 2 S) {t u : S} (h : L12Coord S t u)
    (hnc : ¬ ∀ x : S, x * t = t * x) : Nat.card (L12N t) = 16 := by
  obtain ⟨n₀, hn₀N, hn₀ne⟩ := aor_l12_exists_N hS h hnc
  have hn₀R : n₀ ∉ L12R t := fun hr =>
    hn₀ne (Subgroup.mem_centralizer_singleton_iff.mp hr)
  have hle : L12R t ≤ L12N t := Subgroup.le_normalizer
  have hidx : ((L12R t).subgroupOf (L12N t)).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨n₀, hn₀N⟩, fun b => ?_⟩
    by_cases hbR : (b : S) ∈ L12R t
    · right
      refine ⟨Subgroup.mem_subgroupOf.mpr hbR, ?_⟩
      intro hba
      rw [Subgroup.mem_subgroupOf] at hba
      have hba' : (b : S) * n₀ ∈ L12R t := by simpa using hba
      exact hn₀R (by
        have h := (L12R t).mul_mem ((L12R t).inv_mem hbR) hba'
        simpa using h)
    · left
      have hbN : (b : S) ∈ L12N t := b.2
      have hbt : (b : S) * t * (b : S)⁻¹ = u ^ 2 * t := by
        rcases aor_l12_N_conj hS h hnc hbN with h1 | h1
        · exfalso
          apply hbR
          rw [Subgroup.mem_centralizer_singleton_iff]
          calc (b : S) * t = ((b : S) * t * (b : S)⁻¹) * (b : S) := by group
            _ = t * (b : S) := by rw [h1]
        · rw [h1]; exact (aor_l12_u2_comm_t h).symm
      have hat : n₀ * t * n₀⁻¹ = u ^ 2 * t := by
        rcases aor_l12_N_conj hS h hnc hn₀N with h1 | h1
        · exfalso
          apply hn₀R
          rw [Subgroup.mem_centralizer_singleton_iff]
          calc n₀ * t = (n₀ * t * n₀⁻¹) * n₀ := by group
            _ = t * n₀ := by rw [h1]
        · rw [h1]; exact (aor_l12_u2_comm_t h).symm
      refine ⟨?_, fun hb => hbR (Subgroup.mem_subgroupOf.mp hb)⟩
      rw [Subgroup.mem_subgroupOf]
      rw [Subgroup.mem_centralizer_singleton_iff]
      show (b : S) * n₀ * t = t * ((b : S) * n₀)
      have hconj : ((b : S) * n₀) * t * ((b : S) * n₀)⁻¹ = t := by
        calc ((b : S) * n₀) * t * ((b : S) * n₀)⁻¹
            = (b : S) * (n₀ * t * n₀⁻¹) * (b : S)⁻¹ := by group
          _ = (b : S) * (u ^ 2 * t) * (b : S)⁻¹ := by rw [hat]
          _ = ((b : S) * u ^ 2 * (b : S)⁻¹) * ((b : S) * t * (b : S)⁻¹) := by group
          _ = u ^ 2 * (u ^ 2 * t) := by rw [aor_l12_conj_z h hbN, hbt]
          _ = t := by rw [← mul_assoc, ← pow_two, h.z_sq, one_mul]
      calc (b : S) * n₀ * t
          = (((b : S) * n₀) * t * ((b : S) * n₀)⁻¹) * ((b : S) * n₀) := by group
        _ = t * ((b : S) * n₀) := by rw [hconj]
  have hcardR' : Nat.card ((L12R t).subgroupOf (L12N t)) = 8 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]
    exact h.card
  have hmul := Subgroup.index_mul_card (H := (L12R t).subgroupOf (L12N t))
  rw [hidx, hcardR'] at hmul
  exact hmul.symm.trans (by decide)

theorem aor_l12_mem_N {t u : S} (h : L12Coord S t u) (hz : ∀ x : S, x * u ^ 2 = u ^ 2 * x)
    {x : S} (hx : x * t * x⁻¹ * t⁻¹ ∈ Subgroup.zpowers u) : x ∈ L12N t := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx
  have hxtx : x * t * x⁻¹ = u ^ k * t := by
    calc x * t * x⁻¹ = (x * t * x⁻¹ * t⁻¹) * t := by group
      _ = u ^ k * t := by rw [← hk]
  have hyR : x * t * x⁻¹ ∈ L12R t := by
    rw [Subgroup.mem_centralizer_singleton_iff, hxtx]
    have hc : Commute (u ^ k) t := (show Commute u t from h.comm).zpow_left k
    calc (u ^ k * t) * t = u ^ k * (t * t) := by rw [mul_assoc]
      _ = u ^ k := by rw [← pow_two, h.t_sq, mul_one]
      _ = t * (u ^ k * t) := by rw [hc.eq, ← mul_assoc, ← pow_two, h.t_sq, one_mul]
  have hy2 : (x * t * x⁻¹) ^ 2 = 1 := by
    rw [conj_pow, h.t_sq, mul_one, mul_inv_cancel]
  rcases h.R_inv (Subgroup.mem_centralizer_singleton_iff.mp hyR) hy2 with h1 | h1 | h1 | h1
  · exfalso
    have ht1 : t = 1 := by
      have hc := congrArg (fun z => x⁻¹ * z * x) h1
      rwa [show x⁻¹ * (x * t * x⁻¹) * x = t by group,
        show x⁻¹ * (1 : S) * x = 1 by group] at hc
    exact h.t_ne_one ht1
  · exfalso
    have ht2 : t = u ^ 2 := by
      have hc := congrArg (fun z => x⁻¹ * z * x) h1
      rw [show x⁻¹ * (x * t * x⁻¹) * x = t by group] at hc
      rwa [show x⁻¹ * u ^ 2 * x = u ^ 2 by rw [hz x⁻¹]; group] at hc
    exact h.t_ne_z ht2
  · exact (Subgroup.le_normalizer (H := L12R t))
      (Subgroup.mem_centralizer_singleton_iff.mpr (by
        calc x * t = (x * t * x⁻¹) * x := by group
          _ = t * x := by rw [h1]))
  · have hxtx2 : x * t * x⁻¹ = u ^ 2 * t := h1
    refine Subgroup.mem_set_normalizer_iff.mpr (fun r => ⟨?_, ?_⟩)
    · intro hr
      have hr' : r * t = t * r := Subgroup.mem_centralizer_singleton_iff.mp hr
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        ((aor_l12_conj_comm_iff h hz hxtx2).mpr hr')
    · intro hr
      have hr' : (x * r * x⁻¹) * t = t * (x * r * x⁻¹) :=
        Subgroup.mem_centralizer_singleton_iff.mp hr
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        ((aor_l12_conj_comm_iff h hz hxtx2).mp hr')

end CFSG.OddStandard.SmallF3.Omega
