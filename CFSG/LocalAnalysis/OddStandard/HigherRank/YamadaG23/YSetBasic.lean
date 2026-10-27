module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YCtx
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YHyp
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YSylow
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} (s : Setting3 G L)

private theorem centralizer_singleton_le_normalizer_zpowers {G : Type} [Group G] (t : G) :
    Subgroup.centralizer ({t} : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers t : Set G) := by
  rw [Subgroup.zpowers_eq_closure, ← Subgroup.normalizer_singleton]
  exact Subgroup.normalizer_le_normalizer_closure ({t} : Set G)

theorem s3_comm_t_of_mem_T {x : G} (hx : x ∈ s.T) : x * s.t = s.t * x :=
  (Subgroup.mem_centralizer_iff.mp (s.sylow_T.1 hx) s.t (by simp)).symm

theorem s3_comm_t_of_mem_L {x : G} (hx : x ∈ L) : x * s.t = s.t * x :=
  Subgroup.mem_centralizer_iff.mp s.t_mem x hx

theorem s3_t_mem_R : s.t ∈ s.R := by
  let X : Subgroup G := L ⊔ centIn (centralizer ({s.t} : Set G)) L
  have hXc : X ≤ Subgroup.centralizer ({s.t} : Set G) := by
    apply sup_le
    · intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact (Subgroup.mem_centralizer_iff.mp s.t_mem x hx).symm
    · exact inf_le_left
  have hXn : X ≤ Subgroup.normalizer (Subgroup.zpowers s.t : Set G) :=
    hXc.trans (centralizer_singleton_le_normalizer_zpowers s.t)
  have htX : s.t ∈ X := by
    apply Subgroup.mem_sup_right
    exact Subgroup.mem_inf.mpr
      ⟨Subgroup.mem_centralizer_singleton_iff.mpr rfl, s.t_mem⟩
  have hzt : IsPGroup 2 (Subgroup.zpowers s.t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, s.t_order]; norm_num)
  have hRsup : IsPGroup 2 ↥(s.R ⊔ Subgroup.zpowers s.t) :=
    IsPGroup.to_sup_of_normal_right' (H := s.R) (K := Subgroup.zpowers s.t)
      s.sylow_R.2.1 hzt (s.sylow_R.1.trans hXn)
  have heq : s.R = s.R ⊔ Subgroup.zpowers s.t :=
    sylowIn_eq_of_le (V := X) (P := s.R) (Q := s.R ⊔ Subgroup.zpowers s.t)
      s.sylow_R hRsup (sup_le s.sylow_R.1 (Subgroup.zpowers_le.mpr htX)) le_sup_left
  have hz_le : Subgroup.zpowers s.t ≤ s.R := by
    rw [heq]
    exact le_sup_right
  exact hz_le (Subgroup.mem_zpowers s.t)

theorem s3_t_mem_T : s.t ∈ s.T :=
  s.R_le_T (s3_t_mem_R s)

theorem s3_S_le_L : s.fr.S ≤ L :=
  s.sylow_S.1

theorem s3_A_le_S : s.fr.A ≤ s.fr.S := by
  apply Subgroup.closure_mono
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
  tauto

theorem s3_A_le_L : s.fr.A ≤ L :=
  (s3_A_le_S s).trans (s3_S_le_L s)

theorem s3_S_le_T : s.fr.S ≤ s.T :=
  s.S_le_R.trans s.R_le_T

theorem s3_A_le_T : s.fr.A ≤ s.T :=
  (s3_A_le_S s).trans (s3_S_le_T s)

theorem s3_z_mem_A : s.fr.z ∈ s.fr.A := by
  show s.fr.b₁ ^ 2 ∈ s.fr.A
  exact Subgroup.pow_mem s.fr.A (Subgroup.subset_closure (by simp)) 2

theorem s3_z_mem_L : s.fr.z ∈ L :=
  s3_A_le_L s (s3_z_mem_A s)

theorem s3_z_mem_T : s.fr.z ∈ s.T :=
  s3_A_le_T s (s3_z_mem_A s)

theorem s3_comm_t_of_mem_A {a : G} (ha : a ∈ s.fr.A) : a * s.t = s.t * a :=
  s3_comm_t_of_mem_L s (s3_A_le_L s ha)

theorem s3_t_not_mem_L (h31 : s.Fact31) : s.t ∉ L := by
  have h := h31.2.2.1 1
  simpa using h

theorem s3_t_ne_z (h31 : s.Fact31) : s.t ≠ s.fr.z := by
  intro h
  apply s3_t_not_mem_L s h31
  rw [h]
  exact s3_z_mem_L s

theorem s3_z_order (hA : LFactsA s) : orderOf s.fr.z = 2 :=
  hA.z_order

theorem s3_cen_S (hA : LFactsA s) : cen s.fr.S = s.fr.Z :=
  hA.cen_S

private theorem four_mul {G : Type} [Group G] {z t x y : G} (hzz : z * z = 1) (htt : t * t = 1)
    (hzt : t * z = z * t)
    (hx : x = 1 ∨ x = z ∨ x = t ∨ x = z * t)
    (hy : y = 1 ∨ y = z ∨ y = t ∨ y = z * t) :
    x * y = 1 ∨ x * y = z ∨ x * y = t ∨ x * y = z * t := by
  rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl
  · left; rw [one_mul]
  · right; left; rw [one_mul]
  · right; right; left; rw [one_mul]
  · right; right; right; rw [one_mul]
  · right; left; rw [mul_one]
  · left; rw [hzz]
  · right; right; right; rfl
  · right; right; left; rw [← mul_assoc, hzz, one_mul]
  · right; right; left; rw [mul_one]
  · right; right; right; rw [hzt]
  · left; rw [htt]
  · right; left; rw [← mul_assoc, hzt, mul_assoc, htt, mul_one]
  · right; right; right; rw [mul_one]
  · right; right; left; rw [mul_assoc, hzt, ← mul_assoc, hzz, one_mul]
  · right; left; rw [mul_assoc, htt, mul_one]
  · left
    calc (z * t) * (z * t) = z * ((t * z) * t) := by group
      _ = z * ((z * t) * t) := by rw [hzt]
      _ = z * (z * (t * t)) := by group
      _ = 1 := by rw [htt, mul_one, hzz]

theorem s3_mem_zt_iff (hA : LFactsA s) {w : G} :
    w ∈ zt s ↔ w = 1 ∨ w = s.fr.z ∨ w = s.t ∨ w = s.fr.z * s.t := by
  have hzz : s.fr.z * s.fr.z = 1 := by
    rw [← pow_two, ← s3_z_order s hA]
    exact pow_orderOf_eq_one s.fr.z
  have htt : s.t * s.t = 1 := by
    rw [← pow_two, ← s.t_order]
    exact pow_orderOf_eq_one s.t
  have hzt : s.t * s.fr.z = s.fr.z * s.t :=
    (s3_comm_t_of_mem_A s (s3_z_mem_A s)).symm
  constructor
  · intro hw
    rw [zt] at hw
    refine Subgroup.closure_induction
      (p := fun w _ => w = 1 ∨ w = s.fr.z ∨ w = s.t ∨ w = s.fr.z * s.t) ?_ ?_ ?_ ?_ hw
    · intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · right; left; rfl
      · right; right; left; rfl
    · left; rfl
    · intro x y _ _ hx hy
      exact four_mul hzz htt hzt hx hy
    · intro x _ hx
      rcases hx with rfl | rfl | rfl | rfl
      · left; rw [inv_one]
      · right; left; rw [inv_eq_of_mul_eq_one_right hzz]
      · right; right; left; rw [inv_eq_of_mul_eq_one_right htt]
      · right; right; right
        rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hzz, inv_eq_of_mul_eq_one_right htt, hzt]
  · rw [zt]
    rintro (rfl | rfl | rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.mul_mem _
        (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))

theorem s3_zt_le_T : zt s ≤ s.T := by
  rw [zt, Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · exact s3_z_mem_T s
  · exact s3_t_mem_T s

theorem s3_zt_le_cent_A (hA : LFactsA s) : zt s ≤ centralizer (s.fr.A : Set G) := by
  rw [zt, Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · change s.fr.z ∈ Subgroup.centralizer (s.fr.A : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have hcen : cen s.fr.A = s.fr.Z := hA.cen_A
    have hzZ : s.fr.z ∈ s.fr.Z := Subgroup.mem_zpowers s.fr.z
    have hzA : s.fr.z ∈ cen s.fr.A := hcen.symm ▸ hzZ
    exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hzA).2 a ha
  · change s.t ∈ Subgroup.centralizer (s.fr.A : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact s3_comm_t_of_mem_A s ha

theorem s3_zt_le_C0 (hA : LFactsA s) (e : Setting3.Ext s) : zt s ≤ C0 e := by
  rw [C0]
  exact le_inf ((s3_zt_le_T s).trans e.T_le) (s3_zt_le_cent_A s hA)

theorem s3_inf_H_T1 (e : Setting3.Ext s) : e.T₁ ⊓ s.H = s.T :=
  (sylowIn_eq_of_le (V := s.H) (P := s.T) (Q := e.T₁ ⊓ s.H)
    s.sylow_T e.sylow.2.1.to_inf_left inf_le_right (le_inf e.T_le s.sylow_T.1)).symm

theorem s3_conj_z (hA : LFactsA s) (e : Setting3.Ext s) (h32 : e.Fact32) {x : G}
    (hx : x ∈ e.T₁) : x * s.fr.z * x⁻¹ = s.fr.z := by
  have hSleT : s.fr.S ≤ e.T₁ := h32.2.1.1
  have hnormS : (s.fr.S.subgroupOf e.T₁).Normal := h32.2.1.2
  have hzS : s.fr.z ∈ s.fr.S := s3_A_le_S s (s3_z_mem_A s)
  have hzT : s.fr.z ∈ e.T₁ := hSleT hzS
  have hconjS : x * s.fr.z * x⁻¹ ∈ s.fr.S := by
    have h := hnormS.conj_mem ⟨s.fr.z, hzT⟩ (Subgroup.mem_subgroupOf.mpr hzS) ⟨x, hx⟩
    exact Subgroup.mem_subgroupOf.mp h
  have hconj_invS : ∀ u ∈ s.fr.S, x⁻¹ * u * x ∈ s.fr.S := by
    intro u hu
    have h := hnormS.conj_mem ⟨u, hSleT hu⟩ (Subgroup.mem_subgroupOf.mpr hu)
      ⟨x⁻¹, Subgroup.inv_mem _ hx⟩
    simpa using Subgroup.mem_subgroupOf.mp h
  have hzcent : s.fr.z ∈ Subgroup.centralizer (s.fr.S : Set G) := by
    have hzcen : s.fr.z ∈ cen s.fr.S := (s3_cen_S s hA).symm ▸ Subgroup.mem_zpowers s.fr.z
    exact (Subgroup.mem_inf.mp hzcen).2
  have hconj_cen : x * s.fr.z * x⁻¹ ∈ Subgroup.centralizer (s.fr.S : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have hzu : (x⁻¹ * u * x) * s.fr.z = s.fr.z * (x⁻¹ * u * x) :=
      Subgroup.mem_centralizer_iff.mp hzcent (x⁻¹ * u * x) (hconj_invS u hu)
    calc u * (x * s.fr.z * x⁻¹)
        = x * ((x⁻¹ * u * x) * s.fr.z) * x⁻¹ := by group
      _ = x * (s.fr.z * (x⁻¹ * u * x)) * x⁻¹ := by rw [hzu]
      _ = (x * s.fr.z * x⁻¹) * u := by group
  have hyZ : x * s.fr.z * x⁻¹ ∈ s.fr.Z := by
    have hmem : x * s.fr.z * x⁻¹ ∈ cen s.fr.S := Subgroup.mem_inf.mpr ⟨hconjS, hconj_cen⟩
    rwa [s3_cen_S s hA] at hmem
  rw [SFrame.Z] at hyZ
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hyZ
  have hkmod : s.fr.z ^ k = 1 ∨ s.fr.z ^ k = s.fr.z := by
    have h := zpow_mod_orderOf s.fr.z k
    rw [s3_z_order s hA] at h
    rcases Int.emod_two_eq_zero_or_one k with h2 | h2
    · left
      rw [← h, show k % ((2:ℕ):ℤ) = 0 from by simpa using h2]
      simp
    · right
      rw [← h, show k % ((2:ℕ):ℤ) = 1 from by simpa using h2]
      simp
  rcases hkmod with h1 | hz
  · exfalso
    have hz1 : s.fr.z = 1 := by
      calc s.fr.z = x⁻¹ * (x * s.fr.z * x⁻¹) * x := by group
        _ = 1 := by rw [← hk, h1]; group
    have hord := s3_z_order s hA
    rw [hz1, orderOf_one] at hord
    norm_num at hord
  · rw [← hk]; exact hz

theorem s3_conj_A (e : Setting3.Ext s) (h32 : e.Fact32) {x : G} (hx : x ∈ e.T₁) {a : G}
    (ha : a ∈ s.fr.A) : x * a * x⁻¹ ∈ s.fr.A := by
  have h := h32.1.2.conj_mem ⟨a, h32.1.1 ha⟩ (Subgroup.mem_subgroupOf.mpr ha) ⟨x, hx⟩
  exact Subgroup.mem_subgroupOf.mp h

end CFSG.OddStandard.HigherRank.YamadaG23
