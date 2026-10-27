module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7B0Defs
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7BFa
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y56One
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y56Two

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private lemma zpow_eq_one_or_self {v : G} (hv : v * v = 1) (m : ℤ) :
    v ^ m = 1 ∨ v ^ m = v := by
  have hv2 : v ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hv
  obtain ⟨j, hj | hj⟩ := Int.even_or_odd' m
  · left; rw [hj, zpow_mul, hv2, one_zpow]
  · right; rw [hj, zpow_add, zpow_mul, hv2, one_zpow, one_mul, zpow_one]

private lemma eq_one_or_eq_of_mem_zpowers {v g : G} (hv : v * v = 1)
    (hg : g ∈ zpowers v) : g = 1 ∨ g = v := by
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
  exact zpow_eq_one_or_self hv i

private lemma y7b_E_le_A (c : Ctx7 G L) (hb : B5Std c) : c.s.fr.E ≤ c.s.fr.A := by
  have h1 : c.s.fr.E ≤ c.s.fr.E ⊔ c.s.fr.F := le_sup_left
  have h2 : c.s.fr.E ⊔ c.s.fr.F ≤ c.s.fr.A ⊓ c.s.fr.B :=
    le_of_eq (y7b_EF_eq hb.hH)
  exact h1.trans (h2.trans inf_le_left)

private lemma y7b_z_sq (c : Ctx7 G L) (hb : B5Std c) :
    c.s.fr.z * c.s.fr.z = 1 := by
  rw [← pow_two]
  exact y56_E_sq hb.hH c.s.fr.z (y56_z_mem_E hb.hH)

private lemma y7b_d_sq (c : Ctx7 G L) : c.d * c.d = 1 := by
  rw [← pow_two]
  exact y5_d_sq c.toCtx5

private lemma y7b_t_sq (c : Ctx7 G L) : c.s.t * c.s.t = 1 := by
  rw [← pow_two, ← c.s.t_order]
  exact pow_orderOf_eq_one c.s.t

private lemma y7b_d_cent_E (c : Ctx7 G L) (hb : B5Std c) :
    ∀ e ∈ c.s.fr.E, e * c.d = c.d * e := by
  intro e he
  have h := y5_d_cent_A c.toCtx5 e (y7b_E_le_A c hb he)
  have h' : c.d * e = e * c.d := by
    calc c.d * e = (c.d * e * c.d⁻¹) * c.d := by group
      _ = e * c.d := by rw [h]
  exact h'.symm

private lemma y7b_z_d_comm (c : Ctx7 G L) (hb : B5Std c) :
    c.s.fr.z * c.d = c.d * c.s.fr.z := by
  have h := y5_d_cent_A c.toCtx5 c.s.fr.z (y7b_E_le_A c hb (y56_z_mem_E hb.hH))
  have h' : c.d * c.s.fr.z = c.s.fr.z * c.d := by
    calc c.d * c.s.fr.z = (c.d * c.s.fr.z * c.d⁻¹) * c.d := by group
      _ = c.s.fr.z * c.d := by rw [h]
  exact h'.symm

private lemma y7b_z_t_comm (c : Ctx7 G L) (hb : B5Std c) :
    c.s.fr.z * c.s.t = c.s.t * c.s.fr.z :=
  y56_t_comm_E c.s c.s.fr.z (y56_z_mem_E hb.hH)

private lemma y7b_t_d_conj (c : Ctx7 G L) (hb : B5Std c) :
    c.s.t * c.d * c.s.t⁻¹ = c.s.fr.z * c.d := by
  have hdsq : c.d * c.d = 1 := y7b_d_sq c
  have ht_sq : c.s.t * c.s.t = 1 := y7b_t_sq c
  have hzt : c.s.fr.z * c.s.t = c.s.t * c.s.fr.z := y7b_z_t_comm c hb
  have hd_inv : c.d⁻¹ = c.d := inv_eq_of_mul_eq_one_right hdsq
  have ht_inv : c.s.t⁻¹ = c.s.t := inv_eq_of_mul_eq_one_right ht_sq
  have hdt_eq : c.d * c.s.t * c.d = c.s.fr.z * c.s.t := by
    rw [← y5_dtd hb.hH, hd_inv]
  have h1 : c.s.t * c.d * c.s.t * c.d = c.s.fr.z := by
    calc c.s.t * c.d * c.s.t * c.d
        = c.s.t * (c.d * c.s.t * c.d) := by group
      _ = c.s.t * (c.s.fr.z * c.s.t) := by rw [hdt_eq]
      _ = c.s.fr.z := by rw [hzt, ← mul_assoc, ht_sq, one_mul]
  rw [ht_inv]
  calc c.s.t * c.d * c.s.t
      = c.s.t * c.d * c.s.t * (c.d * c.d) := by rw [hdsq, mul_one]
    _ = (c.s.t * c.d * c.s.t * c.d) * c.d := by group
    _ = c.s.fr.z * c.d := by rw [h1]

private lemma y7b_V1_eq_four (c : Ctx7 G L) (hb : B5Std c) :
    (V1 c.e : Set G) = ({1, c.s.fr.z, c.d, c.s.fr.z * c.d} : Set G) := by
  have hzsq : c.s.fr.z * c.s.fr.z = 1 := y7b_z_sq c hb
  have hdsq : c.d * c.d = 1 := y7b_d_sq c
  have hzd : c.s.fr.z * c.d = c.d * c.s.fr.z := y7b_z_d_comm c hb
  rw [c.hV]
  have hgen : ({c.s.fr.z, c.d} : Set G) = {c.s.fr.z} ∪ {c.d} := by
    ext x; simp [or_comm]
  have hnorm : ∀ x ∈ zpowers c.s.fr.z, ∀ y ∈ zpowers c.d,
      x * y * x⁻¹ ∈ zpowers c.d := by
    intro x hx y hy
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hcomm : (c.s.fr.z ^ m) * (c.d ^ n) = (c.d ^ n) * (c.s.fr.z ^ m) :=
      (Commute.zpow_zpow hzd m n).eq
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
    exact Subgroup.mem_zpowers_iff.mpr ⟨n, rfl⟩
  apply le_antisymm
  · intro x hx
    rw [hgen, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure,
      ← Subgroup.zpowers_eq_closure] at hx
    obtain ⟨a, ha, b, hb', rfl⟩ := mem_sup_of_normalizes hnorm x hx
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb'
    have hzm := zpow_eq_one_or_self hzsq m
    have hdn := zpow_eq_one_or_self hdsq n
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases hzm with hzm | hzm <;> rcases hdn with hdn | hdn <;> rw [hzm, hdn] <;> simp
  · intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact (closure {c.s.fr.z, c.d}).one_mem
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))

theorem y7b_card_V1 (c : Ctx7 G L) (hb : B5Std c) : Nat.card ↥(V1 c.e) = 4 := by
  have hzsq : c.s.fr.z * c.s.fr.z = 1 := y7b_z_sq c hb
  have hdsq : c.d * c.d = 1 := y7b_d_sq c
  have hset := y7b_V1_eq_four c hb
  have hz_ne_one : c.s.fr.z ≠ 1 := y54_z_ne_one hb.hH
  have hz_zt : c.s.fr.z ∈ zt c.s := Subgroup.subset_closure (by simp)
  have hd_ne_one : c.d ≠ 1 := by
    intro h
    exact c.d_not_mem (by rw [h]; exact (zt c.s).one_mem)
  have hd_ne_z : c.d ≠ c.s.fr.z := by
    intro h
    exact c.d_not_mem (by rw [h]; exact hz_zt)
  have h1zd : (1 : G) ≠ c.s.fr.z * c.d := by
    intro h
    exact hd_ne_z (by
      calc c.d = c.s.fr.z⁻¹ * (c.s.fr.z * c.d) := by group
        _ = c.s.fr.z := by rw [← h, mul_one, inv_eq_of_mul_eq_one_right hzsq])
  have hzzd : c.s.fr.z ≠ c.s.fr.z * c.d := by
    intro h
    have h2 : c.s.fr.z * 1 = c.s.fr.z * c.d := by simpa [mul_one] using h
    exact hd_ne_one (mul_left_cancel h2).symm
  have hdzd : c.d ≠ c.s.fr.z * c.d := by
    intro h
    have h2 : c.d * c.d = (c.s.fr.z * c.d) * c.d := congrArg (fun x => x * c.d) h
    rw [mul_assoc, hdsq, mul_one] at h2
    exact hz_ne_one h2.symm
  have h4card : ({1, c.s.fr.z, c.d, c.s.fr.z * c.d} : Set G).ncard = 4 := by
    have h1 : (1 : G) ∉ ({c.s.fr.z, c.d, c.s.fr.z * c.d} : Set G) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rintro (h | h | h)
      · exact hz_ne_one h.symm
      · exact hd_ne_one h.symm
      · exact h1zd h
    have h2 : c.s.fr.z ∉ ({c.d, c.s.fr.z * c.d} : Set G) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rintro (h | h)
      · exact hd_ne_z h.symm
      · exact hzzd h
    have h3 : c.d ∉ ({c.s.fr.z * c.d} : Set G) := by
      simpa using hdzd
    rw [Set.ncard_insert_of_notMem h1, Set.ncard_insert_of_notMem h2,
      Set.ncard_insert_of_notMem h3, Set.ncard_singleton]
  change Nat.card (V1 c.e : Set G) = 4
  rw [Nat.card_coe_set_eq, hset, h4card]

theorem y7b_V1_le_M4 (c : Ctx7 G L) (hb : B5Std c) : V1 c.e ≤ M4 c.e := by
  have hpair : ({c.s.fr.z, c.d} : Set G).Pairwise Commute := by
    intro x hx y hy hxy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact absurd rfl hxy
    · exact y7b_z_d_comm c hb
    · exact (y7b_z_d_comm c hb).symm
    · exact absurd rfl hxy
  haveI : IsMulCommutative ↥(closure ({c.s.fr.z, c.d} : Set G)) :=
    Subgroup.isMulCommutative_closure hpair
  have hV1C : V1 c.e ≤ Subgroup.centralizer (V1 c.e : Set G) := by
    rw [c.hV]
    exact Subgroup.le_centralizer_iff_isMulCommutative.mpr
      (inferInstance : IsMulCommutative ↥(closure ({c.s.fr.z, c.d} : Set G)))
  have hV1C4 : V1 c.e ≤ C4 c.s := by
    unfold V1
    exact inf_le_left.trans (y56_C0_le_C4 c.toCtx5 hb.hH)
  unfold M4 centIn
  exact le_inf hV1C4 hV1C

theorem y7b_V1_le_V2 (c : Ctx7 G L) (hb : B5Std c) : V1 c.e ≤ V2 c.e := by
  unfold V2
  exact le_inf (by unfold V1; exact inf_le_right) (y7b_V1_le_M4 c hb)

theorem y7b_E_le_M4 (c : Ctx7 G L) (hb : B5Std c) : c.s.fr.E ≤ M4 c.e := by
  have hEC4 : c.s.fr.E ≤ C4 c.s := by
    calc c.s.fr.E ≤ c.s.fr.E ⊔ zpowers c.s.t := le_sup_left
      _ = c.s.H ⊓ C4 c.s := (y56_H_inf_C4 c.toCtx5 hb.hH).symm
      _ ≤ C4 c.s := inf_le_right
  have hEcent : c.s.fr.E ≤ Subgroup.centralizer (V1 c.e : Set G) := by
    have hgen : ({c.s.fr.z, c.d} : Set G) ⊆
        Subgroup.centralizer (c.s.fr.E : Set G) := by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact Subgroup.mem_centralizer_iff.mpr
          (fun f hf => y56_E_comm hb.hH f hf c.s.fr.z (y56_z_mem_E hb.hH))
      · exact Subgroup.mem_centralizer_iff.mpr (fun f hf => y7b_d_cent_E c hb f hf)
    rw [c.hV]
    exact Subgroup.le_centralizer_iff.mpr
      ((Subgroup.closure_le (Subgroup.centralizer (c.s.fr.E : Set G))).mpr hgen)
  unfold M4 centIn
  exact le_inf hEC4 hEcent

theorem y7b_H_inf_M4 (c : Ctx7 G L) (hb : B5Std c) :
    c.s.H ⊓ M4 c.e = c.s.fr.E := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxH, hxM4⟩ := Subgroup.mem_inf.mp hx
    unfold M4 centIn at hxM4
    obtain ⟨hxC4, hxcent⟩ := Subgroup.mem_inf.mp hxM4
    have hdV1 : c.d ∈ V1 c.e := by
      rw [c.hV]; exact Subgroup.subset_closure (by simp)
    have hxsup : x ∈ c.s.fr.E ⊔ zpowers c.s.t := by
      rw [← y56_H_inf_C4 c.toCtx5 hb.hH]
      exact Subgroup.mem_inf.mpr ⟨hxH, hxC4⟩
    have hnorm : ∀ y ∈ c.s.fr.E, ∀ u ∈ zpowers c.s.t,
        y * u * y⁻¹ ∈ zpowers c.s.t := by
      intro y hy u hu
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
      have hy_conj : y * c.s.t * y⁻¹ = c.s.t := by
        rw [y56_t_comm_E c.s y hy]; group
      rw [← conj_zpow, hy_conj]
      exact Subgroup.mem_zpowers_iff.mpr ⟨i, rfl⟩
    obtain ⟨e, he, u, hu, hxeu⟩ := mem_sup_of_normalizes hnorm x hxsup
    rcases eq_one_or_eq_of_mem_zpowers (y7b_t_sq c) hu with hu | hu
    · rw [hu, mul_one] at hxeu
      rw [hxeu]; exact he
    · exfalso
      rw [hu] at hxeu
      have hxd : c.d * x = x * c.d :=
        Subgroup.mem_centralizer_iff.mp hxcent c.d hdV1
      have hed : (e : G) * c.d = c.d * (e : G) := y7b_d_cent_E c hb e he
      have h1 : (e : G) * (c.d * c.s.t) = (e : G) * (c.s.t * c.d) := by
        calc (e : G) * (c.d * c.s.t)
            = c.d * ((e : G) * c.s.t) := by rw [← mul_assoc, hed, mul_assoc]
          _ = c.d * x := by rw [← hxeu]
          _ = x * c.d := hxd
          _ = ((e : G) * c.s.t) * c.d := by rw [hxeu]
          _ = (e : G) * (c.s.t * c.d) := by rw [mul_assoc]
      have htdeq : c.s.t * c.d = c.d * c.s.t := (mul_left_cancel h1).symm
      have hdsq : c.d * c.d = 1 := y7b_d_sq c
      have hd_inv : c.d⁻¹ = c.d := inv_eq_of_mul_eq_one_right hdsq
      have hz1 : c.s.fr.z = 1 := by
        have hzt' : c.s.fr.z * c.s.t = c.s.t := by
          rw [← y5_dtd hb.hH, hd_inv]
          calc c.d * c.s.t * c.d = (c.s.t * c.d) * c.d := by rw [htdeq]
            _ = c.s.t * (c.d * c.d) := by rw [mul_assoc]
            _ = c.s.t := by rw [hdsq, mul_one]
        have h2 : c.s.fr.z * c.s.t = 1 * c.s.t := by rw [hzt', one_mul]
        exact mul_right_cancel h2
      exact y54_z_ne_one hb.hH hz1
  · intro x hx
    refine Subgroup.mem_inf.mpr ⟨?_, y7b_E_le_M4 c hb hx⟩
    unfold Setting3.H
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact (y56_t_comm_E c.s x hx).symm

theorem y7b_comm_V1_t (c : Ctx7 G L) (hb : B5Std c) :
    ∀ v ∈ V1 c.e, c.s.t * v * c.s.t⁻¹ ∈ V1 c.e ∧ ⁅v, c.s.t⁆ ∈ c.s.fr.Z := by
  have hzsq : c.s.fr.z * c.s.fr.z = 1 := y7b_z_sq c hb
  have hdsq : c.d * c.d = 1 := y7b_d_sq c
  have ht_sq : c.s.t * c.s.t = 1 := y7b_t_sq c
  have ht_inv : c.s.t⁻¹ = c.s.t := inv_eq_of_mul_eq_one_right ht_sq
  have hzt : c.s.fr.z * c.s.t = c.s.t * c.s.fr.z := y7b_z_t_comm c hb
  have hdt : c.s.t * c.d * c.s.t⁻¹ = c.s.fr.z * c.d := y7b_t_d_conj c hb
  have hcomm_one : ⁅(1 : G), c.s.t⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr (by group)
  have hcomm_zt : ⁅c.s.fr.z, c.s.t⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr hzt
  have hcomm_dt : ⁅c.d, c.s.t⁆ = c.s.fr.z := by
    rw [commutatorElement_def]
    rw [y5_dtd hb.hH]
    rw [mul_assoc, ht_inv, ht_sq, mul_one]
  have hcomm_zd_t : ⁅c.s.fr.z * c.d, c.s.t⁆ = c.s.fr.z := by
    rw [commutatorElement_mul_left_eq_conj_mul, hcomm_dt, hcomm_zt, mul_one]
    group
  have htz : c.s.t * c.s.fr.z * c.s.t⁻¹ = c.s.fr.z := by
    rw [hzt.symm]; group
  have htzd : c.s.t * (c.s.fr.z * c.d) * c.s.t⁻¹ = c.d := by
    calc c.s.t * (c.s.fr.z * c.d) * c.s.t⁻¹
        = (c.s.t * c.s.fr.z * c.s.t⁻¹) * (c.s.t * c.d * c.s.t⁻¹) := by group
      _ = c.s.fr.z * (c.s.fr.z * c.d) := by rw [htz, hdt]
      _ = c.d := by rw [← mul_assoc, hzsq, one_mul]
  have hzV1 : c.s.fr.z ∈ V1 c.e := by
    rw [c.hV]; exact Subgroup.subset_closure (by simp)
  have hdV1 : c.d ∈ V1 c.e := by
    rw [c.hV]; exact Subgroup.subset_closure (by simp)
  have hzdV1 : c.s.fr.z * c.d ∈ V1 c.e := (V1 c.e).mul_mem hzV1 hdV1
  have hset := y7b_V1_eq_four c hb
  intro v hv
  have hv' : v ∈ ({1, c.s.fr.z, c.d, c.s.fr.z * c.d} : Set G) := by
    rw [← hset]; exact hv
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv'
  rcases hv' with rfl | rfl | rfl | rfl
  · exact ⟨by simpa using (V1 c.e).one_mem,
      by rw [hcomm_one]; exact (c.s.fr.Z).one_mem⟩
  · exact ⟨by rw [htz]; exact hzV1,
      by rw [hcomm_zt]; exact (c.s.fr.Z).one_mem⟩
  · exact ⟨by rw [hdt]; exact hzdV1,
      by rw [hcomm_dt]; exact Subgroup.mem_zpowers c.s.fr.z⟩
  · exact ⟨by rw [htzd]; exact hdV1,
      by rw [hcomm_zd_t]; exact Subgroup.mem_zpowers c.s.fr.z⟩

end CFSG.OddStandard.HigherRank.YamadaG23
