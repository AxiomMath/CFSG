module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YSetBasic
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YIdx2

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private theorem mem_zpowers_of_orderOf_eq_two {v x : G} (hv : orderOf v = 2) :
    x ∈ Subgroup.zpowers v ↔ x = 1 ∨ x = v := by
  have h2 : v ^ (2 : ℤ) = 1 := by
    have := pow_orderOf_eq_one v
    rw [hv] at this
    rw [zpow_ofNat, this]
  constructor
  · rintro ⟨k, rfl⟩
    rcases Int.emod_two_eq_zero_or_one k with hk | hk
    · left
      change v ^ k = 1
      rw [← Int.ediv_mul_add_emod k 2, hk, add_zero, mul_comm, zpow_mul, h2, one_zpow]
    · right
      change v ^ k = v
      rw [← Int.ediv_mul_add_emod k 2, hk, zpow_add, mul_comm, zpow_mul, h2, one_zpow,
        one_mul, zpow_one]
  · rintro (h | h) <;> rw [h]
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers v

theorem intro5_core {s : Setting3 G L} (e : Setting3.Ext s) (hLF : LFactsA s) (hdef : e.FactDef)
    (hf32 : e.Fact32) (hC : centIn s.T s.fr.A = zt s) (hnb : ¬ BranchA e) :
    ∃ d : G, d ∈ C0 e ∧ orderOf d = 2 ∧ d ∉ zt s ∧ d ∉ s.T ∧ (d * s.t) ^ 4 = 1 ∧
      (d * s.t) ^ 2 = s.fr.z ∧ C0 e = zt s ⊔ zpowers d := by
  have hz2 : s.fr.z ^ 2 = 1 := by
    have := pow_orderOf_eq_one s.fr.z
    rwa [s3_z_order s hLF] at this
  have hz1 : s.fr.z ≠ 1 :=
    ((orderOf_eq_prime_iff (p := 2) (x := s.fr.z)).mp (s3_z_order s hLF)).2
  have ht2 : s.t ^ 2 = 1 := by
    have := pow_orderOf_eq_one s.t
    rwa [s.t_order] at this
  have hzz : s.fr.z * s.fr.z = 1 := by rw [← pow_two]; exact hz2
  have htt : s.t * s.t = 1 := by rw [← pow_two]; exact ht2
  have hzt_comm : s.fr.z * s.t = s.t * s.fr.z := s3_comm_t_of_mem_L s (s3_z_mem_L s)
  have h1Q : (1 : G) ∈ zt s := (zt s).one_mem
  have htQ : s.t ∈ zt s := Subgroup.subset_closure (by simp)
  have htC0 : s.t ∈ C0 e := s3_zt_le_C0 s hLF e htQ
  have hnotle : ¬ (C0 e : Set G) ⊆ (zt s : Set G) := by
    intro h
    exact hnb (le_antisymm (fun x hx => h hx) (s3_zt_le_C0 s hLF e))
  obtain ⟨x, hxC0, hxQ⟩ := Set.not_subset.mp hnotle
  have hxC0' := hxC0
  simp only [C0, centIn] at hxC0'
  have hxT1 : x ∈ e.T₁ := (Subgroup.mem_inf.mp hxC0').1
  have hxcentA : x ∈ centralizer (s.fr.A : Set G) := (Subgroup.mem_inf.mp hxC0').2
  have hxT : x ∉ s.T := by
    intro hx
    apply hxQ
    rw [← hC]
    exact Subgroup.mem_inf.mpr ⟨hx, hxcentA⟩
  have hmem : x * s.t * x⁻¹ ∈ conjClass e.T₁ s.t := ⟨x, hxT1, rfl⟩
  rw [hdef.2.2] at hmem
  obtain ⟨y, hyCen, hy_eq⟩ := hmem
  have hyZp : y ∈ Subgroup.zpowers s.fr.z := by
    have hyZ : y ∈ s.fr.Z := by
      rw [← s3_cen_S s hLF]
      exact hyCen
    simpa [SFrame.Z] using hyZ
  have hxt : x * s.t * x⁻¹ = s.fr.z * s.t := by
    rcases (mem_zpowers_of_orderOf_eq_two (s3_z_order s hLF)).mp hyZp with hy1 | hyz
    · exfalso
      rw [hy1, one_mul] at hy_eq
      have hcomm : s.t * x = x * s.t := by
        have h := congrArg (fun w => w * x) hy_eq
        have h' : x * s.t = s.t * x := by simpa [mul_assoc] using h
        exact h'.symm
      have hxcentt : x ∈ centralizer ({s.t} : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        subst hh
        exact hcomm
      have hxH : x ∈ s.H := by simpa [Setting3.H] using hxcentt
      have hxIn : x ∈ e.T₁ ⊓ s.H := Subgroup.mem_inf.mpr ⟨hxT1, hxH⟩
      rw [s3_inf_H_T1 s e] at hxIn
      exact hxT hxIn
    · rw [hyz] at hy_eq
      exact hy_eq
  have hxz : x * s.fr.z * x⁻¹ = s.fr.z := s3_conj_z s hLF e hf32 hxT1
  have hxt' : x * s.t = s.fr.z * s.t * x := by
    have h := congrArg (fun w => w * x) hxt
    simpa [mul_assoc] using h
  have hx2T : x ^ 2 ∈ s.T := sq_mem_of_relIndex_two e.T_le hdef.2.1 hxT1
  have hx2C0 : x ^ 2 ∈ C0 e := pow_mem hxC0 2
  have hx2centA : x ^ 2 ∈ centralizer (s.fr.A : Set G) := pow_mem hxcentA 2
  have hx2zt : x ^ 2 ∈ zt s := by
    rw [← hC]
    exact Subgroup.mem_inf.mpr ⟨hx2T, hx2centA⟩
  have hx2 : x ^ 2 = 1 ∨ x ^ 2 = s.fr.z := by
    rcases (s3_mem_zt_iff s hLF).mp hx2zt with h | h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exfalso
      have hconj : x * s.t * x⁻¹ = s.t := by
        rw [← h]
        group
      have hzt_eq : s.fr.z * s.t = s.t := hxt.symm.trans hconj
      have hz_eq_one : s.fr.z = 1 := by
        calc s.fr.z = (s.fr.z * s.t) * s.t⁻¹ := by group
          _ = s.t * s.t⁻¹ := by rw [hzt_eq]
          _ = 1 := by group
      exact hz1 hz_eq_one
    · exfalso
      have hconj : x * (s.fr.z * s.t) * x⁻¹ = s.fr.z * (s.fr.z * s.t) := by
        calc x * (s.fr.z * s.t) * x⁻¹
            = (x * s.fr.z * x⁻¹) * (x * s.t * x⁻¹) := by group
          _ = s.fr.z * (s.fr.z * s.t) := by rw [hxz, hxt]
      have hconj_t : s.fr.z * (s.fr.z * s.t) = s.t := by
        rw [← mul_assoc, hzz, one_mul]
      have hself : x * (s.fr.z * s.t) * x⁻¹ = s.fr.z * s.t := by
        rw [← h]
        group
      have hzt_eq : s.fr.z * s.t = s.t := hself.symm.trans (hconj.trans hconj_t)
      have hz_eq_one : s.fr.z = 1 := by
        calc s.fr.z = (s.fr.z * s.t) * s.t⁻¹ := by group
          _ = s.t * s.t⁻¹ := by rw [hzt_eq]
          _ = 1 := by group
      exact hz1 hz_eq_one
  have hinf : C0 e ⊓ s.T = zt s := by
    apply le_antisymm
    · intro y hy
      have hyT : y ∈ s.T := (Subgroup.mem_inf.mp hy).2
      have hyC0 : y ∈ C0 e := (Subgroup.mem_inf.mp hy).1
      have hyC0' := hyC0
      simp only [C0, centIn] at hyC0'
      have hycent : y ∈ centralizer (s.fr.A : Set G) := (Subgroup.mem_inf.mp hyC0').2
      rw [← hC]
      exact Subgroup.mem_inf.mpr ⟨hyT, hycent⟩
    · intro y hy
      exact Subgroup.mem_inf.mpr ⟨s3_zt_le_C0 s hLF e hy, s3_zt_le_T s hy⟩
  have hXK : C0 e ≤ e.T₁ := by
    intro y hy
    have hy' := hy
    simp only [C0, centIn] at hy'
    exact (Subgroup.mem_inf.mp hy').1
  rcases hx2 with hx2one | hx2z
  · have hxt2 : (x * s.t) ^ 2 = s.fr.z := by
      calc (x * s.t) ^ 2 = x * s.t * x * s.t := by rw [pow_two]; group
        _ = (s.fr.z * s.t * x) * x * s.t := by rw [hxt']
        _ = s.fr.z * s.t * (x * x) * s.t := by group
        _ = s.fr.z * s.t * 1 * s.t := by rw [← pow_two, hx2one]
        _ = s.fr.z * (s.t * s.t) := by group
        _ = s.fr.z := by rw [htt, mul_one]
    have hxt4 : (x * s.t) ^ 4 = 1 := by
      calc (x * s.t) ^ 4 = ((x * s.t) ^ 2) ^ 2 := by
            rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul]
        _ = s.fr.z ^ 2 := by rw [hxt2]
        _ = 1 := hz2
    refine ⟨x, hxC0, orderOf_eq_prime hx2one (fun h => hxQ (by rw [h]; exact h1Q)), hxQ, hxT,
      hxt4, hxt2, ?_⟩
    calc C0 e = (C0 e ⊓ s.T) ⊔ zpowers x :=
          eq_sup_zpowers_of_relIndex_two (H := s.T) (K := e.T₁) (X := C0 e) (d := x)
            hXK hdef.2.1 hxC0 hxT
      _ = zt s ⊔ zpowers x := by rw [hinf]
  · have hdC0 : x * s.t ∈ C0 e := Subgroup.mul_mem _ hxC0 htC0
    have hdQ : x * s.t ∉ zt s := by
      intro h
      apply hxQ
      have htinv : s.t⁻¹ ∈ zt s := Subgroup.inv_mem _ htQ
      have hmem := Subgroup.mul_mem _ h htinv
      have hx_eq : (x * s.t) * s.t⁻¹ = x := by group
      rwa [hx_eq] at hmem
    have hdT : x * s.t ∉ s.T := by
      intro h
      apply hxT
      have htinv : s.t⁻¹ ∈ s.T := Subgroup.inv_mem _ (s3_t_mem_T s)
      have hmem := Subgroup.mul_mem _ h htinv
      have hx_eq : (x * s.t) * s.t⁻¹ = x := by group
      rwa [hx_eq] at hmem
    have hd2 : (x * s.t) ^ 2 = 1 := by
      calc (x * s.t) ^ 2 = x * s.t * x * s.t := by rw [pow_two]; group
        _ = (s.fr.z * s.t * x) * x * s.t := by rw [hxt']
        _ = s.fr.z * s.t * (x * x) * s.t := by group
        _ = s.fr.z * s.t * s.fr.z * s.t := by rw [← pow_two, hx2z]
        _ = s.fr.z * (s.t * s.fr.z) * s.t := by group
        _ = s.fr.z * (s.fr.z * s.t) * s.t := by rw [hzt_comm]
        _ = (s.fr.z * s.fr.z) * (s.t * s.t) := by group
        _ = 1 := by rw [hzz, htt, mul_one]
    have hdtt : (x * s.t) * s.t = x := by rw [mul_assoc, htt, mul_one]
    have hdt2 : ((x * s.t) * s.t) ^ 2 = s.fr.z := by rw [hdtt, hx2z]
    have hdt4 : ((x * s.t) * s.t) ^ 4 = 1 := by
      rw [hdtt]
      calc x ^ 4 = (x ^ 2) ^ 2 := by
            rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul]
        _ = s.fr.z ^ 2 := by rw [hx2z]
        _ = 1 := hz2
    refine ⟨x * s.t, hdC0, orderOf_eq_prime hd2 (fun h => hdQ (by rw [h]; exact h1Q)), hdQ,
      hdT, hdt4, hdt2, ?_⟩
    calc C0 e = (C0 e ⊓ s.T) ⊔ zpowers (x * s.t) :=
          eq_sup_zpowers_of_relIndex_two (H := s.T) (K := e.T₁) (X := C0 e) (d := x * s.t)
            hXK hdef.2.1 hdC0 hdT
      _ = zt s ⊔ zpowers (x * s.t) := by rw [hinf]

end CFSG.OddStandard.HigherRank.YamadaG23
