module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecTenSwapQ

public section

namespace CFSG.OddStandard.AltStdSec.SwapPattern

open Subgroup Equiv Equiv.Perm

variable {G : Type} [Group G] {z : G} {ι : Perm (Fin 10) →* G}

private theorem z_comm_iota (hC : CentData z ι) (σ : Perm (Fin 10)) : Commute z (ι σ) :=
  hC.comm σ

private theorem z_pow_mul_self (hC : CentData z ι) (n : ℕ) : z ^ n * z ^ n = 1 := by
  rw [← pow_add, show n + n = 2 * n by omega, pow_mul, pow_two, hC.mul_self, one_pow]

private theorem iota_comm_z_pow (hC : CentData z ι) (σ : Perm (Fin 10)) (n : ℕ) :
    ι σ * z ^ n = z ^ n * ι σ :=
  (z_comm_iota hC σ).symm.pow_right n

@[expose] def Tgrp (z : G) (ι : Perm (Fin 10) →* G) (Q : Subgroup (Perm (Fin 10))) : Subgroup G :=
  zpowers z ⊔ Q.map ι

theorem map_le_Tgrp (Q : Subgroup (Perm (Fin 10))) : Q.map ι ≤ Tgrp z ι Q := by
  exact le_sup_right

theorem z_mem_Tgrp (Q : Subgroup (Perm (Fin 10))) : z ∈ Tgrp z ι Q := by
  exact Subgroup.mem_sup_left (Subgroup.mem_zpowers z)

theorem mem_Tgrp_iff (hC : CentData z ι) {Q : Subgroup (Perm (Fin 10))} {g : G} :
    g ∈ Tgrp z ι Q ↔ ∃ (i : Fin 2) (q : Perm (Fin 10)), q ∈ Q ∧ g = z ^ (i : ℕ) * ι q := by
  constructor
  · intro hg
    let S : Subgroup G :=
      { carrier := {g | ∃ (i : Fin 2) (q : Perm (Fin 10)), q ∈ Q ∧ g = z ^ (i : ℕ) * ι q}
        one_mem' := ⟨0, 1, Q.one_mem, by simp⟩
        mul_mem' := by
          rintro _ _ ⟨i, q, hq, rfl⟩ ⟨j, q', hq', rfl⟩
          refine ⟨⟨((i : ℕ) + (j : ℕ)) % 2, Nat.mod_lt _ (by norm_num)⟩, q * q',
            Q.mul_mem hq hq', ?_⟩
          rw [map_mul]
          calc z ^ (i : ℕ) * ι q * (z ^ (j : ℕ) * ι q')
              = z ^ (i : ℕ) * (ι q * z ^ (j : ℕ)) * ι q' := by group
            _ = z ^ (i : ℕ) * (z ^ (j : ℕ) * ι q) * ι q' := by rw [iota_comm_z_pow hC q j]
            _ = z ^ ((i : ℕ) + (j : ℕ)) * (ι q * ι q') := by rw [pow_add]; group
            _ = z ^ (((i : ℕ) + (j : ℕ)) % 2) * (ι q * ι q') := by
                  rw [← pow_mod_orderOf z ((i : ℕ) + (j : ℕ)), hC.order]
        inv_mem' := by
          rintro _ ⟨i, q, hq, rfl⟩
          refine ⟨i, q⁻¹, Q.inv_mem hq, ?_⟩
          rw [mul_inv_rev, ← map_inv,
            show (z ^ (i : ℕ))⁻¹ = z ^ (i : ℕ) from
              inv_eq_of_mul_eq_one_right (z_pow_mul_self hC i)]
          exact iota_comm_z_pow hC q⁻¹ i }
    have hzS : z ∈ S := ⟨1, 1, Q.one_mem, by simp⟩
    have hmap : Q.map ι ≤ S := by
      intro x hx
      obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hx
      exact ⟨0, q, hq, by simp⟩
    have hle : Tgrp z ι Q ≤ S := by
      rw [Tgrp]
      exact sup_le (Subgroup.zpowers_le.mpr hzS) hmap
    exact hle hg
  · rintro ⟨i, q, hq, rfl⟩
    exact mul_mem (Subgroup.mem_sup_left (pow_mem (Subgroup.mem_zpowers z) i))
      (Subgroup.mem_sup_right (Subgroup.mem_map_of_mem ι hq))

theorem z_notMem_map (hC : CentData z ι) (Q : Subgroup (Perm (Fin 10))) : z ∉ Q.map ι := by
  intro hz
  obtain ⟨q, -, hq⟩ := Subgroup.mem_map.mp hz
  exact hC.ne_z q hq

theorem Tgrp_card (hC : CentData z ι) (Q : Subgroup (Perm (Fin 10))) :
    Nat.card (Tgrp z ι Q) = 2 * Nat.card Q := by
  let f : Fin 2 × ↥Q → ↥(Tgrp z ι Q) := fun x =>
    ⟨z ^ (x.1 : ℕ) * ι (x.2 : Perm (Fin 10)),
      mul_mem (Subgroup.mem_sup_left (pow_mem (Subgroup.mem_zpowers z) x.1))
        (Subgroup.mem_sup_right (Subgroup.mem_map_of_mem ι x.2.2))⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨i, q⟩ ⟨j, q'⟩ h
      have h' : z ^ (i : ℕ) * ι (q : Perm (Fin 10)) = z ^ (j : ℕ) * ι (q' : Perm (Fin 10)) := by
        simpa only [f] using congrArg Subtype.val h
      by_cases hij : i = j
      · subst hij
        have hq : (q : Perm (Fin 10)) = (q' : Perm (Fin 10)) := hC.inj (mul_left_cancel h')
        exact Prod.ext rfl (Subtype.ext hq)
      · exfalso
        have hval : (i : ℕ) ≠ (j : ℕ) := fun hv => hij (Fin.ext hv)
        have hsum : (i : ℕ) + (j : ℕ) = 1 := by
          have hi := i.isLt
          have hj := j.isLt
          omega
        have hzi : z ^ (i : ℕ) * z ^ (i : ℕ) = 1 := z_pow_mul_self hC i
        have h1 : ι q = z * ι q' := by
          calc ι q = (z ^ (i : ℕ) * z ^ (i : ℕ)) * ι q := by rw [hzi, one_mul]
            _ = z ^ (i : ℕ) * (z ^ (i : ℕ) * ι q) := by group
            _ = z ^ (i : ℕ) * (z ^ (j : ℕ) * ι q') := by rw [h']
            _ = (z ^ (i : ℕ) * z ^ (j : ℕ)) * ι q' := by group
            _ = z ^ ((i : ℕ) + (j : ℕ)) * ι q' := by rw [pow_add]
            _ = z * ι q' := by rw [hsum]; simp
        have h3 : z = ι q * (ι q')⁻¹ := by
          rw [h1]; group
        have h4 : ι (q * q'⁻¹) = z := by
          rw [map_mul, Subgroup.coe_inv, map_inv]
          exact h3.symm
        exact hC.ne_z (q * q'⁻¹) h4
    · intro g
      obtain ⟨i, q, hq, hg⟩ := (mem_Tgrp_iff hC).mp g.2
      exact ⟨(i, ⟨q, hq⟩), Subtype.ext hg.symm⟩
  have hcard := Nat.card_congr (Equiv.ofBijective f hf)
  rw [← hcard, Nat.card_prod, Nat.card_fin]

theorem Tgrp_isPGroup (hC : CentData z ι) {Q : Subgroup (Perm (Fin 10))} (hQ : IsPGroup 2 Q) :
    IsPGroup 2 (Tgrp z ι Q) := by
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hQ
  refine IsPGroup.of_card (n := n + 1) ?_
  rw [Tgrp_card hC Q, hn, pow_succ]
  ring

theorem relIndex_map_Tgrp (hC : CentData z ι) (Q : Subgroup (Perm (Fin 10))) :
    (Q.map ι).relIndex (Tgrp z ι Q) = 2 := by
  rw [Subgroup.relIndex]
  have hcardH : Nat.card ((Q.map ι).subgroupOf (Tgrp z ι Q)) = Nat.card Q := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (map_le_Tgrp (z := z) (ι := ι) Q)).toEquiv]
    exact Subgroup.card_map_of_injective hC.inj
  have hmul := Subgroup.card_mul_index (H := (Q.map ι).subgroupOf (Tgrp z ι Q))
  rw [hcardH, Tgrp_card hC Q] at hmul
  rw [mul_comm (2 : ℕ) (Nat.card Q)] at hmul
  haveI : Nonempty ↥Q := ⟨⟨1, Q.one_mem⟩⟩
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos hmul

@[expose] def Fgrp (T : Subgroup G) : Subgroup G := centralizer (T : Set G) ⊓ T

theorem mem_Fgrp_iff (hC : CentData z ι) {Q : Subgroup (Perm (Fin 10))} (hQ : GoodQ Q) {p : G} :
    p ∈ Fgrp (Tgrp z ι Q) ↔
      ∃ i j k : Fin 2, p = z ^ (i : ℕ) * (ι τ₀) ^ (j : ℕ) * (ι ρ₄) ^ (k : ℕ) := by
  constructor
  · intro hp
    rw [Fgrp, Subgroup.mem_inf] at hp
    obtain ⟨hp_cent, hp_T⟩ := hp
    obtain ⟨i, q, hq, hpq⟩ := (mem_Tgrp_iff hC).mp hp_T
    have hqcent : ∀ q' ∈ Q, q * q' = q' * q := by
      intro q' hq'
      have hq'T : ι q' ∈ Tgrp z ι Q := map_le_Tgrp Q (Subgroup.mem_map_of_mem ι hq')
      have hcomm : (z ^ (i : ℕ) * ι q) * ι q' = ι q' * (z ^ (i : ℕ) * ι q) := by
        simpa only [hpq] using ((Subgroup.mem_centralizer_iff.mp hp_cent) (ι q') hq'T).symm
      have hL : (z ^ (i : ℕ) * ι q) * ι q' = z ^ (i : ℕ) * (ι q * ι q') := by group
      have hR : ι q' * (z ^ (i : ℕ) * ι q) = z ^ (i : ℕ) * (ι q' * ι q) := by
        rw [← mul_assoc, iota_comm_z_pow hC q' i]; group
      rw [hL, hR] at hcomm
      have hcancel : ι q * ι q' = ι q' * ι q := mul_left_cancel hcomm
      rw [← map_mul, ← map_mul] at hcancel
      exact hC.inj hcancel
    rcases hQ.center q hq hqcent with h1 | h2 | h3 | h4
    · exact ⟨i, 0, 0, by rw [hpq, h1]; simp⟩
    · exact ⟨i, 1, 0, by rw [hpq, h2]; simp⟩
    · exact ⟨i, 0, 1, by rw [hpq, h3]; simp⟩
    · exact ⟨i, 1, 1, by rw [hpq, h4, map_mul]; simp [mul_assoc]⟩
  · rintro ⟨i, j, k, rfl⟩
    rw [Fgrp]
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro t ht
      obtain ⟨a, q, hq, rfl⟩ := (mem_Tgrp_iff hC).mp ht
      have hz : Commute z (z ^ (i : ℕ) * (ι τ₀) ^ (j : ℕ) * (ι ρ₄) ^ (k : ℕ)) :=
        (((Commute.refl z).pow_right i).mul_right ((z_comm_iota hC τ₀).pow_right j)).mul_right
          ((z_comm_iota hC ρ₄).pow_right k)
      have hqt : Commute (ι q) (ι τ₀) := by
        show ι q * ι τ₀ = ι τ₀ * ι q
        rw [← map_mul, ← map_mul]
        congr 1
        exact (hQ.τ₀_comm q hq).symm
      have hqr : Commute (ι q) (ι ρ₄) := by
        show ι q * ι ρ₄ = ι ρ₄ * ι q
        rw [← map_mul, ← map_mul]
        congr 1
        exact (hQ.ρ₄_comm q hq).symm
      have hqp : Commute (ι q) (z ^ (i : ℕ) * (ι τ₀) ^ (j : ℕ) * (ι ρ₄) ^ (k : ℕ)) :=
        ((((z_comm_iota hC q).symm).pow_right i).mul_right (hqt.pow_right j)).mul_right
          (hqr.pow_right k)
      exact (hz.pow_left a).mul_left hqp
    · refine mul_mem (mul_mem ?_ ?_) ?_
      · exact Subgroup.mem_sup_left (pow_mem (Subgroup.mem_zpowers z) i)
      · exact Subgroup.mem_sup_right (pow_mem (Subgroup.mem_map_of_mem ι hQ.τ₀_mem) j)
      · exact Subgroup.mem_sup_right (pow_mem (Subgroup.mem_map_of_mem ι hQ.ρ₄_mem) k)

theorem normalizer_le_normalizer_Fgrp (T : Subgroup G) :
    normalizer (T : Set G) ≤ normalizer (Fgrp T : Set G) := by
  intro g hg
  rw [Subgroup.mem_set_normalizer_iff] at hg ⊢
  intro p
  constructor
  · intro hp
    rw [Fgrp] at hp ⊢
    obtain ⟨hpc, hpT⟩ := Subgroup.mem_inf.mp hp
    refine Subgroup.mem_inf.mpr ⟨?_, (hg p).mp hpT⟩
    rw [Subgroup.mem_centralizer_iff] at hpc ⊢
    intro t ht
    have hgtg : g⁻¹ * t * g ∈ T := by
      have hthis : g * (g⁻¹ * t * g) * g⁻¹ = t := by group
      exact (hg (g⁻¹ * t * g)).mpr (hthis.symm ▸ ht)
    have hcomm := hpc (g⁻¹ * t * g) hgtg
    calc t * (g * p * g⁻¹) = g * ((g⁻¹ * t * g) * p) * g⁻¹ := by group
      _ = g * (p * (g⁻¹ * t * g)) * g⁻¹ := by rw [hcomm]
      _ = (g * p * g⁻¹) * t := by group
  · intro hp
    rw [Fgrp] at hp ⊢
    obtain ⟨hpc, hpT⟩ := Subgroup.mem_inf.mp hp
    refine Subgroup.mem_inf.mpr ⟨?_, (hg p).mpr hpT⟩
    rw [Subgroup.mem_centralizer_iff] at hpc ⊢
    intro t ht
    have hgtg : g * t * g⁻¹ ∈ T := (hg t).mp ht
    have hcomm := hpc (g * t * g⁻¹) hgtg
    calc t * p = g⁻¹ * ((g * t * g⁻¹) * (g * p * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * p * g⁻¹) * (g * t * g⁻¹)) * g := by rw [hcomm]
      _ = p * t := by group

end CFSG.OddStandard.AltStdSec.SwapPattern
