module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888XS1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888M3a
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888PH0

public section

open Subgroup

namespace CFSG.OddStandard.SmallF3.Omega

variable {H X : Type} [Group H] [Group X] {z : H} {K : Fin 4 → Subgroup H} {α : H →* X}

private lemma ga2a_prod_eq {Y : Type} [Group Y] (c : Fin 4 → Y) (i j : Fin 4) (hij : i ≠ j)
    (hck : ∀ k, k ≠ i → k ≠ j → c k = 1) (hcm : c i * c j = c j * c i) :
    c 0 * c 1 * c 2 * c 3 = c i * c j := by
  have h0 := hck 0
  have h1 := hck 1
  have h2 := hck 2
  have h3 := hck 3
  fin_cases i <;> fin_cases j <;> simp at hij <;> simp_all

theorem exists_involution_of_suppTwo (hS : PlaneSetup z K α)
    (hSys : PlaneSys (planeV hS.quad α) (planeW hS.quad α))
    (v : planeV hS.quad α) (hv : SuppTwo hSys v) :
    ∃ (d : H) (i j : Fin 4), i ≠ j ∧ d ∈ Sec5B517Q8 hS.quad ∧ d * d = 1 ∧ d ≠ 1 ∧ d ≠ z ∧
      d ∈ K i ⊔ K j ∧ α d = (v : X) ∧ ∃ r ∈ Sec5B517Q8 hS.quad, r * d * r⁻¹ = d * z := by
  classical
  have hcard : (suppIdx hSys v).card = 2 := hv
  obtain ⟨i, j, hij, hsupp⟩ := Finset.card_eq_two.mp hcard
  have hmem : ∀ k, k ∈ suppIdx hSys v ↔ comp hSys v k ≠ 1 := fun k => by simp [suppIdx]
  have hci : comp hSys v i ≠ 1 := (hmem i).mp (by rw [hsupp]; simp)
  have hcj : comp hSys v j ≠ 1 := (hmem j).mp (by rw [hsupp]; simp)
  have hck : ∀ k, k ≠ i → k ≠ j → comp hSys v k = 1 := by
    intro k hki hkj
    by_contra hne
    have h := (hmem k).mpr hne
    rw [hsupp] at h
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with h | h
    · exact hki h
    · exact hkj h
  have hcm : comp hSys v i * comp hSys v j = comp hSys v j * comp hSys v i :=
    hSys.comm _ (hSys.le i (comp_mem hSys v i)) _ (hSys.le j (comp_mem hSys v j))
  have hvij : (v : X) = comp hSys v i * comp hSys v j := by
    rw [prod_comp hSys v]
    exact ga2a_prod_eq (comp hSys v) i j hij hck hcm
  obtain ⟨qc, hqc, hqca⟩ := Subgroup.mem_map.mp (comp_mem hSys v i)
  obtain ⟨hqcQ, hqcK⟩ := Subgroup.mem_inf.mp hqc
  obtain ⟨qd, hqd, hqdb⟩ := Subgroup.mem_map.mp (comp_mem hSys v j)
  obtain ⟨hqdQ, hqdK⟩ := Subgroup.mem_inf.mp hqd
  have hqc4 : qc ^ 4 = 1 := Sec5B517Q8.pow_four hS.quad hqcQ
  have hqd4 : qd ^ 4 = 1 := Sec5B517Q8.pow_four hS.quad hqdQ
  have hz_alpha : α z = 1 :=
    MonoidHom.mem_ker.mp (by rw [hS.ker]; exact Subgroup.mem_zpowers z)
  have hqc1 : qc ≠ 1 := by
    intro h
    apply hci
    rw [← hqca, h, map_one]
  have hqc_z : qc ≠ z := by
    intro h
    apply hci
    rw [← hqca, h, hz_alpha]
  have hqd1 : qd ≠ 1 := by
    intro h
    apply hcj
    rw [← hqdb, h, map_one]
  have hqd_z : qd ≠ z := by
    intro h
    apply hcj
    rw [← hqdb, h, hz_alpha]
  have hqcsq : qc * qc = z := by
    rcases Sec5B517Quad.sq_of_pow4 hS.quad hqcK hqc4 with h | h
    · rcases Sec5B517Quad.eq_of_sq hS.quad hqcK h with h1 | h1
      · exact absurd h1 hqc1
      · exact absurd h1 hqc_z
    · exact h
  have hqdsq : qd * qd = z := by
    rcases Sec5B517Quad.sq_of_pow4 hS.quad hqdK hqd4 with h | h
    · rcases Sec5B517Quad.eq_of_sq hS.quad hqdK h with h1 | h1
      · exact absurd h1 hqd1
      · exact absurd h1 hqd_z
    · exact h
  set e : H := qc * qd with he
  have heQ : e ∈ Sec5B517Q8 hS.quad := (Sec5B517Q8 hS.quad).mul_mem hqcQ hqdQ
  have heK : e ∈ K i ⊔ K j := Subgroup.mul_mem_sup hqcK hqdK
  have he_alpha : α e = (v : X) := by
    rw [he, map_mul, hqca, hqdb, hvij]
  have hee : e * e = 1 := by
    have hcomm : qc * qd = qd * qc := hS.quad.comm i j hij qc hqcK qd hqdK
    have h1 : (qc * qd) * (qc * qd) = qc * (qd * qc) * qd := by group
    have h2 : qc * (qd * qc) * qd = qc * (qc * qd) * qd := by rw [hcomm]
    have h3 : qc * (qc * qd) * qd = (qc * qc) * (qd * qd) := by group
    rw [he, h1, h2, h3, hqcsq, hqdsq, hS.quad.z_sq]
  have hv1 : (v : X) ≠ 1 := by
    intro h
    have hab1 : comp hSys v i * comp hSys v j = 1 := by rw [← hvij, h]
    have ha_bd : comp hSys v i ∈ planeW hS.quad α j := by
      rw [eq_inv_of_mul_eq_one_left hab1]
      exact (planeW hS.quad α j).inv_mem (comp_mem hSys v j)
    have haz : comp hSys v i ∈ planeW hS.quad α i ⊓ planeW hS.quad α j :=
      ⟨comp_mem hSys v i, ha_bd⟩
    rw [hSys.inf_eq_bot hij] at haz
    exact hci (Subgroup.mem_bot.mp haz)
  have he1 : e ≠ 1 := by
    intro h
    exact hv1 (by rw [← he_alpha, h, map_one])
  have hez : e ≠ z := by
    intro h
    exact hv1 (by rw [← he_alpha, h, hz_alpha])
  refine ⟨e, i, j, hij, heQ, hee, he1, hez, heK, he_alpha, ?_⟩
  obtain ⟨r, hrK, hr4, hrqc⟩ :=
    Sec5B517Quad.exists_inverting hS.quad hqcK hqc4 hqc1 hqc_z
  have hrQ : r ∈ Sec5B517Q8 hS.quad := Sec5B517Q8.mem_of_mem hS.quad hrK hr4
  have hrqd : r * qd * r⁻¹ = qd := by
    rw [hS.quad.comm i j hij r hrK qd hqdK]
    group
  refine ⟨r, hrQ, ?_⟩
  rw [he]
  rw [show r * (qc * qd) * r⁻¹ = (r * qc * r⁻¹) * (r * qd * r⁻¹) by group]
  rw [hrqc, hrqd]
  rw [show qc * z * qd = (qc * qd) * z by
    rw [mul_assoc, hS.quad.z_comm hqdK, ← mul_assoc]]

end CFSG.OddStandard.SmallF3.Omega
