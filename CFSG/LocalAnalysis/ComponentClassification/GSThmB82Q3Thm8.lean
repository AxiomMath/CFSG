module

public import CFSG.LocalAnalysis.ComponentClassification.GS82FuseQ3Defs
public import CFSG.LocalAnalysis.ComponentClassification.GS82HDefs
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82CIA0L
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB51Unbal
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4X81Conf
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82SecondCentral

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

namespace Eight2

private theorem exists_central_of_dihedral {G : Type*} [Group G] {P B : Subgroup G} {x b : G}
    (hx : x * x = 1) (hxP : ∀ p ∈ P, x * p * x⁻¹ ∈ P) (hbB : b ∈ B) (hbP : b ∈ P)
    (hb : b * b = 1) (hb1 : b ≠ 1) (hBx : B ⊓ centralizer ({x} : Set G) = ⊥)
    (hn : ∃ m : ℕ, orderOf (x * b) = 2 ^ m) :
    ∃ j : ℕ, ∃ d ∈ P, orderOf d = 2 ∧ d * b = b * d ∧ d * x = x * d ∧
      ((x * b) ^ j)⁻¹ * b * (x * b) ^ j = b * d := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  obtain ⟨r, hr⟩ : ∃ r, r = x * b := ⟨_, rfl⟩
  rw [← hr] at hn ⊢
  have hxr : x = r * b := by rw [hr, mul_assoc, hb, mul_one]
  have hbr : ∀ i : ℕ, b * r ^ i * b⁻¹ = (r ^ i)⁻¹ := by
    intro i
    rw [← conj_pow, ← inv_pow]
    congr 1
    rw [hr, mul_inv_rev, hxi, hbi, mul_assoc, mul_assoc, hb, mul_one]
  have hbu : ∀ i : ℕ, (r ^ i)⁻¹ * b * r ^ i = b * r ^ (2 * i) := by
    intro i
    rw [← hbr i, two_mul, pow_add]
    group
  have hsq : r ^ 2 ≠ 1 := by
    intro h2
    apply hb1
    rw [hr, pow_two] at h2
    have hbx : b * x = x * b := by
      calc b * x = x⁻¹ * (x * b * (x * b)) * b⁻¹ := by group
        _ = x * b := by rw [h2, mul_one, hxi, hbi]
    have hbC : b ∈ B ⊓ centralizer ({x} : Set G) :=
      mem_inf.mpr ⟨hbB, mem_centralizer_singleton_iff.mpr hbx⟩
    rw [hBx] at hbC
    exact mem_bot.mp hbC
  obtain ⟨m, hm⟩ := hn
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := by
    refine ⟨m - 2, ?_⟩
    by_contra hne
    apply hsq
    rw [← orderOf_dvd_iff_pow_eq_one, hm]
    have hm2 : m < 2 := by omega
    interval_cases m <;> norm_num
  obtain ⟨j, hj⟩ : ∃ j, 2 ^ k = j := ⟨_, rfl⟩
  have hjpos : 0 < j := hj ▸ pow_pos (by norm_num) k
  have hn4 : orderOf r = 4 * j := by rw [hm, ← hj]; ring
  have hr2P : r ^ 2 ∈ P := by
    have h1 : r ^ 2 = x * b * x⁻¹ * b := by rw [hr, pow_two, hxi]; group
    rw [h1]
    exact mul_mem (hxP b hbP) hbP
  have hdP : r ^ (2 * j) ∈ P := by
    rw [pow_mul]
    exact pow_mem hr2P j
  have hdd : r ^ (2 * j) * r ^ (2 * j) = 1 := by
    rw [← pow_add, show 2 * j + 2 * j = orderOf r by rw [hn4]; ring, pow_orderOf_eq_one]
  have hd1 : r ^ (2 * j) ≠ 1 := by
    intro h
    have h1 := Nat.le_of_dvd (by omega) (orderOf_dvd_of_pow_eq_one h)
    rw [hn4] at h1
    omega
  have hd2 : orderOf (r ^ (2 * j)) = 2 := orderOf_eq_prime (by rw [pow_two]; exact hdd) hd1
  have hdb : r ^ (2 * j) * b = b * r ^ (2 * j) := by
    have h1 := hbr (2 * j)
    rw [inv_eq_of_mul_eq_one_right hdd] at h1
    calc r ^ (2 * j) * b = b * r ^ (2 * j) * b⁻¹ * b := by rw [h1]
      _ = b * r ^ (2 * j) := by group
  have hdx : r ^ (2 * j) * x = x * r ^ (2 * j) := by
    rw [hxr]
    calc r ^ (2 * j) * (r * b) = r * (r ^ (2 * j) * b) := by
          rw [← mul_assoc, (Commute.pow_self r (2 * j)).eq, mul_assoc]
      _ = r * b * r ^ (2 * j) := by rw [hdb, mul_assoc]
  exact ⟨j, r ^ (2 * j), hdP, hd2, hdb, hdx, hbu j⟩

namespace CtxA0

variable {X : Type} [Group X] [Finite X] (c : CtxA0 X)

private theorem eq_a_of_mem_sup {d : X}
    (hBx : c.s.h.secB0 c.s.y ⊓ centralizer ({c.s.h.x} : Set X) = ⊥)
    (hdB : d ∈ zpowers c.s.h.a ⊔ c.s.h.secB0 c.s.y) (hd2 : orderOf d = 2)
    (hdx : d * c.s.h.x = c.s.h.x * d) : d = c.s.h.a := by
  have haB : zpowers c.s.h.a ≤ normalizer (c.s.h.secB0 c.s.y : Set X) := by
    refine (zpowers_le.mpr ?_).trans (centralizer_le_normalizer _)
    rw [mem_centralizer_iff]
    intro w hw
    exact c.s.h.comm_a (c.s.h.B_le_S (c.s.h.secB0_le_B c.s.y hw))
  have hdmem : d ∈ ((zpowers c.s.h.a ⊔ c.s.h.secB0 c.s.y : Subgroup X) : Set X) := hdB
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ haB] at hdmem
  obtain ⟨α, hα, β, hβ, hαβ⟩ := Set.mem_mul.mp hdmem
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hα
  have hβ' : β = (c.s.h.a ^ k)⁻¹ * d := by rw [← hαβ]; group
  have hβx : β ∈ c.s.h.secB0 c.s.y ⊓ centralizer ({c.s.h.x} : Set X) := by
    refine mem_inf.mpr ⟨hβ, mem_centralizer_singleton_iff.mpr ?_⟩
    have hc : Commute ((c.s.h.a ^ k)⁻¹ * d) c.s.h.x :=
      ((Commute.zpow_right c.s.h.x_comm_a k).symm.inv_left).mul_left hdx
    rw [hβ']
    exact hc.eq
  rw [hBx, mem_bot] at hβx
  rw [hβx, mul_one] at hαβ
  have hk : c.s.h.a ^ k = c.s.h.a ^ (k % 2) := by
    have h1 := (zpow_mod_orderOf c.s.h.a k).symm
    rwa [c.s.h.orderOf_a, Nat.cast_ofNat] at h1
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · exfalso
    rw [h0, zpow_zero] at hk
    rw [← hαβ, hk, orderOf_one] at hd2
    exact absurd hd2 (by norm_num)
  · rw [← hαβ, hk, h1, zpow_one]

theorem exists_conj_b_of_three (hS : SchreierFor Blueprint.Catalog) (hPsi : GS82LemmaPsi)
    (hA : ¬ Nonempty (↥(generalizedFitting (c.s.h.subQuot c.s.y)) ≃* alternatingGroup (Fin 10)))
    (hp : c.s.p = 3) (hf : c.s.f = 1) :
    ∃ u ∈ c.s.h.S, u⁻¹ * c.b * u = c.s.h.a * c.b := by
  have := c.s.isSimpleGroup
  have hU := c.s.unbalTriple
  have hxS : c.s.h.x ∈ c.s.h.S := c.s.h.x_mem
  have hx : c.s.h.x * c.s.h.x = 1 := by
    have h1 := pow_orderOf_eq_one c.s.h.x
    rwa [(gsUnbalancingTriple_iff.mp hU).2.1, pow_two] at h1
  have hBx := Hyp52.secB0_inf_centralizer_eq_bot hS c.s.nonab c.s.h c.s.maxTriple c.s.isoAt hU
    c.s.y
  have hxP : ∀ w ∈ c.s.h.P, c.s.h.x * w * c.s.h.x⁻¹ ∈ c.s.h.P := fun w hw =>
    mem_inf.mpr ⟨mul_mem (mul_mem hxS (mem_inf.mp hw).1) (inv_mem hxS),
      X81.conj_mem_coreActionKernel (c.s.h.S_le_normalizer hxS) (mem_inf.mp hw).2⟩
  obtain ⟨j, d, hdP, hd2, hdb, hdx, hu⟩ := exists_central_of_dihedral hx hxP c.hbB c.hbP c.hbb
    c.b_ne_one hBx (c.s.h.orderOf_eq_two_pow_of_mem_S (mul_mem hxS c.hbS))
  have hda : d = c.s.h.a := by
    by_cases hdB : d ∈ zpowers c.s.h.a ⊔ c.s.h.secB0 c.s.y
    · exact c.eq_a_of_mem_sup hBx hdB hd2 hdx
    · exfalso
      obtain ⟨M, hM, -⟩ := c.s.isoAt c.s.h.x d (c.s.h.S_le hxS) hU hd2
        (c.s.h.comm_a (c.s.h.P_le_S hdP)).symm hdx.symm (mem_inf.mp hdP).2
      exact hPsi X c hA hp hf d hdP hd2 hdb hdB ⟨M, hM⟩
  refine ⟨(c.s.h.x * c.b) ^ j, pow_mem (mul_mem hxS c.hbS) j, ?_⟩
  rw [hu, hda, c.hba]

end CtxA0

end Eight2

theorem gs82Step2FuseQ3_of_psi (hS : SchreierFor Blueprint.Catalog) (hPsi : GS82LemmaPsi) :
    GS82Step2FuseQ3 := by
  intro X _ _ c hA hp hf
  obtain ⟨u, hu, hub⟩ := c.exists_conj_b_of_three hS hPsi hA hp hf
  exact ⟨c.s.t * u, c.conj_tu_a hu hub, c.conj_tu_z hu hub⟩

end CFSG.ComponentClassification.GSThmB
