module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84A3Ker
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84B1Set

public section

namespace CFSG.OddStandard.SmallF3.Omega

namespace B89

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z g : G} {B E : Subgroup G}

theorem E_inf_OX (hE : Sec8E G t L S z g B E) :
    ∀ e ∈ E, e ∈ oddCoreIn (normalizer (E : Set G)) → e = 1 :=
  RedAct.inf_of_card_two_pow (k := 8) hE.elem.2 (odd_card_oddCoreIn _)

theorem E_sq (hE : Sec8E G t L S z g B E) {e : G} (he : e ∈ E) : e * e = 1 := by
  rw [← pow_two]
  exact hE.elem.1.2 e he

theorem OX_conj_mem {n o : G} (hn : n ∈ normalizer (E : Set G))
    (ho : o ∈ oddCoreIn (normalizer (E : Set G))) :
    n * o * n⁻¹ ∈ oddCoreIn (normalizer (E : Set G)) := by
  have hle := (oddCoreIn_normal (normalizer (E : Set G))).1
  have hnormX : normalizer (E : Set G) ≤ normalizer (oddCoreIn (normalizer (E : Set G)) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mp (oddCoreIn_normal _).2
  exact (Subgroup.mem_normalizer_iff.mp (hnormX hn) o).mp ho

theorem cent_decomp (F : Sec8T84Base) (hE : Sec8E G t L S z g B E) {c : G}
    (hc : c ∈ centralizer (E : Set G)) (hct : c * t = t * c) :
    ∃ b ∈ B, ∃ o ∈ oddCoreIn (normalizer (E : Set G)), o * t = t * o ∧ c = b * o := by
  obtain ⟨hcE, hOc⟩ := F.hCE G t L S z g B E hE
  have hEO : ∀ x ∈ E, ∀ y ∈ oddCoreIn (normalizer (E : Set G)), x * y = y * x :=
    fun x hx y hy => Subgroup.mem_centralizer_iff.mp (hOc hy) x hx
  have hcmem : c ∈ E ⊔ oddCoreIn (normalizer (E : Set G)) := by
    rw [← hcE]
    exact hc
  obtain ⟨e, he, o, ho, rfl⟩ := A3.exists_mul_of_comm hEO hcmem
  have htX := t_mem_X hE
  have h1 : t * e * t⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp htX e).mp he
  have h2 : t * o * t⁻¹ ∈ oddCoreIn (normalizer (E : Set G)) := OX_conj_mem htX ho
  have h3 : (t * e * t⁻¹) * (t * o * t⁻¹) = e * o := by
    calc (t * e * t⁻¹) * (t * o * t⁻¹) = t * (e * o) * t⁻¹ := by group
      _ = e * o := by rw [← hct]; group
  have h4 : (t * e * t⁻¹)⁻¹ * e = (t * o * t⁻¹) * o⁻¹ := by
    have h5 : t * o * t⁻¹ = (t * e * t⁻¹)⁻¹ * (e * o) := by
      rw [← h3]
      group
    rw [h5]
    group
  have h6 : (t * e * t⁻¹)⁻¹ * e = 1 :=
    E_inf_OX hE _ (mul_mem (inv_mem h1) he) (by rw [h4]; exact mul_mem h2 (inv_mem ho))
  have h7 : (t * o * t⁻¹) * o⁻¹ = 1 := by
    rw [← h4]
    exact h6
  have h8 : t * e * t⁻¹ = e := inv_mul_eq_one.mp h6
  have h9 : t * o * t⁻¹ = o := mul_inv_eq_one.mp h7
  have h10 : e * t = t * e := by
    calc e * t = (t * e * t⁻¹) * t := by rw [h8]
      _ = t * e := by group
  have h11 : o * t = t * o := by
    calc o * t = (t * o * t⁻¹) * t := by rw [h9]
      _ = t * o := by group
  refine ⟨e, ?_, o, ho, h11, rfl⟩
  have h12 : e ∈ E ⊓ centralizer ({t} : Set G) :=
    Subgroup.mem_inf.mpr ⟨he, Subgroup.mem_centralizer_singleton_iff.mpr h10⟩
  rwa [hE.cent_t] at h12

theorem exists_odd_pow_sq_mem_B (F : Sec8T84Base) (hE : Sec8E G t L S z g B E) {y : G}
    (hy : y * t = t * y) (hyc : y * y ∈ centralizer (E : Set G)) :
    ∃ m : ℕ, Odd m ∧ (y ^ m) * (y ^ m) ∈ B := by
  have hyt : (y * y) * t = t * (y * y) := by
    calc (y * y) * t = y * (y * t) := by group
      _ = y * (t * y) := by rw [hy]
      _ = (y * t) * y := by group
      _ = (t * y) * y := by rw [hy]
      _ = t * (y * y) := by group
  obtain ⟨b, hb, o, ho, -, hbo⟩ := cent_decomp F hE hyc hyt
  have hodd : Odd (orderOf o) :=
    Odd.of_dvd_nat (odd_card_oddCoreIn _) (Subgroup.orderOf_dvd_natCard _ ho)
  have hbo_comm : Commute b o := by
    have hOc := (F.hCE G t L S z g B E hE).2 ho
    exact Subgroup.mem_centralizer_iff.mp hOc b (B_le_E hE hb)
  refine ⟨orderOf o, hodd, ?_⟩
  have h1 : (y ^ orderOf o) * (y ^ orderOf o) = (b * o) ^ orderOf o := by
    rw [← hbo, ← pow_add, ← two_mul, pow_mul, sq]
  have h2 : (b * o) ^ orderOf o = b ^ orderOf o := by
    rw [Commute.mul_pow hbo_comm, pow_orderOf_eq_one, mul_one]
  have h3 : b ^ orderOf o = b := by
    obtain ⟨k, hk⟩ := hodd
    rw [hk, pow_succ, pow_mul, sq, E_sq hE (B_le_E hE hb), one_pow, one_mul]
  rw [h1, h2, h3]
  exact hb

end B89

end CFSG.OddStandard.SmallF3.Omega
