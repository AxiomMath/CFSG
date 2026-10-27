module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8Fink
public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec8s_odd_cent_E [Finite G] {t : G} {L S : Subgroup G} {z g : G} {B E : Subgroup G}
    (hE : Sec8E G t L S z g B E) {o : G} (ho : Odd (orderOf o))
    (hoX : o ∈ normalizer (E : Set G)) (hot : o * t = t * o)
    (hoB : ∀ b ∈ B, o * b = b * o) : o ∈ centralizer (E : Set G) := by
  classical
  have ht2 : t * t = 1 := by
    rw [← pow_two, ← hE.ctx.involution, pow_orderOf_eq_one]
  have hB2 : ∀ b ∈ B, b * b = 1 :=
    fun b hb => CFSG.Open.IsElemAbelian.mul_self_eq_one hE.ctx.B_e16.1 hb
  have hot_inv : o⁻¹ * t * o = t := by
    calc o⁻¹ * t * o = o⁻¹ * (t * o) := by group
      _ = o⁻¹ * (o * t) := by rw [← hot]
      _ = t := by group
  have hot_conj : o * t * o⁻¹ = t := by
    calc o * t * o⁻¹ = (o * t) * o⁻¹ := by group
      _ = (t * o) * o⁻¹ := by rw [hot]
      _ = t := by group
  have hkey : ∀ e ∈ E, o * (o * e * o⁻¹) * o⁻¹ = e := by
    intro e he
    have he' : o * e * o⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp hoX e).mp he
    have hlamB : e * t * e⁻¹ * t⁻¹ ∈ B := hE.comm_le e he
    have hcomm : o * (e * t * e⁻¹ * t⁻¹) = (e * t * e⁻¹ * t⁻¹) * o := hoB _ hlamB
    have hlam : (o * e * o⁻¹) * t * (o * e * o⁻¹)⁻¹ * t⁻¹ = e * t * e⁻¹ * t⁻¹ := by
      calc (o * e * o⁻¹) * t * (o * e * o⁻¹)⁻¹ * t⁻¹
          = o * e * (o⁻¹ * t * o) * e⁻¹ * o⁻¹ * t⁻¹ := by group
        _ = o * e * t * e⁻¹ * o⁻¹ * t⁻¹ := by rw [hot_inv]
        _ = o * (e * t * e⁻¹) * o⁻¹ * t⁻¹ := by group
        _ = o * ((e * t * e⁻¹ * t⁻¹) * t) * o⁻¹ * t⁻¹ := by group
        _ = o * (e * t * e⁻¹ * t⁻¹) * t * o⁻¹ * t⁻¹ := by group
        _ = (e * t * e⁻¹ * t⁻¹) * o * t * o⁻¹ * t⁻¹ := by rw [hcomm]
        _ = (e * t * e⁻¹ * t⁻¹) * (o * t * o⁻¹) * t⁻¹ := by group
        _ = (e * t * e⁻¹ * t⁻¹) * t * t⁻¹ := by rw [hot_conj]
        _ = e * t * e⁻¹ * t⁻¹ := by group
    have hlam' : (o * e * o⁻¹) * t * (o * e * o⁻¹)⁻¹ = e * t * e⁻¹ := by
      calc (o * e * o⁻¹) * t * (o * e * o⁻¹)⁻¹
          = ((o * e * o⁻¹) * t * (o * e * o⁻¹)⁻¹ * t⁻¹) * t := by group
        _ = (e * t * e⁻¹ * t⁻¹) * t := by rw [hlam]
        _ = e * t * e⁻¹ := by group
    have hk : (e⁻¹ * (o * e * o⁻¹)) * t = t * (e⁻¹ * (o * e * o⁻¹)) := by
      have h1 : (e⁻¹ * (o * e * o⁻¹)) * t * (e⁻¹ * (o * e * o⁻¹))⁻¹ = t := by
        calc (e⁻¹ * (o * e * o⁻¹)) * t * (e⁻¹ * (o * e * o⁻¹))⁻¹
            = e⁻¹ * ((o * e * o⁻¹) * t * (o * e * o⁻¹)⁻¹) * e := by group
          _ = e⁻¹ * (e * t * e⁻¹) * e := by rw [hlam']
          _ = t := by group
      calc (e⁻¹ * (o * e * o⁻¹)) * t
          = ((e⁻¹ * (o * e * o⁻¹)) * t * (e⁻¹ * (o * e * o⁻¹))⁻¹) *
              (e⁻¹ * (o * e * o⁻¹)) := by group
        _ = t * (e⁻¹ * (o * e * o⁻¹)) := by rw [h1]
    have hkcent : e⁻¹ * (o * e * o⁻¹) ∈ centralizer ({t} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hk
    have hbB : e⁻¹ * (o * e * o⁻¹) ∈ B := by
      rw [← hE.cent_t]
      exact ⟨E.mul_mem (E.inv_mem he) he', hkcent⟩
    have hobo : o * (e⁻¹ * (o * e * o⁻¹)) * o⁻¹ = e⁻¹ * (o * e * o⁻¹) := by
      calc o * (e⁻¹ * (o * e * o⁻¹)) * o⁻¹
          = (e⁻¹ * (o * e * o⁻¹)) * o * o⁻¹ := by rw [hoB _ hbB]
        _ = e⁻¹ * (o * e * o⁻¹) := by group
    have hbb : (e⁻¹ * (o * e * o⁻¹)) * (e⁻¹ * (o * e * o⁻¹)) = 1 := hB2 _ hbB
    have he'eq : o * e * o⁻¹ = e * (e⁻¹ * (o * e * o⁻¹)) := by group
    calc o * (o * e * o⁻¹) * o⁻¹
        = (o * e * o⁻¹) * (o * (e⁻¹ * (o * e * o⁻¹)) * o⁻¹) := by group
      _ = (o * e * o⁻¹) * (e⁻¹ * (o * e * o⁻¹)) := by rw [hobo]
      _ = (e * (e⁻¹ * (o * e * o⁻¹))) * (e⁻¹ * (o * e * o⁻¹)) :=
            congrArg (fun x => x * (e⁻¹ * (o * e * o⁻¹))) he'eq
      _ = e * ((e⁻¹ * (o * e * o⁻¹)) * (e⁻¹ * (o * e * o⁻¹))) := by group
      _ = e * 1 := by rw [hbb]
      _ = e := by rw [mul_one]
  have hsq : o ^ 2 ∈ centralizer (E : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    have h := hkey e he
    have hsq' : o * o * e = e * (o * o) := by
      calc o * o * e = o * (o * e) := by group
        _ = o * ((o * e * o⁻¹) * o) := by group
        _ = (o * (o * e * o⁻¹)) * o := by group
        _ = (o * (o * e * o⁻¹) * o⁻¹) * o * o := by group
        _ = e * o * o := by rw [h]
        _ = e * (o * o) := by group
    rw [pow_two]
    exact hsq'.symm
  obtain ⟨m, hm⟩ := ho
  have ho_eq : o = (o ^ 2) ^ (m + 1) := by
    rw [← pow_mul]
    have h3 : 2 * (m + 1) = orderOf o + 1 := by rw [hm]; ring
    rw [h3, pow_succ, pow_orderOf_eq_one, one_mul]
  rw [ho_eq]
  exact (centralizer (E : Set G)).pow_mem hsq (m + 1)

end CFSG.OddStandard.SmallF3.Omega
