module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5CoverAct

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem t5c_conj_of_mul_odd {A : Type*} [Group A] {e e' m : A} (he : e * e = 1)
    (he' : e' * e' = 1) (hm : e' = m * e) (hodd : Odd (orderOf m)) :
    ∃ o ∈ Subgroup.zpowers m, e' = o * e * o⁻¹ := by
  have hm1 : m * (e * m * e⁻¹) = 1 := by
    have h1 : (m * e) * (m * e) = m * (e * m * e⁻¹) * (e * e) := by group
    rw [hm, h1, he, mul_one] at he'
    exact he'
  have hinv : e * m * e⁻¹ = m⁻¹ := eq_inv_of_mul_eq_one_right hm1
  obtain ⟨k, hk⟩ := hodd
  have hmk : m ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one m
  refine ⟨m ^ (k + 1), Subgroup.pow_mem _ (Subgroup.mem_zpowers m) _, ?_⟩
  have hsq : m ^ (k + 1) * m ^ (k + 1) = m := by
    rw [← pow_add, show k + 1 + (k + 1) = (2 * k + 1) + 1 by ring, pow_succ, hmk, one_mul]
  have hconj : e * m ^ (k + 1) * e⁻¹ = (m ^ (k + 1))⁻¹ := by
    rw [← conj_pow, hinv, inv_pow]
  calc e' = m * e := hm
    _ = (m ^ (k + 1) * m ^ (k + 1)) * e⁻¹ := by rw [hsq, inv_eq_of_mul_eq_one_right he]
    _ = m ^ (k + 1) * (e * e) * m ^ (k + 1) * e⁻¹ := by rw [he, mul_one]
    _ = m ^ (k + 1) * e * (e * m ^ (k + 1) * e⁻¹) := by group
    _ = m ^ (k + 1) * e * (m ^ (k + 1))⁻¹ := by rw [hconj]

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {hQ : Q.Nondegenerate}

theorem t5c_conj_exact (hL : IsOm6Z2 L) {φ : ↥L →* omegaGroup hQ} (h : IsCoverMap L φ) {b : G}
    (hb2 : b * b = 1) {x : simGroup Q} (hb : CoverAct L φ b x) {u : G} (hu : u ∈ L)
    (he2 : (u * b) * (u * b) = 1) {c : omegaGroup hQ}
    (hc : ((φ ⟨u, hu⟩ : omegaGroup hQ) : OGroup Q) =
      (c : OGroup Q) * simAct Q x (c : OGroup Q)⁻¹) :
    u * b ∈ conjClassIn L b := by
  obtain ⟨l, hl⟩ := h.surjective c
  let l' : ↥L := ⟨b * (l : G) * b⁻¹, (Subgroup.mem_normalizer_iff.mp hb.1 (l : G)).mp l.2⟩
  have hl' : ((φ l' : omegaGroup hQ) : OGroup Q) = simAct Q x (c : OGroup Q) := by
    rw [hb.2 l l' rfl, hl]
  let M : ↥L := l * l'⁻¹ * (⟨u, hu⟩ : ↥L)⁻¹
  have hφM : φ M = 1 := by
    apply Subtype.ext
    have h1 : ((φ M : omegaGroup hQ) : OGroup Q) =
        (c : OGroup Q) * (simAct Q x (c : OGroup Q))⁻¹ *
          ((φ ⟨u, hu⟩ : omegaGroup hQ) : OGroup Q)⁻¹ := by
      simp only [M, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hl, hl']
    have h2 : simAct Q x ((c : OGroup Q)⁻¹) = (simAct Q x (c : OGroup Q))⁻¹ := map_inv _ _
    rw [h1, hc, h2, Subgroup.coe_one]
    group
  have hMker : M ∈ φ.ker := MonoidHom.mem_ker.mpr hφM
  have hodd : Odd (orderOf (M : G)) := by
    rw [Subgroup.orderOf_coe]
    exact ((h.oddCentralCover hL).odd_card_ker).of_dvd_nat
      (Subgroup.orderOf_dvd_natCard φ.ker hMker)
  have hMG : (M : G) = (l : G) * b * (l : G)⁻¹ * b⁻¹ * u⁻¹ := by
    simp only [M, l', Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have he'2 : ((l : G) * b * (l : G)⁻¹) * ((l : G) * b * (l : G)⁻¹) = 1 := by
    calc ((l : G) * b * (l : G)⁻¹) * ((l : G) * b * (l : G)⁻¹)
        = (l : G) * (b * b) * (l : G)⁻¹ := by group
      _ = 1 := by rw [hb2]; group
  have hm : (l : G) * b * (l : G)⁻¹ = (M : G) * (u * b) := by
    rw [hMG]
    group
  obtain ⟨o, ho, hoe⟩ := t5c_conj_of_mul_odd he2 he'2 hm hodd
  have hoL : o ∈ L := (Subgroup.zpowers_le.mpr M.2) ho
  refine ⟨o⁻¹ * (l : G), L.mul_mem (L.inv_mem hoL) l.2, ?_⟩
  calc u * b = o⁻¹ * (o * (u * b) * o⁻¹) * o := by group
    _ = o⁻¹ * ((l : G) * b * (l : G)⁻¹) * o := by rw [← hoe]
    _ = (o⁻¹ * (l : G)) * b * (o⁻¹ * (l : G))⁻¹ := by group

end CFSG.OddStandard.SmallF3.Omega
