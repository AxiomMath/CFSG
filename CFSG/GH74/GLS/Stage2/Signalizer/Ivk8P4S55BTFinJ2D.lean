module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTFinFour
public import CFSG.Sporadic.SmallOddCore.J2
public import Certificates.Certificate55106
public import Certificates.Data.GH74.BTFinCk

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT.FinJ2

open Subgroup CFSG CFSG.Certificates CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier
  CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native Certificates.BTFinCk

theorem le_j2R : j2P ≤ j2R := le_sup_left

theorem mem_j2P_of_odd
    {x : Equiv.Perm (Fin 315)} (hx : x ∈ j2R)
    (ho : Odd (orderOf x)) : x ∈ j2P := by
  obtain ⟨hU2, -, -, hmap, -, hRmem, -⟩ := ctuc_j2_normalizing_involution_permutation_model
  obtain ⟨m, hm⟩ := ho
  by_contra hxP
  have hxx : x * x ∈ j2P := FinFour.mul_mem_of_not_mem (fun y hy => (hRmem y).1 hy)
    (by rw [← pow_two]; exact hU2) (fun p hp => by rw [← hmap]; exact ⟨p, hp, rfl⟩) hx hx hxP
    hxP
  apply hxP
  have hx1 : x = (x * x) ^ (m + 1) := by
    rw [← pow_two, ← pow_mul]
    calc x = x ^ (2 * m + 1) * x := by rw [← hm, pow_orderOf_eq_one, one_mul]
      _ = x ^ (2 * (m + 1)) := by rw [← pow_succ, show 2 * m + 1 + 1 = 2 * (m + 1) by ring]
  rw [hx1]
  exact j2P.pow_mem hxx _

theorem not_seven_dvd {t : Equiv.Perm (Fin 315)} (ht : t ∈ j2P)
    (ho : orderOf t = 2) :
    ¬ 7 ∣ Nat.card ↥(j2P ⊓ centralizer ({t} : Set (Equiv.Perm (Fin 315)))) := by
  obtain ⟨-, -, -, hrows, hcover, -, hmap, -⟩ :=
    ctuc_j2_all_involution_fixed_subgroups_odd_core_trivial
  obtain ⟨r, hr, g, hg, rfl⟩ := hcover _ (le_j2R ht) ho
  obtain ⟨-, -, hout, -, hcent, -⟩ := hrows r hr
  have hrP : tp 315 r.rep ∈ j2P := by
    have := j2P.mul_mem (j2P.mul_mem (j2P.inv_mem hg) ht) hg
    rwa [show g⁻¹ * (g * tp 315 r.rep * g⁻¹) * g = tp 315 r.rep by group] at this
  have hro : r.outer = false := by
    cases h : r.outer
    · rfl
    · exact absurd hrP (hout.1 h)
  rw [CFSG.Sporadic.SmallOddCore.inf_centralizer_conj j2P hg,
    Subgroup.card_map_of_injective (MulAut.conj g).injective, hcent]
  have hmem : (r.outer, r.classSize, r.centOrder) ∈
      [(true, 1800, 336), (false, 2520, 240), (false, 315, 1920)] := by
    rw [← hmap]
    exact List.mem_map.2 ⟨r, hr, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
  rcases hmem with ⟨h1, -, -⟩ | ⟨-, -, h3⟩ | ⟨-, -, h3⟩
  · rw [hro] at h1
    exact absurd h1 (by decide)
  · rw [h3]; norm_num
  · rw [h3]; norm_num

theorem not_eight_dvd
    {x : Equiv.Perm (Fin 315)} (hx : x ∈ j2R) (ho : orderOf x = 5) :
    ¬ 8 ∣ Nat.card ↥(j2R ⊓ centralizer ({x} : Set (Equiv.Perm (Fin 315)))) :=
  Certificates.certificate55106.2 x (mem_j2P_of_odd hx (by rw [ho]; exact ⟨2, by norm_num⟩))
    ho

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT.FinJ2
