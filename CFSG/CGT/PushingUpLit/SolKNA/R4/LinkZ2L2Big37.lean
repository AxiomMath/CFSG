module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2Big33
public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2Big4

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected)
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
open CFSG.ClassicalInvolution.Q3.TL4.Z2W
open CFSG.Blueprint

section Pure

variable {Y : Type} [Group Y]

theorem exists_orderOf_eq_two_pow (P : Sylow 2 Y) {x : Y} (hx : x ∈ (P : Subgroup Y)) :
    ∃ L : ℕ, orderOf x = 2 ^ L := by
  obtain ⟨L, hL⟩ := IsPGroup.iff_orderOf.mp P.isPGroup' ⟨x, hx⟩
  exact ⟨L, by simpa using hL⟩

theorem two_le_of_orderOf_eq_two_pow {x : Y} {L : ℕ} (hx : orderOf x = 2 ^ L) (hx1 : x ≠ 1)
    (hx2 : x * x ≠ 1) : 2 ≤ L := by
  by_contra h
  have hL : L = 0 ∨ L = 1 := by omega
  rcases hL with rfl | rfl
  · rw [pow_zero] at hx
    exact hx1 (orderOf_eq_one_iff.mp hx)
  · rw [pow_one] at hx
    exact hx2 (by rw [← pow_two, ← hx, pow_orderOf_eq_one])

theorem pow_half_mul_self_eq_one {x : Y} {L : ℕ} (hL : 1 ≤ L) (hx : orderOf x = 2 ^ L) :
    x ^ 2 ^ (L - 1) * x ^ 2 ^ (L - 1) = 1 ∧ x ^ 2 ^ (L - 1) ≠ 1 := by
  constructor
  · rw [← pow_add, ← two_mul, ← pow_succ', Nat.sub_add_cancel hL, ← hx, pow_orderOf_eq_one]
  · intro h
    have hdvd : orderOf x ∣ 2 ^ (L - 1) := orderOf_dvd_of_pow_eq_one h
    rw [hx] at hdvd
    have hle : 2 ^ L ≤ 2 ^ (L - 1) := Nat.le_of_dvd (pow_pos (by norm_num) _) hdvd
    have hlt : 2 ^ (L - 1) < 2 ^ L := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega

theorem eq_of_mem_zpowers_of_mul_self_eq_one [Finite Y] {b a c : Y} (ha : a ∈ Subgroup.zpowers b)
    (hc : c ∈ Subgroup.zpowers b) (ha2 : a * a = 1) (hc2 : c * c = 1) (ha1 : a ≠ 1) (hc1 : c ≠ 1) :
    a = c :=
  CFSG.ClassicalInvolution.Disconnected.AschTight.S1916.eq_of_mul_self_eq_one_of_isCyclic
    (Subgroup.isCyclic_zpowers b) ha hc ha2 hc2 ha1 hc1

theorem pow_half_eq_of_mem_zpowers [Finite Y] {b a c : Y} {L : ℕ} (hL : 1 ≤ L)
    (hc : orderOf c = 2 ^ L) (hcb : c ∈ Subgroup.zpowers b) (ha : a ∈ Subgroup.zpowers b)
    (ha2 : a * a = 1) (ha1 : a ≠ 1) : c ^ 2 ^ (L - 1) = a := by
  obtain ⟨h2, h1⟩ := pow_half_mul_self_eq_one hL hc
  exact eq_of_mem_zpowers_of_mul_self_eq_one ((Subgroup.zpowers b).pow_mem hcb _) ha h2 ha2 h1 ha1

end Pure

section Cit3


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {J : Subgroup Y} {u : Y} {R₀ T₀ : Subgroup Y} {P : Sylow 2 Y}

theorem Z2SetR.tu_mul_self (hs : Z2SetR r n R S t J u R₀ T₀ P) : t * u * (t * u) = 1 := by
  calc t * u * (t * u) = t * (u * t) * u := by group
    _ = t * (t * u) * u := by rw [hs.tu_comm]
    _ = (t * t) * (u * u) := by group
    _ = 1 := by rw [hs.t2, hs.u2, mul_one]

theorem Z2SetR.tri_of_pi4 (hs : Z2SetR r n R S t J u R₀ T₀ P) (hr : 4 ≤ r) {x : Y}
    (hx : x ∈ edgeCent (P : Subgroup Y) t u) {L : ℕ} (hL : 2 ≤ L) (hxL : x ^ 2 ^ L = 1) :
    (ActsTriv (linkLayer R t) (x ^ 2 ^ (L - 1)) ∨ ActsLike (linkLayer R t) (x ^ 2 ^ (L - 1)) u ∨
        ¬ InnerModOdd (linkLayer R t) (x ^ 2 ^ (L - 1))) ∧
      (ActsTriv (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u) (x ^ 2 ^ (L - 1)) ∨
        ActsLike (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u) (x ^ 2 ^ (L - 1)) t ∨
        ¬ InnerModOdd (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u)
          (x ^ 2 ^ (L - 1))) := by
  obtain ⟨p, f, hm⟩ := hs.exists_linkModel hr (z2BigModelArith_holds r)
  exact ⟨hs.pi_t_pi4_involution hr (z2BigModelPi4_holds r) hm hx hL hxL,
    hs.pi_u_pi4_involution hr (z2BigModelPi4_holds r) hm hx hL hxL⟩

theorem Z2SetR.eq_tu_of_tri (hs : Z2SetR r n R S t J u R₀ T₀ P) (hr : 4 ≤ r)
    (hX : Z2BigXPlusA r n) (h1 : C264One (CoreAssembly.conjClass (tightCore R)) t u)
    (hall : NoA1All R t J u) (hno : ¬ InvOutsideA (P : Subgroup Y) t u) {x : Y}
    (hxA : x ∈ edgeCent (P : Subgroup Y) t u) (hx2 : x * x = 1)
    (htt : ActsTriv (linkLayer R t) x ∨ ActsLike (linkLayer R t) x u ∨
      ¬ InnerModOdd (linkLayer R t) x)
    (htu : ActsTriv (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u) x ∨
      ActsLike (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u) x t ∨
      ¬ InnerModOdd (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u) x)
    {g : Y} (hg : g * x * g⁻¹ = t * u) : x = t * u := by
  by_cases hout : ¬ InnerModOdd (linkLayer R t) x ∨
      ¬ InnerModOdd (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u) x
  · exact absurd hg (hX hr Y R S t J u R₀ T₀ P hs h1 hall hno x hxA hx2 hout g)
  · simp only [not_or, not_not] at hout
    have hE : ActsInE R t J u x :=
      ⟨htt.elim Or.inl (fun h => h.elim Or.inr (fun h' => absurd hout.1 h')),
        htu.elim Or.inl (fun h => h.elim Or.inr (fun h' => absurd hout.2 h'))⟩
    have hEm := hs.mem_E_of_actsInE hxA hE
    have hxg : g⁻¹ * (t * u) * g = x := by
      rw [← hg]
      group
    have h2 := hs.eq_tu_of_conj_mem_E (g := g) (by rw [hxg]; exact hEm)
    rw [hxg] at h2
    exact h2

theorem Z2SetR.eq_tu_of_pi4 (hs : Z2SetR r n R S t J u R₀ T₀ P) (hr : 4 ≤ r)
    (hX : Z2BigXPlusA r n) (h1 : C264One (CoreAssembly.conjClass (tightCore R)) t u)
    (hall : NoA1All R t J u) (hno : ¬ InvOutsideA (P : Subgroup Y) t u) {x : Y}
    (hxA : x ∈ edgeCent (P : Subgroup Y) t u) {L : ℕ} (hL : 2 ≤ L) (hxL : x ^ 2 ^ L = 1) {g : Y}
    (hg : g * x ^ 2 ^ (L - 1) * g⁻¹ = t * u) : x ^ 2 ^ (L - 1) = t * u := by
  have hx2 : x ^ 2 ^ (L - 1) * x ^ 2 ^ (L - 1) = 1 := by
    rw [← pow_add, ← two_mul, ← pow_succ', show L - 1 + 1 = L by omega, hxL]
  obtain ⟨h1t, h1u⟩ := hs.tri_of_pi4 hr hxA hL hxL
  exact hs.eq_tu_of_tri hr hX h1 hall hno ((edgeCent (P : Subgroup Y) t u).pow_mem hxA _) hx2
    h1t h1u hg

theorem Z2SetR.mem_edgeCent_conj_iff_of_fix (hs : Z2SetR r n R S t J u R₀ T₀ P)
    (h1 : C264One (CoreAssembly.conjClass (tightCore R)) t u) {x g : Y}
    (hxP : x ∈ (P : Subgroup Y)) (hg : g⁻¹ * (t * u) * g = t * u)
    (hxg : g⁻¹ * x * g ∈ (P : Subgroup Y)) :
    x ∈ edgeCent (P : Subgroup Y) t u ↔ g⁻¹ * x * g ∈ edgeCent (P : Subgroup Y) t u := by
  have hc : g⁻¹ ∈ Subgroup.centralizer ({t * u} : Set Y) := mem_centralizer_of_conj_eq hg
  have h := hs.mem_edgeCent_iff_conj h1 hxP hc (by rwa [inv_inv])
  rwa [inv_inv] at h

end Cit3

end CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big
