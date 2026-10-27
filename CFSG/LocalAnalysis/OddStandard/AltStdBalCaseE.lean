module

public import CFSG.LocalAnalysis.OddStandard.AltStdBalKey
public import CFSG.LocalAnalysis.OddStandard.AltStdBalPartner

public section

namespace CFSG.OddStandard.AltStdBal

open Subgroup CFSG.OddStandard.Solomon75
open CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977

section CaseE

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {Q : Subgroup G} {z : G}

theorem card_eq_two_or_four_le_Q (d : Cyc L Q z) : Nat.card Q = 2 ∨ 4 ≤ Nat.card Q := by
  obtain ⟨j, hj⟩ := d.pgroup.exists_card_eq
  have h2 : 2 ∣ Nat.card Q := by
    have := orderOf_dvd_natCard (⟨z, d.mem⟩ : Q)
    rwa [Subgroup.orderOf_mk, d.order] at this
  rcases j with _ | _ | j
  · rw [hj] at h2
    norm_num at h2
  · left
    simpa using hj
  · right
    rw [hj]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (j + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem inf_eq_bot_of_cyc {Q T : Subgroup G} {z a : G} (hQc : IsCyclic Q) (hQp : IsPGroup 2 Q)
    (hz : z ∈ Q) (hz2 : orderOf z = 2) (hTc : IsCyclic T) (haT : a ∈ T) (ha2 : orderOf a = 2)
    (hne : z ≠ a) : T ⊓ Q = ⊥ := by
  by_contra hP
  have hPp : IsPGroup 2 (T ⊓ Q : Subgroup G) := hQp.to_le inf_le_right
  obtain ⟨m, hm⟩ := hPp.exists_card_eq
  have h2 : 2 ∣ Nat.card (T ⊓ Q : Subgroup G) := by
    rcases m with _ | m
    · exfalso
      have h1 : Nat.card (T ⊓ Q : Subgroup G) = 1 := by simpa using hm
      exact hP (Subgroup.card_eq_one.1 h1)
    · rw [hm, pow_succ]
      exact dvd_mul_left 2 _
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := (T ⊓ Q : Subgroup G)) 2 h2
  have hy2 : orderOf (y : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hy
  have hyT : (y : G) ∈ T := (Subgroup.mem_inf.1 y.2).1
  have hyQ : (y : G) ∈ Q := (Subgroup.mem_inf.1 y.2).2
  have h1 := eq_of_orderOf_eq_two_of_isCyclic hQc hyQ hz hy2 hz2
  have h2' := eq_of_orderOf_eq_two_of_isCyclic hTc hyT haT hy2 ha2
  exact hne (h1.symm.trans h2')

omit [Finite G] in
theorem centralizer_conj_singleton (g z : G) :
    centralizer ({g⁻¹ * z * g} : Set G) = CFSG.conjugate (centralizer ({z} : Set G)) g := by
  have := centralizer_singleton_map_mulEquiv (MulAut.conj g⁻¹) z
  simpa [MulAut.conj_apply, CFSG.conjugate] using this

theorem Cyc.comm_sup (d : Cyc L Q z) {q u : G} (hq : q ∈ Q) (hu : u ∈ L ⊔ Q) :
    q * u = u * q := by
  obtain ⟨l, hl, q', hq', rfl⟩ := (mem_sup_iff_mul d).1 hu
  calc q * (l * q') = (q * l) * q' := by group
    _ = (l * q) * q' := by rw [d.comm_L hq hl]
    _ = l * (q * q') := by group
    _ = l * (q' * q) := by rw [d.comm_Q hq hq']
    _ = (l * q') * q := by group

theorem card_eq_two_of_centralizer_le_sup (h : Setting G L n) (d : Cyc L Q z)
    (hE : centralizer ({z} : Set G) ≤ L ⊔ Q) : Nat.card Q = 2 := by
  rcases card_eq_two_or_four_le_Q d with h2 | h4
  · exact h2
  exfalso
  obtain ⟨g, hne, hcomm, -, -⟩ := exists_partner h d
  have d' := d.conj g
  have hE' : centralizer ({g⁻¹ * z * g} : Set G) ≤
      CFSG.conjugate L g ⊔ CFSG.conjugate Q g := by
    rw [centralizer_conj_singleton]
    unfold CFSG.conjugate
    rw [← Subgroup.map_sup]
    exact Subgroup.map_mono hE
  have hzC' : z ∈ centralizer ({g⁻¹ * z * g} : Set G) :=
    mem_centralizer_singleton_iff.2 hcomm.symm
  have hzLT : z ∈ CFSG.conjugate L g ⊔ CFSG.conjugate Q g := hE' hzC'
  have hTC : ∀ t ∈ CFSG.conjugate Q g, t * z = z * t := fun t ht => d'.comm_sup ht hzLT
  have hTQ : CFSG.conjugate Q g ⊓ Q = ⊥ :=
    inf_eq_bot_of_cyc d.cyclic d.pgroup d.mem d.order d'.cyclic d'.mem d'.order hne.symm
  have haC : g⁻¹ * z * g ∈ centralizer ({z} : Set G) := mem_centralizer_singleton_iff.2 hcomm
  have hsq : ∀ t ∈ CFSG.conjugate Q g, ∀ y ∈ L, y * (g⁻¹ * z * g) = (g⁻¹ * z * g) * y →
      t * y ^ 2 = y ^ 2 * t := by
    intro t ht y _ hya
    have hyC' : y ∈ centralizer ({g⁻¹ * z * g} : Set G) := mem_centralizer_singleton_iff.2 hya
    exact d'.comm_sup ht (pow_mem (hE' hyC') 2)
  have key := no_order_four_of_commute h d d'.cyclic d'.mem d'.order hTQ (hE haC) hsq
  have hTcard : Nat.card (CFSG.conjugate Q g) = Nat.card Q := card_conjugate Q g
  obtain ⟨t, htT, ht4⟩ := exists_orderOf_eq_two_pow (k := 2) d'.cyclic d'.pgroup
    (by rw [hTcard]; simpa using h4)
  exact key t htT (hE (mem_centralizer_singleton_iff.2 (hTC t htT))) (by simpa using ht4)

end CaseE

end CFSG.OddStandard.AltStdBal
