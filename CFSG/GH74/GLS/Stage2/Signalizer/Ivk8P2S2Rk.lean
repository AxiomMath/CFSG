module

public import CFSG.GH74.GLS.IVK.Defs
public import CFSG.GH74.Uniqueness.SU.SU1Basic
public import CFSG.Foundations.SteinbergCAGeneratedCoreNodes
public import CFSG.Dihedral.DisconnectedInvolutionGraph.QuaternionRankOne

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.P2S2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS

open CFSG.DisconnectedInvolutionGraph.Helpers (NoCommutingDistinctInvolutions Involution
  quaternion_no_commuting_distinct_involutions no_commuting_distinct_involutions_of_injective
  no_commuting_distinct_involutions_sylow_iff)

theorem cyclic_unique_involution {R : Type} [Group R] [Finite R] (hc : IsCyclic R) {a b : R}
    (ha : orderOf a = 2) (hb : orderOf b = 2) : a = b := by
  classical
  have := Fintype.ofFinite R
  by_contra hab
  have ha1 : a ≠ 1 := fun h => by rw [h, orderOf_one] at ha; omega
  have hb1 : b ≠ 1 := fun h => by rw [h, orderOf_one] at hb; omega
  have ha2 : a ^ 2 = 1 := by have := pow_orderOf_eq_one a; rwa [ha] at this
  have hb2 : b ^ 2 = 1 := by have := pow_orderOf_eq_one b; rwa [hb] at this
  have hle := IsCyclic.card_pow_eq_one_le (α := R) (n := 2) (by norm_num)
  have hsub : ({1, a, b} : Finset R) ⊆ Finset.univ.filter (fun x : R => x ^ 2 = 1) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hx with rfl | rfl | rfl <;> simp [*]
  have hcard : ({1, a, b} : Finset R).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair hab]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h => ha1 h.symm, fun h => hb1 h.symm⟩
  have := Finset.card_le_card hsub
  omega

theorem noCommuting_of_isCyclic {R : Type} [Group R] [Finite R] (hc : IsCyclic R) :
    NoCommutingDistinctInvolutions R := fun a b _ =>
  Subtype.ext (cyclic_unique_involution hc a.2 b.2)

theorem noCommuting_of_isQuat {R : Type} [Group R] (h : ∃ n, IVK.IsQuaternionTwoGroup R n) :
    NoCommutingDistinctInvolutions R := by
  obtain ⟨n, -, ⟨e⟩⟩ := h
  have : NeZero (2 ^ (n - 2)) := ⟨pow_ne_zero _ (by norm_num)⟩
  exact no_commuting_distinct_involutions_of_injective e.toMonoidHom e.injective
    (quaternion_no_commuting_distinct_involutions (2 ^ (n - 2)))

theorem pRank_le_one_of_noCommuting {G : Type} [Group G] [Finite G] {Y : Subgroup G}
    (h : NoCommutingDistinctInvolutions ↥Y) : CFSG.pRank 2 ↥Y ≤ 1 := by
  by_contra hgt
  have hgt' : 2 ≤ CFSG.pRank 2 ↥Y := by omega
  rw [CFSG.Foundations.SteinbergCA.pRank_coe_eq_open_pRank Nat.prime_two] at hgt'
  obtain ⟨E, hEY, hE, hcard⟩ := CFSG.GH74.Uniqueness.SU.SU1.exists_pRank (p := 2) one_lt_two Y
  have h4 : 4 ≤ Nat.card E := by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ Open.pRank 2 Y := Nat.pow_le_pow_right (by norm_num) hgt'
  have hne : E ≠ ⊥ := (Subgroup.one_lt_card_iff_ne_bot E).mp (by omega)
  obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hEel := CFSG.GH74.Uniqueness.SU.SU1.isElemAbelian_iff.mp hE
  have ha1 : (a : G) ≠ 1 := fun h' => ha (Subtype.ext h')
  have ha2 : (a : G) ^ 2 = 1 := hEel.2 a a.2
  have hao : orderOf (a : G) = 2 := orderOf_eq_prime ha2 ha1
  have hnle : ¬ E ≤ zpowers (a : G) := by
    intro hle
    have := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers, hao] at this
    omega
  obtain ⟨b, hbE, hbz⟩ : ∃ b ∈ E, b ∉ zpowers (a : G) := by
    by_contra hcon
    push Not at hcon
    exact hnle (fun x hx => hcon x hx)
  have hb1 : b ≠ 1 := fun h' => hbz (h' ▸ Subgroup.one_mem _)
  have hb2 : b ^ 2 = 1 := hEel.2 b hbE
  have hbo : orderOf b = 2 := orderOf_eq_prime hb2 hb1
  have hcomm : (a : G) * b = b * (a : G) := hEel.1 a a.2 b hbE
  let a' : Involution ↥Y := ⟨⟨a, hEY a.2⟩, by rw [Subgroup.orderOf_mk]; exact hao⟩
  let b' : Involution ↥Y := ⟨⟨b, hEY hbE⟩, by rw [Subgroup.orderOf_mk]; exact hbo⟩
  have := h a' b' (Subtype.ext hcomm)
  apply hbz
  have hab : (a : G) = b := congrArg (fun x : Involution ↥Y => (x.1 : G)) this
  rw [← hab]
  exact Subgroup.mem_zpowers _

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.P2S2
