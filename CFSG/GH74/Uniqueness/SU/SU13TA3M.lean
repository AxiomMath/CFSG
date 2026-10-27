module

public import CFSG.GH74.Uniqueness.SU.SU13TA3PermM
public import CFSG.GH74.Uniqueness.SU.SU13TA3P3
public import CFSG.Dihedral.DisconnectedInvolutionGraph.RankOneQuaternionRecognition

public section

namespace CFSG.GH74.Uniqueness.SU.SU13.TA.L10

open Equiv Equiv.Perm Subgroup CFSG.GH74.Uniqueness.SU.SU13.TA

variable {H : Type} [Group H] {π : H →* alternatingGroup (Fin 10)}

@[expose] def M0 (c : Cfg π) : Subgroup H := centralizer ({c.s₂} : Set H)

theorem mem_M0_iff (c : Cfg π) {m : H} : m ∈ M0 c ↔ m * c.s₂ = c.s₂ * m :=
  Subgroup.mem_centralizer_singleton_iff

theorem π_mem_Mb {c : Cfg π} {m : H} (hm : m ∈ M0 c) : π m ∈ Mb := by
  rw [mem_Mb_iff]
  have h := congrArg π ((mem_M0_iff c).mp hm)
  rw [map_mul, map_mul, c.π_s₂] at h
  exact congrArg Subtype.val h

theorem mem_M0_of_π_mem_Mb (hπ : TwoCover π) (c : Cfg π) {m : H} (hm : π m ∈ Mb) : m ∈ M0 c := by
  rw [mem_M0_iff]
  have h : Commute (π m) (π c.s₂) := by
    rw [c.π_s₂]
    exact Subtype.ext (mem_Mb_iff.mp hm).eq
  exact (hπ.commute_of_odd_orderOf (odd_orderOf_s₂ c) h).eq

theorem card_M0 (hπ : TwoCover π) (c : Cfg π) : Nat.card (M0 c) = 432 := by
  have := hπ.card_centralizer_singleton (odd_orderOf_s₂ c)
  rw [c.π_s₂, card_centralizer_ea_mul_eb] at this
  exact this

theorem s₁_mem_M0 (hπ : TwoCover π) (c : Cfg π) : c.s₁ ∈ M0 c :=
  mem_M0_of_π_mem_Mb hπ c (by rw [c.π_s₁]; exact ec_mem_Mb)

theorem t_mem_M0 (hπ : TwoCover π) (c : Cfg π) : c.t ∈ M0 c :=
  mem_M0_of_π_mem_Mb hπ c (by rw [c.π_t]; exact et_mem_Mb)

theorem exists_O [Finite H] (hπ : TwoCover π) (c : Cfg π) :
    ∃ O : Subgroup H, IsPGroup 3 O ∧ O.map π = Obar ∧ Nat.card O = 9 ∧ O ≤ M0 c ∧
      (∀ m ∈ M0 c, ∀ o ∈ O, m * o * m⁻¹ ∈ O) ∧
      (∀ x ∈ O, c.t * x = x * c.t → x ∈ zpowers c.s₂) := by
  have hO3 : IsPGroup 3 Obar := IsPGroup.of_card (n := 2) (by rw [card_Obar]; norm_num)
  obtain ⟨O, hO, hOmap⟩ := hπ.exists_lift_isPGroup_three hO3
  refine ⟨O, hO, hOmap, ?_, ?_, ?_, ?_⟩
  · rw [← hπ.card_map_of_isPGroup_three hO, hOmap, card_Obar]
  · intro o ho
    refine mem_M0_of_π_mem_Mb hπ c ?_
    exact Obar_le_Mb (hOmap ▸ Subgroup.mem_map_of_mem π ho)
  · intro m hm o ho
    have hw : π (m * o * m⁻¹) ∈ O.map π := by
      rw [hOmap, map_mul, map_mul, map_inv]
      exact conj_mem_Obar (π_mem_Mb hm) (hOmap ▸ Subgroup.mem_map_of_mem π ho)
    obtain ⟨o', ho', hoo'⟩ := hw
    have hodd : Odd (orderOf (m * o * m⁻¹)) := by
      rw [← SemiconjBy.orderOf_eq m (show m * o = m * o * m⁻¹ * m by group)]
      exact TwoCover.odd_orderOf_of_mem_isPGroup_three hO ho
    have := hπ.eq_of_odd_orderOf_of_map_eq (TwoCover.odd_orderOf_of_mem_isPGroup_three hO ho') hodd
      hoo'
    rw [← this]
    exact ho'
  · intro x hx htx
    have hπx : π x ∈ Obar := hOmap ▸ Subgroup.mem_map_of_mem π hx
    have hcomm : et * π x = π x * et := by
      have := congrArg π htx
      rwa [map_mul, map_mul, c.π_t] at this
    obtain ⟨k, hk⟩ := mem_zpowers_of_commute_et hπx hcomm
    have hπk : π (c.s₂ ^ k) = π x := by rw [map_zpow, c.π_s₂]; exact hk
    have hodd : Odd (orderOf (c.s₂ ^ k)) := by
      have h3 : (c.s₂ ^ k) ^ 3 = 1 := by
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, c.s₂_pow, one_zpow]
      exact Odd.of_dvd_nat (by decide : Odd 3) (orderOf_dvd_of_pow_eq_one h3)
    have := hπ.eq_of_odd_orderOf_of_map_eq hodd (TwoCover.odd_orderOf_of_mem_isPGroup_three hO hx)
      hπk
    rw [← this]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) _

@[expose] def Qh (π : H →* alternatingGroup (Fin 10)) : Subgroup H := Vb.comap π

theorem card_Qh (hπ : TwoCover π) : Nat.card (Qh π) = 8 := by
  rw [Qh, hπ.card_comap, card_Vb]

theorem Qh_le_M0 (hπ : TwoCover π) (c : Cfg π) : Qh π ≤ M0 c := fun _ hq =>
  mem_M0_of_π_mem_Mb hπ c (Vb_le_Mb hq)

theorem conj_mem_Qh {c : Cfg π} {m q : H} (hm : m ∈ M0 c) (hq : q ∈ Qh π) : m * q * m⁻¹ ∈ Qh π := by
  show π (m * q * m⁻¹) ∈ Vb
  rw [map_mul, map_mul, map_inv]
  exact conj_mem_Vb (π_mem_Mb hm) hq

theorem sq_of_mem_Qh (hπ : TwoCover π) {z : H} (hz : z ∈ π.ker) (hz1 : z ≠ 1) {q : H}
    (hq : q ∈ Qh π) (hqk : q ∉ π.ker) : q ^ 2 = z := by
  have hπq : π q ≠ 1 := fun h => hqk h
  obtain ⟨hk, h1⟩ := hπ.sq_mem_ker_ne_one_of_cycleType_two_two (by norm_num) (x := q)
    (cycleType_Vb hq hπq)
  exact hπ.eq_of_mem_ker_ne_one' hk hz h1 hz1

theorem pow_four_of_mem_Qh (hπ : TwoCover π) {z : H} (hz : z ∈ π.ker) (hz1 : z ≠ 1) {q : H}
    (hq : q ∈ Qh π) : q ^ 4 = 1 := by
  have hz2 : z ^ 2 = 1 := hπ.sq_eq_one_of_mem_ker' hz
  by_cases hqk : q ∈ π.ker
  · have := hπ.sq_eq_one_of_mem_ker' hqk
    rw [show 4 = 2 * 2 from rfl, pow_mul, this, one_pow]
  · rw [show 4 = 2 * 2 from rfl, pow_mul, sq_of_mem_Qh hπ hz hz1 hq hqk, hz2]

theorem nonempty_mulEquiv_Qh [Finite H] (hπ : TwoCover π) {z : H} (hz : z ∈ π.ker) (hz1 : z ≠ 1) :
    Nonempty (QuaternionGroup 2 ≃* Qh π) := by
  have hz2 : z ^ 2 = 1 := hπ.sq_eq_one_of_mem_ker' hz
  have hq4 : ∀ q ∈ Qh π, q ^ 4 = 1 := fun q hq => pow_four_of_mem_Qh hπ hz hz1 hq
  have huniq : ∀ q ∈ Qh π, orderOf q = 2 → q = z := by
    intro q hq hq2
    have hq1 : q ≠ 1 := fun h => by rw [h, orderOf_one] at hq2; omega
    by_cases hqk : q ∈ π.ker
    · exact hπ.eq_of_mem_ker_ne_one' hqk hz hq1 hz1
    · exfalso
      have hsq := sq_of_mem_Qh hπ hz hz1 hq hqk
      have : q ^ 2 = 1 := by rw [← hq2]; exact pow_orderOf_eq_one q
      rw [hsq] at this
      exact hz1 (by simpa [hz2] using this)
  have hrank : CFSG.DisconnectedInvolutionGraph.Helpers.NoCommutingDistinctInvolutions ↥(Qh π) :=
    fun a b _ => Subtype.ext (Subtype.ext
      ((huniq a.1.1 a.1.2 (by rw [Subgroup.orderOf_coe]; exact a.2)).trans
        (huniq b.1.1 b.1.2 (by rw [Subgroup.orderOf_coe]; exact b.2)).symm))
  have hpg : IsPGroup 2 ↥(Qh π) := IsPGroup.of_card (n := 3) (by rw [card_Qh hπ]; norm_num)
  rcases CFSG.DisconnectedInvolutionGraph.Helpers.rank_one_two_cyclic_or_quaternion hpg hrank with
    hcyc | ⟨k, hk, ⟨e⟩⟩
  · exfalso
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥(Qh π))
    have hord : orderOf g = 8 := by
      rw [orderOf_eq_card_of_forall_mem_zpowers hg, card_Qh hπ]
    have h4 : (g : H) ^ 4 = 1 := hq4 g g.2
    have : orderOf (g : H) ∣ 4 := orderOf_dvd_of_pow_eq_one h4
    rw [Subgroup.orderOf_coe, hord] at this
    omega
  · have hcard : Nat.card (QuaternionGroup (2 ^ k)) = 8 := by
      rw [Nat.card_congr e.toEquiv, card_Qh hπ]
    rw [Nat.card_eq_fintype_card, QuaternionGroup.card] at hcard
    have : 2 ^ k = 2 := by omega
    have hk1 : k = 1 := by
      have := Nat.pow_right_injective (le_refl 2) (show 2 ^ k = 2 ^ 1 by omega)
      exact this
    subst hk1
    exact ⟨e⟩

theorem ec_conj_ev1_not_mem_Obar : (ec * ev1 * ec⁻¹)⁻¹ * ev1 ∉ Obar := by
  intro h
  have h6 := (mem_AS_iff.mp h.2).1
  revert h6
  decide

theorem exists_q_comm_not_mem_O (hπ : TwoCover π) (c : Cfg π) {O : Subgroup H}
    (hOmap : O.map π = Obar) : ∃ q ∈ Qh π, (c.s₁ * q * c.s₁⁻¹)⁻¹ * q ∉ O := by
  obtain ⟨q, hq⟩ := hπ.surj ev1
  refine ⟨q, show π q ∈ Vb by rw [hq]; exact mem_Vb_iff.mpr (Or.inr (Or.inl rfl)), fun h => ?_⟩
  have h2 : π ((c.s₁ * q * c.s₁⁻¹)⁻¹ * q) ∈ Obar := hOmap ▸ Subgroup.mem_map_of_mem π h
  rw [map_mul, map_inv, map_mul, map_mul, map_inv, c.π_s₁, hq] at h2
  exact ec_conj_ev1_not_mem_Obar h2

end CFSG.GH74.Uniqueness.SU.SU13.TA.L10
