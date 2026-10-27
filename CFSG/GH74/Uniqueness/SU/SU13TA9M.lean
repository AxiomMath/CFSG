module

public import CFSG.GH74.Uniqueness.SU.SU13TA9PermM
public import CFSG.GH74.Uniqueness.SU.SU13TA9P3
public import CFSG.GH74.Uniqueness.SU.SU13TA9F
public import CFSG.GH74.Uniqueness.SU.SU13TB0Syl
public import CFSG.GH74.Uniqueness.SU.SU13TB1Core

public section

namespace CFSG.GH74.Uniqueness.SU.SU13.TA.L9

open Equiv Equiv.Perm Subgroup CFSG.GH74.Uniqueness.SU.SU13.TA CFSG.GH74.Uniqueness.SU.SU13.TB

variable {H : Type} [Group H] {π : H →* alternatingGroup (Fin 9)}

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

theorem card_M0 (hπ : TwoCover π) (c : Cfg π) : Nat.card (M0 c) = 108 := by
  have := hπ.card_centralizer_singleton (odd_orderOf_s₂ c)
  rw [c.π_s₂, card_centralizer_ea_mul_eb] at this
  exact this

theorem t_mem_M0 (hπ : TwoCover π) (c : Cfg π) : c.t ∈ M0 c :=
  mem_M0_of_π_mem_Mb hπ c (by rw [c.π_t]; exact et_mem_Mb)

@[expose] def IsE (π : H →* alternatingGroup (Fin 9)) (E : Subgroup H) : Prop :=
  IsPGroup 3 E ∧ E.map π = Ebar

namespace IsE

variable {E : Subgroup H}

theorem card (hπ : TwoCover π) (hE : IsE π E) : Nat.card E = 27 := by
  rw [← hπ.card_map_of_isPGroup_three hE.1, hE.2, card_Ebar]

theorem odd_orderOf (hE : IsE π E) {y : H} (hy : y ∈ E) : Odd (orderOf y) :=
  TwoCover.odd_orderOf_of_mem_isPGroup_three hE.1 hy

theorem map_mem (hE : IsE π E) {y : H} (hy : y ∈ E) : π y ∈ Ebar :=
  hE.2 ▸ Subgroup.mem_map_of_mem π hy

theorem mem_iff (hπ : TwoCover π) (hE : IsE π E) {y : H} (hy : Odd (orderOf y)) :
    y ∈ E ↔ π y ∈ Ebar := by
  refine ⟨hE.map_mem, fun h => ?_⟩
  have h' : π y ∈ E.map π := hE.2 ▸ h
  obtain ⟨e, he, hey⟩ := h'
  have := hπ.eq_of_odd_orderOf_of_map_eq (hE.odd_orderOf he) hy hey
  rw [← this]
  exact he

theorem le_M0 (hπ : TwoCover π) (c : Cfg π) (hE : IsE π E) : E ≤ M0 c := fun _ hy =>
  mem_M0_of_π_mem_Mb hπ c (Ebar_le_Mb (hE.map_mem hy))

theorem conj_mem (hπ : TwoCover π) (c : Cfg π) (hE : IsE π E) {m e : H} (hm : m ∈ M0 c)
    (he : e ∈ E) : m * e * m⁻¹ ∈ E := by
  have hodd : Odd (orderOf (m * e * m⁻¹)) := by
    rw [← SemiconjBy.orderOf_eq m (show m * e = m * e * m⁻¹ * m by group)]
    exact hE.odd_orderOf he
  rw [hE.mem_iff hπ hodd, map_mul, map_mul, map_inv]
  exact conj_mem_Ebar (π_mem_Mb hm) (hE.map_mem he)

theorem oc_M0 [Finite H] (hπ : TwoCover π) (c : Cfg π) (hE : IsE π E) :
    oc (M0 c) = E := by
  apply le_antisymm
  · intro x hx
    have hxM : x ∈ M0 c := oc_le _ hx
    have hodd : Odd (orderOf x) :=
      Odd.of_dvd_nat (odd_card_oc (M0 c)) (Subgroup.orderOf_dvd_natCard _ hx)
    rw [hE.mem_iff hπ hodd]
    exact mem_Ebar_of_odd_orderOf (π_mem_Mb hxM) (Odd.of_dvd_nat hodd (orderOf_map_dvd π x))
  · refine le_oc_of_normal_odd (hE.le_M0 hπ c) (fun g hg n hn => hE.conj_mem hπ c hg hn) ?_
    rw [hE.card hπ]
    decide

theorem cent_t (hπ : TwoCover π) (c : Cfg π) (hE : IsE π E) {y : H} (hy : y ∈ E)
    (h : c.t * y = y * c.t) : y ∈ zpowers c.s₂ := by
  have hπy : π y ∈ Ebar := hE.map_mem hy
  have hcomm : et * π y = π y * et := by
    have := congrArg π h
    rwa [map_mul, map_mul, c.π_t] at this
  obtain ⟨k, hk⟩ := mem_zpowers_of_commute_et hπy hcomm
  have hπk : π (c.s₂ ^ k) = π y := by rw [map_zpow, c.π_s₂]; exact hk
  have hodd : Odd (orderOf (c.s₂ ^ k)) := by
    have h3 : (c.s₂ ^ k) ^ 3 = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, c.s₂_pow, one_zpow]
    exact Odd.of_dvd_nat (by decide : Odd 3) (orderOf_dvd_of_pow_eq_one h3)
  have := hπ.eq_of_odd_orderOf_of_map_eq hodd (hE.odd_orderOf hy) hπk
  rw [← this]
  exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) _

end IsE

theorem odd_orderOf_s₄ (c : Cfg π) : Odd (orderOf c.s₄) := by
  have hne : c.s₄ ≠ 1 := fun h => by
    have := c.π_s₄
    rw [h, map_one] at this
    exact ea_mul_eb_inv_ne_one this.symm
  have := orderOf_eq_prime (hp := ⟨Nat.prime_three⟩) c.s₄_pow hne
  rw [this]
  decide

namespace IsE

variable {E : Subgroup H}

theorem s₁_mem (hπ : TwoCover π) (c : Cfg π) (hE : IsE π E) : c.s₁ ∈ E :=
  (hE.mem_iff hπ (odd_orderOf_s₁ c)).mpr (by rw [c.π_s₁]; exact ec_mem_Ebar)

theorem s₂_mem (hπ : TwoCover π) (c : Cfg π) (hE : IsE π E) : c.s₂ ∈ E :=
  (hE.mem_iff hπ (odd_orderOf_s₂ c)).mpr (by rw [c.π_s₂]; exact ea_mul_eb_mem_Ebar)

theorem s₄_mem (hπ : TwoCover π) (c : Cfg π) (hE : IsE π E) : c.s₄ ∈ E :=
  (hE.mem_iff hπ (odd_orderOf_s₄ c)).mpr (by rw [c.π_s₄]; exact ea_mul_eb_inv_mem_Ebar)

end IsE

end CFSG.GH74.Uniqueness.SU.SU13.TA.L9
