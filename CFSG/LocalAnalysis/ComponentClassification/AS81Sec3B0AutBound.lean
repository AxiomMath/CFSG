module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3B0Model
public import CFSG.LocalAnalysis.ComponentClassification.PerfectAutomorphisms

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81.SuzB0

open Subgroup CFSG.Open

theorem two_pow_lt (i : Fin 6) : 2 ^ (i : ℕ) < 64 :=
  calc 2 ^ (i : ℕ) < 2 ^ 6 := Nat.pow_lt_pow_right (by norm_num) i.2
    _ = 64 := by norm_num

namespace Coord

variable {H : Type} [Group H] {t : H} {q : ℕ → H} (C : Coord t q)
include C

local notation "ψ" => psi (t := t) (q := q)

theorem t_comm {y : H} (hy : y ∈ C.Q) : t * y = y * t :=
  (C.forall_comm_iff C.t_mem).mpr (mem_zpowers t) y hy

theorem psi_t : ψ t = 0 := (C.psi_ker' t C.t_mem).mpr (mem_zpowers t)

theorem eq_one_or_eq_t_of_mem_zpowers {x : H} (hx : x ∈ zpowers t) : x = 1 ∨ x = t := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
  rw [← zpow_mod_orderOf, C.orderOf_t]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [Nat.cast_ofNat, h, zpow_zero]
  · right
    rw [Nat.cast_ofNat, h, zpow_one]

theorem eq_or_eq_mul_t_of_psi_eq {x y : H} (hx : x ∈ C.Q) (hy : y ∈ C.Q) (h : ψ x = ψ y) :
    x = y ∨ x = y * t := by
  rcases C.eq_one_or_eq_t_of_mem_zpowers
      ((Sec2.psi_eq_iff C.psi_add' C.psi_ker' hx hy).mp h) with h1 | h1
  · exact Or.inl (mul_inv_eq_one.mp h1)
  · right
    rw [← C.t_comm hy, ← h1, inv_mul_cancel_right]

theorem mulAut_apply_t (φ : MulAut ↥C.Q) : ((φ ⟨t, C.t_mem⟩ : ↥C.Q) : H) = t := by
  have hz : ((φ ⟨t, C.t_mem⟩ : ↥C.Q) : H) ∈ zpowers t := by
    refine (C.forall_comm_iff (φ ⟨t, C.t_mem⟩).2).mp fun y hy => ?_
    obtain ⟨y', hy'⟩ := φ.surjective ⟨y, hy⟩
    have hyy : y = ((φ y' : ↥C.Q) : H) := (congrArg Subtype.val hy').symm
    have h1 : (⟨t, C.t_mem⟩ : ↥C.Q) * y' = y' * ⟨t, C.t_mem⟩ := Subtype.ext (C.t_comm y'.2)
    have h2 := congrArg (fun z : ↥C.Q => (z : H)) (congrArg φ h1)
    simp only [map_mul, Subgroup.coe_mul] at h2
    rw [hyy]
    exact h2
  rcases C.eq_one_or_eq_t_of_mem_zpowers hz with h | h
  · exfalso
    apply C.t_ne
    have h1 : φ ⟨t, C.t_mem⟩ = 1 := Subtype.ext h
    rw [← map_one φ] at h1
    exact congrArg Subtype.val (φ.injective h1)
  · exact h

@[expose] noncomputable def lift (u : Fin 6 → ZMod 2) : H := Classical.choose (C.psi_surj u)

theorem lift_mem (u : Fin 6 → ZMod 2) : C.lift u ∈ C.Q := (Classical.choose_spec (C.psi_surj u)).1

theorem psi_lift (u : Fin 6 → ZMod 2) : ψ (C.lift u) = u :=
  (Classical.choose_spec (C.psi_surj u)).2

@[expose] noncomputable def autVec (φ : MulAut ↥C.Q) (u : Fin 6 → ZMod 2) : Fin 6 → ZMod 2 :=
  ψ ((φ ⟨C.lift u, C.lift_mem u⟩ : ↥C.Q) : H)

theorem autVec_psi (φ : MulAut ↥C.Q) {a : H} (ha : a ∈ C.Q) :
    C.autVec φ (ψ a) = ψ ((φ ⟨a, ha⟩ : ↥C.Q) : H) := by
  unfold autVec
  rcases C.eq_or_eq_mul_t_of_psi_eq (C.lift_mem (ψ a)) ha (C.psi_lift _) with h | h
  · have e : (⟨C.lift (ψ a), C.lift_mem _⟩ : ↥C.Q) = ⟨a, ha⟩ := Subtype.ext h
    rw [e]
  · have e : (⟨C.lift (ψ a), C.lift_mem _⟩ : ↥C.Q) = ⟨a, ha⟩ * ⟨t, C.t_mem⟩ := Subtype.ext h
    rw [e, map_mul, Subgroup.coe_mul, C.psi_mul (φ _).2 (φ _).2, C.mulAut_apply_t, C.psi_t,
      add_zero]

theorem autVec_add (φ : MulAut ↥C.Q) (u w : Fin 6 → ZMod 2) :
    C.autVec φ (u + w) = C.autVec φ u + C.autVec φ w := by
  obtain ⟨a, ha, rfl⟩ := C.psi_surj u
  obtain ⟨b, hb, rfl⟩ := C.psi_surj w
  rw [← C.psi_mul ha hb, C.autVec_psi φ (C.Q.mul_mem ha hb), C.autVec_psi φ ha,
    C.autVec_psi φ hb, show (⟨a * b, C.Q.mul_mem ha hb⟩ : ↥C.Q) = ⟨a, ha⟩ * ⟨b, hb⟩ from rfl,
    map_mul, Subgroup.coe_mul, C.psi_mul (φ _).2 (φ _).2]

theorem autVec_inv_autVec (φ : MulAut ↥C.Q) (u : Fin 6 → ZMod 2) :
    C.autVec φ⁻¹ (C.autVec φ u) = u := by
  obtain ⟨a, ha, rfl⟩ := C.psi_surj u
  rw [C.autVec_psi φ ha, C.autVec_psi φ⁻¹ (φ ⟨a, ha⟩).2]
  simp

@[expose] noncomputable def autLin (φ : MulAut ↥C.Q) :
    (Fin 6 → ZMod 2) ≃ₗ[ZMod 2] (Fin 6 → ZMod 2) where
  toFun := C.autVec φ
  invFun := C.autVec φ⁻¹
  map_add' := C.autVec_add φ
  map_smul' r u := by
    rcases CFSG.RankThree.Literature.FSmith.zmod2_eq_zero_or_eq_one r with rfl | rfl
    · rw [zero_smul, RingHom.id_apply, zero_smul, ← Sec2.psi_one C.psi_add',
        C.autVec_psi φ C.Q.one_mem, show (⟨1, C.Q.one_mem⟩ : ↥C.Q) = 1 from rfl, map_one,
        Subgroup.coe_one]
    · rw [one_smul, RingHom.id_apply, one_smul]
  left_inv := C.autVec_inv_autVec φ
  right_inv u := by
    have h := C.autVec_inv_autVec φ⁻¹ u
    rwa [inv_inv] at h

theorem autLin_apply (φ : MulAut ↥C.Q) (u : Fin 6 → ZMod 2) : C.autLin φ u = C.autVec φ u := rfl

theorem autLin_mem_orthogonalGroup (φ : MulAut ↥C.Q) :
    C.autLin φ ∈ TauCeti.QuadraticMap.orthogonalGroup Sec2Omega.qMinusForm := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro u
  obtain ⟨a, ha, rfl⟩ := C.psi_surj u
  rw [C.autLin_apply, C.autVec_psi φ ha, Sec2Omega.qMinusForm_apply, Sec2Omega.qMinusForm_apply]
  have h3 : ((φ ⟨a, ha⟩ : ↥C.Q) : H) * ((φ ⟨a, ha⟩ : ↥C.Q) : H) = 1 ↔ a * a = 1 := by
    rw [← Subgroup.coe_mul, ← map_mul, OneMemClass.coe_eq_one, map_eq_one_iff φ φ.injective]
    constructor
    · intro h
      exact congrArg Subtype.val h
    · intro h
      exact Subtype.ext h
  have key := (C.mul_self_eq_one_iff (φ ⟨a, ha⟩).2).symm.trans (h3.trans (C.mul_self_eq_one_iff ha))
  rcases CFSG.RankThree.Literature.FSmith.zmod2_eq_zero_or_eq_one (qMinus (ψ a)) with h | h <;>
    rcases CFSG.RankThree.Literature.FSmith.zmod2_eq_zero_or_eq_one
      (qMinus (ψ ((φ ⟨a, ha⟩ : ↥C.Q) : H))) with h' | h'
  · rw [h, h']
  · exact absurd (key.mpr h) (by rw [h']; exact one_ne_zero)
  · exact absurd (key.mp h') (by rw [h]; exact one_ne_zero)
  · rw [h, h']

open scoped Classical in
noncomputable def autBits (φ : MulAut ↥C.Q) (i : Fin 6) : Bool :=
  decide (((φ ⟨q (2 ^ (i : ℕ)), C.q_mem (two_pow_lt i)⟩ : ↥C.Q) : H) =
    C.lift (C.autVec φ (bitVec (2 ^ (i : ℕ)))))

theorem eq_on_q_of_eq_on_gens {φ φ' : MulAut ↥C.Q}
    (h : ∀ i < 6, ∀ hi : q (2 ^ i) ∈ C.Q, φ ⟨q (2 ^ i), hi⟩ = φ' ⟨q (2 ^ i), hi⟩) :
    ∀ v < 64, ∀ hv : q v ∈ C.Q, φ ⟨q v, hv⟩ = φ' ⟨q v, hv⟩ := by
  have ht : φ ⟨t, C.t_mem⟩ = φ' ⟨t, C.t_mem⟩ := Subtype.ext (by
    rw [C.mulAut_apply_t, C.mulAut_apply_t])
  intro v
  induction v using Nat.strong_induction_on with
  | _ v ih =>
    intro hv hvQ
    by_cases hv0 : v = 0
    · subst hv0
      have e : (⟨q 0, hvQ⟩ : ↥C.Q) = 1 := Subtype.ext C.q_zero
      rw [e, map_one, map_one]
    · obtain ⟨i, hi, hlt⟩ := exists_xor_lt v hv hv0
      have hi64 : 2 ^ i < 64 := two_pow_lt ⟨i, hi⟩
      have hw : 2 ^ i ^^^ v < 64 := xor_lt hi64 hv
      have hmul := C.mul (2 ^ i) hi64 (2 ^ i ^^^ v) hw
      rw [xor_xor_cancel] at hmul
      have e : (⟨q (2 ^ i), C.q_mem hi64⟩ : ↥C.Q) * ⟨q (2 ^ i ^^^ v), C.q_mem hw⟩ =
          ⟨q v, hvQ⟩ * ⟨t, C.t_mem⟩ ^ gammaBit (2 ^ i) (2 ^ i ^^^ v) := Subtype.ext (by
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_pow, hmul])
      have e1 := congrArg φ e
      have e2 := congrArg φ' e
      rw [map_mul, map_mul, map_pow] at e1 e2
      rw [h i hi, ih _ hlt hw, ht] at e1
      rw [e1] at e2
      exact mul_right_cancel e2

theorem autLinBits_injective {φ φ' : MulAut ↥C.Q} (hL : C.autLin φ = C.autLin φ')
    (hB : C.autBits φ = C.autBits φ') : φ = φ' := by
  have hV : ∀ u, C.autVec φ u = C.autVec φ' u := fun u => by
    rw [← C.autLin_apply, ← C.autLin_apply, hL]
  have hgen : ∀ i < 6, ∀ hi : q (2 ^ i) ∈ C.Q, φ ⟨q (2 ^ i), hi⟩ = φ' ⟨q (2 ^ i), hi⟩ := by
    intro i hi hiQ
    have hb := congrFun hB ⟨i, hi⟩
    simp only [autBits, decide_eq_decide] at hb
    have hi64 := two_pow_lt ⟨i, hi⟩
    set u := C.autVec φ (bitVec (2 ^ i)) with hu
    have hψ : ψ ((φ ⟨q (2 ^ i), hiQ⟩ : ↥C.Q) : H) = u := by
      rw [← C.autVec_psi φ hiQ, C.psi_q hi64]
    have hψ' : ψ ((φ' ⟨q (2 ^ i), hiQ⟩ : ↥C.Q) : H) = u := by
      rw [← C.autVec_psi φ' hiQ, C.psi_q hi64, ← hV]
    rw [← hV] at hb
    apply Subtype.ext
    have hne : C.lift u * t ≠ C.lift u := fun h => C.t_ne (by
      simpa using h)
    rcases C.eq_or_eq_mul_t_of_psi_eq (φ _).2 (C.lift_mem u)
        (hψ.trans (C.psi_lift u).symm) with h1 | h1 <;>
      rcases C.eq_or_eq_mul_t_of_psi_eq (φ' _).2 (C.lift_mem u)
        (hψ'.trans (C.psi_lift u).symm) with h2 | h2
    · rw [h1, h2]
    · exact absurd (h2.symm.trans (hb.mp h1)) hne
    · exact absurd (h1.symm.trans (hb.mpr h2)) hne
    · rw [h1, h2]
  have hq := C.eq_on_q_of_eq_on_gens hgen
  have ht : φ ⟨t, C.t_mem⟩ = φ' ⟨t, C.t_mem⟩ := Subtype.ext (by
    rw [C.mulAut_apply_t, C.mulAut_apply_t])
  refine MulEquiv.ext fun x => ?_
  obtain ⟨v, hv, a, -, hx⟩ := C.mem_Q_iff.mp x.2
  have e : x = ⟨q v, C.q_mem hv⟩ * ⟨t, C.t_mem⟩ ^ a := Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_pow]
    exact hx)
  rw [e, map_mul, map_mul, map_pow, map_pow, hq v hv, ht]

theorem card_mulAut_le
    (hO : Nat.card (TauCeti.QuadraticMap.orthogonalGroup Sec2Omega.qMinusForm) = 51840) :
    Nat.card (MulAut ↥C.Q) ≤ 3317760 := by
  have : Finite (TauCeti.QuadraticMap.orthogonalGroup Sec2Omega.qMinusForm) :=
    Nat.finite_of_card_ne_zero (by rw [hO]; norm_num)
  let f : MulAut ↥C.Q →
      ↥(TauCeti.QuadraticMap.orthogonalGroup Sec2Omega.qMinusForm) × (Fin 6 → Bool) :=
    fun φ => (⟨C.autLin φ, C.autLin_mem_orthogonalGroup φ⟩, C.autBits φ)
  have hf : Function.Injective f := fun φ φ' h =>
    C.autLinBits_injective (congrArg Subtype.val (Prod.ext_iff.mp h).1) (Prod.ext_iff.mp h).2
  calc Nat.card (MulAut ↥C.Q)
      ≤ Nat.card (↥(TauCeti.QuadraticMap.orthogonalGroup Sec2Omega.qMinusForm) ×
          (Fin 6 → Bool)) := Nat.card_le_card_of_injective f hf
    _ = 3317760 := by
      rw [Nat.card_prod, hO, Nat.card_eq_fintype_card (α := Fin 6 → Bool), Fintype.card_fun,
        Fintype.card_bool, Fintype.card_fin]
      norm_num

end Coord

open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four CFSG.Sporadic.SuzOddCore

theorem card_orthogonalGroup_qMinusForm :
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup Sec2Omega.qMinusForm) = 51840 := by
  obtain ⟨hcardΩ, hidx, -, -⟩ := omega_facts b0_parts.2.2.2.2.2.2
  set O := TauCeti.QuadraticMap.orthogonalGroup Sec2Omega.qMinusForm with hOdef
  have hΩO : timmesfeldOmega qMinus ≤ O := by
    rw [Sec2Omega.timmesfeldOmega_qMinus, commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    exact O.mul_mem (O.mul_mem (O.mul_mem ha hb) (O.inv_mem ha)) (O.inv_mem hb)
  have h := ((timmesfeldOmega qMinus).subgroupOf O).card_mul_index
  rw [hidx, Nat.card_congr (subgroupOfEquivOfLe hΩO).toEquiv, hcardΩ] at h
  omega

theorem card_mulAut_Q_le :
    Nat.card (MulAut ↥coord_qVec.Q) ≤ 3317760 :=
  coord_qVec.card_mulAut_le card_orthogonalGroup_qMinusForm

theorem card_invE_one :
    Nat.card ↥(invE 1) = 3317760 := by
  rw [card_invE (by norm_num)]
  rfl

theorem mem_zpowers_of_commute_Q
    {z : ↥(invE 1)} (hz : ∀ a ∈ coord_qVec.Q, (z : Equiv.Perm (Fin 1782)) * a = a * z) :
    (z : Equiv.Perm (Fin 1782)) ∈ zpowers (suzInv 1) := by
  have hρ : rho1 z = 1 := by
    refine LinearEquiv.ext fun u => ?_
    obtain ⟨a, ha, rfl⟩ := coord_qVec.psi_surj u
    rw [show rho1 z = coord_qVec.rho invE_le z from rfl, coord_qVec.rho_psi invE_le z ha,
      hz a ha, mul_inv_cancel_right]
    rfl
  have hzQ : (z : Equiv.Perm (Fin 1782)) ∈ coord_qVec.Q := by
    have : z ∈ rho1.ker := hρ
    rw [ker_rho1, mem_subgroupOf] at this
    exact this
  exact (coord_qVec.forall_comm_iff hzQ).mp hz

theorem mem_center_invE_one_iff
    {z : ↥(invE 1)} :
    z ∈ center ↥(invE 1) ↔ (z : Equiv.Perm (Fin 1782)) ∈ zpowers (suzInv 1) := by
  constructor
  · intro hz
    refine mem_zpowers_of_commute_Q fun a ha => ?_
    have h := congrArg Subtype.val (mem_center_iff.mp hz ⟨a, Q_le_invE ha⟩)
    exact h.symm
  · intro hz
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hz
    rw [mem_center_iff]
    intro g
    have hgt : (g : Equiv.Perm (Fin 1782)) * suzInv 1 = suzInv 1 * g :=
      mem_centralizer_singleton_iff.mp (invE_le g.2).2
    apply Subtype.ext
    show (g : Equiv.Perm (Fin 1782)) * (z : Equiv.Perm (Fin 1782)) =
      (z : Equiv.Perm (Fin 1782)) * (g : Equiv.Perm (Fin 1782))
    rw [← hk]
    exact (Commute.zpow_right hgt k).eq

theorem card_center_invE_one :
    Nat.card (center ↥(invE 1)) = 2 := by
  have h : center ↥(invE 1) = (zpowers (suzInv 1)).subgroupOf (invE 1) := by
    ext z
    rw [mem_center_invE_one_iff, mem_subgroupOf]
  rw [h, Nat.card_congr (subgroupOfEquivOfLe (zpowers_le.mpr suzInv_mem_invE)).toEquiv,
    Nat.card_zpowers, coord_qVec.orderOf_t]

theorem card_range_conj_invE_one :
    Nat.card (MulAut.conj : ↥(invE 1) →* MulAut ↥(invE 1)).range = 1658880 := by
  have hker : (MulAut.conj : ↥(invE 1) →* MulAut ↥(invE 1)).ker = center ↥(invE 1) := by
    ext g
    rw [MonoidHom.mem_ker, mem_center_iff]
    constructor
    · intro h x
      have hx := DFunLike.congr_fun h x
      rw [MulAut.conj_apply, MulAut.one_apply] at hx
      calc x * g = g * x * g⁻¹ * g := by rw [hx]
        _ = g * x := by group
    · intro h
      refine MulEquiv.ext fun x => ?_
      rw [MulAut.conj_apply, MulAut.one_apply, ← h x, mul_inv_cancel_right]
  have h := Subgroup.card_ker_mul_card_range (MulAut.conj : ↥(invE 1) →* MulAut ↥(invE 1))
  rw [hker, card_center_invE_one, card_invE_one] at h
  omega

theorem map_Q_invE_one
    (α : MulAut ↥(invE 1)) :
    (coord_qVec.Q.subgroupOf (invE 1)).map α.toMonoidHom = coord_qVec.Q.subgroupOf (invE 1) := by
  set Qc := coord_qVec.Q.subgroupOf (invE 1) with hQc
  have hN : Qc.Normal := by
    rw [hQc, ← ker_rho1]
    exact rho1.normal_ker
  set N := Qc.map α.toMonoidHom with hNdef
  have hNn : N.Normal := hN.map α.toMonoidHom α.surjective
  have hcardQc : Nat.card Qc = 128 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe Q_le_invE).toEquiv, coord_qVec.card_Q]
  have hcardN : Nat.card N = 128 := by
    rw [hNdef, card_map_of_injective α.injective, hcardQc]
  have hsimple := (omega_facts b0_parts.2.2.2.2.2.2).2.2.1
  rw [← range_rho1] at hsimple
  have hM : (N.map rho1.rangeRestrict).Normal := hNn.map _ rho1.rangeRestrict_surjective
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map rho1.rangeRestrict) with h | h
  · have hle : N ≤ Qc := by
      rw [Subgroup.map_eq_bot_iff, MonoidHom.ker_rangeRestrict, ker_rho1] at h
      exact h
    exact eq_of_le_of_card_ge hle (by rw [hcardN, hcardQc])
  · exfalso
    have h1 : Nat.card (N.map rho1.rangeRestrict) = 25920 := by
      rw [h, card_top, card_range_rho1]
    have h2 := Nat.le_of_dvd (by rw [hcardN]; norm_num) (card_map_dvd (H := N) rho1.rangeRestrict)
    rw [h1, hcardN] at h2
    norm_num at h2

@[expose] noncomputable def restrictQ
    (α : MulAut ↥(invE 1)) : MulAut ↥coord_qVec.Q :=
  ((subgroupOfEquivOfLe Q_le_invE).symm.trans ((α.subgroupMap _).trans
    (MulEquiv.subgroupCongr (map_Q_invE_one α)))).trans (subgroupOfEquivOfLe Q_le_invE)

theorem restrictQ_apply
    (α : MulAut ↥(invE 1)) (y : ↥coord_qVec.Q) :
    ((restrictQ α y : ↥coord_qVec.Q) : Equiv.Perm (Fin 1782)) =
      ((α ⟨y, Q_le_invE y.2⟩ : ↥(invE 1)) : Equiv.Perm (Fin 1782)) :=
  rfl

theorem restrictQ_injective
    {α β : MulAut ↥(invE 1)} (h : restrictQ α = restrictQ β) :
    α = β := by
  set γ := β⁻¹ * α with hγ
  have hfix : ∀ y : ↥(invE 1), (y : Equiv.Perm (Fin 1782)) ∈ coord_qVec.Q → γ y = y := by
    intro y hy
    have h1 := congrArg (fun φ : MulAut ↥coord_qVec.Q => ((φ ⟨y, hy⟩ : ↥coord_qVec.Q) :
      Equiv.Perm (Fin 1782))) h
    simp only [restrictQ_apply] at h1
    have h2 : α y = β y := Subtype.ext h1
    rw [hγ, MulAut.mul_apply, h2, MulAut.inv_apply, MulEquiv.symm_apply_apply]
  have hcentral : ∀ c : ↥(invE 1), c⁻¹ * γ.toMonoidHom c ∈ center ↥(invE 1) := by
    intro c
    set z := c⁻¹ * γ c with hz
    have hzQ : ∀ a ∈ coord_qVec.Q, (z : Equiv.Perm (Fin 1782)) * a = a * z := by
      intro a ha
      have hca : (c : Equiv.Perm (Fin 1782)) * a * (c : Equiv.Perm (Fin 1782))⁻¹ ∈ coord_qVec.Q :=
        coord_qVec.conj_mem_Q invE_le c ha
      have e1 := hfix (c * ⟨a, Q_le_invE ha⟩ * c⁻¹) hca
      rw [map_mul, map_mul, map_inv, hfix ⟨a, Q_le_invE ha⟩ ha] at e1
      have e2 := congrArg (fun x : ↥(invE 1) => (x : Equiv.Perm (Fin 1782))) e1
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at e2
      rw [hz, Subgroup.coe_mul, Subgroup.coe_inv]
      calc (c : Equiv.Perm (Fin 1782))⁻¹ * (γ c : Equiv.Perm (Fin 1782)) * a
          = (c : Equiv.Perm (Fin 1782))⁻¹ * ((γ c : Equiv.Perm (Fin 1782)) * a *
              (γ c : Equiv.Perm (Fin 1782))⁻¹) * (γ c : Equiv.Perm (Fin 1782)) := by group
        _ = (c : Equiv.Perm (Fin 1782))⁻¹ * ((c : Equiv.Perm (Fin 1782)) * a *
              (c : Equiv.Perm (Fin 1782))⁻¹) * (γ c : Equiv.Perm (Fin 1782)) := by rw [e2]
        _ = a * ((c : Equiv.Perm (Fin 1782))⁻¹ * (γ c : Equiv.Perm (Fin 1782))) := by group
    exact mem_center_invE_one_iff.mpr (mem_zpowers_of_commute_Q hzQ)
  have : Group.IsPerfect ↥(invE 1) := ⟨invE_one_perfect⟩
  have hid := PerfectAutomorphisms.hom_eq_id_of_central_displacement γ.toMonoidHom hcentral
  have hγ1 : γ = 1 := MulEquiv.ext fun x => by
    have := DFunLike.congr_fun hid x
    simpa using this
  rw [hγ] at hγ1
  exact (inv_mul_eq_one.mp hγ1).symm

theorem card_mulAut_invE_one_le :
    Nat.card (MulAut ↥(invE 1)) ≤ 3317760 := by
  have : Finite (MulAut ↥coord_qVec.Q) :=
    Finite.of_injective (fun φ : MulAut ↥coord_qVec.Q => (φ : ↥coord_qVec.Q ≃ ↥coord_qVec.Q))
      fun φ ψ h => MulEquiv.ext fun x => congrFun (congrArg DFunLike.coe h) x
  exact (Nat.card_le_card_of_injective restrictQ fun α β h => restrictQ_injective h).trans
    card_mulAut_Q_le

end CFSG.ComponentClassification.AS81.SuzB0
