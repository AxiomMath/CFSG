module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCorePAction
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCorePAlt

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open CFSG.Open
open Equiv

variable {X : Type} [Group X] [Finite X] {Y : Subgroup X} {e v : X} {L : Subgroup X}

namespace OneComponent

theorem nonempty_inf_mulEquiv_quaternion (hL : OneComponent Y e v L)
    (hZ : Nat.card (Subgroup.center L) = 2)
    (eA : L ⧸ Subgroup.center L ≃* alternatingGroup (Fin 5)) (T : Sylow 2 X) :
    Nonempty (((T : Subgroup X) ⊓ L : Subgroup X) ≃* QuaternionGroup 2) := by
  obtain ⟨S, hS⟩ := hL.exists_sylow_map_eq T
  obtain ⟨φ⟩ := nonempty_sylow_mulEquiv_quaternion_of_alternating hL.perfect hZ eA S
  exact ⟨(MulEquiv.subgroupCongr hS.symm).trans
    (((S : Subgroup L).equivMapOfInjective L.subtype L.subtype_injective).symm.trans φ)⟩

theorem mem_sup_of_mem_sup (hL : OneComponent Y e v L) (hZ : Nat.card (Subgroup.center L) = 2)
    (T : Sylow 2 X) {t : X} (htT : t ∈ (T : Subgroup X))
    (ht : t ∈ L ⊔ Subgroup.centralizer (L : Set X)) :
    t ∈ ((T : Subgroup X) ⊓ L) ⊔ ((T : Subgroup X) ⊓ Subgroup.centralizer (L : Set X)) := by
  obtain ⟨l, hl, k, hk, rfl⟩ := hL.exists_mul_eq_of_mem_sup hZ T htT ht
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hl) (Subgroup.mem_sup_right hk)

theorem inv_mul_mem_sup (hL : OneComponent Y e v L) (hZ : Nat.card (Subgroup.center L) = 2)
    (eA : L ⧸ Subgroup.center L ≃* alternatingGroup (Fin 5)) (T : Sylow 2 X) {a b : X}
    (haT : a ∈ (T : Subgroup X)) (hbT : b ∈ (T : Subgroup X))
    (ha : a ∉ ((T : Subgroup X) ⊓ L) ⊔ ((T : Subgroup X) ⊓ Subgroup.centralizer (L : Set X)))
    (hb : b ∉ ((T : Subgroup X) ⊓ L) ⊔ ((T : Subgroup X) ⊓ Subgroup.centralizer (L : Set X))) :
    a⁻¹ * b ∈ ((T : Subgroup X) ⊓ L) ⊔ ((T : Subgroup X) ⊓ Subgroup.centralizer (L : Set X)) := by
  have := hL.normal
  have hsa := sign_eq_neg_one_of_not_mem hL.perfect eA
    (fun h => ha (hL.mem_sup_of_mem_sup hZ T haT h))
  have hsb := sign_eq_neg_one_of_not_mem hL.perfect eA
    (fun h => hb (hL.mem_sup_of_mem_sup hZ T hbT h))
  refine hL.mem_sup_of_mem_sup hZ T ((T : Subgroup X).mul_mem ((T : Subgroup X).inv_mem haT) hbT)
    (mem_sup_centralizer_of_sign hL.perfect eA ?_)
  rw [map_mul, map_inv, map_mul, map_inv, hsa, hsb]
  decide

abbrev barOf (L : Subgroup X) {x : X} (hx : x ∈ L) : L ⧸ Subgroup.center L :=
  ((⟨x, hx⟩ : L) : L ⧸ Subgroup.center L)

theorem exists_moved (hL : OneComponent Y e v L) (hc : BaseConfig Y e)
    (hZ : Nat.card (Subgroup.center L) = 2)
    (eA : L ⧸ Subgroup.center L ≃* alternatingGroup (Fin 5)) (T : Sylow 2 X) {y : X}
    (hyT : y ∈ (T : Subgroup X))
    (hy : y ∉ ((T : Subgroup X) ⊓ L) ⊔ ((T : Subgroup X) ⊓ Subgroup.centralizer (L : Set X))) :
    ∃ m ∈ (T : Subgroup X) ⊓ L, y * m * y⁻¹ ≠ m ∧ y * m * y⁻¹ ≠ m * e := by
  have := hL.normal
  by_contra hall
  push Not at hall
  obtain ⟨φ⟩ := hL.nonempty_inf_mulEquiv_quaternion hZ eA T
  have heQ : e ∈ (T : Subgroup X) ⊓ L := ⟨hc.mem_sylow T, hL.mem⟩
  obtain ⟨q₁, hq₁, q₂, hq₂, h11, h22, h21, h21e⟩ := quaternion_exists_pair φ heQ hc.order
  have heZ : barOf L hL.mem = 1 := (QuotientGroup.eq_one_iff _).mpr (hL.mem_center hc)
  have hbar_mul : ∀ {x x' : X} (hx : x ∈ L) (hx' : x' ∈ L),
      barOf L (L.mul_mem hx hx') = barOf L hx * barOf L hx' := fun _ _ => rfl
  have hsq : ∀ {x : X} (hx : x ∈ L), x * x = e → barOf L hx * barOf L hx = 1 := by
    intro x hx hxx
    rw [← hbar_mul]
    convert heZ using 3
  have hne1 : ∀ {x : X} (hx : x ∈ L), x * x = e → barOf L hx ≠ 1 := by
    intro x hx hxx h
    rcases hL.eq_one_or_eq_of_card_two hc hZ ((QuotientGroup.eq_one_iff _).mp h) with h' | h'
    · have h1 : x = 1 := congrArg Subtype.val h'
      rw [h1, mul_one] at hxx
      have h2 := hc.order
      rw [← hxx, orderOf_one] at h2
      exact absurd h2 (by decide)
    · have h1 : x = e := h'
      rw [h1, hc.mul_self] at hxx
      have h2 := hc.order
      rw [← hxx, orderOf_one] at h2
      exact absurd h2 (by decide)
  have hperm : ∀ {x : X} (hx : x ∈ L), x * x = e →
      Perm.sign (permOf eA (barOf L hx)) = 1 ∧
        permOf eA (barOf L hx) * permOf eA (barOf L hx) = 1 ∧ permOf eA (barOf L hx) ≠ 1 :=
    fun hx hxx => ⟨sign_permOf eA _, by rw [← permOf_mul, hsq hx hxx, permOf_one],
      fun h => hne1 hx hxx (permOf_injective eA (h.trans (permOf_one eA).symm))⟩
  have heZ' : ((⟨e, hL.mem⟩ : L) : L ⧸ Subgroup.center L) = 1 := heZ
  have hfix : ∀ {x : X}, x ∈ (T : Subgroup X) ⊓ L → ∀ hxL : x ∈ L,
      permAction eA y * permOf eA (barOf L hxL) = permOf eA (barOf L hxL) * permAction eA y := by
    intro x hx hxL
    have h := permOf_mk_conj eA y hxL
    have hbar : ((⟨y * x * y⁻¹, this.conj_mem x hxL y⟩ : L) : L ⧸ Subgroup.center L) =
        barOf L hxL := by
      by_cases hxy : y * x * y⁻¹ = x
      · exact congrArg _ (Subtype.ext hxy)
      · have h'' : (⟨y * x * y⁻¹, this.conj_mem x hxL y⟩ : L) = ⟨x, hxL⟩ * ⟨e, hL.mem⟩ :=
          Subtype.ext (hall x hx hxy)
        rw [h'', QuotientGroup.mk_mul, heZ', mul_one]
    rw [hbar] at h
    calc permAction eA y * permOf eA (barOf L hxL) =
        permAction eA y * permOf eA (barOf L hxL) * (permAction eA y)⁻¹ * permAction eA y := by
          group
      _ = permOf eA (barOf L hxL) * permAction eA y := by rw [← h]
  have hsign : Perm.sign (permAction eA y) = 1 := by
    refine s5_sign_eq_one_of_centralizes_four _ (hperm hq₁.2 h11) _ ⟨(hperm hq₂.2 h22).1,
      (hperm hq₂.2 h22).2.1, (hperm hq₂.2 h22).2.2, fun h => ?_, ?_⟩ _ (hfix hq₁ hq₁.2)
      (hfix hq₂ hq₂.2)
    ·
      have h' := QuotientGroup.eq.mp (permOf_injective eA h)
      rcases hL.eq_one_or_eq_of_card_two hc hZ h' with h'' | h''
      · exact h21 ((inv_mul_eq_one.mp (congrArg Subtype.val h'')).symm)
      · exact h21e (by
          have h3 : q₁⁻¹ * q₂ = e := h''
          rw [← h3]
          group)
    ·
      rw [← permOf_mul, ← permOf_mul]
      congr 1
      rw [← hbar_mul, ← hbar_mul]
      have hanti := quaternion_anticomm φ heQ hc.order hq₁ hq₂ h11 h22 h21 h21e
      rw [show (barOf L (L.mul_mem hq₁.2 hq₂.2)) =
          barOf L (L.mul_mem hq₂.2 hq₁.2) * barOf L hL.mem from by
        rw [← hbar_mul]
        exact congrArg _ (Subtype.ext hanti), heZ, mul_one]
  exact hy (hL.mem_sup_of_mem_sup hZ T hyT (mem_sup_centralizer_of_sign hL.perfect eA hsign))

theorem partC (hL : OneComponent Y e v L) (hc : BaseConfig Y e) (hv : v * v = e)
    (hvn : (Subgroup.zpowers v).Normal) (hZ : Nat.card (Subgroup.center L) = 2)
    (eA : L ⧸ Subgroup.center L ≃* alternatingGroup (Fin 5))
    (hα : ∀ x : X, orderOf x = 2 → x ∈ L ⊔ Subgroup.centralizer (L : Set X)) (T : Sylow 2 X) :
    PartC (T : Subgroup X) ((T : Subgroup X) ⊓ L)
      ((T : Subgroup X) ⊓ Subgroup.centralizer (L : Set X)) e v := by
  have hLn := hL.normal
  have hKn := hL.centralizer_normal
  have heK : e ∈ Subgroup.centralizer (L : Set X) :=
    Subgroup.mem_centralizer_iff.mpr fun l _ => (hc.commute_center l).eq
  exact
    { isPGroup := T.isPGroup'
      left_le := inf_le_left
      right_le := inf_le_left
      quaternion := hL.nonempty_inf_mulEquiv_quaternion hZ eA T
      commute := fun q hq p hp => Subgroup.mem_centralizer_iff.mp hp.2 q hq.2
      mem_inf := fun x hxQ hxP => by
        rcases hL.eq_one_or_eq_of_card_two hc hZ
            (mem_center_of_mem_centralizer (l := ⟨x, hxQ.2⟩) hxP.2) with h | h
        · exact Or.inl (congrArg Subtype.val h)
        · exact Or.inr h
      order := hc.order
      center := hc.center
      mem_left := ⟨hc.mem_sylow T, hL.mem⟩
      mem_right := ⟨hc.mem_sylow T, heK⟩
      self_mem := ⟨hc.mem_sylow_of_sq hv hvn T, hL.mem_centralizer⟩
      sq := hv
      unique := fun p hp hp2 => hL.eq_of_mem_centralizer p hp.2 hp2
      normal_left := fun t ht q hq => ⟨(T : Subgroup X).mul_mem ((T : Subgroup X).mul_mem ht hq.1)
        ((T : Subgroup X).inv_mem ht), hLn.conj_mem q hq.2 t⟩
      normal_right := fun t ht p hp => ⟨(T : Subgroup X).mul_mem
        ((T : Subgroup X).mul_mem ht hp.1) ((T : Subgroup X).inv_mem ht), hKn.conj_mem p hp.2 t⟩
      involution_mem := fun t ht ht2 => hL.mem_sup_of_mem_sup hZ T ht (hα t ht2)
      inv_mul_mem := fun a ha b hb ha' hb' => hL.inv_mul_mem_sup hZ eA T ha hb ha' hb'
      outer := fun y hy hy' => hL.exists_moved hc hZ eA T hy hy' }

end OneComponent

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
