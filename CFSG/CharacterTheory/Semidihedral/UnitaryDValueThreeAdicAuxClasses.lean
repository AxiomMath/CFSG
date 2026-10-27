module

public import CFSG.CharacterTheory.Semidihedral.UnitaryDValueThreeAdicAuxCoset

public section

namespace CFSG.Semidihedral.UnitaryDValue

namespace DValueData

namespace Exceptional

variable {G : Type} [Group G] [Fintype G] {D : DValueData G} (E : D.Exceptional)

theorem card_centralizer_inf_QT
    (hsyl : ∀ v ∈ D.QT, v ∉ D.primaryPart 3 →
      (Nat.card (Subgroup.centralizer ({v} : Set G))).factorization 3 = E.h)
    {w : G} (hw : w ∈ D.QT) (hwP : w ∉ D.primaryPart 3) :
    Nat.card (Subgroup.centralizer ({w} : Set G) ⊓ D.QT : Subgroup G) = 3 ^ E.h := by
  set H := Subgroup.centralizer ({w} : Set G) ⊓ D.QT with hH
  have hHp : IsPGroup 3 H := D.isPGroup_QT.to_le inf_le_right
  obtain ⟨a, ha⟩ := hHp.exists_card_eq
  have hZH : E.Z ≤ H := fun z hz =>
    ⟨Subgroup.mem_centralizer_singleton_iff.mpr (E.Z_comm_QT hz hw).symm,
      D.P_le_QT (E.Z_le_P hz)⟩
  have hwH : w ∈ H := ⟨Subgroup.mem_centralizer_singleton_iff.mpr rfl, hw⟩
  have hwZ : w ∉ E.Z := fun h => hwP (E.Z_le_P h)
  have h1 : 3 ^ (E.h - 1) ∣ 3 ^ a := by
    rw [← E.card_Z, ← ha]
    exact Subgroup.card_dvd_of_le hZH
  have h1' : E.h - 1 ≤ a := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h1
  have h2 : a ≠ E.h - 1 := by
    intro heq
    apply hwZ
    have hcard : Nat.card H ≤ Nat.card E.Z := by rw [ha, E.card_Z, heq]
    rw [Subgroup.eq_of_le_of_card_ge hZH hcard]
    exact hwH
  have h3 : 3 ^ a ∣ Nat.card (Subgroup.centralizer ({w} : Set G)) := by
    rw [← ha]
    exact Subgroup.card_dvd_of_le inf_le_left
  have h3' : a ≤ E.h := by
    rw [← hsyl w hw hwP]
    exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three Nat.card_pos.ne').mp h3
  rw [ha]
  congr 1
  have := E.three_le_h
  omega

theorem exists_conj_QT (hgw : D.GWStep)
    (hsyl : ∀ v ∈ D.QT, v ∉ D.primaryPart 3 →
      (Nat.card (Subgroup.centralizer ({v} : Set G))).factorization 3 = E.h)
    {w w' : G} (hw : w ∈ D.QT) (hwP : w ∉ D.primaryPart 3) (hconj : IsConj w w')
    (hcoset : w' * w⁻¹ ∈ D.primaryPart 3) : ∃ q ∈ D.QT, q * w * q⁻¹ = w' := by
  have hw'Q : w' ∈ D.QT := by
    have e : w' = w' * w⁻¹ * w := by group
    rw [e]
    exact D.QT.mul_mem (D.P_le_QT hcoset) hw
  have hw'P : w' ∉ D.primaryPart 3 := by
    intro h
    apply hwP
    have e : w = (w' * w⁻¹)⁻¹ * w' := by group
    rw [e]
    exact (D.primaryPart 3).mul_mem ((D.primaryPart 3).inv_mem hcoset) h
  obtain ⟨g, hg⟩ := isConj_iff.mp hconj
  set K := Subgroup.centralizer ({w'} : Set G) with hK
  have hcardS : Nat.card ((Subgroup.centralizer ({w'} : Set G) ⊓ D.QT).subgroupOf K) =
      3 ^ (Nat.card K).factorization 3 := by
    rw [card_subgroupOf_of_le' inf_le_left, E.card_centralizer_inf_QT hsyl hw'Q hw'P,
      hsyl w' hw'Q hw'P]
  let S : Sylow 3 K := Sylow.ofCard _ hcardS
  have hgZ : ∀ z ∈ E.Z, g * z * g⁻¹ ∈ K := by
    intro z hz
    rw [hK, Subgroup.mem_centralizer_singleton_iff, ← hg]
    have hzw : z * w = w * z := (E.Z_comm_QT hz hw).symm
    calc g * z * g⁻¹ * (g * w * g⁻¹) = g * (z * w) * g⁻¹ := by group
      _ = g * (w * z) * g⁻¹ := by rw [hzw]
      _ = g * w * g⁻¹ * (g * z * g⁻¹) := by group
  let Zg : Subgroup K := ((E.Z).map (MulAut.conj g).toMonoidHom).subgroupOf K
  have hZg : IsPGroup 3 Zg := by
    have h1 : IsPGroup 3 E.Z := (D.isPGroup_primaryPart 3).to_le E.Z_le_P
    exact (h1.map _).comap_of_injective _ Subtype.val_injective
  obtain ⟨R, hR⟩ := hZg.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq K R S
  set r := (c : G) * g with hr
  have hrw : r * w * r⁻¹ = w' := by
    rw [hr, conj_mul_eq, hg]
    exact conj_eq_of_comm (Subgroup.mem_centralizer_singleton_iff.mp c.2)
  have hrZ : ∀ z ∈ E.Z, r * z * r⁻¹ ∈ D.QT ∧ r * z * r⁻¹ ∈ K := by
    intro z hz
    have hmem : (⟨g * z * g⁻¹, hgZ z hz⟩ : K) ∈ (R : Subgroup K) := hR ⟨z, hz, rfl⟩
    have h2 : c * ⟨g * z * g⁻¹, hgZ z hz⟩ * c⁻¹ ∈ (S : Subgroup K) := by
      rw [← hc, Sylow.coe_subgroup_smul]
      exact ⟨_, hmem, rfl⟩
    have h3 : ((c * ⟨g * z * g⁻¹, hgZ z hz⟩ * c⁻¹ : K) : G) ∈
        Subgroup.centralizer ({w'} : Set G) ⊓ D.QT := by
      have h4 := h2
      rw [Sylow.coe_ofCard] at h4
      exact h4
    have e : ((c * ⟨g * z * g⁻¹, hgZ z hz⟩ * c⁻¹ : K) : G) = r * z * r⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hr]
      group
    rw [e] at h3
    exact ⟨h3.2, h3.1⟩
  have hrZZ : ∀ z ∈ E.Z, r * z * r⁻¹ ∈ E.Z := by
    intro z hz
    obtain ⟨hzQ, hzK⟩ := hrZ z hz
    have hzP : r * z * r⁻¹ ∈ D.primaryPart 3 := by
      by_contra hnot
      refine E.not_conj_mem_P hgw hzQ hnot (g := r⁻¹) ?_
      have e : r⁻¹ * (r * z * r⁻¹) * r⁻¹⁻¹ = z := by group
      rw [e]
      exact E.Z_le_P hz
    refine (E.conj_fix_iff hw'Q hw'P hzP).mp ?_
    exact conj_eq_of_comm (Subgroup.mem_centralizer_singleton_iff.mp hzK).symm
  have hu₀3W : E.u₀ ^ 3 ∈ D.W := E.Z_le_W E.u₀_cube_mem_Z
  have htZ : ∀ u ∈ Subgroup.zpowers (E.u₀ ^ 3),
      D.t * u * D.t⁻¹ ∈ Subgroup.zpowers (E.u₀ ^ 3) := by
    intro u hu
    rw [E.t_conj_Z hu]
    exact hu
  have hrN : r ∈ Subgroup.normalizer (Subgroup.zpowers (E.u₀ ^ 3) : Set G) :=
    mem_normalizer_of_conj_mem_of_finite hrZZ
  rcases D.normalizer_conj_of_le_W hu₀3W E.u₀_cube_ne_one htZ hrN with hfix | hinv
  ·
    have hfix3 := hfix _ E.u₀_cube_mem_Z
    have hrT := E.centralizer_le_normalizer_T hgw E.u₀_cube_mem_Z E.u₀_cube_ne_one
      (Subgroup.mem_centralizer_singleton_iff.mpr (comm_of_conj_eq hfix3))
    exact D.exists_conj_QT_of_mem_CT (E.mem_CT_of_fix hrT hfix3) hw hw'Q hrw
  ·
    exfalso
    have hinv3 := hinv _ E.u₀_cube_mem_Z
    have hfix3 : r * D.y⁻¹ * E.u₀ ^ 3 * (r * D.y⁻¹)⁻¹ = E.u₀ ^ 3 := by
      rw [conj_mul_eq, inv_inv, D.y_inv_conj_W hu₀3W, conj_inv_eq, hinv3, inv_inv]
    have hrT := E.centralizer_le_normalizer_T hgw E.u₀_cube_mem_Z E.u₀_cube_ne_one
      (Subgroup.mem_centralizer_singleton_iff.mpr (comm_of_conj_eq hfix3))
    have hinvC := D.mul_y_conj_mul_mem_C (E.mem_CT_of_fix hrT hfix3) (D.QT_le_CT hw)
    rw [show r * D.y⁻¹ * D.y = r by group, hrw] at hinvC
    have hw2C : w * w ∈ D.C := by
      have e : w * w = (w' * w⁻¹)⁻¹ * (w' * w) := by group
      rw [e]
      exact D.C.mul_mem (D.C.inv_mem (D.primaryPart_le_C 3 hcoset)) hinvC
    have hw2P := D.mem_P_of_mem_QT_of_mem_C (D.QT.mul_mem hw hw) hw2C
    apply hwP
    have e : w = w ^ 3 * (w * w)⁻¹ := by group
    rw [e]
    exact (D.primaryPart 3).mul_mem (D.cube_mem_P_of_mem_QT hw) ((D.primaryPart 3).inv_mem hw2P)

theorem ncard_coset_self (hgw : D.GWStep)
    (hsyl : ∀ v ∈ D.QT, v ∉ D.primaryPart 3 →
      (Nat.card (Subgroup.centralizer ({v} : Set G))).factorization 3 = E.h)
    {w : G} (hw : w ∈ D.QT) (hwP : w ∉ D.primaryPart 3) :
    {u : G | IsConj w u ∧ u * w⁻¹ ∈ D.primaryPart 3}.ncard = 9 := by
  set w₀ : D.QT := ⟨w, hw⟩ with hw₀
  have hset : {u : G | IsConj w u ∧ u * w⁻¹ ∈ D.primaryPart 3} =
      Subtype.val '' MulAction.orbit (ConjAct D.QT) w₀ := by
    ext u
    constructor
    · rintro ⟨hconj, hcoset⟩
      obtain ⟨q, hq, hqu⟩ := E.exists_conj_QT hgw hsyl hw hwP hconj hcoset
      have huQ : u ∈ D.QT := hqu ▸ D.QT.mul_mem (D.QT.mul_mem hq hw) (D.QT.inv_mem hq)
      refine ⟨⟨u, huQ⟩, ⟨ConjAct.toConjAct (⟨q, hq⟩ : D.QT), ?_⟩, rfl⟩
      apply Subtype.ext
      change ((ConjAct.toConjAct (⟨q, hq⟩ : D.QT) • w₀ : D.QT) : G) = u
      rw [ConjAct.smul_def, ConjAct.ofConjAct_toConjAct]
      exact hqu
    · rintro ⟨x, ⟨g, rfl⟩, rfl⟩
      change IsConj w ((g • w₀ : D.QT) : G) ∧ ((g • w₀ : D.QT) : G) * w⁻¹ ∈ D.primaryPart 3
      rw [ConjAct.smul_def]
      refine ⟨isConj_iff.mpr ⟨(ConjAct.ofConjAct g : D.QT), rfl⟩, ?_⟩
      exact D.QT_commutator_mem_P (ConjAct.ofConjAct g).2 hw
  rw [hset, Set.ncard_image_of_injective _ Subtype.val_injective, ← MulAction.index_stabilizer]
  have h1 := (MulAction.stabilizer (ConjAct D.QT) w₀).card_mul_index
  rw [← Subgroup.nat_card_centralizer_nat_card_stabilizer] at h1
  have hcent : Subgroup.centralizer ({w₀} : Set D.QT) =
      (Subgroup.centralizer ({w} : Set G) ⊓ D.QT).subgroupOf D.QT := by
    ext c
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      exact ⟨congrArg Subtype.val h, c.2⟩
    · intro h
      exact Subtype.ext h.1
  rw [hcent, card_subgroupOf_of_le' inf_le_right, E.card_centralizer_inf_QT hsyl hw hwP] at h1
  have hQ : Nat.card (ConjAct D.QT) = 3 ^ E.h * 9 := by
    rw [Nat.card_congr ConjAct.ofConjAct.toEquiv, E.card_QT_eq, pow_add]
    norm_num
  rw [hQ] at h1
  exact Nat.eq_of_mul_eq_mul_left (pow_pos (by norm_num) E.h) h1

include E in
theorem exists_mul_y_mem_normalizer_QT :
    ∃ h ∈ D.CT, h * D.y ∈ Subgroup.normalizer (D.QT : Set G) := by
  have hle := D.QT_le_CT
  let P' : Sylow 3 D.CT := (D.sylowQT E.three_dvd_q).subtype (by rw [D.coe_sylowQT]; exact hle)
  have hP : (P' : Subgroup D.CT) = D.QT.subgroupOf D.CT := by
    rw [Sylow.coe_subtype, D.coe_sylowQT]
  exact exists_mul_mem_normalizer_of_sylow hle P' hP (fun k hk => D.y_conj_CT hk)

theorem ncard_conj_coset (hgw : D.GWStep)
    (hsyl : ∀ v ∈ D.QT, v ∉ D.primaryPart 3 →
      (Nat.card (Subgroup.centralizer ({v} : Set G))).factorization 3 = E.h)
    {v : G} (hv : v ∈ D.QT) (hvP : v ∉ D.primaryPart 3) :
    {u : G | IsConj v u ∧ u * D.tThree⁻¹ ∈ D.primaryPart 3}.ncard = 9 ∧
      {u : G | IsConj v u ∧ u * D.tThree ∈ D.primaryPart 3}.ncard = 9 := by
  obtain ⟨h, hh, hQ⟩ := E.exists_mul_y_mem_normalizer_QT
  set v' := h * D.y * v * (h * D.y)⁻¹ with hv'
  have hv'Q : v' ∈ D.QT := (Subgroup.mem_normalizer_iff.mp hQ v).mp hv
  have hv'v : v' * v ∈ D.primaryPart 3 :=
    D.mem_P_of_mem_QT_of_mem_C (D.QT.mul_mem hv'Q hv)
      (D.mul_y_conj_mul_mem_C hh (D.QT_le_CT hv))
  have hv'P : v' ∉ D.primaryPart 3 := by
    intro h1
    apply hvP
    have e : v = v'⁻¹ * (v' * v) := by group
    rw [e]
    exact (D.primaryPart 3).mul_mem ((D.primaryPart 3).inv_mem h1) hv'v
  have hconj : IsConj v v' := isConj_iff.mpr ⟨h * D.y, rfl⟩
  have hself := E.ncard_coset_self hgw hsyl hv hvP
  have hother := E.ncard_coset_self hgw hsyl hv'Q hv'P
  have hiff : ∀ u, IsConj v u ↔ IsConj v' u := fun u =>
    ⟨fun h1 => hconj.symm.trans h1, fun h1 => hconj.trans h1⟩
  rcases D.mul_tThree_inv_mem_or hv hvP with h1 | h1
  ·
    have h2 : v' * D.tThree⁻¹⁻¹ ∈ D.primaryPart 3 := by
      have hτ : D.tThree⁻¹ * (v * D.tThree⁻¹) * D.tThree⁻¹⁻¹ ∈ D.primaryPart 3 :=
        D.conj_mem_primaryPart (inv_mem D.tThree_mem_normalizer_T) h1
      have e : v' * D.tThree⁻¹⁻¹ =
          v' * v * (D.tThree⁻¹ * (v * D.tThree⁻¹) * D.tThree⁻¹⁻¹)⁻¹ := by group
      rw [e]
      exact (D.primaryPart 3).mul_mem hv'v ((D.primaryPart 3).inv_mem hτ)
    constructor
    · have e : {u : G | IsConj v u ∧ u * D.tThree⁻¹ ∈ D.primaryPart 3} =
          {u : G | IsConj v u ∧ u * v⁻¹ ∈ D.primaryPart 3} := by
        ext u
        exact and_congr Iff.rfl (mul_inv_mem_iff_of_mul_inv_mem h1)
      rw [e]
      exact hself
    · have e : {u : G | IsConj v u ∧ u * D.tThree ∈ D.primaryPart 3} =
          {u : G | IsConj v' u ∧ u * v'⁻¹ ∈ D.primaryPart 3} := by
        ext u
        have h3 := mul_inv_mem_iff_of_mul_inv_mem (c := u) h2
        rw [inv_inv] at h3
        exact and_congr (hiff u) h3
      rw [e]
      exact hother
  ·
    have h1' : v * D.tThree⁻¹⁻¹ ∈ D.primaryPart 3 := by
      rw [inv_inv]
      exact h1
    have h2 : v' * D.tThree⁻¹ ∈ D.primaryPart 3 := by
      have hτ : D.tThree * (v * D.tThree) * D.tThree⁻¹ ∈ D.primaryPart 3 :=
        D.conj_mem_primaryPart D.tThree_mem_normalizer_T h1
      have e : v' * D.tThree⁻¹ = v' * v * (D.tThree * (v * D.tThree) * D.tThree⁻¹)⁻¹ := by
        group
      rw [e]
      exact (D.primaryPart 3).mul_mem hv'v ((D.primaryPart 3).inv_mem hτ)
    constructor
    · have e : {u : G | IsConj v u ∧ u * D.tThree⁻¹ ∈ D.primaryPart 3} =
          {u : G | IsConj v' u ∧ u * v'⁻¹ ∈ D.primaryPart 3} := by
        ext u
        exact and_congr (hiff u) (mul_inv_mem_iff_of_mul_inv_mem h2)
      rw [e]
      exact hother
    · have e : {u : G | IsConj v u ∧ u * D.tThree ∈ D.primaryPart 3} =
          {u : G | IsConj v u ∧ u * v⁻¹ ∈ D.primaryPart 3} := by
        ext u
        have h3 := mul_inv_mem_iff_of_mul_inv_mem (c := u) h1'
        rw [inv_inv] at h3
        exact and_congr Iff.rfl h3
      rw [e]
      exact hself

end Exceptional

end DValueData

end CFSG.Semidihedral.UnitaryDValue
