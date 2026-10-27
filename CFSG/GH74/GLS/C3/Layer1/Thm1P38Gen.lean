module

public import CFSG.GH74.GLS.C3.Layer1.Thm1P38Group
public import CFSG.GH74.GLS.C3.Layer1.EvenSE413

public section

namespace CFSG.GH74.GLS.C3.Layer1.Thm1P38

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.C3.Layer1
  CFSG.GH74.GLS.C3.Layer1.Thm1

variable {G : Type} [Group G]

theorem le_closure_invol_of_dihedral {P : Subgroup G} {m : ℕ} (hd : IVK.IsDihedralOrder ↥P m) :
    P ≤ closure {u : G | u ∈ P ∧ orderOf u = 2} := by
  obtain ⟨k, -, -, ⟨ρ⟩⟩ := hd
  have hmem : ∀ i : ZMod k, ((ρ.symm (DihedralGroup.sr i) : ↥P) : G) ∈
      closure {u : G | u ∈ P ∧ orderOf u = 2} := fun i => by
    refine subset_closure ⟨(ρ.symm (DihedralGroup.sr i)).2, ?_⟩
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, DihedralGroup.orderOf_sr]
  intro p hp
  obtain ⟨d, hd⟩ : ∃ d, ρ ⟨p, hp⟩ = d := ⟨_, rfl⟩
  have hp' : (⟨p, hp⟩ : ↥P) = ρ.symm d := by rw [← hd, ρ.symm_apply_apply]
  rcases d with i | i
  · have h1 : DihedralGroup.r i = DihedralGroup.sr 0 * DihedralGroup.sr i := by
      rw [DihedralGroup.sr_mul_sr, sub_zero]
    rw [h1, map_mul] at hp'
    have h2 := congrArg Subtype.val hp'
    rw [Subgroup.coe_mul] at h2
    rw [show p = _ from h2]
    exact mul_mem (hmem 0) (hmem i)
  · have h2 := congrArg Subtype.val hp'
    rw [show p = _ from h2]
    exact hmem i

theorem twoPart_centralizer_eq_of_isConj {a b : G} (h : IsConj a b) :
    twoPartCard (centralizer ({a} : Set G)) = twoPartCard (centralizer ({b} : Set G)) := by
  unfold twoPartCard
  rw [card_centralizer_eq_of_isConj' h]

theorem mul_self_eq_one_of_comm {p e : G} (hpe : e * p = p * e) (hee : e * e = 1)
    (h : p * e * (p * e) = 1) : p * p = 1 := by
  calc p * p = p * p * (e * e) := by rw [hee, mul_one]
    _ = p * e * (p * e) := by
        calc p * p * (e * e) = p * (p * e) * e := by group
          _ = p * (e * p) * e := by rw [hpe]
          _ = p * e * (p * e) := by group
    _ = 1 := h

namespace Env37

variable [Finite G] {x y : G} {K T V W : Subgroup G} {f z : G}
  (E : Env37 x y K T V W f z) (D : L37Data x K T f z) {S : Subgroup G} {a : G}

include E

theorem actHom_conj_inner {g u v : G} (hgC : g ∈ centralizer ({x} : Set G))
    (huC : u ∈ centralizer ({x} : Set G)) (hvC : v ∈ centralizer ({x} : Set G))
    (h : g * u * g⁻¹ = v) (hu : Back.actHom E.hKN ⟨u, huC⟩ ∈ IVK.innAut (kBar K)) :
    Back.actHom E.hKN ⟨v, hvC⟩ ∈ IVK.innAut (kBar K) := by
  have h1 : (⟨v, hvC⟩ : ↥(centralizer ({x} : Set G))) =
      ⟨g, hgC⟩ * ⟨u, huC⟩ * ⟨g, hgC⟩⁻¹ := Subtype.ext h.symm
  rw [h1, map_mul, map_mul, map_inv]
  exact Subgroup.Normal.conj_mem (IVK.innAut_normal (K := kBar K)) _ hu _

theorem mem_cent_of_mem_sup {g : G} (hg : g ∈ K ⊔ zpowers f) : g ∈ centralizer ({x} : Set G) :=
  (sup_le E.cfg.hKx (zpowers_le.2 E.hfC)) hg

theorem actHom_P_mul_outer {p g : G} (hp : p ∈ T ⊓ K) (hgC : g ∈ centralizer ({x} : Set G))
    (hg : Back.actHom E.hKN ⟨g, hgC⟩ ∉ IVK.innAut (kBar K))
    (hpg : p * g ∈ centralizer ({x} : Set G)) :
    Back.actHom E.hKN ⟨p * g, hpg⟩ ∉ IVK.innAut (kBar K) := by
  intro hin
  apply hg
  have hpC : p ∈ centralizer ({x} : Set G) := E.hCx hp.1
  have h1 : (⟨p * g, hpg⟩ : ↥(centralizer ({x} : Set G))) = ⟨p, hpC⟩ * ⟨g, hgC⟩ := rfl
  rw [h1, map_mul] at hin
  have := (IVK.innAut (kBar K)).mul_mem
    ((IVK.innAut (kBar K)).inv_mem (E.actHom_inner_of_mem_P p hp hpC)) hin
  simpa using this

theorem exists_conj_z_of_mem_P {u : G} (hu : u ∈ T ⊓ K) (hu2 : orderOf u = 2) :
    ∃ g ∈ K ⊔ zpowers f, g * u * g⁻¹ = z := by
  obtain ⟨g, hg, h⟩ := E.fusion' u (Subgroup.mem_sup_left hu) hu2
  have hgC := E.mem_cent_of_mem_sup hg
  have huC : u ∈ centralizer ({x} : Set G) := E.hCx hu.1
  have hin := E.actHom_inner_of_mem_P u hu huC
  rcases h with h | h | h
  · exact ⟨g, hg, h⟩
  · exact absurd (E.actHom_conj_inner hgC huC E.hfC h hin) E.hfout
  · have hzC : z ∈ centralizer ({x} : Set G) := E.hCx E.hzP.1
    have hfzC : f * z ∈ centralizer ({x} : Set G) :=
      (centralizer ({x} : Set G)).mul_mem E.hfC hzC
    exact absurd (E.actHom_conj_inner hgC huC hfzC h hin)
      (E.actHom_f_mul_outer z (Subgroup.mem_sup_left (mem_zpowers z)) hfzC)

theorem false_of_isConj_F (hle : Nat.card ↥V ≤ Nat.card ↥T)
    (hlt : Nat.card ↥T < twoPartCard (centralizer ({z} : Set G))) {u g : G} (hzu : IsConj z u)
    (hg : IsFMember x K T g) (hug : IsConj u g) : False := by
  have h1 := twoPart_centralizer_eq_of_isConj (hzu.trans hug)
  have h2 := E.bound hle hg
  omega

theorem false_of_isConj_x (hlt : Nat.card ↥T < twoPartCard (centralizer ({z} : Set G))) {u : G}
    (hzu : IsConj z u) (hux : IsConj u x) : False := by
  have h1 := twoPart_centralizer_eq_of_isConj (hzu.trans hux)
  have h2 : Nat.card ↥T = twoPartCard (centralizer ({x} : Set G)) := E.cfg.setup.sylowT.card_eq
  omega

include D

theorem mem_P_of_isConj_z (hle : Nat.card ↥V ≤ Nat.card ↥T)
    (hlt : Nat.card ↥T < twoPartCard (centralizer ({z} : Set G)))
    (hax : a * x * a⁻¹ = x * z) {u : G} (hu : u ∈ thompsonJ2 T) (hconj : IsConj z u) :
    u ∈ T ⊓ K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hu2 : orderOf u = 2 := by
    obtain ⟨c, hc⟩ := isConj_iff.1 hconj
    rw [← hc, orderOf_conj_eq']
    exact E.hz2'
  have huu : u * u = 1 := by
    have := pow_orderOf_eq_one u
    rwa [hu2, sq] at this
  rw [D.ha] at hu
  obtain ⟨p, hp, e, he, rfl⟩ := Thm1P310.exists_mul_of_mem_sup
    (fun u hu w hw => (E.hEP w hw u hu).symm) hu
  have hpe : e * p = p * e := E.hEP e he p hp
  have hpC : p ∈ centralizer ({x} : Set G) := E.hCx hp.1
  have hzC : z ∈ centralizer ({x} : Set G) := E.hCx E.hzP.1
  have hfpC : f * p = p * f := E.hfP p hp
  rcases Thm1G33.klein_cases E.hf2 E.hx2 E.hfx he with h | h | h | h
  · rw [h, mul_one]
    exact hp
  ·
    exfalso
    rw [h] at hconj hu2
    have hmem : p * f ∈ T ⊓ K ⊔ zpowers f :=
      (T ⊓ K ⊔ zpowers f).mul_mem (Subgroup.mem_sup_left hp)
        (Subgroup.mem_sup_right (mem_zpowers f))
    obtain ⟨g, hg, hcase⟩ := E.fusion' (p * f) hmem hu2
    have hgC := E.mem_cent_of_mem_sup hg
    have hpfC : p * f ∈ centralizer ({x} : Set G) :=
      (centralizer ({x} : Set G)).mul_mem hpC E.hfC
    have hout := E.actHom_P_mul_outer hp E.hfC E.hfout hpfC
    rcases hcase with h1 | h1 | h1
    · have hC : g * (p * f) * g⁻¹ ∈ centralizer ({x} : Set G) := by rw [h1]; exact hzC
      refine E.actHom_conj_outer hgC hpfC hout hC ?_
      have e1 : (⟨g * (p * f) * g⁻¹, hC⟩ : ↥(centralizer ({x} : Set G))) = ⟨z, hzC⟩ :=
        Subtype.ext h1
      rw [e1]
      exact E.actHom_z hzC
    · exact E.false_of_isConj_F hle hlt hconj E.cfg.mem (isConj_iff.2 ⟨g, h1⟩)
    · exact E.false_of_isConj_F hle hlt hconj
        (E.isFMember_f_mul z (Subgroup.mem_sup_left (mem_zpowers z))) (isConj_iff.2 ⟨g, h1⟩)
  ·
    exfalso
    rw [h] at hconj huu
    have hhxe : p * x = x * p := E.hxc p hp.1
    have hp2 : p * p = 1 := mul_self_eq_one_of_comm (by rw [← hhxe]) E.hx2 huu
    by_cases hp1 : p = 1
    · rw [hp1, one_mul] at hconj
      exact E.false_of_isConj_x hlt hconj (isConj_iff.2 ⟨1, by simp⟩)
    · have hp2' : orderOf p = 2 := orderOf_eq_prime (by rw [sq]; exact hp2) hp1
      obtain ⟨g, hg, hgz⟩ := E.exists_conj_z_of_mem_P hp hp2'
      have hgC := E.mem_cent_of_mem_sup hg
      have hgx : g * x * g⁻¹ = x := by
        have := mem_centralizer_singleton_iff.1 hgC
        rw [this]
        group
      have h1 : g * (p * x) * g⁻¹ = x * z := by
        calc g * (p * x) * g⁻¹ = (g * p * g⁻¹) * (g * x * g⁻¹) := by group
          _ = z * x := by rw [hgz, hgx]
          _ = x * z := E.hzx
      exact E.false_of_isConj_x hlt hconj
        ((isConj_iff.2 ⟨g, h1⟩ : IsConj (p * x) (x * z)).trans
          (isConj_iff.2 ⟨a, hax⟩ : IsConj x (x * z)).symm)
  ·
    exfalso
    rw [h] at hconj hu2 huu
    have hfxP : (f * x) * p = p * (f * x) := by rw [h] at hpe; exact hpe
    have hfxfx : (f * x) * (f * x) = 1 := by
      calc f * x * (f * x) = f * (x * f) * x := by group
        _ = f * (f * x) * x := by rw [E.hfx]
        _ = (f * f) * (x * x) := by group
        _ = 1 := by rw [E.hf2, E.hx2, one_mul]
    have hp2 : p * p = 1 := mul_self_eq_one_of_comm hfxP hfxfx huu
    have hpf2 : p * f * (p * f) = 1 := by
      calc p * f * (p * f) = p * (f * p) * f := by group
        _ = p * (p * f) * f := by rw [hfpC]
        _ = (p * p) * (f * f) := by group
        _ = 1 := by rw [hp2, E.hf2, one_mul]
    have hpfC : p * f ∈ centralizer ({x} : Set G) :=
      (centralizer ({x} : Set G)).mul_mem hpC E.hfC
    have hout := E.actHom_P_mul_outer hp E.hfC E.hfout hpfC
    have hne : p * f ≠ 1 := by
      intro h1
      apply hout
      have : (⟨p * f, hpfC⟩ : ↥(centralizer ({x} : Set G))) = 1 := Subtype.ext h1
      rw [this, map_one]
      exact (IVK.innAut (kBar K)).one_mem
    have hpf2' : orderOf (p * f) = 2 := orderOf_eq_prime (by rw [sq]; exact hpf2) hne
    have hmem : p * f ∈ T ⊓ K ⊔ zpowers f :=
      (T ⊓ K ⊔ zpowers f).mul_mem (Subgroup.mem_sup_left hp)
        (Subgroup.mem_sup_right (mem_zpowers f))
    obtain ⟨g, hg, hcase⟩ := E.fusion' (p * f) hmem hpf2'
    have hgC := E.mem_cent_of_mem_sup hg
    have hgx : g * x * g⁻¹ = x := by
      have := mem_centralizer_singleton_iff.1 hgC
      rw [this]
      group
    have hxB : x ∈ zpowers z ⊔ zpowers x := Subgroup.mem_sup_right (mem_zpowers x)
    have hzB : z ∈ zpowers z ⊔ zpowers x := Subgroup.mem_sup_left (mem_zpowers z)
    have hsplit : g * (p * (f * x)) * g⁻¹ = (g * (p * f) * g⁻¹) * x := by
      calc g * (p * (f * x)) * g⁻¹ = (g * (p * f) * g⁻¹) * (g * x * g⁻¹) := by group
        _ = (g * (p * f) * g⁻¹) * x := by rw [hgx]
    rcases hcase with h1 | h1 | h1
    · have hC : g * (p * f) * g⁻¹ ∈ centralizer ({x} : Set G) := by rw [h1]; exact hzC
      refine E.actHom_conj_outer hgC hpfC hout hC ?_
      have e1 : (⟨g * (p * f) * g⁻¹, hC⟩ : ↥(centralizer ({x} : Set G))) = ⟨z, hzC⟩ :=
        Subtype.ext h1
      rw [e1]
      exact E.actHom_z hzC
    · have h2 : g * (p * (f * x)) * g⁻¹ = f * x := by rw [hsplit, h1]
      exact E.false_of_isConj_F hle hlt hconj (E.isFMember_f_mul x hxB) (isConj_iff.2 ⟨g, h2⟩)
    · have h2 : g * (p * (f * x)) * g⁻¹ = f * (z * x) := by
        rw [hsplit, h1, mul_assoc]
      exact E.false_of_isConj_F hle hlt hconj
        (E.isFMember_f_mul (z * x) ((zpowers z ⊔ zpowers x).mul_mem hzB hxB))
        (isConj_iff.2 ⟨g, h2⟩)

theorem hgen (hle : Nat.card ↥V ≤ Nat.card ↥T)
    (hlt : Nat.card ↥T < twoPartCard (centralizer ({z} : Set G)))
    (hax : a * x * a⁻¹ = x * z) :
    T ⊓ K = closure {u : G | u ∈ thompsonJ2 T ∧ IsConj z u} := by
  apply le_antisymm
  · obtain ⟨n, -, -, hd⟩ := E.hdih
    refine (le_closure_invol_of_dihedral hd).trans (closure_mono ?_)
    rintro u ⟨hu, hu2⟩
    refine ⟨?_, ?_⟩
    · rw [D.ha]
      exact Subgroup.mem_sup_left hu
    · obtain ⟨g, -, hg⟩ := E.exists_conj_z_of_mem_P hu hu2
      exact isConj_iff.2 ⟨g⁻¹, by rw [← hg]; group⟩
  · rw [Subgroup.closure_le]
    intro u hu
    exact E.mem_P_of_isConj_z D hle hlt hax hu.1 hu.2

end Env37

end CFSG.GH74.GLS.C3.Layer1.Thm1P38
