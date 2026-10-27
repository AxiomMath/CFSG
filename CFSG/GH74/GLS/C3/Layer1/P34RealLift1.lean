module

public import CFSG.GH74.GLS.C3.Layer1.P34RealCtx
public import CFSG.GH74.GLS.C3.Layer1.P34RealAut

public section

namespace CFSG.GH74.GLS.C3.Layer1.P34Real

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.C3.Layer1
  CFSG.GH74.GLS.C3.Layer1.Thm1
open scoped commutatorElement

variable {G : Type} [Group G] {K : Subgroup G}

namespace Real34

variable [Finite G] {x : G} {T : Subgroup G} {f : G} (H : Real34 x K T f)

include H in
noncomputable def phiP : ↥(T ⊓ K) →* MulAut (kBar K) :=
  (Back.actHom H.KN).comp (Subgroup.inclusion H.P_le_C)

omit [Finite G] in
include H in
theorem phiP_apply (p : ↥(T ⊓ K)) : H.phiP p = act H.KN (p : G) := by
  unfold phiP
  rw [MonoidHom.comp_apply, act_of_mem H.KN (H.P_le_C p.2)]
  rfl

include H in
theorem phiP_injective : Function.Injective H.phiP := fun p₁ p₂ h =>
  Subtype.ext (H.act_inj_P p₁.2 p₂.2 (by rw [← H.phiP_apply, ← H.phiP_apply, h]))

include H in
theorem range_phiP : H.phiP.range = H.B ⊓ innAut (kBar K) := by
  ext u
  rw [H.mem_B_inf_inn]
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨p, p.2, (H.phiP_apply p).symm⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨⟨p, hp⟩, H.phiP_apply ⟨p, hp⟩⟩

include H in
noncomputable def isoPbar : ↥(T ⊓ K) ≃* ↥(H.B ⊓ innAut (kBar K)) :=
  (MonoidHom.ofInjective H.phiP_injective).trans (MulEquiv.subgroupCongr H.range_phiP)

include H in
theorem isoPbar_apply (p : ↥(T ⊓ K)) :
    ((H.isoPbar p : ↥(H.B ⊓ innAut (kBar K))) : MulAut (kBar K)) = act H.KN (p : G) := by
  rw [← H.phiP_apply]
  rfl

section Aut

variable {zb : MulAut (kBar K)} (hA : AutP34 H.B (act H.KN f) zb)

include H hA in
theorem P_dihedral : P34.IsDihedralGE8 (T ⊓ K) := by
  obtain ⟨n, hn, hdih⟩ := hA.dihedral
  exact isDihedralGE8_of_equiv H.isoPbar hn hdih.2

include H hA in
theorem exists_z : ∃ z ∈ T ⊓ K, act H.KN z = zb :=
  (H.mem_B_inf_inn).1 hA.z_mem

variable {z : G} (hz : z ∈ T ⊓ K) (hzb : act H.KN z = zb)

include H hA hz hzb in
theorem z_sq : z * z = 1 := by
  have hzC := H.P_le_C hz
  have h1 : act H.KN (z * z) = act H.KN 1 := by
    rw [act_mul H.KN hzC hzC, hzb, act_one]
    have := pow_orderOf_eq_one zb
    rwa [hA.z_order, sq] at this
  exact H.act_inj_P (Subgroup.mul_mem _ hz hz) (Subgroup.one_mem _) h1

omit [Finite G] in
include H hA hz hzb in
theorem z_ne_one : z ≠ 1 := by
  rintro rfl
  rw [act_one] at hzb
  have := hA.z_order
  rw [← hzb, orderOf_one] at this
  omega

include H hA hz hzb in
theorem z_order : orderOf z = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by rw [sq]; exact z_sq H hA hz hzb) (z_ne_one H hA hz hzb)

include H hA hz hzb in
theorem z_central {a : G} (ha : a ∈ T ⊓ K) : a * z = z * a := by
  have haC := H.P_le_C ha
  have hzC := H.P_le_C hz
  have hmem : act H.KN a ∈ H.B ⊓ innAut (kBar K) := (H.mem_B_inf_inn).2 ⟨a, ha, rfl⟩
  have h1 : act H.KN (a * z) = act H.KN (z * a) := by
    rw [act_mul H.KN haC hzC, act_mul H.KN hzC haC, hzb]
    exact (hA.z_cent _ hmem).symm
  exact H.act_inj_P (Subgroup.mul_mem _ ha hz) (Subgroup.mul_mem _ hz ha) h1

include H hA hz hzb in
theorem z_unique_aux {c : G} (hc : c ∈ T ⊓ K) (hcc : ∀ a ∈ T ⊓ K, c * a = a * c) :
    c = 1 ∨ c = z := by
  have hcb : act H.KN c ∈ H.B ⊓ innAut (kBar K) := (H.mem_B_inf_inn).2 ⟨c, hc, rfl⟩
  have hcentral : ∀ q ∈ H.B ⊓ innAut (kBar K), act H.KN c * q = q * act H.KN c := by
    intro q hq
    obtain ⟨a, ha, rfl⟩ := (H.mem_B_inf_inn).1 hq
    rw [← act_mul H.KN (H.P_le_C hc) (H.P_le_C ha), ← act_mul H.KN (H.P_le_C ha) (H.P_le_C hc),
      hcc a ha]
  rcases hA.z_unique _ hcb hcentral with h | h
  · left
    exact H.act_inj_P hc (Subgroup.one_mem _) (by rw [h, act_one])
  · right
    exact H.act_inj_P hc hz (by rw [h, hzb])

include H in
theorem f_not_mem_PQ : f ∉ (T ⊓ K) ⊔ H.Q := fun h => H.act_f_not_inn (H.act_PQ h).2

include H hA in
theorem commutator_mem_PQ {a b : G} (ha : a ∈ T) (hb : b ∈ T) :
    a * b * a⁻¹ * b⁻¹ ∈ (T ⊓ K) ⊔ H.Q := by
  have haC := H.T_le_C ha
  have hbC := H.T_le_C hb
  have hmem := hA.abelian (act H.KN a) ((H.mem_B).2 ⟨a, ha, rfl⟩) (act H.KN b)
    ((H.mem_B).2 ⟨b, hb, rfl⟩)
  have h1 : act H.KN (a * b * a⁻¹ * b⁻¹) = act H.KN a * act H.KN b * (act H.KN a)⁻¹ *
      (act H.KN b)⁻¹ := by
    rw [act_mul H.KN (Subgroup.mul_mem _ (Subgroup.mul_mem _ haC hbC) (Subgroup.inv_mem _ haC))
      (Subgroup.inv_mem _ hbC), act_mul H.KN (Subgroup.mul_mem _ haC hbC) (Subgroup.inv_mem _ haC),
      act_mul H.KN haC hbC, act_inv H.KN haC, act_inv H.KN hbC]
  refine H.mem_PQ_of_act_mem (T.mul_mem (T.mul_mem (T.mul_mem ha hb) (T.inv_mem ha)) (T.inv_mem hb))
    ?_
  rw [h1]
  exact hmem

include H hA hz hzb in
theorem cent_P_iff {t : G} (ht : t ∈ T) :
    (∀ a ∈ T ⊓ K, t * a = a * t) ↔ t ∈ (H.Q ⊔ zpowers f) ⊔ zpowers z := by
  have hfC : f ∈ centralizer ({x} : Set G) := H.T_le_C H.f_mem
  have hzC : z ∈ centralizer ({x} : Set G) := H.P_le_C hz
  have hαα : act H.KN f * act H.KN f = 1 := by
    rw [← act_mul H.KN hfC hfC, H.f_sq, act_one]
  have hzz : zb * zb = 1 := by
    have := pow_orderOf_eq_one zb
    rwa [hA.z_order, sq] at this
  constructor
  · intro hc
    have htC := H.T_le_C ht
    have hu : ∀ q ∈ H.B ⊓ innAut (kBar K), act H.KN t * q = q * act H.KN t := by
      intro q hq
      obtain ⟨a, ha, rfl⟩ := (H.mem_B_inf_inn).1 hq
      rw [← act_mul H.KN htC (H.P_le_C ha), ← act_mul H.KN (H.P_le_C ha) htC, hc a ha]
    have hmem := hA.cent_B (act H.KN t) ((H.mem_B).2 ⟨t, ht, rfl⟩) hu
    have hcomm : ∀ a ∈ zpowers (act H.KN f), ∀ b ∈ zpowers zb, a * b = b * a := by
      intro a ha b hb
      obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 ha
      obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hb
      have hfz : Commute (act H.KN f) zb := (H.act_f_comm_Pbar hA.z_mem)
      exact (hfz.zpow_zpow i j).eq
    obtain ⟨a, ha, b, hb, hab⟩ := Back.exists_mul_of_mem_sup_of_commute hcomm hmem
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 ha
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hb
    have hT' : f ^ i * z ^ j ∈ T :=
      T.mul_mem (Subgroup.zpow_mem _ H.f_mem i) (Subgroup.zpow_mem _ hz.1 j)
    have hq := H.fiber_mem_Q ht hT' (by
      rw [act_mul H.KN (Subgroup.zpow_mem _ hfC i) (Subgroup.zpow_mem _ hzC j),
        act_zpow H.KN hfC, act_zpow H.KN hzC, hzb, hab])
    have : t = (f ^ i * z ^ j) * ((f ^ i * z ^ j)⁻¹ * t) := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _
      (Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.zpow_mem _ (mem_zpowers f) i)))
      (Subgroup.mem_sup_right (Subgroup.zpow_mem _ (mem_zpowers z) j)))
      (Subgroup.mem_sup_left (Subgroup.mem_sup_left hq))
  · intro h a ha
    have hle : (H.Q ⊔ zpowers f) ⊔ zpowers z ≤ centralizer ((T ⊓ K : Subgroup G) : Set G) := by
      refine sup_le (sup_le ?_ ?_) ?_
      · intro q hq
        exact mem_centralizer_iff.2 fun a ha => H.P_comm_Q ha hq
      · rw [zpowers_le]
        exact mem_centralizer_iff.2 fun a ha => (H.f_cent a ha).symm
      · rw [zpowers_le]
        exact mem_centralizer_iff.2 fun a ha => z_central H hA hz hzb ha
    exact (mem_centralizer_iff.1 (hle h) a ha).symm

include H in
theorem iso_Ph {h : G} (hh : h ∈ T) (hh2 : h * h = 1) (hhR : h ∉ ((T ⊓ K) ⊔ H.Q) ⊔ zpowers f) :
    Nonempty (↥((T ⊓ K) ⊔ zpowers h) ≃* ↥((H.B ⊓ innAut (kBar K)) ⊔ zpowers (act H.KN h))) := by
  have hhC := H.T_le_C hh
  set D : Subgroup G := (T ⊓ K) ⊔ zpowers h with hD
  have hDT : D ≤ T := sup_le inf_le_left ((zpowers_le).2 hh)
  have hDC : D ≤ centralizer ({x} : Set G) := hDT.trans H.T_le_C
  let ψ : ↥D →* MulAut (kBar K) := (Back.actHom H.KN).comp (Subgroup.inclusion hDC)
  have hψ : ∀ d : ↥D, ψ d = act H.KN (d : G) := fun d => by
    simp only [ψ, MonoidHom.comp_apply]
    rw [act_of_mem H.KN (hDC d.2)]
    rfl
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro d hd
    rw [hψ] at hd
    have hle : zpowers h ≤ normalizer ((T ⊓ K : Subgroup G) : Set G) := by
      rw [zpowers_le]
      exact H.mem_normalizer_P hh
    have hd' : (d : G) ∈ (((T ⊓ K) ⊔ zpowers h : Subgroup G) : Set G) := d.2
    rw [Subgroup.coe_mul_of_right_le_normalizer_left (T ⊓ K) (zpowers h) hle] at hd'
    obtain ⟨p, hp, w, hw, hpw⟩ := hd'
    have hpC := H.P_le_C hp
    have hpw' : (d : G) = p * w := hpw.symm
    rcases mem_zpowers_of_mul_self hh2 hw with hw1 | hwh
    · rw [hw1, mul_one] at hpw'
      have h1 : act H.KN p = act H.KN 1 := by rw [act_one, ← hpw']; exact hd
      have := H.act_inj_P hp (Subgroup.one_mem _) h1
      exact Subtype.ext (by rw [hpw', this]; rfl)
    · exfalso
      rw [hpw', hwh, act_mul H.KN hpC hhC] at hd
      have h2 : act H.KN h = (act H.KN p)⁻¹ := eq_inv_of_mul_eq_one_right hd
      have h3 : act H.KN h ∈ H.B ⊓ innAut (kBar K) := by
        rw [h2]
        exact Subgroup.inv_mem _ ((H.mem_B_inf_inn).2 ⟨p, hp, rfl⟩)
      exact hhR (Subgroup.mem_sup_left (H.mem_PQ_of_act_mem hh h3))
  have hrange : ψ.range = (H.B ⊓ innAut (kBar K)) ⊔ zpowers (act H.KN h) := by
    apply le_antisymm
    · rintro u ⟨d, rfl⟩
      let S : Subgroup (MulAut (kBar K)) := (H.B ⊓ innAut (kBar K)) ⊔ zpowers (act H.KN h)
      let U : Subgroup G := (S.comap (Back.actHom H.KN)).map (centralizer ({x} : Set G)).subtype
      have hle : D ≤ U := by
        refine sup_le ?_ ?_
        · intro p hp
          refine ⟨⟨p, H.P_le_C hp⟩, ?_, rfl⟩
          show Back.actHom H.KN ⟨p, H.P_le_C hp⟩ ∈ S
          rw [← act_of_mem H.KN (H.P_le_C hp)]
          exact Subgroup.mem_sup_left ((H.mem_B_inf_inn).2 ⟨p, hp, rfl⟩)
        · rw [zpowers_le]
          refine ⟨⟨h, hhC⟩, ?_, rfl⟩
          show Back.actHom H.KN ⟨h, hhC⟩ ∈ S
          rw [← act_of_mem H.KN hhC]
          exact Subgroup.mem_sup_right (mem_zpowers _)
      obtain ⟨m, hm, hmd⟩ := hle d.2
      rw [hψ, ← hmd]
      show act H.KN (m : G) ∈ S
      rw [act_of_mem H.KN m.2]
      exact hm
    · refine sup_le ?_ ?_
      · intro u hu
        obtain ⟨p, hp, rfl⟩ := (H.mem_B_inf_inn).1 hu
        exact ⟨⟨p, Subgroup.mem_sup_left hp⟩, by rw [hψ]⟩
      · rw [zpowers_le]
        exact ⟨⟨h, Subgroup.mem_sup_right (mem_zpowers h)⟩, by rw [hψ]⟩
  exact ⟨(MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)⟩

include H hA in
theorem exists_h : ∃ h ∈ T, h * h = 1 ∧
    (∀ t ∈ T, t * t = 1 → t ∈ ((T ⊓ K) ⊔ H.Q) ⊔ zpowers f ∨
      ∃ r ∈ (T ⊓ K) ⊔ H.Q, t = r * h) ∧
    (h = 1 ∨ (h ∉ ((T ⊓ K) ⊔ H.Q) ⊔ zpowers f ∧ P34.IsDihedralGE8 ((T ⊓ K) ⊔ zpowers h))) := by
  by_cases hex : ∃ t ∈ T, t * t = 1 ∧ t ∉ ((T ⊓ K) ⊔ H.Q) ⊔ zpowers f
  · obtain ⟨h, hhT, hh2, hhR⟩ := hex
    have hhC := H.T_le_C hhT
    have hu : act H.KN h ∈ H.B := (H.mem_B).2 ⟨h, hhT, rfl⟩
    have hu2 : act H.KN h * act H.KN h = 1 := by rw [← act_mul H.KN hhC hhC, hh2, act_one]
    have hunot : act H.KN h ∉ (H.B ⊓ innAut (kBar K)) ⊔ zpowers (act H.KN f) := fun hmem =>
      hhR ((H.mem_PQf_iff hhT).2 hmem)
    refine ⟨h, hhT, hh2, ?_, Or.inr ⟨hhR, ?_⟩⟩
    · intro t ht ht2
      by_cases htR : t ∈ ((T ⊓ K) ⊔ H.Q) ⊔ zpowers f
      · exact Or.inl htR
      · right
        have htC := H.T_le_C ht
        have hu' : act H.KN t ∈ H.B := (H.mem_B).2 ⟨t, ht, rfl⟩
        have hu'2 : act H.KN t * act H.KN t = 1 := by rw [← act_mul H.KN htC htC, ht2, act_one]
        have hu'not : act H.KN t ∉ (H.B ⊓ innAut (kBar K)) ⊔ zpowers (act H.KN f) := fun hmem =>
          htR ((H.mem_PQf_iff ht).2 hmem)
        have key := hA.invol_coset (act H.KN h) hu hu2 hunot (act H.KN t) hu' hu'2 hu'not
        have hhinv : h⁻¹ = h := inv_eq_of_mul_eq_one_right hh2
        refine ⟨t * h⁻¹, ?_, by group⟩
        refine H.mem_PQ_of_act_mem (T.mul_mem ht (T.inv_mem hhT)) ?_
        rw [act_mul H.KN htC (Subgroup.inv_mem _ hhC), act_inv H.KN hhC]
        exact key
    · obtain ⟨n, hn2, ⟨e⟩⟩ := hA.invol_dih (act H.KN h) hu hu2 hunot
      obtain ⟨e'⟩ := H.iso_Ph hhT hh2 hhR
      exact ⟨n, hn2, ⟨e'.trans e⟩⟩
  · push Not at hex
    exact ⟨1, T.one_mem, mul_one 1, fun t ht ht2 => Or.inl (hex t ht ht2), Or.inl rfl⟩

end Aut

end Real34

end CFSG.GH74.GLS.C3.Layer1.P34Real
