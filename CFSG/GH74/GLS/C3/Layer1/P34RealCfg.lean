module

public import CFSG.GH74.GLS.C3.Layer1.P34RealLift2

public section

namespace CFSG.GH74.GLS.C3.Layer1.P34Real

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.C3.Layer1
  CFSG.GH74.GLS.C3.Layer1.Thm1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {K : Subgroup G}

namespace Real34

variable {x : G} {T : Subgroup G} {f : G} (H : Real34 x K T f)

omit [Finite G] in
include H in
theorem act_x : act H.KN x = 1 := by
  have hxC : x ∈ centralizer ({x} : Set G) := mem_centralizer_singleton_iff.2 rfl
  rw [act_of_mem H.KN hxC]
  refine (Back.actHom_eq_one_iff_commutator_mem H.KN ⟨x, hxC⟩).2 (fun k hk => ?_)
  have hxk : k * x = x * k := mem_centralizer_singleton_iff.1 (H.KC hk)
  have : ⁅k, x⁆ = 1 := by
    rw [commutatorElement_def, hxk]
    group
  rw [this]
  exact (pPrimeCoreOf 2 K).one_mem

omit [Finite G] in
include H in
theorem x_mem_Q : x ∈ H.Q := (H.mem_Q).2 ⟨H.x_mem, H.act_x⟩

omit [Finite G] in
include H in
theorem Q_norm {t a : G} (ht : t ∈ T) (ha : a ∈ H.Q) : t * a * t⁻¹ ∈ H.Q := by
  have haT := (H.mem_Q).1 ha
  refine (H.mem_Q).2 ⟨T.mul_mem (T.mul_mem ht haT.1) (T.inv_mem ht), ?_⟩
  rw [act_conj H.KN (H.T_le_C ht) (H.T_le_C haT.1), haT.2]
  group

omit [Finite G] in
include H in
theorem CMK_normal {g n : G} (hg : g ∈ centralizer ({x} : Set G))
    (hn : n ∈ CMK (centralizer ({x} : Set G)) K) :
    g * n * g⁻¹ ∈ CMK (centralizer ({x} : Set G)) K :=
  CMK_conj H.KN hg hn

section Aut

variable {zb : MulAut (kBar K)} (hA : AutP34 H.B (act H.KN f) zb)

include H hA in
theorem cfg (hsimple : IsSimpleGroup G) (hnonab : ∃ a b : G, a * b ≠ b * a) (hTidx : ¬ 2 ∣ T.index)
    (hx2 : orderOf x = 2) (hQ : IsCyclic ↥H.Q ∨ P34.IsMaximalClassTwoGroup ↥H.Q) :
    ∃ (P Q : Subgroup G) (z h : G), P34.Cfg34 G T P Q x z f h := by
  obtain ⟨z, hz, hzb⟩ := exists_z H hA
  obtain ⟨h, hhT, hh2, hinvol, hh⟩ := exists_h H hA
  refine ⟨T ⊓ K, H.Q, z, h, ?_⟩
  exact
    { X_simple := hsimple
      X_nonab := hnonab
      T_pgroup := H.sylowT.isPGroup
      T_index := hTidx
      x_mem := H.x_mem
      x_order := hx2
      x_central := fun t ht => mem_centralizer_singleton_iff.1 (H.T_le_C ht)
      P_le := inf_le_left
      Q_le := H.Q_le_T
      P_norm := fun t ht a ha =>
        ⟨T.mul_mem (T.mul_mem ht ha.1) (T.inv_mem ht), H.KN t (H.T_le_C ht) a ha.2⟩
      Q_norm := fun t ht a ha => H.Q_norm ht ha
      PQ_inf := by
        refine eq_bot_iff.2 fun g hg => ?_
        have h1 := (H.mem_Q).1 hg.2
        have : g = 1 := H.act_inj_P hg.1 (Subgroup.one_mem _) (by rw [h1.2, act_one])
        rw [this]
        exact Subgroup.one_mem _
      x_mem_Q := H.x_mem_Q
      P_dihedral := P_dihedral H hA
      z_mem := hz
      z_order := z_order H hA hz hzb
      z_central := fun a ha => z_central H hA hz hzb ha
      z_unique := fun c hc hcc => z_unique_aux H hA hz hzb hc (fun a ha => (hcc a ha).symm)
      Q_shape := hQ
      f_mem := H.f_mem
      f_order := H.f_order
      f_not_mem := H.f_not_mem_PQ
      f_cent := H.f_cent
      h_mem := hhT
      h_sq := hh2
      kf_abelian := fun a ha b hb => commutator_mem_PQ H hA ha hb
      kf_invol := hinvol
      kf_h := hh
      kf_3B := fun t ht => cent_P_iff H hA hz hzb ht
      kf_conj_P := fun p hp hp2 => by
        obtain ⟨g, hgK, -, hg⟩ := field_conj_P H hA hz hzb hp hp2
        exact ⟨g⁻¹, by rw [← hg]; group⟩
      kf_conj_xP := fun p hp hp2 => by
        obtain ⟨g, hgK, -, hg⟩ := field_conj_P H hA hz hzb hp hp2
        have hgx : g * x = x * g := mem_centralizer_singleton_iff.1 (H.KC hgK)
        refine ⟨g⁻¹, ?_⟩
        calc g⁻¹⁻¹ * (x * z) * g⁻¹ = g * x * z * g⁻¹ := by group
          _ = x * (g * z * g⁻¹) := by rw [hgx]; group
          _ = x * p := by rw [← hg]; group
      kf_C := fun y hy hy2 hyR hyP => field_C H hA hz hzb hy hy2 hyR hyP
      kf_zC := fun g hg hgT => ⟨hgT, by
        simpa using H.KN g⁻¹ (Subgroup.inv_mem _ hg) z hz.2⟩
      kf_shear := fun w hw hw2 hwc hwQz => field_shear H hA hz hzb hw hw2 hwc hwQz
      kf_N := ⟨CMK (centralizer ({x} : Set G)) K, fun g hg n hn => H.CMK_normal hg hn, by
        rw [inf_comm]
        rfl⟩ }

end Aut

end Real34

end CFSG.GH74.GLS.C3.Layer1.P34Real
