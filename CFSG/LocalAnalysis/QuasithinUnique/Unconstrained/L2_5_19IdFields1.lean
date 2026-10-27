module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdNormC1

public section

namespace CFSG.QuasithinUnique.Id2519

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

section Elementary

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {hs : UnconstrainedSetting G T M}
  {N : Notation25 hs} {t zK i : G} {Ki KP : Subgroup G}

theorem exists_E4_K (h : Facts258 N) : ∃ E : Subgroup G, E ≤ N.K ∧ IsElemAbelian 2 E ∧ Nat.card E = 4 := by
  obtain ⟨E, hE, hE4⟩ := exists_four_of_shape (N.tuple.sylow.isPGroup.to_le N.SK_le_S)
    h.SK_shape
  exact ⟨E, hE.trans N.SK_le_K, hE4.1, hE4.2⟩

theorem Rgrp_le_normalizer_KP (hsh : Shape N t i Ki KP) :
    Rgrp2519 N i ≤ Subgroup.normalizer (KP : Set G) := fun _ hb =>
  hsh.mem_normalizer (Rgrp2519_le_centralizer N i hb)
    (Subgroup.centralizer_le_normalizer _ (Rgrp2519_le_centralizer_K N i hb))

theorem normalizes_R0 (hsh : Shape N t i Ki KP) {c : G}
    (hc : c ∈ N.S ⊓ Subgroup.centralizer ({i} : Set G))
    (hcK : c ∈ Subgroup.normalizer (N.K : Set G)) :
    c ∈ Subgroup.normalizer ((Rgrp2519 N i ⊓ Subgroup.centralizer (KP : Set G) : Subgroup G) :
      Set G) := by
  have hKP : c ∈ Subgroup.normalizer (KP : Set G) := hsh.mem_normalizer hc.2 hcK
  refine mem_normalizer_inf ?_ (mem_normalizer_centralizer hKP)
  unfold Rgrp2519
  exact mem_normalizer_inf (mem_normalizer_inf (Subgroup.le_normalizer hc.1)
    (Subgroup.le_normalizer hc.2)) (mem_normalizer_inf (Subgroup.le_normalizer hc.1)
    (mem_normalizer_centralizer hcK))

theorem i_mem_R0 (hi : Hyp2519 N i) (hsh : Shape N t i Ki KP) :
    i ∈ Rgrp2519 N i ⊓ Subgroup.centralizer (KP : Set G) :=
  ⟨hi.mem_R, Subgroup.mem_centralizer_iff.mpr fun _ hk =>
    Subgroup.mem_centralizer_singleton_iff.mp (hsh.KP_le hk)⟩

theorem KP_le_centralizer_of_mem_R0 {r : G}
    (hr : r ∈ Rgrp2519 N i ⊓ Subgroup.centralizer (KP : Set G)) :
    KP ≤ Subgroup.centralizer ({r} : Set G) := fun k hk =>
  Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hr.2 k hk)

end Elementary

section Fields1

variable {G : Type} [Group G] [Finite G] {K Ki KP : Subgroup G} {t i : G}

theorem Case1.three_rank (c : Case1 K Ki KP t i) :
    ∃ A : Subgroup G, A ≤ KP ∧ IsElemAbelian 3 A ∧ Nat.card A = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨a, ha⟩ := exists_order_three_of_isL2pType c.type
  have haG : orderOf (a : G) = 3 := (Subgroup.orderOf_coe a).trans ha
  obtain ⟨x, hx, hax⟩ := c.exists_diag' a.2
  have hy : t * x * t ∈ CFSG.conjugate Ki t := conj_involution_mem c.t_sq rfl hx
  have hxy : x * (t * x * t) = (t * x * t) * x :=
    BenderBranch.commute_of_commutator_eq_bot c.comm hx hy
  have h3 : (x * (t * x * t)) ^ 3 = 1 := by
    rw [← hax]
    have := pow_orderOf_eq_one (a : G)
    rwa [haG] at this
  rw [Commute.mul_pow (show Commute x (t * x * t) from hxy) 3] at h3
  have hxy3 := eq_and_eq_of_mul_eq_mul c.inf (Subgroup.pow_mem Ki hx 3) Ki.one_mem
    (Subgroup.pow_mem _ hy 3) (CFSG.conjugate Ki t).one_mem (by rw [h3, one_mul])
  have hx1 : x ≠ 1 := by
    intro h1
    rw [h1] at hax
    have : (a : G) = 1 := by rw [hax]; simp [c.t_sq]
    rw [this] at haG
    simp at haG
  have hy1 : t * x * t ≠ 1 := by
    intro h1
    apply hx1
    calc x = (t * t) * x * (t * t) := by rw [c.t_sq]; group
      _ = t * (t * x * t) * t := by group
      _ = 1 := by rw [h1, mul_one, c.t_sq]
  have hxo : orderOf x = 3 := orderOf_eq_prime hxy3.1 hx1
  have hyo : orderOf (t * x * t) = 3 := orderOf_eq_prime hxy3.2 hy1
  have hinf : Subgroup.zpowers x ⊓ Subgroup.zpowers (t * x * t) = ⊥ := by
    refine le_bot_iff.mp ?_
    rw [← c.inf]
    exact inf_le_inf (Subgroup.zpowers_le.mpr hx) (Subgroup.zpowers_le.mpr hy)
  obtain ⟨A, hA, hAab, hAc⟩ := exists_E9_of_commute hxo hyo hxy hinf
  refine ⟨A, ?_, hAab, hAc⟩
  rw [hA]
  refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
  · rw [c.KP_eq]; exact Subgroup.mem_sup_left hx
  · rw [c.KP_eq]; exact Subgroup.mem_sup_right hy

end Fields1

section Ident1

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {hs : UnconstrainedSetting G T M}
  {N : Notation25 hs} {t zK i : G} {Ki KP : Subgroup G}

theorem ident_case1 (hI : Inputs2519) (h : Lv2518 N t zK) (hi : Hyp2519 N i)
    (hsh : Shape N t i Ki KP) (hne : Ki ≠ CFSG.conjugate Ki t) :
    ∃ R2 : Subgroup G, Ident2519 N t i Ki KP R2 := by
  have hf := h.facts2511
  have c := case1_of_shape hI h hi hsh hne
  have hsimple := hs.setting.simple
  have hnonab := hs.setting.nonabelian
  have hq := hs.setting.qtke
  have hti : t * i = i * t := N.t_comm_of_mem_S hf hi.mem_S
  have hKperf : ⁅N.K, N.K⁆ = N.K :=
    Subgroup.isPerfect_iff.mp (BenderBranch.isQuasisimple_of_isComponentIn N.isComp).1
  have hindex : (Rgrp2519 N i ⊓ Subgroup.centralizer (KP : Set G)).relIndex (Rgrp2519 N i) = 2 :=
    c.relIndex_eq_two (Rgrp_le_normalizer_KP hsh) (Rgrp2519_le_centralizer_K N i)
      (N.t_mem_R hf hi.mem_S)
  refine ⟨Rgrp2519 N i ⊓ Subgroup.centralizer (KP : Set G), ?_⟩
  exact
    { comp := hsh.comp
      K_le := hsh.K_le
      KP_le := hsh.KP_le
      shape := Or.inl ⟨hne, c.KP_eq, c.comm⟩
      K_eq := by rw [c.diag]; exact (perfectResidualOf_of_perfect hKperf).symm
      three_rank := c.three_rank
      center_three := fun x hx _ => c.center_KP_trivial hx
      R2_le := inf_le_left
      R2_index := hindex
      R2_norm := fun _ _ _ _ c' hc' hcK => normalizes_R0 hsh hc' hcK
      R2_not_comp := fun r hr _ _ => c.not_isComponentIn (KP_le_centralizer_of_mem_R0 hr)
      R0_index := fun _ => hindex
      normal_C := fun _ j hj hj1 hj2 => by
        have hjS : j ∈ N.S := hj.1.1.1
        have hji : j * i = i * j := Subgroup.mem_centralizer_singleton_iff.mp hj.1.1.2
        exact normalC_case1 hI hsimple hnonab hq c (N.two_dvd_card_K h.facts258)
          (exists_E4_K h.facts258) hi.ne_one hi.mul_self hti hj1 (by rw [← sq]; exact hj2)
          hji (N.t_comm_of_mem_S hf hjS).symm hj.2
      perfect_cent := fun _ Y hYN hYK hY => c.perfect_cent hYN hYK hY }

end Ident1

end CFSG.QuasithinUnique.Id2519
