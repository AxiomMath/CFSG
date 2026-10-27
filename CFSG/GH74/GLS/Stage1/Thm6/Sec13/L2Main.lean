module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.L2Act
public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.L2Fus
public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.L2Aut
public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.L2CaseB

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec13

open Subgroup Equiv
open scoped commutatorElement

variable {G : Type} [Group G]

structure Final4 (x : G) (T V H : Subgroup G) (f : G) (y₁ : G) : Prop where
  T16 : Nat.card T = 16
  h64 : Nat.card ↥(H ⊔ T) = 64
  hsq : ∀ s ∈ H ⊔ T, s * s ∈ Hzero H f
  free₁ : IsFreeConj x (Hzero H f) y₁
  y₁S : y₁ ∈ H ⊔ T
  y₁H : y₁ ∉ H
  cls : ∀ s ∈ H ⊔ T, ∃ p ∈ Hzero H f, s = p ∨ s = p * x ∨ s = p * y₁ ∨ s = p * (x * y₁)
  reps : ∀ s ∈ H ⊔ T, s ∉ Hzero H f →
    ∃ y' : G, IsFreeConj x (Hzero H f) y' ∧ ∃ p ∈ Hzero H f, s = p * y'

namespace Ctx2S

variable {x : G} {T V H : Subgroup G} {f : G} {y₁ : G} {S : Subgroup G}
  (c : Ctx2S G x T V H f S) (d : Final4 x T V H f y₁)
include c d

omit d in
theorem Hs_le_N : H ⊔ T ≤ normalizer ((Hzero H f : Subgroup G) : Set G) :=
  c.Hs_le_S0.trans inf_le_right

theorem Hs_comm_in_P : ∀ a ∈ H ⊔ T, ∀ b ∈ H ⊔ T, a * b * a⁻¹ * b⁻¹ ∈ Hzero H f := by
  intro a ha b hb
  have := c.normIn_Hs.normal
  have hR2 : ∀ r : ↥(H ⊔ T) ⧸ (Hzero H f).subgroupOf (H ⊔ T), r * r = 1 := by
    intro r
    obtain ⟨⟨s, hs⟩, rfl⟩ := (QuotientGroup.mk'_surjective _) r
    show qm (H ⊔ T) (Hzero H f) ⟨s, hs⟩ * qm (H ⊔ T) (Hzero H f) ⟨s, hs⟩ = 1
    rw [← map_mul]
    exact qm_eq_one.2 (d.hsq s hs)
  have hc := exp_two_comm hR2 (qm (H ⊔ T) (Hzero H f) ⟨a, ha⟩) (qm (H ⊔ T) (Hzero H f) ⟨b, hb⟩)
  have h : ⁅qm (H ⊔ T) (Hzero H f) ⟨a, ha⟩, qm (H ⊔ T) (Hzero H f) ⟨b, hb⟩⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.2 hc
  rw [← map_commutatorElement, qm_eq_one] at h
  exact h

theorem rho_Hs_eq_one_iff [Finite G] {s : G} (hs : s ∈ H ⊔ T) :
    rho (Hzero H f) s = 1 ↔ s ∈ Hzero H f := by
  constructor
  · intro h
    apply c.cent_eq_P d.reps s hs
    exact (rho_eq_one_iff (c.Hs_le_N hs)).1 h
  · intro h
    exact rho_of_mem_P c.c2.P_comm h

theorem card_imgS [Finite G] : Nat.card (imgS (Hzero H f) (H ⊔ T)) = 4 := by
  let ψ : ↥(H ⊔ T) →* MulAut ↥(Hzero H f) :=
    { toFun := fun s => rho (Hzero H f) s.1
      map_one' := rho_one
      map_mul' := fun a b => rho_mul (c.Hs_le_N a.2) (c.Hs_le_N b.2) }
  have hrange : ψ.range = imgS (Hzero H f) (H ⊔ T) := by
    ext σ
    rw [mem_imgS_rho]
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨s.1, s.2, c.Hs_le_N s.2, rfl⟩
    · rintro ⟨s, hs, hsN, rfl⟩
      exact ⟨⟨s, hs⟩, rfl⟩
  have hker : ψ.ker = (Hzero H f).subgroupOf (H ⊔ T) := by
    ext s
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    exact c.rho_Hs_eq_one_iff d s.2
  have h := Subgroup.card_ker_mul_card_range ψ
  rw [hker, hrange, d.h64] at h
  have e : Nat.card ((Hzero H f).subgroupOf (H ⊔ T)) = Nat.card (Hzero H f) :=
    Nat.card_congr (subgroupOfEquivOfLe (c.normIn_Hs.le)).toEquiv
  rw [e, c.c2.P_card] at h
  omega

theorem imgS_four [Finite G] : IsFourGroup (imgS (Hzero H f) (H ⊔ T)) := by
  refine ⟨?_, c.card_imgS d⟩
  have hN := c.Hs_le_N
  intro σ hσ
  obtain ⟨s, hs, hsN, rfl⟩ := mem_imgS_rho.1 hσ
  refine ⟨?_, fun τ hτ => ?_⟩
  · rw [← rho_mul hsN hsN]
    exact rho_of_mem_P c.c2.P_comm (d.hsq s hs)
  · obtain ⟨s', hs', hs'N, rfl⟩ := mem_imgS_rho.1 hτ
    rw [← rho_mul hsN hs'N, ← rho_mul hs'N hsN]
    apply rho_eq_of_quot c.c2.P_comm ((normalizer _).mul_mem hsN hs'N)
      ((normalizer _).mul_mem hs'N hsN)
    have := c.Hs_comm_in_P d s'⁻¹ ((H ⊔ T).inv_mem hs') s⁻¹ ((H ⊔ T).inv_mem hs)
    have e : (s * s')⁻¹ * (s' * s) = s'⁻¹ * s⁻¹ * s'⁻¹⁻¹ * s⁻¹⁻¹ := by group
    rw [e]; exact this

end Ctx2S

namespace Ctx2S

variable {x : G} {T V H : Subgroup G} {f : G} {y₁ : G} {S : Subgroup G}
  (c : Ctx2S G x T V H f S) (d : Final4 x T V H f y₁)
include c d

theorem fix_of_mem_W [Finite G] {w : G} (hwV : w ∈ V) (hwy : y₁ * w * y₁⁻¹ = w) {s : G} (hs : s ∈ H ⊔ T) :
    s * w * s⁻¹ = w := by
  have hP := c.c2.c3
  have hwP : w ∈ Hzero H f := hP.V_le_H0 hwV
  have hxw : x * w * x⁻¹ = w := by
    have := hP.x_comm_V hwV
    calc x * w * x⁻¹ = (w * x) * x⁻¹ := by rw [this]
      _ = w := by group
  obtain ⟨p, hp, h | h | h | h⟩ := d.cls s hs
  · rw [h]
    have := c.c2.P_comm p hp w hwP
    calc p * w * p⁻¹ = (w * p) * p⁻¹ := by rw [this]
      _ = w := by group
  · rw [h]
    have h1 : p * x * w * (p * x)⁻¹ = p * (x * w * x⁻¹) * p⁻¹ := by group
    rw [h1, hxw]
    have := c.c2.P_comm p hp w hwP
    calc p * w * p⁻¹ = (w * p) * p⁻¹ := by rw [this]
      _ = w := by group
  · rw [h]
    have h1 : p * y₁ * w * (p * y₁)⁻¹ = p * (y₁ * w * y₁⁻¹) * p⁻¹ := by group
    rw [h1, hwy]
    have := c.c2.P_comm p hp w hwP
    calc p * w * p⁻¹ = (w * p) * p⁻¹ := by rw [this]
      _ = w := by group
  · rw [h]
    have h1 : p * (x * y₁) * w * (p * (x * y₁))⁻¹ = p * (x * (y₁ * w * y₁⁻¹) * x⁻¹) * p⁻¹ := by group
    rw [h1, hwy, hxw]
    have := c.c2.P_comm p hp w hwP
    calc p * w * p⁻¹ = (w * p) * p⁻¹ := by rw [this]
      _ = w := by group

theorem fix_card [Finite G] :
    Nat.card {e : ↥(Hzero H f) // ∀ σ ∈ imgS (Hzero H f) (H ⊔ T), σ e = e} = 2 := by
  have hP := c.c2.c3
  have hN := c.Hs_le_N
  have hxS : x ∈ H ⊔ T := Subgroup.mem_sup_left hP.x_mem_H
  let W : Subgroup G := V ⊓ centralizer ({y₁} : Set G)
  have hxσ : rho (Hzero H f) x ∈ imgS (Hzero H f) (H ⊔ T) :=
    mem_imgS_rho.2 ⟨x, hxS, hN hxS, rfl⟩
  have hyσ : rho (Hzero H f) y₁ ∈ imgS (Hzero H f) (H ⊔ T) :=
    mem_imgS_rho.2 ⟨y₁, d.y₁S, hN d.y₁S, rfl⟩
  have hW : ∀ e : {e : ↥(Hzero H f) // ∀ σ ∈ imgS (Hzero H f) (H ⊔ T), σ e = e}, (e.1 : G) ∈ W := by
    intro e
    have h1 := e.2 _ hxσ
    have h2 := e.2 _ hyσ
    have h1' : x * (e.1 : G) * x⁻¹ = e.1 := by
      have := congrArg (fun m : ↥(Hzero H f) => (m : G)) h1
      rw [rho_apply (hN hxS)] at this
      exact this
    have h2' : y₁ * (e.1 : G) * y₁⁻¹ = e.1 := by
      have := congrArg (fun m : ↥(Hzero H f) => (m : G)) h2
      rw [rho_apply (hN d.y₁S)] at this
      exact this
    refine ⟨?_, ?_⟩
    · rw [← hP.C_H0_x]
      refine ⟨e.1.2, ?_⟩
      show (e.1 : G) ∈ centralizer ({x} : Set G)
      rw [mem_centralizer_iff]
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      rw [hw]
      calc x * (e.1 : G) = (x * (e.1 : G) * x⁻¹) * x := by group
        _ = (e.1 : G) * x := by rw [h1']
    · show (e.1 : G) ∈ centralizer ({y₁} : Set G)
      rw [mem_centralizer_iff]
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      rw [hw]
      calc y₁ * (e.1 : G) = (y₁ * (e.1 : G) * y₁⁻¹) * y₁ := by group
        _ = (e.1 : G) * y₁ := by rw [h2']
  have hcard : Nat.card {e : ↥(Hzero H f) // ∀ σ ∈ imgS (Hzero H f) (H ⊔ T), σ e = e} = Nat.card W := by
    apply Nat.card_congr
    exact
      { toFun := fun e => ⟨e.1.1, hW e⟩
        invFun := fun w => ⟨⟨w.1, hP.V_le_H0 w.2.1⟩, fun σ hσ => by
          obtain ⟨s, hs, hsN, rfl⟩ := mem_imgS_rho.1 hσ
          apply Subtype.ext
          rw [rho_apply hsN]
          have hwy : y₁ * (w : G) * y₁⁻¹ = w := by
            have := mem_centralizer_iff.1 w.2.2 y₁ rfl
            calc y₁ * (w : G) * y₁⁻¹ = ((w : G) * y₁) * y₁⁻¹ := by rw [this]
              _ = w := by group
          exact c.fix_of_mem_W d w.2.1 hwy hs⟩
        left_inv := fun e => rfl
        right_inv := fun w => rfl }
  rw [hcard]
  have hy₁ : y₁ * y₁ = 1 := d.free₁.sq c.c2
  have hVnot : ¬ y₁ ∈ centralizer (V : Set G) := by
    intro h
    have : y₁ ∈ (H ⊔ T) ⊓ centralizer (V : Set G) := ⟨d.y₁S, h⟩
    rw [hP.Hstar_inf_C] at this
    exact d.y₁H this
  have hWlt : W < V := by
    refine lt_of_le_of_ne inf_le_left (fun h => hVnot ?_)
    rw [mem_centralizer_iff]
    intro v hv
    have : v ∈ W := by rw [h]; exact hv
    exact (mem_centralizer_iff.1 this.2 y₁ rfl).symm
  have hV2 : IsPGroup 2 ↥V := IsPGroup.of_card (n := 2) (by rw [hP.out.V_four.2]; norm_num)
  have hy₁V : ∀ v ∈ V, y₁ * v * y₁⁻¹ ∈ V := by
    intro v hv
    exact (mem_normalizer_iff.1 (hP.Hstar_le_N d.y₁S) v).1 hv
  obtain ⟨z, hzV, hz1, hzy⟩ := exists_fixed_ne_one hy₁ hV2 (by rw [hP.out.V_four.2]; norm_num) hy₁V
  have hzW : z ∈ W := by
    refine ⟨hzV, ?_⟩
    show z ∈ centralizer ({y₁} : Set G)
    rw [mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    rw [hw]
    calc y₁ * z = (y₁ * z * y₁⁻¹) * y₁ := by group
      _ = z * y₁ := by rw [hzy]
  have h2 : 1 < Nat.card W := one_lt_card_of_ne_one hzW hz1
  have h3 := Subgroup.card_lt_of_lt hWlt
  rw [hP.out.V_four.2] at h3
  have hd : Nat.card W ∣ 4 := by
    have := Subgroup.card_dvd_of_le (inf_le_left : W ≤ V)
    rwa [hP.out.V_four.2] at this
  have hne3 : Nat.card W ≠ 3 := by
    intro h; rw [h] at hd; norm_num at hd
  omega

end Ctx2S


namespace Ctx2S

variable {x : G} {T V H : Subgroup G} {f : G} {y₁ : G} {S : Subgroup G}
  (c : Ctx2S G x T V H f S) (d : Final4 x T V H f y₁)
include c d

omit d in
theorem rho_x_ne_one [Finite G] : rho (Hzero H f) x ≠ 1 := by
  have hP := c.c2.c3
  have hxS : x ∈ H ⊔ T := Subgroup.mem_sup_left hP.x_mem_H
  intro h
  have h1 := (rho_eq_one_iff (c.Hs_le_N hxS)).1 h
  have hle : Hzero H f ≤ V := by
    intro p hp
    rw [← hP.C_H0_x]
    refine ⟨hp, ?_⟩
    show p ∈ centralizer ({x} : Set G)
    rw [mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    rw [hw]
    have := h1 p hp
    calc x * p = (x * p * x⁻¹) * x := by group
      _ = p * x := by rw [this]
  have := Subgroup.card_le_of_le hle
  rw [c.c2.P_card, hP.out.V_four.2] at this
  omega

theorem strongly_closed [Finite G] (h10 : IG_10_31) :
    ∀ a ∈ Hzero H f, ∀ g : G, g * a * g⁻¹ ∈ H ⊔ T → g * a * g⁻¹ ∈ Hzero H f := by
  intro a ha g hg
  by_contra hnot
  have ha2 : a * a = 1 := c.c2.P_sq a ha
  have hga2 : (g * a * g⁻¹) * (g * a * g⁻¹) = 1 := by
    calc (g * a * g⁻¹) * (g * a * g⁻¹) = g * (a * a) * g⁻¹ := by group
      _ = 1 := by rw [ha2]; group
  obtain ⟨w, hw⟩ := c.fusion_invol h10 d.reps _ hg hga2 hnot
  apply c.c2.not_fused (g⁻¹ * w)
  have : (g⁻¹ * w) * x * (g⁻¹ * w)⁻¹ = a := by
    calc (g⁻¹ * w) * x * (g⁻¹ * w)⁻¹ = g⁻¹ * (w * x * w⁻¹) * g := by group
      _ = g⁻¹ * (g * a * g⁻¹) * g := by rw [← hw]
      _ = a := by group
  rw [this]; exact ha

theorem conj_to_z [Finite G] (h10 : IG_10_31) (h1620 : IG_16_20) (hS : Sylow2In (H ⊔ T) ⊤) :
    ∀ σ ∈ imgS (Hzero H f) (H ⊔ T), σ ≠ 1 →
      ∃ g ∈ (actHom (Hzero H f)).range, g * rho (Hzero H f) x * g⁻¹ = σ := by
  have hP := c.c2.c3
  have hxS : x ∈ H ⊔ T := Subgroup.mem_sup_left hP.x_mem_H
  intro σ hσ hσ1
  obtain ⟨s, hs, hsN, rfl⟩ := mem_imgS_rho.1 hσ
  have hsP : s ∉ Hzero H f := fun h => hσ1 (rho_of_mem_P c.c2.P_comm h)
  obtain ⟨y', hy', p, hp, hsp⟩ := d.reps s hs hsP
  have hpN : p ∈ normalizer ((Hzero H f : Subgroup G) : Set G) := Subgroup.le_normalizer hp
  have hy'S : y' ∈ H ⊔ T := by
    have : y' = p⁻¹ * s := by rw [hsp]; group
    rw [this]
    exact (H ⊔ T).mul_mem ((H ⊔ T).inv_mem (Subgroup.mem_sup_left (hP.H0_le hp))) hs
  have hy'N : y' ∈ normalizer ((Hzero H f : Subgroup G) : Set G) := c.Hs_le_N hy'S
  have hrs : rho (Hzero H f) s = rho (Hzero H f) y' := by
    rw [hsp, rho_mul hpN hy'N, rho_of_mem_P c.c2.P_comm hp, one_mul]
  obtain ⟨⟨w, hw⟩, -⟩ := hy'
  have hwS : w * x * w⁻¹ ∈ H ⊔ T := hw ▸ hy'S
  obtain ⟨n, hnN, hn⟩ := h1620 G (H ⊔ T) (Hzero H f) hS c.normIn_Hs.le c.c2.P_comm
    (c.strongly_closed d h10) x hxS w hwS
  refine ⟨rho (Hzero H f) n, ⟨⟨n, hnN⟩, ?_⟩, ?_⟩
  · exact (rho_of_mem hnN).symm
  · rw [hrs, hw, ← hn, ← rho_inv hnN, ← rho_mul hnN (c.Hs_le_N hxS), ← rho_mul
      ((normalizer _).mul_mem hnN (c.Hs_le_N hxS)) ((normalizer _).inv_mem hnN)]

end Ctx2S

namespace Ctx2S

variable {x : G} {T V H : Subgroup G} {f : G} {y₁ : G} {S : Subgroup G}
  (c : Ctx2S G x T V H f S) (d : Final4 x T V H f y₁)
include c d

theorem all_invol_conj [Finite G] (h10 : IG_10_31) (h1620 : IG_16_20) (hS : Sylow2In (H ⊔ T) ⊤) :
    ∀ u ∈ (actHom (Hzero H f)).range, ∀ v ∈ (actHom (Hzero H f)).range, u ≠ 1 → u * u = 1 →
      v ≠ 1 → v * v = 1 → ∃ g ∈ (actHom (Hzero H f)).range, g * u * g⁻¹ = v := by
  have : Finite (MulAut ↥(Hzero H f)) :=
    Finite.of_injective (fun m : MulAut ↥(Hzero H f) => (m : ↥(Hzero H f) → ↥(Hzero H f)))
      DFunLike.coe_injective
  have hSylX : Sylow2In (imgS (Hzero H f) (H ⊔ T)) (actHom (Hzero H f)).range :=
    sylow2In_imgS hS c.Hs_le_N
  have key : ∀ u ∈ (actHom (Hzero H f)).range, u ≠ 1 → u * u = 1 →
      ∃ g ∈ (actHom (Hzero H f)).range, g * rho (Hzero H f) x * g⁻¹ = u := by
    intro u hu hu1 huu
    have hZ2 : IsPGroup 2 ↥(zpowers u) := by
      have hord : orderOf u = 2 := orderOf_eq_prime (by rw [pow_two]; exact huu) hu1
      exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord]; norm_num)
    obtain ⟨Q, hQ, huQ⟩ := SylowIn.exists_ge (p := 2)
      ((zpowers_le).2 hu : zpowers u ≤ (actHom (Hzero H f)).range) hZ2
    obtain ⟨cc, hccX, hcc⟩ := SylowIn.conj (p := 2) hSylX hQ
    have h1 : cc⁻¹ * u * cc ∈ imgS (Hzero H f) (H ⊔ T) :=
      (hcc u).1 (huQ (mem_zpowers u))
    have h2 : cc⁻¹ * u * cc ≠ 1 := by
      intro h
      apply hu1
      have : u = cc * (cc⁻¹ * u * cc) * cc⁻¹ := by group
      rw [this, h]; group
    obtain ⟨g, hgX, hg⟩ := c.conj_to_z d h10 h1620 hS _ h1 h2
    refine ⟨cc * g, (actHom (Hzero H f)).range.mul_mem hccX hgX, ?_⟩
    have : cc * g * rho (Hzero H f) x * (cc * g)⁻¹ = cc * (g * rho (Hzero H f) x * g⁻¹) * cc⁻¹ := by
      group
    rw [this, hg]; group
  intro u hu v hv hu1 huu hv1 hvv
  obtain ⟨a, haX, ha⟩ := key u hu hu1 huu
  obtain ⟨b, hbX, hb⟩ := key v hv hv1 hvv
  refine ⟨b * a⁻¹, (actHom (Hzero H f)).range.mul_mem hbX ((actHom (Hzero H f)).range.inv_mem haX), ?_⟩
  rw [← ha, ← hb]; group

end Ctx2S

namespace Ctx2S

variable {x : G} {T V H : Subgroup G} {f : G} {y₁ : G} {S : Subgroup G}
  (c : Ctx2S G x T V H f S) (d : Final4 x T V H f y₁)
include c d

theorem false_of_final4 [Finite G] (h10 : IG_10_31) (h1620 : IG_16_20) (h218 : IV2_2_18)
    (hS : Sylow2In (H ⊔ T) ⊤) : False := by
  have hP := c.c2.c3
  have hxS : x ∈ H ⊔ T := Subgroup.mem_sup_left hP.x_mem_H
  have hN := c.Hs_le_N
  have hSylX := sylow2In_imgS hS hN
  have hfour := c.imgS_four d
  have hfix := c.fix_card d
  have hxN := hN hxS
  have hy₁N := hN d.y₁S
  have hz : rho (Hzero H f) x ∈ imgS (Hzero H f) (H ⊔ T) :=
    mem_imgS_rho.2 ⟨x, hxS, hxN, rfl⟩
  have hy₁σ : rho (Hzero H f) y₁ ∈ imgS (Hzero H f) (H ⊔ T) :=
    mem_imgS_rho.2 ⟨y₁, d.y₁S, hy₁N, rfl⟩
  have hy₁2 : y₁ * y₁ = 1 := d.free₁.sq c.c2
  have hfN : f ∈ normalizer ((Hzero H f : Subgroup G) : Set G) := hP.f_norm_H0
  have hfx : f * x = x * f := hP.hI.f_comm_x
  have hfix4 : Nat.card {e : ↥(Hzero H f) // rho (Hzero H f) x e = e} = 4 := by
    rw [← hP.out.V_four.2]
    apply Nat.card_congr
    refine
      { toFun := fun e => ⟨e.1.1, ?_⟩
        invFun := fun v => ⟨⟨v.1, hP.V_le_H0 v.2⟩, ?_⟩
        left_inv := fun e => rfl
        right_inv := fun v => rfl }
    · have h1 := congrArg (fun m : ↥(Hzero H f) => (m : G)) e.2
      rw [rho_apply hxN] at h1
      rw [← hP.C_H0_x]
      refine ⟨e.1.2, ?_⟩
      show (e.1 : G) ∈ centralizer ({x} : Set G)
      rw [mem_centralizer_iff]
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      rw [hw]
      have h1' : x * (e.1 : G) * x⁻¹ = e.1 := h1
      calc x * (e.1 : G) = (x * (e.1 : G) * x⁻¹) * x := by group
        _ = (e.1 : G) * x := by rw [h1']
    · apply Subtype.ext
      rw [rho_apply hxN]
      have := hP.x_comm_V v.2
      calc x * (v : G) * x⁻¹ = (v * x) * x⁻¹ := by rw [this]
        _ = v := by group
  have hVnot : ¬ y₁ ∈ centralizer (V : Set G) := by
    intro h
    have : y₁ ∈ (H ⊔ T) ⊓ centralizer (V : Set G) := ⟨d.y₁S, h⟩
    rw [hP.Hstar_inf_C] at this
    exact d.y₁H this
  have hfV' : ¬ f ∈ centralizer (V : Set G) := hP.hc.f_not
  have hiso := autC_iso (E := ↥(Hzero H f))
    (fun e => Subtype.ext (c.c2.P_sq e e.2)) (fun a b => Subtype.ext (c.c2.P_comm a a.2 b b.2))
    ((actHom (Hzero H f)).range) (imgS (Hzero H f) (H ⊔ T)) hSylX
    (z := rho (Hzero H f) x) (t := rho (Hzero H f) y₁) (f := rho (Hzero H f) f)
    hz (c.rho_x_ne_one) (by rw [← rho_mul hxN hxN, hP.x_sq, rho_one])
    hy₁σ (by rw [← rho_mul hy₁N hy₁N, hy₁2, rho_one])
    (fun σ hσ => by
      obtain ⟨s, hs, hsN, rfl⟩ := mem_imgS_rho.1 hσ
      obtain ⟨p, hp, h | h | h | h⟩ := d.cls s hs
      · left
        rw [h]; exact rho_of_mem_P c.c2.P_comm hp
      · right; left
        rw [h, rho_mul (Subgroup.le_normalizer hp) hxN, rho_of_mem_P c.c2.P_comm hp, one_mul]
      · right; right; left
        rw [h, rho_mul (Subgroup.le_normalizer hp) hy₁N, rho_of_mem_P c.c2.P_comm hp, one_mul]
      · right; right; right
        rw [h, rho_mul (Subgroup.le_normalizer hp) ((normalizer _).mul_mem hxN hy₁N),
          rho_of_mem_P c.c2.P_comm hp, one_mul, rho_mul hxN hy₁N])
    (fun σ hσ => (hfour.1 σ hσ).2 _ hz) hfix4
    (by
      rw [mem_centralizer_iff] at hVnot
      push Not at hVnot
      obtain ⟨v, hv, hne⟩ := hVnot
      refine ⟨⟨v, hP.V_le_H0 hv⟩, ?_, ?_⟩
      · apply Subtype.ext
        rw [rho_apply hxN]
        have := hP.x_comm_V hv
        calc x * v * x⁻¹ = (v * x) * x⁻¹ := by rw [this]
          _ = v := by group
      · intro h
        apply hne
        have h1 := congrArg (fun m : ↥(Hzero H f) => (m : G)) h
        rw [rho_apply hy₁N] at h1
        have h2 : y₁ * v * y₁⁻¹ = v := h1
        calc v * y₁ = (y₁ * v * y₁⁻¹) * y₁ := by rw [h2]
          _ = y₁ * v := by group)
    ⟨⟨f, hfN⟩, (rho_of_mem hfN).symm⟩
    (by rw [← rho_mul hfN hxN, ← rho_mul hxN hfN, hfx])
    (by
      obtain ⟨k, hk⟩ := hP.hc.f3
      exact ⟨k, by rw [← rho_pow hfN, hk, rho_one]⟩)
    (by
      rw [mem_centralizer_iff] at hfV'
      push Not at hfV'
      obtain ⟨v, hv, hne⟩ := hfV'
      refine ⟨⟨v, hP.V_le_H0 hv⟩, ?_, ?_⟩
      · apply Subtype.ext
        rw [rho_apply hxN]
        have := hP.x_comm_V hv
        calc x * v * x⁻¹ = (v * x) * x⁻¹ := by rw [this]
          _ = v := by group
      · intro h
        apply hne
        have h1 := congrArg (fun m : ↥(Hzero H f) => (m : G)) h
        rw [rho_apply hfN] at h1
        have h2 : f * v * f⁻¹ = v := h1
        calc v * f = (f * v * f⁻¹) * f := by rw [h2]
          _ = f * v := by group)
  exact h218 ↥(Hzero H f) c.c2.e24 _ _ hSylX hfour hfix (rho (Hzero H f) x) hz
    (c.rho_x_ne_one) hiso (c.all_invol_conj d h10 h1620 hS)

end Ctx2S

theorem lemma13_2 (h9 : IG_9_16) (h10 : IG_10_31) (h15 : IG_15_15) (h1620 : IG_16_20)
    (h218 : IV2_2_18) : Lemma13_2 := by
  intro G _ _ x T V H f hout hc hp hne
  have c3 : Ctx3 G x T V H f := ⟨hout, hc, hp⟩
  have c2 : Ctx2 G x T V H f := ⟨c3, hne⟩
  obtain ⟨S, c⟩ := c2.exists_S h9
  have hS0 : ¬ S0 S (Hzero H f) < S := fun hlt => c.false_of_gamma h10 hlt
  have hS0le : S ≤ S0 S (Hzero H f) := by
    by_contra hnot
    exact hS0 (lt_of_le_of_ne (inf_le_left : S0 S (Hzero H f) ≤ S) (fun h => hnot h.symm.le))
  have hSeq : S = H ⊔ T := by
    by_contra hneq
    exact c.false_of_beta h10 h15 hS0le (lt_of_le_of_ne c.le (fun h => hneq h.symm))
  obtain ⟨hT16, h64, hsq⟩ := c.caseA_struct h15 hSeq
  obtain ⟨y₁, hfree₁, hy₁S, hy₁H, hcls, hreps⟩ := c.exists_free_reps h15 hSeq hT16 h64 hsq
  exact c.false_of_final4 (y₁ := y₁) ⟨hT16, h64, hsq, hfree₁, hy₁S, hy₁H, hcls, hreps⟩ h10 h1620
    h218 (hSeq ▸ c.syl)

end CFSG.GH74.GLS.Stage1.Thm6.Sec13
