module

public import CFSG.GH74.GLS.LU.Local.FiveL66l
public import CFSG.GH74.GLS.LU.Local.FiveNcount
public import CFSG.GH74.GLS.LU.Local.FiveS3
public import CFSG.GH74.GLS.LU.Local.FiveL66j

public section

open Subgroup CFSG CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS CFSG.GH74.GLS.LU CFSG.Blueprint CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

namespace CFSG.GH74.GLS.LU.Local.Five

section XFacts

variable {G : Type} [Group G] [Finite G] {z u x : G}

theorem x_mem_NN (hz2 : z * z = 1) (hu2 : u * u = 1) (hzu : z * u = u * z)
    (hxz : x * z * x⁻¹ = u) (hxu : x * u * x⁻¹ = z * u) : x ∈ NN z u := by
  refine mem_NN_of_conj_mem_UU hz2 hu2 hzu ?_ ?_
  · rw [hxz]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers u)
  · rw [hxu]
    exact (UU z u).mul_mem (Subgroup.mem_sup_left (Subgroup.mem_zpowers z))
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers u))

omit [Finite G] in
theorem x_cube_mem_PP (hu2 : u * u = 1) (hzu : z * u = u * z)
    (hxz : x * z * x⁻¹ = u) (hxu : x * u * x⁻¹ = z * u) : x ^ 3 ∈ PP z u := by
  have hxzu : x * (z * u) * x⁻¹ = z := by
    calc x * (z * u) * x⁻¹ = (x * z * x⁻¹) * (x * u * x⁻¹) := by group
      _ = u * (z * u) := by rw [hxz, hxu]
      _ = (u * z) * u := by group
      _ = (z * u) * u := by rw [hzu]
      _ = z * (u * u) := by group
      _ = z := by rw [hu2, mul_one]
  have h3 : x ^ 3 = x * x * x := pow_three' x
  have e1 : x * x * x * z * (x * x * x)⁻¹ = z := by
    calc x * x * x * z * (x * x * x)⁻¹ = x * (x * (x * z * x⁻¹) * x⁻¹) * x⁻¹ := by group
      _ = z := by rw [hxz, hxu, hxzu]
  have e2 : x * x * x * u * (x * x * x)⁻¹ = u := by
    calc x * x * x * u * (x * x * x)⁻¹ = x * (x * (x * u * x⁻¹) * x⁻¹) * x⁻¹ := by group
      _ = u := by rw [hxu, hxzu, hxz]
  rw [h3]
  exact mem_PP.mpr ⟨mul_inv_eq_iff_eq_mul.mp e1, mul_inv_eq_iff_eq_mul.mp e2⟩

omit [Finite G] in
theorem conj_mem_PP {n p : G} (hn : n ∈ NN z u) (hp : p ∈ PP z u) : n * p * n⁻¹ ∈ PP z u := by
  have hzU : z ∈ UU z u := Subgroup.mem_sup_left (Subgroup.mem_zpowers z)
  have huU : u ∈ UU z u := Subgroup.mem_sup_right (Subgroup.mem_zpowers u)
  have hpU : ∀ a ∈ UU z u, p * a = a * p := fun a ha =>
    (Subgroup.mem_centralizer_iff.mp hp a ha).symm
  have key : ∀ a ∈ UU z u, (n * p * n⁻¹) * a = a * (n * p * n⁻¹) := by
    intro a ha
    have ha' : n⁻¹ * a * n ∈ UU z u := conj_mem_UU_of_mem_NN hn ha
    have h1 := hpU _ ha'
    calc n * p * n⁻¹ * a = n * (p * (n⁻¹ * a * n)) * n⁻¹ := by group
      _ = n * ((n⁻¹ * a * n) * p) * n⁻¹ := by rw [h1]
      _ = a * (n * p * n⁻¹) := by group
  exact mem_PP.mpr ⟨key z hzU, key u huU⟩

end XFacts

section CentPH

variable {G : Type} [Group G] {z u : G} {H : Subgroup G}

@[expose] def CentPH (z u : G) (H : Subgroup G) (n : G) : Prop :=
  ∀ p ∈ PP z u, n * p * n⁻¹ * p⁻¹ ∈ H

theorem CentPH.one : CentPH z u H 1 := fun p _ => by simp

theorem CentPH.mul {n₁ n₂ : G} (hn₁ : cjL n₁ H = H) (h₁ : CentPH z u H n₁) (h₂ : CentPH z u H n₂) :
    CentPH z u H (n₁ * n₂) := by
  intro p hp
  have e : n₁ * n₂ * p * (n₁ * n₂)⁻¹ * p⁻¹ =
      (n₁ * (n₂ * p * n₂⁻¹ * p⁻¹) * n₁⁻¹) * (n₁ * p * n₁⁻¹ * p⁻¹) := by group
  rw [e]
  refine H.mul_mem ?_ (h₁ p hp)
  have := mem_cjL_self (g := n₁) (h₂ p hp)
  rwa [hn₁] at this

theorem CentPH.inv {n : G} (hn : cjL n⁻¹ H = H) (h : CentPH z u H n) : CentPH z u H n⁻¹ := by
  intro p hp
  have e : n⁻¹ * p * n⁻¹⁻¹ * p⁻¹ = n⁻¹ * (n * p * n⁻¹ * p⁻¹)⁻¹ * n⁻¹⁻¹ := by group
  rw [e]
  have := mem_cjL_self (g := n⁻¹) (H.inv_mem (h p hp))
  rwa [hn] at this

theorem centPH_of_mem_PP (hnorm : ∀ p ∈ PP z u, cjL p H = H) (hsq : ∀ p ∈ PP z u, p * p ∈ H)
    {n : G} (hn : n ∈ PP z u) : CentPH z u H n :=
  comm_mem_of_sq_mem hnorm hsq n hn

theorem CentPH.conj {n g : G} (hg : g ∈ NN z u) (hgH : cjL g H = H) (h : CentPH z u H n) :
    CentPH z u H (g * n * g⁻¹) := by
  intro p hp
  have hp' : g⁻¹ * p * g ∈ PP z u := by
    have := conj_mem_PP ((NN z u).inv_mem hg) hp
    simpa using this
  have e : g * n * g⁻¹ * p * (g * n * g⁻¹)⁻¹ * p⁻¹ =
      g * (n * (g⁻¹ * p * g) * n⁻¹ * (g⁻¹ * p * g)⁻¹) * g⁻¹ := by group
  rw [e]
  have := mem_cjL_self (g := g) (h _ hp')
  rwa [hgH] at this

@[expose] def centSub (z u : G) (H : Subgroup G) (hNH : ∀ n ∈ NN z u, cjL n H = H) :
    Subgroup ↥(NN z u) where
  carrier := {n | CentPH z u H n.1}
  one_mem' := CentPH.one
  mul_mem' := fun {a _} ha hb => CentPH.mul (hNH a.1 a.2) ha hb
  inv_mem' := fun {a} ha => CentPH.inv (hNH (a⁻¹).1 (a⁻¹).2) ha

theorem centSub_normal (hNH : ∀ n ∈ NN z u, cjL n H = H) : (centSub z u H hNH).Normal := by
  refine ⟨fun n hn g => ?_⟩
  exact CentPH.conj g.2 (hNH g.1 g.2) hn

end CentPH

section CentNotX

variable {G : Type} [Group G] [Finite G] {p f : ℕ} {z : G} {S : Sylow 2 G} {K₁ K₂ H : Subgroup G}
  {t u w₁ : G} {Gs : Type} [Group Gs] {z' t' u' : Gs} {S' : Sylow 2 Gs} {K₁' K₂' : Subgroup Gs}
  {ht : t ∈ Cz z} {hu : u ∈ Cz z} {ψ : ↥(Cz z) ≃* ↥(Cz z')}

theorem not_centPH_x (c : FiveCtx G p f z S K₁ K₂ t u) (b66 : Five66W z t u K₁ K₂ H w₁) {x : G}
    (hxz : x * z * x⁻¹ = u) (hxu : x * u * x⁻¹ = z * u) : ¬ CentPH z u H x := by
  intro hcent
  have hztc : z * t = t * z := c.hs.zt_comm
  have hut : u * t = t * u := c.hs.ut
  have hxuz : x⁻¹ * u * x = z := by rw [← hxz]; group
  have hxzu : x⁻¹ * (z * u) * x = u := by rw [← hxu]; group
  have htL : t ∈ normalizer ((cj K₁ x⁻¹ : Subgroup G) : Set G) :=
    t_norm_L c.toLUCtx (h₀ := x⁻¹) (by simpa using hxz)
  have hpN : x⁻¹ * t * x ∈ normalizer (K₁ : Set G) := by
    apply CFSG.Walter.J1.mem_normalizer_of_conj_mem
    intro k hk
    have h1 : x * k * x⁻¹ ∈ cj K₁ x⁻¹ := by
      have e0 : x⁻¹ * (x * k * x⁻¹) * x⁻¹⁻¹ = k := by group
      rw [mem_cj, e0]; exact hk
    have h2 : t * (x * k * x⁻¹) * t⁻¹ ∈ cj K₁ x⁻¹ :=
      ((Subgroup.mem_normalizer_iff.mp htL _).mp h1)
    have h3 := mem_cj.mp h2
    have e : x⁻¹ * (t * (x * k * x⁻¹) * t⁻¹) * x⁻¹⁻¹ = (x⁻¹ * t * x) * k * (x⁻¹ * t * x)⁻¹ := by
      group
    rwa [e] at h3
  have hpP : x⁻¹ * t * x ∈ PP z u := by
    refine mem_PP.mpr ⟨?_, ?_⟩
    · calc x⁻¹ * t * x * z = x⁻¹ * t * (x * z * x⁻¹) * x := by group
        _ = x⁻¹ * (t * u) * x := by rw [hxz]; group
        _ = x⁻¹ * (u * t) * x := by rw [hut]
        _ = (x⁻¹ * u * x) * (x⁻¹ * t * x) := by group
        _ = z * (x⁻¹ * t * x) := by rw [hxuz]
    · have htzu : t * (z * u) = (z * u) * t := by
        calc t * (z * u) = (t * z) * u := by group
          _ = (z * t) * u := by rw [hztc]
          _ = z * (t * u) := by group
          _ = z * (u * t) := by rw [hut]
          _ = (z * u) * t := by group
      calc x⁻¹ * t * x * u = x⁻¹ * t * (x * u * x⁻¹) * x := by group
        _ = x⁻¹ * (t * (z * u)) * x := by rw [hxu]; group
        _ = x⁻¹ * ((z * u) * t) * x := by rw [htzu]
        _ = (x⁻¹ * (z * u) * x) * (x⁻¹ * t * x) := by group
        _ = u * (x⁻¹ * t * x) := by rw [hxzu]
  have hH := hcent _ hpP
  have e : x * (x⁻¹ * t * x) * x⁻¹ * (x⁻¹ * t * x)⁻¹ = t * (x⁻¹ * t * x)⁻¹ := by group
  rw [e] at hH
  have hp1 : cjL (x⁻¹ * t * x) K₁ = K₁ := cjL_eq_of_mem_normalizer hpN
  have hh1 : cjL (t * (x⁻¹ * t * x)⁻¹) K₁ = K₁ := (b66.H_normK _ hH).1
  have ht1 : cjL t K₁ = K₁ := by
    have e2 : t = (t * (x⁻¹ * t * x)⁻¹) * (x⁻¹ * t * x) := by group
    calc cjL t K₁ = cjL ((t * (x⁻¹ * t * x)⁻¹) * (x⁻¹ * t * x)) K₁ := by rw [← e2]
      _ = cjL (t * (x⁻¹ * t * x)⁻¹) (cjL (x⁻¹ * t * x) K₁) := (cjL_cjL _ _ _).symm
      _ = K₁ := by rw [hp1, hh1]
  exact c.hc.ne (ht1.symm.trans c.hs.t_swap)

end CentNotX

section CentPP

variable {G : Type} [Group G] [Finite G] {p f : ℕ} {z : G} {S : Sylow 2 G} {K₁ K₂ H : Subgroup G}
  {t u w₁ : G} {Gs : Type} [Group Gs] {z' t' u' : Gs} {S' : Sylow 2 Gs} {K₁' K₂' : Subgroup Gs}
  {ψ : ↥(Cz z) ≃* ↥(Cz z')}

theorem ModelPic.centPH_imp_PP (c : FiveCtx G p f z S K₁ K₂ t u)
    (pic : ModelPic z t u K₁ K₂ c.t_mem_Cz c.u_mem_Cz z' S' K₁' K₂' t' u' ψ)
    (b66 : Five66W z t u K₁ K₂ H w₁) (hNH : ∀ n ∈ NN z u, cjL n H = H) {x : G}
    (hxz : x * z * x⁻¹ = u) (hxu : x * u * x⁻¹ = z * u) {n : G} (hn : n ∈ NN z u)
    (hcent : CentPH z u H n) : n ∈ PP z u := by
  have hz2 : z * z = 1 := c.hs.z_sq
  have hu2 : u * u = 1 := c.hs.u_sq
  have hzu : z * u = u * z := c.hs.zu_comm
  have hz1 : z ≠ 1 := c.z_ne_one
  have hu1 : u ≠ 1 := by
    intro h
    have := c.hs.u_ord
    rw [h, orderOf_one] at this
    omega
  have huz : u ≠ z := c.hs.u_ne
  have hxN : x ∈ NN z u := x_mem_NN hz2 hu2 hzu hxz hxu
  obtain ⟨hPnorm, hPsq⟩ := pic.PP_facts b66
  have hwz : w₁ * z * w₁⁻¹ = z := by
    calc w₁ * z * w₁⁻¹ = (z * w₁) * w₁⁻¹ := by rw [c.hc.cz₁ b66.w₁_mem]
      _ = z := by group
  have hsurj := rhoUSharp_surjective hz2 hu2 hzu hz1 hu1 huz hwz b66.w₁_u hxz hxu
  have hT : Nat.card (USharp z u) = 3 := card_USharp hz2 hu2 hzu hz1 hu1 huz
  have hker := ker_rhoUSharp hz1 hu1
  by_contra hnP
  have hρn : rhoUSharp z u ⟨n, hn⟩ ≠ 1 := by
    intro h
    apply hnP
    have h1 : (⟨n, hn⟩ : ↥(NN z u)) ∈ (rhoUSharp z u).ker := h
    rw [hker] at h1
    exact h1
  have : (centSub z u H hNH).Normal := centSub_normal hNH
  have : ((centSub z u H hNH).map (rhoUSharp z u)).Normal :=
    Subgroup.Normal.map inferInstance (rhoUSharp z u) hsurj
  have hnC : (⟨n, hn⟩ : ↥(NN z u)) ∈ centSub z u H hNH := hcent
  have hτ3 : rhoUSharp z u ⟨x, hxN⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have h1 : (⟨x, hxN⟩ : ↥(NN z u)) ^ 3 ∈ (rhoUSharp z u).ker := by
      rw [hker]
      exact x_cube_mem_PP hu2 hzu hxz hxu
    exact h1
  have hmem : rhoUSharp z u ⟨x, hxN⟩ ∈ (centSub z u H hNH).map (rhoUSharp z u) :=
    perm3_normal_gen hT _ (Subgroup.mem_map_of_mem _ hnC) hρn hτ3
  obtain ⟨cc, hcc, hρcc⟩ := Subgroup.mem_map.mp hmem
  have hker2 : cc⁻¹ * ⟨x, hxN⟩ ∈ (rhoUSharp z u).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hρcc, inv_mul_cancel]
  rw [hker] at hker2
  have hP2 : (cc : G)⁻¹ * x ∈ PP z u := hker2
  have hc2 : CentPH z u H ((cc : G)⁻¹ * x) := centPH_of_mem_PP hPnorm hPsq hP2
  have hx' : CentPH z u H x := by
    have h1 := CentPH.mul (hNH cc.1 cc.2) hcc hc2
    have e : (cc : G) * ((cc : G)⁻¹ * x) = x := by group
    rwa [e] at h1
  exact not_centPH_x c b66 hxz hxu hx'

end CentPP

end CFSG.GH74.GLS.LU.Local.Five
