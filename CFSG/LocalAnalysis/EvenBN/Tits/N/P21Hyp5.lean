module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.P21Hyp4
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P21Hyp3
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P21Rho
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P21Hyp2

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N

open Subgroup CFSG.LocalAnalysis.EvenBN.Tits.I21L

section Heavy

variable {G : Type} [Group G] [Finite G] {d : Data G} {z₀ : G}


theorem p21_isF20 (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h19 : Node19 d z₀)
    (h19b : Node19b d z₀) (h20 : Node20 d z₀) {y₁ : G} (hy : IsV1 d z₀ y₁) {u x : ↥(Ialpha d)}
    (hx : (x : MulAut ↥(Ws d)) = alpha d d.x₅) (hu : (u : MulAut ↥(Ws d)) = alpha d y₁) :
    P5.IsF20 x u := by
  have hx5 := p21_x5_mem_Ig h49 hd h19b h20
  have hy1 := p21_y1_mem_Ig h20 hy
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply Subtype.ext
    show (x : MulAut ↥(Ws d)) ^ 5 = 1
    rw [hx]
    exact p21_alpha_x5_pow_five hd hx5
  · intro h
    exact p21_alpha_x5_ne_one h49 hd h19 h19b h20 (hx ▸ congrArg Subtype.val h)
  · apply Subtype.ext
    show (u : MulAut ↥(Ws d)) ^ 4 = 1
    rw [hu, ← alpha_pow hy1 4, hy.pow_four hd hz, alpha_one]
  · apply Subtype.ext
    show (u : MulAut ↥(Ws d)) * x * (u : MulAut ↥(Ws d))⁻¹ = (x : MulAut ↥(Ws d)) ^ 3
    rw [hu, hx, ← alpha_pow hx5 3, ← hy.conj_x5 hd, alpha_conj hy1 hx5]

theorem p21_cent_Y (h49 : d.Thm49Statement) (hd : d.Hyp) (h19b : Node19b d z₀)
    (h20 : Node20 d z₀) {y₁ : G} (hy : IsV1 d z₀ y₁) {t u x : ↥(Ialpha d)}
    (ht : (t : MulAut ↥(Ws d)) = alpha d d.t) (hx : (x : MulAut ↥(Ws d)) = alpha d d.x₅)
    (hu : (u : MulAut ↥(Ws d)) = alpha d y₁) :
    centralizer ({t} : Set ↥(Ialpha d)) = zpowers t ⊔ (zpowers x ⊔ zpowers u) ∧
      Disjoint (zpowers t) (zpowers x ⊔ zpowers u) := by
  obtain ⟨-, hB, hC, -⟩ := h20.2.2.2.2.2.1 y₁ hy
  rw [p21_Alpha_Xg h49 hd h19b h20] at hB hC
  rw [← ht, ← hx, ← hu] at hB hC
  exact ⟨p21_transfer_cent (Ialpha d) hB, p21_transfer_disjoint (Ialpha d) hC⟩

theorem p21_hypYW (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h09 : Node09 d z₀)
    (h19 : Node19 d z₀) (h19b : Node19b d z₀) (h20 : Node20 d z₀) {y₁ : G} (hy : IsV1 d z₀ y₁)
    {i : G}
    (hfuse : alpha d (d.t * d.pv 2) = alpha d i * alpha d d.t * (alpha d i)⁻¹)
    {t u x h : ↥(Ialpha d)} (ht : (t : MulAut ↥(Ws d)) = alpha d d.t)
    (hx : (x : MulAut ↥(Ws d)) = alpha d d.x₅) (hu : (u : MulAut ↥(Ws d)) = alpha d y₁)
    (hh : (h : MulAut ↥(Ws d)) = alpha d i) :
    HypYW (rhoI d (elemAb2_Ws h19)) t u x h := by
  have htIg := p21_t_mem_Ig h09 h20
  obtain ⟨hcent, hdisj⟩ := p21_cent_Y h49 hd h19b h20 hy ht hx hu
  have hF := p21_isF20 h49 hd hz h19 h19b h20 hy hx hu
  have htt : t * t = 1 := by
    apply Subtype.ext
    show (t : MulAut ↥(Ws d)) * t = 1
    rw [ht, ← alpha_mul htIg htIg, hd.t_mul_self, alpha_one]
  have ht1 : t ≠ 1 := fun h1 =>
    p21_alpha_t_ne_one h19 h20 htIg (ht ▸ congrArg Subtype.val h1)
  have hx_c : x ∈ centralizer ({t} : Set ↥(Ialpha d)) := by
    rw [hcent]
    exact mem_sup_right (mem_sup_left (mem_zpowers x))
  refine ⟨finrank_Ws h19, rhoI_injective _, p21_secTwoHyp htt ht1 hF hdisj hcent, hF.orderOf_x, ?_,
    (mem_centralizer_singleton_iff.1 hx_c).symm, Or.inr hF.conj,
    hcent.trans (p21_closure_three t u x).symm, ?_⟩
  · intro v hv
    rw [rhoI_apply, hx] at hv
    have h1 : alpha d d.x₅ (EVec.toE (elemAb2_Ws h19) v) = EVec.toE (elemAb2_Ws h19) v := by
      have := congrArg (EVec.toE (elemAb2_Ws h19)) hv
      rwa [EVec.toE_ofE] at this
    have h2 := p21_fix_x5 h49 hd h19 h19b h20 h1
    rw [← EVec.ofE_toE (elemAb2_Ws h19) v, h2, EVec.ofE_one]
  · apply Subtype.ext
    show (h : MulAut ↥(Ws d)) * t * (h : MulAut ↥(Ws d))⁻¹ =
      (t : MulAut ↥(Ws d)) * (u : MulAut ↥(Ws d)) ^ 2
    rw [hh, ht, hu, pow_two, p21_alpha_y1_sq h49 hd hz h09 h20 hy, ← hfuse,
      alpha_mul htIg (p21_pv2_mem_Ig hd h20)]

theorem p21_hyp (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀)
    (h09 : Node09 d z₀) (h19 : Node19 d z₀) (h19b : Node19b d z₀) (h20 : Node20 d z₀) :
    ∃ (hW : ElemAb2 ↥(Ws d)) (t u x h : ↥(Ialpha d)),
      (t : MulAut ↥(Ws d)) = alpha d d.t ∧ (x : MulAut ↥(Ws d)) = alpha d d.x₅ ∧
      (Alpha d (Xg d)).subgroupOf (Ialpha d) = zpowers x ∧
      HypYW (rhoI d hW) t u x h := by
  obtain ⟨y₁, hy⟩ : ∃ y₁, IsV1 d z₀ y₁ := h09.2.2.2.2.2.2.2.2.2.2.2.2
  have hx5 := p21_x5_mem_Ig h49 hd h19b h20
  have ht := p21_t_mem_Ig h09 h20
  have hy1 := p21_y1_mem_Ig h20 hy
  obtain ⟨i, hi, hfuse⟩ := h20.2.2.2.2.2.2.2
  refine ⟨elemAb2_Ws h19, alphaHom d ⟨d.t, ht⟩, alphaHom d ⟨y₁, hy1⟩, alphaHom d ⟨d.x₅, hx5⟩,
    alphaHom d ⟨i, hi⟩, rfl, rfl, ?_,
    p21_hypYW h49 hd hz h09 h19 h19b h20 hy hfuse rfl rfl rfl rfl⟩
  rw [p21_Alpha_Xg h49 hd h19b h20]
  exact p21_zpowers_subgroupOf (Ialpha d) (alphaHom d ⟨d.x₅, hx5⟩)

end Heavy

end CFSG.LocalAnalysis.EvenBN.Tits.N
