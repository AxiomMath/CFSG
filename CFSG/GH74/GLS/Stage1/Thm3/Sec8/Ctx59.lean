module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx58
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx55
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic19

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
open scoped commutatorElement Pointwise

namespace Setup8

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ W₁ W₂ U : Subgroup G} {u h : G}
  {Y E₁ E₂ : Subgroup G} {t w : G}

theorem false_of_cfg89 (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (h31 : IVK_3_1a_lifted) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h)
    (hP8 : Nat.card ↥(Pof S K₁) = 8) (hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ (1 + 1))
    (cfg : Cfg88 z S K₁ W₂ U u h Y t w) (hE : EData Y U E₁ E₂)
    (eY : Nonempty (↥Y ≃* Bg.TwoGroups.SylSL3_4))
    (h87 : ∀ s ∈ Pz S z, orderOf s = 2 → s⁻¹ * u * s = u * z →
      conjugate E₁ s = E₁ ∧ conjugate E₂ s = E₂)
    (h88a : ∀ y ∈ Y, orderOf (y * w) = 2 → Y ⊓ centralizer ({y * w} : Set G) = U)
    (h88b : conjugate E₁ w = E₂) : False := by
  obtain ⟨eY⟩ := eY
  have hY := cfg.hY
  have hUA : U ≤ Aof S K₁ W₂ h := hs.U_le_A hII hq hrec (le_refl _) hk
  have hUY : U ≤ Y := hUA.trans hY.A_le
  have hUN : ∀ y ∈ Y, ∀ c ∈ U, y * c * y⁻¹ ∈ U := fun y hy c hc =>
    hs.U_norm y (hY.Y_le_S hy) c hc
  obtain ⟨hcomm, hcentral⟩ := Basic.comm_central_of_equiv eY hUY hs.U_four.2 hUN
  have hsq : ∀ a ∈ Y, a * a ∈ U := Basic.sq_mem_of_equiv eY hUY hs.U_four.2 hUN
  have hwo : orderOf w = 2 := orderOf_eq_prime (by rw [pow_two]; exact cfg.hw2) cfg.hw1
  have hCw : Y ⊓ centralizer ({w} : Set G) = U := by
    have := h88a 1 (one_mem Y) (by rwa [one_mul])
    simpa using this
  have ht1 : t ≠ 1 := fun e => cfg.htW (e ▸ one_mem _)
  have ht2o : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact cfg.ht2) ht1
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right cfg.ht2
  have htu : t⁻¹ * u * t = u * z := by
    have := cfg.htu
    rw [ht'] at this ⊢
    exact this
  obtain ⟨h87t, -⟩ := h87 t cfg.htP ht2o htu
  have hswap := d_swap h87t h88b
  have hdP := d_not_P hs hE cfg hII h87 hswap
  obtain ⟨hC32, x₀, hx₀S, hx₀d, hx₀4⟩ :=
    hs.exists_x₀ hII cfg hE hUY hcentral hcomm hsq hswap hCw
  obtain ⟨hQ₁16, -, -, -⟩ := hs.case3 hII hq hrec hP8 cfg.hS256
  obtain ⟨w₁, hw₁S, hw₁u, hw₁4⟩ := hs.exists_w₁ hII hq hQ₁16
  have hdS : t * w ∈ S := Nh_le_S (d_mem_Nh cfg)
  obtain ⟨g, hgW, hgC⟩ := hs.transfer8 hII (Wsub S U) (t * w) W_le_S
    (hs.relIndex_W_eq_two hII hq hk) hdS (d_not_W cfg) (tw_sq cfg)
  have hcnt := Basic.card_cent_le_conj hgC
  set d' : G := g⁻¹ * (t * w) * g with hd'
  have hd'2 : d' * d' = 1 := by
    have : d' * d' = g⁻¹ * ((t * w) * (t * w)) * g := by rw [hd']; group
    rw [this, tw_sq cfg]
    group
  have hd'1 : d' ≠ 1 := by
    intro e
    apply d_ne_one cfg
    have : t * w = g * d' * g⁻¹ := by rw [hd']; group
    rw [this, e]
    group
  have hd'o : orderOf d' = 2 := orderOf_eq_prime (by rw [pow_two]; exact hd'2) hd'1
  have hx₀' : g⁻¹ * x₀ * g ∈ S := hgC x₀ hx₀S hx₀d
  have hx₀'c : (g⁻¹ * x₀ * g) * d' = d' * (g⁻¹ * x₀ * g) := by
    calc (g⁻¹ * x₀ * g) * d' = g⁻¹ * (x₀ * (t * w)) * g := by rw [hd']; group
      _ = g⁻¹ * ((t * w) * x₀) * g := by rw [hx₀d]
      _ = d' * (g⁻¹ * x₀ * g) := by rw [hd']; group
  have hx₀'4 : ((g⁻¹ * x₀ * g) * (g⁻¹ * x₀ * g)) * ((g⁻¹ * x₀ * g) * (g⁻¹ * x₀ * g)) =
      g⁻¹ * z * g := by
    have e := conj_pow (a := g⁻¹) (b := x₀) (i := 4)
    simp only [inv_inv] at e
    rw [hx₀4] at e
    have e4 : ((g⁻¹ * x₀ * g) * (g⁻¹ * x₀ * g)) * ((g⁻¹ * x₀ * g) * (g⁻¹ * x₀ * g)) =
        (g⁻¹ * x₀ * g) ^ 4 := by
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    rw [e4, e]
  have hgz : g⁻¹ * z * g ≠ 1 := by
    intro e
    apply hs.z_ne
    have : z = g * (g⁻¹ * z * g) * g⁻¹ := by group
    rw [this, e]
    group
  rcases W_dec cfg d' hgW with hd'Y | ⟨y, hy, hd'y⟩
  · by_cases hdU : d' ∈ U
    ·
      have hd'P : d' ∈ Pz S z := hs.U_le_Pz hII hq hdU
      have hconj : IsConj z d' := hs.invol_P_conj hII h31 d' hd'P hd'o
      have hdc : IsConj z (t * w) := hconj.trans (isConj_iff.2 ⟨g, by rw [hd']; group⟩)
      have hzP : z ∈ Pz S z := hs.U_le_Pz hII hq hs.z_mem
      have hdz : t * w ≠ z := fun e => hdP (by rw [e]; exact hzP)
      have huz : u ≠ z := fun e => hs.u_ne (by rw [e]; exact Subgroup.mem_zpowers z)
      exact Basic.no_fusion_contradiction (hs.m4 hII).S_syl (S4_mem_U cfg hsq) hs.U_elems hs.z_mem
        hs.u_mem hs.U_four.2 hs.z_sq hs.z_ne (hs.four_sq u hs.u_mem) huz hdz hdc hs.u_conj hx₀S hx₀d
        hx₀4 hw₁S hw₁u hw₁4 (hs.Z_S_le hII hq hrec cfg) (hs.no_conj_in_C hII hq hdS hdP)
    ·
      have hsq' : (g⁻¹ * x₀ * g) * (g⁻¹ * x₀ * g) ∈ Y := sq_mem_Y cfg _ hx₀'
      have hsqc : ((g⁻¹ * x₀ * g) * (g⁻¹ * x₀ * g)) * d' =
          d' * ((g⁻¹ * x₀ * g) * (g⁻¹ * x₀ * g)) := by
        calc ((g⁻¹ * x₀ * g) * (g⁻¹ * x₀ * g)) * d' =
            (g⁻¹ * x₀ * g) * ((g⁻¹ * x₀ * g) * d') := by group
          _ = (g⁻¹ * x₀ * g) * (d' * (g⁻¹ * x₀ * g)) := by rw [hx₀'c]
          _ = ((g⁻¹ * x₀ * g) * d') * (g⁻¹ * x₀ * g) := by group
          _ = (d' * (g⁻¹ * x₀ * g)) * (g⁻¹ * x₀ * g) := by rw [hx₀'c]
          _ = d' * ((g⁻¹ * x₀ * g) * (g⁻¹ * x₀ * g)) := by group
      obtain ⟨hc₁, hc₂⟩ := Basic.centralizer_noncentral eY hUY hs.U_four.2 hUN hE.le₁ hE.le₂
        hE.elem₁.1 (E₁_sq hE) hE.elem₂.1 (E₂_sq hE) hE.card₁ hE.card₂ hE.inter hE.prod
        (invol_of_EData hE)
      rcases invol_of_EData hE d' hd'Y hd'2 with hE1 | hE2
      · have hmem := hc₁ d' hE1 hdU _ hsq' hsqc
        have := E₁_sq hE _ hmem
        rw [hx₀'4] at this
        exact hgz this
      · have hmem := hc₂ d' hE2 hdU _ hsq' hsqc
        have := E₂_sq hE _ hmem
        rw [hx₀'4] at this
        exact hgz this
  ·
    have hyw2 : (y * w) * (y * w) = 1 := by rw [← hd'y]; exact hd'2
    have hyw1 : y * w ≠ 1 := by rw [← hd'y]; exact hd'1
    have hord : orderOf (y * w) = 2 := orderOf_eq_prime (by rw [pow_two]; exact hyw2) hyw1
    have hCyd : Y ⊓ centralizer ({d'} : Set G) = U := by rw [hd'y]; exact h88a y hy hord
    have hle : Nat.card ↥(S ⊓ centralizer ({d'} : Set G)) ≤
        4 * Nat.card ↥(Y ⊓ (S ⊓ centralizer ({d'} : Set G))) :=
      Basic.card_le_mul_inf inf_le_left (le_of_eq (relIndex_Y_S hII hs cfg))
    have hYS : Y ⊓ (S ⊓ centralizer ({d'} : Set G)) = Y ⊓ centralizer ({d'} : Set G) := by
      rw [← inf_assoc, inf_eq_left.2 hY.Y_le_S]
    rw [hYS, hCyd, hs.U_four.2] at hle
    omega

end Setup8

theorem lemma_8_9 (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (h31 : IVK_3_1a_lifted) : Lemma8_9 := by
  intro G _ _ z S K₁ K₂ W₁ W₂ U u h Y D t w hs hP8 hS7 hC E₁ E₂ hE
  by_contra hne
  have hw1 : w ≠ 1 := fun hw => hne (hs.card_S_eq_of_w_one hII hC hE hw)
  have cfg := hs.cfg88 hII hq hrec hP8 hS7 hC hE hw1
  have hV := hs.card_V₁ hII hq
  have hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ (1 + 1) := by norm_num; omega
  obtain ⟨h88a, h88b⟩ :=
    lemma_8_8 hII hq hrec G z S K₁ K₂ W₁ W₂ U u h Y D t w hs hP8 hS7 hC E₁ E₂ hE hw1
  exact hs.false_of_cfg89 hII hq hrec h31 hP8 hk cfg hE hC.2.2.1.2.2.2.1
    (fun s hsP hs2 hsu =>
      lemma_8_7 hII hq hrec G z S K₁ K₂ W₁ W₂ U u h Y D t w hs hP8 hS7 hC E₁ E₂ hE s hsP hs2 hsu)
    h88a h88b

end CFSG.GH74.GLS.Stage1.Thm3.Sec8
