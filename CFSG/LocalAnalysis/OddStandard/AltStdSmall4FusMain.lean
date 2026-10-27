module

public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4FusMainCent
public import CFSG.LocalAnalysis.OddStandard.AltStdEvenFusMainEight

public section

namespace CFSG.OddStandard.AltStdSmall4.Fus

open Subgroup Equiv

variable {G : Type} [Group G] [Finite G] {L Q : Subgroup G} {n : ℕ}
  {θ : L ≃* alternatingGroup (Fin n)} {z : G}

namespace Main

theorem exists_conj_of_isHStar (c : Config G L Q n θ z) {H : Subgroup G}
    {Nbar Rbar : Subgroup (Perm (Fin n))} {k : ℕ} {cc : Subgroup (Perm (Fin n)) → Prop}
    (hH : IsHStar c H Nbar) (hR : FusR n c.hn8 Nbar Rbar k cc)
    (hk : ∀ P : Sylow 2 (centralizer ({z} : Set G)), Nat.card P = 2 ^ (k + 1))
    (hcc : ∀ x ∈ normalizer (sSyl c H Rbar : Set G), x⁻¹ * z * x = z * w θ c.hn8 →
      x⁻¹ * w θ c.hn8 * x = w θ c.hn8 → ¬ cc (xBar c H x)) :
    ∃ g ∈ N0 θ c.hn8 z, g * z * g⁻¹ = z * w θ c.hn8 := by
  by_contra hneg
  push Not at hneg
  obtain ⟨x, hxN, hxz, hxw⟩ := hH.exists_x hR hk
  have htr := hR.tr_mem
  rcases hR.fx (xBar c H x) (hH.xBar_le htr hxN) (hH.tr_one_mem_xBar hxw)
      (hH.card_xBar htr hxN hxz hxw) (fun _ hσ => mul_self_of_mem_xBar hσ) with
    ⟨t, htN, ht2, htX, htc⟩ | ⟨g, hgN, hgX, hgw⟩ | hc
  ·
    obtain ⟨t', ht'H, ht'ρ⟩ := hH.surj t htN
    have ht'2 : (t' : G) ^ 2 ^ 1 = 1 := by
      have : t' * t' = 1 := hH.eq_of_rhoC_eq (mul_mem ht'H ht'H) (one_mem H)
        (by rw [map_mul, ht'ρ, ht2, map_one])
      rw [pow_one, sq]
      exact congrArg Subtype.val this
    have ht'X : ∀ y ∈ xSub θ c.hn8 z x H, (t' : G) * y = y * t' := by
      intro y hy
      have hyC : y ∈ centralizer ({z} : Set G) := hH.le (xSub_le_H hy)
      have h1 : t' * ⟨y, hyC⟩ = ⟨y, hyC⟩ * t' :=
        hH.eq_of_rhoC_eq (mul_mem ht'H (xSub_le_H hy)) (mul_mem (xSub_le_H hy) ht'H) (by
          rw [map_mul, map_mul, ht'ρ]
          exact htc _ (mem_xBar_iff.2 ⟨⟨y, hyC⟩, hy, rfl⟩))
      exact congrArg Subtype.val h1
    exact htX (mem_xBar_iff.2 ⟨t', hH.mem_xSub_of_comm htr hxN hxz hxw ht'H ht'2 ht'X, ht'ρ⟩)
  ·
    obtain ⟨g', hg'H, hg'ρ⟩ := hH.surj g hgN
    have hg'X : ∀ y ∈ xSub θ c.hn8 z x H, (g' : G) * y * (g' : G)⁻¹ ∈ xSub θ c.hn8 z x H := by
      intro y hy
      have hyC : y ∈ centralizer ({z} : Set G) := hH.le (xSub_le_H hy)
      obtain ⟨y', hy', hy'ρ⟩ := mem_xBar_iff.1 (hgX _ (mem_xBar_iff.2 ⟨⟨y, hyC⟩, hy, rfl⟩))
      have h1 : y' = g' * ⟨y, hyC⟩ * g'⁻¹ := hH.eq_of_rhoC_eq (xSub_le_H hy')
        (mul_mem (mul_mem hg'H (xSub_le_H hy)) (inv_mem hg'H))
        (by rw [hy'ρ, map_mul, map_mul, map_inv, hg'ρ])
      have h2 : (y' : G) = g' * y * (g' : G)⁻¹ := congrArg Subtype.val h1
      rw [← h2]
      exact hy'
    have hcomm := hH.comm_w_of_normalizes htr hxN hxz hxw hneg hg'H hg'X
    apply hgw
    have hwC : w θ c.hn8 ∈ centralizer ({z} : Set G) := L_le_cent c (w_mem_L c)
    have h1 : g' * ⟨w θ c.hn8, hwC⟩ = ⟨w θ c.hn8, hwC⟩ * g' := Subtype.ext hcomm
    have h2 := congrArg (rhoC c) h1
    rwa [map_mul, map_mul, hg'ρ, rhoC_w] at h2
  ·
    exact hcc x hxN hxz hxw hc

end Main

theorem sec4FusionN0_of_parts
    (h9 : FusR 9 le89 (alternatingGroup (Fin 9)) rBar9 6 cc9)
    (hS9 : FusR 9 le89 ⊤ rBarS9 7 fun _ => False)
    (h11 : FusR 11 le811 (alternatingGroup (Fin 11)) rBar11 7 fun _ => False)
    (hJ : FusJ) (hP : FusP42)
    (h8 : FusR 8 le88 (alternatingGroup (Fin 8)) rBar8 6 cc8)
    (hS8 : FusR 8 le88 ⊤ rBarS8 7 fun _ => False)
    (h10 : FusR 10 le810 (alternatingGroup (Fin 10)) rBar10 7 fun _ => False)
    (hJ8 : FusJ8) (hP8 : FusP42Eight) : Sec4FusionN0 := by
  intro G _ _ L Q n θ z c
  have hsyl := sec4CentSylowCard_holds G L Q n θ z c
  rcases c.shape with hin | ⟨h9n, u, huC, huO, hu2⟩
  · rcases c.n_cases with rfl | rfl | rfl | rfl
    · exact Main.exists_conj_of_isHStar c (Main.isHStar_inner c) h8
        (fun P => (hsyl P).1 ⟨Or.inl rfl, hin⟩)
        (fun x hx hxz hxw => Main.not_cc8 c hin hJ8 hP8 h8 hx hxz hxw)
    · exact Main.exists_conj_of_isHStar c (Main.isHStar_inner c) h9
        (fun P => (hsyl P).1 ⟨Or.inr rfl, hin⟩)
        (fun x hx hxz hxw => Main.not_cc9 c hin hJ hP h9 hx hxz hxw)
    · exact Main.exists_conj_of_isHStar c (Main.isHStar_inner c) h10
        (fun P => (hsyl P).2 fun h => by have := h.1; omega) (fun _ _ _ _ h => h)
    · exact Main.exists_conj_of_isHStar c (Main.isHStar_inner c) h11
        (fun P => (hsyl P).2 fun h => by have := h.1; omega) (fun _ _ _ _ h => h)
  · have hA : ¬ IsASmall L n z := fun h => huO (h.2 huC)
    rcases (show n = 8 ∨ n = 9 by have := c.hn8; omega) with rfl | rfl
    · exact Main.exists_conj_of_isHStar c (Main.isHStar_outer c huC huO hu2) hS8
        (fun P => (hsyl P).2 hA) (fun _ _ _ _ h => h)
    · exact Main.exists_conj_of_isHStar c (Main.isHStar_outer c huC huO hu2) hS9
        (fun P => (hsyl P).2 hA) (fun _ _ _ _ h => h)

end CFSG.OddStandard.AltStdSmall4.Fus
