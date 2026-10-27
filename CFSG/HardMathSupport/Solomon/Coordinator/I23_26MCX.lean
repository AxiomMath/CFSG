module

public import CFSG.HardMathSupport.Solomon.Coordinator.I23_26MCT

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

variable {Y : Type*} [Group Y] [Finite Y] {K E : Subgroup Y}

theorem mc_cent_of_ne {A B : Subgroup Y} (hA : IsComponentOf A ⊤) (hB : IsComponentOf B ⊤)
    (hne : A ≠ B) {a : Y} (ha : a ∈ A) : a ∈ Subgroup.centralizer (B : Set Y) :=
  Subgroup.mem_centralizer_iff.2 fun _ hw => (mc_comm_of_ne hA hB hne ha hw).symm

theorem mc_cross (hK : IsComponentOf K ⊤) (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hE3 : ∀ a ∈ E, a ^ 3 = 1) (hE27 : Nat.card E = 27)
    (hfaith : ∀ e ∈ E, (∀ k ∈ K, e * k = k * e) → e = 1)
    {e₀ j : Y} (he₀ : e₀ ∈ E) (hj : j ∈ E) (hne : GLBConj j K ≠ GLBConj e₀ K) :
    ∃ y z : Y, y ∈ mcT K E ∧ z ∈ mcT K E ∧
      (∀ w ∈ GLBConj e₀ K, w * (y⁻¹ * z) = (y⁻¹ * z) * w) ∧
      ∃ w ∈ GLBConj j K, w * (y⁻¹ * z) ≠ (y⁻¹ * z) * w := by
  have hK₀ : IsComponentOf (GLBConj e₀ K) ⊤ := mc_isComponentOf_gLBConj hK e₀
  have hKj : IsComponentOf (GLBConj j K) ⊤ := mc_isComponentOf_gLBConj hK j
  obtain ⟨x, hxdef⟩ : ∃ x : Y, x = e₀⁻¹ * j := ⟨_, rfl⟩
  have hx : x ∈ E := by rw [hxdef]; exact E.mul_mem (E.inv_mem he₀) hj
  have hxj : GLBConj x (GLBConj e₀ K) = GLBConj j K := by
    rw [mc_conj_conj, hxdef, mul_inv_cancel_left]
  have hxK : GLBConj x K ≠ K := by
    intro hc
    apply hne
    rw [← hxj]
    exact (mc_conj_eq_iff hEc he₀ hx).2 hc
  have hx3 : x ^ 3 = 1 := hE3 x hx
  have hxne : GLBConj x (GLBConj e₀ K) ≠ GLBConj e₀ K := mc_moves hEc he₀ hx hxK
  have hxinv_ne : GLBConj x⁻¹ (GLBConj e₀ K) ≠ GLBConj e₀ K :=
    (mc_gLBConj_inv_ne hx3 hxne).1
  have hcomp_x : IsComponentOf (GLBConj x (GLBConj e₀ K)) ⊤ := mc_isComponentOf_gLBConj hK₀ x
  have hcomp_xi : IsComponentOf (GLBConj x⁻¹ (GLBConj e₀ K)) ⊤ :=
    mc_isComponentOf_gLBConj hK₀ x⁻¹
  by_cases hH : ∃ h ∈ E, h ≠ 1 ∧ GLBConj h K = K
  ·
    obtain ⟨h, hh, hh1, hhK⟩ := hH
    have hbad : ∃ u ∈ GLBConj j K, ∃ v ∈ GLBConj j K,
        ¬ (v * (u⁻¹ * (h⁻¹ * u * h)) = (u⁻¹ * (h⁻¹ * u * h)) * v) := by
      by_contra hcon
      push Not at hcon
      have hcomm := mc_commute_of_perfect (mc_commutator_eq_of_qs hKj.2.2)
        (mc_normalizes hEc hj hh hhK) hcon
      exact hh1 (mc_faith_conj hEc hfaith hj h hh fun k hk => hcomm k hk)
    obtain ⟨u, hu, v, hv, hbad⟩ := hbad
    obtain ⟨k, hkdef⟩ : ∃ k : Y, k = x * u * x⁻¹ := ⟨_, rfl⟩
    have hu' : u ∈ GLBConj x (GLBConj e₀ K) := by rw [hxj]; exact hu
    have hv' : v ∈ GLBConj x (GLBConj e₀ K) := by rw [hxj]; exact hv
    have hk : k ∈ GLBConj e₀ K := by rw [hkdef]; exact mem_gLBConj.1 hu'
    have hk1 : x⁻¹ * k * x = u := by rw [hkdef]; group
    have hk2 : (x * h)⁻¹ * k * (x * h) = h⁻¹ * u * h := by rw [hkdef]; group
    have hxh : x * h ∈ E := E.mul_mem hx hh
    have hxhK : GLBConj (x * h) K ≠ K := by
      intro hc
      have h1 : GLBConj h (GLBConj x K) = GLBConj h K := by
        rw [mc_conj_conj, hc, hhK]
      exact hxK (mc_conj_inj h h1)
    have hhK₀ : GLBConj h (GLBConj e₀ K) = GLBConj e₀ K := (mc_conj_eq_iff hEc he₀ hh).2 hhK
    have eq1 : GLBConj (x * h) (GLBConj e₀ K) = GLBConj x (GLBConj e₀ K) := by
      rw [← mc_conj_conj h x, mc_conj_comm hEc hh hx, hhK₀]
    have eq2 : GLBConj (x * h)⁻¹ (GLBConj e₀ K) = GLBConj x⁻¹ (GLBConj e₀ K) := by
      rw [mul_inv_rev, ← mc_conj_conj x⁻¹ h⁻¹, mc_conj_inv_self hhK₀]
    have ha₁ : x⁻¹ * k * x ∈ GLBConj x (GLBConj e₀ K) := mc_mem_conj hk
    have ha₂ : x * k * x⁻¹ ∈ GLBConj x⁻¹ (GLBConj e₀ K) := mc_mem_conj_inv hk
    have hb₁ : (x * h)⁻¹ * k * (x * h) ∈ GLBConj x (GLBConj e₀ K) := by
      rw [← eq1]; exact mc_mem_conj hk
    have hb₂ : (x * h) * k * (x * h)⁻¹ ∈ GLBConj x⁻¹ (GLBConj e₀ K) := by
      rw [← eq2]; exact mc_mem_conj_inv hk
    have hyz : (mcD x k)⁻¹ * mcD (x * h) k =
        (x * k * x⁻¹)⁻¹ * (x⁻¹ * k * x)⁻¹ *
          (((x * h)⁻¹ * k * (x * h)) * ((x * h) * k * (x * h)⁻¹)) := by
      unfold mcD; group
    refine ⟨mcD x k, mcD (x * h) k,
      Subgroup.subset_closure ⟨e₀, he₀, x, hx, hx3, hxK, k, hk, rfl⟩,
      Subgroup.subset_closure ⟨e₀, he₀, x * h, hxh, hE3 _ hxh, hxhK, k, hk, rfl⟩, ?_, v, hv, ?_⟩
    · have hmem : (mcD x k)⁻¹ * mcD (x * h) k ∈ Subgroup.centralizer (GLBConj e₀ K : Set Y) := by
        rw [hyz]
        refine mul_mem (mul_mem (inv_mem ?_) (inv_mem ?_)) (mul_mem ?_ ?_)
        · exact mc_cent_of_ne hcomp_xi hK₀ hxinv_ne ha₂
        · exact mc_cent_of_ne hcomp_x hK₀ hxne ha₁
        · exact mc_cent_of_ne hcomp_x hK₀ hxne hb₁
        · exact mc_cent_of_ne hcomp_xi hK₀ hxinv_ne hb₂
      intro w hw
      exact Subgroup.mem_centralizer_iff.1 hmem w hw
    · intro hcomm
      apply hbad
      have c1 : Commute v (x * k * x⁻¹) :=
        (mc_comm_23 hK₀ hx3 hxne ha₂ hv').symm
      have c3 : Commute v ((x * h) * k * (x * h)⁻¹) :=
        (mc_comm_23 hK₀ hx3 hxne hb₂ hv').symm
      have c2 : Commute v ((mcD x k)⁻¹ * mcD (x * h) k) := hcomm
      have hid : (x⁻¹ * k * x)⁻¹ * ((x * h)⁻¹ * k * (x * h)) =
          (x * k * x⁻¹) * ((mcD x k)⁻¹ * mcD (x * h) k) * ((x * h) * k * (x * h)⁻¹)⁻¹ := by
        rw [hyz]; group
      have hcv : v * ((x⁻¹ * k * x)⁻¹ * ((x * h)⁻¹ * k * (x * h))) =
          ((x⁻¹ * k * x)⁻¹ * ((x * h)⁻¹ * k * (x * h))) * v := by
        rw [hid]
        exact ((c1.mul_right c2).mul_right c3.inv_right).eq
      rw [hk1, hk2] at hcv
      exact hcv
  ·
    push Not at hH
    have hg₂ : ∃ g₂ ∈ E, g₂ ≠ 1 ∧ g₂ ≠ x ∧ g₂ ≠ x⁻¹ := by
      by_contra hcon
      push Not at hcon
      have hsub : (E : Set Y) ⊆ {1, x, x⁻¹} := by
        intro g hg
        by_cases h1 : g = 1
        · simp [h1]
        by_cases h2 : g = x
        · simp [h2]
        have := hcon g hg h1 h2
        simp [this]
      have hle : Nat.card E ≤ 3 := by
        have e1 : Nat.card E = (E : Set Y).ncard := Nat.card_coe_set_eq (E : Set Y)
        have e2 := Set.ncard_le_ncard hsub
        have h1 := Set.ncard_insert_le (1 : Y) ({x, x⁻¹} : Set Y)
        have h2 := Set.ncard_insert_le x ({x⁻¹} : Set Y)
        have h3 : ({x⁻¹} : Set Y).ncard = 1 := Set.ncard_singleton _
        omega
      omega
    obtain ⟨g₂, hg₂E, hg₂1, hg₂x, hg₂xi⟩ := hg₂
    have hg₂K : GLBConj g₂ K ≠ K := hH g₂ hg₂E hg₂1
    have hg₂3 : g₂ ^ 3 = 1 := hE3 g₂ hg₂E
    have hg₂K₀ : GLBConj g₂ (GLBConj e₀ K) ≠ GLBConj e₀ K := mc_moves hEc he₀ hg₂E hg₂K
    have hg₂inv_ne : GLBConj g₂⁻¹ (GLBConj e₀ K) ≠ GLBConj e₀ K :=
      (mc_gLBConj_inv_ne hg₂3 hg₂K₀).1
    have hne1 : GLBConj g₂ (GLBConj e₀ K) ≠ GLBConj x (GLBConj e₀ K) := by
      refine mc_ne_of_moves hEc he₀ hg₂E hx ?_
      refine hH _ (E.mul_mem hg₂E (E.inv_mem hx)) ?_
      intro hc
      exact hg₂x (mul_inv_eq_one.1 hc)
    have hne2 : GLBConj g₂⁻¹ (GLBConj e₀ K) ≠ GLBConj x (GLBConj e₀ K) := by
      refine mc_ne_of_moves hEc he₀ (E.inv_mem hg₂E) hx ?_
      refine hH _ (E.mul_mem (E.inv_mem hg₂E) (E.inv_mem hx)) ?_
      intro hc
      exact hg₂xi (inv_eq_iff_eq_inv.1 (mul_inv_eq_one.1 hc))
    obtain ⟨u0, v0, h0⟩ := mc_exists_noncomm hK₀.2.2
    have hk : (u0 : Y) ∈ GLBConj e₀ K := u0.2
    have hw' : x⁻¹ * (v0 : Y) * x ∈ GLBConj x (GLBConj e₀ K) := mc_mem_conj v0.2
    have ha₁ : x⁻¹ * (u0 : Y) * x ∈ GLBConj x (GLBConj e₀ K) := mc_mem_conj hk
    have ha₂ : x * (u0 : Y) * x⁻¹ ∈ GLBConj x⁻¹ (GLBConj e₀ K) := mc_mem_conj_inv hk
    have hb₁ : g₂⁻¹ * (u0 : Y) * g₂ ∈ GLBConj g₂ (GLBConj e₀ K) := mc_mem_conj hk
    have hb₂ : g₂ * (u0 : Y) * g₂⁻¹ ∈ GLBConj g₂⁻¹ (GLBConj e₀ K) := mc_mem_conj_inv hk
    have hyz : (mcD x (u0 : Y))⁻¹ * mcD g₂ (u0 : Y) =
        (x * (u0 : Y) * x⁻¹)⁻¹ * (x⁻¹ * (u0 : Y) * x)⁻¹ *
          ((g₂⁻¹ * (u0 : Y) * g₂) * (g₂ * (u0 : Y) * g₂⁻¹)) := by
      unfold mcD; group
    refine ⟨mcD x (u0 : Y), mcD g₂ (u0 : Y),
      Subgroup.subset_closure ⟨e₀, he₀, x, hx, hx3, hxK, u0, hk, rfl⟩,
      Subgroup.subset_closure ⟨e₀, he₀, g₂, hg₂E, hg₂3, hg₂K, u0, hk, rfl⟩, ?_,
      x⁻¹ * (v0 : Y) * x, by rw [← hxj]; exact hw', ?_⟩
    · have hmem : (mcD x (u0 : Y))⁻¹ * mcD g₂ (u0 : Y) ∈
          Subgroup.centralizer (GLBConj e₀ K : Set Y) := by
        rw [hyz]
        refine mul_mem (mul_mem (inv_mem ?_) (inv_mem ?_)) (mul_mem ?_ ?_)
        · exact mc_cent_of_ne hcomp_xi hK₀ hxinv_ne ha₂
        · exact mc_cent_of_ne hcomp_x hK₀ hxne ha₁
        · exact mc_cent_of_ne (mc_isComponentOf_gLBConj hK₀ g₂) hK₀ hg₂K₀ hb₁
        · exact mc_cent_of_ne (mc_isComponentOf_gLBConj hK₀ g₂⁻¹) hK₀ hg₂inv_ne hb₂
      intro w hw
      exact Subgroup.mem_centralizer_iff.1 hmem w hw
    · intro hcomm
      have c1 : Commute (x⁻¹ * (v0 : Y) * x) (x * (u0 : Y) * x⁻¹) :=
        (mc_comm_23 hK₀ hx3 hxne ha₂ hw').symm
      have c2 : Commute (x⁻¹ * (v0 : Y) * x) ((mcD x (u0 : Y))⁻¹ * mcD g₂ (u0 : Y)) := hcomm
      have c3 : Commute (x⁻¹ * (v0 : Y) * x) (g₂⁻¹ * (u0 : Y) * g₂) :=
        (mc_comm_of_ne (mc_isComponentOf_gLBConj hK₀ g₂) hcomp_x hne1 hb₁ hw').symm
      have c4 : Commute (x⁻¹ * (v0 : Y) * x) (g₂ * (u0 : Y) * g₂⁻¹) :=
        (mc_comm_of_ne (mc_isComponentOf_gLBConj hK₀ g₂⁻¹) hcomp_x hne2 hb₂ hw').symm
      have hid : (x⁻¹ * (u0 : Y) * x)⁻¹ =
          (x * (u0 : Y) * x⁻¹) * ((mcD x (u0 : Y))⁻¹ * mcD g₂ (u0 : Y)) *
            ((g₂⁻¹ * (u0 : Y) * g₂) * (g₂ * (u0 : Y) * g₂⁻¹))⁻¹ := by
        rw [hyz]; group
      have hcv : Commute (x⁻¹ * (v0 : Y) * x) (x⁻¹ * (u0 : Y) * x)⁻¹ := by
        rw [hid]
        exact (c1.mul_right c2).mul_right (c3.mul_right c4).inv_right
      have hcv' : (x⁻¹ * (v0 : Y) * x) * (x⁻¹ * (u0 : Y) * x) =
          (x⁻¹ * (u0 : Y) * x) * (x⁻¹ * (v0 : Y) * x) := by
        have := hcv.inv_right
        rw [inv_inv] at this
        exact this.eq
      apply h0
      apply Subtype.ext
      show (u0 : Y) * v0 = v0 * u0
      calc (u0 : Y) * v0 = x * ((x⁻¹ * (u0 : Y) * x) * (x⁻¹ * (v0 : Y) * x)) * x⁻¹ := by group
        _ = x * ((x⁻¹ * (v0 : Y) * x) * (x⁻¹ * (u0 : Y) * x)) * x⁻¹ := by rw [hcv']
        _ = v0 * u0 := by group

end CFSG.HardMathSupport.Solomon.Coordinator
