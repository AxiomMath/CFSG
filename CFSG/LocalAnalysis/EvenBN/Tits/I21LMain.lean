module

public import CFSG.LocalAnalysis.EvenBN.Tits.I21LDich
public import CFSG.LocalAnalysis.EvenBN.Tits.I21LCaseE
public import CFSG.LocalAnalysis.EvenBN.Tits.I21LCaseA
public import CFSG.GF2Type.Smith1980Orth.W4SigmaGL

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.I21L

open Module Subgroup CFSG.LocalAnalysis.EvenBN.Tits CFSG.Open

section Main

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {Y : Type} [Group Y] [Finite Y]
  {ρ : Y →* (V ≃ₗ[ZMod 2] V)} {t u x h : Y}



theorem thm107_card_dvd_sec622N (H : HypYW ρ t u x h) : Nat.card Y ∣ sec622N := by
  haveI : Module.Finite (ZMod 2) V := Module.finite_of_finrank_pos (by rw [H.dim]; norm_num)
  have h1 : Nat.card Y ∣ Nat.card (V ≃ₗ[ZMod 2] V) := Subgroup.card_dvd_of_injective ρ H.inj
  rw [CFSG.GF2Type.Smith1980Orth.W4Sigma.card_linearEquiv_eq_prod H.dim] at h1
  have h2 : ∏ i : Fin 8, (2 ^ 8 - 2 ^ (i : ℕ)) = sec622N := by
    simp [Fin.prod_univ_succ, sec622N]
  rwa [h2] at h1

theorem thm107_two_elements_pow_eight (H : HypYW ρ t u x h) :
    ∀ g : Y, (∃ k : ℕ, orderOf g = 2 ^ k) → g ^ 8 = 1 := by
  rintro g ⟨k, hk⟩
  haveI : Module.Finite (ZMod 2) V := Module.finite_of_finrank_pos (by rw [H.dim]; norm_num)
  have hg : (ρ g) ^ (2 ^ k) = 1 := by
    rw [← map_pow, ← hk, pow_orderOf_eq_one, map_one]
  have := pow_eq_one_of_two_pow (ρ g) hg (m := 3) (by rw [H.dim]; norm_num)
  apply H.inj
  rw [map_pow, map_one]
  simpa using this

theorem thm107_closure_pair_inv (t u : Y) : closure ({t, u⁻¹} : Set Y) = closure {t, u} := by
  refine le_antisymm ((Subgroup.closure_le _).2 ?_) ((Subgroup.closure_le _).2 ?_)
  · rintro g (rfl | rfl)
    · exact subset_closure (by simp)
    · exact inv_mem (subset_closure (by simp))
  · rintro g (rfl | rfl)
    · exact subset_closure (by simp)
    · have : g = (g⁻¹)⁻¹ := (inv_inv g).symm
      rw [this]
      exact inv_mem (subset_closure (by simp))

theorem thm107_closure_triple_inv (t u x : Y) :
    closure ({t, u⁻¹, x} : Set Y) = closure {t, u, x} := by
  refine le_antisymm ((Subgroup.closure_le _).2 ?_) ((Subgroup.closure_le _).2 ?_)
  · rintro g (rfl | rfl | rfl)
    · exact subset_closure (by simp)
    · exact inv_mem (subset_closure (by simp))
    · exact subset_closure (by simp)
  · rintro g (rfl | rfl | rfl)
    · exact subset_closure (by simp)
    · have : g = (g⁻¹)⁻¹ := (inv_inv g).symm
      rw [this]
      exact inv_mem (subset_closure (by simp))
    · exact subset_closure (by simp)

theorem thm107_exists_u_sq (H : HypYW ρ t u x h) :
    ∃ u' : Y, u' * x * u'⁻¹ = x ^ 2 ∧ u' ^ 2 = u ^ 2 ∧ SecTwoHyp Y t u' ∧
      closure ({t, u', x} : Set Y) = closure {t, u, x} := by
  have hu4 : u ^ 4 = 1 := by rw [← H.sec.orderOf_u]; exact pow_orderOf_eq_one u
  have hx5 : x ^ 5 = 1 := by rw [← H.ord_x]; exact pow_orderOf_eq_one x
  rcases H.ux with h2 | h3
  · exact ⟨u, h2, rfl, H.sec, rfl⟩
  · refine ⟨u⁻¹, ?_, ?_, ?_, thm107_closure_triple_inv t u x⟩
    · have hy3 : (u⁻¹ * x * u) ^ 3 = x := by
        have e : (u⁻¹ * x * u) ^ 3 = u⁻¹ * x ^ 3 * u := by
          have := conj_pow (a := u⁻¹) (b := x) (i := 3)
          simpa using this
        rw [e, ← h3]
        group
      have hy5 : (u⁻¹ * x * u) ^ 5 = 1 := by
        have := conj_pow (a := u⁻¹) (b := x) (i := 5)
        rw [inv_inv] at this
        rw [this, hx5]
        group
      calc u⁻¹ * x * u⁻¹⁻¹ = u⁻¹ * x * u := by rw [inv_inv]
        _ = (u⁻¹ * x * u) ^ 6 := by rw [pow_succ, hy5, one_mul]
        _ = ((u⁻¹ * x * u) ^ 3) ^ 2 := by rw [← pow_mul]
        _ = x ^ 2 := by rw [hy3]
    · have h22 : u ^ 2 * u ^ 2 = 1 := by rw [← pow_add]; exact hu4
      calc u⁻¹ ^ 2 = (u ^ 2)⁻¹ := by rw [inv_pow]
        _ = u ^ 2 := inv_eq_of_mul_eq_one_right h22
    · have hq : (u ^ 2)⁻¹ = u ^ 2 := by
        have h22 : u ^ 2 * u ^ 2 = 1 := by rw [← pow_add]; exact hu4
        exact inv_eq_of_mul_eq_one_right h22
      refine ⟨H.sec.orderOf_t, (orderOf_inv u).trans H.sec.orderOf_u,
        (show Commute t u from H.sec.commute).inv_right.eq, ?_, ?_⟩
      · rw [inv_pow, hq]
        exact H.sec.sq_ne
      · have := H.sec.sylow
        unfold secTwoR at this ⊢
        rwa [thm107_closure_pair_inv]

theorem thm_10_7 (H : HypYW ρ t u x h) :
    ((Nonempty (normalClosure ({x} : Set Y) ≃* alternatingGroup (Fin 6)) ∧
        PGLTwoSquareOuter (normalClosure ({x} : Set Y)) t) ∨
      Nonempty (normalClosure ({x} : Set Y) ≃* Multiplicative (ZMod 5) × Multiplicative (ZMod 5))) ∧
      Thm107P ρ t := by
  obtain ⟨u', hux', hu'sq, hsec', hcl'⟩ := thm107_exists_u_sq H
  have hC' : centralizer ({t} : Set Y) = closure {t, u', x} := by rw [hcl']; exact H.cent
  have hh' : h * t * h⁻¹ = t * u' ^ 2 := by rw [hu'sq]; exact H.fuse
  rcases dichotomy hsec' H.ord_x H.tx hux' hC' hh' (thm107_card_dvd_sec622N H)
      (thm107_two_elements_pow_eight H) with hxO | ⟨hxO, hL⟩
  · obtain ⟨hZ, hP⟩ := case_E25 H hxO
    exact ⟨Or.inr hZ, hP⟩
  · rw [hu'sq] at hL
    obtain ⟨hA, hP⟩ := case_A6 H hxO hL
    exact ⟨Or.inl hA, hP⟩

end Main

end CFSG.LocalAnalysis.EvenBN.Tits.I21L
