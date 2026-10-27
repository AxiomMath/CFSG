module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecTenSwapData

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup Equiv Equiv.Perm CFSG.OddStandard.AltStdSec.SwapPattern

variable {G : Type} [Group G]

theorem exists_coord_homs {x : G} {ι₁ : Perm (Fin 10) →* G} (hC : CentData x ι₁) :
    ∃ (π : ↥(centralizer ({x} : Set G)) →* Perm (Fin 10))
      (κ : ↥(centralizer ({x} : Set G)) →* ℤˣ),
      SymSec x π ∧ κ (selfC x) = -1 ∧
      (∀ (σ : Perm (Fin 10)) (c : ↥(centralizer ({x} : Set G))),
        (c : G) = ι₁ σ → π c = σ ∧ κ c = 1) ∧
      (∀ (σ : Perm (Fin 10)) (c : ↥(centralizer ({x} : Set G))),
        (c : G) = x * ι₁ σ → π c = σ ∧ κ c = -1) := by
  classical
  let a : ℤˣ →* G := MonoidHom.mk' (fun u => if u = 1 then (1 : G) else x) (by
    intro u v
    rcases Int.units_eq_one_or u with rfl | rfl <;>
      rcases Int.units_eq_one_or v with rfl | rfl
    · rw [one_mul, if_pos rfl, one_mul]
    · rw [one_mul, if_neg (by decide), if_pos rfl, one_mul]
    · rw [mul_one, if_neg (by decide), if_pos rfl, mul_one]
    · rw [show ((-1 : ℤˣ) * (-1)) = 1 from by decide, if_pos rfl,
        if_neg (by decide), hC.mul_self])
  have ha_one : a (1 : ℤˣ) = 1 := rfl
  have ha_neg : a (-1 : ℤˣ) = x := by
    show (if (-1 : ℤˣ) = 1 then (1 : G) else x) = x
    rw [if_neg (by decide)]
  have hax : ∀ u : ℤˣ, a u * x = x * a u := by
    intro u
    rcases Int.units_eq_one_or u with rfl | rfl
    · rw [ha_one, one_mul, mul_one]
    · rw [ha_neg]
  have ha_comm : ∀ (u : ℤˣ) (σ : Perm (Fin 10)), a u * ι₁ σ = ι₁ σ * a u := by
    intro u σ
    rcases Int.units_eq_one_or u with rfl | rfl
    · rw [ha_one, one_mul, mul_one]
    · rw [ha_neg]
      exact hC.comm σ
  let Φ : ℤˣ × Perm (Fin 10) →* G :=
    MonoidHom.mk' (fun p => a p.1 * ι₁ p.2) (by
      intro p q
      show a (p.1 * q.1) * ι₁ (p.2 * q.2) =
        (a p.1 * ι₁ p.2) * (a q.1 * ι₁ q.2)
      calc a (p.1 * q.1) * ι₁ (p.2 * q.2)
          = a p.1 * a q.1 * (ι₁ p.2 * ι₁ q.2) := by rw [map_mul, map_mul]
        _ = a p.1 * (a q.1 * ι₁ p.2) * ι₁ q.2 := by group
        _ = a p.1 * (ι₁ p.2 * a q.1) * ι₁ q.2 := by rw [ha_comm q.1 p.2]
        _ = (a p.1 * ι₁ p.2) * (a q.1 * ι₁ q.2) := by group)
  have hΦ_apply : ∀ p : ℤˣ × Perm (Fin 10), Φ p = a p.1 * ι₁ p.2 := fun _ => rfl
  have hΦ_mem : ∀ p : ℤˣ × Perm (Fin 10), Φ p ∈ centralizer ({x} : Set G) := by
    intro p
    rw [mem_centralizer_singleton_iff, hΦ_apply p]
    calc (a p.1 * ι₁ p.2) * x = a p.1 * (ι₁ p.2 * x) := by group
      _ = a p.1 * (x * ι₁ p.2) := by rw [← hC.comm p.2]
      _ = (a p.1 * x) * ι₁ p.2 := by group
      _ = (x * a p.1) * ι₁ p.2 := by rw [hax p.1]
      _ = x * (a p.1 * ι₁ p.2) := by group
  have hΦ_inj : Function.Injective Φ := by
    rintro ⟨u, σ⟩ ⟨v, τ⟩ h
    have h' : a u * ι₁ σ = a v * ι₁ τ := h
    rcases Int.units_eq_one_or u with rfl | rfl <;>
      rcases Int.units_eq_one_or v with rfl | rfl
    · exact Prod.ext rfl (hC.inj (by simpa [ha_one] using h'))
    · exfalso
      have h2 : ι₁ σ = x * ι₁ τ := by simpa [ha_one, ha_neg] using h'
      have hx : ι₁ (σ * τ⁻¹) = x := by
        rw [map_mul, map_inv, h2]
        group
      exact hC.ne_z _ hx
    · exfalso
      have h2' : x * ι₁ σ = ι₁ τ := by simpa [ha_one, ha_neg] using h'
      have h2 : ι₁ τ = x * ι₁ σ := h2'.symm
      have hx : ι₁ (τ * σ⁻¹) = x := by
        rw [map_mul, map_inv, h2]
        group
      exact hC.ne_z _ hx
    · have h2 : x * ι₁ σ = x * ι₁ τ := by simpa [ha_neg] using h'
      exact Prod.ext rfl (hC.inj (mul_left_cancel h2))
  let Φ' : ℤˣ × Perm (Fin 10) →* ↥(centralizer ({x} : Set G)) :=
    Φ.codRestrict (centralizer ({x} : Set G)) hΦ_mem
  have hΦ'_apply : ∀ p : ℤˣ × Perm (Fin 10), (Φ' p : G) = a p.1 * ι₁ p.2 :=
    fun p => hΦ_apply p
  have hΦ'_inj : Function.Injective Φ' := by
    intro p q h
    exact hΦ_inj (congrArg Subtype.val h)
  have hΦ'_surj : Function.Surjective Φ' := by
    intro g
    obtain ⟨σ, hg | hg⟩ := hC.cases (g : G) g.2
    · exact ⟨(1, σ), Subtype.ext (by rw [hΦ'_apply, ha_one, one_mul]; exact hg.symm)⟩
    · exact ⟨(-1, σ), Subtype.ext (by rw [hΦ'_apply, ha_neg]; exact hg.symm)⟩
  let e : ℤˣ × Perm (Fin 10) ≃* ↥(centralizer ({x} : Set G)) :=
    MulEquiv.ofBijective Φ' ⟨hΦ'_inj, hΦ'_surj⟩
  have he_apply : ∀ p : ℤˣ × Perm (Fin 10), (e p : G) = a p.1 * ι₁ p.2 :=
    fun p => hΦ'_apply p
  let π : ↥(centralizer ({x} : Set G)) →* Perm (Fin 10) :=
    (MonoidHom.snd ℤˣ (Perm (Fin 10))).comp e.symm.toMonoidHom
  let κ : ↥(centralizer ({x} : Set G)) →* ℤˣ :=
    (MonoidHom.fst ℤˣ (Perm (Fin 10))).comp e.symm.toMonoidHom
  have hπe : ∀ p : ℤˣ × Perm (Fin 10), π (e p) = p.2 := by
    intro p
    simp [π, MulEquiv.symm_apply_apply]
  have hκe : ∀ p : ℤˣ × Perm (Fin 10), κ (e p) = p.1 := by
    intro p
    simp [κ, MulEquiv.symm_apply_apply]
  have hSym : SymSec x π := by
    refine ⟨?_, ?_⟩
    · intro σ
      exact ⟨e (1, σ), by rw [hπe]⟩
    · intro c
      obtain ⟨p, rfl⟩ := e.surjective c
      rw [hπe p]
      constructor
      · intro hσ
        rw [he_apply p, hσ, map_one, mul_one]
        rcases Int.units_eq_one_or p.1 with hu | hu
        · exact Or.inl (by simp [hu, ha_one])
        · exact Or.inr (by simp [hu, ha_neg])
      · rintro (h | h)
        · rw [he_apply p] at h
          rcases Int.units_eq_one_or p.1 with hu | hu
          · rw [hu, ha_one, one_mul] at h
            exact hC.inj (by simp [h])
          · rw [hu, ha_neg] at h
            exact absurd (mul_left_cancel
              (show x * ι₁ p.2 = x * x by simp [h, hC.mul_self])) (hC.ne_z p.2)
        · rw [he_apply p] at h
          rcases Int.units_eq_one_or p.1 with hu | hu
          · rw [hu, ha_one, one_mul] at h
            exact absurd h (hC.ne_z p.2)
          · rw [hu, ha_neg] at h
            have hι : ι₁ p.2 = 1 :=
              mul_left_cancel (show x * ι₁ p.2 = x * 1 by simp [h])
            exact hC.inj (by simp [hι])
  have hself : e (-1, 1) = selfC x := by
    apply Subtype.ext
    simp [selfC, he_apply, ha_neg]
  refine ⟨π, κ, hSym, ?_, ?_, ?_⟩
  · rw [← hself]
    exact hκe (-1, 1)
  · intro σ c hc
    have hce : c = e (1, σ) := by
      apply Subtype.ext
      rw [he_apply, ha_one, one_mul]
      exact hc
    exact ⟨by rw [hce]; exact hπe (1, σ), by rw [hce]; exact hκe (1, σ)⟩
  · intro σ c hc
    have hce : c = e (-1, σ) := by
      apply Subtype.ext
      rw [he_apply, ha_neg]
      exact hc
    exact ⟨by rw [hce]; exact hπe (-1, σ), by rw [hce]; exact hκe (-1, σ)⟩

end CFSG.OddStandard.AltStdSec.SwapPartner
