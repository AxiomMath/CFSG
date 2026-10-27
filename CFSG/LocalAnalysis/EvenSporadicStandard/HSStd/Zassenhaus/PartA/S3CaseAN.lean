module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S3CaseAS5

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Equiv Subgroup CFSG.Open

section Odd

theorem s3a_normal_odd {D : Type} [Group D] (hz : fusionZStar D = ⊥) (N : Subgroup D) [N.Normal]
    (hN : Odd (Nat.card N)) : N = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hle : N ≤ fusionOddCore D := le_sSup ⟨inferInstance, hN⟩
  have h1 : x ∈ fusionOddCore D := hle hx
  have h2 : x ∈ fusionZStar D := by
    unfold fusionZStar
    rw [Subgroup.mem_comap]
    have : (QuotientGroup.mk' (fusionOddCore D)) x = 1 := (QuotientGroup.eq_one_iff x).2 h1
    rw [this]
    exact one_mem _
  rw [hz] at h2
  exact h2

end Odd

section Cent

variable {D : Type} [Group D] [Finite D] {t : D} {K : Subgroup D}

theorem s3a_K_mem_cent (h : DShape D t K) {k : D} (hk : k ∈ K) :
    k ∈ centralizer ({t} : Set D) := by
  rw [h.cent]
  exact Subgroup.mem_sup_right hk

theorem s3a_comm_aux {k x : D} (ht : t * t = 1) (hk : t * k = k * t) (hx : t * x = x * t) :
    (t * k) * x * (t * k)⁻¹ * x⁻¹ = k * x * k⁻¹ * x⁻¹ := by
  have hkc : Commute t k := hk
  have hxc : Commute t x := hx
  have hu : t * (k * x * k⁻¹) = (k * x * k⁻¹) * t :=
    ((hkc.mul_right hxc).mul_right hkc.inv_right).eq
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have h1 : t * (k * x * k⁻¹) * t⁻¹ = k * x * k⁻¹ := by
    rw [hu, ht', mul_assoc, ht, mul_one]
  calc (t * k) * x * (t * k)⁻¹ * x⁻¹ = (t * (k * x * k⁻¹) * t⁻¹) * x⁻¹ := by group
    _ = _ := by rw [h1]

theorem s3a_normal_dichotomy (h : DShape D t K) (ψ : ↥K ≃* Perm (Fin 5)) (M : Subgroup D)
    (hMC : M ≤ centralizer ({t} : Set D))
    (hM : ∀ c ∈ centralizer ({t} : Set D), ∀ m ∈ M, c * m * c⁻¹ ∈ M) :
    (∀ m ∈ M, m = 1 ∨ m = t) ∨ ∀ a, s3a_iota ψ a ∈ M := by
  by_cases hall : ∀ m ∈ M, m = 1 ∨ m = t
  · exact Or.inl hall
  right
  push Not at hall
  obtain ⟨m, hmM, hm1, hmt⟩ := hall
  obtain ⟨k, hk, hmk⟩ := s3a_cent_decomp h (hMC hmM)
  have hk1 : (⟨k, hk⟩ : ↥K) ≠ 1 := by
    intro e
    have : k = 1 := congrArg Subtype.val e
    rcases hmk with rfl | rfl
    · exact hm1 this
    · exact hmt (by rw [this, mul_one])
  have hψk : ψ ⟨k, hk⟩ ≠ 1 := fun e => hk1 (ψ.injective (by rw [e, map_one]))
  obtain ⟨y, hy⟩ := s3a_perm5_center _ hψk
  set x : ↥K := ψ.symm y with hx
  have hxC : (x : D) ∈ centralizer ({t} : Set D) := s3a_K_mem_cent h x.2
  have hmem : m * x * m⁻¹ * x⁻¹ ∈ M := by
    have := M.mul_mem hmM (hM _ hxC _ (M.inv_mem hmM))
    simpa [mul_assoc] using this
  have hcomm_eq : m * x * m⁻¹ * x⁻¹ = k * x * k⁻¹ * x⁻¹ := by
    rcases hmk with rfl | rfl
    · rfl
    · exact s3a_comm_aux h.t_sq (s3a_K_comm h hk) (s3a_K_comm h x.2)
  set n : ↥K := ⟨k, hk⟩ * x * ⟨k, hk⟩⁻¹ * x⁻¹ with hn
  have hnval : (n : D) = k * x * k⁻¹ * x⁻¹ := by simp [hn]
  let MK : Subgroup (Perm (Fin 5)) := (M.comap K.subtype).map ψ.toMonoidHom
  have hMKn : ψ n ∈ MK := ⟨n, by
    show (n : D) ∈ M
    rw [hnval, ← hcomm_eq]; exact hmem, rfl⟩
  have hMKne : MK ≠ ⊥ := by
    intro e
    have h1 : ψ n = 1 := by
      have := hMKn
      rw [e] at this
      exact Subgroup.mem_bot.1 this
    apply hy
    have : ψ ⟨k, hk⟩ * y * (ψ ⟨k, hk⟩)⁻¹ * y⁻¹ = 1 := by
      have e2 : ψ n = ψ ⟨k, hk⟩ * y * (ψ ⟨k, hk⟩)⁻¹ * y⁻¹ := by
        simp [hn, hx]
      rw [← e2]; exact h1
    calc ψ ⟨k, hk⟩ * y = (ψ ⟨k, hk⟩ * y * (ψ ⟨k, hk⟩)⁻¹ * y⁻¹) * (y * ψ ⟨k, hk⟩) := by group
      _ = y * ψ ⟨k, hk⟩ := by rw [this, one_mul]
  have hMKnormal : MK.Normal := by
    refine ⟨?_⟩
    intro z hz g
    obtain ⟨w, hw, rfl⟩ := hz
    refine ⟨ψ.symm g * w * (ψ.symm g)⁻¹, ?_, by simp⟩
    show ((ψ.symm g * w * (ψ.symm g)⁻¹ : ↥K) : D) ∈ M
    have := hM _ (s3a_K_mem_cent h (ψ.symm g).2) _ hw
    simpa using this
  have hA := s3a_perm5_normal MK hMKne
  intro a
  obtain ⟨w, hw, hwa⟩ := hA a.2
  have : w = ψ.symm (a : Perm (Fin 5)) := by
    apply ψ.injective
    simpa using hwa
  rw [s3a_iota_apply, ← this]
  exact hw

end Cent

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
