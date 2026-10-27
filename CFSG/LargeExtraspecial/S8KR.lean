module

public import CFSG.LargeExtraspecial.S8KQ

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S8

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}

variable {H : Hyp4 S g} {C : Cons311 S g} {t : S.O} {ht : t ∈ S.Lbar g} {ht1 : t ≠ 1}
  {hVQ : ¬ V S g t ≤ S.Qa g}

namespace Bad4

variable {D : Std H C ht ht1 hVQ} {τ : S.O} (B : Bad4 D τ)
include B

theorem commSpace_t_mul_eq {σ : S.O} (hσ : σ ∈ conjCentM S t) (hσN : σ ∉ Nbar S g t) :
    commSpace ((t * σ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) =
      Vt S g t ⊔ commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
  have hσV := B.red.fix_Vt hσ
  have h1 := commSpace_mul_eq_sup (x := t) (y := σ)
    (by rw [(commSpace_t_eq H C ht ht1 hVQ).1]; exact B.red.inf_eq_bot hσ hσN) (fun v hv => by
      have hvW := commSpace_le_Wt_of_fix hσV hv
      rw [← (commSpace_t_eq H C ht ht1 hVQ).2] at hvW
      exact mem_fixSpace.mp hvW)
  rw [h1, (commSpace_t_eq H C ht ht1 hVQ).1, B.sup_eq hσ hσN]

theorem classify_N1bar {a : S.O} (ha : a ∈ N1bar S g t τ) (ha1 : a ≠ 1) :
    (a ∈ conjD S t ∧ commSpace (a : S.Qt ≃ₗ[ZMod 2] S.Qt) ≤
        Vt S g t ⊔ commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt)) ∨
      commSpace (a : S.Qt ≃ₗ[ZMod 2] S.Qt) = Vt S g t ⊔ commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
  have hY := B.commSpace_le_of_mem_N1bar ha
  have hab := (B.red.N1bar_spec B.mem B.not_mem).2.1
  have hFA : S9.Fbar S g t ≤ N1bar S g t τ := B.Fbar_le
  have hFhA : (S9.Fbar S g t).map (MulAut.conj (S.ρ D.h)).toMonoidHom ≤ N1bar S g t τ := by
    rintro _ ⟨f, hf, rfl⟩
    exact B.conj_mem D.hh (hFA hf)
  obtain ⟨f₁, hf₁, f₂, hf₂, rfl⟩ := exists_mul_of_mem_sup_of_commute
    (fun p hp k hk => (hab p (hFA hp) k (hFhA hk)).1) (B.N1bar_le_Fbar_sup ha)
  obtain ⟨f, hfF, rfl⟩ := hf₂
  have hf₁A := hFA hf₁
  have hf₂A := hFhA ⟨f, hfF, rfl⟩
  have hD₂ : (MulAut.conj (S.ρ D.h)).toMonoidHom f ≠ 1 →
      (MulAut.conj (S.ρ D.h)).toMonoidHom f ∈ conjD S t := fun h1 => by
    have hf1 : f ≠ 1 := fun h => h1 (by rw [h, map_one])
    obtain ⟨x, hxM, hxf⟩ := B.mem_conjD_of_mem_Fbar hfF hf1
    refine ⟨S.ρ D.h * x, mul_mem (Rbar_le_Mbar D.hh) hxM, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hxf]
    group
  by_cases h₁ : f₁ = 1
  · left
    rw [h₁, one_mul] at ha1 ⊢
    exact ⟨hD₂ ha1, by rw [h₁, one_mul] at hY; exact hY⟩
  by_cases h₂ : (MulAut.conj (S.ρ D.h)).toMonoidHom f = 1
  · left
    rw [h₂, mul_one] at ha1 ⊢
    exact ⟨B.mem_conjD_of_mem_Fbar hf₁ h₁, by rw [h₂, mul_one] at hY; exact hY⟩
  have hne : f₁ ≠ (MulAut.conj (S.ρ D.h)).toMonoidHom f := by
    intro h
    apply ha1
    rw [← h]
    exact (hab f₁ hf₁A f₁ hf₁A).2
  rcases B.mul_mem_conjD_or (B.mem_conjD_of_mem_Fbar hf₁ h₁) (hD₂ h₂)
      (B.commSpace_le_of_mem_N1bar hf₁A) (B.commSpace_le_of_mem_N1bar hf₂A) hne with h | h
  · exact Or.inl ⟨h, hY⟩
  · exact Or.inr h

theorem exists_comm_of_mem_N1bar {a : S.O} (ha : a ∈ N1bar S g t τ) :
    ∃ n ∈ Nbar S g t, (n * τ * n⁻¹ * τ⁻¹)⁻¹ * a ∈ zpowers t := by
  have := B.red.nqHyp
  have hτK := mem_CMt_of_mem_conjCentM B.mem
  have hle := (B.red.N1bar_spec B.mem B.not_mem).1
  have hcN : ∀ n ∈ Nbar S g t, n * τ * n⁻¹ * τ⁻¹ ∈ Nbar S g t := fun n hn =>
    hle (comm_mem_N1bar hn)
  have h1 : nqMk ⟨a, hle ha⟩ ∈ LinearMap.range (nqComm S g t ⟨τ, hτK⟩) := by
    rw [← nqSub_N1bar H hτK hle]
    exact ⟨⟨a, hle ha⟩, ha, rfl⟩
  refine (LinearMap.mem_range.mp h1).elim fun m hm =>
    (nqMk_surjective (S := S) (g := g) (t := t) m).elim fun n hn => ?_
  subst hn
  have h2 : nqMk ⟨(n : S.O) * τ * (n : S.O)⁻¹ * τ⁻¹, hcN _ n.2⟩ = nqMk ⟨a, hle ha⟩ :=
    (nqComm_mk (⟨τ, hτK⟩ : CMt S t) n (hcN _ n.2)).symm.trans hm
  have h3 := (nqMk_eq_iff _ _).mp h2
  exact ⟨n, n.2, h3⟩

theorem classify_mul {e : S.O} (he : e * τ ∈ N1bar S g t τ) :
    (e ∈ conjD S t ∧ commSpace (e : S.Qt ≃ₗ[ZMod 2] S.Qt) ≤
        Vt S g t ⊔ commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt)) ∨
      commSpace (e : S.Qt ≃ₗ[ZMod 2] S.Qt) = Vt S g t ⊔ commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
  have haQ := H.conj_mem
  have htt : t * t = 1 := mul_self_of_mem_Lbar S haQ ht
  have hττ : τ * τ = 1 := mul_self_of_mem_conjCentM H ht B.mem
  have hτi : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right hττ
  obtain ⟨n, hn, hc⟩ := B.exists_comm_of_mem_N1bar he
  obtain ⟨hbad, hbadN⟩ := conj_bad haQ B.mem B.not_mem hn
  have hnτM : n * τ * n⁻¹ ∈ S.Mbar := hbad.1
  rcases eq_one_or_eq_of_mem_zpowers htt hc with h | h
  ·
    have e1 : e = n * τ * n⁻¹ := by
      calc e = (e * τ) * τ⁻¹ := by group
        _ = (n * τ * n⁻¹ * τ⁻¹) * ((n * τ * n⁻¹ * τ⁻¹)⁻¹ * (e * τ)) * τ⁻¹ := by group
        _ = n * τ * n⁻¹ * (τ * τ)⁻¹ := by rw [h]; group
        _ = n * τ * n⁻¹ := by rw [hττ, inv_one, mul_one]
    left
    rw [e1]
    refine ⟨?_, ?_⟩
    · obtain ⟨-, -, x, hxM, hxτ⟩ := B.mem
      exact ⟨n * x, mul_mem (Rbar_le_Mbar (Nbar_le_Rbar hn)) hxM, by rw [hxτ]; group⟩
    · rw [← B.sup_eq hbad hbadN]
      exact le_sup_right
  ·
    right
    have hcomm : (n * τ * n⁻¹ * τ⁻¹) * t = t * (n * τ * n⁻¹ * τ⁻¹) :=
      commute_of_mem_Rbar haQ (Nbar_le_Rbar
        ((B.red.N1bar_spec B.mem B.not_mem).1 (comm_mem_N1bar hn)))
    have e1 : e = t * (n * τ * n⁻¹) := by
      calc e = (e * τ) * τ⁻¹ := by group
        _ = (n * τ * n⁻¹ * τ⁻¹) * ((n * τ * n⁻¹ * τ⁻¹)⁻¹ * (e * τ)) * τ⁻¹ := by group
        _ = (n * τ * n⁻¹ * τ⁻¹) * t * τ⁻¹ := by rw [h]
        _ = t * (n * τ * n⁻¹ * τ⁻¹) * τ⁻¹ := by rw [hcomm]
        _ = t * (n * τ * n⁻¹) * (τ * τ)⁻¹ := by group
        _ = t * (n * τ * n⁻¹) := by rw [hττ, inv_one, mul_one]
    rw [e1]
    exact B.commSpace_t_mul_eq hbad hbadN

theorem classify {e : S.O} (he : e ∈ closure (insert τ (N1bar S g t τ : Set S.O)))
    (he1 : e ≠ 1) :
    (e ∈ conjD S t ∧ commSpace (e : S.Qt ≃ₗ[ZMod 2] S.Qt) ≤
        Vt S g t ⊔ commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt)) ∨
      commSpace (e : S.Qt ≃ₗ[ZMod 2] S.Qt) = Vt S g t ⊔ commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) :=
  (B.mem_or_mul_mem he).elim (fun h => B.classify_N1bar h he1) (fun h => B.classify_mul h)

end Bad4

end CFSG.LargeExtraspecial.S8
