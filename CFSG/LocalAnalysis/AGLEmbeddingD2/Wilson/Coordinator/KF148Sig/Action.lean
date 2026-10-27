module

public import CFSG.RankThree.GroupTheory.SteinbergCEThetaQuotientAction
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF148Sig

open Subgroup CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory

variable {Γ : Type*} [Group Γ] {L : Subgroup Γ} {X : Type*} [Group X]

@[expose] noncomputable def toX (ψ : L ⧸ aschbacherSolvableCore 3 L ≃* X) : L →* X :=
  ψ.toMonoidHom.comp (QuotientGroup.mk' _)

theorem toX_apply (ψ : L ⧸ aschbacherSolvableCore 3 L ≃* X) (l : L) :
    toX ψ l = ψ (l : L ⧸ aschbacherSolvableCore 3 L) := rfl

theorem toX_eq_one_iff (ψ : L ⧸ aschbacherSolvableCore 3 L ≃* X) (l : L) :
    toX ψ l = 1 ↔ l ∈ aschbacherSolvableCore 3 L := by
  rw [toX_apply, ← map_one ψ, ψ.injective.eq_iff, QuotientGroup.eq_one_iff]

variable {A : Subgroup Γ} (hAL : A ≤ normalizer (L : Set Γ))
  (ψ : L ⧸ aschbacherSolvableCore 3 L ≃* X)

@[expose] noncomputable def actX : A →* MulAut X :=
  (MulAut.congr ψ).toMonoidHom.comp (thetaQuotientAction 3 hAL)

theorem actX_toX (a : A) (l : L) :
    actX hAL ψ a (toX ψ l) = toX ψ ⟨a * l * (a : Γ)⁻¹, (hAL a.2 l).mp l.2⟩ := by
  simp only [actX, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.congr_apply,
    MulEquiv.trans_apply, toX_apply, MulEquiv.symm_apply_apply]
  congr 1

theorem actX_eq_one_iff (a : A) :
    actX hAL ψ a = 1 ↔
      ∀ l ∈ L, (a : Γ) * l * (a : Γ)⁻¹ * l⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) L := by
  rw [← mem_ker_thetaQuotientAction_iff 3 hAL a, MonoidHom.mem_ker, actX, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, ← map_one (MulAut.congr ψ), (MulAut.congr ψ).injective.eq_iff]

variable (hc : center X = ⊥) (hodd : ∀ α : MulAut X, Odd (orderOf α) → ∃ g : X, α = MulAut.conj g)
  (hA3 : ∀ a ∈ A, a ^ 3 = 1)

omit hc in
theorem conj_injective_of_center_eq_bot (hc : center X = ⊥) :
    Function.Injective (MulAut.conj : X →* MulAut X) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have : g ∈ center X := mem_center_iff.mpr fun y => by
    have h := congrArg (fun σ : MulAut X => σ y) hg
    simp only [MulAut.conj_apply, MulAut.one_apply] at h
    calc y * g = (g * y * g⁻¹) * g := by rw [h]
      _ = g * y := by group
  rw [hc] at this
  exact (mem_bot.mp this)

include hodd hA3 in
theorem actX_mem_range (a : A) : actX hAL ψ a ∈ (MulAut.conj : X →* MulAut X).range := by
  have h3 : actX hAL ψ a ^ 3 = 1 := by
    rw [← map_pow, show a ^ 3 = 1 from Subtype.ext (by simpa using hA3 a a.2), map_one]
  obtain ⟨g, hg⟩ := hodd _ (Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one h3))
  exact ⟨g, hg.symm⟩

@[expose] noncomputable def innerHom : A →* X :=
  (MonoidHom.ofInjective (conj_injective_of_center_eq_bot hc)).symm.toMonoidHom.comp
    ((actX hAL ψ).codRestrict _ (actX_mem_range hAL ψ hodd hA3))

theorem conj_innerHom (a : A) :
    MulAut.conj (innerHom hAL ψ hc hodd hA3 a) = actX hAL ψ a := by
  have h := (MonoidHom.ofInjective (conj_injective_of_center_eq_bot hc)).apply_symm_apply
    ((actX hAL ψ).codRestrict _ (actX_mem_range hAL ψ hodd hA3) a)
  have h' := congrArg Subtype.val h
  rwa [MonoidHom.ofInjective_apply] at h'

theorem toX_conj (a : A) (l : L) :
    toX ψ ⟨a * l * (a : Γ)⁻¹, (hAL a.2 l).mp l.2⟩ =
      innerHom hAL ψ hc hodd hA3 a * toX ψ l * (innerHom hAL ψ hc hodd hA3 a)⁻¹ := by
  rw [← actX_toX hAL ψ a l, ← conj_innerHom hAL ψ hc hodd hA3 a, MulAut.conj_apply]

theorem innerHom_eq_one_iff (a : A) :
    innerHom hAL ψ hc hodd hA3 a = 1 ↔
      ∀ l ∈ L, (a : Γ) * l * (a : Γ)⁻¹ * l⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) L := by
  rw [← actX_eq_one_iff hAL ψ, ← conj_innerHom hAL ψ hc hodd hA3 a,
    ← map_one (MulAut.conj : X →* MulAut X), (conj_injective_of_center_eq_bot hc).eq_iff]

end CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF148Sig
