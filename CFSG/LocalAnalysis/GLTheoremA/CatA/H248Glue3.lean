module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.H248Glue2

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H248

open CFSG.Open
open scoped commutatorElement

theorem isQuasisimple_of_central_quotient {E F : Type} [Group E] [Group F] (N : Subgroup E) [N.Normal]
    (hN : N ≤ Subgroup.center E) (hperf : commutator E = ⊤) (e : (E ⧸ N) ≃* F)
    (hF : CFSG.Open.IsQuasisimple F) :
    CFSG.Open.IsQuasisimple E ∧ Nonempty ((E ⧸ Subgroup.center E) ≃* (F ⧸ Subgroup.center F)) := by
  let φ : E →* F := e.toMonoidHom.comp (QuotientGroup.mk' N)
  have hφ : Function.Surjective φ := by
    intro y
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective N (e.symm y)
    exact ⟨x, by rw [show φ x = e ((QuotientGroup.mk' N) x) from rfl, hx, MulEquiv.apply_symm_apply]⟩
  have hker : ∀ x : E, φ x = 1 → x ∈ Subgroup.center E := by
    intro x hx
    apply hN
    have h1 : (QuotientGroup.mk' N) x = 1 := by
      apply e.injective
      simpa [φ] using hx
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact h1
  have hcenter := center_eq_comap_of_perfect φ hφ hperf hker
  let ψ : E →* (F ⧸ Subgroup.center F) := (QuotientGroup.mk' (Subgroup.center F)).comp φ
  have hψ : Function.Surjective ψ := fun y => by
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨x, hx⟩ := hφ z
    exact ⟨x, by simp [ψ, hx]⟩
  have hkerψ : ψ.ker = Subgroup.center E := by
    ext x
    rw [MonoidHom.mem_ker, hcenter, Subgroup.mem_comap]
    simp [ψ, QuotientGroup.eq_one_iff]
  have hiso : (E ⧸ Subgroup.center E) ≃* (F ⧸ Subgroup.center F) :=
    (QuotientGroup.quotientMulEquivOfEq hkerψ.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)
  have hFs : IsSimpleGroup (F ⧸ Subgroup.center F) := hF.2
  refine ⟨⟨hperf, ?_⟩, ⟨hiso⟩⟩
  exact hiso.isSimpleGroup

theorem quotient_comap_center_equiv {E F : Type} [Group E] [Group F] (φ : E →* F)
    (hφ : Function.Surjective φ) (Z : Subgroup F) [Z.Normal] :
    Nonempty ((E ⧸ Z.comap φ) ≃* (F ⧸ Z)) := by
  let ψ : E →* (F ⧸ Z) := (QuotientGroup.mk' Z).comp φ
  have hψ : Function.Surjective ψ := fun y => by
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨x, hx⟩ := hφ z
    exact ⟨x, by simp [ψ, hx]⟩
  have hkerψ : ψ.ker = Z.comap φ := by
    ext x
    simp [ψ, MonoidHom.mem_ker, QuotientGroup.eq_one_iff]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hkerψ.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)⟩

theorem exists_noncomm_of_perfect {S : Type} [Group S] [Nontrivial S] (hperf : commutator S = ⊤) :
    ∃ a b : S, a * b ≠ b * a := by
  by_contra h
  have h' : ∀ a b : S, a * b = b * a := fun a b => by
    by_contra hab
    exact h ⟨a, b, hab⟩
  have hbot : commutator S = ⊥ := by
    rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro a _
    rw [Subgroup.mem_centralizer_iff]
    intro b _
    exact (h' a b).symm
  rw [hperf] at hbot
  exact (top_ne_bot : (⊤ : Subgroup S) ≠ ⊥) hbot

end CFSG.LocalAnalysis.GLTheoremA.H248
