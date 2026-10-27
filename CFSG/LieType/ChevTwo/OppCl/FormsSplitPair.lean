module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LieType.BorelTits.FormFlag

public section

namespace CFSG.LieType.ChevTwo.OppCl.FS

open CFSG.LieType.BorelTits

variable {F : Type} [Field F] [Finite F] {V : Type} [AddCommGroup V] [Module F V] [Finite V]



theorem finrank_compl_eq (Φ : ReflForm F V) (W Cc : Submodule F V)
    (hC : IsCompl (Φ.perp W) Cc) : Module.finrank F Cc = Module.finrank F W := by
  haveI : FiniteDimensional F V := Module.Finite.of_finite
  have h1 := Φ.finrank_perp W
  have h2 := Submodule.finrank_add_eq_of_isCompl hC
  omega

theorem eq_zero_of_forall_β_compl (Φ : ReflForm F V) (W Cc : Submodule F V)
    (hC : IsCompl (Φ.perp W) Cc) {w : V} (hw : w ∈ W) (h : ∀ c ∈ Cc, Φ.β w c = 0) : w = 0 := by
  refine Φ.nondeg w fun v => ?_
  have hv : v ∈ Φ.perp W ⊔ Cc := by
    rw [hC.sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨p, hp, c, hc, rfl⟩ := Submodule.mem_sup.mp hv
  rw [Φ.add_right, Φ.mem_perp.mp hp w hw, h c hc, add_zero]

theorem exists_β_eq (Φ : ReflForm F V) (W Cc : Submodule F V) (hC : IsCompl (Φ.perp W) Cc)
    (φ : Cc →ₗ[F] F) : ∃ w ∈ W, ∀ c : Cc, Φ.β w (c : V) = φ c := by
  haveI : FiniteDimensional F V := Module.Finite.of_finite
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : W → Module.Dual F Cc,
      ∀ (w : W) (c : Cc), Ψ w c = Φ.β (w : V) (c : V) :=
    ⟨fun w => LinearMap.comp (Φ.toDual (w : V)) Cc.subtype, fun _ _ => rfl⟩
  have hinj : Function.Injective Ψ := by
    intro w w' h
    have hzero : (w : V) - (w' : V) = 0 := by
      refine eq_zero_of_forall_β_compl Φ W Cc hC (sub_mem w.2 w'.2) fun c hc => ?_
      have hβ : Φ.β (w : V) c = Φ.β (w' : V) c := by
        have e1 := hΨ w ⟨c, hc⟩
        have e2 := hΨ w' ⟨c, hc⟩
        rw [h] at e1
        exact e1.symm.trans e2
      rw [Φ.β_sub_left, hβ, sub_self]
    exact Subtype.ext (sub_eq_zero.mp hzero)
  have hcard : Nat.card (Module.Dual F Cc) = Nat.card W := by
    have h1 : Nat.card (Module.Dual F Cc) = Nat.card F ^ Module.finrank F (Module.Dual F Cc) :=
      Module.natCard_eq_pow_finrank
    have h2 : Nat.card W = Nat.card F ^ Module.finrank F W := Module.natCard_eq_pow_finrank
    rw [h1, h2, Subspace.dual_finrank_eq, finrank_compl_eq Φ W Cc hC]
  haveI : Finite (Module.Dual F Cc) := Module.finite_of_finite F
  have hbij : Function.Bijective Ψ := hinj.bijective_of_nat_card_le hcard.le
  obtain ⟨w, hw⟩ := hbij.2 φ
  refine ⟨(w : V), w.2, fun c => ?_⟩
  rw [← hΨ, hw]

end CFSG.LieType.ChevTwo.OppCl.FS
