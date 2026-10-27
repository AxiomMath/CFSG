module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4FamModel
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk95Gen

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.LU.Local CFSG.Blueprint
  CFSG.Sporadic.Schreier
open scoped commutatorElement

theorem Ivk95Cfg.false_of_model_class {M : Type} [Group M] {P R A : Subgroup M} {tX : M}
    (hM : Ivk73Model P R A tX) {J : Type} [Group J] [Finite J] {z : J} (h : Ivk95Cfg z)
    (θ : J ≃* ↥P) {g : M} (hg : g ∈ R) (hgt : ((θ z : ↥P) : M) = g * tX * g⁻¹) : False := by
  have hnorm : ∀ x ∈ P, g * x * g⁻¹ ∈ P := hM.autModel.conj_mem g hg
  have hnorm' : ∀ x ∈ P, g⁻¹ * x * g ∈ P := fun x hx => by
    simpa using hM.autModel.conj_mem g⁻¹ (R.inv_mem hg) x hx
  let ι : J →* M := P.subtype.comp θ.toMonoidHom
  have hι : Function.Injective ι := fun a b hab => θ.injective (Subtype.ext hab)
  let A' : Subgroup M := A.map (MulAut.conj g).toMonoidHom
  have hcent := GHInv.map_conj_centralizerIn_of_norm hnorm hnorm' tX
  have hmem : ∀ x ∈ centralizer ({z} : Set J), ι x ∈ (centralizerIn P tX).map (MulAut.conj g).toMonoidHom := by
    intro x hx
    rw [hcent, mem_centralizerIn]
    refine ⟨(θ x).2, ?_⟩
    rw [← hgt]
    have := mem_centralizer_singleton_iff.mp hx
    have h2 : θ x * θ z = θ z * θ x := by rw [← map_mul, ← map_mul, this]
    exact congrArg Subtype.val h2
  refine h.false_of_derived_le (F := A'.comap ι) ?_ ?_
  · have hfinA : Finite ↥A := Nat.finite_of_card_ne_zero (by rw [hM.card_A]; norm_num)
    have hfinA' : Finite ↥A' :=
      Finite.of_equiv ↥A (A.equivMapOfInjective (MulAut.conj g).toMonoidHom
        (MulAut.conj g).injective).toEquiv
    have h1 : Nat.card ↥(A'.comap ι) ≤ Nat.card ↥A' :=
      Nat.card_le_card_of_injective (fun x => (⟨ι x.1, x.2⟩ : ↥A'))
        (fun a b hab => by
          apply Subtype.ext
          have h3 := congrArg Subtype.val hab
          exact hι h3)
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hM.card_A] at h1
    omega
  · intro x hx y hy
    obtain ⟨a, ha, hax⟩ := hmem x hx
    obtain ⟨b, hb, hby⟩ := hmem y hy
    show ι ⁅x, y⁆ ∈ A'
    rw [map_commutatorElement, ← hax, ← hby]
    refine ⟨⁅a, b⁆, hM.derived a ha b hb, ?_⟩
    simp [commutatorElement_def, MulAut.conj_apply]
    group

end CFSG.GH74.GLS.IVK.Proofs2
