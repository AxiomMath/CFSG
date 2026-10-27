module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.HallSubgroups.Core
public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.GroupTheory

open Subgroup

@[expose] def SylowPQMaximal (p q : ℕ) (Y : Type*) [Group Y] : Prop :=
  ∀ (P : Sylow p Y) (H : Subgroup Y), (P : Subgroup Y) ≤ H →
    IsPiSubgroup {r : Nat.Primes | (r : ℕ) = p ∨ (r : ℕ) = q} H → IsPGroup p H

variable {p q : ℕ} {Y : Type*} [Group Y]

theorem isPiSubgroup_pair_iff {H : Subgroup Y} :
    IsPiSubgroup {r : Nat.Primes | (r : ℕ) = p ∨ (r : ℕ) = q} H ↔
      ∀ r : ℕ, r.Prime → r ∣ Nat.card H → r = p ∨ r = q :=
  ⟨fun h r hr hdvd => h ⟨r, hr⟩ hdvd, fun h r hdvd => h r r.2 hdvd⟩

theorem SylowPQMaximal.of_mulEquiv {Y' : Type*} [Group Y'] (e : Y ≃* Y')
    (h : SylowPQMaximal p q Y) : SylowPQMaximal p q Y' := by
  intro P H hPH hH
  have hinj : Function.Injective e.toMonoidHom := e.injective
  have hsurj : Function.Surjective e.toMonoidHom := e.surjective
  have hrange : (P : Subgroup Y') ≤ e.toMonoidHom.range := by
    rw [MonoidHom.range_eq_top.mpr hsurj]
    exact le_top
  have hmap := Subgroup.map_comap_eq_self_of_surjective hsurj H
  have hcard : Nat.card (H.comap e.toMonoidHom) = Nat.card H := by
    conv_rhs => rw [← hmap]
    exact (Subgroup.card_map_of_injective hinj).symm
  have h₀ := h (P.comapOfInjective e.toMonoidHom hinj hrange) (H.comap e.toMonoidHom)
    (Subgroup.comap_mono hPH) (fun r hr => hH r (hcard ▸ hr))
  have h₁ := h₀.map e.toMonoidHom
  rwa [hmap] at h₁

theorem SylowPQMaximal.of_isPGroup (hY : IsPGroup p Y) : SylowPQMaximal p q Y :=
  fun _ H _ _ => hY.to_subgroup H

end CFSG.GroupTheory
