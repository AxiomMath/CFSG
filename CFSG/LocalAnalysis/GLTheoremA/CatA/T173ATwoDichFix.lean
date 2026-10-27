module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172AExistGL
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173XDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173A

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.S172A.GL (fixSp comSp)
open CFSG.LocalAnalysis.GLTheoremA.T173X
  (stdLayer innerClosure stdFamily IsStdElt StdVanishes StdTyped StdExtends)

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

private theorem fixSp_mem_centralizer_iff (g : V ≃ₗ[ZMod 2] V)
    (c : ↥(Subgroup.centralizer ({g} : Set (V ≃ₗ[ZMod 2] V)))) (x : V) :
    ((c : V ≃ₗ[ZMod 2] V) x ∈ fixSp g) ↔ x ∈ fixSp g := by
  constructor
  · intro hx
    have hc : (c : V ≃ₗ[ZMod 2] V)⁻¹ * g = g * (c : V ≃ₗ[ZMod 2] V)⁻¹ :=
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.inv_mem _ c.2)
    have h := S172A.GL.cent_fix (e := g) (g := (c : V ≃ₗ[ZMod 2] V)⁻¹) hc hx
    simpa using h
  · intro hx
    exact S172A.GL.cent_fix (e := g) (g := (c : V ≃ₗ[ZMod 2] V))
      (Subgroup.mem_centralizer_singleton_iff.mp c.2) hx

private def fixRestrictHom (g : V ≃ₗ[ZMod 2] V) :
    ↥(Subgroup.centralizer ({g} : Set (V ≃ₗ[ZMod 2] V))) →* Equiv.Perm (fixSp g) where
  toFun c := Equiv.Perm.subtypePerm ((c : V ≃ₗ[ZMod 2] V) : V ≃ V)
    (fixSp_mem_centralizer_iff g c)
  map_one' := by
    apply Equiv.ext
    intro x
    apply Subtype.ext
    simp
  map_mul' c d := by
    apply Equiv.ext
    intro x
    apply Subtype.ext
    rfl

@[simp]
private theorem fixRestrictHom_apply (g : V ≃ₗ[ZMod 2] V)
    (c : ↥(Subgroup.centralizer ({g} : Set (V ≃ₗ[ZMod 2] V)))) (x : fixSp g) :
    (fixRestrictHom g c x : V) = (c : V ≃ₗ[ZMod 2] V) (x : V) := rfl

theorem lin_two_layer_fixed_trivial {g : V ≃ₗ[ZMod 2] V} (hg3 : g ^ 3 = 1)
    (hfix : Module.finrank (ZMod 2) (fixSp g) = 2)
    (hcomp : CFSG.Open.IsComponentOf (stdLayer g)
      (Subgroup.centralizer ({g} : Set (V ≃ₗ[ZMod 2] V)))) :
    ∀ l ∈ stdLayer g, ∀ v ∈ fixSp g, l v = v := by
  classical
  haveI : Group.IsPerfect ↥(stdLayer g) := ⟨hcomp.2.2.1⟩
  haveI : Finite V := Module.finite_of_finite (ZMod 2)
  have hcard : Nat.card (fixSp g) ≤ 4 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), hfix]
    norm_num [Nat.card_zmod]
  haveI : Group.IsSolvable (Equiv.Perm (fixSp g)) := Equiv.Perm.isSolvable hcard
  let f : ↥(stdLayer g) →* Equiv.Perm (fixSp g) :=
    (fixRestrictHom g).comp (Subgroup.inclusion hcomp.1)
  haveI : Group.IsPerfect f.range := Group.IsPerfect.range f
  have hbot : f.range = ⊥ := by
    have hnt : ¬ Nontrivial ↥f.range := by
      intro h
      haveI : Nontrivial ↥f.range := h
      have hsol : Group.IsSolvable ↥f.range :=
        Group.isSolvable_of_isSolvable_injective (f := (f.range).subtype)
          (f.range).subtype_injective
      exact (Group.IsPerfect.not_isSolvable f.range) hsol
    haveI : Subsingleton ↥f.range := not_nontrivial_iff_subsingleton.mp hnt
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    exact congrArg Subtype.val (Subsingleton.elim (⟨x, hx⟩ : ↥f.range) 1)
  intro l hl v hv
  have hfl : f ⟨l, hl⟩ = 1 := by
    have hmem : f ⟨l, hl⟩ ∈ f.range := ⟨⟨l, hl⟩, rfl⟩
    rw [hbot] at hmem
    simpa using hmem
  have hval := congrArg (fun e : Equiv.Perm (fixSp g) => (e ⟨v, hv⟩ : V)) hfl
  simpa [f] using hval

end CFSG.LocalAnalysis.GLTheoremA.T173A

end
