module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.OffenderTensor
public import CFSG.Quasithin.Background.B6Defs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian

public section

namespace CFSG.QuasithinUnique.Setup.Layer

open CFSG.QuasithinUnique.Setup.Offender CFSG.Quasithin.B6
open TensorProduct Module

universe u

section Res

variable (k : Type*) {F : Type*} [Field k] [Field F] [Algebra k F] {W : Type*} [AddCommGroup W]
  [Module k W] [Module F W] [IsScalarTower k F W]

@[expose] def resK : (W ≃ₗ[F] W) →* (W ≃ₗ[k] W) where
  toFun f := f.restrictScalars k
  map_one' := rfl
  map_mul' _ _ := rfl

variable {k}

theorem resK_apply (f : W ≃ₗ[F] W) (w : W) : resK k f w = f w := rfl

theorem resK_injective : Function.Injective (resK k : (W ≃ₗ[F] W) →* (W ≃ₗ[k] W)) := fun f g h =>
  LinearEquiv.ext fun w => by
    have := congrArg (fun x : W ≃ₗ[k] W => x w) h
    exact this

theorem mem_range_resK {g : W ≃ₗ[k] W} (h : ∀ (c : F) (w : W), g (c • w) = c • g w) :
    g ∈ (resK k : (W ≃ₗ[F] W) →* (W ≃ₗ[k] W)).range :=
  ⟨{ g with map_smul' := fun c w => h c w }, LinearEquiv.ext fun _ => rfl⟩

end Res

section Transport

theorem isPerfect_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (h : Group.IsPerfect G) : Group.IsPerfect H := by
  rw [Group.isPerfect_def] at h ⊢
  rw [commutator_def] at h ⊢
  rw [← Subgroup.map_top_of_surjective e.toMonoidHom e.surjective, ← Subgroup.map_commutator, h,
    Subgroup.map_top_of_surjective e.toMonoidHom e.surjective]

theorem isPerfect_of_map_eq {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Injective f) (K : Subgroup G) {K' : Subgroup H} (hK : K.map f = K')
    (h : Group.IsPerfect ↥K') : Group.IsPerfect ↥K := by
  subst hK
  exact isPerfect_of_mulEquiv (K.equivMapOfInjective f hf).symm h

theorem nontrivial_of_map_eq {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Injective f) (K : Subgroup G) {K' : Subgroup H} (hK : K.map f = K')
    (h : Nontrivial ↥K') : Nontrivial ↥K := by
  subst hK
  exact (K.equivMapOfInjective f hf).toEquiv.nontrivial

theorem isElementaryAbelian_comap {p : ℕ} {X Y : Type*} [Group X] [Group Y] (f : X →* Y)
    (hf : Function.Injective f) (B : Subgroup Y) [hB : CFSG.IsElementaryAbelian p ↥B] :
    CFSG.IsElementaryAbelian p ↥(B.comap f) := by
  refine { is_comm := ⟨fun a b => ?_⟩, exponent_dvd_p := ?_ }
  · apply Subtype.ext
    have := congrArg Subtype.val
      (hB.toIsMulCommutative.is_comm.comm ⟨f a, a.2⟩ ⟨f b, b.2⟩)
    apply hf
    simpa using this
  · refine Monoid.exponent_dvd_of_forall_pow_eq_one fun g => ?_
    apply Subtype.ext
    have h1 := Monoid.exponent_dvd_iff_forall_pow_eq_one.1 hB.exponent_dvd_p ⟨f g, g.2⟩
    apply hf
    have h2 : (f g) ^ p = 1 := congrArg Subtype.val h1
    simpa using h2

theorem conjSub_comap {G H : Type*} [Group G] [Group H] (f : G →* H) (a : G) (X : Subgroup H) :
    conjSub a (X.comap f) = (conjSub (f a) X).comap f := by
  ext x
  rw [mem_conjSub, Subgroup.mem_comap, Subgroup.mem_comap, mem_conjSub]
  simp [map_mul, map_inv]

end Transport

end CFSG.QuasithinUnique.Setup.Layer
