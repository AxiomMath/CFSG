module

public import CFSG.CGT.PushingUpLit.BHS6.NatBridge
public import CFSG.Quasithin.Background.JonesParshallBasic

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.CGT.PushingUpLit.BHS6

structure NatSec (n : ℕ) {V : Type} [CommGroup V] (G : Subgroup (MulAut V)) where
  θ : ↥G ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)
  β : ↥(commV G) →* Multiplicative (Fin 2 → GaloisField 2 n)
  surj : Function.Surjective β
  ker : β.ker = (commV G ⊓ fixV G).subgroupOf (commV G)
  equiv : ∀ (g : ↥G) (p : ↥(commV G)) (hp : (g : MulAut V) (p : V) ∈ commV G),
    β ⟨(g : MulAut V) (p : V), hp⟩ = Multiplicative.ofAdd
      ((θ g : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)).mulVec (Multiplicative.toAdd (β p)))

theorem NatSec.exists_of_isNatSectionBy {n : ℕ} {V : Type} [CommGroup V]
    {G : Subgroup (MulAut V)}
    (h : IsNatSectionBy (fun (s : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n))
        (x : Multiplicative (Fin 2 → GaloisField 2 n)) =>
          Multiplicative.ofAdd ((s : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)).mulVec
            (Multiplicative.toAdd x))) G (commV G) (commV G ⊓ fixV G)) :
    Nonempty (NatSec n G) := by
  obtain ⟨-, θ, β, hs, hk, he⟩ := h
  exact ⟨⟨θ, β, hs, hk, he⟩⟩

variable {V : Type} [CommGroup V] {G : Subgroup (MulAut V)}

theorem commV_apply_mem {g : MulAut V} (hg : g ∈ G) {u : V} (hu : u ∈ commV G) :
    g u ∈ commV G :=
  CFSG.Quasithin.commV_apply_mem_of_mem hg hu

@[expose] def commEl (g : ↥G) (v : V) : ↥(commV G) :=
  ⟨(g : MulAut V) v * v⁻¹, Subgroup.subset_closure ⟨(g : MulAut V), g.2, v, rfl⟩⟩

theorem commEl_val (g : ↥G) (v : V) : (commEl g v : V) = (g : MulAut V) v * v⁻¹ := rfl

theorem commEl_mul_left (g h : ↥G) (v : V) :
    commEl (g * h) v = ⟨(g : MulAut V) (commEl h v : V), commV_apply_mem g.2 (commEl h v).2⟩ *
      commEl g v := by
  apply Subtype.ext
  change ((g : MulAut V) * (h : MulAut V)) v * v⁻¹ = (g : MulAut V) ((h : MulAut V) v * v⁻¹) *
    ((g : MulAut V) v * v⁻¹)
  rw [map_mul, map_inv]
  simp only [MulAut.mul_apply]
  group

theorem commEl_mul_right (g : ↥G) (v w : V) : commEl g (v * w) = commEl g v * commEl g w := by
  apply Subtype.ext
  change (g : MulAut V) (v * w) * (v * w)⁻¹ = ((g : MulAut V) v * v⁻¹) * ((g : MulAut V) w * w⁻¹)
  rw [map_mul, mul_inv]
  exact mul_mul_mul_comm _ _ _ _

section Cocycle

variable {n : ℕ} (S : NatSec n G)
  (ρ : Representation (ZMod 2) ↥G (Fin 2 → GaloisField 2 n))
  (hρ : ∀ (g : ↥G) (w : Fin 2 → GaloisField 2 n),
    ρ g w = (S.θ g : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)).mulVec w)

@[expose] noncomputable def NatSec.cv (v : V) : ↥G → (Fin 2 → GaloisField 2 n) :=
  fun g => Multiplicative.toAdd (S.β (commEl g v))

omit hρ ρ in
theorem NatSec.cv_one : S.cv (1 : V) = 0 := by
  funext g
  have : commEl g (1 : V) = 1 := Subtype.ext (by simp [commEl_val])
  simp [NatSec.cv, this]

omit hρ ρ in
theorem NatSec.cv_mul (v w : V) : S.cv (v * w) = S.cv v + S.cv w := by
  funext g
  simp [NatSec.cv, commEl_mul_right, toAdd_mul]

include hρ in
theorem NatSec.cv_cocycle (v : V) : ∀ g h, S.cv v (g * h) = S.cv v g + ρ g (S.cv v h) := by
  intro g h
  have hp := commV_apply_mem g.2 (commEl h v).2
  have e := S.equiv g (commEl h v) hp
  have hmul := congrArg S.β (commEl_mul_left g h v)
  rw [map_mul, e] at hmul
  simp only [NatSec.cv]
  rw [hmul, toAdd_mul, toAdd_ofAdd, hρ, add_comm]

include hρ in
theorem NatSec.cv_mem_Z1 (v : V) : S.cv v ∈ Z1 ρ := S.cv_cocycle ρ hρ v

include hρ in
theorem NatSec.cv_apply_of_mem {u : V} (hu : u ∈ commV G) (g : ↥G) :
    S.cv u g = ρ g (Multiplicative.toAdd (S.β ⟨u, hu⟩)) - Multiplicative.toAdd (S.β ⟨u, hu⟩) := by
  have hp := commV_apply_mem g.2 hu
  have e := S.equiv g ⟨u, hu⟩ hp
  have h1 : commEl g u = ⟨(g : MulAut V) u, hp⟩ * (⟨u, hu⟩ : ↥(commV G))⁻¹ := Subtype.ext rfl
  change Multiplicative.toAdd (S.β (commEl g u)) = _
  rw [h1, map_mul, map_inv, e, toAdd_mul, toAdd_inv, toAdd_ofAdd, hρ, sub_eq_add_neg]

include hρ in
theorem NatSec.cv_mem_B1 {u : V} (hu : u ∈ commV G) : S.cv u ∈ B1 ρ :=
  ⟨Multiplicative.toAdd (S.β ⟨u, hu⟩), funext fun g => (S.cv_apply_of_mem ρ hρ hu g).symm⟩

@[expose] noncomputable def NatSec.Lam : V →* Multiplicative (H1 ρ) where
  toFun v := Multiplicative.ofAdd
    (Submodule.Quotient.mk (⟨S.cv v, S.cv_mem_Z1 ρ hρ v⟩ : Z1 ρ) : H1 ρ)
  map_one' := by
    have : (⟨S.cv (1 : V), S.cv_mem_Z1 ρ hρ 1⟩ : Z1 ρ) = 0 := Subtype.ext (S.cv_one)
    simp only [this]
    rfl
  map_mul' v w := by
    have : (⟨S.cv (v * w), S.cv_mem_Z1 ρ hρ (v * w)⟩ : Z1 ρ) =
        ⟨S.cv v, S.cv_mem_Z1 ρ hρ v⟩ + ⟨S.cv w, S.cv_mem_Z1 ρ hρ w⟩ := Subtype.ext (S.cv_mul v w)
    simp only [this, Submodule.Quotient.mk_add]
    rfl

include hρ in
theorem NatSec.Lam_eq_one_iff (v : V) : S.Lam ρ hρ v = 1 ↔ S.cv v ∈ B1 ρ := by
  change Multiplicative.ofAdd (Submodule.Quotient.mk (⟨S.cv v, S.cv_mem_Z1 ρ hρ v⟩ : Z1 ρ) :
    H1 ρ) = 1 ↔ _
  rw [← ofAdd_zero, Multiplicative.ofAdd.injective.eq_iff, Submodule.Quotient.mk_eq_zero]
  rfl

end Cocycle

end CFSG.CGT.PushingUpLit.CGT6
