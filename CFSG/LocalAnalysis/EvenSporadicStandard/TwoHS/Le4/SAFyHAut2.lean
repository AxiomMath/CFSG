module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFyHAut
public import CFSG.RankThree.Transfer.Wreath

public section

namespace CFSG.EvenSporadicStandard.TwoHS

namespace SAFyHAut

open CFSG.RankThree.Transfer

section Restr

variable {A : Type*} [Group A] [Finite A]

@[expose] noncomputable def restr (α : MulAut (A × A)) (h : α ∈ presSubgroup A) : MulAut A :=
  MulEquiv.ofBijective (restrHom α)
    ⟨restrHom_injective (mem_presSubgroup.mp h),
      Finite.surjective_of_injective (restrHom_injective (mem_presSubgroup.mp h))⟩

theorem restr_apply (α : MulAut (A × A)) (h : α ∈ presSubgroup A) (a : A) :
    restr α h a = (α (a, 1)).1 := rfl

theorem apply_one_eq_restr (α : MulAut (A × A)) (h : α ∈ presSubgroup A) (a : A) :
    α (a, 1) = (restr α h a, 1) :=
  Prod.ext rfl (mem_presSubgroup.mp h a)

theorem restr_eq_iff (α : MulAut (A × A)) (h : α ∈ presSubgroup A) (e : MulAut A) :
    restr α h = e ↔ ∀ a, α (a, 1) = (e a, 1) := by
  constructor
  · rintro rfl a
    exact apply_one_eq_restr α h a
  · intro H
    ext a
    rw [restr_apply, H a]

end Restr

section Wreath

variable {A : Type*} [Group A] [Finite A] [IsSimpleGroup A] (hZ : Subgroup.center A = ⊥)

@[expose] noncomputable def theta : (phi hZ).ker →* MulAut A where
  toFun α := restr α.1 ((phi_eq_one_iff hZ).mp α.2)
  map_one' := by
    rw [restr_eq_iff]
    intro a
    rfl
  map_mul' α β := by
    rw [restr_eq_iff]
    intro a
    show (α.1 * β.1) (a, 1) = _
    rw [MulAut.mul_apply, apply_one_eq_restr β.1 ((phi_eq_one_iff hZ).mp β.2) a,
      apply_one_eq_restr α.1 ((phi_eq_one_iff hZ).mp α.2), MulAut.mul_apply]

theorem theta_eq_iff {g : MulAut (A × A)} (hg : g ∈ (phi hZ).ker) (e : MulAut A) :
    theta hZ ⟨g, hg⟩ = e ↔ ∀ a, g (a, 1) = (e a, 1) :=
  restr_eq_iff g ((phi_eq_one_iff hZ).mp hg) e

@[expose] noncomputable def kk :
    MulAut (A × A) →* MulAut A ≀ᵣ Multiplicative (ZMod 2) :=
  kaloujnineKrasner (phi hZ) (sect A) (phi_sect hZ) (theta hZ)

theorem kk_left_eq_iff {α : MulAut (A × A)} (hα : phi hZ α = 1) (x : Multiplicative (ZMod 2))
    (e : MulAut A) :
    (kk hZ α).left x = e ↔ ∀ a, ((sect A x)⁻¹ * α * sect A x) (a, 1) = (e a, 1) := by
  have h : (kk hZ α).left x =
      theta hZ ⟨_, kaloujnineKrasner_mem (phi hZ) (sect A) (phi_sect hZ) α x⟩ := rfl
  rw [h, theta_eq_iff]
  simp only [hα, inv_one, one_mul]

theorem kk_left_one_eq_iff {α : MulAut (A × A)} (hα : phi hZ α = 1) (e : MulAut A) :
    (kk hZ α).left 1 = e ↔ ∀ a, α (a, 1) = (e a, 1) := by
  rw [kk_left_eq_iff hZ hα, sect_one]
  simp

theorem kk_left_ofAdd_one_eq_iff {α : MulAut (A × A)} (hα : phi hZ α = 1) (e : MulAut A) :
    (kk hZ α).left (Multiplicative.ofAdd 1) = e ↔ ∀ a, α (1, a) = (1, e a) := by
  rw [kk_left_eq_iff hZ hα, sect_ofAdd_one, sw_inv]
  refine forall_congr' fun a => ?_
  simp [MulAut.mul_apply, Prod.swap_eq_iff_eq_swap]

theorem kk_injective : Function.Injective (kk hZ) := by
  rw [injective_iff_map_eq_one]
  intro α hα
  have h1 : phi hZ α = 1 := congrArg RegularWreathProduct.right hα
  have hl : ∀ x, (kk hZ α).left x = 1 := fun x => by rw [hα]; rfl
  have e1 := (kk_left_one_eq_iff hZ h1 1).mp (hl 1)
  have e2 := (kk_left_ofAdd_one_eq_iff hZ h1 1).mp (hl _)
  refine MulEquiv.ext fun x => ?_
  obtain ⟨a, b⟩ := x
  have hx : ((a, b) : A × A) = (a, 1) * (1, b) := by simp
  rw [hx, map_mul, e1 a, e2 b]
  simp

theorem kk_surjective : Function.Surjective (kk hZ) := by
  refine kaloujnineKrasner_surjective (phi hZ) (sect A) (phi_sect hZ) (theta hZ) fun f => ?_
  let r : MulAut (A × A) := MulEquiv.prodCongr (f 1) (f (Multiplicative.ofAdd 1))
  have hr0 : ∀ a b, r (a, b) = (f 1 a, f (Multiplicative.ofAdd 1) b) := fun a b => rfl
  have hr : r ∈ (phi hZ).ker := by
    rw [MonoidHom.mem_ker, phi_eq_one_iff]
    intro a
    simp [hr0]
  refine ⟨⟨r, hr⟩, fun x => ?_⟩
  have hx : x = 1 ∨ x = Multiplicative.ofAdd 1 := by revert x; decide
  have h1 : phi hZ r = 1 := hr
  rcases hx with rfl | rfl
  · exact (kk_left_one_eq_iff hZ h1 _).mpr fun a => by simp [hr0]
  · exact (kk_left_ofAdd_one_eq_iff hZ h1 _).mpr fun a => by simp [hr0]

noncomputable def mulAutProdEquivWreath :
    MulAut (A × A) ≃* MulAut A ≀ᵣ Multiplicative (ZMod 2) :=
  MulEquiv.ofBijective (kk hZ) ⟨kk_injective hZ, kk_surjective hZ⟩

end Wreath

end SAFyHAut

end CFSG.EvenSporadicStandard.TwoHS
