module

public import CFSG.Yardstones.Md0ec50421ce4.Definitions

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.StdD4

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open scoped commutatorElement

theorem eq_of_mod_center_of_commutator_eq_top {X : Type} [Group X] (hX : commutator X = ⊤) (f g : X →* X)
    (h : ∀ x : X, (f x)⁻¹ * g x ∈ Subgroup.center X) (x : X) : f x = g x := by
  let c : X →* X := MonoidHom.mk' (fun y => (f y)⁻¹ * g y) (fun y z => by
    have hz : (f z)⁻¹ * ((f y)⁻¹ * g y) = ((f y)⁻¹ * g y) * (f z)⁻¹ :=
      Subgroup.mem_center_iff.1 (h y) _
    calc (f (y * z))⁻¹ * g (y * z)
        = (f z)⁻¹ * ((f y)⁻¹ * g y) * g z := by
          rw [map_mul, map_mul]; group
      _ = ((f y)⁻¹ * g y) * ((f z)⁻¹ * g z) := by
          rw [hz]; group)
  have hc : ∀ y : X, c y = (f y)⁻¹ * g y := fun y => rfl
  have hcomm : ∀ u v : X, c ⁅u, v⁆ = 1 := by
    intro u v
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    rw [hc u, hc v]
    exact (Subgroup.mem_center_iff.1 (h u) _).symm
  have hle : commutator X ≤ c.ker := by
    rw [commutator_def]
    exact Subgroup.commutator_le.2 (fun u _ v _ => MonoidHom.mem_ker.2 (hcomm u v))
  rw [hX] at hle
  have hx : c x = 1 := MonoidHom.mem_ker.1 (hle (Subgroup.mem_top x))
  rw [hc x] at hx
  exact inv_mul_eq_one.1 hx

theorem inducesInnerMod_of_perfect {G : Type} [Group G] (L : Subgroup G) (hL : commutator ↥L = ⊤) (p : ℕ) (b : G)
    (hbN : ∀ l ∈ L, b⁻¹ * l * b ∈ L) {R : Type} [Group R] (θ : ↥L ⧸ Subgroup.center ↥L ≃* R) (r : R)
    (hind : ∀ l : ↥L, θ (QuotientGroup.mk ⟨b⁻¹ * (l : G) * b, hbN l l.2⟩) = r * θ (QuotientGroup.mk l) * r⁻¹) :
    InducesInnerMod p L b := by
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (θ.symm r)
  have hxr : θ (QuotientGroup.mk x) = r := by
    rw [hx, MulEquiv.apply_symm_apply]
  let f : ↥L →* ↥L := MonoidHom.mk' (fun l => ⟨b⁻¹ * (l : G) * b, hbN l l.2⟩)
    (fun u v => Subtype.ext (by simp [mul_assoc]))
  let g : ↥L →* ↥L := (MulAut.conj x).toMonoidHom
  have hfg : ∀ l : ↥L, θ (QuotientGroup.mk (f l)) = θ (QuotientGroup.mk (g l)) := by
    intro l
    have hfl : f l = ⟨b⁻¹ * (l : G) * b, hbN l l.2⟩ := rfl
    have hgl : (QuotientGroup.mk (g l) : ↥L ⧸ Subgroup.center ↥L) =
        QuotientGroup.mk x * QuotientGroup.mk l * (QuotientGroup.mk x)⁻¹ := by
      simp only [g, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [hfl, hind l, hgl, map_mul, map_mul, map_inv, hxr]
  have hcen : ∀ l : ↥L, (f l)⁻¹ * g l ∈ Subgroup.center ↥L := fun l =>
    QuotientGroup.eq.1 (θ.injective (hfg l))
  have hfeq : ∀ l : ↥L, f l = g l := fun l =>
    eq_of_mod_center_of_commutator_eq_top hL f g hcen l
  unfold InducesInnerMod
  refine ⟨(x : G)⁻¹, L.inv_mem x.2, fun y hy => ?_⟩
  have hy' : b⁻¹ * y * b = (x : G) * y * (x : G)⁻¹ := by
    have := congrArg Subtype.val (hfeq ⟨y, hy⟩)
    simpa [f, g, MulAut.conj_apply] using this
  rw [inv_inv, hy', inv_mul_cancel]
  exact Subgroup.one_mem _

end CFSG.LocalAnalysis.GLTheoremA.CatB.StdD4
