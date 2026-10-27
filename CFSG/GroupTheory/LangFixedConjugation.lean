module

public import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Tactic.Group
public import Mathlib.Algebra.Group.End

public section

namespace MonoidHom

variable {G : Type*} [Group G]

theorem apply_mul_inv_eq_of_inv_mul_apply_eq (F : G →* G) {g z : G}
    (h : g⁻¹ * F g = z⁻¹ * F z) : F (g * z⁻¹) = g * z⁻¹ := by
  have hF : F g = g * (z⁻¹ * F z) := by
    calc
      F g = g * (g⁻¹ * F g) := by group
      _ = g * (z⁻¹ * F z) := by rw [h]
  rw [map_mul, map_inv, hF]
  group

end MonoidHom

namespace Subgroup

variable {G : Type*} [Group G]

theorem map_inf_eqLocus_conj_of_inv_mul_apply_eq (A : Subgroup G) (F : G →* G)
    {g n : G} (hN : g ∈ normalizer (A : Set G)) (hLang : g⁻¹ * F g = n) :
    (A ⊓ MonoidHom.eqLocus ((MulAut.conj n).toMonoidHom.comp F) (MonoidHom.id G)).map
        (MulAut.conj g).toMonoidHom = A ⊓ MonoidHom.eqLocus F (MonoidHom.id G) := by
  have hF : F g = g * n := by
    calc
      F g = g * (g⁻¹ * F g) := by group
      _ = g * n := by rw [hLang]
  have hcov (x : G) : F (g * x * g⁻¹) = g * (n * F x * n⁻¹) * g⁻¹ := by
    rw [map_mul, map_mul, map_inv, hF]
    group
  ext w
  constructor
  · intro hw
    obtain ⟨x, hx, rfl⟩ := mem_map.1 hw
    obtain ⟨hxA, hxF⟩ := hx
    refine ⟨(mem_normalizer_iff.1 hN x).1 hxA, ?_⟩
    change F (g * x * g⁻¹) = g * x * g⁻¹
    change n * F x * n⁻¹ = x at hxF
    rw [hcov, hxF]
  · rintro ⟨hwA, hwF⟩
    change F w = w at hwF
    have hxA : g⁻¹ * w * g ∈ A := (mem_normalizer_iff''.1 hN w).1 hwA
    have hback : g * (g⁻¹ * w * g) * g⁻¹ = w := by group
    have hxF : g⁻¹ * w * g ∈
        MonoidHom.eqLocus ((MulAut.conj n).toMonoidHom.comp F) (MonoidHom.id G) := by
      change n * F (g⁻¹ * w * g) * n⁻¹ = g⁻¹ * w * g
      apply (MulAut.conj g).injective
      change g * (n * F (g⁻¹ * w * g) * n⁻¹) * g⁻¹ = g * (g⁻¹ * w * g) * g⁻¹
      rw [← hcov, hback, hwF]
    refine mem_map.2 ⟨g⁻¹ * w * g, ⟨hxA, hxF⟩, ?_⟩
    change g * (g⁻¹ * w * g) * g⁻¹ = w
    exact hback

end Subgroup

namespace Subgroup

variable {G K : Type*} [Group G] [Group K]

theorem exists_conj_of_lang_node_images (F : K →* K) {n0 z g : K}
    (hz : z⁻¹ * F z = n0) (hg : g⁻¹ * F g = n0) (B : Subgroup K)
    (hgN : g ∈ normalizer (B : Set K)) (e : G →* K) (hei : Function.Injective e)
    (herange : e.range = MonoidHom.eqLocus F (MonoidHom.id K)) (N R : Subgroup G)
    (hN : N.map ((MulAut.conj z⁻¹).toMonoidHom.comp e) =
      B ⊓ MonoidHom.eqLocus ((MulAut.conj n0).toMonoidHom.comp F) (MonoidHom.id K))
    (hR : R.map e = B ⊓ MonoidHom.eqLocus F (MonoidHom.id K)) :
    ∃ u : G, R.map (MulAut.conj u).toMonoidHom = N := by
  have hc : F (g * z⁻¹) = g * z⁻¹ :=
    MonoidHom.apply_mul_inv_eq_of_inv_mul_apply_eq F (hg.trans hz.symm)
  have hcrange : g * z⁻¹ ∈ e.range := by
    rw [herange]
    exact hc
  obtain ⟨u, hu⟩ := hcrange
  have hm : (N.map (MulAut.conj u).toMonoidHom).map e =
      (N.map ((MulAut.conj z⁻¹).toMonoidHom.comp e)).map (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.map_map, Subgroup.map_map]
    apply congrArg (fun φ : G →* K => N.map φ)
    apply DFunLike.ext
    intro x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [map_mul, map_mul, map_inv, hu]
    group
  have hNU : N.map (MulAut.conj u).toMonoidHom = R := by
    apply Subgroup.map_injective hei
    rw [hm, hN, Subgroup.map_inf_eqLocus_conj_of_inv_mul_apply_eq B F hgN hg, hR]
  refine ⟨u⁻¹, ?_⟩
  rw [← hNU, Subgroup.map_map]
  have hid : (MulAut.conj u⁻¹).toMonoidHom.comp (MulAut.conj u).toMonoidHom = MonoidHom.id G := by
    apply DFunLike.ext
    intro x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MonoidHom.id_apply]
    group
  rw [hid, Subgroup.map_id]


end Subgroup
