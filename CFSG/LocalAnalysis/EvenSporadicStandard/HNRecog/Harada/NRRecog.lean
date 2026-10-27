module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.NRWreath
public import CFSG.Monster.B.Recog.GenericIndexTwo

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup

variable {N : Type*} [Group N]

theorem nonempty_mulEquiv_a5WrTwo {L : Subgroup N}
    (e : alternatingGroup (Fin 5) × alternatingGroup (Fin 5) ≃* L) (hL : L.index = 2) {v : N}
    (hv : v ∉ L) (hv2 : v * v = 1) (hswap : ∀ a b, v * (e (a, b) : N) * v⁻¹ = e (b, a)) :
    Nonempty (N ≃* A5WrTwo) := by
  have hrange : (L.subtype.comp e.toMonoidHom).range = L := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr e.surjective, Subgroup.map_top,
      Subgroup.range_subtype]
  obtain ⟨e', -, -⟩ := CFSG.Monster.B.Recog.exists_mulEquiv_of_index_two_of_eq
    (L.subtype.comp e.toMonoidHom) wrBase
    (L.subtype_injective.comp e.injective) wrBase_injective
    (by rw [hrange]; exact hL) index_range_wrBase
    (by rw [hrange]; exact hv) wrSwap_notMem_range_wrBase
    Prod.swap 1
    (fun ⟨x, y⟩ => by simpa using hswap x y)
    (fun p => wrSwap_mul_wrBase_mul_inv p)
    (by rw [hv2, map_one])
    wrSwap_mul_self
  exact ⟨e'⟩

theorem nonempty_mulEquiv_a5WrTwo_of_components (L₁ : Subgroup N)
    (e₁ : alternatingGroup (Fin 5) ≃* L₁) {v : N} (hv2 : v * v = 1)
    (hcomm : ∀ x ∈ L₁, ∀ y ∈ L₁, x * (v * y * v⁻¹) = v * y * v⁻¹ * x)
    (hdisj : ∀ x ∈ L₁, ∀ y ∈ L₁, x = v * y * v⁻¹ → x = 1)
    (hidx : (L₁ ⊔ L₁.map (MulAut.conj v).toMonoidHom).index = 2) :
    Nonempty (N ≃* A5WrTwo) := by
  let f : alternatingGroup (Fin 5) →* N := L₁.subtype.comp e₁.toMonoidHom
  let L₂ : Subgroup N := L₁.map (MulAut.conj v).toMonoidHom
  let g : alternatingGroup (Fin 5) →* N := (MulAut.conj v).toMonoidHom.comp f
  have hfrange : f.range = L₁ := by
    change (L₁.subtype.comp e₁.toMonoidHom).range = L₁
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr e₁.surjective, Subgroup.map_top,
      Subgroup.range_subtype]
  have hgrange : g.range = L₂ := by
    change ((MulAut.conj v).toMonoidHom.comp f).range = L₂
    rw [MonoidHom.range_comp, hfrange]
  have hfmem : ∀ a, f a ∈ L₁ := fun a => by
    rw [← hfrange]
    exact ⟨a, rfl⟩
  have hg_apply : ∀ a, g a = v * f a * v⁻¹ := fun _ => rfl
  have hfinj : Function.Injective f := fun _ _ h => e₁.injective (Subtype.ext h)
  have hginj : Function.Injective g := (MulAut.conj v).injective.comp hfinj
  have hcommute : ∀ a b, Commute (f a) (g b) := fun a b => by
    show f a * g b = g b * f a
    rw [hg_apply b]
    exact hcomm (f a) (hfmem a) (f b) (hfmem b)
  let φ : alternatingGroup (Fin 5) × alternatingGroup (Fin 5) →* N :=
    MonoidHom.noncommCoprod f g hcommute
  have hφ_apply : ∀ a b, φ (a, b) = f a * g b := fun _ _ => rfl
  have hdisjr : Disjoint f.range g.range := by
    rw [disjoint_iff_inf_le]
    intro x hx
    rw [Subgroup.mem_bot]
    obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp hx.1
    obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp hx.2
    rw [← ha]
    exact hdisj (f a) (hfmem a) (f b) (hfmem b) (by rw [ha, ← hb, hg_apply b])
  have hφinj : Function.Injective φ :=
    (MonoidHom.noncommCoprod_injective f g hcommute).mpr ⟨hfinj, hginj, hdisjr⟩
  have hφrange : φ.range = L₁ ⊔ L₂ := by
    change (MonoidHom.noncommCoprod f g hcommute).range = L₁ ⊔ L₂
    rw [MonoidHom.noncommCoprod_range f g hcommute, hfrange, hgrange]
  have hφindex : φ.range.index = 2 := by rw [hφrange]; exact hidx
  have hvg : ∀ b, v * g b * v⁻¹ = f b := fun b => by
    rw [hg_apply b]
    calc v * (v * f b * v⁻¹) * v⁻¹ = (v * v) * f b * (v⁻¹ * v⁻¹) := by group
      _ = f b := by rw [hv2, one_mul, ← mul_inv_rev, hv2, inv_one, mul_one]
  have hswapφ : ∀ a b, v * (MonoidHom.ofInjective hφinj (a, b) : N) * v⁻¹ =
      (MonoidHom.ofInjective hφinj (b, a) : N) := by
    intro a b
    rw [MonoidHom.ofInjective_apply, MonoidHom.ofInjective_apply, hφ_apply a b, hφ_apply b a]
    calc v * (f a * g b) * v⁻¹ = (v * f a * v⁻¹) * (v * g b * v⁻¹) := by group
      _ = g a * f b := by rw [← hg_apply a, hvg b]
      _ = f b * g a := (hcommute b a).eq.symm
  have hvnot : v ∉ φ.range := by
    intro hvmem
    obtain ⟨p, hp⟩ := MonoidHom.mem_range.mp hvmem
    obtain ⟨a, b⟩ := p
    have hpa : v = f a * g b := by rw [← hp, hφ_apply a b]
    have hL1bot : ∀ w ∈ L₁, w = 1 := by
      intro w hw
      have hcommw : g b * w = w * g b := (hcomm w hw (f b) (hfmem b)).symm
      have hmem : v * w * v⁻¹ ∈ L₁ := by
        have heq : (f a * g b) * w * (f a * g b)⁻¹ = f a * w * (f a)⁻¹ := by
          calc (f a * g b) * w * (f a * g b)⁻¹
              = f a * (g b * w) * (f a * g b)⁻¹ := by group
            _ = f a * (w * g b) * (f a * g b)⁻¹ := by rw [hcommw]
            _ = f a * w * (f a)⁻¹ := by group
        rw [hpa, heq]
        exact L₁.mul_mem (L₁.mul_mem (hfmem a) hw) (L₁.inv_mem (hfmem a))
      have hx1 : v * w * v⁻¹ = 1 := hdisj (v * w * v⁻¹) hmem w hw rfl
      calc w = v⁻¹ * (v * w * v⁻¹) * v := by group
        _ = 1 := by rw [hx1]; group
    haveI : Subsingleton L₁ :=
      ⟨fun x y => Subtype.ext (by rw [hL1bot x x.2, hL1bot y y.2])⟩
    haveI : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
    exact not_subsingleton (alternatingGroup (Fin 5)) e₁.injective.subsingleton
  exact nonempty_mulEquiv_a5WrTwo (L := φ.range) (MonoidHom.ofInjective hφinj) hφindex hvnot hv2
    hswapφ

end CFSG.EvenSporadicStandard.HNRecog.Harada
