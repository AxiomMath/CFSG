module

public import CFSG.LieType.Chevalley.LangFrobeniusFixedDerived
public import CFSG.LieType.Chevalley.LangFiniteRootCentralizer
public import CFSG.GroupTheory.LangNormOneDescent

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.GroupTheory

theorem map_baseChangeGL_adjointGroup_le
    {τ : Tag} {K L : Type} [Field K] [Field L]
    (f : K →+* L) : (adjointGroup τ K).map (baseChangeGL f) ≤ adjointGroup τ L := by
  rintro _ ⟨g, hg, rfl⟩
  exact baseChangeGL_mem_adjointGroup f hg

variable (τ : Tag) (K L : Type) [Field K] [Field L] [Algebra K L]

abbrev langRationalImage :
    Subgroup (adjointGroup τ L) :=
  ((adjointGroup τ K).map (baseChangeGL (algebraMap K L))).subgroupOf (adjointGroup τ L)

variable {τ K L}

theorem mem_langRationalImage
    {g : adjointGroup τ L} :
    g ∈ langRationalImage τ K L ↔
      (g : ModGL τ L) ∈ (adjointGroup τ K).map (baseChangeGL (algebraMap K L)) :=
  Subgroup.mem_subgroupOf

theorem entrywise_frobenius_langRationalImage
    [Finite K] (Fr : L →+* L)
    (hFr : ∀ c, Fr c = c ^ Nat.card K) (u : langRationalImage τ K L) :
    Units.map (entrywiseHom Fr) ((u : adjointGroup τ L) : ModGL τ L) = u := by
  obtain ⟨g, -, hg⟩ := mem_langRationalImage.1 u.2
  rw [← hg]
  exact units_map_entrywiseHom_baseChangeGL_algebraMap Fr hFr g

theorem exceptional_Lang_actual_involution_conjugacy_reduction
    [Finite K]
    (hK : Odd (Nat.card K)) [IsAlgClosure K L] (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (S : MulAut (adjointGroup τ L))
    (hSH : (langRationalImage τ K L).map S.toMonoidHom = langRationalImage τ K L)
    (hS2 : ∀ g : adjointGroup τ L,
      ((S (S g) : adjointGroup τ L) : ModGL τ L) = Units.map (entrywiseHom Fr) (g : ModGL τ L))
    (hLang : ∀ y : adjointGroup τ L, ∃ h : adjointGroup τ L, y = h⁻¹ * S h)
    (x : adjointGroup τ L)
    (hx : x ∈ Subgroup.normalizer (langRationalImage τ K L : Set (adjointGroup τ L))) :
    (∃ α : MulAut (langRationalImage τ K L), ∀ u, (α u : adjointGroup τ L) = x * S u * x⁻¹) ∧
    ∀ α : MulAut (langRationalImage τ K L), (∀ u, (α u : adjointGroup τ L) = x * S u * x⁻¹) →
      α * α = 1 →
      ∃ h : adjointGroup τ L, Units.map (entrywiseHom Fr) (h : ModGL τ L) = h ∧
        ∃ ψ : MulAut (langRationalImage τ K L), (∀ u, (ψ u : adjointGroup τ L) = h * u * h⁻¹) ∧
          (∀ u, ((ψ * α * ψ⁻¹) u : adjointGroup τ L) = S u) ∧
          (α.toMonoidHom.eqLocus (MonoidHom.id _)).map ψ.toMonoidHom =
            (S.toMonoidHom.comp (langRationalImage τ K L).subtype).eqLocus
              (langRationalImage τ K L).subtype ∧
          ∃ e : ↥(α.toMonoidHom.eqLocus (MonoidHom.id _)) ≃*
              ↥((S.toMonoidHom.comp (langRationalImage τ K L).subtype).eqLocus
                (langRationalImage τ K L).subtype),
            ∀ u, (e u : langRationalImage τ K L) = ψ u := by
  set H := langRationalImage τ K L with hHdef
  have hSS : ∀ u : H, S (S u) = u := fun u =>
    Subtype.ext ((hS2 u).trans (entrywise_frobenius_langRationalImage Fr hFr u))
  have hαmap : H.map (MulAut.conj x * S).toMonoidHom = H := by
    rw [map_toMonoidHom_mul_mulAut, hSH]
    exact map_conj_eq_of_mem_normalizer hx
  refine ⟨⟨mulAutRestrict H (MulAut.conj x * S) hαmap, fun u => ?_⟩, fun α hα hα2 => ?_⟩
  · rw [coe_mulAutRestrict, MulAut.mul_apply, MulAut.conj_apply]
  have hcomm : ∀ u : H, x * S x * u = u * (x * S x) := by
    intro u
    have h1 : (α (α u) : adjointGroup τ L) = u := by
      rw [← MulAut.mul_apply, hα2, MulAut.one_apply]
    rw [hα, hα u, map_mul, map_mul, map_inv, hSS u] at h1
    calc x * S x * u = (x * (S x * u * (S x)⁻¹) * x⁻¹) * (x * S x) := by group
      _ = u * (x * S x) := by rw [h1]
  have hz : x * S x = 1 := by
    obtain ⟨-, -, hC, -⟩ :=
      exceptional_Lang_finite_root_centralizer_faithfulness τ K hK L (algebraMap K L)
    refine Subtype.ext (hC _ (x * S x).2 fun g hg => ?_)
    have := hcomm ⟨⟨g, map_baseChangeGL_adjointGroup_le _ hg⟩, mem_langRationalImage.2 hg⟩
    exact congrArg Subtype.val this
  obtain ⟨h, hhR, hxh, -⟩ := exceptional_Lang_norm_one_descent S.toMonoidHom (m := 2)
    (by norm_num) hLang x (by simpa [List.range_succ] using hz)
  have hSh : S (S h) = h := hhR
  have hhF : Units.map (entrywiseHom Fr) (h : ModGL τ L) = h := by
    rw [← hS2, hSh]
  obtain ⟨-, -, hRN, -⟩ :=
    exceptional_Lang_Frobenius_fixed_derived_root_group τ K hK L Fr hFr
  have hhN₀ := hRN ⟨h.2, hhF⟩
  have hhN : h ∈ Subgroup.normalizer (H : Set (adjointGroup τ L)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro g
    rw [hHdef, mem_langRationalImage, mem_langRationalImage]
    exact Subgroup.mem_normalizer_iff.1 hhN₀ g
  set ψ : MulAut H := mulAutRestrict H (MulAut.conj h) (map_conj_eq_of_mem_normalizer hhN)
    with hψdef
  have hψ : ∀ u : H, (ψ u : adjointGroup τ L) = h * u * h⁻¹ := fun u => by
    rw [hψdef, coe_mulAutRestrict, MulAut.conj_apply]
  have hψinv : ∀ u : H, (ψ⁻¹ u : adjointGroup τ L) = h⁻¹ * u * h := fun u => by
    have h1 : (ψ (ψ⁻¹ u) : adjointGroup τ L) = u := by
      rw [MulAut.apply_inv_self]
    rw [hψ] at h1
    rw [← h1]
    group
  have hconj : ∀ u : H, ((ψ * α * ψ⁻¹) u : adjointGroup τ L) = S u := by
    intro u
    rw [MulAut.mul_apply, MulAut.mul_apply, hψ, hα, hψinv, map_mul, map_mul, map_inv, hxh]
    change h * (h⁻¹ * S h * ((S h)⁻¹ * S u * S h) * (h⁻¹ * S h)⁻¹) * h⁻¹ = S u
    group
  have hmap : (α.toMonoidHom.eqLocus (MonoidHom.id _)).map ψ.toMonoidHom =
      (S.toMonoidHom.comp H.subtype).eqLocus H.subtype := by
    ext w
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨u, hu, rfl⟩
      have hu' : α u = u := hu
      have h1 := hconj (ψ u)
      rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self, hu'] at h1
      exact h1.symm
    · intro hw
      have hw' : S (w : adjointGroup τ L) = w := hw
      refine ⟨ψ⁻¹ w, ?_, MulAut.apply_inv_self _ ψ w⟩
      have h1 : (ψ * α * ψ⁻¹) w = w := Subtype.ext ((hconj w).trans hw')
      rw [MulAut.mul_apply, MulAut.mul_apply] at h1
      have h2 : ψ⁻¹ (ψ (α (ψ⁻¹ w))) = ψ⁻¹ w := by rw [h1]
      rwa [MulAut.inv_apply_self] at h2
  refine ⟨h, hhF, ψ, hψ, hconj, hmap,
    ((α.toMonoidHom.eqLocus (MonoidHom.id _)).equivMapOfInjective ψ.toMonoidHom
      ψ.injective).trans (MulEquiv.subgroupCongr hmap), fun u => rfl⟩

end CFSG.LieType.Chevalley
