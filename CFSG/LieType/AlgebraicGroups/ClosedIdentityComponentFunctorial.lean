module

public import CFSG.LieType.AlgebraicGroups.CentralizerComponentInduction
import CFSG.Mathlib.GroupTheory.NormalizerTorsion

public noncomputable section
namespace CFSG.LieType.AlgebraicGroups
open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {τ : Tag} {k : Type} [Field k]

theorem finiteIndex_subgroupOf_of_finite_left_factor {Z E T : Subgroup (ModGL τ k)}
    [Finite E] (hEZ : E ≤ Z) (hZ : ∀ z ∈ Z, ∃ e ∈ E, ∃ t ∈ T, z = e * t) :
    (T.subgroupOf Z).FiniteIndex := by
  have hsurj : Function.Surjective (fun e : E =>
      (QuotientGroup.mk (⟨e, hEZ e.2⟩ : Z) : Z ⧸ T.subgroupOf Z)) := by
    intro q
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨e, he, t, ht, hzt⟩ := hZ z z.2
    have heZ : e ∈ Z := hEZ he
    refine ⟨⟨e, he⟩, ?_⟩
    apply QuotientGroup.eq.mpr
    change e⁻¹ * (z : ModGL τ k) ∈ T
    rw [hzt, inv_mul_cancel_left]
    exact ht
  have : Finite (Z ⧸ T.subgroupOf Z) := Finite.of_surjective _ hsurj
  exact Subgroup.finiteIndex_of_finite_quotient

theorem closedIdentityComponent_inf_eq_of_le
    (G T : Subgroup (ModGL τ k)) (hG : closedIdentityComponent G ≤ T) :
    closedIdentityComponent (G ⊓ T) = closedIdentityComponent G := by
  apply le_antisymm (closedIdentityComponent_mono inf_le_left)
  exact subset_closedIdentityComponent (le_inf (closedIdentityComponent_le G) hG)
    (closedIdentityComponent G).one_mem (isPointIrreducible_closedIdentityComponent G)

theorem closedIdentityComponent_le_of_isPointClosed_finiteIndex
    {Z T : Subgroup (ModGL τ k)}
    (hT : IsPointClosed k (transportPoints (modGLPoint τ k) (T : Set (ModGL τ k))))
    [(T.subgroupOf Z).FiniteIndex] : closedIdentityComponent Z ≤ T := by
  let e := modGLZariski τ k
  let Z' := Z.map e.toMonoidHom
  let T' := T.map e.toMonoidHom
  have hTc : IsClosed (T' : Set (SeminaireExp3.ZariskiGL (Label τ) k)) := by
    rw [isPointClosed_iff_isClosed_image] at hT
    exact hT
  let f := e.toMonoidHom.subgroupMap Z
  have hf : Function.Surjective f := e.toMonoidHom.subgroupMap_surjective Z
  have hK : ((T.subgroupOf Z).map f) = T'.subgroupOf Z' := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact mem_map_of_mem e.toMonoidHom hz
    · intro hx
      obtain ⟨z, rfl⟩ := hf x
      have hzT : (z : ModGL τ k) ∈ T := by
        change e (z : ModGL τ k) ∈ T.map e.toMonoidHom at hx
        simpa only [MulEquiv.symm_apply_apply] using (Subgroup.mem_map_equiv).mp hx
      exact ⟨z, hzT, rfl⟩
  have : (T'.subgroupOf Z').FiniteIndex := hK ▸ Subgroup.FiniteIndex.map_of_surjective (T.subgroupOf Z) hf
  have hle : SeminaireExp3.ZariskiGL.identityComponent Z' ≤ T' :=
    SeminaireExp3.ZariskiGL.identityComponent_le_of_isClosed hTc
  intro g hg
  have h : e g ∈ T' := hle (mem_closedIdentityComponent.mp hg)
  simpa only [MulEquiv.symm_apply_apply] using (Subgroup.mem_map_equiv).mp h

theorem isPointIrreducible_map_conj {S : Subgroup (ModGL τ k)}
    (hS : IsPointIrreducible k (transportPoints (modGLPoint τ k) (S : Set (ModGL τ k))))
    (g : ModGL τ k) :
    IsPointIrreducible k (transportPoints (modGLPoint τ k)
      (S.map (MulAut.conj g).toMonoidHom : Set (ModGL τ k))) := by
  rw [isPointIrreducible_iff_isIrreducible_image] at hS ⊢
  have h := hS.image (fun x => modGLZariski τ k g * x * (modGLZariski τ k g)⁻¹)
    ((continuous_mul_const _).comp (continuous_const_mul _)).continuousOn
  convert h using 1
  ext x
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    refine ⟨modGLZariski τ k z, ⟨z, hz, rfl⟩, ?_⟩
    change modGLZariski τ k g * modGLZariski τ k z * (modGLZariski τ k g)⁻¹ =
      modGLZariski τ k (g * z * g⁻¹)
    rw [map_mul, map_mul, map_inv]
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨(MulAut.conj g) z, mem_map_of_mem _ hz, by rw [MulAut.conj_apply, map_mul, map_mul, map_inv]⟩

theorem closedIdentityComponent_map_conj_le (Z : Subgroup (ModGL τ k))
    (g : ModGL τ k) :
    (closedIdentityComponent Z).map (MulAut.conj g).toMonoidHom ≤
      closedIdentityComponent (Z.map (MulAut.conj g).toMonoidHom) :=
  subset_closedIdentityComponent (Subgroup.map_mono (closedIdentityComponent_le Z))
    (Subgroup.one_mem _) (isPointIrreducible_map_conj
      (isPointIrreducible_closedIdentityComponent Z) g)

theorem closedIdentityComponent_map_conj (Z : Subgroup (ModGL τ k))
    (g : ModGL τ k) :
    closedIdentityComponent (Z.map (MulAut.conj g).toMonoidHom) =
      (closedIdentityComponent Z).map (MulAut.conj g).toMonoidHom := by
  refine le_antisymm ?_ (closedIdentityComponent_map_conj_le Z g)
  have h := closedIdentityComponent_map_conj_le
    (Z.map (MulAut.conj g).toMonoidHom) g⁻¹
  have hc : ((MulAut.conj g⁻¹).toMonoidHom).comp (MulAut.conj g).toMonoidHom =
      MonoidHom.id (ModGL τ k) := by
    apply MonoidHom.ext
    intro x
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  rw [Subgroup.map_map, hc, Subgroup.map_id] at h
  intro x hx
  have hm : g⁻¹ * x * g ∈ closedIdentityComponent Z :=
    h (mem_map_of_mem (MulAut.conj g⁻¹).toMonoidHom hx)
  exact ⟨g⁻¹ * x * g, hm, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩

theorem closedIdentityComponent_hyperplane_centralizer_eq
    (G E H : Subgroup (ModGL τ k)) (e : ModGL τ k)
    (hE : E = H ⊔ Subgroup.zpowers e) :
    closedIdentityComponent (closedIdentityComponent (G ⊓ Subgroup.centralizer (H : Set (ModGL τ k))) ⊓
      Subgroup.centralizer {e}) =
        closedIdentityComponent (G ⊓ Subgroup.centralizer (E : Set (ModGL τ k))) := by
  rw [← closedIdentityComponent_inf_centralizer_eq]
  congr 1
  have hCE : Subgroup.centralizer (E : Set (ModGL τ k)) =
      Subgroup.centralizer (H : Set (ModGL τ k)) ⊓ Subgroup.centralizer {e} := by
    apply le_antisymm
    · apply le_inf
      · apply Subgroup.centralizer_le
        intro h hh
        rw [hE]
        exact (le_sup_left : H ≤ H ⊔ Subgroup.zpowers e) hh
      · exact Subgroup.centralizer_le (by
          intro y hy
          rw [Set.mem_singleton_iff] at hy
          subst y
          rw [hE]
          exact mem_sup_right (Subgroup.mem_zpowers e))
    · intro x hx
      rw [Subgroup.mem_centralizer_iff]
      have hHX : H ≤ Subgroup.centralizer {x} := by
        intro h hh
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact Subgroup.mem_centralizer_iff.mp hx.1 h hh
      have heX : Subgroup.zpowers e ≤ Subgroup.centralizer {x} := by
        apply (Subgroup.zpowers_le).mpr
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_singleton_iff.mp hx.2).symm
      have heall : E ≤ Subgroup.centralizer {x} := by rw [hE]; exact sup_le hHX heX
      intro y hy
      exact Subgroup.mem_centralizer_singleton_iff.mp (heall hy)
  rw [hCE, inf_assoc]

theorem map_adjoint_centralizer_conj (E : Subgroup (ModGL τ k))
    {g : ModGL τ k} (hg : g ∈ adjointGroup τ k) :
    (adjointGroup τ k ⊓ centralizer (E : Set (ModGL τ k))).map (MulAut.conj g).toMonoidHom =
      adjointGroup τ k ⊓ centralizer
        (E.map (MulAut.conj g).toMonoidHom : Set (ModGL τ k)) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨(adjointGroup τ k).mul_mem ((adjointGroup τ k).mul_mem hg hy.1)
      ((adjointGroup τ k).inv_mem hg), ?_⟩
    change g * y * g⁻¹ ∈ centralizer (E.map (MulAut.conj g).toMonoidHom : Set (ModGL τ k))
    rw [mem_centralizer_iff]
    rintro z ⟨e, he, rfl⟩
    have hye := mem_centralizer_iff.mp hy.2 e he
    change (g * e * g⁻¹) * (g * y * g⁻¹) = (g * y * g⁻¹) * (g * e * g⁻¹)
    calc _ = g * (e * y) * g⁻¹ := by group
      _ = g * (y * e) * g⁻¹ := by rw [hye]
      _ = _ := by group
  · rintro ⟨hxG, hxE⟩
    refine ⟨g⁻¹ * x * g, ⟨(adjointGroup τ k).mul_mem
      ((adjointGroup τ k).mul_mem ((adjointGroup τ k).inv_mem hg) hxG) hg, ?_⟩, ?_⟩
    · change g⁻¹ * x * g ∈ centralizer (E : Set (ModGL τ k))
      rw [mem_centralizer_iff]
      intro e he
      have h := mem_centralizer_iff.mp hxE ((MulAut.conj g) e) (mem_map_of_mem _ he)
      change (g * e * g⁻¹) * x = x * (g * e * g⁻¹) at h
      calc _ = g⁻¹ * ((g * e * g⁻¹) * x) * g := by group
        _ = g⁻¹ * (x * (g * e * g⁻¹)) * g := by rw [h]
        _ = _ := by group
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group


theorem mem_normalizer_connected_adjoint_centralizer
    (E : Subgroup (ModGL τ k)) {g : ModGL τ k}
    (hg : g ∈ adjointGroup τ k) (hgE : g ∈ normalizer (E : Set (ModGL τ k))) :
    g ∈ normalizer (closedIdentityComponent
      (adjointGroup τ k ⊓ centralizer (E : Set (ModGL τ k))) : Set (ModGL τ k)) := by
  have hmap := map_adjoint_centralizer_conj E hg
  change (adjointGroup τ k ⊓ centralizer (E : Set (ModGL τ k))).map (MulAut.conj g) =
      adjointGroup τ k ⊓ centralizer
        ((E.map (MulAut.conj g) : Subgroup (ModGL τ k)) : Set (ModGL τ k)) at hmap
  rw [mem_normalizer_iff_map_conj_eq.mp hgE] at hmap
  apply normalizer_le_normalizer_closedIdentityComponent
  exact mem_normalizer_iff_map_conj_eq.mpr hmap

theorem normalizer_inf_connected_hyperplane_centralizer_eq
    (E H : Subgroup (ModGL τ k)) (e : ModGL τ k)
    (hE : E = H ⊔ zpowers e)
    (heS : e ∈ closedIdentityComponent
      (adjointGroup τ k ⊓ centralizer (E : Set (ModGL τ k))))
    {m : ℕ} (hem : e ^ m = 1)
    (hSm : ∀ x ∈ closedIdentityComponent
      (adjointGroup τ k ⊓ centralizer (E : Set (ModGL τ k))), x ^ m = 1 → x ∈ E) :
    normalizer (closedIdentityComponent
      (adjointGroup τ k ⊓ centralizer (E : Set (ModGL τ k))) : Set (ModGL τ k)) ⊓
      closedIdentityComponent (adjointGroup τ k ⊓ centralizer (H : Set (ModGL τ k))) =
    normalizer (E : Set (ModGL τ k)) ⊓
      closedIdentityComponent (adjointGroup τ k ⊓ centralizer (H : Set (ModGL τ k))) := by
  apply le_antisymm
  · intro g hg
    exact ⟨mem_normalizer_of_eq_sup_zpowers_of_torsion E H _ e hE heS hem hSm hg.1
      (closedIdentityComponent_le _ hg.2).2, hg.2⟩
  · intro g hg
    exact ⟨mem_normalizer_connected_adjoint_centralizer E
      (closedIdentityComponent_le _ hg.2).1 hg.1, hg.2⟩

theorem closedIdentityComponent_normalizer_inf_le_centralizer
    (E K : Subgroup (ModGL τ k)) [Finite E] :
    closedIdentityComponent (normalizer (E : Set (ModGL τ k)) ⊓ K) ≤
      centralizer (E : Set (ModGL τ k)) := by
  have : Finite E.normalizerMonoidHom.range := inferInstance
  have : ((centralizer (E : Set (ModGL τ k))).subgroupOf
      (normalizer (E : Set (ModGL τ k)))).FiniteIndex := by
    rw [← normalizerMonoidHom_ker]
    exact finiteIndex_ker E.normalizerMonoidHom
  have : (centralizer (E : Set (ModGL τ k))).IsFiniteRelIndex
      (normalizer (E : Set (ModGL τ k))) :=
    isFiniteRelIndex_iff_finiteIndex.mpr inferInstance
  have : (centralizer (E : Set (ModGL τ k))).IsFiniteRelIndex
      (normalizer (E : Set (ModGL τ k)) ⊓ K) :=
    isFiniteRelIndex_of_le_right _ inf_le_left
  have : ((centralizer (E : Set (ModGL τ k))).subgroupOf
      (normalizer (E : Set (ModGL τ k)) ⊓ K)).FiniteIndex := inferInstance
  exact closedIdentityComponent_le_of_isPointClosed_finiteIndex
    (isPointClosed_centralizer (E : Set (ModGL τ k)))

theorem closedIdentityComponent_normalizer_inf_hyperplane_eq
    (G E H : Subgroup (ModGL τ k)) [Finite E] (hHE : H ≤ E) :
    closedIdentityComponent (normalizer (E : Set (ModGL τ k)) ⊓
      closedIdentityComponent (G ⊓ centralizer (H : Set (ModGL τ k)))) =
    closedIdentityComponent (G ⊓ centralizer (E : Set (ModGL τ k))) := by
  let K := closedIdentityComponent (G ⊓ centralizer (H : Set (ModGL τ k)))
  let N := normalizer (E : Set (ModGL τ k)) ⊓ K
  let S := closedIdentityComponent (G ⊓ centralizer (E : Set (ModGL τ k)))
  apply le_antisymm
  · have hNC := closedIdentityComponent_normalizer_inf_le_centralizer E K
    have hNG : closedIdentityComponent N ≤ G :=
      (closedIdentityComponent_le N).trans
        (inf_le_right.trans ((closedIdentityComponent_le _).trans inf_le_left))
    exact subset_closedIdentityComponent (le_inf hNG hNC) (Subgroup.one_mem _)
      (isPointIrreducible_closedIdentityComponent _)
  · have hSC : S ≤ centralizer (E : Set (ModGL τ k)) :=
      (closedIdentityComponent_le _).trans inf_le_right
    have hSK : S ≤ K := closedIdentityComponent_mono
      (inf_le_inf_left G (centralizer_le hHE))
    exact subset_closedIdentityComponent
      (le_inf (hSC.trans (centralizer_le_normalizer _)) hSK) (Subgroup.one_mem _)
        (isPointIrreducible_closedIdentityComponent _)

theorem closedIdentityComponent_torus_normalizer_inf_hyperplane_eq
    (E H : Subgroup (ModGL τ k)) [Finite E] (e : ModGL τ k)
    (hE : E = H ⊔ zpowers e)
    (heS : e ∈ closedIdentityComponent
      (adjointGroup τ k ⊓ centralizer (E : Set (ModGL τ k))))
    {m : ℕ} (hem : e ^ m = 1)
    (hSm : ∀ x ∈ closedIdentityComponent
      (adjointGroup τ k ⊓ centralizer (E : Set (ModGL τ k))), x ^ m = 1 → x ∈ E) :
    closedIdentityComponent (normalizer (closedIdentityComponent
      (adjointGroup τ k ⊓ centralizer (E : Set (ModGL τ k))) : Set (ModGL τ k)) ⊓
      closedIdentityComponent (adjointGroup τ k ⊓ centralizer (H : Set (ModGL τ k)))) =
    closedIdentityComponent (adjointGroup τ k ⊓ centralizer (E : Set (ModGL τ k))) := by
  rw [normalizer_inf_connected_hyperplane_centralizer_eq E H e hE heS hem hSm]
  exact closedIdentityComponent_normalizer_inf_hyperplane_eq _ _ _
    (by rw [hE]; exact le_sup_left)

theorem closedIdentityComponent_self_centralizer_eq_of_hyperplane
    (G E H : Subgroup (ModGL τ k)) (e : ModGL τ k)
    (hE : E = H ⊔ zpowers e)
    (heS : e ∈ closedIdentityComponent (G ⊓ centralizer (E : Set (ModGL τ k))))
    (hcomm : ∀ x ∈ closedIdentityComponent (G ⊓ centralizer (E : Set (ModGL τ k))),
      ∀ y ∈ closedIdentityComponent (G ⊓ centralizer (E : Set (ModGL τ k))), x * y = y * x) :
    let K := closedIdentityComponent (G ⊓ centralizer (H : Set (ModGL τ k)))
    let S := closedIdentityComponent (G ⊓ centralizer (E : Set (ModGL τ k)))
    closedIdentityComponent (K ⊓ centralizer (S : Set (ModGL τ k))) = S := by
  let K := closedIdentityComponent (G ⊓ centralizer (H : Set (ModGL τ k)))
  let S := closedIdentityComponent (G ⊓ centralizer (E : Set (ModGL τ k)))
  have hHE : H ≤ E := by rw [hE]; exact le_sup_left
  have hSK : S ≤ K := closedIdentityComponent_mono
    (inf_le_inf_left G (centralizer_le hHE))
  have hSC : S ≤ centralizer (S : Set (ModGL τ k)) := by
    intro x hx
    rw [mem_centralizer_iff]
    intro y hy
    exact hcomm y hy x hx
  apply le_antisymm
  · have hle : K ⊓ centralizer (S : Set (ModGL τ k)) ≤ K ⊓ centralizer {e} :=
      inf_le_inf_left _ (centralizer_le (Set.singleton_subset_iff.mpr heS))
    have h := closedIdentityComponent_mono hle
    rw [closedIdentityComponent_hyperplane_centralizer_eq G E H e hE] at h
    exact h
  · exact subset_closedIdentityComponent (le_inf hSK hSC) (Subgroup.one_mem _)
      (isPointIrreducible_closedIdentityComponent _)

end CFSG.LieType.AlgebraicGroups
