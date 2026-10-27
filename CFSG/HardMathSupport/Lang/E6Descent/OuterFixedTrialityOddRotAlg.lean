module

public import CFSG.LieType.AlgebraicGroups.ConnectedToralLangFrobenius
public import CFSG.LieType.AlgebraicGroups.E6GraphCentralizerLangCurves
public import CFSG.LieType.AlgebraicGroups.E6GraphCentralizerLangWords
import CFSG.LieType.AlgebraicGroups.ConvolutionPoints

public noncomputable section

namespace CFSG.HardMathSupport.Lang.E6Descent

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups WithConv

open scoped CFSG.ConvolutionPoints

section Closure

variable {k : Type} [Field k] [IsAlgClosed k] {A : Type} [CommRing A] [HopfAlgebra k A]
  [Algebra.FiniteType k A]

theorem isPointIrreducible_closureSubgroup (H : Subgroup (WithConv (A →ₐ[k] k)))
    (hirr : IsPointIrreducible k (subgroupPoints H)) :
    IsPointIrreducible k (subgroupPoints (closureSubgroup H)) := by
  have hprime : (subgroupIdeal H).IsPrime :=
    PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime.1 hirr
  unfold IsPointIrreducible
  rw [PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime]
  have h : pointsIdeal (pointsZero k (subgroupIdeal H)) = subgroupIdeal H :=
    pointsIdeal_pointsZero_of_isRadical (isRadical_pointsIdeal _)
  have h' : PrimeSpectrum.vanishingIdeal (pointSpec '' subgroupPoints (closureSubgroup H)) =
      subgroupIdeal H := h
  rw [h']
  exact hprime

theorem isConnectedAlgebraicSubgroup_closureSubgroup (H : Subgroup (WithConv (A →ₐ[k] k)))
    (hirr : IsPointIrreducible k (subgroupPoints H)) :
    IsConnectedAlgebraicSubgroup k (closureSubgroup H) := by
  have hirr' := isPointIrreducible_closureSubgroup H hirr
  have hclosed : IsPointClosed k (subgroupPoints (closureSubgroup H)) := by
    refine ⟨closure (pointSpec '' subgroupPoints H), isClosed_closure, ?_⟩
    exact pointsZero_pointsIdeal (subgroupPoints H)
  exact isConnectedAlgebraicSubgroup _ hclosed.isPointConstructible hirr'

theorem closureSubgroup_le_of_isPointClosed (H Zp : Subgroup (WithConv (A →ₐ[k] k)))
    (hZ : IsPointClosed k (subgroupPoints Zp)) (hHZ : H ≤ Zp) : closureSubgroup H ≤ Zp := by
  obtain ⟨Zc, hZc, hZeq⟩ := hZ
  intro y hy
  have h1 : pointSpec y.ofConv ∈ closure (pointSpec '' subgroupPoints H) := by
    have : y.ofConv ∈ pointsZero k (pointsIdeal (subgroupPoints H)) := hy
    rw [pointsZero_pointsIdeal] at this
    exact this
  have h2 : pointSpec '' subgroupPoints H ⊆ Zc := by
    rintro _ ⟨x, hx, rfl⟩
    have : x ∈ subgroupPoints Zp := hHZ hx
    rw [hZeq] at this
    exact this
  have h3 := hZc.closure_subset_iff.2 h2 h1
  have : y.ofConv ∈ subgroupPoints Zp := by
    rw [hZeq]
    exact h3
  exact this

end Closure

section Lang

variable {τ : Tag} {k : Type} [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p]

theorem exists_frobTwist_of_isPointIrreducible {Z R : Subgroup (ModGL τ k)}
    (hZ : IsPointClosed k (transportPoints (modGLPoint τ k) (Z : Set (ModGL τ k))))
    (hRZ : R ≤ Z)
    (hirr : IsPointIrreducible k (transportPoints (modGLPoint τ k) (R : Set (ModGL τ k))))
    {e : ℕ} (he : 1 ≤ e) (Q : ModGL τ k)
    (hRF : ∀ g ∈ R, frobTwistGL τ k p e Q g ∈ R) :
    ∀ c ∈ R, ∃ z ∈ Z, z⁻¹ * frobTwistGL τ k p e Q z = c := by
  set E := (modGLPoint τ k) with hE
  set Rp : Subgroup (WithConv (GLCoord k (Label τ) →ₐ[k] k)) := R.map E.toMonoidHom with hRp
  set Hb := closureSubgroup Rp with hHb
  have hRpts : subgroupPoints Rp = transportPoints E (R : Set (ModGL τ k)) :=
    subgroupPoints_map E R
  have hconn : IsConnectedAlgebraicSubgroup k Hb :=
    isConnectedAlgebraicSubgroup_closureSubgroup Rp (by rw [hRpts]; exact hirr)
  set Zb : Subgroup (ModGL τ k) := Hb.comap E.toMonoidHom with hZb
  have hZbmap : Zb.map E.toMonoidHom = Hb :=
    Subgroup.map_comap_eq_self_of_surjective E.surjective _
  have hmemZb : ∀ g : ModGL τ k, g ∈ Zb ↔ (E g).ofConv ∈ pointsZero k (subgroupIdeal Rp) :=
    fun g => Iff.rfl
  have hco : ∀ (g : ModGL τ k) (a : GLCoord k (Label τ)),
      (E g).ofConv (frobTwistCoGL p e Q a) = (E (frobTwistGL τ k p e Q g)).ofConv a := by
    intro g a
    have h := modGLPoint_symm_comp_frobTwistCoGL p e Q (E g).ofConv
    rw [toConv_ofConv, MulEquiv.symm_apply_apply] at h
    have h2 : E (frobTwistGL τ k p e Q g) = toConv ((E g).ofConv.comp (frobTwistCoGL p e Q)) := by
      rw [← h, hE, MulEquiv.apply_symm_apply]
    rw [h2, ofConv_toConv]
    rfl
  have hQ : ∀ g ∈ Zb, frobTwistGL τ k p e Q g ∈ Zb := by
    intro g hg a ha
    show (E (frobTwistGL τ k p e Q g)).ofConv a = 0
    rw [← hco]
    refine hg _ (mem_subgroupIdeal.2 fun y hy => ?_)
    obtain ⟨r, hr, rfl⟩ := hy
    show (E r).ofConv (frobTwistCoGL p e Q a) = 0
    rw [hco]
    exact mem_subgroupIdeal.1 ha _ ⟨_, hRF r hr, rfl⟩
  have hconn' : IsConnectedAlgebraicSubgroup k (Zb.map E.toMonoidHom) := by
    rw [hZbmap]; exact hconn
  obtain ⟨_, -, -, hlang⟩ := exists_frobTwist_restriction p hconn' he Q hQ
  have hRZb : R ≤ Zb := by
    intro g hg
    exact le_closureSubgroup Rp ⟨g, hg, rfl⟩
  have hZbZ : Zb ≤ Z := by
    have hZp : IsPointClosed k (subgroupPoints (Z.map E.toMonoidHom)) := by
      rw [subgroupPoints_map]; exact hZ
    have h1 : Hb ≤ Z.map E.toMonoidHom :=
      closureSubgroup_le_of_isPointClosed Rp _ hZp (Subgroup.map_mono hRZ)
    intro g hg
    obtain ⟨g', hg', hgg'⟩ := h1 hg
    have : g' = g := E.injective hgg'
    rwa [← this]
  intro c hc
  obtain ⟨z, hz, hzc⟩ := hlang c (hRZb hc)
  exact ⟨z, hZbZ hz, hzc⟩

end Lang

section Curves

variable {τ : Tag} {k : Type} [Field k] [IsAlgClosed k]

open WordCurve in
theorem isPointIrreducible_closure_wordCurves
    {ι : Type}
    (F : ι → WordCurve τ k) (hinvF : ∀ i, ∀ g ∈ (F i).values, g⁻¹ ∈ (F i).values) :
    IsPointIrreducible k (transportPoints (modGLPoint τ k)
      ((Subgroup.closure (⋃ i, (F i).values) : Subgroup (ModGL τ k)) : Set (ModGL τ k))) := by
  have hone : ∀ l, (1 : ModGL τ k) ∈ (listProd F l).values := fun l => one_mem_values _
  have hsub : ∀ l, (listProd F l).values ⊆
      ((Subgroup.closure (⋃ i, (F i).values) : Subgroup (ModGL τ k)) : Set (ModGL τ k)) := by
    intro l
    induction l with
    | nil =>
      intro g hg
      rw [values_listProd_nil, Set.mem_singleton_iff] at hg
      rw [hg]
      exact one_mem _
    | cons i l ih =>
      intro g hg
      rw [values_listProd_cons] at hg
      obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.1 hg
      exact mul_mem (Subgroup.subset_closure (Set.mem_iUnion.2 ⟨i, ha⟩)) (ih hb)
  have hinv : ∀ l, ∀ g ∈ (listProd F l).values, g⁻¹ ∈ (listProd F l.reverse).values := by
    intro l
    induction l with
    | nil =>
      intro g hg
      rw [values_listProd_nil, Set.mem_singleton_iff] at hg
      rw [hg, inv_one]
      exact hone _
    | cons i l ih =>
      intro g hg
      rw [values_listProd_cons] at hg
      obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.1 hg
      rw [mul_inv_rev, List.reverse_cons, values_listProd_append, values_listProd_singleton]
      exact Set.mem_mul.2 ⟨b⁻¹, ih b hb, a⁻¹, hinvF i a ha, rfl⟩
  let U : Subgroup (ModGL τ k) :=
    { carrier := ⋃ l, (listProd F l).values
      mul_mem' := by
        intro a b ha hb
        obtain ⟨l₁, ha⟩ := Set.mem_iUnion.1 ha
        obtain ⟨l₂, hb⟩ := Set.mem_iUnion.1 hb
        refine Set.mem_iUnion.2 ⟨l₁ ++ l₂, ?_⟩
        rw [values_listProd_append]
        exact Set.mem_mul.2 ⟨a, ha, b, hb, rfl⟩
      one_mem' := Set.mem_iUnion.2 ⟨[], hone []⟩
      inv_mem' := by
        intro a ha
        obtain ⟨l, ha⟩ := Set.mem_iUnion.1 ha
        exact Set.mem_iUnion.2 ⟨l.reverse, hinv l a ha⟩ }
  have hU : ((Subgroup.closure (⋃ i, (F i).values) : Subgroup (ModGL τ k)) : Set (ModGL τ k)) =
      ⋃ l, (listProd F l).values := by
    refine le_antisymm ?_ (Set.iUnion_subset hsub)
    have hle : Subgroup.closure (⋃ i, (F i).values) ≤ U := by
      rw [Subgroup.closure_le]
      refine Set.iUnion_subset fun i g hg => ?_
      refine Set.mem_iUnion.2 ⟨[i], ?_⟩
      rw [values_listProd_singleton]
      exact hg
    exact hle
  rw [hU, transportPoints, Set.image_iUnion]
  have : Nonempty (List ι) := ⟨[]⟩
  refine isPointIrreducible_iUnion_of_directed _ (fun l => ?_) fun l₁ l₂ => ⟨l₁ ++ l₂, ?_, ?_⟩
  · have h : (fun g : ModGL τ k => (modGLPoint τ k g).ofConv) '' (listProd F l).values =
        Set.range fun z : (listProd F l).D →ₐ[k] k =>
          z.comp (unitCo k (wordUnit τ _ (listProd F l).word)) := by
      ext y
      constructor
      · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
        exact ⟨z, comp_unitCo_wordUnit z _⟩
      · rintro ⟨z, rfl⟩
        exact ⟨_, ⟨z, rfl⟩, (comp_unitCo_wordUnit z _).symm⟩
    rw [h]
    exact isPointIrreducible_range_of_isDomain _
  · refine Set.image_mono fun g hg => ?_
    rw [values_listProd_append]
    exact Set.mem_mul.2 ⟨g, hg, 1, hone l₂, mul_one g⟩
  · refine Set.image_mono fun g hg => ?_
    rw [values_listProd_append]
    exact Set.mem_mul.2 ⟨1, hone l₁, g, hg, one_mul g⟩

end Curves

end CFSG.HardMathSupport.Lang.E6Descent
