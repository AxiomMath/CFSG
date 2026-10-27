module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeToralityProof
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeFactsWeyl

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.CentralExt.MinusculeClosed
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

set_option linter.unusedSectionVars false

section BC


theorem minBC_minBC_E6 {k k' k'' : Type} [Field k] [Field k'] [Field k''] (ι : k →+* k')
    (φ : k' →+* k'') (g : e6Data_valid.minGroup k) :
    minBC e6Data_valid φ (minBC e6Data_valid ι g) = minBC e6Data_valid (φ.comp ι) g := by
  apply Subtype.ext
  apply Units.ext
  simp only [minBC, MonoidHom.codRestrict_apply, MonoidHom.comp_apply, Subgroup.coe_subtype,
    coe_minUnitsBC]
  refine minEnd_ext fun a => ?_
  rw [minEndBC_single, minEndBC_single, minEndBC_single]
  ext b
  simp

theorem minBC_minTorus_E6 {k k' : Type} [Field k] [Field k'] (φ : k →+* k')
    (u : Fin Tag.E6.rank → kˣ) :
    minBC e6Data_valid φ (minTorus e6Data_valid k u) =
      minTorus e6Data_valid k' (fun j => Units.map φ.toMonoidHom (u j)) := by
  induction u using CFSG.LieType.Chevalley.ExceptionalCover.torusVec_induction with
  | h1 =>
    have e : (fun j => Units.map φ.toMonoidHom ((1 : Fin Tag.E6.rank → kˣ) j)) = 1 := by
      funext j
      simp
    rw [map_one, map_one, e, map_one]
  | hmul t t' ht ht' =>
    have e : (fun j => Units.map φ.toMonoidHom ((t * t') j)) =
        (fun j => Units.map φ.toMonoidHom (t j)) * fun j => Units.map φ.toMonoidHom (t' j) := by
      funext j
      simp
    rw [map_mul, map_mul, ht, ht', e, map_mul]
  | hsingle a s =>
    have e : (fun j => Units.map φ.toMonoidHom ((Pi.mulSingle a s : Fin Tag.E6.rank → kˣ) j)) =
        Pi.mulSingle a (Units.map φ.toMonoidHom s) := by
      funext j
      by_cases hj : j = a
      · subst hj
        simp
      · simp [Pi.mulSingle_eq_of_ne hj]
    rw [e, minTorus_mulSingle, minTorus_mulSingle]
    simp only [MinData.Valid.hm, MinData.Valid.nt, map_mul, map_inv, minBC_xm_single,
      minBC_xm_neg_single]
    congr 1 <;> simp

end BC

section Center


theorem exists_minTorus_of_mem_center_E6 {k : Type} [Field k] {z : e6Data_valid.minGroup k}
    (hz : z ∈ Subgroup.center (e6Data_valid.minGroup k)) :
    ∃ u : Fin Tag.E6.rank → kˣ, z = minTorus e6Data_valid k u ∧ ∀ j, u j ^ 3 = 1 := by
  obtain ⟨u, rfl⟩ := center_le_range_minTorus e6Data_valid k isFiniteType_cartan_E6
    (e6Datum_isCTGroupDatum k) (e6Datum_steinbergExtras k) (e6Datum_bruhatExtras k) hz
  refine ⟨u, rfl, fun l => ?_⟩
  have hc := mem_centerChars.1 ((minTorus_mem_center_iff e6Data_valid k u).1 hz)
  have hsymm : ∀ i j : Fin Tag.E6.rank, Tag.E6.cartan i j = Tag.E6.cartan j i := by
    intro i j
    fin_cases i <;> fin_cases j <;> rfl
  have e1 : ∀ i, (∏ j, u j ^ Tag.E6.cartan j i) ^ e6CartanAdj l i =
      ∏ j, u j ^ (e6CartanAdj l i * Tag.E6.cartan i j) := fun i => by
    rw [← Finset.prod_zpow]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [← zpow_mul, hsymm i j, mul_comm]
  have e2 : ∏ i, ∏ j, u j ^ (e6CartanAdj l i * Tag.E6.cartan i j) =
      ∏ j, u j ^ (∑ i, e6CartanAdj l i * Tag.E6.cartan i j) := by
    rw [Finset.prod_comm]
    refine Finset.prod_congr rfl fun j _ => ?_
    exact prod_zpow_eq_zpow_sum (u j) Finset.univ _
  have e3 : ∏ j, u j ^ (∑ i, e6CartanAdj l i * Tag.E6.cartan i j) = u l ^ (3 : ℤ) := by
    simp_rw [e6CartanAdj_mul]
    rw [Finset.prod_eq_single l (fun j _ hj => by rw [ite_eq_right (Ne.symm hj), zpow_zero])
      (fun h => absurd (Finset.mem_univ l) h), ite_eq_left rfl]
  have e4 : ∏ i, (∏ j, u j ^ Tag.E6.cartan j i) ^ e6CartanAdj l i = 1 := by
    simp [hc]
  have h3 : u l ^ (3 : ℤ) = 1 := by
    rw [← e3, ← e2, ← e4]
    exact Finset.prod_congr rfl fun i _ => (e1 i).symm
  exact_mod_cast h3

end Center

section Generic

variable {G H : Type*} [Group G] [Group H]

theorem commute_of_mem_closure_lift (π : G →* H) (T : G) (hker : ∀ g, π g = 1 → ∀ x, g * x = x * g)
    {X : Set H} (hX : ∀ x ∈ X, ∃ g, π g = x ∧ g * T = T * g) :
    ∀ h ∈ Subgroup.closure X, (∃ g, π g = h) ∧ ∀ g, π g = h → g * T = T * g := by
  intro h hh
  induction hh using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨g₀, hg₀, hc⟩ := hX x hx
    refine ⟨⟨g₀, hg₀⟩, fun g hg => ?_⟩
    have hz := hker (g₀⁻¹ * g) (by rw [map_mul, map_inv, hg, hg₀, inv_mul_cancel])
    calc g * T = g₀ * (g₀⁻¹ * g) * T := by group
      _ = g₀ * ((g₀⁻¹ * g) * T) := by group
      _ = g₀ * (T * (g₀⁻¹ * g)) := by rw [hz]
      _ = (g₀ * T) * (g₀⁻¹ * g) := by group
      _ = (T * g₀) * (g₀⁻¹ * g) := by rw [hc]
      _ = T * g := by group
  | one => exact ⟨⟨1, map_one π⟩, fun g hg => hker g hg T⟩
  | mul h₁ h₂ _ _ ih₁ ih₂ =>
    obtain ⟨⟨g₁, hg₁⟩, c₁⟩ := ih₁
    obtain ⟨⟨g₂, hg₂⟩, c₂⟩ := ih₂
    refine ⟨⟨g₁ * g₂, by rw [map_mul, hg₁, hg₂]⟩, fun g hg => ?_⟩
    have hl : π (g₁⁻¹ * g) = h₂ := by rw [map_mul, map_inv, hg, hg₁, inv_mul_cancel_left]
    have e₁ := c₁ g₁ hg₁
    have e₂ := c₂ _ hl
    calc g * T = g₁ * ((g₁⁻¹ * g) * T) := by group
      _ = g₁ * (T * (g₁⁻¹ * g)) := by rw [e₂]
      _ = (g₁ * T) * (g₁⁻¹ * g) := by group
      _ = (T * g₁) * (g₁⁻¹ * g) := by rw [e₁]
      _ = T * g := by group
  | inv h₁ _ ih =>
    obtain ⟨⟨g₁, hg₁⟩, c₁⟩ := ih
    refine ⟨⟨g₁⁻¹, by rw [map_inv, hg₁]⟩, fun g hg => ?_⟩
    have e := c₁ g⁻¹ (by rw [map_inv, hg, inv_inv])
    calc g * T = g * (T * g⁻¹) * g := by group
      _ = g * (g⁻¹ * T) * g := by rw [← e]
      _ = T * g := by group

end Generic

section Lift


variable {k : Type} [Field k] [Finite k]

theorem mem_center_of_isogeny_eq_one {g : e6Data_valid.minGroup k}
    (hg : ((e6Isogeny k g : adjointGroup Tag.E6 k) : ModGL Tag.E6 k) = 1) :
    g ∈ Subgroup.center (e6Data_valid.minGroup k) := by
  refine ker_e6IsogenyT_le_center k ?_
  rw [MonoidHom.mem_ker]
  change e6Isogeny k g = 1
  exact Subtype.ext hg

theorem commute_minTorus_of_pinnedX [CharP k 2] (u : Fin Tag.E6.rank → kˣ)
    {γ : Fin Tag.E6.rank → ℤ} (hγ : γ ∈ rootCharKernel (e6RootParams u)) (c : k)
    {gl : e6Data_valid.minGroup k}
    (hgl : ((e6Isogeny k gl : adjointGroup Tag.E6 k) : ModGL Tag.E6 k) = pinnedX Tag.E6 k γ c) :
    gl * minTorus e6Data_valid k u = minTorus e6Data_valid k u * gl := by
  set T := minTorus e6Data_valid k u with hT
  set x := pinnedX Tag.E6 k γ c with hx
  set d := rootDiagUnit Tag.E6 (e6RootParams u) with hd
  have hπT : ((e6Isogeny k T : adjointGroup Tag.E6 k) : ModGL Tag.E6 k) = d :=
    e6Isogeny_minTorus u
  have hx2 : x * x = 1 := by
    rw [hx, ← pinnedX_add, CharTwo.add_self_eq_zero, pinnedX_zero]
  have hxd : d * x = x * d := by
    have h := rootDiagUnit_conj_pinnedX (e6RootParams u) hγ.1 c
    rw [hγ.2, Units.val_one, one_mul, mul_inv_eq_iff_eq_mul] at h
    exact h
  have hsq : gl * gl ∈ Subgroup.center (e6Data_valid.minGroup k) := by
    refine mem_center_of_isogeny_eq_one ?_
    rw [map_mul, Subgroup.coe_mul, hgl, hx2]
  set κ := gl * T * gl⁻¹ * T⁻¹ with hκ
  have hκc : κ ∈ Subgroup.center (e6Data_valid.minGroup k) := by
    refine mem_center_of_isogeny_eq_one ?_
    rw [hκ, map_mul, map_mul, map_mul, map_inv, map_inv, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inv, hgl, hπT]
    calc x * d * x⁻¹ * d⁻¹ = (x * d) * x⁻¹ * d⁻¹ := rfl
      _ = (d * x) * x⁻¹ * d⁻¹ := by rw [hxd]
      _ = 1 := by group
  have hκ' := Subgroup.mem_center_iff.1 hκc
  have hglT : gl * T * gl⁻¹ = κ * T := by rw [hκ]; group
  have hκ2 : κ * κ = 1 := by
    have h1 : (gl * gl) * T * (gl * gl)⁻¹ = κ * κ * T := by
      calc (gl * gl) * T * (gl * gl)⁻¹ = gl * (gl * T * gl⁻¹) * gl⁻¹ := by group
        _ = gl * (κ * T) * gl⁻¹ := by rw [hglT]
        _ = (gl * κ) * T * gl⁻¹ := by group
        _ = (κ * gl) * T * gl⁻¹ := by rw [hκ' gl]
        _ = κ * (gl * T * gl⁻¹) := by group
        _ = κ * κ * T := by rw [hglT]; group
    have h2 : (gl * gl) * T * (gl * gl)⁻¹ = T := by
      rw [← Subgroup.mem_center_iff.1 hsq T]
      group
    rw [h2] at h1
    calc κ * κ = κ * κ * T * T⁻¹ := by group
      _ = T * T⁻¹ := by rw [← h1]
      _ = 1 := mul_inv_cancel T
  obtain ⟨v, hv, hv3⟩ := exists_minTorus_of_mem_center_E6 hκc
  have hκ3 : κ ^ 3 = 1 := by
    rw [hv, ← map_pow]
    have : v ^ 3 = 1 := funext fun j => by simpa using hv3 j
    rw [this, map_one]
  have hκ1 : κ = 1 := by
    calc κ = κ ^ 3 * (κ * κ)⁻¹ := by group
      _ = 1 := by rw [hκ3, hκ2]; group
  have h3 : gl * T * gl⁻¹ = T := by rw [hglT, hκ1, one_mul]
  calc gl * T = gl * T * gl⁻¹ * gl := by group
    _ = T * gl := by rw [h3]

theorem commute_minTorus_of_mem_toralRootGroup [CharP k 2] (u : Fin Tag.E6.rank → kˣ)
    {g : ModGL Tag.E6 k} (hg : g ∈ toralRootGroup Tag.E6 k (e6RootParams u))
    {gl : e6Data_valid.minGroup k}
    (hgl : ((e6Isogeny k gl : adjointGroup Tag.E6 k) : ModGL Tag.E6 k) = g) :
    gl * minTorus e6Data_valid k u = minTorus e6Data_valid k u * gl := by
  set π : e6Data_valid.minGroup k →* ModGL Tag.E6 k :=
    (adjointGroup Tag.E6 k).subtype.comp (e6Isogeny k) with hπ
  set X : Set (ModGL Tag.E6 k) := Set.range (fun p : Fin Tag.E6.rank × kˣ =>
      torusElt Tag.E6 k p.1 p.2) ∪
    {y | ∃ γ ∈ rootCharKernel (e6RootParams u), ∃ c : k, y = pinnedX Tag.E6 k γ c} with hX
  have hker : ∀ g' : e6Data_valid.minGroup k, π g' = 1 → ∀ y, g' * y = y * g' := fun g' h y =>
    (Subgroup.mem_center_iff.1 (mem_center_of_isogeny_eq_one h) y).symm
  have hgen : ∀ y ∈ X, ∃ g', π g' = y ∧ g' * minTorus e6Data_valid k u =
      minTorus e6Data_valid k u * g' := by
    rintro y (⟨⟨i, t⟩, rfl⟩ | ⟨γ, hγ, c, rfl⟩)
    · refine ⟨e6Data_valid.hm k i t, ?_, ?_⟩
      · change ((e6Isogeny k (e6Data_valid.hm k i t) : adjointGroup Tag.E6 k) :
          ModGL Tag.E6 k) = torusElt Tag.E6 k i t
        rw [torusElt_eq_rootDiagUnit]
        exact e6Isogeny_hm_eq i t
      · rw [← minTorus_mulSingle, ← map_mul, ← map_mul, mul_comm]
    · obtain ⟨g', hg'⟩ := e6Isogeny_surjective k ⟨pinnedX Tag.E6 k γ c,
        pinnedX_mem_adjointGroup γ c⟩
      have hg'' : ((e6Isogeny k g' : adjointGroup Tag.E6 k) : ModGL Tag.E6 k) =
          pinnedX Tag.E6 k γ c := by rw [hg']
      exact ⟨g', hg'', commute_minTorus_of_pinnedX u hγ c hg''⟩
  have hle : toralRootGroup Tag.E6 k (e6RootParams u) ≤ Subgroup.closure X := by
    refine sup_le ?_ ?_
    · exact Subgroup.closure_mono Set.subset_union_left
    · refine iSup₂_le fun γ hγ => (Subgroup.closure_le _).2 ?_
      rintro _ ⟨c, rfl⟩
      exact Subgroup.subset_closure (Set.mem_union_right _ ⟨γ, hγ, c, rfl⟩)
  exact (commute_of_mem_closure_lift π _ hker hgen g (hle hg)).2 gl hgl

end Lift

section Shift


variable {k : Type} [Field k] [Finite k]

theorem rootChar_e6Shift_of_commute_lift [CharP k 2] (u : Fin Tag.E6.rank → kˣ)
    {cl : e6Data_valid.minGroup k} (hcl : cl * minTorus e6Data_valid k u =
      minTorus e6Data_valid k u * cl)
    {w : WeylGroup Tag.E6} {h u' v' : ModGL Tag.E6 k} (hh : h ∈ torusGroup Tag.E6 k)
    (hu' : u' ∈ rootSpan Tag.E6 k (rootCharKernel (e6RootParams u)))
    (hv' : v' ∈ rootSpan Tag.E6 k (rootCharKernel (e6RootParams u)))
    (hdec : ((e6Isogeny k cl : adjointGroup Tag.E6 k) : ModGL Tag.E6 k) =
      h * u' * canonicalRep (coxeterSystem Tag.E6) k w * v')
    (hw : w ∈ rootCharStabilizer (e6RootParams u)) :
    rootChar (e6RootParams u) (e6Shift w) = 1 := by
  set a := e6RootParams u with ha
  set T := minTorus e6Data_valid k u with hT
  have hM₁ : h * u' ∈ toralRootGroup Tag.E6 k a :=
    mul_mem (Subgroup.mem_sup_left hh) (Subgroup.mem_sup_right hu')
  have hM₂ : v' ∈ toralRootGroup Tag.E6 k a := Subgroup.mem_sup_right hv'
  have hadj : ∀ {x : ModGL Tag.E6 k}, x ∈ toralRootGroup Tag.E6 k a → x ∈ adjointGroup Tag.E6 k :=
    fun hx => (toralRootGroup_le a hx).1
  obtain ⟨l₁, hl₁⟩ := e6Isogeny_surjective k ⟨h * u', hadj hM₁⟩
  obtain ⟨l₂, hl₂⟩ := e6Isogeny_surjective k ⟨v', hadj hM₂⟩
  have hl₁' : ((e6Isogeny k l₁ : adjointGroup Tag.E6 k) : ModGL Tag.E6 k) = h * u' := by
    rw [hl₁]
  have hl₂' : ((e6Isogeny k l₂ : adjointGroup Tag.E6 k) : ModGL Tag.E6 k) = v' := by
    rw [hl₂]
  have c₁ := commute_minTorus_of_mem_toralRootGroup u hM₁ hl₁'
  have c₂ := commute_minTorus_of_mem_toralRootGroup u hM₂ hl₂'
  set y := l₁⁻¹ * cl * l₂⁻¹ with hy
  have hyT : T * y = y * T := by
    have e1 : l₁⁻¹ * T = T * l₁⁻¹ := by
      calc l₁⁻¹ * T = l₁⁻¹ * (T * l₁) * l₁⁻¹ := by group
        _ = l₁⁻¹ * (l₁ * T) * l₁⁻¹ := by rw [c₁]
        _ = T * l₁⁻¹ := by group
    have e2 : l₂⁻¹ * T = T * l₂⁻¹ := by
      calc l₂⁻¹ * T = l₂⁻¹ * (T * l₂) * l₂⁻¹ := by group
        _ = l₂⁻¹ * (l₂ * T) * l₂⁻¹ := by rw [c₂]
        _ = T * l₂⁻¹ := by group
    calc T * y = T * l₁⁻¹ * cl * l₂⁻¹ := by rw [hy]; group
      _ = l₁⁻¹ * (T * cl) * l₂⁻¹ := by rw [← e1]; group
      _ = l₁⁻¹ * (cl * T) * l₂⁻¹ := by rw [hcl]
      _ = l₁⁻¹ * cl * (T * l₂⁻¹) := by group
      _ = l₁⁻¹ * cl * (l₂⁻¹ * T) := by rw [e2]
      _ = y * T := by rw [hy]; group
  have hyπ : ((e6Isogeny k y : adjointGroup Tag.E6 k) : ModGL Tag.E6 k) =
      rootDiagUnit Tag.E6 (e6RootParams (1 : Fin Tag.E6.rank → kˣ)) *
        canonicalRep (coxeterSystem Tag.E6) k w := by
    have e : e6RootParams (1 : Fin Tag.E6.rank → kˣ) = 1 := by
      funext j
      simp [e6RootParams]
    rw [e, rootDiagUnit_one, one_mul, hy, map_mul, map_mul, map_inv, map_inv, Subgroup.coe_mul,
      Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inv, hl₁', hl₂', hdec]
    group
  exact rootChar_e6Shift_of_commute hyT (e6Isogeny_minTorus u) hyπ rfl rfl hw

end Shift

end CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3

end
