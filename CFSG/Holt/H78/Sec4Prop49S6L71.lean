module

public import CFSG.Holt.H78.Sec4Toolkit
import CFSG.Holt.H78.Sec4Prop49
import CFSG.Holt.H78.Sec4Known
import CFSG.Holt.H78.SEModelFive

public section

namespace CFSG.Holt.H78

open MulAction CFSG.Holt Equiv
open scoped Pointwise

section Group

private theorem isSolvable_range_of_ker_le {H A B : Type*} [Group H] [Group A] [Group B]
    (f : H →* A) (g : H →* B) (hfg : f.ker ≤ g.ker) (hf : Group.IsSolvable f.range) :
    Group.IsSolvable g.range := by
  have : Group.IsSolvable (H ⧸ f.ker) := Group.isSolvable_of_surjective
    (f := (QuotientGroup.quotientKerEquivRange f).symm.toMonoidHom) (MulEquiv.surjective _)
  have : Group.IsSolvable (H ⧸ g.ker) :=
    Group.isSolvable_of_surjective (QuotientGroup.map_surjective_of_surjective f.ker g.ker
      (MonoidHom.id H) (fun x => QuotientGroup.mk_surjective x) hfg)
  exact Group.isSolvable_of_surjective
    (f := (QuotientGroup.quotientKerEquivRange g).toMonoidHom) (MulEquiv.surjective _)

private theorem isSolvable_pi_of_finite' {ι : Type*} [Finite ι] {H : ι → Type*}
    [∀ i, Group (H i)] [∀ i, Group.IsSolvable (H i)] : Group.IsSolvable (∀ i, H i) := by
  classical
  have := Fintype.ofFinite ι
  choose n hn using fun i => (inferInstance : Group.IsSolvable (H i)).solvable
  refine ⟨⟨Finset.univ.sup n, ?_⟩⟩
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  funext i
  have h1 : x i ∈ derivedSeries (H i) (Finset.univ.sup n) :=
    map_derivedSeries_le_derivedSeries (Pi.evalMonoidHom H i) _ ⟨x, hx, rfl⟩
  have h2 := derivedSeries_antitone (H i) (Finset.le_sup (Finset.mem_univ i)) h1
  rw [hn i] at h2
  exact Subgroup.mem_bot.1 h2

variable {X Y : Type*} (f : X → Y)

private def fibrePermSubgroup' : Subgroup (Perm X) where
  carrier := {π | ∃ σ : Perm Y, ∀ x, f (π x) = σ (f x)}
  mul_mem' := by
    rintro π τ ⟨σ, hσ⟩ ⟨σ', hσ'⟩
    exact ⟨σ * σ', fun x => by rw [Perm.mul_apply, hσ, hσ', Perm.mul_apply]⟩
  one_mem' := ⟨1, fun _ => rfl⟩
  inv_mem' := by
    rintro π ⟨σ, hσ⟩
    exact ⟨σ⁻¹, fun x => Perm.eq_inv_iff_eq.mpr (by rw [← hσ]; simp)⟩

variable {f}

private theorem fibre_perm_unique' (hf : Function.Surjective f) {π : Perm X} {σ τ : Perm Y}
    (hσ : ∀ x, f (π x) = σ (f x)) (hτ : ∀ x, f (π x) = τ (f x)) : σ = τ :=
  Equiv.ext fun y => by
    obtain ⟨x, rfl⟩ := hf y
    rw [← hσ, hτ]

private noncomputable def fibreActHom' (hf : Function.Surjective f) :
    fibrePermSubgroup' f →* Perm Y where
  toFun π := π.2.choose
  map_one' := fibre_perm_unique' hf (1 : fibrePermSubgroup' f).2.choose_spec fun _ => rfl
  map_mul' π τ := fibre_perm_unique' hf (π * τ).2.choose_spec fun x => by
    rw [Subgroup.coe_mul, Perm.mul_apply, π.2.choose_spec, τ.2.choose_spec, Perm.mul_apply]

private theorem fibreActHom'_eq (hf : Function.Surjective f) (π : fibrePermSubgroup' f)
    {σ : Perm Y} (hσ : ∀ x, f ((π : Perm X) x) = σ (f x)) : fibreActHom' hf π = σ :=
  fibre_perm_unique' hf π.2.choose_spec hσ

end Group

section Perm

variable {F : Type*} [Fintype F] [DecidableEq F]

theorem alternatingGroup_le_closure_longInv_perm (hodd : Odd (Fintype.card F))
    (h3 : 3 ≤ Fintype.card F) : alternatingGroup F ≤ Subgroup.closure (longInv (Perm F) F) := by
  set C := Subgroup.closure (longInv (Perm F) F) with hCdef
  have hconj : ∀ g : Perm F, ∀ x ∈ C, g * x * g⁻¹ ∈ C := by
    intro g x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx => exact Subgroup.subset_closure (conj_mem_longInv hx g)
    | one => rw [mul_one, mul_inv_cancel]; exact C.one_mem
    | mul x y _ _ hx hy =>
      rw [show g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) by group]
      exact C.mul_mem hx hy
    | inv x _ hx =>
      rw [show g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ by group]
      exact C.inv_mem hx
  obtain ⟨e, he⟩ := exists_mem_longInv_perm hodd h3
  obtain ⟨r, hr, hr'⟩ := he.2
  have her : e r = r := hr
  obtain ⟨p, hp⟩ := Fintype.exists_ne_of_one_lt_card (by omega) r
  have hee : ∀ x, e (e x) = x := fun x => by
    rw [← Perm.mul_apply, mul_self_eq_one_of_mem_longInv he, Perm.one_apply]
  have hep : e p ≠ p := fun h => hp (hr' p h)
  have hepr : e p ≠ r := fun h => hp (by rw [← hee p, h, her])
  have hτ : (e * (swap p r * e * (swap p r)⁻¹)).IsThreeCycle := by
    have h1 : e * swap p r * e⁻¹ = swap (e p) r := by rw [← swap_apply_apply, her]
    rw [show e * (swap p r * e * (swap p r)⁻¹) = (e * swap p r * e⁻¹) * swap p r by
      rw [swap_inv, inv_eq_self_of_mem_longInv he]; group, h1, swap_comm (e p) r,
      swap_comm p r]
    exact Perm.isThreeCycle_swap_mul_swap_same hepr.symm hp.symm hep
  have hτC : e * (swap p r * e * (swap p r)⁻¹) ∈ C :=
    C.mul_mem (Subgroup.subset_closure he) (Subgroup.subset_closure (conj_mem_longInv he _))
  rw [← Perm.closure_three_cycles_eq_alternating, Subgroup.closure_le]
  intro σ hσ
  obtain ⟨c, hc⟩ := isConj_iff.mp (Perm.isConj_iff_cycleType_eq.mpr
    ((show (e * (swap p r * e * (swap p r)⁻¹)).cycleType = {3} from hτ).trans
      (show σ.cycleType = {3} from hσ).symm))
  rw [SetLike.mem_coe, ← hc]
  exact hconj c _ hτC

theorem not_isSolvable_of_longInv_perm_subset (hodd : Odd (Fintype.card F))
    (h5 : 5 ≤ Fintype.card F) {R : Subgroup (Perm F)} (hR : longInv (Perm F) F ⊆ R) :
    ¬ Group.IsSolvable R := by
  intro hsol
  have hA : alternatingGroup F ≤ R := (alternatingGroup_le_closure_longInv_perm hodd
    (by omega)).trans ((Subgroup.closure_le R).mpr hR)
  have : Group.IsSolvable (Perm F) := Group.isSolvable_of_ker_le_range R.subtype Perm.sign
    (by rw [Subgroup.range_subtype]; exact hA)
  exact Perm.not_isSolvable F (by rw [Cardinal.mk_fintype]; exact_mod_cast h5) this

end Perm

theorem HoltData.exists_longInv_update {K X : Type*}
    [Group K] [Finite K] [MulAction K X] (D : HoltData K X) (k : D.ι) {y₁ : Perm (D.Ψc k)}
    (hr : y₁ ∈ (D.ρ k).range) (hJ : y₁ ∈ longInv (Perm (D.Ψc k)) (D.Ψc k)) :
    ∃ u : jHull K X, (u : K) ∈ longInv K X ∧ D.ρ k u = y₁ ∧
      ∀ j, j ≠ k → D.ρ j u = D.ρ j D.tHull := by
  classical
  obtain ⟨u, huJ, hu⟩ := D.exists_mem_longInv_rho_eq
    (Function.update (fun j => D.ρ j D.tHull) k y₁) (fun j => by
      rcases eq_or_ne j k with rfl | hj
      · rw [Function.update_self]; exact hr
      · rw [Function.update_of_ne hj]; exact ⟨_, rfl⟩) (fun j => by
      rcases eq_or_ne j k with rfl | hj
      · rw [Function.update_self]; exact hJ
      · rw [Function.update_of_ne hj]; exact D.rho_mem_longInv D.t_mem j)
  exact ⟨u, huJ, by rw [hu, Function.update_self], fun j hj => by
    rw [hu, Function.update_of_ne hj]⟩

section SAFL

variable {K : Type*} [Group K] [Finite K] {X : Type*} [MulAction K X]

theorem HoltData.isSolvable_closure_longInvSwap_of_isNaturalSE (D : HoltData K X)
    (hSE : ∀ i, IsNaturalSE (D.M i)) (a b : X) :
    Group.IsSolvable (Subgroup.closure (longInvSwap K X a b)) := by
  classical
  set C := Subgroup.closure (longInvSwap K X a b) with hCdef
  have hCH : C ≤ jHull K X := Subgroup.closure_mono fun t ht => ht.1
  set S : ∀ i, Subgroup (Perm (D.Ψc i)) := fun i =>
    (stabilizer (D.M i) ({D.coord a i, D.coord b i} : Set (D.Ψc i))).map (D.M i).subtype
    with hSdef
  have hSsol : ∀ i, Group.IsSolvable (S i) := fun i => by
    obtain ⟨n, j, e, hA⟩ := (hSE i).exists_isBenderAction
    have := hA.isSolvable_stabilizer_pair (D.coord a i) (D.coord b i)
    exact Group.isSolvable_of_surjective (f := (Subgroup.equivMapOfInjective
      (stabilizer (D.M i) ({D.coord a i, D.coord b i} : Set (D.Ψc i))) (D.M i).subtype
      (D.M i).subtype_injective).toMonoidHom) (MulEquiv.surjective _)
  have hgen : C.subgroupOf (jHull K X) ≤ ⨅ i, (S i).comap (D.ρ i) := by
    rw [← closure_preimage_eq_subgroupOf fun t ht => mem_jHull_of_mem_longInv ht.1,
      Subgroup.closure_le]
    intro y hy
    rw [SetLike.mem_coe, Subgroup.mem_iInf]
    intro i
    have hsw := D.rho_mem_swapSet (u := y) hy i
    have hM : D.ρ i y ∈ D.M i := by
      have h := hsw.1
      rwa [D.range_rho_of_not_isOuterFactor (hSE i).not_isOuterFactor] at h
    have hya : D.ρ i y (D.coord a i) = D.coord b i := hsw.2.2
    have hyb : D.ρ i y (D.coord b i) = D.coord a i := apply_eq_of_mem_swapSet hsw
    refine ⟨⟨D.ρ i y, hM⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, mem_stabilizer_iff, Set.smul_set_insert, Set.smul_set_singleton]
    show ({D.ρ i y (D.coord a i), D.ρ i y (D.coord b i)} : Set (D.Ψc i)) = _
    rw [hya, hyb, Set.pair_comm]
  have hmem : ∀ c : C, ∀ i, D.ρ i (Subgroup.inclusion hCH c) ∈ S i := fun c i =>
    Subgroup.mem_iInf.mp (hgen (Subgroup.mem_subgroupOf.mpr c.2)) i
  let g : C →* ∀ i, S i := MonoidHom.pi fun i =>
    ((D.ρ i).comp (Subgroup.inclusion hCH)).codRestrict (S i) fun c => hmem c i
  have hker : Group.IsSolvable g.ker := by
    have := D.isSolvable_jOrbitKernel
    let κ : g.ker →* jOrbitKernel K X :=
      (C.subtype.comp g.ker.subtype).codRestrict _ fun x =>
        (D.mem_jOrbitKernel_iff_rho (h := Subgroup.inclusion hCH x)).mpr fun i =>
          congrArg Subtype.val (congrFun (MonoidHom.mem_ker.mp x.2) i)
    refine Group.isSolvable_of_isSolvable_injective (f := κ) fun x y hxy => ?_
    have h := congrArg Subtype.val hxy
    exact Subtype.ext (Subtype.ext h)
  have : Group.IsSolvable (∀ i, S i) := isSolvable_pi_of_finite'
  exact Group.isSolvable_of_ker_le_range g.ker.subtype g (Subgroup.range_subtype _).ge

end SAFL

section L71

private def jHom {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [MulAction G Ω]
    (hG : IsStarGroup G Ω) (α β : Ω) : Subgroup.closure (longInvSwap G Ω α β) →*
      jHull (twoPointSection G Ω α β) (holtDelta G Ω α β) where
  toFun w := ⟨twoPointElt (closure_longInvSwap_le_stabilizer_pair α β w.2),
    twoPointElt_mem_jHull hG w.2⟩
  map_one' := Subtype.ext (Subtype.ext (map_one (twoPointHom G Ω α β)))
  map_mul' u v := Subtype.ext (Subtype.ext (map_mul (twoPointHom G Ω α β) ⟨u, _⟩ ⟨v, _⟩))

private abbrev jEltS {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [MulAction G Ω]
    (hG : IsStarGroup G Ω) {α β : Ω} {c : G} (hc : c ∈ longInvSwap G Ω α β) :
    jHull (twoPointSection G Ω α β) (holtDelta G Ω α β) :=
  jHom hG α β ⟨c, Subgroup.subset_closure hc⟩

theorem closure_longInvSwap_inf_centralizer_le_stabilizer {G : Type} [Group G] {Ω : Type}
    [MulAction G Ω] (α β : Ω) (s : G) :
    Subgroup.closure (longInvSwap G Ω α β ∩
        (Subgroup.centralizer ((Subgroup.zpowers s : Subgroup G) : Set G) : Set G)) ≤
      stabilizer G (holtDelta G Ω α β ∩ fixSet Ω (Subgroup.zpowers s)) := by
  rw [Subgroup.closure_le]
  rintro c ⟨hc, hcs⟩
  have h1 : c ∈ stabilizer G (holtDelta G Ω α β) := mem_stabilizer_holtDelta_of_mem_longInvSwap hc
  have h2 : c ∈ stabilizer G (fixSet Ω (Subgroup.zpowers s)) :=
    centralizer_le_stabilizer_fixSet _ hcs
  rw [SetLike.mem_coe, mem_stabilizer_iff, Set.smul_set_inter, mem_stabilizer_iff.mp h1,
    mem_stabilizer_iff.mp h2]

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω]

theorem Sec4Setting.isSolvable_jSection_of_isTypeL (hS : Sec4Setting G Ω)
    (hL48 : ∀ {α : Ω} {v : G}, IsTypeL G Ω α v →
      ∀ (D : HoltData (typeLSection G Ω v) (fixSet Ω (Subgroup.zpowers v))) (i : D.ι),
        IsNaturalSE (factorImage _ _ (D.L i) (D.ρ i)))
    {γ α β : Ω} {s : G} (hs : IsTypeL G Ω γ s) (hsα : s • α = α) (hsβ : s • β = β) :
    Group.IsSolvable (inducedPerm (Subgroup.closure (longInvSwap G Ω α β ∩
        (Subgroup.centralizer ((Subgroup.zpowers s : Subgroup G) : Set G) : Set G)))
      (holtDelta G Ω α β ∩ fixSet Ω (Subgroup.zpowers s))
      (closure_longInvSwap_inf_centralizer_le_stabilizer α β s)) := by
  classical
  set V := Subgroup.zpowers s
  have hV : IsPGroup 2 V := isPGroup_zpowers_of_orderOf_eq_two hs.orderOf_eq_two
  have hα : α ∈ fixSet Ω V := mem_fixSet_zpowers_iff.mpr hsα
  have hβ : β ∈ fixSet Ω V := mem_fixSet_zpowers_iff.mpr hsβ
  have h3 := three_le_card_fixSet_of_isTypeL hS.star hs
  obtain ⟨DK⟩ := hS.holtData_typeLSection hs
  have hsol : Group.IsSolvable (Subgroup.closure (longInvSwap (centralizerImage Ω V)
      (fixSet Ω V) ⟨α, hα⟩ ⟨β, hβ⟩)) :=
    DK.isSolvable_closure_longInvSwap_of_isNaturalSE (hL48 hs DK) ⟨α, hα⟩ ⟨β, hβ⟩
  set H := Subgroup.closure (longInvSwap G Ω α β ∩ (Subgroup.centralizer (V : Set G) : Set G))
  have hHC : H ≤ Subgroup.centralizer (V : Set G) := (Subgroup.closure_le _).mpr fun c hc => hc.2
  let f : H →* centralizerImage Ω V :=
    (MulAction.toPermHom (Subgroup.centralizer (V : Set G)) (fixSet Ω V)).rangeRestrict.comp
      (Subgroup.inclusion hHC)
  have hle : f.range ≤ Subgroup.closure (longInvSwap (centralizerImage Ω V) (fixSet Ω V)
      ⟨α, hα⟩ ⟨β, hβ⟩) := by
    rw [MonoidHom.range_eq_map, ← Subgroup.closure_closure_coe_preimage (k := _),
      MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨⟨c, hcH⟩, hc, rfl⟩
    exact Subgroup.subset_closure ((hS.mem_longInvSwap_centralizerImage_iff hV h3 _).mpr
      ⟨c, hc.1, hc.2, fun ω => rfl⟩)
  have hf : Group.IsSolvable f.range :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)
  refine isSolvable_range_of_ker_le f _ (fun h hh => ?_) hf
  rw [MonoidHom.mem_ker] at hh ⊢
  refine Equiv.ext fun ω => Subtype.ext ?_
  have h1 := congrArg (fun π : centralizerImage Ω V =>
    (((π : Perm (fixSet Ω V)) ⟨ω, ω.2.2⟩ : fixSet Ω V) : Ω)) hh
  exact h1

theorem Sec4Setting.false_of_isTypeL_of_coord (hS : Sec4Setting G Ω)
    (hL48 : ∀ {α : Ω} {v : G}, IsTypeL G Ω α v →
      ∀ (D : HoltData (typeLSection G Ω v) (fixSet Ω (Subgroup.zpowers v))) (i : D.ι),
        IsNaturalSE (factorImage _ _ (D.L i) (D.ρ i)))
    {α β γ : Ω} (hαβ : α ≠ β) {z : G} (hz : IsTypeL G Ω γ z) (hzα : z • α = α)
    (hzβ : z • β = β) (D' : HoltData (twoPointSection G Ω α β) (holtDelta G Ω α β))
    (k : D'.ι) (F : Finset (D'.Ψc k)) (hodd : Odd F.card) (h5 : 5 ≤ F.card)
    (hFz : ∀ δ : holtDelta G Ω α β, z • (δ : Ω) = δ ↔ D'.coord δ k ∈ F)
    (hreal : ∀ e : Perm F, e ∈ longInv (Perm F) F →
      ∃ y ∈ longInv (Perm (D'.Ψc k)) (D'.Ψc k), y ∈ (D'.ρ k).range ∧ ∀ ψ : F, y ψ = e ψ) :
    False := by
  classical
  have h3Δ := three_le_card_holtDelta_of_holtData hS.star D'
  set V := Subgroup.zpowers z with hVdef
  have hV : IsPGroup 2 V := isPGroup_zpowers_of_orderOf_eq_two hz.orderOf_eq_two
  have hα : α ∈ fixSet Ω V := mem_fixSet_zpowers_iff.mpr hzα
  have hβ : β ∈ fixSet Ω V := mem_fixSet_zpowers_iff.mpr hzβ
  have h3 := three_le_card_fixSet_of_isTypeL hS.star hz
  obtain ⟨DK⟩ := hS.holtData_typeLSection hz
  have hsol := DK.isSolvable_closure_longInvSwap_of_isNaturalSE (hL48 hz DK) ⟨α, hα⟩ ⟨β, hβ⟩
  have hgen := fun π => hS.mem_longInvSwap_centralizerImage_iff hV h3 (a := ⟨α, hα⟩)
    (b := ⟨β, hβ⟩) π
  set kS := longInvSwap (centralizerImage Ω V) (fixSet Ω V) ⟨α, hα⟩ ⟨β, hβ⟩ with hkS
  set Λ : Set (fixSet Ω V) := {p | (p : Ω) ∈ holtDelta G Ω α β} with hΛ
  have hCΛ : Subgroup.closure kS ≤ stabilizer (centralizerImage Ω V) Λ := by
    rw [Subgroup.closure_le]
    intro π hπ
    obtain ⟨c, hc, -, hcπ⟩ := (hgen π).mp hπ
    rw [SetLike.mem_coe, mem_stabilizer_set]
    intro p
    show ((π • p : fixSet Ω V) : Ω) ∈ holtDelta G Ω α β ↔ (p : Ω) ∈ holtDelta G Ω α β
    rw [show ((π • p : fixSet Ω V) : Ω) = c • (p : Ω) from hcπ p]
    exact mem_stabilizer_set.mp (mem_stabilizer_holtDelta_of_mem_longInvSwap hc) _
  set r := inducedHom (Subgroup.closure kS) Λ hCΛ with hrdef
  have hfF : ∀ p : Λ, D'.coord ⟨((p : fixSet Ω V) : Ω), p.2⟩ k ∈ F := fun p =>
    (hFz _).mp (mem_fixSet_zpowers_iff.mp (p : fixSet Ω V).2)
  set f : Λ → F := fun p => ⟨D'.coord ⟨((p : fixSet Ω V) : Ω), p.2⟩ k, hfF p⟩ with hfdef
  have hf : Function.Surjective f := by
    rintro ⟨ψ, hψ⟩
    obtain ⟨δ, hδ⟩ := D'.exists_coord_apply_eq k ψ
    have hδV : (δ : Ω) ∈ fixSet Ω V := mem_fixSet_zpowers_iff.mpr ((hFz δ).mpr (hδ ▸ hψ))
    exact ⟨⟨⟨δ, hδV⟩, δ.2⟩, Subtype.ext hδ⟩
  have hcF : ∀ (c : G) (hc : c ∈ longInvSwap G Ω α β), c ∈ Subgroup.centralizer (V : Set G) →
      ∀ ψ : D'.Ψc k, D'.ρ k (jEltS hS.star hc) ψ ∈ F ↔ ψ ∈ F := by
    intro c hc hcV
    have hcJ : (jEltS hS.star hc : twoPointSection G Ω α β) ∈
        longInv (twoPointSection G Ω α β) (holtDelta G Ω α β) :=
      (hS.mem_longInv_twoPointSection_iff hαβ h3Δ _).mpr ⟨c, hc, fun _ => rfl⟩
    have hcz : c * z = z * c := mem_centralizer_zpowers_iff.mp hcV
    have himp : ∀ ψ, ψ ∈ F → D'.ρ k (jEltS hS.star hc) ψ ∈ F := by
      intro ψ hψ
      obtain ⟨δ, rfl⟩ := D'.exists_coord_apply_eq k ψ
      rw [← D'.coord_smul, ← hFz]
      show z • (c • (δ : Ω)) = c • (δ : Ω)
      rw [smul_smul, ← hcz, mul_smul, (hFz δ).mpr hψ]
    have hinv : ∀ ψ, D'.ρ k (jEltS hS.star hc) (D'.ρ k (jEltS hS.star hc) ψ) =
        ψ := fun ψ => by
      rw [← Perm.mul_apply, mul_self_eq_one_of_mem_longInv (D'.rho_mem_longInv hcJ k),
        Perm.one_apply]
    exact fun ψ => ⟨fun h => hinv ψ ▸ himp _ h, himp ψ⟩
  have hgenσ : ∀ (π : centralizerImage Ω V) (hπ : π ∈ Subgroup.closure kS) (c : G)
      (hc : c ∈ longInvSwap G Ω α β) (hcV : c ∈ Subgroup.centralizer (V : Set G)),
      (∀ ω : fixSet Ω V, ((π : Perm (fixSet Ω V)) ω : Ω) = c • (ω : Ω)) →
      ∀ p : Λ, f (r ⟨π, hπ⟩ p) =
        (D'.ρ k (jEltS hS.star hc)).subtypePerm (hcF c hc hcV) (f p) := by
    intro π hπ c hc hcV hcπ p
    apply Subtype.ext
    simp only [hfdef, Perm.subtypePerm_apply]
    rw [← D'.coord_smul]
    congr 1
    apply Subtype.ext
    exact hcπ p
  have hle : r.range ≤ fibrePermSubgroup' f := by
    rw [MonoidHom.range_eq_map, ← Subgroup.closure_closure_coe_preimage (k := kS),
      MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨⟨π, hπC⟩, hπ, rfl⟩
    obtain ⟨c, hc, hcV, hcπ⟩ := (hgen π).mp hπ
    exact ⟨_, hgenσ π hπC c hc hcV hcπ⟩
  set φ : Subgroup.closure kS →* Perm F :=
    (fibreActHom' hf).comp (r.codRestrict _ fun x => hle ⟨x, rfl⟩) with hφdef
  have hφ : ∀ (π : centralizerImage Ω V) (hπ : π ∈ kS) (c : G)
      (hc : c ∈ longInvSwap G Ω α β) (hcV : c ∈ Subgroup.centralizer (V : Set G)),
      (∀ ω : fixSet Ω V, ((π : Perm (fixSet Ω V)) ω : Ω) = c • (ω : Ω)) →
      φ ⟨π, Subgroup.subset_closure hπ⟩ =
        (D'.ρ k (jEltS hS.star hc)).subtypePerm (hcF c hc hcV) :=
    fun π _ c hc hcV hcπ => fibreActHom'_eq hf _ (hgenσ π _ c hc hcV hcπ)
  have hJ : longInv (Perm F) F ⊆ φ.range := by
    intro e he
    obtain ⟨y₁, hy₁J, hy₁r, hy₁e⟩ := hreal e he
    obtain ⟨u, huJ, huk, -⟩ := D'.exists_longInv_update k hy₁r hy₁J
    obtain ⟨c₀, hc₀, hc₀u⟩ := (hS.mem_longInv_twoPointSection_iff hαβ h3Δ _).mp huJ
    set ΛΩ : Set Ω := {ω | ∃ δ : holtDelta G Ω α β, (δ : Ω) = ω ∧ D'.coord δ k ∈ F} with hΛΩ
    have hc₀mem : ∀ ω ∈ ΛΩ, c₀ • ω ∈ ΛΩ := by
      rintro _ ⟨δ, rfl, hδ⟩
      refine ⟨(u : twoPointSection G Ω α β) • δ, hc₀u δ, ?_⟩
      rw [D'.coord_smul, huk, show D'.coord δ k = ((⟨_, hδ⟩ : F) : D'.Ψc k) from rfl,
        hy₁e ⟨_, hδ⟩]
      exact (e ⟨_, hδ⟩).2
    have hc₀Λ : c₀ ∈ stabilizer G ΛΩ := by
      rw [mem_stabilizer_set]
      intro ω
      refine ⟨fun h => ?_, hc₀mem ω⟩
      have := hc₀mem _ h
      rwa [smul_smul, mul_self_eq_one_of_mem_longInv hc₀.1, one_smul] at this
    have hΛV : ΛΩ ⊆ fixSet Ω V := by
      rintro _ ⟨δ, rfl, hδ⟩
      exact mem_fixSet_zpowers_iff.mpr ((hFz δ).mpr hδ)
    have hΛne : ΛΩ.Nonempty := by
      obtain ⟨ψ, hψ⟩ : F.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨δ, hδ⟩ := D'.exists_coord_apply_eq k ψ
      exact ⟨δ, δ, rfl, hδ ▸ hψ⟩
    obtain ⟨c, hc, hcV, hcΛ⟩ := hS.exists_mem_longInvSwap_centralizer_eqOn hαβ hV
      (Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨mem_stabilizer_iff.mpr hzα,
        mem_stabilizer_iff.mpr hzβ⟩)) hΛne hΛV hc₀ hc₀Λ
    have hπ : centralizerImageElt (Ω := Ω) hcV ∈ kS :=
      (hgen _).mpr ⟨c, hc, hcV, fun ω => rfl⟩
    refine ⟨⟨_, Subgroup.subset_closure hπ⟩, (hφ _ hπ c hc hcV fun ω => rfl).trans ?_⟩
    refine Equiv.ext fun ψ => Subtype.ext ?_
    show D'.ρ k (jEltS hS.star hc) ψ = (e ψ : D'.Ψc k)
    obtain ⟨δ, hδ⟩ := D'.exists_coord_apply_eq k ψ
    have hδΛ : (δ : Ω) ∈ ΛΩ := ⟨δ, rfl, hδ ▸ ψ.2⟩
    have hcu : (jEltS hS.star hc : twoPointSection G Ω α β) • δ =
        (u : twoPointSection G Ω α β) • δ :=
      Subtype.ext ((hcΛ _ hδΛ).trans (hc₀u δ).symm)
    rw [← hδ, ← D'.coord_smul, hcu, D'.coord_smul, huk, hδ, hy₁e ψ]
  have hsolC : Group.IsSolvable (Subgroup.closure kS) := hsol
  have hsolR : Group.IsSolvable φ.range :=
    Group.isSolvable_of_surjective φ.rangeRestrict_surjective
  exact not_isSolvable_of_longInv_perm_subset (by rwa [Fintype.card_coe])
    (by rwa [Fintype.card_coe]) hJ hsolR

end L71

end CFSG.Holt.H78
