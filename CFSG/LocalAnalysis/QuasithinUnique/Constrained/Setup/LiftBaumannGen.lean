module

public import CFSG.LocalAnalysis.ComponentInitial.CentralSL2Semilinear
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftFamilyCount
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftBaumannNat

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open CFSG.QuasithinUnique.Setup.Offender CFSG.QuasithinUnique.Setup.Layer CFSG.QuasithinUnique
  CFSG.Quasithin.B6 CFSG.QuasithinUnique.Setup.SL2Modules
open scoped MatrixGroups LinearAlgebra.Projectivization
open Projectivization

universe v

section SL2

variable {F : Type*} [Field F]

@[expose] def sl2W : SL(2, F) := ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩

theorem sl2W_mul_uElt (s : F) : sl2W * uElt s = lElt (-s) * sl2W := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  fin_cases i <;> fin_cases j <;> simp [sl2W, uElt, lElt, Matrix.mul_apply, Fin.sum_univ_two]

theorem sl2W_conj_uElt (s : F) : sl2W * uElt s * sl2W⁻¹ = lElt (-s) := by
  rw [mul_inv_eq_iff_eq_mul]
  exact sl2W_mul_uElt s

theorem sl2_sup_conj_eq_top (x : SL(2, F)) (A : Subgroup SL(2, F))
    (hA : ∀ g, g ∈ A ↔ ∃ t, x⁻¹ * g * x = uElt t) :
    A ⊔ A.map (MulAut.conj (x * sl2W * x⁻¹)).toMonoidHom = ⊤ := by
  set C := A ⊔ A.map (MulAut.conj (x * sl2W * x⁻¹)).toMonoidHom with hC
  have h1 : ∀ t : F, x * uElt t * x⁻¹ ∈ C := fun t =>
    Subgroup.mem_sup_left ((hA _).2 ⟨t, by group⟩)
  have h2 : ∀ t : F, x * lElt t * x⁻¹ ∈ C := fun t => by
    refine Subgroup.mem_sup_right ⟨x * uElt (-t) * x⁻¹, (hA _).2 ⟨-t, by group⟩, ?_⟩
    have h := sl2W_conj_uElt (F := F) (-t)
    rw [neg_neg] at h
    show (x * sl2W * x⁻¹) * (x * uElt (-t) * x⁻¹) * (x * sl2W * x⁻¹)⁻¹ = _
    calc (x * sl2W * x⁻¹) * (x * uElt (-t) * x⁻¹) * (x * sl2W * x⁻¹)⁻¹
        = x * (sl2W * uElt (-t) * sl2W⁻¹) * x⁻¹ := by group
      _ = x * lElt t * x⁻¹ := by rw [h]
  have h3 : ∀ y ∈ Subgroup.closure (Set.range (uElt (F := F)) ∪ Set.range (lElt (F := F))),
      x * y * x⁻¹ ∈ C := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem y hy =>
      rcases hy with ⟨t, rfl⟩ | ⟨t, rfl⟩
      · exact h1 t
      · exact h2 t
    | one => simp
    | mul y z _ _ hy hz =>
      have := C.mul_mem hy hz
      rwa [show x * y * x⁻¹ * (x * z * x⁻¹) = x * (y * z) * x⁻¹ by group] at this
    | inv y _ hy =>
      have := C.inv_mem hy
      rwa [show (x * y * x⁻¹)⁻¹ = x * y⁻¹ * x⁻¹ by group] at this
  refine eq_top_iff.2 fun M _ => ?_
  have hM : x⁻¹ * M * x ∈
      Subgroup.closure (Set.range (uElt (F := F)) ∪ Set.range (lElt (F := F))) := by
    have e : Set.range (CFSG.LocalAnalysis.ComponentInitial.sl2Upper F) ∪
        Set.range (CFSG.LocalAnalysis.ComponentInitial.sl2Lower F) =
        Set.range (uElt (F := F)) ∪ Set.range (lElt (F := F)) := rfl
    rw [← e, CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower]
    trivial
  have h4 := h3 _ hM
  rwa [show x * (x⁻¹ * M * x) * x⁻¹ = M by group] at h4

end SL2

section Natural

variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [Finite V] {F : Type} [Field F]
  [Fintype F] [Fintype (ℙ F (Fin 2 → F))] [DecidableEq (ℙ F (Fin 2 → F))]
  {H T : Subgroup (V ≃ₗ[ZMod 2] V)} {n r : ℕ} {Lc : Fin r → Subgroup (V ≃ₗ[ZMod 2] V)}

omit [Finite V] [Fintype F] [Fintype (ℙ F (Fin 2 → F))] [DecidableEq (ℙ F (Fin 2 → F))] in
theorem natural_exists_conj_gen (hnat : NaturalFamily H F r Lc) {i : Fin r}
    {U : Subgroup (V ≃ₗ[ZMod 2] V)} (hU : IsSylowTwoOf U (Lc i)) :
    ∃ g ∈ Lc i, Lc i ≤ U ⊔ conjSub g U := by
  obtain ⟨θ, β, x, -, hline⟩ := natural_coords hnat hU
  set A := (U.subgroupOf (Lc i)).map θ.toMonoidHom with hAdef
  have hA : ∀ g, g ∈ A ↔ ∃ t, x⁻¹ * g * x = uElt t := fun g => by
    have h1 := conj_mem_range_iff_fixes_line x g
    have h2 := mem_rootGroup_iff (x⁻¹ * g * x)
    rw [hline g]
    constructor
    · intro h
      exact h2.1 (h1.2 h)
    · intro h
      exact h1.1 (h2.2 h)
  have hgen := sl2_sup_conj_eq_top x A hA
  set g : ↥(Lc i) := θ.symm (x * sl2W * x⁻¹) with hg
  refine ⟨g, g.2, ?_⟩
  set Cl := U ⊔ conjSub (g : V ≃ₗ[ZMod 2] V) U with hCl
  have hAle : A ≤ (Cl.subgroupOf (Lc i)).map θ.toMonoidHom := by
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨u, Subgroup.mem_subgroupOf.2
      (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.1 hu)), rfl⟩
  have hAle2 : A.map (MulAut.conj (x * sl2W * x⁻¹)).toMonoidHom ≤
      (Cl.subgroupOf (Lc i)).map θ.toMonoidHom := by
    rintro _ ⟨a, ⟨u, hu, rfl⟩, rfl⟩
    refine ⟨g * u * g⁻¹, Subgroup.mem_subgroupOf.2 ?_, ?_⟩
    · have hmem : (g : V ≃ₗ[ZMod 2] V) * (u : V ≃ₗ[ZMod 2] V) * (g : V ≃ₗ[ZMod 2] V)⁻¹ ∈
          conjSub (g : V ≃ₗ[ZMod 2] V) U :=
        conjSub_mem_of_mem (x := (g : V ≃ₗ[ZMod 2] V)) (Subgroup.mem_subgroupOf.1 hu)
      exact Subgroup.mem_sup_right hmem
    · rw [map_mul, map_mul, map_inv]
      simp [hg, MulAut.conj_apply]
      group
  intro l hl
  have hl' : θ ⟨l, hl⟩ ∈ A ⊔ A.map (MulAut.conj (x * sl2W * x⁻¹)).toMonoidHom := by
    rw [hgen]
    trivial
  obtain ⟨c, hc, hcl⟩ := sup_le hAle hAle2 hl'
  have hcl' : c = ⟨l, hl⟩ := θ.injective hcl
  rw [hcl'] at hc
  exact Subgroup.mem_subgroupOf.1 hc

theorem exists_gen_element_of_local (ctx : FamilyCtx H T n F r Lc)
    (U : Fin r → Subgroup (V ≃ₗ[ZMod 2] V))
    (hUcomm : ∀ i j : Fin r, i ≠ j → ∀ x ∈ Lc i, ∀ y ∈ U j, x * y = y * x)
    (hgen : ∀ i, ∃ g ∈ Lc i, Lc i ≤ U i ⊔ conjSub g (U i)) :
    ∃ g ∈ ⨆ i, Lc i, (⨆ i, Lc i) ≤ (⨆ i, U i) ⊔ conjSub g (⨆ i, U i) := by
  classical
  choose gj hgj hgen using hgen
  have hcentrL : ∀ i j : Fin r, i ≠ j → ∀ x ∈ Lc i,
      x ∈ Subgroup.centralizer (Lc j : Set (V ≃ₗ[ZMod 2] V)) := fun i j hij x hx =>
    Subgroup.mem_centralizer_iff.2 fun y hy => (ctx.hLc.elem_commute hij x hx y hy).symm
  have hcentrU : ∀ i j : Fin r, i ≠ j → ∀ x ∈ Lc i,
      x ∈ Subgroup.centralizer (U j : Set (V ≃ₗ[ZMod 2] V)) := fun i j hij x hx =>
    Subgroup.mem_centralizer_iff.2 fun y hy => (hUcomm i j hij x hx y hy).symm
  have key : ∀ s : Finset (Fin r), ∃ g ∈ ⨆ i ∈ s, Lc i, ∀ j ∈ s,
      ∃ c ∈ Subgroup.centralizer (U j : Set (V ≃ₗ[ZMod 2] V)), g = gj j * c := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨1, Subgroup.one_mem _, by simp⟩
    | insert a s ha ih =>
      obtain ⟨g, hg, hgs⟩ := ih
      have hleL : (⨆ i ∈ s, Lc i) ≤
          Subgroup.centralizer (Lc a : Set (V ≃ₗ[ZMod 2] V)) := by
        refine iSup₂_le fun i hi x hx => ?_
        exact hcentrL i a (fun h => ha (h ▸ hi)) x hx
      have hleU : (⨆ i ∈ s, Lc i) ≤
          Subgroup.centralizer (U a : Set (V ≃ₗ[ZMod 2] V)) := by
        refine iSup₂_le fun i hi x hx => ?_
        exact hcentrU i a (fun h => ha (h ▸ hi)) x hx
      have hgcL := hleL hg
      have hgcU := hleU hg
      have hmono : (⨆ i ∈ s, Lc i) ≤ ⨆ i ∈ insert a s, Lc i :=
        biSup_mono fun i hi => Finset.mem_insert_of_mem hi
      refine ⟨g * gj a, Subgroup.mul_mem _ (hmono hg)
        (Subgroup.mem_iSup_of_mem a (Subgroup.mem_iSup_of_mem (Finset.mem_insert_self a s)
          (hgj a))), fun j hj => ?_⟩
      rcases Finset.mem_insert.1 hj with hja | hjs
      · subst hja
        refine ⟨g, hgcU, ?_⟩
        exact (Subgroup.mem_centralizer_iff.1 hgcL (gj _) (hgj _)).symm
      · obtain ⟨c, hc, hgc'⟩ := hgs j hjs
        refine ⟨c * gj a, Subgroup.mul_mem _ hc
          (hcentrU a j (fun h => ha (h ▸ hjs)) _ (hgj a)), ?_⟩
        rw [hgc', mul_assoc]
  obtain ⟨g, hg, hgs⟩ := key Finset.univ
  have hgK : g ∈ ⨆ i, Lc i := by simpa using hg
  refine ⟨g, hgK, iSup_le fun j => ?_⟩
  obtain ⟨c, hc, hgc⟩ := hgs j (Finset.mem_univ j)
  have hconj : conjSub (gj j) (U j) ≤ conjSub g (⨆ i, U i) := by
    intro y hy
    rw [mem_conjSub] at hy ⊢
    have hy' : (gj j)⁻¹ * y * gj j ∈ U j := hy
    have hcomm : c⁻¹ * ((gj j)⁻¹ * y * gj j) * c = (gj j)⁻¹ * y * gj j := by
      have h1 := Subgroup.mem_centralizer_iff.1 hc _ hy'
      calc c⁻¹ * ((gj j)⁻¹ * y * gj j) * c = c⁻¹ * (((gj j)⁻¹ * y * gj j) * c) := mul_assoc _ _ _
        _ = c⁻¹ * (c * ((gj j)⁻¹ * y * gj j)) := by rw [h1]
        _ = (gj j)⁻¹ * y * gj j := inv_mul_cancel_left c _
    have h5 : g⁻¹ * y * g = (gj j)⁻¹ * y * gj j := by
      rw [hgc, ← hcomm]
      group
    rw [h5]
    exact Subgroup.mem_iSup_of_mem j hy'
  calc Lc j ≤ U j ⊔ conjSub (gj j) (U j) := hgen j
    _ ≤ (⨆ i, U i) ⊔ conjSub g (⨆ i, U i) :=
      sup_le_sup (le_iSup U j) hconj

theorem natural_exists_gen_element (ctx : FamilyCtx H T n F r Lc) (hnat : NaturalFamily H F r Lc)
    (hU : ∀ i, IsSylowTwoOf (T ⊓ Lc i) (Lc i)) :
    ∃ g ∈ ⨆ i, Lc i, (⨆ i, Lc i) ≤ (⨆ i, T ⊓ Lc i) ⊔ conjSub g (⨆ i, T ⊓ Lc i) :=
  exists_gen_element_of_local ctx (fun i => T ⊓ Lc i)
    (fun _ _ hij x hx y hy => ctx.hLc.elem_commute hij x hx y (hy.2))
    (fun i => natural_exists_conj_gen hnat (hU i))

omit [Finite V] [Fintype (ℙ F (Fin 2 → F))] [DecidableEq (ℙ F (Fin 2 → F))] in
theorem natCard_W_natural (hnat : NaturalFamily H F r Lc) (i : Fin r) :
    Nat.card (↥(commGL (Lc i) ⊤) ⧸ fixIn (Lc i) (commGL (Lc i) ⊤)) =
      Fintype.card F * Fintype.card F := by
  obtain ⟨θ, β, -, -⟩ := hnat.model i
  rw [Nat.card_congr β.toEquiv, Nat.card_fun, Nat.card_eq_fintype_card (α := F)]
  simp [sq]

theorem card_V_natural (ctx : FamilyCtx H T n F r Lc) (hnat : NaturalFamily H F r Lc) :
    Nat.card V = Nat.card ↥(fixGL (oddGen H)) * 2 ^ (2 * n * r) := by
  rw [card_V_eq_prod ctx, Finset.prod_congr rfl fun i _ => natCard_W_natural hnat i,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, ctx.hF, ← pow_add, ← two_mul,
    ← pow_mul]

end Natural

end CFSG.QuasithinUnique.Setup.Lift
