module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftFamilyDecomp

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open CFSG.QuasithinUnique.Setup.Offender CFSG.QuasithinUnique.Setup.Layer CFSG.QuasithinUnique
  CFSG.Quasithin.B6 CFSG.QuasithinUnique.Setup.SL2Modules
open scoped MatrixGroups LinearAlgebra.Projectivization commutatorElement
open Projectivization

universe v

section Off

variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [Finite V] {F : Type} [Field F]
  [Fintype F] [Fintype (ℙ F (Fin 2 → F))] [DecidableEq (ℙ F (Fin 2 → F))]
  {H T : Subgroup (V ≃ₗ[ZMod 2] V)} {n r : ℕ} {Lc : Fin r → Subgroup (V ≃ₗ[ZMod 2] V)}

omit [Finite V] in
theorem off_disp (ctx : FamilyCtx H T n F r Lc) {A : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hA : IsMinOffender H A) {i : Fin r} (hmove : ⁅Lc i, A⁆ ≠ ⊥) :
    A ≤ trivMod (commGL (Lc i) ⊤) := by
  obtain ⟨hd, -⟩ := ctx.offd A hA i hmove
  intro a ha w
  have hw : w ∈ commGL (Lc i) ⊤ ⊔ fixGL A := by rw [hd.V_split]; trivial
  obtain ⟨x, hx, c, hc, rfl⟩ := Submodule.mem_sup.1 hw
  have hax : a x ∈ commGL (Lc i) ⊤ := hd.inv_A a ha x hx
  have hac : a c = c := hc a ha
  rw [map_add, hac]
  have e : a x + c - (x + c) = a x - x := by abel
  rw [e]
  exact Submodule.sub_mem _ hax hx

omit [Finite V] in
theorem off_fix_other (ctx : FamilyCtx H T n F r Lc) {A : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hA : IsMinOffender H A) {i : Fin r} (hmove : ⁅Lc i, A⁆ ≠ ⊥) {j : Fin r} (hji : j ≠ i) :
    A ≤ centSub (MonoidHom.id (V ≃ₗ[ZMod 2] V)) (commGL (Lc j) ⊤) := by
  obtain ⟨-, hd2⟩ := ctx.offd A hA i hmove
  have hdisp := off_disp ctx hA hmove
  intro a ha u hu
  have hle : commGL (Lc j) ⊤ ≤ LinearMap.ker ((a : V →ₗ[ZMod 2] V) - LinearMap.id) := by
    rw [commSub_le_iff]
    intro l hl w _
    have hcomm : (l : V ≃ₗ[ZMod 2] V) * a = a * l :=
      (hd2 (Lc j) (ctx.hLc.isComp j) (fun h => hji (ctx.hLc.injective h))).2 l hl a ha
    have h1 : a (l w) = l (a w) := by
      have := congrArg (fun φ : V ≃ₗ[ZMod 2] V => φ w) hcomm
      simpa using this.symm
    have hy : a w - w ∈ commGL (Lc i) ⊤ := hdisp ha w
    have hly : l (a w - w) = a w - w := ctx.layer.others_fix i j hji l hl _ hy
    rw [map_sub] at hly
    rw [LinearMap.mem_ker]
    show a ((MonoidHom.id (V ≃ₗ[ZMod 2] V)) l w - w) - ((MonoidHom.id (V ≃ₗ[ZMod 2] V)) l w - w) = 0
    simp only [MonoidHom.id_apply, map_sub, h1]
    rw [show l (a w) - a w - (l w - w) = (l (a w) - l w) - (a w - w) by abel, hly, sub_self]
  have := hle hu
  rw [LinearMap.mem_ker] at this
  exact sub_eq_zero.1 this

theorem off_fix_C (ctx : FamilyCtx H T n F r Lc) {A : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hA : IsMinOffender H A) {i : Fin r} (hmove : ⁅Lc i, A⁆ ≠ ⊥) :
    A ≤ centSub (MonoidHom.id (V ≃ₗ[ZMod 2] V)) (fixGL (oddGen H)) := by
  intro a ha c hc
  rcases alt_dichotomy ctx hA i hmove with ⟨hAL, -⟩ | ⟨-, hZ, -⟩
  · have haK : a ∈ oddGen H := by
      rw [ctx.layer.K_eq]
      exact Subgroup.mem_iSup_of_mem i (hAL ha)
    exact hc a haK
  · have h1 : a c - c ∈ commGL (Lc i) ⊤ := off_disp ctx hA hmove ha c
    have h2 : a c ∈ fixGL (oddGen H) := H_fix_C ctx (hA.1 ha) hc
    have h3 : a c - c ∈ fixGL (oddGen H) := (fixGL (oddGen H)).sub_mem h2 hc
    have h4 : a c - c ∈ commGL (Lc i) ⊤ ⊓ fixGL (oddGen H) := ⟨h1, h3⟩
    rw [I_inf_C ctx i, hZ] at h4
    exact sub_eq_zero.1 ((Submodule.mem_bot _).1 h4)

theorem off_comm (ctx : FamilyCtx H T n F r Lc) {A A' : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hA : IsMinOffender H A) (hA' : IsMinOffender H A') {i j : Fin r} (hi : ⁅Lc i, A⁆ ≠ ⊥)
    (hj : ⁅Lc j, A'⁆ ≠ ⊥) (hij : i ≠ j) : ∀ a ∈ A, ∀ a' ∈ A', a * a' = a' * a := by
  intro a ha a' ha'
  apply LinearEquiv.ext
  intro v
  obtain ⟨hd, -⟩ := ctx.offd A hA i hi
  obtain ⟨hd', -⟩ := ctx.offd A' hA' j hj
  let E : Submodule (ZMod 2) V := LinearMap.eqLocus
    ((a : V →ₗ[ZMod 2] V) ∘ₗ (a' : V →ₗ[ZMod 2] V)) ((a' : V →ₗ[ZMod 2] V) ∘ₗ (a : V →ₗ[ZMod 2] V))
  have hE : (⊤ : Submodule (ZMod 2) V) ≤ E := by
    rw [← V_sum ctx]
    refine sup_le (iSup_le fun k => ?_) ?_
    · intro u hu
      show a (a' u) = a' (a u)
      by_cases hki : k = i
      · subst hki
        have h1 : a' u = u := off_fix_other ctx hA' hj hij ha' u hu
        have h2 : a' (a u) = a u := off_fix_other ctx hA' hj hij ha' _ (hd.inv_A a ha u hu)
        rw [h1, h2]
      · by_cases hkj : k = j
        · subst hkj
          have h1 : a u = u := off_fix_other ctx hA hi (Ne.symm hij) ha u hu
          have h2 : a (a' u) = a' u := off_fix_other ctx hA hi (Ne.symm hij) ha _ (hd'.inv_A a' ha' u hu)
          rw [h1, h2]
        · have h1 : a u = u := off_fix_other ctx hA hi hki ha u hu
          have h2 : a' u = u := off_fix_other ctx hA' hj hkj ha' u hu
          rw [h2, h1, h2]
    · intro c hc
      have h1 : a c = c := off_fix_C ctx hA hi ha c hc
      have h2 : a' c = c := off_fix_C ctx hA' hj ha' c hc
      show a (a' c) = a' (a c)
      rw [h2, h1, h2]
  have := hE (Submodule.mem_top : v ∈ ⊤)
  exact this

omit [Finite V] in
theorem le_blockB_gen {L A : Subgroup (V ≃ₗ[ZMod 2] V)} (hA : IsMinOffender H A)
    (hmove : ⁅L, A⁆ ≠ ⊥) : A ≤ blockB H L :=
  le_iSup₂_of_le A ⟨hA, hmove⟩ le_rfl

omit [Finite V] in
theorem blockB_le_of {L X : Subgroup (V ≃ₗ[ZMod 2] V)}
    (h : ∀ A, IsMinOffender H A → ⁅L, A⁆ ≠ ⊥ → A ≤ X) : blockB H L ≤ X :=
  iSup₂_le fun A hA => h A hA.1 hA.2

omit [Finite V] in
theorem blockB_le_centSub_I (ctx : FamilyCtx H T n F r Lc) {i j : Fin r} (hji : j ≠ i) :
    blockB H (Lc i) ≤ centSub (MonoidHom.id (V ≃ₗ[ZMod 2] V)) (commGL (Lc j) ⊤) :=
  blockB_le_of fun _ hA hmove => off_fix_other ctx hA hmove hji

theorem blockB_le_centSub_C (ctx : FamilyCtx H T n F r Lc) {i : Fin r} :
    blockB H (Lc i) ≤ centSub (MonoidHom.id (V ≃ₗ[ZMod 2] V)) (fixGL (oddGen H)) :=
  blockB_le_of fun _ hA hmove => off_fix_C ctx hA hmove

omit [Finite V] in
theorem blockB_le_trivMod (ctx : FamilyCtx H T n F r Lc) {i : Fin r} :
    blockB H (Lc i) ≤ trivMod (commGL (Lc i) ⊤) :=
  blockB_le_of fun _ hA hmove => off_disp ctx hA hmove

omit [Finite V] in
theorem blockB_le_J (i : Fin r) : blockB H (Lc i) ≤ offenderJ H :=
  blockB_le_of fun _ hA _ => le_offenderJ hA

omit [Finite V] in
theorem Lc_le_blockB (ctx : FamilyCtx H T n F r Lc) (i : Fin r) : Lc i ≤ blockB H (Lc i) := by
  obtain ⟨A, hA, hLA⟩ := ctx.layer.moving i
  exact le_blockB (ctx.hLc.isComp i).1 hA hLA (ctx.hLc.ne_bot i)

omit [Finite V] in
theorem blockB_I_eq (ctx : FamilyCtx H T n F r Lc) (i : Fin r) :
    commGL (blockB H (Lc i)) ⊤ = commGL (Lc i) ⊤ := by
  apply le_antisymm
  · rw [commSub_le_iff]
    intro b hb u _
    exact blockB_le_trivMod ctx hb u
  · exact commSub_mono_left _ (Lc_le_blockB ctx i)

theorem blockB_comm (ctx : FamilyCtx H T n F r Lc) {i j : Fin r} (hij : i ≠ j) :
    ∀ x ∈ blockB H (Lc i), ∀ y ∈ blockB H (Lc j), x * y = y * x := by
  have h1 : ∀ A, IsMinOffender H A → ⁅Lc i, A⁆ ≠ ⊥ →
      blockB H (Lc j) ≤ Subgroup.centralizer (A : Set (V ≃ₗ[ZMod 2] V)) := by
    intro A hA hmove
    refine blockB_le_of fun A' hA' hmove' y hy => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact off_comm ctx hA hA' hmove hmove' hij a ha y hy
  have h2 : blockB H (Lc i) ≤ Subgroup.centralizer (blockB H (Lc j) : Set (V ≃ₗ[ZMod 2] V)) := by
    refine blockB_le_of fun A hA hmove a ha => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro y' hy'
    exact (Subgroup.mem_centralizer_iff.1 (h1 A hA hmove hy') a ha).symm
  intro x hx y hy
  exact (Subgroup.mem_centralizer_iff.1 (h2 hx) y hy).symm

theorem blockB_direct (ctx : FamilyCtx H T n F r Lc) (i : Fin r) :
    blockB H (Lc i) ⊓ (⨆ j, ⨆ (_ : j ≠ i), blockB H (Lc j)) = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxi, hxj⟩
  have hfixI : x ∈ centSub (MonoidHom.id (V ≃ₗ[ZMod 2] V)) (commGL (Lc i) ⊤) :=
    (iSup₂_le fun j hji => blockB_le_centSub_I ctx (i := j) (j := i) (Ne.symm hji) :
      (⨆ j, ⨆ (_ : j ≠ i), blockB H (Lc j)) ≤
        centSub (MonoidHom.id (V ≃ₗ[ZMod 2] V)) (commGL (Lc i) ⊤)) hxj
  have hall : ∀ v : V, x v = v := by
    have h : (⊤ : Submodule (ZMod 2) V) ≤ LinearMap.ker ((x : V →ₗ[ZMod 2] V) - LinearMap.id) := by
      rw [← V_sum ctx]
      refine sup_le (iSup_le fun k => ?_) ?_
      · intro u hu
        rw [LinearMap.mem_ker]
        by_cases hk : k = i
        · subst hk
          exact sub_eq_zero.2 (hfixI u hu)
        · exact sub_eq_zero.2 (blockB_le_centSub_I ctx hk hxi u hu)
      · intro c hc
        rw [LinearMap.mem_ker]
        exact sub_eq_zero.2 (blockB_le_centSub_C ctx hxi c hc)
    intro v
    have := h (Submodule.mem_top : v ∈ ⊤)
    rw [LinearMap.mem_ker] at this
    exact sub_eq_zero.1 this
  exact Subgroup.mem_bot.2 (LinearEquiv.ext hall)

omit [Finite V] in
theorem offenderJ_eq (ctx : FamilyCtx H T n F r Lc) : offenderJ H = ⨆ i, blockB H (Lc i) := by
  apply le_antisymm
  · refine iSup₂_le fun A hA => ?_
    obtain ⟨-, i, hi, -⟩ := ctx.layer.offender A hA
    exact (le_blockB_gen hA hi).trans (le_iSup (fun i => blockB H (Lc i)) i)
  · exact iSup_le blockB_le_J

theorem blockB_normal (ctx : FamilyCtx H T n F r Lc) (i : Fin r) :
    ((blockB H (Lc i)).subgroupOf (offenderJ H)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer (blockB_le_J i), offenderJ_eq ctx]
  refine iSup_le fun j => ?_
  by_cases hji : j = i
  · subst hji
    exact Subgroup.le_normalizer
  · have : blockB H (Lc j) ≤ Subgroup.centralizer (blockB H (Lc i) : Set (V ≃ₗ[ZMod 2] V)) :=
      fun y hy => Subgroup.mem_centralizer_iff.2 fun x hx =>
        blockB_comm ctx (Ne.symm hji) x hx y hy
    exact this.trans (Subgroup.centralizer_le_normalizer _)

omit [Finite V] in
theorem T_le_H (ctx : FamilyCtx H T n F r Lc) : T ≤ H :=
  le_sup_right.trans (le_of_eq ctx.layer.H_eq_KT)

theorem blockB_subnormal (ctx : FamilyCtx H T n F r Lc) (i : Fin r) :
    ((blockB H (Lc i)).subgroupOf H).IsSubnormal := by
  have hJH : offenderJ H ≤ H := offenderJ_le
  have hJnorm : offenderJ H ≤ Subgroup.normalizer (blockB H (Lc i) : Set (V ≃ₗ[ZMod 2] V)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (blockB_le_J i)).1 (blockB_normal ctx i)
  have hle : (blockB H (Lc i)).subgroupOf H ≤ (offenderJ H).subgroupOf H :=
    fun x hx => blockB_le_J i hx
  have hn : (((blockB H (Lc i)).subgroupOf H).subgroupOf ((offenderJ H).subgroupOf H)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    show (((g * n * g⁻¹ : ↥((offenderJ H).subgroupOf H)) : ↥H) : V ≃ₗ[ZMod 2] V) ∈ blockB H (Lc i)
    have e : (((g * n * g⁻¹ : ↥((offenderJ H).subgroupOf H)) : ↥H) : V ≃ₗ[ZMod 2] V) =
        ((g : ↥H) : V ≃ₗ[ZMod 2] V) * ((n : ↥H) : V ≃ₗ[ZMod 2] V) *
          ((g : ↥H) : V ≃ₗ[ZMod 2] V)⁻¹ := rfl
    rw [e]
    exact (Subgroup.mem_normalizer_iff.1 (hJnorm g.2) _).1 hn
  exact Subgroup.IsSubnormal.trans hle hn.isSubnormal ctx.layer.J_normal.isSubnormal

omit [Finite V] in
theorem family_trans (ctx : FamilyCtx H T n F r Lc) (i j : Fin r) :
    ∃ t ∈ T, (Lc i).map (MulAut.conj t).toMonoidHom = Lc j ∧
      (blockB H (Lc i)).map (MulAut.conj t).toMonoidHom = blockB H (Lc j) ∧
      (commGL (Lc i) ⊤).map (t : V →ₗ[ZMod 2] V) = commGL (Lc j) ⊤ := by
  obtain ⟨t, ht, h⟩ := ctx.layer.transitive i j
  have hB : conjSub t (blockB H (Lc i)) = blockB H (Lc j) :=
    blockB_conj (T_le_H ctx ht) h
  refine ⟨t, ht, h, hB, ?_⟩
  rw [← commGL_conjSub]
  exact congrArg (fun X => commGL X ⊤) h

omit [Finite V] in
theorem family_perm (ctx : FamilyCtx H T n F r Lc) {t : V ≃ₗ[ZMod 2] V} (ht : t ∈ T) (i : Fin r) :
    ∃ j, (Lc i).map (MulAut.conj t).toMonoidHom = Lc j ∧
      (blockB H (Lc i)).map (MulAut.conj t).toMonoidHom = blockB H (Lc j) ∧
      (commGL (Lc i) ⊤).map (t : V →ₗ[ZMod 2] V) = commGL (Lc j) ⊤ := by
  obtain ⟨j, h⟩ := ctx.hLc.perm (T_le_H ctx ht) i
  have hB : conjSub t (blockB H (Lc i)) = blockB H (Lc j) :=
    blockB_conj (T_le_H ctx ht) h
  refine ⟨j, h, hB, ?_⟩
  rw [← commGL_conjSub]
  exact congrArg (fun X => commGL X ⊤) h

theorem C_eq_J (ctx : FamilyCtx H T n F r Lc) : fixGL (oddGen H) = fixGL (offenderJ H) := by
  apply le_antisymm
  · intro c hc
    have hle : offenderJ H ≤ MulAction.stabilizer (V ≃ₗ[ZMod 2] V) c := by
      refine iSup₂_le fun A hA a ha => ?_
      obtain ⟨-, i, hi, -⟩ := ctx.layer.offender A hA
      exact off_fix_C ctx hA hi ha c hc
    exact fun g hg => hle hg
  · exact fixSub_anti _ ctx.layer.K_le_J

end Off

end CFSG.QuasithinUnique.Setup.Lift
