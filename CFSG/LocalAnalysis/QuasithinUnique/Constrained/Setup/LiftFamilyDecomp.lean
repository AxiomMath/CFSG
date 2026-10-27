module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftFamilySplit
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftDirect

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open CFSG.QuasithinUnique.Setup.Offender CFSG.QuasithinUnique.Setup.Layer CFSG.QuasithinUnique
  CFSG.Quasithin.B6 CFSG.QuasithinUnique.Setup.SL2Modules
open scoped MatrixGroups LinearAlgebra.Projectivization commutatorElement
open Projectivization

universe v

section Decomp

variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [Finite V] {F : Type} [Field F]
  [Fintype F] [Fintype (ℙ F (Fin 2 → F))] [DecidableEq (ℙ F (Fin 2 → F))]
  {H T : Subgroup (V ≃ₗ[ZMod 2] V)} {n r : ℕ} {Lc : Fin r → Subgroup (V ≃ₗ[ZMod 2] V)}

theorem split_all (ctx : FamilyCtx H T n F r Lc) (i : Fin r) :
    commGL (Lc i) ⊤ ⊔ fixGL (Lc i) = ⊤ := by
  obtain ⟨A, hA, hLA⟩ := ctx.layer.moving i
  have hmove : ⁅Lc i, A⁆ ≠ ⊥ := by rw [hLA]; exact ctx.hLc.ne_bot i
  obtain ⟨hd, -⟩ := ctx.offd A hA i hmove
  rcases alt_dichotomy ctx hA i hmove with hN | hD
  · exact V_split_natural (by have := ctx.hn; omega) ctx.hF (ctx.α i) (ctx.layer.center_trivial i)
      hN hd.V_split
  · exact V_split_deleted ctx.hF (ctx.α i) (ctx.layer.center_trivial i) hD

omit [Finite V] in
theorem mem_fixGL_biSup {s : Finset (Fin r)} {y : V}
    (h : ∀ j ∈ s, ∀ x ∈ Lc j, x y = y) : y ∈ fixGL (⨆ j ∈ s, Lc j) := by
  intro x hx
  have hle : (⨆ j ∈ s, Lc j) ≤ MulAction.stabilizer (V ≃ₗ[ZMod 2] V) y :=
    iSup₂_le fun j hj z hz => h j hj z hz
  exact hle hx

theorem V_sum_aux (ctx : FamilyCtx H T n F r Lc) (s : Finset (Fin r)) :
    (⨆ i ∈ s, commGL (Lc i) ⊤) ⊔ fixGL (⨆ i ∈ s, Lc i) = ⊤ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [show (⨆ i ∈ (∅ : Finset (Fin r)), Lc i) = ⊥ by simp,
      show (⨆ i ∈ (∅ : Finset (Fin r)), commGL (Lc i) ⊤) = ⊥ by simp, bot_sup_eq]
    exact fixSub_bot _
  | insert a s ha ih =>
    rw [Finset.iSup_insert, Finset.iSup_insert, eq_top_iff]
    intro v _
    have hv : v ∈ (⨆ i ∈ s, commGL (Lc i) ⊤) ⊔ fixGL (⨆ i ∈ s, Lc i) := by rw [ih]; trivial
    obtain ⟨x, hx, c, hc, rfl⟩ := Submodule.mem_sup.1 hv
    have hc' : c ∈ commGL (Lc a) ⊤ ⊔ fixGL (Lc a) := by rw [split_all ctx a]; trivial
    obtain ⟨y, hy, c', hc'', rfl⟩ := Submodule.mem_sup.1 hc'
    have hy_fix : ∀ j ∈ s, ∀ z ∈ Lc j, z y = y := fun j hj z hz =>
      ctx.layer.others_fix a j (fun h => ha (h ▸ hj)) z hz y hy
    have hy' : y ∈ fixGL (⨆ i ∈ s, Lc i) := mem_fixGL_biSup hy_fix
    have hc'fix : c' ∈ fixGL (⨆ i ∈ s, Lc i) := by
      have := (fixGL (⨆ i ∈ s, Lc i)).sub_mem hc hy'
      simpa using this
    have hc'all : c' ∈ fixGL (Lc a ⊔ ⨆ i ∈ s, Lc i) := by
      have h := fixSub_sup (MonoidHom.id (V ≃ₗ[ZMod 2] V)) (Lc a) (⨆ i ∈ s, Lc i)
      have h2 : c' ∈ fixSub (MonoidHom.id (V ≃ₗ[ZMod 2] V)) (Lc a) ⊓
          fixSub (MonoidHom.id (V ≃ₗ[ZMod 2] V)) (⨆ i ∈ s, Lc i) := ⟨hc'', hc'fix⟩
      rw [← h] at h2
      exact h2
    have e : x + (y + c') = (y + x) + c' := by abel
    rw [e]
    exact Submodule.add_mem_sup (Submodule.add_mem_sup hy hx) hc'all

theorem V_sum (ctx : FamilyCtx H T n F r Lc) :
    (⨆ i, commGL (Lc i) ⊤) ⊔ fixGL (oddGen H) = ⊤ := by
  have := V_sum_aux ctx Finset.univ
  simpa [Finset.mem_univ, ctx.layer.K_eq] using this

omit [Finite V] in
theorem sum_direct (ctx : FamilyCtx H T n F r Lc) (x : Fin r → V)
    (hx : ∀ i, x i ∈ commGL (Lc i) ⊤) (hs : ∑ i, x i ∈ fixGL (oddGen H)) (j : Fin r) :
    x j ∈ fixGL (Lc j) := by
  classical
  intro l hl
  have hlK : l ∈ oddGen H := by
    rw [ctx.layer.K_eq]
    exact Subgroup.mem_iSup_of_mem j hl
  have h1 : l (∑ i, x i) = ∑ i, x i := hs l hlK
  rw [map_sum, Fintype.sum_eq_add_sum_compl j (fun i => l (x i)),
    Fintype.sum_eq_add_sum_compl j x] at h1
  have h2 : ∑ i ∈ ({j} : Finset (Fin r))ᶜ, l (x i) = ∑ i ∈ ({j} : Finset (Fin r))ᶜ, x i := by
    refine Finset.sum_congr rfl fun i hi => ?_
    have hij : j ≠ i := fun h => by simp [h] at hi
    exact ctx.layer.others_fix i j hij l hl (x i) (hx i)
  rw [h2] at h1
  exact add_right_cancel h1

omit [Finite V] in
theorem mem_normalizer_oddGen (ctx : FamilyCtx H T n F r Lc) {h : V ≃ₗ[ZMod 2] V} (hh : h ∈ H) :
    h ∈ Subgroup.normalizer (oddGen H : Set (V ≃ₗ[ZMod 2] V)) := by
  have hperm : ∀ g ∈ H, conjSub g (oddGen H) ≤ oddGen H := by
    intro g hg
    rw [ctx.layer.K_eq, OrderIso.map_iSup]
    refine iSup_le fun i => ?_
    obtain ⟨j, hj⟩ := ctx.hLc.perm hg i
    exact (le_of_eq hj).trans (le_iSup Lc j)
  exact mem_normalizer_of_conjSub_le (hperm h hh) (hperm h⁻¹ (H.inv_mem hh))

omit [Finite V] in
theorem H_perm_I (ctx : FamilyCtx H T n F r Lc) {h : V ≃ₗ[ZMod 2] V} (hh : h ∈ H) (i : Fin r) :
    ∃ j, (commGL (Lc i) ⊤).map (h : V →ₗ[ZMod 2] V) = commGL (Lc j) ⊤ := by
  obtain ⟨j, hj⟩ := ctx.hLc.perm hh i
  refine ⟨j, ?_⟩
  rw [← commGL_conjSub]
  exact congrArg (fun X => commGL X ⊤) hj

theorem H_fix_C (ctx : FamilyCtx H T n F r Lc) {h : V ≃ₗ[ZMod 2] V} (hh : h ∈ H) {c : V}
    (hc : c ∈ fixGL (oddGen H)) : h c ∈ fixGL (oddGen H) :=
  (mem_fixSub_map_iff (MonoidHom.id (V ≃ₗ[ZMod 2] V)) (mem_normalizer_oddGen ctx hh) c).2 hc

omit [Finite V] in
theorem I_inf_C (ctx : FamilyCtx H T n F r Lc) (i : Fin r) :
    commGL (Lc i) ⊤ ⊓ fixGL (oddGen H) = commGL (Lc i) ⊤ ⊓ fixGL (Lc i) := by
  apply le_antisymm
  · refine inf_le_inf_left _ (fixSub_anti _ ?_)
    rw [ctx.layer.K_eq]
    exact le_iSup Lc i
  · intro x hx
    refine ⟨hx.1, ?_⟩
    have hle : oddGen H ≤ MulAction.stabilizer (V ≃ₗ[ZMod 2] V) x := by
      rw [ctx.layer.K_eq]
      refine iSup_le fun j z hz => ?_
      by_cases hji : j = i
      · subst hji
        exact hx.2 z hz
      · exact ctx.layer.others_fix i j hji z hz x hx.1
    exact fun z hz => hle hz

theorem K_faithful_VC (ctx : FamilyCtx H T n F r Lc) {x : V ≃ₗ[ZMod 2] V} (hxK : x ∈ oddGen H)
    (hx : x ∈ trivMod (fixGL (oddGen H))) : x = 1 := by
  classical
  have hcommP : Pairwise fun i j => ∀ a b : V ≃ₗ[ZMod 2] V, a ∈ Lc i → b ∈ Lc j → Commute a b :=
    fun i j hij a b ha hb => ctx.hLc.elem_commute hij a ha b hb
  have hkr : x ∈ (Subgroup.noncommPiCoprod hcommP).range := by
    rw [Subgroup.noncommPiCoprod_range, ← ctx.layer.K_eq]
    exact hxK
  obtain ⟨xs, rfl⟩ := hkr
  have hcoord : ∀ j, (xs j : V ≃ₗ[ZMod 2] V) = 1 := by
    intro j
    have hmul := noncommPiCoprod_eq_mul_update Lc hcommP xs j
    have hcj : Subgroup.noncommPiCoprod hcommP (Function.update xs j 1) ∈
        centSub (MonoidHom.id (V ≃ₗ[ZMod 2] V)) (commGL (Lc j) ⊤) := by
      rw [Subgroup.noncommPiCoprod_apply]
      refine Subgroup.noncommProd_mem _ _ fun i _ => ?_
      by_cases hij : i = j
      · subst hij
        simp [Function.update_self]
      · rw [Function.update_of_ne hij]
        intro v hv
        exact ctx.layer.others_fix j i hij _ (xs i).2 v hv
    have hfaith := ctx.layer.faithful_W j (xs j : V ≃ₗ[ZMod 2] V) (xs j).2
    refine hfaith fun v hv => ?_
    have h1 : (Subgroup.noncommPiCoprod hcommP xs) v = (xs j : V ≃ₗ[ZMod 2] V) v := by
      rw [hmul]
      have hcv : (Subgroup.noncommPiCoprod hcommP (Function.update xs j 1)) v = v :=
        mem_centSub.1 hcj v hv
      show (xs j : V ≃ₗ[ZMod 2] V) ((Subgroup.noncommPiCoprod hcommP (Function.update xs j 1)) v) = _
      rw [hcv]
    have h2 : (xs j : V ≃ₗ[ZMod 2] V) v - v ∈ fixGL (oddGen H) := by
      rw [← h1]
      exact hx v
    have h3 : (xs j : V ≃ₗ[ZMod 2] V) v - v ∈ commGL (Lc j) ⊤ :=
      mem_commSub_of (ρ := MonoidHom.id (V ≃ₗ[ZMod 2] V)) (xs j).2 (Submodule.mem_top : v ∈ ⊤)
    have h4 : (xs j : V ≃ₗ[ZMod 2] V) v - v ∈ commGL (Lc j) ⊤ ⊓ fixGL (oddGen H) := ⟨h3, h2⟩
    rw [I_inf_C ctx j] at h4
    exact h4.2
  have hxs : xs = 1 := funext fun j => Subtype.ext (hcoord j)
  rw [hxs, map_one]

theorem faithful_VC (ctx : FamilyCtx H T n F r Lc) {h : V ≃ₗ[ZMod 2] V} (hh : h ∈ H)
    (hf : ∀ v, h v - v ∈ fixGL (oddGen H)) : h = 1 := by
  have hhC : h ∈ trivMod (fixGL (oddGen H)) := hf
  have hcomm : ∀ k ∈ oddGen H, h * k = k * h := by
    intro k hk
    have hkH : k ∈ H := oddGen_le_self H hk
    have hn : h ∈ Subgroup.normalizer (oddGen H : Set (V ≃ₗ[ZMod 2] V)) :=
      mem_normalizer_oddGen ctx hh
    have h1 : h * k * h⁻¹ ∈ oddGen H := (Subgroup.mem_normalizer_iff.1 hn k).1 hk
    have hK : (h * k * h⁻¹) * k⁻¹ ∈ oddGen H :=
      Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hk)
    have hT : h * (k * h⁻¹ * k⁻¹) ∈ trivMod (fixGL (oddGen H)) := by
      refine Subgroup.mul_mem _ hhC ?_
      exact conj_mem_trivMod (fun z hz => H_fix_C ctx hkH hz) (Subgroup.inv_mem _ hhC)
    have e : h * (k * h⁻¹ * k⁻¹) = (h * k * h⁻¹) * k⁻¹ := by group
    rw [e] at hT
    have h2 := K_faithful_VC ctx hK hT
    have h3 : h * k * h⁻¹ = k := by
      have := congrArg (· * k) h2
      simpa using this
    calc h * k = (h * k * h⁻¹) * h := by group
      _ = k * h := by rw [h3]
  have hmem : h ∈ H ⊓ Subgroup.centralizer (oddGen H : Set (V ≃ₗ[ZMod 2] V)) :=
    ⟨hh, Subgroup.mem_centralizer_iff.2 fun k hk => (hcomm k hk).symm⟩
  rw [ctx.layer.centralizer_trivial] at hmem
  exact Subgroup.mem_bot.1 hmem

end Decomp

end CFSG.QuasithinUnique.Setup.Lift
