module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftFamilyDelC
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesAlt5Plane

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open CFSG.QuasithinUnique.Setup.Offender CFSG.QuasithinUnique.Setup.Layer CFSG.QuasithinUnique
  CFSG.Quasithin.B6 CFSG.QuasithinUnique.Setup.SL2Modules
open scoped MatrixGroups LinearAlgebra.Projectivization commutatorElement
open Projectivization

universe v

section Generic

theorem natCard_span_singleton_zmod2 {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] {w : V}
    (hw : w ≠ 0) : Nat.card (Submodule.span (ZMod 2) {w}) = 2 := by
  rw [Nat.card_eq_two_iff]
  refine ⟨0, ⟨w, Submodule.mem_span_singleton_self _⟩, ?_, ?_⟩
  · intro h
    exact hw (congrArg Subtype.val h).symm
  · ext s
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 s.2
    have hz : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
    rcases hz a with rfl | rfl
    · left
      apply Subtype.ext
      simpa using ha.symm
    · right
      apply Subtype.ext
      simpa using ha.symm

theorem natCard_eq_two_of_gen {G : Type*} [Group G] {A' : Subgroup G} {a₁ : G} (ha₁ : a₁ ∈ A')
    (hne : a₁ ≠ 1) (hA' : ∀ a ∈ A', a = 1 ∨ a = a₁) : Nat.card A' = 2 := by
  rw [Nat.card_eq_two_iff]
  refine ⟨1, ⟨a₁, ha₁⟩, ?_, ?_⟩
  · intro h
    exact hne (congrArg Subtype.val h).symm
  · ext g
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    rcases hA' g g.2 with h | h
    · left; exact Subtype.ext h
    · right; exact Subtype.ext h

theorem ker_sub_id_eq_fixGL {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    {A' : Subgroup (V ≃ₗ[ZMod 2] V)} {a₁ : V ≃ₗ[ZMod 2] V} (ha₁ : a₁ ∈ A')
    (hA' : ∀ a ∈ A', a = 1 ∨ a = a₁) :
    LinearMap.ker ((a₁ : V →ₗ[ZMod 2] V) - LinearMap.id) = fixGL A' := by
  ext v
  rw [LinearMap.mem_ker]
  show a₁ v - v = 0 ↔ v ∈ fixGL A'
  constructor
  · intro hv g hg
    rcases hA' g hg with rfl | rfl
    · rfl
    · exact sub_eq_zero.1 hv
  · intro hv
    have h1 : a₁ v = v := hv a₁ ha₁
    show a₁ v - v = 0
    rw [h1, sub_self]

end Generic

section Weight

variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [Finite V] {F : Type} [Field F]
  [Fintype F] [Fintype (ℙ F (Fin 2 → F))] [DecidableEq (ℙ F (Fin 2 → F))]
  {H T : Subgroup (V ≃ₗ[ZMod 2] V)} {n r : ℕ} {Lc : Fin r → Subgroup (V ≃ₗ[ZMod 2] V)}
  {ctx : FamilyCtx H T n F r Lc} {i : Fin r}

omit [Finite V] in
theorem weight_eq_of_mem (ctx : FamilyCtx H T n F r Lc) {A : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hA : IsMinOffender H A) : weight (MonoidHom.id (V ≃ₗ[ZMod 2] V)) A = Nat.card V := by
  obtain ⟨-, j, -, -, -, -, -, -, -, hw, -⟩ := ctx.layer.offender A hA
  exact hw

theorem exists_third_point {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (h5 : Fintype.card Ω = 5)
    (x y : Ω) : ∃ ω : Ω, ω ≠ x ∧ ω ≠ y := by
  by_contra hcon
  push Not at hcon
  have hsub : (Finset.univ : Finset Ω) ⊆ {x, y} := by
    intro z _
    by_cases hzx : z = x
    · simp [hzx]
    · simp [hcon z hzx]
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_univ, h5] at h1
  have h2 := Finset.card_le_two (a := x) (b := y)
  omega

omit [Finite V] in
theorem DelModel.range_transposition (M : DelModel ctx i)
    (h5 : Fintype.card (ℙ F (Fin 2 → F)) = 5) {x y : ℙ F (Fin 2 → F)} (hxy : x ≠ y)
    {a₁ : V ≃ₗ[ZMod 2] V} (hB₁ : a₁ ∈ blockB H (Lc i)) (hψ₁ : M.ψ ⟨a₁, hB₁⟩ = Equiv.swap x y)
    (hV : commGL (Lc i) ⊤ ⊔ LinearMap.ker ((a₁ : V →ₗ[ZMod 2] V) - LinearMap.id) = ⊤) :
    ∃ w₀ : ↥(commGL (Lc i) ⊤), (w₀ : V) ≠ 0 ∧
      (∀ (u u' : ↥(commGL (Lc i) ⊤)), (u' : V) = a₁ (u : V) →
        u' - u = ((((M.β u : ↥(SL2Modules.evenWeight (ℙ F (Fin 2 → F)))) :
            ℙ F (Fin 2 → F) → ZMod 2) x +
          ((M.β u : ↥(SL2Modules.evenWeight (ℙ F (Fin 2 → F)))) :
            ℙ F (Fin 2 → F) → ZMod 2) y)) • w₀) ∧
      LinearMap.range ((a₁ : V →ₗ[ZMod 2] V) - LinearMap.id) =
        Submodule.span (ZMod 2) {(w₀ : V)} := by
  classical
  let _ : AddCommGroup (ZMod 2) := zmod2AddCommGroup
  let D : V →ₗ[ZMod 2] V := (a₁ : V →ₗ[ZMod 2] V) - LinearMap.id
  have hDapp : ∀ v, D v = a₁ v - v := fun v => rfl
  obtain ⟨ω, hωx, hωy⟩ := exists_third_point h5 x y
  let w₀ : ↥(commGL (Lc i) ⊤) := M.β.symm (pairVec x y)
  have hcompat1 : ∀ (u u' : ↥(commGL (Lc i) ⊤)), (u' : V) = a₁ (u : V) →
      u' - u = ((((M.β u : ↥(SL2Modules.evenWeight (ℙ F (Fin 2 → F)))) :
          ℙ F (Fin 2 → F) → ZMod 2) x +
        ((M.β u : ↥(SL2Modules.evenWeight (ℙ F (Fin 2 → F)))) :
          ℙ F (Fin 2 → F) → ZMod 2) y)) • w₀ := by
    intro u u' hu'
    have h1 := M.compat ⟨a₁, hB₁⟩ u u' hu'
    rw [hψ₁] at h1
    apply M.β.injective
    rw [map_sub, map_smul]
    have hβw₀ : M.β w₀ = pairVec x y := M.β.apply_symm_apply _
    rw [hβw₀]
    have hu'β : M.β u' = (permU (Equiv.swap x y)).val (M.β u) := Subtype.ext h1
    rw [hu'β, sub_eq_add_neg, ZModModule.neg_eq_self]
    exact swap_add_one_apply hxy (M.β u)
  have hrange : LinearMap.range D = Submodule.span (ZMod 2) {(w₀ : V)} := by
    apply le_antisymm
    · rintro _ ⟨v, rfl⟩
      have hv : v ∈ commGL (Lc i) ⊤ ⊔ LinearMap.ker D := by rw [hV]; trivial
      obtain ⟨u, hu, f, hf, rfl⟩ := Submodule.mem_sup.1 hv
      have hDf : D f = 0 := LinearMap.mem_ker.1 hf
      rw [map_add, hDf, add_zero]
      have hu' : a₁ u ∈ commGL (Lc i) ⊤ := blockB_isInvariant ctx i a₁ hB₁ u hu
      have h2 := congrArg Subtype.val (hcompat1 ⟨u, hu⟩ ⟨a₁ u, hu'⟩ rfl)
      rw [Submodule.coe_sub, Submodule.coe_smul] at h2
      exact Submodule.mem_span_singleton.2 ⟨_, h2.symm⟩
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      let u₀ : ↥(commGL (Lc i) ⊤) := M.β.symm (pairVec x ω)
      have hu₀' : a₁ (u₀ : V) ∈ commGL (Lc i) ⊤ := blockB_isInvariant ctx i a₁ hB₁ u₀ u₀.2
      have h2 := hcompat1 u₀ ⟨a₁ u₀, hu₀'⟩ rfl
      have hβu₀ : M.β u₀ = pairVec x ω := M.β.apply_symm_apply _
      have hc : (((M.β u₀ : ↥(SL2Modules.evenWeight (ℙ F (Fin 2 → F)))) :
          ℙ F (Fin 2 → F) → ZMod 2) x +
          ((M.β u₀ : ↥(SL2Modules.evenWeight (ℙ F (Fin 2 → F)))) :
            ℙ F (Fin 2 → F) → ZMod 2) y) = 1 := by
        rw [hβu₀, pairVec_apply, pairVec_apply]
        simp [hωx.symm, hxy.symm, hωy.symm]
      rw [hc, one_smul] at h2
      refine ⟨(u₀ : V), ?_⟩
      have h3 := congrArg Subtype.val h2
      rw [Submodule.coe_sub] at h3
      exact h3
  have hw₀ : (w₀ : V) ≠ 0 := by
    intro h
    have h1 : w₀ = 0 := Subtype.ext h
    have h2 : pairVec x y = 0 := by
      have := congrArg M.β h1
      rw [map_zero] at this
      exact (M.β.apply_symm_apply _).symm.trans this
    have h3 := congrArg (fun v : ↥(SL2Modules.evenWeight (ℙ F (Fin 2 → F))) =>
      (v : ℙ F (Fin 2 → F) → ZMod 2) x) h2
    simp [pairVec_apply, hxy] at h3
  exact ⟨w₀, hw₀, hcompat1, hrange⟩

omit [Finite V] in
theorem DelModel.sup_ker_eq_top (M : DelModel ctx i)
    (h5 : Fintype.card (ℙ F (Fin 2 → F)) = 5) {x y : ℙ F (Fin 2 → F)} (hxy : x ≠ y)
    {a₁ : V ≃ₗ[ZMod 2] V} (hB₁ : a₁ ∈ blockB H (Lc i)) (hψ₁ : M.ψ ⟨a₁, hB₁⟩ = Equiv.swap x y)
    (hV : commGL (Lc i) ⊤ ⊔ LinearMap.ker ((a₁ : V →ₗ[ZMod 2] V) - LinearMap.id) = ⊤)
    {W : Submodule (ZMod 2) V} (hW : ∃ w ∈ W, a₁ w ≠ w) :
    W ⊔ LinearMap.ker ((a₁ : V →ₗ[ZMod 2] V) - LinearMap.id) = ⊤ := by
  classical
  obtain ⟨w₀, hw₀, -, hrange⟩ := M.range_transposition h5 hxy hB₁ hψ₁ hV
  obtain ⟨w, hwW, hw⟩ := hW
  let D : V →ₗ[ZMod 2] V := (a₁ : V →ₗ[ZMod 2] V) - LinearMap.id
  have hz : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  have hDw : D w ≠ 0 := fun h => hw (sub_eq_zero.1 h)
  have hDw_mem : D w ∈ Submodule.span (ZMod 2) {(w₀ : V)} := by
    rw [← hrange]
    exact ⟨w, rfl⟩
  obtain ⟨c₁, hc₁⟩ := Submodule.mem_span_singleton.1 hDw_mem
  have hc₁1 : c₁ = 1 := by
    rcases hz c₁ with h | h
    · exfalso
      apply hDw
      rw [← hc₁, h, zero_smul]
    · exact h
  rw [eq_top_iff]
  intro v _
  have hDv_mem : D v ∈ Submodule.span (ZMod 2) {(w₀ : V)} := by
    rw [← hrange]
    exact ⟨v, rfl⟩
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hDv_mem
  rcases hz c with h | h
  · rw [h, zero_smul] at hc
    exact Submodule.mem_sup_right (LinearMap.mem_ker.2 hc.symm)
  · rw [h, one_smul] at hc
    rw [hc₁1, one_smul] at hc₁
    have hker : v - w ∈ LinearMap.ker D := by
      rw [LinearMap.mem_ker, map_sub, ← hc, hc₁, sub_self]
    have e : v = w + (v - w) := by abel
    rw [e]
    exact Submodule.add_mem_sup hwW hker

omit [Finite V] in
theorem DelModel.weight_transposition (M : DelModel ctx i) {A : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hA : IsMinOffender H A) (hmove : ⁅Lc i, A⁆ ≠ ⊥)
    (h5 : Fintype.card (ℙ F (Fin 2 → F)) = 5) {x y : ℙ F (Fin 2 → F)} (hxy : x ≠ y)
    {A' : Subgroup (V ≃ₗ[ZMod 2] V)} (hA'A : A' ≤ A) {a₁ : V ≃ₗ[ZMod 2] V} (ha₁ : a₁ ∈ A')
    (hB₁ : a₁ ∈ blockB H (Lc i)) (hψ₁ : M.ψ ⟨a₁, hB₁⟩ = Equiv.swap x y)
    (hA' : ∀ a ∈ A', a = 1 ∨ a = a₁) :
    weight (MonoidHom.id (V ≃ₗ[ZMod 2] V)) A' = Nat.card V := by
  classical
  obtain ⟨hd, -⟩ := ctx.offd A hA i hmove
  have hVsplit : commGL (Lc i) ⊤ ⊔ fixGL A = ⊤ := hd.V_split
  have hkerD := ker_sub_id_eq_fixGL ha₁ hA'
  have hV : commGL (Lc i) ⊤ ⊔ LinearMap.ker ((a₁ : V →ₗ[ZMod 2] V) - LinearMap.id) = ⊤ := by
    rw [eq_top_iff]
    calc (⊤ : Submodule (ZMod 2) V) = commGL (Lc i) ⊤ ⊔ fixGL A := hVsplit.symm
      _ ≤ commGL (Lc i) ⊤ ⊔ fixGL A' :=
        sup_le_sup_left (fixSub_anti (MonoidHom.id (V ≃ₗ[ZMod 2] V)) hA'A) _
      _ = commGL (Lc i) ⊤ ⊔ LinearMap.ker ((a₁ : V →ₗ[ZMod 2] V) - LinearMap.id) := by
        rw [hkerD]
  obtain ⟨w₀, hw₀, -, hrange⟩ := M.range_transposition h5 hxy hB₁ hψ₁ hV
  have hcard2 := natCard_span_singleton_zmod2 hw₀
  have hne : a₁ ≠ 1 := by
    intro h1
    have h2 : M.ψ ⟨a₁, hB₁⟩ = 1 := by
      have e : (⟨a₁, hB₁⟩ : ↥(blockB H (Lc i))) = 1 := Subtype.ext h1
      rw [e, map_one]
    rw [hψ₁] at h2
    exact swap_ne_one hxy h2
  have hcardA' := natCard_eq_two_of_gen ha₁ hne hA'
  have hmul := natCard_eq_ker_mul_range ((a₁ : V →ₗ[ZMod 2] V) - LinearMap.id)
  rw [hrange, hcard2, hkerD] at hmul
  show Nat.card A' * Nat.card (fixSub (MonoidHom.id (V ≃ₗ[ZMod 2] V)) A') = Nat.card V
  rw [hcardA', hmul]
  ring

end Weight

end CFSG.QuasithinUnique.Setup.Lift
