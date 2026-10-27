module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftFamilyDelD
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftFamilyNatFam

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open CFSG.QuasithinUnique.Setup.Offender CFSG.QuasithinUnique.Setup.Layer CFSG.QuasithinUnique
  CFSG.Quasithin.B6 CFSG.QuasithinUnique.Setup.SL2Modules
open scoped MatrixGroups LinearAlgebra.Projectivization commutatorElement
open Projectivization

universe v

section Transp2

variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [Finite V] {F : Type} [Field F]
  [Fintype F] [Fintype (ℙ F (Fin 2 → F))] [DecidableEq (ℙ F (Fin 2 → F))]
  {H T : Subgroup (V ≃ₗ[ZMod 2] V)} {n r : ℕ} {Lc : Fin r → Subgroup (V ≃ₗ[ZMod 2] V)}
  {ctx : FamilyCtx H T n F r Lc} {i : Fin r}

omit [Finite V] in
theorem DelModel.not_double_transposition (M : DelModel ctx i) {A : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hA : IsMinOffender H A) (hmove : ⁅Lc i, A⁆ ≠ ⊥)
    (h5 : Fintype.card (ℙ F (Fin 2 → F)) = 5) {x y z t : ℙ F (Fin 2 → F)} (hxy : x ≠ y)
    (hxz : x ≠ z) (hyz : y ≠ z) (hzt : z ≠ t)
    (h : (A.subgroupOf (blockB H (Lc i))).map M.ψ.toMonoidHom =
      Subgroup.closure {Equiv.swap x y, Equiv.swap z t}) : False := by
  classical
  have hs1 : Equiv.swap x y ∈ (A.subgroupOf (blockB H (Lc i))).map M.ψ.toMonoidHom := by
    rw [h]
    exact Subgroup.subset_closure (by simp)
  have hs2 : Equiv.swap z t ∈ (A.subgroupOf (blockB H (Lc i))).map M.ψ.toMonoidHom := by
    rw [h]
    exact Subgroup.subset_closure (by simp)
  obtain ⟨b₁, hb₁A, hb₁⟩ := hs1
  obtain ⟨b₂, hb₂A, hb₂⟩ := hs2
  have hb₁A' : (b₁ : V ≃ₗ[ZMod 2] V) ∈ A := hb₁A
  have hb₂A' : (b₂ : V ≃ₗ[ZMod 2] V) ∈ A := hb₂A
  have hb₁' : M.ψ b₁ = Equiv.swap x y := hb₁
  have hb₂' : M.ψ b₂ = Equiv.swap z t := hb₂
  obtain ⟨A', hA'def⟩ : ∃ A' : Subgroup (V ≃ₗ[ZMod 2] V), A' = A ⊓
      ((Subgroup.closure {Equiv.swap x y}).comap M.ψ.toMonoidHom).map
        (blockB H (Lc i)).subtype := ⟨_, rfl⟩
  have hmemA' : ∀ a, a ∈ A' ↔ a ∈ A ∧ ∃ b : ↥(blockB H (Lc i)),
      M.ψ b ∈ Subgroup.closure {Equiv.swap x y} ∧ (b : V ≃ₗ[ZMod 2] V) = a := by
    intro a
    rw [hA'def]
    constructor
    · rintro ⟨ha, b, hb, rfl⟩
      exact ⟨ha, b, hb, rfl⟩
    · rintro ⟨ha, b, hb, rfl⟩
      exact ⟨ha, b, hb, rfl⟩
  have hA'A : A' ≤ A := fun a ha => ((hmemA' a).1 ha).1
  have hA'1 : ∀ a ∈ A', a = 1 ∨ a = (b₁ : V ≃ₗ[ZMod 2] V) := by
    intro a ha
    obtain ⟨-, b, hb, rfl⟩ := (hmemA' a).1 ha
    rcases (mem_closure_swap _).1 hb with h1 | h1
    · left
      have : b = 1 := M.ψ.injective (by rw [h1, map_one])
      rw [this]
      rfl
    · right
      have : b = b₁ := M.ψ.injective (by rw [h1, hb₁'])
      rw [this]
  have hb₁mem : (b₁ : V ≃ₗ[ZMod 2] V) ∈ A' :=
    (hmemA' _).2 ⟨hb₁A', b₁, by rw [hb₁']; exact Subgroup.subset_closure (Set.mem_singleton _), rfl⟩
  have hweight := M.weight_transposition hA hmove h5 hxy hA'A hb₁mem b₁.2 hb₁' hA'1
  have hne : A' ≠ ⊥ := by
    intro hbot
    have h1 : (b₁ : V ≃ₗ[ZMod 2] V) ∈ A' := hb₁mem
    rw [hbot, Subgroup.mem_bot] at h1
    have h2 : b₁ = 1 := Subtype.ext h1
    rw [h2, map_one] at hb₁'
    exact swap_ne_one hxy hb₁'.symm
  have hlt : A' < A := by
    refine lt_of_le_of_ne hA'A ?_
    intro heq
    have h2 : (b₂ : V ≃ₗ[ZMod 2] V) ∈ A' := by rw [heq]; exact hb₂A'
    obtain ⟨-, b, hb, hbb⟩ := (hmemA' _).1 h2
    have hbb2 : b = b₂ := Subtype.ext hbb
    rw [hbb2, hb₂'] at hb
    rcases (mem_closure_swap _).1 hb with h1 | h1
    · exact swap_ne_one hzt h1
    · have h3 := congrArg (fun π : Equiv.Perm (ℙ F (Fin 2 → F)) => π z) h1
      simp only [Equiv.swap_apply_left,
        Equiv.swap_apply_of_ne_of_ne hxz.symm hyz.symm] at h3
      exact hzt h3.symm
  have hw := hA.2.2.2.2 A' (bot_lt_iff_ne_bot.2 hne) hlt
  rw [hweight, weight_eq_of_mem ctx hA] at hw
  exact lt_irrefl _ hw

theorem DelModel.single_transposition (M : DelModel ctx i)
    (hdel : ∀ A, IsMinOffender H A → ∀ i, ⁅Lc i, A⁆ ≠ ⊥ → DelData n (Lc i) A (ctx.α i))
    {A : Subgroup (V ≃ₗ[ZMod 2] V)} (hA : IsMinOffender H A) (hmove : ⁅Lc i, A⁆ ≠ ⊥)
    (h5 : Fintype.card (ℙ F (Fin 2 → F)) = 5) :
    ∃ x y : ℙ F (Fin 2 → F), x ≠ y ∧
      (A.subgroupOf (blockB H (Lc i))).map M.ψ.toMonoidHom = Subgroup.closure {Equiv.swap x y} := by
  obtain ⟨-, -, -, β, ψA, -, hψAL, -, hshape⟩ := hdel A hA i hmove
  have hmap := M.map_agree hA hmove h5 ψA hψAL
  rcases hshape with ⟨x, y, hxy, h⟩ | ⟨x, y, z, t, hxy, hxz, hxt, hyz, hyt, hzt, h⟩
  · exact ⟨x, y, hxy, hmap.trans h⟩
  · exact (M.not_double_transposition hA hmove h5 hxy hxz hyz hzt (hmap.trans h)).elim

omit [Finite V] in
theorem DelModel.mem_iff_image (M : DelModel ctx i) {X : Subgroup (V ≃ₗ[ZMod 2] V)}
    {K : Subgroup (Equiv.Perm (ℙ F (Fin 2 → F)))}
    (h : (X.subgroupOf (blockB H (Lc i))).map M.ψ.toMonoidHom = K) (b : ↥(blockB H (Lc i))) :
    (b : V ≃ₗ[ZMod 2] V) ∈ X ↔ M.ψ b ∈ K := by
  constructor
  · intro hb
    rw [← h]
    exact ⟨b, hb, rfl⟩
  · intro hb
    rw [← h] at hb
    obtain ⟨b', hb', hψ⟩ := hb
    have hbb : b' = b := M.ψ.injective hψ
    rw [← hbb]
    exact hb'

theorem DelModel.isMinOffender_of_transposition (M : DelModel ctx i)
    (hdel : ∀ A, IsMinOffender H A → ∀ i, ⁅Lc i, A⁆ ≠ ⊥ → DelData n (Lc i) A (ctx.α i))
    (h5 : Fintype.card (ℙ F (Fin 2 → F)) = 5) {A : Subgroup (V ≃ₗ[ZMod 2] V)}
    {x y : ℙ F (Fin 2 → F)} (hxy : x ≠ y) (hAB : A ≤ blockB H (Lc i))
    (h : (A.subgroupOf (blockB H (Lc i))).map M.ψ.toMonoidHom = Subgroup.closure {Equiv.swap x y}) :
    IsMinOffender H A ∧ ⁅Lc i, A⁆ ≠ ⊥ := by
  classical
  obtain ⟨A₀, hA₀, hLA₀⟩ := ctx.layer.moving i
  have hmove₀ : ⁅Lc i, A₀⁆ ≠ ⊥ := by rw [hLA₀]; exact ctx.hLc.ne_bot i
  obtain ⟨x₀, y₀, hxy₀, h₀⟩ := M.single_transposition hdel hA₀ hmove₀ h5
  obtain ⟨σ, hσ, hσx, hσy⟩ := alt_two_transitive h5 hxy₀ hxy
  rw [← M.alt] at hσ
  obtain ⟨l, hl, hlσ⟩ := hσ
  have hl' : (l : V ≃ₗ[ZMod 2] V) ∈ Lc i := hl
  have hlH : (l : V ≃ₗ[ZMod 2] V) ∈ H := (ctx.hLc.isComp i).1 hl'
  have hψl : M.ψ l = σ := hlσ
  have hlB : (l : V ≃ₗ[ZMod 2] V) ∈ blockB H (Lc i) := l.2
  have hA₀B : A₀ ≤ blockB H (Lc i) := le_blockB_gen hA₀ hmove₀
  have hsw1 : σ⁻¹ * Equiv.swap x y * σ = Equiv.swap x₀ y₀ := by
    have e := Equiv.swap_apply_apply σ⁻¹ x y
    rw [Equiv.Perm.inv_eq_iff_eq.2 hσx.symm, Equiv.Perm.inv_eq_iff_eq.2 hσy.symm, inv_inv] at e
    exact e.symm
  have hsw2 : σ * Equiv.swap x₀ y₀ * σ⁻¹ = Equiv.swap x y := by
    have e := Equiv.swap_apply_apply σ x₀ y₀
    rw [hσx, hσy] at e
    exact e.symm
  have hconj : A = conjSub (l : V ≃ₗ[ZMod 2] V) A₀ := by
    ext a
    constructor
    · intro ha
      have haB : a ∈ blockB H (Lc i) := hAB ha
      rw [mem_conjSub]
      have hb'B : (l : V ≃ₗ[ZMod 2] V)⁻¹ * a * l ∈ blockB H (Lc i) :=
        Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hlB) haB) hlB
      have h1 := (M.mem_iff_image h ⟨a, haB⟩).1 ha
      refine (M.mem_iff_image h₀ ⟨_, hb'B⟩).2 ?_
      have e : M.ψ ⟨(l : V ≃ₗ[ZMod 2] V)⁻¹ * a * l, hb'B⟩ = σ⁻¹ * M.ψ ⟨a, haB⟩ * σ := by
        have hh : (⟨(l : V ≃ₗ[ZMod 2] V)⁻¹ * a * l, hb'B⟩ : ↥(blockB H (Lc i))) =
            l⁻¹ * ⟨a, haB⟩ * l := Subtype.ext rfl
        rw [hh, map_mul, map_mul, map_inv, hψl]
      rw [e]
      rcases (mem_closure_swap _).1 h1 with h2 | h2
      · rw [h2, mul_one, inv_mul_cancel]
        exact Subgroup.one_mem _
      · rw [h2, hsw1]
        exact Subgroup.subset_closure (Set.mem_singleton _)
    · intro ha
      rw [mem_conjSub] at ha
      have hb'B : (l : V ≃ₗ[ZMod 2] V)⁻¹ * a * l ∈ blockB H (Lc i) := hA₀B ha
      have haB : a ∈ blockB H (Lc i) := by
        have hh : a = (l : V ≃ₗ[ZMod 2] V) * ((l : V ≃ₗ[ZMod 2] V)⁻¹ * a * l) *
            (l : V ≃ₗ[ZMod 2] V)⁻¹ := by group
        rw [hh]
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hlB hb'B) (Subgroup.inv_mem _ hlB)
      refine (M.mem_iff_image h ⟨a, haB⟩).2 ?_
      have h1 := (M.mem_iff_image h₀ ⟨_, hb'B⟩).1 ha
      have e : M.ψ ⟨a, haB⟩ = σ * M.ψ ⟨(l : V ≃ₗ[ZMod 2] V)⁻¹ * a * l, hb'B⟩ * σ⁻¹ := by
        have hh : (⟨a, haB⟩ : ↥(blockB H (Lc i))) =
            l * ⟨(l : V ≃ₗ[ZMod 2] V)⁻¹ * a * l, hb'B⟩ * l⁻¹ := Subtype.ext (by
          show a = (l : V ≃ₗ[ZMod 2] V) * ((l : V ≃ₗ[ZMod 2] V)⁻¹ * a * l) *
            (l : V ≃ₗ[ZMod 2] V)⁻¹
          group)
        rw [hh, map_mul, map_mul, map_inv, hψl]
      rw [e]
      rcases (mem_closure_swap _).1 h1 with h2 | h2
      · rw [h2, mul_one, mul_inv_cancel]
        exact Subgroup.one_mem _
      · rw [h2, hsw2]
        exact Subgroup.subset_closure (Set.mem_singleton _)
  rw [hconj]
  exact ⟨hA₀.conj hlH, conj_comm_moves hl' hmove₀⟩

end Transp2

end CFSG.QuasithinUnique.Setup.Lift
