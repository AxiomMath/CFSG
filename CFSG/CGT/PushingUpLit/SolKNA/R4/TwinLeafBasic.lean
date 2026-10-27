module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSmallMain

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf

open CFSG CFSG.Open CFSG.ClassicalInvolution
open CFSG.CGT.PushingUpLit.SolKNA.R4 CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSmall
open QuaternionGroup

theorem embedsAut_mulAut (F : Type) [Group F] : EmbedsAut F (MulAut F) := by
  intro Y _ N _ ⟨e⟩ hC
  have hg : Function.Injective (MulAut.conjNormal : Y →* MulAut ↥N) := by
    rw [injective_iff_map_eq_one]
    intro y hy
    have h1 : y ∈ Subgroup.centralizer (N : Set Y) := by
      rw [Subgroup.mem_centralizer_iff]
      intro m hm
      have := congrArg (fun α : MulAut ↥N => ((α ⟨m, hm⟩ : ↥N) : Y)) hy
      simp only [MulAut.conjNormal_apply, MulAut.one_apply] at this
      calc m * y = (y * m * y⁻¹) * y := by rw [this]
        _ = y * m := by group
    rw [hC, Subgroup.mem_bot] at h1
    exact h1
  exact ⟨(MulAut.congr e).toMonoidHom.comp (MulAut.conjNormal : Y →* MulAut ↥N),
    (MulAut.congr e).injective.comp hg⟩

@[expose] def Q16Q16 {G : Type*} [Group G] (x y x' y' : G) : Prop :=
  Q16Pair x y ∧ Q16Pair x' y' ∧ x ^ 4 = x' ^ 4 ∧ x * x' = x' * x ∧ x * y' = y' * x ∧
    y * x' = x' * y ∧ y * y' = y' * y

@[expose] def NoQ16Q16 (G : Type*) [Group G] : Prop := ∀ x y x' y' : G, ¬ Q16Q16 x y x' y'

theorem Q16Q16.map {G H : Type*} [Group G] [Group H] (f : G →* H) (hf : Function.Injective f)
    {x y x' y' : G} (h : Q16Q16 x y x' y') : Q16Q16 (f x) (f y) (f x') (f y') := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨h1.map f hf, h2.map f hf, by rw [← map_pow, ← map_pow, h3], ?_, ?_, ?_, ?_⟩ <;>
    simp only [← map_mul, h4, h5, h6, h7]

theorem NoQ16Q16.of_injective {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Injective f) (h : NoQ16Q16 H) : NoQ16Q16 G :=
  fun x y x' y' hxy => h (f x) (f y) (f x') (f y') (hxy.map f hf)

theorem exists_q16Pair_mem {G : Type*} [Group G] {P : Subgroup G} {r : ℕ} (hr : 4 ≤ r)
    (e : ↥P ≃* QuaternionGroup (2 ^ (r - 2))) : ∃ x ∈ P, ∃ y ∈ P, Q16Pair x y := by
  obtain ⟨m, hm0, hm⟩ : ∃ m : ℕ, 0 < m ∧ 2 ^ (r - 2) = 4 * m :=
    ⟨2 ^ (r - 4), by positivity, by rw [show r - 2 = (r - 4) + 2 by omega, pow_add]; ring⟩
  let ι : QuaternionGroup (2 ^ (r - 2)) →* G := P.subtype.comp e.symm.toMonoidHom
  have hι : Function.Injective ι :=
    Subtype.val_injective.comp e.symm.injective
  have := (quaternionGroup_q16Pair (n := 2 ^ (r - 2)) hm0 hm).map ι hι
  exact ⟨_, (e.symm _).2, _, (e.symm _).2, this⟩

theorem twinLeafR_of_noQ16Aut {r n : ℕ} (hr : 4 ≤ r) {P : ∀ (F : Type) [Group F], Prop}
    (h : ∀ (F : Type) [Group F], P F → NoQ16 (MulAut F)) : TwinLeafR r n P :=
  twinLeafR_of_noQ16 hr fun F _ hF => ⟨MulAut F, inferInstance, embedsAut_mulAut F, h F hF⟩

end CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf
