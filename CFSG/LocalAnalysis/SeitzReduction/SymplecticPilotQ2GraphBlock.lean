module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2GraphTwist
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SixRevCommBasic
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2GraphPlane

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear mem_blockSpecialLinear)
open CFSG.LocalAnalysis.ComponentInitial
open scoped MatrixGroups

variable {N ε : ℕ} {K : Type} [Field K]

theorem nonempty_q2Block_mulEquiv (hK : Nat.card K = 2) (R : Finset (Fin N)) :
    Nonempty (q2Block ε K R ≃*
      LinearFlag.projectiveSL ((planeCoordsQ2 ε R)ᶜ.card) K) := by
  set S : Finset (Fin (2 * N + ε)) := (planeCoordsQ2 ε R)ᶜ with hS
  have e1 : SpecialLinearGroup S K ≃* q2Block ε K R :=
    (MonoidHom.ofInjective (LinearPilot.blockEmbed_injective S)).trans
      (MulEquiv.subgroupCongr (LinearPilot.range_blockEmbed S))
  have e2 : SpecialLinearGroup S K ≃* SpecialLinearGroup (Fin S.card) K :=
    LinearPilot.reindexSpecialLinear S.equivFin
  have e3 : SpecialLinearGroup (Fin S.card) K ≃* LinearFlag.projectiveSL S.card K :=
    MulEquiv.ofBijective (LinearFlag.proj S.card K)
      ⟨LinearPilot.proj_injective_of_card_two hK, LinearFlag.proj_surjective S.card K⟩
  exact ⟨(e1.symm.trans e2).trans e3⟩

variable (ε) in
@[expose] noncomputable def q2GraphBlock [CharP K 2] (hK : Nat.card K = 2) (R : Finset (Fin N)) :
    MulAut (q2Block ε K R) where
  toFun x := ⟨q2Graph (N := N) ε hK (x : SpecialLinearGroup (Fin (2 * N + ε)) K),
    q2Graph_mem_q2Block hK x.2⟩
  invFun x := ⟨q2Graph (N := N) ε hK (x : SpecialLinearGroup (Fin (2 * N + ε)) K),
    q2Graph_mem_q2Block hK x.2⟩
  left_inv x := Subtype.ext (by
    change q2Graph (N := N) ε hK (q2Graph ε hK (x : SpecialLinearGroup (Fin (2 * N + ε)) K)) = x
    rw [← MulAut.mul_apply, q2Graph_mul_self, MulAut.one_apply])
  right_inv x := Subtype.ext (by
    change q2Graph (N := N) ε hK (q2Graph ε hK (x : SpecialLinearGroup (Fin (2 * N + ε)) K)) = x
    rw [← MulAut.mul_apply, q2Graph_mul_self, MulAut.one_apply])
  map_mul' x y := Subtype.ext (map_mul (q2Graph (N := N) ε hK)
    (x : SpecialLinearGroup (Fin (2 * N + ε)) K) y)

theorem coe_q2GraphBlock [CharP K 2] (hK : Nat.card K = 2) {R : Finset (Fin N)}
    (x : q2Block ε K R) : ((q2GraphBlock ε hK R x : q2Block ε K R) :
      SpecialLinearGroup (Fin (2 * N + ε)) K) =
        q2Graph ε hK (x : SpecialLinearGroup (Fin (2 * N + ε)) K) := rfl

variable (ε K) in
@[expose] noncomputable def q2SpBlock (hK : Nat.card K = 2) (R : Finset (Fin N)) :
    Subgroup (q2Block ε K R) :=
  ((spBlock K Rᶜ).map (q2Embed ε hK)).subgroupOf (q2Block ε K R)

theorem mem_q2SpBlock (hK : Nat.card K = 2) {R : Finset (Fin N)} {x : q2Block ε K R} :
    x ∈ q2SpBlock ε K hK R ↔ ∃ y ∈ spBlock K Rᶜ, q2Embed ε hK y = x :=
  Iff.rfl

theorem q2GraphBlock_fix [CharP K 2] (hK : Nat.card K = 2) {R : Finset (Fin N)}
    {x : q2Block ε K R} (hx : x ∈ q2SpBlock ε K hK R) : q2GraphBlock ε hK R x = x := by
  obtain ⟨y, -, hy⟩ := (mem_q2SpBlock hK).1 hx
  apply Subtype.ext
  rw [coe_q2GraphBlock, ← hy, q2Graph_q2Embed]

theorem eq_one_of_commute_q2SpBlock [CharP K 2] (hK : Nat.card K = 2) (hε : ε ≤ 1)
    {R : Finset (Fin N)} (a : q2Block ε K R)
    (ha : ∀ s ∈ q2SpBlock ε K hK R, a * s = s * a) : a = 1 := by
  apply Subtype.ext
  refine eq_one_of_commute_q2Embed hK hε a.2 fun y hy => ?_
  have hs : (⟨q2Embed ε hK y, (q2Embed_mem_q2Block_iff hK).2 hy⟩ : q2Block ε K R) ∈
      q2SpBlock ε K hK R := (mem_q2SpBlock hK).2 ⟨y, hy, rfl⟩
  exact congrArg Subtype.val (ha _ hs)

theorem q2Transvection_one_mul_self [CharP K 2] {n : ℕ} {a b : Fin n} (hab : a ≠ b) :
    SpecialLinearGroup.transvection hab (1 : K) * SpecialLinearGroup.transvection hab 1 = 1 := by
  apply Subtype.ext
  change Matrix.transvection a b (1 : K) * Matrix.transvection a b 1 = 1
  rw [Matrix.transvection_mul_transvection_same a b hab (1 : K) 1, CharTwo.add_self_eq_zero,
    Matrix.transvection_zero]

theorem q2Graph_transvection_ne [CharP K 2] (hK : Nat.card K = 2) {p p' : Fin N} (hpp : p ≠ p') :
    q2Graph ε hK (SpecialLinearGroup.transvection (show q2Coord N ε (Sum.inl (Sum.inl p)) ≠
      q2Coord N ε (Sum.inl (Sum.inl p')) from fun h => hpp (Sum.inl.inj (Sum.inl.inj
        ((q2Coord N ε).injective h)))) (1 : K)) ≠
      SpecialLinearGroup.transvection (show q2Coord N ε (Sum.inl (Sum.inl p)) ≠
      q2Coord N ε (Sum.inl (Sum.inl p')) from fun h => hpp (Sum.inl.inj (Sum.inl.inj
        ((q2Coord N ε).injective h)))) (1 : K) := by
  set a := q2Coord N ε (Sum.inl (Sum.inl p)) with ha
  set b := q2Coord N ε (Sum.inl (Sum.inl p')) with hb
  have hab : a ≠ b := fun h => hpp (Sum.inl.inj (Sum.inl.inj ((q2Coord N ε).injective h)))
  intro h
  have h1 := congrArg (fun z : SpecialLinearGroup (Fin (2 * N + ε)) K =>
    (z : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) K) a b) h
  have hinv : (SpecialLinearGroup.transvection hab (1 : K))⁻¹ =
      SpecialLinearGroup.transvection hab 1 :=
    inv_eq_of_mul_eq_one_right (q2Transvection_one_mul_self hab)
  rw [coe_q2Graph, hinv, q2GramMat_mul_mul_apply, transpose_apply,
    SpecialLinearGroup.transvection_coe] at h1
  have hpa : q2Par N ε a = q2Coord N ε (Sum.inl (Sum.inr p)) := by
    rw [ha, q2Par_q2Coord]; rfl
  have hpb : q2Par N ε b = q2Coord N ε (Sum.inl (Sum.inr p')) := by
    rw [hb, q2Par_q2Coord]; rfl
  rw [hpa, hpb] at h1
  simp only [Matrix.add_apply, single_apply, Matrix.one_apply,
    (q2Coord N ε).injective.eq_iff, ha, hb] at h1
  simp [hpp, Ne.symm hpp] at h1

theorem q2GraphBlock_not_mem_inner [CharP K 2] (hK : Nat.card K = 2) (hε : ε ≤ 1)
    {R : Finset (Fin N)} {p p' : Fin N} (hpp : p ≠ p') (hp : p ∉ R) (hp' : p' ∉ R) :
    q2GraphBlock ε hK R ∉ (MulAut.conj : q2Block ε K R →* MulAut (q2Block ε K R)).range := by
  rintro ⟨a, ha⟩
  have ha1 : a = 1 := by
    refine eq_one_of_commute_q2SpBlock hK hε a fun s hs => ?_
    have h := q2GraphBlock_fix hK hs
    rw [← ha, MulAut.conj_apply] at h
    calc a * s = a * s * a⁻¹ * a := by group
      _ = s * a := by rw [h]
  rw [ha1, map_one] at ha
  set a₀ := q2Coord N ε (Sum.inl (Sum.inl p)) with ha₀
  set b₀ := q2Coord N ε (Sum.inl (Sum.inl p')) with hb₀
  have hab : a₀ ≠ b₀ := fun h => hpp (Sum.inl.inj (Sum.inl.inj ((q2Coord N ε).injective h)))
  have hmem : SpecialLinearGroup.transvection hab (1 : K) ∈ q2Block ε K R := by
    refine LinearPilot.transvection_mem_blockSpecialLinear hab ?_ ?_ 1
    · rw [Finset.mem_compl, ha₀, q2Coord_mem_planeCoordsQ2]; exact hp
    · rw [Finset.mem_compl, hb₀, q2Coord_mem_planeCoordsQ2]; exact hp'
  apply q2Graph_transvection_ne (ε := ε) hK hpp
  have := congrArg (fun α : MulAut (q2Block ε K R) =>
    ((α ⟨_, hmem⟩ : q2Block ε K R) : SpecialLinearGroup (Fin (2 * N + ε)) K)) ha
  simpa [coe_q2GraphBlock] using this.symm

theorem eq_or_eq_q2Graph_of_range_eq [CharP K 2] {G : Type*} [Group G] (hK : Nat.card K = 2)
    (hε : ε ≤ 1) {R : Finset (Fin N)} {p p' : Fin N} (hpp : p ≠ p') (hp : p ∉ R) (hp' : p' ∉ R)
    (h3 : 3 ≤ ((planeCoordsQ2 ε R)ᶜ).card) (φP φQ : q2Block ε K R →* G)
    (hP : Function.Injective φP) (hQ : Function.Injective φQ) (hr : φP.range = φQ.range)
    (hS : ∀ s ∈ q2SpBlock ε K hK R, φP s = φQ s) :
    (∀ x, φP x = φQ x) ∨ ∀ x, φP x = φQ (q2GraphBlock ε hK R x) := by
  set θ : MulAut (q2Block ε K R) := ((MonoidHom.ofInjective hP).trans
    (MulEquiv.subgroupCongr hr)).trans (MonoidHom.ofInjective hQ).symm with hθdef
  have hθ : ∀ y, φQ (θ y) = φP y := by
    intro y
    have h := (MonoidHom.ofInjective hQ).apply_symm_apply
      (MulEquiv.subgroupCongr hr (MonoidHom.ofInjective hP y))
    have h2 := congrArg Subtype.val h
    rw [MonoidHom.ofInjective_apply] at h2
    exact h2
  obtain ⟨χ⟩ := nonempty_q2Block_mulEquiv (ε := ε) hK R
  rcases eq_one_or_eq_of_fix (S := q2SpBlock ε K hK R) (eq_one_of_commute_q2SpBlock hK hε)
      (fun α β hα hβ => mul_inv_mem_inner_of_not_mem hK h3 χ hα hβ)
      (fun s hs => q2GraphBlock_fix hK hs) (q2GraphBlock_not_mem_inner hK hε hpp hp hp')
      (τ := θ) (fun s hs => hQ ((hθ s).trans (hS s hs))) with h1 | h1
  · left
    intro x
    rw [← hθ x, h1, MulAut.one_apply]
  · right
    intro x
    rw [← hθ x, h1]

end CFSG.SeitzReduction.SymplecticPilot
