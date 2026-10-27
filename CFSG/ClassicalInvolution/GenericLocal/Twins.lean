module

public import CFSG.Assembly.Subnormal
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.ClassicalInvolution

open scoped MatrixGroups

private theorem mem_map_conj_iff' {G : Type*} [Group G] {J : Subgroup G} {g x : G} :
    x ∈ J.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ J := by
  rw [Subgroup.mem_map_equiv]
  simp

section Perfect

variable {G : Type*} [Group G]

open scoped Pointwise in
theorem perfect_le_normalizer_of_invariant {P : Subgroup G} [Group.IsPerfect P]
    {S : Set (Subgroup G)}
    (hS : ∀ p ∈ P, ∀ M ∈ S, M.map (MulAut.conj p).toMonoidHom ∈ S) (hcard : S.encard ≤ 4)
    {M : Subgroup G} (hM : M ∈ S) : P ≤ Subgroup.normalizer (M : Set G) := by
  let _ : MulAction P (Subgroup G) :=
    MulAction.compHom (Subgroup G) ((MulAut.conj : G →* MulAut G).comp P.subtype)
  have hsmul : ∀ (p : P) (N : Subgroup G), p • N = N.map (MulAut.conj (p : G)).toMonoidHom :=
    fun _ _ => rfl
  let S' : SubMulAction P (Subgroup G) :=
    { carrier := S
      smul_mem' := fun p N hN => by
        rw [hsmul]
        exact hS p p.2 N hN }
  have hfin : (S' : Set (Subgroup G)).Finite := Set.finite_of_encard_le_coe hcard
  have : Finite S' := hfin.to_subtype
  have hS4 : Nat.card S' ≤ 4 := by
    have h1 : Nat.card S' = (S' : Set (Subgroup G)).ncard := Nat.card_coe_set_eq _
    have h2 : (((S' : Set (Subgroup G)).ncard : ℕ) : ℕ∞) = (S' : Set (Subgroup G)).encard :=
      hfin.cast_ncard_eq
    rw [h1]
    have h3 : (((S' : Set (Subgroup G)).ncard : ℕ) : ℕ∞) ≤ 4 := by
      rw [h2]
      exact hcard
    exact_mod_cast h3
  let ψ : P →* Equiv.Perm S' := MulAction.toPermHom P S'
  have hsolv : Group.IsSolvable (Equiv.Perm S') := Equiv.Perm.isSolvable hS4
  have hψ : ∀ p : P, ψ p = 1 := by
    have : Group.IsPerfect ψ.range := Group.IsPerfect.range ψ
    by_contra hcon
    push Not at hcon
    obtain ⟨p, hp⟩ := hcon
    have hnt : Nontrivial ψ.range := ⟨⟨⟨ψ p, p, rfl⟩, 1, fun h => hp (congrArg Subtype.val h)⟩⟩
    exact Group.IsPerfect.not_isSolvable ψ.range inferInstance
  intro p hp
  have h1 : M.map (MulAut.conj p).toMonoidHom = M :=
    congrArg (fun f : Equiv.Perm S' => (f ⟨M, hM⟩ : S').1) (hψ ⟨p, hp⟩)
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have h2 : p * x * p⁻¹ ∈ M ↔ x ∈ M := by
    conv_lhs => rw [← h1]
    rw [mem_map_conj_iff', show p⁻¹ * (p * x * p⁻¹) * p = x by group]
  exact h2.symm

end Perfect

section Family

variable {G : Type*} [Group G]

private theorem map_map_conj_eq (J : Subgroup G) (a b : G) :
    (J.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      J.map (MulAut.conj (b * a)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  show b * (a * x * a⁻¹) * b⁻¹ = b * a * x * (b * a)⁻¹
  group

private theorem mem_normalizer_of_commute {M : Subgroup G} {x : G}
    (h : ∀ y ∈ M, x * y = y * x) : x ∈ Subgroup.normalizer (M : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    rw [h y hy]
    simpa using hy
  · intro hy
    have h1 := h _ hy
    have h2 : x * y * x⁻¹ = y := by
      have : x * (x * y * x⁻¹) = x * y := by rw [h1]; group
      exact mul_left_cancel this
    rw [h2] at hy
    exact hy

private theorem isSubnormal_subgroupOf_top {J X : Subgroup G} (h : CFSG.Open.IsSubnormal J X) :
    CFSG.Open.IsSubnormal (J.subgroupOf X) ⊤ :=
  CFSG.Open.IsSubnormal.of_mathlib h.subgroupOf

end Family

end CFSG.ClassicalInvolution
