module

public import CFSG.HardMathSupport.Solomon.Coordinator.I24_7FiCoverData
public import CFSG.HardMathSupport.Solomon.Coordinator.I24_7FiLift

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.CaseThreeNs

theorem fi_mem_normalizer_map {X X' : Type*} [Group X] [Group X'] (τ : X ≃* X') {E : Subgroup X}
    {n : X} (hn : n ∈ Subgroup.normalizer (E : Set X)) :
    τ n ∈ Subgroup.normalizer ((E.map τ.toMonoidHom : Subgroup X') : Set X') := by
  rw [Subgroup.mem_normalizer_iff] at hn ⊢
  intro h
  obtain ⟨h0, rfl⟩ := τ.surjective h
  have e1 : τ n * τ h0 * (τ n)⁻¹ = τ (n * h0 * n⁻¹) := by simp
  rw [e1]
  have key : ∀ x : X, τ x ∈ E.map τ.toMonoidHom ↔ x ∈ E := fun x => by
    constructor
    · intro hx
      obtain ⟨x', hx', hxx⟩ := Subgroup.mem_map.1 hx
      have : x' = x := τ.injective hxx
      exact this ▸ hx'
    · intro hx
      exact Subgroup.mem_map.2 ⟨x, hx, rfl⟩
  rw [key, key]
  exact hn h0

variable {Y : Type*} [Group Y] [Finite Y] {M : Type*} [Group M] [Finite M]

theorem weakCore_of_coverData (hD : Fi22CoverData M) (hY : commutator Y = ⊤)
    (N : Subgroup Y) [N.Normal] (hNc : N ≤ Subgroup.center Y) (e : Y ⧸ N ≃* M)
    (P : Subgroup Y) (_hP : IsPGroup 3 P) (hPc : Nat.card P = 3 ^ (Nat.card Y).factorization 3)
    (hNP : Nat.card ↥(N ⊓ P) ≤ 3) : (⊤ : Subgroup Y) ≤ weakCoreIn 3 P ⊤ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P0, E5, Q4, n5, n4, n4', hP0, hP0c, hE5P, hE5e, hE5c, hQ4P, hQ4e, hQ4c, hn5, hn4, hn4',
    hgen⟩ := hD
  set π : Y →* Y ⧸ N := QuotientGroup.mk' N with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective N
  let PS : Sylow 3 Y := Sylow.ofCard P hPc
  have hPS : (PS : Subgroup Y) = P := Sylow.coe_ofCard P hPc
  let PbS : Sylow 3 (Y ⧸ N) := PS.mapSurjective hπs
  let QS : Sylow 3 M := PbS.mapSurjective (f := e.toMonoidHom) e.surjective
  let P0S : Sylow 3 M := Sylow.ofCard P0 hP0c
  have hP0S : (P0S : Subgroup M) = P0 := Sylow.coe_ofCard P0 hP0c
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M QS P0S
  let τ : M ≃* Y ⧸ N := (MulAut.conj g⁻¹).trans e.symm
  have hτ : ∀ x ∈ P0, τ x ∈ (PS : Subgroup Y).map π := by
    intro x hx
    have hx' : x ∈ ((g • QS : Sylow 3 M) : Subgroup M) := by
      rw [hg, hP0S]
      exact hx
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hx'
    obtain ⟨s, hs, hsx⟩ := hx'
    rw [MulAut.smul_def, MulAut.conj_apply] at hsx
    have hs' : s ∈ (((PS : Subgroup Y).map π).map e.toMonoidHom : Subgroup M) := hs
    obtain ⟨z, hz, hzs⟩ := Subgroup.mem_map.1 hs'
    have : τ x = z := by
      have h1 : g⁻¹ * x * g = s := by
        rw [← hsx]
        group
      show e.symm ((MulAut.conj g⁻¹) x) = z
      rw [MulAut.conj_apply, inv_inv, h1]
      rw [← hzs]
      exact e.symm_apply_apply z
    exact this ▸ hz
  have hgenτ : Subgroup.closure ({τ n5, τ n4, τ n4'} : Set (Y ⧸ N)) = ⊤ := by
    have : ({τ n5, τ n4, τ n4'} : Set (Y ⧸ N)) = τ.toMonoidHom '' ({n5, n4, n4'} : Set M) := by
      simp [Set.image_insert_eq]
    rw [this, ← MonoidHom.map_closure, hgen, Subgroup.map_top_of_surjective _ τ.surjective]
  have hNP' : Nat.card ↥(N ⊓ (PS : Subgroup Y)) ≤ 3 := by rw [hPS]; exact hNP
  have key : ∀ (E : Subgroup M) (r : ℕ), E ≤ P0 → IsElemAbelian 3 E → Nat.card E = 3 ^ r →
      4 ≤ r → ∀ n ∈ Subgroup.normalizer (E : Set M), ∀ y : Y, π y = τ n →
      y ∈ weakCoreIn 3 P ⊤ := by
    intro E r hE hEe hEc hr n hn y hy
    have hle : E.map τ.toMonoidHom ≤ (PS : Subgroup Y).map π := by
      rintro _ ⟨x, hx, rfl⟩
      exact hτ x (hE hx)
    have hcard : Nat.card ↥(E.map τ.toMonoidHom) = 3 ^ r := by
      rw [Subgroup.card_map_of_injective τ.injective, hEc]
    have := fi_lift_mem_weakCore N hNc PS hle (fi_elemAbelian_map hEe τ.toMonoidHom) hr hcard
      hNP' (y := y) (by
        rw [show QuotientGroup.mk' N y = τ n from hy]
        exact fi_mem_normalizer_map τ hn)
    rwa [hPS] at this
  set Γ := weakCoreIn 3 P ⊤ with hΓ
  have h5 := fun y hy => key E5 5 hE5P hE5e hE5c (by norm_num) n5 hn5 y hy
  have h4 := fun y hy => key Q4 4 hQ4P hQ4e hQ4c (by norm_num) n4 hn4 y hy
  have h4' := fun y hy => key Q4 4 hQ4P hQ4e hQ4c (by norm_num) n4' hn4' y hy
  obtain ⟨y5, hy5⟩ := hπs (τ n5)
  obtain ⟨y4, hy4⟩ := hπs (τ n4)
  obtain ⟨y4', hy4'⟩ := hπs (τ n4')
  have hmap : (⊤ : Subgroup (Y ⧸ N)) ≤ Γ.map π := by
    rw [← hgenτ, Subgroup.closure_le]
    intro z hz
    rcases hz with rfl | rfl | rfl
    · exact ⟨y5, h5 y5 hy5, hy5⟩
    · exact ⟨y4, h4 y4 hy4, hy4⟩
    · exact ⟨y4', h4' y4' hy4', hy4'⟩
  have hΓN : ∀ y : Y, ∃ γ ∈ Γ, γ⁻¹ * y ∈ N := by
    intro y
    obtain ⟨γ, hγ, hγy⟩ := hmap (Subgroup.mem_top (π y))
    refine ⟨γ, hγ, ?_⟩
    apply (QuotientGroup.eq_one_iff _).1
    change QuotientGroup.mk' N (γ⁻¹ * y) = 1
    rw [map_mul, map_inv, hγy, inv_mul_cancel]
  intro y hy
  rw [← hY] at hy
  rw [commutator_def] at hy
  refine (Subgroup.commutator_le.2 ?_) hy
  intro a _ b _
  obtain ⟨γ1, hγ1, hn1⟩ := hΓN a
  obtain ⟨γ2, hγ2, hn2⟩ := hΓN b
  have c1 := Subgroup.mem_center_iff.1 (hNc hn1)
  have c2 := Subgroup.mem_center_iff.1 (hNc hn2)
  have h1 : a * b * a⁻¹ * b⁻¹ = γ1 * γ2 * γ1⁻¹ * γ2⁻¹ := by
    obtain ⟨n1, hn1e⟩ : ∃ n1, n1 = γ1⁻¹ * a := ⟨_, rfl⟩
    obtain ⟨n2, hn2e⟩ : ∃ n2, n2 = γ2⁻¹ * b := ⟨_, rfl⟩
    have ea : a = γ1 * n1 := by rw [hn1e]; group
    have eb : b = γ2 * n2 := by rw [hn2e]; group
    rw [← hn1e] at c1
    rw [← hn2e] at c2
    have k1 : ∀ g, n1 * g = g * n1 := fun g => (c1 g).symm
    have k2 : ∀ g, n2 * g = g * n2 := fun g => (c2 g).symm
    rw [ea, eb]
    calc γ1 * n1 * (γ2 * n2) * (γ1 * n1)⁻¹ * (γ2 * n2)⁻¹
        = γ1 * (n1 * γ2) * n2 * n1⁻¹ * γ1⁻¹ * n2⁻¹ * γ2⁻¹ := by group
      _ = γ1 * (γ2 * n1) * n2 * n1⁻¹ * γ1⁻¹ * n2⁻¹ * γ2⁻¹ := by rw [k1 γ2]
      _ = γ1 * γ2 * (n1 * n2 * n1⁻¹) * γ1⁻¹ * n2⁻¹ * γ2⁻¹ := by group
      _ = γ1 * γ2 * (n2 * n1 * n1⁻¹) * γ1⁻¹ * n2⁻¹ * γ2⁻¹ := by rw [k1 n2]
      _ = γ1 * γ2 * n2 * γ1⁻¹ * n2⁻¹ * γ2⁻¹ := by group
      _ = γ1 * γ2 * (n2 * γ1⁻¹) * n2⁻¹ * γ2⁻¹ := by group
      _ = γ1 * γ2 * (γ1⁻¹ * n2) * n2⁻¹ * γ2⁻¹ := by rw [k2 γ1⁻¹]
      _ = γ1 * γ2 * γ1⁻¹ * γ2⁻¹ := by group
  show a * b * a⁻¹ * b⁻¹ ∈ Γ
  rw [h1]
  exact Γ.mul_mem (Γ.mul_mem (Γ.mul_mem hγ1 hγ2) (Γ.inv_mem hγ1)) (Γ.inv_mem hγ2)

end CFSG.HardMathSupport.Solomon.Coordinator
