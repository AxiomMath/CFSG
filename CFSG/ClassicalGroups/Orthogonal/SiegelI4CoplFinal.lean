module

public import CFSG.ClassicalGroups.Orthogonal.SiegelI4CoplPlane
public import CFSG.ClassicalGroups.Orthogonal.SiegelI4CoplChain
public import CFSG.ClassicalGroups.Orthogonal.SiegelI4CoplRefl

public section

namespace CFSG.ClassicalGroups.Orthogonal.SiegelRT1

open CFSG.ClassicalGroups.Alternating CFSG.HardMathSupport.Kantor79 QuadraticMap Module

variable {K : Type} [Field K] [Finite K] [CharP K 2]
  {N : Type*} [AddCommGroup N] [Module K N] [FiniteDimensional K N]
  {BN : LinearMap.BilinForm K N}
  {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

@[expose] noncomputable def perpPts (hBN : BN.IsAlt) (ρ : Gsp BN →* (V ≃ₗ[K] V)) (a : N) :
    Submodule K V :=
  ⨆ (y : N) (_ : y ≠ 0 ∧ BN y a = 0), pt hBN ρ y

theorem pt_le_perpPts (hBN : BN.IsAlt) (ρ : Gsp BN →* (V ≃ₗ[K] V)) {a y : N} (hy0 : y ≠ 0)
    (hy : BN y a = 0) : pt hBN ρ y ≤ perpPts hBN ρ a :=
  le_iSup₂ (f := fun (y : N) (_ : y ≠ 0 ∧ BN y a = 0) => pt hBN ρ y) y ⟨hy0, hy⟩

theorem sup_sup_eq_of_le {A B C : Submodule K V} (h : C ≤ A) : A ⊔ (B ⊔ C) = A ⊔ B :=
  le_antisymm (sup_le le_sup_left (sup_le le_sup_right (h.trans le_sup_left)))
    (sup_le_sup_left le_sup_left _)

section Final

variable {hBN : BN.IsAlt} {Qf : QuadraticForm K V} {ρ : Gsp BN →* (V ≃ₗ[K] V)}
  (hs : I4Setting hBN Qf ρ) (hcopl : ∀ π, IsPlane BN π → Copl (planeFamily hBN ρ π))

include hs hcopl

theorem fixes_pt_of_orth {a y : N} (hy0 : y ≠ 0) (hya : BN y a = 0) (μ : K) :
    ∀ v ∈ pt hBN ρ y, ρ (Tsp hBN a μ) v = v := by
  have hfix : (Tsp hBN a μ).app y = y := by
    rw [Tsp_app, hya, mul_zero, zero_smul, add_zero]
  have hmap := pt_map hBN ρ (Tsp hBN a μ) y
  rw [hfix] at hmap
  have hinv : ρ (Tsp hBN a μ) * ρ (Tsp hBN a μ) = 1 := by
    rw [← map_mul, Tsp_mul_self, map_one]
  exact apply_eq_self_of_map_eq hinv (finrank_pt hs hcopl hy0) hmap.symm

theorem perpPts_le_ker (a : N) (μ : K) :
    perpPts hBN ρ a ≤ LinearMap.ker ((ρ (Tsp hBN a μ) : V →ₗ[K] V) - 1) := by
  refine iSup₂_le fun y hy v hv => ?_
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearEquiv.coe_coe, Module.End.one_apply,
    fixes_pt_of_orth hs hcopl hy.1 hy.2 μ v hv, sub_self]

theorem sup_pt_eq_of_orth {a x x' : N} (hx : BN x a ≠ 0) (hx' : BN x' a ≠ 0)
    (hxx' : BN x x' = 0) :
    perpPts hBN ρ a ⊔ pt hBN ρ x = perpPts hBN ρ a ⊔ pt hBN ρ x' := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hx (by simp)
  have hx'0 : x' ≠ 0 := by
    rintro rfl
    exact hx' (by simp)
  by_cases hind : LinearIndependent K ![x, x']
  ·
    have hℓ := isLine_span_pair hBN hxx' hind
    have hxℓ : x ∈ Submodule.span K {x, x'} := Submodule.subset_span (by simp)
    have hx'ℓ : x' ∈ Submodule.span K {x, x'} := Submodule.subset_span (by simp)
    obtain ⟨y, hy⟩ : ∃ y : N, y = BN x' a • x + BN x a • x' := ⟨_, rfl⟩
    have hyℓ : y ∈ Submodule.span K {x, x'} := by
      rw [hy]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ hxℓ) (Submodule.smul_mem _ _ hx'ℓ)
    have hya : BN y a = 0 := by
      have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
      rw [hy, map_add, map_smul, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
        LinearMap.smul_apply, smul_eq_mul, smul_eq_mul]
      linear_combination (BN x' a * BN x a) * h2
    have hxy : LinearIndependent K ![x, y] := by
      rw [LinearIndependent.pair_iff] at hind ⊢
      intro s t hst
      rw [hy] at hst
      have h := hind (s + t * BN x' a) (t * BN x a) (by linear_combination (norm := module) hst)
      have ht : t = 0 := (mul_eq_zero.mp h.2).resolve_right hx
      simp only [ht, zero_mul, add_zero] at h
      exact ⟨h.1, ht⟩
    have hx'y : LinearIndependent K ![x', y] := by
      rw [LinearIndependent.pair_iff] at hind ⊢
      intro s t hst
      rw [hy] at hst
      have h := hind (t * BN x' a) (s + t * BN x a) (by linear_combination (norm := module) hst)
      have ht : t = 0 := (mul_eq_zero.mp h.1).resolve_right hx'
      simp only [ht, zero_mul, add_zero] at h
      exact ⟨h.2, ht⟩
    have hy0 : y ≠ 0 := by simpa using hxy.ne_zero (1 : Fin 2)
    have h1 := famSpace_eq_sup_pt hs hcopl hℓ hxℓ hyℓ hxy
    have h2 := famSpace_eq_sup_pt hs hcopl hℓ hx'ℓ hyℓ hx'y
    have hyS := pt_le_perpPts hBN ρ hy0 hya
    calc perpPts hBN ρ a ⊔ pt hBN ρ x = perpPts hBN ρ a ⊔ (pt hBN ρ x ⊔ pt hBN ρ y) :=
          (sup_sup_eq_of_le hyS).symm
      _ = perpPts hBN ρ a ⊔ (pt hBN ρ x' ⊔ pt hBN ρ y) := by rw [← h1, ← h2]
      _ = perpPts hBN ρ a ⊔ pt hBN ρ x' := sup_sup_eq_of_le hyS
  · rw [LinearIndependent.pair_iff' hx0] at hind
    push Not at hind
    obtain ⟨c, hc⟩ := hind
    have hc0 : c ≠ 0 := by
      rintro rfl
      exact hx'0 (by rw [← hc, zero_smul])
    rw [← hc, pt_smul hBN ρ hc0 x]

theorem sup_pt_eq {a x x' : N} (hx : BN x a ≠ 0) (hx' : BN x' a ≠ 0) :
    perpPts hBN ρ a ⊔ pt hBN ρ x = perpPts hBN ρ a ⊔ pt hBN ρ x' := by
  obtain ⟨z₁, z₂, h1, h2, h3, hz₁, hz₂⟩ :=
    exists_orth_path hBN hs.nondegN (by have := hs.dimN; omega) hx hx'
  rw [sup_pt_eq_of_orth hs hcopl hx hz₁ h1, sup_pt_eq_of_orth hs hcopl hz₁ hz₂ h2,
    sup_pt_eq_of_orth hs hcopl hz₂ hx' h3]

theorem perpPts_sup_pt_eq_top {a x₀ : N} (hx₀ : BN x₀ a ≠ 0) :
    perpPts hBN ρ a ⊔ pt hBN ρ x₀ = ⊤ := by
  refine top_le_iff.mp ?_
  rw [← iSup_pt_eq_top hs hcopl]
  refine iSup₂_le fun y hy0 => ?_
  by_cases hya : BN y a = 0
  · exact (pt_le_perpPts hBN ρ hy0 hya).trans le_sup_left
  · rw [sup_pt_eq hs hcopl hx₀ hya]
    exact le_sup_right

theorem finrank_movedSpace_Tsp_le_one {a : N} (ha : a ≠ 0) (μ : K) :
    finrank K (movedSpace (ρ (Tsp hBN a μ))) ≤ 1 := by
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, BN x₀ a ≠ 0 := by
    by_contra h
    push Not at h
    exact ha (hs.nondegN.2 a h)
  have hx₀0 : x₀ ≠ 0 := by
    rintro rfl
    exact hx₀ (by simp)
  have htop := perpPts_sup_pt_eq_top hs hcopl hx₀
  have hker := perpPts_le_ker hs hcopl a μ
  unfold movedSpace
  have hbot : Submodule.map ((ρ (Tsp hBN a μ) : V →ₗ[K] V) - 1) (perpPts hBN ρ a) = ⊥ :=
    eq_bot_iff.mpr (Submodule.map_le_iff_le_comap.mpr hker)
  rw [LinearMap.range_eq_map, ← htop, Submodule.map_sup, hbot, bot_sup_eq]
  calc finrank K ↥(Submodule.map ((ρ (Tsp hBN a μ) : V →ₗ[K] V) - 1) (pt hBN ρ x₀))
      ≤ finrank K (pt hBN ρ x₀) := Submodule.finrank_map_le _ _
    _ = 1 := finrank_pt hs hcopl hx₀0

omit hs hcopl in
theorem finrank_movedSpace_pos_of_ne_one {u : V ≃ₗ[K] V} (hu : u ≠ 1) :
    0 < finrank K (movedSpace u) := by
  by_contra h
  have h0 : finrank K (movedSpace u) = 0 := by omega
  have hbot : movedSpace u = ⊥ := Submodule.finrank_eq_zero.mp h0
  apply hu
  refine LinearEquiv.ext fun v => ?_
  have hv : u v - v ∈ movedSpace u := sub_mem_movedSpace u v
  rw [hbot, Submodule.mem_bot] at hv
  simpa [sub_eq_zero] using hv

theorem not_copl_all : False := by
  have hNpos : 0 < finrank K N := by have := hs.dimN; omega
  haveI : Nontrivial N := Module.nontrivial_of_finrank_pos hNpos
  obtain ⟨a, ha⟩ := exists_ne (0 : N)
  obtain ⟨l, hl0, hl1⟩ : ∃ l : K, l ≠ 0 ∧ l ≠ 1 := by
    classical
    haveI : Fintype K := Fintype.ofFinite K
    have hcard : ({0, 1} : Finset K).card < (Finset.univ : Finset K).card := by
      have h1 : ({0, 1} : Finset K).card ≤ 2 := Finset.card_le_two
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
      have := hs.card
      omega
    obtain ⟨l, -, hl⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hl
    exact ⟨l, hl.1, hl.2⟩
  have hmov : ∀ μ : K, μ ≠ 0 → finrank K (movedSpace (ρ (Tsp hBN a μ))) = 1 := by
    intro μ hμ
    have hle := finrank_movedSpace_Tsp_le_one hs hcopl ha μ
    have hne : ρ (Tsp hBN a μ) ≠ 1 := fun h => by
      have h1 := hs.inj (h.trans (map_one ρ).symm)
      rcases (Tsp_eq_one_iff hBN hs.nondegN a μ).mp h1 with h2 | h2
      exacts [ha h2, hμ h2]
    have := finrank_movedSpace_pos_of_ne_one hne
    omega
  have hprod : ρ (Tsp hBN a 1) * ρ (Tsp hBN a l) = ρ (Tsp hBN a (1 + l)) := by
    rw [← map_mul, Tsp_mul_Tsp]
  have hu : ρ (Tsp hBN a 1) = ρ (Tsp hBN a l) :=
    eq_of_finrank_movedSpace_mul_le_one hs.nondeg (fun v => hs.iso _ v) (fun v => hs.iso _ v)
      (hmov 1 one_ne_zero) (hmov l hl0)
      (by rw [hprod]; exact finrank_movedSpace_Tsp_le_one hs hcopl ha (1 + l))
  have hT : Tsp hBN a 1 = Tsp hBN a l := hs.inj hu
  have hsum : Tsp hBN a (1 + l) = 1 := by
    rw [← Tsp_mul_Tsp, ← hT, Tsp_mul_self]
  rcases (Tsp_eq_one_iff hBN hs.nondegN a (1 + l)).mp hsum with h | h
  · exact ha h
  · apply hl1
    have h2 : l = -1 := eq_neg_of_add_eq_zero_right h
    rw [h2, CharTwo.neg_eq]

end Final

end CFSG.ClassicalGroups.Orthogonal.SiegelRT1
