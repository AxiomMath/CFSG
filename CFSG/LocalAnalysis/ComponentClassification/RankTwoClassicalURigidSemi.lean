module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalURigidModule

public section

namespace CFSG.ComponentClassification.RankTwoClassical.URigid

open Matrix Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial

variable {K : Type} [Field K] [CharP K 2] {ε f : ℕ} (h : UnitaryFieldData 2 f K)

theorem smat_apply_zero (g : stabE (ε := ε) h) :
    (∀ k, smat h g (.inr (.inl k)) hE = 0) ∧ (∀ l, smat h g hF (.inr (.inl l)) = 0) ∧
      smat h g hF hE = 0 ∧ smat h g hF hF = 1 := by
  obtain ⟨c, hc⟩ := exists_eq_eichM_avec h g
  obtain ⟨-, h2, -, h4, h5, h6, -, -⟩ := eichM_mul_blkZM_apply h.bar (avec h g) c (rmat h g)
  rw [hc]
  exact ⟨h4, h5, h6, h2⟩

section Cocycle

variable {Z : Matrix (HypIndex 1 ε) (HypIndex 1 ε) K} {τ : K ≃+* K}
  (hZe : ∀ k, Z (.inr (.inl k)) hE = 0) (hZf : ∀ l, Z hF (.inr (.inl l)) = 0)
include hZe

theorem fcol_of_semi_commute {g g' : stabE (ε := ε) h}
    (hg : Z * (smat h g).map τ = smat h g' * Z) :
    zBlock Z *ᵥ (τ ∘ avec h g) + (fun k => Z (.inr (.inl k)) hF) =
      rmat h g' *ᵥ (fun k => Z (.inr (.inl k)) hF) + Z hF hF • avec h g' := by
  obtain ⟨-, -, -, hgff⟩ := smat_apply_zero h g
  obtain ⟨hge, -, -, -⟩ := smat_apply_zero h g'
  funext i
  have h1 := congrFun (congrFun hg (.inr (.inl i))) hF
  simp only [Matrix.mul_apply, Fintype.sum_sum_type, Finset.univ_unique, Finset.sum_singleton,
    Matrix.map_apply, Fin.default_eq_zero] at h1
  rw [show (Sum.inl 0 : HypIndex 1 ε) = hE from rfl,
    show (Sum.inr (Sum.inr 0) : HypIndex 1 ε) = hF from rfl, hZe, hge, hgff, map_one,
    zero_mul, zero_mul, zero_add, zero_add, mul_one] at h1
  show (∑ x, zBlock Z i x * (τ ∘ avec h g) x) + Z (.inr (.inl i)) hF =
    (∑ x, rmat h g' i x * Z (.inr (.inl x)) hF) + Z hF hF * avec h g' i
  rw [mul_comm (Z hF hF)]
  exact h1

include hZf in
theorem zblock_of_semi_commute {g g' : stabE (ε := ε) h}
    (hg : Z * (smat h g).map τ = smat h g' * Z) :
    zBlock Z * (rmat h g).map τ = rmat h g' * zBlock Z := by
  obtain ⟨-, hgf, -, -⟩ := smat_apply_zero h g
  obtain ⟨hge, -, -, -⟩ := smat_apply_zero h g'
  ext i j
  have h1 := congrFun (congrFun hg (.inr (.inl i))) (.inr (.inl j))
  simp only [Matrix.mul_apply, Fintype.sum_sum_type, Finset.univ_unique, Finset.sum_singleton,
    Matrix.map_apply, Fin.default_eq_zero] at h1
  rw [show (Sum.inl 0 : HypIndex 1 ε) = hE from rfl,
    show (Sum.inr (Sum.inr 0) : HypIndex 1 ε) = hF from rfl, hZe, hge, hgf, hZf, map_zero,
    zero_mul, zero_mul, mul_zero, mul_zero, zero_add, zero_add, add_zero, add_zero] at h1
  exact h1

include hZf in
theorem exists_mem_ker_avec_conj_eq_zero [Finite K] {H : Subgroup (stabE (ε := ε) h)}
    (hZH : ∀ g ∈ H, Z * (smat h g).map τ = smat h g * Z)
    (hinj : ∀ a : Fin ε → K, Z hF hF • a = zBlock Z *ᵥ (τ ∘ a) → a = 0) :
    ∃ x₀ ∈ (zBlockHom (ε := ε) h).ker, ∀ g ∈ H, avec h (x₀⁻¹ * g * x₀) = 0 := by
  set w₀ : Fin ε → K := fun k => Z (.inr (.inl k)) hF
  let T : (Fin ε → K) →+ (Fin ε → K) :=
    { toFun := fun a => Z hF hF • a - zBlock Z *ᵥ (τ ∘ a)
      map_zero' := by
        have : (τ ∘ (0 : Fin ε → K)) = 0 := funext fun _ => map_zero τ
        simp [this]
      map_add' := fun a b => by
        have : (τ ∘ (a + b)) = τ ∘ a + τ ∘ b := funext fun _ => map_add τ _ _
        rw [this, smul_add, mulVec_add]
        abel }
  have hTinj : Function.Injective T := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    exact hinj a (sub_eq_zero.mp ha)
  have hTsurj : Function.Surjective T := Finite.surjective_of_injective hTinj
  obtain ⟨v₀, hv₀⟩ := hTsurj w₀
  have hTρ : ∀ g ∈ H, ∀ a, T (rmat h g *ᵥ a) = rmat h g *ᵥ T a := by
    intro g hg a
    have hmap : τ ∘ (rmat h g *ᵥ a) = (rmat h g).map τ *ᵥ (τ ∘ a) :=
      funext fun i => RingHom.map_mulVec τ.toRingHom (rmat h g) a i
    change Z hF hF • (rmat h g *ᵥ a) - zBlock Z *ᵥ (τ ∘ (rmat h g *ᵥ a)) =
      rmat h g *ᵥ (Z hF hF • a - zBlock Z *ᵥ (τ ∘ a))
    rw [hmap, mulVec_mulVec, zblock_of_semi_commute h hZe hZf (hZH g hg), mulVec_sub,
      mulVec_smul, mulVec_mulVec]
  have hkey : ∀ g ∈ H, avec h g = v₀ - rmat h g *ᵥ v₀ := by
    intro g hg
    apply hTinj
    have h1 := fcol_of_semi_commute h hZe (hZH g hg)
    rw [map_sub, hTρ g hg, hv₀]
    change Z hF hF • avec h g - zBlock Z *ᵥ (τ ∘ avec h g) = w₀ - rmat h g *ᵥ w₀
    rw [sub_eq_sub_iff_add_eq_add, add_comm, ← h1, add_comm]
  obtain ⟨x₀, hx₀, hx₀v⟩ := exists_mem_ker_avec_eq h v₀
  have hx1 : rmat h x₀⁻¹ = 1 := by
    rw [rmat, MonoidHom.mem_ker.mp (inv_mem hx₀)]
    rfl
  refine ⟨x₀, hx₀, fun g hg => ?_⟩
  rw [avec_mul, avec_mul, rmat_mul, hx1, Matrix.one_mul, avec_inv, hx1]
  simp only [one_mulVec, hx₀v, hkey g hg]
  abel

end Cocycle

section Two

variable [Finite K]

omit [Finite K] in
theorem mem_stdW_of_avec_eq_zero {H : Subgroup (stabE (ε := 2) h)} (hH : ⁅H, H⁆ = H)
    (hHa : ∀ g ∈ H, avec h g = 0) {g : stabE (ε := 2) h} (hg : g ∈ H) : g ∈ stdW h := by
  have h1 := le_avecCvalSub_of_perfect h hH (C := ⊥) (fun g hg => by
      rw [Submodule.mem_bot]
      exact hHa g hg)
    (fun g _ v hv => by
      rw [Submodule.mem_bot] at hv
      rw [hv, mulVec_zero]) hg
  exact mem_stdW_of h h1.1 h1.2 fun j hj => absurd j.2 (by omega)

end Two

end CFSG.ComponentClassification.RankTwoClassical.URigid
