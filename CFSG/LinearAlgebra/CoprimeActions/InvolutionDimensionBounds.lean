module

public import CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.ExtraspecialHyperplaneVocabulary
public import CFSG.GroupTheory.CoprimeActionSupport.InvertedOddOrderDisplacementRank
public import CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.FixedSpace

public section

namespace CFSG.LinearAlgebra.CoprimeActions.InvolutionDimensionBounds

open CFSG.LinearAlgebra CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations Module

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] noncomputable def toEquivHom (ρ : Representation (ZMod 2) G V) : G →* (V ≃ₗ[ZMod 2] V) where
  toFun g := LinearEquiv.ofLinear (ρ g) (ρ g⁻¹)
    (by ext v; rw [LinearMap.comp_apply, ← rho_mul_apply]; simp)
    (by ext v; rw [LinearMap.comp_apply, ← rho_mul_apply]; simp)
  map_one' := by ext v; simp [LinearEquiv.ofLinear_apply]
  map_mul' g h := by
    ext v
    simp only [LinearEquiv.ofLinear_apply, LinearEquiv.mul_apply, rho_mul_apply]

theorem toEquivHom_apply (ρ : Representation (ZMod 2) G V) (g : G) (v : V) :
    toEquivHom ρ g v = ρ g v := by simp [toEquivHom]

theorem toEquivHom_coe (ρ : Representation (ZMod 2) G V) (g : G) :
    ((toEquivHom ρ g : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V) = ρ g := by
  ext v; exact toEquivHom_apply ρ g v

theorem commSpace_zpowers_eq_range (ρ : Representation (ZMod 2) G V) (x : G)
    (hx : IsOfFinOrder x) :
    commSpace ρ (Subgroup.zpowers x) = LinearMap.range ((ρ x : V →ₗ[ZMod 2] V) - 1) := by
  apply le_antisymm
  · apply Submodule.span_le.2
    rintro _ ⟨g, hg, v, rfl⟩
    obtain ⟨k, rfl⟩ := (hx.mem_powers_iff_mem_zpowers).2 hg
    show _ ∈ LinearMap.range _
    clear hg
    induction k generalizing v with
    | zero => simp
    | succ k ih =>
      have h1 := ih v
      have : ρ (x ^ (k+1)) v - v = ((ρ x : V →ₗ[ZMod 2] V) - 1) (ρ (x ^ k) v) +
          (ρ (x ^ k) v - v) := by
        rw [pow_succ', map_mul]; simp
      rw [this]
      exact Submodule.add_mem _ ⟨_, rfl⟩ h1
  · rintro _ ⟨v, rfl⟩
    exact Submodule.subset_span ⟨x, Subgroup.mem_zpowers x, v, by simp⟩

theorem finrank_commSpace_le_two_mul [Module.Finite (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (X : Subgroup G) (hX : Nat.card X = p) (t : G) (ht : orderOf t = 2)
    (hinv : ∀ x ∈ X, t * x * t⁻¹ = x⁻¹) :
    finrank (ZMod 2) (commSpace ρ X) ≤ 2 * finrank (ZMod 2) (commSpace ρ (Subgroup.zpowers t)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite X := Nat.finite_of_card_ne_zero (by rw [hX]; exact hp.ne_zero)
  haveI : IsCyclic X := isCyclic_of_prime_card hX
  obtain ⟨x, hx⟩ := IsCyclic.exists_generator (α := X)
  have hxp : (x : G) ^ p = 1 := by
    have := pow_card_eq_one' (G := X) (x := x)
    rw [hX] at this
    simpa using congrArg Subtype.val this
  have hXeq : X = Subgroup.zpowers (x : G) := by
    apply le_antisymm
    · intro y hy
      obtain ⟨k, hk⟩ := hx ⟨y, hy⟩
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩
    · rw [Subgroup.zpowers_le]; exact x.2
  have hfin : IsOfFinOrder (x : G) := isOfFinOrder_iff_pow_eq_one.2 ⟨p, hp.pos, hxp⟩
  have ht2 : t ^ 2 = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
  have ht1 : IsOfFinOrder t := isOfFinOrder_iff_pow_eq_one.2 ⟨2, by norm_num, ht2⟩
  rw [hXeq, commSpace_zpowers_eq_range ρ _ hfin, commSpace_zpowers_eq_range ρ _ ht1]
  have htinv : t⁻¹ = t := by
    rw [inv_eq_iff_mul_eq_one, ← pow_two]; exact ht2
  have hxX : (x : G) ∈ X := x.2
  have := hinv _ hxX
  rw [htinv] at this
  have := CFSG.GroupTheory.CoprimeActionSupport.InvertedOddOrderDisplacementRank.finrank_range_le (toEquivHom ρ t) (toEquivHom ρ x)
    p (hp.eq_two_or_odd'.resolve_left hp2)
    (by rw [← map_mul, ← pow_two, ht2, map_one])
    (by rw [← map_pow, hxp, map_one])
    (by rw [← map_mul, ← map_mul, this, map_inv])
  rw [toEquivHom_coe, toEquivHom_coe] at this
  exact this

theorem finrank_commOn_le [Module.Finite (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (X : Subgroup G) (U : Submodule (ZMod 2) V) :
    finrank (ZMod 2) (commOn ρ X U) ≤ finrank (ZMod 2) (commSpace ρ X) := by
  apply Submodule.finrank_mono
  apply Submodule.span_mono
  rintro _ ⟨x, hx, u, -, rfl⟩
  exact ⟨x, hx, u, rfl⟩

end CFSG.LinearAlgebra.CoprimeActions.InvolutionDimensionBounds
