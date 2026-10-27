module

public import CFSG.LieType.Chevalley.Covering
public import CFSG.LieType.BorelTits.WeightedMatrix

public section

namespace CFSG.LieType.Chevalley

open CFSG.LieType.BorelTits CFSG.LieType.BorelTits.Weighted
open scoped RealInnerProductSpace

variable {W Φ ι' : Type*} [Group W] [MulAction W Φ] {Rc : RootCombinatorics W Φ ι'}
variable {G : Type*} [Group G] (D : RootGroupData Rc G)
variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] (b : Module.Basis ι K V)
variable (ρ : G →* Module.End K V)
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem eq_zero_of_repr_eq_zero {f : Module.End K V} (h : ∀ i j, b.repr (f (b j)) i = 0) :
    f = 0 :=
  b.ext fun j => b.repr.injective (by ext i; simpa using h i j)

theorem holds_of_rootGroupData [Finite G] [Finite W] [Finite ι] [FiniteDimensional ℝ E]
    (p : ℕ) [Fact p.Prime] [CharP K p] (hρ : Function.Injective ρ)
    (act : W →* (E ≃ₗᵢ[ℝ] E)) (wt : ι → E) (rootE : Φ → E) (Dc : Set E) (v₀ : E)
    (hnorm : ∀ i, D.X (Rc.simple i) ≤ Subgroup.normalizer (D.Ui i : Set G))
    (hrank : ∀ i, D.RankOne i)
    (hgen : Subgroup.closure ((D.B : Set G) ∪ Set.range fun i => (D.n i : G)) = ⊤)
    (hgenW : Subgroup.closure (Set.range Rc.refl) = ⊤)
    (hspan : Submodule.span ℝ (Set.range wt) = ⊤)
    (hfix : ∀ v : E, (∀ w, act w v = v) → v = 0)
    (hcover : ∀ x : E, ∃ w, ∃ y ∈ Dc, x = act w y)
    (hmono : ∀ m : D.N, ∀ i j, b.repr (ρ m (b j)) i ≠ 0 → wt i = act (D.φ m) (wt j))
    (hroot : ∀ α, ∀ x ∈ D.X α, ∀ i j, b.repr (ρ x (b j) - b j) i ≠ 0 →
      ∃ k : ℕ, 1 ≤ k ∧ wt i = wt j + (k : ℝ) • rootE α)
    (hrootneg : ∀ α, rootE (Rc.neg α) = -rootE α)
    (hpos : ∀ α, Rc.pos α → ∀ v ∈ Dc, 0 ≤ ⟪rootE α, v⟫)
    (hv₀ : ∀ α, Rc.pos α → 0 < ⟪rootE α, v₀⟫)
    (hne : ∀ α, D.X α ≠ ⊥)
    (hW1 : ∀ w : W, (∀ i, Rc.pos (w • Rc.simple i)) → w = 1)
    (hH : Nat.Coprime (Nat.card D.H) p) :
    Holds G p := by
  classical
  have hφsurj : Function.Surjective D.φ := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← hgenW, Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨D.n i, D.φ_n i⟩
  choose nW hnW using hφsurj
  set n : W → G := fun w => (nW w : G) with hn
  have hsub : ∀ (x : G) i j, b.repr ((ρ x - 1) (b j)) i = b.repr (ρ x (b j) - b j) i := by
    intro x i j
    rw [LinearMap.sub_apply, Module.End.one_apply]
  have hentry : ∀ α, ∀ x ∈ D.X α, ∀ v : E, ∀ i j, b.repr ((ρ x - 1) (b j)) i ≠ 0 →
      ∃ k : ℕ, 1 ≤ k ∧ ⟪wt i, v⟫ = ⟪wt j, v⟫ + k * ⟪rootE α, v⟫ := by
    intro α x hx v i j hij
    rw [hsub] at hij
    obtain ⟨k, hk, hw⟩ := hroot α x hx i j hij
    refine ⟨k, hk, ?_⟩
    rw [hw, inner_add_left, inner_smul_left]
    simp only [RCLike.conj_to_real]
  have hraise : ∀ α, ∀ x ∈ D.X α, ∀ v : E, 0 ≤ ⟪rootE α, v⟫ →
      Raises b wt v ⟪rootE α, v⟫ (ρ x - 1) ∧ Raises b wt v 0 (ρ x) := by
    intro α x hx v h0
    have h1 : Raises b wt v ⟪rootE α, v⟫ (ρ x - 1) := by
      intro i j hij
      obtain ⟨k, hk, hw⟩ := hentry α x hx v i j hij
      have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
      rw [hw]
      nlinarith
    refine ⟨h1, ?_⟩
    have : ρ x = 1 + (ρ x - 1) := by abel
    rw [this]
    exact (raises_one v).add (h1.mono h0)
  have hUgk : D.U ≤ gradedKernel b wt ρ v₀ := by
    refine iSup₂_le fun α hα x hx => ?_
    exact ⟨⟪rootE α, v₀⟫, hv₀ α hα, (hraise α x hx v₀ (hv₀ α hα).le).1⟩
  have hUp : IsPGroup p D.U := (isPGroup_gradedKernel ρ p hρ v₀).to_le hUgk
  have hdisj : ∀ α, ¬Rc.pos α → D.U ⊓ D.X α = ⊥ := by
    intro α hα
    rw [eq_bot_iff]
    rintro x ⟨hxU, hxα⟩
    rw [Subgroup.mem_bot]
    obtain ⟨c, hc, hxc⟩ := hUgk hxU
    have hneg : ⟪rootE α, v₀⟫ < 0 := by
      have := hv₀ _ ((Rc.pos_or_pos_neg α).resolve_left hα)
      rwa [hrootneg, inner_neg_left, neg_pos] at this
    have hzero : ρ x - 1 = 0 := by
      refine eq_zero_of_repr_eq_zero b fun i j => ?_
      by_contra hij
      have h1 := hxc i j hij
      obtain ⟨k, hk, hw⟩ := hentry α x hxα v₀ i j hij
      have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
      nlinarith
    exact hρ (by rw [map_one]; exact sub_eq_zero.mp hzero)
  have hBtri : ∀ v ∈ Dc, D.B ≤ triangular b wt ρ v := by
    intro v hv
    refine sup_le ?_ ?_
    · intro x hx
      obtain ⟨k, hk, rfl⟩ := (RootGroupData.mem_H_iff (D := D)).mp hx
      intro i j hij
      rw [hmono k i j hij, hk, map_one, LinearIsometryEquiv.coe_one, id, add_zero]
    · refine iSup₂_le fun α hα x hx => ?_
      exact (hraise α x hx v (hpos α hα v hv)).2
  have hbruhat : ∀ g : G, ∃ w, ∃ b₁ ∈ D.B, ∃ b₂ ∈ D.B, g = b₁ * n w * b₂ := by
    intro g
    obtain ⟨m, b₁, hb₁, b₂, hb₂, rfl⟩ := D.exists_mem_doubleCoset hnorm hrank hgen g
    refine ⟨D.φ m, b₁, hb₁, ((nW (D.φ m))⁻¹ * m : D.N) * b₂, mul_mem ?_ hb₂, ?_⟩
    · exact D.H_le_B ((RootGroupData.mem_H_iff (D := D)).mpr
        ⟨_, by rw [map_mul, map_inv, hnW, inv_mul_cancel], rfl⟩)
    · simp [hn, mul_assoc]
  have hN : Subgroup.normalizer (D.U : Set G) ≤ D.B :=
    D.normalizer_le hnorm hrank hgen hdisj hne hW1
  obtain ⟨S, hS⟩ := D.exists_sylow_eq_U p hUp hN hH
  have hdat : WeightedBruhat b wt ρ act n D.B S Dc v₀ := by
    refine ⟨hspan, hfix, ?_, ?_, hcover, ?_, hbruhat, ?_⟩
    · intro w i j hij
      rw [hmono (nW w) i j hij, hnW]
    · intro w i j hij
      have h := hmono (nW w)⁻¹ i j (by simpa [hn] using hij)
      rw [map_inv, hnW] at h
      rw [h, show act w (act w⁻¹ (wt j)) = (act w * act w⁻¹) (wt j) from rfl, ← map_mul,
        mul_inv_cancel, map_one]
      rfl
    · intro x hx v hv i j hij
      have := (hBtri v hv hx) i j hij
      linarith
    · intro u hu i j hij
      rw [hS] at hu
      obtain ⟨c, hc, huc⟩ := hUgk hu
      have := huc i j (by rwa [hsub])
      linarith
  exact holds_of_weightedBruhat ρ p hρ S hdat (by rw [hS]; exact hN)

end CFSG.LieType.Chevalley
