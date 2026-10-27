module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.TimmL2Unip

public section

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Timm.L2

open Matrix Subgroup CFSG.Open
open scoped MatrixGroups

variable {n : ℕ}

local notation "M[" g "]" =>
  ((g : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))

@[expose] def W_of (A : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :
    Submodule (ZMod 2) (Fin n → ZMod 2) :=
  LinearMap.range (Matrix.toLin' (M[A] - 1))

theorem mem_W_of_iff {A : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)} {w : Fin n → ZMod 2} :
    w ∈ W_of A ↔ ∃ u, (M[A] - 1) *ᵥ u = w := by
  unfold W_of
  rw [LinearMap.mem_range]
  simp only [Matrix.toLin'_apply]

theorem sq_zero_of_involution {A : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)}
    (hAA : M[A] * M[A] = 1) (v : Fin n → ZMod 2) : (M[A] - 1) *ᵥ ((M[A] - 1) *ᵥ v) = 0 := by
  have hA2 : ∀ u, M[A] *ᵥ (M[A] *ᵥ u) = u := fun u => by
    rw [mulVec_mulVec, hAA, one_mulVec]
  have hN' : ∀ w, (M[A] - 1) *ᵥ w = M[A] *ᵥ w - w := fun w => by
    rw [sub_mulVec, one_mulVec]
  rw [hN', hN' v, mulVec_sub, hA2]
  rw [show (v - M[A] *ᵥ v) - (M[A] *ᵥ v - v) = (v + v) - (M[A] *ᵥ v + M[A] *ᵥ v) by abel,
    add_self_zmod2, add_self_zmod2, sub_self]

theorem W_of_facts {A : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)} (hAA : M[A] * M[A] = 1)
    (hA1 : A ≠ 1) :
    (∃ x, (M[A] - 1) *ᵥ x ≠ 0) ∧ W_of A ≠ ⊥ ∧ W_of A ≠ ⊤ ∧
      2 * Module.finrank (ZMod 2) (W_of A) ≤ n := by
  have hN : M[A] - 1 ≠ 0 := by
    intro h0
    apply hA1
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_one]
    exact sub_eq_zero.1 h0
  obtain ⟨x, hx⟩ : ∃ x, (M[A] - 1) *ᵥ x ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hN
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro v
    simp only [Matrix.toLin'_apply, Matrix.zero_mulVec]
    exact hcon v
  have hxW : (M[A] - 1) *ᵥ x ∈ W_of A := mem_W_of_iff.2 ⟨x, rfl⟩
  have hbot : W_of A ≠ ⊥ := by
    intro h
    rw [h, Submodule.mem_bot] at hxW
    exact hx hxW
  have htop : W_of A ≠ ⊤ := by
    intro h
    have hxT : x ∈ W_of A := by rw [h]; exact Submodule.mem_top
    obtain ⟨u, hu⟩ := mem_W_of_iff.1 hxT
    apply hx
    rw [← hu, sq_zero_of_involution hAA]
  refine ⟨⟨x, hx⟩, hbot, htop, ?_⟩
  have hle : W_of A ≤ LinearMap.ker (Matrix.toLin' (M[A] - 1)) := by
    intro w hw
    obtain ⟨u, rfl⟩ := mem_W_of_iff.1 hw
    rw [LinearMap.mem_ker, Matrix.toLin'_apply]
    exact sq_zero_of_involution hAA u
  have h1 := gen_rn (Matrix.toLin' (M[A] - 1))
  have h2 := Submodule.finrank_mono hle
  unfold W_of at h2 ⊢
  omega

theorem W_inv_of_comm {A g k : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)} (hk : g * k = 1)
    (hkg : k * g = 1) (hcomm : g * A = A * g) :
    (∀ w ∈ W_of A, M[g] *ᵥ w ∈ W_of A) ∧ (∀ w ∈ W_of A, M[k] *ᵥ w ∈ W_of A) := by
  have key : ∀ {c : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)},
      M[c] * M[A] = M[A] * M[c] → ∀ w ∈ W_of A, M[c] *ᵥ w ∈ W_of A := by
    intro c hc w hw
    obtain ⟨u, rfl⟩ := mem_W_of_iff.1 hw
    rw [mem_W_of_iff]
    refine ⟨M[c] *ᵥ u, ?_⟩
    have hc2 : (M[A] - 1) * M[c] = M[c] * (M[A] - 1) := by
      rw [sub_mul, mul_sub, one_mul, mul_one, hc]
    calc (M[A] - 1) *ᵥ (M[c] *ᵥ u) = ((M[A] - 1) * M[c]) *ᵥ u := by rw [mulVec_mulVec]
      _ = (M[c] * (M[A] - 1)) *ᵥ u := by rw [hc2]
      _ = M[c] *ᵥ ((M[A] - 1) *ᵥ u) := by rw [mulVec_mulVec]
  refine ⟨key ?_, key ?_⟩
  · rw [← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul, hcomm]
  · have hc' : k * A = A * k := by
      calc k * A = k * A * (g * k) := by rw [hk, mul_one]
        _ = k * (A * g) * k := by group
        _ = k * (g * A) * k := by rw [hcomm]
        _ = (k * g) * (A * k) := by group
        _ = A * k := by rw [hkg, one_mul]
    rw [← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul, hc']

theorem normalizer_unip_of_comm {A g : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)}
    (hcomm : g * A = A * g) :
    g ∈ normalizer ((unip (W_of A) : Subgroup (Matrix.SpecialLinearGroup (Fin n) (ZMod 2))) :
      Set (Matrix.SpecialLinearGroup (Fin n) (ZMod 2))) := by
  obtain ⟨k, hk, hkg⟩ : ∃ k, g * k = 1 ∧ k * g = 1 := ⟨g⁻¹, mul_inv_cancel g, inv_mul_cancel g⟩
  obtain ⟨hW1, hW2⟩ := W_inv_of_comm hk hkg hcomm
  exact mem_normalizer_unip_of (W_of A) hk hkg hW1 hW2

theorem exists_normalizing_element (hn : 3 ≤ n) {A : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)}
    (hAA : M[A] * M[A] = 1) (hA1 : A ≠ 1) :
    ∃ g₀ : Matrix.SpecialLinearGroup (Fin n) (ZMod 2), g₀ * A ≠ A * g₀ ∧
      g₀ ∈ normalizer ((unip (W_of A) : Subgroup (Matrix.SpecialLinearGroup (Fin n) (ZMod 2))) :
        Set (Matrix.SpecialLinearGroup (Fin n) (ZMod 2))) := by
  obtain ⟨⟨x, hx⟩, -, -, hdim⟩ := W_of_facts hAA hA1
  have hx0 : x ≠ 0 := fun h => hx (by rw [h, mulVec_zero])
  have hS : W_of A ⊔ Submodule.span (ZMod 2) {x} ≠ ⊤ := by
    intro hS
    have hfin : Module.finrank (ZMod 2) ↥(W_of A ⊔ Submodule.span (ZMod 2) {x}) = n := by
      rw [hS, gen_top]
    have hsum := gen_sup_le (K := ZMod 2) (W_of A) (Submodule.span (ZMod 2) {x})
    have hsp : Module.finrank (ZMod 2) ↥(Submodule.span (ZMod 2) {x}) = 1 :=
      gen_span hx0
    omega
  obtain ⟨h, hh0, hhS⟩ := exists_vec_annihilator hS
  have hhW : ∀ w ∈ W_of A, h ⬝ᵥ w = 0 := fun w hw => hhS w (Submodule.mem_sup_left hw)
  have hhx : h ⬝ᵥ x = 0 :=
    hhS x (Submodule.mem_sup_right (Submodule.mem_span_singleton_self x))
  obtain ⟨g₀, hg₀⟩ : ∃ g₀ : Matrix.SpecialLinearGroup (Fin n) (ZMod 2),
      g₀ = oneAddOuter x h hhx := ⟨_, rfl⟩
  obtain ⟨k₀, hk₀, hk₀'⟩ : ∃ k₀ : Matrix.SpecialLinearGroup (Fin n) (ZMod 2),
      g₀ * k₀ = 1 ∧ k₀ * g₀ = 1 := ⟨g₀⁻¹, mul_inv_cancel g₀, inv_mul_cancel g₀⟩
  have hgM : M[g₀] = 1 + outer x h := by rw [hg₀]; rfl
  have hfix : ∀ w ∈ W_of A, M[g₀] *ᵥ w = w := by
    intro w hw
    rw [hgM, oneAdd_mulVec, hhW w hw, zero_smul, add_zero]
  refine ⟨g₀, ?_, mem_normalizer_unip_of (W_of A) hk₀ hk₀'
    (fun w hw => by rw [hfix w hw]; exact hw)
    (fun w hw => by rw [inv_fix_of_fix hk₀' hfix w hw]; exact hw)⟩
  intro hcomm
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hh0
  obtain ⟨e, he⟩ : ∃ e : Fin n → ZMod 2, e = Pi.single i 1 := ⟨_, rfl⟩
  have hv : h ⬝ᵥ e = 1 := by
    rw [he, dotProduct_single, mul_one]
    have key : ∀ c : ZMod 2, c ≠ 0 → c = 1 := by decide
    exact key _ hi
  have hNe : h ⬝ᵥ ((M[A] - 1) *ᵥ e) = 0 := hhW _ (mem_W_of_iff.2 ⟨e, rfl⟩)
  have hAe : M[A] *ᵥ e = e + (M[A] - 1) *ᵥ e := by
    rw [sub_mulVec, one_mulVec]; abel
  have hAx : M[A] *ᵥ x = x + (M[A] - 1) *ᵥ x := by
    rw [sub_mulVec, one_mulVec]; abel
  have hy : h ⬝ᵥ (M[A] *ᵥ e) = 1 := by
    rw [hAe, dotProduct_add, hv, hNe, add_zero]
  have hL : M[g₀] *ᵥ (M[A] *ᵥ e) = M[A] *ᵥ e + x := by
    rw [hgM, oneAdd_mulVec, hy, one_smul]
  have hR : M[g₀] *ᵥ e = e + x := by
    rw [hgM, oneAdd_mulVec, hv, one_smul]
  have hmat := congrArg (fun g : Matrix.SpecialLinearGroup (Fin n) (ZMod 2) => M[g] *ᵥ e) hcomm
  simp only [Matrix.SpecialLinearGroup.coe_mul] at hmat
  rw [← mulVec_mulVec, ← mulVec_mulVec, hL, hR, mulVec_add, hAx] at hmat
  exact hx (left_eq_add.1 (add_left_cancel hmat))

theorem mem_normalizer_comap {G H : Type} [Group G] [Group H] (e : G ≃* H) (U : Subgroup H)
    (g : G) :
    g ∈ normalizer ((U.comap e.toMonoidHom : Subgroup G) : Set G) ↔
      e g ∈ normalizer (U : Set H) := by
  simp only [Subgroup.mem_normalizer_iff, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom,
    map_mul, map_inv]
  constructor
  · intro hg h'
    obtain ⟨h, rfl⟩ := e.surjective h'
    exact hg h
  · intro hg h
    exact hg (e h)

theorem not_isMaxTwoLocal_centralizer_SL {G : Type} [Group G] (hn : 3 ≤ n)
    (e : G ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) {z : G} (hz : orderOf z = 2) :
    ¬ IsMaxTwoLocalSubgroup (centralizer ({z} : Set G)) := by
  intro hmax
  have hz2 : z * z = 1 := by rw [← pow_two, ← hz, pow_orderOf_eq_one]
  have hAA0 : e z * e z = 1 := by rw [← map_mul, hz2, map_one]
  have hAA : M[e z] * M[e z] = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, hAA0, Matrix.SpecialLinearGroup.coe_one]
  have hA1 : e z ≠ 1 := by
    intro h
    have hz1 : z = 1 := e.injective (by rw [h, map_one])
    rw [hz1, orderOf_one] at hz
    norm_num at hz
  obtain ⟨g₀, hg₀comm, hg₀N⟩ := exists_normalizing_element hn hAA hA1
  obtain ⟨-, hbot, htop, -⟩ := W_of_facts hAA hA1
  obtain ⟨u₁, hu₁, hu₁1⟩ := exists_ne_one_unip hbot htop
  let P : Subgroup G := (unip (W_of (e z))).comap e.toMonoidHom
  have hPbot : P ≠ ⊥ := by
    intro h
    have hmem : e.symm u₁ ∈ P := by
      show e (e.symm u₁) ∈ unip (W_of (e z))
      rw [MulEquiv.apply_symm_apply]
      exact hu₁
    rw [h, Subgroup.mem_bot] at hmem
    apply hu₁1
    rw [← MulEquiv.apply_symm_apply e u₁, hmem, map_one]
  have hP2 : IsPGroup 2 P := by
    intro x
    refine ⟨1, ?_⟩
    have hx : e (x : G) ∈ unip (W_of (e z)) := x.2
    have hsq : e (x : G) * e (x : G) = 1 := by
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
      exact unip_mul_self _ hx
    apply Subtype.ext
    rw [Subgroup.coe_pow, pow_one, pow_two, OneMemClass.coe_one]
    exact e.injective (by rw [map_mul, map_one]; exact hsq)
  have hTL : IsTwoLocal (normalizer (P : Set G)) := ⟨P, hPbot, hP2, rfl⟩
  have hle : centralizer ({z} : Set G) ≤ normalizer (P : Set G) := by
    intro g hg
    rw [Subgroup.mem_centralizer_singleton_iff] at hg
    have hcomm : e g * e z = e z * e g := by
      have := congrArg e hg
      rwa [map_mul, map_mul] at this
    exact (mem_normalizer_comap e _ g).2 (normalizer_unip_of_comm hcomm)
  have heq := hmax.2 (normalizer (P : Set G)) hTL hle
  have hmem : e.symm g₀ ∈ normalizer (P : Set G) := by
    refine (mem_normalizer_comap e _ _).2 ?_
    rw [MulEquiv.apply_symm_apply]
    exact hg₀N
  rw [heq, Subgroup.mem_centralizer_singleton_iff] at hmem
  apply hg₀comm
  have := congrArg e hmem
  rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at this

theorem not_isMaxTwoLocal_centralizer_of_psl {G : Type} [Group G] (hn : 3 ≤ n)
    (e : G ≃* ProjectiveSpecialLinearGroup (Fin n) (ZMod 2)) {z : G} (hz : orderOf z = 2) :
    ¬ IsMaxTwoLocalSubgroup (centralizer ({z} : Set G)) :=
  not_isMaxTwoLocal_centralizer_SL hn
    (e.trans (CFSG.LargeExtraspecial.DW.slEquivPSL n).symm) hz

end CFSG.LocalAnalysis.GLTheoremA.Timm.L2
