module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.G2Pair
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.A2Split.Defs
public import CFSG.LieType.Chevalley.E6GraphInvertedRootRotation
public import CFSG.LieType.Chevalley.LangRootRankOne

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.CTP
  CFSG.HardMathSupport.Lang.D4Three CFSG.LieType.Steinberg.Adjoint

section Abstract

variable {G : Type*} [Group G] {K : Type*} [Field K]

theorem triple_mul {x₀ x₁ x₂ : K → G} (h0 : ∀ a b, x₀ (a + b) = x₀ a * x₀ b)
    (h1 : ∀ a b, x₁ (a + b) = x₁ a * x₁ b) (h2 : ∀ a b, x₂ (a + b) = x₂ a * x₂ b)
    (c01 : ∀ a b, Commute (x₀ a) (x₁ b)) (c02 : ∀ a b, Commute (x₀ a) (x₂ b))
    (c12 : ∀ a b, Commute (x₁ a) (x₂ b)) (a b e a' b' e' : K) :
    x₀ a * x₁ b * x₂ e * (x₀ a' * x₁ b' * x₂ e') = x₀ (a + a') * x₁ (b + b') * x₂ (e + e') := by
  rw [h0, h1, h2]
  have e1 : x₀ a * x₁ b * x₂ e * (x₀ a' * x₁ b' * x₂ e') =
      x₀ a * (x₁ b * (x₂ e * x₀ a')) * x₁ b' * x₂ e' := by group
  rw [e1, ← (c02 a' e).eq, ← mul_assoc (x₁ b), ← (c01 a' b).eq]
  have e2 : x₀ a * (x₀ a' * x₁ b * x₂ e) * x₁ b' * x₂ e' =
      x₀ a * x₀ a' * x₁ b * (x₂ e * x₁ b') * x₂ e' := by group
  rw [e2, ← (c12 b' e).eq]
  group

theorem mem_of_orbit (M : Subgroup G) (α : MulAut G) (hM : ∀ g, α g = g → g ∈ M)
    {x₀ x₁ x₂ : K → G} (h0 : ∀ a b, x₀ (a + b) = x₀ a * x₀ b)
    (h1 : ∀ a b, x₁ (a + b) = x₁ a * x₁ b) (h2 : ∀ a b, x₂ (a + b) = x₂ a * x₂ b)
    (z0 : x₀ 0 = 1) (z1 : x₁ 0 = 1) (z2 : x₂ 0 = 1)
    (c01 : ∀ a b, Commute (x₀ a) (x₁ b)) (c02 : ∀ a b, Commute (x₀ a) (x₂ b))
    (c12 : ∀ a b, Commute (x₁ a) (x₂ b)) {κ₀ κ₁ κ₂ : K}
    (hα0 : ∀ c, α (x₀ c) = x₁ (κ₀ * c)) (hα1 : ∀ c, α (x₁ c) = x₂ (κ₁ * c))
    (hα2 : ∀ c, α (x₂ c) = x₀ (κ₂ * c)) (hκ : κ₂ * κ₁ * κ₀ = 1)
    {d : G} (hd : d ∈ M) {μ₀ μ₁ μ₂ : K} (hd0 : ∀ c, d * x₀ c * d⁻¹ = x₀ (μ₀ * c))
    (hd1 : ∀ c, d * x₁ c * d⁻¹ = x₁ (μ₁ * c)) (hd2 : ∀ c, d * x₂ c * d⁻¹ = x₂ (μ₂ * c))
    (h01 : μ₀ ≠ μ₁) (h02 : μ₀ ≠ μ₂) (h12 : μ₁ ≠ μ₂) (c : K) : x₀ c ∈ M := by
  set u : K → G := fun a => x₀ a * x₁ (κ₀ * a) * x₂ (κ₁ * κ₀ * a) with hu
  have hufix : ∀ a, α (u a) = u a := by
    intro a
    simp only [hu, map_mul, hα0, hα1, hα2]
    rw [show κ₂ * (κ₁ * κ₀ * a) = a by rw [← mul_assoc, ← mul_assoc, hκ, one_mul]]
    rw [show κ₁ * (κ₀ * a) = κ₁ * κ₀ * a by ring]
    have e : x₁ (κ₀ * a) * x₂ (κ₁ * κ₀ * a) * x₀ a = x₀ a * x₁ (κ₀ * a) * x₂ (κ₁ * κ₀ * a) := by
      rw [mul_assoc, ← (c02 a _).eq, ← mul_assoc, ← (c01 a _).eq, mul_assoc]
    exact e
  have huM : ∀ a, u a ∈ M := fun a => hM _ (hufix a)
  have hconj1 : ∀ a b e, d * (x₀ a * x₁ b * x₂ e) * d⁻¹ =
      x₀ (μ₀ * a) * x₁ (μ₁ * b) * x₂ (μ₂ * e) := by
    intro a b e
    rw [← hd0, ← hd1, ← hd2]
    group
  have hconj2 : ∀ a b e, d * d * (x₀ a * x₁ b * x₂ e) * (d * d)⁻¹ =
      x₀ (μ₀ * (μ₀ * a)) * x₁ (μ₁ * (μ₁ * b)) * x₂ (μ₂ * (μ₂ * e)) := by
    intro a b e
    rw [← hconj1, show d * d * (x₀ a * x₁ b * x₂ e) * (d * d)⁻¹ =
      d * (d * (x₀ a * x₁ b * x₂ e) * d⁻¹) * d⁻¹ by group, hconj1]
  set D := (μ₀ - μ₁) * (μ₀ - μ₂) with hD
  have hD0 : D ≠ 0 := mul_ne_zero (sub_ne_zero.2 h01) (sub_ne_zero.2 h02)
  set a₀ := μ₁ * μ₂ / D * c
  set a₁ := -(μ₁ + μ₂) / D * c
  set a₂ := 1 / D * c
  have hm0 : u a₀ ∈ M := huM a₀
  have hm1 : d * u a₁ * d⁻¹ ∈ M := M.mul_mem (M.mul_mem hd (huM a₁)) (M.inv_mem hd)
  have hm2 : d * d * u a₂ * (d * d)⁻¹ ∈ M :=
    M.mul_mem (M.mul_mem (M.mul_mem hd hd) (huM a₂)) (M.inv_mem (M.mul_mem hd hd))
  have hprod := M.mul_mem (M.mul_mem hm0 hm1) hm2
  have tm := triple_mul h0 h1 h2 c01 c02 c12
  rw [hu] at hprod
  simp only at hprod
  rw [hconj1, hconj2, tm, tm] at hprod
  have ex0 : a₀ + μ₀ * a₁ + μ₀ * (μ₀ * a₂) = c := by
    simp only [a₀, a₁, a₂]
    field_simp
    ring
  have ex1 : κ₀ * a₀ + μ₁ * (κ₀ * a₁) + μ₁ * (μ₁ * (κ₀ * a₂)) = 0 := by
    simp only [a₀, a₁, a₂]
    field_simp
    ring
  have ex2 : κ₁ * κ₀ * a₀ + μ₂ * (κ₁ * κ₀ * a₁) + μ₂ * (μ₂ * (κ₁ * κ₀ * a₂)) = 0 := by
    simp only [a₀, a₁, a₂]
    field_simp
    ring
  rw [ex0, ex1, ex2, z1, z2, mul_one, mul_one] at hprod
  exact hprod

end Abstract

section D4


variable {K : Type} [Field K]

local notation "𝕩" => xPar (rootOperatorFamily Tag.D4)

theorem coe_xPar_eq_pinnedX_sign {γ : Fin Tag.D4.rank → ℤ} (hγ : IsRoot Tag.D4 γ) :
    ∃ s : K, s * s = 1 ∧ ∀ c : K, ((𝕩 γ c : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K) =
      pinnedX Tag.D4 K γ (s * c) := by
  refine ⟨((rootOperatorFamily Tag.D4).pinnedFamilySign γ : K),
    (rootOperatorFamily Tag.D4).pinnedFamilySign_mul_self K γ, fun c => ?_⟩
  rw [(rootOperatorFamily Tag.D4).pinnedX_eq_eltUnit K hγ, ← mul_assoc,
    (rootOperatorFamily Tag.D4).pinnedFamilySign_mul_self K γ, one_mul, xPar_of_isRoot hγ]
  rfl

@[expose] def rhoL (v : Fin Tag.D4.rank → ℤ) : Fin Tag.D4.rank → ℤ := permLattice TwistTag.D4.perm v

theorem isRoot_rhoL {v : Fin Tag.D4.rank → ℤ} (hv : IsRoot Tag.D4 v) : IsRoot Tag.D4 (rhoL v) :=
  hv.permLattice TwistTag.D4.cartan_perm

theorem d4Graph_one_xPar {γ : Fin Tag.D4.rank → ℤ} (hγ : IsRoot Tag.D4 γ) :
    ∃ ε : K, ε * ε = 1 ∧ ∀ c : K,
      d4Graph K 1 (𝕩 γ c) = 𝕩 (rhoL γ) (ε * c) := by
  have hργ : IsRoot Tag.D4 (rhoL γ) := isRoot_rhoL hγ
  obtain ⟨s, hs, hγs⟩ := coe_xPar_eq_pinnedX_sign (K := K) hγ
  obtain ⟨s', hs', hργs⟩ := coe_xPar_eq_pinnedX_sign (K := K) hργ
  obtain ⟨ε₀, hε₀, hP⟩ := diagramMap_conj_pinnedX (K := K) TwistTag.D4 hγ
  refine ⟨s' * ε₀ * s, ?_, fun c => Subtype.ext ?_⟩
  · calc s' * ε₀ * s * (s' * ε₀ * s) = (s' * s') * (ε₀ * ε₀) * (s * s) := by ring
      _ = 1 := by rw [hs, hs', hε₀]; ring
  · rw [coe_d4Graph, pow_one, hγs, hργs]
    have h1 := hP (s * c)
    have h2 : s' * (s' * ε₀ * s * c) = ε₀ * (s * c) := by
      calc s' * (s' * ε₀ * s * c) = (s' * s') * (ε₀ * (s * c)) := by ring
        _ = ε₀ * (s * c) := by rw [hs', one_mul]
    rw [h2]
    exact h1

theorem torusElement_xPar (i : Fin Tag.D4.rank) (t : Kˣ) {γ : Fin Tag.D4.rank → ℤ}
    (hγ : IsRoot Tag.D4 γ) (c : K) :
    torusElement Tag.D4 K i t * 𝕩 γ c * (torusElement Tag.D4 K i t)⁻¹ =
      𝕩 γ (((t ^ (∑ j, Tag.D4.cartan i j * γ j) : Kˣ) : K) * c) := by
  rw [xPar_of_isRoot hγ, xPar_of_isRoot hγ]
  exact (rootOperatorFamily Tag.D4).torusElement_mul_eltElement_mul_inv i t ⟨γ, hγ⟩ c

theorem sl2At_HSL (i : Fin Tag.D4.rank) (t : Kˣ) : sl2At K i (HSL t) = torusElement Tag.D4 K i t :=
  Subtype.ext (simpleRootSL2_HSL i t)

theorem HSL_mul (a b : Kˣ) : HSL a * HSL b = HSL (a * b) := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul]
  simp only [HSL]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

theorem HSL_pow_three {ω : Kˣ} (hω : ω ^ 3 = 1) : HSL ω ^ 3 = 1 := by
  rw [pow_succ, pow_two, HSL_mul, HSL_mul, ← pow_two, ← pow_succ, hω]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [HSL]

theorem gammaP_pow_three {B : SL2 K} (hB : B ^ 3 = 1) : gammaP K B ^ 3 = 1 := by
  have hc : Commute (MulAut.conj (sl2At K ⟨2, by decide⟩ B)) (d4Graph K 1) := by
    refine MulEquiv.ext fun y => ?_
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, d4Graph_one_sl2Two]
  have h3 : d4Graph K 1 ^ 3 = 1 := by
    rw [pow_succ, pow_two, ← CFSG.LieType.SeitzGeneration.ExcWideThree.d4Graph_add,
      ← CFSG.LieType.SeitzGeneration.ExcWideThree.d4Graph_add,
      CFSG.LieType.SeitzGeneration.ExcWideThree.d4Graph_three]
  rw [gammaP, hc.mul_pow, ← map_pow, ← map_pow, hB, map_one, map_one, one_mul, h3]

theorem gammaP_HSL_xPar (ω : Kˣ) {γ : Fin Tag.D4.rank → ℤ} (hγ : IsRoot Tag.D4 γ) :
    ∃ κ : K, κ ≠ 0 ∧ ∀ c : K,
      gammaP K (HSL ω) (𝕩 γ c) = 𝕩 (rhoL γ) (κ * c) := by
  obtain ⟨ε, hε, h⟩ := d4Graph_one_xPar (K := K) hγ
  have hργ : IsRoot Tag.D4 (rhoL γ) := isRoot_rhoL hγ
  refine ⟨((ω ^ (∑ j, Tag.D4.cartan ⟨2, by decide⟩ j * rhoL γ j) :
    Kˣ) : K) * ε, mul_ne_zero (Units.ne_zero _) ?_, fun c => ?_⟩
  · intro h0
    rw [h0, zero_mul] at hε
    exact zero_ne_one hε
  · rw [gammaP, MulAut.mul_apply, MulAut.conj_apply, h, sl2At_HSL, torusElement_xPar _ _ hργ,
      mul_assoc]

@[expose] def orbitRoots : List (Fin Tag.D4.rank → ℤ) :=
  [![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 0, 1], ![1, 0, 1, 0], ![0, 1, 1, 0], ![0, 0, 1, 1],
    ![1, 1, 1, 0], ![0, 1, 1, 1], ![1, 0, 1, 1], ![-1, 0, 0, 0], ![0, -1, 0, 0],
    ![0, 0, 0, -1], ![-1, 0, -1, 0], ![0, -1, -1, 0], ![0, 0, -1, -1], ![-1, -1, -1, 0],
    ![0, -1, -1, -1], ![-1, 0, -1, -1]]

@[expose] def dExp (r : Fin Tag.D4.rank → ℤ) : ℤ :=
  ∑ j, Tag.D4.cartan ⟨0, by decide⟩ j * r j - ∑ j, Tag.D4.cartan ⟨1, by decide⟩ j * r j

theorem orbitRoots_facts : ∀ r ∈ orbitRoots,
    IsRoot Tag.D4 r ∧ IsRoot Tag.D4 (rhoL r) ∧
    IsRoot Tag.D4 (rhoL (rhoL r)) ∧
    rhoL (rhoL
      (rhoL r)) = r ∧
    r ≠ rhoL r ∧ r ≠ -rhoL r ∧
    ¬IsRoot Tag.D4 (r + rhoL r) ∧
    r ≠ rhoL (rhoL r) ∧
    r ≠ -rhoL (rhoL r) ∧
    ¬IsRoot Tag.D4 (r + rhoL (rhoL r)) ∧
    rhoL r ≠
      rhoL (rhoL r) ∧
    rhoL r ≠
      -rhoL (rhoL r) ∧
    ¬IsRoot Tag.D4 (rhoL r +
      rhoL (rhoL r)) ∧
    dExp r ≠ dExp (rhoL r) ∧
    dExp r ≠ dExp (rhoL (rhoL r)) ∧
    dExp (rhoL r) ≠
      dExp (rhoL (rhoL r)) ∧
    dExp r ∈ ({2, -2, 0} : Finset ℤ) ∧
    dExp (rhoL r) ∈ ({2, -2, 0} : Finset ℤ) ∧
    dExp (rhoL (rhoL r)) ∈
      ({2, -2, 0} : Finset ℤ) := by
  simp only [isRoot_iff_mem_artifactRoots]
  decide

theorem val_zpow_ne_of_four {l : Kˣ} (hl : l ^ 4 ≠ 1) {m n : ℤ}
    (hm : m ∈ ({2, -2, 0} : Finset ℤ)) (hn : n ∈ ({2, -2, 0} : Finset ℤ)) (hmn : m ≠ n) :
    ((l ^ m : Kˣ) : K) ≠ ((l ^ n : Kˣ) : K) := by
  intro h
  have h' : l ^ m = l ^ n := Units.ext h
  have h1 : l ^ (m - n) = 1 := by rw [zpow_sub, h', mul_inv_cancel]
  have h2 : ∀ k : ℤ, l ^ k = 1 → (k = 2 ∨ k = -2 ∨ k = 4 ∨ k = -4) → l ^ 4 = 1 := by
    intro k hk hk'
    rcases hk' with rfl | rfl | rfl | rfl
    · have : l ^ (4 : ℤ) = 1 := by
        rw [show (4 : ℤ) = 2 * 2 by norm_num, zpow_mul, hk, one_zpow]
      exact_mod_cast this
    · have : l ^ (4 : ℤ) = 1 := by
        rw [show (4 : ℤ) = -2 * -2 by norm_num, zpow_mul, hk, one_zpow]
      exact_mod_cast this
    · exact_mod_cast hk
    · have : l ^ (4 : ℤ) = 1 := by
        rw [show (4 : ℤ) = -4 * -1 by norm_num, zpow_mul, hk, one_zpow]
      exact_mod_cast this
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm hn
  refine hl (h2 (m - n) h1 ?_)
  rcases hm with rfl | rfl | rfl <;> rcases hn with rfl | rfl | rfl <;>
    first | exact absurd rfl hmn | norm_num

theorem dTorus_xPar (l : Kˣ) {r : Fin Tag.D4.rank → ℤ} (hr : IsRoot Tag.D4 r) (c : K) :
    torusElement Tag.D4 K ⟨0, by decide⟩ l * torusElement Tag.D4 K ⟨1, by decide⟩ l⁻¹ * 𝕩 r c *
        (torusElement Tag.D4 K ⟨0, by decide⟩ l * torusElement Tag.D4 K ⟨1, by decide⟩ l⁻¹)⁻¹ =
      𝕩 r (((l ^ dExp r : Kˣ) : K) * c) := by
  rw [show torusElement Tag.D4 K ⟨0, by decide⟩ l * torusElement Tag.D4 K ⟨1, by decide⟩ l⁻¹ *
      𝕩 r c * (torusElement Tag.D4 K ⟨0, by decide⟩ l *
        torusElement Tag.D4 K ⟨1, by decide⟩ l⁻¹)⁻¹ =
      torusElement Tag.D4 K ⟨0, by decide⟩ l * (torusElement Tag.D4 K ⟨1, by decide⟩ l⁻¹ *
        𝕩 r c * (torusElement Tag.D4 K ⟨1, by decide⟩ l⁻¹)⁻¹) *
          (torusElement Tag.D4 K ⟨0, by decide⟩ l)⁻¹ by group,
    torusElement_xPar _ _ hr, torusElement_xPar _ _ hr, ← mul_assoc, ← Units.val_mul, inv_zpow',
    ← zpow_add, dExp, sub_eq_add_neg]

theorem closure_fixedSubgroup_gammaP_HSL_torus {ω : Kˣ} (hω : ω ^ 3 = 1) {l : Kˣ}
    (hl : l ^ 4 ≠ 1) :
    Subgroup.closure ((fixedSubgroup (gammaP K (HSL ω)) : Set ↥(adjointGroup Tag.D4 K)) ∪
      {torusElement Tag.D4 K ⟨0, by decide⟩ l * torusElement Tag.D4 K ⟨1, by decide⟩ l⁻¹}) =
      ⊤ := by
  set α := gammaP K (HSL ω) with hαdef
  set M := Subgroup.closure ((fixedSubgroup α : Set ↥(adjointGroup Tag.D4 K)) ∪
      {torusElement Tag.D4 K ⟨0, by decide⟩ l * torusElement Tag.D4 K ⟨1, by decide⟩ l⁻¹})
    with hMdef
  have hM : ∀ g, α g = g → g ∈ M := fun g hg => Subgroup.subset_closure (Or.inl hg)
  have hd : torusElement Tag.D4 K ⟨0, by decide⟩ l * torusElement Tag.D4 K ⟨1, by decide⟩ l⁻¹ ∈
      M := Subgroup.subset_closure (Or.inr rfl)
  have hα3 : ∀ g, α (α (α g)) = g := by
    intro g
    have h := congrArg (fun φ : MulAut ↥(adjointGroup Tag.D4 K) => φ g)
      (gammaP_pow_three (HSL_pow_three hω))
    simpa [pow_succ, MulAut.mul_apply] using h
  have horb : ∀ r ∈ orbitRoots, ∀ c, 𝕩 r c ∈ M := by
    intro r hr c
    obtain ⟨h0, h1, h2, h3, n01, m01, s01, n02, m02, s02, n12, m12, s12, e01, e02, e12, em0, em1,
      em2⟩ := orbitRoots_facts r hr
    obtain ⟨κ₀, -, hκ₀⟩ := gammaP_HSL_xPar ω h0
    obtain ⟨κ₁, -, hκ₁⟩ := gammaP_HSL_xPar ω h1
    obtain ⟨κ₂, -, hκ₂⟩ := gammaP_HSL_xPar ω h2
    rw [h3] at hκ₂
    have hκ : κ₂ * κ₁ * κ₀ = 1 := by
      have h := hα3 (𝕩 r 1)
      rw [hκ₀, hκ₁, hκ₂] at h
      have h' := xPar_injective h0 h
      linear_combination h'
    exact mem_of_orbit M α hM (fun a b => xPar_add r a b) (fun a b => xPar_add _ a b)
      (fun a b => xPar_add _ a b) (xPar_zero r) (xPar_zero _) (xPar_zero _)
      (fun a b => CFSG.LieType.Steinberg.TwistedD4.commute_xPar h0 h1 n01 m01 s01 a b)
      (fun a b => CFSG.LieType.Steinberg.TwistedD4.commute_xPar h0 h2 n02 m02 s02 a b)
      (fun a b => CFSG.LieType.Steinberg.TwistedD4.commute_xPar h1 h2 n12 m12 s12 a b)
      hκ₀ hκ₁ hκ₂ hκ hd (dTorus_xPar l h0) (dTorus_xPar l h1) (dTorus_xPar l h2)
      (val_zpow_ne_of_four hl em0 em1 e01) (val_zpow_ne_of_four hl em0 em2 e02)
      (val_zpow_ne_of_four hl em1 em2 e12) c
  have hsingle : ∀ i : Fin Tag.D4.rank, i ≠ ⟨2, by decide⟩ →
      Pi.single i 1 ∈ orbitRoots ∧ -Pi.single i 1 ∈ orbitRoots := by decide
  refine eq_top_of_simple_mem fun i c => ?_
  by_cases hi : i = ⟨2, by decide⟩
  · subst hi
    have hn0 : CFSG.LieType.Steinberg.weylElement 𝕩 ⟨0, by decide⟩ (1 : Kˣ) ∈ M := by
      unfold CFSG.LieType.Steinberg.weylElement
      exact M.mul_mem (M.mul_mem (horb _ (by decide) _) (horb _ (by decide) _))
        (horb _ (by decide) _)
    have hfacts : (Pi.single (⟨0, by decide⟩ : Fin Tag.D4.rank) 1 +
          Pi.single ⟨2, by decide⟩ 1) ∈ orbitRoots ∧
        -(Pi.single (⟨0, by decide⟩ : Fin Tag.D4.rank) 1 + Pi.single ⟨2, by decide⟩ 1) ∈
          orbitRoots ∧
        reflect Tag.D4 ⟨0, by decide⟩ (Pi.single ⟨0, by decide⟩ 1 + Pi.single ⟨2, by decide⟩ 1) =
          Pi.single ⟨2, by decide⟩ 1 ∧
        reflect Tag.D4 ⟨0, by decide⟩ (-(Pi.single ⟨0, by decide⟩ 1 +
          Pi.single ⟨2, by decide⟩ 1)) = -Pi.single ⟨2, by decide⟩ 1 := by decide
    obtain ⟨m1, m2, e1, e2⟩ := hfacts
    obtain ⟨hr1, -⟩ := orbitRoots_facts _ m1
    obtain ⟨hr2, -⟩ := orbitRoots_facts _ m2
    obtain ⟨ε, hε, hc⟩ := exists_weyl_conj (K := K) ⟨0, by decide⟩ hr1
    obtain ⟨ε', hε', hc'⟩ := exists_weyl_conj (K := K) ⟨0, by decide⟩ hr2
    rw [e1] at hc
    rw [e2] at hc'
    exact ⟨mem_of_conj_eq hn0 hε hc (horb _ m1) c, mem_of_conj_eq hn0 hε' hc' (horb _ m2) c⟩
  · obtain ⟨h1, h2⟩ := hsingle i hi
    exact ⟨horb _ h1 c, horb _ h2 c⟩

end D4

end CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph
