module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotAutU

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap CFSG.ClassicalGroups.Orthogonal
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (plusIndexEquiv minusIndexEquiv coordinateQuadPlus coordinateQuadMinus regular_coordinateQuadPlus
    regular_coordinateQuadMinus)

variable {K : Type*} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

@[expose] def IsLongRoot (Q : QuadraticForm K (Fin d → K)) (z : matrixProjectiveDerived Q) :
    Prop :=
  ∃ u w : Fin d → K, Q u = 0 ∧ Q w = 0 ∧ polar Q u w = 0 ∧ LinearIndependent K ![u, w] ∧
    ∃ E : orthDerived Q, (E : (Fin d → K) ≃ₗ[K] (Fin d → K)) = eichler Q u w ∧ projHom Q E = z

theorem IsLongRoot.conj {z : matrixProjectiveDerived Q} (hz : IsLongRoot Q z)
    (x : matrixProjectiveDerived Q) : IsLongRoot Q (x * z * x⁻¹) := by
  obtain ⟨u, w, hu, hw, huw, hind, E, hE, rfl⟩ := hz
  obtain ⟨X, rfl⟩ := projHom_surjective Q x
  have hXO : (X : (Fin d → K) ≃ₗ[K] (Fin d → K)) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    Subgroup.commutator_le_self _ X.2
  refine ⟨(X : (Fin d → K) ≃ₗ[K] (Fin d → K)) u, (X : (Fin d → K) ≃ₗ[K] (Fin d → K)) w,
    by rw [map_of_mem hXO, hu], by rw [map_of_mem hXO, hw], by rw [polar_map_of_mem hXO, huw],
    ?_, X * E * X⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
  · rw [LinearIndependent.pair_iff] at hind ⊢
    intro s t hst
    apply hind s t
    apply (X : (Fin d → K) ≃ₗ[K] (Fin d → K)).injective
    rw [map_add, map_smul, map_smul, hst, map_zero]
  · change (X : (Fin d → K) ≃ₗ[K] (Fin d → K)) * E * (X : (Fin d → K) ≃ₗ[K] (Fin d → K))⁻¹ = _
    rw [hE, eichler_conj hXO]

theorem exists_mem_elementaryGroup_apply_pair (hQ : (polarBilin Q).Nondegenerate)
    {P₁ P₂ P₃ : HypPair Q} (h₁₂ : P₁.Orth P₂) (h₁₃ : P₁.Orth P₃) (h₂₃ : P₂.Orth P₃)
    {u w : Fin d → K} (hu : Q u = 0) (hw : Q w = 0) (huw : polar Q u w = 0)
    (hind : LinearIndependent K ![u, w]) :
    ∃ g ∈ elementaryGroup Q, g u = P₁.e ∧ g w = P₂.e := by
  rw [LinearIndependent.pair_iff] at hind
  have hu0 : u ≠ 0 := fun h0 => by
    have := (hind 1 0 (by rw [h0, smul_zero, zero_smul, add_zero])).1
    exact one_ne_zero this
  obtain ⟨g₁, hg₁, hg₁u⟩ := exists_mem_elementaryGroup_apply_eq hQ h₁₂ hu0 P₁.e_ne_zero
    (by rw [hu, P₁.Q_e])
  have hg₁O := elementaryGroup_le_orthogonalGroup Q hg₁
  have hx : Q (g₁ w) = 0 := by rw [map_of_mem hg₁O, hw]
  have hex : polar Q P₁.e (g₁ w) = 0 := by rw [← hg₁u, polar_map_of_mem hg₁O, huw]
  have hxe : ∀ c : K, g₁ w ≠ c • P₁.e := by
    intro c hc
    rw [← hg₁u, ← map_smul] at hc
    have h1 := g₁.injective hc
    have := (hind (-c) 1 (by rw [h1, neg_smul, one_smul, neg_add_cancel])).2
    exact one_ne_zero this
  obtain ⟨g₂, hg₂, hg₂e, hg₂x⟩ := exists_fix_apply_eq_of_polar_eq_zero h₁₂ h₁₃ h₂₃ hQ hx hex hxe
  refine ⟨g₂ * g₁, mul_mem hg₂ hg₁, ?_, ?_⟩
  · rw [LinearEquiv.mul_apply, hg₁u, hg₂e]
  · rw [LinearEquiv.mul_apply, hg₂x]

theorem isConj_of_isLongRoot [Finite K] (hQ : (polarBilin Q).Nondegenerate)
    {P₁ P₂ P₃ : HypPair Q} (h₁₂ : P₁.Orth P₂) (h₁₃ : P₁.Orth P₃) (h₂₃ : P₂.Orth P₃)
    {z z' : matrixProjectiveDerived Q} (hz : IsLongRoot Q z) (hz' : IsLongRoot Q z') :
    IsConj z z' := by
  have hT := exists_totallySingular_of_hypPairs h₁₂ h₁₃ h₂₃
  have hEΩ : elementaryGroup Q ≤ orthDerived Q := elementaryGroup_le_orthDerived hQ hT
  obtain ⟨u, w, hu, hw, huw, hind, E, hE, rfl⟩ := hz
  obtain ⟨u', w', hu', hw', huw', hind', E', hE', rfl⟩ := hz'
  obtain ⟨g, hg, hgu, hgw⟩ := exists_mem_elementaryGroup_apply_pair hQ h₁₂ h₁₃ h₂₃ hu hw huw hind
  obtain ⟨g', hg', hg'u, hg'w⟩ :=
    exists_mem_elementaryGroup_apply_pair hQ h₁₂ h₁₃ h₂₃ hu' hw' huw' hind'
  set h := g'⁻¹ * g with hh
  have hhE : h ∈ elementaryGroup Q := mul_mem (inv_mem hg') hg
  have hhO := elementaryGroup_le_orthogonalGroup Q hhE
  have hhu : h u = u' := by
    rw [hh, LinearEquiv.mul_apply, hgu, ← hg'u, LinearEquiv.inv_apply_apply']
  have hhw : h w = w' := by
    rw [hh, LinearEquiv.mul_apply, hgw, ← hg'w, LinearEquiv.inv_apply_apply']
  rw [isConj_iff]
  refine ⟨projHom Q ⟨h, hEΩ hhE⟩, ?_⟩
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  change h * (E : (Fin d → K) ≃ₗ[K] (Fin d → K)) * h⁻¹ = E'
  rw [hE, hE', eichler_conj hhO, hhu, hhw]

theorem isLongRoot_of_commute_rootSylow [Finite K] [CharP K 2]
    (hQ : (polarBilin Q).Nondegenerate) {P₁ P₂ P₃ : HypPair Q} (h₁₂ : P₁.Orth P₂)
    (h₁₃ : P₁.Orth P₃) (h₂₃ : P₂.Orth P₃) {z : matrixProjectiveDerived Q} (hz1 : z ≠ 1)
    (hz : ∀ r ∈ rootSylowBar (Q := Q) P₁.e P₂.e, r * z = z * r) : IsLongRoot Q z := by
  have hT := exists_totallySingular_of_hypPairs h₁₂ h₁₃ h₂₃
  have hQ' := exists_map_ne_zero_of_hypPair P₁
  obtain ⟨Z, rfl⟩ := projHom_surjective Q z
  have hZO : (Z : (Fin d → K) ≃ₗ[K] (Fin d → K)) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    Subgroup.commutator_le_self _ Z.2
  have hcommR : ∀ E : orthDerived Q,
      (E : (Fin d → K) ≃ₗ[K] (Fin d → K)) ∈ rootSylowSub (Q := Q) P₁.e P₂.e →
        ∀ x, (Z : (Fin d → K) ≃ₗ[K] (Fin d → K)) ((E : (Fin d → K) ≃ₗ[K] (Fin d → K)) x) =
          (E : (Fin d → K) ≃ₗ[K] (Fin d → K)) ((Z : (Fin d → K) ≃ₗ[K] (Fin d → K)) x) := by
    intro E hE x
    have h := hz _ (projHom_mem_rootSylowBar hE)
    rw [← map_mul, ← map_mul] at h
    have h' := congrArg (fun A : orthDerived Q => (A : (Fin d → K) ≃ₗ[K] (Fin d → K)) x)
      (projHom_injective hQ' h)
    exact h'.symm
  obtain ⟨-, γ, -, x₀, -, hx₀, hZ⟩ := eq_smul_eichler_of_commute (φ := (Z : (Fin d → K) ≃ₗ[K]
      (Fin d → K)).toAddEquiv) (σ := RingEquiv.refl K) (μ := 1) (polarNondegOn_top hQ) h₁₂
    Submodule.mem_top Submodule.mem_top Submodule.mem_top Submodule.mem_top one_ne_zero
    (fun c x => by simp) (fun x => by simp [map_of_mem hZO]) (fun _ _ => Submodule.mem_top)
    (fun w _ hw x _ => hcommR ⟨eichler Q P₁.e w, eichler_mem_orthDerived hQ hT _ _⟩
      (eichler_mem_rootSylowSub_left hw _) x)
  have hZ' : ∀ x, (Z : (Fin d → K) ≃ₗ[K] (Fin d → K)) x = γ • eichler Q P₁.e x₀ x :=
    fun x => hZ x Submodule.mem_top
  have hγ : γ = 1 := by
    apply eq_one_of_mul_self_eq_one
    have h1 := map_of_mem hZO (P₂.e + P₂.f)
    rw [hZ', map_smul_eq_sq, map_of_mem (eichler_mem_orthogonalGroup Q P₁.e x₀),
      QuadraticMap.map_add Q, P₂.Q_e, P₂.Q_f, P₂.polar_ef] at h1
    linear_combination h1
  have hZE : ∀ x, (Z : (Fin d → K) ≃ₗ[K] (Fin d → K)) x = eichler Q P₁.e x₀ x := fun x => by
    rw [hZ', hγ, one_smul]
  have hx₀e : x₀ = polar Q x₀ P₂.f • P₂.e := by
    refine eq_smul_of_forall_commute_eichler hQ h₁₂ h₁₃ h₂₃ hx₀ fun w h2w h1w => ?_
    apply LinearEquiv.ext
    intro x
    have h := hcommR ⟨eichler Q P₂.e w, eichler_mem_orthDerived hQ hT _ _⟩
      (eichler_mem_rootSylowSub_right h₁₂.ee h2w h1w) x
    simp only [LinearEquiv.mul_apply]
    rw [← hZE, ← hZE]
    exact h.symm
  set c := polar Q x₀ P₂.f with hc
  have hc0 : c ≠ 0 := by
    intro h0
    apply hz1
    have hZ1 : Z = 1 := by
      apply Subtype.ext
      apply LinearEquiv.ext
      intro x
      rw [hZE, hx₀e, h0, zero_smul, eichler_zero_right]
      rfl
    rw [hZ1, map_one]
  have he₂f₁ : polar Q P₂.e P₁.f = 0 := by rw [polar_comm]; exact h₁₂.fe
  refine ⟨P₁.e, c • P₂.e, P₁.Q_e, by rw [map_smul_eq_sq, P₂.Q_e, mul_zero],
    by rw [polar_smul_right_eq, h₁₂.ee, mul_zero], ?_, Z, ?_, rfl⟩
  · rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 := congrArg (fun v => polar Q v P₁.f) hst
    have h2 := congrArg (fun v => polar Q v P₂.f) hst
    simp only [polar_add_left, polar_smul_left_eq, P₁.polar_ef, he₂f₁, h₁₂.ef, P₂.polar_ef,
      polar_zero_left] at h1 h2
    have hs : s = 0 := by linear_combination h1
    refine ⟨hs, ?_⟩
    have : t * c = 0 := by linear_combination h2
    exact (mul_eq_zero.mp this).resolve_right hc0
  · apply LinearEquiv.ext
    intro x
    rw [hZE, ← hx₀e]

theorem isLongRoot_of_commute_sylow [Finite K] [CharP K 2] (hQ : (polarBilin Q).Nondegenerate)
    {P₁ P₂ P₃ : HypPair Q} (h₁₂ : P₁.Orth P₂) (h₁₃ : P₁.Orth P₃) (h₂₃ : P₂.Orth P₃)
    (U : Sylow 2 (matrixProjectiveDerived Q)) {z : matrixProjectiveDerived Q} (hz1 : z ≠ 1)
    (hz : ∀ u ∈ (U : Subgroup (matrixProjectiveDerived Q)), u * z = z * u) : IsLongRoot Q z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_conj_mem_sylow (isPGroup_rootSylowBar (Q := Q) P₁.e P₂.e) U
  have h := isLongRoot_of_commute_rootSylow hQ h₁₂ h₁₃ h₂₃ (z := x⁻¹ * z * x)
    (fun h0 => hz1 (by
      have e : z = x * (x⁻¹ * z * x) * x⁻¹ := by group
      rw [e, h0]
      group))
    (fun r hr => by
      have h1 := hz _ (hx r hr)
      calc r * (x⁻¹ * z * x) = x⁻¹ * ((x * r * x⁻¹) * z) * x := by group
        _ = x⁻¹ * (z * (x * r * x⁻¹)) * x := by rw [h1]
        _ = x⁻¹ * z * x * r := by group)
  have := h.conj x
  rwa [show x * (x⁻¹ * z * x) * x⁻¹ = z by group] at this

section Coordinates

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] [CharP K 2] in
theorem exists_three_pairs_plus {n : ℕ} (hn : 3 ≤ n) :
    ∃ P₁ P₂ P₃ : HypPair (coordinateQuadPlus n K), P₁.Orth P₂ ∧ P₁.Orth P₃ ∧ P₂.Orth P₃ := by
  have h0 := isHypCoord_coordinateQuadPlus (K := K) (⟨0, by omega⟩ : Fin n)
  have h1 := isHypCoord_coordinateQuadPlus (K := K) (⟨1, by omega⟩ : Fin n)
  have h2 := isHypCoord_coordinateQuadPlus (K := K) (⟨2, by omega⟩ : Fin n)
  exact ⟨h0.hypPair, h1.hypPair, h2.hypPair, h0.orth h1 (pairDisjoint_plus (by simp [Fin.ext_iff])),
    h0.orth h2 (pairDisjoint_plus (by simp [Fin.ext_iff])),
    h1.orth h2 (pairDisjoint_plus (by simp [Fin.ext_iff]))⟩

omit [Finite K] [CharP K 2] in
theorem exists_three_pairs_minus {n : ℕ} (hn : 4 ≤ n) (b c : K) :
    ∃ P₁ P₂ P₃ : HypPair (coordinateQuadMinus n K (by omega) b c),
      P₁.Orth P₂ ∧ P₁.Orth P₃ ∧ P₂.Orth P₃ := by
  have h0 := isHypCoord_coordinateQuadMinus (K := K) (by omega : 1 ≤ n) b c
    (⟨0, by omega⟩ : Fin (n - 1))
  have h1 := isHypCoord_coordinateQuadMinus (K := K) (by omega : 1 ≤ n) b c
    (⟨1, by omega⟩ : Fin (n - 1))
  have h2 := isHypCoord_coordinateQuadMinus (K := K) (by omega : 1 ≤ n) b c
    (⟨2, by omega⟩ : Fin (n - 1))
  exact ⟨h0.hypPair, h1.hypPair, h2.hypPair,
    h0.orth h1 (pairDisjoint_minus _ (by simp [Fin.ext_iff])),
    h0.orth h2 (pairDisjoint_minus _ (by simp [Fin.ext_iff])),
    h1.orth h2 (pairDisjoint_minus _ (by simp [Fin.ext_iff]))⟩

omit [CharP K 2] in
theorem isConj_of_isLongRoot_plus {n : ℕ} (hn : 3 ≤ n)
    {z z' : matrixProjectiveDerived (coordinateQuadPlus n K)}
    (hz : IsLongRoot _ z) (hz' : IsLongRoot _ z') : IsConj z z' := by
  obtain ⟨P₁, P₂, P₃, h₁₂, h₁₃, h₂₃⟩ := exists_three_pairs_plus (K := K) hn
  exact isConj_of_isLongRoot (regular_coordinateQuadPlus n K hn).1 h₁₂ h₁₃ h₂₃ hz hz'

omit [CharP K 2] in
theorem isConj_of_isLongRoot_minus {n : ℕ} (hn : 4 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {z z' : matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c)}
    (hz : IsLongRoot _ z) (hz' : IsLongRoot _ z') : IsConj z z' := by
  obtain ⟨P₁, P₂, P₃, h₁₂, h₁₃, h₂₃⟩ := exists_three_pairs_minus (K := K) hn b c
  exact isConj_of_isLongRoot (regular_coordinateQuadMinus n K b c hn hirr).1 h₁₂ h₁₃ h₂₃ hz hz'

theorem isLongRoot_of_commute_sylow_plus {n : ℕ} (hn : 3 ≤ n)
    (U : Sylow 2 (matrixProjectiveDerived (coordinateQuadPlus n K)))
    {z : matrixProjectiveDerived (coordinateQuadPlus n K)} (hz1 : z ≠ 1)
    (hz : ∀ u ∈ (U : Subgroup (matrixProjectiveDerived (coordinateQuadPlus n K))),
      u * z = z * u) : IsLongRoot _ z := by
  obtain ⟨P₁, P₂, P₃, h₁₂, h₁₃, h₂₃⟩ := exists_three_pairs_plus (K := K) hn
  exact isLongRoot_of_commute_sylow (regular_coordinateQuadPlus n K hn).1 h₁₂ h₁₃ h₂₃ U hz1 hz

theorem isLongRoot_of_commute_sylow_minus {n : ℕ} (hn : 4 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (U : Sylow 2 (matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c)))
    {z : matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c)} (hz1 : z ≠ 1)
    (hz : ∀ u ∈ (U : Subgroup (matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c))),
      u * z = z * u) : IsLongRoot _ z := by
  obtain ⟨P₁, P₂, P₃, h₁₂, h₁₃, h₂₃⟩ := exists_three_pairs_minus (K := K) hn b c
  exact isLongRoot_of_commute_sylow (regular_coordinateQuadMinus n K b c hn hirr).1 h₁₂ h₁₃ h₂₃ U
    hz1 hz

omit [CharP K 2] in
theorem exists_isLongRoot_mem_pairPerpOf {d : ℕ} {Q : QuadraticForm K (Fin d → K)}
    (hQ : (polarBilin Q).Nondegenerate) {a b a₂ b₂ a₃ b₃ : Fin d} (h : IsHypCoord Q a b)
    (h₂ : IsHypCoord Q a₂ b₂) (h₃ : IsHypCoord Q a₃ b₃) (d₂ : PairDisjoint a b a₂ b₂)
    (d₃ : PairDisjoint a b a₃ b₃) (d₂₃ : PairDisjoint a₂ b₂ a₃ b₃) :
    ∃ z ∈ pairPerpOf Q a b, IsLongRoot Q z := by
  have hT := exists_threeSingular_of_isHypCoord h h₂ h₃ d₂ d₃ d₂₃
  have hu : (Pi.single a₂ 1 : Fin d → K) ∈ perpSub K a b := (h₂.hypPair_mem_perpSub d₂).1
  have hw : (Pi.single a₃ 1 : Fin d → K) ∈ perpSub K a b := (h₃.hypPair_mem_perpSub d₃).1
  set E : orthDerived Q := ⟨eichler Q (Pi.single a₂ 1) (Pi.single a₃ 1),
    eichler_mem_orthDerived hQ hT _ _⟩ with hE
  refine ⟨projHom Q E, ⟨E, h.eichler_mem_stabSub hu hw, rfl⟩, Pi.single a₂ 1, Pi.single a₃ 1,
    h₂.map_left, h₃.map_left, ?_, ?_, E, rfl, rfl⟩
  · rw [h₂.polar_left, Pi.single_eq_of_ne d₂₃.left_ne_right.symm]
  · rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 := congrFun hst a₂
    have h2 := congrFun hst a₃
    simp [d₂₃.left_ne_left, d₂₃.left_ne_left.symm] at h1 h2
    exact ⟨h1, h2⟩

omit [CharP K 2] in
theorem exists_isLongRoot_mem_pairPerp {n : ℕ} (hn : 3 ≤ n) (k : Fin n) :
    ∃ z ∈ pairPerp (K := K) k, IsLongRoot (coordinateQuadPlus n K) z := by
  obtain ⟨i, j, hik, hjk, hij⟩ := exists_two_ne hn k
  exact exists_isLongRoot_mem_pairPerpOf (regular_coordinateQuadPlus n K hn).1
    (isHypCoord_coordinateQuadPlus k) (isHypCoord_coordinateQuadPlus i)
    (isHypCoord_coordinateQuadPlus j) (pairDisjoint_plus hik.symm) (pairDisjoint_plus hjk.symm)
    (pairDisjoint_plus hij)

omit [CharP K 2] in
theorem exists_isLongRoot_mem_minusPairPerp {n : ℕ} (hn : 4 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (k : Fin (n - 1)) :
    ∃ z ∈ minusPairPerp (K := K) (one_le_of_four_le hn) b c k,
      IsLongRoot (coordinateQuadMinus n K (one_le_of_four_le hn) b c) z := by
  obtain ⟨i, j, hik, hjk, hij⟩ := exists_two_ne (by omega : 3 ≤ n - 1) k
  exact exists_isLongRoot_mem_pairPerpOf (regular_coordinateQuadMinus n K b c hn hirr).1
    (isHypCoord_coordinateQuadMinus _ b c k) (isHypCoord_coordinateQuadMinus _ b c i)
    (isHypCoord_coordinateQuadMinus _ b c j) (pairDisjoint_minus _ hik.symm)
    (pairDisjoint_minus _ hjk.symm) (pairDisjoint_minus _ hij)

theorem isConj_of_isConj_map {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) {z z' : X}
    (h : IsConj (e z) (e z')) : IsConj z z' := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  refine isConj_iff.mpr ⟨e.symm c, e.injective ?_⟩
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hc]

theorem exists_sylow_commute_map {X Y : Type*} [Group X] [Group Y] [Finite Y] (e : X ≃* Y)
    (U : Sylow 2 X) {z : X} (hz : ∀ u ∈ (U : Subgroup X), u * z = z * u) :
    ∃ U' : Sylow 2 Y, ∀ u ∈ (U' : Subgroup Y), u * e z = e z * u := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨U', hU'⟩ := exists_sylow_map_mulEquiv e U
  refine ⟨U', fun u hu => ?_⟩
  obtain ⟨x, rfl⟩ := e.surjective u
  rw [← map_mul, ← map_mul, hz x ((hU' x).2 hu)]

theorem isLongRoot_of_commute_sylow_plus_of_mulEquiv {X : Type*} [Group X] {n : ℕ}
    (e : X ≃* matrixProjectiveDerived (coordinateQuadPlus n K)) (hn : 3 ≤ n) (U : Sylow 2 X)
    {z : X} (hz1 : z ≠ 1) (hz : ∀ u ∈ (U : Subgroup X), u * z = z * u) :
    IsLongRoot _ (e z) := by
  obtain ⟨U', hU'⟩ := exists_sylow_commute_map e U hz
  exact isLongRoot_of_commute_sylow_plus hn U'
    (fun h0 => hz1 (e.injective (h0.trans (map_one e).symm))) hU'

theorem isLongRoot_of_commute_sylow_minus_of_mulEquiv {X : Type*} [Group X] {n : ℕ} (hn : 4 ≤ n)
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : X ≃* matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c)) (U : Sylow 2 X)
    {z : X} (hz1 : z ≠ 1) (hz : ∀ u ∈ (U : Subgroup X), u * z = z * u) :
    IsLongRoot _ (e z) := by
  obtain ⟨U', hU'⟩ := exists_sylow_commute_map e U hz
  exact isLongRoot_of_commute_sylow_minus hn hirr U'
    (fun h0 => hz1 (e.injective (h0.trans (map_one e).symm))) hU'

omit [CharP K 2] in
theorem isConj_of_isLongRoot_plus_of_mulEquiv {X : Type*} [Group X] {n : ℕ}
    (e : X ≃* matrixProjectiveDerived (coordinateQuadPlus n K)) (hn : 3 ≤ n) {z z' : X}
    (hz : IsLongRoot _ (e z)) (hz' : IsLongRoot _ (e z')) : IsConj z z' :=
  isConj_of_isConj_map e (isConj_of_isLongRoot_plus hn hz hz')

omit [CharP K 2] in
theorem isConj_of_isLongRoot_minus_of_mulEquiv {X : Type*} [Group X] {n : ℕ} (hn : 4 ≤ n)
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : X ≃* matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c)) {z z' : X}
    (hz : IsLongRoot _ (e z)) (hz' : IsLongRoot _ (e z')) : IsConj z z' :=
  isConj_of_isConj_map e (isConj_of_isLongRoot_minus hn hirr hz hz')

end Coordinates

end CFSG.SeitzReduction.OmegaPilot
