module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS04I117ZeroB

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA

open Module QuadraticMap
open CFSG.LieType.Universal.Spin CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open CFSG.HardMathSupport.Timmesfeld.DFour
open CFSG.HardMathSupport.Malle.E27Lie

section Zero

variable {K : Type} [Field K] [Finite K]
  {g : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)}

section CaseA

@[expose] def eigSp (g : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) (c : K) :
    Submodule K (Fin 4 ⊕ Fin 4 → K) :=
  LinearMap.ker ((g : (Fin 4 ⊕ Fin 4 → K) →ₗ[K] (Fin 4 ⊕ Fin 4 → K)) - c • LinearMap.id)

omit [Finite K] in
theorem mem_eigSp {c : K} {v : Fin 4 ⊕ Fin 4 → K} : v ∈ eigSp g c ↔ g v = c • v := by
  simp [eigSp, sub_eq_zero]

omit [Finite K] in
theorem root_facts (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) {ω : K} (hω : ω ^ 2 + ω + 1 = 0) :
    ω ≠ -1 - ω ∧ ω * (-1 - ω) = 1 ∧ ω ^ 2 ≠ 1 ∧ (-1 - ω) ^ 2 ≠ 1 ∧
      ∀ l : K, l ^ 2 + l + 1 = 0 → l = ω ∨ l = -1 - ω := by
  refine ⟨fun h => ?_, by linear_combination -hω, fun h => ?_, fun h => ?_, fun l hl => ?_⟩
  · apply h3
    have : (2 * ω + 1) = 0 := by linear_combination h
    linear_combination 4 * hω - (2 * ω + 1) * this
  · have h' : (ω - 1) * (ω + 1) = 0 := by linear_combination h
    rcases mul_eq_zero.1 h' with h1 | h1
    · apply h3
      have : ω = 1 := by linear_combination h1
      rw [this] at hω
      linear_combination hω
    · have : ω = -1 := by linear_combination h1
      rw [this] at hω
      norm_num at hω
  · have h' : (-1 - ω - 1) * (-1 - ω + 1) = 0 := by linear_combination h
    rcases mul_eq_zero.1 h' with h1 | h1
    · apply h3
      have : ω = -2 := by linear_combination -h1
      rw [this] at hω
      linear_combination hω
    · have : ω = 0 := by linear_combination -h1
      rw [this] at hω
      norm_num at hω
  · have : (l - ω) * (l - (-1 - ω)) = 0 := by linear_combination hl - hω
    rcases mul_eq_zero.1 this with h1 | h1
    · left; linear_combination h1
    · right; linear_combination h1

variable (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K))

omit [Finite K] in
include hg in
theorem eig_orth {c : K} (hc : c ^ 2 ≠ 1) {u v : Fin 4 ⊕ Fin 4 → K} (hu : u ∈ eigSp g c)
    (hv : v ∈ eigSp g c) : polar (quadPlus 4 K) u v = 0 := by
  rw [mem_eigSp] at hu hv
  have h := polar_isometry hg u v
  rw [hu, hv, QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right, smul_eq_mul,
    smul_eq_mul] at h
  have h' : (c ^ 2 - 1) * polar (quadPlus 4 K) u v = 0 := by linear_combination h
  exact (mul_eq_zero.mp h').resolve_left (sub_ne_zero.mpr hc)

omit [Finite K] in
include hg in
theorem eig_singular (h2 : (2 : K) ≠ 0) {c : K} (hc : c ^ 2 ≠ 1) :
    ∀ x ∈ eigSp g c, quadPlus 4 K x = 0 := by
  intro x hx
  have h := eig_orth hg hc hx hx
  rw [QuadraticMap.polar_self] at h
  have : (2 : K) * quadPlus 4 K x = 0 := by simpa [two_smul, two_mul] using h
  exact (mul_eq_zero.mp this).resolve_left h2

omit [Finite K] in
theorem eig_sup (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) (hsum : ∀ v, v + g v + g (g v) = 0)
    {ω : K} (hω : ω ^ 2 + ω + 1 = 0) :
    eigSp g ω ⊔ eigSp g (-1 - ω) = ⊤ := by
  obtain ⟨hne, hprod, -, -, -⟩ := root_facts h2 h3 hω
  have hd : ω - (-1 - ω) ≠ 0 := sub_ne_zero.mpr hne
  have hd' : (-1 - ω) - ω ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  rw [eq_top_iff]
  intro v _
  have h1 : ∀ w, g (g w) = -w - g w := fun w => by
    have h := hsum w
    calc g (g w) = (w + g w + g (g w)) - w - g w := by abel
      _ = -w - g w := by rw [h]; abel
  refine Submodule.mem_sup.2 ⟨(ω - (-1 - ω))⁻¹ • (g v - (-1 - ω) • v), ?_,
    ((-1 - ω) - ω)⁻¹ • (g v - ω • v), ?_, ?_⟩
  · rw [mem_eigSp, map_smul, map_sub, map_smul, h1, smul_comm ω]
    congr 1
    have : ω • (g v - (-1 - ω) • v) = ω • g v - (ω * (-1 - ω)) • v := by
      rw [smul_sub, smul_smul]
    rw [this, hprod]
    module
  · rw [mem_eigSp, map_smul, map_sub, map_smul, h1, smul_comm (-1 - ω)]
    congr 1
    have : (-1 - ω) • (g v - ω • v) = (-1 - ω) • g v - ((-1 - ω) * ω) • v := by
      rw [smul_sub, smul_smul]
    rw [this, mul_comm, hprod]
    module
  · have e1 : ((-1 - ω) - ω)⁻¹ = -(ω - (-1 - ω))⁻¹ := by
      rw [← inv_neg]
      congr 1
      ring
    rw [e1, neg_smul, ← sub_eq_add_neg, ← smul_sub]
    have : g v - (-1 - ω) • v - (g v - ω • v) = (ω - (-1 - ω)) • v := by module
    rw [this, smul_smul, inv_mul_cancel₀ hd, one_smul]

omit [Finite K] in
theorem eig_inf (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) {ω : K} (hω : ω ^ 2 + ω + 1 = 0) :
    eigSp g ω ⊓ eigSp g (-1 - ω) = ⊥ := by
  obtain ⟨hne, -, -, -, -⟩ := root_facts h2 h3 hω
  rw [eq_bot_iff]
  intro v ⟨h1, h2'⟩
  have h1 := mem_eigSp.1 h1
  have h2' := mem_eigSp.1 h2'
  have : (ω - (-1 - ω)) • v = 0 := by rw [sub_smul, ← h1, ← h2', sub_self]
  rw [Submodule.mem_bot]
  exact (smul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hne)

include hg in
theorem finrank_eig_le_four (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    (hg3 : ∀ v, g (g (g v)) = v)
    (hd : finrank K (LinearMap.ker ((g : (Fin 4 ⊕ Fin 4 → K) →ₗ[K] _) - LinearMap.id)) = 0)
    {c : K} (hc : c ^ 2 ≠ 1) : finrank K (eigSp g c) ≤ 4 := by
  have hfix : fixSp g = ⊥ := Submodule.finrank_eq_zero.1 hd
  have hmov : movSp g = ⊤ := by
    have hsup := movSp_sup_fixSp h3 hg3
    rwa [hfix, sup_bot_eq] at hsup
  have := two_mul_finrank_le_movSp h3 hg3 hg (nondegenerate_polarBilin_quadPlus 4 K)
    (S := eigSp g c) (by rw [hmov]; exact le_top) (eig_singular hg h2 hc)
  rw [hfix, finrank_bot, finrank_V8] at this
  omega

include hg in
theorem finrank_eig_eq_four (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    (hsum : ∀ v, v + g v + g (g v) = 0) (hg3 : ∀ v, g (g (g v)) = v)
    (hd : finrank K (LinearMap.ker ((g : (Fin 4 ⊕ Fin 4 → K) →ₗ[K] _) - LinearMap.id)) = 0)
    {ω : K} (hω : ω ^ 2 + ω + 1 = 0) :
    finrank K (eigSp g ω) = 4 ∧ finrank K (eigSp g (-1 - ω)) = 4 := by
  obtain ⟨-, -, hω2, hω2', -⟩ := root_facts h2 h3 hω
  have h1 := finrank_eig_le_four hg h2 h3 hg3 hd hω2
  have h2' := finrank_eig_le_four hg h2 h3 hg3 hd hω2'
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq (eigSp g ω) (eigSp g (-1 - ω))
  rw [eig_sup h2 h3 hsum hω, eig_inf h2 h3 hω, finrank_top, finrank_bot, finrank_V8] at hsup
  omega

omit [Finite K] in
theorem card_lines_le [Finite K] {W : Submodule K (Fin 4 ⊕ Fin 4 → K)} (hW : finrank K W = 4) :
    Nat.card {L : Submodule K (Fin 4 ⊕ Fin 4 → K) // finrank K L = 1 ∧ L ≤ W} ≤
      ∑ i ∈ Finset.range 4, Nat.card K ^ i := by
  rw [← Projectivization.card_of_finrank (k := K) (V := W) hW]
  refine Nat.card_le_card_of_surjective
    (fun p : Projectivization K W => (⟨p.submodule.map W.subtype, ?_, Submodule.map_subtype_le _ _⟩ :
      {L : Submodule K (Fin 4 ⊕ Fin 4 → K) // finrank K L = 1 ∧ L ≤ W})) ?_
  · rw [Submodule.finrank_map_subtype_eq W p.submodule, Projectivization.finrank_submodule]
  · rintro ⟨L, hL1, hLW⟩
    obtain ⟨v, hv0, hv⟩ := finrank_eq_one_iff'.1 hL1
    have hvW : (v : Fin 4 ⊕ Fin 4 → K) ∈ W := hLW v.2
    have hv0' : (⟨(v : Fin 4 ⊕ Fin 4 → K), hvW⟩ : W) ≠ 0 := fun h =>
      hv0 (Subtype.ext (by simpa using congrArg (Subtype.val : W → Fin 4 ⊕ Fin 4 → K) h))
    refine ⟨Projectivization.mk K ⟨(v : Fin 4 ⊕ Fin 4 → K), hvW⟩ hv0', ?_⟩
    apply Subtype.ext
    simp only
    rw [Projectivization.submodule_mk, Submodule.map_span, Set.image_singleton]
    ext x
    rw [Submodule.mem_span_singleton]
    constructor
    · rintro ⟨c, rfl⟩
      exact L.smul_mem c v.2
    · intro hx
      obtain ⟨c, hc⟩ := hv ⟨x, hx⟩
      exact ⟨c, congrArg Subtype.val hc⟩

instance finite_submodule_V8 : Finite (Submodule K (Fin 4 ⊕ Fin 4 → K)) :=
  Finite.of_injective (fun L : Submodule K (Fin 4 ⊕ Fin 4 → K) => (L : Set (Fin 4 ⊕ Fin 4 → K)))
    SetLike.coe_injective

omit [Finite K] in
theorem sumTwo_eq_zero {v : Fin 4 ⊕ Fin 4 → K} {l : K} (hv : v ≠ 0)
    (hsum : ∀ v, v + g v + g (g v) = 0) (hl : g v = l • v) : l ^ 2 + l + 1 = 0 := by
  have h := hsum v
  rw [hl, map_smul, hl, smul_smul] at h
  have h' : (1 + l + l * l) • v = 0 := by
    rw [add_smul, add_smul, one_smul]
    exact h
  have := (smul_eq_zero.mp h').resolve_right hv
  linear_combination this

include hg in
theorem card_lines_inv_le (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    (hsum : ∀ v, v + g v + g (g v) = 0) (hg3 : ∀ v, g (g (g v)) = v)
    (hd : finrank K (LinearMap.ker ((g : (Fin 4 ⊕ Fin 4 → K) →ₗ[K] _) - LinearMap.id)) = 0)
    {ω : K} (hω : ω ^ 2 + ω + 1 = 0) :
    Nat.card {L : Submodule K (Fin 4 ⊕ Fin 4 → K) // L ∈ singularSubspaces (quadPlus 4 K) 1 ∧
        L.map (g : (Fin 4 ⊕ Fin 4 → K) →ₗ[K] (Fin 4 ⊕ Fin 4 → K)) = L} ≤
      2 * ∑ i ∈ Finset.range 4, Nat.card K ^ i := by
  obtain ⟨-, -, hω2, hω2', hroots⟩ := root_facts h2 h3 hω
  obtain ⟨hd1, hd2⟩ := finrank_eig_eq_four hg h2 h3 hsum hg3 hd hω
  set c₂ : K := -1 - ω with hc₂
  have hlineinv : ∀ (c : K) (L : Submodule K (Fin 4 ⊕ Fin 4 → K)), c ^ 2 ≠ 1 →
      finrank K L = 1 → L ≤ eigSp g c →
      L ∈ singularSubspaces (quadPlus 4 K) 1 ∧
        L.map (g : (Fin 4 ⊕ Fin 4 → K) →ₗ[K] (Fin 4 ⊕ Fin 4 → K)) = L := by
    intro c L hc hL1 hLc
    refine ⟨⟨hL1, fun x hx => eig_singular hg h2 hc x (hLc hx)⟩, map_eq_of_invariant hg3 ?_⟩
    intro x hx
    have := mem_eigSp.1 (hLc hx)
    show g x ∈ L
    rw [this]
    exact L.smul_mem c hx
  let f : {L : Submodule K (Fin 4 ⊕ Fin 4 → K) // finrank K L = 1 ∧ L ≤ eigSp g ω} ⊕
      {L : Submodule K (Fin 4 ⊕ Fin 4 → K) // finrank K L = 1 ∧ L ≤ eigSp g c₂} →
      {L : Submodule K (Fin 4 ⊕ Fin 4 → K) // L ∈ singularSubspaces (quadPlus 4 K) 1 ∧
        L.map (g : (Fin 4 ⊕ Fin 4 → K) →ₗ[K] (Fin 4 ⊕ Fin 4 → K)) = L} :=
    Sum.elim (fun L => ⟨L.1, hlineinv ω L.1 hω2 L.2.1 L.2.2⟩)
      (fun L => ⟨L.1, hlineinv c₂ L.1 hω2' L.2.1 L.2.2⟩)
  have hsurj : Function.Surjective f := by
    rintro ⟨L, ⟨hL1, -⟩, hLi⟩
    obtain ⟨v, hv0, hv⟩ := finrank_eq_one_iff'.1 hL1
    have hgv : g (v : Fin 4 ⊕ Fin 4 → K) ∈ L := by
      have : g (v : Fin 4 ⊕ Fin 4 → K) ∈
          L.map (g : (Fin 4 ⊕ Fin 4 → K) →ₗ[K] (Fin 4 ⊕ Fin 4 → K)) :=
        Submodule.mem_map_of_mem v.2
      rwa [hLi] at this
    obtain ⟨l, hl⟩ := hv ⟨g (v : Fin 4 ⊕ Fin 4 → K), hgv⟩
    have hl' : g (v : Fin 4 ⊕ Fin 4 → K) = l • (v : Fin 4 ⊕ Fin 4 → K) := (congrArg Subtype.val hl).symm
    have hv0' : (v : Fin 4 ⊕ Fin 4 → K) ≠ 0 := fun h => hv0 (Subtype.ext h)
    have hroot := sumTwo_eq_zero hv0' hsum hl'
    have hLspan : ∀ x ∈ L, ∃ c : K, c • (v : Fin 4 ⊕ Fin 4 → K) = x := fun x hx => by
      obtain ⟨c, hc⟩ := hv ⟨x, hx⟩
      exact ⟨c, congrArg Subtype.val hc⟩
    rcases hroots l hroot with h | h
    · refine ⟨Sum.inl ⟨L, hL1, fun x hx => ?_⟩, rfl⟩
      obtain ⟨c, rfl⟩ := hLspan x hx
      rw [mem_eigSp, map_smul, hl', h]
      exact smul_comm _ _ _
    · refine ⟨Sum.inr ⟨L, hL1, fun x hx => ?_⟩, rfl⟩
      obtain ⟨c, rfl⟩ := hLspan x hx
      rw [mem_eigSp, map_smul, hl', h]
      exact smul_comm _ _ _
  have hfin1 : Finite {L : Submodule K (Fin 4 ⊕ Fin 4 → K) // finrank K L = 1 ∧ L ≤ eigSp g ω} :=
    inferInstance
  have hfin2 : Finite {L : Submodule K (Fin 4 ⊕ Fin 4 → K) // finrank K L = 1 ∧ L ≤ eigSp g c₂} :=
    inferInstance
  calc _ ≤ Nat.card ({L : Submodule K (Fin 4 ⊕ Fin 4 → K) // finrank K L = 1 ∧ L ≤ eigSp g ω} ⊕
      {L : Submodule K (Fin 4 ⊕ Fin 4 → K) // finrank K L = 1 ∧ L ≤ eigSp g c₂}) :=
        Nat.card_le_card_of_surjective f hsurj
    _ = _ + _ := Nat.card_sum
    _ ≤ _ := Nat.add_le_add (card_lines_le hd1) (card_lines_le hd2)
    _ = _ := by ring

omit [Finite K] in
theorem coords4 {W : Submodule K (Fin 4 ⊕ Fin 4 → K)} (b : Module.Basis (Fin 4) K W) {x₀ x₁ x₂ x₃ : K}
    (h : x₀ • b 0 + x₁ • b 1 + x₂ • b 2 + x₃ • b 3 = 0) : x₀ = 0 ∧ x₁ = 0 ∧ x₂ = 0 ∧ x₃ = 0 := by
  have := Fintype.linearIndependent_iff.1 b.linearIndependent ![x₀, x₁, x₂, x₃] (by
    simpa [Fin.sum_univ_four] using h)
  exact ⟨this 0, this 1, this 2, this 3⟩

@[expose] def planeVec {W : Submodule K (Fin 4 ⊕ Fin 4 → K)} (b : Module.Basis (Fin 4) K W)
    (c : Fin 4 → K) : W × W :=
  (b 0 + c 0 • b 2 + c 1 • b 3, b 1 + c 2 • b 2 + c 3 • b 3)

omit [Finite K] in
theorem planeVec_indep {W : Submodule K (Fin 4 ⊕ Fin 4 → K)} (b : Module.Basis (Fin 4) K W)
    (c : Fin 4 → K) {x y : K}
    (h : x • (planeVec b c).1 + y • (planeVec b c).2 = 0) : x = 0 ∧ y = 0 := by
  have h' : x • b 0 + y • b 1 + (x * c 0 + y * c 2) • b 2 + (x * c 1 + y * c 3) • b 3 = 0 := by
    rw [← h]
    simp only [planeVec]
    module
  obtain ⟨h0, h1, -, -⟩ := coords4 b h'
  exact ⟨h0, h1⟩

omit [Finite K] in
theorem planeVec_inj {W : Submodule K (Fin 4 ⊕ Fin 4 → K)} (b : Module.Basis (Fin 4) K W)
    {c c' : Fin 4 → K}
    (h : Submodule.span K {(planeVec b c).1, (planeVec b c).2} =
      Submodule.span K {(planeVec b c').1, (planeVec b c').2}) : c = c' := by
  have h1 : (planeVec b c).1 ∈ Submodule.span K {(planeVec b c').1, (planeVec b c').2} := by
    rw [← h]; exact Submodule.subset_span (by simp)
  have h2 : (planeVec b c).2 ∈ Submodule.span K {(planeVec b c').1, (planeVec b c').2} := by
    rw [← h]; exact Submodule.subset_span (by simp)
  obtain ⟨x, y, hxy⟩ := Submodule.mem_span_pair.1 h1
  obtain ⟨x', y', hxy'⟩ := Submodule.mem_span_pair.1 h2
  have e1 : (x - 1) • b 0 + y • b 1 + (x * c' 0 + y * c' 2 - c 0) • b 2 +
      (x * c' 1 + y * c' 3 - c 1) • b 3 = 0 := by
    have : x • (planeVec b c').1 + y • (planeVec b c').2 - (planeVec b c).1 = 0 := by
      rw [hxy]; abel
    rw [← this]
    simp only [planeVec]
    module
  have e2 : x' • b 0 + (y' - 1) • b 1 + (x' * c' 0 + y' * c' 2 - c 2) • b 2 +
      (x' * c' 1 + y' * c' 3 - c 3) • b 3 = 0 := by
    have : x' • (planeVec b c').1 + y' • (planeVec b c').2 - (planeVec b c).2 = 0 := by
      rw [hxy']; abel
    rw [← this]
    simp only [planeVec]
    module
  obtain ⟨a0, a1, a2, a3⟩ := coords4 b e1
  obtain ⟨b0, b1, b2, b3⟩ := coords4 b e2
  have hx : x = 1 := by linear_combination a0
  have hy : y = 0 := a1
  have hx' : x' = 0 := b0
  have hy' : y' = 1 := by linear_combination b1
  funext i
  fin_cases i
  · simp only [Fin.zero_eta]
    rw [hx, hy] at a2
    linear_combination -a2
  · simp only [Fin.mk_one]
    rw [hx, hy] at a3
    linear_combination -a3
  · show c 2 = c' 2
    rw [hx', hy'] at b2
    linear_combination -b2
  · show c 3 = c' 3
    rw [hx', hy'] at b3
    linear_combination -b3

include hg in
theorem exists_planes_family (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    (hsum : ∀ v, v + g v + g (g v) = 0) (hg3 : ∀ v, g (g (g v)) = v)
    (hd : finrank K (LinearMap.ker ((g : (Fin 4 ⊕ Fin 4 → K) →ₗ[K] _) - LinearMap.id)) = 0)
    {ω : K} (hω : ω ^ 2 + ω + 1 = 0) :
    ∃ F : (Fin 4 → K) → Submodule K (Fin 4 ⊕ Fin 4 → K), Function.Injective F ∧
      ∀ c, F c ∈ singularSubspaces (quadPlus 4 K) 4 ∧
        (F c).map (g : (Fin 4 ⊕ Fin 4 → K) →ₗ[K] (Fin 4 ⊕ Fin 4 → K)) = F c := by
  classical
  obtain ⟨-, -, hω2, hω2', -⟩ := root_facts h2 h3 hω
  obtain ⟨hdW, hdW'⟩ := finrank_eig_eq_four hg h2 h3 hsum hg3 hd hω
  set W := eigSp g ω with hW
  set W' := eigSp g (-1 - ω) with hW'
  have hinf : W ⊓ W' = ⊥ := eig_inf h2 h3 hω
  have hWs := eig_singular hg h2 hω2
  have hW's := eig_singular hg h2 hω2'
  have hfix : fixSp g = ⊥ := Submodule.finrank_eq_zero.1 hd
  have hmov : movSp g = ⊤ := by
    have hsup := movSp_sup_fixSp h3 hg3
    rwa [hfix, sup_bot_eq] at hsup
  have hle4 : ∀ M : Submodule K (Fin 4 ⊕ Fin 4 → K), (∀ x ∈ M, quadPlus 4 K x = 0) →
      finrank K M ≤ 4 := fun M hM => by
    have := two_mul_finrank_le_movSp h3 hg3 hg (nondegenerate_polarBilin_quadPlus 4 K)
      (S := M) (by rw [hmov]; exact le_top) hM
    rw [hfix, finrank_bot, finrank_V8] at this
    omega
  let b : Module.Basis (Fin 4) K W := Module.finBasisOfFinrankEq K W hdW
  let P : (Fin 4 → K) → Submodule K (Fin 4 ⊕ Fin 4 → K) := fun c =>
    (Submodule.span K {(planeVec b c).1, (planeVec b c).2}).map W.subtype
  have hPW : ∀ c, P c ≤ W := fun c => Submodule.map_subtype_le _ _
  have hPr : ∀ c, finrank K (P c) = 2 := by
    intro c
    have hli : LinearIndependent K ![(planeVec b c).1, (planeVec b c).2] := by
      rw [LinearIndependent.pair_iff]
      exact fun x y h => planeVec_indep b c h
    have h := finrank_span_eq_card hli
    rw [Fintype.card_fin] at h
    have hset : Set.range ![(planeVec b c).1, (planeVec b c).2] =
        {(planeVec b c).1, (planeVec b c).2} := by
      ext x
      simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff, Fin.exists_fin_two,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      tauto
    rw [hset] at h
    simp only [P]
    rw [Submodule.finrank_map_subtype_eq W]
    exact h
  have hPg : ∀ c, ∀ x ∈ P c, g x = ω • x := fun c x hx => mem_eigSp.1 (hPW c hx)
  let A : (Fin 4 → K) → Submodule K (Fin 4 ⊕ Fin 4 → K) := fun c =>
    W' ⊓ LinearMap.BilinForm.orthogonal (polarBilin (quadPlus 4 K)) (P c)
  have hAr : ∀ c, 2 ≤ finrank K (A c) := by
    intro c
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq W'
      (LinearMap.BilinForm.orthogonal (polarBilin (quadPlus 4 K)) (P c))
    have h2' := LinearMap.BilinForm.finrank_orthogonal (nondegenerate_polarBilin_quadPlus 4 K) (P c)
    have h3' := Submodule.finrank_le (W' ⊔ LinearMap.BilinForm.orthogonal (polarBilin (quadPlus 4 K)) (P c))
    rw [finrank_V8, hPr] at h2'
    rw [finrank_V8] at h3'
    simp only [A]
    omega
  have hAW' : ∀ c, A c ≤ W' := fun c => inf_le_left
  let M : (Fin 4 → K) → Submodule K (Fin 4 ⊕ Fin 4 → K) := fun c => P c ⊔ A c
  have hMs : ∀ c, ∀ x ∈ M c, quadPlus 4 K x = 0 := by
    intro c x hx
    obtain ⟨p, hp, a, ha, rfl⟩ := Submodule.mem_sup.1 hx
    have hpa : polar (quadPlus 4 K) p a = 0 := mem_orth_iff.1 ha.2 p hp
    rw [QuadraticMap.map_add (quadPlus 4 K) p a, hWs p (hPW c hp), hW's a (hAW' c ha), hpa]
    simp
  have hPA : ∀ c, P c ⊓ A c = ⊥ := fun c => by
    rw [eq_bot_iff, ← hinf]
    exact inf_le_inf (hPW c) (hAW' c)
  have hMr : ∀ c, finrank K (M c) = 4 := by
    intro c
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq (P c) (A c)
    rw [hPA, finrank_bot, hPr] at h1
    have h2' := hle4 (M c) (hMs c)
    have h3' := hAr c
    simp only [M] at h2' ⊢
    omega
  have hMi : ∀ c, ∀ x ∈ M c, g x ∈ M c := by
    intro c x hx
    obtain ⟨p, hp, a, ha, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add, hPg c p hp, mem_eigSp.1 (hAW' c ha)]
    exact Submodule.add_mem_sup ((P c).smul_mem _ hp) ((A c).smul_mem _ ha)
  have hMW : ∀ c, M c ⊓ W = P c := by
    intro c
    refine le_antisymm ?_ (le_inf le_sup_left (hPW c))
    rintro x ⟨hxM, hxW⟩
    obtain ⟨p, hp, a, ha, rfl⟩ := Submodule.mem_sup.1 hxM
    have haW : a ∈ W := by
      have := W.sub_mem hxW (hPW c hp)
      simpa using this
    have : a ∈ W ⊓ W' := ⟨haW, hAW' c ha⟩
    rw [hinf, Submodule.mem_bot] at this
    rw [this, add_zero]
    exact hp
  refine ⟨M, fun c c' hcc => ?_, fun c => ⟨⟨hMr c, hMs c⟩, map_eq_of_invariant hg3 (hMi c)⟩⟩
  have hP : P c = P c' := by rw [← hMW c, ← hMW c', hcc]
  exact planeVec_inj b (Submodule.map_injective_of_injective W.injective_subtype hP)

end CaseA

end Zero

end CFSG.LocalAnalysis.GLTheoremA
