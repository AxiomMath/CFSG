module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165OmTorus4
public import CFSG.GroupTheory.CommutingMovingElemAbelian
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165OmTorus2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165OmTorus5

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open QuadraticMap CFSG.Open CFSG.ClassicalGroups.Orthogonal CFSG.LieType.SeitzGeneration.OrthBlk
open CFSG.RankThree.Classical2

namespace OmTorus

variable {F W : Type} [Field F] [Finite F] [CharP F 2] [AddCommGroup W] [Module F W]
  [FiniteDimensional F W] {Q : QuadraticForm F W}

@[expose] noncomputable def pairSpan (P : HypPair Q) : Submodule F W :=
  Submodule.span F {P.e, P.f}

private theorem pairSpan_orthogonal {P P' : HypPair Q} (h : P.Orth P') :
    pairSpan P ≤ perp Q (pairSpan P') := by
  intro x hx
  rw [mem_perp]
  intro y hy
  rw [pairSpan, Submodule.mem_span_pair] at hx hy
  obtain ⟨α, β, rfl⟩ := hx
  obtain ⟨γ, δ, rfl⟩ := hy
  have h1 : polar Q P'.e P.e = 0 := by rw [polar_comm]; exact h.ee
  have h2 : polar Q P'.e P.f = 0 := by rw [polar_comm]; exact h.fe
  have h3 : polar Q P'.f P.e = 0 := by rw [polar_comm]; exact h.ef
  have h4 : polar Q P'.f P.f = 0 := by rw [polar_comm]; exact h.ff
  simp only [polar_add_left, polar_add_right, polar_smul_left_eq, polar_smul_right_eq,
    h.ee, h.ef, h.fe, h.ff, h1, h2, h3, h4]
  ring

theorem perp_anti {U V : Submodule F W} (h : U ≤ V) :
    perp Q V ≤ perp Q U := by
  intro x hx
  rw [mem_perp] at hx ⊢
  intro y hy
  exact hx y (h hy)

@[expose] noncomputable def blockSpan (P P' : HypPair Q) : Submodule F W :=
  pairSpan P ⊔ pairSpan P'

theorem blockSpan_orthogonal {P₀ P₁ R₀ R₁ : HypPair Q}
    (h00 : P₀.Orth R₀) (h01 : P₀.Orth R₁) (h10 : P₁.Orth R₀) (h11 : P₁.Orth R₁) :
    blockSpan P₀ P₁ ≤ perp Q (blockSpan R₀ R₁) := by
  have hP₀ : pairSpan P₀ ≤ perp Q (blockSpan R₀ R₁) := by
    intro x hx
    rw [mem_perp]
    intro y hy
    rw [blockSpan, Submodule.mem_sup] at hy
    obtain ⟨c, hc, d, hd, rfl⟩ := hy
    rw [polar_comm, polar_add_right, polar_comm Q x c, polar_comm Q x d,
      mem_perp.mp (pairSpan_orthogonal h00 hx) c hc,
      mem_perp.mp (pairSpan_orthogonal h01 hx) d hd, add_zero]
  have hP₁ : pairSpan P₁ ≤ perp Q (blockSpan R₀ R₁) := by
    intro x hx
    rw [mem_perp]
    intro y hy
    rw [blockSpan, Submodule.mem_sup] at hy
    obtain ⟨c, hc, d, hd, rfl⟩ := hy
    rw [polar_comm, polar_add_right, polar_comm Q x c, polar_comm Q x d,
      mem_perp.mp (pairSpan_orthogonal h10 hx) c hc,
      mem_perp.mp (pairSpan_orthogonal h11 hx) d hd, add_zero]
  exact sup_le hP₀ hP₁

theorem plusPlaneA_subset (P P' : HypPair Q) (h : P.Orth P') (c : F)
    (hc : ∀ s t : F, s ^ 2 + s * t + c * t ^ 2 = 0 → s = 0 ∧ t = 0) :
    (plusPlaneA P P' h c hc).A ≤ blockSpan P P' := by
  intro x hx
  rw [plusPlaneA] at hx
  rw [blockSpan]
  rw [Submodule.mem_span_pair] at hx
  obtain ⟨α, β, rfl⟩ := hx
  refine Submodule.mem_sup.mpr ⟨α • (P.e + P.f) + β • P.e, ?_,
    β • (c • P'.e + P'.f), ?_, ?_⟩
  · rw [pairSpan, Submodule.mem_span_pair]
    exact ⟨α + β, α, by module⟩
  · rw [pairSpan, Submodule.mem_span_pair]
    exact ⟨β * c, β, by module⟩
  · module

theorem plusPlaneB_subset (P P' : HypPair Q) (h : P.Orth P') (c : F)
    (hc : ∀ s t : F, s ^ 2 + s * t + c * t ^ 2 = 0 → s = 0 ∧ t = 0) :
    (plusPlaneB P P' h c hc).A ≤ blockSpan P P' := by
  intro x hx
  rw [plusPlaneB] at hx
  rw [blockSpan]
  rw [Submodule.mem_span_pair] at hx
  obtain ⟨α, β, rfl⟩ := hx
  refine Submodule.mem_sup.mpr ⟨α • (P.e + P.f), ?_,
    α • P'.e + β • (c • P'.e + P'.f), ?_, ?_⟩
  · rw [pairSpan, Submodule.mem_span_pair]
    exact ⟨α, α, by module⟩
  · rw [pairSpan, Submodule.mem_span_pair]
    exact ⟨(α + β * c), β, by module⟩
  · module

theorem exists_elemAbelian_of_planeFrames {ι : Type} [Fintype ι] {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2)
    (hqF : q ∣ Nat.card F + 1) (D : ι → PlaneFrame Q)
    (horth : ∀ i j, i ≠ j → (D i).A ≤ perp Q (D j).A) :
    ∃ T : Subgroup (W ≃ₗ[F] W), T ≤ orthDerived Q ∧ IsElemAbelian q T ∧
      Nat.card ι ≤ CFSG.Open.pRank q T := by
  classical
  have hdata : ∀ i, ∃ t : W ≃ₗ[F] W,
      t ∈ TauCeti.QuadraticMap.orthogonalGroup Q ∧ t ∈ orthDerived Q ∧
      orderOf t = q ∧ (∀ w ∈ perp Q (D i).A, t w = w) ∧
      (∀ x ∈ (D i).A, t x ∈ (D i).A) ∧
      (∀ a : ℤ, (t ^ a) (D i).u = (D i).u → (q : ℤ) ∣ a) :=
    fun i => exists_plane_torus (D i) hq hq2 hqF
  let t : ι → W ≃ₗ[F] W := fun i => Classical.choose (hdata i)
  have ht : ∀ i, t i ∈ TauCeti.QuadraticMap.orthogonalGroup Q ∧ t i ∈ orthDerived Q ∧
      orderOf (t i) = q ∧ (∀ w ∈ perp Q (D i).A, t i w = w) ∧
      (∀ x ∈ (D i).A, t i x ∈ (D i).A) ∧
      (∀ a : ℤ, ((t i) ^ a) (D i).u = (D i).u → (q : ℤ) ∣ a) :=
    fun i => Classical.choose_spec (hdata i)
  have ht_mem : ∀ i, t i ∈ orthDerived Q := fun i => (ht i).2.1
  have ht_order : ∀ i, orderOf (t i) = q := fun i => (ht i).2.2.1
  have ht_fix : ∀ i, ∀ w ∈ perp Q (D i).A, t i w = w := fun i => (ht i).2.2.2.1
  have ht_map : ∀ i, ∀ x ∈ (D i).A, t i x ∈ (D i).A := fun i => (ht i).2.2.2.2.1
  have ht_move : ∀ i, ∀ a : ℤ, ((t i) ^ a) (D i).u = (D i).u → (q : ℤ) ∣ a :=
    fun i => (ht i).2.2.2.2.2
  have hcomm : ∀ i j, Commute (t i) (t j) := by
    intro i j
    by_cases hij : i = j
    · subst hij; exact Commute.refl _
    · exact commute_of_orthogonal_supports (D i).polarNondegOn (D j).polarNondegOn
        (horth i j hij) (ht_fix i) (ht_fix j) (ht_map i) (ht_map j)
  have horth' : ∀ i j, i ≠ j → (D j).A ≤ perp Q (D i).A := by
    intro i j hij x hx
    rw [mem_perp]
    intro y hy
    rw [polar_comm]
    exact mem_perp.mp (horth i j hij hy) x hx
  have hfix : ∀ i j, i ≠ j → t i (D j).u = (D j).u := by
    intro i j hij
    exact ht_fix i (D j).u (horth' i j hij (D j).hu)
  obtain ⟨T, hTH, hTelem, hTcard, hTrank⟩ :=
    CFSG.exists_elemAbelian_of_commuting_moving hq t (fun i => (D i).u) (MonoidHom.id _)
      ht_mem ht_order hcomm ht_move hfix
  exact ⟨T, hTH, hTelem, by simpa using hTrank⟩

theorem exists_elemAbelian_of_planeFrames_in {ι : Type} [Fintype ι] {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2)
    (hqF : q ∣ Nat.card F + 1) (D : ι → PlaneFrame Q)
    (horth : ∀ i j, i ≠ j → (D i).A ≤ perp Q (D j).A) :
    ∃ T : Subgroup ↥(orthDerived Q), IsElemAbelian q T ∧
      Nat.card ι ≤ CFSG.Open.pRank q T := by
  classical
  have hdata : ∀ i, ∃ t : W ≃ₗ[F] W,
      t ∈ TauCeti.QuadraticMap.orthogonalGroup Q ∧ t ∈ orthDerived Q ∧
      orderOf t = q ∧ (∀ w ∈ perp Q (D i).A, t w = w) ∧
      (∀ x ∈ (D i).A, t x ∈ (D i).A) ∧
      (∀ a : ℤ, (t ^ a) (D i).u = (D i).u → (q : ℤ) ∣ a) :=
    fun i => exists_plane_torus (D i) hq hq2 hqF
  let t : ι → W ≃ₗ[F] W := fun i => Classical.choose (hdata i)
  have ht : ∀ i, t i ∈ TauCeti.QuadraticMap.orthogonalGroup Q ∧ t i ∈ orthDerived Q ∧
      orderOf (t i) = q ∧ (∀ w ∈ perp Q (D i).A, t i w = w) ∧
      (∀ x ∈ (D i).A, t i x ∈ (D i).A) ∧
      (∀ a : ℤ, ((t i) ^ a) (D i).u = (D i).u → (q : ℤ) ∣ a) :=
    fun i => Classical.choose_spec (hdata i)
  have ht_mem : ∀ i, t i ∈ orthDerived Q := fun i => (ht i).2.1
  have ht_order : ∀ i, orderOf (t i) = q := fun i => (ht i).2.2.1
  have ht_fix : ∀ i, ∀ w ∈ perp Q (D i).A, t i w = w := fun i => (ht i).2.2.2.1
  have ht_map : ∀ i, ∀ x ∈ (D i).A, t i x ∈ (D i).A := fun i => (ht i).2.2.2.2.1
  have ht_move : ∀ i, ∀ a : ℤ, ((t i) ^ a) (D i).u = (D i).u → (q : ℤ) ∣ a :=
    fun i => (ht i).2.2.2.2.2
  have hcomm : ∀ i j, Commute (t i) (t j) := by
    intro i j
    by_cases hij : i = j
    · subst hij; exact Commute.refl _
    · exact commute_of_orthogonal_supports (D i).polarNondegOn (D j).polarNondegOn
        (horth i j hij) (ht_fix i) (ht_fix j) (ht_map i) (ht_map j)
  have horth' : ∀ i j, i ≠ j → (D j).A ≤ perp Q (D i).A := by
    intro i j hij x hx
    rw [mem_perp]
    intro y hy
    rw [polar_comm]
    exact mem_perp.mp (horth i j hij hy) x hx
  have hfix : ∀ i j, i ≠ j → t i (D j).u = (D j).u := by
    intro i j hij
    exact ht_fix i (D j).u (horth' i j hij (D j).hu)
  let tΩ : ι → ↥(orthDerived Q) := fun i => ⟨t i, ht_mem i⟩
  have hordΩ : ∀ i, orderOf (tΩ i) = q := by
    intro i
    have h1 : orderOf (↑(tΩ i) : W ≃ₗ[F] W) = orderOf (tΩ i) :=
      orderOf_injective (Subgroup.subtype _) Subtype.coe_injective (tΩ i)
    rw [← h1]
    exact ht_order i
  have hcommΩ : ∀ i j, Commute (tΩ i) (tΩ j) := by
    intro i j
    apply Subtype.ext
    exact hcomm i j
  have hmoveΩ : ∀ i (a : ℤ), (orthDerived Q).subtype ((tΩ i) ^ a) (D i).u = (D i).u →
      (q : ℤ) ∣ a := by
    intro i a ha
    exact ht_move i a (by simpa using ha)
  have hfixΩ : ∀ i j, i ≠ j → (orthDerived Q).subtype (tΩ i) (D j).u = (D j).u := by
    intro i j hij
    simpa using hfix i j hij
  obtain ⟨T, -, hTelem, -, hTrank⟩ :=
    CFSG.exists_elemAbelian_of_commuting_moving hq tΩ (fun i => (D i).u)
      (orthDerived Q).subtype (fun i => Subgroup.mem_top _) hordΩ hcommΩ hmoveΩ hfixΩ
  exact ⟨T, hTelem, hTrank⟩

end OmTorus

end CFSG.LocalAnalysis.GLTheoremA.Y10F
