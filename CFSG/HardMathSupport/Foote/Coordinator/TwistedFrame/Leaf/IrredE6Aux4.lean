module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.IrredE6Aux3

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.IrredE6Aux

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis

set_option linter.unusedSectionVars false


theorem commute_of_facts {α β : V6} (hα : α ∈ rootFinset Tag.E6) (hβ : β ∈ rootFinset Tag.E6)
    (hne : α ≠ β) (hne' : α ≠ -β) (hnot : α + β ∉ rootFinset Tag.E6) (F : Type) [Field F]
    (a b : F) : Commute (pinnedX Tag.E6 F α a) (pinnedX Tag.E6 F β b) :=
  (simply_laced_root_commutator_unit.{0} Tag.E6 simplyLaced_E6 (mem_rootFinset.1 hα)
    (mem_rootFinset.1 hβ) hne hne').2 (fun h => hnot (mem_rootFinset.2 h)) F _
      (mem_rootSubgroup.2 ⟨a, rfl⟩) _ (mem_rootSubgroup.2 ⟨b, rfl⟩)

theorem comm_of_facts {α β : V6} (hα : α ∈ rootFinset Tag.E6) (hβ : β ∈ rootFinset Tag.E6)
    (hne : α ≠ β) (hne' : α ≠ -β) (hr : α + β ∈ rootFinset Tag.E6) :
    (commConst Tag.E6 α β (1, 1) = 1 ∨ commConst Tag.E6 α β (1, 1) = -1) ∧
    ∀ (F : Type) [Field F] (a b : F), pinnedX Tag.E6 F α a * pinnedX Tag.E6 F β b *
      (pinnedX Tag.E6 F α a)⁻¹ * (pinnedX Tag.E6 F β b)⁻¹ =
        pinnedX Tag.E6 F (α + β) ((commConst Tag.E6 α β (1, 1) : F) * a * b) := by
  obtain ⟨h1, h2⟩ := (simply_laced_root_commutator_unit.{0} Tag.E6 simplyLaced_E6
    (mem_rootFinset.1 hα) (mem_rootFinset.1 hβ) hne hne').1 (mem_rootFinset.1 hr)
  refine ⟨h1, fun F _ a b => ?_⟩
  have := h2 F a b
  rwa [commutatorElement_def] at this

theorem int_unit_ne_zero {F : Type} [Field F] {N : ℤ} (h : N = 1 ∨ N = -1) : (N : F) ≠ 0 := by
  rcases h with h | h <;> rw [h] <;> simp

@[expose] def PairFacts (γ₁ γ₂ δ₁ δ₂ : V6) : Prop :=
  (γ₁ ∈ rootFinset Tag.E6 ∧ γ₂ ∈ rootFinset Tag.E6 ∧ δ₁ ∈ rootFinset Tag.E6 ∧
      δ₂ ∈ rootFinset Tag.E6) ∧
    (γ₁ ≠ γ₂ ∧ γ₁ ≠ -γ₂ ∧ γ₁ + γ₂ ∈ rootFinset Tag.E6) ∧
    (δ₁ ≠ δ₂ ∧ δ₁ ≠ -δ₂ ∧ δ₁ + δ₂ ∈ rootFinset Tag.E6) ∧
    (∀ x ∈ [γ₁, γ₂], ∀ y ∈ [δ₁, δ₂], x ≠ y ∧ x ≠ -y ∧ x + y ∉ rootFinset Tag.E6) ∧
    (∀ i : Fin Tag.E6.rank, i.val ∉ TwClass.e6Six.J₂ → (γ₁ + γ₂) i = 0 ∧ (δ₁ + δ₂) i = 0)

section Rational

variable {K : Type} [Field K] [Finite K] (D : LangLevi Tag.E6 K wE)

theorem pinnedX_mem_adjointGroup {F : Type} [Field F] (α : V6) (c : F) :
    pinnedX Tag.E6 F α c ∈ adjointGroup Tag.E6 F :=
  rootSubgroup_le_adjointGroup α (mem_rootSubgroup.2 ⟨c, rfl⟩)

theorem exists_rational_S2 (hK : 3 ≤ Nat.card K) {γ₁ γ₂ δ₁ δ₂ : V6} (hw₁ : wE • γ₁ = δ₁)
    (hw₂ : wE • γ₂ = δ₂) (hP : PairFacts γ₁ γ₂ δ₁ δ₂) :
    ∃ (α β : D.L) (U : Finset D.L), α ≠ 0 ∧ β ≠ 0 ∧ Nat.card K ^ 2 ≤ U.card ∧
      ∀ u ∈ U, ∃ l ∈ D.frame TwClass.e6Six.S₂,
        D.g⁻¹ * baseChangeGL (algebraMap K D.L) l * D.g =
          pinnedX Tag.E6 D.L (γ₁ + γ₂) (α * u) *
            pinnedX Tag.E6 D.L (δ₁ + δ₂) (β * u ^ Nat.card K) := by
  obtain ⟨⟨r₁, r₂, r₃, r₄⟩, ⟨n₁, n₁', s₁⟩, ⟨n₂, n₂', s₂⟩, hcross, hJ⟩ := hP
  have hc : ∀ x ∈ [γ₁, γ₂], ∀ y ∈ [δ₁, δ₂], ∀ a b : D.L,
      Commute (pinnedX Tag.E6 D.L x a) (pinnedX Tag.E6 D.L y b) := by
    intro x hx y hy a b
    obtain ⟨h1, h2, h3⟩ := hcross x hx y hy
    have hxr : x ∈ rootFinset Tag.E6 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact r₁
      · exact r₂
    have hyr : y ∈ rootFinset Tag.E6 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl
      · exact r₃
      · exact r₄
    exact commute_of_facts hxr hyr h1 h2 h3 D.L a b
  have m₁ : γ₁ ∈ [γ₁, γ₂] := by simp
  have m₂ : γ₂ ∈ [γ₁, γ₂] := by simp
  have m₃ : δ₁ ∈ [δ₁, δ₂] := by simp
  have m₄ : δ₂ ∈ [δ₁, δ₂] := by simp
  obtain ⟨e₁, A₁, he₁, hA₁, hA₁f⟩ := exists_sigFix_pair D hK (mem_rootFinset.1 r₁)
    (fun a b => by rw [hw₁]; exact (hc γ₁ m₁ δ₁ m₃ a b).eq)
  obtain ⟨e₂, A₂, he₂, hA₂, hA₂f⟩ := exists_sigFix_pair D hK (mem_rootFinset.1 r₂)
    (fun a b => by rw [hw₂]; exact (hc γ₂ m₂ δ₂ m₄ a b).eq)
  rw [hw₁] at hA₁f
  rw [hw₂] at hA₂f
  set q := Nat.card K with hq
  obtain ⟨s₀, hs₀, hs₀0⟩ := Finset.exists_mem_ne (show 1 < A₁.card by nlinarith) (0 : D.L)
  obtain ⟨hN₁, hF₁⟩ := comm_of_facts r₁ r₂ n₁ n₁' s₁
  obtain ⟨hN₂, hF₂⟩ := comm_of_facts r₃ r₄ n₂ n₂' s₂
  refine ⟨(commConst Tag.E6 γ₁ γ₂ (1, 1) : D.L) * s₀,
    (commConst Tag.E6 δ₁ δ₂ (1, 1) : D.L) * (e₁ * s₀ ^ q) * e₂, A₂,
    mul_ne_zero (int_unit_ne_zero hN₁) hs₀0,
    mul_ne_zero (mul_ne_zero (int_unit_ne_zero hN₂) (mul_ne_zero he₁ (pow_ne_zero _ hs₀0))) he₂,
    hA₂, fun u hu => ?_⟩
  set y₁ := pinnedX Tag.E6 D.L γ₁ s₀ * pinnedX Tag.E6 D.L δ₁ (e₁ * s₀ ^ q) with hy₁
  set y₂ := pinnedX Tag.E6 D.L γ₂ u * pinnedX Tag.E6 D.L δ₂ (e₂ * u ^ q) with hy₂
  have hy₁G : y₁ ∈ adjointGroup Tag.E6 D.L :=
    mul_mem (pinnedX_mem_adjointGroup _ _) (pinnedX_mem_adjointGroup _ _)
  have hy₂G : y₂ ∈ adjointGroup Tag.E6 D.L :=
    mul_mem (pinnedX_mem_adjointGroup _ _) (pinnedX_mem_adjointGroup _ _)
  obtain ⟨l, hl, hle⟩ := exists_rational_comm D hy₁G hy₂G (hA₁f s₀ hs₀) (hA₂f u hu)
  have hz : y₁ * y₂ * y₁⁻¹ * y₂⁻¹ =
      pinnedX Tag.E6 D.L (γ₁ + γ₂) ((commConst Tag.E6 γ₁ γ₂ (1, 1) : D.L) * s₀ * u) *
        pinnedX Tag.E6 D.L (δ₁ + δ₂)
          ((commConst Tag.E6 δ₁ δ₂ (1, 1) : D.L) * (e₁ * s₀ ^ q) * (e₂ * u ^ q)) := by
    rw [hy₁, hy₂, comm_split (hc γ₁ m₁ δ₁ m₃ _ _) (hc γ₁ m₁ δ₂ m₄ _ _) (hc γ₂ m₂ δ₁ m₃ _ _)
      (hc γ₂ m₂ δ₂ m₄ _ _), hF₁, hF₂]
  have hgl : D.g⁻¹ * baseChangeGL (algebraMap K D.L) l * D.g = y₁ * y₂ * y₁⁻¹ * y₂⁻¹ := by
    rw [hle]
    group
  refine ⟨l, (TwBasicAux.mem_frame_iff D _ l).2 ⟨hl, ?_⟩, ?_⟩
  · rw [hgl, hz]
    have h1 : γ₁ + γ₂ ∈ TwClass.e6Six.S₂ := ⟨mem_rootFinset.1 s₁, fun i hi => (hJ i hi).1⟩
    have h2 : δ₁ + δ₂ ∈ TwClass.e6Six.S₂ := ⟨mem_rootFinset.1 s₂, fun i hi => (hJ i hi).2⟩
    exact mul_mem (pinnedX_mem_rootSpan h1 _) (pinnedX_mem_rootSpan h2 _)
  · rw [hgl, hz]
    congr 2
    ring

end Rational

theorem algebraize {E M : Type*} [Field E] [AddCommGroup M] [Module E M] (N : Submodule E M)
    (A B : M →ₗ[E] M) (q : ℕ) (hq : 2 ≤ q) (α β : E) (hα : α ≠ 0) (hβ : β ≠ 0) (U : Finset E)
    (hU : q + 1 < U.card)
    (h : ∀ u ∈ U, ∀ v ∈ N, (v + (β * u ^ q) • B v) + (α * u) • A (v + (β * u ^ q) • B v) ∈ N) :
    (∀ v ∈ N, A v ∈ N) ∧ (∀ v ∈ N, B v ∈ N) := by
  set ex : Fin 4 → ℕ := ![0, 1, q, q + 1] with hex
  have hinj : Function.Injective ex := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [ex] at hij ⊢ <;> omega
  have hd : ∀ i, ex i ≤ q + 1 := by
    intro i
    fin_cases i <;> simp [ex]
  have key : ∀ v ∈ N, ∀ i, (![v, α • A v, β • B v, (α * β) • A (B v)] : Fin 4 → M) i ∈ N := by
    intro v hv
    refine sep_inj N U (q + 1) hU ex hinj hd _ fun u hu => ?_
    have e : ∑ i, u ^ ex i • (![v, α • A v, β • B v, (α * β) • A (B v)] : Fin 4 → M) i =
        (v + (β * u ^ q) • B v) + (α * u) • A (v + (β * u ^ q) • B v) := by
      rw [Fin.sum_univ_four, map_add, map_smul]
      simp only [ex, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, pow_zero, pow_one, one_smul]
      module
    rw [e]
    exact h u hu v hv
  refine ⟨fun v hv => ?_, fun v hv => ?_⟩
  · have h1 := key v hv 1
    simp only [Matrix.cons_val_one, Matrix.head_cons] at h1
    exact (N.smul_mem_iff hα).1 h1
  · have h2 := key v hv 2
    simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at h2
    exact (N.smul_mem_iff hβ).1 h2

@[expose] def e02 : V6 := e0 + e2
@[expose] def e45 : V6 := e4 + e5

theorem wE_e02 : wE • e02 = e45 := by rw [e02, e45, smul_add, wE_e0, wE_e2]

theorem pf1 : PairFacts e02 (-e2) e45 (-e5) := by unfold PairFacts; decide +kernel
theorem pf2 : PairFacts e02 (-e0) e45 (-e4) := by unfold PairFacts; decide +kernel
theorem pf3 : PairFacts (-e02) e2 (-e45) e5 := by unfold PairFacts; decide +kernel
theorem pf4 : PairFacts (-e02) e0 (-e45) e4 := by unfold PairFacts; decide +kernel

theorem sum1 : e02 + -e2 = e0 ∧ e45 + -e5 = e4 := by
  constructor <;> simp only [e02, e45] <;> abel
theorem sum2 : e02 + -e0 = e2 ∧ e45 + -e4 = e5 := by
  constructor <;> simp only [e02, e45] <;> abel
theorem sum3 : -e02 + e2 = -e0 ∧ -e45 + e5 = -e4 := by
  constructor <;> simp only [e02, e45] <;> abel
theorem sum4 : -e02 + e0 = -e2 ∧ -e45 + e4 = -e5 := by
  constructor <;> simp only [e02, e45] <;> abel

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.IrredE6Aux
