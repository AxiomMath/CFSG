module

public import CFSG.ClassicalInvolution.Asc77.WP3SCUGenA
public import CFSG.ClassicalInvolution.Balance.StrongPowDiagMain

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Balance.StrongBalance
  CFSG.ClassicalInvolution.Balance.StrongBalance.Linear
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Disconnected
open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.RouteD.Gaps (diagGL coe_transvection_eq slConjugation_diagGL_apply)
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation)
open scoped MatrixGroups

section Sign

variable {n : ℕ} {k : Type} [Field k]

theorem slConjugation_signGL_transvection (σ : Fin n → Bool) {i j : Fin n} (hij : i ≠ j) (a : k)
    (h : σ i = σ j) :
    slConjugation n k (signGL k σ) (Matrix.SpecialLinearGroup.transvection hij a) =
      Matrix.SpecialLinearGroup.transvection hij a := by
  refine Subtype.ext (Matrix.ext fun p q => ?_)
  rw [signGL, slConjugation_diagGL_apply, coe_transvection_eq]
  have hs : (signUnit k (σ i) : k) * (((signUnit k (σ j))⁻¹ : kˣ) : k) = 1 := by
    rw [h, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hpp : ∀ p : Fin n, (signUnit k (σ p) : k) * (((signUnit k (σ p))⁻¹ : kˣ) : k) = 1 :=
    fun p => by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  by_cases hpq : p = q
  · subst hpq
    have hne : ¬ (i = p ∧ j = p) := fun ⟨h1, h2⟩ => hij (h1.trans h2.symm)
    simp only [ite_true, hne, ite_false, add_zero]
    calc _ = (signUnit k (σ p) : k) * (((signUnit k (σ p))⁻¹ : kˣ) : k) := by ring
      _ = 1 := hpp p
  · by_cases hpair : i = p ∧ j = q
    · obtain ⟨rfl, rfl⟩ := hpair
      simp only [hpq, ite_false, true_and, ite_true, zero_add]
      calc _ = a * ((signUnit k (σ i) : k) * (((signUnit k (σ j))⁻¹ : kˣ) : k)) := by ring
        _ = a := by rw [hs, mul_one]
    · simp only [hpq, hpair, ite_false, add_zero, mul_zero, zero_mul]

theorem slConjugation_signGL_diagonal (σ : Fin n → Bool) {y : SL(n, k)}
    (hy : ∃ D : Fin n → k, (y : Matrix (Fin n) (Fin n) k) = Matrix.diagonal D) :
    slConjugation n k (signGL k σ) y = y := by
  obtain ⟨D, hD⟩ := hy
  refine Subtype.ext (Matrix.ext fun p q => ?_)
  rw [signGL, slConjugation_diagGL_apply, hD]
  by_cases hpq : p = q
  · subst hpq
    simp only [Matrix.diagonal_apply_eq]
    rw [mul_comm (signUnit k (σ p) : k) (D p), mul_assoc, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, mul_one]
  · simp [Matrix.diagonal_apply_ne _ hpq]

end Sign

section Cover

variable {n : ℕ} {k : Type} [Field k] {X : Type} [Group X]

theorem commute_of_conj_eq {f x : X} (h : f * x * f⁻¹ = x) : x * f = f * x :=
  (mul_inv_eq_iff_eq_mul.mp h).symm

theorem mem_of_chart_cover (hn : 2 ≤ n) (ψ : SL(n, k) →* X) (P₀ : SL(n, k))
    (σ₁ σ₂ : Fin n → Bool) {f₁ f₂ : X}
    (h₁ : ∀ y, f₁ * (ψ.comp (MulAut.conj P₀).toMonoidHom) y * f₁⁻¹ =
      (ψ.comp (MulAut.conj P₀).toMonoidHom) (slConjugation n k (signGL k σ₁) y))
    (h₂ : ∀ y, f₂ * (ψ.comp (MulAut.conj P₀).toMonoidHom) y * f₂⁻¹ =
      (ψ.comp (MulAut.conj P₀).toMonoidHom) (slConjugation n k (signGL k σ₂) y))
    {W : Subgroup X}
    (hW : ∀ x ∈ ψ.range, (x * f₁ = f₁ * x ∨ x * f₂ = f₂ * x ∨ x * (f₁ * f₂) = (f₁ * f₂) * x) →
      x ∈ W) : ψ.range ≤ W := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  set Ψ := ψ.comp (MulAut.conj P₀).toMonoidHom with hΨ
  have hΨrange : ∀ y, Ψ y ∈ ψ.range := fun y => ⟨P₀ * y * P₀⁻¹, rfl⟩
  have hall : ∀ y, Ψ y ∈ W := by
    intro y
    refine Matrix.SpecialLinearGroup.diagonal_transvection_induction' (fun y => Ψ y ∈ W) y
      ?_ ?_ ?_
    · intro i j hij c hc
      refine hW _ (hΨrange _) (Or.inl (commute_of_conj_eq ?_))
      rw [h₁, slConjugation_signGL_diagonal σ₁
        ⟨_, Matrix.SpecialLinearGroup.diag2n_coe hij c hc⟩]
    · intro i j hij a
      by_cases e1 : σ₁ i = σ₁ j
      · refine hW _ (hΨrange _) (Or.inl (commute_of_conj_eq ?_))
        rw [h₁, slConjugation_signGL_transvection σ₁ hij a e1]
      · by_cases e2 : σ₂ i = σ₂ j
        · refine hW _ (hΨrange _) (Or.inr (Or.inl (commute_of_conj_eq ?_)))
          rw [h₂, slConjugation_signGL_transvection σ₂ hij a e2]
        · refine hW _ (hΨrange _) (Or.inr (Or.inr (commute_of_conj_eq ?_)))
          have e : (f₁ * f₂) * Ψ (Matrix.SpecialLinearGroup.transvection hij a) * (f₁ * f₂)⁻¹ =
              f₁ * (f₂ * Ψ (Matrix.SpecialLinearGroup.transvection hij a) * f₂⁻¹) * f₁⁻¹ := by
            group
          have hcomp : slConjugation n k (signGL k σ₁) (slConjugation n k (signGL k σ₂)
              (Matrix.SpecialLinearGroup.transvection hij a)) =
              slConjugation n k (signGL k fun j => decide (σ₁ j = σ₂ j))
                (Matrix.SpecialLinearGroup.transvection hij a) := by
            rw [signGL_agree, map_mul]
            rfl
          rw [e, h₂, h₁, hcomp, slConjugation_signGL_transvection
            (fun j => decide (σ₁ j = σ₂ j)) hij a (decide_eq_of_ne e1 e2)]
    · intro A B hA hB
      simp only [map_mul]
      exact W.mul_mem hA hB
  rintro _ ⟨y, rfl⟩
  have : ψ y = Ψ (P₀⁻¹ * y * P₀) := by
    simp only [hΨ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul,
      map_inv]
    group
  rw [this]
  exact hall _

end Cover

section Comp

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

omit [Finite G] in
theorem exists_mem_not_mem_finset (B : Subgroup G) (S : Finset G) (h : S.card < Nat.card B) :
    ∃ b ∈ B, b ∉ S := by
  by_contra hcon
  push Not at hcon
  have hsub : (B : Set G) ⊆ (S : Set G) := fun b hb => by simpa using hcon b hb
  have h1 : Nat.card B ≤ S.card := by
    have := Set.ncard_le_ncard hsub S.finite_toSet
    calc Nat.card B = (B : Set G).ncard := (Nat.card_coe_set_eq _)
      _ ≤ (S : Set G).ncard := this
      _ = S.card := Set.ncard_coe_finset S
  omega

omit [Fact p.Prime] [Finite G] in
theorem exists_two_gens {B : Subgroup G} (hB8 : Nat.card B = 8) :
    ∃ e₁ ∈ B, ∃ e₂ ∈ B, e₁ ≠ 1 ∧ e₁ ≠ c ∧ e₂ ≠ 1 ∧ e₂ ≠ c ∧ e₁ * e₂ ≠ 1 ∧ e₁ * e₂ ≠ c := by
  classical
  obtain ⟨e₁, he₁B, he₁⟩ := exists_mem_not_mem_finset B {1, c} (by
    rw [hB8]; exact (Finset.card_le_two).trans_lt (by norm_num))
  obtain ⟨e₂, he₂B, he₂⟩ := exists_mem_not_mem_finset B {1, c, e₁⁻¹, e₁⁻¹ * c} (by
    rw [hB8]
    exact (Finset.card_le_four).trans_lt (by norm_num))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at he₁ he₂
  refine ⟨e₁, he₁B, e₂, he₂B, he₁.1, he₁.2, he₂.1, he₂.2.1, fun h => he₂.2.2.1 ?_, fun h => ?_⟩
  · exact eq_inv_of_mul_eq_one_right h
  · apply he₂.2.2.2
    rw [← h]
    group

theorem range_secComponentHom_le_memberJoin (hs : SecData p f c (exactFamily Ω c))
    (D : LocalLieSystemAt p f (exactFamily Ω c) c) (j : Fin D.card) :
    (secComponentHom hs.normalizes D j).range ≤ memberJoin (exactFamily Ω c) c := by
  rintro _ ⟨k, rfl⟩
  rw [← range_sectionQuotientHom hs.normalizes]
  exact ⟨D.hom j k, rfl⟩

theorem notMoved_comp_mem (hΩ : ConjInvariant Ω) {B : Subgroup G} (hB : IsElemAbelian 2 B)
    (hcB : c ∈ B) (hc1 : c ≠ 1) (hs : SecData p f c (exactFamily Ω c))
    (D : LocalLieSystemAt p f (exactFamily Ω c) c) (j : Fin D.card)
    (hnot : ¬ MovedByAll B c (secComponentHom hs.normalizes D j).range)
    (k : (compModel D j).K) :
    secComponentHom hs.normalizes D j k ∈ modOdd c (⨆ F ∈ signalizerFunctorEk 2 2 B,
      (Subgroup.centralizer (F : Set G) ⊓ exactLayer Ω c)) := by
  obtain ⟨x, hxB, hxZ, hx⟩ : ∃ x ∈ modOdd c B, x ∉ modOdd c (Subgroup.zpowers c) ∧
      ∀ y ∈ (secComponentHom hs.normalizes D j).range, x * y = y * x := by
    by_contra hcon
    apply hnot
    intro x hx hxZ
    by_contra hne
    push Not at hne
    exact hcon ⟨x, hx, hxZ, hne⟩
  obtain ⟨e, heB, rfl⟩ := mem_modOdd_iff.mp hxB
  have he1 : (e : G) ≠ 1 := by
    intro h
    apply hxZ
    have : e = 1 := Subtype.ext h
    rw [this, map_one]
    exact Subgroup.one_mem _
  have hec : (e : G) ≠ c := by
    intro h
    apply hxZ
    have : e = ⟨c, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ := Subtype.ext h
    rw [this]
    exact oddQuotMk_mem_modOdd (Subgroup.mem_zpowers c) _
  exact mem_modOdd_of_commutes_gen hΩ hB hcB hc1 heB he1 hec
    (range_secComponentHom_le_memberJoin hs D j ⟨k, rfl⟩) fun he => hx _ ⟨k, rfl⟩

theorem psl_comp_mem_of_diag (hΩ : ConjInvariant Ω) {B : Subgroup G} (hB : IsElemAbelian 2 B)
    (hB8 : Nat.card B = 8) (hcB : c ∈ B) (hc1 : c ≠ 1) (hs : SecData p f c (exactFamily Ω c))
    (D : LocalLieSystemAt p f (exactFamily Ω c) c) (j : Fin D.card) (htag : D.tag j = .PSL)
    (hp2 : p ≠ 2)
    (hdiag : ToralActionDiag 2 (D.tag j) (D.rank j) p (D.exp j) Fact.out
      (secComponentHom hs.normalizes D j) (modOdd c B)) (k : (compModel D j).K) :
    secComponentHom hs.normalizes D j k ∈ modOdd c (⨆ F ∈ signalizerFunctorEk 2 2 B,
      (Subgroup.centralizer (F : Set G) ⊓ exactLayer Ω c)) := by
  obtain ⟨ε, P, hP, hact⟩ := hdiag.1 htag
  have hn : 2 ≤ D.rank j := by
    have := D.admissible j
    rw [htag] at this
    exact this.2.2.1
  have h2 : (2 : GaloisField p (D.exp j)) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField (D.exp j) hp2
  set ψ' := (secComponentHom hs.normalizes D j).comp ε.symm.toMonoidHom with hψ'
  have hBC : B ≤ Subgroup.centralizer ({c} : Set G) := Lemma52Proof.le_centralizer_of_mem hB hcB
  obtain ⟨e₁, he₁B, e₂, he₂B, he₁1, he₁c, he₂1, he₂c, he₁₂1, he₁₂c⟩ := exists_two_gens (c := c) hB8
  set f₁ : OddQuot c := oddQuotMk c ⟨e₁, hBC he₁B⟩ with hf₁
  set f₂ : OddQuot c := oddQuotMk c ⟨e₂, hBC he₂B⟩ with hf₂
  have hf₁B : f₁ ∈ modOdd c B := oddQuotMk_mem_modOdd he₁B (hBC he₁B)
  have hf₂B : f₂ ∈ modOdd c B := oddQuotMk_mem_modOdd he₂B (hBC he₂B)
  obtain ⟨P₀, σ₁, σ₂, hch₁, hch₂⟩ := exists_chart_of_lifts_gl (by omega) h2 ψ'
    ⟨P, hP, hact⟩ hf₁B hf₂B
  have hrange : ψ'.range = (secComponentHom hs.normalizes D j).range :=
    BootRank3.range_comp_symm ε _
  have hcover := mem_of_chart_cover hn ψ' P₀ σ₁ σ₂ hch₁ hch₂
    (W := modOdd c (⨆ F ∈ signalizerFunctorEk 2 2 B,
      (Subgroup.centralizer (F : Set G) ⊓ exactLayer Ω c))) (fun x hx hcomm => by
      have hxJ : x ∈ memberJoin (exactFamily Ω c) c :=
        range_secComponentHom_le_memberJoin hs D j (hrange ▸ hx)
      rcases hcomm with h | h | h
      · exact mem_modOdd_of_commutes_gen hΩ hB hcB hc1 he₁B he₁1 he₁c hxJ fun he => h.symm
      · exact mem_modOdd_of_commutes_gen hΩ hB hcB hc1 he₂B he₂1 he₂c hxJ fun he => h.symm
      · have hmul : oddQuotMk c ⟨e₁ * e₂, hBC (B.mul_mem he₁B he₂B)⟩ = f₁ * f₂ := by
          rw [hf₁, hf₂, ← map_mul]
          rfl
        exact mem_modOdd_of_commutes_gen hΩ hB hcB hc1 (B.mul_mem he₁B he₂B) he₁₂1 he₁₂c hxJ
          fun he => by
            have := h.symm
            rwa [← hmul] at this)
  have hmem : secComponentHom hs.normalizes D j k ∈ ψ'.range := ⟨ε k, by simp [hψ']⟩
  exact hcover hmem

end Comp

end CFSG.ClassicalInvolution.Asc77
