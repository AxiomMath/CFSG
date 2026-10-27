module

public import CFSG.LieType.SeitzGeneration.OuterOrthGeneric
public import CFSG.RankThree.PartOne.SEITZ2.OmegaTail
public import CFSG.RankThree.PartOne.KC.OrthogonalNoninnerPlane
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldBY

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix Subgroup CFSG.RankThree.PartOne CFSG.RankThree.PartOne.CTP
  CFSG.RankThree.PartOne.KCOrthogonalSubfield CFSG.RankThree.Classical.SteinbergBY
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBHigherLinearField
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open CFSG.Assembly.LowTwoRank (StatedProj StatedOmega StatedQuadMinus StatedLieAdmissible
  StatedLieTag StatedClassicalModel)

section Rational

variable {n ℓ e p : ℕ} {K : Type} [Field K] [Finite K]

omit [Finite K] in
theorem fixed_of_orderOf_orth {k : Subfield K} {σ₀ : K ≃+* K} (hℓ : ℓ.Prime) (he : 1 ≤ e)
    (hp : p.Prime) (hK : Nat.card K = ℓ ^ (e * p)) (hσ₀ : orderOf σ₀ = p)
    (hfix : ∀ x, x ∈ k ↔ σ₀ x = x) {σ : K ≃+* K} (hσ : orderOf σ = p) :
    ∀ x, x ∈ k ↔ σ x = x := by
  have hf : 1 ≤ e * p := Nat.mul_pos he hp.pos
  have hzp : Subgroup.zpowers σ₀ = Subgroup.zpowers σ :=
    zpowers_ringEquiv_eq_of_orderOf hℓ hf hK hσ₀ hσ
  have key : ∀ {a a' : K ≃+* K}, Subgroup.zpowers a = Subgroup.zpowers a' →
      ∀ x, a x = x → a' x = x := by
    intro a a' haa' x hx
    have hb : a' ∈ Subgroup.zpowers a := haa' ▸ Subgroup.mem_zpowers a'
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    have hstab : Subgroup.zpowers a ≤ MulAction.stabilizer (K ≃+* K) x :=
      (Subgroup.zpowers_le (H := MulAction.stabilizer (K ≃+* K) x)).mpr hx
    exact hstab (Subgroup.zpow_mem_zpowers a m)
  intro x
  rw [hfix x]
  exact ⟨key hzp x, key hzp.symm x⟩

theorem fieldAutData_minus_rational (hpair : SubfieldPairOmegaMinus) (hn : 4 ≤ n) (hn1 : 1 ≤ n)
    (hℓ : ℓ.Prime) (he : 1 ≤ e) (hp : p.Prime) (hp3 : 3 < p) (hpℓ : p ≠ ℓ) {k : Subfield K}
    (hk : Nat.card k = ℓ ^ e) (hK : Nat.card K = ℓ ^ (e * p)) {σ₀ : K ≃+* K}
    (hσ₀ : orderOf σ₀ = p) (hfix : ∀ x, x ∈ k ↔ σ₀ x = x) (b c : k)
    (hirr : ∀ s : k, s ^ 2 + b * s + c ≠ 0) :
    FieldAutData (matrixProjectiveDerived (coordinateQuadMinus n K hn1 (b : K) (c : K))) p := by
  classical
  have hp2 : p ≠ 2 := by omega
  have hf : 1 ≤ e * p := Nat.mul_pos he hp.pos
  have hfixall := fun σ (h : orderOf σ = p) => fixed_of_orderOf_orth hℓ he hp hK hσ₀ hfix h
  have hirrK : ∀ s : K, s ^ 2 + (b : K) * s + (c : K) ≠ 0 :=
    rootFree_of_odd_degree k hp hp2 (finrank_subfield_eq k hℓ he hk hK) b c hirr
  have hM : StatedClassicalModel
      (StatedProj (StatedOmega (StatedQuadMinus n K (b : K) (c : K)))) .POmegaMinus n ℓ (e * p) :=
    ⟨⟨hℓ, hf, hn⟩, K, inferInstance, inferInstance, hK, b, c, hirrK, ⟨MulEquiv.refl _⟩⟩
  have hg : OrthogonalGates (coordinateQuadMinus n K hn1 (b : K) (c : K)) (e * p) :=
    orthogonal_large_prime_semilinear_field_and_diagonal_gates _ .POmegaMinus
      (Or.inr (Or.inr rfl)) n ℓ (e * p) hM hn1 K hK b c hirrK (MulEquiv.refl _)
  refine fieldAutData_matrixProjectiveDerived _ hℓ hf hK hp hp3 hg
    (fun σ h v => coordinateQuadMinus_fieldAut k n hn1 (hfixall σ h) b c v) ?_ ?_
  · intro α hα
    obtain ⟨hE, hD⟩ := outer_mem_E_not_D hg hp hp3 hα
    have hdesc := orthogonal_prime_semilinear_actual_fixed_form_descent _ .POmegaMinus
      (Or.inr (Or.inr rfl)) n ℓ (e * p) p hM hp hp3 hpℓ hn1 K hK b c hirrK (MulEquiv.refl _) α hE hD
      hα.1
    refine exists_conj_fieldAutT_of_descent _ hE hdesc
      (fun σ h v => coordinateQuadMinus_fieldAut k n hn1 (hfixall σ h) b c v) ?_
    intro U Q₀ hord hdisp
    obtain ⟨b', c', hirr', ν, S₀, -, -, S, ν', hSQ, -, hSA, -⟩ := hdisp
    have hfixV := hfixall U.val.right hord
    have hσk' : ∀ x, x ∈ semilinearFixedSubfield U.val.right ↔ U.val.right x = x :=
      fun x => RingHom.mem_eqLocusField
    have hb'k : (b' : K) ∈ k := (hfixV _).2 ((hσk' _).1 b'.2)
    have hc'k : (c' : K) ∈ k := (hfixV _).2 ((hσk' _).1 c'.2)
    have hirrkK : ∀ s ∈ k, s ^ 2 + (b : K) * s + (c : K) ≠ 0 := fun s hs hz =>
      hirr ⟨s, hs⟩ (Subtype.ext (by simpa using hz))
    have hirr'kK : ∀ s ∈ k, s ^ 2 + (b' : K) * s + (c' : K) ≠ 0 := by
      intro s hs hz
      have hsV : s ∈ KCOrthogonalDescent.fixedField U.val := (hσk' s).2 ((hfixV s).1 hs)
      exact hirr' ⟨s, hsV⟩ (Subtype.ext (by simpa using hz))
    obtain ⟨μ, hμk, hμQ⟩ :=
      SEITZ2.exists_tail_isometry k hn1 b.2 c.2 hb'k hc'k hirrkK hirr'kK
    have hμσ : glFieldAut (Fin (2 * n)) K U.val.right μ = μ :=
      Units.ext (Matrix.ext fun i j => (hfixV _).1 (hμk i j))
    refine ⟨μ * S, ν', fun v => ?_, ?_⟩
    · rw [Units.val_mul, ← Matrix.mulVec_mulVec]
      exact (hμQ _).trans (hSQ v)
    · rw [mul_assoc, hSA, map_mul, hμσ]
  · intro σ hσ
    obtain ⟨-, hconc⟩ :=
      orthogonal_prime_subfield_fixed_group_and_full_centralizer_unconditional .POmegaMinus
        (Or.inr (Or.inr rfl)) n ℓ e p ⟨hℓ, he, hn⟩ hp hp3 hpℓ hn1 K k hk hK σ hσ (hfixall σ hσ)
        b c hirr
    exact fixedGood_of_subfieldConclusion hconc
      (hpair n ℓ e p hn hℓ he hp hp3 hpℓ K k hk hK b c hirr)

end Rational

section Model

variable {G : Type} [Group G] [Finite G] {n ℓ f p : ℕ}

omit [Finite G] in
theorem isOuterOfOrder_congr {P : Type} [Group P] (e : G ≃* P) {α : MulAut G}
    (hα : IsOuterOfOrder p α) : IsOuterOfOrder p (MulAut.congr e α) :=
  ⟨(MulEquiv.orderOf_eq (MulAut.congr e) α).trans hα.1, fun g hg =>
    hα.2 (e.symm g) (eq_conj_of_congr_eq_conj e hg)⟩

theorem exists_conj_mem_of_plane_orth {c : StatedLieTag}
    (hc : c = .POmegaOdd ∨ c = .POmegaPlus ∨ c = .POmegaMinus)
    (hM : StatedClassicalModel G c n ℓ f) (hp : p.Prime) (hp3 : 3 < p) (hpℓ : p ≠ ℓ)
    (E : Subgroup (MulAut G)) (hE : CFSG.IsElementaryAbelian p E) (hEc : Nat.card E = p ^ 2) :
    ∃ g : G, g ≠ 1 ∧ MulAut.conj g ∈ E := by
  have : Fact p.Prime := ⟨hp⟩
  have hp1 : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hp.one_lt
  have hnontriv : ∃ x : MulAut G, x ∈ E ∧ x ∈ (MulAut.conj : G →* MulAut G).range ∧ x ≠ 1 := by
    by_cases hin : E ≤ (MulAut.conj : G →* MulAut G).range
    · have hne : E ≠ ⊥ := fun h0 => by
        have := Subgroup.card_eq_one.2 h0
        omega
      obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
      exact ⟨x, x.2, hin x.2, fun h => hx1 (Subtype.ext h)⟩
    · have hpl := orthogonal_noninner_plane_local_core_product_odd_of_subfield
        orthogonal_prime_subfield_core_clause_unconditional G c ℓ f n p hc hM hp hp3 hpℓ
        ⊤ le_top E le_top hE hEc hin
      have hne : (E ⊓ (MulAut.conj : G →* MulAut G).range) ≠ ⊥ := fun h0 => by
        have := Subgroup.card_eq_one.2 h0
        have h1 := hpl.1
        rw [this] at h1
        have := hp.one_lt
        omega
      obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
      exact ⟨x, x.2.1, x.2.2, fun h => hx1 (Subtype.ext h)⟩
  obtain ⟨x, hxE, ⟨g, hg⟩, hx1⟩ := hnontriv
  exact ⟨g, fun h1 => hx1 (by rw [← hg, h1, map_one]), hg ▸ hxE⟩

omit [Finite G] in
theorem exists_rational_model_minus (hn1 : 1 ≤ n) (hM : StatedClassicalModel G .POmegaMinus n ℓ f)
    (hp : p.Prime) (hp3 : 3 < p) (hpℓ : p ≠ ℓ) {α : MulAut G} (hα : IsOuterOfOrder p α) :
    ∃ (e : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (k : Subfield K) (σ : K ≃+* K) (b c : k),
      1 ≤ e ∧ f = p * e ∧ Nat.card k = ℓ ^ e ∧ Nat.card K = ℓ ^ (e * p) ∧ orderOf σ = p ∧
        (∀ x, x ∈ k ↔ σ x = x) ∧ (∀ s : k, s ^ 2 + b * s + c ≠ 0) ∧
        Nonempty (G ≃* matrixProjectiveDerived (coordinateQuadMinus n K hn1 (b : K) (c : K))) := by
  classical
  have hf1 : 1 ≤ f := hM.1.2.1
  obtain ⟨-, K, _, _, hK, b₁, c₁, hirr₁, ⟨e₁⟩⟩ := id hM
  have hg : OrthogonalGates (coordinateQuadMinus n K hn1 b₁ c₁) f :=
    orthogonal_large_prime_semilinear_field_and_diagonal_gates G .POmegaMinus
      (Or.inr (Or.inr rfl)) n ℓ f hM hn1 K hK b₁ c₁ hirr₁ e₁
  have ha := isOuterOfOrder_congr (coordinateMinusWitnessEquiv K hn1 b₁ c₁ e₁) hα
  obtain ⟨haE, haD⟩ := outer_mem_E_not_D hg hp hp3 ha
  have hdesc := orthogonal_prime_semilinear_actual_fixed_form_descent G .POmegaMinus
    (Or.inr (Or.inr rfl)) n ℓ f p hM hp hp3 hpℓ hn1 K hK b₁ c₁ hirr₁ e₁ _ haE haD ha.1
  obtain ⟨g, hg'⟩ := haE
  obtain ⟨hpf, hrest⟩ := hdesc
  obtain ⟨hord', hcard, V, cc, Q₀, hVκ, hVr, hFFD, hDisp⟩ := hrest g.val.right ⟨g, hg', rfl⟩
  obtain ⟨b', c', hirr', ν, S₀, hS₀, hCM, hT⟩ := hDisp
  obtain ⟨S, ν', hSQ, hSS₀, hSA, Θ, hΘ1, g', hg'l, hg'r, hΘ⟩ := hT
  obtain ⟨e, rfl⟩ := hpf
  have he : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with h0 | h0
    · rw [h0, mul_zero] at hf1
      omega
    · exact h0
  rw [Nat.mul_div_cancel_left e hp.pos] at hcard
  have hσV : orderOf V.val.right = p := by rw [hVr]; exact hord'
  have hσk : ∀ x, x ∈ semilinearFixedSubfield V.val.right ↔ V.val.right x = x :=
    fun x => RingHom.mem_eqLocusField
  have hcard' : Nat.card (semilinearFixedSubfield V.val.right) = ℓ ^ e := by
    rw [hVr]
    exact hcard
  exact ⟨e, K, inferInstance, inferInstance, semilinearFixedSubfield V.val.right, V.val.right,
    b', c', he, rfl, hcard', by rw [mul_comm]; exact hK, hσV, hσk, hirr',
    ⟨(coordinateMinusWitnessEquiv K hn1 b₁ c₁ e₁).trans Θ⟩⟩

theorem fieldAutData_minus (hpair : SubfieldPairOmegaMinus)
    (hM : StatedClassicalModel G .POmegaMinus n ℓ f) (hp : p.Prime) (hp3 : 3 < p)
    (hpℓ : p ≠ ℓ) : FieldAutData G p := by
  obtain ⟨hℓ, hf, hn⟩ := id hM.1
  have hn1 : 1 ≤ n := by omega
  by_cases hex : ∃ α : MulAut G, IsOuterOfOrder p α
  · obtain ⟨α, hα⟩ := hex
    obtain ⟨e, K, _, _, k, σ, b, c, he, -, hk, hK, hσ, hfix, hirr, ⟨ψ⟩⟩ :=
      exists_rational_model_minus hn1 hM hp hp3 hpℓ hα
    exact (fieldAutData_minus_rational hpair hn hn1 hℓ he hp hp3 hpℓ hk hK hσ hfix b c
      hirr).of_mulEquiv ψ hp
  · exact ⟨fun E hE hEc => exists_conj_mem_of_plane_orth (Or.inr (Or.inr rfl)) hM hp hp3 hpℓ E hE
      hEc, fun σ hσ => absurd ⟨σ, hσ⟩ hex, fun σ τ hσ _ _ => absurd ⟨σ, hσ⟩ hex⟩

end Model

end CFSG.LieType.SeitzGeneration
