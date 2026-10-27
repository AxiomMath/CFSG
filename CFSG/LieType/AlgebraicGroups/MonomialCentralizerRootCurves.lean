module

public import CFSG.LieType.AlgebraicGroups.IdentityComponentLang
import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassD4
import CFSG.LieType.SeitzGeneration.ExcHighThree.RootDegreeInj
import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCoverRoots

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {τ : Tag} {k : Type} [Field k]

section Curves


theorem infinite_range_of_isPolynomialCurve [Infinite k] {c : k → ModGL τ k}
    (hc : IsPolynomialCurve c) {s t : k} (hst : c s ≠ c t) : (Set.range c).Infinite := by
  obtain ⟨P, hP⟩ := hc
  intro hfin
  have hne : ∃ a b, (P a b).eval s ≠ (P a b).eval t := by
    by_contra h
    push Not at h
    apply hst
    have hE : endMatrix τ (c s : Module.End k (RootModule τ k)) =
        endMatrix τ (c t : Module.End k (RootModule τ k)) := by
      ext a b
      rw [hP s a b, hP t a b, h a b]
    refine Units.ext ?_
    have hEnd := (LinearMap.toMatrixAlgEquiv (v₁ := Finsupp.basisSingleOne)).injective hE
    simpa only [endMatrix] using hEnd
  obtain ⟨a, b, hab⟩ := hne
  set p : Polynomial k := P a b with hp
  have hrange : (Set.range fun x : k => p.eval x).Finite := by
    have himg := hfin.image
      (fun A : ModGL τ k => endMatrix τ (A : Module.End k (RootModule τ k)) a b)
    refine Set.Finite.subset himg ?_
    rintro y ⟨x, rfl⟩
    exact ⟨c x, ⟨x, rfl⟩, hP x a b⟩
  have hcover : (Set.univ : Set k) ⊆
      ⋃ v ∈ Set.range fun x : k => p.eval x, {x | p.eval x = v} := by
    intro x _
    exact Set.mem_iUnion.2 ⟨p.eval x, Set.mem_iUnion.2 ⟨⟨x, rfl⟩, rfl⟩⟩
  have hfinite : (Set.univ : Set k).Finite := by
    refine Set.Finite.subset (hrange.biUnion (fun v _ => ?_)) hcover
    have hv : p - Polynomial.C v ≠ 0 := by
      intro hv
      apply hab
      rw [sub_eq_zero.1 hv]
      simp
    have := Polynomial.finite_setOfPred_isRoot hv
    simpa [Polynomial.IsRoot, sub_eq_zero] using this
  exact Set.infinite_univ hfinite

end Curves



private lemma weylQuotientHom_mul_self {n : ModGL τ k} (hn : n ∈ monomialSubgroup τ k)
    (hn2 : n ^ 2 = 1) :
    weylQuotientHom τ k ⟨n, hn⟩ * weylQuotientHom τ k ⟨n, hn⟩ = 1 := by
  have hn2' : n * n = 1 := by simpa [pow_two] using hn2
  have h : (⟨n, hn⟩ * ⟨n, hn⟩ : monomialSubgroup τ k) = 1 := by
    refine Subtype.ext ?_
    simpa using hn2'
  have := congrArg (weylQuotientHom τ k) h
  rw [map_mul, map_one] at this
  exact this

private lemma monomial_mu_mul_eq_one {n : ModGL τ k} (hn : n ∈ monomialSubgroup τ k)
    (hn2 : n ^ 2 = 1) {γ : Fin τ.rank → ℤ} (_hγ : IsRoot τ γ) {μ μ' : kˣ}
    (hμ : ∀ c : k, n * pinnedX τ k γ c * n⁻¹ =
      pinnedX τ k (weylQuotientHom τ k ⟨n, hn⟩ • γ) (μ * c))
    (hμ' : ∀ c : k, n * pinnedX τ k (weylQuotientHom τ k ⟨n, hn⟩ • γ) c * n⁻¹ =
      pinnedX τ k γ (μ' * c)) : μ' * μ = 1 := by
  have hn2' : n * n = 1 := by simpa [pow_two] using hn2
  have hnin : n⁻¹ * n⁻¹ = 1 := by rw [← mul_inv_rev, hn2', inv_one]
  have hX : ∀ c : k, pinnedX τ k γ (μ' * μ * c) = pinnedX τ k γ c := by
    intro c
    calc pinnedX τ k γ (μ' * μ * c)
        = pinnedX τ k γ (μ' * (μ * c)) := by
          congr 1
          ring
      _ = n * pinnedX τ k (weylQuotientHom τ k ⟨n, hn⟩ • γ) (μ * c) * n⁻¹ :=
          (hμ' (μ * c)).symm
      _ = n * (n * pinnedX τ k γ c * n⁻¹) * n⁻¹ := by rw [← hμ c]
      _ = pinnedX τ k γ c := by
          have hcalc : n * (n * pinnedX τ k γ c * n⁻¹) * n⁻¹ =
              (n * n) * pinnedX τ k γ c * (n⁻¹ * n⁻¹) := by group
          rw [hcalc, hn2', hnin, one_mul, mul_one]
  have h1 := hX 1
  rw [mul_one] at h1
  exact Units.ext (by simpa using (pinnedX_injective τ k γ h1))

private lemma rootChar_weyl_smul {a : Fin τ.rank → kˣ} {n : ModGL τ k}
    (hn : n ∈ monomialSubgroup τ k) (hna : rootDiagUnit τ a * n = n * rootDiagUnit τ a)
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) {μ : kˣ}
    (hμ : ∀ c : k, n * pinnedX τ k γ c * n⁻¹ =
      pinnedX τ k (weylQuotientHom τ k ⟨n, hn⟩ • γ) (μ * c)) :
    rootChar a (weylQuotientHom τ k ⟨n, hn⟩ • γ) = rootChar a γ := by
  have hβ : IsRoot τ (weylQuotientHom τ k ⟨n, hn⟩ • γ) := IsRoot.smul hγ _
  have hkey : rootDiagUnit τ a * (n * pinnedX τ k γ (1 : k) * n⁻¹) *
        (rootDiagUnit τ a)⁻¹ =
      n * (rootDiagUnit τ a * pinnedX τ k γ (1 : k) * (rootDiagUnit τ a)⁻¹) * n⁻¹ := by
    calc rootDiagUnit τ a * (n * pinnedX τ k γ (1 : k) * n⁻¹) * (rootDiagUnit τ a)⁻¹
        = (rootDiagUnit τ a * n) * pinnedX τ k γ (1 : k) *
            (n⁻¹ * (rootDiagUnit τ a)⁻¹) := by group
      _ = (n * rootDiagUnit τ a) * pinnedX τ k γ (1 : k) *
            ((rootDiagUnit τ a)⁻¹ * n⁻¹) := by
          have hinv : n⁻¹ * (rootDiagUnit τ a)⁻¹ =
              (rootDiagUnit τ a)⁻¹ * n⁻¹ := by
            rw [← mul_inv_rev, hna, mul_inv_rev]
          rw [hna, hinv]
      _ = n * (rootDiagUnit τ a * pinnedX τ k γ (1 : k) * (rootDiagUnit τ a)⁻¹) * n⁻¹ := by
          group
  have h3 : pinnedX τ k (weylQuotientHom τ k ⟨n, hn⟩ • γ)
        ((rootChar a (weylQuotientHom τ k ⟨n, hn⟩ • γ) : k) * ((μ : k) * 1)) =
      pinnedX τ k (weylQuotientHom τ k ⟨n, hn⟩ • γ)
        ((μ : k) * ((rootChar a γ : k) * 1)) := by
    calc pinnedX τ k (weylQuotientHom τ k ⟨n, hn⟩ • γ)
          ((rootChar a (weylQuotientHom τ k ⟨n, hn⟩ • γ) : k) * ((μ : k) * 1))
        = rootDiagUnit τ a * pinnedX τ k (weylQuotientHom τ k ⟨n, hn⟩ • γ) ((μ : k) * 1) *
            (rootDiagUnit τ a)⁻¹ := (rootDiagUnit_conj_pinnedX a hβ ((μ : k) * 1)).symm
      _ = rootDiagUnit τ a * (n * pinnedX τ k γ (1 : k) * n⁻¹) * (rootDiagUnit τ a)⁻¹ := by
          rw [← hμ 1]
      _ = n * (rootDiagUnit τ a * pinnedX τ k γ (1 : k) * (rootDiagUnit τ a)⁻¹) * n⁻¹ :=
          hkey
      _ = n * pinnedX τ k γ ((rootChar a γ : k) * 1) * n⁻¹ := by
          rw [rootDiagUnit_conj_pinnedX a hγ (1 : k)]
      _ = pinnedX τ k (weylQuotientHom τ k ⟨n, hn⟩ • γ)
            ((μ : k) * ((rootChar a γ : k) * 1)) := hμ ((rootChar a γ : k) * 1)
  have h := pinnedX_injective τ k (weylQuotientHom τ k ⟨n, hn⟩ • γ) h3
  rw [mul_one, mul_one] at h
  have h' : (μ : k) * (rootChar a (weylQuotientHom τ k ⟨n, hn⟩ • γ) : k) =
      (μ : k) * (rootChar a γ : k) := by
    rw [mul_comm (μ : k) (rootChar a (weylQuotientHom τ k ⟨n, hn⟩ • γ) : k)]
    exact h
  exact Units.ext (mul_left_cancel₀ μ.ne_zero h')

private lemma commute_rootDiagUnit_pinnedX {a : Fin τ.rank → kˣ} {γ : Fin τ.rank → ℤ}
    (hγ : IsRoot τ γ) (hχ : rootChar a γ = 1) (c : k) :
    Commute (pinnedX τ k γ c) (rootDiagUnit τ a) := by
  have h := rootDiagUnit_conj_pinnedX a hγ c
  rw [hχ] at h
  simp only [Units.val_one, one_mul] at h
  change pinnedX τ k γ c * rootDiagUnit τ a = rootDiagUnit τ a * pinnedX τ k γ c
  calc pinnedX τ k γ c * rootDiagUnit τ a
      = (rootDiagUnit τ a * pinnedX τ k γ c * (rootDiagUnit τ a)⁻¹) *
          rootDiagUnit τ a := by rw [h]
    _ = rootDiagUnit τ a * pinnedX τ k γ c := by group

private lemma commute_of_conj_eq_self {g n : ModGL τ k} (h : n * g * n⁻¹ = g) :
    Commute g n := by
  change g * n = n * g
  calc g * n = (n * g * n⁻¹) * n := by rw [h]
    _ = n * g := by group

private lemma isPolynomialCurve_pinnedX_mul (α : Fin τ.rank → ℤ) (c : k) :
    IsPolynomialCurve fun t : k => pinnedX τ k α (c * t) := by
  obtain ⟨P, hP⟩ := isPolynomialCurve_pinnedX (τ := τ) (k := k) α
    (Polynomial.C c * Polynomial.X)
  refine ⟨P, fun t a b => ?_⟩
  change endMatrix τ (pinnedX τ k α (c * t) : Module.End k (RootModule τ k)) a b =
    (P a b).eval t
  have hc : c * t = (Polynomial.C c * Polynomial.X).eval t := by
    simp [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  rw [hc, hP]

private lemma isPolynomialCurve_pinnedX_mul_sq (α : Fin τ.rank → ℤ) (c : k) :
    IsPolynomialCurve fun t : k => pinnedX τ k α (c * t ^ 2) := by
  obtain ⟨P, hP⟩ := isPolynomialCurve_pinnedX (τ := τ) (k := k) α
    (Polynomial.C c * Polynomial.X ^ 2)
  refine ⟨P, fun t a b => ?_⟩
  change endMatrix τ (pinnedX τ k α (c * t ^ 2) : Module.End k (RootModule τ k)) a b =
    (P a b).eval t
  have hc : c * t ^ 2 = (Polynomial.C c * Polynomial.X ^ 2).eval t := by
    simp [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  rw [hc, hP]

theorem exists_additive_curve_of_good_root (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (hk : ringChar k ≠ 2) (a : Fin τ.rank → kˣ) {n : ModGL τ k}
    (hn : n ∈ monomialSubgroup τ k) (hn2 : n ^ 2 = 1)
    (hna : rootDiagUnit τ a * n = n * rootDiagUnit τ a) {α : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (hαa : rootChar a α = 1) (hαinv : weylQuotientHom τ k ⟨n, hn⟩ • α ≠ -α)
    (hgood : ¬ (weylQuotientHom τ k ⟨n, hn⟩ • α = α ∧
      ∀ c : k, n * pinnedX τ k α c * n⁻¹ = pinnedX τ k α (-c))) :
    ∃ c : k → ModGL τ k, IsPolynomialCurve c ∧ c 0 = 1 ∧ (∀ s t, c (s + t) = c s * c t) ∧
      (∃ t, c t ≠ 1) ∧
        ∀ t, c t ∈ adjointGroup τ k ∧ Commute (c t) (rootDiagUnit τ a) ∧ Commute (c t) n := by
  classical
  let w : WeylGroup τ := weylQuotientHom τ k ⟨n, hn⟩
  let β : Fin τ.rank → ℤ := w • α
  have hw2 : w * w = 1 := by
    change weylQuotientHom τ k ⟨n, hn⟩ * weylQuotientHom τ k ⟨n, hn⟩ = 1
    exact weylQuotientHom_mul_self hn hn2
  have hwβ : w • β = α := by
    change w • (w • α) = α
    rw [← mul_smul, hw2, one_smul]
  have hβroot : IsRoot τ β := by
    change IsRoot τ (w • α)
    exact IsRoot.smul hα w
  have hne' : α ≠ -β := by
    intro h
    apply hαinv
    rw [h, smul_neg, hwβ, h]
  have hsymm : ∀ i, τ.symmetrizer i i = 1 := by
    rcases hτ with rfl | rfl | rfl | rfl <;> intro i <;> simp [Tag.symmetrizer]
  obtain ⟨μ, hμ⟩ := monomial_conj_pinnedX hn hα
  obtain ⟨μβ, hμβ0⟩ := monomial_conj_pinnedX hn hβroot
  have hμβ : ∀ c : k, n * pinnedX τ k β c * n⁻¹ = pinnedX τ k α (μβ * c) := by
    intro c
    have h := hμβ0 c
    rwa [hwβ] at h
  have hμβμ : μβ * μ = 1 := monomial_mu_mul_eq_one hn hn2 hα hμ hμβ
  have hweyl : rootChar a β = rootChar a α := by
    change rootChar a (w • α) = rootChar a α
    exact rootChar_weyl_smul hn hna hα hμ
  have hβa : rootChar a β = 1 := by rw [hweyl, hαa]
  by_cases hG1 : β = α
  · have hwα : w • α = α := hG1
    have hμ2 : μ * μ = 1 :=
      monomial_mu_mul_eq_one hn hn2 hα hμ (by
        intro c
        change n * pinnedX τ k β c * n⁻¹ = pinnedX τ k α (μ * c)
        have h := hμ c
        rw [hwα] at h
        rw [hG1]
        exact h)
    have hgood' : ¬ ∀ c : k, n * pinnedX τ k α c * n⁻¹ = pinnedX τ k α (-c) := by
      intro hall
      exact hgood ⟨hwα, hall⟩
    have hμne : μ ≠ -1 := by
      intro hμneg
      apply hgood'
      intro c
      rw [hμ c, hwα, hμneg]
      congr 1
      norm_num
    have hμ1 : μ = 1 := by
      have hsq : (μ : k) ^ 2 = 1 := by
        rw [pow_two]
        exact congrArg (fun u : kˣ => (u : k)) hμ2
      rcases sq_eq_one_iff.1 hsq with h | h
      · exact Units.ext (by simpa using h)
      · exact absurd (Units.ext (by simpa using h)) hμne
    refine ⟨fun t => pinnedX τ k α t, ?_, ?_, ?_, ?_, ?_⟩
    · simpa using isPolynomialCurve_pinnedX (τ := τ) (k := k) α Polynomial.X
    · simp [pinnedX_zero]
    · intro s t
      exact pinnedX_add τ k α s t
    · refine ⟨1, ?_⟩
      intro h
      have h' : (1 : k) = 0 := pinnedX_injective τ k α (by simp [h, pinnedX_zero])
      exact one_ne_zero h'
    · intro t
      refine ⟨pinnedX_mem_adjointGroup α t, commute_rootDiagUnit_pinnedX hα hαa t, ?_⟩
      refine commute_of_conj_eq_self ?_
      rw [hμ t, hwα, hμ1]
      simp
  · by_cases hG2 : 0 ≤ CFSG.LieType.Steinberg.Adjoint.iform α β
    · have hne : α ≠ β := fun h => hG1 h.symm
      have hfacts := CFSG.SeitzReduction.classD4_not_isRoot_add hτ hα hβroot hG2
      have hcomm : ∀ a b : k, Commute (pinnedX τ k α a) (pinnedX τ k β b) := by
        intro a b
        exact (simply_laced_root_commutator_unit τ hτ hα hβroot hne hne').2 hfacts.1 k
          (pinnedX τ k α a) (mem_rootSubgroup.2 ⟨a, rfl⟩)
          (pinnedX τ k β b) (mem_rootSubgroup.2 ⟨b, rfl⟩)
      refine ⟨fun t => pinnedX τ k α t * pinnedX τ k β (μ * t), ?_, ?_, ?_, ?_, ?_⟩
      · have h1 : IsPolynomialCurve fun t : k => pinnedX τ k α t := by
          simpa using isPolynomialCurve_pinnedX (τ := τ) (k := k) α Polynomial.X
        exact h1.mul (isPolynomialCurve_pinnedX_mul β (μ : k))
      · simp [pinnedX_zero]
      · intro s t
        have hc : Commute (pinnedX τ k β (μ * s)) (pinnedX τ k α t) :=
          (hcomm t (μ * s)).symm
        calc pinnedX τ k α (s + t) * pinnedX τ k β (μ * (s + t))
            = pinnedX τ k α s * pinnedX τ k α t *
                (pinnedX τ k β (μ * s) * pinnedX τ k β (μ * t)) := by
              rw [pinnedX_add τ k α, show (μ : k) * (s + t) = μ * s + μ * t by ring,
                pinnedX_add τ k β]
          _ = pinnedX τ k α s * (pinnedX τ k α t * pinnedX τ k β (μ * s)) *
                pinnedX τ k β (μ * t) := by group
          _ = pinnedX τ k α s * (pinnedX τ k β (μ * s) * pinnedX τ k α t) *
                pinnedX τ k β (μ * t) := by rw [← hc.eq]
          _ = (pinnedX τ k α s * pinnedX τ k β (μ * s)) *
                (pinnedX τ k α t * pinnedX τ k β (μ * t)) := by group
      · let φ : (Fin τ.rank → ℤ) →+ ℤ :=
          { toFun := fun v => CFSG.LieType.Steinberg.Adjoint.iform v (α + β)
            map_zero' := by simp [CFSG.LieType.Steinberg.Adjoint.iform]
            map_add' := fun u v => CFSG.LieType.Steinberg.Adjoint.iform_add_left u v (α + β) }
        have hφα : 0 < φ α := by
          change 0 < CFSG.LieType.Steinberg.Adjoint.iform α (α + β)
          rw [CFSG.LieType.Steinberg.Adjoint.iform_add_right,
            CFSG.SeitzReduction.classD4_iform_self hτ hα]
          linarith
        have hφβ : 0 < φ β := by
          change 0 < CFSG.LieType.Steinberg.Adjoint.iform β (α + β)
          rw [CFSG.LieType.Steinberg.Adjoint.iform_add_right,
            CFSG.LieType.Steinberg.Adjoint.iform_comm β α,
            CFSG.SeitzReduction.classD4_iform_self hτ hβroot]
          linarith
        have hnt : pinnedX τ k α 1 * pinnedX τ k β (μ : k) ≠ 1 := by
          intro h1
          let c : (Fin τ.rank → ℤ) → k :=
            fun x => if x = α then 1 else if x = β then (μ : k) else 0
          have hcα : c α = 1 := by simp [c]
          have hcβ : c β = (μ : k) := by simp [c, hne.symm]
          have hL : ∀ x ∈ [α, β], IsRoot τ x ∧ 0 < φ x := by
            intro x hx
            rcases List.mem_cons.1 hx with rfl | hx
            · exact ⟨hα, hφα⟩
            rcases List.mem_cons.1 hx with rfl | hx
            · exact ⟨hβroot, hφβ⟩
            exact (List.not_mem_nil hx).elim
          have hlist : ([α, β].map fun γ => pinnedX τ k γ (c γ)).prod =
              pinnedX τ k α 1 * pinnedX τ k β (μ : k) := by
            simp [c, hne.symm]
          have heq : ([α, β].map fun γ => pinnedX τ k γ (c γ)).prod =
              ([α, β].map fun γ => pinnedX τ k γ ((fun _ => (0 : k)) γ)).prod := by
            rw [hlist, h1]
            simp [pinnedX_zero]
          have hinj := CFSG.LieType.SeitzGeneration.ExcHighThree.pinnedX_list_prod_injective_deg
            φ [α, β] (by simp [hne]) hL c (fun _ => 0) heq
          have hα0 := hinj α (by simp)
          rw [hcα] at hα0
          exact one_ne_zero hα0
        refine ⟨1, ?_⟩
        simpa using hnt
      · intro t
        refine ⟨mul_mem (pinnedX_mem_adjointGroup α t)
          (pinnedX_mem_adjointGroup β (μ * t)), ?_, ?_⟩
        · exact (commute_rootDiagUnit_pinnedX hα hαa t).mul_left
            (commute_rootDiagUnit_pinnedX hβroot hβa (μ * t))
        · refine commute_of_conj_eq_self ?_
          have hμμ : (μβ : k) * (μ : k) = 1 := by
            rw [← Units.val_mul, hμβμ, Units.val_one]
          calc n * (pinnedX τ k α t * pinnedX τ k β (μ * t)) * n⁻¹
              = (n * pinnedX τ k α t * n⁻¹) *
                  (n * pinnedX τ k β (μ * t) * n⁻¹) := by group
            _ = pinnedX τ k β (μ * t) * pinnedX τ k α (μβ * (μ * t)) := by
                rw [hμ t, hμβ]
            _ = pinnedX τ k β (μ * t) * pinnedX τ k α t := by
                congr 1
                rw [← mul_assoc, hμμ, one_mul]
            _ = pinnedX τ k α t * pinnedX τ k β (μ * t) := (hcomm t (μ * t)).symm.eq
    · have hne : α ≠ β := fun h => hG1 h.symm
      have hm : CFSG.LieType.Steinberg.Adjoint.iform α β = -1 := by
        rcases CFSG.LieType.Chevalley.SimplyLacedCover.iform_mem hsymm hα hβroot hne hne' with
          h | h | h
        · exact h
        · exfalso
          apply hG2
          rw [h]
        · exfalso
          apply hG2
          rw [h]
          norm_num
      have hγroot : IsRoot τ (α + β) :=
        (CFSG.SeitzReduction.classD4_isRoot_add hτ hα hβroot hm).1
      have hformαγ : CFSG.LieType.Steinberg.Adjoint.iform α (α + β) = 1 := by
        rw [CFSG.LieType.Steinberg.Adjoint.iform_add_right,
          CFSG.SeitzReduction.classD4_iform_self hτ hα, hm]
        norm_num
      have hformβγ : CFSG.LieType.Steinberg.Adjoint.iform β (α + β) = 1 := by
        rw [CFSG.LieType.Steinberg.Adjoint.iform_add_right,
          CFSG.LieType.Steinberg.Adjoint.iform_comm β α,
          CFSG.SeitzReduction.classD4_iform_self hτ hβroot, hm]
        norm_num
      have hαγ : α ≠ α + β := by
        intro h
        have hzero : β = 0 := by
          have h1 := congrArg (fun v : Fin τ.rank → ℤ => v - α) h
          rw [add_sub_cancel_left, sub_self] at h1
          exact h1.symm
        exact hβroot.ne_zero hzero
      have hβγ : β ≠ α + β := by
        intro h
        have hzero : α = 0 := by
          have h1 := congrArg (fun v : Fin τ.rank → ℤ => v - β) h
          rw [add_sub_cancel_right, sub_self] at h1
          exact h1.symm
        exact hα.ne_zero hzero
      have hfactsαγ := CFSG.SeitzReduction.classD4_not_isRoot_add hτ hα hγroot
        (by rw [hformαγ]; norm_num)
      have hcommαγ : ∀ a b : k, Commute (pinnedX τ k α a) (pinnedX τ k (α + β) b) := by
        intro a b
        exact (simply_laced_root_commutator_unit τ hτ hα hγroot hαγ hfactsαγ.2).2
          hfactsαγ.1 k (pinnedX τ k α a) (mem_rootSubgroup.2 ⟨a, rfl⟩)
          (pinnedX τ k (α + β) b) (mem_rootSubgroup.2 ⟨b, rfl⟩)
      have hfactsβγ := CFSG.SeitzReduction.classD4_not_isRoot_add hτ hβroot hγroot
        (by rw [hformβγ]; norm_num)
      have hcommβγ : ∀ a b : k, Commute (pinnedX τ k β a) (pinnedX τ k (α + β) b) := by
        intro a b
        exact (simply_laced_root_commutator_unit τ hτ hβroot hγroot hβγ hfactsβγ.2).2
          hfactsβγ.1 k (pinnedX τ k β a) (mem_rootSubgroup.2 ⟨a, rfl⟩)
          (pinnedX τ k (α + β) b) (mem_rootSubgroup.2 ⟨b, rfl⟩)
      obtain ⟨hCunit, hcommAB⟩ :=
        (simply_laced_root_commutator_unit τ hτ hα hβroot hne hne').1 hγroot
      let Cc : k := ((commConst τ α β (1, 1) : ℤ) : k)
      have hC0 : Cc ≠ 0 := by
        change ((commConst τ α β (1, 1) : ℤ) : k) ≠ 0
        rcases hCunit with h | h <;> rw [h] <;> norm_num
      have hCrev : ∀ a b : k,
          (commutatorElement (G := ModGL τ k)).bracket (pinnedX τ k β a)
            (pinnedX τ k α b) =
          pinnedX τ k (α + β) (-(Cc * a * b)) := by
        intro a b
        have h := hcommAB k b a
        calc (commutatorElement (G := ModGL τ k)).bracket (pinnedX τ k β a) (pinnedX τ k α b)
            = ((commutatorElement (G := ModGL τ k)).bracket (pinnedX τ k α b)
                (pinnedX τ k β a))⁻¹ := by
                rw [commutatorElement_def, commutatorElement_def]
                group
          _ = (pinnedX τ k (α + β) ((commConst τ α β (1, 1) : ℤ) * b * a))⁻¹ := by
                rw [h]
          _ = pinnedX τ k (α + β) (-(Cc * b * a)) := by
                rw [pinnedX_neg]
          _ = pinnedX τ k (α + β) (-(Cc * a * b)) := by
                congr 1
                ring
      let lam : k := -(Cc * (μ : k)) / 2
      have h2 : (2 : k) ≠ 0 := Ring.two_ne_zero hk
      have hlam : 2 * lam = -(Cc * (μ : k)) := by
        change 2 * (-(Cc * (μ : k)) / 2) = -(Cc * (μ : k))
        field_simp
      obtain ⟨μγ, hμγ0⟩ := monomial_conj_pinnedX hn hγroot
      have hwγ : w • (α + β) = α + β := by
        rw [smul_add]
        have hwα : w • α = β := rfl
        rw [hwα, hwβ, add_comm]
      have hμγ : ∀ c : k, n * pinnedX τ k (α + β) c * n⁻¹ =
          pinnedX τ k (α + β) (μγ * c) := by
        intro c
        have h := hμγ0 c
        rwa [hwγ] at h
      have hμγneg : μγ = -1 := by
        have hμ1 : n * pinnedX τ k α 1 * n⁻¹ = pinnedX τ k β (μ : k) := by
          simpa using hμ 1
        have hμβ1 : n * pinnedX τ k β 1 * n⁻¹ = pinnedX τ k α (μβ : k) := by
          simpa using hμβ 1
        have hμm1 : n * (pinnedX τ k α 1)⁻¹ * n⁻¹ = (pinnedX τ k β (μ : k))⁻¹ := by
          calc n * (pinnedX τ k α 1)⁻¹ * n⁻¹ = (n * pinnedX τ k α 1 * n⁻¹)⁻¹ := by group
            _ = (pinnedX τ k β (μ : k))⁻¹ := by rw [hμ1]
        have hμβm1 : n * (pinnedX τ k β 1)⁻¹ * n⁻¹ = (pinnedX τ k α (μβ : k))⁻¹ := by
          calc n * (pinnedX τ k β 1)⁻¹ * n⁻¹ = (n * pinnedX τ k β 1 * n⁻¹)⁻¹ := by group
            _ = (pinnedX τ k α (μβ : k))⁻¹ := by rw [hμβ1]
        have hL : n * (commutatorElement (G := ModGL τ k)).bracket
              (pinnedX τ k α 1) (pinnedX τ k β 1) * n⁻¹ =
            (commutatorElement (G := ModGL τ k)).bracket
              (pinnedX τ k β (μ : k)) (pinnedX τ k α (μβ : k)) := by
          rw [commutatorElement_def, commutatorElement_def]
          calc n * (pinnedX τ k α 1 * pinnedX τ k β 1 * (pinnedX τ k α 1)⁻¹ *
                (pinnedX τ k β 1)⁻¹) * n⁻¹
              = (n * pinnedX τ k α 1 * n⁻¹) * (n * pinnedX τ k β 1 * n⁻¹) *
                  (n * (pinnedX τ k α 1)⁻¹ * n⁻¹) *
                  (n * (pinnedX τ k β 1)⁻¹ * n⁻¹) := by group
            _ = pinnedX τ k β (μ : k) * pinnedX τ k α (μβ : k) *
                  (pinnedX τ k β (μ : k))⁻¹ * (pinnedX τ k α (μβ : k))⁻¹ := by
                rw [hμ1, hμβ1, hμm1, hμβm1]
        have hEq : (commutatorElement (G := ModGL τ k)).bracket
              (pinnedX τ k β (μ : k)) (pinnedX τ k α (μβ : k)) =
            pinnedX τ k (α + β) ((μγ : k) * (Cc * 1 * 1)) := by
          calc (commutatorElement (G := ModGL τ k)).bracket
                (pinnedX τ k β (μ : k)) (pinnedX τ k α (μβ : k))
              = n * (commutatorElement (G := ModGL τ k)).bracket
                  (pinnedX τ k α 1) (pinnedX τ k β 1) * n⁻¹ :=
                  hL.symm
            _ = n * pinnedX τ k (α + β) (Cc * 1 * 1) * n⁻¹ := by
                rw [hcommAB k 1 1]
            _ = pinnedX τ k (α + β) ((μγ : k) * (Cc * 1 * 1)) := by
                simpa using hμγ (Cc * 1 * 1)
        have hval := pinnedX_injective τ k (α + β)
          (hEq.symm.trans (hCrev (μ : k) (μβ : k)))
        rw [mul_one, mul_one] at hval
        have hμμ : (μβ : k) * (μ : k) = 1 := by
          rw [← Units.val_mul, hμβμ, Units.val_one]
        have hCc : (μγ : k) * Cc = -Cc := by
          rw [mul_assoc, show (μ : k) * (μβ : k) = 1 by rw [mul_comm, hμμ], mul_one] at hval
          exact hval
        have hval1 : (μγ : k) = -1 := by
          have h' : (μγ : k) * Cc = (-1 : k) * Cc := by
            rw [neg_one_mul]
            exact hCc
          exact mul_right_cancel₀ hC0 h'
        exact Units.ext hval1
      have hγa : rootChar a (α + β) = 1 := by
        rw [rootChar_add, hαa, hβa, one_mul]
      have hCommαγ : ∀ a b : k, Commute (pinnedX τ k (α + β) a) (pinnedX τ k α b) :=
        fun a b => (hcommαγ b a).symm
      have hCommβγ : ∀ a b : k, Commute (pinnedX τ k (α + β) a) (pinnedX τ k β b) :=
        fun a b => (hcommβγ b a).symm
      have hCommαγ_eq : ∀ x y : k, pinnedX τ k (α + β) x * pinnedX τ k α y =
          pinnedX τ k α y * pinnedX τ k (α + β) x :=
        fun x y => (hCommαγ x y).eq
      have hCommβγ_eq : ∀ x y : k, pinnedX τ k (α + β) x * pinnedX τ k β y =
          pinnedX τ k β y * pinnedX τ k (α + β) x :=
        fun x y => (hCommβγ x y).eq
      have hAB : ∀ s t : k, pinnedX τ k β (μ * s) * pinnedX τ k α t =
          pinnedX τ k (α + β) (-(Cc * (μ : k) * s * t)) * pinnedX τ k α t *
            pinnedX τ k β (μ * s) := by
        intro s t
        have h := hCrev (μ * s) t
        rw [commutatorElement_def] at h
        calc pinnedX τ k β (μ * s) * pinnedX τ k α t
            = (pinnedX τ k β (μ * s) * pinnedX τ k α t * (pinnedX τ k β (μ * s))⁻¹ *
                (pinnedX τ k α t)⁻¹) * (pinnedX τ k α t * pinnedX τ k β (μ * s)) := by
                group
          _ = pinnedX τ k (α + β) (-(Cc * (μ * s) * t)) *
                (pinnedX τ k α t * pinnedX τ k β (μ * s)) := by rw [h]
          _ = pinnedX τ k (α + β) (-(Cc * (μ : k) * s * t)) * pinnedX τ k α t *
                pinnedX τ k β (μ * s) := by
                rw [show -(Cc * ((μ : k) * s) * t) = -(Cc * (μ : k) * s * t) by ring]
                group
      have hpoly : IsPolynomialCurve fun t : k =>
          pinnedX τ k α t * pinnedX τ k β (μ * t) *
            pinnedX τ k (α + β) (lam * t ^ 2) := by
        have h1 : IsPolynomialCurve fun t : k => pinnedX τ k α t := by
          simpa using isPolynomialCurve_pinnedX (τ := τ) (k := k) α Polynomial.X
        exact (h1.mul (isPolynomialCurve_pinnedX_mul β (μ : k))).mul
          (isPolynomialCurve_pinnedX_mul_sq (α + β) lam)
      have hzero : pinnedX τ k α 0 * pinnedX τ k β (μ * 0) *
          pinnedX τ k (α + β) (lam * 0 ^ 2) = 1 := by
        simp [pinnedX_zero]
      have hadd : ∀ s t : k,
          pinnedX τ k α (s + t) * pinnedX τ k β (μ * (s + t)) *
            pinnedX τ k (α + β) (lam * (s + t) ^ 2) =
          (pinnedX τ k α s * pinnedX τ k β (μ * s) *
            pinnedX τ k (α + β) (lam * s ^ 2)) *
          (pinnedX τ k α t * pinnedX τ k β (μ * t) *
            pinnedX τ k (α + β) (lam * t ^ 2)) := by
        intro s t
        have hz : -(Cc * (μ : k) * s * t) + (lam * s ^ 2 + lam * t ^ 2) =
            lam * (s + t) ^ 2 := by
          linear_combination -(s * t) * hlam
        apply Eq.symm
        calc (pinnedX τ k α s * pinnedX τ k β (μ * s) *
              pinnedX τ k (α + β) (lam * s ^ 2)) *
              (pinnedX τ k α t * pinnedX τ k β (μ * t) *
                pinnedX τ k (α + β) (lam * t ^ 2))
            = pinnedX τ k α s * pinnedX τ k β (μ * s) *
                (pinnedX τ k (α + β) (lam * s ^ 2) * pinnedX τ k α t) *
                pinnedX τ k β (μ * t) * pinnedX τ k (α + β) (lam * t ^ 2) := by
              group
          _ = pinnedX τ k α s * pinnedX τ k β (μ * s) *
                (pinnedX τ k α t * pinnedX τ k (α + β) (lam * s ^ 2)) *
                pinnedX τ k β (μ * t) * pinnedX τ k (α + β) (lam * t ^ 2) := by
              rw [hCommαγ_eq (lam * s ^ 2) t]
          _ = pinnedX τ k α s * pinnedX τ k β (μ * s) * pinnedX τ k α t *
                (pinnedX τ k (α + β) (lam * s ^ 2) * pinnedX τ k β (μ * t)) *
                pinnedX τ k (α + β) (lam * t ^ 2) := by
              group
          _ = pinnedX τ k α s * pinnedX τ k β (μ * s) * pinnedX τ k α t *
                (pinnedX τ k β (μ * t) * pinnedX τ k (α + β) (lam * s ^ 2)) *
                pinnedX τ k (α + β) (lam * t ^ 2) := by
              rw [hCommβγ_eq (lam * s ^ 2) (μ * t)]
          _ = pinnedX τ k α s * pinnedX τ k β (μ * s) * pinnedX τ k α t *
                pinnedX τ k β (μ * t) *
                (pinnedX τ k (α + β) (lam * s ^ 2) *
                  pinnedX τ k (α + β) (lam * t ^ 2)) := by
              group
          _ = pinnedX τ k α s * pinnedX τ k β (μ * s) * pinnedX τ k α t *
                pinnedX τ k β (μ * t) *
                pinnedX τ k (α + β) (lam * s ^ 2 + lam * t ^ 2) := by
              rw [← pinnedX_add τ k (α + β)]
          _ = pinnedX τ k α s * (pinnedX τ k β (μ * s) * pinnedX τ k α t) *
                pinnedX τ k β (μ * t) *
                pinnedX τ k (α + β) (lam * s ^ 2 + lam * t ^ 2) := by
              group
          _ = pinnedX τ k α s *
                (pinnedX τ k (α + β) (-(Cc * (μ : k) * s * t)) * pinnedX τ k α t *
                  pinnedX τ k β (μ * s)) * pinnedX τ k β (μ * t) *
                pinnedX τ k (α + β) (lam * s ^ 2 + lam * t ^ 2) := by
              rw [hAB]
          _ = pinnedX τ k α s * pinnedX τ k (α + β) (-(Cc * (μ : k) * s * t)) *
                pinnedX τ k α t * pinnedX τ k β (μ * s) * pinnedX τ k β (μ * t) *
                pinnedX τ k (α + β) (lam * s ^ 2 + lam * t ^ 2) := by
              group
          _ = (pinnedX τ k (α + β) (-(Cc * (μ : k) * s * t)) * pinnedX τ k α s) *
                pinnedX τ k α t * pinnedX τ k β (μ * s) * pinnedX τ k β (μ * t) *
                pinnedX τ k (α + β) (lam * s ^ 2 + lam * t ^ 2) := by
              rw [← hCommαγ_eq (-(Cc * (μ : k) * s * t)) s]
          _ = pinnedX τ k (α + β) (-(Cc * (μ : k) * s * t)) *
                (pinnedX τ k α s * pinnedX τ k α t) * pinnedX τ k β (μ * s) *
                pinnedX τ k β (μ * t) *
                pinnedX τ k (α + β) (lam * s ^ 2 + lam * t ^ 2) := by
              group
          _ = pinnedX τ k (α + β) (-(Cc * (μ : k) * s * t)) *
                pinnedX τ k α (s + t) * pinnedX τ k β (μ * s) *
                pinnedX τ k β (μ * t) *
                pinnedX τ k (α + β) (lam * s ^ 2 + lam * t ^ 2) := by
              rw [← pinnedX_add τ k α]
          _ = pinnedX τ k (α + β) (-(Cc * (μ : k) * s * t)) *
                pinnedX τ k α (s + t) *
                (pinnedX τ k β (μ * s) * pinnedX τ k β (μ * t)) *
                pinnedX τ k (α + β) (lam * s ^ 2 + lam * t ^ 2) := by
              group
          _ = pinnedX τ k (α + β) (-(Cc * (μ : k) * s * t)) *
                pinnedX τ k α (s + t) * pinnedX τ k β (μ * (s + t)) *
                pinnedX τ k (α + β) (lam * s ^ 2 + lam * t ^ 2) := by
              rw [← pinnedX_add τ k β, show (μ : k) * s + μ * t = μ * (s + t) by ring]
          _ = pinnedX τ k α (s + t) *
                (pinnedX τ k (α + β) (-(Cc * (μ : k) * s * t)) *
                  pinnedX τ k β (μ * (s + t))) *
                pinnedX τ k (α + β) (lam * s ^ 2 + lam * t ^ 2) := by
              rw [hCommαγ_eq (-(Cc * (μ : k) * s * t)) (s + t)]
              group
          _ = pinnedX τ k α (s + t) *
                (pinnedX τ k β (μ * (s + t)) *
                  pinnedX τ k (α + β) (-(Cc * (μ : k) * s * t))) *
                pinnedX τ k (α + β) (lam * s ^ 2 + lam * t ^ 2) := by
              rw [hCommβγ_eq (-(Cc * (μ : k) * s * t)) (μ * (s + t))]
          _ = pinnedX τ k α (s + t) * pinnedX τ k β (μ * (s + t)) *
                (pinnedX τ k (α + β) (-(Cc * (μ : k) * s * t)) *
                  pinnedX τ k (α + β) (lam * s ^ 2 + lam * t ^ 2)) := by
              group
          _ = pinnedX τ k α (s + t) * pinnedX τ k β (μ * (s + t)) *
                pinnedX τ k (α + β) (-(Cc * (μ : k) * s * t) +
                  (lam * s ^ 2 + lam * t ^ 2)) := by
              rw [← pinnedX_add τ k (α + β)]
          _ = pinnedX τ k α (s + t) * pinnedX τ k β (μ * (s + t)) *
                pinnedX τ k (α + β) (lam * (s + t) ^ 2) := by rw [hz]
      have hnt : pinnedX τ k α 1 * pinnedX τ k β (μ : k) *
          pinnedX τ k (α + β) lam ≠ 1 := by
        intro h1
        let φ : (Fin τ.rank → ℤ) →+ ℤ :=
          { toFun := fun v => CFSG.LieType.Steinberg.Adjoint.iform v (α + β)
            map_zero' := by simp [CFSG.LieType.Steinberg.Adjoint.iform]
            map_add' := fun u v => CFSG.LieType.Steinberg.Adjoint.iform_add_left u v (α + β) }
        have hφα : 0 < φ α := by
          change 0 < CFSG.LieType.Steinberg.Adjoint.iform α (α + β)
          rw [hformαγ]
          norm_num
        have hφβ : 0 < φ β := by
          change 0 < CFSG.LieType.Steinberg.Adjoint.iform β (α + β)
          rw [hformβγ]
          norm_num
        have hφγ : 0 < φ (α + β) := by
          change 0 < CFSG.LieType.Steinberg.Adjoint.iform (α + β) (α + β)
          rw [CFSG.SeitzReduction.classD4_iform_self hτ hγroot]
          norm_num
        let c : (Fin τ.rank → ℤ) → k := fun x =>
          if x = α then 1 else if x = β then (μ : k) else
            if x = α + β then lam else 0
        have hcα : c α = 1 := by simp [c]
        have hcβ : c β = (μ : k) := by simp [c, hne.symm]
        have hcγ : c (α + β) = lam := by
          simp only [c]
          rw [if_neg (Ne.symm hαγ), if_neg (Ne.symm hβγ)]
          simp
        have hL : ∀ x ∈ [α, β, α + β], IsRoot τ x ∧ 0 < φ x := by
          intro x hx
          rcases List.mem_cons.1 hx with rfl | hx
          · exact ⟨hα, hφα⟩
          rcases List.mem_cons.1 hx with rfl | hx
          · exact ⟨hβroot, hφβ⟩
          rcases List.mem_cons.1 hx with rfl | hx
          · exact ⟨hγroot, hφγ⟩
          exact (List.not_mem_nil hx).elim
        have hlist : ([α, β, α + β].map fun γ => pinnedX τ k γ (c γ)).prod =
            pinnedX τ k α 1 * pinnedX τ k β (μ : k) * pinnedX τ k (α + β) lam := by
          change pinnedX τ k α (c α) * pinnedX τ k β (c β) *
            pinnedX τ k (α + β) (c (α + β)) = _
          rw [hcα, hcβ, hcγ]
        have heq : ([α, β, α + β].map fun γ => pinnedX τ k γ (c γ)).prod =
            ([α, β, α + β].map fun γ => pinnedX τ k γ ((fun _ => (0 : k)) γ)).prod := by
          rw [hlist, h1]
          simp [pinnedX_zero]
        have hinj := CFSG.LieType.SeitzGeneration.ExcHighThree.pinnedX_list_prod_injective_deg
          φ [α, β, α + β] (by simp [hne, hαγ, hβγ]) hL c (fun _ => 0) heq
        have hα0 := hinj α (by simp)
        rw [hcα] at hα0
        exact one_ne_zero hα0
      refine ⟨fun t : k => pinnedX τ k α t * pinnedX τ k β (μ * t) *
          pinnedX τ k (α + β) (lam * t ^ 2), hpoly, hzero, hadd, ?_, ?_⟩
      · refine ⟨1, ?_⟩
        simpa using hnt
      · intro t
        refine ⟨mul_mem (mul_mem (pinnedX_mem_adjointGroup α t)
          (pinnedX_mem_adjointGroup β (μ * t)))
          (pinnedX_mem_adjointGroup (α + β) (lam * t ^ 2)), ?_, ?_⟩
        · exact ((commute_rootDiagUnit_pinnedX hα hαa t).mul_left
            (commute_rootDiagUnit_pinnedX hβroot hβa (μ * t))).mul_left
            (commute_rootDiagUnit_pinnedX hγroot hγa (lam * t ^ 2))
        · refine commute_of_conj_eq_self ?_
          have hμμ : (μβ : k) * (μ : k) = 1 := by
            rw [← Units.val_mul, hμβμ, Units.val_one]
          have hαpar : (μβ : k) * ((μ : k) * t) = t := by
            rw [← mul_assoc, hμμ, one_mul]
          have hγpar : (μγ : k) * (lam * t ^ 2) = -(lam * t ^ 2) := by
            rw [hμγneg]
            norm_num
          have hγpar' : -(Cc * (μ : k) * t * t) + -(lam * t ^ 2) = lam * t ^ 2 := by
            linear_combination -(t ^ 2) * hlam
          calc n * (pinnedX τ k α t * pinnedX τ k β (μ * t) *
                pinnedX τ k (α + β) (lam * t ^ 2)) * n⁻¹
              = (n * pinnedX τ k α t * n⁻¹) * (n * pinnedX τ k β (μ * t) * n⁻¹) *
                  (n * pinnedX τ k (α + β) (lam * t ^ 2) * n⁻¹) := by group
            _ = pinnedX τ k β (μ * t) * pinnedX τ k α (μβ * (μ * t)) *
                  pinnedX τ k (α + β) (μγ * (lam * t ^ 2)) := by
                rw [hμ t, hμβ, hμγ]
            _ = pinnedX τ k β (μ * t) * pinnedX τ k α t *
                  pinnedX τ k (α + β) (-(lam * t ^ 2)) := by
                rw [hαpar, hγpar]
            _ = pinnedX τ k α t * pinnedX τ k β (μ * t) *
                  pinnedX τ k (α + β) (lam * t ^ 2) := by
                calc pinnedX τ k β (μ * t) * pinnedX τ k α t *
                      pinnedX τ k (α + β) (-(lam * t ^ 2))
                    = (pinnedX τ k (α + β) (-(Cc * (μ : k) * t * t)) *
                        pinnedX τ k α t * pinnedX τ k β (μ * t)) *
                        pinnedX τ k (α + β) (-(lam * t ^ 2)) := by
                        rw [hAB t t]
                    _ = pinnedX τ k α t * (pinnedX τ k (α + β) (-(Cc * (μ : k) * t * t)) *
                        pinnedX τ k β (μ * t)) *
                        pinnedX τ k (α + β) (-(lam * t ^ 2)) := by
                        rw [(hCommαγ (-(Cc * (μ : k) * t * t)) t).eq]
                        group
                    _ = pinnedX τ k α t * (pinnedX τ k β (μ * t) *
                        pinnedX τ k (α + β) (-(Cc * (μ : k) * t * t))) *
                        pinnedX τ k (α + β) (-(lam * t ^ 2)) := by
                        rw [(hCommβγ (-(Cc * (μ : k) * t * t)) (μ * t)).eq]
                    _ = pinnedX τ k α t * pinnedX τ k β (μ * t) *
                        (pinnedX τ k (α + β) (-(Cc * (μ : k) * t * t)) *
                          pinnedX τ k (α + β) (-(lam * t ^ 2))) := by group
                    _ = pinnedX τ k α t * pinnedX τ k β (μ * t) *
                        pinnedX τ k (α + β) (-(Cc * (μ : k) * t * t) + -(lam * t ^ 2)) := by
                        rw [pinnedX_add τ k (α + β)]
                    _ = pinnedX τ k α t * pinnedX τ k β (μ * t) *
                        pinnedX τ k (α + β) (lam * t ^ 2) := by rw [hγpar']

end CFSG.LieType.AlgebraicGroups
