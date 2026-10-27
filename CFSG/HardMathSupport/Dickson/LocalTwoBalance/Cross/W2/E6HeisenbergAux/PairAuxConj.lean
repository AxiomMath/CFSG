module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeBlock

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.E6Heis.PairAux

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.CrossChar

theorem closure_pair_commute {G : Type*} [Group G] {X Y : G} (hXY : X * Y = Y * X) :
    ∀ g ∈ Subgroup.closure ({X, Y} : Set G), ∀ h ∈ Subgroup.closure ({X, Y} : Set G),
      g * h = h * g := by
  have hpair : ({X, Y} : Set G).Pairwise Commute := by
    intro p hp q hq _
    rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
    · exact Commute.refl _
    · exact hXY
    · exact hXY.symm
    · exact Commute.refl _
  intro g hg h hh
  exact Set.centralizer_centralizer_comm_of_comm hpair _
    (Subgroup.closure_le_centralizer_centralizer _ hg) _
    (Subgroup.closure_le_centralizer_centralizer _ hh)

theorem closure_pair_pow_eq_one {G : Type*} [Group G] {X Y : G} (hXY : X * Y = Y * X) {n : ℕ}
    (hX : X ^ n = 1) (hY : Y ^ n = 1) :
    ∀ g ∈ Subgroup.closure ({X, Y} : Set G), g ^ n = 1 := by
  have hc := closure_pair_commute hXY
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact hX
    · exact hY
  | one => exact one_pow n
  | mul x y hx hy ihx ihy =>
    have hxy : Commute x y := hc x hx y hy
    rw [hxy.mul_pow, ihx, ihy, one_mul]
  | inv x hx ihx => rw [inv_pow, ihx, inv_one]

theorem exists_conj_pair_normal_form_bar {K : Type} [Field K] [Finite K] (h3 : ¬ 3 ∣ Nat.card K)
    {A : Subgroup (ModGL Tag.E6 (AlgebraicClosure K))}
    (hA : A ≤ adjointGroup Tag.E6 (AlgebraicClosure K))
    (hAfin : (A : Set (ModGL Tag.E6 (AlgebraicClosure K))).Finite)
    (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hexp : ∀ x ∈ A, x ^ 3 = 1)
    {x₀ y₀ : ModGL Tag.E6 (AlgebraicClosure K)} (hx₀A : x₀ ∈ A) (hy₀A : y₀ ∈ A) :
    ∃ c ∈ adjointGroup Tag.E6 (AlgebraicClosure K),
      ∃ (a b : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ) (w : WeylGroup Tag.E6),
        (∀ i, a i ^ 3 = 1) ∧ w ∈ rootCharStabilizer a ∧
        c * x₀ * c⁻¹ = rootDiagUnit Tag.E6 a ∧
        c * y₀ * c⁻¹ =
          rootDiagUnit Tag.E6 b * canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) w := by
  classical
  have hp : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ℓ, hℓK⟩ := CharP.exists K
  have hℓp : ℓ.Prime := CharP.char_is_prime K ℓ
  have : Fact ℓ.Prime := ⟨hℓp⟩
  have : CharP (AlgebraicClosure K) ℓ :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective ℓ
  have hℓ : ℓ ≠ 3 := by
    rintro rfl
    have : Fintype K := Fintype.ofFinite K
    obtain ⟨n, -, hn⟩ := FiniteField.card K 3
    apply h3
    rw [Nat.card_eq_fintype_card, hn]
    exact dvd_pow_self 3 n.ne_zero
  have halg := isAlgebraic_zmod_algebraicClosure_of_finite K ℓ
  have hLp : ringChar (AlgebraicClosure K) ≠ 3 := by
    rw [ringChar.eq (AlgebraicClosure K) ℓ]
    exact hℓ
  have hmon := monomialToralAt_E6_three
  obtain ⟨c₁, hc₁, hc₁N⟩ := exists_conj_le_monomial_bar hℓ halg hA hAfin hexp
  obtain ⟨g, hg, hgn⟩ := exists_conj_mem_torusGroup_of_mem_monomial hmon hLp (hc₁N x₀ hx₀A)
    (conj_pow_eq_one' c₁ (hexp x₀ hx₀A))
  obtain ⟨c, hcdef⟩ : ∃ c, c = g * c₁ := ⟨_, rfl⟩
  have hcC : c ∈ adjointGroup Tag.E6 (AlgebraicClosure K) := hcdef ▸ mul_mem hg hc₁
  obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hgn
  have hda : c * x₀ * c⁻¹ = rootDiagUnit Tag.E6 a := by
    rw [← ha, hcdef]
    group
  have hap : ∀ i, a i ^ 3 = 1 := by
    have h : rootDiagUnit Tag.E6 (a ^ 3) = rootDiagUnit Tag.E6 1 := by
      rw [rootDiagUnit_pow', rootDiagUnit_one, ← hda, conj_pow_eq_one' c (hexp x₀ hx₀A)]
    intro i
    have := congrFun (CFSG.LieType.Chevalley.rootDiagUnit_injective h) i
    simpa using this
  obtain ⟨A', hA'⟩ : ∃ A' : Subgroup (ModGL Tag.E6 (AlgebraicClosure K)),
      A' = A.map (MulAut.conj c).toMonoidHom := ⟨_, rfl⟩
  have hA'mem : ∀ x ∈ A, c * x * c⁻¹ ∈ A' := fun x hx => hA' ▸ ⟨x, hx, rfl⟩
  have hA'C : A' ≤ adjointGroup Tag.E6 (AlgebraicClosure K) := by
    rw [hA']
    rintro _ ⟨x, hx, rfl⟩
    exact mul_mem (mul_mem hcC (hA hx)) (inv_mem hcC)
  have hA'fin : (A' : Set (ModGL Tag.E6 (AlgebraicClosure K))).Finite := by
    rw [hA']
    exact Set.Finite.image _ hAfin
  have hA'a : ∀ y ∈ A', rootDiagUnit Tag.E6 a * y = y * rootDiagUnit Tag.E6 a := by
    rw [hA']
    rintro _ ⟨x, hx, rfl⟩
    change rootDiagUnit Tag.E6 a * (c * x * c⁻¹) = c * x * c⁻¹ * rootDiagUnit Tag.E6 a
    rw [← hda]
    calc c * x₀ * c⁻¹ * (c * x * c⁻¹) = c * (x₀ * x) * c⁻¹ := by group
      _ = c * (x * x₀) * c⁻¹ := by rw [hcomm x₀ hx₀A x hx]
      _ = c * x * c⁻¹ * (c * x₀ * c⁻¹) := by group
  have hA'exp : ∀ y ∈ A', y ^ 3 = 1 := by
    rw [hA']
    rintro _ ⟨x, hx, rfl⟩
    exact conj_pow_eq_one' c (hexp x hx)
  obtain ⟨z, hz, hzd, hzN⟩ := exists_conj_le_monomial_centralizer_bar hℓ halg a hA'C hA'fin hA'a
    hA'exp
  obtain ⟨n', hn'⟩ : ∃ n, n = z * (c * y₀ * c⁻¹) * z⁻¹ := ⟨_, rfl⟩
  have hn'N : n' ∈ monomialSubgroup Tag.E6 (AlgebraicClosure K) := hn' ▸ hzN _ (hA'mem y₀ hy₀A)
  have hn'a : rootDiagUnit Tag.E6 a * n' = n' * rootDiagUnit Tag.E6 a := by
    have h1 := hA'a _ (hA'mem y₀ hy₀A)
    have hzd' : rootDiagUnit Tag.E6 a * z⁻¹ = z⁻¹ * rootDiagUnit Tag.E6 a := by
      calc rootDiagUnit Tag.E6 a * z⁻¹ = z⁻¹ * (z * rootDiagUnit Tag.E6 a) * z⁻¹ := by group
        _ = z⁻¹ * (rootDiagUnit Tag.E6 a * z) * z⁻¹ := by rw [hzd]
        _ = z⁻¹ * rootDiagUnit Tag.E6 a := by group
    calc rootDiagUnit Tag.E6 a * n' = (rootDiagUnit Tag.E6 a * z) * (c * y₀ * c⁻¹) * z⁻¹ := by
          rw [hn']; group
      _ = z * (rootDiagUnit Tag.E6 a * (c * y₀ * c⁻¹)) * z⁻¹ := by rw [hzd]; group
      _ = z * (c * y₀ * c⁻¹) * (rootDiagUnit Tag.E6 a * z⁻¹) := by rw [h1]; group
      _ = n' * rootDiagUnit Tag.E6 a := by rw [hzd', hn']; group
  obtain ⟨w, k, hk, e⟩ := monomialSubgroup_le_torusWeylCosets hn'N
  obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hk
  have hw : w ∈ rootCharStabilizer a := by
    rw [← conj_canonicalRep_eq_iff]
    have hdk : rootDiagUnit Tag.E6 a * k = k * rootDiagUnit Tag.E6 a :=
      rootDiagUnit_mul_comm_of_mem_torusGroup a hk
    have hna : rootDiagUnit Tag.E6 a * (k * canonicalRep (coxeterSystem Tag.E6) _ w) =
        (k * canonicalRep (coxeterSystem Tag.E6) _ w) * rootDiagUnit Tag.E6 a := by
      rw [← e]
      exact hn'a
    have h1 : rootDiagUnit Tag.E6 a * canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) w =
        canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) w * rootDiagUnit Tag.E6 a := by
      have e1 : rootDiagUnit Tag.E6 a * canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) w =
          k⁻¹ * (rootDiagUnit Tag.E6 a *
            (k * canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) w)) := by
        rw [← mul_assoc (rootDiagUnit Tag.E6 a) k, hdk]
        group
      rw [e1, hna]
      group
    rw [h1, mul_inv_cancel_right]
  refine ⟨z * c, mul_mem hz hcC, a, b, w, hap, hw, ?_, ?_⟩
  · calc z * c * x₀ * (z * c)⁻¹ = z * (c * x₀ * c⁻¹) * z⁻¹ := by group
      _ = z * rootDiagUnit Tag.E6 a * z⁻¹ := by rw [hda]
      _ = rootDiagUnit Tag.E6 a := by rw [← hzd, mul_inv_cancel_right]
  · calc z * c * y₀ * (z * c)⁻¹ = n' := by rw [hn']; group
      _ = k * canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) w := e
      _ = rootDiagUnit Tag.E6 b * canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) w := by
          rw [hb]

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.E6Heis.PairAux
