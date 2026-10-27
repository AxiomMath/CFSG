module

public import CFSG.HardMathSupport.Dickson.Bal207.LocalBalClassicalOrthTwoLocal
public import CFSG.HardMathSupport.Dickson.Bal207.OrthEightLocal
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.D4TrialityAux.Basic
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.OrthQ2Main8

public section

namespace CFSG.HardMathSupport.Dickson.Bal207.OrthRow.Two

open Polynomial Module QuadraticMap CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.GroupTheory.WeirSylow CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.OrthogonalInvolutions
  CFSG.RankThree.Classical2 CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
  CFSG.LocalAnalysis.ComponentInitial CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.RankThree.PartOne.KCOrthogonalAut CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

section Projective

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem exists_lift_of_orderOf_eq_three (hK : Nat.card K = 2)
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) {a : ProjOrthDerived Q}
    (ha : orderOf a = 3) :
    ∃ x : orthDerived Q, OddOrderIsometry Q 3 (x : V ≃ₗ[K] V) ∧
      Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)) =
        centralizerImage Q (x : V ≃ₗ[K] V) := by
  obtain ⟨-, -, -, -, -, -, -, -, hlift⟩ :=
    CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hQ hT
  obtain ⟨x, ⟨hxa, hxp⟩, -, -⟩ := hlift 3 Nat.prime_three (by norm_num) a ha
  exact ⟨x, oddOrderIsometry_of_orthDerived Nat.prime_three
      (by rw [ringChar_eq_two_of_card hK]; norm_num) hQ x hxp,
    (orth3_conj_injective_and_centralizer hQ hT Nat.prime_three (by norm_num) a ha x hxa
      hxp).2⟩

theorem noNormalPPrime_centralizer_projOrthDerived (hK : Nat.card K = 2)
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    (hpar : IsPlusType Q ↔ Even (finrank K V / 2)) {a : ProjOrthDerived Q}
    (ha : orderOf a = 3) :
    NoNormalPPrime 3 (Subgroup.centralizer ({a} : Set (ProjOrthDerived Q))) := by
  have := charP_two hK
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K)
    (by have := OrthEight.three_le_finrank_of_singular hT; omega)
  obtain ⟨x, hx, hcent⟩ := exists_lift_of_orderOf_eq_three hK hQ hT ha
  have hinj : Function.Injective
      (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))) := piOrth_injective hQ
  rw [hcent, centralizerImage, W2.noNormalPPrime_map_iff _ hinj,
    ← W2.noNormalPPrime_map_iff _ (orthDerived Q).subtype_injective,
    Subgroup.subgroupOf_map_subtype]
  exact noNormalPPrime_isometryCentralizer_inf_orthDerived hK hx hQ hT hpar

theorem eq_one_of_conj_fixes_centralizer_projOrthDerived (hK : Nat.card K = 2)
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    (hpar : IsPlusType Q ↔ Even (finrank K V / 2)) {a : ProjOrthDerived Q}
    (ha : orderOf a = 3) {G : V ≃ₗ[K] V} (hG : G ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    {k : ℕ} (hk : Nat.Coprime 3 k) (hGk : G ^ k = 1)
    (hfix : ∀ y : orthDerived Q, (QuotientGroup.mk y : ProjOrthDerived Q) ∈
        Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)) →
      ∃ hy : G * (y : V ≃ₗ[K] V) * G⁻¹ ∈ orthDerived Q,
        (QuotientGroup.mk ⟨G * y * G⁻¹, hy⟩ : ProjOrthDerived Q) = QuotientGroup.mk y) :
    G = 1 := by
  have := charP_two hK
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K)
    (by have := OrthEight.three_le_finrank_of_singular hT; omega)
  obtain ⟨x, hx, hcent⟩ := exists_lift_of_orderOf_eq_three hK hQ hT ha
  have hinj : Function.Injective (piOrth Q) := piOrth_injective hQ
  refine eq_one_of_commute_isometryCentralizer_inf hK hx x.2 hQ hT hpar hG hk hGk fun f hf => ?_
  obtain ⟨hfM, hfΩ⟩ := Subgroup.mem_inf.mp hf
  have ht : (QuotientGroup.mk (⟨f, hfΩ⟩ : orthDerived Q) : ProjOrthDerived Q) ∈
      Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)) := by
    rw [hcent]
    exact ⟨⟨f, hfΩ⟩, Subgroup.mem_subgroupOf.mpr hfM, rfl⟩
  obtain ⟨hy, hGf⟩ := hfix ⟨f, hfΩ⟩ ht
  have h1 := @hinj ⟨G * f * G⁻¹, hy⟩ ⟨f, hfΩ⟩ hGf
  have h2 : G * f * G⁻¹ = f := congrArg Subtype.val h1
  calc G * f = G * f * G⁻¹ * G := by group
    _ = f * G := by rw [h2]

theorem eq_one_of_fixes_centralizer_projOrthDerived (hK : Nat.card K = 2)
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    (hpar : IsPlusType Q ↔ Even (finrank K V / 2)) {a : ProjOrthDerived Q}
    (ha : orderOf a = 3) {G : V ≃ₗ[K] V} (hG : G ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    {α : MulAut (ProjOrthDerived Q)}
    (hα : ∀ y : orthDerived Q, ∃ hy : G * (y : V ≃ₗ[K] V) * G⁻¹ ∈ orthDerived Q,
      α (QuotientGroup.mk y) = QuotientGroup.mk ⟨G * y * G⁻¹, hy⟩)
    (hco : Nat.Coprime 3 (orderOf α))
    (hfix : ∀ t ∈ Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)), α t = t) : α = 1 := by
  classical
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  have hα' : ∀ y : orthDerived Q, α (QuotientGroup.mk y) = QuotientGroup.mk
      (⟨G * (y : V ≃ₗ[K] V) * G⁻¹, conj_mem_orthDerived hG y.2⟩ : orthDerived Q) :=
    fun y => (hα y).choose_spec
  have hpow := orth2_conj_pow hG hα'
  have hfixn : ∀ (n : ℕ), ∀ t ∈ Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)),
      (α ^ n) t = t := by
    intro n
    induction n with
    | zero => intro t _; rw [pow_zero, MulAut.one_apply]
    | succ n ih =>
      intro t ht
      rw [pow_succ', MulAut.mul_apply, ih t ht, hfix t ht]
  obtain ⟨e, m', hm', hGo⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos G).ne' 3
    (by norm_num)
  have hG1 : G ^ (3 ^ e) = 1 := by
    refine eq_one_of_conj_fixes_centralizer_projOrthDerived hK hQ hT hpar ha (pow_mem hG _)
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hm') ?_ fun y hy => ?_
    · rw [← pow_mul, ← hGo, pow_orderOf_eq_one]
    · exact ⟨conj_mem_orthDerived (pow_mem hG _) y.2, (hpow (3 ^ e) y).symm.trans (hfixn _ _ hy)⟩
  have hα1 : α ^ (3 ^ e) = 1 := by
    refine MulEquiv.ext fun t => ?_
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective t
    rw [hpow (3 ^ e) y, MulAut.one_apply]
    exact congrArg _ (Subtype.ext (by simp [hG1]))
  have hdvd : orderOf α ∣ 3 ^ e := orderOf_dvd_of_pow_eq_one hα1
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_left e hco).symm hdvd)

end Projective

section Matrix

variable {K : Type} [Field K] [Finite K]

theorem exists_isometry_of_mem_matrixProjectiveImage (hK : Nat.card K = 2) {d : ℕ} (hd : 0 < d)
    {Q : QuadraticForm K (Fin d → K)} (α : MulAut (ProjOrthDerived Q))
    (hα : MulAut.congr (coordBridge Q hd).symm α ∈ matrixProjectiveImage Q) :
    ∃ G ∈ TauCeti.QuadraticMap.orthogonalGroup Q, ∀ y : orthDerived Q,
      ∃ hy : G * (y : (Fin d → K) ≃ₗ[K] (Fin d → K)) * G⁻¹ ∈ orthDerived Q,
        α (QuotientGroup.mk y) = QuotientGroup.mk ⟨G * y * G⁻¹, hy⟩ :=
  exists_isometry_of_inducedBySemilinear hK (exists_semilin_of_mem_matrixProjectiveImage Q hd α hα)

variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem mem_innerAut_of_pow_three_of_induced (hK : Nat.card K = 2)
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) (h5 : 5 ≤ finrank K V)
    {α : MulAut (ProjOrthDerived Q)} (hα : KCOrthogonalAut.InducedBySemilinear Q α)
    (h3 : α ^ 3 = 1) : α ∈ innerAut (ProjOrthDerived Q) := by
  have : CharP K 2 := charP_two hK
  obtain ⟨-, -, -, -, -, -, hodd, -⟩ :=
    CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hQ hT
  obtain ⟨G, hGO, hG⟩ := exists_isometry_of_inducedBySemilinear hK hα
  have hGα : ∀ y : orthDerived Q, α (QuotientGroup.mk y) = QuotientGroup.mk
      (⟨G * (y : V ≃ₗ[K] V) * G⁻¹, conj_mem_orthDerived hGO y.2⟩ : orthDerived Q) := fun y =>
    (hG y).choose_spec
  have hG3 : G ^ 3 = 1 := orth2_isometry_eq_one hK hQ h5 (pow_mem hGO 3)
    (orth2_conj_eq_of_eq_one hK (pow_mem hGO 3) (orth2_conj_pow hGO hGα 3) h3)
  have hGodd : Odd (orderOf G) := Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one hG3)
  have hGΩ : G ∈ orthDerived Q := hodd G hGO hGodd
  refine ⟨QuotientGroup.mk ⟨G, hGΩ⟩, ?_⟩
  ext t
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective t
  rw [MulAut.conj_apply, hGα y, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
    ← QuotientGroup.mk_mul]
  rfl

end Matrix

section Inner

variable {K : Type} [Field K] [Finite K]

theorem coreFreeAt_conj_projOrthDerived (hK : Nat.card K = 2) {d : ℕ} (hd : 0 < d)
    {Q : QuadraticForm K (Fin d → K)} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K (Fin d → K), finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    (hpar : IsPlusType Q ↔ Even (finrank K (Fin d → K) / 2))
    (hE : ∀ g : MulAut (ProjOrthDerived Q), Nat.Coprime 3 (orderOf g) →
      ∃ β : MulAut (ProjOrthDerived Q),
        MulAut.congr (coordBridge Q hd).symm (β⁻¹ * g * β) ∈ matrixProjectiveImage Q)
    {a : ProjOrthDerived Q} (ha : orderOf a = 3) : CoreFreeAt 3 (MulAut.conj a) := by
  refine coreFreeAt_conj_of_inner (KCOrthogonalD4.conj_injective_projOrthDerived Q hQ hT)
    (noNormalPPrime_centralizer_projOrthDerived hK hQ hT hpar ha) fun g hg _ hfix => ?_
  obtain ⟨β, hβ⟩ := hE g hg
  have hco : Nat.Coprime 3 (orderOf (β⁻¹ * g * β)) := by
    have h := MulEquiv.orderOf_eq (MulAut.conj β⁻¹) g
    rw [MulAut.conj_apply, inv_inv] at h
    rwa [h]
  obtain ⟨G, hG, hGα⟩ := exists_isometry_of_mem_matrixProjectiveImage hK hd _ hβ
  have hα : β⁻¹ * g * β = 1 := by
    refine eq_one_of_fixes_centralizer_projOrthDerived hK hQ hT hpar
      ((MulEquiv.orderOf_eq β⁻¹ a).trans ha) hG hGα hco fun t ht => ?_
    have ht' : β t ∈ Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)) := by
      rw [Subgroup.mem_centralizer_singleton_iff] at ht ⊢
      have h1 := congrArg β ht
      rwa [map_mul, map_mul, MulAut.apply_inv_self] at h1
    rw [MulAut.mul_apply, MulAut.mul_apply, hfix _ ht', MulAut.inv_apply_self]
  calc g = β * (β⁻¹ * g * β) * β⁻¹ := by group
    _ = 1 := by rw [hα, mul_one, mul_inv_cancel]

theorem coreFreeAt_of_mem_matrixProjectiveImage (hK : Nat.card K = 2) {d : ℕ} (hd : 0 < d)
    {Q : QuadraticForm K (Fin d → K)} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K (Fin d → K), finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    (hpar : IsPlusType Q ↔ Even (finrank K (Fin d → K) / 2)) (h5 : 5 ≤ d)
    (hE : ∀ g : MulAut (ProjOrthDerived Q), Nat.Coprime 3 (orderOf g) →
      ∃ β : MulAut (ProjOrthDerived Q),
        MulAut.congr (coordBridge Q hd).symm (β⁻¹ * g * β) ∈ matrixProjectiveImage Q)
    {x : MulAut (matrixProjectiveDerived Q)} (hxE : x ∈ matrixProjectiveImage Q) (hx3 : x ^ 3 = 1)
    (hx1 : x ≠ 1) : CoreFreeAt 3 x := by
  classical
  set φ := coordBridge Q hd
  have hα : MulAut.congr φ.symm (MulAut.congr φ x) ∈ matrixProjectiveImage Q := by
    rwa [congr_symm_congr]
  have hα3 : (MulAut.congr φ x) ^ 3 = 1 := by rw [← map_pow, hx3, map_one]
  obtain ⟨t, ht⟩ := mem_innerAut_of_pow_three_of_induced hK hQ hT
    (by rw [Module.finrank_fin_fun]; exact h5)
    (exists_semilin_of_mem_matrixProjectiveImage Q hd _ hα) hα3
  have hinj := KCOrthogonalD4.conj_injective_projOrthDerived Q hQ hT
  have ht3 : t ^ 3 = 1 := by
    apply hinj
    rw [map_pow, map_one, ht, hα3]
  have ht1 : t ≠ 1 := by
    rintro rfl
    refine hx1 ?_
    have h1 : MulAut.congr φ x = 1 := by rw [← ht, map_one]
    calc x = MulAut.congr φ.symm (MulAut.congr φ x) := (congr_symm_congr φ x).symm
      _ = 1 := by rw [h1, map_one]
  have hord : orderOf t = 3 := orderOf_eq_prime ht3 ht1
  have h := coreFreeAt_congr φ.symm
    (coreFreeAt_conj_projOrthDerived hK hd hQ hT hpar hE hord)
  rwa [ht, congr_symm_congr] at h

end Inner

end CFSG.HardMathSupport.Dickson.Bal207.OrthRow.Two

end
