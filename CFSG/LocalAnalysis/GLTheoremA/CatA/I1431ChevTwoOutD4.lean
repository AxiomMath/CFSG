module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ChevTwoOutEnt
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ChevTwoOutTriD4
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.D4Aux.Normal

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I1431C2

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.HardMathSupport.Solomon.Coordinator CFSG.Assembly.LowTwoRank
  CFSG.HardMathSupport.Lang.D4Three CFSG.HardMathSupport.Lang.E6Descent
  CFSG.ComponentClassification.CatLeaf CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Solomon.UniquenessMaximal CFSG.RankThree.PartOne.Sec66T
open CFSG.HardMathSupport.Dickson.Sec6.I923 CFSG.HardMathSupport.Dickson.Sec6.I923.D4Aux
  CFSG.HardMathSupport.Dickson.Sec6.I923.TriD4Aux
open CFSG.HardMathSupport.Lang.E6Descent (twistedEntrywiseAut)
open CFSG.HardMathSupport.Dickson.Sec6 (FamD4 blueprintLieModel_D)
open scoped commutatorElement

theorem card_u42_lt_triD4Order {Q : ℕ} (hQ : 2 ≤ Q) :
    25920 < Q ^ 12 * (Q ^ 2 - 1) * (Q ^ 6 - 1) * (Q ^ 8 + Q ^ 4 + 1) := by
  have h1 : 4096 ≤ Q ^ 12 :=
    calc 4096 = 2 ^ 12 := by norm_num
      _ ≤ Q ^ 12 := Nat.pow_le_pow_left hQ 12
  have h2 : 4 ≤ Q ^ 2 :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ Q ^ 2 := Nat.pow_le_pow_left hQ 2
  have h3 : 64 ≤ Q ^ 6 :=
    calc 64 = 2 ^ 6 := by norm_num
      _ ≤ Q ^ 6 := Nat.pow_le_pow_left hQ 6
  calc 25920 < 4096 * 3 * 63 * 1 := by norm_num
    _ ≤ Q ^ 12 * (Q ^ 2 - 1) * (Q ^ 6 - 1) * (Q ^ 8 + Q ^ 4 + 1) :=
      Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul h1 (by omega)) (by omega)) (by omega)

section D4


theorem u42Layer_entrywiseAdjointAut_D4 {d : ℕ} (hd : 1 ≤ d) {K : Type} [Field K] [Finite K]
    (σ : K ≃+* K) (hk : Nat.card (fixSubfield σ) = 2 ^ d) :
    U42Layer (entrywiseAdjointAut Tag.D4 σ) False := by
  haveI : Finite ↥(fixSubfield σ) := Subtype.finite
  obtain ⟨hs, hnab⟩ := isSimple_adjointD4 (fixSubfield σ)
  exact u42Layer_entrywise σ hs hnab fun h =>
    absurd (eq_of_catalogIs_u4two_lieModel h
      (lieModel_adjointD4 Nat.prime_two hd (fixSubfield σ) hk)).1 (by decide)

theorem u42Layer_twistedEntrywiseAut_D4_one {d : ℕ} (hd : 1 ≤ d) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ d) ^ 3) (r : ℕ) (hr : r = 1 ∨ r = 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ ((2 ^ d) ^ r)) :
    U42Layer (twistedEntrywiseAut TwistTag.D4 1 σ) False := by
  classical
  haveI := finite_adjointD4 K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (k := d * 3) (by omega) (by rw [hK, pow_mul])
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  obtain ⟨-, -, htw, hs, hnab⟩ := triality_both_field_orientations_simple_full_ambient_fixed_group
    2 d Nat.prime_two hd K hK (AlgebraicClosure K) r hr σ.toRingHom hσ
    (iterateFrobenius (AlgebraicClosure K) 2 d) (fun c => iterateFrobenius_def _ _ _)
  have hcard := (triality_both_orientations_exact_finite_order 2 d Nat.prime_two hd K hK r hr
    σ.toRingHom hσ).1
  haveI := hs
  let e : ↥(fixSubgroup (twistedEntrywiseAut TwistTag.D4 1 σ)) ≃*
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    (CFSG.HardMathSupport.Lang.E6Descent.fixedSubgroupTwistedEntrywiseAutOneEquiv
      TwistTag.D4 σ).trans (MulEquiv.subgroupCongr htw)
  refine u42Layer_of_fixed_equiv _ e hs hnab fun hT => ?_
  have h1 := CFSG.LocalAnalysis.GLTheoremA.I1431Z.card_eq_of_u4two hT
  rw [hcard] at h1
  have h2 : 2 ≤ 2 ^ d :=
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hd
  have h3 := card_u42_lt_triD4Order h2
  generalize 2 ^ d = Q at h1 h3
  omega

theorem u42Layer_twistedEntrywiseAut_D4 {d : ℕ} (hd : 1 ≤ d) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ d) ^ 3) (T : K ≃+* K) (hT : ∀ c, T c = c ^ (2 ^ d)) (j : ℤ)
    (hj : j = 1 ∨ j = 2) : U42Layer (twistedEntrywiseAut TwistTag.D4 j T) False := by
  rcases hj with rfl | rfl
  · exact u42Layer_twistedEntrywiseAut_D4_one hd hK 1 (Or.inl rfl) T (by simpa using hT)
  · have hT3 := ringEquiv_cube_apply_eq hK hT
    have hTinv : ∀ c, T⁻¹ c = c ^ ((2 ^ d) ^ 2) := by
      intro c
      have h1 : T⁻¹ (T (T (T c))) = T (T c) := RingEquiv.symm_apply_apply T _
      rw [hT3] at h1
      rw [h1, hT, hT, ← pow_mul, sq]
    exact u42Layer_of_fix_eq
      (CFSG.HardMathSupport.Lang.E6Descent.fixedSubgroup_twistedEntrywiseAut_D4_two T)
      (u42Layer_twistedEntrywiseAut_D4_one hd hK 2 (Or.inr rfl) T⁻¹ hTinv)

theorem u42Layer_adjointD4_of_fieldType {f : ℕ} (hf : 1 ≤ f)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = 2 ^ f)
    (α : MulAut (adjointGroup Tag.D4 K)) (hα3 : α ^ 3 = 1) (g : adjointGroup Tag.D4 K)
    (a : Fin Tag.D4.rank → Kˣ) (σ : K ≃+* K) (hσ3 : σ ^ 3 = 1) (hσ1 : σ ≠ 1)
    (hαeq : α = MulAut.conj g * (exactNormalAut Tag.D4 K a σ 0 * d4Graph K 0)) :
    U42Layer α False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two hf hK
  obtain ⟨d, T, hd0, hdf, hT, hT3, hσT⟩ := exists_frobenius_of_cube Nat.prime_two hf K hK σ hσ3 hσ1
  rw [d4Graph_zero, mul_one] at hαeq
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    exact four_le_card Nat.prime_two (by omega)
  have hKd : Nat.card K = (2 ^ d) ^ 3 := by rw [hK, ← pow_mul, hdf]
  have hfix : Nat.card (fixSubfield T) = 2 ^ d :=
    CFSG.RankThree.PartOne.KGD.card_fixSubfield_cube Nat.prime_two hd0 hKd T hT
  have hfield : U42Layer (entrywiseAdjointAut Tag.D4 T) False :=
    u42Layer_entrywiseAdjointAut_D4 hd0 T hfix
  have hconj : ∀ (β : MulAut (adjointGroup Tag.D4 K)) (g' : adjointGroup Tag.D4 K)
      (a' : Fin Tag.D4.rank → Kˣ), β = MulAut.conj g' * exactNormalAut Tag.D4 K a' T 0 →
      β ^ 3 = 1 → U42Layer β False := by
    intro β g' a' hβ hβ3
    obtain ⟨ψ, hψ⟩ := exists_conj_eq_entrywiseAdjointAut_D4 hK hK4 hd0 hdf T hT g' a' β hβ hβ3
    exact u42Layer_of_conj ψ β (hψ ▸ hfield)
  rcases hσT with hσ | hσ
  · rw [hσ] at hαeq
    exact hconj α g a hαeq hα3
  · obtain ⟨g', a', hα2⟩ := sq_conj_mul_exactNormalAut g a σ
    have hσ2 : σ ^ 2 = T := by
      rw [hσ, ← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, hT3, one_mul]
    rw [hσ2, ← hαeq] at hα2
    have hα23 : (α ^ 2) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hα3, one_pow]
    have hα22 : (α ^ 2) ^ 2 = α := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, hα3, one_mul]
    have hfixeq : fixSubgroup α = fixSubgroup (α ^ 2) := fixedSubgroup_pow_eq hα22
    exact u42Layer_of_fix_eq hfixeq (hconj (α ^ 2) g' a' hα2 hα23)

theorem u42Layer_adjointD4_of_graphFieldType {f : ℕ} (hf : 1 ≤ f)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = 2 ^ f)
    (α : MulAut (adjointGroup Tag.D4 K)) (hα3 : α ^ 3 = 1) (g : adjointGroup Tag.D4 K)
    (a : Fin Tag.D4.rank → Kˣ) (σ : K ≃+* K) (ε : ℕ) (hε : ε < 3) (hε0 : ε ≠ 0)
    (hσ3 : σ ^ 3 = 1) (hσ1 : σ ≠ 1)
    (hαeq : α = MulAut.conj g * (exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε)) :
    U42Layer α False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two hf hK
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf σ = 3 := orderOf_eq_prime hσ3 hσ1
  obtain ⟨e, T, he, hef, hT, hσT⟩ := exists_frobenius_eq_or_inv_of_orderOf_three Nat.prime_two hf K
    hK σ hord
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    exact four_le_card Nat.prime_two (by omega)
  have hKe : Nat.card K = (2 ^ e) ^ 3 := by rw [hK, ← pow_mul, hef]
  have hε' : ε = 1 ∨ ε = 2 := by omega
  rcases hσT with hσ | hσ
  · rw [hσ] at hαeq
    obtain ⟨ψ, hψ⟩ :=
      exists_conj_eq_twistedEntrywiseAut_of_normalForm K hK hK4 he hef T hT α hα3 g a ε hαeq
    refine u42Layer_of_conj ψ α ?_
    rw [hψ]
    exact u42Layer_twistedEntrywiseAut_D4 he hKe T hT (ε : ℤ) (by omega)
  · rw [hσ] at hαeq
    obtain ⟨ψ, hψ⟩ := exists_conj_inv_eq_twistedEntrywiseAut_of_normalForm K hK hK4 he hef T T⁻¹
      hT (mul_inv_cancel T) α hα3 g a ε hαeq
    have hshift : twistedEntrywiseAut TwistTag.D4 (-(ε : ℤ)) T =
        twistedEntrywiseAut TwistTag.D4 (3 - (ε : ℤ)) T := by
      have h := twistedEntrywiseAut_add_mul_order TwistTag.D4 (-(ε : ℤ)) 1 T
      rw [show -(ε : ℤ) + 1 * ((TwistTag.D4.order : ℕ) : ℤ) = 3 - (ε : ℤ) by
        change -(ε : ℤ) + 1 * 3 = _
        ring] at h
      exact h.symm
    have hinv : U42Layer α⁻¹ False := by
      refine u42Layer_of_conj ψ α⁻¹ ?_
      rw [hψ, hshift]
      exact u42Layer_twistedEntrywiseAut_D4 he hKe T hT (3 - (ε : ℤ)) (by omega)
    exact (u42Layer_inv_iff α False).1 hinv

theorem u42Layer_adjointD4_of_graphType {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ f) (α : MulAut (adjointGroup Tag.D4 K)) (hα3 : α ^ 3 = 1)
    (g : adjointGroup Tag.D4 K) (a : Fin Tag.D4.rank → Kˣ) {ε : ℕ} (hε : ε = 1 ∨ ε = 2)
    (hαeq : α = MulAut.conj g * (exactNormalAut Tag.D4 K a 1 0 * d4Graph K ε)) :
    U42Layer α False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K₃, _, _, Fr, hK₃, hFr, φ, hφ3, hφout, ⟨e⟩⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Dual.exists_dual_fixEquiv hf K hK α
      hα3 g a hε hαeq
  haveI := finite_graphFixedRootGroup_D4 Fr
  exact u42Layer_of_fixEquiv e (u42Layer_three_D4_outer_two hf hK₃ Fr hFr φ hφ3 hφout)

theorem u42Layer_adjointD4_outer {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ f) (α : MulAut (adjointGroup Tag.D4 K)) (hα3 : α ^ 3 = 1)
    (hα : α ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner (adjointGroup Tag.D4 K)) :
    U42Layer α False := by
  obtain ⟨g, a, σ, ε, hε, hαeq, hσ3, hcase⟩ := outer_cube_normal_form_cases α hα3 hα
  rcases hcase with ⟨hε0, hσ1⟩ | ⟨hε0, hσ1⟩ | ⟨hε0, hσ1⟩
  · subst hε0
    exact u42Layer_adjointD4_of_fieldType hf K hK α hα3 g a σ hσ3 hσ1 hαeq
  · exact u42Layer_adjointD4_of_graphFieldType hf K hK α hα3 g a σ ε hε hε0 hσ3 hσ1 hαeq
  · subst hσ1
    exact u42Layer_adjointD4_of_graphType hf K hK α hα3 g a (by omega) hαeq

end D4

section Family


theorem u42Out_d4 : U42OuterAt FamD4 := by
  intro S _ _ hs hnab ⟨d, hv⟩ hF hc ⟨e⟩ α hα hp
  cases d with
  | D r q =>
    exfalso
    have hq2 : q.p = 2 := hc
    have hr4 : r = 4 := hF
    subst hr4
    have hm := blueprintLieModel_D 4 q hv e
    have hC : StatedClassicalModel S .POmegaPlus 4 q.p q.exponent :=
      (lieModel_classical_iff (by decide)).mp hm
    obtain ⟨-, K, _, _, hK, ⟨e0⟩⟩ := hC
    rw [hq2] at hK
    obtain ⟨e'⟩ :=
      CFSG.HardMathSupport.Lang.Coordinator.D4Bridge.nonempty_statedProj_equiv_adjointGroup K
    let E : S ≃* adjointGroup Tag.D4 K := e0.trans e'
    haveI := finite_adjointD4 K
    have hα3 : MulAut.congr E α ^ 3 = 1 := by rw [← map_pow, hp.1, map_one]
    have hαi : MulAut.congr E α ∉
        CFSG.ComponentClassification.OuterAutomorphisms.inner (adjointGroup Tag.D4 K) := by
      rintro ⟨c, hc'⟩
      refine not_mem_range_conj_of_not_mem_innAutDerived hα
        ⟨E.symm c, (MulAut.congr E).injective ?_⟩
      rw [CFSG.ComponentClassification.OuterAutomorphisms.congr_conj, MulEquiv.apply_symm_apply]
      exact hc'
    exact hp.apply (u42Layer_congr E (u42Layer_adjointD4_outer q.exponent_pos K hK _ hα3 hαi))
  | _ => exact hF.elim

end Family

end CFSG.LocalAnalysis.GLTheoremA.I1431C2

end
