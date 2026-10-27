module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222OrthTwoA
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222OrthPairC
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofResidual

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Module Matrix QuadraticMap Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.RankTwoStandard CFSG.LieType.Universal.Spin
open scoped Matrix

theorem fix_of_odd_orderOf {G : Type} [Group G] {p u g : G} (hp2 : p * p = 1) (hp1 : p ≠ 1)
    (hgp : g * p = p * g) (hu2 : u * u = 1) (hg : Odd (orderOf g))
    (horb : g * u * g⁻¹ = u ∨ g * u * g⁻¹ = u * p) : g * u * g⁻¹ = u := by
  rcases horb with h | h
  · exact h
  exfalso
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  have hgu : g * u = u * p * g := by rw [← h]; group
  have h1 : u * g * u⁻¹ = p * g := by
    rw [hui, mul_assoc, hgu, ← mul_assoc, ← mul_assoc, hu2, one_mul]
  have h2 : (u * g * u⁻¹) ^ orderOf g = 1 := by
    rw [conj_pow, pow_orderOf_eq_one, mul_one, mul_inv_cancel]
  obtain ⟨k, hk⟩ := hg
  rw [h1, Commute.mul_pow hgp.symm, pow_orderOf_eq_one, mul_one, hk, pow_succ, pow_mul,
    _root_.sq, hp2, one_pow, one_mul] at h2
  exact hp1 h2

section Rotation

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] {Q : QuadraticForm K (ι → K)}

@[expose] noncomputable def anisoRot (Q : QuadraticForm K (ι → K)) (a b : ι → K) :
    Matrix ι ι K :=
  1 + polMat Q a a + polMat Q b (a + b)

theorem anisoRot_mulVec (a b v : ι → K) :
    anisoRot Q a b *ᵥ v = v + Q.polarBilin v a • a + Q.polarBilin v b • (a + b) := by
  rw [anisoRot, add_mulVec, add_mulVec, one_mulVec, polMat_mulVec, polMat_mulVec]

omit [DecidableEq ι] in
theorem exists_basis_of_rank_two {N : Matrix ι ι K} (hrk : N.rank = 2) :
    ∃ n : Fin 2 → ι → K, LinearIndependent K n ∧ (∀ i, ∃ u, N *ᵥ u = n i) ∧
      ∀ v, ∃ s t : K, N *ᵥ v = s • n 0 + t • n 1 := by
  have hR : finrank K (LinearMap.range N.mulVecLin) = 2 := hrk
  obtain ⟨b⟩ : Nonempty (Basis (Fin 2) K (LinearMap.range N.mulVecLin)) :=
    ⟨Module.finBasisOfFinrankEq K _ hR⟩
  refine ⟨fun i => (b i : ι → K), b.linearIndependent.map' _ (Submodule.ker_subtype _),
    fun i => ?_, fun v => ?_⟩
  · obtain ⟨u, hu⟩ := (b i).2
    exact ⟨u, hu⟩
  · have h := b.sum_repr ⟨N *ᵥ v, v, rfl⟩
    rw [Fin.sum_univ_two] at h
    refine ⟨b.repr ⟨N *ᵥ v, v, rfl⟩ 0, b.repr ⟨N *ᵥ v, v, rfl⟩ 1, ?_⟩
    have h2 := congrArg Subtype.val h
    simpa using h2.symm

omit [DecidableEq ι] in
theorem exists_polar_pair_perp (hQ : Q.polarBilin.Nondegenerate) {m : ℕ}
    (hm : m + m < Fintype.card ι) {g : Fin m → ι → K} (hg : LinearIndependent K g) :
    ∃ c c' : ι → K, (∀ i, Q.polarBilin c (g i) = 0) ∧ (∀ i, Q.polarBilin c' (g i) = 0) ∧
      Q.polarBilin c c' = 1 := by
  obtain ⟨c, hc, hcn⟩ := exists_polar_perp_not_mem_span (Q := Q) hm g
  obtain ⟨w, hw⟩ := exists_polar_dual Q hQ (Fin.cons c g : Fin (m + 1) → ι → K)
    (linearIndependent_finCons.mpr ⟨hg, hcn⟩)
  refine ⟨c, w 0, hc, fun i => ?_, ?_⟩
  · have h := hw i.succ 0
    simp only [Fin.cons_succ, Fin.succ_ne_zero, ite_false] at h
    rw [polarBilin_comm]
    exact h
  · simpa using hw 0 0

variable [CharP K 2]

theorem anisoRot_mul_anisoRot {a b : ι → K} (hab : Q.polarBilin a b = 1) :
    anisoRot Q a b * anisoRot Q b a = 1 := by
  have hba : Q.polarBilin b a = 1 := (polarBilin_comm Q b a).trans hab
  have haa : Q.polarBilin a a = 0 := TypeCData.pol_self a
  have hbb : Q.polarBilin b b = 0 := TypeCData.pol_self b
  refine Matrix.ext_iff_mulVec.mpr fun v => ?_
  rw [← mulVec_mulVec, anisoRot_mulVec, anisoRot_mulVec, one_mulVec]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hab, hba,
    haa, hbb]
  linear_combination (norm := module) CharTwo.two_eq_zero (R := K) •
    ((2 * Q.polarBilin v a + Q.polarBilin v b) • a + (Q.polarBilin v a + Q.polarBilin v b) • b)

theorem anisoRot_mul_self {a b : ι → K} (hab : Q.polarBilin a b = 1) :
    anisoRot Q a b * anisoRot Q a b = anisoRot Q b a := by
  have hba : Q.polarBilin b a = 1 := (polarBilin_comm Q b a).trans hab
  have haa : Q.polarBilin a a = 0 := TypeCData.pol_self a
  have hbb : Q.polarBilin b b = 0 := TypeCData.pol_self b
  refine Matrix.ext_iff_mulVec.mpr fun v => ?_
  rw [← mulVec_mulVec, anisoRot_mulVec, anisoRot_mulVec, anisoRot_mulVec]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hab, hba,
    haa, hbb]
  linear_combination (norm := module) CharTwo.two_eq_zero (R := K) •
    ((Q.polarBilin v a + 2 * Q.polarBilin v b) • a + Q.polarBilin v b • b)

@[expose] noncomputable def anisoRotGL {a b : ι → K} (hab : Q.polarBilin a b = 1) : GL ι K where
  val := anisoRot Q a b
  inv := anisoRot Q b a
  val_inv := anisoRot_mul_anisoRot hab
  inv_val := anisoRot_mul_anisoRot ((polarBilin_comm Q b a).trans hab)

theorem coe_anisoRotGL {a b : ι → K} (hab : Q.polarBilin a b = 1) :
    ((anisoRotGL hab : GL ι K) : Matrix ι ι K) = anisoRot Q a b := rfl

theorem anisoRotGL_pow_three {a b : ι → K} (hab : Q.polarBilin a b = 1) :
    (anisoRotGL hab : GL ι K) ^ 3 = 1 := Units.ext (by
  rw [pow_succ, pow_two, Units.val_mul, Units.val_mul, coe_anisoRotGL, anisoRot_mul_self hab,
    anisoRot_mul_anisoRot ((polarBilin_comm Q b a).trans hab), Units.val_one])

theorem anisoRot_isometry {a b : ι → K} (ha : Q a = 1) (hb : Q b = 1)
    (hab : Q.polarBilin a b = 1) (v : ι → K) : Q (anisoRot Q a b *ᵥ v) = Q v := by
  have haa : Q.polarBilin a a = 0 := TypeCData.pol_self a
  rw [anisoRot_mulVec, add_assoc, quad_add, quad_add, QuadraticMap.map_smul,
    QuadraticMap.map_smul, quad_add, ha, hb, hab]
  simp only [map_add, map_smul, LinearMap.smul_apply, smul_eq_mul, haa, hab]
  linear_combination (Q.polarBilin v a ^ 2 + 2 * Q.polarBilin v b ^ 2 +
    Q.polarBilin v a * Q.polarBilin v b) * CharTwo.two_eq_zero (R := K)

theorem rank_anisoRot_sub_one {a b : ι → K} (hab : Q.polarBilin a b = 1) :
    (anisoRot Q a b - 1).rank = 2 := by
  have hba : Q.polarBilin b a = 1 := (polarBilin_comm Q b a).trans hab
  have haa : Q.polarBilin a a = 0 := TypeCData.pol_self a
  have hbb : Q.polarBilin b b = 0 := TypeCData.pol_self b
  refine rank_eq_two_of (u := a) (w := b) (fun s t h => ?_) (fun v => ⟨Q.polarBilin v a +
    Q.polarBilin v b, Q.polarBilin v b, ?_⟩) ⟨b, ?_⟩ ⟨a + b, ?_⟩
  · have h1 := congrArg (fun y => Q.polarBilin y a) h
    have h2 := congrArg (fun y => Q.polarBilin y b) h
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, haa,
      hab, hba, hbb, map_zero, LinearMap.zero_apply, mul_zero, mul_one, zero_add,
      add_zero] at h1 h2
    exact ⟨h2, h1⟩
  · rw [sub_mulVec, one_mulVec, anisoRot_mulVec]
    module
  · rw [sub_mulVec, one_mulVec, anisoRot_mulVec, hba, hbb, one_smul, zero_smul, add_zero,
      add_sub_cancel_left]
  · rw [sub_mulVec, one_mulVec, anisoRot_mulVec]
    simp only [map_add, LinearMap.add_apply, haa, hab, hba, hbb, zero_add, add_zero, one_smul]
    linear_combination (norm := module) CharTwo.two_eq_zero (R := K) • a

omit [CharP K 2] in
theorem anisoRot_mul_eq {N : Matrix ι ι K}
    (hadj : ∀ u v, Q.polarBilin (N *ᵥ u) v = Q.polarBilin u (N *ᵥ v)) {a b : ι → K}
    (ha : N *ᵥ a = 0) (hb : N *ᵥ b = 0) :
    anisoRot Q a b * N = N := Matrix.ext_iff_mulVec.mpr fun v => by
  rw [← mulVec_mulVec, anisoRot_mulVec, hadj, hadj, ha, hb, map_zero, zero_smul, zero_smul,
    add_zero, add_zero]

omit [CharP K 2] in
theorem mul_anisoRot_eq {N : Matrix ι ι K} {a b : ι → K} (ha : N *ᵥ a = 0) (hb : N *ᵥ b = 0) :
    N * anisoRot Q a b = N := Matrix.ext_iff_mulVec.mpr fun v => by
  rw [← mulVec_mulVec, anisoRot_mulVec, mulVec_add, mulVec_add, mulVec_smul, mulVec_smul,
    mulVec_add, ha, hb, add_zero, smul_zero, smul_zero, add_zero, add_zero]

theorem eq_of_commute_anisoRot {a b : ι → K} (hab : Q.polarBilin a b = 1) {U : Matrix ι ι K}
    (hU2 : U * U = 1) (hUT : U * anisoRot Q a b = anisoRot Q a b * U) :
    U *ᵥ a = a ∧ U *ᵥ b = b := by
  have hba : Q.polarBilin b a = 1 := (polarBilin_comm Q b a).trans hab
  have haa : Q.polarBilin a a = 0 := TypeCData.pol_self a
  have hbb : Q.polarBilin b b = 0 := TypeCData.pol_self b
  have hT : ∀ v, U *ᵥ (anisoRot Q a b *ᵥ v) = anisoRot Q a b *ᵥ (U *ᵥ v) := fun v => by
    rw [mulVec_mulVec, hUT, ← mulVec_mulVec]
  have h1 := hT b
  rw [anisoRot_mulVec, anisoRot_mulVec, hba, hbb, zero_smul, add_zero, one_smul,
    mulVec_add] at h1
  obtain ⟨α, β, hUa⟩ : ∃ α β : K, U *ᵥ a = α • a + β • b :=
    ⟨Q.polarBilin (U *ᵥ b) a + Q.polarBilin (U *ᵥ b) b, Q.polarBilin (U *ᵥ b) b, by
      linear_combination (norm := module) h1⟩
  have hUaa : Q.polarBilin (U *ᵥ a) a = β := by
    rw [hUa]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, haa,
      hba, mul_zero, mul_one, zero_add]
  have hUab : Q.polarBilin (U *ᵥ a) b = α := by
    rw [hUa]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hab,
      hbb, mul_zero, mul_one, add_zero]
  have h2 := hT a
  rw [anisoRot_mulVec, anisoRot_mulVec, haa, hab, zero_smul, add_zero, one_smul, hUaa, hUab,
    mulVec_add, mulVec_add] at h2
  have hUb : U *ᵥ b = β • a + (α - β) • b := by
    linear_combination (norm := module) h2 - hUa
  have h3 : U *ᵥ (U *ᵥ a) = a := by rw [mulVec_mulVec, hU2, one_mulVec]
  rw [hUa, mulVec_add, mulVec_smul, mulVec_smul, hUa, hUb] at h3
  have h4 := congrArg (fun y => Q.polarBilin y a) h3
  have h5 := congrArg (fun y => Q.polarBilin y b) h3
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, haa, hab,
    hba, hbb, mul_zero, mul_one, zero_add, add_zero] at h4 h5
  have hβ : β = 0 := by
    have h6 : β ^ 2 = 0 := by
      linear_combination -h4 + α * β * CharTwo.two_eq_zero (R := K)
    exact pow_eq_zero_iff two_ne_zero |>.mp h6
  rw [hβ] at h5 hUa hUb
  have hα : α = 1 := by
    have h6 : (α - 1) ^ 2 = 0 := by
      linear_combination h5 + (1 - α) * CharTwo.two_eq_zero (R := K)
    exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h6)
  rw [hα] at hUa hUb
  refine ⟨?_, ?_⟩
  · rw [hUa]
    module
  · rw [hUb]
    module

end Rotation

section Span

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] [Finite K] [CharP K 2]
  {Q : QuadraticForm K (ι → K)}

omit [DecidableEq ι] [CharP K 2] in
private theorem two_cases (hK : Nat.card K = 2) (t : K) : t = 0 ∨ t = 1 := by
  by_cases ht : t = 0
  · exact Or.inl ht
  · have h := congrArg Units.val (eq_one_of_units_of_card_eq_two hK (Units.mk0 t ht))
    exact Or.inr (by simpa using h)

omit [Fintype ι] [DecidableEq ι] in
private theorem exists_nonsingular_of_pair (hK : Nat.card K = 2) {c c' : ι → K}
    (hcc : Q.polarBilin c c' = 1) :
    ∃ a x : ι → K, Q a = 1 ∧ Q.polarBilin a x = 1 ∧
      ∀ y, Q.polarBilin c y = 0 → Q.polarBilin c' y = 0 →
        Q.polarBilin a y = 0 ∧ Q.polarBilin x y = 0 := by
  rcases two_cases hK (Q c) with hc | hc
  · rcases two_cases hK (Q c') with hc' | hc'
    · refine ⟨c + c', c, ?_, ?_, fun y h1 h2 => ⟨?_, h1⟩⟩
      · rw [quad_add, hc, hc', hcc, zero_add, zero_add]
      · rw [map_add, LinearMap.add_apply, TypeCData.pol_self, polarBilin_comm Q c' c, hcc,
          zero_add]
      · rw [map_add, LinearMap.add_apply, h1, h2, add_zero]
    · exact ⟨c', c, hc', (polarBilin_comm Q c' c).trans hcc, fun y h1 h2 => ⟨h2, h1⟩⟩
  · exact ⟨c, c', hc, hcc, fun y h1 h2 => ⟨h1, h2⟩⟩

omit [DecidableEq ι] in
theorem mulVec_eq_zero_of_anisotropic (hK : Nat.card K = 2) (hQ : Q.polarBilin.Nondegenerate)
    (hι : 7 ≤ Fintype.card ι) {N : Matrix ι ι K}
    (hadj : ∀ u v, Q.polarBilin (N *ᵥ u) v = Q.polarBilin u (N *ᵥ v)) (hrk : N.rank = 2)
    {D : Matrix ι ι K}
    (hD : ∀ a b, N *ᵥ a = 0 → N *ᵥ b = 0 → Q a = 1 → Q b = 1 → Q.polarBilin a b = 1 →
      D *ᵥ a = 0) {k : ι → K} (hk : N *ᵥ k = 0) : D *ᵥ k = 0 := by
  have hBs : ∀ a b, Q.polarBilin a b = Q.polarBilin b a := polarBilin_comm Q
  obtain ⟨n, hn, hnN, hspan⟩ := exists_basis_of_rank_two hrk
  have hker : ∀ v, Q.polarBilin v (n 0) = 0 → Q.polarBilin v (n 1) = 0 → N *ᵥ v = 0 := by
    intro v h0 h1
    refine hQ.1 _ fun w => ?_
    obtain ⟨s, t, hst⟩ := hspan w
    rw [hadj, hst, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, h0, h1, mul_zero,
      mul_zero, add_zero]
  have hkerB : ∀ v, N *ᵥ v = 0 → ∀ i, Q.polarBilin v (n i) = 0 := by
    intro v hv i
    obtain ⟨u, hu⟩ := hnN i
    rw [← hu, ← hadj, hv, map_zero, LinearMap.zero_apply]
  have hperpspan : ∀ y ∈ Submodule.span K (Set.range n), ∀ x, N *ᵥ x = 0 →
      Q.polarBilin y x = 0 := by
    intro y hy x hx
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hy
    rw [← hc, Fin.sum_univ_two, map_add, map_smul, map_smul, LinearMap.add_apply,
      LinearMap.smul_apply, LinearMap.smul_apply, hBs (n 0), hBs (n 1), hkerB x hx 0,
      hkerB x hx 1, smul_zero, smul_zero, add_zero]
  have hH3 : ∀ a x, N *ᵥ a = 0 → N *ᵥ x = 0 → Q a = 1 → Q.polarBilin a x = 1 →
      D *ᵥ a = 0 := by
    intro a x ha hx hQa hax
    have han : a ∉ Submodule.span K (Set.range n) := fun h => by
      have h1 := hperpspan a h x hx
      rw [hax] at h1
      exact one_ne_zero h1
    obtain ⟨c, c', hc, hc', hcc'⟩ := exists_polar_pair_perp hQ (m := 3) (by omega)
      (linearIndependent_finCons.mpr ⟨hn, han⟩)
    have hca : Q.polarBilin c a = 0 := by simpa using hc 0
    have hc'a : Q.polarBilin c' a = 0 := by simpa using hc' 0
    have hcN : N *ᵥ c = 0 := hker c (by simpa only [Fin.cons_succ] using hc (Fin.succ 0))
      (by simpa only [Fin.cons_succ] using hc (Fin.succ 1))
    have hc'N : N *ᵥ c' = 0 := hker c' (by simpa only [Fin.cons_succ] using hc' (Fin.succ 0))
      (by simpa only [Fin.cons_succ] using hc' (Fin.succ 1))
    have hac : Q.polarBilin a c = 0 := by rw [hBs]; exact hca
    have hac' : Q.polarBilin a c' = 0 := by rw [hBs]; exact hc'a
    rcases two_cases hK (Q x) with hQx | hQx
    · rcases two_cases hK (Q (x + c)) with h1 | h1
      · rcases two_cases hK (Q (x + c')) with h2 | h2
        · refine hD a (x + c + c') ha (by rw [mulVec_add, mulVec_add, hx, hcN, hc'N, add_zero,
            add_zero]) hQa ?_ (by rw [map_add, map_add, hac, hac', hax, add_zero, add_zero])
          rw [quad_add, h1, map_add, LinearMap.add_apply, hcc']
          rw [quad_add, hQx] at h2
          linear_combination h2
        · exact hD a (x + c') ha (by rw [mulVec_add, hx, hc'N, add_zero]) hQa h2
            (by rw [map_add, hac', hax, add_zero])
      · exact hD a (x + c) ha (by rw [mulVec_add, hx, hcN, add_zero]) hQa h1
          (by rw [map_add, hac, hax, add_zero])
    · exact hD a x ha hx hQa hQx hax
  by_cases hkn : k ∈ Submodule.span K (Set.range n)
  ·
    have hkx : ∀ y, N *ᵥ y = 0 → Q.polarBilin k y = 0 := fun y hy => hperpspan k hkn y hy
    obtain ⟨c, c', hc, hc', hcc'⟩ := exists_polar_pair_perp hQ (m := 2) (by omega) hn
    have hcN : N *ᵥ c = 0 := hker c (hc 0) (hc 1)
    have hc'N : N *ᵥ c' = 0 := hker c' (hc' 0) (hc' 1)
    obtain ⟨a₀, x₀, hQa₀, ha₀x₀, hp₀⟩ := exists_nonsingular_of_pair hK hcc'
    have ha₀N : N *ᵥ a₀ = 0 :=
      hker a₀ (hp₀ (n 0) (hc 0) (hc' 0)).1 (hp₀ (n 1) (hc 1) (hc' 1)).1
    have hx₀N : N *ᵥ x₀ = 0 :=
      hker x₀ (hp₀ (n 0) (hc 0) (hc' 0)).2 (hp₀ (n 1) (hc 1) (hc' 1)).2
    have hDa₀ := hH3 a₀ x₀ ha₀N hx₀N hQa₀ ha₀x₀
    rcases two_cases hK (Q k) with hQk | hQk
    · have h1 := hH3 (k + a₀) x₀ (by rw [mulVec_add, hk, ha₀N, add_zero]) hx₀N
        (by rw [quad_add, hQk, hQa₀, hkx a₀ ha₀N, zero_add, add_zero])
        (by rw [map_add, LinearMap.add_apply, hkx x₀ hx₀N, ha₀x₀, zero_add])
      rw [mulVec_add, hDa₀, add_zero] at h1
      exact h1
    ·
      have hcn : c ∉ Submodule.span K (Set.range n) := fun h => by
        have h1 := hperpspan c h c' hc'N
        rw [hcc'] at h1
        exact one_ne_zero h1
      obtain ⟨e, e', he, he', hee'⟩ := exists_polar_pair_perp hQ (m := 3) (by omega)
        (linearIndependent_finCons.mpr ⟨hn, hcn⟩)
      have hec : Q.polarBilin e c = 0 := by simpa using he 0
      have he'c : Q.polarBilin e' c = 0 := by simpa using he' 0
      have heN : N *ᵥ e = 0 := hker e (by simpa only [Fin.cons_succ] using he (Fin.succ 0))
        (by simpa only [Fin.cons_succ] using he (Fin.succ 1))
      have he'N : N *ᵥ e' = 0 := hker e' (by simpa only [Fin.cons_succ] using he' (Fin.succ 0))
        (by simpa only [Fin.cons_succ] using he' (Fin.succ 1))
      have hcc : Q.polarBilin c c = 0 := TypeCData.pol_self c
      set e₁ := e + Q.polarBilin e c' • c with he₁
      set e₁' := e' + Q.polarBilin e' c' • c with he₁'
      have he₁c : Q.polarBilin e₁ c = 0 := by
        rw [he₁, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, hec, hcc,
          smul_zero, add_zero]
      have he₁'c : Q.polarBilin e₁' c = 0 := by
        rw [he₁', map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, he'c, hcc,
          smul_zero, add_zero]
      have he₁c' : Q.polarBilin e₁ c' = 0 := by
        rw [he₁, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, hcc', smul_eq_mul,
          mul_one, CharTwo.add_self_eq_zero]
      have he₁'c' : Q.polarBilin e₁' c' = 0 := by
        rw [he₁', map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, hcc',
          smul_eq_mul, mul_one, CharTwo.add_self_eq_zero]
      have he₁e₁' : Q.polarBilin e₁ e₁' = 1 := by
        rw [he₁, he₁']
        simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
          hee', hec, hcc, hBs c e', he'c, mul_zero, add_zero]
      obtain ⟨a₁, x₁, hQa₁, ha₁x₁, hp₁⟩ := exists_nonsingular_of_pair hK he₁e₁'
      have he₁n : ∀ i, Q.polarBilin e₁ (n i) = 0 := fun i => by
        rw [he₁, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, hkerB c hcN i,
          smul_zero, add_zero]
        simpa only [Fin.cons_succ] using he i.succ
      have he₁'n : ∀ i, Q.polarBilin e₁' (n i) = 0 := fun i => by
        rw [he₁', map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, hkerB c hcN i,
          smul_zero, add_zero]
        simpa only [Fin.cons_succ] using he' i.succ
      have ha₁N : N *ᵥ a₁ = 0 :=
        hker a₁ (hp₁ (n 0) (he₁n 0) (he₁'n 0)).1 (hp₁ (n 1) (he₁n 1) (he₁'n 1)).1
      have hx₁N : N *ᵥ x₁ = 0 :=
        hker x₁ (hp₁ (n 0) (he₁n 0) (he₁'n 0)).2 (hp₁ (n 1) (he₁n 1) (he₁'n 1)).2
      have hDa₁ := hH3 a₁ x₁ ha₁N hx₁N hQa₁ ha₁x₁
      have ha₁c : Q.polarBilin a₁ c = 0 := (hp₁ c he₁c he₁'c).1
      have ha₁c' : Q.polarBilin a₁ c' = 0 := (hp₁ c' he₁c' he₁'c').1
      have ha₀a₁ : Q.polarBilin a₀ a₁ = 0 :=
        (hp₀ a₁ (by rw [hBs]; exact ha₁c) (by rw [hBs]; exact ha₁c')).1
      have hx₀a₁ : Q.polarBilin a₁ x₀ = 0 := by
        rw [hBs]
        exact (hp₀ a₁ (by rw [hBs]; exact ha₁c) (by rw [hBs]; exact ha₁c')).2
      have h1 := hH3 (k + a₀ + a₁) x₀
        (by rw [mulVec_add, mulVec_add, hk, ha₀N, ha₁N, add_zero, add_zero]) hx₀N
        (by
          rw [quad_add, quad_add, hQk, hQa₀, hQa₁, hkx a₀ ha₀N, map_add, LinearMap.add_apply,
            hkx a₁ ha₁N, ha₀a₁]
          linear_combination CharTwo.two_eq_zero (R := K))
        (by rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, hkx x₀ hx₀N,
          ha₀x₀, hx₀a₁, zero_add, add_zero])
      rw [mulVec_add, mulVec_add, hDa₀, hDa₁, add_zero, add_zero] at h1
      exact h1
  ·
    have hli : LinearIndependent K (Fin.cons k n : Fin 3 → ι → K) :=
      linearIndependent_finCons.mpr ⟨hn, hkn⟩
    obtain ⟨w, hw⟩ := exists_polar_dual Q hQ (Fin.cons k n : Fin 3 → ι → K) hli
    have hkw : Q.polarBilin k (w 0) = 1 := by simpa using hw 0 0
    have hwN : N *ᵥ w 0 = 0 := hker _
      (by rw [hBs]; simpa only [Fin.cons_succ, Fin.succ_ne_zero, ite_false] using hw (Fin.succ 0) 0)
      (by rw [hBs]; simpa only [Fin.cons_succ, Fin.succ_ne_zero, ite_false] using hw (Fin.succ 1) 0)
    rcases two_cases hK (Q k) with hQk | hQk
    · obtain ⟨c, c', hc, hc', hcc'⟩ := exists_polar_pair_perp hQ (m := 3) (by omega) hli
      obtain ⟨a₀, x₀, hQa₀, ha₀x₀, hp₀⟩ := exists_nonsingular_of_pair hK hcc'
      have hp : ∀ i, Q.polarBilin a₀ ((Fin.cons k n : Fin 3 → ι → K) i) = 0 ∧
          Q.polarBilin x₀ ((Fin.cons k n : Fin 3 → ι → K) i) = 0 := fun i => hp₀ _ (hc i) (hc' i)
      have ha₀N : N *ᵥ a₀ = 0 := hker a₀ (by simpa only [Fin.cons_succ] using (hp (Fin.succ 0)).1)
        (by simpa only [Fin.cons_succ] using (hp (Fin.succ 1)).1)
      have hx₀N : N *ᵥ x₀ = 0 := hker x₀ (by simpa only [Fin.cons_succ] using (hp (Fin.succ 0)).2)
        (by simpa only [Fin.cons_succ] using (hp (Fin.succ 1)).2)
      have hka₀ : Q.polarBilin k a₀ = 0 := by rw [hBs]; simpa using (hp 0).1
      have hkx₀ : Q.polarBilin k x₀ = 0 := by rw [hBs]; simpa using (hp 0).2
      have hDa₀ := hH3 a₀ x₀ ha₀N hx₀N hQa₀ ha₀x₀
      have h1 := hH3 (k + a₀) x₀ (by rw [mulVec_add, hk, ha₀N, add_zero]) hx₀N
        (by rw [quad_add, hQk, hQa₀, hka₀, zero_add, add_zero])
        (by rw [map_add, LinearMap.add_apply, hkx₀, ha₀x₀, zero_add])
      rw [mulVec_add, hDa₀, add_zero] at h1
      exact h1
    · exact hH3 k (w 0) hk hwN hQk hkw

end Span

section RankTwo

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] [CharP K 2]
  {Q : QuadraticForm K (ι → K)}

omit [DecidableEq ι] [CharP K 2] in
theorem exists_eq_of_rank_two {N : Matrix ι ι K} (hrk : N.rank = 2) {x y : ι → K}
    (hli : LinearIndependent K ![N *ᵥ x, N *ᵥ y]) (v : ι → K) :
    ∃ s t : K, N *ᵥ v = s • (N *ᵥ x) + t • (N *ᵥ y) := by
  have hrange : Submodule.span K (Set.range ![N *ᵥ x, N *ᵥ y]) =
      LinearMap.range N.mulVecLin := by
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · rw [Submodule.span_le, Set.range_subset_iff]
      intro i
      fin_cases i
      · exact ⟨x, rfl⟩
      · exact ⟨y, rfl⟩
    · rw [finrank_span_eq_card hli, Fintype.card_fin]
      exact hrk.symm
  have hv : N *ᵥ v ∈ Submodule.span K (Set.range ![N *ᵥ x, N *ᵥ y]) := by
    rw [hrange]
    exact ⟨v, rfl⟩
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hv
  rw [Fin.sum_univ_two] at hc
  exact ⟨c 0, c 1, by simpa using hc.symm⟩

omit [CharP K 2] in
theorem eq_of_fix_typeA_rank_two (hQ : Q.polarBilin.Nondegenerate) {N : Matrix ι ι K}
    (hadj : ∀ u v, Q.polarBilin (N *ᵥ u) v = Q.polarBilin u (N *ᵥ v))
    (hrk : N.rank = 2) (hsing : ∀ v, Q (N *ᵥ v) = 0)
    (halt : ∀ v, Q.polarBilin v (N *ᵥ v) = 0) {X : Matrix ι ι K}
    (hXQ : ∀ v, Q (X *ᵥ v) = Q v) (hfix : ∀ k, N *ᵥ k = 0 → X *ᵥ k = k) :
    ∃ c : K, X = 1 + c • N := by
  have hBs : ∀ a b, Q.polarBilin a b = Q.polarBilin b a := polarBilin_comm Q
  have hXB := polarBilin_mulVec_of_isometry Q hXQ
  have hpair : ∀ w, N *ᵥ w ≠ 0 → ∃ x, Q.polarBilin w (N *ᵥ x) = 1 ∧
      Q.polarBilin x (N *ᵥ w) = 1 ∧
      (∀ a b : K, a • (N *ᵥ w) + b • (N *ᵥ x) = 0 → a = 0 ∧ b = 0) ∧
      ∀ v, N *ᵥ v = Q.polarBilin v (N *ᵥ x) • (N *ᵥ w) +
        Q.polarBilin v (N *ᵥ w) • (N *ᵥ x) := by
    intro w hw
    obtain ⟨x, hx⟩ := exists_polarBilin_eq_one hQ hw
    have hwx : Q.polarBilin w (N *ᵥ x) = 1 := by rw [← hadj, hBs, hx]
    have hli : ∀ a b : K, a • (N *ᵥ w) + b • (N *ᵥ x) = 0 → a = 0 ∧ b = 0 := by
      intro a b hab
      have h1 := congrArg (Q.polarBilin w) hab
      have h2 := congrArg (Q.polarBilin x) hab
      simp only [map_add, map_smul, smul_eq_mul, halt, hwx, hx, map_zero, mul_zero, mul_one,
        zero_add, add_zero] at h1 h2
      exact ⟨h2, h1⟩
    refine ⟨x, hwx, hx, hli, fun v => ?_⟩
    obtain ⟨s, t, hst⟩ := exists_eq_of_rank_two hrk (LinearIndependent.pair_iff.mpr hli) v
    have h1 := congrArg (fun y => Q.polarBilin y x) hst
    have h2 := congrArg (fun y => Q.polarBilin y w) hst
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      smul_eq_mul] at h1 h2
    rw [hadj v x, hadj w x, hadj x x, hwx, halt x, mul_one, mul_zero, add_zero] at h1
    rw [hadj v w, hadj w w, hadj x w, halt w, hx, mul_zero, mul_one, zero_add] at h2
    rw [hst, h1, h2]
  have hmem : ∀ w, N *ᵥ w ≠ 0 → ∃ c : K, (X - 1) *ᵥ w = c • (N *ᵥ w) := by
    intro w hw
    obtain ⟨x, hwx, hxw, -, hdec⟩ := hpair w hw
    obtain ⟨r, hr⟩ : ∃ r, r = (X - 1) *ᵥ w := ⟨_, rfl⟩
    rw [← hr]
    have hXw : X *ᵥ w = w + r := by rw [hr, sub_mulVec, one_mulVec, add_sub_cancel]
    have hrk0 : ∀ k, N *ᵥ k = 0 → Q.polarBilin r k = 0 := fun k hk => by
      have h1 := hXB w k
      rw [hfix k hk, hXw, map_add, LinearMap.add_apply, add_eq_left] at h1
      exact h1
    have hr2 : r = Q.polarBilin r x • (N *ᵥ w) + Q.polarBilin r w • (N *ᵥ x) := by
      rw [← sub_eq_zero]
      refine hQ.1 _ fun v => ?_
      obtain ⟨k, hkdef⟩ : ∃ k, k = v - Q.polarBilin v (N *ᵥ x) • w -
          Q.polarBilin v (N *ᵥ w) • x := ⟨_, rfl⟩
      have hk : N *ᵥ k = 0 := by
        rw [hkdef, mulVec_sub, mulVec_sub, mulVec_smul, mulVec_smul, hdec v, sub_sub, sub_self]
      have hv : v = k + Q.polarBilin v (N *ᵥ x) • w + Q.polarBilin v (N *ᵥ w) • x := by
        rw [hkdef]; abel
      have hrk' := hrk0 _ hk
      have hNk : ∀ y, Q.polarBilin (N *ᵥ y) k = 0 := fun y => by
        rw [hadj, hk, map_zero]
      have hww : Q.polarBilin (N *ᵥ w) w = 0 := by rw [hBs]; exact halt w
      have hxx : Q.polarBilin (N *ᵥ x) x = 0 := by rw [hBs]; exact halt x
      have hwx' : Q.polarBilin (N *ᵥ w) x = 1 := by rw [hBs]; exact hxw
      have hxw' : Q.polarBilin (N *ᵥ x) w = 1 := by rw [hBs]; exact hwx
      rw [hv]
      simp only [map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply,
        LinearMap.smul_apply, smul_eq_mul, hrk', hNk, hww, hxx, hwx', hxw']
      ring
    have hQr : Q r = 0 := by
      rw [hr2, ← mulVec_smul, ← mulVec_smul, ← mulVec_add, hsing]
    have hwr : Q.polarBilin r w = 0 := by
      have h1 := hXQ w
      rw [hXw, quad_add, hQr, add_zero, add_eq_left, hBs] at h1
      exact h1
    refine ⟨Q.polarBilin r x, ?_⟩
    calc r = Q.polarBilin r x • (N *ᵥ w) + Q.polarBilin r w • (N *ᵥ x) := hr2
      _ = Q.polarBilin r x • (N *ᵥ w) := by rw [hwr, zero_smul, add_zero]
  obtain ⟨y₀, hy₀⟩ : ∃ y₀, N *ᵥ y₀ ≠ 0 := by
    by_contra! h
    have hN0 : N = 0 := Matrix.ext_iff_mulVec.mpr fun v => by rw [h v, zero_mulVec]
    rw [hN0, Matrix.rank_zero] at hrk
    exact absurd hrk (by norm_num)
  obtain ⟨x₀, -, -, hli, -⟩ := hpair y₀ hy₀
  obtain ⟨c, hc⟩ := exists_eq_smul_of_mulVec_mem hli hmem
  exact ⟨c, by rw [← hc, add_sub_cancel]⟩

theorem eq_of_fix_typeC_rank_two [Finite K] (hQ : Q.polarBilin.Nondegenerate)
    {N : Matrix ι ι K} (hN : N * N = 0) (hiso : ∀ v, Q (v + N *ᵥ v) = Q v) (hrk : N.rank = 2)
    {z : ι → K} (hz : ∀ v, Q.polarBilin v z ^ 2 = Q (N *ᵥ v)) (hz0 : z ≠ 0) (hQz : Q z = 0)
    {X : Matrix ι ι K} (hXQ : ∀ v, Q (X *ᵥ v) = Q v) (hfix : ∀ k, N *ᵥ k = 0 → X *ᵥ k = k)
    (hev : Even (X - 1).rank) : ∃ s t : K, X = 1 + s • N + t • polMat Q z z := by
  have hBs : ∀ a b, Q.polarBilin a b = Q.polarBilin b a := polarBilin_comm Q
  have hadj := polar_mulVec_adj Q hN hiso
  have hNN : ∀ a, N *ᵥ (N *ᵥ a) = 0 := fun a => by rw [mulVec_mulVec, hN, zero_mulVec]
  have hXB := polarBilin_mulVec_of_isometry Q hXQ
  obtain ⟨y₀, hy₀⟩ := exists_mulVec_eq_of_sqrt_vector hQ hN hiso hz
  have hy₀z : Q.polarBilin y₀ z = 0 := by
    have h1 := hz y₀
    rwa [hy₀, hQz, pow_eq_zero_iff two_ne_zero] at h1
  obtain ⟨x₁, hx₁⟩ := exists_polarBilin_eq_one hQ hz0
  obtain ⟨y₁, hy₁⟩ : ∃ y₁, y₁ = N *ᵥ x₁ := ⟨_, rfl⟩
  have hQy₁ : Q y₁ = 1 := by rw [hy₁, ← hz, hx₁, one_pow]
  have hy₁y₀ : Q.polarBilin y₁ y₀ = 1 := by rw [hy₁, hadj, hy₀, hx₁]
  have hNy₁ : N *ᵥ y₁ = 0 := by rw [hy₁]; exact hNN x₁
  have hker : ∀ v, Q.polarBilin v z = 0 → Q.polarBilin v y₁ = 0 → N *ᵥ v = 0 :=
    fun v hvz hvy => mulVec_eq_zero_of_rank_two hQ hN hiso hrk hz hz0 hQz hx₁ hvz (hy₁ ▸ hvy)
  have hkz : ∀ k, N *ᵥ k = 0 → Q.polarBilin k z = 0 := fun k hk => by
    have h1 := hz k
    rwa [hk, QuadraticMap.map_zero, pow_eq_zero_iff two_ne_zero] at h1
  have hky : ∀ k, N *ᵥ k = 0 → Q.polarBilin k y₁ = 0 := fun k hk => by
    rw [hy₁, ← hadj, hk, map_zero, LinearMap.zero_apply]
  have hzz : Q.polarBilin z z = 0 := TypeCData.pol_self z
  have hy₁y₁ : Q.polarBilin y₁ y₁ = 0 := TypeCData.pol_self y₁
  have hy₁z : Q.polarBilin y₁ z = 0 := hkz y₁ hNy₁
  have hzy₁ : Q.polarBilin z y₁ = 0 := by rw [hBs]; exact hy₁z
  have hx₁y₁ : Q.polarBilin x₁ y₁ = 1 := by
    rw [hy₁, polar_self_mulVec Q hiso, ← hz, hx₁, one_pow]
  obtain ⟨d, hd⟩ : ∃ d, d = x₁ + y₀ := ⟨_, rfl⟩
  have hdz : Q.polarBilin d z = 1 := by
    rw [hd, map_add, LinearMap.add_apply, hx₁, hy₀z, add_zero]
  have hdy₁ : Q.polarBilin d y₁ = 0 := by
    rw [hd, map_add, LinearMap.add_apply, hx₁y₁, hBs y₀ y₁, hy₁y₀, CharTwo.add_self_eq_zero]
  have hzd : Q.polarBilin z d = 1 := by rw [hBs]; exact hdz
  have hy₁d : Q.polarBilin y₁ d = 0 := by rw [hBs]; exact hdy₁
  have hzy₀ : Q.polarBilin z y₀ = 0 := by rw [hBs]; exact hy₀z
  have hy₀y₁ : Q.polarBilin y₀ y₁ = 1 := by rw [hBs]; exact hy₁y₀
  have hNd : N *ᵥ d = y₁ + z := by rw [hd, mulVec_add, hy₀, ← hy₁]
  have hdec : ∀ v, N *ᵥ (v - Q.polarBilin v z • d - Q.polarBilin v y₁ • y₀) = 0 := by
    intro v
    refine hker _ ?_ ?_
    · simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hdz,
        hy₀z]
      ring
    · simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hdy₁,
        hy₀y₁]
      ring
  have hY : ∀ v, (X - 1) *ᵥ v = Q.polarBilin v z • ((X - 1) *ᵥ d) +
      Q.polarBilin v y₁ • ((X - 1) *ᵥ y₀) := fun v => by
    have h1 : (X - 1) *ᵥ (v - Q.polarBilin v z • d - Q.polarBilin v y₁ • y₀) = 0 := by
      rw [sub_mulVec, one_mulVec, hfix _ (hdec v), sub_self]
    rw [mulVec_sub, mulVec_sub, mulVec_smul, mulVec_smul] at h1
    linear_combination (norm := module) h1
  have hperp : ∀ r, (∀ k, N *ᵥ k = 0 → Q.polarBilin r k = 0) →
      r = Q.polarBilin r d • z + Q.polarBilin r y₀ • y₁ := by
    intro r hr
    rw [← sub_eq_zero]
    refine hQ.1 _ fun v => ?_
    obtain ⟨k, hkdef⟩ : ∃ k, k = v - Q.polarBilin v z • d - Q.polarBilin v y₁ • y₀ := ⟨_, rfl⟩
    have hk : N *ᵥ k = 0 := by rw [hkdef]; exact hdec v
    have hv : v = k + Q.polarBilin v z • d + Q.polarBilin v y₁ • y₀ := by rw [hkdef]; abel
    have hzk : Q.polarBilin z k = 0 := by rw [hBs]; exact hkz _ hk
    have hy₁k : Q.polarBilin y₁ k = 0 := by rw [hBs]; exact hky _ hk
    have hrk' := hr _ hk
    rw [hv]
    simp only [map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, smul_eq_mul, hrk', hzk, hy₁k, hzd, hzy₀, hy₁d, hy₁y₀]
    ring
  have hYperp : ∀ v k, N *ᵥ k = 0 → Q.polarBilin ((X - 1) *ᵥ v) k = 0 := fun v k hk => by
    have h1 := hXB v k
    rw [hfix k hk] at h1
    rw [sub_mulVec, one_mulVec, map_sub, LinearMap.sub_apply, h1, sub_self]
  obtain ⟨s, δ, hYy₀⟩ : ∃ s δ : K, (X - 1) *ᵥ y₀ = s • z + δ • y₁ :=
    ⟨_, _, hperp _ (hYperp y₀)⟩
  obtain ⟨t, s', hYd⟩ : ∃ t s' : K, (X - 1) *ᵥ d = t • z + s' • y₁ :=
    ⟨_, _, hperp _ (hYperp d)⟩
  have hXy₀ : X *ᵥ y₀ = y₀ + (s • z + δ • y₁) := by
    rw [← hYy₀, sub_mulVec, one_mulVec, add_sub_cancel]
  have hXd : X *ᵥ d = d + (t • z + s' • y₁) := by
    rw [← hYd, sub_mulVec, one_mulVec, add_sub_cancel]
  have hss : s' = s := by
    have h1 := hXB d y₀
    rw [hXd, hXy₀] at h1
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hdz,
      hdy₁, hzy₀, hzz, hzy₁, hy₁y₀, hy₁z, hy₁y₁] at h1
    linear_combination h1 - s * CharTwo.two_eq_zero (R := K)
  have hδ : δ ^ 2 = δ := by
    have h1 := hXQ y₀
    rw [hXy₀, quad_add, quad_add, QuadraticMap.map_smul, QuadraticMap.map_smul, hQz,
      hQy₁] at h1
    simp only [map_add, map_smul, LinearMap.smul_apply, smul_eq_mul, hy₀z, hy₀y₁, hzy₁] at h1
    linear_combination h1 - δ * CharTwo.two_eq_zero (R := K)
  have hts : t = s ^ 2 := by
    have h1 := hXQ d
    rw [hXd, quad_add, quad_add, QuadraticMap.map_smul, QuadraticMap.map_smul, hQz,
      hQy₁, hss] at h1
    simp only [map_add, map_smul, LinearMap.smul_apply, smul_eq_mul, hdz, hdy₁, hzy₁] at h1
    linear_combination h1 - s ^ 2 * CharTwo.two_eq_zero (R := K)
  have hXv : ∀ v, (X - 1) *ᵥ v = Q.polarBilin v z • (s ^ 2 • z + s • y₁) +
      Q.polarBilin v y₁ • (s • z + δ • y₁) := fun v => by rw [hY v, hYd, hYy₀, hss, hts]
  have hNv : ∀ v, N *ᵥ v = Q.polarBilin v z • (y₁ + z) + Q.polarBilin v y₁ • z := fun v => by
    have h1 := hdec v
    rw [mulVec_sub, mulVec_sub, mulVec_smul, mulVec_smul, hNd, hy₀] at h1
    linear_combination (norm := module) h1
  have hδ01 : δ = 0 ∨ δ = 1 := by
    have h1 : δ * (δ - 1) = 0 := by linear_combination hδ
    rcases mul_eq_zero.mp h1 with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)
  rcases hδ01 with hδ0 | hδ1
  · refine ⟨s, s ^ 2 - s, Matrix.ext_iff_mulVec.mpr fun v => ?_⟩
    have h1 := hXv v
    rw [hδ0, zero_smul, add_zero, sub_mulVec, one_mulVec] at h1
    rw [add_mulVec, add_mulVec, one_mulVec, smul_mulVec, smul_mulVec, hNv, polMat_mulVec]
    linear_combination (norm := module) h1
  · exfalso
    obtain ⟨c, hc⟩ : ∃ c, c = y₁ + s • z := ⟨_, rfl⟩
    have hc0 : c ≠ 0 := fun h => by
      have h1 := congrArg (fun y => Q.polarBilin y y₀) h
      simp only [hc, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
        hy₁y₀, hzy₀, mul_zero, add_zero, map_zero, LinearMap.zero_apply] at h1
      exact one_ne_zero h1
    have hXc : X - 1 = polMat Q c c := Matrix.ext_iff_mulVec.mpr fun v => by
      rw [hXv v, hδ1, polMat_mulVec, hc]
      simp only [map_add, map_smul, smul_eq_mul]
      module
    rw [hXc, rank_polMat_self hQ hc0] at hev
    exact Nat.not_even_one hev

end RankTwo

section Groups

variable {G : Type} [Group G] {A : Subgroup G} {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
  [Finite K] [CharP K 2]

theorem noPairOrbit_rankTwo_orth_two (Q : QuadraticForm K (ι → K)) (q : (ι → K) → K)
    (hq : ⇑Q = q) (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (ι → K), finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hK : Nat.card K = 2) (hι : 7 ≤ Fintype.card ι)
    {e : rankTwoQuot A ≃* StatedProj (StatedOmega q)} (hZ : Odd (Nat.card (center ↥A)))
    {p : G} (hp2 : orderOf p = 2) {M : GL ι K} (hpM : Represents e p M) (hM2 : orderOf M = 2)
    (hrk : commRank M = 2) : NoPairOrbit A p := by
  subst hq
  have hBs : ∀ a b, Q.polarBilin a b = Q.polarBilin b a := polarBilin_comm Q
  have hp2' : p ^ 2 = 1 := by rw [← hp2]; exact pow_orderOf_eq_one p
  have hM2' : M ^ 2 = 1 := by rw [← hM2]; exact pow_orderOf_eq_one M
  have hp1 : p ≠ 1 := fun h => by rw [h, orderOf_one] at hp2; omega
  have hpp : p * p = 1 := by rw [← _root_.sq]; exact hp2'
  have hMQ := statedOmega_isometry hpM.2.1
  have hN : ((M : Matrix ι ι K) - 1) * ((M : Matrix ι ι K) - 1) = 0 := sub_one_mul_self hM2'
  have hiso : ∀ v, Q (v + ((M : Matrix ι ι K) - 1) *ᵥ v) = Q v := fun v => by
    rw [sub_mulVec, one_mulVec, add_sub_cancel]
    exact hMQ v
  obtain ⟨z, hz⟩ := exists_sqrt_vector Q hQ hN hiso
  have hQz : Q z = 0 :=
    quad_eq_zero_of_sqrt_vector hQ hMQ hN (even_commRank_of_mem_statedOmega Q hQ hpM.2.1) hz
  have hrk' : ((M : Matrix ι ι K) - 1).rank = 2 := hrk
  obtain ⟨N, hNdef⟩ : ∃ N, N = (M : Matrix ι ι K) - 1 := ⟨_, rfl⟩
  rw [← hNdef] at hN hiso hrk' hz
  have hMN : (M : Matrix ι ι K) = 1 + N := by rw [hNdef, add_sub_cancel]
  have hadj := polar_mulVec_adj Q hN hiso
  have hcomm : ∀ X : GL ι K, X * M = M * X → (X : Matrix ι ι K) * N = N * X := fun X hXM => by
    have h1 := congrArg (fun Y : GL ι K => (Y : Matrix ι ι K)) hXM
    simp only [Units.val_mul] at h1
    rw [hNdef, Matrix.mul_sub, Matrix.sub_mul, h1, Matrix.mul_one, Matrix.one_mul]
  intro u hu hu2 horb
  have hu2' : u * u = 1 := by rw [← _root_.sq]; exact hu2
  obtain ⟨U, hU⟩ := exists_represents e (mem_inf.mp hu).1
  have hUQ := statedOmega_isometry hU.2.1
  have hU2 : U ^ 2 = 1 := by
    have h1 := hU.pow 2
    rw [hu2] at h1
    obtain ⟨c, hc⟩ := (represents_one (e := e)).exists_scalar h1
    rw [hc, eq_one_of_units_of_card_eq_two hK c, map_one, one_mul]
  have hU2' : (U : Matrix ι ι K) * U = 1 := by
    have h1 := congrArg (fun Y : GL ι K => (Y : Matrix ι ι K)) hU2
    simpa [_root_.sq] using h1
  have hrot : ∀ a b, N *ᵥ a = 0 → N *ᵥ b = 0 → Q a = 1 → Q b = 1 → Q.polarBilin a b = 1 →
      (U : Matrix ι ι K) *ᵥ a = a := by
    intro a b ha hb hQa hQb hab
    have hTH : anisoRotGL hab ∈ StatedOmega ⇑Q := mem_statedOmega_of Q hQ hT
      (fun v => by rw [coe_anisoRotGL]; exact anisoRot_isometry hQa hQb hab v)
      (by rw [commRank, coe_anisoRotGL, rank_anisoRot_sub_one hab]; exact even_two)
    have hTM : anisoRotGL hab * M = M * anisoRotGL hab := Units.ext (by
      rw [Units.val_mul, Units.val_mul, coe_anisoRotGL, hMN, Matrix.mul_add, Matrix.add_mul,
        Matrix.mul_one, Matrix.one_mul, anisoRot_mul_eq hadj ha hb, mul_anisoRot_eq ha hb])
    obtain ⟨g, hg⟩ := exists_represents_of_mem (e := e) hTH
    have hgp : g * p = p * g := commute_of_represents hZ hg hpM hp2' hTM
    have hgC : g ∈ A ⊓ centralizer ({p} : Set G) :=
      mem_inf.mpr ⟨hg.1, mem_centralizer_singleton_iff.mpr hgp⟩
    have hgo : Odd (orderOf g) :=
      odd_orderOf_of_represents hZ hg (k := 3) ⟨1, rfl⟩ (anisoRotGL_pow_three hab)
    have hfix := fix_of_odd_orderOf hpp hp1 hgp hu2' hgo (horb g hgC)
    have hgu : g * u = u * g := by rw [← mul_inv_eq_iff_eq_mul.mp hfix]
    have hTU := hg.mul_comm_of_commute hU hU2 hgu
    rw [coe_anisoRotGL] at hTU
    exact (eq_of_commute_anisoRot hab hU2' hTU.symm).1
  have hfix : ∀ k, N *ᵥ k = 0 → (U : Matrix ι ι K) *ᵥ k = k := fun k hk => by
    have h := mulVec_eq_zero_of_anisotropic hK hQ hι hadj hrk' (D := (U : Matrix ι ι K) - 1)
      (fun a b ha hb hQa hQb hab => by
        rw [sub_mulVec, one_mulVec, hrot a b ha hb hQa hQb hab, sub_self]) hk
    rwa [sub_mulVec, one_mulVec, sub_eq_zero] at h
  by_cases hsing : ∀ v, Q (N *ᵥ v) = 0
  ·
    have halt : ∀ v, Q.polarBilin v (N *ᵥ v) = 0 := fun v => by
      rw [polar_self_mulVec Q hiso, hsing]
    obtain ⟨c, hc⟩ := eq_of_fix_typeA_rank_two hQ hadj hrk' hsing halt hUQ hfix
    refine central_of_commute_all hZ hpM hM2' hu2 hU fun X _ hXM => Units.ext ?_
    rw [Units.val_mul, Units.val_mul, hc, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
      Matrix.one_mul, Matrix.mul_smul, Matrix.smul_mul, hcomm X hXM]
  ·
    push Not at hsing
    have hzB : ∀ v, Q.polarBilin v z ^ 2 = Q.polarBilin v (N *ᵥ v) := fun v => by
      rw [polar_self_mulVec Q hiso]
      exact hz v
    have hz0 : z ≠ 0 := by
      rintro rfl
      obtain ⟨v, hv⟩ := hsing
      exact hv (by rw [← hz v, map_zero, zero_pow two_ne_zero])
    obtain ⟨s, t, hst⟩ := eq_of_fix_typeC_rank_two hQ hN hiso hrk' hz hz0 hQz hUQ hfix
      (even_commRank_of_mem_statedOmega Q hQ hU.2.1)
    have hPz : ∀ X : GL ι K, (∀ v, Q ((X : Matrix ι ι K) *ᵥ v) = Q v) → X * M = M * X →
        (X : Matrix ι ι K) * polMat Q z z = polMat Q z z * X := fun X hXQ hXM => by
      have hXB := polarBilin_mulVec_of_isometry Q hXQ
      have hXz := mulVec_sqrt_vector_of_commute_adj hQ hzB hXB (hcomm X hXM)
      have h1 := conj_polMat_self_of_polar hXB z
      rw [hXz] at h1
      calc (X : Matrix ι ι K) * polMat Q z z =
          X * polMat Q z z * ((X⁻¹ : GL ι K) : Matrix ι ι K) * X := by
            rw [Matrix.mul_assoc _ (((X⁻¹ : GL ι K) : Matrix ι ι K)), Units.inv_mul,
              Matrix.mul_one]
        _ = polMat Q z z * X := by rw [h1]
    refine central_of_commute_all hZ hpM hM2' hu2 hU fun X hX hXM => Units.ext ?_
    rw [Units.val_mul, Units.val_mul, hst, Matrix.mul_add, Matrix.mul_add, Matrix.add_mul,
      Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.smul_mul, hcomm X hXM, hPz X (statedOmega_isometry hX) hXM]

end Groups

end CFSG.ComponentClassification.RankTwoClassical
