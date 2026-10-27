module

public import CFSG.ClassicalGroups.Orthogonal.Eichler
public import CFSG.ClassicalGroups.Orthogonal.Hyperbolic
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.ClassicalGroups.Orthogonal.Small

open QuadraticMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem eq_zero_of_mem_perp_of_finrank_le_two [FiniteDimensional K V] (P : HypPair Q)
    (hdim : Module.finrank K V ≤ 2) {x : V} (hx : x ∈ P.perp) : x = 0 := by
  by_contra hx0
  obtain ⟨hxe, hxf⟩ := HypPair.mem_perp.mp hx
  have hli : LinearIndependent K ![P.e, P.f, x] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fin.sum_univ_three] at hg
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] at hg
    have h1 := congrArg (fun z => polar Q z P.f) hg
    have h2 := congrArg (fun z => polar Q z P.e) hg
    simp only [polar_add_left, polar_smul_left_eq, polar_zero_left, P.polar_ef, P.polar_ee,
      P.polar_ff, P.polar_fe, polar_comm Q x P.f, polar_comm Q x P.e, hxe, hxf, mul_zero, mul_one,
      add_zero, zero_add] at h1 h2
    rw [h1, h2, zero_smul, zero_smul, zero_add, zero_add] at hg
    have hg2 : g 2 = 0 := (smul_eq_zero.mp hg).resolve_right hx0
    intro i
    fin_cases i
    · exact h1
    · exact h2
    · exact hg2
  have := hli.fintype_card_le_finrank
  simp at this
  omega

theorem eichler_eq_one_of_finrank_le_two [FiniteDimensional K V]
    (hQ : (polarBilin Q).Nondegenerate) (hdim : Module.finrank K V ≤ 2) {u w : V} (hu : Q u = 0)
    (hw : polar Q u w = 0) : eichler Q u w = 1 := by
  by_cases hu0 : u = 0
  · rw [hu0, eichler_zero_left]
  obtain ⟨P, rfl⟩ := exists_hypPair hQ hu hu0
  have hproj : P.proj w = 0 := eq_zero_of_mem_perp_of_finrank_le_two P hdim (P.proj_mem_perp w)
  have hwe : polar Q w P.e = 0 := by rw [polar_comm, hw]
  have hw' : w = polar Q w P.f • P.e := by
    have := P.eq_add_proj w
    rw [hproj, add_zero, hwe, zero_smul, add_zero] at this
    exact this
  have h1 := eichler_add_smul_self P.Q_e (0 : V) (polar Q w P.f)
  rw [zero_add, eichler_zero_right] at h1
  rw [hw', h1]

theorem eq_one_of_pow_three_eq_one [FiniteDimensional K V] (hK : (3 : K) = 0) (h2 : (2 : K) ≠ 0)
    (hQ : (polarBilin Q).Nondegenerate) (hdim : Module.finrank K V ≤ 2) {μ : V ≃ₗ[K] V}
    (hμ : μ ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (h3 : μ ^ 3 = 1) : μ = 1 := by
  have hμ3 : ∀ x, μ (μ (μ x)) = x := fun x => by
    have := congrArg (fun g : V ≃ₗ[K] V => g x) h3
    simpa [pow_succ, LinearEquiv.mul_apply] using this
  set N : V →ₗ[K] V := (μ : V →ₗ[K] V) - LinearMap.id with hN
  have hNx : ∀ x, N x = μ x - x := fun x => rfl
  have hN3 : ∀ x, N (N (N x)) = 0 := fun x => by
    have h1 : N (N (N x)) = (3 : K) • (μ x - μ (μ x)) := by
      simp only [hNx, map_sub, hμ3]
      module
    rw [h1, hK, zero_smul]
  have hN2 : ∀ x, N (N x) = 0 := by
    intro x
    by_contra hy
    have hli : LinearIndependent K ![x, N x, N (N x)] := by
      rw [Fintype.linearIndependent_iff]
      intro g hg
      rw [Fin.sum_univ_three] at hg
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons] at hg
      have h1 := congrArg N hg
      simp only [map_add, map_smul, map_zero, hN3, smul_zero, add_zero] at h1
      have h2 := congrArg N h1
      simp only [map_add, map_smul, map_zero, hN3, smul_zero, add_zero] at h2
      have hg0 : g 0 = 0 := (smul_eq_zero.mp h2).resolve_right hy
      rw [hg0, zero_smul, zero_add] at h1
      have hg1 : g 1 = 0 := (smul_eq_zero.mp h1).resolve_right hy
      rw [hg0, hg1, zero_smul, zero_smul, zero_add, zero_add] at hg
      have hg2 : g 2 = 0 := (smul_eq_zero.mp hg).resolve_right hy
      intro i
      fin_cases i
      · exact hg0
      · exact hg1
      · exact hg2
    have := hli.fintype_card_le_finrank
    simp at this
    omega
  have hN1 : ∀ x, N x = 0 := by
    intro x
    by_contra hv
    set v := N x with hvdef
    have hNv : N v = 0 := hN2 x
    have hμv : μ v = v := by
      have := hNx v
      rw [hNv] at this
      exact (sub_eq_zero.mp this.symm)
    have hμx : μ x = x + v := by
      have := hNx x
      rw [← hvdef] at this
      rw [this]
      abel
    have hQx : Q (x + v) = Q x := by
      have := map_of_mem hμ x
      rw [hμx] at this
      exact this
    have hQx2 : Q (x + v + v) = Q (x + v) := by
      have := map_of_mem hμ (x + v)
      rw [μ.map_add, hμx, hμv] at this
      exact this
    rw [QuadraticMap.map_add Q x v] at hQx
    rw [QuadraticMap.map_add Q (x + v) v, QuadraticMap.map_add Q x v, polar_add_left,
      polar_self_eq_two_mul] at hQx2
    have hQv : Q v = 0 := by
      have h5 : 2 * Q v = 0 := by linear_combination hQx2 - hQx
      exact (mul_eq_zero.mp h5).resolve_left h2
    have hxv : polar Q x v = 0 := by linear_combination hQx - hQv
    have hvv : polar Q v v = 0 := by rw [polar_self_eq_two_mul, hQv, mul_zero]
    obtain ⟨u, hu⟩ := exists_polar_ne_zero hQ hv
    have hli : LinearIndependent K ![x, v, u] := by
      rw [Fintype.linearIndependent_iff]
      intro g hg
      rw [Fin.sum_univ_three] at hg
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons] at hg
      have h1 := congrArg (fun z => polar Q z v) hg
      simp only [polar_add_left, polar_smul_left_eq, polar_zero_left, hxv, hvv, mul_zero,
        zero_add] at h1
      have hg2 : g 2 = 0 := by
        have h6 : g 2 * polar Q u v = 0 := by simpa using h1
        have hu' : polar Q u v ≠ 0 := by rwa [polar_comm]
        exact (mul_eq_zero.mp h6).resolve_right hu'
      rw [hg2, zero_smul, add_zero] at hg
      have h7 := congrArg N hg
      simp only [map_add, map_smul, map_zero, hNv, smul_zero, add_zero] at h7
      have hg0 : g 0 = 0 := (smul_eq_zero.mp h7).resolve_right hv
      rw [hg0, zero_smul, zero_add] at hg
      have hg1 : g 1 = 0 := (smul_eq_zero.mp hg).resolve_right hv
      intro i
      fin_cases i
      · exact hg0
      · exact hg1
      · exact hg2
    have := hli.fintype_card_le_finrank
    simp at this
    omega
  exact LinearEquiv.ext fun x => by
    have := hN1 x
    rw [hNx, sub_eq_zero] at this
    exact this

theorem natCard_linearEquiv_dvd_of_finrank_le_two [Finite K] [FiniteDimensional K V]
    (hK : Nat.card K = 3) (hdim : Module.finrank K V ≤ 2) : Nat.card (V ≃ₗ[K] V) ∣ 48 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hq : Fintype.card K = 3 := by rw [← Nat.card_eq_fintype_card]; exact hK
  set b := Module.finBasis K V with hb
  let e : (V ≃ₗ[K] V) ≃* Matrix.GeneralLinearGroup (Fin (Module.finrank K V)) K :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv K V).symm.trans
      (Units.mapEquiv (LinearMap.toMatrixAlgEquiv b).toRingEquiv.toMulEquiv)
  rw [Nat.card_congr e.toEquiv, Matrix.card_GL_field, hq]
  obtain ⟨n, hn⟩ : ∃ n, Module.finrank K V = n := ⟨_, rfl⟩
  rw [hn] at hdim ⊢
  interval_cases n
  · simp
  · simp
  · simp [Fin.prod_univ_two]

theorem pow_sixteen_eq_one_of_finrank_le_two [Finite K] [FiniteDimensional K V]
    (hK : Nat.card K = 3) (hQ : (polarBilin Q).Nondegenerate) (hdim : Module.finrank K V ≤ 2)
    {ν : V ≃ₗ[K] V} (hν : ν ∈ TauCeti.QuadraticMap.orthogonalGroup Q) : ν ^ 16 = 1 := by
  have h3 : (3 : K) = 0 := by
    have : Fintype K := Fintype.ofFinite K
    have h := Nat.cast_card_eq_zero K
    rw [← Nat.card_eq_fintype_card, hK] at h
    exact_mod_cast h
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun g : V ≃ₗ[K] V => (g : V → V))
    DFunLike.coe_injective
  have h2 : (2 : K) ≠ 0 := by
    intro h
    have : (1 : K) = 0 := by linear_combination h3 - h
    exact one_ne_zero this
  have hdvd : orderOf ν ∣ 48 :=
    (orderOf_dvd_natCard ν).trans (natCard_linearEquiv_dvd_of_finrank_le_two hK hdim)
  have hcop : Nat.Coprime (orderOf ν) 3 := by
    by_contra hnot
    have h3d : 3 ∣ orderOf ν := by
      by_contra hn
      exact hnot ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hn).symm
    obtain ⟨k, hk⟩ := h3d
    have hpos : 0 < orderOf ν := orderOf_pos ν
    set μ := ν ^ k with hμ
    have hμO : μ ∈ TauCeti.QuadraticMap.orthogonalGroup Q := Subgroup.pow_mem _ hν k
    have hμ3 : μ ^ 3 = 1 := by
      rw [hμ, ← pow_mul, mul_comm, ← hk, pow_orderOf_eq_one]
    have hμ1 := eq_one_of_pow_three_eq_one h3 h2 hQ hdim hμO hμ3
    have hdk : orderOf ν ∣ k := orderOf_dvd_of_pow_eq_one hμ1
    have hkpos : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · rw [h0, mul_zero] at hk
        omega
      · exact h0
    have := Nat.le_of_dvd hkpos hdk
    omega
  have h16 : orderOf ν ∣ 16 := by
    have : orderOf ν ∣ 16 * 3 := hdvd
    exact hcop.dvd_of_dvd_mul_right this
  exact orderOf_dvd_iff_pow_eq_one.mp h16

end CFSG.ClassicalGroups.Orthogonal.Small
