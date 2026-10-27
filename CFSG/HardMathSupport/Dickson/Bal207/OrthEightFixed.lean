module

public import CFSG.HardMathSupport.Dickson.Bal207.OrthEightBasic

public section

namespace CFSG.HardMathSupport.Dickson.Bal207.OrthEight

open Polynomial Module QuadraticMap CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.GroupTheory.WeirSylow CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.OrthogonalInvolutions
  CFSG.RankThree.Classical2

section Plane

variable {K : Type} [Field K] {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  {R : QuadraticForm K W}

theorem eq_one_of_sq_eq_one_of_dicksonHom [CharP K 2] (hR : R.polarBilin.Nondegenerate)
    (h2 : finrank K W = 2) {t : TauCeti.QuadraticMap.orthogonalGroup R} (ht : t ^ 2 = 1)
    (hδ : dicksonHom R hR t = 1) : t = 1 := by
  have h2K : (2 : K) = 0 := CharP.cast_eq_zero K 2
  set T : W ≃ₗ[K] W := (t : W ≃ₗ[K] W) with hT
  have hTT : ∀ v, T (T v) = v := fun v => by
    have := congrArg (fun g : TauCeti.QuadraticMap.orthogonalGroup R => (g : W ≃ₗ[K] W) v) ht
    simpa [pow_two] using this
  have hnil : ∀ v, T (T v - v) - (T v - v) = 0 := fun v => by
    calc T (T v - v) - (T v - v) = (v - T v) - (T v - v) := by rw [map_sub, hTT]
      _ = (2 : K) • (v - T v) := by module
      _ = 0 := by rw [h2K, zero_smul]
  obtain ⟨n, hn⟩ : Even (finrank K (commSpace T)) :=
    even_finrank_commSpace_of_dicksonHom_eq_one hR hδ
  have hle : finrank K (commSpace T) ≤ 2 := (Submodule.finrank_le _).trans h2.le
  have hfix : ∀ u, T u = u := by
    rcases (show finrank K (commSpace T) = 0 ∨ finrank K (commSpace T) = 2 by omega) with h0 | h2c
    · have hbot : commSpace T = ⊥ := Submodule.finrank_eq_zero.mp h0
      intro u
      have hu := sub_mem_commSpace T u
      rw [hbot, Submodule.mem_bot, sub_eq_zero] at hu
      exact hu
    · have htop : commSpace T = ⊤ := Submodule.eq_top_of_finrank_eq (h2c.trans h2.symm)
      intro u
      have hu : u ∈ commSpace T := by
        rw [htop]
        exact Submodule.mem_top
      obtain ⟨u', rfl⟩ := mem_commSpace.mp hu
      exact sub_eq_zero.mp (hnil u')
  exact Subtype.ext (LinearEquiv.ext hfix)

theorem eq_one_of_sq_eq_one_of_commute [CharP K 2] (hR : R.polarBilin.Nondegenerate)
    (h2 : finrank K W = 2) {t u : TauCeti.QuadraticMap.orthogonalGroup R} (ht : t ^ 2 = 1)
    (hu : u ^ 3 = 1) (hu1 : u ≠ 1) (htu : t * u = u * t) : t = 1 := by
  by_cases hδ : dicksonHom R hR t = 1
  · exact eq_one_of_sq_eq_one_of_dicksonHom hR h2 ht hδ
  exfalso
  have hδu : dicksonHom R hR u = 1 := dicksonHom_eq_one_of_pow_eq_one hR ⟨1, rfl⟩ hu
  have hδut : dicksonHom R hR (u * t) ≠ 1 := by rwa [map_mul, hδu, one_mul]
  have hodd : finrank K (commSpace ((u * t : TauCeti.QuadraticMap.orthogonalGroup R) :
      W ≃ₗ[K] W)) = 1 := by
    have hle : finrank K (commSpace ((u * t : TauCeti.QuadraticMap.orthogonalGroup R) :
        W ≃ₗ[K] W)) ≤ 2 := (Submodule.finrank_le _).trans h2.le
    by_contra hne1
    apply hδut
    have hev : Even (finrank K (commSpace ((u * t : TauCeti.QuadraticMap.orthogonalGroup R) :
        W ≃ₗ[K] W))) := by
      rcases (show finrank K (commSpace ((u * t : TauCeti.QuadraticMap.orthogonalGroup R) :
          W ≃ₗ[K] W)) = 0 ∨ finrank K (commSpace ((u * t : TauCeti.QuadraticMap.orthogonalGroup R) :
          W ≃ₗ[K] W)) = 2 by omega) with h | h
      · rw [h]
        exact ⟨0, rfl⟩
      · rw [h]
        exact ⟨1, rfl⟩
    rw [dicksonHom_apply, ZMod.natCast_eq_zero_iff_even.mpr hev, ofAdd_zero]
  have hsq : (u * t) * (u * t) = 1 :=
    Subtype.ext (mul_self_eq_one_of_finrank_commSpace_eq_one hR (u * t).2 hodd)
  have hu2 : u ^ 2 = 1 := by
    have : (u * t) * (u * t) = u ^ 2 * t ^ 2 := by
      calc (u * t) * (u * t) = u * (t * u) * t := by simp only [mul_assoc]
        _ = u * (u * t) * t := by rw [htu]
        _ = u ^ 2 * t ^ 2 := by simp only [pow_two, mul_assoc]
    rw [this, ht, mul_one] at hsq
    exact hsq
  apply hu1
  calc u = u ^ 3 * (u ^ 2)⁻¹ := by group
    _ = 1 := by rw [hu, hu2, inv_one, mul_one]

theorem sq_eq_one_of_coprime_of_card_eighteen {G : Type*} [Group G] (hcard : Nat.card G = 18)
    {t : G} (ht : Nat.Coprime 3 (orderOf t)) : t ^ 2 = 1 := by
  have h18 : orderOf t ∣ 9 * 2 := by
    have := orderOf_dvd_natCard t
    rwa [hcard] at this
  have h9 : Nat.Coprime (orderOf t) 9 := by simpa using (Nat.Coprime.pow_left 2 ht).symm
  exact orderOf_dvd_iff_pow_eq_one.mp (h9.dvd_of_dvd_mul_left h18)

end Plane

section Orders

variable {K : Type} [Field K] [Finite K] {W : Type} [AddCommGroup W] [Module K W]
  [FiniteDimensional K W] {R : QuadraticForm K W}

theorem natCard_orthogonalGroup_two_minus (hK : Nat.card K = 8)
    (hR : (polarBilin R).Nondegenerate) (h2 : finrank K W = 2) (hminus : ¬ IsPlusType R) :
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup R) = 18 := by
  have hq : ((Nat.card K : ℕ) : ℤ) = 8 := by exact_mod_cast hK
  have h := natCard_orthogonalGroup_of_type hR (m := 0) (by omega) (ε := -1)
    (Or.inr ⟨rfl, hminus⟩)
  rw [hq, Finset.Icc_eq_empty_of_lt (by norm_num : (0 : ℕ) < 1), Finset.prod_empty] at h
  have h18 : (Nat.card (TauCeti.QuadraticMap.orthogonalGroup R) : ℤ) = 18 := by
    rw [h]
    norm_num
  exact_mod_cast h18

theorem three_dvd_natCard_orthogonalGroup (hK : Nat.card K = 8)
    (hR : (polarBilin R).Nondegenerate) {m : ℕ} (hdim : finrank K W = 2 * (m + 1))
    (h : 1 ≤ m ∨ ¬ IsPlusType R) :
    3 ∣ Nat.card (TauCeti.QuadraticMap.orthogonalGroup R) := by
  have hq : ((Nat.card K : ℕ) : ℤ) = 8 := by exact_mod_cast hK
  have hO : ∀ ε : ℤ, ((ε = 1 ∧ IsPlusType R) ∨ (ε = -1 ∧ ¬ IsPlusType R)) →
      (3 : ℤ) ∣ (Nat.card (TauCeti.QuadraticMap.orthogonalGroup R) : ℤ) := by
    intro ε hε
    rw [natCard_orthogonalGroup_of_type hR hdim hε, hq]
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · have hminus : ¬ IsPlusType R := h.resolve_left (by norm_num)
      rcases hε with ⟨-, hp⟩ | ⟨rfl, -⟩
      · exact absurd hp hminus
      · rw [Finset.Icc_eq_empty_of_lt (by norm_num : (0 : ℕ) < 1), Finset.prod_empty]
        norm_num
    · have h1 : (1 : ℕ) ∈ Finset.Icc 1 m := Finset.mem_Icc.mpr ⟨le_rfl, hm⟩
      exact Dvd.dvd.mul_left ((by norm_num : (3 : ℤ) ∣ ((8 : ℤ) ^ 2) ^ 1 - 1).trans
        (Finset.dvd_prod_of_mem (fun i : ℕ => ((8 : ℤ) ^ 2) ^ i - 1) h1)) _
  have hZ : (3 : ℤ) ∣ (Nat.card (TauCeti.QuadraticMap.orthogonalGroup R) : ℤ) := by
    by_cases hp : IsPlusType R
    · exact hO 1 (Or.inl ⟨rfl, hp⟩)
    · exact hO (-1) (Or.inr ⟨rfl, hp⟩)
  exact_mod_cast hZ

end Orders

section Fixed

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {x : V ≃ₗ[K] V}

@[expose] noncomputable def fixedRestrict (Q : QuadraticForm K V) (x : V ≃ₗ[K] V) :
    ↥(isometryCentralizer Q x) →*
      ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype)) :=
  (isometryRestrictFixed Q x).codRestrict _ isometryRestrictFixed_mem_orthogonalGroup

omit [Finite K] [FiniteDimensional K V] in
theorem coe_fixedRestrict_apply (g : ↥(isometryCentralizer Q x)) (w : fixedSpace x) :
    ((((fixedRestrict Q x g : TauCeti.QuadraticMap.orthogonalGroup
      (Q.comp (fixedSpace x).subtype)) : fixedSpace x ≃ₗ[K] fixedSpace x) w : fixedSpace x) :
        V) = g.1 w := rfl

omit [Finite K] [FiniteDimensional K V] in
theorem fixes_of_fixedRestrict_eq_one {g : V ≃ₗ[K] V} (hg : g ∈ isometryCentralizer Q x)
    (h : fixedRestrict Q x ⟨g, hg⟩ = 1) : ∀ w ∈ fixedSpace x, g w = w := fun w hw => by
  have h1 := coe_fixedRestrict_apply (Q := Q) ⟨g, hg⟩ ⟨w, hw⟩
  rw [h] at h1
  exact h1.symm

omit [Finite K] [FiniteDimensional K V] in
theorem fixedRestrict_pow_eq_one {g : V ≃ₗ[K] V} (hg : g ∈ isometryCentralizer Q x) {k : ℕ}
    (hgk : g ^ k = 1) : fixedRestrict Q x ⟨g, hg⟩ ^ k = 1 := by
  rw [← map_pow]
  have : (⟨g, hg⟩ : ↥(isometryCentralizer Q x)) ^ k = 1 := Subtype.ext hgk
  rw [this, map_one]

theorem finite_orthogonalGroup_fixed :
    Finite (TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype)) := by
  have : Finite V := Module.finite_of_finite K
  have : Finite (fixedSpace x ≃ₗ[K] fixedSpace x) :=
    Finite.of_injective (fun e : fixedSpace x ≃ₗ[K] fixedSpace x =>
      (e : fixedSpace x → fixedSpace x)) fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  exact Subtype.finite

theorem not_isPlusType_fixedSpace_of_two (hK : Nat.card K = 8) (hx : OddOrderIsometry Q 3 x)
    (hpar : IsPlusType Q ↔ Even (finrank K V / 2)) (h2 : finrank K (fixedSpace x) = 2) :
    ¬ IsPlusType (Q.comp (fixedSpace x).subtype) := by
  rw [isPlusType_fixedSpace_iff hK hx hpar, h2]
  decide

theorem three_dvd_natCard_orthogonalGroup_fixed (hK : Nat.card K = 8)
    (hx : OddOrderIsometry Q 3 x) (h4 : 4 ≤ finrank K (fixedSpace x)) :
    3 ∣ Nat.card (TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype)) := by
  have := charP_two hK
  obtain ⟨a, ha⟩ := hx.even_finrank_fixed
  have hW : finrank K (fixedSpace x) = 2 * (a - 1 + 1) := by omega
  exact three_dvd_natCard_orthogonalGroup hK hx.polarBilin_fixed_nondegenerate hW
    (Or.inl (by omega))

theorem exists_supportedBlock_pow_three (hx : OddOrderIsometry Q 3 x)
    (h3 : 3 ∣ Nat.card (TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype))) :
    ∃ U : ↥(supportedBlock Q x (X - 1)), U ^ 3 = 1 ∧ U ≠ 1 ∧
      orderOf (⟨restrictFixed Q x U, restrictFixed_mem_orthogonalGroup U⟩ :
        TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype)) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := finite_orthogonalGroup_fixed (Q := Q) (x := x)
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 3 h3
  obtain ⟨U, hU⟩ := restrictFixed_surjective hx u.1 u.2
  have hu3 : u ^ 3 = 1 := by
    rw [← hu]
    exact pow_orderOf_eq_one u
  have hU3 : U ^ 3 = 1 := by
    refine restrictFixed_injective hx ?_
    rw [map_pow, hU, map_one]
    simpa using congrArg Subtype.val hu3
  have huU : (⟨restrictFixed Q x U, restrictFixed_mem_orthogonalGroup U⟩ :
      TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype)) = u := Subtype.ext hU
  refine ⟨U, hU3, fun h1 => ?_, by rw [huU, hu]⟩
  have : u = 1 := by
    rw [← huU, h1]
    exact Subtype.ext (map_one _)
  rw [this, orderOf_one] at hu
  exact absurd hu (by norm_num)

theorem fixes_fixedSpace_two_of_mem_orthDerived (hK : Nat.card K = 8)
    (hx : OddOrderIsometry Q 3 x) (hQ : Q.polarBilin.Nondegenerate)
    (hpar : IsPlusType Q ↔ Even (finrank K V / 2)) (h2 : finrank K (fixedSpace x) = 2)
    {g : V ≃ₗ[K] V} (hgM : g ∈ isometryCentralizer Q x) (hgΩ : g ∈ orthDerived Q) {k : ℕ}
    (hk : Nat.Coprime 3 k) (hgk : g ^ k = 1) : ∀ w ∈ fixedSpace x, g w = w := by
  have := charP_two hK
  obtain ⟨Rep, hRep⟩ := hx.exists_orbitRepresentatives
  have hQW := hx.polarBilin_fixed_nondegenerate
  have hcard := natCard_orthogonalGroup_two_minus hK hQW h2
    (not_isPlusType_fixedSpace_of_two hK hx hpar h2)
  have htk := fixedRestrict_pow_eq_one hgM hgk
  have hco : Nat.Coprime 3 (orderOf (fixedRestrict Q x ⟨g, hgM⟩)) :=
    hk.coprime_dvd_right (orderOf_dvd_of_pow_eq_one htk)
  have ht2 := sq_eq_one_of_coprime_of_card_eighteen hcard hco
  have hδ : dicksonHom _ hQW (fixedRestrict Q x ⟨g, hgM⟩) = 1 :=
    hx.dickson_restrict_eq_one ⟨1, rfl⟩ hQ hRep hgM hgΩ
  exact fixes_of_fixedRestrict_eq_one hgM (eq_one_of_sq_eq_one_of_dicksonHom hQW h2 ht2 hδ)

theorem fixes_fixedSpace_two_of_commute (hK : Nat.card K = 8) (hx : OddOrderIsometry Q 3 x)
    (hpar : IsPlusType Q ↔ Even (finrank K V / 2)) (h2 : finrank K (fixedSpace x) = 2)
    {g : V ≃ₗ[K] V} (hgM : g ∈ isometryCentralizer Q x) {k : ℕ} (hk : Nat.Coprime 3 k)
    (hgk : g ^ k = 1)
    (hcomm : ∀ U ∈ supportedBlock Q x (X - 1), U ^ 3 = 1 → g * U = U * g) :
    ∀ w ∈ fixedSpace x, g w = w := by
  have := charP_two hK
  have hQW := hx.polarBilin_fixed_nondegenerate
  have hcard := natCard_orthogonalGroup_two_minus hK hQW h2
    (not_isPlusType_fixedSpace_of_two hK hx hpar h2)
  have htk := fixedRestrict_pow_eq_one hgM hgk
  have hco : Nat.Coprime 3 (orderOf (fixedRestrict Q x ⟨g, hgM⟩)) :=
    hk.coprime_dvd_right (orderOf_dvd_of_pow_eq_one htk)
  have ht2 := sq_eq_one_of_coprime_of_card_eighteen hcard hco
  obtain ⟨U, hU3, -, hUo⟩ := exists_supportedBlock_pow_three hx (by rw [hcard]; norm_num)
  set u : TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype) :=
    ⟨restrictFixed Q x U, restrictFixed_mem_orthogonalGroup U⟩ with hu
  have hu3 : u ^ 3 = 1 := by
    rw [← hUo]
    exact pow_orderOf_eq_one u
  have hu1 : u ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at hUo
    exact absurd hUo (by norm_num)
  have huU : u = fixedRestrict Q x ⟨U.1, supportedBlock_le_isometryCentralizer _ U.2⟩ :=
    Subtype.ext (isometryRestrictFixed_restrictFixed U).symm
  have hgU := hcomm U.1 U.2 (congrArg Subtype.val hU3)
  have htu : fixedRestrict Q x ⟨g, hgM⟩ * u = u * fixedRestrict Q x ⟨g, hgM⟩ := by
    rw [huU, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hgU
  exact fixes_of_fixedRestrict_eq_one hgM (eq_one_of_sq_eq_one_of_commute hQW h2 ht2 hu3 hu1 htu)

theorem fixes_fixedSpace_of_commute_derived (hK : Nat.card K = 8) (hx : OddOrderIsometry Q 3 x)
    (hQ : (polarBilin Q).Nondegenerate) (h3 : 3 ≤ finrank K (fixedSpace x)) {g : V ≃ₗ[K] V}
    (hg : g ∈ isometryCentralizer Q x)
    (hcomm : ∀ f ∈ supportedFixedDerived Q x, g * f = f * g) :
    ∀ w ∈ fixedSpace x, g w = w := by
  have := charP_two hK
  refine F106.OddRadOrth.fixes_of_commute_listed hx hQ h3 ?_ hg fun f hf v => ?_
  · rintro (⟨-, h⟩ | ⟨-, h | h⟩) <;> omega
  · exact congrArg (fun e : V ≃ₗ[K] V => e v) (hcomm f hf)

theorem eq_one_of_commute_supportedFixedDerived (hK : Nat.card K = 8)
    (hx : OddOrderIsometry Q 3 x) (hQ : (polarBilin Q).Nondegenerate)
    (h3 : 3 ≤ finrank K (fixedSpace x)) {f : V ≃ₗ[K] V} (hf : f ∈ supportedFixedDerived Q x)
    (hcomm : ∀ f' ∈ supportedFixedDerived Q x, f * f' = f' * f) : f = 1 :=
  eq_one_of_fixes hK hx (fixes_fixedSpace_of_commute_derived hK hx hQ h3
    (supportedFixedDerived_le_isometryCentralizer hf) hcomm)
    (fixes_cyc3_of_mem_supportedBlock_fixed hK (supportedFixedDerived_le_supportedBlock hf))

end Fixed

end CFSG.HardMathSupport.Dickson.Bal207.OrthEight

end
