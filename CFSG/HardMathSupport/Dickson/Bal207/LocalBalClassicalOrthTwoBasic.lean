module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.OrthQ2Unit
public import CFSG.RankThree.PartOne.K159.RowFourType
public import CFSG.ClassicalInvolution.RouteD.TWYType
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.OrthTwoAux.Quad

public section

namespace CFSG.HardMathSupport.Dickson.Bal207.OrthRow.Two

open Polynomial Module QuadraticMap CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.GroupTheory.WeirSylow CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.Classical2

section Field

variable {K : Type} [Field K] [Finite K]

theorem charP_two (hK : Nat.card K = 2) : CharP K 2 :=
  CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.OrthTwoAux.card_two_charP hK

end Field

section Primary

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {x : V ≃ₗ[K] V}

theorem primaryFactor_cases (hK : Nat.card K = 2) (hx : OddOrderIsometry Q 3 x) {h : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) : h = X - 1 ∨ h = cyc3 K := by
  have hdvd : h ∣ (X ^ 3 - 1 : K[X]) := hx.dvd_X_pow_sub_one hh
  have hfac : (X ^ 3 - 1 : K[X]) = (X - 1) * cyc3 K := by
    unfold cyc3
    ring
  rw [hfac] at hdvd
  have hirr := irreducible_of_mem_primaryFactors hh
  have hmon := monic_of_mem_primaryFactors hh
  rcases hirr.prime.dvd_or_dvd hdvd with h1 | h1
  · exact Or.inl (eq_of_monic_of_associated hmon monic_X_sub_one
      (hirr.associated_of_dvd irreducible_X_sub_one h1))
  · exact Or.inr (eq_of_monic_of_associated hmon (monic_cyc3 K)
      (hirr.associated_of_dvd (irreducible_cyc3 hK) h1))

theorem primaryComponent_cyc3_eq_bot (hK : Nat.card K = 2)
    (hh : cyc3 K ∉ primaryFactors x.toLinearMap) :
    primaryComponent x.toLinearMap (cyc3 K) = ⊥ := by
  by_contra hne
  exact hh (mem_primaryFactors_of_primaryComponent_ne_bot (irreducible_cyc3 hK) (monic_cyc3 K) hne)

theorem othersSpace_le_cyc3 (hK : Nat.card K = 2) (hx : OddOrderIsometry Q 3 x) :
    othersSpace x.toLinearMap (X - 1) ≤ primaryComponent x.toLinearMap (cyc3 K) := by
  unfold othersSpace
  refine iSup₂_le fun k hk => ?_
  rcases primaryFactor_cases hK hx hk.1 with rfl | rfl
  · exact absurd rfl hk.2.1
  · exact le_rfl

theorem cyc3_le_othersSpace (hK : Nat.card K = 2) :
    primaryComponent x.toLinearMap (cyc3 K) ≤ othersSpace x.toLinearMap (X - 1) := by
  by_cases hh : cyc3 K ∈ primaryFactors x.toLinearMap
  · intro v hv
    refine Submodule.mem_iSup_of_mem (cyc3 K) (Submodule.mem_iSup_of_mem
      ⟨hh, cyc3_ne_X_sub_one K, ?_⟩ hv)
    rw [reciprocalPolynomial_X_sub_one]
    exact cyc3_ne_X_sub_one K
  · rw [primaryComponent_cyc3_eq_bot hK hh]
    exact bot_le

theorem fixedSpace_le_othersSpace_cyc3 :
    fixedSpace x ≤ othersSpace x.toLinearMap (cyc3 K) := by
  by_cases hh : (X - 1 : K[X]) ∈ primaryFactors x.toLinearMap
  · intro v hv
    rw [fixedSpace_eq_primaryComponent] at hv
    refine Submodule.mem_iSup_of_mem (X - 1) (Submodule.mem_iSup_of_mem
      ⟨hh, (cyc3_ne_X_sub_one K).symm, ?_⟩ hv)
    rw [reciprocal_cyc3]
    exact (cyc3_ne_X_sub_one K).symm
  · rw [fixedSpace_eq_bot_of_not_mem hh]
    exact bot_le

theorem othersSpace_eq_cyc3 (hK : Nat.card K = 2) (hx : OddOrderIsometry Q 3 x) :
    othersSpace x.toLinearMap (X - 1) = primaryComponent x.toLinearMap (cyc3 K) :=
  le_antisymm (othersSpace_le_cyc3 hK hx) (cyc3_le_othersSpace hK)

theorem isCompl_fixedSpace_cyc3 (hK : Nat.card K = 2) (hx : OddOrderIsometry Q 3 x) :
    IsCompl (fixedSpace x) (primaryComponent x.toLinearMap (cyc3 K)) := by
  have h := hx.fixed_others.1
  rwa [othersSpace_eq_cyc3 hK hx] at h

theorem polar_fixedSpace_cyc3 (hK : Nat.card K = 2) (hx : OddOrderIsometry Q 3 x) {w v : V}
    (hw : w ∈ fixedSpace x) (hv : v ∈ primaryComponent x.toLinearMap (cyc3 K)) :
    polar Q w v = 0 :=
  hx.fixed_others.2 w hw v (cyc3_le_othersSpace hK hv)

theorem finrank_cyc3 (hK : Nat.card K = 2) :
    finrank K (primaryComponent x.toLinearMap (cyc3 K)) =
      2 * primaryMultiplicity x.toLinearMap (cyc3 K) := by
  have : Fact (Irreducible (cyc3 K)) := ⟨irreducible_cyc3 hK⟩
  rw [finrank_primaryComponent, natDegree_cyc3]

theorem eq_one_of_fixes (hK : Nat.card K = 2) (hx : OddOrderIsometry Q 3 x) {g : V ≃ₗ[K] V}
    (hW : ∀ w ∈ fixedSpace x, g w = w)
    (hh : ∀ v ∈ primaryComponent x.toLinearMap (cyc3 K), g v = v) : g = 1 := by
  ext v
  obtain ⟨w, hw, r, hr, rfl⟩ := exists_add_of_isCompl (isCompl_fixedSpace_cyc3 hK hx) v
  rw [map_add, hW w hw, hh r hr]
  rfl

theorem fixes_fixedSpace_of_mem_supportedBlock_cyc3 {g : V ≃ₗ[K] V}
    (hg : g ∈ supportedBlock Q x (cyc3 K)) : ∀ w ∈ fixedSpace x, g w = w := fun w hw =>
  (mem_supportedBlock.mp hg).2 w (fixedSpace_le_othersSpace_cyc3 hw)

theorem fixes_cyc3_of_mem_supportedBlock_fixed (hK : Nat.card K = 2) {g : V ≃ₗ[K] V}
    (hg : g ∈ supportedBlock Q x (X - 1)) :
    ∀ v ∈ primaryComponent x.toLinearMap (cyc3 K), g v = v := fun v hv =>
  (mem_supportedBlock.mp hg).2 v (cyc3_le_othersSpace hK hv)

theorem cyc3_mem_primaryFactors (hK : Nat.card K = 2)
    (hm : 1 ≤ primaryMultiplicity x.toLinearMap (cyc3 K)) :
    cyc3 K ∈ primaryFactors x.toLinearMap := by
  refine mem_primaryFactors_of_primaryComponent_ne_bot (irreducible_cyc3 hK) (monic_cyc3 K)
    fun h => ?_
  have h1 := finrank_cyc3 (x := x) hK
  rw [h, finrank_bot] at h1
  omega

end Primary

section WittType

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {x : V ≃ₗ[K] V}

omit [Finite K] [FiniteDimensional K V] in
theorem restrict_eq_comp (U : Submodule K V) : Q.restrict U = Q.comp U.subtype :=
  QuadraticMap.ext fun _ => rfl

theorem isPlusType_fixedSpace_iff (hK : Nat.card K = 2) (hx : OddOrderIsometry Q 3 x)
    (hpar : IsPlusType Q ↔ Even (finrank K V / 2)) :
    IsPlusType (Q.comp (fixedSpace x).subtype) ↔ Even (finrank K (fixedSpace x) / 2) := by
  classical
  have := charP_two hK
  set W := fixedSpace x with hWdef
  set R := primaryComponent x.toLinearMap (cyc3 K) with hRdef
  set m := primaryMultiplicity x.toLinearMap (cyc3 K) with hm
  have hc : IsCompl W R := isCompl_fixedSpace_cyc3 hK hx
  have horth : ∀ w ∈ W, ∀ r ∈ R, polar Q w r = 0 := fun w hw r hr =>
    polar_fixedSpace_cyc3 hK hx hw hr
  have hWnd : PolarNondegOn Q W := fun w hw hperp => hx.regular w fun v => by
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_add_of_isCompl hc v
    rw [polar_add_right, hperp a ha, horth w hw b hb, add_zero]
  have hRnd : PolarNondegOn Q R := fun r hr hperp => hx.regular r fun v => by
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_add_of_isCompl hc v
    rw [polar_add_right, polar_comm, horth a ha r hr, hperp b hb, zero_add]
  obtain ⟨a, ha⟩ : Even (finrank K W) := hx.even_finrank_fixed
  have hR : finrank K R = 2 * m := finrank_cyc3 hK
  have hdim : finrank K W + finrank K R = finrank K V := Submodule.finrank_add_eq_of_isCompl hc
  have hWd : finrank K W = 2 * a := by omega
  have hRtype : IsPlusType (Q.comp R.subtype) ↔ Even m := by
    refine K159.isPlusType_iff_even_of_fixedFree hx Nat.prime_three (by norm_num)
      (by rw [hK] <;> norm_num) m R (fun u hu => ?_) (fun u hu h => hRnd u hu h)
      (fun u hu h => ?_) hR
    · exact apply_mem_primaryComponent_of_mem_centralizer
        (Subgroup.mem_centralizer_singleton_iff.2 rfl) hu
    · exact (Submodule.disjoint_def.mp hc.1) u (mem_fixedSpace.mpr h) hu
  rcases Nat.eq_zero_or_pos a with ha0 | ha0
  · have hW0 : finrank K W = 0 := by omega
    refine ⟨fun _ => by rw [hW0]; exact ⟨0, rfl⟩, fun _ => ⟨⊥, ?_, fun y hy => ?_⟩⟩
    · rw [finrank_bot, hW0]
    · rw [(Submodule.mem_bot K).mp hy, map_zero]
  rcases Nat.eq_zero_or_pos m with hm0 | hm0
  · have hR0 : R = ⊥ := Submodule.finrank_eq_zero.mp (by omega)
    have hWtop : W = ⊤ := by
      rw [hR0] at hc
      exact eq_top_of_isCompl_bot hc
    let e : (Q.comp W.subtype).IsometryEquiv Q :=
      { toLinearEquiv := LinearEquiv.ofTop W hWtop
        map_app' := fun _ => rfl }
    rw [isPlusType_congr e, hpar]
    have : finrank K V = finrank K W := by omega
    rw [this]
  have h := CFSG.ClassicalInvolution.RouteD.TWY.isPlusType_iff_of_isCompl hc horth hWnd hRnd ha0
    hm0 hWd hR
  rw [restrict_eq_comp, restrict_eq_comp, hpar, hRtype,
    show finrank K V / 2 = a + m by omega, Nat.even_add] at h
  rw [show finrank K W / 2 = a by omega]
  tauto

end WittType

section Scalar

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {x : V ≃ₗ[K] V}

theorem fixes_cyc3 (hK : Nat.card K = 2) (hx : OddOrderIsometry Q 3 x) {G : V ≃ₗ[K] V}
    (hGx : G * x = x * G) {k : ℕ} (hk : Nat.Coprime 3 k) (hGk : G ^ k = 1)
    (hcomm : 2 ≤ primaryMultiplicity x.toLinearMap (cyc3 K) →
      ∀ f ∈ specialBlock Q x (cyc3 K), G * f = f * G) :
    ∀ v ∈ primaryComponent x.toLinearMap (cyc3 K), G v = v := by
  classical
  have := charP_two hK
  have hirr := irreducible_cyc3 hK
  have : Fact (Irreducible (cyc3 K)) := ⟨hirr⟩
  set Vh := primaryComponent x.toLinearMap (cyc3 K) with hVh
  by_cases hne : Vh = ⊥
  · intro v hv
    rw [hne, Submodule.mem_bot] at hv
    rw [hv, map_zero]
  have hh : cyc3 K ∈ primaryFactors x.toLinearMap :=
    mem_primaryFactors_of_primaryComponent_ne_bot hirr (monic_cyc3 K) hne
  have hGc : G ∈ Subgroup.centralizer ({x} : Set (V ≃ₗ[K] V)) :=
    Subgroup.mem_centralizer_singleton_iff.2 hGx
  obtain ⟨c, hc⟩ : ∃ c : AdjoinRoot (cyc3 K), ∀ w : Vh, (G (w : V) : V) = ((c • w : Vh) : V) := by
    by_cases hm : 2 ≤ primaryMultiplicity x.toLinearMap (cyc3 K)
    · exact orth2_exists_smul_of_commute_specialBlock hx (by decide) hh (cyc3_ne_X_sub_one K)
        (reciprocal_cyc3 K).symm hm hGc (hcomm hm)
    · have : Nontrivial Vh := Submodule.nontrivial_iff_ne_bot.mpr hne
      have hpos : 0 < finrank (AdjoinRoot (cyc3 K)) Vh := Module.finrank_pos
      have hm1 : finrank (AdjoinRoot (cyc3 K)) Vh = 1 := by
        have : primaryMultiplicity x.toLinearMap (cyc3 K) = finrank (AdjoinRoot (cyc3 K)) Vh := rfl
        omega
      obtain ⟨c, hc, -⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hm1
        ((centralizerGL x (cyc3 K) ⟨G, hGc⟩ : BlockGL x (cyc3 K)) :
          Module.End (AdjoinRoot (cyc3 K)) Vh)
      refine ⟨c, fun w => ?_⟩
      have h1 := coe_centralizerGL x (cyc3 K) ⟨G, hGc⟩ w
      rw [hc] at h1
      exact h1.symm
  have hGpow : ∀ (n : ℕ) (w : Vh), ((G ^ n) (w : V) : V) = ((c ^ n • w : Vh) : V) := by
    intro n
    induction n with
    | zero => intro w; simp
    | succ n ih =>
      intro w
      rw [pow_succ', LinearEquiv.mul_apply, ih w, pow_succ', mul_smul, hc]
  obtain ⟨w₀, hw₀, hw₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hw₀' : (⟨w₀, hw₀⟩ : Vh) ≠ 0 := fun h0 => hw₀0 (congrArg Subtype.val h0)
  have hck : c ^ k = 1 := by
    have h1 : ((⟨w₀, hw₀⟩ : Vh) : V) = ((c ^ k • ⟨w₀, hw₀⟩ : Vh) : V) := by
      rw [← hGpow k ⟨w₀, hw₀⟩, hGk]
      rfl
    have h2 : (c ^ k - 1) • (⟨w₀, hw₀⟩ : Vh) = 0 := by
      apply Subtype.ext
      rw [sub_smul, one_smul, Submodule.coe_sub, ← h1]
      simp
    rcases smul_eq_zero.1 h2 with h3 | h3
    · exact sub_eq_zero.1 h3
    · exact absurd h3 hw₀'
  have hk0 : k ≠ 0 := by
    rintro rfl
    norm_num at hk
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_pow hk0] at hck
    exact zero_ne_one hck
  have hc3 : c ^ 3 = 1 := by
    have : Fintype K := Fintype.ofFinite K
    have : Module.Finite K (AdjoinRoot (cyc3 K)) := (AdjoinRoot.powerBasis hirr.ne_zero).finite
    have : Finite (AdjoinRoot (cyc3 K)) := Module.finite_of_finite K
    have : Fintype (AdjoinRoot (cyc3 K)) := Fintype.ofFinite _
    have hcard : Fintype.card (AdjoinRoot (cyc3 K)) = 4 := by
      rw [Module.card_eq_pow_finrank (K := K), (AdjoinRoot.powerBasis hirr.ne_zero).finrank,
        AdjoinRoot.powerBasis_dim, natDegree_cyc3, ← Nat.card_eq_fintype_card, hK]
      norm_num
    have := FiniteField.pow_card_sub_one_eq_one c hc0
    rwa [hcard] at this
  have hc1 : c = 1 := by
    have := pow_gcd_eq_one.2 ⟨hc3, hck⟩
    rwa [Nat.Coprime.gcd_eq_one hk, pow_one] at this
  intro v hv
  have := hc ⟨v, hv⟩
  rw [hc1, one_smul] at this
  exact this

end Scalar

section Special

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {x : V ≃ₗ[K] V}

theorem specialBlock_le_orthDerived (hK : Nat.card K = 2) (hx : OddOrderIsometry Q 3 x)
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    (hh : cyc3 K ∈ primaryFactors x.toLinearMap) :
    specialBlock Q x (cyc3 K) ≤ orthDerived Q := by
  have := charP_two hK
  intro f hf
  have hfO := (Subgroup.mem_inf.mp (specialBlock_le_isometryCentralizer _ hf)).1
  have heven := hx.even_finrank_commSpace_of_mem_supportedBlock (Nat.odd_iff.2 rfl) hh
    (cyc3_ne_X_sub_one K) (specialBlock_le_supportedBlock _ hf)
  exact FieldFix.omegaGroup_le_orthDerived hQ hT
    (CFSG.RankThree.OrthogonalInvolutions.mem_omegaGroup.2 ⟨hfO, heven⟩)

end Special

end CFSG.HardMathSupport.Dickson.Bal207.OrthRow.Two

end
