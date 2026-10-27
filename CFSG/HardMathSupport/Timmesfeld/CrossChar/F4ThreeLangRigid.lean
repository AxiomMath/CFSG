module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.F4ThreeLangFamily
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.BadThreeLang
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.OuterFieldCore
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidCriterion

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.Classical CFSG.RankThree.PartOne.KE
open scoped MatrixGroups

set_option linter.unusedSectionVars false

section Rigid

variable (K : Type) [Field K] [Finite K] {Fr : AlgebraicClosure K →+* AlgebraicClosure K}
  (hFr : ∀ c, Fr c = c ^ Nat.card K) {w : WeylGroup Tag.F4}
  {g0 : ModGL Tag.F4 (AlgebraicClosure K)} (hg0C : g0 ∈ adjointGroup Tag.F4 (AlgebraicClosure K))
  (hg0 : Units.map (entrywiseHom Fr) g0 =
    g0 * canonicalRep (coxeterSystem Tag.F4) (AlgebraicClosure K) w)
  (S : LangSetup Tag.F4 (AlgebraicClosure K) 3)
  (hSD : S.D = LangDatum.ofFrobenius Fr (Nat.card K) hFr w hg0C hg0)

theorem f4Three_exists_plane_elt {L : Type} [Field L] [IsAlgClosed L] (S : LangSetup Tag.F4 L 3)
    {D₁ : Subgroup (ModGL Tag.F4 L)} (hD₁E : D₁ ≤ S.E) (hD₁c : Nat.card D₁ = 3 ^ 2)
    (γ : Fin Tag.F4.rank → ℤ) :
    ∃ a : Fin Tag.F4.rank → Lˣ, rootDiagUnit Tag.F4 a ∈ D₁ ∧ rootDiagUnit Tag.F4 a ≠ 1 ∧
      rootChar a γ = 1 := by
  have := S.finite_Γ
  have hD₁Γ : D₁ ≤ S.Γ := fun x hx => (S.E_le (hD₁E hx)).2
  have : Finite D₁ := Finite.of_injective (Subgroup.inclusion hD₁Γ)
    (Subgroup.inclusion_injective hD₁Γ)
  have hD₁T : D₁ ≤ torusGroup Tag.F4 L := fun x hx =>
    (mem_twistedTorusOf.1 (S.E_le (hD₁E hx)).1).1
  exact exists_rootChar_eq_one_of_finite Nat.prime_three hD₁T (fun x hx => S.E_exp x (hD₁E hx))
    (by rw [hD₁c]; norm_num) γ

include hSD in
theorem f4Three_centralizerTrivial (hq3 : ¬ 3 ∣ Nat.card K) (hK4 : 4 ≤ Nat.card K)
    {D₁ : Subgroup (ModGL Tag.F4 (AlgebraicClosure K))} (hD₁E : D₁ ≤ S.E)
    (hD₁c : Nat.card D₁ = 3 ^ 2) : CentralizerTrivial S D₁ := by
  classical
  intro Z hZC hcomm
  refine eq_one_of_commute_rootRankOneGroup_simple hZC fun k => ?_
  obtain ⟨a, haD, ha1, hχ⟩ := f4Three_exists_plane_elt S hD₁E hD₁c (Pi.single k 1)
  have hE := hD₁E haD
  have hk : (Pi.single k 1 : Fin Tag.F4.rank → ℤ) ∈ kernelRoots (rootCharHom a) :=
    ⟨isRoot_single Tag.F4 k, hχ⟩
  set i : KernelComponent (rootCharHom a) := ⟦⟨_, hk⟩⟧ with hi
  have hki : (Pi.single k 1 : Fin Tag.F4.rank → ℤ) ∈ componentRoots (rootCharHom a) i :=
    ⟨hk, rfl⟩
  obtain ⟨z, P, hnorm, hfix, hζ⟩ := f4Three_exists_family K hFr hg0C hg0 S hSD hq3 hE i
  have : Fintype K := Fintype.ofFinite K
  have hcardK : Fintype.card K = Nat.card K := Nat.card_eq_fintype_card.symm
  have hcommγ : ∀ γ ∈ componentRoots (rootCharHom a) i,
      ∀ x ∈ rootRankOneGroup Tag.F4 (AlgebraicClosure K) γ, Commute (z⁻¹ * Z * z) x := by
    intro γ hγ
    obtain ⟨ζ, hζ3, hζP⟩ := hζ γ hγ
    refine commute_rootRankOneGroup_of_twisted (algebraMap K (AlgebraicClosure K))
      (by rw [hcardK]; simp [entryDegreeBound]; omega) γ (P γ) fun A => ?_
    have hmem := f4Three_mem_bigComponentSet S hK4 haD ha1 i (hnorm i) hγ (hfix γ hγ) hζ3 hζP
      (B := conjSL (P γ) (Matrix.SpecialLinearGroup.map (algebraMap K (AlgebraicClosure K)) A))
      ⟨_, ⟨A, rfl⟩, rfl⟩
    exact (commute_conj_iff Z z _).1 (hcomm _ (Or.inl hmem))
  have hcommS : rootSpan Tag.F4 (AlgebraicClosure K) (componentRoots (rootCharHom a) i) ≤
      Subgroup.centralizer {z⁻¹ * Z * z} := by
    refine (rootSpan_le_iSup_rootRankOne i).trans (iSup₂_le fun β hβ => ?_)
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.2
      (hcommγ β (simpleRoots_subset hβ) x hx).symm.eq
  intro x hx
  obtain ⟨B, rfl⟩ := hx
  have hxS := f4Three_rootSL2_mem_component K i hki B
  have hx' : z⁻¹ * rootSL2 Tag.F4 (AlgebraicClosure K) (Pi.single k 1) B * z ∈
      rootSpan Tag.F4 (AlgebraicClosure K) (componentRoots (rootCharHom a) i) := by
    refine (hnorm i _).2 ?_
    simpa [mul_assoc] using hxS
  have h1 : Commute (z⁻¹ * Z * z)
      (z⁻¹ * rootSL2 Tag.F4 (AlgebraicClosure K) (Pi.single k 1) B * z) :=
    (Subgroup.mem_centralizer_singleton_iff.1 (hcommS hx')).symm
  have h2 := h1.map (MulAut.conj z).toMonoidHom
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h2
  have e1 : z * (z⁻¹ * Z * z) * z⁻¹ = Z := by group
  have e2 : z * (z⁻¹ * rootSL2 Tag.F4 (AlgebraicClosure K) (Pi.single k 1) B * z) * z⁻¹ =
      rootSL2 Tag.F4 (AlgebraicClosure K) (Pi.single k 1) B := by group
  rw [e1, e2] at h2
  exact h2

include hSD in
theorem f4Three_noFrobeniusInner (hq3 : ¬ 3 ∣ Nat.card K) (hK4 : 4 ≤ Nat.card K)
    (hq4 : Nat.card K ≠ 4) {D₁ : Subgroup (ModGL Tag.F4 (AlgebraicClosure K))} (hD₁E : D₁ ≤ S.E)
    (hD₁c : Nat.card D₁ = 3 ^ 2) : NoFrobeniusInner S D₁ := by
  classical
  intro r f j _ hr hqf hj0 hjf z' hz'
  have hq := f4Three_q_eq K hFr hg0C hg0 S hSD
  obtain ⟨a, haD, ha1, hχ⟩ := f4Three_exists_plane_elt S hD₁E hD₁c (Pi.single 0 1)
  have hE := hD₁E haD
  have hk : (Pi.single 0 1 : Fin Tag.F4.rank → ℤ) ∈ kernelRoots (rootCharHom a) :=
    ⟨isRoot_single Tag.F4 0, hχ⟩
  set i : KernelComponent (rootCharHom a) := ⟦⟨_, hk⟩⟧ with hi
  set γ : Fin Tag.F4.rank → ℤ := Pi.single 0 1 with hγdef
  have hγ : γ ∈ componentRoots (rootCharHom a) i := ⟨hk, rfl⟩
  obtain ⟨z, P, hnorm, hfix, hζ⟩ := f4Three_exists_family K hFr hg0C hg0 S hSD hq3 hE i
  obtain ⟨ζ, hζ3, hζP⟩ := hζ γ hγ
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨j₁, g₁, hρ⟩ := exists_rootSL2_conjSL_eq (τ := Tag.F4) (L := AlgebraicClosure K) γ (P γ)
  have hxt : ∀ t : K, z * rootSL2 Tag.F4 (AlgebraicClosure K) γ (conjSL (P γ)
      (Matrix.SpecialLinearGroup.map (algebraMap K (AlgebraicClosure K)) (uSL t))) * z⁻¹ =
      (z * g₁) * pinnedX Tag.F4 (AlgebraicClosure K) (Pi.single j₁ 1)
        (((pinnedData Tag.F4 (Pi.single j₁ 1)).2.2 : AlgebraicClosure K) *
          algebraMap K (AlgebraicClosure K) t) * (z * g₁)⁻¹ := by
    intro t
    rw [hρ, sl2_map_uSL, ← rootSL2_single, rootSL2_uSL_eq, zsmul_eq_mul]
    group
  have hεL : ((pinnedData Tag.F4 (Pi.single j₁ 1)).2.2 : AlgebraicClosure K) ≠ 0 := by
    rcases pinnedSign_eq Tag.F4 (Pi.single j₁ 1 : Fin Tag.F4.rank → ℤ) with h | h <;>
      rw [h] <;> simp
  obtain ⟨a₀, b₀, ha₀, -, hab⟩ := conj_map_pinnedX_expand (by decide) (RingHom.id _) (z * g₁) hεL
    (Pi.single j₁ 1)
  set ψ : AlgebraicClosure K →+* AlgebraicClosure K := iterateFrobenius (AlgebraicClosure K) r j
    with hψ
  obtain ⟨a₁, b₁, ha₁, -, hab'⟩ := conj_map_pinnedX_expand (by decide) ψ (z * g₁) hεL
    (Pi.single j₁ 1)
  have hψpow : ∀ x : AlgebraicClosure K, ψ x = x ^ (r ^ j) := fun x => by
    rw [hψ, iterateFrobenius_def]
  have hid : ∀ x : ModGL Tag.F4 (AlgebraicClosure K),
      Units.map (entrywiseHom (RingHom.id (AlgebraicClosure K))) x = x :=
    fun x => Units.ext (entrywise_id _)
  have hr2 := hr.two_le
  have hf1 : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · rw [h0, pow_zero, hq] at hqf
      omega
    · exact h0
  refine no_twisted_conj (algebraMap K (AlgebraicClosure K)) hr hj0 hjf one_pos
    (by rw [← Nat.card_eq_fintype_card, ← hq, hqf, pow_one]) (by rw [← hqf, hq]; exact hK4)
    (fun hc2 => ?_) [0] (List.nodup_singleton 0) (List.mem_singleton_self 0)
    (fun k hk => by rw [List.mem_singleton] at hk; omega)
    (fun _ => a₀) (fun _ => b₀) (fun _ => a₁) (fun _ => b₁) ha₀ ha₁ z' fun t => ?_
  ·
    have hr2' : r = 2 := by
      have : r ∣ 2 := by
        rw [← hc2]
        exact dvd_pow_self r hj0.ne'
      exact (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 this
    subst hr2'
    have hf3 : 3 ≤ f := by
      by_contra hlt
      have : f = 1 ∨ f = 2 := by omega
      rcases this with rfl | rfl
      · omega
      · exact hq4 (by rw [← hq, hqf]; norm_num)
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by omega) hf3
  ·
    have hmem := f4Three_mem_bigComponentSet S hK4 haD ha1 i (hnorm i) hγ (hfix γ hγ) hζ3 hζP
      (B := conjSL (P γ) (Matrix.SpecialLinearGroup.map (algebraMap K (AlgebraicClosure K))
        (uSL t))) ⟨_, ⟨uSL t, rfl⟩, rfl⟩
    have h := hz' _ (Or.inl hmem)
    rw [hxt] at h
    set X := z * g₁ * pinnedX Tag.F4 (AlgebraicClosure K) (Pi.single j₁ 1)
      (((pinnedData Tag.F4 (Pi.single j₁ 1)).2.2 : AlgebraicClosure K) *
        algebraMap K (AlgebraicClosure K) t) * (z * g₁)⁻¹ with hX
    have hEnd : (z' : Module.End (AlgebraicClosure K) (RootModule Tag.F4 (AlgebraicClosure K))) *
        ((Units.map (entrywiseHom ψ) X : ModGL Tag.F4 (AlgebraicClosure K)) :
          Module.End (AlgebraicClosure K) (RootModule Tag.F4 (AlgebraicClosure K))) *
        ((z'⁻¹ : ModGL Tag.F4 (AlgebraicClosure K)) :
          Module.End (AlgebraicClosure K) (RootModule Tag.F4 (AlgebraicClosure K))) =
        (X : Module.End (AlgebraicClosure K) (RootModule Tag.F4 (AlgebraicClosure K))) := by
      rw [← Units.val_mul, ← Units.val_mul, h]
    have e1 := hab (algebraMap K (AlgebraicClosure K) t)
    rw [hid] at e1
    have e2 := hab' (algebraMap K (AlgebraicClosure K) t)
    rw [e1, e2, hψpow] at hEnd
    rw [evAt_prodList, evAt_prodList]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, pow_zero,
      pow_one]
    simpa using hEnd

include hSD in
theorem f4Three_setupRigid_odd
    (hQ : ThreeLargeQ (Nat.card K)) (hodd : Odd (Nat.card K)) :
    SetupRigid S := by
  have hq := f4Three_q_eq K hFr hg0C hg0 S hSD
  have hK4 : 4 ≤ Nat.card K := by
    obtain ⟨h3, h2, h4⟩ := hQ
    have h1 : 2 ≤ Nat.card K := Finite.one_lt_card
    obtain ⟨m, hm⟩ := hodd
    omega
  refine setupRigid_F4 S (by rw [hq]; exact hodd) (fun D₁ hD₁ hc => ?_) (fun D₁ hD₁ hc => ?_)
  · exact f4Three_noFrobeniusInner K hFr hg0C hg0 S hSD hQ.1 hK4 hQ.2.2 hD₁ hc
  · exact f4Three_centralizerTrivial K hFr hg0C hg0 S hSD hQ.1 hK4 hD₁ hc

end Rigid

section Balance

theorem f4Three_langTorusPlaneBalance_odd
    (hsub : LangSubnormal)
    (hin : LangComponentsQuasisimple .inner) (hsu : LangComponentsQuasisimple .suN)
    (htw : LangComponentsQuasisimple .twoD) (hex : LangComponentsQuasisimple .exc)
    (w : WeylGroup Tag.F4) :
    LangTorusPlaneBalance Tag.F4 w 3 fun q => ThreeLargeQ q ∧ Odd q :=
  langTorusPlaneBalance_of_setupRigidAt (Or.inl rfl)
    (fun K _ _ => commutator_adjointGroup_F4_eq_top K) w Nat.prime_three
    (fun q hq2 hQ => ⟨hQ.1.1, Or.inr (by
      obtain ⟨⟨h3, h2, h4⟩, m, hm⟩ := hQ
      omega)⟩)
    (fun K _ _ Fr hFr g0 hg0C hg0 S hSD hQK => by
      have : IsAlgClosed (AlgebraicClosure K) := IsAlgClosure.isAlgClosed K
      exact f4Three_setupRigid_odd K hFr hg0C hg0 S hSD hQK.1 hQK.2)
    hsub hin hsu htw hex

end Balance

end CFSG.HardMathSupport.Timmesfeld.CrossChar
