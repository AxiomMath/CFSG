module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SteinbergLangFamily
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.OuterFieldCore
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidCriterion

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.Classical CFSG.RankThree.PartOne.KE
open scoped MatrixGroups

set_option linter.unusedSectionVars false


theorem steinbergLang_exists_plane_elt {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
    (S : LangSetup τ L p) {D₁ : Subgroup (ModGL τ L)} (hD₁E : D₁ ≤ S.E)
    (hD₁c : Nat.card D₁ = p ^ 2) (γ : Fin τ.rank → ℤ) :
    ∃ a : Fin τ.rank → Lˣ, rootDiagUnit τ a ∈ D₁ ∧ rootDiagUnit τ a ≠ 1 ∧ rootChar a γ = 1 := by
  have := S.finite_Γ
  have hp := S.hp
  have hD₁Γ : D₁ ≤ S.Γ := fun x hx => (S.E_le (hD₁E hx)).2
  have : Finite D₁ := Finite.of_injective (Subgroup.inclusion hD₁Γ)
    (Subgroup.inclusion_injective hD₁Γ)
  have hD₁T : D₁ ≤ torusGroup τ L := fun x hx => (mem_twistedTorusOf.1 (S.E_le (hD₁E hx)).1).1
  refine exists_rootChar_eq_one_of_finite hp hD₁T (fun x hx => S.E_exp x (hD₁E hx)) ?_ γ
  rw [hD₁c]
  have := hp.one_lt
  nlinarith

section Rigid

variable {τ : Tag} (K : Type) [Field K] [Finite K] {Fr : AlgebraicClosure K →+* AlgebraicClosure K}
  (hFr : ∀ c, Fr c = c ^ Nat.card K) {w : WeylGroup τ}
  {g0 : ModGL τ (AlgebraicClosure K)} (hg0C : g0 ∈ adjointGroup τ (AlgebraicClosure K))
  (hg0 : Units.map (entrywiseHom Fr) g0 =
    g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w)
  {p : ℕ} (S : LangSetup τ (AlgebraicClosure K) p)
  (hSD : S.D = LangDatum.ofFrobenius Fr (Nat.card K) hFr w hg0C hg0)

include hSD in
theorem steinbergLang_centralizerTrivial (hp : p.Prime)
    (hst : ∀ b : Fin τ.rank → (AlgebraicClosure K)ˣ, (∀ i, b i ^ p = 1) →
      rootCharStabilizerSubgroup b ≤ kernelReflectionGroup b)
    {w₀ : WeylGroup τ} (hw₀ : ∀ u : Fin τ.rank → ℤ, w₀ • u = -u)
    (hqp : Nat.card K % p = 1 ∨ Nat.card K % p = p - 1) (hK4 : 4 ≤ Nat.card K)
    (hdeg : entryDegreeBound τ < Nat.card K)
    {D₁ : Subgroup (ModGL τ (AlgebraicClosure K))} (hD₁E : D₁ ≤ S.E)
    (hD₁c : Nat.card D₁ = p ^ 2) : CentralizerTrivial S D₁ := by
  classical
  intro Z hZC hcomm
  refine eq_one_of_commute_rootRankOneGroup_simple hZC fun k => ?_
  obtain ⟨a, haD, ha1, hχ⟩ := steinbergLang_exists_plane_elt S hD₁E hD₁c (Pi.single k 1)
  have hE := hD₁E haD
  have hk : (Pi.single k 1 : Fin τ.rank → ℤ) ∈ kernelRoots (rootCharHom a) :=
    ⟨isRoot_single τ k, hχ⟩
  set i : KernelComponent (rootCharHom a) := ⟦⟨_, hk⟩⟧ with hi
  have hki : (Pi.single k 1 : Fin τ.rank → ℤ) ∈ componentRoots (rootCharHom a) i := ⟨hk, rfl⟩
  obtain ⟨z, P, hnorm, hfix, hζ⟩ :=
    steinbergLang_exists_family K hFr hg0C hg0 S hSD hp hst hw₀ hqp hE i
  have : Fintype K := Fintype.ofFinite K
  have hcardK : Fintype.card K = Nat.card K := Nat.card_eq_fintype_card.symm
  have hcommγ : ∀ γ ∈ componentRoots (rootCharHom a) i,
      ∀ x ∈ rootRankOneGroup τ (AlgebraicClosure K) γ, Commute (z⁻¹ * Z * z) x := by
    intro γ hγ
    obtain ⟨ζ, hζp, hζP⟩ := hζ γ hγ
    refine commute_rootRankOneGroup_of_twisted (algebraMap K (AlgebraicClosure K))
      (by rw [hcardK]; exact hdeg) γ (P γ) fun A => ?_
    have hmem := steinbergLang_mem_bigComponentSet S hp hK4 haD ha1 i (hnorm i) hγ (hfix γ hγ)
      hζp hζP (B := conjSL (P γ)
        (Matrix.SpecialLinearGroup.map (algebraMap K (AlgebraicClosure K)) A))
      ⟨_, ⟨A, rfl⟩, rfl⟩
    exact (commute_conj_iff Z z _).1 (hcomm _ (Or.inl hmem))
  have hcommS : rootSpan τ (AlgebraicClosure K) (componentRoots (rootCharHom a) i) ≤
      Subgroup.centralizer {z⁻¹ * Z * z} := by
    refine (rootSpan_le_iSup_rootRankOne i).trans (iSup₂_le fun β hβ => ?_)
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.2
      (hcommγ β (simpleRoots_subset hβ) x hx).symm.eq
  intro x hx
  obtain ⟨B, rfl⟩ := hx
  have hxS := steinbergLang_rootSL2_mem_component K i hki B
  have hx' : z⁻¹ * rootSL2 τ (AlgebraicClosure K) (Pi.single k 1) B * z ∈
      rootSpan τ (AlgebraicClosure K) (componentRoots (rootCharHom a) i) := by
    refine (hnorm i _).2 ?_
    simpa [mul_assoc] using hxS
  have h1 : Commute (z⁻¹ * Z * z)
      (z⁻¹ * rootSL2 τ (AlgebraicClosure K) (Pi.single k 1) B * z) :=
    (Subgroup.mem_centralizer_singleton_iff.1 (hcommS hx')).symm
  have h2 := h1.map (MulAut.conj z).toMonoidHom
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h2
  have e1 : z * (z⁻¹ * Z * z) * z⁻¹ = Z := by group
  have e2 : z * (z⁻¹ * rootSL2 τ (AlgebraicClosure K) (Pi.single k 1) B * z) * z⁻¹ =
      rootSL2 τ (AlgebraicClosure K) (Pi.single k 1) B := by group
  rw [e1, e2] at h2
  exact h2

include hSD in
theorem steinbergLang_noFrobeniusInner (hτ : τ ≠ .G2) (hp : p.Prime)
    (hst : ∀ b : Fin τ.rank → (AlgebraicClosure K)ˣ, (∀ i, b i ^ p = 1) →
      rootCharStabilizerSubgroup b ≤ kernelReflectionGroup b)
    {w₀ : WeylGroup τ} (hw₀ : ∀ u : Fin τ.rank → ℤ, w₀ • u = -u)
    (hqp : Nat.card K % p = 1 ∨ Nat.card K % p = p - 1) (hK4 : 4 ≤ Nat.card K)
    (hq4 : Nat.card K ≠ 4 ∨ SimplyLacedTag τ)
    {D₁ : Subgroup (ModGL τ (AlgebraicClosure K))} (hD₁E : D₁ ≤ S.E)
    (hD₁c : Nat.card D₁ = p ^ 2) : NoFrobeniusInner S D₁ := by
  classical
  intro r f j _ hr hqf hj0 hjf z' hz'
  have hq := steinbergLang_q_eq K hFr hg0C hg0 S hSD
  obtain ⟨a, haD, ha1, hχ⟩ := steinbergLang_exists_plane_elt S hD₁E hD₁c (Pi.single 0 1)
  have hE := hD₁E haD
  have hk : (Pi.single 0 1 : Fin τ.rank → ℤ) ∈ kernelRoots (rootCharHom a) :=
    ⟨isRoot_single τ 0, hχ⟩
  set i : KernelComponent (rootCharHom a) := ⟦⟨_, hk⟩⟧ with hi
  set γ : Fin τ.rank → ℤ := Pi.single 0 1 with hγdef
  have hγ : γ ∈ componentRoots (rootCharHom a) i := ⟨hk, rfl⟩
  obtain ⟨z, P, hnorm, hfix, hζ⟩ :=
    steinbergLang_exists_family K hFr hg0C hg0 S hSD hp hst hw₀ hqp hE i
  obtain ⟨ζ, hζp, hζP⟩ := hζ γ hγ
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨j₁, g₁, hρ⟩ := exists_rootSL2_conjSL_eq (τ := τ) (L := AlgebraicClosure K) γ (P γ)
  have hxt : ∀ t : K, z * rootSL2 τ (AlgebraicClosure K) γ (conjSL (P γ)
      (Matrix.SpecialLinearGroup.map (algebraMap K (AlgebraicClosure K)) (uSL t))) * z⁻¹ =
      (z * g₁) * pinnedX τ (AlgebraicClosure K) (Pi.single j₁ 1)
        (((pinnedData τ (Pi.single j₁ 1)).2.2 : AlgebraicClosure K) *
          algebraMap K (AlgebraicClosure K) t) * (z * g₁)⁻¹ := by
    intro t
    rw [hρ, sl2_map_uSL, ← rootSL2_single, rootSL2_uSL_eq, zsmul_eq_mul]
    group
  have hεL : ((pinnedData τ (Pi.single j₁ 1)).2.2 : AlgebraicClosure K) ≠ 0 := by
    rcases pinnedSign_eq τ (Pi.single j₁ 1 : Fin τ.rank → ℤ) with h | h <;> rw [h] <;> simp
  obtain ⟨a₀, b₀, ha₀, hrk₀, hab⟩ := conj_map_pinnedX_expand hτ (RingHom.id _) (z * g₁) hεL
    (Pi.single j₁ 1)
  set ψ : AlgebraicClosure K →+* AlgebraicClosure K := iterateFrobenius (AlgebraicClosure K) r j
    with hψ
  obtain ⟨a₁, b₁, ha₁, hrk₁, hab'⟩ := conj_map_pinnedX_expand hτ ψ (z * g₁) hεL
    (Pi.single j₁ 1)
  have hψpow : ∀ x : AlgebraicClosure K, ψ x = x ^ (r ^ j) := fun x => by
    rw [hψ, iterateFrobenius_def]
  have hid : ∀ x : ModGL τ (AlgebraicClosure K),
      Units.map (entrywiseHom (RingHom.id (AlgebraicClosure K))) x = x :=
    fun x => Units.ext (entrywise_id _)
  have hr2 := hr.two_le
  have hf1 : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · rw [h0, pow_zero, hq] at hqf
      omega
    · exact h0
  have hmain : ∀ t : K,
      (z' : Module.End (AlgebraicClosure K) (RootModule τ (AlgebraicClosure K))) *
        evAt ((algebraMap K (AlgebraicClosure K) t) ^ (r ^ j))
          (prodList (r ^ f) (fun _ => a₁) (fun _ => b₁) [0]) *
        ((z'⁻¹ : ModGL τ (AlgebraicClosure K)) :
          Module.End (AlgebraicClosure K) (RootModule τ (AlgebraicClosure K))) =
        evAt (algebraMap K (AlgebraicClosure K) t)
          (prodList (r ^ f) (fun _ => a₀) (fun _ => b₀) [0]) := by
    intro t
    have hmem := steinbergLang_mem_bigComponentSet S hp hK4 haD ha1 i (hnorm i) hγ (hfix γ hγ)
      hζp hζP (B := conjSL (P γ) (Matrix.SpecialLinearGroup.map
        (algebraMap K (AlgebraicClosure K)) (uSL t))) ⟨_, ⟨uSL t, rfl⟩, rfl⟩
    have h := hz' _ (Or.inl hmem)
    rw [hxt] at h
    set X := z * g₁ * pinnedX τ (AlgebraicClosure K) (Pi.single j₁ 1)
      (((pinnedData τ (Pi.single j₁ 1)).2.2 : AlgebraicClosure K) *
        algebraMap K (AlgebraicClosure K) t) * (z * g₁)⁻¹ with hX
    have hEnd : (z' : Module.End (AlgebraicClosure K) (RootModule τ (AlgebraicClosure K))) *
        ((Units.map (entrywiseHom ψ) X : ModGL τ (AlgebraicClosure K)) :
          Module.End (AlgebraicClosure K) (RootModule τ (AlgebraicClosure K))) *
        ((z'⁻¹ : ModGL τ (AlgebraicClosure K)) :
          Module.End (AlgebraicClosure K) (RootModule τ (AlgebraicClosure K))) =
        (X : Module.End (AlgebraicClosure K) (RootModule τ (AlgebraicClosure K))) := by
      rw [← Units.val_mul, ← Units.val_mul, h]
    have e1 := hab (algebraMap K (AlgebraicClosure K) t)
    rw [hid] at e1
    have e2 := hab' (algebraMap K (AlgebraicClosure K) t)
    rw [e1, e2, hψpow] at hEnd
    rw [evAt_prodList, evAt_prodList]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, pow_zero,
      pow_one]
    simpa using hEnd
  have hcardK : Fintype.card K = (r ^ f) ^ 1 := by
    rw [← Nat.card_eq_fintype_card, ← hq, hqf, pow_one]
  by_cases hex : r ^ j = 2 ∧ r ^ f = 4
  ·
    obtain ⟨hrj, hrf⟩ := hex
    have hsl : SimplyLacedTag τ := by
      rcases hq4 with h | h
      · exact absurd (by rw [← hq, hqf, hrf]) h
      · exact h
    have hm4 := twisted_conj_q4 (algebraMap K (AlgebraicClosure K)) one_pos
      (by rw [hcardK, hrf]) [0] (List.nodup_singleton 0) (List.mem_singleton_self 0)
      (fun k hk => by rw [List.mem_singleton] at hk; omega)
      (fun _ => a₀) (fun _ => b₀) (fun _ => a₁) (fun _ => b₁) z' (fun t => by
        have := hmain t
        rwa [hrf, hrj] at this)
    obtain ⟨h1, -⟩ := hrk₁ hsl
    obtain ⟨-, h2⟩ := hrk₀ hsl
    have h3 := finrank_range_conj_eq z' a₁
    rw [hm4] at h3
    omega
  · refine no_twisted_conj (algebraMap K (AlgebraicClosure K)) hr hj0 hjf one_pos hcardK
      (by rw [← hqf, hq]; exact hK4) (fun hc2 => ?_) [0] (List.nodup_singleton 0)
      (List.mem_singleton_self 0) (fun k hk => by rw [List.mem_singleton] at hk; omega)
      (fun _ => a₀) (fun _ => b₀) (fun _ => a₁) (fun _ => b₁) ha₀ ha₁ z' hmain
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
      · exact hex ⟨hc2, by norm_num⟩
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by omega) hf3

end Rigid

end CFSG.HardMathSupport.Timmesfeld.CrossChar
