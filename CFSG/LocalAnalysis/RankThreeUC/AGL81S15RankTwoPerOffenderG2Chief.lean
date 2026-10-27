module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoG2Offender

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.Open CFSG.RankThree.FFModules CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall
open Module

private noncomputable def g2c_factorG2 {K : Type*} [Group K] {V : Type*}
    [AddCommGroup V] [Module (ZMod 2) V] [Finite V] {ρ : Representation (ZMod 2) K V}
    {F : Type} [Field F] (ψ : K ⧸ CFSG.pCore 2 K ≃* ↥(cayleyGroup F))
    {U U' : Subrepresentation ρ} (h : U ⋖ U') :
    Representation (ZMod 2) ↥(cayleyGroup F) (U'.toSubmodule ⧸ factorSub U U') :=
  have := factor_isTrivial_pCore h
  ((factorRep U U').ofQuotient (CFSG.pCore 2 K)).comp ψ.symm.toMonoidHom

private theorem g2c_factorG2_apply {K : Type*} [Group K] {V : Type*}
    [AddCommGroup V] [Module (ZMod 2) V] [Finite V] {ρ : Representation (ZMod 2) K V}
    {F : Type} [Field F] (ψ : K ⧸ CFSG.pCore 2 K ≃* ↥(cayleyGroup F))
    {U U' : Subrepresentation ρ} (h : U ⋖ U') (k : K)
    (x : U'.toSubmodule ⧸ factorSub U U') :
    g2c_factorG2 ψ h (ψ (k : K ⧸ CFSG.pCore 2 K)) x = factorRep U U' k x := by
  simp only [g2c_factorG2, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.symm_apply_apply, Representation.ofQuotient_coe_apply]

private theorem g2c_factorG2_isIrreducible {K : Type*} [Group K] {V : Type*}
    [AddCommGroup V] [Module (ZMod 2) V] [Finite V] {ρ : Representation (ZMod 2) K V}
    {F : Type} [Field F] (ψ : K ⧸ CFSG.pCore 2 K ≃* ↥(cayleyGroup F))
    {U U' : Subrepresentation ρ} (h : U ⋖ U') :
    (g2c_factorG2 ψ h).IsIrreducible := by
  have : Nontrivial (U'.toSubmodule ⧸ factorSub U U') := factor_nontrivial h
  have hnt : Nontrivial (Subrepresentation (g2c_factorG2 ψ h)) := by
    refine ⟨⟨⊥, ⊤, fun he => ?_⟩⟩
    obtain ⟨x, hx⟩ := exists_ne (0 : U'.toSubmodule ⧸ factorSub U U')
    have h1 : x ∈ (⊤ : Subrepresentation (g2c_factorG2 ψ h)).toSubmodule := Submodule.mem_top
    rw [← he] at h1
    exact hx h1
  refine IsSimpleOrder.mk fun a => ?_
  have hinv : ∀ k, ∀ x ∈ a.toSubmodule, factorRep U U' k x ∈ a.toSubmodule := by
    intro k x hx
    rw [← g2c_factorG2_apply ψ h]
    exact a.apply_mem_toSubmodule _ hx
  rcases factor_invariant_eq_bot_or_top h a.toSubmodule hinv with hb | ht
  · exact Or.inl (Subrepresentation.toSubmodule_injective hb)
  · exact Or.inr (Subrepresentation.toSubmodule_injective ht)

private theorem g2c_factorG2_irr {K : Type*} [Group K] {V : Type*}
    [AddCommGroup V] [Module (ZMod 2) V] [Finite V] {ρ : Representation (ZMod 2) K V}
    {F : Type} [Field F] (ψ : K ⧸ CFSG.pCore 2 K ≃* ↥(cayleyGroup F))
    {U U' : Subrepresentation ρ} (h : U ⋖ U') :
    ∀ X : Submodule (ZMod 2) (U'.toSubmodule ⧸ factorSub U U'),
      (∀ g, ∀ x ∈ X, g2c_factorG2 ψ h g x ∈ X) → X = ⊥ ∨ X = ⊤ := by
  intro X hX
  let S : Subrepresentation (g2c_factorG2 ψ h) :=
    { toSubmodule := X
      apply_mem_toSubmodule := hX }
  rcases (show IsSimpleOrder (Subrepresentation (g2c_factorG2 ψ h)) from
    g2c_factorG2_isIrreducible ψ h).eq_bot_or_eq_top S with hb | ht
  · left
    exact congrArg Subrepresentation.toSubmodule hb
  · right
    exact congrArg Subrepresentation.toSubmodule ht

private theorem g2c_fixSub_factorG2 {K : Type*} [Group K] {V : Type*}
    [AddCommGroup V] [Module (ZMod 2) V] [Finite V] {ρ : Representation (ZMod 2) K V}
    {F : Type} [Field F] (ψ : K ⧸ CFSG.pCore 2 K ≃* ↥(cayleyGroup F))
    {U U' : Subrepresentation ρ} (h : U ⋖ U') (A : Subgroup K) :
    fixSub (g2c_factorG2 ψ h) ((A.map (QuotientGroup.mk' (CFSG.pCore 2 K))).map ψ.toMonoidHom) =
      fixSub (factorRep U U') A := by
  ext x
  rw [mem_fixSub, mem_fixSub]
  constructor
  · intro hx a ha
    rw [← g2c_factorG2_apply ψ h]
    exact hx _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
  · rintro hx _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    have := g2c_factorG2_apply ψ h a x
    simp only [QuotientGroup.mk'_apply, MulEquiv.coe_toMonoidHom] at this ⊢
    rw [this]
    exact hx a ha

private theorem g2c_factor_data_g2
    {K : Type*} [Group K] {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {ρ : Representation (ZMod 2) K V}
    {F : Type} [Field F] [Fintype F] [CharP F 2] {n : ℕ} (hn : 2 ≤ n)
    (hF : Nat.card F = 2 ^ n) (hs : IsSimpleGroup ↥(cayleyGroup F))
    (ψ : K ⧸ CFSG.pCore 2 K ≃* ↥(cayleyGroup F)) {r : ℕ}
    {Vs : Fin (r + 1) → Subrepresentation ρ} (hVs : IsCompositionSeries r Vs)
    (A : Subgroup K) [CFSG.IsElementaryAbelian 2 A] (hA : ¬ A ≤ CFSG.pCore 2 K)
    (hsum : ∑ i ∈ nontrivialFactors Vs, factorCodim Vs A i ≤
      Nat.log 2 (Nat.card (A.map (QuotientGroup.mk' (CFSG.pCore 2 K)))))
    {i : Fin r} (hi : i ∈ nontrivialFactors Vs) :
    (∃ φ : ((Vs i.succ).toSubmodule ⧸ factorSub (Vs i.castSucc) (Vs i.succ)) ≃+ (Ix3 → F),
        ∀ (k : K) (x : (Vs i.succ).toSubmodule ⧸ factorSub (Vs i.castSucc) (Vs i.succ)),
          φ (factorRep (Vs i.castSucc) (Vs i.succ) k x) =
            g2Act (ψ (k : K ⧸ CFSG.pCore 2 K)) (φ x)) ∧
      Nat.log 2 (Nat.card (A.map (QuotientGroup.mk' (CFSG.pCore 2 K)))) ≤
        factorCodim Vs A i := by
  classical
  have hFc : Fintype.card F = 2 ^ n := by
    rw [← Nat.card_eq_fintype_card]
    exact hF
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := CFSG.pCore 2 K with hP
  set Abar := A.map (QuotientGroup.mk' P) with hAbar
  set B := Abar.map ψ.toMonoidHom with hB
  have : CFSG.IsElementaryAbelian 2 Abar := CFSG.IsElementaryAbelian.map (QuotientGroup.mk' P)
  have : CFSG.IsElementaryAbelian 2 B := CFSG.IsElementaryAbelian.map ψ.toMonoidHom
  have hcardB : Nat.card B = Nat.card Abar :=
    Subgroup.card_map_of_injective ψ.injective
  have hBne : B ≠ ⊥ := by
    obtain ⟨a, haA, haP⟩ := Set.not_subset.mp hA
    intro hbot
    have hmem : ψ (a : K ⧸ P) ∈ B := by
      rw [hB]
      exact ⟨_, ⟨a, haA, rfl⟩, rfl⟩
    rw [hbot, Subgroup.mem_bot, map_eq_one_iff _ ψ.injective, QuotientGroup.eq_one_iff] at hmem
    exact haP hmem
  have : Finite (K ⧸ P) := Finite.of_injective ψ ψ.injective
  have : Finite Abar :=
    Finite.of_injective (fun x : Abar => (x : K ⧸ P)) fun _ _ h => Subtype.ext h
  have hpAbar : IsPGroup 2 Abar := CFSG.IsElementaryAbelian.isPGroup 2 Abar
  obtain ⟨k0, hk0⟩ := hpAbar.exists_card_eq
  have hAbarPow : Nat.card Abar = 2 ^ Nat.log 2 (Nat.card Abar) := by
    rw [hk0, Nat.log_pow (by norm_num)]
  have hBpow : Nat.card B = 2 ^ Nat.log 2 (Nat.card Abar) :=
    hcardB.trans hAbarPow
  have hcov : Vs i.castSucc ⋖ Vs i.succ := hVs.covBy i
  let W := (Vs i.succ).toSubmodule ⧸ factorSub (Vs i.castSucc) (Vs i.succ)
  let π : ↥(cayleyGroup F) →* (W ≃ₗ[ZMod 2] W) := repGL (g2c_factorG2 ψ hcov)
  set Ai : Subgroup (W ≃ₗ[ZMod 2] W) := B.map π with hAi
  have : CFSG.IsElementaryAbelian 2 Ai := by
    rw [hAi]
    exact CFSG.IsElementaryAbelian.map π
  have hntπ : ∃ g, π g ≠ 1 := by
    obtain ⟨k, hk⟩ := mem_nontrivialFactors.mp hi
    refine ⟨ψ (k : K ⧸ P), fun h1 => hk ?_⟩
    refine LinearMap.ext fun x => ?_
    have h2 : (g2c_factorG2 ψ hcov) (ψ (k : K ⧸ P)) = 1 := by
      apply LinearMap.ext
      intro y
      have := congrArg (fun (e : W ≃ₗ[ZMod 2] W) => e y) h1
      simpa [π, repGL_apply] using this
    rw [← g2c_factorG2_apply ψ hcov k x, h2]
  have hπinj : Function.Injective π := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal π.ker with hbot | htop
    · exact hbot
    · exfalso
      obtain ⟨g, hg⟩ := hntπ
      exact hg (MonoidHom.mem_ker.mp (by rw [htop]; exact Subgroup.mem_top g))
  have hcardAi : Nat.card Ai = Nat.card B := by
    rw [hAi]
    exact Subgroup.card_map_of_injective hπinj
  have hA1 : Ai ≠ ⊥ := by
    intro hbot
    apply hBne
    rw [Subgroup.eq_bot_iff_forall]
    intro b hb
    have hmem : π b ∈ Ai := by
      rw [hAi]
      exact ⟨b, hb, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hπinj (by rw [hmem, map_one])
  have hirr : ∀ U : Submodule (ZMod 2) W,
      (∀ g, ∀ u ∈ U, π g u ∈ U) → U = ⊥ ∨ U = ⊤ := by
    intro U hU
    exact g2c_factorG2_irr ψ hcov U fun g u hu => hU g u hu
  have hWnt : Nontrivial W := factor_nontrivial hcov
  have hnorm : ∀ a ∈ Ai, ∀ x, ∃ y, a * π x * a⁻¹ = π y := by
    intro a ha x
    rw [hAi] at ha
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp ha
    refine ⟨b * x * b⁻¹, ?_⟩
    rw [← map_mul, ← map_inv, ← map_mul]
  have hfix : fixSub (g2c_factorG2 ψ hcov) B =
      fixSub (factorRep (Vs i.castSucc) (Vs i.succ)) A := by
    rw [hB, hAbar]
    exact g2c_fixSub_factorG2 ψ hcov A
  have hfixcard : Nat.card ↥(fixSub (g2c_factorG2 ψ hcov) B) =
      Nat.card {m : W // ∀ a ∈ Ai, a m = m} := by
    apply Nat.card_congr
    refine Equiv.subtypeEquivRight fun m => ?_
    rw [mem_fixSub]
    constructor
    · intro hm a ha
      rw [hAi] at ha
      obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp ha
      rw [repGL_apply, hm b hb]
    · intro hm b hb
      have := hm (π b) (by rw [hAi]; exact ⟨b, hb, rfl⟩)
      rwa [repGL_apply] at this
  have hsingle : factorCodim Vs A i ≤ Nat.log 2 (Nat.card Abar) :=
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hi).trans hsum
  have h2b : 2 ^ (finrank (ZMod 2) W - finrank (ZMod 2) (fixSub (g2c_factorG2 ψ hcov) B)) ≤
      Nat.card Ai := by
    have hcod : factorCodim Vs A i =
        finrank (ZMod 2) W - finrank (ZMod 2) (fixSub (g2c_factorG2 ψ hcov) B) := by
      rw [factorCodim, ← hfix]
    rw [← hcod]
    calc 2 ^ factorCodim Vs A i ≤ 2 ^ Nat.log 2 (Nat.card Abar) :=
          Nat.pow_le_pow_right (by norm_num) hsingle
      _ = Nat.card Abar := hAbarPow.symm
      _ = Nat.card Ai := by rw [hcardAi, hcardB]
  have hoff : Nat.card W ≤ Nat.card Ai * Nat.card {m : W // ∀ a ∈ Ai, a m = m} := by
    have h := card_mul_le_of_codim (g2c_factorG2 ψ hcov) B (n := 1) (m := Nat.card Ai) ?_
    · rw [mul_one] at h
      rwa [hfixcard] at h
    · simpa using h2b
  obtain ⟨φ, hφ⟩ :=
    CFSG.Quasithin.B42G2F.exists_natural_of_offender (K := F) hFc hn π hπinj hWnt hirr Ai hnorm
      (inferInstance : CFSG.IsElementaryAbelian 2 Ai) hA1 hoff
  obtain ⟨-, hineq⟩ :=
    g2_offender_facts_of_natural hn hFc π hπinj hWnt hirr Ai hnorm
      (inferInstance : CFSG.IsElementaryAbelian 2 Ai) hA1 hoff
  have hb_le : Nat.log 2 (Nat.card Abar) ≤ factorCodim Vs A i := by
    have hpow : 2 ^ Nat.log 2 (Nat.card Abar) *
        Nat.card ↥(fixSub (g2c_factorG2 ψ hcov) B) ≤ Nat.card W := by
      rw [hfixcard, ← hBpow, ← hcardAi]
      exact hineq
    have hcod : Nat.log 2 (Nat.card Abar) ≤
        finrank (ZMod 2) W - finrank (ZMod 2) (fixSub (g2c_factorG2 ψ hcov) B) :=
      le_codim_of_card hpow
    rw [show factorCodim Vs A i =
        finrank (ZMod 2) W - finrank (ZMod 2) (fixSub (g2c_factorG2 ψ hcov) B) from by
      rw [factorCodim, ← hfix]]
    exact hcod
  refine ⟨⟨φ, fun k x => ?_⟩, hb_le⟩
  rw [← g2c_factorG2_apply ψ hcov k x]
  exact hφ (ψ (k : K ⧸ P)) x

theorem chief_factors_g2
    {K : Type} [Group K] {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {ρ : Representation (ZMod 2) K V} {F : Type} [Field F] [Fintype F] [CharP F 2] {n : ℕ}
    (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) (hs : IsSimpleGroup ↥(cayleyGroup F))
    (ψ : K ⧸ CFSG.pCore 2 K ≃* ↥(cayleyGroup F)) {r : ℕ}
    {Vs : Fin (r + 1) → Subrepresentation ρ} (hVs : IsCompositionSeries r Vs)
    (A : Subgroup K) [CFSG.IsElementaryAbelian 2 A] (hA : ¬ A ≤ CFSG.pCore 2 K)
    (hsum : ∑ i ∈ nontrivialFactors Vs, factorCodim Vs A i ≤
      Nat.log 2 (Nat.card (A.map (QuotientGroup.mk' (CFSG.pCore 2 K))))) :
    (nontrivialFactors Vs).card ≤ 1 ∧
      ∀ i ∈ nontrivialFactors Vs,
        ∃ φ : ((Vs i.succ).toSubmodule ⧸ factorSub (Vs i.castSucc) (Vs i.succ)) ≃+ (Ix3 → F),
          ∀ (k : K) (x : (Vs i.succ).toSubmodule ⧸ factorSub (Vs i.castSucc) (Vs i.succ)),
            φ (factorRep (Vs i.castSucc) (Vs i.succ) k x) =
              g2Act (ψ (k : K ⧸ CFSG.pCore 2 K)) (φ x) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (K ⧸ CFSG.pCore 2 K) := Finite.of_injective ψ ψ.injective
  have : Finite ↥(A.map (QuotientGroup.mk' (CFSG.pCore 2 K))) :=
    Finite.of_injective (fun x => (x : K ⧸ CFSG.pCore 2 K)) fun _ _ h => Subtype.ext h
  have : CFSG.IsElementaryAbelian 2 ↥(A.map (QuotientGroup.mk' (CFSG.pCore 2 K))) :=
    CFSG.IsElementaryAbelian.map (QuotientGroup.mk' (CFSG.pCore 2 K))
  have hAbar_ne : A.map (QuotientGroup.mk' (CFSG.pCore 2 K)) ≠ ⊥ := by
    intro hbot
    obtain ⟨a, haA, haP⟩ := Set.not_subset.mp hA
    have hmem : (a : K ⧸ CFSG.pCore 2 K) ∈ A.map (QuotientGroup.mk' (CFSG.pCore 2 K)) :=
      ⟨a, haA, rfl⟩
    rw [hbot, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hmem
    exact haP hmem
  have hpAbar : IsPGroup 2 ↥(A.map (QuotientGroup.mk' (CFSG.pCore 2 K))) :=
    CFSG.IsElementaryAbelian.isPGroup 2 _
  obtain ⟨k0, hk0⟩ := hpAbar.exists_card_eq
  have hAbarPow : Nat.card ↥(A.map (QuotientGroup.mk' (CFSG.pCore 2 K))) =
      2 ^ Nat.log 2 (Nat.card ↥(A.map (QuotientGroup.mk' (CFSG.pCore 2 K)))) := by
    rw [hk0, Nat.log_pow (by norm_num)]
  have hb1 : 1 ≤ Nat.log 2 (Nat.card ↥(A.map (QuotientGroup.mk' (CFSG.pCore 2 K)))) := by
    have hcard2 : 2 ≤ Nat.card ↥(A.map (QuotientGroup.mk' (CFSG.pCore 2 K))) := by
      have hne1 : Nat.card ↥(A.map (QuotientGroup.mk' (CFSG.pCore 2 K))) ≠ 1 :=
        fun h => hAbar_ne (Subgroup.card_eq_one.mp h)
      have hpos : 0 < Nat.card ↥(A.map (QuotientGroup.mk' (CFSG.pCore 2 K))) := Nat.card_pos
      omega
    rcases Nat.eq_zero_or_pos
        (Nat.log 2 (Nat.card ↥(A.map (QuotientGroup.mk' (CFSG.pCore 2 K))))) with h0 | hpos
    · exfalso
      have h1 : Nat.card ↥(A.map (QuotientGroup.mk' (CFSG.pCore 2 K))) = 1 := by
        rw [hAbarPow, h0, pow_zero]
      omega
    · exact hpos
  refine ⟨?_, ?_⟩
  · rw [Finset.card_le_one]
    intro i hi j hj
    by_contra hij
    have h1 := (g2c_factor_data_g2 hn hF hs ψ hVs A hA hsum hi).2
    have h2 := (g2c_factor_data_g2 hn hF hs ψ hVs A hA hsum hj).2
    have hsub : ({i, j} : Finset (Fin r)) ⊆ nontrivialFactors Vs := by
      intro x hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hi
      · exact hj
    have hsum2 : factorCodim Vs A i + factorCodim Vs A j ≤
        Nat.log 2 (Nat.card ↥(A.map (QuotientGroup.mk' (CFSG.pCore 2 K)))) := by
      calc factorCodim Vs A i + factorCodim Vs A j
          = ∑ x ∈ ({i, j} : Finset (Fin r)), factorCodim Vs A x := by
            rw [Finset.sum_pair hij]
        _ ≤ ∑ x ∈ nontrivialFactors Vs, factorCodim Vs A x :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => Nat.zero_le _)
        _ ≤ _ := hsum
    omega
  · intro i hi
    exact (g2c_factor_data_g2 hn hF hs ψ hVs A hA hsum hi).1

end CFSG.LocalAnalysis.RankThreeUC.S15

end
