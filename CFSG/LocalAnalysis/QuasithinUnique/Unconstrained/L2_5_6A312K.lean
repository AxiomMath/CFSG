module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_6A312Ord
public import CFSG.LieType.Simplicity.Classical
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_6
public import CFSG.Adapters.LinearFieldTransport

public section

namespace CFSG.QuasithinUnique.Unc25G2

namespace A312Sub

open CFSG.Open CFSG.Quasithin
open CFSG.QuasithinUnique.Vol2Native.A312L

theorem isSimpleGroup_of_stated {X : Type} [Group X] {t : CFSG.Assembly.LowTwoRank.StatedLieTag}
    {n p f : ℕ} (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel X t n p f) : IsSimpleGroup X :=
  (CFSG.LieType.Simplicity.fam_classical_converse X
    ((CFSG.Milestones.fam_classical_model_membership_alltags X).2 ⟨t, n, p, f, h⟩)).2.2

theorem not_isPGroup_two_of_quasisimple {Q : Type*} [Group Q] [Finite Q]
    (hQ : CFSG.IsQuasisimple Q) : ¬ IsPGroup 2 Q := by
  intro h2
  have : Group.IsNilpotent Q := h2.isNilpotent
  have hs : Group.IsSolvable Q := inferInstance
  obtain ⟨a, b, hab⟩ := hQ.2.2
  have : Nontrivial (Q ⧸ Subgroup.center Q) := ⟨⟨a, b, fun h => hab (by rw [h])⟩⟩
  have hne : Nontrivial Q := (QuotientGroup.mk_surjective (s := Subgroup.center Q)).nontrivial
  exact (Group.IsSolvable.commutator_lt_top_of_nontrivial (G := Q)).ne (Group.isPerfect_def.mp hQ.1)

theorem pCore_eq_bot_of_simple {Q : Type*} [Group Q] [Finite Q] [IsSimpleGroup Q]
    (hnp : ¬ IsPGroup 2 Q) : CFSG.pCore 2 Q = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (CFSG.pCore 2 Q) with h | h
  · exact h
  · exfalso
    apply hnp
    have := CFSG.pCore_isPGroup (p := 2) (G := Q)
    rw [h] at this
    exact IsPGroup.of_equiv this Subgroup.topEquiv

theorem fusionIsBenderGroup_of_isPSL {X : Type} [Group X] {n : ℕ} (h : IsPSL 2 2 n X) :
    fusionIsBenderGroup X := by
  obtain ⟨hadm, K, hF, hFin, hK, ⟨e⟩⟩ := h
  have hn : 2 ≤ n := by
    have h1 : 1 ≤ n := hadm.2.1
    have h2 : (2, 2 ^ n) ≠ (2, 2) := hadm.2.2.2.1
    by_contra hlt
    apply h2
    have : n = 1 := by omega
    subst this
    norm_num
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype K := Fintype.ofFinite K
  have : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  have hcard : Fintype.card K = Fintype.card (GaloisField 2 n) := by
    rw [← Nat.card_eq_fintype_card, hK, ← Nat.card_eq_fintype_card,
      GaloisField.card 2 n (by omega)]
  let φ : K ≃+* GaloisField 2 n := FiniteField.ringEquivOfCardEq hcard
  exact Or.inl ⟨n, hn, ⟨e.trans ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm.trans
    (CFSG.ClassicalModels.projectiveSpecialLinearFieldEquiv φ (Fin 2)))⟩⟩

theorem simple_or_cover
    {G : Type} [Group G] {K : Subgroup G} (hKl : IsListed25 K)
    (hKnb : ¬ fusionIsBenderGroup ↥K) :
    IsSimpleGroup ↥K ∨ StatedClassicalModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL 3 2 2 := by
  rcases hKl with hB | hR | ⟨h33 | ⟨⟨e⟩⟩⟩ | ⟨p, -, -, hp⟩
  · exact absurd hB hKnb
  · rcases hR with ⟨n, -, h⟩ | ⟨n, -, h⟩ | ⟨⟨e⟩⟩ | h
    · exact Or.inl (isSimpleGroup_of_stated (t := .PSL) h)
    · exact Or.inl (isSimpleGroup_of_stated (t := .PSp) h)
    · have : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
      exact Or.inl e.isSimpleGroup
    · exact Or.inr h
  · exact Or.inl (isSimpleGroup_of_stated (t := .PSL) h33)
  · have hs : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .M11) :=
      (CFSG.Sporadic.Mathieu.fam_m11_simplicity).2.2
    exact Or.inl (e.isSimpleGroup)
  · exact Or.inl (isSimpleGroup_of_stated (t := .PSL) hp)

theorem quot_equiv {K B : Type*} [Group K] [Group B] [Finite K] [Finite B] (ψ : K →* B)
    (hψs : Function.Surjective ψ) (hψk : IsPGroup 2 ψ.ker)
    (hYs : IsSimpleGroup (K ⧸ CFSG.pCore 2 K)) (hYnp : ¬ IsPGroup 2 (K ⧸ CFSG.pCore 2 K)) :
    Nonempty ((B ⧸ CFSG.pCore 2 B) ≃* (K ⧸ CFSG.pCore 2 K)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π₀ := QuotientGroup.mk' (CFSG.pCore 2 K) with hπ₀
  have hle : ψ.ker ≤ π₀.ker := by
    rw [hπ₀, QuotientGroup.ker_mk']
    exact le_sSup ⟨inferInstance, hψk⟩
  let θ : B →* (K ⧸ CFSG.pCore 2 K) := (MonoidHom.liftOfSurjective ψ hψs) ⟨π₀, hle⟩
  have hθψ : ∀ x, θ (ψ x) = π₀ x := fun x => by
    exact MonoidHom.liftOfRightInverse_comp_apply ψ (Function.surjInv hψs)
      (Function.rightInverse_surjInv hψs) ⟨π₀, hle⟩ x
  have hθs : Function.Surjective θ := fun y => by
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective y
    exact ⟨ψ k, hθψ k⟩
  have hker : θ.ker = CFSG.pCore 2 B := by
    apply le_antisymm
    · intro x hx
      obtain ⟨k, rfl⟩ := hψs x
      have h1 : π₀ k = 1 := by rw [← hθψ]; exact hx
      have hk : k ∈ CFSG.pCore 2 K := (QuotientGroup.eq_one_iff k).mp h1
      have hN : ((CFSG.pCore 2 K).map ψ).Normal :=
        Subgroup.Normal.map CFSG.pCore_normal ψ hψs
      have hP : IsPGroup 2 ((CFSG.pCore 2 K).map ψ) :=
        (CFSG.pCore_isPGroup (p := 2) (G := K)).map ψ
      have hmap : (CFSG.pCore 2 K).map ψ ≤ CFSG.pCore 2 B := le_sSup ⟨hN, hP⟩
      exact hmap ⟨k, hk, rfl⟩
    · intro x hx
      have hN : ((CFSG.pCore 2 B).map θ).Normal :=
        Subgroup.Normal.map CFSG.pCore_normal θ hθs
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((CFSG.pCore 2 B).map θ) with h | h
      · have : θ x ∈ (CFSG.pCore 2 B).map θ := ⟨x, hx, rfl⟩
        rw [h] at this
        exact this
      · exfalso
        apply hYnp
        have := (CFSG.pCore_isPGroup (p := 2) (G := B)).map θ
        rw [h] at this
        exact IsPGroup.of_equiv this Subgroup.topEquiv
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective θ hθs)⟩


theorem card_alt_five_loc : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  decide

theorem card_alt_six_loc : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  decide

theorem two_pow_mul_ne_20160 (n : ℕ) : 2 ^ n * (4 ^ n - 1) ≠ 20160 := by
  by_cases hn : n ≤ 4
  · interval_cases n <;> norm_num
  · push Not at hn
    have h1 : 2 ^ 5 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have h2 : 4 ^ 5 ≤ 4 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have h3 : 32 * 1023 ≤ 2 ^ n * (4 ^ n - 1) := Nat.mul_le_mul (by simpa using h1) (by omega)
    omega

theorem K_side
    {G : Type} [Group G] {K : Subgroup G} (hKq : CFSG.IsQuasisimple ↥K)
    (hKl : IsListed25 K) (hKnb : ¬ fusionIsBenderGroup ↥K) {B : Type} [Group B] [Finite B]
    [Finite G] (ψ : ↥K →* B) (hψs : Function.Surjective ψ) (hψk : IsPGroup 2 ψ.ker) :
    (¬ ∃ n : ℕ, IsPSL 2 2 n (B ⧸ CFSG.pCore 2 B)) ∧ ¬ IsAlt 5 B ∧
      (IsAlt 6 B → Nonempty (↥K ≃* alternatingGroup (Fin 6))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases simple_or_cover hKl hKnb with hS | hC
  ·
    have hKnp : ¬ IsPGroup 2 ↥K := not_isPGroup_two_of_quasisimple hKq
    have hkerbot : ψ.ker = ⊥ := by
      have := hS
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ψ.ker with h | h
      · exact h
      · exfalso
        apply hKnp
        rw [h] at hψk
        exact IsPGroup.of_equiv hψk Subgroup.topEquiv
    let e : ↥K ≃* B := MulEquiv.ofBijective ψ ⟨(MonoidHom.ker_eq_bot_iff ψ).mp hkerbot, hψs⟩
    have hBs : IsSimpleGroup B := @MulEquiv.isSimpleGroup B _ ↥K _ hS e.symm
    have hBnp : ¬ IsPGroup 2 B := fun h => hKnp (IsPGroup.of_equiv h e.symm)
    have hpc : CFSG.pCore 2 B = ⊥ := @pCore_eq_bot_of_simple B _ _ hBs hBnp
    let q : (B ⧸ CFSG.pCore 2 B) ≃* B :=
      (QuotientGroup.quotientMulEquivOfEq hpc).trans QuotientGroup.quotientBot
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨n, hn⟩
      exact hKnb (fusionIsBenderGroup_of_isPSL (IsPSL.of_mulEquiv (q.trans e.symm) hn))
    · intro h5
      have h1 : IsPSL 2 2 2 B := CFSG.QuasithinUnique.Ch1.statedClassicalModel_psl_two_four_of_alternating_five B h5
      exact hKnb (fusionIsBenderGroup_of_isPSL (IsPSL.of_mulEquiv e.symm h1))
    · intro h6
      obtain ⟨f⟩ := h6
      exact ⟨e.trans f⟩
  ·
    have hYs : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K) := isSimpleGroup_of_stated (t := .PSL) hC
    have hY := card_psl_three_four (X := ↥K ⧸ CFSG.pCore 2 ↥K) hC
    have hYnp : ¬ IsPGroup 2 (↥K ⧸ CFSG.pCore 2 ↥K) := by
      intro h2
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp h2
      have h3 : 3 ∣ 2 ^ n := by rw [← hn, hY]; norm_num
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
      omega
    obtain ⟨q⟩ := quot_equiv ψ hψs hψk hYs hYnp
    have hq : Nat.card (B ⧸ CFSG.pCore 2 B) = 20160 := by rw [Nat.card_congr q.toEquiv, hY]
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨n, hn⟩
      have := card_psl_two_even hn
      rw [hq] at this
      exact two_pow_mul_ne_20160 n this.symm
    · intro h5
      obtain ⟨f⟩ := h5
      have h60 : Nat.card B = 60 := (Nat.card_congr f.toEquiv).trans card_alt_five_loc
      have := Subgroup.card_quotient_dvd_card (CFSG.pCore 2 B)
      rw [hq, h60] at this
      omega
    · intro h6
      exfalso
      obtain ⟨f⟩ := h6
      have h360 : Nat.card B = 360 := (Nat.card_congr f.toEquiv).trans card_alt_six_loc
      have := Subgroup.card_quotient_dvd_card (CFSG.pCore 2 B)
      rw [hq, h360] at this
      omega


end A312Sub

end CFSG.QuasithinUnique.Unc25G2
