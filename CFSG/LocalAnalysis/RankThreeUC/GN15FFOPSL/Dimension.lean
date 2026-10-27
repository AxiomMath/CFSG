module

public import CFSG.HardMathSupport.GuralnickMalle.FGeneral
public import CFSG.HardMathSupport.GuralnickMalle.EndFieldDescent.Basic
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX10SpArith
public import CFSG.LocalAnalysis.RankThreeUC.GN15FFOPSL.Top.Select.Best

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.PSL

open Module Representation
open CFSG.HardMathSupport.GuralnickMalle
open scoped MonoidAlgebra

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]

omit [Finite W] in
theorem card_fixSubGen_tautRep (G : Subgroup (W ≃ₗ[ZMod 2] W)) (A : Subgroup ↥G) :
    Nat.card (fixSubGen (tautRep G) A) =
      Nat.card {w : W // ∀ a ∈ A.map G.subtype, a w = w} := by
  have h : (fixSubGen (tautRep G) A : Set W) =
      {w : W | ∀ a ∈ A.map G.subtype, a w = w} := by
    ext w
    constructor
    · intro hw a ha
      obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
      exact hw a' ha'
    · intro hw a ha
      exact hw (a : W ≃ₗ[ZMod 2] W) (Subgroup.mem_map_of_mem G.subtype ha)
  change Nat.card {w : W // w ∈ (fixSubGen (tautRep G) A : Set W)} =
    Nat.card {w : W // ∀ a ∈ A.map G.subtype, a w = w}
  rw [h]
  rfl

omit [Finite W] in
theorem weight1Gen_tautRep (G : Subgroup (W ≃ₗ[ZMod 2] W)) (A : Subgroup ↥G) :
    weight1Gen (tautRep G) A =
      Nat.card (A.map G.subtype) *
        Nat.card {w : W // ∀ a ∈ A.map G.subtype, a w = w} := by
  rw [weight1Gen, card_fixSubGen_tautRep, Subgroup.card_subtype G A]


theorem card_le_card_of_best {G D : Subgroup (W ≃ₗ[ZMod 2] W)}
    (hirr : ∀ Z : Submodule (ZMod 2) W, (∀ g ∈ G, ∀ z ∈ Z, g z ∈ Z) → Z = ⊥ ∨ Z = ⊤)
    (hDG : D ≤ G) (hD1 : D ≠ ⊥)
    (hbest : ∀ B : Subgroup (W ≃ₗ[ZMod 2] W), B ≤ D →
      Nat.card B * Nat.card {w : W // ∀ b ∈ B, b w = w} ≤
        Nat.card D * Nat.card {w : W // ∀ d ∈ D, d w = w})
    (hoff : Nat.card W ≤ Nat.card D * Nat.card {w : W // ∀ d ∈ D, d w = w}) :
    Nat.card W ≤ Nat.card G := by
  classical
  have : Finite (W ≃ₗ[ZMod 2] W) :=
    Finite.of_injective (fun f : W ≃ₗ[ZMod 2] W => (f : W → W)) DFunLike.coe_injective
  have : Finite ↥G := Subtype.finite
  have hnt : Nontrivial W := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    have : Subsingleton W := h
    have : Subsingleton (W ≃ₗ[ZMod 2] W) :=
      ⟨fun f g => LinearEquiv.ext fun w => Subsingleton.elim _ _⟩
    exact hD1 ((Subgroup.eq_bot_iff_forall D).mpr fun d _ => Subsingleton.elim d 1)
  have : Nontrivial W := hnt
  have hirrρ : (tautRep G).IsIrreducible := by
    refine
      { exists_pair_ne := ?_
        eq_bot_or_eq_top := ?_ }
    · obtain ⟨v, hv⟩ := exists_ne (0 : W)
      refine ⟨⊥, ⊤, ?_⟩
      intro h'
      have h1 : v ∈ (⊤ : Subrepresentation (tautRep G)) := trivial
      rw [← h'] at h1
      exact hv ((Submodule.mem_bot (ZMod 2)).mp h1)
    · intro σ
      rcases hirr σ.toSubmodule (fun g hg z hz =>
        σ.apply_mem_toSubmodule ⟨g, hg⟩ hz) with h | h
      · exact Or.inl (Subrepresentation.ext h)
      · exact Or.inr (Subrepresentation.ext h)
  have : (tautRep G).IsIrreducible := hirrρ
  have hmapD : (D.subgroupOf G).map G.subtype = D := by
    ext d
    constructor
    · intro hd
      obtain ⟨d', hd', rfl⟩ := Subgroup.mem_map.mp hd
      exact hd'
    · intro hd
      refine Subgroup.mem_map.mpr ⟨⟨d, hDG hd⟩, ?_, rfl⟩
      rwa [Subgroup.mem_subgroupOf]
  have hbest' : IsBestFGen (tautRep G) (D.subgroupOf G) := by
    intro A hA
    have hmaple : A.map G.subtype ≤ D := by
      rintro b hb
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hb
      have hmem : (a : W ≃ₗ[ZMod 2] W) ∈ D := by
        have := hA ha
        rwa [Subgroup.mem_subgroupOf] at this
      exact hmem
    have h := hbest (A.map G.subtype) hmaple
    rw [weight1Gen_tautRep G A, weight1Gen_tautRep G (D.subgroupOf G), hmapD]
    exact h
  have hne : D.subgroupOf G ≠ ⊥ := by
    intro h
    apply hD1
    have h0 : D.subgroupOf G = (⊥ : Subgroup (W ≃ₗ[ZMod 2] W)).subgroupOf G := by
      simpa using h
    have h' : D ⊓ G = (⊥ : Subgroup (W ≃ₗ[ZMod 2] W)) ⊓ G :=
      (Subgroup.subgroupOf_inj).mp h0
    simpa [inf_eq_left.mpr hDG] using h'
  have hfaith : ∀ g : ↥G, (∀ v : W, tautRep G g v = v) → g = 1 := by
    intro g hg
    apply Subtype.ext
    apply LinearEquiv.ext
    intro w
    simpa using hg w
  have hle : weight1Gen (tautRep G) (D.subgroupOf G) ≤ Nat.card ↥G :=
    weight1Gen_le_card_of_irreducible_of_faithful hbest' hne hfaith
  calc Nat.card W
      ≤ Nat.card D * Nat.card {w : W // ∀ d ∈ D, d w = w} := hoff
    _ = weight1Gen (tautRep G) (D.subgroupOf G) := by
        rw [weight1Gen_tautRep G (D.subgroupOf G), hmapD]
    _ ≤ Nat.card ↥G := hle
    _ = Nat.card G := rfl

theorem card_range_sup_le {Γ : Type*} [Group Γ] [Finite Γ] (R D : Subgroup Γ)
    (hDN : D ≤ Subgroup.normalizer (R : Set Γ)) (h2 : Nat.card D ≤ 2 * Nat.card ↥(D ⊓ R)) :
    Nat.card ↥(R ⊔ D) ≤ 2 * Nat.card R := by
  let : (R.subgroupOf D).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hDN
  let : (R.subgroupOf (D ⊔ R)).Normal := Subgroup.normal_subgroupOf_sup_of_le_normalizer hDN
  have hcardRD : Nat.card ↥(R.subgroupOf D) = Nat.card ↥(D ⊓ R) := by
    rw [← Subgroup.inf_subgroupOf_right (H := R) (K := D), inf_comm D R]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  have h2' : Nat.card D ≤ 2 * Nat.card ↥(R.subgroupOf D) := by
    rwa [hcardRD]
  have hDcard : Nat.card D =
      Nat.card (↥D ⧸ R.subgroupOf D) * Nat.card ↥(R.subgroupOf D) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (R.subgroupOf D)
  have hqle : Nat.card (↥D ⧸ R.subgroupOf D) ≤ 2 := by
    apply Nat.le_of_mul_le_mul_right (c := Nat.card ↥(R.subgroupOf D)) _ Nat.card_pos
    rw [← hDcard]
    exact h2'
  have hq : Nat.card (↥D ⧸ R.subgroupOf D) =
      Nat.card (↥(D ⊔ R) ⧸ R.subgroupOf (D ⊔ R)) :=
    Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient D R hDN).toEquiv
  have hquot : Nat.card (↥(R ⊔ D) ⧸ R.subgroupOf (R ⊔ D)) =
      Nat.card (↥D ⧸ R.subgroupOf D) := by
    rw [sup_comm R D]
    exact hq.symm
  have hRcard : Nat.card ↥(R.subgroupOf (R ⊔ D)) = Nat.card R :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left : R ≤ R ⊔ D)).toEquiv
  have hRDcard : Nat.card ↥(R ⊔ D) =
      Nat.card (↥(R ⊔ D) ⧸ R.subgroupOf (R ⊔ D)) *
        Nat.card ↥(R.subgroupOf (R ⊔ D)) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (R.subgroupOf (R ⊔ D))
  calc Nat.card ↥(R ⊔ D)
      = Nat.card (↥(R ⊔ D) ⧸ R.subgroupOf (R ⊔ D)) *
          Nat.card ↥(R.subgroupOf (R ⊔ D)) := hRDcard
    _ = Nat.card (↥D ⧸ R.subgroupOf D) * Nat.card R := by rw [hquot, hRcard]
    _ ≤ 2 * Nat.card R := Nat.mul_le_mul_right _ hqle

theorem two_mul_card_specialLinearGroup_lt {K : Type} [Field K] [Fintype K] {n : ℕ}
    (hn : 2 ≤ n) :
    2 * Nat.card (Matrix.SpecialLinearGroup (Fin n) K) < Fintype.card K ^ (n ^ 2) := by
  classical
  let q := Nat.card K
  have hFq : Fintype.card K = q := Fintype.card_eq_nat_card
  have hq2 : 2 ≤ q := by
    have h := Finite.one_lt_card (α := K)
    omega
  have hSL := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq
    (K := K) (n := n) (by omega)
  have hP : ∏ j ∈ Finset.Icc 2 n, (q ^ j - 1) < q ^ (∑ j ∈ Finset.Icc 2 n, j) := by
    rw [← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_lt_prod₀ ?_ ?_ ?_
    · intro j hj
      have hj2 : 2 ≤ j := (Finset.mem_Icc.mp hj).1
      have h1 : 1 < q ^ j := one_lt_pow₀ (by omega : 1 < q) (by omega : j ≠ 0)
      omega
    · intro j _
      exact Nat.sub_le _ _
    · refine ⟨2, Finset.mem_Icc.mpr ⟨le_rfl, hn⟩, ?_⟩
      have h1 : 0 < q ^ 2 := pow_pos (by omega : 0 < q) 2
      omega
  have h2S : 2 * (∑ j ∈ Finset.Icc 2 n, j) + 2 = n * (n + 1) :=
    CFSG.ComponentClassification.CatLeafProof.X10Sp.two_mul_sum_Icc_two (by omega)
  have h2e : 2 * (n * (n - 1) / 2) = n * (n - 1) :=
    Nat.mul_div_cancel' (Nat.two_dvd_mul_sub_one n)
  have hexp : n * (n - 1) / 2 + (∑ j ∈ Finset.Icc 2 n, j) = n ^ 2 - 1 := by
    have hmain : 2 * (n * (n - 1) / 2) +
        (2 * (∑ j ∈ Finset.Icc 2 n, j) + 2) = 2 * n ^ 2 := by
      rw [h2e, h2S]
      nlinarith [Nat.sub_add_cancel (by omega : 1 ≤ n)]
    omega
  have hqpow : q ^ (n * (n - 1) / 2) * (∏ j ∈ Finset.Icc 2 n, (q ^ j - 1)) <
      q ^ (n ^ 2 - 1) := by
    calc q ^ (n * (n - 1) / 2) * (∏ j ∈ Finset.Icc 2 n, (q ^ j - 1))
        < q ^ (n * (n - 1) / 2) * q ^ (∑ j ∈ Finset.Icc 2 n, j) :=
          Nat.mul_lt_mul_of_pos_left hP (pow_pos (by omega : 0 < q) _)
      _ = q ^ (n * (n - 1) / 2 + (∑ j ∈ Finset.Icc 2 n, j)) := by
          rw [← pow_add]
      _ = q ^ (n ^ 2 - 1) := by rw [hexp]
  have hSLlt : Nat.card (Matrix.SpecialLinearGroup (Fin n) K) < q ^ (n ^ 2 - 1) := by
    rw [hSL]
    exact hqpow
  calc 2 * Nat.card (Matrix.SpecialLinearGroup (Fin n) K)
      < 2 * q ^ (n ^ 2 - 1) := Nat.mul_lt_mul_of_pos_left hSLlt (by norm_num)
    _ ≤ q * q ^ (n ^ 2 - 1) := Nat.mul_le_mul_right _ hq2
    _ = q ^ (n ^ 2) := by
        rw [mul_comm, ← pow_succ, Nat.sub_add_cancel (by nlinarith : 1 ≤ n ^ 2)]
    _ = Fintype.card K ^ (n ^ 2) := by rw [hFq]

theorem mul_finrank_lt_of_best {m : ℕ} (hm : 2 ≤ m) {K : Type} [Field K] [Fintype K] [CharP K 2]
    {f : ℕ} (hK : Fintype.card K = 2 ^ f)
    (ρ : Representation (ZMod 2) (Matrix.SpecialLinearGroup (Fin m) K) W)
    (hirr : ρ.IsIrreducible)
    (R : Subgroup (W ≃ₗ[ZMod 2] W)) (hR : ∀ g, ∃ r ∈ R, ∀ w, r w = ρ g w)
    (hR' : ∀ r ∈ R, ∃ g, ∀ w, r w = ρ g w)
    (D : Subgroup (W ≃ₗ[ZMod 2] W))
    (hDN : D ≤ Subgroup.normalizer (R : Set (W ≃ₗ[ZMod 2] W)))
    (h2 : Nat.card D ≤ 2 * Nat.card ↥(D ⊓ R)) (hD1 : D ≠ ⊥)
    (hbest : ∀ B : Subgroup (W ≃ₗ[ZMod 2] W), B ≤ D →
      Nat.card B * Nat.card {w : W // ∀ b ∈ B, b w = w} ≤
        Nat.card D * Nat.card {w : W // ∀ d ∈ D, d w = w})
    (hoff : Nat.card W ≤ Nat.card D * Nat.card {w : W // ∀ d ∈ D, d w = w})
    {s : ℕ} (hE : Nat.card (Module.End
      (MonoidAlgebra (ZMod 2) (Matrix.SpecialLinearGroup (Fin m) K)) ρ.asModule) = 2 ^ s) :
    s * Module.finrank (Module.End
      (MonoidAlgebra (ZMod 2) (Matrix.SpecialLinearGroup (Fin m) K)) ρ.asModule) ρ.asModule <
      f * m ^ 2 := by
  classical
  have : Finite (W ≃ₗ[ZMod 2] W) :=
    Finite.of_injective (fun f : W ≃ₗ[ZMod 2] W => (f : W → W)) DFunLike.coe_injective
  have : FiniteDimensional (ZMod 2) W := Module.finite_iff_finite.mpr inferInstance
  have : ρ.IsIrreducible := hirr
  let d := Module.finrank (Module.End
    (MonoidAlgebra (ZMod 2) (Matrix.SpecialLinearGroup (Fin m) K)) ρ.asModule) ρ.asModule
  have hW : Nat.card W = 2 ^ (s * d) := by
    have h := card_eq_pow_finrank_endField ρ
    rw [hE] at h
    rw [h, ← pow_mul]
  have hcard : Nat.card W ≤ 2 * Nat.card (Matrix.SpecialLinearGroup (Fin m) K) := by
    have hGirr : ∀ Z : Submodule (ZMod 2) W,
        (∀ g ∈ R ⊔ D, ∀ z ∈ Z, g z ∈ Z) → Z = ⊥ ∨ Z = ⊤ := by
      intro Z hZ
      have hZρ : ∀ g : Matrix.SpecialLinearGroup (Fin m) K, ∀ z ∈ Z, ρ g z ∈ Z := by
        intro g z hz
        obtain ⟨r, hrR, hr⟩ := hR g
        rw [← hr z]
        exact hZ r (Subgroup.mem_sup_left hrR) z hz
      rcases hirr.eq_bot_or_eq_top ⟨Z, hZρ⟩ with h | h
      · exact Or.inl (congrArg Subrepresentation.toSubmodule h)
      · exact Or.inr (congrArg Subrepresentation.toSubmodule h)
    have h1 := card_le_card_of_best (G := R ⊔ D) (D := D) hGirr le_sup_right hD1 hbest hoff
    have h3 := card_range_sup_le R D hDN h2
    have hRcard : Nat.card R ≤ Nat.card (Matrix.SpecialLinearGroup (Fin m) K) := by
      let φ : Matrix.SpecialLinearGroup (Fin m) K → R := fun g =>
        ⟨Classical.choose (hR g), (Classical.choose_spec (hR g)).1⟩
      have hφ : Function.Surjective φ := by
        intro r
        obtain ⟨g, hg⟩ := hR' r r.2
        refine ⟨g, ?_⟩
        apply Subtype.ext
        apply LinearEquiv.ext
        intro w
        exact ((Classical.choose_spec (hR g)).2 w).trans (hg w).symm
      exact Nat.card_le_card_of_surjective φ hφ
    exact h1.trans (h3.trans (Nat.mul_le_mul_left 2 hRcard))
  have hlt : Nat.card W < 2 ^ (f * m ^ 2) := by
    have hSL := two_mul_card_specialLinearGroup_lt (K := K) hm
    rw [hK, ← pow_mul] at hSL
    exact lt_of_le_of_lt hcard hSL
  have hpow : 2 ^ (s * d) < 2 ^ (f * m ^ 2) := by
    simpa [hW] using hlt
  change s * d < f * m ^ 2
  exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp hpow

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.PSL
