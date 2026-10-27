module

public import CFSG.HardMathSupport.GuralnickMalle.SL6Exterior3F
public import CFSG.HardMathSupport.GuralnickMalle.SL6Exterior3F.Transvection
public import CFSG.HardMathSupport.GuralnickMalle.SL6Exterior3F.Quotient
public import CFSG.HardMathSupport.GuralnickMalle.SL6Exterior3F.EndNode
public import CFSG.HardMathSupport.GuralnickMalle.SL6Exterior3F.Singular

public section

namespace CFSG.HardMathSupport.GuralnickMalle

open Module
open CFSG.Open

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] [CharP K 2] in
theorem finrank_range_toMatrix'_lt_three_iff
    (f : (Fin 3 → K) →ₗ[K] (Fin 3 → K)) :
    Module.finrank K (LinearMap.range f) < 3 ↔
      ¬ IsUnit (LinearMap.toMatrix' f).det := by
  have hle : Module.finrank K (LinearMap.range f) ≤ 3 := by
    calc Module.finrank K (LinearMap.range f)
        ≤ Module.finrank K (⊤ : Submodule K (Fin 3 → K)) := Submodule.finrank_mono le_top
      _ = 3 := by rw [finrank_top, Module.finrank_fin_fun]
  have htop : Module.finrank K (LinearMap.range f) = 3 ↔ IsUnit f := by
    rw [LinearMap.isUnit_iff_range_eq_top]
    constructor
    · intro h
      exact Submodule.eq_top_of_finrank_eq (by rw [h, Module.finrank_fin_fun])
    · intro h
      rw [h, finrank_top, Module.finrank_fin_fun]
  calc Module.finrank K (LinearMap.range f) < 3
      ↔ Module.finrank K (LinearMap.range f) ≠ 3 := by omega
    _ ↔ ¬ IsUnit f := not_congr htop
    _ ↔ ¬ IsUnit (LinearMap.toMatrix' f) :=
        (not_congr (LinearMap.isUnit_toMatrix'_iff (f := f))).symm
    _ ↔ ¬ IsUnit (LinearMap.toMatrix' f).det :=
        not_congr (Matrix.isUnit_iff_isUnit_det (LinearMap.toMatrix' f))

omit [CharP K 2] in
theorem card_rank_lt_three_le_card_singular :
    Nat.card {f : (Fin 3 → K) →ₗ[K] (Fin 3 → K) //
        Module.finrank K (LinearMap.range f) < 3} ≤
      Nat.card {M : Matrix (Fin 3) (Fin 3) K // ¬ IsUnit M.det} := by
  refine Nat.card_le_card_of_injective
    (fun f => ⟨LinearMap.toMatrix' f.1,
      (finrank_range_toMatrix'_lt_three_iff f.1).mp f.2⟩) ?_
  intro x y hxy
  exact Subtype.ext (LinearMap.toMatrix'.injective (congr_arg Subtype.val hxy))

theorem glExterior3_weight1Gen_le_of_inv
    (hinv : ∀ a : GL (Fin 6) K, a * a = 1 → a ≠ 1 →
      Module.finrank K (fixSubGen (glExterior3Rep K) (Subgroup.closure {a})) +
        2 * natRank a ≤ 16)
    (A : Subgroup (GL (Fin 6) K)) (hA : A ≠ ⊥) (hAel : CFSG.Open.IsElemAbelian 2 A) :
    weight1Gen (glExterior3Rep K) A ≤ Nat.card K ^ 19 := by
  classical
  let c : ℕ := Module.finrank K (fixSubGen (glExterior3Rep K) A)
  have hfixcard : Nat.card (fixSubGen (glExterior3Rep K) A) = Nat.card K ^ c :=
    card_fixSubGen_glExterior3 A
  have hsq : ∀ a ∈ A, a * a = 1 := by
    intro a ha
    simpa [pow_two] using hAel.2 a ha
  have hc_le_closure : ∀ a ∈ A, c ≤
      Module.finrank K (fixSubGen (glExterior3Rep K) (Subgroup.closure {a})) := by
    intro a ha
    refine Submodule.finrank_mono (fixSubGen_antitone ?_)
    rw [Subgroup.closure_le]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rwa [hx]
  obtain ⟨a₀, ha₀ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA
  have ha₀ : (a₀ : GL (Fin 6) K) ∈ A := a₀.2
  have ha₀1 : (a₀ : GL (Fin 6) K) ≠ 1 := by
    intro h
    exact ha₀ne (Subtype.ext h)
  by_contra hle
  have hw_gt : Nat.card K ^ 19 < weight1Gen (glExterior3Rep K) A := not_le.mp hle
  have hw_gt' : Nat.card K ^ 19 <
      Nat.card A * Nat.card (fixSubGen (glExterior3Rep K) A) := hw_gt
  have hweight_le_of : ∀ r : ℕ, r ≤ 19 → Nat.card A ≤ Nat.card K ^ r → c ≤ 19 - r →
      weight1Gen (glExterior3Rep K) A ≤ Nat.card K ^ 19 := by
    intro r _ hcard hc
    show Nat.card A * Nat.card (fixSubGen (glExterior3Rep K) A) ≤ Nat.card K ^ 19
    rw [hfixcard]
    calc Nat.card A * Nat.card K ^ c
        ≤ Nat.card K ^ r * Nat.card K ^ (19 - r) :=
          Nat.mul_le_mul hcard (Nat.pow_le_pow_right (Nat.card_pos) hc)
      _ = Nat.card K ^ 19 := by
          rw [← pow_add]
          congr 1
          omega
  by_cases h3 : ∃ a ∈ A, a ≠ 1 ∧ natRank a = 3
  ·
    obtain ⟨a, haA, hane, hrank3⟩ := h3
    have hc10 : c ≤ 10 := by
      have h := hinv a (hsq a haA) hane
      have hcl := hc_le_closure a haA
      rw [hrank3] at h
      omega
    have hcard9 := card_le_pow_nine A hAel
    have hle19 := hweight_le_of 9 (by norm_num) hcard9 (by omega)
    exact (not_lt.mpr hle19) hw_gt
  · push Not at h3
    by_cases hall1 : ∀ a ∈ A, a ≠ 1 → natRank a = 1
    ·
      have hrank1 : ∀ a ∈ A, a ≠ 1 → Module.finrank K (LinearMap.range
          (Matrix.toLin' ((a : Matrix (Fin 6) (Fin 6) K)) - 1)) = 1 := by
        intro a ha hane
        rw [← natRank_eq_finrank_range_sub_one]
        exact hall1 a ha hane
      have hcard5 := card_le_pow_five_of_forall_rank_one K A hAel hA hrank1
      have hc14 : c ≤ 14 := by
        have h := hinv (a₀ : GL (Fin 6) K) (hsq _ ha₀) ha₀1
        have h1 := hall1 (a₀ : GL (Fin 6) K) ha₀ ha₀1
        have hcl := hc_le_closure (a₀ : GL (Fin 6) K) ha₀
        rw [h1] at h
        omega
      have hle19 := hweight_le_of 5 (by norm_num) hcard5 (by omega)
      exact (not_lt.mpr hle19) hw_gt
    ·
      push Not at hall1
      obtain ⟨a₂, ha₂A, ha₂ne, ha₂rank⟩ := hall1
      have hrank2 : natRank a₂ = 2 := by
        have hpos := one_le_natRank ha₂ne
        have hle3 := natRank_le_three a₂ (hsq a₂ ha₂A)
        have hne3 := h3 a₂ ha₂A ha₂ne
        omega
      have hc12 : c ≤ 12 := by
        have h := hinv a₂ (hsq a₂ ha₂A) ha₂ne
        have hcl := hc_le_closure a₂ ha₂A
        rw [hrank2] at h
        omega
      have h2 : ∀ a ∈ A, a ≠ 1 → natRank a ≤ 2 := by
        intro a ha hane
        have hle3 := natRank_le_three a (hsq a ha)
        have hne3 := h3 a ha hane
        omega
      have hfix_le12 : Nat.card (fixSubGen (glExterior3Rep K) A) ≤ Nat.card K ^ 12 := by
        rw [hfixcard]
        exact Nat.pow_le_pow_right (Nat.card_pos) hc12
      have hgt7 : Nat.card K ^ 7 < Nat.card A := by
        have hlt : Nat.card K ^ 7 * Nat.card K ^ 12 <
            Nat.card A * Nat.card K ^ 12 := by
          calc Nat.card K ^ 7 * Nat.card K ^ 12 = Nat.card K ^ 19 := by
                rw [← pow_add]
            _ < Nat.card A * Nat.card K ^ 12 :=
                lt_of_lt_of_le hw_gt' (Nat.mul_le_mul_left _ hfix_le12)
        exact Nat.lt_of_mul_lt_mul_right hlt
      obtain ⟨e, he, hfixe⟩ := exists_fixed_vector_natural A hA hAel
      obtain ⟨φ, ψ, a, b, haA, hbA, hφe, hψe, hind, ha_mat, hb_mat⟩ :=
        exists_independent_transvections K A hAel he hfixe hgt7
      have hc11 : c ≤ 11 := by
        have hcl : Subgroup.closure ({a, b} : Set (GL (Fin 6) K)) ≤ A := by
          rw [Subgroup.closure_le]
          intro x hx
          rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
          rcases hx with rfl | rfl
          · exact haA
          · exact hbA
        have hmono : Module.finrank K (fixSubGen (glExterior3Rep K) A) ≤
            Module.finrank K (fixSubGen (glExterior3Rep K)
              (Subgroup.closure {a, b})) :=
          Submodule.finrank_mono (fixSubGen_antitone hcl)
        have h11 := finrank_fix_le_eleven_of_independent_transvections e he hφe hψe
          hind a b ha_mat hb_mat
        omega
      have hfix_le11 : Nat.card (fixSubGen (glExterior3Rep K) A) ≤ Nat.card K ^ 11 := by
        rw [hfixcard]
        exact Nat.pow_le_pow_right (Nat.card_pos) hc11
      have hgt8 : Nat.card K ^ 8 < Nat.card A := by
        have hlt : Nat.card K ^ 8 * Nat.card K ^ 11 <
            Nat.card A * Nat.card K ^ 11 := by
          calc Nat.card K ^ 8 * Nat.card K ^ 11 = Nat.card K ^ 19 := by
                rw [← pow_add]
            _ < Nat.card A * Nat.card K ^ 11 :=
                lt_of_lt_of_le hw_gt' (Nat.mul_le_mul_left _ hfix_le11)
        exact Nat.lt_of_mul_lt_mul_right hlt
      have h9 := nine_le_finrank_nilpSpan A hAel hgt8
      have hcard_rank := card_le_card_rank_lt_three A hAel h9 h2
      have hcard_sing : Nat.card A ≤
          Nat.card {M : Matrix (Fin 3) (Fin 3) K // ¬ IsUnit M.det} :=
        hcard_rank.trans card_rank_lt_three_le_card_singular
      have hq2 : 2 ≤ Nat.card K := by
        have h : 1 < Nat.card K := Finite.one_lt_card
        omega
      have hA_lt : Nat.card A < 2 * Nat.card K ^ 8 :=
        lt_of_le_of_lt hcard_sing (card_singular_matrices_lt K hq2)
      obtain ⟨f, hf⟩ := exists_natCard_eq_two_pow (K := K)
      obtain ⟨r, hr⟩ := exists_natCard_eq_two_pow_of_isPGroup (G := A) hAel.isPGroup
      have hq8 : Nat.card K ^ 8 = 2 ^ (8 * f) := by
        rw [hf, ← pow_mul]
        congr 1
        omega
      have hgt_pow : 2 ^ (8 * f) < 2 ^ r := by
        rw [← hq8, ← hr]
        exact hgt8
      have h2pow : 2 * 2 ^ (8 * f) ≤ 2 ^ r := two_mul_pow_le_of_lt hgt_pow
      have hlt_pow : 2 ^ r < 2 * 2 ^ (8 * f) := by
        rw [← hr, ← hq8]
        exact hA_lt
      exact (not_lt_of_ge h2pow) hlt_pow

theorem sl6Exterior3_weight1Gen_le_of_inv
    (hinv : ∀ a : GL (Fin 6) K, a * a = 1 → a ≠ 1 →
      Module.finrank K (fixSubGen (glExterior3Rep K) (Subgroup.closure {a})) +
        2 * natRank a ≤ 16)
    (A : Subgroup ↥(StatedSL 6 K)) (hA : A ≠ ⊥) (hAel : IsElementaryAbelian 2 ↥A) :
    weight1Gen (sl6Exterior3Rep K) A ≤ Nat.card K ^ 19 := by
  have hbase : CFSG.Open.IsElemAbelian 2 A :=
    (CFSG.Open.isElemAbelian_iff_isElementaryAbelian (p := 2) (E := A)).mpr hAel
  have hmapel : CFSG.Open.IsElemAbelian 2 (A.map (StatedSL 6 K).subtype) :=
    hbase.map (StatedSL 6 K).subtype
  have hmapne : A.map (StatedSL 6 K).subtype ≠ ⊥ := fun hbot =>
    hA ((Subgroup.map_eq_bot_iff_of_injective A
      (StatedSL 6 K).subtype_injective).mp hbot)
  have hgl := glExterior3_weight1Gen_le_of_inv hinv (A.map (StatedSL 6 K).subtype)
    hmapne hmapel
  rwa [weight1Gen_sl6Exterior3Rep_eq_map]

theorem sl6Exterior3_mul_weight1Gen_lt_of_inv
    (hinv : ∀ a : GL (Fin 6) K, a * a = 1 → a ≠ 1 →
      Module.finrank K (fixSubGen (glExterior3Rep K) (Subgroup.closure {a})) +
        2 * natRank a ≤ 16)
    {m : ℕ} (hm : m < Nat.card K)
    (A : Subgroup ↥(StatedSL 6 K)) (hA : A ≠ ⊥) (hAel : IsElementaryAbelian 2 ↥A) :
    m * weight1Gen (sl6Exterior3Rep K) A < Nat.card (⋀[K]^3 (Fin 6 → K)) := by
  have hle := sl6Exterior3_weight1Gen_le_of_inv hinv A hA hAel
  have hqpos : 0 < Nat.card K := Nat.card_pos
  have hV : Nat.card (⋀[K]^3 (Fin 6 → K)) = Nat.card K ^ 20 := card_sl6Exterior3
  rw [hV]
  calc m * weight1Gen (sl6Exterior3Rep K) A
      ≤ m * Nat.card K ^ 19 := Nat.mul_le_mul_left m hle
    _ < Nat.card K * Nat.card K ^ 19 :=
        Nat.mul_lt_mul_of_pos_right hm (pow_pos hqpos 19)
    _ = Nat.card K ^ 20 := by
        rw [mul_comm, ← pow_succ]

end CFSG.HardMathSupport.GuralnickMalle
