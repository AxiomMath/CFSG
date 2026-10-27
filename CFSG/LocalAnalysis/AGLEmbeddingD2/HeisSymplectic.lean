module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.HeisSymplecticReal
public import CFSG.LocalAnalysis.AGLEmbeddingD2.HeisSymplecticPart

public section

namespace CFSG.AGLEmbeddingD2.HeisSymplectic

open Matrix CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.Universal.Symplectic
  CFSG.AGLEmbeddingD2.SquareSymplectic CFSG.AGLEmbeddingD2.PartStab CFSG.AGLEmbeddingD2.ParabLevi

section Arith

variable {n : ℕ} {F : Type} [Field F] [Finite F]

theorem isMulCommutative_of_isPGroup_five_statedSp {f : ℕ} (hF : Nat.card F = 2 ^ f)
    (hfm : (Odd f ∧ n + n < 20) ∨ (f % 4 = 2 ∧ n + n < 10) ∨ (4 ∣ f ∧ n + n < 5))
    {Q : Subgroup (StatedSp n F)} (hQ : IsPGroup 5 Q) : IsMulCommutative Q :=
  AbelianSylowGL.isMulCommutative_of_isPGroup_of_injective (StatedSp n F).subtype
    (Subgroup.subtype_injective _) (fun Q' hQ' =>
      isMulCommutative_of_isPGroup_five_GL_fintype (σ := Fin n ⊕ Fin n) hF
        (by simpa [Fintype.card_sum] using hfm) Q' hQ') hQ

theorem exists_omega [CharP F 2] {f : ℕ} (hF : Nat.card F = 2 ^ f) (hf : Even f) :
    ∃ ω : F, ω ^ 2 + ω + 1 = 0 := by
  obtain ⟨k, hk⟩ := hf
  have h3 : 3 ∣ Nat.card F - 1 := by
    rw [hF, hk, ← two_mul, pow_mul]
    simpa using Nat.sub_dvd_pow_sub_pow 4 1 k
  obtain ⟨ω, hω⟩ := SquareLinear.exists_orderOf_eq_three h3
  have hω3 : (ω : F) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← hω, pow_orderOf_eq_one, Units.val_one]
  have hω1 : (ω : F) ≠ 1 := by
    intro h
    have : ω = 1 := Units.ext h
    rw [this, orderOf_one] at hω
    omega
  refine ⟨ω, ?_⟩
  have : ((ω : F) - 1) * ((ω : F) ^ 2 + ω + 1) = 0 := by linear_combination hω3
  exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hω1)

theorem exists_orderOf_eq_five {f : ℕ} (hF : Nat.card F = 2 ^ f) (hf : 4 ∣ f) :
    ∃ t : Fˣ, orderOf t = 5 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have h5 : 5 ∣ Nat.card Fˣ := by
    rw [Nat.card_units, hF]
    exact (CyclicSylowGL.five_dvd_two_pow_sub_one_iff f).2 hf
  exact exists_prime_orderOf_dvd_card' 5 h5

omit [Finite F] in
theorem torus_elt_pow (k : Fin n) {ω : Fˣ} {m : ℕ} (hω : ω ^ m = 1) :
    (equivStatedSp n F (TauCeti.GLSymplecticFin.diagonal (corootVec n F k ω))) ^ m = 1 := by
  rw [← map_pow, ← map_pow, CFSG.AGLEmbedding.ParabHub.corootVec_pow_eq_one k hω, map_one,
    map_one]

end Arith

section Main

open CFSG.AGLEmbedding CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime
  CFSG.AGLEmbeddingD2.HeisEngine

variable {n : ℕ} {F : Type} [Field F]

theorem not_run_of_no_orth {I : Set (Fin n)}
    (hno : ¬ ∃ a ∈ I, ∃ b ∈ I, ∃ c ∈ I, a.val + 2 ≤ b.val ∧ b.val + 2 ≤ c.val) {c : ℕ} :
    ¬ ∀ i, c ≤ i → i < c + 5 → NodeIn I i := by
  intro h
  obtain ⟨h0, h0'⟩ := h c le_rfl (by omega)
  obtain ⟨h2, h2'⟩ := h (c + 2) (by omega) (by omega)
  obtain ⟨h4, h4'⟩ := h (c + 4) (by omega) (by omega)
  exact hno ⟨_, h0', _, h2', _, h4', by simp, by simp⟩

theorem three_le_pRank_five_sp [Finite F] [CharP F 2] {Y : Type} [Group Y] [Finite Y]
    (e : Y ≃* StatedProj (StatedSp n F)) {X : Type} [Group X] [Finite X]
    (ρ : X →* Y) (hρ : Function.Surjective ρ) (hρker : ρ.ker ≤ Subgroup.center X)
    (hρ5 : Nat.Coprime 5 (Nat.card ρ.ker)) (T : Sylow 2 Y) (J : Subgroup Y)
    (hNJ : Subgroup.normalizer ((T : Subgroup Y) : Set Y) ≤ J) (hJ : J ≠ ⊤)
    (P : Subgroup Y) (hPJ : P ≤ J) (hP : IsPGroup 5 P) (hPc : ¬ IsMulCommutative P) :
    3 ≤ CFSG.Open.pRank 5 (J.comap ρ) := by
  classical
  have _ := hJ
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have := Fintype.ofFinite F
  obtain ⟨f, -, hf⟩ := FiniteField.card F 2
  have hfc : Nat.card F = 2 ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card, hf]
  have hb := borelQuotient_sp e
  obtain ⟨π', hb', hker', hBJ⟩ := SquareGeneric.BorelQuotient.exists_conj_parab hb T hNJ
  obtain ⟨Q, hQle, hQ5, hQnc⟩ := exists_nonabelian_le_torus_sup_leviM hb' hBJ (by norm_num) hPJ hP
    hPc
  have hmod : (f : ℕ) % 4 = 0 ∨ (f : ℕ) % 4 = 2 ∨ Odd (f : ℕ) := by
    rcases Nat.even_or_odd (f : ℕ) with ⟨k, hk⟩ | ho
    · omega
    · exact Or.inr (Or.inr ho)
  rcases hmod with h0 | h2 | hodd
  ·
    have h4 : 4 ∣ (f : ℕ) := by omega
    by_cases hn : n ≤ 2
    · exact absurd (isMulCommutative_of_isPGroup_five_statedSp hfc
        (Or.inr (Or.inr ⟨h4, by omega⟩)) hQ5) hQnc
    · obtain ⟨t, ht⟩ := exists_orderOf_eq_five hfc h4
      have ht5 : t ^ 5 = 1 := by rw [← ht, pow_orderOf_eq_one]
      have ht1 : t ≠ 1 := by
        intro h
        rw [h, orderOf_one] at ht
        omega
      have hπ5 : Nat.Coprime 5 (Nat.card π'.ker) := by
        rw [hker', ker_comp_mk'_eq_bot (by omega) e, Subgroup.card_bot]
        exact Nat.coprime_one_right 5
      let a : Fin n := ⟨0, by omega⟩
      let b : Fin n := ⟨1, by omega⟩
      let c : Fin n := ⟨2, by omega⟩
      exact (three_le_pRank_of_torus hb'.extras hπ5 hBJ (a := a) (b := b) (c := c)
        (fun h => absurd (congrArg Fin.val h) (by simp [a, b]))
        (fun h => absurd (congrArg Fin.val h) (by simp [a, c]))
        (fun h => absurd (congrArg Fin.val h) (by simp [b, c])) (torus_elt_mem a t)
        (torus_elt_mem b t) (torus_elt_mem c t) (torus_elt_pow a ht5) (torus_elt_pow b ht5)
        (torus_elt_pow c ht5) (torus_elt_ne_one a ht1) (torus_elt_ne_one b ht1)
        (torus_elt_ne_one c ht1)).trans (pRank_le_pRank_comap_of_coprime hρ hρ5 J)
  ·
    by_cases hn : n ≤ 4
    · exact absurd (isMulCommutative_of_isPGroup_five_statedSp hfc
        (Or.inr (Or.inl ⟨h2, by omega⟩)) hQ5) hQnc
    · obtain ⟨ω, hω⟩ := exists_omega hfc (Nat.even_iff.2 (by omega))
      by_cases ho : ∃ a ∈ negIndices (rootDatum n F) (J.comap π'),
          ∃ b ∈ negIndices (rootDatum n F) (J.comap π'),
          ∃ c ∈ negIndices (rootDatum n F) (J.comap π'), a.val + 2 ≤ b.val ∧ b.val + 2 ≤ c.val
      · obtain ⟨a, ha, b, hb2, c, hc, hab, hbc⟩ := ho
        exact three_le_pRank_of_triple (by decide) hb'.ker_central ρ hρ hρker
          (commutes_rankOne_of_cartan_eq_zero hb'.extras (fun h => by rw [h] at hab; omega)
            (cartan_eq_zero_of_far (Or.inl hab)))
          (commutes_rankOne_of_cartan_eq_zero hb'.extras (fun h => by rw [h] at hab; omega)
            (cartan_eq_zero_of_far (Or.inl (by omega))))
          (commutes_rankOne_of_cartan_eq_zero hb'.extras (fun h => by rw [h] at hbc; omega)
            (cartan_eq_zero_of_far (Or.inl hbc)))
          (realOver_rankOne hω (rankOne_le_of_mem_negIndices hBJ ha))
          (realOver_rankOne hω (rankOne_le_of_mem_negIndices hBJ hb2))
          (realOver_rankOne hω (rankOne_le_of_mem_negIndices hBJ hc))
      · exact absurd (isMulCommutative_of_le_torus_sup_leviM (n := n) (M := 8) (R := 5) (T := 5)
          (fun σ _ _ hσ P hP => isMulCommutative_of_isPGroup_five_GL_fintype hfc
            (Or.inr (Or.inl ⟨h2, by omega⟩)) P hP) (by norm_num) (by norm_num)
          (fun c _ => not_run_of_no_orth ho) (fun c _ => not_run_of_no_orth ho) hQle hQ5) hQnc
  ·
    by_cases hn : n ≤ 9
    · exact absurd (isMulCommutative_of_isPGroup_five_statedSp hfc
        (Or.inl ⟨hodd, by omega⟩) hQ5) hQnc
    · have hLJ : ∀ S : Set (Fin n), S ⊆ negIndices (rootDatum n F) (J.comap π') →
          leviM (rootDatum n F) S ≤ J.comap π' := fun S hS =>
        iSup₂_le fun i hi => rankOne_le_of_mem_negIndices hBJ (hS hi)
      by_cases ha1 : ∃ c, c + 12 ≤ n ∧ ∀ i, c ≤ i → i < c + 11 →
          NodeIn (negIndices (rootDatum n F) (J.comap π')) i
      ·
        obtain ⟨c, hc, hrun⟩ := ha1
        have hpiece : ∀ c', c ≤ c' → c' + 3 ≤ c + 11 →
            piece n c' 3 ⊆ negIndices (rootDatum n F) (J.comap π') := fun c' h1 h2 i hi =>
          (hrun i.val (by have := hi.1; omega) (by have := hi.2; omega)).2
        exact three_le_pRank_of_triple (by decide) hb'.ker_central ρ hρ hρker
          (commutes_leviM fun i hi j hj => by have := hi.2; have := hj.1; omega)
          (commutes_leviM fun i hi j hj => by have := hi.2; have := hj.1; omega)
          (commutes_leviM fun i hi j hj => by have := hi.2; have := hj.1; omega)
          (realOver_A3 c (by omega) (hLJ _ (hpiece c le_rfl (by omega))))
          (realOver_A3 (c + 4) (by omega) (hLJ _ (hpiece (c + 4) (by omega) (by omega))))
          (realOver_A3 (c + 8) (by omega) (hLJ _ (hpiece (c + 8) (by omega) (by omega))))
      · by_cases ha2 : ∀ i, n - 10 ≤ i → i < n - 10 + 10 →
            NodeIn (negIndices (rootDatum n F) (J.comap π')) i
        ·
          have hpiece : ∀ c', n - 10 ≤ c' → c' + 3 ≤ n →
              piece n c' 3 ⊆ negIndices (rootDatum n F) (J.comap π') := fun c' h1 h2 i hi =>
            (ha2 i.val (by have := hi.1; omega) (by have := hi.2; omega)).2
          let a : Fin n := ⟨n - 2, by omega⟩
          let b : Fin n := ⟨n - 1, by omega⟩
          have hCI : ({a, b} : Set (Fin n)) ⊆ negIndices (rootDatum n F) (J.comap π') := by
            rintro i (rfl | rfl)
            · exact (ha2 (n - 2) (by omega) (by omega)).2
            · exact (ha2 (n - 1) (by omega) (by omega)).2
          exact three_le_pRank_of_triple (by decide) hb'.ker_central ρ hρ hρker
            (commutes_leviM fun i hi j hj => by have := hi.2; have := hj.1; omega)
            (commutes_leviM fun i hi j hj => by
              have := hi.2
              rcases hj with rfl | rfl <;> simp only [a, b] <;> omega)
            (commutes_leviM fun i hi j hj => by
              have := hi.2
              rcases hj with rfl | rfl <;> simp only [a, b] <;> omega)
            (realOver_A3 (n - 10) (by omega) (hLJ _ (hpiece (n - 10) le_rfl (by omega))))
            (realOver_A3 (n - 6) (by omega) (hLJ _ (hpiece (n - 6) (by omega) (by omega))))
            (realOver_C2 (a := a) (b := b) (by simp only [a, b]; omega) (by simp only [b]; omega)
              (hLJ _ hCI))
        · exact absurd (isMulCommutative_of_le_torus_sup_leviM (n := n) (M := 18) (R := 11)
            (T := 10) (fun σ _ _ hσ P hP => isMulCommutative_of_isPGroup_five_GL_fintype hfc
              (Or.inl ⟨hodd, by omega⟩) P hP) (by norm_num) (by norm_num)
            (fun c hc h => ha1 ⟨c, by omega, h⟩)
            (fun c hc h => ha2 fun i hi1 hi2 => h i (by omega) (by omega)) hQle hQ5) hQnc

end Main

end CFSG.AGLEmbeddingD2.HeisSymplectic
