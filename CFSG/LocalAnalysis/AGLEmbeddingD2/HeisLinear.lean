module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.HeisLinearElems
public import CFSG.LocalAnalysis.AGLEmbeddingD2.HeisLinearResidual

public section

namespace CFSG.AGLEmbeddingD2.HeisLinear

open CFSG.Open CFSG.LieType.Universal CFSG.LieType.Universal.SpecialLinear
  CFSG.LieType.CurtisTits CFSG.LieType.RootSystem CFSG.LieType.Steinberg CFSG.AGLEmbedding
  CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime CFSG.AGLEmbeddingD2.ParabLevi
  CFSG.AGLEmbeddingD2.SquareGeneric CFSG.AGLEmbeddingD2.SquareLinear
  CFSG.AGLEmbeddingD2.CyclicSylowGL CFSG.AGLEmbeddingD2.HeisEngine

section Facts

theorem commutes_leviM {K : Type*} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
    {H : Fin D.rank → Subgroup K} (hext : SteinbergExtras D n H) {A B : Set (Fin D.rank)}
    (h : ∀ i ∈ A, ∀ j ∈ B, i ≠ j ∧ D.cartan i j = 0) : Commutes (leviM D A) (leviM D B) := by
  have h1 : ∀ i ∈ A, ∀ j ∈ B, Commutes (rankOne D.rootGroup i) (rankOne D.rootGroup j) :=
    fun i hi j hj => commutes_rankOne_of_cartan_eq_zero hext (h i hi j hj).1 (h i hi j hj).2
  have h2 : ∀ i ∈ A, Commutes (rankOne D.rootGroup i) (leviM D B) := fun i hi =>
    (commutes_iff_le_centralizer.2 (iSup₂_le fun j hj =>
      commutes_iff_le_centralizer.1 (h1 i hi j hj).symm)).symm
  exact commutes_iff_le_centralizer.2 (iSup₂_le fun i hi =>
    commutes_iff_le_centralizer.1 (h2 i hi))

variable {F : Type} [Field F]

theorem exists_orderOf_eq_five [Finite F] (h5 : 5 ∣ Nat.card F - 1) :
    ∃ t : Fˣ, orderOf t = 5 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have h : 5 ∣ Nat.card Fˣ := by rw [Nat.card_units]; exact h5
  exact exists_prime_orderOf_dvd_card' 5 h

theorem cube_root_of_orderOf_eq_three {ω : Fˣ} (hω : orderOf ω = 3) :
    (ω : F) ^ 2 + ω + 1 = 0 := by
  have h3 : (ω : F) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← hω, pow_orderOf_eq_one, Units.val_one]
  have h1 : (ω : F) - 1 ≠ 0 := by
    intro h
    have : ω = 1 := Units.ext (sub_eq_zero.1 h)
    rw [this, orderOf_one] at hω
    omega
  have : ((ω : F) - 1) * ((ω : F) ^ 2 + ω + 1) = 0 := by linear_combination h3
  exact (mul_eq_zero.1 this).resolve_left h1

end Facts

section Main

set_option linter.unusedVariables false in
theorem three_le_pRank_five_sl {m : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
    {Y : Type} [Group Y] [Finite Y]
    (e : Matrix.ProjectiveSpecialLinearGroup (Fin (m + 1)) F ≃* Y) {X : Type} [Group X]
    [Finite X] (ρ : X →* Y) (hρ : Function.Surjective ρ) (hρker : ρ.ker ≤ Subgroup.center X)
    (h5 : 5 ∣ Nat.card ρ.ker → 5 ∣ m + 1 ∧ 5 ∣ Nat.card F - 1) (T : Sylow 2 Y) (J : Subgroup Y)
    (hNJ : Subgroup.normalizer ((T : Subgroup Y) : Set Y) ≤ J) (hJ : J ≠ ⊤)
    (P : Subgroup Y) (hPJ : P ≤ J) (hP : IsPGroup 5 P) (hPc : ¬ IsMulCommutative P) :
    3 ≤ CFSG.Open.pRank 5 (J.comap ρ) := by
  classical
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have := Fintype.ofFinite F
  obtain ⟨f, -, hf⟩ := FiniteField.card F 2
  have hfc : Nat.card F = 2 ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card, hf]
  have hb := borelQuotient_sl e
  obtain ⟨π', hb', hker', hBJ⟩ := BorelQuotient.exists_conj_parab hb T hNJ
  have hBJ' : (borel (rootDatum m F) (torus m F)).map π' ≤ J :=
    Subgroup.map_le_iff_le_comap.mpr hBJ
  obtain ⟨j, hj⟩ := LieOut.exists_node_not_mem_negIndices hb' hBJ' hJ
  obtain ⟨Q, hQ, hQp, hQc⟩ := exists_nonabelian_le_torus_sup_leviM hb' hBJ (by norm_num) hPJ hP hPc
  have hres : ∀ n : ℕ, (¬ ∃ a, RunIn (negIndices (rootDatum m F) (J.comap π')) a n) →
      ((Odd (f : ℕ) ∧ n < 20) ∨ ((f : ℕ) % 4 = 2 ∧ n < 10) ∨ (4 ∣ (f : ℕ) ∧ n < 5)) → False :=
    fun n hn hfm => hQc (isMulCommutative_of_le_torus_sup_leviM hfc hn hfm hQ hQp)
  have hcart : ∀ a b : Fin m, a.val + 2 ≤ b.val → (rootDatum m F).cartan a b = 0 := by
    intro a b hab
    change CartanMatrix.A m a b = 0
    have h1 : a ≠ b := fun h => by rw [h] at hab; omega
    have h2 : ¬ (a.val + 1 = b.val ∨ b.val + 1 = a.val) := by omega
    simp only [CartanMatrix.A, Matrix.of_apply, h1, h2, ite_false]
  have hcomm : ∀ a b : Fin m, a.val + 2 ≤ b.val →
      Commutes (rankOne (rootDatum m F).rootGroup a) (rankOne (rootDatum m F).rootGroup b) :=
    fun a b hab => commutes_rankOne_of_cartan_eq_zero hb'.extras
      (fun h => by rw [h] at hab; omega) (hcart a b hab)
  by_cases h4 : 4 ∣ (f : ℕ)
  ·
    have h5q : 5 ∣ Nat.card F - 1 := by
      have := (five_dvd_pow_sub_one_iff hfc 1).2 (by simpa using h4)
      simpa using this
    obtain ⟨t, ht⟩ := exists_orderOf_eq_five h5q
    by_cases hm5 : 5 ≤ m
    ·
      let a : Fin m := ⟨0, by omega⟩
      let b : Fin m := ⟨2, by omega⟩
      let c : Fin m := ⟨4, by omega⟩
      exact three_le_pRank_of_triple (by decide : Odd 5) hb'.ker_central ρ hρ hρker
        (hcomm a b (by simp [a, b])) (hcomm a c (by simp [a, c])) (hcomm b c (by simp [b, c]))
        (realOver_torus_five hBJ a ht) (realOver_torus_five hBJ b ht)
        (realOver_torus_five hBJ c ht)
    · exfalso
      exact hres 4 (not_exists_runIn_four (m := m) (by omega) hj)
        (Or.inr (Or.inr ⟨h4, by norm_num⟩))
  by_cases h2 : (f : ℕ) % 4 = 2
  ·
    have h3q : 3 ∣ Nat.card F - 1 := by
      obtain ⟨k, hk⟩ : ∃ k, (f : ℕ) = 2 * k := ⟨(f : ℕ) / 2, by omega⟩
      have hq : Nat.card F = 4 ^ k := by rw [hfc, hk, pow_mul]; norm_num
      rw [hq]
      simpa using Nat.sub_dvd_pow_sub_pow 4 1 k
    obtain ⟨ω, hω⟩ := exists_orderOf_eq_three h3q
    have hω' := cube_root_of_orderOf_eq_three (F := F) hω
    by_cases ho : ∃ a ∈ negIndices (rootDatum m F) (J.comap π'),
        ∃ b ∈ negIndices (rootDatum m F) (J.comap π'),
        ∃ c ∈ negIndices (rootDatum m F) (J.comap π'), a.val + 2 ≤ b.val ∧ b.val + 2 ≤ c.val
    · obtain ⟨a, ha, b, hb2, c, hc, hab, hbc⟩ := ho
      exact three_le_pRank_of_triple (by decide : Odd 5) hb'.ker_central ρ hρ hρker
        (hcomm a b hab) (hcomm a c (by omega)) (hcomm b c hbc)
        (realOver_upper_lower_five hBJ ha hω') (realOver_upper_lower_five hBJ hb2 hω')
        (realOver_upper_lower_five hBJ hc hω')
    · exfalso
      exact hres 5 (fun ⟨a, ha⟩ => ho (exists_orth_of_runIn ha)) (Or.inr (Or.inl ⟨h2, by norm_num⟩))
  ·
    have hodd : Odd (f : ℕ) := Nat.odd_iff.2 (by omega)
    by_cases ht : ∃ x y z : ℕ, x + 4 ≤ y ∧ y + 4 ≤ z ∧
        RunIn (negIndices (rootDatum m F) (J.comap π')) x 3 ∧
        RunIn (negIndices (rootDatum m F) (J.comap π')) y 3 ∧
        RunIn (negIndices (rootDatum m F) (J.comap π')) z 3
    · obtain ⟨x, y, z, hxy, hyz, hx, hy, hz⟩ := ht
      refine three_le_pRank_of_triple (by decide : Odd 5) hb'.ker_central ρ hρ hρker
        (commutes_leviM hb'.extras ?_) (commutes_leviM hb'.extras ?_)
        (commutes_leviM hb'.extras ?_) (realOver_leviM_five hBJ hx.1 hx.2)
        (realOver_leviM_five hBJ hy.1 hy.2) (realOver_leviM_five hBJ hz.1 hz.2)
      · rintro i ⟨hi1, hi2⟩ k ⟨hk1, hk2⟩
        exact ⟨fun h => by rw [h] at hi2; omega, hcart i k (by omega)⟩
      · rintro i ⟨hi1, hi2⟩ k ⟨hk1, hk2⟩
        exact ⟨fun h => by rw [h] at hi2; omega, hcart i k (by omega)⟩
      · rintro i ⟨hi1, hi2⟩ k ⟨hk1, hk2⟩
        exact ⟨fun h => by rw [h] at hi2; omega, hcart i k (by omega)⟩
    · exfalso
      exact hres 11 (fun ⟨a, ha⟩ => ht (exists_runs_of_runIn ha)) (Or.inl ⟨hodd, by norm_num⟩)

end Main

end CFSG.AGLEmbeddingD2.HeisLinear
