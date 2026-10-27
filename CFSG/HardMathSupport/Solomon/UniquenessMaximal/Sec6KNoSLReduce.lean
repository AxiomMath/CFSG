module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FNotL2
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdAux
public import CFSG.GH74.Generic.S1.CompArith
public import CFSG.GH74.L5U5.ModelsBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdBasic

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.QuasithinUnique.Id2519

namespace NoSLReduce

section Unipotent

variable {K : Type} [Field K]

def uMat (a b : K) : Matrix (Fin 3) (Fin 3) K := !![1, a, b; 0, 1, 0; 0, 0, 1]

theorem uMat_mul (a b a' b' : K) : uMat a b * uMat a' b' = uMat (a + a') (b + b') := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uMat, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem uMat_zero : uMat (0 : K) 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uMat]

def uGL (a b : K) : GL (Fin 3) K :=
  ⟨uMat a b, uMat (-a) (-b), by rw [uMat_mul]; simp [uMat_zero],
    by rw [uMat_mul]; simp [uMat_zero]⟩

theorem uGL_mul (a b a' b' : K) : uGL a b * uGL a' b' = uGL (a + a') (b + b') :=
  Units.ext (uMat_mul a b a' b')

theorem uGL_zero : uGL (0 : K) 0 = 1 := Units.ext uMat_zero

theorem uGL_mem (a b : K) : uGL a b ∈ StatedSL 3 K := by
  apply Subgroup.subset_closure
  show (uMat a b).det = 1
  simp [uMat, Matrix.det_fin_three]

def uHom : Multiplicative (K × K) →* ↥(StatedSL 3 K) where
  toFun m := ⟨uGL (Multiplicative.toAdd m).1 (Multiplicative.toAdd m).2, uGL_mem _ _⟩
  map_one' := Subtype.ext (by simpa using uGL_zero (K := K))
  map_mul' m m' := Subtype.ext (by
    simpa using (uGL_mul (Multiplicative.toAdd m).1 (Multiplicative.toAdd m).2
      (Multiplicative.toAdd m').1 (Multiplicative.toAdd m').2).symm)

theorem uHom_injective : Function.Injective (uHom (K := K)) := by
  intro m m' h
  have h1 := congrArg (fun g : ↥(StatedSL 3 K) =>
    ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) h
  have h01 := congrFun (congrFun h1 0) 1
  have h02 := congrFun (congrFun h1 0) 2
  simp only [uHom, MonoidHom.coe_mk, OneHom.coe_mk, uGL, uMat] at h01 h02
  apply Multiplicative.toAdd.injective
  exact Prod.ext (by simpa using h01) (by simpa using h02)

end Unipotent

theorem two_eq_zero_of_card_four {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4) :
    (2 : K) = 0 := by
  obtain ⟨p, hp⟩ := CharP.exists K
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hpp, hcard⟩ := FiniteField.card (K := K) p
  have h4 : p ^ (n : ℕ) = 2 ^ 2 := by
    rw [← hcard, ← Nat.card_eq_fintype_card, hK]; norm_num
  have hd : p ∣ 2 ^ 2 := h4 ▸ dvd_pow_self p n.ne_zero
  have hp2 : p = 2 :=
    (Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).1 (hpp.dvd_of_dvd_pow hd)
  subst hp2
  exact_mod_cast CharP.cast_eq_zero K 2

theorem hasElemAb_sixteen_statedSL {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4) :
    HasElemAb 2 16 ↥(StatedSL 3 K) := by
  have h2 := two_eq_zero_of_card_four hK
  refine ⟨(uHom (K := K)).range, ⟨⟨⟨?_⟩⟩, ?_⟩, ?_⟩
  · rintro ⟨x, m, rfl⟩ ⟨y, m', rfl⟩
    apply Subtype.ext
    show uHom m * uHom m' = uHom m' * uHom m
    rw [← map_mul, ← map_mul, mul_comm]
  · rintro x ⟨m, rfl⟩
    rw [← map_pow]
    have : m ^ 2 = 1 := by
      apply Multiplicative.toAdd.injective
      have h : ∀ z : K, z + z = 0 := fun z => by
        rw [← two_mul, h2, zero_mul]
      ext <;> simp [pow_two, h]
    rw [this, map_one]
  · rw [Nat.card_congr (MonoidHom.ofInjective (uHom_injective (K := K))).toEquiv.symm]
    change Nat.card (K × K) = 16
    rw [Nat.card_prod, hK]

end NoSLReduce

open NoSLReduce

theorem hasElemAb_sixteen_of_isSLThreeFour {X : Type} [Group X] (h : IsSLThreeFour X) :
    HasElemAb 2 16 X := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
  exact HasElemAb.of_mulEquiv e.symm (hasElemAb_sixteen_statedSL hK)

@[expose] def IsLThreeEpsPar (e : ℕ) (Y : Type*) [Group Y] : Prop :=
  (∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K % 3 = 1 ∧ Nat.card K % 2 = e ∧
      Nonempty (Y ≃* StatedProj (StatedSL 3 K))) ∨
    (∃ (K : Type) (_ : Field K) (_ : Finite K) (q : ℕ), Nat.card K = q ^ 2 ∧ q % 3 = 2 ∧
      q % 2 = e ∧ Nonempty (Y ≃* StatedProj (StatedSU 3 q K)))

@[expose] def IsPSLThreeEven (Y : Type*) [Group Y] : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K % 3 = 1 ∧ Nat.card K % 2 = 0 ∧
    Nonempty (Y ≃* StatedProj (StatedSL 3 K))

@[expose] def InputL3U3OddNoSec16 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], IsLThreeEpsPar 1 Y →
    ∀ (H : Subgroup Y) (N : Subgroup ↥H) [N.Normal], ¬ HasElemAb 2 16 (↥H ⧸ N)

@[expose] def InputPSL3EvenNoSL : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], IsPSLThreeEven Y →
    ∀ (H : Subgroup Y) (N : Subgroup ↥H) [N.Normal], ¬ IsSLThreeFour (↥H ⧸ N)

theorem four_pow_mod_five (m : ℕ) : 4 ^ m % 5 = 1 ∨ 4 ^ m % 5 = 4 := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ]; omega

theorem not_five_dvd_psuCard_two_pow {f : ℕ} (hf : f % 2 = 1) :
    ¬ 5 ∣ CFSG.GH74.Generic.S1.psuCard (2 ^ f) := by
  obtain ⟨m, rfl⟩ : ∃ m, f = 2 * m + 1 := ⟨f / 2, by omega⟩
  set q := 2 ^ (2 * m + 1) with hq
  have hq' : q = 2 * 4 ^ m := by rw [hq, pow_succ, pow_mul]; ring
  have hq5 : q % 5 = 2 ∨ q % 5 = 3 := by rcases four_pow_mod_five m with h | h <;> omega
  have hq3 : q % 3 = 2 := by
    have : 4 ^ m % 3 = 1 := by rw [Nat.pow_mod]; simp
    omega
  have hg : Nat.gcd 3 (q + 1) = 3 := by
    have : 3 ∣ q + 1 := by omega
    exact Nat.gcd_eq_left this
  unfold CFSG.GH74.Generic.S1.psuCard
  rw [hg]
  intro h
  have hX : 3 ∣ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) := by
    have h3 : 3 ∣ q ^ 3 + 1 := by
      have : q ^ 3 % 3 = 2 := by rw [Nat.pow_mod, hq3]
      omega
    exact Dvd.dvd.mul_left (Dvd.dvd.mul_left h3 _) _
  have h5 : 5 ∣ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) := by
    rw [← Nat.mul_div_cancel' hX]
    exact Dvd.dvd.mul_left h 3
  have hp5 : Nat.Prime 5 := by norm_num
  have hqpos : 0 < q := by rw [hq']; positivity
  have hq2 : q ^ 2 % 5 = 4 := by
    rw [Nat.pow_mod]; rcases hq5 with h | h <;> rw [h]
  have hq3' : q ^ 3 % 5 = 3 ∨ q ^ 3 % 5 = 2 := by
    rw [Nat.pow_mod]; rcases hq5 with h | h <;> rw [h] <;> norm_num
  have hq2pos : 0 < q ^ 2 := by positivity
  rcases (Nat.Prime.dvd_mul hp5).1 h5 with h | h
  · have := hp5.dvd_of_dvd_pow h
    omega
  · rcases (Nat.Prime.dvd_mul hp5).1 h with h | h <;> omega

theorem not_sl_of_psu_even {Y : Type} [Group Y] [Finite Y] {K : Type} [Field K] [Finite K]
    {q : ℕ} (hc : Nat.card K = q ^ 2) (hq3 : q % 3 = 2) (hq2 : q % 2 = 0)
    (e : Y ≃* StatedProj (StatedSU 3 q K)) (H : Subgroup Y) (N : Subgroup ↥H) [N.Normal] :
    ¬ IsSLThreeFour (↥H ⧸ N) := by
  intro hSL
  have h60 := card_slThreeFour hSL
  have hdvd : 60480 ∣ Nat.card Y := by
    rw [← h60]
    exact (Dvd.intro _ (Subgroup.card_eq_card_quotient_mul_card_subgroup N).symm).trans
      (Subgroup.card_subgroup_dvd_card H)
  obtain ⟨p, f, hp, hchar, rfl⟩ := CFSG.GH74.L5U5.exists_prime_pow_of_card_eq_sq hc
  have hp2 : p = 2 := by
    have h2 : 2 ∣ p ^ f := Nat.dvd_of_mod_eq_zero hq2
    exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp.out).1
      (Nat.prime_two.dvd_of_dvd_pow h2)).symm
  subst hp2
  have hf1 : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h | h
    · subst h; simp at hq2
    · exact h
  have hfodd : f % 2 = 1 := by
    by_contra hne
    obtain ⟨m, rfl⟩ : ∃ m, f = 2 * m := ⟨f / 2, by omega⟩
    have : (2 ^ (2 * m)) % 3 = 1 := by
      rw [pow_mul, Nat.pow_mod]; simp
    omega
  have hcard : Nat.card Y = CFSG.GH74.Generic.S1.psuCard (2 ^ f) := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.GH74.Generic.S1.card_stated_psu3 hp.out hf1 hc
  rw [hcard] at hdvd
  exact not_five_dvd_psuCard_two_pow hfodd ((by norm_num : 5 ∣ 60480).trans hdvd)

theorem inputNoSLSection_of_odd_even (hOdd : InputL3U3OddNoSec16)
    (hEven : InputPSL3EvenNoSL) : InputNoSLSection := by
  intro Y _ _ hY H N _ hSL
  rcases hY with ⟨K, hF, hfin, h3, ⟨e⟩⟩ | ⟨K, hF, hfin, q, hc, hq3, ⟨e⟩⟩
  · rcases Nat.mod_two_eq_zero_or_one (Nat.card K) with h2 | h2
    · exact hEven Y ⟨K, hF, hfin, h3, h2, ⟨e⟩⟩ H N hSL
    · exact hOdd Y (Or.inl ⟨K, hF, hfin, h3, h2, ⟨e⟩⟩) H N
        (hasElemAb_sixteen_of_isSLThreeFour hSL)
  · rcases Nat.mod_two_eq_zero_or_one q with h2 | h2
    · exact not_sl_of_psu_even hc hq3 h2 e H N hSL
    · exact hOdd Y (Or.inr ⟨K, hF, hfin, q, hc, hq3, h2, ⟨e⟩⟩) H N
        (hasElemAb_sixteen_of_isSLThreeFour hSL)

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
