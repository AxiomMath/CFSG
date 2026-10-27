module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureThree.Dispatch
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureThree.Wreath
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.GlueGroup
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AltBlocksOrder

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureThree

open CFSG.Open Equiv Equiv.Perm Subgroup
open CFSG.RankThree.PartOne.StrongP (HasNoncommPair)
open CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis
open scoped commutatorElement

namespace AltThree

theorem exists_injective_pi_alt {k m n : ℕ} (h : k * m ≤ n) :
    ∃ φ : (Fin k → alternatingGroup (Fin m)) →* alternatingGroup (Fin n),
      Function.Injective φ := by
  classical
  let ψ : (Fin k → Perm (Fin m)) →* Perm (Fin k × Fin m) :=
    { toFun := fun σ => Equiv.prodCongrRight σ
      map_one' := Equiv.ext fun _ => rfl
      map_mul' := fun _ _ => Equiv.ext fun _ => rfl }
  have hψ : Function.Injective ψ := fun σ τ hστ => funext fun a => Equiv.ext fun b => by
    have := congrArg (fun f : Perm (Fin k × Fin m) => (f (a, b)).2) hστ
    simpa [ψ] using this
  obtain ⟨ι⟩ : Nonempty (Fin k × Fin m ↪ Fin n) :=
    Function.Embedding.nonempty_of_card_le (by simpa using h)
  let χ : (Fin k → alternatingGroup (Fin m)) →* Perm (Fin n) :=
    (viaEmbeddingHom ι).comp (ψ.comp ((alternatingGroup (Fin m)).subtype.compLeft (Fin k)))
  have hχ : ∀ x, χ x ∈ alternatingGroup (Fin n) := fun x => by
    rw [mem_alternatingGroup]
    simp only [χ, MonoidHom.comp_apply, viaEmbeddingHom_apply, viaEmbedding, sign_extendDomain]
    change sign (Equiv.prodCongrRight _) = 1
    rw [sign_prodCongrRight]
    exact Finset.prod_eq_one fun i _ => (x i).2
  refine ⟨χ.codRestrict _ hχ, (MonoidHom.injective_codRestrict _ _ _).mpr ?_⟩
  refine (viaEmbeddingHom_injective ι).comp (hψ.comp fun x y hxy => funext fun i => ?_)
  exact Subtype.ext (congrFun hxy i)

theorem exists_injective_nine {n : ℕ} (h : 9 ≤ n) :
    ∃ φ : alternatingGroup (Fin 9) →* alternatingGroup (Fin n), Function.Injective φ := by
  obtain ⟨φ, hφ⟩ := exists_injective_pi_alt (k := 1) (m := 9) (n := n) (by omega)
  let c : alternatingGroup (Fin 9) →* (Fin 1 → alternatingGroup (Fin 9)) :=
    { toFun := fun x _ => x
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  refine ⟨φ.comp c, hφ.comp fun x y hxy => ?_⟩
  exact congrFun hxy 0

@[expose] def u9 : Perm (Fin 9) := swap 0 1 * swap 1 2

@[expose] def v9 : Perm (Fin 9) := swap 3 4 * swap 4 5

@[expose] def w9 : Perm (Fin 9) := swap 6 7 * swap 7 8

@[expose] def y9 : Perm (Fin 9) :=
  (swap 0 3 * swap 3 6) * (swap 1 4 * swap 4 7) * (swap 2 5 * swap 5 8)

theorem sign_swap_mul_swap {a b c d : Fin 9} (hab : a ≠ b) (hcd : c ≠ d) :
    sign (swap a b * swap c d) = 1 := by
  rw [Perm.sign_mul, sign_swap hab, sign_swap hcd]
  rfl

theorem u9_mem : u9 ∈ alternatingGroup (Fin 9) :=
  sign_swap_mul_swap (by decide) (by decide)

theorem v9_mem : v9 ∈ alternatingGroup (Fin 9) :=
  sign_swap_mul_swap (by decide) (by decide)

theorem w9_mem : w9 ∈ alternatingGroup (Fin 9) :=
  sign_swap_mul_swap (by decide) (by decide)

theorem y9_mem : y9 ∈ alternatingGroup (Fin 9) := by
  rw [mem_alternatingGroup, y9, Perm.sign_mul, Perm.sign_mul,
    sign_swap_mul_swap (by decide) (by decide), sign_swap_mul_swap (by decide) (by decide),
    sign_swap_mul_swap (by decide) (by decide)]
  rfl

theorem rels :
    u9 * v9 = v9 * u9 ∧ u9 * w9 = w9 * u9 ∧ v9 * w9 = w9 * v9 ∧ u9 ^ 3 = 1 ∧ v9 ^ 3 = 1 ∧
      w9 ^ 3 = 1 ∧ y9 ^ 3 = 1 ∧ y9 * u9 * y9⁻¹ = v9 ∧ y9 * v9 * y9⁻¹ = w9 ∧
      y9 * w9 * y9⁻¹ = u9 ∧ u9 * y9 ≠ y9 * u9 := by
  unfold u9 v9 w9 y9
  decide +kernel

theorem comm_rels :
    ⁅u9, y9⁆ ^ 3 = 1 ∧ ⁅v9, y9⁆ ^ 3 = 1 ∧ (1 : Perm (Fin 9)) ≠ ⁅u9, y9⁆ ∧
      (1 : Perm (Fin 9)) ≠ ⁅u9, y9⁆ ^ 2 ∧ (1 : Perm (Fin 9)) ≠ ⁅v9, y9⁆ ∧
      ⁅u9, y9⁆ ≠ ⁅u9, y9⁆ ^ 2 ∧ ⁅u9, y9⁆ ≠ ⁅v9, y9⁆ ∧ ⁅u9, y9⁆ ^ 2 ≠ ⁅v9, y9⁆ := by
  simp only [commutatorElement_def]
  unfold u9 v9 y9
  decide +kernel

end AltThree

open AltThree

theorem dichThreeAt_alt_of_nine_le {n : ℕ} (hn : 9 ≤ n) :
    DichThreeAt (alternatingGroup (Fin n)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨φ, hφ⟩ := exists_injective_nine hn
  obtain ⟨huv, huw, hvw, hu, hv, hw, hy, h1, h2, h3, hnc⟩ := rels
  obtain ⟨hc1, hc2, hd1, hd2, hd3, hd4, hd5, hd6⟩ := comm_rels
  set u : alternatingGroup (Fin 9) := ⟨u9, u9_mem⟩
  set v : alternatingGroup (Fin 9) := ⟨v9, v9_mem⟩
  set w : alternatingGroup (Fin 9) := ⟨w9, w9_mem⟩
  set y : alternatingGroup (Fin 9) := ⟨y9, y9_mem⟩
  have hval : ∀ {a b : alternatingGroup (Fin 9)}, (a : Perm (Fin 9)) = b → φ a = φ b :=
    fun h => congrArg φ (Subtype.ext h)
  have hne : ∀ {a b : alternatingGroup (Fin 9)}, (a : Perm (Fin 9)) ≠ b → φ a ≠ φ b :=
    fun h hab => h (congrArg Subtype.val (hφ hab))
  have e1 : φ u * φ v = φ v * φ u := by rw [← map_mul, ← map_mul]; exact hval huv
  have e2 : φ u * φ w = φ w * φ u := by rw [← map_mul, ← map_mul]; exact hval huw
  have e3 : φ v * φ w = φ w * φ v := by rw [← map_mul, ← map_mul]; exact hval hvw
  have e4 : φ u ^ 3 = 1 := by rw [← map_pow, ← map_one φ]; exact hval hu
  have e5 : φ v ^ 3 = 1 := by rw [← map_pow, ← map_one φ]; exact hval hv
  have e6 : φ w ^ 3 = 1 := by rw [← map_pow, ← map_one φ]; exact hval hw
  have e7 : φ y ^ 3 = 1 := by rw [← map_pow, ← map_one φ]; exact hval hy
  have e8 : φ y * φ u * (φ y)⁻¹ = φ v := by
    rw [← map_inv, ← map_mul, ← map_mul]; exact hval h1
  have e9 : φ y * φ v * (φ y)⁻¹ = φ w := by
    rw [← map_inv, ← map_mul, ← map_mul]; exact hval h2
  have e10 : φ y * φ w * (φ y)⁻¹ = φ u := by
    rw [← map_inv, ← map_mul, ← map_mul]; exact hval h3
  have e11 : φ u * φ y ≠ φ y * φ u := by rw [← map_mul, ← map_mul]; exact hne hnc
  set U : Subgroup (alternatingGroup (Fin n)) := closure {φ u, φ v, φ w, φ y} with hUdef
  have hU : IsPGroup 3 U := isPGroup_closure_cycle e1 e2 e3 e4 e5 e6 e7 e8 e9 e10
  refine ⟨Or.inr (Or.inl ⟨φ u, φ y, e4, e7, e11, hU.to_le (closure_mono ?_)⟩), Or.inl ?_⟩
  · intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha ⊢
    rcases ha with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inr (Or.inr rfl))
  refine SylowDichotomyAt.of_not_cyclic_derived hU ?_
  have hmu : φ u ∈ U := subset_closure (by simp)
  have hmv : φ v ∈ U := subset_closure (by simp)
  have hmy : φ y ∈ U := subset_closure (by simp)
  have hc₁ : ⁅φ u, φ y⁆ ∈ ⁅U, U⁆ := commutator_mem_commutator hmu hmy
  have hc₂ : ⁅φ v, φ y⁆ ∈ ⁅U, U⁆ := commutator_mem_commutator hmv hmy
  have hcomm : ∀ a b : alternatingGroup (Fin 9), ⁅φ a, φ b⁆ = φ ⁅a, b⁆ := fun a b => by
    simp only [commutatorElement_def, map_mul, map_inv]
  have hcu : (⁅u, y⁆ : alternatingGroup (Fin 9)).val = ⁅u9, y9⁆ := rfl
  have hcv : (⁅v, y⁆ : alternatingGroup (Fin 9)).val = ⁅v9, y9⁆ := rfl
  have g1 : ⁅φ u, φ y⁆ ^ 3 = 1 := by
    rw [hcomm, ← map_pow, ← map_one φ]; exact hval (by rw [Subgroup.coe_pow, hcu]; exact hc1)
  have g2 : ⁅φ v, φ y⁆ ^ 3 = 1 := by
    rw [hcomm, ← map_pow, ← map_one φ]; exact hval (by rw [Subgroup.coe_pow, hcv]; exact hc2)
  have g3 : (1 : alternatingGroup (Fin n)) ≠ ⁅φ u, φ y⁆ := by
    rw [hcomm, ← map_one φ]; exact hne (by rw [hcu]; exact hd1)
  have g4 : (1 : alternatingGroup (Fin n)) ≠ ⁅φ u, φ y⁆ ^ 2 := by
    rw [hcomm, ← map_pow, ← map_one φ]; exact hne (by rw [Subgroup.coe_pow, hcu]; exact hd2)
  have g5 : (1 : alternatingGroup (Fin n)) ≠ ⁅φ v, φ y⁆ := by
    rw [hcomm, ← map_one φ]; exact hne (by rw [hcv]; exact hd3)
  have g6 : ⁅φ u, φ y⁆ ≠ ⁅φ u, φ y⁆ ^ 2 := by
    rw [hcomm, ← map_pow]; exact hne (by rw [Subgroup.coe_pow, hcu]; exact hd4)
  have g7 : ⁅φ u, φ y⁆ ≠ ⁅φ v, φ y⁆ := by
    rw [hcomm, hcomm]; exact hne (by rw [hcu, hcv]; exact hd5)
  have g8 : ⁅φ u, φ y⁆ ^ 2 ≠ ⁅φ v, φ y⁆ := by
    rw [hcomm, hcomm, ← map_pow]; exact hne (by rw [Subgroup.coe_pow, hcu, hcv]; exact hd6)
  refine not_isCyclic_of_four_cubes (H := ↥⁅U, U⁆) (a := 1)
    (b := ⟨⁅φ u, φ y⁆, hc₁⟩) (c := ⟨⁅φ u, φ y⁆, hc₁⟩ ^ 2) (d := ⟨⁅φ v, φ y⁆, hc₂⟩)
    (one_pow 3) (Subtype.ext g1) ?_ (Subtype.ext g2) ?_ ?_ ?_ ?_ ?_ ?_
  · apply Subtype.ext
    rw [← pow_mul, Subgroup.coe_pow]
    show ⁅φ u, φ y⁆ ^ (2 * 3) = 1
    rw [pow_mul', g1, one_pow]
  · exact fun h => g3 (congrArg Subtype.val h)
  · exact fun h => g4 (by simpa using congrArg Subtype.val h)
  · exact fun h => g5 (congrArg Subtype.val h)
  · exact fun h => g6 (by simpa using congrArg Subtype.val h)
  · exact fun h => g7 (congrArg Subtype.val h)
  · exact fun h => g8 (by simpa using congrArg Subtype.val h)

theorem dichThreeAt_alt_of_le_eight {n : ℕ} (hn2 : 2 ≤ n) (hn : n ≤ 8) :
    DichThreeAt (alternatingGroup (Fin n)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfac : (Nat.card (alternatingGroup (Fin n))).factorization 3 ≤ 2 := by
    rw [KFactProofs.Stroth.AltBlocks.factorization_card_alternatingGroup_fin Nat.prime_three
      (by norm_num) hn2 (by omega)]
    omega
  have hab : ∀ S : Sylow 3 (alternatingGroup (Fin n)),
      IsMulCommutative (S : Subgroup (alternatingGroup (Fin n))) := by
    intro S
    by_contra hS
    have h1 := pow_three_le_card_of_nonabelian S.isPGroup' hS
    rw [S.card_eq_multiplicity] at h1
    have h2 : 3 ^ (Nat.card (alternatingGroup (Fin n))).factorization 3 ≤ 3 ^ 2 :=
      Nat.pow_le_pow_right (by norm_num) hfac
    omega
  exact ⟨Or.inl hab, Or.inl (SylowDichotomyAt.of_factorization_le (by omega))⟩

theorem dichThreeAt_alt_of_twelve_le {n : ℕ} (hn : 12 ≤ n) :
    DichThreeAt (alternatingGroup (Fin n)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨φ, hφ⟩ := exists_injective_pi_alt (k := 4) (m := 3) (n := n) (by omega)
  have hA3 : Nat.card (alternatingGroup (Fin 3)) = 3 := by
    have h2 : 2 * Nat.card (alternatingGroup (Fin 3)) = Nat.factorial 3 := by
      rw [two_mul_nat_card_alternatingGroup, Nat.card_perm, Nat.card_fin]
    have : Nat.factorial 3 = 6 := rfl
    omega
  have hcomm3 : ∀ a b : alternatingGroup (Fin 3), a * b = b * a := by
    haveI : IsCyclic (alternatingGroup (Fin 3)) := isCyclic_of_prime_card hA3
    exact (IsCyclic.isMulCommutative (α := alternatingGroup (Fin 3))).is_comm.comm
  have hexp3 : ∀ a : alternatingGroup (Fin 3), a ^ 3 = 1 := fun a => by
    have h := pow_card_eq_one' (x := a)
    rwa [hA3] at h
  have hcard4 : Nat.card (Fin 4 → alternatingGroup (Fin 3)) = 3 ^ 4 := by
    rw [Nat.card_fun, hA3, Nat.card_eq_fintype_card, Fintype.card_fin]
  set E : Subgroup (alternatingGroup (Fin n)) := φ.range with hEdef
  have hE : IsElemAbelian 3 E := by
    refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, ?_⟩
    · obtain ⟨_, a, rfl⟩ := x
      obtain ⟨_, b, rfl⟩ := y
      simp only [Subgroup.coe_mul]
      rw [← map_mul, ← map_mul, show a * b = b * a from funext fun i => hcomm3 (a i) (b i)]
    · rintro _ ⟨a, rfl⟩
      rw [← map_pow, show a ^ 3 = 1 from funext fun i => hexp3 (a i), map_one]
  have hEcard : Nat.card E = 3 ^ 4 :=
    (Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv).symm.trans hcard4
  have h4 : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (alternatingGroup (Fin n))) :=
    le_pRank_of_elemAbelian (by norm_num) le_top hE hEcard
  exact ⟨Or.inr (Or.inr (Or.inl h4)),
    Or.inl (SylowDichotomyAt.of_elemAbelian Nat.prime_three hE hEcard le_rfl)⟩

theorem dichThreeAlt_holds : DichThreeAlt := by
  intro n hn
  by_cases h8 : n ≤ 8
  · exact dichThreeAt_alt_of_le_eight (by omega) h8
  by_cases h11 : n ≤ 11
  · exact dichThreeAt_alt_of_nine_le (by omega)
  · exact dichThreeAt_alt_of_twelve_le (by omega)

end CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureThree
