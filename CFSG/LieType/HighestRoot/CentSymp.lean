module

public import CFSG.LieType.HighestRoot.CentLinear
public import CFSG.LieType.HighestRoot.GenBasic
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Complement
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.RankOne
public import CFSG.LieType.Universal.Symplectic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoAllFields
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.LieType.HighestRoot

open CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

variable {K : Type} [Field K] {m : ℕ}

theorem eq_one_of_mem_center_of_pow_three [Finite K] (hK : Nat.card K = 3)
    {b : StatedSp m K} (hb : b ∈ Subgroup.center (StatedSp m K)) (h3 : b ^ 3 = 1) : b = 1 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · apply Subtype.ext
    apply Units.ext
    ext a
    exact a.elim (fun i => i.elim0) (fun i => i.elim0)
  rw [CFSG.LieType.Universal.Symplectic.center_eq, Subgroup.mem_subgroupOf] at hb
  obtain ⟨u, hu⟩ := hb
  set a : Fin m ⊕ Fin m := Sum.inl ⟨0, hm⟩
  have hgl : (b : GL (Fin m ⊕ Fin m) K) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, h3, Subgroup.coe_one]
  rw [← hu, ← map_pow] at hgl
  have h1 := congrArg (fun g : GL (Fin m ⊕ Fin m) K =>
    (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) a a) hgl
  simp only [Units.val_one, Matrix.one_apply_eq] at h1
  have hu3 : (u : K) ^ 3 = 1 := by
    rw [← h1]
    simp [Matrix.diagonal_pow, Matrix.diagonal_apply_eq]
  have hu1 : u = 1 := Units.ext (eq_one_of_pow_three_eq_one hK hu3)
  apply Subtype.ext
  rw [Subgroup.coe_one, ← hu, hu1, map_one]

theorem mem_longRootSp2_of_orderOf_eq_three [Finite K] (hK : Nat.card K = 3) (k : Fin (m + 1))
    {x : StatedSp (m + 1) K}
    (hx : x ∈ Subgroup.centralizer ({longInv K (m + 1) k} : Set (StatedSp (m + 1) K)))
    (h3 : orderOf x = 3) (hc : ∀ y ∈ complGroup (longInv K (m + 1) k), Commute x y) :
    x ∈ longRootSp2 K (m + 1) k := by
  have h2 := two_ne_zero_of_card_eq_three hK
  have hL := isLongRootSp2_standard (K := K) (n := m + 1) k
  obtain ⟨a, ha, b, hb, rfl⟩ := hL.exists_mul_of_mem_centralizer h2 hx
  have hab : Commute a b := hL.commute_of_mem_complGroup h2 ha hb
  have hbc : ∀ y ∈ complGroup (longInv K (m + 1) k), Commute b y := by
    intro y hy
    have e : b = a⁻¹ * (a * b) := by group
    rw [e]
    exact (hL.commute_of_mem_complGroup h2 ha hy).inv_left.mul_left (hc y hy)
  have hb3 : b ^ 3 = 1 := by
    have hx3 : (a * b) ^ 3 = 1 := by
      rw [← h3]
      exact pow_orderOf_eq_one _
    rw [hab.mul_pow] at hx3
    have e : b ^ 3 = (a ^ 3)⁻¹ := eq_inv_of_mul_eq_one_right hx3
    refine Subgroup.disjoint_def.1 (hL.disjoint_complGroup h2) ?_ (pow_mem hb 3)
    rw [e]
    exact inv_mem (pow_mem ha 3)
  obtain ⟨e⟩ := hL.nonempty_mulEquiv_complGroup h2
  have hcen : e.symm ⟨b, hb⟩ ∈ Subgroup.center (StatedSp m K) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨y, rfl⟩ := e.symm.surjective g
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hbc y y.2).eq.symm
  have hpow : e.symm ⟨b, hb⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨b, hb⟩ : complGroup (longInv K (m + 1) k)) ^ 3 = 1 := Subtype.ext hb3
    rw [this, map_one]
  have h1 := eq_one_of_mem_center_of_pow_three hK hcen hpow
  have hb1 : b = 1 := by
    have := congrArg (fun g => ((e g : complGroup _) : StatedSp (m + 1) K)) h1
    simpa using this
  rw [hb1, mul_one]
  exact ha

theorem centralizerCondition_longRootSp2 (h2 : (2 : K) ≠ 0) (k : Fin (m + 1)) :
    CentralizerCondition K (longRootSp2 K (m + 1) k) := by
  have hL := isLongRootSp2_standard (K := K) (n := m + 1) k
  have hc := isClassicalSL2_longRootSp2 h2 k
  intro z hz hz2
  obtain rfl := hL.eq_of_orderOf_eq_two h2 hz hz2
  refine ⟨hc.centralizer_le_normalizer, fun hK L hLc hLn hLe hzL => ?_⟩
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have hceq := hL.centralizer_eq h2
  refine eq_of_normal_of_orderOf_three hK hz2 hc.nonempty_mulEquiv
    (by rw [hceq]; exact le_sup_right) ?_ ?_
    (fun x hx h3 hcomm => mem_longRootSp2_of_orderOf_eq_three hK k hx h3 hcomm) hLc hLn hLe hzL
  · rw [hceq]
    exact sup_le (le_normalizer_of_forall_commute fun x hx y hy =>
      hL.commute_of_mem_complGroup h2 hx hy) Subgroup.le_normalizer
  · intro hzC
    have h1 := Subgroup.disjoint_def.1 (hL.disjoint_complGroup h2) hc.mem hzC
    rw [h1, orderOf_one] at hz2
    exact absurd hz2 (by decide)

theorem highestRootCZ_symplectic {F : Type} [Field F] (h2 : (2 : F) ≠ 0) (m : ℕ) :
    HighestRootCZ (CFSG.LieType.Universal.Symplectic.rootDatum (m + 1) F) F := by
  refine ⟨Pi.single (Fin.last m) 1, Or.inl ⟨1, Fin.last m, by simp⟩, fun δ hδ =>
    (CFSG.ClassicalInvolution.ModelFacts.isLongest_single_cartanC (m := m + 1) (by omega) rfl
      (CFSG.LieType.Universal.Symplectic.rootDatum (m + 1) F).isFiniteType
      (k := Fin.last m) (by simp)).2 δ hδ, ?_⟩
  have e : rankOneGroup (CFSG.LieType.Universal.Symplectic.rootDatum (m + 1) F)
      (Pi.single (Fin.last m) 1) = longRootSp2 F (m + 1) (Fin.last m) :=
    (range_longBlock_eq_rankOne (K := F) (by simp)).symm
  rw [e]
  exact centralizerCondition_longRootSp2 h2 _

end CFSG.LieType.HighestRoot
