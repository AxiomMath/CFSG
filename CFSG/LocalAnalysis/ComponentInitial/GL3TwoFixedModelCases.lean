module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSLSemilinearInvolution
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTIUnitarySocleForms
public import CFSG.LocalAnalysis.ComponentClassification.SymmetricLocalEvenSymplecticSource
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.BinaryThreeSpaceFixedCodimensions

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.GL3TwoFixedModel

open Matrix Subgroup LinearFlag CFSG.Assembly.LowTwoRank FourGroupEvenCanonical
open CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.ComponentClassification.UnbalancedCatalog.EvenLinearSL
open CFSG.ComponentClassification.CatalogueBHigherLinearField
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification.OutcomeLocal (blockSwapIsometryEquivStatedSp oneRestrictEquiv
  nonempty_altIsometry_mulEquiv_statedSp dotForm_restrict_isAlt dotForm_restrict_nondegenerate
  finrank_dotForm_ker)
open CFSG.ComponentClassification.SymmetricLocal
  (small_standard_source_even_simple_symplectic_parameters_stated)

section Fixed

variable {G : Type*} [Group G]

@[expose] def autFixed (α : MulAut G) : Subgroup G :=
  (α : G →* G).eqLocus (MonoidHom.id G)

theorem mem_autFixed {α : MulAut G} {g : G} : g ∈ autFixed α ↔ α g = g :=
  Iff.rfl

end Fixed

section Normal

variable {M : Type*} [Group M]

theorem le_or_commutator_eq_bot {F T N : Subgroup M} (hTF : T ≤ F)
    (hTn : (T.subgroupOf F).Normal) [IsSimpleGroup T] (hNF : N ≤ F)
    (hTN : T ≤ normalizer (N : Set M)) : T ≤ N ∨ ⁅T, N⁆ = ⊥ := by
  have hnorm : (N.subgroupOf T).Normal := normal_subgroupOf_of_le_normalizer hTN
  rcases hnorm.eq_bot_or_eq_top with hbot | htop
  · right
    have hNT : N ≤ normalizer (T : Set M) := fun y hy =>
      (normal_subgroupOf_iff_le_normalizer hTF).1 hTn (hNF hy)
    rw [eq_bot_iff]
    intro z hz
    have h1 : z ∈ T := le_normalizer_iff_commutator_le_left.1 hNT hz
    have h2 : z ∈ N := le_normalizer_iff_commutator_le_right.1 hTN hz
    have h3 : (⟨z, h1⟩ : T) ∈ N.subgroupOf T := h2
    rw [hbot] at h3
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val (Subgroup.mem_bot.1 h3)
  · exact Or.inl (subgroupOf_eq_top.1 htop)

theorem le_of_normal_of_centralizer_commute {F T N : Subgroup M} (hTF : T ≤ F)
    (hTn : (T.subgroupOf F).Normal) [IsSimpleGroup T] (hTnab : ∃ a b : T, a * b ≠ b * a)
    (hNF : N ≤ F) (hTN : T ≤ normalizer (N : Set M))
    (hC : ∀ x ∈ T, ∀ y ∈ T, x ∈ centralizer (N : Set M) → y ∈ centralizer (N : Set M) →
      x * y = y * x) : T ≤ N := by
  rcases le_or_commutator_eq_bot hTF hTn hNF hTN with hle | hcomm
  · exact hle
  · exfalso
    obtain ⟨a, b, hab⟩ := hTnab
    have hTC : T ≤ centralizer (N : Set M) := commutator_eq_bot_iff_le_centralizer.1 hcomm
    exact hab (Subtype.ext (hC _ a.2 _ b.2 (hTC a.2) (hTC b.2)))

theorem false_of_normal_of_centralizer_two_group [Finite M] {F T R Q : Subgroup M} (hTF : T ≤ F)
    (hTn : (T.subgroupOf F).Normal) [IsSimpleGroup T] (hTnab : ∃ a b : T, a * b ≠ b * a)
    (hRF : R ≤ F) (hTR : T ≤ normalizer (R : Set M)) (hRab : ⁅R, R⁆ = ⊥) (hQ : IsPGroup 2 Q)
    (hC : ∀ x ∈ T, x ∈ centralizer (R : Set M) → x ∈ Q) : False := by
  obtain ⟨a, b, hab⟩ := hTnab
  have hRR : R ≤ centralizer (R : Set M) := commutator_eq_bot_iff_le_centralizer.1 hRab
  have hTRc : T ≤ centralizer (R : Set M) := by
    rcases le_or_commutator_eq_bot hTF hTn hRF hTR with hle | hcomm
    · exfalso
      exact hab (Subtype.ext (mem_centralizer_iff.1 (hRR (hle b.2)) a (hle a.2)))
    · exact commutator_eq_bot_iff_le_centralizer.1 hcomm
  have hT2 : IsPGroup 2 T := hQ.to_le fun x hx => hC x hx (hTRc hx)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial T := ⟨⟨a * b, b * a, hab⟩⟩
  have hZ := hT2.center_nontrivial
  rcases (inferInstance : (center T).Normal).eq_bot_or_eq_top with h | h
  · rw [h] at hZ
    exact (not_nontrivial_iff_subsingleton.2 inferInstance) hZ
  · exact hab ((mem_center_iff.1 (h ▸ mem_top b)) a)

end Normal

section GL3Two

theorem card_GL_three_two : Nat.card (GL (Fin 3) (ZMod 2)) = 168 :=
  CFSG.ProperTwoGeneratedCore.BinaryThreeSpace.FixedCodim.card_GL3

@[expose] def unipotentThree : GL (Fin 3) (ZMod 2) :=
  ⟨!![1, 1, 0; 0, 1, 1; 0, 0, 1], !![1, 1, 1; 0, 1, 1; 0, 0, 1], by decide, by decide⟩

theorem unipotentThree_pow_four : unipotentThree ^ 4 = 1 ∧ unipotentThree ^ 2 ≠ 1 := by
  refine ⟨Units.ext ?_, fun h => ?_⟩
  · rw [Units.val_pow_eq_pow_val]
    decide
  · have := congrArg Units.val h
    rw [Units.val_pow_eq_pow_val] at this
    revert this
    decide

end GL3Two

section LinearTwo

variable {K : Type*} [Field K] [CharP K 2]

theorem sq_eq_trace_smul_add_one (g : SpecialLinearGroup (Fin 2) K) :
    (g : Matrix (Fin 2) (Fin 2) K) * g =
      ((g : Matrix (Fin 2) (Fin 2) K) 0 0 + (g : Matrix (Fin 2) (Fin 2) K) 1 1) • g + 1 := by
  have hdet := g.2
  rw [Matrix.det_fin_two] at hdet
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul, Matrix.one_apply, Fin.isValue, Fin.zero_eta, Fin.mk_one] <;>
    simp <;> first | ring1 | linear_combination (-1 : K) * hdet - h2

theorem sq_eq_one_of_sq_eq_smul_add_one {A : Matrix (Fin 2) (Fin 2) K} {t : K}
    (hsq : A * A = t • A + 1) (h4 : A * A * (A * A) = 1) : A * A = 1 := by
  have htt : t + t = 0 := CharTwo.add_self_eq_zero t
  have hexp : A * A * (A * A) = t ^ 2 • (A * A) + 1 := by
    calc A * A * (A * A) = (t • A + 1) * (t • A + 1) := by rw [hsq]
      _ = t ^ 2 • (A * A) + (t + t) • A + 1 := by
          simp only [add_mul, mul_add, smul_mul_smul_comm, one_mul, mul_one]
          module
      _ = t ^ 2 • (A * A) + 1 := by rw [htt, zero_smul, add_zero]
  have hz : t ^ 2 • (A * A) = 0 := add_eq_right.1 (hexp.symm.trans h4)
  have hAA : A * A ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h4
    exact zero_ne_one h4
  have ht0 : t = 0 := by
    rcases smul_eq_zero.1 hz with h | h
    · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h
    · exact absurd h hAA
  rw [hsq, ht0, zero_smul, zero_add]

theorem sl_two_sq_eq_one_of_pow_four (g : SpecialLinearGroup (Fin 2) K) (hg : g ^ 4 = 1) :
    g ^ 2 = 1 := by
  have hg' : g * g * (g * g) = 1 := by
    rw [← hg]
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  have h4 : (g : Matrix (Fin 2) (Fin 2) K) * g * (g * g) = 1 := congrArg Subtype.val hg'
  have h2 := sq_eq_one_of_sq_eq_smul_add_one (sq_eq_trace_smul_add_one g) h4
  rw [pow_two]
  exact Subtype.ext h2

theorem sq_eq_one_of_pow_four_eq_one (x : projectiveSL 2 K) (hx : x ^ 4 = 1) : x ^ 2 = 1 := by
  set e := LinearCover.projectiveSLTwoEquivSL K
  have h := sl_two_sq_eq_one_of_pow_four (e x) (by rw [← map_pow, hx, map_one])
  have := congrArg e.symm h
  rwa [map_pow, MulEquiv.symm_apply_apply, map_one] at this

end LinearTwo

section Arith

theorem le_three_of_two_pow_dvd {m : ℕ} (h : 2 ^ m ∣ 168) : m ≤ 3 := by
  by_contra hm
  have h16 : 2 ^ 4 ∣ 168 := (Nat.pow_dvd_pow 2 (by omega)).trans h
  norm_num at h16

theorem three_le_choose_two {n : ℕ} (hn : 3 ≤ n) : 3 ≤ n * (n - 1) / 2 := by
  have h6 : 6 ≤ n * (n - 1) :=
    calc 6 = 3 * 2 := by norm_num
      _ ≤ n * (n - 1) := Nat.mul_le_mul hn (by omega)
  omega

theorem eq_three_of_choose_two_le {n : ℕ} (hn : 3 ≤ n) (h : n * (n - 1) / 2 ≤ 3) : n = 3 := by
  by_contra h3
  have h12 : 12 ≤ n * (n - 1) :=
    calc 12 = 4 * 3 := by norm_num
      _ ≤ n * (n - 1) := Nat.mul_le_mul (by omega) (by omega)
  omega

theorem eq_of_pow_pow_dvd {a b : ℕ} (ha : 1 ≤ a) (hb : 3 ≤ b) (h : (2 ^ a) ^ b ∣ 168) :
    a = 1 ∧ b = 3 := by
  rw [← pow_mul] at h
  have h3 := le_three_of_two_pow_dvd h
  have h1 : a * 3 ≤ a * b := Nat.mul_le_mul_left a hb
  obtain ⟨c, hc⟩ : ∃ c, c = a * b := ⟨_, rfl⟩
  rw [← hc] at h3 h1
  have ha1 : a = 1 := by omega
  subst ha1
  exact ⟨rfl, by omega⟩

end Arith

section Transport

variable {M : Type*} [Group M]

theorem mem_map_conj_inv {g x : M} {T : Subgroup M} :
    x ∈ T.map (MulAut.conj g⁻¹).toMonoidHom ↔ g * x * g⁻¹ ∈ T := by
  rw [mem_map_equiv, MulAut.conj_symm_apply, inv_inv]

theorem conj_transport {I : Subgroup M} [hI : I.Normal] {α β g : M} (hαβ : α = g * β * g⁻¹)
    {T : Subgroup M} (hT : T ≤ I ⊓ centralizer {α})
    (hTn : (T.subgroupOf (I ⊓ centralizer {α})).Normal) :
    T.map (MulAut.conj g⁻¹).toMonoidHom ≤ I ⊓ centralizer {β} ∧
      ((T.map (MulAut.conj g⁻¹).toMonoidHom).subgroupOf (I ⊓ centralizer {β})).Normal := by
  have hmem : ∀ y, y ∈ I ⊓ centralizer {β} ↔ g * y * g⁻¹ ∈ I ⊓ centralizer {α} := by
    intro y
    rw [mem_inf, mem_inf, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff, hαβ]
    constructor
    · rintro ⟨hy, hc⟩
      refine ⟨hI.conj_mem y hy g, ?_⟩
      calc g * y * g⁻¹ * (g * β * g⁻¹) = g * (y * β) * g⁻¹ := by group
        _ = g * (β * y) * g⁻¹ := by rw [hc]
        _ = g * β * g⁻¹ * (g * y * g⁻¹) := by group
    · rintro ⟨hy, hc⟩
      refine ⟨?_, ?_⟩
      · have h1 := hI.conj_mem _ hy g⁻¹
        rwa [show g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y by group] at h1
      · calc y * β = g⁻¹ * (g * y * g⁻¹ * (g * β * g⁻¹)) * g := by group
          _ = g⁻¹ * (g * β * g⁻¹ * (g * y * g⁻¹)) * g := by rw [hc]
          _ = β * y := by group
  refine ⟨fun x hx => (hmem x).2 (hT (mem_map_conj_inv.1 hx)), ⟨fun x hx y => ?_⟩⟩
  rw [mem_subgroupOf, mem_map_conj_inv] at hx ⊢
  have h1 := hTn.conj_mem ⟨_, (hmem x).1 x.2⟩ (mem_subgroupOf.2 hx) ⟨_, (hmem y).1 y.2⟩
  rw [mem_subgroupOf] at h1
  have h2 : g * ((y * x * y⁻¹ : ↥(I ⊓ centralizer {β})) : M) * g⁻¹ =
      g * y * g⁻¹ * (g * x * g⁻¹) * (g * y * g⁻¹)⁻¹ := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [h2]
  exact h1

theorem eq_of_le_of_normal {F T N : Subgroup M} (hTN : T ≤ N) (hNF : N ≤ F)
    (hTn : (T.subgroupOf F).Normal) [IsSimpleGroup N] (hT : T ≠ ⊥) : T = N := by
  have hn : (T.subgroupOf N).Normal := ⟨fun x hx y => by
    rw [mem_subgroupOf] at hx ⊢
    have h := hTn.conj_mem ⟨x, hNF x.2⟩ (mem_subgroupOf.2 hx) ⟨y, hNF y.2⟩
    rw [mem_subgroupOf] at h
    exact h⟩
  rcases hn.eq_bot_or_eq_top with h | h
  · exfalso
    apply hT
    rw [eq_bot_iff]
    intro x hx
    have hx' : (⟨x, hTN hx⟩ : N) ∈ T.subgroupOf N := hx
    rw [h, mem_bot] at hx'
    rw [mem_bot]
    exact congrArg Subtype.val hx'
  · exact le_antisymm hTN (subgroupOf_eq_top.1 h)

theorem ne_bot_of_isSimpleGroup (T : Subgroup M) [IsSimpleGroup T] : T ≠ ⊥ :=
  (Subgroup.nontrivial_iff_ne_bot T).1 inferInstance

end Transport

section Unitary

variable {K : Type} [Field K]

theorem pow_dvd_card_unitaryPSU {p e : ℕ} (h : UnitaryFieldData p e K) {n : ℕ} (hn : 2 ≤ n) :
    (p ^ e) ^ (n * (n - 1) / 2) ∣ Nat.card (unitaryPSU h n) := by
  obtain ⟨r, ε, hε, rfl⟩ : ∃ r ε, ε ≤ 1 ∧ n = 2 * r + ε := ⟨n / 2, n % 2, by omega, by omega⟩
  have hr : 1 ≤ r := by omega
  obtain ⟨hU, -, -, ⟨eU, -⟩, -, -, -⟩ := unitary_order_and_Sylow h hr hε
  obtain ⟨R, hR⟩ := exists_isHypTransport h (r := r) (ε := ε)
  rw [← Nat.card_congr (hypProjTransport h hR).toEquiv, ← hU, Nat.card_congr eU.toEquiv]
  exact Subgroup.card_subgroup_dvd_card _

theorem card_unitaryPSU_three (h : UnitaryFieldData 2 1 K) : Nat.card (unitaryPSU h 3) = 72 := by
  obtain ⟨-, -, -, -, -, hS, hP⟩ := unitary_order_and_Sylow h (r := 1) (ε := 1) le_rfl le_rfl
  obtain ⟨R, hR⟩ := exists_isHypTransport h (r := 1) (ε := 1)
  have hS' : Nat.card (hypSU h 1 1) = 216 := by
    have h216 : (Nat.card (hypSU h 1 1) : ℤ) = 216 := by
      rw [hS]
      decide
    exact_mod_cast h216
  have h1 := (Nat.card_congr (hypProjTransport h hR).toEquiv).symm
  rw [hP, hS'] at h1
  exact h1.trans (by norm_num)

end Unitary

section Cases

variable {K : Type} [Field K] {n : ℕ}

theorem field_case [Finite K] {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (hn : 3 ≤ n)
    {τ : K ≃+* K} (hfe : Even f) (hτx : ∀ x, τ x = x ^ 2 ^ (f / 2))
    {T : Subgroup (MulAut (projectiveSL n K))}
    (hT : T ≤ inner (projectiveSL n K) ⊓ centralizer {fieldAut n K τ})
    (hTn : (T.subgroupOf (inner (projectiveSL n K) ⊓ centralizer {fieldAut n K τ})).Normal)
    [IsSimpleGroup T] (hTnab : ∃ a b : T, a * b ≠ b * a) (hcard : Nat.card T = 168) :
    n = 3 ∧ f = 2 := by
  obtain ⟨-, ⟨e, -⟩, hNinn, -, hNC, hNnormal, hcentN⟩ :=
    linear_quadratic_field_full_centralizer_rigidity τ hn
  have hNF := le_inf hNinn hNC
  have hle : T ≤ (subfieldConj n τ).range :=
    le_of_normal_of_centralizer_commute hT hTn hTnab hNF
      (fun t ht => (normal_subgroupOf_iff_le_normalizer hNC).1 hNnormal (hT ht).2)
      (fun x _ y _ hxN hyN => by
        rw [hcentN] at hxN hyN
        obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hxN
        obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hyN
        exact (Commute.zpow_zpow_self _ i j).eq)
  have hsimp : IsSimpleGroup (ProjectiveSpecialLinearGroup (Fin n) (fixedField K τ)) :=
    (CFSG.LinearGroups.linear_projective_simple (by omega) (Or.inl hn)).2.1
  have : IsSimpleGroup (subfieldConj n τ).range :=
    (e.symm.trans (LinearCover.projectiveSpecialLinearEquivProjectiveSL n _).symm).isSimpleGroup
  have heq := eq_of_le_of_normal hle hNF hTn (ne_bot_of_isSimpleGroup T)
  have hcardP : Nat.card (projectiveSL n (fixedField K τ)) = 168 := by
    rw [Nat.card_congr e.toEquiv, ← heq, hcard]
  obtain ⟨m, hm⟩ := hfe
  have he : 1 ≤ f / 2 := by omega
  have hKe : Nat.card K = 2 ^ (2 * (f / 2)) := by rw [hK]; congr 1; omega
  have h : UnitaryFieldData 2 (f / 2) K := ⟨Nat.prime_two, he, hKe⟩
  have hk : Nat.card (fixedField K τ) = 2 ^ (f / 2) := by
    rw [← h.card_fixedField]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun x =>
      (mem_fixedField K τ x).trans (by rw [hτx]; exact Iff.rfl))
  have hdvd : Nat.card (fixedField K τ) ^ (n * (n - 1) / 2) ∣ 168 := by
    rw [← card_projUnitriangular n, ← hcardP]
    exact Subgroup.card_subgroup_dvd_card _
  rw [hk] at hdvd
  obtain ⟨h1, h3⟩ := eq_of_pow_pow_dvd he (three_le_choose_two hn) hdvd
  exact ⟨eq_three_of_choose_two_le hn h3.le, by omega⟩

theorem graph_field_case {e : ℕ} (h : UnitaryFieldData 2 e K) (hn : 3 ≤ n) {σ : K ≃+* K}
    (hσ : ∀ x, σ x = h.bar x) {T : Subgroup (MulAut (projectiveSL n K))}
    (hT : T ≤ inner (projectiveSL n K) ⊓ centralizer {fieldAut n K σ * dualAut n K})
    (hTn : (T.subgroupOf
      (inner (projectiveSL n K) ⊓ centralizer {fieldAut n K σ * dualAut n K})).Normal)
    [IsSimpleGroup T] (hTnab : ∃ a b : T, a * b ≠ b * a) (hcard : Nat.card T = 168) : False := by
  have := h.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, ⟨ι, -⟩, hNinn, -, hNC, hNnormal, hcentN⟩ :=
    linear_graph_field_full_centralizer_rigidity h hn σ hσ
  have hNF := le_inf hNinn hNC
  have hle : T ≤ (unitarySU 2 e K n).map (conjAut n K) :=
    le_of_normal_of_centralizer_commute hT hTn hTnab hNF
      (fun t ht => (normal_subgroupOf_iff_le_normalizer hNC).1 hNnormal (hT ht).2)
      (fun x _ y _ hxN hyN => by
        rw [hcentN] at hxN hyN
        obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hxN
        obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hyN
        exact (Commute.zpow_zpow_self _ i j).eq)
  have hcardN : Nat.card ((unitarySU 2 e K n).map (conjAut n K)) = Nat.card (unitaryPSU h n) :=
    (Nat.card_congr ι.toEquiv).symm
  by_cases hq : n = 3 ∧ e = 1
  · obtain ⟨rfl, rfl⟩ := hq
    have hdvd : 168 ∣ Nat.card (unitaryPSU h 3) := by
      rw [← hcardN, ← hcard]
      exact Subgroup.card_dvd_of_le hle
    rw [card_unitaryPSU_three h] at hdvd
    norm_num at hdvd
  · have hnq : (n, 2 ^ e) ≠ (3, 2) := by
      intro h32
      simp only [Prod.mk.injEq] at h32
      exact hq ⟨h32.1, Nat.pow_right_injective (le_refl 2) (by simpa using h32.2)⟩
    have := CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU K 2 e h.card_eq_sq n hn
      hnq
    have : IsSimpleGroup ((unitarySU 2 e K n).map (conjAut n K)) :=
      (ι.symm.trans (unitaryPSUEquiv h (by omega))).isSimpleGroup
    have heq := eq_of_le_of_normal hle hNF hTn (ne_bot_of_isSimpleGroup T)
    have hdvd := pow_dvd_card_unitaryPSU h (n := n) (by omega)
    rw [← hcardN, ← heq, hcard] at hdvd
    obtain ⟨h1, h3⟩ := eq_of_pow_pow_dvd h.one_le (three_le_choose_two hn) hdvd
    exact hq ⟨eq_three_of_choose_two_le hn h3.le, h1⟩

theorem symplectic_case {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (hn : 3 ≤ n)
    (C : GL (Fin n) K) {r : ℕ} (hr : 1 ≤ r)
    (hCr : (n = 2 * r ∧ (C : Matrix (Fin n) (Fin n) K) = UnitaryHigher.blockSwapJ n r) ∨
      ((C : Matrix (Fin n) (Fin n) K) = 1 ∧ n = 2 * r + 1))
    {T : Subgroup (MulAut (projectiveSL n K))}
    (hT : T ≤ inner (projectiveSL n K) ⊓ centralizer {conjAut n K C * dualAut n K})
    (hTn : (T.subgroupOf
      (inner (projectiveSL n K) ⊓ centralizer {conjAut n K C * dualAut n K})).Normal)
    [IsSimpleGroup T] (hTnab : ∃ a b : T, a * b ≠ b * a) (hcard : Nat.card T = 168) : False := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  have hC : (C : Matrix (Fin n) (Fin n) K) = 1 ∨
      ∃ r, n = 2 * r ∧ (C : Matrix (Fin n) (Fin n) K) = UnitaryHigher.blockSwapJ n r := by
    rcases hCr with ⟨h1, h2⟩ | ⟨h1, -⟩
    · exact Or.inr ⟨r, h1, h2⟩
    · exact Or.inl h1
  obtain ⟨hinj, hNinn, -, -, hNC, hNnormal, hcan⟩ :=
    even_linear_canonical_graph_symplectic_centralizers hf hK hn C hC
  have hcent := (hcan (by
    rcases hCr with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨r, h1, h2⟩
    · exact Or.inr ⟨h1, ⟨r, h2⟩⟩)).1
  have hNF := le_inf hNinn hNC
  have hle : T ≤ (matrixIsometryGroup (C : Matrix (Fin n) (Fin n) K)).map (conjAut n K) :=
    le_of_normal_of_centralizer_commute hT hTn hTnab hNF
      (fun t ht => (normal_subgroupOf_iff_le_normalizer hNC).1 hNnormal (hT ht).2)
      (fun x hx y hy hxN hyN => by
        have hx' := mem_inf.2 ⟨(hT hx).2, hxN⟩
        have hy' := mem_inf.2 ⟨(hT hy).2, hyN⟩
        rw [hcent] at hx' hy'
        obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hx'
        obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hy'
        exact (Commute.zpow_zpow_self _ i j).eq)
  have eN : (matrixIsometryGroup (C : Matrix (Fin n) (Fin n) K)).map (conjAut n K) ≃*
      matrixIsometryGroup (C : Matrix (Fin n) (Fin n) K) :=
    (MulEquiv.subgroupCongr (by rw [MonoidHom.range_comp, range_subtype])).trans
      (MonoidHom.ofInjective hinj).symm
  obtain ⟨eSp⟩ : Nonempty (matrixIsometryGroup (C : Matrix (Fin n) (Fin n) K) ≃* StatedSp r K) := by
    rcases hCr with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨(MulEquiv.subgroupCongr (congrArg matrixIsometryGroup h2)).trans
        (blockSwapIsometryEquivStatedSp (by omega))⟩
    · have hC1 : (C : Matrix (Fin n) (Fin n) K) =
          ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by rw [h1, Units.val_one]
      obtain ⟨e₂⟩ := nonempty_altIsometry_mulEquiv_statedSp _
        (dotForm_restrict_isAlt (k := K) (n := n)) (dotForm_restrict_nondegenerate h2)
        (finrank_dotForm_ker h2)
      exact ⟨((MulEquiv.subgroupCongr (congrArg matrixIsometryGroup hC1)).trans
        (oneRestrictEquiv h2)).trans e₂⟩
  have hcardN : Nat.card ((matrixIsometryGroup (C : Matrix (Fin n) (Fin n) K)).map
      (conjAut n K)) = Nat.card (StatedSp r K) := Nat.card_congr (eN.trans eSp).toEquiv
  have hdvd : 168 ∣ Nat.card (StatedSp r K) := by
    rw [← hcardN, ← hcard]
    exact Subgroup.card_dvd_of_le hle
  have hSp := SymplecticFlag.card_statedSp (K := K) r
  rw [hK] at hSp
  by_cases hsmall : f = 1 ∧ (r = 1 ∨ r = 2)
  · obtain ⟨rfl, hr12⟩ := hsmall
    rcases hr12 with rfl | rfl <;> rw [hSp] at hdvd <;> revert hdvd <;> decide
  · have hcond : (Infinite K ∨ 4 ≤ Nat.card K) ∨ (Nat.card K = 3 ∧ 2 ≤ r) ∨
        (Nat.card K = 2 ∧ 3 ≤ r) := by
      by_cases hf1 : f = 1
      · right
        right
        refine ⟨by rw [hK, hf1]; norm_num, ?_⟩
        by_contra hr3
        exact hsmall ⟨hf1, by omega⟩
      · left
        right
        rw [hK]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
    have := CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp K r hr hcond
    obtain ⟨-, -, -, -, ⟨eProj⟩⟩ := small_standard_source_even_simple_symplectic_parameters_stated
      (X := StatedSp r K) hK hr ⟨MulEquiv.refl _⟩
    have : IsSimpleGroup ((matrixIsometryGroup (C : Matrix (Fin n) (Fin n) K)).map
        (conjAut n K)) := ((eN.trans eSp).trans eProj.symm).isSimpleGroup
    have heq := eq_of_le_of_normal hle hNF hTn (ne_bot_of_isSimpleGroup T)
    have h168 : Nat.card (StatedSp r K) = 168 := by rw [← hcardN, ← heq, hcard]
    have hdvd2 : 2 ^ (f * r ^ 2) ∣ 168 := by
      rw [← h168, hSp, pow_mul]
      exact dvd_mul_right _ _
    have hle3 := le_three_of_two_pow_dvd hdvd2
    have hr1 : r = 1 := by
      by_contra hr1
      have h4 : 1 * 2 ^ 2 ≤ f * r ^ 2 := Nat.mul_le_mul hf (Nat.pow_le_pow_left (by omega) 2)
      omega
    subst hr1
    rw [hSp] at h168
    have hf3 : f ≤ 3 := by simpa using hle3
    interval_cases f <;> revert h168 <;> decide

theorem radical_case {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (hn : 3 ≤ n) (hev : Even n)
    {T : Subgroup (MulAut (projectiveSL n K))}
    (hT : T ≤ inner (projectiveSL n K) ⊓ centralizer {dualAut n K})
    (hTn : (T.subgroupOf (inner (projectiveSL n K) ⊓ centralizer {dualAut n K})).Normal)
    [IsSimpleGroup T] (hTnab : ∃ a b : T, a * b ≠ b * a) : False := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  have : Finite (MulAut (projectiveSL n K)) := finite_mulAut_projectiveSL
  obtain ⟨r, hr⟩ := hev
  obtain ⟨-, -, -, -, -, -, -, -, -, hRinn, hRC, hRn, hCR, hQ, -⟩ :=
    even_linear_nonalternating_graph_radical hf hK (show n = 2 * r by omega) (by omega)
      (⟨0, by omega⟩ : Fin n)
  refine false_of_normal_of_centralizer_two_group hT hTn hTnab (le_inf hRinn hRC)
    (fun t ht => (normal_subgroupOf_iff_le_normalizer hRC).1 hRn (hT ht).2) ?_ hQ ?_
  · rw [eq_bot_iff, commutator_le]
    rintro _ ⟨g, hg, rfl⟩ _ ⟨g', hg', rfl⟩
    rw [mem_bot, commutatorElement_eq_one_iff_mul_comm, ← map_mul, ← map_mul,
      NonalternatingRadical.radicalGroup_comm ⟨r, hr⟩ hg hg']
  · intro x hx hxR
    have hx' := mem_inf.2 ⟨(hT hx).2, hxR⟩
    rwa [hCR] at hx'

theorem even_linear_cases (hn : 3 ≤ n) {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    {α : MulAut (projectiveSL n K)} (hα2 : α ^ 2 = 1) (hαout : α ∉ inner (projectiveSL n K))
    {T : Subgroup (MulAut (projectiveSL n K))}
    (hT : T ≤ inner (projectiveSL n K) ⊓ centralizer {α})
    (hTn : (T.subgroupOf (inner (projectiveSL n K) ⊓ centralizer {α})).Normal)
    [IsSimpleGroup T] (hTnab : ∃ a b : T, a * b ≠ b * a) (hcard : Nat.card T = 168) :
    n = 3 ∧ f = 2 ∧ ∃ (H : GL (Fin n) K) (σ : K ≃+* K), (∀ x, σ x = x ^ 2) ∧
      α = conjAut n K H * fieldAut n K σ * (conjAut n K H)⁻¹ := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  have htrans : ∀ {β g : MulAut (projectiveSL n K)}, α = g * β * g⁻¹ →
      ∃ T' : Subgroup (MulAut (projectiveSL n K)),
        T' ≤ inner (projectiveSL n K) ⊓ centralizer {β} ∧
        (T'.subgroupOf (inner (projectiveSL n K) ⊓ centralizer {β})).Normal ∧
        IsSimpleGroup T' ∧ (∃ a b : T', a * b ≠ b * a) ∧ Nat.card T' = 168 := by
    intro β g hαβ
    obtain ⟨h1, h2⟩ := conj_transport hαβ hT hTn
    set e := T.equivMapOfInjective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective
    refine ⟨_, h1, h2, e.symm.isSimpleGroup, ?_, (Nat.card_congr e.toEquiv).symm.trans hcard⟩
    obtain ⟨a, b, hab⟩ := hTnab
    exact ⟨e a, e b, fun h => hab (e.injective (by rw [map_mul, map_mul, h]))⟩
  obtain ⟨-, hform⟩ := automorphism_generation (K := K) hn
  obtain ⟨A, τ, ε, hε, rfl⟩ := hform α
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hε with rfl | rfl
  · rw [pow_zero, mul_one] at hα2 hαout ⊢
    by_cases hτ : τ = 1
    · subst hτ
      rw [map_one, mul_one] at hα2 hαout
      exact absurd (conjAut_mem_inner_of_sq_eq_one hf hK A hα2) hαout
    obtain ⟨hfe, hτx, H, hαH⟩ := even_linear_field_involution_descent hf hK hn A τ hτ hα2
    obtain ⟨T', h1, h2, h3, h4, h5⟩ := htrans hαH
    obtain ⟨rfl, rfl⟩ := field_case hf hK hn hfe hτx h1 h2 h4 h5
    exact ⟨rfl, rfl, H, τ, fun x => by rw [hτx]; norm_num, hαH⟩
  · rw [pow_one] at hα2 hαout
    exfalso
    by_cases hτ : τ = 1
    · subst hτ
      rw [map_one, mul_one] at hα2 hαout
      obtain ⟨-, ⟨H₀, C, -, hα, hC⟩, -⟩ :=
        UnitaryHigher.even_linear_pure_graph_involution_normal_forms hf hK hn A hα2
      obtain ⟨T', h1, h2, h3, h4, h5⟩ := htrans (β := conjAut n K C * dualAut n K)
        (g := conjAut n K H₀) (by rw [map_one, mul_one, pow_one]; exact hα)
      rcases hC with ⟨h1C, -⟩ | ⟨r, hr, hJ, -⟩
      · rcases Nat.even_or_odd n with hev | ⟨r, hr⟩
        · have hβ : conjAut n K C * dualAut n K = dualAut n K := by
            rw [show C = 1 from Units.ext h1C, map_one, one_mul]
          rw [hβ] at h1 h2
          exact radical_case hf hK hn hev h1 h2 h4
        · exact symplectic_case hf hK hn C (r := r) (by omega) (Or.inr ⟨h1C, hr⟩) h1 h2 h4 h5
      · exact symplectic_case hf hK hn C (r := r) (by omega) (Or.inl ⟨hr, hJ⟩) h1 h2 h4 h5
    · obtain ⟨hfe, hτx, B, hαB⟩ :=
        UnitaryHigher.linear_graph_field_involution_descent Nat.prime_two hf hK hn A τ hτ hα2
      obtain ⟨m, hm⟩ := hfe
      have he : 1 ≤ f / 2 := by omega
      have hKe : Nat.card K = 2 ^ (2 * (f / 2)) := by rw [hK]; congr 1; omega
      have h : UnitaryFieldData 2 (f / 2) K := ⟨Nat.prime_two, he, hKe⟩
      obtain ⟨T', h1, h2, h3, h4, h5⟩ := htrans (β := fieldAut n K τ * dualAut n K)
        (g := conjAut n K B) (by rw [pow_one]; exact hαB)
      exact graph_field_case h hn (fun x => by rw [hτx, h.bar_apply]) h1 h2 h4 h5

end Cases

end CFSG.LocalAnalysis.ComponentInitial.GL3TwoFixedModel
