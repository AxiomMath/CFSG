module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs256k
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs256h2
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs295f2
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeTwE6TwoModel
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeCharData
import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeTwE6TwoFusion
import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeTwE6TwoCriterion
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal209TwoOuterIn
import CFSG.LieType.SeitzGeneration.ExcPlaneModel
import CFSG.LieType.SeitzGeneration.ExcTorusCatTw
import CFSG.Adapters.TauCetiExceptional.EvenAll
import CFSG.LieType.Chevalley.EvenF4AutomorphismNormalForm
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.AssemblyExc
import CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridgeHolds
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs295e2
import CFSG.LieType.Chevalley.GraphFixedCenterTrivial
import CFSG.LieType.Chevalley.GraphFixedF4Canonical
import CFSG.LocalAnalysis.StandardType.GGTableBE6TwoPilotLayer
import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeE6TwoFusion
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeE6TwoBalance
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LayerBridge
import CFSG.LocalAnalysis.GLTheoremB.LayerTools
import CFSG.Assembly.OrderReductions.LinearOrders
public import CFSG.Quasithin.Background.A3Structure36BPrime
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.Basic
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcCtx
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcPlumb
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcSmall
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwCoreAssembly
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24Plane
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24Red
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeFactsTwoF
public import CFSG.LieType.SeitzGeneration.SeitzStatus
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294KDOutTwE6

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256k

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.StandardType CFSG.StandardType.TableBExc.E6Three CFSG.StandardType.E6ThreeEnd
  CFSG.StandardType.E6TwoPilot
open CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3E6
open scoped MatrixGroups

section Normalize

variable {X : Type*} [Group X] [Finite X]

theorem mem_normalizer_of_pow_three_pow_k {C J : Subgroup X} (hJ : CFSG.Open.IsComponentOf J C)
    (hA5 : Nonempty ((↥J ⧸ Subgroup.center ↥J) ≃* alternatingGroup (Fin 5)))
    (h5 : ¬ 5 ^ 3 ∣ Nat.card X) {g : X} (hg : g ∈ C) {n : ℕ} (hgn : g ^ (3 ^ n) = 1) :
    g ∈ Subgroup.normalizer (J : Set X) := by
  classical
  by_contra hN
  have hodd : 2 * ((3 ^ n + 1) / 2) = 3 ^ n + 1 := by
    have h : (3 ^ n) % 2 = 1 := by
      rw [Nat.pow_mod]
      norm_num
    omega
  have hsq : g = (g ^ 2) ^ ((3 ^ n + 1) / 2) := by
    rw [← pow_mul, hodd, pow_succ, hgn, one_mul]
  set J₁ := J.map (MulAut.conj g : X →* X) with hJ₁def
  set J₂ := J.map (MulAut.conj (g ^ 2) : X →* X) with hJ₂def
  have hJ₁ : CFSG.Open.IsComponentOf J₁ C := isComponentOf_map_conj_of_mem_k hJ hg
  have hJ₂ : CFSG.Open.IsComponentOf J₂ C := isComponentOf_map_conj_of_mem_k hJ (pow_mem hg 2)
  have hne01 : J ≠ J₁ := fun h => hN (mem_normalizer_of_map_conj_eq_self_k h.symm)
  have hne02 : J ≠ J₂ := fun h => hN (by
    have h2 := mem_normalizer_of_map_conj_eq_self_k h.symm
    rw [hsq]
    exact pow_mem h2 _)
  have hne12 : J₁ ≠ J₂ := fun h => hN (by
    have h2 := mem_normalizer_of_map_conj_eq_k h
    have e2 : g⁻¹ * g ^ 2 = g := by group
    rwa [e2] at h2)
  let H : Fin 3 → Subgroup X := ![J, J₁, J₂]
  have hH : ∀ i, CFSG.Open.IsComponentOf (H i) C := by
    intro i
    fin_cases i
    · exact hJ
    · exact hJ₁
    · exact hJ₂
  have hdist : ∀ i j, i ≠ j → H i ≠ H j := by
    intro i j hij
    fin_cases i <;> fin_cases j
    all_goals first
      | exact absurd rfl hij
      | exact hne01
      | exact hne01.symm
      | exact hne02
      | exact hne02.symm
      | exact hne12
      | exact hne12.symm
  have hcomm : Pairwise fun i j => ∀ x y : X, x ∈ H i → y ∈ H j → Commute x y :=
    fun i j hij x y hx hy =>
      CFSG.LocalAnalysis.GLTheoremA.I142.components_commute_of_ne (hH i) (hH j) (hdist i j hij)
        x hx y hy
  have hA5' : ∀ i, Nonempty ((↥(H i) ⧸ Subgroup.center ↥(H i)) ≃* alternatingGroup (Fin 5)) := by
    intro i
    fin_cases i
    · exact hA5
    · exact nonempty_a5_map (MulAut.conj g) hA5
    · exact nonempty_a5_map (MulAut.conj (g ^ 2)) hA5
  have h60 := sixty_pow_dvd_of_pairwise_commute H hcomm (fun i => (hH i).1) hA5'
  rw [show Fintype.card (Fin 3) = 3 by rfl] at h60
  exact h5 ((pow_dvd_pow_of_dvd (by norm_num : 5 ∣ 60) 3).trans
    (h60.trans (Subgroup.card_subgroup_dvd_card C)))

end Normalize

section Commutator

variable {X : Type*} [Group X]

theorem commutator_mul_comm_of_three_group_k {A' R : Subgroup X} [Finite A'] {m : ℕ}
    (hA' : Nat.card A' ∣ 3 ^ m) (hnorm : ∀ a ∈ A', ∀ r ∈ R, a * r * a⁻¹ ∈ R)
    (hperf : commutator R = ⊤)
    (hA5 : Nonempty ((↥R ⧸ Subgroup.center ↥R) ≃* alternatingGroup (Fin 5)))
    {x y : X} (hx : x ∈ A') (hy : y ∈ A') {r : X} (hr : r ∈ R) :
    x * y * x⁻¹ * y⁻¹ * r = r * (x * y * x⁻¹ * y⁻¹) := by
  obtain ⟨e⟩ := hA5
  let ψ : ↥A' →* MulAut (alternatingGroup (Fin 5)) :=
    (MulAut.congr e).toMonoidHom.comp ((autQuotCenter ↥R).comp (conjAutOfNormalizes R A' hnorm))
  have hrange : Nat.card ψ.range ∣ 3 := by
    refine dvd_three_of_dvd_pow_of_dvd_120 (m := m) ((Subgroup.card_range_dvd ψ).trans hA') ?_
    rw [← card_mulAut_alternatingGroup_five_k]
    exact Subgroup.card_subgroup_dvd_card _
  have hcomm : ∀ p q : ψ.range, p * q = q * p := by
    rcases (Nat.dvd_prime Nat.prime_three).1 hrange with h1 | h3
    · intro p q
      haveI : Subsingleton ψ.range := (Nat.card_eq_one_iff_unique.1 h1).1
      exact Subsingleton.elim _ _
    · haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      haveI : Finite ψ.range := Nat.finite_of_card_ne_zero (by rw [h3]; norm_num)
      haveI : IsCyclic ψ.range := isCyclic_of_prime_card h3
      obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ψ.range)
      intro p q
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hg p)
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hg q)
      exact (Commute.zpow_zpow_self g i j).eq
  set a : ↥A' := ⟨x, hx⟩ with ha
  set b : ↥A' := ⟨y, hy⟩ with hb
  have hab : ψ a * ψ b = ψ b * ψ a :=
    congrArg Subtype.val
      (hcomm ⟨ψ a, ⟨a, rfl⟩⟩ ⟨ψ b, ⟨b, rfl⟩⟩)
  have hψc : ψ (a * b * a⁻¹ * b⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hab]
    group
  have h1 : autQuotCenter ↥R (conjAutOfNormalizes R A' hnorm (a * b * a⁻¹ * b⁻¹)) = 1 := by
    apply (MulAut.congr e).injective
    rw [map_one]
    exact hψc
  have h3 := eq_one_of_autQuotCenter_eq_one hperf h1
  have h4 : ((a * b * a⁻¹ * b⁻¹ : ↥A') : X) * r * ((a * b * a⁻¹ * b⁻¹ : ↥A') : X)⁻¹ = r :=
    congrArg (fun σ : MulAut ↥R => ((σ ⟨r, hr⟩ : R) : X)) h3
  have hc : ((a * b * a⁻¹ * b⁻¹ : ↥A') : X) = x * y * x⁻¹ * y⁻¹ := rfl
  rw [hc] at h4
  calc x * y * x⁻¹ * y⁻¹ * r
      = x * y * x⁻¹ * y⁻¹ * r * (x * y * x⁻¹ * y⁻¹)⁻¹ * (x * y * x⁻¹ * y⁻¹) := by group
    _ = r * (x * y * x⁻¹ * y⁻¹) := by rw [h4]

end Commutator

section SL6

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] [CharP K 2]

theorem pow_three_eq_one_of_dCert_k (hK : Nat.card K = 2) {Z₁ Z₂ : SL(6, K)} {Zm₁ Zm₂ : List ℕ}
    (h₁ : (Z₁ : Matrix (Fin 6) (Fin 6) K) = real K Zm₁)
    (h₂ : (Z₂ : Matrix (Fin 6) (Fin 6) K) = real K Zm₂) (hl₁ : Zm₁.length = 6)
    (hl₂ : Zm₂.length = 6) (hb₁ : ∀ a ∈ Zm₁, a < 64) (hb₂ : ∀ a ∈ Zm₂, a < 64)
    (hd₁ : bdiag Zm₁ = true) (hd₂ : bdiag Zm₂ = true) (hcert : dCert [Zm₁, Zm₂] [] = true)
    {x : SL(6, K)} (hx₁ : x * Z₁ = Z₁ * x) (hx₂ : x * Z₂ = Z₂ * x) : x ^ 3 = 1 := by
  have hrealpow : ∀ (g : SL(6, K)) (n : ℕ),
      ((g ^ n : SL(6, K)) : Matrix (Fin 6) (Fin 6) K) = (g : Matrix (Fin 6) (Fin 6) K) ^ n :=
    fun g n => Matrix.SpecialLinearGroup.coe_pow g n
  have hd : ∀ Zm ∈ [Zm₁, Zm₂], bdiag Zm = true := by
    intro Zm hZm
    rcases List.mem_pair.1 hZm with rfl | rfl
    · exact hd₁
    · exact hd₂
  have hcM : ∀ y : SL(6, K), y * Z₁ = Z₁ * y → y * Z₂ = Z₂ * y →
      certM [Zm₁, Zm₂] [] (maskOf (y : Matrix (Fin 6) (Fin 6) K)) = true := by
    intro y hy₁ hy₂
    refine certM_of_dCert hcert hd (length_maskOf _) (maskOf_lt _) fun Zm hZm => ?_
    rcases List.mem_pair.1 hZm with rfl | rfl
    · exact mmul_comm_of_commute hK h₁ hl₁ hb₁ hy₁
    · exact mmul_comm_of_commute hK h₂ hl₂ hb₂ hy₂
  have hx30 : x ^ 30 = 1 := by
    have h := hcM x hx₁ hx₂
    simp only [certM, Bool.and_eq_true, beq_iff_eq] at h
    have hAl := length_maskOf (x : Matrix (Fin 6) (Fin 6) K)
    have e := congrArg (real K) h.1
    rw [real_mmul _ _ (length_p30 hAl), real_p30 hAl, real_maskOf_SL hK x] at e
    have e' : x ^ 30 * x ^ 30 = x ^ 30 := Subtype.ext (by
      rw [Matrix.SpecialLinearGroup.coe_mul, hrealpow]
      exact e)
    exact mul_eq_left.1 e'
  have hy₁ : x ^ 3 * Z₁ = Z₁ * x ^ 3 := (Commute.pow_left (show Commute x Z₁ from hx₁) 3).eq
  have hy₂ : x ^ 3 * Z₂ = Z₂ * x ^ 3 := (Commute.pow_left (show Commute x Z₂ from hx₂) 3).eq
  have hy10 : (x ^ 3) ^ 10 = 1 := by rw [← pow_mul]; exact hx30
  have hrest : p10 (maskOf ((x ^ 3 : SL(6, K)) : Matrix (Fin 6) (Fin 6) K)) ≠ mone ∨
      maskOf ((x ^ 3 : SL(6, K)) : Matrix (Fin 6) (Fin 6) K) = mone := by
    have h := hcM (x ^ 3) hy₁ hy₂
    simp only [certM, List.any_nil, Bool.or_false, Bool.and_eq_true, Bool.or_eq_true,
      Bool.not_eq_true', beq_eq_false_iff_ne, beq_iff_eq] at h
    exact h.2
  set B := maskOf ((x ^ 3 : SL(6, K)) : Matrix (Fin 6) (Fin 6) K) with hB
  have hBl : B.length = 6 := length_maskOf _
  have hBb : ∀ a ∈ B, a < 64 := maskOf_lt _
  have hBy : real K B = ((x ^ 3 : SL(6, K)) : Matrix (Fin 6) (Fin 6) K) := real_maskOf_SL hK _
  have hp10 : p10 B = mone := by
    refine real_injective (R := K) (length_p10 hBl) length_mone (mmul_lt _ _ (mmul_lt _ _ hBb))
      mone_lt ?_
    rw [real_p10 hBl, hBy, real_mone, ← hrealpow, hy10, Matrix.SpecialLinearGroup.coe_one]
  have hB1 : B = mone := by
    rcases hrest with h | h
    · exact absurd hp10 h
    · exact h
  refine Subtype.ext ?_
  rw [← hBy, hB1, real_mone, Matrix.SpecialLinearGroup.coe_one]

end SL6

section E6Rest

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem not_dvd_ordE6_two_k : ¬ 5 ^ 3 ∣ CFSG.Open.ordE6 2 := by
  unfold CFSG.Open.ordE6
  norm_num

theorem pow_three_eq_one_of_commute_phi0_k (hK : Nat.card K = 2) {Z₁ Z₂ : SL(6, K)}
    (hZ : ∀ M : SL(6, K), M * Z₁ = Z₁ * M → M * Z₂ = Z₂ * M → M ^ 3 = 1)
    {x : adjointGroup .E6 K} (hx0 : x * uE6Two 0 = uE6Two 0 * x)
    (hx1 : x * phi0 K Z₁ = phi0 K Z₁ * x) (hx2 : x * phi0 K Z₂ = phi0 K Z₂ * x) : x ^ 3 = 1 := by
  have hxc : x ∈ Subgroup.centralizer ({uE6Two 0} : Set (adjointGroup .E6 K)) :=
    Subgroup.mem_centralizer_singleton_iff.2 hx0
  obtain ⟨y, hy, l, hl, rfl⟩ := exists_mul_of_mem_centralizer_uE6Two_zero hK hxc
  have hlr : l ∈ (phi0 K).range := by rw [range_phi0]; exact hl
  obtain ⟨M, rfl⟩ := hlr
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  have hyL : ∀ j ∈ leviB0 K, uE6Two 0 ^ k * j = j * uE6Two 0 ^ k := fun j hj =>
    (Commute.zpow_left (uE6Two_zero_comm_of_mem_leviB0 hj) k).eq
  have hZL : ∀ Z : SL(6, K), phi0 K Z ∈ leviB0 K := fun Z => by
    rw [← range_phi0]
    exact ⟨Z, rfl⟩
  have hcomm : ∀ Z : SL(6, K),
      uE6Two 0 ^ k * phi0 K M * phi0 K Z = phi0 K Z * (uE6Two 0 ^ k * phi0 K M) →
        M * Z = Z * M := by
    intro Z h
    apply phi0_injective hK
    rw [map_mul, map_mul]
    have h' : uE6Two 0 ^ k * (phi0 K M * phi0 K Z) = uE6Two 0 ^ k * (phi0 K Z * phi0 K M) := by
      calc uE6Two 0 ^ k * (phi0 K M * phi0 K Z) = uE6Two 0 ^ k * phi0 K M * phi0 K Z := by group
        _ = phi0 K Z * (uE6Two 0 ^ k * phi0 K M) := h
        _ = (phi0 K Z * uE6Two 0 ^ k) * phi0 K M := by group
        _ = (uE6Two 0 ^ k * phi0 K Z) * phi0 K M := by rw [← hyL _ (hZL Z)]
        _ = uE6Two 0 ^ k * (phi0 K Z * phi0 K M) := by group
    exact mul_left_cancel h'
  have hM3 : M ^ 3 = 1 := hZ M (hcomm Z₁ hx1) (hcomm Z₂ hx2)
  have hu3 : (uE6Two (K := K) 0 ^ k) ^ 3 = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
      uE6Two_pow_three CharTwo.two_eq_zero 0, one_zpow]
  have hc : Commute (uE6Two (K := K) 0 ^ k) (phi0 K M) := hyL _ (hZL M)
  rw [hc.mul_pow, hu3, one_mul, ← map_pow, hM3, map_one]

theorem sE6Two_commutator_torus_k (h2 : (2 : K) = 0) (x : Fin 4 → ZMod 3) :
    sE6Two K * torusE6Two h2 (.ofAdd x) * (sE6Two K)⁻¹ * (torusE6Two h2 (.ofAdd x))⁻¹ =
      torusE6Two h2 (.ofAdd (msFun x - x)) := by
  rw [torusE6Two_msAut h2, msAut_ofAdd, ← map_inv, ← map_mul, ← ofAdd_neg, ← ofAdd_add,
    sub_eq_add_neg]

theorem tE6Two_commutator_torus_k (h2 : (2 : K) = 0) (x : Fin 4 → ZMod 3) :
    tE6Two K * torusE6Two h2 (.ofAdd x) * (tE6Two K)⁻¹ * (torusE6Two h2 (.ofAdd x))⁻¹ =
      torusE6Two h2 (.ofAdd (mtFun x - x)) := by
  rw [torusE6Two_mtAut h2, mtAut_ofAdd, ← map_inv, ← map_mul, ← ofAdd_neg, ← ofAdd_add,
    sub_eq_add_neg]

theorem sE6Two_mem_range_psiHom_k (h2 : (2 : K) = 0) : sE6Two K ∈ (psiHom K h2).range :=
  ⟨SemidirectProduct.inr (Multiplicative.ofAdd 1, 1), by
    rw [psiHom_apply, stHom_apply]
    simp only [SemidirectProduct.left_inr, SemidirectProduct.right_inr, map_one, one_mul,
      toAdd_ofAdd, toAdd_one, ZMod.val_zero, pow_zero, mul_one]
    exact pow_one _⟩

theorem tE6Two_mem_range_psiHom_k (h2 : (2 : K) = 0) : tE6Two K ∈ (psiHom K h2).range :=
  ⟨SemidirectProduct.inr (1, Multiplicative.ofAdd 1), by
    rw [psiHom_apply, stHom_apply]
    simp only [SemidirectProduct.left_inr, SemidirectProduct.right_inr, map_one, one_mul,
      toAdd_ofAdd, toAdd_one, ZMod.val_zero, pow_zero]
    exact pow_one _⟩

theorem torusE6Two_mem_range_psiHom_k (h2 : (2 : K) = 0) (x : Fin 4 → ZMod 3) :
    torusE6Two h2 (.ofAdd x) ∈ (psiHom K h2).range :=
  ⟨SemidirectProduct.inl (.ofAdd x), psiHom_inl h2 _⟩

theorem commutator_mul_comm_of_mem_psiHom_k (hK : Nat.card K = 2) {v : Fin 4 → ZMod 3}
    {J : Subgroup (adjointGroup .E6 K)}
    (hJ : CFSG.Open.IsComponentOf J (Subgroup.centralizer
      ({torusE6Two CharTwo.two_eq_zero (.ofAdd v)} : Set (adjointGroup .E6 K))))
    (hA5 : Nonempty ((↥J ⧸ Subgroup.center ↥J) ≃* alternatingGroup (Fin 5)))
    {a b : adjointGroup .E6 K} (ha : a ∈ (psiHom K CharTwo.two_eq_zero).range)
    (hb : b ∈ (psiHom K CharTwo.two_eq_zero).range)
    (hav : a * torusE6Two CharTwo.two_eq_zero (.ofAdd v) =
      torusE6Two CharTwo.two_eq_zero (.ofAdd v) * a)
    (hbv : b * torusE6Two CharTwo.two_eq_zero (.ofAdd v) =
      torusE6Two CharTwo.two_eq_zero (.ofAdd v) * b)
    {j : adjointGroup .E6 K} (hj : j ∈ J) :
    a * b * a⁻¹ * b⁻¹ * j = j * (a * b * a⁻¹ * b⁻¹) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  haveI : Finite (adjointGroup .E6 K) := generated_group_finite .E6 K
  set C := Subgroup.centralizer
    ({torusE6Two CharTwo.two_eq_zero (.ofAdd v)} : Set (adjointGroup .E6 K)) with hC
  set P₀ := (psiHom K CharTwo.two_eq_zero).range with hP₀
  set A' := P₀ ⊓ C with hA'
  have hP₀card : Nat.card P₀ = 3 ^ 6 := card_range_psiHom _
  have hcardA' : Nat.card A' ∣ 3 ^ 6 := hP₀card ▸ Subgroup.card_dvd_of_le inf_le_left
  have h5 : ¬ 5 ^ 3 ∣ Nat.card (adjointGroup .E6 K) := by
    rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_E6, hK]
    exact not_dvd_ordE6_two_k
  have hnorm : ∀ g ∈ A', ∀ r ∈ J, g * r * g⁻¹ ∈ J := by
    intro g hg r hr
    have hg6 : g ^ (3 ^ 6) = 1 := by
      have h := pow_card_eq_one' (G := P₀) (x := ⟨g, hg.1⟩)
      rw [hP₀card] at h
      have h' := congrArg Subtype.val h
      rw [Subgroup.coe_pow, Subgroup.coe_one] at h'
      exact h'
    have hN := mem_normalizer_of_pow_three_pow_k hJ hA5 h5 hg.2 hg6
    exact (Subgroup.mem_normalizer_iff.1 hN r).1 hr
  exact commutator_mul_comm_of_three_group_k hcardA' hnorm hJ.2.2.1 hA5
    ⟨ha, Subgroup.mem_centralizer_singleton_iff.2 hav⟩
    ⟨hb, Subgroup.mem_centralizer_singleton_iff.2 hbv⟩ hj

theorem false_of_commute_e6Two_targets_k (hK : Nat.card K = 2) {J : Subgroup (adjointGroup .E6 K)}
    (hA5 : Nonempty ((↥J ⧸ Subgroup.center ↥J) ≃* alternatingGroup (Fin 5)))
    (h₁ : ∀ j ∈ J, torusE6Two CharTwo.two_eq_zero (.ofAdd ![1, 1, 1, 1]) * j =
      j * torusE6Two CharTwo.two_eq_zero (.ofAdd ![1, 1, 1, 1]))
    (h₂ : ∀ j ∈ J, torusE6Two CharTwo.two_eq_zero (.ofAdd ![1, 2, 0, 0]) * j =
      j * torusE6Two CharTwo.two_eq_zero (.ofAdd ![1, 2, 0, 0]))
    (h₃ : ∀ j ∈ J, torusE6Two CharTwo.two_eq_zero (.ofAdd ![2, 0, 1, 0]) * j =
      j * torusE6Two CharTwo.two_eq_zero (.ofAdd ![2, 0, 1, 0])) : False := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  set g := genWord K [0, 2] with hgdef
  set Z₁ : SL(6, K) := zSL ![0, 1, 2] with hZ₁
  set Z₂ : SL(6, K) := tvSLWord (zword ![0, 0, 1] ++ zword ![1, 0, 0] ++ zword ![1, 0, 0])
    with hZ₂
  have hZ : ∀ M : SL(6, K), M * Z₁ = Z₁ * M → M * Z₂ = Z₂ * M → M ^ 3 = 1 := fun M hM₁ hM₂ =>
    pow_three_eq_one_of_dCert_k hK (coe_tvSLWord_eq_real _) (coe_tvSLWord_eq_real _)
      (length_wordMask _) (length_wordMask _) (wordMask_lt _) (wordMask_lt _)
      (by decide +kernel) (by decide +kernel) dCert_z012_3 hM₁ hM₂
  have hφ₁ : phi0 K Z₁ = torusE6Two h2 (.ofAdd ![0, 0, 1, 2]) := by
    rw [hZ₁, phi0_zSL h2 (by decide)]
    exact congrArg (fun y => torusE6Two h2 (Multiplicative.ofAdd y)) (by decide)
  have hφ₂ : phi0 K Z₂ = torusE6Two h2 (.ofAdd ![0, 2, 0, 1]) := by
    rw [hZ₂, tvSLWord_append, tvSLWord_append, map_mul, map_mul]
    change phi0 K (zSL ![0, 0, 1]) * phi0 K (zSL ![1, 0, 0]) * phi0 K (zSL ![1, 0, 0]) = _
    rw [phi0_zSL h2 (by decide), phi0_zSL h2 (by decide), ← map_mul, ← map_mul, ← ofAdd_add,
      ← ofAdd_add]
    exact congrArg (fun y => torusE6Two h2 (Multiplicative.ofAdd y)) (by decide)
  have hg : ∀ x : Fin 4 → ZMod 3, g * torusE6Two h2 (.ofAdd x) * g⁻¹ =
      torusE6Two h2 (.ofAdd (wordAct [0, 2] x)) := genWord_conj_torus h2 [0, 2]
  have hj3 : ∀ j ∈ J, j ^ 3 = 1 := by
    intro j hj
    have hcomm : ∀ x : Fin 4 → ZMod 3,
        (∀ j ∈ J, torusE6Two h2 (.ofAdd x) * j = j * torusE6Two h2 (.ofAdd x)) →
          g * j * g⁻¹ * torusE6Two h2 (.ofAdd (wordAct [0, 2] x)) =
            torusE6Two h2 (.ofAdd (wordAct [0, 2] x)) * (g * j * g⁻¹) := by
      intro x hx
      rw [← hg]
      have hxj := hx j hj
      calc g * j * g⁻¹ * (g * torusE6Two h2 (.ofAdd x) * g⁻¹)
          = g * (j * torusE6Two h2 (.ofAdd x)) * g⁻¹ := by group
        _ = g * (torusE6Two h2 (.ofAdd x) * j) * g⁻¹ := by rw [hxj]
        _ = g * torusE6Two h2 (.ofAdd x) * g⁻¹ * (g * j * g⁻¹) := by group
    have c0 := hcomm _ h₁
    have c1 := hcomm _ h₂
    have c2 := hcomm _ h₃
    rw [show wordAct [0, 2] ![1, 1, 1, 1] = Pi.single 0 1 by decide, torusE6Two_single_zero] at c0
    rw [show wordAct [0, 2] ![1, 2, 0, 0] = ![0, 0, 1, 2] by decide, ← hφ₁] at c1
    rw [show wordAct [0, 2] ![2, 0, 1, 0] = ![0, 2, 0, 1] by decide, ← hφ₂] at c2
    have h3 := pow_three_eq_one_of_commute_phi0_k hK hZ c0 c1 c2
    rw [conj_pow] at h3
    calc j ^ 3 = g⁻¹ * (g * j ^ 3 * g⁻¹) * g := by group
      _ = 1 := by rw [h3]; group
  exact false_of_pow_eighteen hA5 J.subtype (by rw [Subgroup.ker_subtype]; exact bot_le) fun k => by
    have hk := hj3 k k.2
    change (k : adjointGroup .E6 K) ^ 18 = 1
    rw [show (18 : ℕ) = 3 * 6 by norm_num, pow_mul, hk, one_pow]

theorem torusE6Two_add_comm_k (h2 : (2 : K) = 0) {J : Subgroup (adjointGroup .E6 K)}
    {x y : Fin 4 → ZMod 3}
    (hx : ∀ j ∈ J, torusE6Two h2 (.ofAdd x) * j = j * torusE6Two h2 (.ofAdd x))
    (hy : ∀ j ∈ J, torusE6Two h2 (.ofAdd y) * j = j * torusE6Two h2 (.ofAdd y)) :
    ∀ j ∈ J, torusE6Two h2 (.ofAdd (x + y)) * j = j * torusE6Two h2 (.ofAdd (x + y)) := by
  intro j hj
  rw [ofAdd_add, map_mul]
  calc torusE6Two h2 (.ofAdd x) * torusE6Two h2 (.ofAdd y) * j
      = torusE6Two h2 (.ofAdd x) * (torusE6Two h2 (.ofAdd y) * j) := by group
    _ = torusE6Two h2 (.ofAdd x) * (j * torusE6Two h2 (.ofAdd y)) := by rw [hy j hj]
    _ = (torusE6Two h2 (.ofAdd x) * j) * torusE6Two h2 (.ofAdd y) := by group
    _ = (j * torusE6Two h2 (.ofAdd x)) * torusE6Two h2 (.ofAdd y) := by rw [hx j hj]
    _ = j * (torusE6Two h2 (.ofAdd x) * torusE6Two h2 (.ofAdd y)) := by group

theorem torusE6Two_comm_k (h2 : (2 : K) = 0) (x y : Fin 4 → ZMod 3) :
    torusE6Two h2 (.ofAdd x) * torusE6Two h2 (.ofAdd y) =
      torusE6Two h2 (.ofAdd y) * torusE6Two h2 (.ofAdd x) := by
  exact ((Commute.all (Multiplicative.ofAdd x) (Multiplicative.ofAdd y)).map (torusE6Two h2)).eq

theorem sE6Two_comm_torus_k (h2 : (2 : K) = 0) {v : Fin 4 → ZMod 3} (hv : msFun v = v) :
    sE6Two K * torusE6Two h2 (.ofAdd v) = torusE6Two h2 (.ofAdd v) * sE6Two K := by
  have h := torusE6Two_msAut h2 (.ofAdd v)
  rw [msAut_ofAdd, hv] at h
  calc sE6Two K * torusE6Two h2 (.ofAdd v)
      = sE6Two K * torusE6Two h2 (.ofAdd v) * (sE6Two K)⁻¹ * sE6Two K := by group
    _ = torusE6Two h2 (.ofAdd v) * sE6Two K := by rw [h]

theorem tE6Two_comm_torus_k (h2 : (2 : K) = 0) {v : Fin 4 → ZMod 3} (hv : mtFun v = v) :
    tE6Two K * torusE6Two h2 (.ofAdd v) = torusE6Two h2 (.ofAdd v) * tE6Two K := by
  have h := torusE6Two_mtAut h2 (.ofAdd v)
  rw [mtAut_ofAdd, hv] at h
  calc tE6Two K * torusE6Two h2 (.ofAdd v)
      = tE6Two K * torusE6Two h2 (.ofAdd v) * (tE6Two K)⁻¹ * tE6Two K := by group
    _ = torusE6Two h2 (.ofAdd v) * tE6Two K := by rw [h]

theorem false_of_comp_e6Two_d4t2_k (hK : Nat.card K = 2) {J : Subgroup (adjointGroup .E6 K)}
    (hJ : CFSG.Open.IsComponentOf J (Subgroup.centralizer
      ({torusE6Two CharTwo.two_eq_zero (.ofAdd ![0, 1, 2, 0])} : Set (adjointGroup .E6 K))))
    (hA5 : Nonempty ((↥J ⧸ Subgroup.center ↥J) ≃* alternatingGroup (Fin 5))) : False := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hsv : sE6Two K * torusE6Two h2 (.ofAdd ![0, 1, 2, 0]) =
      torusE6Two h2 (.ofAdd ![0, 1, 2, 0]) * sE6Two K := sE6Two_comm_torus_k h2 (by decide)
  have hcs : ∀ x : Fin 4 → ZMod 3, ∀ j ∈ J,
      torusE6Two h2 (.ofAdd (msFun x - x)) * j = j * torusE6Two h2 (.ofAdd (msFun x - x)) := by
    intro x j hj
    rw [← sE6Two_commutator_torus_k h2 x]
    exact commutator_mul_comm_of_mem_psiHom_k hK hJ hA5 (sE6Two_mem_range_psiHom_k h2)
      (torusE6Two_mem_range_psiHom_k h2 x) hsv (torusE6Two_comm_k h2 x _) hj
  have hv : ∀ j ∈ J, torusE6Two h2 (.ofAdd ![0, 1, 2, 0]) * j =
      j * torusE6Two h2 (.ofAdd ![0, 1, 2, 0]) := fun j hj =>
    (Subgroup.mem_centralizer_singleton_iff.1 (hJ.1 hj)).symm
  have hc0 := hcs ![1, 0, 0, 0]
  have hc3 := hcs ![0, 0, 0, 1]
  rw [show msFun ![1, 0, 0, 0] - ![1, 0, 0, 0] = ![1, 1, 1, 2] by decide] at hc0
  rw [show msFun ![0, 0, 0, 1] - ![0, 0, 0, 1] = ![1, 1, 1, 0] by decide] at hc3
  have t₁ := torusE6Two_add_comm_k h2 (torusE6Two_add_comm_k h2
    (torusE6Two_add_comm_k h2 hc0 hc0) hc3) hc3
  have t₂ := torusE6Two_add_comm_k h2 hv hc3
  have t₃ := torusE6Two_add_comm_k h2 (torusE6Two_add_comm_k h2 hv hc3) hc3
  rw [show ![1, 1, 1, 2] + ![1, 1, 1, 2] + ![1, 1, 1, 0] + ![1, 1, 1, 0] =
    (![1, 1, 1, 1] : Fin 4 → ZMod 3) by decide] at t₁
  rw [show ![0, 1, 2, 0] + ![1, 1, 1, 0] = (![1, 2, 0, 0] : Fin 4 → ZMod 3) by decide] at t₂
  rw [show ![0, 1, 2, 0] + ![1, 1, 1, 0] + ![1, 1, 1, 0] = (![2, 0, 1, 0] : Fin 4 → ZMod 3) by
    decide] at t₃
  exact false_of_commute_e6Two_targets_k hK hA5 t₁ t₂ t₃

theorem false_of_comp_e6Two_a2cube_k (hK : Nat.card K = 2) {J : Subgroup (adjointGroup .E6 K)}
    (hJ : CFSG.Open.IsComponentOf J (Subgroup.centralizer
      ({torusE6Two CharTwo.two_eq_zero (.ofAdd ![2, 2, 2, 0])} : Set (adjointGroup .E6 K))))
    (hA5 : Nonempty ((↥J ⧸ Subgroup.center ↥J) ≃* alternatingGroup (Fin 5))) : False := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hsv : sE6Two K * torusE6Two h2 (.ofAdd ![2, 2, 2, 0]) =
      torusE6Two h2 (.ofAdd ![2, 2, 2, 0]) * sE6Two K := sE6Two_comm_torus_k h2 (by decide)
  have htv : tE6Two K * torusE6Two h2 (.ofAdd ![2, 2, 2, 0]) =
      torusE6Two h2 (.ofAdd ![2, 2, 2, 0]) * tE6Two K := tE6Two_comm_torus_k h2 (by decide)
  have hcs : ∀ x : Fin 4 → ZMod 3, ∀ j ∈ J,
      torusE6Two h2 (.ofAdd (msFun x - x)) * j = j * torusE6Two h2 (.ofAdd (msFun x - x)) := by
    intro x j hj
    rw [← sE6Two_commutator_torus_k h2 x]
    exact commutator_mul_comm_of_mem_psiHom_k hK hJ hA5 (sE6Two_mem_range_psiHom_k h2)
      (torusE6Two_mem_range_psiHom_k h2 x) hsv (torusE6Two_comm_k h2 x _) hj
  have hct : ∀ x : Fin 4 → ZMod 3, ∀ j ∈ J,
      torusE6Two h2 (.ofAdd (mtFun x - x)) * j = j * torusE6Two h2 (.ofAdd (mtFun x - x)) := by
    intro x j hj
    rw [← tE6Two_commutator_torus_k h2 x]
    exact commutator_mul_comm_of_mem_psiHom_k hK hJ hA5 (tE6Two_mem_range_psiHom_k h2)
      (torusE6Two_mem_range_psiHom_k h2 x) htv (torusE6Two_comm_k h2 x _) hj
  have hc0 := hcs ![1, 0, 0, 0]
  have hd0 := hct ![1, 0, 0, 0]
  have hd1 := hct ![0, 1, 0, 0]
  rw [show msFun ![1, 0, 0, 0] - ![1, 0, 0, 0] = ![1, 1, 1, 2] by decide] at hc0
  rw [show mtFun ![1, 0, 0, 0] - ![1, 0, 0, 0] = ![2, 1, 0, 0] by decide] at hd0
  rw [show mtFun ![0, 1, 0, 0] - ![0, 1, 0, 0] = ![0, 2, 1, 0] by decide] at hd1
  have t₁ := torusE6Two_add_comm_k h2 (torusE6Two_add_comm_k h2
    (torusE6Two_add_comm_k h2 (torusE6Two_add_comm_k h2 hc0 hc0) hd0) hd1) hd1
  have t₂ := torusE6Two_add_comm_k h2 hd0 hd0
  have t₃ := torusE6Two_add_comm_k h2 hd0 hd1
  rw [show ![1, 1, 1, 2] + ![1, 1, 1, 2] + ![2, 1, 0, 0] + ![0, 2, 1, 0] + ![0, 2, 1, 0] =
    (![1, 1, 1, 1] : Fin 4 → ZMod 3) by decide] at t₁
  rw [show ![2, 1, 0, 0] + ![2, 1, 0, 0] = (![1, 2, 0, 0] : Fin 4 → ZMod 3) by decide] at t₂
  rw [show ![2, 1, 0, 0] + ![0, 2, 1, 0] = (![2, 0, 1, 0] : Fin 4 → ZMod 3) by decide] at t₃
  exact false_of_commute_e6Two_targets_k hK hA5 t₁ t₂ t₃

end E6Rest

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256k

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256k

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.StandardType CFSG.StandardType.TableBExc.E6Three CFSG.StandardType.E6ThreeEnd
  CFSG.StandardType.E6TwoPilot
open CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3E6

section E6Transport

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem uE6Two_zero_mul_three_eq_k (h2 : (2 : K) = 0) :
    uE6Two (K := K) 0 * uE6Two 3 = torusE6Two h2 (.ofAdd ![1, 0, 0, 1]) := by
  have e : (![1, 0, 0, 1] : Fin 4 → ZMod 3) = Pi.single 0 1 + Pi.single 3 1 := by decide
  rw [e, ofAdd_add, map_mul, torusE6Two_single_eq_pow, torusE6Two_single_eq_pow, ZMod.val_one,
    pow_one, pow_one]

theorem uE6Two_zero_mul_two_mul_three_eq_k (h2 : (2 : K) = 0) :
    uE6Two (K := K) 0 * uE6Two 2 * uE6Two 3 = torusE6Two h2 (.ofAdd ![1, 0, 1, 1]) := by
  have e : (![1, 0, 1, 1] : Fin 4 → ZMod 3) = Pi.single 0 1 + Pi.single 2 1 + Pi.single 3 1 := by
    decide
  rw [e, ofAdd_add, ofAdd_add, map_mul, map_mul, torusE6Two_single_eq_pow,
    torusE6Two_single_eq_pow, torusE6Two_single_eq_pow, ZMod.val_one, pow_one, pow_one, pow_one]

theorem map_conj_centralizer_genWord_k (h2 : (2 : K) = 0) (w : List (Fin 6))
    (v : Fin 4 → ZMod 3) :
    (Subgroup.centralizer ({torusE6Two h2 (.ofAdd v)} : Set (adjointGroup .E6 K))).map
      (MulAut.conj (genWord K w) : adjointGroup .E6 K →* adjointGroup .E6 K) =
        Subgroup.centralizer ({torusE6Two h2 (.ofAdd (wordAct w v))} :
          Set (adjointGroup .E6 K)) := by
  rw [← genWord_conj_torus h2 w v]
  exact CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3.map_conj_centralizer _ _

theorem noA5Comp_centralizer_u0u3_E6_two (hK : Nat.card K = 2) {J : Subgroup (adjointGroup .E6 K)}
    (hJ : CFSG.Open.IsComponentOf J
      (Subgroup.centralizer ({uE6Two 0 * uE6Two 3} : Set (adjointGroup .E6 K)))) :
    ¬ Nonempty ((↥J ⧸ Subgroup.center ↥J) ≃* alternatingGroup (Fin 5)) := by
  intro hA5
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hJ' := CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map
    (MulAut.conj (genWord K [3, 0])) hJ
  rw [uE6Two_zero_mul_three_eq_k h2, map_conj_centralizer_genWord_k h2,
    show wordAct [3, 0] ![1, 0, 0, 1] = ![0, 1, 2, 0] by decide] at hJ'
  exact false_of_comp_e6Two_d4t2_k hK hJ' (nonempty_a5_map _ hA5)

theorem noA5Comp_centralizer_u0u2u3_E6_two (hK : Nat.card K = 2)
    {J : Subgroup (adjointGroup .E6 K)}
    (hJ : CFSG.Open.IsComponentOf J
      (Subgroup.centralizer ({uE6Two 0 * uE6Two 2 * uE6Two 3} : Set (adjointGroup .E6 K)))) :
    ¬ Nonempty ((↥J ⧸ Subgroup.center ↥J) ≃* alternatingGroup (Fin 5)) := by
  intro hA5
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hJ' := CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map
    (MulAut.conj (genWord K [3, 0, 0])) hJ
  rw [uE6Two_zero_mul_two_mul_three_eq_k h2, map_conj_centralizer_genWord_k h2,
    show wordAct [3, 0, 0] ![1, 0, 1, 1] = ![2, 2, 2, 0] by decide] at hJ'
  exact false_of_comp_e6Two_a2cube_k hK hJ' (nonempty_a5_map _ hA5)

end E6Transport

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256k

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256k

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup PerfectInLayer)
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3

section Inner

theorem noA5_comp_of_congr_conj {S X : Type*} [Group S] [Group X] (e : S ≃* X)
    (hinj : Function.Injective (MulAut.conj : X →* MulAut X))
    (h : ∀ t₁ : X, t₁ ^ 3 = 1 → ∀ J' : Subgroup X,
      CFSG.Open.IsComponentOf J' (fixSubgroup (MulAut.conj t₁)) →
        ¬ Nonempty ((↥J' ⧸ Subgroup.center ↥J') ≃* alternatingGroup (Fin 5)))
    {β : MulAut S} (hβ : β ^ 3 = 1) {t₁ : X} (ht₁ : MulAut.conj t₁ = MulAut.congr e β)
    {J : Subgroup S} (hJ : CFSG.Open.IsComponentOf J (fixSubgroup β)) :
    ¬ Nonempty ((↥J ⧸ Subgroup.center ↥J) ≃* alternatingGroup (Fin 5)) := by
  intro hA5
  have ht3 : t₁ ^ 3 = 1 := by
    apply hinj
    rw [map_pow, ht₁, ← map_pow, hβ, map_one, map_one]
  have hJ' := CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map e hJ
  rw [← fixSubgroup_congr_k, ← ht₁] at hJ'
  exact h t₁ ht3 _ hJ' (nonempty_a5_map e hA5)

end Inner

section FE78

open CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem exists_conj_eq_reeF4_two {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) (α : MulAut (adjointGroup CFSG.LieType.Ree.ReeTag.F4.tag K))
    (hα : α ^ 3 = 1) : ∃ g, MulAut.conj g = α := by
  have : CharP K 2 := charP_two_of_card_two hK
  have : CharP K CFSG.LieType.Ree.ReeTag.F4.prime := ‹CharP K 2›
  have hK1 : Nat.card K = 2 ^ 1 := by rw [hK]; norm_num
  obtain ⟨-, -, ⟨Θ, -, -, hker⟩, -⟩ :=
    CFSG.LieType.Chevalley.even_F4_exact_automorphism_normal_form (f := 1) le_rfl K hK1
  have h1 : Θ α = 1 := by
    have h3 : Θ α ^ 3 = 1 := by rw [← map_pow, hα, map_one]
    generalize Θ α = z at h3 ⊢
    revert z
    decide
  have h2 : α ∈ Θ.ker := h1
  rw [hker] at h2
  exact h2

theorem exists_conj_eq_F4_two {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) (α : MulAut (adjointGroup Tag.F4 K)) (hα : α ^ 3 = 1) :
    ∃ g : adjointGroup Tag.F4 K, MulAut.conj g = α :=
  exists_conj_eq_reeF4_two hK α hα

end FE78

section FE78On

theorem noA5CompOn_FE78_two :
    Inputs256h.NoA5CompOn fun d => Inputs256c.defField d.1 = 2 ∧
      ∃ q, d.1 = TauCeti.LieTypeIndex.F4 q ∨ d.1 = TauCeti.LieTypeIndex.E7 q ∨
        d.1 = TauCeti.LieTypeIndex.E8 q := by
  intro S _ _ _ _ d hP he β hβ J hJ
  obtain ⟨⟨d, hv⟩, rfl⟩ : ∃ d' : TauCeti.ValidLieTypeIndex, d' = d := ⟨d, rfl⟩
  obtain ⟨h2, q, hq⟩ := hP
  obtain ⟨e⟩ := he
  dsimp only at hq
  rcases hq with rfl | rfl | rfl
  · obtain ⟨K, _, _, hK, -, ⟨eK⟩⟩ := CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup
      CFSG.TauCetiBridge.Even.chevalleyBridgesAll.f4 q hv
    have hK2 : Nat.card K = 2 := hK.trans h2
    let e' : S ≃* adjointGroup Tag.F4 K := e.trans eK
    obtain ⟨t₁, ht₁⟩ := exists_conj_eq_F4_two hK2 (MulAut.congr e' β)
      (by rw [← map_pow, hβ, map_one])
    exact noA5_comp_of_congr_conj e' mulAut_conj_injective_adjointGroup
      (fun _ ht _ hJ' => noA5Comp_inner_F4_two hK2 ht hJ') hβ ht₁ hJ
  · obtain ⟨K, _, _, hK, -, ⟨eK⟩⟩ := CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup
      CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e7 q hv
    have hK2 : Nat.card K = 2 := hK.trans h2
    let e' : S ≃* adjointGroup Tag.E7 K := e.trans eK
    obtain ⟨t₁, ht₁⟩ := mem_innerAut_of_card_two hK2 (Or.inl rfl) (MulAut.congr e' β)
    exact noA5_comp_of_congr_conj e' mulAut_conj_injective_adjointGroup
      (fun _ ht _ hJ' => noA5Comp_inner_E7_two hK2 ht hJ') hβ ht₁ hJ
  · obtain ⟨K, _, _, hK, -, ⟨eK⟩⟩ := CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup
      CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e8 q hv
    have hK2 : Nat.card K = 2 := hK.trans h2
    let e' : S ≃* adjointGroup Tag.E8 K := e.trans eK
    obtain ⟨t₁, ht₁⟩ := mem_innerAut_of_card_two hK2 (Or.inr rfl) (MulAut.congr e' β)
    exact noA5_comp_of_congr_conj e' mulAut_conj_injective_adjointGroup
      (fun _ ht _ hJ' => noA5Comp_inner_E8_two hK2 ht hJ') hβ ht₁ hJ

theorem noA5On_FE78_two :
    Inputs256d.NoA5On fun d => Inputs256c.defField d.1 = 2 ∧
      ∃ q, d.1 = TauCeti.LieTypeIndex.F4 q ∨ d.1 = TauCeti.LieTypeIndex.E7 q ∨
        d.1 = TauCeti.LieTypeIndex.E8 q :=
  Inputs256h.noA5On_of_comp (fun S _ _ hs hna d hd2 hP he β hβ hβ1 =>
      CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.lieSemisimpleCentExceptional S hs hna d
        (by
          obtain ⟨-, q, hq⟩ := hP
          rcases hq with h | h | h <;> rw [h] <;> rfl)
        he 3 Nat.prime_three (by norm_num) (by rw [hd2]; norm_num) β hβ hβ1)
    noA5CompOn_FE78_two

end FE78On

section TwE6

open CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal209TwoOuterInAux
  (exists_ghat conj_ghat_mem_model cocycle_mem_toralRootGroup_of_nonInner exists_model_conj_dV)

@[expose] def NoA5TwE6TwoExotic :
    Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 4 →
    ∀ σ : K ≃+* K, (∀ c, σ c = c ^ 2) →
    ∀ g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K),
      g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K) →
      twistHom TwistTag.E6 (AlgebraicClosure K) (iterateFrobenius (AlgebraicClosure K) 2 1) g0 =
        g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) twE6W0 →
    ∀ m ∈ twE6TwoModel (AlgebraicClosure K),
      m ∉ (⁅twE6TwoModel (AlgebraicClosure K), twE6TwoModel (AlgebraicClosure K)⁆ :
        Subgroup (ModGL Tag.E6 (AlgebraicClosure K))) → m ^ 3 = 1 →
    ∀ y ∈ adjointGroup Tag.E6 (AlgebraicClosure K), ∀ a : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ,
      (∀ i, a i ^ 3 = 1) → rootChar a e6Omega3 = 1 → m = y * rootDiagUnit Tag.E6 a * y⁻¹ →
    ∀ J : Subgroup ↥(⁅twE6TwoModel (AlgebraicClosure K), twE6TwoModel (AlgebraicClosure K)⁆ :
        Subgroup (ModGL Tag.E6 (AlgebraicClosure K))),
      CFSG.Open.IsComponentOf J
        ((Subgroup.centralizer ({m} : Set (ModGL Tag.E6 (AlgebraicClosure K)))).subgroupOf
          (⁅twE6TwoModel (AlgebraicClosure K), twE6TwoModel (AlgebraicClosure K)⁆ :
            Subgroup (ModGL Tag.E6 (AlgebraicClosure K)))) →
      ¬ Nonempty ((↥J ⧸ Subgroup.center ↥J) ≃* alternatingGroup (Fin 5))

theorem not_dvd_orderTwistedE6_two : ¬ 5 ^ 9 ∣ CFSG.Open.orderTwistedE6 2 := by
  unfold CFSG.Open.orderTwistedE6
  norm_num

theorem noA5Comp_twE6_two_of_exotic (hexo : NoA5TwE6TwoExotic) {K : Type} [Field K] [Finite K]
    (hK4 : Nat.card K = 4) (σ : K ≃+* K) (hσ2 : ∀ c, σ c = c ^ 2)
    (h5 : ¬ 5 ^ 9 ∣ Nat.card (twistedE6RootGroup K σ))
    {δ : MulAut (twistedE6RootGroup K σ)} (hδ3 : δ ^ 3 = 1) {J : Subgroup (twistedE6RootGroup K σ)}
    (hJ : CFSG.Open.IsComponentOf J (fixSubgroup δ)) :
    ¬ Nonempty ((↥J ⧸ Subgroup.center ↥J) ≃* alternatingGroup (Fin 5)) := by
  classical
  intro hA5
  have hchar : CharP K 2 := charP_two_of_card_four hK4
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  haveI : Finite (twistedE6RootGroup K σ) := Subtype.finite
  obtain ⟨g0, hg0C, hg0⟩ := exists_twE6Two_lang K
  have hcL : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  set ι := algebraMap K (AlgebraicClosure K) with hι
  set eΓ := twE6TwoEquiv hK4 σ hσ2 hg0C hg0 with heΓ
  haveI : Finite ↥(⁅twE6TwoModel (AlgebraicClosure K), twE6TwoModel (AlgebraicClosure K)⁆ :
      Subgroup (ModGL Tag.E6 (AlgebraicClosure K))) := Finite.of_equiv _ eΓ.toEquiv
  have h5Γ : ¬ 5 ^ 9 ∣ Nat.card ↥(⁅twE6TwoModel (AlgebraicClosure K),
      twE6TwoModel (AlgebraicClosure K)⁆ : Subgroup (ModGL Tag.E6 (AlgebraicClosure K))) := by
    rwa [← Nat.card_congr eΓ.toEquiv]
  obtain ⟨ω₀, hω₀⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3 (by rw [card_units_four hK4])
  set ω : (AlgebraicClosure K)ˣ := Units.map ι.toMonoidHom ω₀ with hωdef
  have hω : orderOf ω = 3 := by
    rw [hωdef, orderOf_injective (Units.map ι.toMonoidHom) (Units.map_injective ι.injective), hω₀]
  by_cases hinn : δ ∈ twistedE6Inn K σ
  ·
    obtain ⟨t₀, rfl⟩ := hinn
    have ht₀ : t₀ ^ 3 = 1 := mulAut_conj_injective_of_center_eq_bot
      (exceptional_fixed_center_trivial TwistTag.E6 K σ) (by rw [map_pow, hδ3, map_one])
    have hs3 : ((eΓ t₀ : ↥(⁅twE6TwoModel (AlgebraicClosure K),
        twE6TwoModel (AlgebraicClosure K)⁆ : Subgroup (ModGL Tag.E6 (AlgebraicClosure K)))) :
          ModGL Tag.E6 (AlgebraicClosure K)) ^ 3 = 1 := by
      have h1 : (eΓ t₀) ^ 3 = 1 := by rw [← map_pow, ht₀, map_one]
      have := congrArg Subtype.val h1
      simpa using this
    obtain ⟨m', hm'M, y, hm'⟩ :=
      twE6TwoFusion_holds K hK4 σ hσ2 g0 hg0C hg0 ω hω _ (eΓ t₀).2 hs3
    have hJ' := CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map eΓ hJ
    rw [← fixSubgroup_congr_k, congr_conj_k, fixSubgroup_conj_eq_subgroupOf] at hJ'
    exact false_of_comp_twE6Two hω h5Γ hm'M hm' hJ' (nonempty_a5_map eΓ hA5)
  ·
    obtain ⟨ĝ, hĝ, hĝC, hĝ3, hĝδ⟩ := exists_ghat hK4 σ hσ2 hδ3 hinn
    set m : ModGL Tag.E6 (AlgebraicClosure K) := g0⁻¹ * baseChangeGL ι ĝ * g0 with hm
    have hmM : m ∈ twE6TwoModel (AlgebraicClosure K) := conj_ghat_mem_model hK4 σ hσ2 hg0C hg0 hĝ
    have hmΓ : m ∉ (⁅twE6TwoModel (AlgebraicClosure K), twE6TwoModel (AlgebraicClosure K)⁆ :
        Subgroup (ModGL Tag.E6 (AlgebraicClosure K))) := by
      intro hmΓ
      obtain ⟨c, hc⟩ := eΓ.surjective ⟨m, hmΓ⟩
      have h1 : ((eΓ c : ↥(⁅twE6TwoModel (AlgebraicClosure K),
          twE6TwoModel (AlgebraicClosure K)⁆ : Subgroup (ModGL Tag.E6 (AlgebraicClosure K)))) :
            ModGL Tag.E6 (AlgebraicClosure K)) = m :=
        congrArg Subtype.val hc
      rw [coe_twE6TwoEquiv] at h1
      have h2 : baseChangeGL ι (c : ModGL TwistTag.E6.tag K) = baseChangeGL ι ĝ := by
        have := congrArg (fun y => g0 * y * g0⁻¹) h1
        simpa [hm, mul_assoc] using this
      exact hĝC (by
        have := baseChangeGL_injective ι h2
        rw [← this]
        exact c.2)
    have hm3 : m ^ 3 = 1 := by
      have h2 := conj_pow (a := g0⁻¹) (b := baseChangeGL ι ĝ) (i := 3)
      have h3 : (g0⁻¹ * baseChangeGL ι ĝ * g0) ^ 3 = g0⁻¹ * baseChangeGL ι ĝ ^ 3 * g0 := by
        simpa using h2
      have h4 : (g0⁻¹ * baseChangeGL ι ĝ * g0) ^ 3 = 1 := by
        rw [h3, ← map_pow, hĝ3, map_one]
        group
      exact h4
    have hmap : (fixSubgroup δ).map (eΓ : twistedE6RootGroup K σ →* ↥(⁅twE6TwoModel
        (AlgebraicClosure K), twE6TwoModel (AlgebraicClosure K)⁆ :
          Subgroup (ModGL Tag.E6 (AlgebraicClosure K)))) =
        (Subgroup.centralizer ({m} : Set (ModGL Tag.E6 (AlgebraicClosure K)))).subgroupOf
          (⁅twE6TwoModel (AlgebraicClosure K), twE6TwoModel (AlgebraicClosure K)⁆ :
            Subgroup (ModGL Tag.E6 (AlgebraicClosure K))) := by
      ext z
      obtain ⟨c, rfl⟩ := eΓ.surjective z
      refine Iff.trans (Subgroup.mem_map_equiv (f := eΓ)) ?_
      rw [MulEquiv.symm_apply_apply]
      exact Inputs295e.mem_fixSubgroup_iff_twE6Two hK4 σ hσ2 hg0C hg0 hĝδ hm c
    have hJm := CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map eΓ hJ
    rw [hmap] at hJm
    obtain ⟨y, hyG, a, ha3, hsy⟩ := exists_conj_toral_E6_three hmM.1 hm3
    by_cases hnon : rootChar a e6Omega3 = 1
    ·
      exact hexo K hK4 σ hσ2 g0 hg0C hg0 m hmM hmΓ hm3 y hyG a ha3 hnon hsy _ hJm
        (nonempty_a5_map eΓ hA5)
    ·
      have hprim : IsPrimitiveRoot (ω : AlgebraicClosure K) 3 :=
        IsPrimitiveRoot.coe_units_iff.2 (IsPrimitiveRoot.iff_orderOf.2 hω)
      have hapow : ∀ i, ∃ n : ℕ, a i = ω ^ n := fun i => by
        obtain ⟨n, -, hn⟩ := hprim.eq_pow_of_pow_eq_one (ξ := (a i : AlgebraicClosure K))
          (by have := congrArg Units.val (ha3 i); simpa using this)
        exact ⟨n, Units.ext (by simpa using hn.symm)⟩
      choose mm hmm using hapow
      have hax : a = torV ω (fun i => (mm i : ZMod 3)) := by
        funext i
        rw [torV, ZMod.val_natCast, hmm i]
        have := pow_mod_orderOf ω (mm i)
        rw [hω] at this
        exact this.symm
      have hcoc := cocycle_mem_toralRootGroup_of_nonInner hmM hyG ha3 hsy hnon
      obtain ⟨m', hm'M, hm'⟩ := exists_model_conj_dV hyG hsy hcoc hax
      exact false_of_comp_twE6Two hω h5Γ hm'M hm' hJm (nonempty_a5_map eΓ hA5)

end TwE6

section E6Two

open CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.StandardType CFSG.StandardType.TableBExc.E6Three CFSG.StandardType.E6ThreeEnd
open CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3E6 (phi0 phi0_injective range_phi0)
open scoped commutatorElement

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem card_sl6_two (hK : Nat.card K = 2) :
    Nat.card (Matrix.SpecialLinearGroup (Fin 6) K) = 20158709760 ∧
      Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 6) K)) = 1 := by
  refine ⟨?_, ?_⟩
  · rw [CFSG.OrderReductions.LinearOrders.card_specialLinear K 6 (by norm_num), hK]
    decide
  · rw [CFSG.OrderReductions.LinearOrders.card_specialLinear_center K 6 (by norm_num), hK]
    rfl

theorem noA5Comp_centralizer_u0_E6_two (hK : Nat.card K = 2) {J : Subgroup (adjointGroup .E6 K)}
    (hJ : CFSG.Open.IsComponentOf J
      (Subgroup.centralizer ({uE6Two 0} : Set (adjointGroup .E6 K)))) :
    ¬ Nonempty ((↥J ⧸ Subgroup.center ↥J) ≃* alternatingGroup (Fin 5)) := by
  intro hA5
  set C := Subgroup.centralizer ({uE6Two (K := K) 0} : Set (adjointGroup .E6 K)) with hC
  have hcomm : ∀ y ∈ Subgroup.zpowers (uE6Two (K := K) 0), ∀ l ∈ leviB0 K, y * l = l * y := by
    rintro _ ⟨k, rfl⟩ l hl
    exact (Commute.zpow_left (uE6Two_zero_comm_of_mem_leviB0 hl) k).eq
  have hcommL : ∀ g ∈ C, ∀ h ∈ C, ⁅g, h⁆ ∈ leviB0 K := by
    intro g hg h hh
    obtain ⟨y₁, hy₁, l₁, hl₁, rfl⟩ := exists_mul_of_mem_centralizer_uE6Two_zero hK hg
    obtain ⟨y₂, hy₂, l₂, hl₂, rfl⟩ := exists_mul_of_mem_centralizer_uE6Two_zero hK hh
    have hm : l₁ * l₂ * l₁⁻¹ * l₂⁻¹ ∈ leviB0 K :=
      mul_mem (mul_mem (mul_mem hl₁ hl₂) (inv_mem hl₁)) (inv_mem hl₂)
    have h12 : y₁ * y₂ = y₂ * y₁ := by
      obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy₁
      obtain ⟨b, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy₂
      exact (Commute.zpow_zpow_self _ a b).eq
    have e : y₁ * l₁ * (y₂ * l₂) * (y₁ * l₁)⁻¹ * (y₂ * l₂)⁻¹ = l₁ * l₂ * l₁⁻¹ * l₂⁻¹ := by
      have c1 := hcomm y₂ hy₂ l₁ hl₁
      have c2 := hcomm y₁⁻¹ (inv_mem hy₁) (l₁ * l₂ * l₁⁻¹) (mul_mem (mul_mem hl₁ hl₂) (inv_mem hl₁))
      have c3 := hcomm y₂⁻¹ (inv_mem hy₂) _ hm
      calc y₁ * l₁ * (y₂ * l₂) * (y₁ * l₁)⁻¹ * (y₂ * l₂)⁻¹
          = y₁ * (l₁ * y₂) * l₂ * l₁⁻¹ * y₁⁻¹ * l₂⁻¹ * y₂⁻¹ := by group
        _ = y₁ * y₂ * ((l₁ * l₂ * l₁⁻¹) * y₁⁻¹) * l₂⁻¹ * y₂⁻¹ := by rw [← c1]; group
        _ = y₁ * y₂ * y₁⁻¹ * ((l₁ * l₂ * l₁⁻¹ * l₂⁻¹) * y₂⁻¹) := by rw [← c2]; group
        _ = (y₁ * y₂ * y₁⁻¹ * y₂⁻¹) * (l₁ * l₂ * l₁⁻¹ * l₂⁻¹) := by rw [← c3]; group
        _ = l₁ * l₂ * l₁⁻¹ * l₂⁻¹ := by rw [h12]; group
    rw [commutatorElement_def, e]
    exact hm
  have hCC : ⁅C, C⁆ ≤ leviB0 K := Subgroup.commutator_le.2 hcommL
  have hJperf : ⁅J, J⁆ = J := Subgroup.isPerfect_iff.1 ⟨hJ.2.2.1⟩
  have hJL : J ≤ leviB0 K := hJperf ▸ (Subgroup.commutator_mono hJ.1 hJ.1).trans hCC
  have hLC : leviB0 K ≤ C := fun j hj =>
    Subgroup.mem_centralizer_singleton_iff.2 (uE6Two_zero_comm_of_mem_leviB0 hj).symm
  have hsub := CFSG.LocalAnalysis.GLTheoremB.isSubnormal_of_le_of_le hJ.2.1 hJL hLC
  have hLq : CFSG.Open.IsQuasisimple (leviB0 K) :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.open_isQuasisimple isQuasisimple_leviB0
  by_cases hJeq : J = leviB0 K
  ·
    subst hJeq
    have eL : Matrix.SpecialLinearGroup (Fin 6) K ≃* leviB0 K :=
      (MonoidHom.ofInjective (phi0_injective hK)).trans (MulEquiv.subgroupCongr range_phi0)
    obtain ⟨hcard, hZ⟩ := card_sl6_two hK
    have hZL : Nat.card (Subgroup.center (leviB0 K)) = 1 := by
      rw [← hZ]
      exact (Nat.card_congr (Subgroup.centerCongr eL).toEquiv).symm
    have h60 := card_eq_sixty_mul_card_center hA5
    rw [hZL, ← Nat.card_congr eL.toEquiv, hcard] at h60
    norm_num at h60
  ·
    have hc := CFSG.LocalAnalysis.GLTheoremA.I142.commute_of_isSubnormal_of_quasisimple hLq hsub
      hJeq
    obtain ⟨a, b, hab⟩ :=
      CFSG.HardMathSupport.Solomon.Coordinator.b3Lie_exists_noncomm_of_isQuasisimple hJ.2.2
    exact hab (Subtype.ext (hc a a.2 b (hJL b.2)))

theorem fixSubgroup_conj_eq_centralizer {G : Type*} [Group G] (t : G) :
    fixSubgroup (MulAut.conj t) = Subgroup.centralizer ({t} : Set G) := by
  ext x
  rw [mem_fixSubgroup, Subgroup.mem_centralizer_singleton_iff, MulAut.conj_apply]
  constructor
  · intro h
    calc x * t = t * x * t⁻¹ * t := by rw [h]
      _ = t * x := by group
  · intro h
    rw [← h]
    group

theorem noA5Comp_E6_two (hK : Nat.card K = 2)
    {t : adjointGroup .E6 K} (ht3 : t ^ 3 = 1) (ht1 : t ≠ 1) {J : Subgroup (adjointGroup .E6 K)}
    (hJ : CFSG.Open.IsComponentOf J (fixSubgroup (MulAut.conj t))) :
    ¬ Nonempty ((↥J ⧸ Subgroup.center ↥J) ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨c, hc⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3E6.exists_conj_eq_rep_E6_two hK t ht3 ht1
  rw [fixSubgroup_conj_eq_centralizer] at hJ
  have hJ' := CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map (MulAut.conj c) hJ
  have hmap : (Subgroup.centralizer ({t} : Set (adjointGroup .E6 K))).map
      (MulAut.conj c : adjointGroup .E6 K →* adjointGroup .E6 K) =
        Subgroup.centralizer ({c * t * c⁻¹} : Set (adjointGroup .E6 K)) := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff] at hw
      rw [Subgroup.mem_centralizer_singleton_iff]
      change c * w * c⁻¹ * (c * t * c⁻¹) = c * t * c⁻¹ * (c * w * c⁻¹)
      calc c * w * c⁻¹ * (c * t * c⁻¹) = c * (w * t) * c⁻¹ := by group
        _ = c * (t * w) * c⁻¹ := by rw [hw]
        _ = c * t * c⁻¹ * (c * w * c⁻¹) := by group
    · intro hz
      refine ⟨c⁻¹ * z * c, ?_, by change c * (c⁻¹ * z * c) * c⁻¹ = z; group⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hz
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      calc c⁻¹ * z * c * t = c⁻¹ * (z * (c * t * c⁻¹)) * c := by group
        _ = c⁻¹ * ((c * t * c⁻¹) * z) * c := by rw [hz]
        _ = t * (c⁻¹ * z * c) := by group
  rw [hmap] at hJ'
  intro hA5
  have hA5' := nonempty_a5_map (MulAut.conj c) hA5
  rcases hc with h | h | h
  · rw [h] at hJ'
    exact noA5Comp_centralizer_u0_E6_two hK hJ' hA5'
  · rw [h] at hJ'
    exact noA5Comp_centralizer_u0u3_E6_two hK hJ' hA5'
  · rw [h] at hJ'
    exact noA5Comp_centralizer_u0u2u3_E6_two hK hJ' hA5'

end E6Two

section Final

open CFSG.HardMathSupport.Solomon.Coordinator.I1420 (lieOrderFormula)
open CFSG.StandardType.TableBExc.E6Three (uE6Two)

theorem noA5CompOn_twE6_two_of_exotic (hexo : NoA5TwE6TwoExotic) :
    Inputs256h.NoA5CompOn fun d => Inputs256c.defField d.1 = 2 ∧
      ∃ q, d.1 = TauCeti.LieTypeIndex.twistedE6 q := by
  intro S _ _ _ _ d hP he β hβ J hJ
  obtain ⟨⟨d, hv⟩, rfl⟩ : ∃ d' : TauCeti.ValidLieTypeIndex, d' = d := ⟨d, rfl⟩
  obtain ⟨h2, q, hq⟩ := hP
  dsimp only at hq
  subst hq
  have hq2 : q.card = 2 := h2
  obtain ⟨hp, hexp⟩ := Inputs295d.p_eq_two_of_card_two hq2
  obtain ⟨K, _, σ, hK, hσ, ⟨eK⟩⟩ := CFSG.LieType.SeitzGeneration.exists_catEquiv_twistedE6 q hv
  have hK4 : Nat.card K = 4 := by rw [hK, hp, hexp]; norm_num
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK4]; norm_num)
  have hσ2 : ∀ c, σ c = c ^ 2 := fun c => by rw [hσ c, hp, hexp, pow_one]
  obtain ⟨e⟩ := he
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  haveI : Finite (twistedE6RootGroup K σ) := Subtype.finite
  have hcard : Nat.card (twistedE6RootGroup K σ) = CFSG.Open.orderTwistedE6 2 := by
    rw [CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds ⟨.twistedE6 q, hv⟩ _
      ⟨eK.symm⟩]
    change CFSG.Open.orderTwistedE6 q.card = _
    rw [hq2]
  set θ : S ≃* twistedE6RootGroup K σ := e.trans eK with hθ
  have hδ3 : MulAut.congr θ β ^ 3 = 1 := by rw [← map_pow, hβ, map_one]
  have hJ' := CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map θ hJ
  rw [← fixSubgroup_congr_k] at hJ'
  intro hA5
  exact noA5Comp_twE6_two_of_exotic hexo hK4 σ hσ2 (by rw [hcard]; exact not_dvd_orderTwistedE6_two)
    hδ3 hJ' (nonempty_a5_map θ hA5)

theorem noA5On_twE6_two_of_exotic (hexo : NoA5TwE6TwoExotic) :
    Inputs256d.NoA5On fun d => Inputs256c.defField d.1 = 2 ∧
      ∃ q, d.1 = TauCeti.LieTypeIndex.twistedE6 q :=
  Inputs256h.noA5On_of_comp (fun S _ _ hs hna d hd2 hP he β hβ hβ1 =>
      CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.lieSemisimpleCentExceptional S hs hna d
        (by
          obtain ⟨-, q, hq⟩ := hP
          rw [hq]
          rfl)
        he 3 Nat.prime_three (by norm_num) (by rw [hd2]; norm_num) β hβ hβ1)
    (noA5CompOn_twE6_two_of_exotic hexo)

theorem noA5CompOn_E6_two :
    Inputs256h.NoA5CompOn fun d => Inputs256c.defField d.1 = 2 ∧
      ∃ q, d.1 = TauCeti.LieTypeIndex.E6 q := by
  intro S _ _ hs hna d hP he β hβ J hJ
  obtain ⟨⟨d, hv⟩, rfl⟩ : ∃ d' : TauCeti.ValidLieTypeIndex, d' = d := ⟨d, rfl⟩
  obtain ⟨h2, q, hq⟩ := hP
  dsimp only at hq
  subst hq
  obtain ⟨e⟩ := he
  haveI := hs
  by_cases hβ1 : β = 1
  · subst hβ1
    have hcard : Nat.card S = lieOrderFormula (TauCeti.LieTypeIndex.E6 q) :=
      CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds ⟨_, hv⟩ S ⟨e⟩
    have hc2 : (TauCeti.LieTypeIndex.E6 q).characteristic = 2 := by
      have hp := (Inputs295d.p_eq_two_of_card_two (q := q) h2).1
      simpa using hp
    exact Inputs256h.noA5_comp_one hna (by
      rw [hcard]
      exact Inputs256h.lieOrderFormula_exc_ne_sixty
        (by simp [CFSG.Yardstones.Md42047359a2a.lieFamily]) hc2) hJ
  obtain ⟨K, _, _, hK, -, ⟨eK⟩⟩ := CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup
    CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e6 q hv
  have hK2 : Nat.card K = 2 := hK.trans h2
  have : CharP K 2 := charP_two_of_card_two hK2
  let e' : S ≃* adjointGroup Tag.E6 K := e.trans eK
  have hβ'3 : MulAut.congr e' β ^ 3 = 1 := by rw [← map_pow, hβ, map_one]
  have hβ'1 : MulAut.congr e' β ≠ 1 := fun h =>
    hβ1 ((MulAut.congr e').injective (h.trans (map_one _).symm))
  have hunits : ∀ u : Kˣ, u = 1 := fun u => by
    have h1 : Nat.card Kˣ = 1 := by rw [Nat.card_units, hK2]
    haveI : Subsingleton Kˣ := (Nat.card_eq_one_iff_unique.1 h1).1
    exact Subsingleton.elim _ _
  rcases CFSG.HardMathSupport.Solomon.Coordinator.LieComp.exists_field_or_inndiag_E
      (Or.inl rfl) Nat.prime_three (by norm_num) _ hβ'3 hβ'1 with
    ⟨σ, -, hσ1, -⟩ | ⟨h, hh, hβh, hh3, hh1⟩
  · exfalso
    apply hσ1
    refine RingEquiv.ext fun c => ?_
    rcases eq_zero_or_eq_one_of_card_two hK2 c with rfl | rfl
    · rw [map_zero]; rfl
    · rw [map_one]; rfl
  · obtain ⟨b, j, hj, rfl⟩ := hh
    have hb : b = 1 := funext fun i => hunits (b i)
    rw [hb, rootDiagUnit_one, one_mul] at hβh hh3 hh1
    set t₁ : adjointGroup Tag.E6 K := ⟨j, hj⟩ with ht₁def
    have ht₁ : MulAut.conj t₁ = MulAut.congr e' β := by
      refine MulEquiv.ext fun c => Subtype.ext ?_
      rw [hβh c]
      rfl
    have ht3 : t₁ ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hh3)
    have ht1 : t₁ ≠ 1 := fun h' => hh1 (congrArg Subtype.val h')
    intro hA5
    have hJ' := CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map e' hJ
    rw [← fixSubgroup_congr_k, ← ht₁] at hJ'
    exact noA5Comp_E6_two hK2 ht3 ht1 hJ' (nonempty_a5_map e' hA5)

theorem noA5On_E6_two :
    Inputs256d.NoA5On fun d => Inputs256c.defField d.1 = 2 ∧
      ∃ q, d.1 = TauCeti.LieTypeIndex.E6 q :=
  Inputs256h.noA5On_of_comp (fun S _ _ hs hna d hd2 hP he β hβ hβ1 =>
      CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.lieSemisimpleCentExceptional S hs hna d
        (by
          obtain ⟨-, q, hq⟩ := hP
          rw [hq]
          rfl)
        he 3 Nat.prime_three (by norm_num) (by rw [hd2]; norm_num) β hβ hβ1)
    noA5CompOn_E6_two

theorem noA5On_FE678_two :
    Inputs256d.NoA5On fun d => Inputs256c.defField d.1 = 2 ∧
      ∃ q, d.1 = TauCeti.LieTypeIndex.F4 q ∨ d.1 = TauCeti.LieTypeIndex.E6 q ∨
        d.1 = TauCeti.LieTypeIndex.E7 q ∨ d.1 = TauCeti.LieTypeIndex.E8 q := by
  refine (noA5On_FE78_two.or noA5On_E6_two).mono ?_
  rintro d ⟨h2, q, hq⟩
  rcases hq with hq | hq | hq | hq
  · exact Or.inl ⟨h2, q, Or.inl hq⟩
  · exact Or.inr ⟨h2, q, hq⟩
  · exact Or.inl ⟨h2, q, Or.inr (Or.inl hq)⟩
  · exact Or.inl ⟨h2, q, Or.inr (Or.inr hq)⟩

end Final

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256k

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256k

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSNotAll24
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs295f
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

section ExoticAux

theorem nonempty_a5_map_of_injective_k {S T : Type*} [Group S] [Group T] (f : S →* T)
    (hf : Function.Injective f) {J : Subgroup S}
    (hA5 : Nonempty ((↥J ⧸ Subgroup.center ↥J) ≃* alternatingGroup (Fin 5))) :
    Nonempty ((↥(J.map f) ⧸ Subgroup.center ↥(J.map f)) ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨e⟩ := hA5
  exact ⟨(QuotientGroup.congr _ _ (J.equivMapOfInjective f hf)
    (Subgroup.map_center_eq _)).symm.trans e⟩

end ExoticAux

section ExoticTypes

theorem card_eq_ordTrialityD4_two_of_equiv_k {G : Type} [Group G] {q : TauCeti.PrimePower}
    (hq2 : q.p = 2) (hq1 : q.exponent = 1) (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid)
    (e : G ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hv⟩).Group) :
    Nat.card G = CFSG.Open.ordTrialityD4 (2 ^ 1) := by
  have hm := CFSG.LieType.SeitzGeneration.chevalleyModel_cat_trialityD4 hv
  rw [hq2, hq1] at hm
  have hcard : Nat.card (CFSG.LieType.SeitzGeneration.Cat ⟨.trialityD4 q, hv⟩) =
      CFSG.Open.ordTrialityD4 (2 ^ 1) := CFSG.Timmesfeld.card_chevalleyExceptionalModel_two hm
  rw [Nat.card_congr e.toEquiv]
  exact hcard

variable {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {h : twistedE6InndiagGL K σ}

theorem not_nonempty_a5_rationalComponent_a2out_k (D : TwE6LineLang K σ 2 h)
    (hdim : twE6MatFixDim K σ h = 24) (hout : twistedE6InndiagConj K σ h ∉ twistedE6Inn K σ)
    (i : KernelComponent (rootCharHom D.a)) :
    ¬ Nonempty ((↥(rationalComponent D.S.ρ D.S.Γ (rootCharHom D.a) i) ⧸
      Subgroup.center ↥(rationalComponent D.S.ρ D.S.Γ (rootCharHom D.a) i)) ≃*
        alternatingGroup (Fin 5)) := by
  rintro ⟨eA⟩
  obtain ⟨hℓ2, he1⟩ := kys_char_two_of_q_two D rfl
  have hmodel := kys_rationalComponent_psu_model D hdim (by norm_num) hout i
  rw [hℓ2, he1, one_mul] at hmodel
  have hcard := CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_three_eight hmodel
  rw [Nat.card_congr eA.toEquiv, card_alternatingGroup_five_k] at hcard
  norm_num at hcard

theorem not_nonempty_a5_rationalComponent_d4_k (D : TwE6LineLang K σ 2 h)
    (hdim : twE6MatFixDim K σ h = 30) (i : KernelComponent (rootCharHom D.a)) :
    ¬ Nonempty ((↥(rationalComponent D.S.ρ D.S.Γ (rootCharHom D.a) i) ⧸
      Subgroup.center ↥(rationalComponent D.S.ρ D.S.Γ (rootCharHom D.a) i)) ≃*
        alternatingGroup (Fin 5)) := by
  classical
  intro hA5
  obtain ⟨eA⟩ := hA5
  obtain ⟨hℓ2, he1⟩ := kys_char_two_of_q_two D rfl
  haveI := kys_finite_rationalComponent D i
  have hall : (kernelRoots (rootCharHom D.a)).ncard = 24 := by
    have := D.hker
    omega
  obtain ⟨hr, hc⟩ := d4t2_class_of_card D.hL3 D.hap hall i
  have hker := d4t2_class_eq_kernel D.hL3 D.hap hall i
  have hρ : ∀ γ ∈ componentRoots (rootCharHom D.a) i,
      D.S.ρ γ ∈ componentRoots (rootCharHom D.a) i := by
    intro γ hγ
    rw [hker] at hγ ⊢
    exact outer_rho_mem_kernelRoots D.S D.hT hγ
  haveI : Fact (ringChar K).Prime := ⟨D.hℓ⟩
  haveI : CharP (AlgebraicClosure K) (ringChar K) := D.hchar
  have h3q : 3 ∣ ringChar K ^ D.e + 1 := by
    rw [hℓ2, he1]
    norm_num
  by_cases hin : twistInner (componentRoots (rootCharHom D.a) i)
      (D.S.ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))
  ·
    obtain ⟨_, w, m0, m1, m2, m3, m4, m5, -, hsum, -, hcl⟩ :=
      CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6UniqAbs.kac_class_data D.hL3 D.hap
    obtain ⟨x, hx, hroots, hncard, -, -⟩ := hcl i
    have hD4 := d4t2in_cmpF_eq_sD4 hsum hx (hncard.symm.trans hc)
    have hfam : componentRoots (rootCharHom D.a) i = rootsOfFam (fun y => w⁻¹ • kacE6.extRoot y)
        (Set.range CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerAbs.lD4) := by
      rw [hroots, hD4, ← CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerAbs.range_lD4]
      exact CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerAbs.image_rootsOf_eq_rootsOfFam
        kacE6 w⁻¹ _
    have hfin : (componentRoots (rootCharHom D.a) i).Finite :=
      (CFSG.Blueprint.Chevalley.finite_setOf_isRoot Tag.E6).subset fun γ hγ => hγ.1.1
    have hs1 : componentOrbitLength D.S.ρ (componentRoots (rootCharHom D.a) i) = 1 :=
      componentOrbitLength_eq_one hfin hρ
    have hinner : twistInner (componentRoots (rootCharHom D.a) i)
        ((D.S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[componentOrbitLength D.S.ρ
          (componentRoots (rootCharHom D.a) i)]) := by
      rw [hs1, Function.iterate_one]
      exact hin
    obtain ⟨hmodel, -⟩ := d4t2in_dModel_center D.S (Or.inr (Or.inl rfl)) D.hT i hinner
      (n := 4) le_rfl (fun y => w⁻¹ • kacE6.extRoot y)
      (fun y => IsRoot.smul (kacE6.isRoot_extRoot y) w⁻¹)
      CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerAbs.lD4 hfam
      (fun c d hcd h1 h2 => by
        show iform (w⁻¹ • kacE6.extRoot
            (CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerAbs.lD4 c))
          (w⁻¹ • kacE6.extRoot
            (CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerAbs.lD4 d)) = 0
        rw [iform_smul, kacE6_extRoot]
        exact CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerAbs.d4_hgram c d hcd h1 h2)
      (fun {F} _ c d h =>
        CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerAbs.d4_frames w⁻¹ c d h)
      D.hℓ D.he D.hSq
    rw [hs1, Nat.mul_one, hℓ2, he1] at hmodel
    have hcard := (CFSG.Timmesfeld.card_statedClassicalModel_two hmodel).2.2.2.1 rfl
    rw [Nat.card_congr eA.toEquiv, card_alternatingGroup_five_k] at hcard
    exact absurd hcard (by decide)
  ·
    have hTp : rootDiagUnit Tag.E6 D.a ^ 3 = 1 := by
      have h1 : rootDiagUnit Tag.E6 (D.a ^ 3) = rootDiagUnit Tag.E6 D.a ^ 3 :=
        (rootDiagUnitHom Tag.E6 (AlgebraicClosure K)).map_pow D.a 3
      have h2 : D.a ^ 3 = 1 := funext fun j => by rw [Pi.pow_apply, D.hap j, Pi.one_apply]
      rw [← h1, h2, CFSG.LieType.Chevalley.rootDiagUnit_one]
    obtain ⟨v, hv, -⟩ := D.S.d4_pinnedT_of_prime Nat.prime_three D.hL3 facts_E6 kacCount_E6_four
      (by decide) (by decide)
      (fun y hy => far_d4_E6 y fun z hz => by
        have h := hy z hz
        rwa [KacData.Adj, extRoot_eq_extRootOf] at h)
      ⟨none, by decide⟩ (lt_of_eq_of_lt kacCount_far_E6 (by decide)) D.hT hTp i hr hc
    obtain ⟨⟨e⟩, -⟩ := d4t2out_rationalComponent_equiv D.S D.hS D.he D.hSq h3q D.hT D.hap i v hv
      hker.symm.le hρ hin
    have hcR := card_eq_ordTrialityD4_two_of_equiv_k hℓ2 he1 _ e
    have h60 := card_eq_sixty_mul_card_center ⟨eA⟩
    rw [hcR] at h60
    have h5 : 5 ∣ CFSG.Open.ordTrialityD4 (2 ^ 1) := by
      rw [h60]
      exact Dvd.dvd.mul_right (by norm_num) _
    exact absurd h5 (by decide)

end ExoticTypes

section Exotic

theorem noA5TwE6TwoExotic_holds : NoA5TwE6TwoExotic := by
  intro K _ _ _ hK σ hσ g0 hg0C hg0 m hmM hmΓ hm3 y hyG a ha3 hinner hmy J hJ hA5
  classical
  set L := AlgebraicClosure K with hL
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  haveI : Finite (twistedE6RootGroup K σ) := Subtype.finite
  obtain ⟨ĝ, hĝ, hĝC, hĝ3, hfout, hm⟩ := kys_exists_inndiag_of_model hK σ hσ hg0C hg0 hmM hmΓ hm3
  set h : twistedE6InndiagGL K σ := ⟨ĝ, hĝ⟩ with hhdef
  have hh1 : h ≠ 1 := fun h1 => hĝC (by
    have h2 : ĝ = 1 := congrArg Subtype.val h1
    rw [h2]
    exact one_mem _)
  have hh3 : h ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hĝ3)
  have hK3 : ringChar K ≠ 3 := by
    rw [ringChar.eq K 2]
    norm_num
  obtain ⟨D⟩ := nonempty_twE6LineLang K σ 2 hK3 hσ (by rw [hK]; norm_num) le_rfl h hh1 hh3
  have hdimA : twE6MatFixDim K σ h = 6 + (kernelRoots (rootCharHom a)).ncard := by
    let g0' : ModGL Tag.E6 L := g0
    refine twE6MatFixDim_eq_of_conj σ h (g0' * y) a ?_
    have hb : baseChangeGL (algebraMap K L) ĝ = g0' * m * g0'⁻¹ := by
      rw [hm]
      change baseChangeGL (algebraMap K L) ĝ =
        g0 * (g0⁻¹ * baseChangeGL (algebraMap K L) ĝ * g0) * g0⁻¹
      group
    change g0' * y * rootDiagUnit Tag.E6 a * (g0' * y)⁻¹ = baseChangeGL (algebraMap K L) ĝ
    rw [hb, hmy]
    group
  have htype := kys_ncard_kernelRoots_of_outer hK σ hσ hg0C hg0 hmM hmΓ hyG ha3 hinner hmy
  set e := twE6TwoEquiv hK σ hσ hg0C hg0 with he
  have hmap : (fixSubgroup (twistedE6InndiagConj K σ h)).map e.toMonoidHom =
      (Subgroup.centralizer ({m} : Set (ModGL Tag.E6 L))).subgroupOf
        (⁅twE6TwoModel L, twE6TwoModel L⁆ : Subgroup (ModGL Tag.E6 L)) := by
    ext z
    obtain ⟨c, rfl⟩ := e.surjective z
    rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
    exact Inputs295e.mem_fixSubgroup_iff_twE6Two hK σ hσ hg0C hg0
      (fun c => twistedE6InndiagConj_apply h c) hm c
  have hmap' : ((Subgroup.centralizer ({m} : Set (ModGL Tag.E6 L))).subgroupOf
      (⁅twE6TwoModel L, twE6TwoModel L⁆ : Subgroup (ModGL Tag.E6 L))).map (e.symm : _ →* _) =
        fixSubgroup (twistedE6InndiagConj K σ h) := by
    rw [← hmap]
    ext z
    constructor
    · rintro ⟨w, ⟨u, hu, rfl⟩, rfl⟩
      simpa using hu
    · intro hz
      exact ⟨e z, ⟨z, hz, rfl⟩, by simp⟩
  have hJ' := CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map e.symm hJ
  rw [hmap', fixSubgroup_eq_fixedPoints] at hJ'
  obtain ⟨i, -, hi⟩ := D.exists_rationalComponent hJ'
  have hA5R : Nonempty ((↥(rationalComponent D.S.ρ D.S.Γ (rootCharHom D.a) i) ⧸
      Subgroup.center ↥(rationalComponent D.S.ρ D.S.Γ (rootCharHom D.a) i)) ≃*
        alternatingGroup (Fin 5)) := by
    rw [← hi]
    exact nonempty_a5_map_of_injective_k D.ι D.hinj (nonempty_a5_map e.symm hA5)
  rcases htype with h18 | h24
  · exact not_nonempty_a5_rationalComponent_a2out_k D (by rw [hdimA, h18]) hfout i hA5R
  · exact not_nonempty_a5_rationalComponent_d4_k D (by rw [hdimA, h24]) i hA5R

end Exotic

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256k

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256k

section Union

theorem noA5On_twE6_two :
    Inputs256d.NoA5On fun d => Inputs256c.defField d.1 = 2 ∧
      ∃ q, d.1 = TauCeti.LieTypeIndex.twistedE6 q :=
  noA5On_twE6_two_of_exotic noA5TwE6TwoExotic_holds

theorem noA5On_exc_two_holds :
    Inputs256d.NoA5On fun d => Inputs256c.defField d.1 = 2 ∧
      ∃ q, d.1 = TauCeti.LieTypeIndex.F4 q ∨ d.1 = TauCeti.LieTypeIndex.E6 q ∨
        d.1 = TauCeti.LieTypeIndex.twistedE6 q ∨ d.1 = TauCeti.LieTypeIndex.E7 q ∨
        d.1 = TauCeti.LieTypeIndex.E8 q := by
  refine (noA5On_FE678_two.or noA5On_twE6_two).mono ?_
  rintro d ⟨h2, q, hq⟩
  rcases hq with hq | hq | hq | hq | hq
  · exact Or.inl ⟨h2, q, Or.inl hq⟩
  · exact Or.inl ⟨h2, q, Or.inr (Or.inl hq)⟩
  · exact Or.inr ⟨h2, q, hq⟩
  · exact Or.inl ⟨h2, q, Or.inr (Or.inr (Or.inl hq))⟩
  · exact Or.inl ⟨h2, q, Or.inr (Or.inr (Or.inr hq))⟩

end Union

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256k

end
