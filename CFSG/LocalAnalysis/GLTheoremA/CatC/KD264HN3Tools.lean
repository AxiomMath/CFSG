module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.CfgITriangular
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Gen.HN3

open CFSG.Open Equiv

theorem sum_fixed_dvd {G X : Type*} [Group G] [Fintype X] [MulAction G X] (A : Subgroup G)
    [Finite A] {n f : ℕ} (hA : Nat.card A = 3 ^ n)
    (hf : ∀ a ∈ A, a ≠ 1 → Nat.card (MulAction.fixedBy X a) = f) :
    3 ^ n ∣ Fintype.card X + (3 ^ n - 1) * f := by
  classical
  haveI : Fintype A := Fintype.ofFinite A
  have hb := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group (G := ↥A) (X := X)
  have hsum : ∑ a : ↥A, Fintype.card (MulAction.fixedBy X a) =
      Fintype.card X + (Fintype.card A - 1) * f := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : ↥A))]
    have h1 : Fintype.card (MulAction.fixedBy X (1 : ↥A)) = Fintype.card X := by
      rw [Fintype.card_subtype]
      simp [MulAction.mem_fixedBy]
    have h2 : ∀ a ∈ Finset.univ.erase (1 : ↥A), Fintype.card (MulAction.fixedBy X a) = f := by
      intro a ha
      have ha1 : (a : G) ≠ 1 := fun h => (Finset.mem_erase.1 ha).1 (Subtype.ext h)
      rw [← hf a a.2 ha1, ← Nat.card_eq_fintype_card]
      rfl
    rw [h1, Finset.sum_congr rfl h2, Finset.sum_const, Finset.card_erase_of_mem
      (Finset.mem_univ _), Finset.card_univ, smul_eq_mul]
  rw [hsum] at hb
  have hcA : Fintype.card A = 3 ^ n := by rw [← Nat.card_eq_fintype_card]; exact hA
  rw [hcA] at hb
  exact ⟨_, hb.trans (mul_comm _ _)⟩

theorem card_filter_conj {G X : Type*} [Group G] [Fintype X] [MulAction G X] [DecidableEq X]
    (c a : G) :
    (Finset.univ.filter fun x : X => (c * a * c⁻¹) • x = x).card =
      (Finset.univ.filter fun x : X => a • x = x).card := by
  refine Finset.card_bij (fun x _ => c⁻¹ • x) ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    have e : a • (c⁻¹ • x) = c⁻¹ • ((c * a * c⁻¹) • x) := by
      simp only [smul_smul]; congr 1; group
    rw [e, hx]
  · intro x _ y _ h
    exact smul_left_cancel _ h
  · intro y hy
    refine ⟨c • y, ?_, by simp⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    rw [mul_smul, mul_smul, inv_smul_smul, hy]

theorem nat_card_fixedBy {G X : Type*} [Group G] [Fintype X] [MulAction G X] [DecidableEq X]
    (a : G) :
    Nat.card (MulAction.fixedBy X a) = (Finset.univ.filter fun x : X => a • x = x).card := by
  classical
  rw [Nat.card_eq_fintype_card, ← Set.toFinset_card]
  congr 1
  ext x
  simp [MulAction.mem_fixedBy]

theorem isElemAbelian_closure {G : Type*} [Group G] {s : Set G} (h3 : ∀ x ∈ s, x ^ 3 = 1)
    (hc : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x) : IsElemAbelian 3 (Subgroup.closure s) := by
  have hEcomm : ∀ a ∈ Subgroup.closure s, ∀ b ∈ Subgroup.closure s, a * b = b * a := by
    intro a ha b hb
    letI := Subgroup.closureCommGroupOfComm (k := s) fun y hy z hz _ => hc y hy z hz
    exact congrArg Subtype.val (mul_comm (⟨a, ha⟩ : ↥(Subgroup.closure s)) ⟨b, hb⟩)
  have hEexp : ∀ a ∈ Subgroup.closure s, a ^ 3 = 1 := by
    intro a ha
    induction ha using Subgroup.closure_induction with
    | mem y hy => exact h3 y hy
    | one => exact one_pow 3
    | mul a b ha hb iha ihb =>
        rw [(show Commute a b from hEcomm a ha b hb).mul_pow, iha, ihb, one_mul]
    | inv a ha iha => rw [inv_pow, iha, inv_one]
  exact ⟨⟨⟨fun a b => Subtype.ext (hEcomm a a.2 b b.2)⟩⟩, fun a ha => hEexp a ha⟩

theorem card_closure_of_not_mem {M : Type} [Group M] [Finite M] {m : ℕ} {x : Fin m → M}
    (hx3 : ∀ i, x i ^ 3 = 1) (hx1 : ∀ i, x i ≠ 1) (hcomm : ∀ i j, x i * x j = x j * x i)
    (hnot : ∀ j : Fin m, x j ∉ S8.CfgI.Triangular.lowerClosure x j.val) :
    3 ^ m ≤ Nat.card (Subgroup.closure (Set.range x)) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [← S8.CfgI.Triangular.lowerClosure_eq]
  suffices h : ∀ k ≤ m, 3 ^ k ≤ Nat.card (S8.CfgI.Triangular.lowerClosure x k) from h m le_rfl
  intro k
  induction k with
  | zero => intro _; simpa using Nat.one_le_iff_ne_zero.2 Nat.card_pos.ne'
  | succ k ih =>
    intro hk
    have hkm : k < m := hk
    set y := x ⟨k, hkm⟩ with hy
    set H := S8.CfgI.Triangular.lowerClosure x k with hH
    have hyH : y ∉ H := hnot ⟨k, hkm⟩
    have hc : ∀ h ∈ H, y * h = h * y := by
      intro h hh
      have hle : H ≤ Subgroup.centralizer ({y} : Set M) := by
        rw [hH, S8.CfgI.Triangular.lowerClosure, Subgroup.closure_le]
        rintro _ ⟨i, -, rfl⟩
        rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff, hy]
        exact hcomm _ _
      exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hh)).symm
    have hyN : Subgroup.zpowers y ≤ Subgroup.normalizer (H : Set M) := by
      rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
      intro h
      constructor
      · intro hh; rw [hc h hh, mul_inv_cancel_right]; exact hh
      · intro hh
        have e := hc _ hh
        have : y * h * y⁻¹ = h := by
          calc y * h * y⁻¹ = y⁻¹ * (y * (y * h * y⁻¹)) := by group
            _ = y⁻¹ * ((y * h * y⁻¹) * y) := by rw [e]
            _ = h := by group
        exact this ▸ hh
    have hprod := CFSG.GH74.GLS.Th2.HY.card_sup_mul_card_inf_of_le_normalizer hyN
    have hcy : Nat.card (Subgroup.zpowers y) = 3 := by
      rw [Nat.card_zpowers, orderOf_eq_prime (hx3 _) (hx1 _)]
    have hinf : Nat.card ↥(Subgroup.zpowers y ⊓ H) = 1 := by
      have hd : Nat.card ↥(Subgroup.zpowers y ⊓ H) ∣ 3 := by
        rw [← hcy]; exact Subgroup.card_dvd_of_le inf_le_left
      rcases (Nat.dvd_prime Nat.prime_three).1 hd with h1 | h3
      · exact h1
      · exfalso
        have heq : Subgroup.zpowers y ⊓ H = Subgroup.zpowers y :=
          Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h3, hcy])
        have : y ∈ Subgroup.zpowers y ⊓ H := by rw [heq]; exact Subgroup.mem_zpowers y
        exact hyH (Subgroup.mem_inf.1 this).2
    rw [hinf, mul_one, hcy] at hprod
    rw [S8.CfgI.Triangular.lowerClosure_succ x hkm, ← hy, sup_comm, hprod, pow_succ, mul_comm]
    exact Nat.mul_le_mul_left 3 (ih hkm.le)

theorem mem_support_of_commute {α : Type*} [Fintype α] [DecidableEq α] {σ τ : Perm α}
    (h : τ * σ = σ * τ) {i : α} (hi : i ∈ σ.support) : τ i ∈ σ.support := by
  rw [Perm.mem_support] at hi ⊢
  intro e
  apply hi
  have : τ (σ i) = τ i := by
    rw [← Perm.mul_apply, h, Perm.mul_apply, e]
  exact τ.injective this

theorem conj_mem_fixing {α : Type*} {Λ : Set α} {g f : Perm α} (hg : ∀ y ∈ Λ, g⁻¹ y ∈ Λ)
    (hf : f ∈ fixingSubgroup (Perm α) Λ) : g * f * g⁻¹ ∈ fixingSubgroup (Perm α) Λ := by
  rw [mem_fixingSubgroup_iff] at hf ⊢
  intro y hy
  have e := hf (g⁻¹ y) (hg y hy)
  rw [Perm.smul_def] at e ⊢
  rw [Perm.mul_apply, Perm.mul_apply, e]
  exact g.apply_symm_apply y

end CFSG.LocalAnalysis.GLTheoremA.KD264Gen.HN3
