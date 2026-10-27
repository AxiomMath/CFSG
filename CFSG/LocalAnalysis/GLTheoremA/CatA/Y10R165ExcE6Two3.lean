module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE6Two2
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesE6NonsplitTorus
public import CFSG.HardMathSupport.Lang.AnisoE6.PlaneConjGen
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Proving.GoursatCentral
public import CFSG.GroupTheory.SupMulCommutative

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE6Two

open Subgroup
open CFSG.Open
open CFSG.SeitzReduction.E6Pilot
open CFSG.LieType.Chevalley
open CFSG.Blueprint.Chevalley
open CFSG.SeitzReduction
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Arithmetic

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem orderOf_natCard_zmod_eq_two {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p)
    (hpq : p ∣ Nat.card K + 1) :
    orderOf ((Nat.card K : ℕ) : ZMod p) = 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hqne1 : ((Nat.card K : ℕ) : ZMod p) ≠ 1 := by
    intro h
    have hd : p ∣ Nat.card K - 1 := by
      have h0 : ((Nat.card K - 1 : ℕ) : ZMod p) = 0 := by
        rw [Nat.cast_sub (Nat.card_pos (α := K)), h]
        simp
      exact (ZMod.natCast_eq_zero_iff _ _).mp h0
    have h2 : p ∣ 2 := by
      have := Nat.dvd_sub hpq hd
      rwa [show Nat.card K + 1 - (Nat.card K - 1) = 2 by
        have := Nat.card_pos (α := K); omega] at this
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) h2
    omega
  have hsq : ((Nat.card K : ℕ) : ZMod p) ^ 2 = 1 := by
    have h : ((Nat.card K + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hpq
    push_cast at h
    linear_combination (((Nat.card K : ℕ) : ZMod p) - 1) * h
  have hdvd : orderOf ((Nat.card K : ℕ) : ZMod p) ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · exact absurd h (fun h => hqne1 (orderOf_eq_one_iff.mp h))
  · exact h

end Arithmetic

private theorem isElemAbelian_sup_of_le_centralizer {G : Type*} [Group G] {p : ℕ}
    {A B : Subgroup G} (hA : IsElemAbelian p A) (hB : IsElemAbelian p B)
    (hBA : B ≤ Subgroup.centralizer (A : Set G)) (hdisj : Disjoint A B)
    (hpA : Nat.card A = p) (hpB : Nat.card B = p ^ 3) :
    IsElemAbelian p (A ⊔ B : Subgroup G) ∧ Nat.card (A ⊔ B : Subgroup G) = p ^ 4 := by
  have hcommAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := by
    intro a ha b hb
    exact Subgroup.mem_centralizer_iff.1 (hBA hb) a ha
  have hcomm : IsMulCommutative (A ⊔ B : Subgroup G) :=
    CFSG.GroupTheory.isMulCommutative_sup_of_elementwise_commute hcommAB hA.1 hB.1
  have hpow : ∀ y ∈ (A ⊔ B : Subgroup G), y ^ p = 1 := by
    intro y hy
    obtain ⟨a, ha, b, hb, rfl⟩ :=
      CFSG.HardMathSupport.Seitz.TrialityOdd.Proving.mem_sup_eq_mul_of_comm A B hcommAB y hy
    rw [Commute.mul_pow (hcommAB a ha b hb), hA.2 a ha, hB.2 b hb, one_mul]
  refine ⟨⟨hcomm, hpow⟩, ?_⟩
  have hnormal : B ≤ Subgroup.normalizer (A : Set G) :=
    hBA.trans (Subgroup.centralizer_le_normalizer _)
  rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hnormal hdisj,
    hpA, hpB]
  ring

section Model

variable {K : Type} [Field K] [Finite K] [CharP K 2]

@[expose] noncomputable def modelE6Two (x : adjointGroup .E6 K)
    (R₃ : Subgroup (adjointGroup .E6 K)) : Subgroup (adjointGroup .E6 K) :=
  Subgroup.zpowers x ⊔ R₃

theorem modelE6Two_isElemAbelian {p : ℕ} [Fact p.Prime] (hp3 : 3 ≤ p)
    (hpq : p ∣ Nat.card K + 1) {X : Subgroup (adjointGroup .E6 K)}
    (hXJ : X ≤ (EPilot.highRootSL2 .E6 K).subgroupOf (adjointGroup .E6 K))
    (hXcyc : IsCyclic X) (hXcard : Nat.card X = Nat.card K + 1)
    {x : adjointGroup .E6 K} (hxX : x ∈ X) (hx : orderOf x = p)
    {R₃ : Subgroup (adjointGroup .E6 K)} (hR3J : R₃ ≤ a5Levi K)
    (hR3 : IsElemAbelian p R₃) (hR3card : Nat.card R₃ = p ^ 3) :
    IsElemAbelian p (Subgroup.zpowers x ⊔ R₃ : Subgroup (adjointGroup .E6 K)) ∧
      Nat.card (Subgroup.zpowers x ⊔ R₃ : Subgroup (adjointGroup .E6 K)) = p ^ 4 := by
  classical
  obtain ⟨hcent, hdisjXJ, hXC⟩ :=
    centralizer_subgroupOf_nonsplit_E6_of_orderOf (K := K) (p := p) hp3 hpq hXJ hXcyc hXcard
      hxX hx
  have hzpX : Subgroup.zpowers x ≤ X := Subgroup.zpowers_le.mpr hxX
  have hzp : IsElemAbelian p (Subgroup.zpowers x) := by
    refine ⟨Subgroup.zpowers_isMulCommutative x, ?_⟩
    intro y hy
    have hdvd : orderOf y ∣ orderOf x := orderOf_dvd_of_mem_zpowers hy
    rw [hx] at hdvd
    exact orderOf_dvd_iff_pow_eq_one.mp hdvd
  have hKH : R₃ ≤ Subgroup.centralizer (Subgroup.zpowers x : Set (adjointGroup .E6 K)) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hzX : z ∈ X := hzpX hz
    have hmem : z ∈ Subgroup.centralizer (a5Levi K : Set (adjointGroup .E6 K)) := hXC hzX
    rw [Subgroup.mem_centralizer_iff] at hmem
    exact (hmem y (hR3J hy)).symm
  have hdisj : Disjoint (Subgroup.zpowers x) R₃ :=
    (hdisjXJ.mono_left hzpX).mono_right hR3J
  have hpH : Nat.card (Subgroup.zpowers x) = p := by
    rw [Nat.card_zpowers, hx]
  exact isElemAbelian_sup_of_le_centralizer hzp hR3 hKH hdisj hpH hR3card

theorem exists_conj_eq_modelE6Two {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    (hpq : p ∣ Nat.card K + 1) {A A₀ : Subgroup (adjointGroup .E6 K)}
    (hA : IsElemAbelian p A) (hAcard : Nat.card A = p ^ 4)
    (hA₀ : IsElemAbelian p A₀) (hA₀card : Nat.card A₀ = p ^ 4) :
    ∃ g : adjointGroup .E6 K, A.map (MulAut.conj g).toMonoidHom = A₀ := by
  haveI : Finite (adjointGroup .E6 K) := Subtype.finite
  have hp : p.Prime := Fact.out
  have hp3 : 3 < p := by omega
  exact CFSG.HardMathSupport.Lang.AnisoE6.exists_conj_eq_of_sylowTorus
    (CFSG.StandardType.ExcFrames.sylowTorus_adjoint_E6_two K hp hp3
      (orderOf_natCard_zmod_eq_two hp (by omega) hpq)) hA hAcard hA₀ hA₀card

end Model

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE6Two
