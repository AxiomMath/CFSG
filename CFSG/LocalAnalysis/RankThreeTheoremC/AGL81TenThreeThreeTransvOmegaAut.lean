module

public import CFSG.RankThree.Classical.SteinbergBYOrthogonalGates
import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDBridge

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.TransvW.OmegaMinusEight

open CFSG.Assembly.LowTwoRank CFSG.RankThree.Classical.SteinbergBY
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification (OuterAutomorphisms.inner OuterAutomorphisms.inner_normal
  OuterAutomorphisms.congr_conj)
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter (linearConjugationHom)

theorem subsingleton_ringEquiv_of_card_two {K : Type} [Field K] (hK : Nat.card K = 2) :
    Subsingleton (K ≃+* K) := by
  have h : ∀ x : K, x = 0 ∨ x = 1 := fun x => by
    by_cases hx : x = 0
    · exact Or.inl hx
    · obtain ⟨u, -, huniq⟩ := (Nat.card_eq_two_iff' (0 : K)).1 hK
      exact Or.inr ((huniq x hx).trans (huniq 1 one_ne_zero).symm)
  refine ⟨fun σ τ => RingEquiv.ext fun x => ?_⟩
  rcases h x with rfl | rfl <;> simp

theorem inner_of_gates_odd {K : Type} [Field K] [Finite K] {d : ℕ} (hK : Nat.card K = 2)
    (Q : QuadraticForm K (Fin d → K)) (hG : OrthogonalGates Q 1)
    (htop : projectivePointFamilyAut Q = ⊤) {n : ℕ} (hn : Odd n)
    (α : MulAut (matrixProjectiveDerived Q)) (hα : α ^ n = 1) :
    α ∈ OuterAutomorphisms.inner (matrixProjectiveDerived Q) := by
  obtain ⟨-, ⟨ψ, -, hψker, -⟩, ⟨-, k₂, hk₂⟩, -, -, hEA, -, -, -⟩ := hG
  have hE : α ∈ matrixProjectiveImage Q := by
    rw [← hEA, htop]
    exact Subgroup.mem_top _
  have := subsingleton_ringEquiv_of_card_two hK
  have hD : α ∈ (linearConjugationHom Q).range := by
    have h1 : (⟨α, hE⟩ : matrixProjectiveImage Q) ∈ ψ.ker := by
      rw [MonoidHom.mem_ker]
      exact Subsingleton.elim _ _
    rw [hψker, Subgroup.mem_subgroupOf] at h1
    exact h1
  have hcop2 : Nat.Coprime n 2 := Nat.coprime_two_right.mpr hn
  set H := OuterAutomorphisms.inner (matrixProjectiveDerived Q)
  set D := (linearConjugationHom Q).range
  have : H.Normal := OuterAutomorphisms.inner_normal _
  set y : D := ⟨α, hD⟩ with hydef
  have hy : y ^ n = 1 := Subtype.ext (by simpa [hydef] using hα)
  have h1 : orderOf (y : D ⧸ H.subgroupOf D) ∣ n :=
    orderOf_dvd_of_pow_eq_one (by rw [← QuotientGroup.mk_pow, hy, QuotientGroup.mk_one])
  have h2 : orderOf (y : D ⧸ H.subgroupOf D) ∣ 2 ^ k₂ := by
    rw [← hk₂, Subgroup.relIndex, Subgroup.index_eq_card]
    exact orderOf_dvd_natCard _
  have h3 : orderOf (y : D ⧸ H.subgroupOf D) = 1 :=
    Nat.Coprime.eq_one_of_dvd ((Nat.Coprime.pow_right k₂ hcop2).coprime_dvd_left h1) h2
  rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h3
  exact h3

theorem exists_conj_of_odd_orderOf {G : Type} [Group G] {m : ℕ}
    (hM : StatedClassicalModel G .POmegaMinus m 2 1) (β : MulAut G) (hβ : Odd (orderOf β)) :
    ∃ y : G, β = MulAut.conj y := by
  obtain ⟨-, -, hm⟩ := hM.1
  obtain ⟨K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := hM.2
  have hn1 : 1 ≤ m := by omega
  have hK2 : Nat.card K = 2 := by simpa using hK
  have hgates := orthogonal_large_prime_semilinear_field_and_diagonal_gates G .POmegaMinus
    (Or.inr (Or.inr rfl)) m 2 1 hM hn1 K hK b c hirr e
  have htop : projectivePointFamilyAut (coordinateQuadMinus m K hn1 b c) = ⊤ :=
    ((OrthogonalTail.orthogonal_geometry_tail_model_point_family_invariant G .POmegaMinus
      (.inr rfl) m 2 1 hM) hn1 K hK b c hirr).2
  set φ := coordinateMinusWitnessEquiv K hn1 b c e
  have hα : (MulAut.congr φ β) ^ orderOf β = 1 := by
    rw [← map_pow, pow_orderOf_eq_one, map_one]
  obtain ⟨t, ht⟩ := inner_of_gates_odd hK2 _ hgates htop hβ _ hα
  refine ⟨φ.symm t, ?_⟩
  apply (MulAut.congr φ).injective
  rw [OuterAutomorphisms.congr_conj, φ.apply_symm_apply]
  exact ht.symm

theorem primePower_eq_two {q : TauCeti.PrimePower} (hq : q.card = 2) :
    q.p = 2 ∧ q.exponent = 1 := by
  have hpe : q.p ^ q.exponent = 2 := (TauCeti.PrimePower.card_def q).symm.trans hq
  have hdvd : q.p ∣ 2 := hpe ▸ dvd_pow_self q.p q.exponent_pos.ne'
  have hqp : q.p = 2 := (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).mp hdvd
  refine ⟨hqp, ?_⟩
  rw [hqp] at hpe
  exact Nat.pow_right_injective le_rfl (by simpa using hpe)

theorem statedClassicalModel_omegaMinusEight {G : Type} [Group G] (d : TauCeti.ValidLieTypeIndex)
    (hd : ∃ q : TauCeti.PrimePower, q.card = 2 ∧ d.1 = .twistedD 4 q)
    (e : G ≃* (TauCeti.CFSGIndex.lie d).Group) : StatedClassicalModel G .POmegaMinus 4 2 1 := by
  obtain ⟨q, hq2, hdq⟩ := hd
  obtain ⟨x, hv⟩ := d
  obtain rfl : x = TauCeti.LieTypeIndex.twistedD 4 q := hdq
  obtain ⟨hqp, hqe⟩ := primePower_eq_two hq2
  have hm := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD_even 4 q hv hqp e
  rwa [hqp, hqe] at hm

theorem exists_conj_of_odd_orderOf_omegaMinusEight {G : Type} [Group G]
    (d : TauCeti.ValidLieTypeIndex)
    (hd : ∃ q : TauCeti.PrimePower, q.card = 2 ∧ d.1 = .twistedD 4 q)
    (e : G ≃* (TauCeti.CFSGIndex.lie d).Group) (β : MulAut G) (hβ : Odd (orderOf β)) :
    ∃ y : G, β = MulAut.conj y :=
  exists_conj_of_odd_orderOf (statedClassicalModel_omegaMinusEight d hd e) β hβ

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.TransvW.OmegaMinusEight
