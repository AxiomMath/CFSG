module

public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonE6Facts
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6CartanRankFour

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped MatrixGroups

section Group

variable {p : ℕ} [Fact p.Prime] {S : Type} [Group S]

@[expose] def orderPHom (x : S) (hx : x ^ p = 1) : Multiplicative (ZMod p) →* S where
  toFun t := x ^ (Multiplicative.toAdd t).val
  map_one' := by simp
  map_mul' s t := by
    simp only [toAdd_mul, ZMod.val_add]
    rw [← pow_eq_pow_mod _ hx, pow_add]

theorem card_multiplicative_zmod : Nat.card (Multiplicative (ZMod p)) = p := by
  rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod p) ≃ ZMod p), Nat.card_zmod]

theorem pow_prime_eq_one_of_multiplicative_zmod (x : Multiplicative (ZMod p)) : x ^ p = 1 := by
  have h := pow_card_eq_one' (G := Multiplicative (ZMod p)) (x := x)
  rwa [card_multiplicative_zmod] at h

end Group

section Sl2

variable {p : ℕ} [Fact p.Prime] {F : Type} [Field F] [CharP F 2] {S : Type} [Group S]

theorem exists_elemAbelian_pow_of_commuting_sl2 {k : ℕ} (c : SL(2, F)) (hcp : c ^ p = 1) (hc1 : c ≠ 1)
    (ψ : Fin k → SL(2, F) →* S) (hψ : ∀ i, Function.Injective (ψ i))
    (hc : ∀ i j, i ≠ j → ∀ A B, Commute (ψ i A) (ψ j B)) :
    ∃ E : Subgroup S, IsElemAbelian p E ∧ Nat.card E = p ^ k ∧
      ∀ N : Subgroup S, (∀ i, ψ i c ∈ N) → E ≤ N := by
  have hp : p.Prime := Fact.out
  have hy : ∀ i, ψ i c ^ p = 1 := fun i => by rw [← map_pow, hcp, map_one]
  have hy1 : ∀ i, ψ i c ≠ 1 := fun i h => hc1 (hψ i (h.trans (map_one (ψ i)).symm))
  have hord : orderOf c = p := orderOf_eq_prime hcp hc1
  let ϕ : ∀ _ : Fin k, Multiplicative (ZMod p) →* S := fun i => orderPHom (ψ i c) (hy i)
  have hϕ : ∀ i s, ϕ i s = ψ i c ^ (Multiplicative.toAdd s).val := fun i s => rfl
  have hϕψ : ∀ i s, ϕ i s = ψ i (c ^ (Multiplicative.toAdd s).val) := fun i s => by
    rw [hϕ, map_pow]
  have hcomm : Pairwise fun i j : Fin k => ∀ (a b : Multiplicative (ZMod p)),
      Commute (ϕ i a) (ϕ j b) := fun i j hij a b => by
    rw [hϕψ, hϕψ]
    exact hc i j hij _ _
  have hϕinj : ∀ i, Function.Injective (ϕ i) := by
    intro i
    rw [injective_iff_map_eq_one]
    intro s hs
    have h : ψ i c ^ (Multiplicative.toAdd s).val = 1 := hs
    have hord' : orderOf (ψ i c) = p := orderOf_eq_prime (hy i) (hy1 i)
    have h3 : p ∣ (Multiplicative.toAdd s).val := by
      have := orderOf_dvd_of_pow_eq_one h
      rwa [hord'] at this
    have hlt := ZMod.val_lt (Multiplicative.toAdd s)
    have h0 : (Multiplicative.toAdd s).val = 0 := Nat.eq_zero_of_dvd_of_lt h3 hlt
    exact Multiplicative.toAdd.injective ((ZMod.val_eq_zero _).1 h0)
  have hcen : ∀ i j, i ≠ j → (ϕ j).range ≤ Subgroup.centralizer ((ψ i).range : Set S) := by
    rintro i j hij _ ⟨b, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨A, rfl⟩
    rw [hϕψ]
    exact (hc i j hij A _).eq
  have hind : iSupIndep fun i => (ϕ i).range := by
    intro i
    rw [disjoint_iff, eq_bot_iff]
    intro g hg
    obtain ⟨hgi, hgj⟩ := Subgroup.mem_inf.1 hg
    obtain ⟨s, rfl⟩ := hgi
    have hgc : ϕ i s ∈ Subgroup.centralizer ((ψ i).range : Set S) :=
      (iSup₂_le fun j hj => hcen i j (Ne.symm hj)) hgj
    have hcn : c ^ (Multiplicative.toAdd s).val ∈ Subgroup.center SL(2, F) := by
      rw [Subgroup.mem_center_iff]
      intro B
      apply hψ i
      rw [map_mul, map_mul, ← hϕψ]
      exact Subgroup.mem_centralizer_iff.1 hgc (ψ i B) ⟨B, rfl⟩
    rw [CFSG.HardMathSupport.Timmesfeld.ComponentBalance.SL2Char2.center_eq_bot, Subgroup.mem_bot] at hcn
    have h3 : p ∣ (Multiplicative.toAdd s).val := by
      have := orderOf_dvd_of_pow_eq_one hcn
      rwa [hord] at this
    obtain ⟨m, hm⟩ := h3
    rw [Subgroup.mem_bot, hϕ, hm, pow_mul, hy i, one_pow]
  set Φ := MonoidHom.noncommPiCoprod ϕ hcomm with hΦdef
  have hΦ : Function.Injective Φ :=
    MonoidHom.injective_noncommPiCoprod_of_iSupIndep ϕ hind hϕinj
  refine ⟨Φ.range, ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩, ?_, ?_⟩
  · obtain ⟨s, hs⟩ := a.2
    obtain ⟨t, ht⟩ := b.2
    change (a : S) * b = b * a
    rw [← hs, ← ht, ← map_mul, ← map_mul, mul_comm]
  · rintro _ ⟨s, rfl⟩
    have hs3 : s ^ p = 1 := funext fun i => pow_prime_eq_one_of_multiplicative_zmod (s i)
    rw [← map_pow, hs3, map_one]
  · rw [← Nat.card_congr (MonoidHom.ofInjective hΦ).toEquiv, Nat.card_pi]
    simp [card_multiplicative_zmod]
  · intro N hN
    rw [hΦdef, MonoidHom.noncommPiCoprod_range]
    refine iSup_le fun i => ?_
    rintro _ ⟨s, rfl⟩
    rw [hϕ]
    exact Subgroup.pow_mem N (hN i) _

end Sl2

section Order5

variable {K : Type} [Field K] [CharP K 2]

@[expose] def c5Mat (w : K) : SL(2, K) :=
  ⟨!![0, 1; 1, w], by
    rw [Matrix.det_fin_two_of]
    have two0 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
    linear_combination (-1 : K) * two0⟩

theorem c5Mat_ne_one (w : K) : c5Mat w ≠ 1 := by
  intro h
  have := congrArg (fun A : SL(2, K) => (A : Matrix (Fin 2) (Fin 2) K) 0 0) h
  simp [c5Mat] at this

theorem c5Mat_pow_five {w : K} (hw : w ^ 2 + w + 1 = 0) : c5Mat w ^ 5 = 1 := by
  have two0 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow]
  simp only [pow_succ, pow_zero, one_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [c5Mat, Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination (w - 1) * hw + w * two0
  · linear_combination (w ^ 2 - w + 3) * hw + (-w - 1) * two0
  · linear_combination (w ^ 2 - w + 3) * hw + (-w - 1) * two0
  · linear_combination (w ^ 3 - w ^ 2 + 4 * w - 3) * hw + (w + 1) * two0

end Order5

section Holds

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ



theorem exists_adjointGroup_equiv_of_label_E6 {Γ : Type} [Group Γ] {J : Subgroup Γ} {lab : GLALabel}
    (hlab : LabelOf J lab) (htag : lab.tag = .E6) (hn : lab.n = 2) (hZ : Subgroup.center ↥J = ⊥) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), Nat.card K = 2 ^ 2 ∧
      Nonempty (↥(adjointGroup Tag.E6 K) ≃* ↥J) := by
  have hM := CFSG.StandardType.Canonical.largeEvenMarking_markedModel hlab
  obtain ⟨-, lab', -, R, _, I, F, θ, -, -, hP, hMM⟩ :=
    CFSG.StandardType.Canonical.largeEvenMarking_exists hM
  have hMM' : CFSG.StandardType.MarkedModel lab R := hP ▸ hMM
  obtain ⟨tag, rank, n⟩ := lab
  simp only at htag hn
  subst htag
  subst hn
  have hC : CFSG.Blueprint.ChevalleyExceptionalModel R .E6 2 2 := by
    unfold CFSG.StandardType.MarkedModel at hMM'
    simp only [CFSG.StandardType.markTag, CFSG.StandardType.markRank, CFSG.StandardType.markChar,
      CFSG.StandardType.markDeg] at hMM'
    rcases hMM' with ⟨h, -⟩ | ⟨-, -, hC⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩
    · exact absurd h (by decide)
    · exact hC
    · exact absurd h (by decide)
    · exact absurd h (by simp)
  obtain ⟨-, K, iF, iFin, hK, ⟨e⟩⟩ := hC
  haveI : CharP K 2 := CFSG.StandardType.charP_two_of_card (m := 2) hK
  let eZ : AdjointQuotient Tag.E6 K ≃* ↥(adjointGroup Tag.E6 K) :=
    (QuotientGroup.quotientMulEquivOfEq (center_adjointGroup_eq_bot (τ := Tag.E6) (K := K))).trans
      QuotientGroup.quotientBot
  let eJ : ↥J ≃* R :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans θ
  exact ⟨K, iF, iFin, inferInstance, hK, ⟨(eZ.symm.trans e.symm).trans eJ.symm⟩⟩

theorem e6FourLocal5_holds : E6FourLocal5 := by
  intro Γ _ _ J lab hlab htag hn hZ
  obtain ⟨K, iF, iFin, iC, hK, ⟨eA⟩⟩ := exists_adjointGroup_equiv_of_label_E6 hlab htag hn hZ
  obtain ⟨ι, U, hι, hc, hU0, hU2, hN⟩ := E6CartanRankFourAux.e6_levi_witness (K := K)
  let ψ : Fin 4 → SL(2, K) →* ↥J := fun i => eA.toMonoidHom.comp (ι i)
  have hψ : ∀ i, Function.Injective (ψ i) := fun i => eA.injective.comp (hι i)
  have hψc : ∀ i j, i ≠ j → ∀ A B, Commute (ψ i A) (ψ j B) := fun i j hij A B => by
    show eA (ι i A) * eA (ι j B) = eA (ι j B) * eA (ι i A)
    rw [← map_mul, ← map_mul, hc i j hij A B]
  obtain ⟨w, -, hw⟩ := TwE6FourRankAux.exists_sq_add_add_one (F := K) (by rw [hK]; norm_num)
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨E, hEel, hEcard, hEN⟩ := exists_elemAbelian_pow_of_commuting_sl2 (p := 5) (c5Mat w)
    (c5Mat_pow_five hw) (c5Mat_ne_one w) ψ hψ hψc
  have hU0' : U.map eA.toMonoidHom ≠ ⊥ := fun h =>
    hU0 ((Subgroup.map_eq_bot_iff_of_injective U (f := eA.toMonoidHom) eA.injective).1 h)
  have hU2' : IsPGroup 2 ↥(U.map eA.toMonoidHom) := hU2.map _
  have hEU : E ≤ Subgroup.normalizer ((U.map eA.toMonoidHom : Subgroup ↥J) : Set ↥J) :=
    hEN _ fun i => Subgroup.le_normalizer_map eA.toMonoidHom
      (Subgroup.mem_map_of_mem _ (hN i (c5Mat w)))
  refine ⟨E.map J.subtype, (U.map eA.toMonoidHom).map J.subtype, Subgroup.map_subtype_le _,
    Subgroup.map_subtype_le _, fun h => hU0' ((Subgroup.map_eq_bot_iff_of_injective _
      (f := J.subtype) J.subtype_injective).1 h), hU2'.map _,
    (Subgroup.map_mono hEU).trans (Subgroup.le_normalizer_map J.subtype),
    CFSG.Open.IsElemAbelian.map hEel J.subtype, ?_⟩
  rw [Subgroup.card_map_of_injective J.subtype_injective, hEcard]

end Holds

end CFSG.LocalAnalysis.GLTheoremA
