module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenElevenOneLieClRankFourSp
import CFSG.RankThree.PartTwo.Sec4.HeringK419OneFieldSp4Engine

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique CFSG.LocalAnalysis.RankThreeUC.S15
open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal)
open CFSG.ComponentClassification.UnbalancedCatalog.EvenLinearSL (mem_semilinearAutGroup_of_odd)

namespace LieClAut

theorem exists_rankFour_psl {X K A : Type} [Group X] [Finite X] [Field K] [Finite K]
    [CommGroup A] [Finite A] {m : ℕ} (hm : 3 ≤ m) (hpow : ∀ c : Kˣ, ∃ u : Kˣ, c = u ^ m)
    (e : X ≃* projectiveSL m K) (hc : center X = ⊥)
    {H : Subgroup (MulAut X)} (hinn : (MulAut.conj : X →* MulAut X).range ≤ H) {α : MulAut X}
    (hαH : α ∈ H) (hα : ∃ k : ℕ, α ^ 3 ^ k = 1)
    (hαn : α ∉ (MulAut.conj : X →* MulAut X).range) (f : A →* SpecialLinearGroup (Fin m) K)
    (hf : Function.Injective ((proj m K).comp f)) (hA3 : ∀ a : A, a ^ 3 = 1)
    (hA : Nat.card A = 27)
    (hfix : ∀ τ : K ≃+* K, τ ^ 3 = 1 → ∀ a, SpecialLinearGroup.map τ.toRingHom (f a) = f a) :
    ∃ F : Subgroup (MulAut X), F ≤ H ∧ IsElemAbelian 3 F ∧ Nat.card F = 81 := by
  classical
  set P := projectiveSL m K
  set Ψ : MulAut X ≃* MulAut P := MulAut.congr e with hΨ
  have hΨconj : ∀ x : X, Ψ (MulAut.conj x) = MulAut.conj (e x) := fun x => by
    ext p
    simp [hΨ]
  have hΨinv : ∀ p : P, Ψ.symm (MulAut.conj p) = MulAut.conj (e.symm p) := fun p => by
    rw [MulEquiv.symm_apply_eq, hΨconj, e.apply_symm_apply]
  have hinnΨ : ∀ β, β ∈ (MulAut.conj : X →* MulAut X).range → Ψ β ∈ inner P := by
    rintro _ ⟨x, rfl⟩
    exact ⟨e x, (hΨconj x).symm⟩
  have hinnΨ' : ∀ γ, γ ∈ inner P → Ψ.symm γ ∈ (MulAut.conj : X →* MulAut X).range := by
    rintro _ ⟨p, rfl⟩
    exact ⟨e.symm p, (hΨinv p).symm⟩
  have hconjA : ∀ B : GL (Fin m) K, conjAut m K B ∈ inner P := fun B => by
    obtain ⟨u, hu⟩ := hpow (GeneralLinearGroup.det B)
    exact CFSG.ComponentClassification.OddSelector.conjAut_mem_inner hu
  have hnot : ∀ τ : K ≃+* K, τ ≠ 1 → fieldAut m K τ ∉ inner P := fun τ hτ h => by
    obtain ⟨Y, hY⟩ := CFSG.ComponentClassification.OddSelector.exists_conjAut_of_mem_inner h
    have h1 : conjAut m K (SpecialLinearGroup.toGL Y) =
        conjAut m K 1 * fieldAut m K τ * dualAut m K ^ 0 := by
      rw [pow_zero, mul_one, map_one, one_mul, hY]
    exact hτ (CFSG.ComponentClassification.OddSelector.eq_of_conjAut_eq_normalForm hm
      (Nat.zero_le 1) h1).1
  obtain ⟨k, hk⟩ := hα
  have hodd : Odd (orderOf (Ψ α)) := by
    rw [MulEquiv.orderOf_eq]
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one hk)
    rw [hj]
    exact Odd.pow (by decide)
  obtain ⟨B, φ, hBφ⟩ := mem_semilinearAutGroup_iff.1
    (mem_semilinearAutGroup_of_odd hm hodd)
  have hφH : Ψ.symm (fieldAut m K φ) ∈ H := by
    have h1 : fieldAut m K φ = (conjAut m K B)⁻¹ * Ψ α := by rw [hBφ]; group
    rw [h1, map_mul, map_inv, Ψ.symm_apply_apply]
    exact H.mul_mem (H.inv_mem (hinn (hinnΨ' _ (hconjA B)))) hαH
  haveI := inner_normal P
  have hφk : φ ^ 3 ^ k = 1 := by
    by_contra hne
    apply hnot _ hne
    have hq : ((fieldAut m K φ : MulAut P) : MulAut P ⧸ inner P) = ((Ψ α : MulAut P) :
        MulAut P ⧸ inner P) := by
      rw [hBφ, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).2 (hconjA B), one_mul]
    rw [map_pow, ← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hq, ← QuotientGroup.mk_pow,
      ← map_pow, hk, map_one, QuotientGroup.mk_one]
  have hφ1 : φ ≠ 1 := by
    rintro rfl
    apply hαn
    have h1 : Ψ α ∈ inner P := by rw [hBφ, map_one, mul_one]; exact hconjA B
    simpa using hinnΨ' _ h1
  obtain ⟨j, hjk, hjo⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one hφk)
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact hφ1 (orderOf_eq_one_iff.1 (by rw [hjo, pow_zero]))
  set τ := φ ^ 3 ^ (j - 1) with hτ
  have hτ3 : τ ^ 3 = 1 := by
    rw [hτ, ← pow_mul, ← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hj0), ← hjo,
      pow_orderOf_eq_one]
  have hτ1 : τ ≠ 1 := by
    intro h
    have h1 := orderOf_dvd_of_pow_eq_one h
    rw [hjo] at h1
    have := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 3)).1 h1
    omega
  set β := Ψ.symm (fieldAut m K τ) with hβ
  have hβH : β ∈ H := by
    rw [hβ, hτ, map_pow, map_pow]
    exact H.pow_mem hφH _
  have hβ3 : β ^ 3 = 1 := by rw [hβ, ← map_pow, ← map_pow, hτ3, map_one, map_one]
  have hβn : β ∉ (MulAut.conj : X →* MulAut X).range := fun h =>
    hnot τ hτ1 (by have := hinnΨ _ h; rwa [hβ, Ψ.apply_symm_apply] at this)
  refine exists_rankFour_of_fixed hc hinn hβH hβ3 hβn
    (e.symm.toMonoidHom.comp ((proj m K).comp f)) (e.symm.injective.comp hf) hA3 hA ?_
  intro a
  simp only [hβ, hΨ, MulAut.congr_symm_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.apply_symm_apply, MulEquiv.trans_apply]
  rw [fieldAut_proj, hfix τ hτ3]

end LieClAut

namespace SpE27

variable {K : Type} [Field K] [CharP K 2]

theorem spE_map (τ : K ≃+* K) (v : Fin 3 → ZMod 3) : (spE v : Matrix _ _ K).map τ = spE v := by
  have h1 := fun x => (map_c τ x).1
  have h2 := fun x => (map_c τ x).2.1
  have h3 := fun x => (map_c τ x).2.2
  simp only [spE, fromBlocks_map, diagonal_map (map_zero τ), h1, h2, h3]

theorem spE_det (v : Fin 3 → ZMod 3) : (spE v : Matrix _ _ K).det = 1 :=
  CFSG.RankThree.PartTwo.Sec4.HeringOF.statedSp_det_eq_one
    (g := ⟨spE v, spE (-v), by rw [spE_mul, add_neg_cancel, spE_zero],
      by rw [spE_mul, neg_add_cancel, spE_zero]⟩)
    (CFSG.Open.StatedAPI.mem_statedSp_iff.2 (spE_mem v))

@[expose] def e6 : Fin 3 ⊕ Fin 3 ≃ Fin 6 := finSumFinEquiv

noncomputable def slE6 : Multiplicative (Fin 3 → ZMod 3) →* SpecialLinearGroup (Fin 6) K where
  toFun v := ⟨(spE v.toAdd).submatrix e6.symm e6.symm, by
    rw [det_submatrix_equiv_self, spE_det]⟩
  map_one' := Subtype.ext (by
    change (spE 0 : Matrix _ _ K).submatrix e6.symm e6.symm = 1
    rw [spE_zero, submatrix_one_equiv])
  map_mul' v w := Subtype.ext (by
    change (spE (v.toAdd + w.toAdd) : Matrix _ _ K).submatrix e6.symm e6.symm =
      (spE v.toAdd).submatrix e6.symm e6.symm * (spE w.toAdd).submatrix e6.symm e6.symm
    rw [submatrix_mul_equiv, spE_mul])

theorem projSlE6_injective : Function.Injective ((proj 6 K).comp (slE6 (K := K))) := by
  refine (injective_iff_map_eq_one _).2 fun v hv => ?_
  obtain ⟨c, -, hc⟩ := mem_scalars.1 (proj_eq_one_iff.1 hv)
  have h0 : ∀ i, (cb (v.toAdd i) : K) = 0 := fun i => by
    have hne : e6 (Sum.inl i) ≠ e6 (Sum.inr i) := fun h => Sum.inl_ne_inr (e6.injective h)
    have h1 : ((slE6 v : SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)
        (e6 (Sum.inl i)) (e6 (Sum.inr i)) = cb (v.toAdd i) := by
      change (spE v.toAdd).submatrix e6.symm e6.symm (e6 (Sum.inl i)) (e6 (Sum.inr i)) = _
      simp [spE]
    rw [← h1, hc]
    simp [scalar_apply, diagonal_apply_ne _ hne]
  exact Multiplicative.toAdd.injective (funext fun i => cb_eq_zero (h0 i))

theorem map_slE6 (τ : K ≃+* K) (v : Multiplicative (Fin 3 → ZMod 3)) :
    SpecialLinearGroup.map τ.toRingHom (slE6 v) = slE6 v := by
  refine Subtype.ext ?_
  change ((spE v.toAdd : Matrix _ _ K).submatrix e6.symm e6.symm).map τ =
    (spE v.toAdd).submatrix e6.symm e6.symm
  rw [← submatrix_map]
  exact congrArg (fun M => M.submatrix e6.symm e6.symm) (spE_map τ v.toAdd)

theorem pow_three_eq_one (a : Multiplicative (Fin 3 → ZMod 3)) : a ^ 3 = 1 := by
  apply Multiplicative.toAdd.injective
  funext i
  simp only [toAdd_pow, toAdd_one, Pi.smul_apply, Pi.zero_apply]
  rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]

theorem card_e27 : Nat.card (Multiplicative (Fin 3 → ZMod 3)) = 27 := by
  simp [Nat.card_eq_fintype_card]

end SpE27

@[expose] def KFactOuterThreeRankFourRestSL : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (d : TauCeti.ValidLieTypeIndex), IsRankTwoPlus d.1 →
    RankThreeList d.1 → (∀ q : TauCeti.PrimePower, d.1 ≠ .B 3 q) →
    (∀ q : TauCeti.PrimePower, d.1 ≠ .A 5 q) → LieClAut.FieldExponentThree d.1 →
    Nonempty (X ≃* (TauCeti.CFSGIndex.lie d).Group) → Subgroup.center X = ⊥ →
    ∀ H : Subgroup (MulAut X),
    (MulAut.conj : X →* MulAut X).range ≤ H →
    (∃ α ∈ H, (∃ k : ℕ, α ^ 3 ^ k = 1) ∧ α ∉ (MulAut.conj : X →* MulAut X).range) →
    ∃ F : Subgroup (MulAut X), F ≤ H ∧ IsElemAbelian 3 F ∧ Nat.card F = 81

theorem kFactOuterThreeRankFourRest_of_sl (h : KFactOuterThreeRankFourRestSL) :
    KFactOuterThreeRankFourRest := by
  classical
  intro X _ _ d hd hl hB h3 he hc H hinn hα
  by_cases hA : ∀ q : TauCeti.PrimePower, d.1 ≠ .A 5 q
  · exact h X d hd hl hB hA h3 he hc H hinn hα
  push Not at hA
  obtain ⟨q, hq⟩ := hA
  obtain ⟨d, hv⟩ := d
  simp only at hq
  subst hq
  obtain ⟨e⟩ := he
  have hp : q.p = 2 := hd.1
  have hodd : Odd q.exponent := hl
  obtain ⟨_, K, _, _, hK, ⟨e'⟩⟩ := CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv e
  rw [hp] at hK
  haveI := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
  have hcop : (Nat.card Kˣ).Coprime 6 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hK]
    have h3 : 2 ^ q.exponent % 3 = 2 := by
      obtain ⟨k, hk⟩ := hodd
      rw [hk, pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
      norm_num
    have h2 : 2 ∣ 2 ^ q.exponent := dvd_pow_self 2 (by obtain ⟨k, hk⟩ := hodd; omega)
    have h1 := Nat.one_le_two_pow (n := q.exponent)
    show Nat.Coprime _ (2 * 3)
    refine Nat.Coprime.mul_right (Nat.coprime_two_right.2 (Nat.odd_iff.2 (by omega)))
      (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 (by omega)))
  have hpow : ∀ c : Kˣ, ∃ u : Kˣ, c = u ^ 6 := fun c =>
    ⟨(powCoprime hcop).symm c, ((powCoprime hcop).apply_symm_apply c).symm.trans
      (powCoprime_apply hcop _)⟩
  let b : projectiveSL 6 K ≃* StatedProj (StatedSL 6 K) :=
    (QuotientGroup.quotientMulEquivOfEq (scalars_eq_center 6 K)).trans
      (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 6 K)
  obtain ⟨α, hαH, hαk, hαn⟩ := hα
  exact LieClAut.exists_rankFour_psl (m := 6) (by norm_num) hpow (e'.trans b.symm) hc hinn hαH
    hαk hαn SpE27.slE6 SpE27.projSlE6_injective SpE27.pow_three_eq_one SpE27.card_e27
    (fun τ _ a => SpE27.map_slE6 τ a)

theorem kFactTenElevenOneLieAutRes_of_rankFourSL
    (hK : KFactOuterThreeRankFourRestSL) (h2 : KFactTenElevenOneLieAutFieldTwo) :
    KFactTenElevenOneLieAutRes :=
  kFactTenElevenOneLieAutRes_of_rankFourRest (kFactOuterThreeRankFourRest_of_sl hK) h2

end CFSG.LocalAnalysis.RankThreeTheoremC
