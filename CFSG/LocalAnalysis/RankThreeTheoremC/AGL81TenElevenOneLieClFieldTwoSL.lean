module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenElevenOneLieClFieldTwo
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossThreeAbelian
import CFSG.RankThree.PartTwo.Sec4.HeringK419OneFieldSp4Engine
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenElevenOneLieClRankFourSp

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique CFSG.LocalAnalysis.RankThreeUC.S15
open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal)
open CFSG.ComponentClassification.UnbalancedCatalog.EvenLinearSL (mem_semilinearAutGroup_of_odd)

namespace FieldTwoE9

open SpE27

variable {K : Type} [Field K] [CharP K 2]

@[expose] def spE (v : Fin 2 → ZMod 3) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  fromBlocks (diagonal fun i => ca (v i)) (diagonal fun i => cb (v i))
    (diagonal fun i => cb (v i)) (diagonal fun i => cd (v i))

theorem spE_mul (v w : Fin 2 → ZMod 3) : (spE v : Matrix _ _ K) * spE w = spE (v + w) := by
  simp only [spE, fromBlocks_multiply, diagonal_mul_diagonal, diagonal_add, Pi.add_apply,
    ca_add, cb_add, cd_add]
  congr 2
  funext i
  rw [← cb_add', ← cb_add]

theorem spE_zero : (spE 0 : Matrix _ _ K) = 1 := by
  simp +decide [spE, ca, cb, cd, ← fromBlocks_one]

theorem spE_mem (v : Fin 2 → ZMod 3) :
    (spE v : Matrix _ _ K)ᵀ * fromBlocks 0 1 (-1) 0 * spE v = fromBlocks 0 1 (-1) 0 := by
  simp only [spE, fromBlocks_transpose, diagonal_transpose, fromBlocks_multiply,
    diagonal_mul_diagonal, Matrix.zero_mul, Matrix.mul_zero, Matrix.one_mul, Matrix.mul_one,
    Matrix.neg_mul, Matrix.mul_neg, zero_add, add_zero]
  congr 1 <;> ext i j <;> by_cases h : i = j <;>
    simp [diagonal_apply, Matrix.one_apply, h, mul_comm]
  · linear_combination (det_eq (K := K) (v j))
  · linear_combination -(det_eq (K := K) (v j))

theorem spE_det (v : Fin 2 → ZMod 3) : (spE v : Matrix _ _ K).det = 1 :=
  CFSG.RankThree.PartTwo.Sec4.HeringOF.statedSp_det_eq_one
    (g := ⟨spE v, spE (-v), by rw [spE_mul, add_neg_cancel, spE_zero],
      by rw [spE_mul, neg_add_cancel, spE_zero]⟩)
    (CFSG.Open.StatedAPI.mem_statedSp_iff.2 (spE_mem v))

theorem spE_map (τ : K ≃+* K) (v : Fin 2 → ZMod 3) : (spE v : Matrix _ _ K).map τ = spE v := by
  have h1 := fun x => (map_c τ x).1
  have h2 := fun x => (map_c τ x).2.1
  have h3 := fun x => (map_c τ x).2.2
  simp only [spE, fromBlocks_map, diagonal_map (map_zero τ), h1, h2, h3]

@[expose] def eL (r : ℕ) : (Fin 2 ⊕ Fin 2) ⊕ Fin r ≃ Fin (4 + r) :=
  (Equiv.sumCongr finSumFinEquiv (Equiv.refl _)).trans finSumFinEquiv

@[expose] def blk (r : ℕ) (v : Fin 2 → ZMod 3) : Matrix (Fin (4 + r)) (Fin (4 + r)) K :=
  (fromBlocks (spE v) 0 0 1 :
    Matrix ((Fin 2 ⊕ Fin 2) ⊕ Fin r) ((Fin 2 ⊕ Fin 2) ⊕ Fin r) K).submatrix (eL r).symm (eL r).symm

theorem blk_mul (r : ℕ) (v w : Fin 2 → ZMod 3) :
    (blk r v : Matrix _ _ K) * blk r w = blk r (v + w) := by
  simp only [blk, submatrix_mul_equiv, fromBlocks_multiply, spE_mul, Matrix.mul_zero,
    Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one]

theorem blk_zero (r : ℕ) : (blk r 0 : Matrix _ _ K) = 1 := by
  simp only [blk, spE_zero, fromBlocks_one, submatrix_one_equiv]

theorem blk_det (r : ℕ) (v : Fin 2 → ZMod 3) : (blk r v : Matrix _ _ K).det = 1 := by
  rw [blk, det_submatrix_equiv_self, det_fromBlocks_zero₂₁, spE_det, det_one, one_mul]

noncomputable def slE (r : ℕ) : Multiplicative (Fin 2 → ZMod 3) →*
    SpecialLinearGroup (Fin (4 + r)) K where
  toFun v := ⟨blk r v.toAdd, blk_det r _⟩
  map_one' := Subtype.ext (blk_zero r)
  map_mul' v w := Subtype.ext (blk_mul r v.toAdd w.toAdd).symm

theorem projSlE_injective (r : ℕ) :
    Function.Injective ((proj (4 + r) K).comp (slE (K := K) r)) := by
  refine (injective_iff_map_eq_one _).2 fun v hv => ?_
  obtain ⟨c, -, hc⟩ := mem_scalars.1 (proj_eq_one_iff.1 hv)
  have h0 : ∀ i, (cb (v.toAdd i) : K) = 0 := fun i => by
    have hne : eL r (Sum.inl (Sum.inl i)) ≠ eL r (Sum.inl (Sum.inr i)) := fun h =>
      Sum.inl_ne_inr (Sum.inl_injective ((eL r).injective h))
    have h1 : ((slE r v : SpecialLinearGroup (Fin (4 + r)) K) : Matrix _ _ K)
        (eL r (Sum.inl (Sum.inl i))) (eL r (Sum.inl (Sum.inr i))) = cb (v.toAdd i) := by
      change blk r v.toAdd (eL r (Sum.inl (Sum.inl i))) (eL r (Sum.inl (Sum.inr i))) = _
      simp [blk, spE]
    rw [← h1, hc]
    simp [scalar_apply, diagonal_apply_ne _ hne]
  exact Multiplicative.toAdd.injective (funext fun i => cb_eq_zero (h0 i))

theorem map_slE (r : ℕ) (τ : K ≃+* K) (v : Multiplicative (Fin 2 → ZMod 3)) :
    SpecialLinearGroup.map τ.toRingHom (slE r v) = slE r v := by
  refine Subtype.ext ?_
  change (blk r v.toAdd : Matrix _ _ K).map τ = blk r v.toAdd
  rw [blk, ← submatrix_map, fromBlocks_map, spE_map]
  simp

theorem pow_three_eq_one (a : Multiplicative (Fin 2 → ZMod 3)) : a ^ 3 = 1 := by
  apply Multiplicative.toAdd.injective
  funext i
  simp only [toAdd_pow, toAdd_one, Pi.smul_apply, Pi.zero_apply]
  rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]

theorem card_e9 : Nat.card (Multiplicative (Fin 2 → ZMod 3)) = 9 := by
  simp [Nat.card_eq_fintype_card]

end FieldTwoE9

namespace LieClAut

theorem three_le_pRank_psl {X K A : Type} [Group X] [Finite X] [Field K] [Finite K]
    [CommGroup A] [Finite A] {m : ℕ} (hm : 3 ≤ m) (hpow : ∀ c : Kˣ, ∃ u : Kˣ, c = u ^ m)
    (hcyc : IsCyclic (K ≃+* K)) (e : X ≃* projectiveSL m K) (hc : center X = ⊥)
    (hab : ∀ P : Subgroup X, IsPGroup 3 P → ∀ a ∈ P, ∀ b ∈ P, a * b = b * a)
    {H : Subgroup (MulAut X)} (hinn : (MulAut.conj : X →* MulAut X).range ≤ H) {α : MulAut X}
    (hαH : α ∈ H) (hα : ∃ k : ℕ, α ^ 3 ^ k = 1)
    (hαn : α ∉ (MulAut.conj : X →* MulAut X).range) (f : A →* SpecialLinearGroup (Fin m) K)
    (hf : Function.Injective ((proj m K).comp f)) (hA3 : ∀ a : A, a ^ 3 = 1)
    (hA : Nat.card A = 9)
    (hfix : ∀ τ : K ≃+* K, τ ^ 3 = 1 → ∀ a, SpecialLinearGroup.map τ.toRingHom (f a) = f a)
    {E : Subgroup (MulAut X)} (hEH : E ≤ H) (hE : IsElemAbelian 3 E) (hEc : Nat.card E = 9) :
    3 ≤ Open.pRank 3 (H ⊓ centralizer (E : Set (MulAut X))) := by
  classical
  haveI := hcyc
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
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
  haveI := inner_normal P
  have hdecomp : ∀ γ : MulAut X, ∀ k : ℕ, γ ^ 3 ^ k = 1 →
      γ ∉ (MulAut.conj : X →* MulAut X).range →
      ∃ (B : GL (Fin m) K) (φ : K ≃+* K), Ψ γ = conjAut m K B * fieldAut m K φ ∧
        φ ^ 3 ^ k = 1 ∧ φ ≠ 1 := by
    intro γ k hk hγn
    have hodd : Odd (orderOf (Ψ γ)) := by
      rw [MulEquiv.orderOf_eq]
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one hk)
      rw [hj]
      exact Odd.pow (by decide)
    obtain ⟨B, φ, hBφ⟩ := mem_semilinearAutGroup_iff.1 (mem_semilinearAutGroup_of_odd hm hodd)
    refine ⟨B, φ, hBφ, ?_, ?_⟩
    · by_contra hne
      apply hnot _ hne
      have hq : ((fieldAut m K φ : MulAut P) : MulAut P ⧸ inner P) = ((Ψ γ : MulAut P) :
          MulAut P ⧸ inner P) := by
        rw [hBφ, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).2 (hconjA B), one_mul]
      rw [map_pow, ← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hq, ← QuotientGroup.mk_pow,
        ← map_pow, hk, map_one, QuotientGroup.mk_one]
    · rintro rfl
      apply hγn
      have h1 : Ψ γ ∈ inner P := by rw [hBφ, map_one, mul_one]; exact hconjA B
      simpa using hinnΨ' _ h1
  obtain ⟨k, hk⟩ := hα
  obtain ⟨B, φ, hBφ, hφk, hφ1⟩ := hdecomp α k hk hαn
  have hφH : Ψ.symm (fieldAut m K φ) ∈ H := by
    have h1 : fieldAut m K φ = (conjAut m K B)⁻¹ * Ψ α := by rw [hBφ]; group
    rw [h1, map_mul, map_inv, Ψ.symm_apply_apply]
    exact H.mul_mem (H.inv_mem (hinn (hinnΨ' _ (hconjA B)))) hαH
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
  refine three_le_pRank_of_abelian hc hinn hab hβH hβ3 hβn
    (e.symm.toMonoidHom.comp ((proj m K).comp f)) (e.symm.injective.comp hf) hA3 hA ?_
    (D := (MulAut.conj : X →* MulAut X).range) (fun δ hδ _ => hδ) ?_ hEH hE hEc
  · intro a
    simp only [hβ, hΨ, MulAut.congr_symm_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.apply_symm_apply, MulEquiv.trans_apply]
    rw [fieldAut_proj, hfix τ hτ3]
  · intro γ _ hγ3 hγn
    obtain ⟨B', φ', hBφ', hφ'3, hφ'1⟩ := hdecomp γ 1 (by simpa using hγ3) hγn
    rw [pow_one] at hφ'3
    rcases eq_or_eq_inv_of_isCyclic hτ3 hτ1 hφ'3 hφ'1 with rfl | rfl
    · left
      have h1 : Ψ (γ * β⁻¹) = conjAut m K B' := by
        rw [map_mul, map_inv, hβ, Ψ.apply_symm_apply, hBφ']
        group
      have := hinnΨ' _ (hconjA B')
      rwa [← h1, Ψ.symm_apply_apply] at this
    · right
      have h1 : Ψ (γ * β) = conjAut m K B' := by
        rw [map_mul, hβ, Ψ.apply_symm_apply, hBφ', map_inv]
        group
      have := hinnΨ' _ (hconjA B')
      rwa [← h1, Ψ.symm_apply_apply] at this

theorem coprime_twenty_of_odd {n : ℕ} (hn : Odd n) : (2 ^ n - 1).Coprime 20 := by
  obtain ⟨k, rfl⟩ := hn
  have h5 : 2 ^ (2 * k + 1) % 5 = 2 ∨ 2 ^ (2 * k + 1) % 5 = 3 := by
    rcases Nat.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · left
      rw [show 2 * (j + j) + 1 = 4 * j + 1 by ring, pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
      norm_num
    · right
      rw [show 2 * (2 * j + 1) + 1 = 4 * j + 3 by ring, pow_add, pow_mul, Nat.mul_mod,
        Nat.pow_mod]
      norm_num
  have h2 : 2 ∣ 2 ^ (2 * k + 1) := dvd_pow_self 2 (by omega)
  have h1 := Nat.one_le_two_pow (n := 2 * k + 1)
  generalize 2 ^ (2 * k + 1) = N at h5 h2 h1 ⊢
  show Nat.Coprime _ (2 ^ 2 * 5)
  refine Nat.Coprime.mul_right (Nat.Coprime.pow_right _
    (Nat.coprime_two_right.2 (Nat.odd_iff.2 (by omega))))
    (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 (by omega)))

theorem three_le_pRank_sl {X K : Type} [Group X] [Finite X] [Field K] [Finite K] {r n : ℕ}
    (hr : r ≤ 1) (hn : Odd n) (hK : Nat.card K = 2 ^ n)
    (e : X ≃* StatedProj (StatedSL (4 + r) K)) (hc : center X = ⊥)
    {H : Subgroup (MulAut X)} (hinn : (MulAut.conj : X →* MulAut X).range ≤ H) {α : MulAut X}
    (hαH : α ∈ H) (hα : ∃ k : ℕ, α ^ 3 ^ k = 1)
    (hαn : α ∉ (MulAut.conj : X →* MulAut X).range)
    {E : Subgroup (MulAut X)} (hEH : E ≤ H) (hE : IsElemAbelian 3 E) (hEc : Nat.card E = 9) :
    3 ≤ Open.pRank 3 (H ⊓ centralizer (E : Set (MulAut X))) := by
  classical
  haveI := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
  have hcop : (Nat.card Kˣ).Coprime (4 + r) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hK]
    exact (coprime_twenty_of_odd hn).coprime_dvd_right (by interval_cases r <;> norm_num)
  have hpow : ∀ c : Kˣ, ∃ u : Kˣ, c = u ^ (4 + r) := fun c =>
    ⟨(powCoprime hcop).symm c, ((powCoprime hcop).apply_symm_apply c).symm.trans
      (powCoprime_apply hcop _)⟩
  have h2 : Nat.card K % 3 = 2 := by
    obtain ⟨k, rfl⟩ := hn
    rw [hK, pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  have hab := comm_of_sylow_comm e
    (KFactProofs.Stroth.Bal3.I294Cross.sylow_comm_psl (by omega) (by omega) h2)
  let b : projectiveSL (4 + r) K ≃* StatedProj (StatedSL (4 + r) K) :=
    (QuotientGroup.quotientMulEquivOfEq (scalars_eq_center (4 + r) K)).trans
      (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj (4 + r) K)
  exact three_le_pRank_psl (by omega) hpow (card_ringAut_and_isCyclic Nat.prime_two K hK).2
    (e.trans b.symm) hc hab hinn hαH hα hαn (FieldTwoE9.slE r) (FieldTwoE9.projSlE_injective r)
    FieldTwoE9.pow_three_eq_one FieldTwoE9.card_e9 (fun τ _ a => FieldTwoE9.map_slE r τ a)
    hEH hE hEc

theorem three_le_pRank_typeA {X : Type} [Group X] [Finite X] {d : TauCeti.ValidLieTypeIndex}
    (hd : IsRankTwoPlus d.1) (hl : RankTwoList d.1)
    (hA : ∃ q : TauCeti.PrimePower, d.1 = .A 3 q ∨ d.1 = .A 4 q)
    (he : Nonempty (X ≃* (TauCeti.CFSGIndex.lie d).Group)) (hc : center X = ⊥)
    {H : Subgroup (MulAut X)} (hinn : (MulAut.conj : X →* MulAut X).range ≤ H)
    (hα : ∃ α ∈ H, (∃ k : ℕ, α ^ 3 ^ k = 1) ∧ α ∉ (MulAut.conj : X →* MulAut X).range)
    {E : Subgroup (MulAut X)} (hEH : E ≤ H) (hE : IsElemAbelian 3 E) (hEc : Nat.card E = 9) :
    3 ≤ Open.pRank 3 (H ⊓ centralizer (E : Set (MulAut X))) := by
  obtain ⟨α, hαH, hαk, hαn⟩ := hα
  obtain ⟨e⟩ := he
  obtain ⟨d, hv⟩ := d
  obtain ⟨q, hq | hq⟩ := hA <;> simp only at hq <;> subst hq
  · obtain ⟨_, K, _, _, hK, ⟨e'⟩⟩ :=
      CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv e
    rw [show q.p = 2 from hd.1] at hK
    exact three_le_pRank_sl (r := 0) (by norm_num) hl hK e' hc hinn hαH hαk hαn hEH hE hEc
  · obtain ⟨_, K, _, _, hK, ⟨e'⟩⟩ :=
      CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv e
    rw [show q.p = 2 from hd.1] at hK
    exact three_le_pRank_sl (r := 1) le_rfl hl hK e' hc hinn hαH hαk hαn hEH hE hEc

end LieClAut

end CFSG.LocalAnalysis.RankThreeTheoremC
