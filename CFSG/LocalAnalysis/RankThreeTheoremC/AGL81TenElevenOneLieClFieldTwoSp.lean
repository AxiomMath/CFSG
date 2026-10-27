module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenElevenOneLieClFieldTwoSL
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossThreeAbelian

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique CFSG.LocalAnalysis.RankThreeUC.S15
open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial

namespace FieldTwoE9

variable {K : Type} [Field K] [CharP K 2]

noncomputable def spEHom2 : Multiplicative (Fin 2 → ZMod 3) →* StatedSp 2 K where
  toFun v := ⟨⟨FieldTwoE9.spE v.toAdd, FieldTwoE9.spE (-v.toAdd),
    by rw [FieldTwoE9.spE_mul, add_neg_cancel, FieldTwoE9.spE_zero],
    by rw [FieldTwoE9.spE_mul, neg_add_cancel, FieldTwoE9.spE_zero]⟩,
    CFSG.Open.StatedAPI.mem_statedSp_iff.2 (FieldTwoE9.spE_mem _)⟩
  map_one' := Subtype.ext (Units.ext FieldTwoE9.spE_zero)
  map_mul' v w := Subtype.ext (Units.ext (FieldTwoE9.spE_mul v.toAdd w.toAdd).symm)

theorem projE2_injective :
    Function.Injective ((SymplecticFlag.proj 2 K).comp (spEHom2 (K := K))) := by
  refine (injective_iff_map_eq_one _).2 fun v hv => ?_
  have hk : spEHom2 v ∈ (SymplecticFlag.proj 2 K).ker := hv
  rw [SymplecticHigher.ker_proj, Subgroup.mem_subgroupOf, StatedScalars] at hk
  obtain ⟨c, hc⟩ := hk
  have h0 : ∀ i, (SpE27.cb (v.toAdd i) : K) = 0 := fun i => by
    have := congrArg (fun g : GL (Fin 2 ⊕ Fin 2) K =>
      (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) (Sum.inl i) (Sum.inr i)) hc
    simpa [spEHom2, FieldTwoE9.spE, Matrix.GeneralLinearGroup.scalar] using this.symm
  exact Multiplicative.toAdd.injective (funext fun i => SpE27.cb_eq_zero (h0 i))

theorem fieldSp_spEHom2 (τ : K ≃+* K) (v : Multiplicative (Fin 2 → ZMod 3)) :
    SymplecticHigher.fieldSp 2 K τ (spEHom2 v) = spEHom2 v := by
  refine Subtype.ext (Units.ext ?_)
  rw [SymplecticHigher.coe_fieldSp]
  exact FieldTwoE9.spE_map τ v.toAdd

end FieldTwoE9

namespace LieClAut

open SymplecticFlag SymplecticHigher
open CFSG.ComponentClassification.UnbalancedCatalog SpChain
open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal)

theorem three_le_pRank_sp4 {X K : Type} [Group X] [Finite X] [Field K] [Finite K] [CharP K 2]
    (hcyc : IsCyclic (K ≃+* K)) (e : X ≃* StatedProj (StatedSp 2 K)) (hc : center X = ⊥)
    (hab : ∀ P : Subgroup X, IsPGroup 3 P → ∀ a ∈ P, ∀ b ∈ P, a * b = b * a)
    {H : Subgroup (MulAut X)} (hinn : (MulAut.conj : X →* MulAut X).range ≤ H) {α : MulAut X}
    (hαH : α ∈ H) (hα : ∃ k : ℕ, α ^ 3 ^ k = 1)
    (hαn : α ∉ (MulAut.conj : X →* MulAut X).range)
    {E : Subgroup (MulAut X)} (hEH : E ≤ H) (hE : IsElemAbelian 3 E) (hEc : Nat.card E = 9) :
    3 ≤ Open.pRank 3 (H ⊓ centralizer (E : Set (MulAut X))) := by
  classical
  haveI := hcyc
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set P := StatedProj (StatedSp 2 K)
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
  have hnot : ∀ τ : K ≃+* K, τ ≠ 1 → fieldAut 2 K τ ∉ inner P := fun τ hτ => by
    have := (spInner_mul_fieldAut_not_mem_inner_iff (1 : StatedSp 2 K) τ).2 hτ
    rwa [map_one, one_mul] at this
  haveI := inner_normal P
  obtain ⟨-, -, hN, hidx⟩ :=
    CFSG.ComponentClassification.CatalogueBSymplecticTwo.kernel_generation (K := K)
  have hodd : ∀ γ : MulAut P, ∀ k : ℕ, γ ^ 3 ^ k = 1 → γ ∈ spSemilinearAutGroup 2 K := by
    intro γ k hk
    have h2 : γ ^ 2 ∈ spSemilinearAutGroup 2 K := by
      have h := Subgroup.pow_index_mem (spSemilinearAutGroup 2 K) γ
      have h0 : (spSemilinearAutGroup 2 K).index ≠ 0 := Subgroup.index_ne_zero_of_finite
      rcases (by omega : (spSemilinearAutGroup 2 K).index = 1 ∨
          (spSemilinearAutGroup 2 K).index = 2) with hi | hi
      · rw [hi, pow_one] at h
        exact Subgroup.pow_mem _ h 2
      · rwa [hi] at h
    obtain ⟨m, hm⟩ : Odd (3 ^ k) := Odd.pow (by decide)
    have hγ : γ = (γ ^ 2) ^ (m + 1) := by
      rw [← pow_mul, show 2 * (m + 1) = 3 ^ k + 1 by omega, pow_succ, hk, one_mul]
    rw [hγ]
    exact Subgroup.pow_mem _ h2 _
  have hdecomp : ∀ γ : MulAut X, ∀ k : ℕ, γ ^ 3 ^ k = 1 →
      γ ∉ (MulAut.conj : X →* MulAut X).range →
      ∃ (g : StatedSp 2 K) (φ : K ≃+* K), Ψ γ = spInner 2 K g * fieldAut 2 K φ ∧
        φ ^ 3 ^ k = 1 ∧ φ ≠ 1 := by
    intro γ k hk hγn
    obtain ⟨g, φ, hgφ⟩ :=
      exists_eq_spInner_mul_fieldAut (hodd (Ψ γ) k (by rw [← map_pow, hk, map_one]))
    refine ⟨g, φ, hgφ, ?_, ?_⟩
    · by_contra hne
      apply hnot _ hne
      have hq : ((fieldAut 2 K φ : MulAut P) : MulAut P ⧸ inner P) = ((Ψ γ : MulAut P) :
          MulAut P ⧸ inner P) := by
        rw [hgφ, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).2 (spInner_mem_inner g),
          one_mul]
      rw [map_pow, ← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hq, ← QuotientGroup.mk_pow,
        ← map_pow, hk, map_one, QuotientGroup.mk_one]
    · rintro rfl
      apply hγn
      have h1 : Ψ γ ∈ inner P := by rw [hgφ, map_one, mul_one]; exact spInner_mem_inner g
      simpa using hinnΨ' _ h1
  obtain ⟨k, hk⟩ := hα
  obtain ⟨g, φ, hgφ, hφk, hφ1⟩ := hdecomp α k hk hαn
  have hφH : Ψ.symm (fieldAut 2 K φ) ∈ H := by
    have h1 : fieldAut 2 K φ = (spInner 2 K g)⁻¹ * Ψ α := by rw [hgφ]; group
    rw [h1, map_mul, map_inv, Ψ.symm_apply_apply]
    exact H.mul_mem (H.inv_mem (hinn (hinnΨ' _ (spInner_mem_inner g)))) hαH
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
  set β := Ψ.symm (fieldAut 2 K τ) with hβ
  have hβH : β ∈ H := by
    rw [hβ, hτ, map_pow, map_pow]
    exact H.pow_mem hφH _
  have hβ3 : β ^ 3 = 1 := by rw [hβ, ← map_pow, ← map_pow, hτ3, map_one, map_one]
  have hβn : β ∉ (MulAut.conj : X →* MulAut X).range := fun h =>
    hnot τ hτ1 (by have := hinnΨ _ h; rwa [hβ, Ψ.apply_symm_apply] at this)
  refine three_le_pRank_of_abelian hc hinn hab hβH hβ3 hβn
    (e.symm.toMonoidHom.comp ((proj 2 K).comp FieldTwoE9.spEHom2))
    (e.symm.injective.comp FieldTwoE9.projE2_injective) FieldTwoE9.pow_three_eq_one
    FieldTwoE9.card_e9 ?_ (D := (MulAut.conj : X →* MulAut X).range) (fun δ hδ _ => hδ) ?_
    hEH hE hEc
  · intro a
    simp only [hβ, hΨ, MulAut.congr_symm_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.apply_symm_apply, MulEquiv.trans_apply]
    rw [fieldAut_proj, FieldTwoE9.fieldSp_spEHom2]
  · intro γ _ hγ3 hγn
    obtain ⟨g', φ', hgφ', hφ'3, hφ'1⟩ := hdecomp γ 1 (by simpa using hγ3) hγn
    rw [pow_one] at hφ'3
    rcases eq_or_eq_inv_of_isCyclic hτ3 hτ1 hφ'3 hφ'1 with rfl | rfl
    · left
      have h1 : Ψ (γ * β⁻¹) = spInner 2 K g' := by
        rw [map_mul, map_inv, hβ, Ψ.apply_symm_apply, hgφ']
        group
      have := hinnΨ' _ (spInner_mem_inner g')
      rwa [← h1, Ψ.symm_apply_apply] at this
    · right
      have h1 : Ψ (γ * β) = spInner 2 K g' := by
        rw [map_mul, hβ, Ψ.apply_symm_apply, hgφ', map_inv]
        group
      have := hinnΨ' _ (spInner_mem_inner g')
      rwa [← h1, Ψ.symm_apply_apply] at this

theorem three_le_pRank_typeB2 {X : Type} [Group X] [Finite X] {d : TauCeti.ValidLieTypeIndex}
    (hd : IsRankTwoPlus d.1) (hB : ∃ q : TauCeti.PrimePower, d.1 = .B 2 q)
    (he : Nonempty (X ≃* (TauCeti.CFSGIndex.lie d).Group)) (hc : center X = ⊥)
    {H : Subgroup (MulAut X)} (hinn : (MulAut.conj : X →* MulAut X).range ≤ H)
    (hα : ∃ α ∈ H, (∃ k : ℕ, α ^ 3 ^ k = 1) ∧ α ∉ (MulAut.conj : X →* MulAut X).range)
    {E : Subgroup (MulAut X)} (hEH : E ≤ H) (hE : IsElemAbelian 3 E) (hEc : Nat.card E = 9) :
    3 ≤ Open.pRank 3 (H ⊓ centralizer (E : Set (MulAut X))) := by
  obtain ⟨α, hαH, hαk, hαn⟩ := hα
  obtain ⟨e⟩ := he
  obtain ⟨d, hv⟩ := d
  obtain ⟨q, hq⟩ := hB
  simp only at hq
  subst hq
  have hp : q.p = 2 := hd.1
  obtain ⟨_, K, _, _, hK, ⟨e'⟩⟩ := CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e
  rw [hp] at hK
  haveI := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
  have h3 : ¬ 3 ∣ Nat.card K := by
    rw [hK]
    exact KFactProofs.Stroth.Bal3.I294Cross.not_three_dvd_pow Nat.prime_two (by norm_num)
  exact three_le_pRank_sp4 (card_ringAut_and_isCyclic Nat.prime_two K hK).2 e' hc
    (comm_of_sylow_comm e' (KFactProofs.Stroth.Bal3.I294Cross.sylow_comm_psp_two h3)) hinn hαH
    hαk hαn hEH hE hEc

end LieClAut

end CFSG.LocalAnalysis.RankThreeTheoremC
