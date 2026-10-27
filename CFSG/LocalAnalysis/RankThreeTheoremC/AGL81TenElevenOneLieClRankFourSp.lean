module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenElevenOneLieClRankFour
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique CFSG.LocalAnalysis.RankThreeUC.S15
open Subgroup Matrix

namespace LieClAut

theorem exists_rankFour_of_fixed {X A : Type} [Group X] [Finite X] [CommGroup A] [Finite A]
    (hc : center X = ⊥) {H : Subgroup (MulAut X)}
    (hinn : (MulAut.conj : X →* MulAut X).range ≤ H) {β : MulAut X} (hβH : β ∈ H)
    (hβ3 : β ^ 3 = 1) (hβn : β ∉ (MulAut.conj : X →* MulAut X).range) (f : A →* X)
    (hf : Function.Injective f) (hA3 : ∀ a : A, a ^ 3 = 1) (hA : Nat.card A = 27)
    (hfix : ∀ a, β (f a) = f a) :
    ∃ F : Subgroup (MulAut X), F ≤ H ∧ IsElemAbelian 3 F ∧ Nat.card F = 81 := by
  have hconj : Function.Injective (MulAut.conj : X →* MulAut X) := by
    refine (injective_iff_map_eq_one _).2 fun x hx => ?_
    have hxc : x ∈ center X := mem_center_iff.2 fun y => by
      have h := congrArg (fun τ : MulAut X => τ y) hx
      simp only [MulAut.conj_apply, MulAut.one_apply] at h
      calc y * x = x * y * x⁻¹ * x := by rw [h]
        _ = x * y := by group
    rw [hc] at hxc
    exact (mem_bot.1 hxc)
  set E := ((MulAut.conj : X →* MulAut X).comp f).range with hE
  have hEc : Nat.card E = 27 := by
    rw [← hA]
    exact (Nat.card_congr (MonoidHom.ofInjective (f := (MulAut.conj : X →* MulAut X).comp f)
      (hconj.comp hf)).toEquiv).symm
  have hEab : CFSG.Assembly.IsElemAbelian 3 E := by
    refine ⟨⟨⟨?_⟩⟩, ?_⟩
    · rintro ⟨_, a, rfl⟩ ⟨_, b, rfl⟩
      exact Subtype.ext (by simp only [Subgroup.coe_mul, ← map_mul, mul_comm a b])
    · rintro _ ⟨a, rfl⟩
      rw [← map_pow, hA3, map_one]
  have hcomm : ∀ γ ∈ E, γ * β = β * γ := by
    rintro _ ⟨a, rfl⟩
    ext y
    simp only [MonoidHom.comp_apply, MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv,
      hfix]
  have hβE : β ∉ E := fun h => hβn (by obtain ⟨a, rfl⟩ := h; exact ⟨f a, rfl⟩)
  refine ⟨E ⊔ zpowers β, sup_le ?_ ((zpowers_le).2 hβH),
    CFSG.RankThree.PartTwo.Sec4.isElemAbelian_sup_zpowers hEab hβ3 hcomm, ?_⟩
  · rintro _ ⟨a, rfl⟩
    exact hinn ⟨f a, rfl⟩
  · rw [CFSG.RankThree.PartTwo.Sec4.card_sup_zpowers_of_not_mem hβ3 hcomm hβE, hEc]

end LieClAut

namespace SpE27

variable {K : Type} [Field K]

@[expose] def ca (x : ZMod 3) : K := if x = 1 then 0 else 1

@[expose] def cb (x : ZMod 3) : K := if x = 0 then 0 else 1

@[expose] def cd (x : ZMod 3) : K := if x = 2 then 0 else 1

variable [CharP K 2]

theorem one_add_one_eq_zero : (1 : K) + 1 = 0 := CharTwo.add_self_eq_zero 1

theorem zmod3_cases (x : ZMod 3) : x = 0 ∨ x = 1 ∨ x = 2 := by
  revert x; decide

theorem ca_add (x y : ZMod 3) : (ca (x + y) : K) = ca x * ca y + cb x * cb y := by
  rcases zmod3_cases x with rfl | rfl | rfl <;> rcases zmod3_cases y with rfl | rfl | rfl <;>
    simp +decide [ca, cb, one_add_one_eq_zero]

theorem cb_add (x y : ZMod 3) : (cb (x + y) : K) = ca x * cb y + cb x * cd y := by
  rcases zmod3_cases x with rfl | rfl | rfl <;> rcases zmod3_cases y with rfl | rfl | rfl <;>
    simp +decide [ca, cb, cd, one_add_one_eq_zero]

theorem cb_add' (x y : ZMod 3) : (cb (x + y) : K) = cb x * ca y + cd x * cb y := by
  rcases zmod3_cases x with rfl | rfl | rfl <;> rcases zmod3_cases y with rfl | rfl | rfl <;>
    simp +decide [ca, cb, cd, one_add_one_eq_zero]

theorem cd_add (x y : ZMod 3) : (cd (x + y) : K) = cb x * cb y + cd x * cd y := by
  rcases zmod3_cases x with rfl | rfl | rfl <;> rcases zmod3_cases y with rfl | rfl | rfl <;>
    simp +decide [ca, cb, cd, one_add_one_eq_zero]

theorem det_eq (x : ZMod 3) : (ca x * cd x - cb x * cb x : K) = 1 := by
  rcases zmod3_cases x with rfl | rfl | rfl <;>
    simp +decide [ca, cb, cd, CharTwo.sub_eq_add]

theorem cb_eq_zero {x : ZMod 3} (h : (cb x : K) = 0) : x = 0 := by
  rcases zmod3_cases x with rfl | rfl | rfl <;> simp +decide [cb] at h ⊢

theorem map_c (τ : K ≃+* K) (x : ZMod 3) :
    τ (ca x) = ca x ∧ τ (cb x) = cb x ∧ τ (cd x) = cd x := by
  rcases zmod3_cases x with rfl | rfl | rfl <;> simp +decide [ca, cb, cd]

@[expose] def spE (v : Fin 3 → ZMod 3) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K :=
  fromBlocks (diagonal fun i => ca (v i)) (diagonal fun i => cb (v i))
    (diagonal fun i => cb (v i)) (diagonal fun i => cd (v i))

theorem spE_mul (v w : Fin 3 → ZMod 3) : (spE v : Matrix _ _ K) * spE w = spE (v + w) := by
  simp only [spE, fromBlocks_multiply, diagonal_mul_diagonal, diagonal_add, Pi.add_apply,
    ca_add, cb_add, cd_add]
  congr 2
  funext i
  rw [← cb_add', ← cb_add]

theorem spE_zero : (spE 0 : Matrix _ _ K) = 1 := by
  simp +decide [spE, ca, cb, cd, ← fromBlocks_one]

theorem spE_mem (v : Fin 3 → ZMod 3) :
    (spE v : Matrix _ _ K)ᵀ * fromBlocks 0 1 (-1) 0 * spE v = fromBlocks 0 1 (-1) 0 := by
  simp only [spE, fromBlocks_transpose, diagonal_transpose, fromBlocks_multiply,
    diagonal_mul_diagonal, Matrix.zero_mul, Matrix.mul_zero, Matrix.one_mul, Matrix.mul_one,
    Matrix.neg_mul, Matrix.mul_neg, zero_add, add_zero]
  congr 1 <;> ext i j <;> by_cases h : i = j <;>
    simp [diagonal_apply, Matrix.one_apply, h, mul_comm]
  · linear_combination (det_eq (K := K) (v j))
  · linear_combination -(det_eq (K := K) (v j))

open CFSG.LocalAnalysis.ComponentInitial

noncomputable def spEHom : Multiplicative (Fin 3 → ZMod 3) →* StatedSp 3 K where
  toFun v := ⟨⟨spE v.toAdd, spE (-v.toAdd), by rw [spE_mul, add_neg_cancel, spE_zero],
    by rw [spE_mul, neg_add_cancel, spE_zero]⟩,
    CFSG.Open.StatedAPI.mem_statedSp_iff.2 (spE_mem _)⟩
  map_one' := Subtype.ext (Units.ext spE_zero)
  map_mul' v w := Subtype.ext (Units.ext (spE_mul v.toAdd w.toAdd).symm)

theorem projE_injective :
    Function.Injective ((SymplecticFlag.proj 3 K).comp (spEHom (K := K))) := by
  refine (injective_iff_map_eq_one _).2 fun v hv => ?_
  have hk : spEHom v ∈ (SymplecticFlag.proj 3 K).ker := hv
  rw [SymplecticHigher.ker_proj, Subgroup.mem_subgroupOf, StatedScalars] at hk
  obtain ⟨c, hc⟩ := hk
  have h0 : ∀ i, (cb (v.toAdd i) : K) = 0 := fun i => by
    have := congrArg (fun g : GL (Fin 3 ⊕ Fin 3) K =>
      (g : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) (Sum.inl i) (Sum.inr i)) hc
    simpa [spEHom, spE, Matrix.GeneralLinearGroup.scalar] using this.symm
  exact Multiplicative.toAdd.injective (funext fun i => cb_eq_zero (h0 i))

theorem fieldSp_spEHom (τ : K ≃+* K) (v : Multiplicative (Fin 3 → ZMod 3)) :
    SymplecticHigher.fieldSp 3 K τ (spEHom v) = spEHom v := by
  refine Subtype.ext (Units.ext ?_)
  rw [SymplecticHigher.coe_fieldSp]
  change (spE v.toAdd).map τ = spE v.toAdd
  have h1 := fun x => (map_c τ x).1
  have h2 := fun x => (map_c τ x).2.1
  have h3 := fun x => (map_c τ x).2.2
  simp only [spE, fromBlocks_map, diagonal_map (map_zero τ), h1, h2, h3]

end SpE27

namespace LieClAut

open CFSG.LocalAnalysis.ComponentInitial SymplecticFlag SymplecticHigher
open CFSG.ComponentClassification.UnbalancedCatalog SpChain
open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal)

theorem exists_rankFour_sp {X : Type} [Group X] [Finite X] {K : Type} [Field K] [Finite K]
    [CharP K 2] (e : X ≃* StatedProj (StatedSp 3 K)) (hc : center X = ⊥)
    {H : Subgroup (MulAut X)} (hinn : (MulAut.conj : X →* MulAut X).range ≤ H) {α : MulAut X}
    (hαH : α ∈ H) (hα : ∃ k : ℕ, α ^ 3 ^ k = 1)
    (hαn : α ∉ (MulAut.conj : X →* MulAut X).range) :
    ∃ F : Subgroup (MulAut X), F ≤ H ∧ IsElemAbelian 3 F ∧ Nat.card F = 81 := by
  classical
  set P := StatedProj (StatedSp 3 K)
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
  have hnot : ∀ τ : K ≃+* K, τ ≠ 1 → fieldAut 3 K τ ∉ inner P := fun τ hτ => by
    have := (spInner_mul_fieldAut_not_mem_inner_iff (1 : StatedSp 3 K) τ).2 hτ
    rwa [map_one, one_mul] at this
  obtain ⟨g, φ, hgφ⟩ := exists_eq_spInner_mul_fieldAut (r := 3) (K := K) (α := Ψ α)
    (by rw [(automorphism_generation (by norm_num)).1]; trivial)
  have hφH : Ψ.symm (fieldAut 3 K φ) ∈ H := by
    have h1 : fieldAut 3 K φ = (spInner 3 K g)⁻¹ * Ψ α := by rw [hgφ]; group
    rw [h1, map_mul, map_inv, Ψ.symm_apply_apply, spInner_eq_conj, hΨinv]
    exact H.mul_mem (H.inv_mem (hinn ⟨_, rfl⟩)) hαH
  obtain ⟨k, hk⟩ := hα
  haveI := inner_normal P
  have hφk : φ ^ 3 ^ k = 1 := by
    by_contra hne
    apply hnot _ hne
    have hq : ((fieldAut 3 K φ : MulAut P) : MulAut P ⧸ inner P) = ((Ψ α : MulAut P) :
        MulAut P ⧸ inner P) := by
      rw [hgφ, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).2 (spInner_mem_inner g),
        one_mul]
    rw [map_pow, ← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hq, ← QuotientGroup.mk_pow,
      ← map_pow, hk, map_one, QuotientGroup.mk_one]
  have hφ1 : φ ≠ 1 := by
    rintro rfl
    apply hαn
    have h1 : Ψ α ∈ inner P := by rw [hgφ, map_one, mul_one]; exact spInner_mem_inner g
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
  set β := Ψ.symm (fieldAut 3 K τ) with hβ
  have hβH : β ∈ H := by
    rw [hβ, hτ, map_pow, map_pow]
    exact H.pow_mem hφH _
  have hβ3 : β ^ 3 = 1 := by rw [hβ, ← map_pow, ← map_pow, hτ3, map_one, map_one]
  have hβn : β ∉ (MulAut.conj : X →* MulAut X).range := fun h =>
    hnot τ hτ1 (by have := hinnΨ _ h; rwa [hβ, Ψ.apply_symm_apply] at this)
  refine exists_rankFour_of_fixed hc hinn hβH hβ3 hβn
    (e.symm.toMonoidHom.comp ((proj 3 K).comp SpE27.spEHom))
    (e.symm.injective.comp SpE27.projE_injective) ?_ ?_ ?_
  · intro a
    apply Multiplicative.toAdd.injective
    funext i
    simp only [toAdd_pow, toAdd_one, Pi.smul_apply, Pi.zero_apply]
    rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  · simp [Nat.card_eq_fintype_card]
  · intro a
    simp only [hβ, hΨ, MulAut.congr_symm_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.apply_symm_apply, MulEquiv.trans_apply]
    rw [fieldAut_proj, SpE27.fieldSp_spEHom]

end LieClAut

@[expose] def KFactOuterThreeRankFourRest : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (d : TauCeti.ValidLieTypeIndex), IsRankTwoPlus d.1 →
    RankThreeList d.1 → (∀ q : TauCeti.PrimePower, d.1 ≠ .B 3 q) →
    LieClAut.FieldExponentThree d.1 →
    Nonempty (X ≃* (TauCeti.CFSGIndex.lie d).Group) → Subgroup.center X = ⊥ →
    ∀ H : Subgroup (MulAut X),
    (MulAut.conj : X →* MulAut X).range ≤ H →
    (∃ α ∈ H, (∃ k : ℕ, α ^ 3 ^ k = 1) ∧ α ∉ (MulAut.conj : X →* MulAut X).range) →
    ∃ F : Subgroup (MulAut X), F ≤ H ∧ IsElemAbelian 3 F ∧ Nat.card F = 81

theorem kFactOuterThreeRankFour_of_rest (h : KFactOuterThreeRankFourRest) :
    KFactOuterThreeRankFour := by
  intro X _ _ d hd hl h3 he hc H hinn hα
  by_cases hB : ∀ q : TauCeti.PrimePower, d.1 ≠ .B 3 q
  · exact h X d hd hl hB h3 he hc H hinn hα
  push Not at hB
  obtain ⟨q, hq⟩ := hB
  obtain ⟨d, hv⟩ := d
  simp only at hq
  subst hq
  obtain ⟨e⟩ := he
  have hp : q.p = 2 := hd.1
  obtain ⟨_, K, _, _, hK, ⟨e'⟩⟩ :=
    CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even 3 q hv hp le_rfl e
  rw [hp] at hK
  haveI := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
  obtain ⟨α, hαH, hαk, hαn⟩ := hα
  exact LieClAut.exists_rankFour_sp e' hc hinn hαH hαk hαn

theorem kFactTenElevenOneLieAutRes_of_rankFourRest
    (hK : KFactOuterThreeRankFourRest) (h2 : KFactTenElevenOneLieAutFieldTwo) :
    KFactTenElevenOneLieAutRes :=
  kFactTenElevenOneLieAutRes_of_rankFour (kFactOuterThreeRankFour_of_rest hK) h2

end CFSG.LocalAnalysis.RankThreeTheoremC
