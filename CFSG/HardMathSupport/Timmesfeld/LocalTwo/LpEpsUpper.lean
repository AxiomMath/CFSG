module

public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LpEpsHeis
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.OuterPlane
public import CFSG.HardMathSupport.Solomon.LocalBalance.Balance
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Families
public import CFSG.HardMathSupport.Timmesfeld.Proving.ExistsOrderPCentralizer
public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPrimeCoreCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.GLTheoremB.QuotientTools
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance Subgroup

theorem exists_gen_pair {G : Type*} [Group G] {p : ℕ} (hp : p.Prime) {D : Subgroup G}
    (hD : IsElemAbelian p D) (hcard : Nat.card D = p ^ 2) :
    ∃ x ∈ D, ∃ y ∈ D, x ≠ 1 ∧ y ∉ zpowers x ∧ closure {x, y} = D := by
  have : Fact p.Prime := ⟨hp⟩
  have hDfin : Finite D := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero 2 hp.ne_zero)
  have hD1 : D ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hcard
    exact absurd hcard.symm (Nat.one_lt_pow (by norm_num) hp.one_lt).ne'
  obtain ⟨⟨x, hxD⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hD1
  have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hxp : orderOf x = p := orderOf_eq_prime (hD.2 x hxD) hx1'
  have hzx : Nat.card (zpowers x) = p := by rw [Nat.card_zpowers, hxp]
  have hzD : zpowers x ≤ D := (Subgroup.zpowers_le).2 hxD
  have : Finite (zpowers x) := Finite.of_injective _ (Subgroup.inclusion_injective hzD)
  obtain ⟨y, hyD, hyx⟩ : ∃ y ∈ D, y ∉ zpowers x := by
    by_contra h
    push Not at h
    have : D ≤ zpowers x := h
    have h1 := Subgroup.card_le_of_le this
    rw [hcard, hzx] at h1
    have : p < p ^ 2 := by
      calc p = p ^ 1 := (pow_one p).symm
        _ < p ^ 2 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    omega
  refine ⟨x, hxD, y, hyD, hx1', hyx, ?_⟩
  have hcl : closure {x, y} ≤ D := by
    rw [closure_le]
    rintro _ (rfl | rfl)
    · exact hxD
    · exact hyD
  have : Finite (closure {x, y}) := Finite.of_injective _ (Subgroup.inclusion_injective hcl)
  have hzcl : zpowers x ≤ closure {x, y} := (Subgroup.zpowers_le).2 (subset_closure (by simp))
  have hycl : y ∈ closure {x, y} := subset_closure (by simp)
  have hdvd : Nat.card (closure {x, y}) ∣ p ^ 2 := hcard ▸ Subgroup.card_dvd_of_le hcl
  obtain ⟨j, hj, hjk⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  have hge : p ≤ Nat.card (closure {x, y}) := hzx ▸ Subgroup.card_le_of_le hzcl
  have hj2 : j = 2 := by
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with h | h | h
    · subst h; rw [pow_zero] at hjk; have := hp.two_le; omega
    · subst h
      exfalso
      rw [pow_one] at hjk
      have heq : zpowers x = closure {x, y} :=
        Subgroup.eq_of_le_of_card_ge hzcl (by rw [hjk, hzx])
      exact hyx (heq ▸ hycl)
    · exact h
  subst hj2
  exact Subgroup.eq_of_le_of_card_ge hcl (by rw [hjk, hcard])


@[expose] def UpperP (p : ℕ) (S : Type*) [Group S] : Prop :=
  ∀ D : Subgroup (MulAut S), IsElemAbelian p D → Nat.card D = p ^ 2 →
    ∀ H : Subgroup (MulAut S), innerAut S ≤ H → D ≤ Subgroup.normalizer (H : Set (MulAut S)) →
      localDeltaIn p H D ≠ ⊥ → ∀ A : Subgroup (MulAut S), D ≤ A → IsElemAbelian p A →
        Finite A → Nat.card A ≤ p ^ 3

structure UpperModel (p : ℕ) (S : Type*) [Group S] (K : Type*) [Field K] where
  M : Type
  [grp : Group M]
  ι : M →* GL (Fin p) K
  ι_inj : Function.Injective ι
  ρ : M →* MulAut S
  ker_ρ : ∀ g : M, ρ g = 1 → ∃ c : Kˣ, ι g = Matrix.GeneralLinearGroup.scalar (Fin p) c
  scalar_ρ : ∀ (g : M) (c : Kˣ), ι g = Matrix.GeneralLinearGroup.scalar (Fin p) c → ρ g = 1
  plane : ∀ A B : M, A * B = B * A → ρ A ^ p = 1 → ρ B ^ p = 1 → ρ A ≠ 1 →
    ρ B ∉ zpowers (ρ A) → ∀ H : Subgroup (MulAut S), innerAut S ≤ H →
      closure {ρ A, ρ B} ≤ Subgroup.normalizer (H : Set (MulAut S)) →
        localDeltaIn p H (closure {ρ A, ρ B}) = ⊥
  outer_bal : ∀ D : Subgroup (MulAut S), IsElemAbelian p D → ¬ D ≤ ρ.range →
    ∀ H : Subgroup (MulAut S), innerAut S ≤ H → localDeltaIn p H D = ⊥
  cyc : ∀ A : Subgroup (MulAut S), IsElemAbelian p A → Finite A →
    ∃ (C : Type) (_ : Group C) (_ : IsCyclic C) (α : A →* C),
      ∀ x : A, α x = 1 → (x : MulAut S) ∈ ρ.range

attribute [instance] UpperModel.grp

section Scalar

variable {K : Type*} [Field K] {p : ℕ}

lemma scalar_eq_one_of {u : Kˣ} [NeZero p]
    (h : Matrix.GeneralLinearGroup.scalar (Fin p) u = 1) : u = 1 := by
  have := congrArg (fun g : GL (Fin p) K => (g : Matrix (Fin p) (Fin p) K) ⟨0, Nat.pos_of_ne_zero
    (NeZero.ne p)⟩ ⟨0, Nat.pos_of_ne_zero (NeZero.ne p)⟩) h
  simpa using this

lemma pow_eq_one_of_conj [NeZero p] {g h : GL (Fin p) K} {a0 a : Kˣ}
    (hg : g ^ p = Matrix.GeneralLinearGroup.scalar (Fin p) a0)
    (hh : h * g * h⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin p) a * g) : a ^ p = 1 := by
  have h1 : (h * g * h⁻¹) ^ p = h * g ^ p * h⁻¹ := conj_pow
  rw [hh, Commute.mul_pow (Matrix.GeneralLinearGroup.scalar_commute a g), hg, ← map_pow,
    ← map_mul] at h1
  have h2 : h * Matrix.GeneralLinearGroup.scalar (Fin p) a0 * h⁻¹ =
      Matrix.GeneralLinearGroup.scalar (Fin p) a0 := by
    rw [← Matrix.GeneralLinearGroup.scalar_commute a0 h]; group
  rw [h2] at h1
  have h3 : Matrix.GeneralLinearGroup.scalar (Fin p) (a ^ p) = 1 := by
    have : Matrix.GeneralLinearGroup.scalar (Fin p) (a ^ p) *
        Matrix.GeneralLinearGroup.scalar (Fin p) a0 =
        1 * Matrix.GeneralLinearGroup.scalar (Fin p) a0 := by
      rw [one_mul, ← map_mul]
      simpa [map_mul] using h1
    exact mul_right_cancel this
  exact scalar_eq_one_of h3

end Scalar


open HeisP in
theorem upperP_of_model {p : ℕ} (hp : p.Prime) {S : Type*} [Group S] {K : Type*} [Field K]
    (hpK : (p : K) ≠ 0) (U : UpperModel p S K) : UpperP p S := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  intro D hD hcard H hH hDH hΔ A hDA hA hAfin
  have hDr : D ≤ U.ρ.range := by
    by_contra h
    exact hΔ (U.outer_bal D hD h H hH)
  obtain ⟨x, hx, y, hy, hx1, hyx, hgen⟩ := exists_gen_pair hp hD hcard
  obtain ⟨A0, rfl⟩ := MonoidHom.mem_range.1 (hDr hx)
  obtain ⟨B0, rfl⟩ := MonoidHom.mem_range.1 (hDr hy)
  have hcomm : U.ρ A0 * U.ρ B0 = U.ρ B0 * U.ρ A0 :=
    congrArg Subtype.val (hD.1.is_comm.comm ⟨_, hx⟩ ⟨_, hy⟩)
  have h1 : U.ρ (A0 * B0 * A0⁻¹ * B0⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]; group
  obtain ⟨c, hc⟩ := U.ker_ρ _ h1
  simp only [map_mul, map_inv] at hc
  by_cases hc1 : c = 1
  · exfalso
    apply hΔ
    have hAB : A0 * B0 = B0 * A0 := by
      apply U.ι_inj
      rw [hc1, map_one] at hc
      rw [map_mul, map_mul]
      rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at hc
      exact hc
    have := U.plane A0 B0 hAB (hD.2 _ hx) (hD.2 _ hy) hx1 hyx H hH (hgen ▸ hDH)
    rwa [hgen] at this
  ·
    have hpow : ∀ X : U.M, U.ρ X ^ p = 1 →
        ∃ a0 : Kˣ, (U.ι X) ^ p = Matrix.GeneralLinearGroup.scalar (Fin p) a0 := by
      intro X hX
      obtain ⟨a0, ha0⟩ := U.ker_ρ (X ^ p) (by rw [map_pow, hX])
      exact ⟨a0, by rw [← map_pow]; exact ha0⟩
    obtain ⟨a0, ha0⟩ := hpow A0 (hD.2 _ hx)
    obtain ⟨b0, hb0⟩ := hpow B0 (hD.2 _ hy)
    have hcp : c ^ p = 1 := by
      have := pow_eq_one_of_conj ha0 (rel_BA hc)
      rwa [inv_pow, inv_eq_one] at this
    have hω : IsPrimitiveRoot c p := by
      have := orderOf_eq_prime hcp hc1
      rw [← this]
      exact IsPrimitiveRoot.orderOf c
    have hmem : ∀ z ∈ A, z ∈ U.ρ.range → z ∈ D := by
      intro z hzA hzr
      obtain ⟨C0, rfl⟩ := MonoidHom.mem_range.1 hzr
      have hxA : U.ρ A0 ∈ A := hDA hx
      have hyA : U.ρ B0 ∈ A := hDA hy
      have hCA : U.ρ C0 * U.ρ A0 = U.ρ A0 * U.ρ C0 :=
        congrArg Subtype.val (hA.1.is_comm.comm ⟨_, hzA⟩ ⟨_, hxA⟩)
      have hCB : U.ρ C0 * U.ρ B0 = U.ρ B0 * U.ρ C0 :=
        congrArg Subtype.val (hA.1.is_comm.comm ⟨_, hzA⟩ ⟨_, hyA⟩)
      obtain ⟨a, ha⟩ := U.ker_ρ (C0 * A0 * C0⁻¹ * A0⁻¹) (by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, hCA]; group)
      obtain ⟨b, hb⟩ := U.ker_ρ (C0 * B0 * C0⁻¹ * B0⁻¹) (by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, hCB]; group)
      simp only [map_mul, map_inv] at ha hb
      have hCA' := rel_AB ha
      have hCB' := rel_AB hb
      obtain ⟨i, j, m, hm⟩ := heisenberg_normalizer_p hω hc hpK (pow_eq_one_of_conj ha0 hCA')
        (pow_eq_one_of_conj hb0 hCB') hCA' hCB'
      have hm0 : U.ρ ((A0 ^ i * B0 ^ j)⁻¹ * C0) = 1 := by
        refine U.scalar_ρ _ m ?_
        rw [map_mul, map_inv, map_mul, map_pow, map_pow, hm, inv_mul_cancel_left]
      have hC0 : C0 = (A0 ^ i * B0 ^ j) * ((A0 ^ i * B0 ^ j)⁻¹ * C0) := by group
      rw [hC0, map_mul, hm0, mul_one, map_mul, map_pow, map_pow, ← hgen]
      exact mul_mem (pow_mem (subset_closure (by simp)) i) (pow_mem (subset_closure (by simp)) j)
    obtain ⟨Cc, _, _, α, hα⟩ := U.cyc A hA hAfin
    have hDfin : Finite D := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero 2 hp.ne_zero)
    have hle := CrossChar.card_le_mul_card_ker' hp (fun h : A => Subtype.ext (hA.2 h h.2)) α
    have hker : Nat.card α.ker ≤ Nat.card D := by
      refine Nat.card_le_card_of_injective
        (fun k => (⟨(k.1 : MulAut S), hmem _ k.1.2 (hα k.1 k.2)⟩ : D)) ?_
      intro k1 k2 h
      have h' : ((k1 : A) : MulAut S) = ((k2 : A) : MulAut S) :=
        congrArg (fun d : D => (d : MulAut S)) h
      exact Subtype.ext (Subtype.ext h')
    calc Nat.card A ≤ p * Nat.card α.ker := hle
      _ ≤ p * p ^ 2 := by
          apply Nat.mul_le_mul_left
          rw [← hcard]; exact hker
      _ = p ^ 3 := by ring

end CFSG.HardMathSupport.Timmesfeld.LocalTwo
