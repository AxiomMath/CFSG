module

public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderFamilies
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderPSUOrder
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderPSUDescent

public section

namespace CFSG.HardMathSupport.Lang.Coordinator

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.Classical CFSG.LieType.Chevalley
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible StatedClassicalModel)
open CFSG.ComponentClassification.CatLeaf (lieOrderNumerator lieOrderDivisor)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem card_fixedSubgroup_eq_of_intertwine {G H : Type*} [Group G] [Group H] (v : G ≃* H)
    (α : MulAut G) (β : MulAut H) (hβ : ∀ x, β (v x) = v (α x)) :
    Nat.card (fixedSubgroup α) = Nat.card (fixedSubgroup β) := by
  refine Nat.card_congr
    { toFun := fun x => ⟨v x, ?_⟩
      invFun := fun y => ⟨v.symm y, ?_⟩
      left_inv := fun x => Subtype.ext (v.symm_apply_apply x)
      right_inv := fun y => Subtype.ext (v.apply_symm_apply y) }
  · have hx : α x = x := x.2
    change β (v x) = v x
    rw [hβ, hx]
  · have hy : β y = y := y.2
    change α (v.symm y) = v.symm y
    apply v.injective
    rw [← hβ, v.apply_symm_apply, hy]

theorem card_fixedSubgroup_congr {G H : Type*} [Group G] [Group H] (θ : G ≃* H) (α : MulAut G) :
    Nat.card (fixedSubgroup (MulAut.congr θ α)) = Nat.card (fixedSubgroup α) :=
  (card_fixedSubgroup_eq_of_intertwine θ α _ fun x => by
    simp [MulAut.congr_apply]).symm

theorem congr_mem_inner_iff {G H : Type*} [Group G] [Group H] (θ : G ≃* H) (α : MulAut G) :
    MulAut.congr θ α ∈ inner H ↔ α ∈ inner G := by
  have key : ∀ x : G, MulAut.congr θ (MulAut.conj x) = MulAut.conj (θ x) := fun x => by
    ext y
    simp [MulAut.congr_apply, MulAut.conj_apply]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨θ.symm y, ?_⟩
    apply (MulAut.congr θ).injective
    rw [key, MulEquiv.apply_symm_apply, hy]
  · rintro ⟨x, rfl⟩
    exact ⟨θ x, (key x).symm⟩

theorem mem_inner_of_mem_primeFormD {ℓ f n p : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData ℓ f K) (hn : 3 ≤ n) (hne : ¬(n = 3 ∧ ℓ ^ f = 2)) (hp : p.Prime)
    (hg : ¬ p ∣ Nat.gcd n (ℓ ^ f + 1))
    {d : MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))}
    (hd : d ∈ primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) (hdp : d ^ p = 1) :
    d ∈ inner (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
  have := h.finite
  obtain ⟨-, -, hquot, -⟩ := unitary_full_diagonal_outer_order h hn hne
  set Q := primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ⧸
    (inner (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))).subgroupOf
      (primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) with hQ
  have h1 : orderOf (QuotientGroup.mk
      (⟨d, hd⟩ : primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) : Q) ∣ p := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← QuotientGroup.mk_pow]
    have : (⟨d, hd⟩ : primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) ^ p = 1 :=
      Subtype.ext hdp
    rw [this]
    rfl
  have h2 : orderOf (QuotientGroup.mk
      (⟨d, hd⟩ : primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) : Q) ∣
      Nat.gcd n (ℓ ^ f + 1) := hquot ▸ (_root_.orderOf_dvd_natCard _)
  rcases (Nat.dvd_prime hp).mp h1 with h3 | h3
  · have h4 := orderOf_eq_one_iff.mp h3
    exact (QuotientGroup.eq_one_iff (N := (inner (primeFormP h
      ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))).subgroupOf
      (primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) _).mp h4
  · exact absurd (h3 ▸ h2) hg

theorem outerFixedOrderBoundAt_PSU : OuterFixedOrderBoundAt .PSU := by
  intro K _ _ n ℓ f hadm hmodel _ p hp hp2 hdiv _ α hαp hαin
  left
  have hcl : StatedClassicalModel K .PSU n ℓ f := by
    rcases hmodel with ⟨-, hcl⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · exact hcl
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
  obtain ⟨⟨hℓ, hf, hn, hne⟩, F, hF, hFin, hFcard, ⟨e⟩⟩ := hcl
  have hne' : ¬(n = 3 ∧ ℓ ^ f = 2) := fun ⟨h1, h2⟩ => hne (by rw [h1, h2])
  have h : UnitaryFieldData ℓ f F := ⟨hℓ, hf, by rw [hFcard, ← pow_mul, mul_comm]⟩
  have : Fact p.Prime := ⟨hp⟩
  have hC1 : IsPrimeFormGram (1 : GL (Fin n) F) := isPrimeFormGram_one
  have hdiv' : ¬ p ∣ Nat.gcd n (ℓ ^ f + 1) := hdiv
  obtain ⟨θ⟩ : Nonempty (K ≃* primeFormP h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) :=
    ⟨(e.trans (unitaryPSUEquiv h (by omega)).symm).trans
      (Classical.choice (unitary_prime_form_full_semilinear_realization h hC1 hn hne').1).symm⟩
  set β := MulAut.congr θ α with hβdef
  have hβp : β ^ p = 1 := by rw [hβdef, ← map_pow, hαp, map_one]
  have hβout : β ∉ inner (primeFormP h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) :=
    fun hin => hαin ((congr_mem_inner_iff θ α).mp hin)
  rw [← card_fixedSubgroup_congr θ α]
  change ∃ f₀ : ℕ, f = p * f₀ ∧ Nat.card (fixedSubgroup β) ∣ lieOrderNumerator .PSU n (ℓ ^ f₀)
  have hβ1 : β ≠ 1 := fun h1 => hβout (h1 ▸ (CFSG.ComponentClassification.OuterAutomorphisms.inner _).one_mem)
  have hβord : orderOf β = p := orderOf_eq_prime hβp hβ1
  set σ := primeFormFieldFactor h hC1 hn hne' β with hσdef
  have hσp : σ ^ p = 1 := by rw [hσdef, ← map_pow, hβp, map_one]
  have hσ1 : σ ≠ 1 := by
    intro hσ1
    have hD : β ∈ primeFormD h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
      rw [← ker_primeFormFieldFactor h hC1 hn hne']
      exact hσ1
    exact hβout (mem_inner_of_mem_primeFormD h hn hne' hp hdiv' hD hβp)
  have hσord : orderOf σ = p := orderOf_eq_prime hσp hσ1
  obtain ⟨-, -, -, -, -, M, hM⟩ :=
    unitary_prime_semilinear_field_descent' h hn hne' hp hp2 β hβord σ hσdef.symm hσord
  set u := primeFormConjHom h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) M with hu
  set fσ := primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ with hfσ
  have hβu : β * u = u * fσ := by
    rw [← hM]
    group
  have hcard1 : Nat.card (fixedSubgroup β) = Nat.card (fixedSubgroup fσ) :=
    (card_fixedSubgroup_eq_of_intertwine (u : _ ≃* _) fσ β fun x => by
      exact congrArg (fun g : MulAut _ => g x) hβu).symm
  have hZ' : ¬ p ∣ Nat.card (normOneScalars h
      (gramSU h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) n) := by
    rw [card_normOneScalars_one h (by omega)]
    exact hdiv'
  obtain ⟨hpf, -, -, -, -, hinj, hrange, -, -, -, -⟩ :=
    prime_subfield_fixed_group_package h hp hp2 hσord n hn hne' hZ'
  have hcard2 : Nat.card (fixedSubgroup fσ) =
      Nat.card (primeFormP (fixSubfield_unitaryFieldData h hp hp2 hσord)
        ((1 : GL (Fin n) (fixSubfield σ)) : Matrix (Fin n) (Fin n) (fixSubfield σ))) := by
    rw [show fixedSubgroup fσ = fieldFixedPSU h n σ from rfl, ← hrange]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  refine ⟨f / p, (Nat.mul_div_cancel' hpf).symm, ?_⟩
  rw [hcard1, hcard2]
  exact Dvd.intro _ (card_primeFormP_one_mul_gcd (fixSubfield_unitaryFieldData h hp hp2 hσord)
    (by omega))

end CFSG.HardMathSupport.Lang.Coordinator
