module

public import CFSG.LocalAnalysis.RankThreeUC.K518HRkGrp
public import CFSG.LocalAnalysis.StandardType.GGL45NtGroupLemmas
public import CFSG.RankThree.PartOne.KC.UnitaryRegularUnipotentLift
public import CFSG.Monster.B.TwoA.Base.ElemAut

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.K518H

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.ComponentClassification.OuterAutomorphisms

section PLevel

variable {p f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

private theorem inner_le_primeFormD (C : Matrix (Fin n) (Fin n) K) :
    inner (primeFormP h C) ≤ primeFormD h C := by
  intro α hα
  obtain ⟨s, rfl⟩ := (mem_inner_primeFormP h C α).mp hα
  exact ⟨_, rfl⟩

private theorem pow_mem_inner_of_mem_primeFormD (C : GL (Fin n) K)
    {d : MulAut (primeFormP h (C : Matrix (Fin n) (Fin n) K))}
    (hd : d ∈ primeFormD h (C : Matrix (Fin n) (Fin n) K)) :
    d ^ (p ^ f + 1) ∈ inner (primeFormP h (C : Matrix (Fin n) (Fin n) K)) := by
  obtain ⟨B, rfl⟩ := hd
  rw [← map_pow]
  have hdet : (((B ^ (p ^ f + 1) : primeFormUnitary h (C : Matrix (Fin n) (Fin n) K)) :
      GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = 1 := by
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, Matrix.det_pow, ← h.norm_eq_pow]
    exact norm_det_eq_one h C B.2
  refine (mem_inner_primeFormP h _ _).mpr ⟨⟨((B ^ (p ^ f + 1) : primeFormUnitary h _) :
    GL (Fin n) K), (B ^ (p ^ f + 1)).2, hdet⟩, ?_⟩
  rfl

private theorem mem_inner_of_mem_primeFormD_of_pow_eq_one (C : GL (Fin n) K) {ℓ k : ℕ}
    (hcop : Nat.Coprime (ℓ ^ k) (p ^ f + 1))
    {β : MulAut (primeFormP h (C : Matrix (Fin n) (Fin n) K))}
    (hβ : β ∈ primeFormD h (C : Matrix (Fin n) (Fin n) K)) (hβk : β ^ (ℓ ^ k) = 1) :
    β ∈ inner (primeFormP h (C : Matrix (Fin n) (Fin n) K)) := by
  have h1 := pow_mem_inner_of_mem_primeFormD h C hβ
  have h2 : (QuotientGroup.mk β : Outer (primeFormP h (C : Matrix (Fin n) (Fin n) K))) ^
      (p ^ f + 1) = 1 := by
    rw [← QuotientGroup.mk_pow]
    exact (QuotientGroup.eq_one_iff _).mpr h1
  have h3 : (QuotientGroup.mk β : Outer (primeFormP h (C : Matrix (Fin n) (Fin n) K))) ^
      (ℓ ^ k) = 1 := by
    rw [← QuotientGroup.mk_pow, hβk, QuotientGroup.mk_one]
  have h4 := Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one h3) hcop
  have h5 : orderOf (QuotientGroup.mk β : Outer (primeFormP h (C : Matrix (Fin n) (Fin n) K))) =
      1 := Nat.Coprime.eq_one_of_dvd h4 (orderOf_dvd_of_pow_eq_one h2)
  exact (QuotientGroup.eq_one_iff β).mp (orderOf_eq_one_iff.mp h5)

private theorem not_dvd_card_map_primeFormD [Finite K] (C : GL (Fin n) K) {ℓ : ℕ} [Fact ℓ.Prime]
    (hℓq : ¬ ℓ ∣ p ^ f + 1) :
    ¬ ℓ ∣ Nat.card ((primeFormD h (C : Matrix (Fin n) (Fin n) K)).map
      (QuotientGroup.mk' (inner (primeFormP h (C : Matrix (Fin n) (Fin n) K))))) := by
  intro hdvd
  obtain ⟨⟨x, hx⟩, hxo⟩ := exists_prime_orderOf_dvd_card' ℓ hdvd
  have hxo' : orderOf x = ℓ := (Subgroup.orderOf_mk x hx).symm.trans hxo
  obtain ⟨d, hd, hdx⟩ := hx
  have h1 : x ^ (p ^ f + 1) = 1 := by
    rw [← hdx, ← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr (pow_mem_inner_of_mem_primeFormD h C hd)
  apply hℓq
  rw [← hxo']
  exact orderOf_dvd_of_pow_eq_one h1

end PLevel

section Main

theorem hasRankTwoPair_primeFormP {f : ℕ} {F : Type} [Field F] [Finite F]
    (h : UnitaryFieldData 2 f F) (hf : 2 ≤ f) {C : GL (Fin 3) F} (hC : IsPrimeFormGram C)
    {ℓ : ℕ} [hℓF : Fact ℓ.Prime] (hℓq : ¬ ℓ ∣ 2 ^ f + 1)
    (hdvd : ℓ ∣ Nat.card (primeFormP h (C : Matrix (Fin 3) (Fin 3) F)))
    {α : MulAut (primeFormP h (C : Matrix (Fin 3) (Fin 3) F))} {k : ℕ} (hα : orderOf α = ℓ ^ k)
    (hαI : α ∉ inner (primeFormP h (C : Matrix (Fin 3) (Fin 3) F))) :
    HasRankTwoPair (inner (primeFormP h (C : Matrix (Fin 3) (Fin 3) F)) ⊔ Subgroup.zpowers α) ℓ := by
  classical
  have hℓ : ℓ.Prime := hℓF.out
  have hq : ¬ (3 = 3 ∧ 2 ^ f = 2) := by
    rintro ⟨-, h2⟩
    have : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    omega
  set P := primeFormP h (C : Matrix (Fin 3) (Fin 3) F) with hP
  set ff := primeFormFieldFactor h hC (le_refl 3) hq with hff
  have hker : ff.ker = primeFormD h (C : Matrix (Fin 3) (Fin 3) F) :=
    ker_primeFormFieldFactor h hC (le_refl 3) hq
  have hIle := inner_le_primeFormD h (C : Matrix (Fin 3) (Fin 3) F)
  have hcop : ∀ j, Nat.Coprime (ℓ ^ j) (2 ^ f + 1) := fun j =>
    Nat.Coprime.pow_left j ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓq)
  have memD : ∀ β : MulAut P, ff β = 1 → β ∈ primeFormD h (C : Matrix (Fin 3) (Fin 3) F) :=
    fun β hβ => hker ▸ hβ
  have ffI : ∀ β ∈ inner P, ff β = 1 := fun β hβ => by
    have : β ∈ ff.ker := hker ▸ hIle hβ
    exact this
  have hDn : (primeFormD h (C : Matrix (Fin 3) (Fin 3) F)).Normal := hker ▸ ff.normal_ker
  have hφk : ff α ^ (ℓ ^ k) = 1 := by rw [← map_pow, ← hα, pow_orderOf_eq_one, map_one]
  have hφ1 : ff α ≠ 1 := by
    intro hφ
    exact hαI (mem_inner_of_mem_primeFormD_of_pow_eq_one h C (hcop k) (memD α hφ)
      (by rw [← hα]; exact pow_orderOf_eq_one α))
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hℓ).mp (orderOf_dvd_of_pow_eq_one hφk)
  have hj0 : j ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hj
    exact hφ1 hj
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  set α₀ : MulAut P := α ^ (ℓ ^ j') with hα₀
  have hφ₀ord : orderOf (ff α₀) = ℓ := by
    rw [hα₀, map_pow, orderOf_pow_of_dvd (pow_ne_zero _ hℓ.ne_zero)
      (by rw [hj]; exact pow_dvd_pow ℓ (Nat.le_succ j')), hj, pow_succ,
      Nat.mul_div_cancel_left _ (pow_pos hℓ.pos j')]
  have hα₀mem : α₀ ∈ Subgroup.zpowers α := Subgroup.pow_mem _ (Subgroup.mem_zpowers α) _
  have hα₀k : α₀ ^ (ℓ ^ k) = 1 := by
    rw [hα₀, pow_right_comm, ← hα, pow_orderOf_eq_one, one_pow]
  set g : MulAut P := primeFormFieldHom h hC (ff α₀) with hg
  have hffg : ff g = ff α₀ := by
    have := primeFormFieldFactor_apply h hC (le_refl 3) hq 1 (ff α₀)
    rwa [map_one, one_mul] at this
  have hφ₀1 : ff α₀ ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hφ₀ord
    exact hℓ.one_lt.ne hφ₀ord
  have hgℓ : g ^ ℓ = 1 := by
    rw [hg, ← map_pow, ← hφ₀ord, pow_orderOf_eq_one, map_one]
  have hg1 : g ≠ 1 := fun h1 => hφ₀1 (by rw [← hffg, h1, map_one])
  have hgord : orderOf g = ℓ := orderOf_eq_prime hgℓ hg1
  have hDmem : α₀ * g⁻¹ ∈ primeFormD h (C : Matrix (Fin 3) (Fin 3) F) := by
    rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hffg, mul_inv_cancel]
  have hgOut : orderOf (QuotientGroup.mk g : Outer P) = ℓ := by
    apply orderOf_eq_prime
    · rw [← QuotientGroup.mk_pow, hgℓ, QuotientGroup.mk_one]
    · intro h1
      exact hφ₀1 (by rw [← hffg]; exact ffI g ((QuotientGroup.eq_one_iff g).mp h1))
  have hα₀Out : orderOf (QuotientGroup.mk α₀ : Outer P) = ℓ := by
    have hα₀ℓ : α₀ ^ ℓ ∈ inner P := by
      refine mem_inner_of_mem_primeFormD_of_pow_eq_one h C (hcop k) (memD _ ?_) ?_
      · rw [map_pow, ← hφ₀ord, pow_orderOf_eq_one]
      · rw [← pow_mul, mul_comm, pow_mul, hα₀k, one_pow]
    apply orderOf_eq_prime
    · rw [← QuotientGroup.mk_pow]
      exact (QuotientGroup.eq_one_iff _).mpr hα₀ℓ
    · intro h1
      exact hφ₀1 (ffI α₀ ((QuotientGroup.eq_one_iff α₀).mp h1))
  obtain ⟨γ, hγ⟩ := exists_conj_mem_sup_zpowers_of_quotient (inner P)
    (primeFormD h (C : Matrix (Fin 3) (Fin 3) F)) hℓ
    (not_dvd_card_map_primeFormD h C hℓq) hgOut hα₀Out hDmem
  set y : MulAut P := γ * g * γ⁻¹ with hy
  have hyH : y ∈ inner P ⊔ Subgroup.zpowers α :=
    sup_le_sup_left (Subgroup.zpowers_le.mpr hα₀mem) _ hγ
  have hyo : orderOf y = ℓ := by
    rw [hy, ← hgord]
    exact (MulAut.conj γ).orderOf_eq g
  have hyI : y ∉ inner P := by
    intro hmem
    have h1 := ffI y hmem
    rw [hy, map_mul, map_mul, map_inv] at h1
    exact hφ₀1 (by rw [← hffg]; simpa using h1)
  obtain ⟨q, hqo, hqy⟩ := CFSG.HardMathSupport.C14Group.exists_fixed_of_order_p hℓ y
    (by rw [← hyo]; exact pow_orderOf_eq_one y) hdvd
  have hcenter : Subgroup.center P = ⊥ := CFSG.RankThree.PartOne.KCUnitaryRegular.center_primeFormP_eq_bot
    h hC (le_refl 3) hq
  have hxo : orderOf (MulAut.conj q : MulAut P) = ℓ := by
    apply orderOf_eq_prime
    · rw [← map_pow, ← hqo, pow_orderOf_eq_one, map_one]
    · intro h1
      have := (mulAutConj_eq_one_iff_mem_center q).mp h1
      rw [hcenter, Subgroup.mem_bot] at this
      rw [this, orderOf_one] at hqo
      exact hℓ.one_lt.ne hqo
  have hxI : (MulAut.conj q : MulAut P) ∈ inner P := ⟨q, rfl⟩
  refine ⟨MulAut.conj q, Subgroup.mem_sup_left hxI, y, hyH, hxo, hyo, ?_, ?_⟩
  · refine MulEquiv.ext fun z => ?_
    change q * (y z) * q⁻¹ = y (q * z * q⁻¹)
    rw [map_mul, map_mul, map_inv, hqy]
  · exact fun hmem => hyI (Subgroup.zpowers_le.mpr hxI hmem)

end Main

end CFSG.LocalAnalysis.RankThreeUC.S15.K518H
