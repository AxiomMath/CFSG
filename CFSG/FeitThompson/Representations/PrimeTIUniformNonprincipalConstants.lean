module

public import CFSG.FeitThompson.Representations.PrimeTIDegreeSignCongruence
public import CFSG.FeitThompson.Representations.CoprimePowerPermutesIrreducibles
import CFSG.FeitThompson.Representations.CoprimePowerNonprincipalPrimeChars
import CFSG.FeitThompson.Representations.IrreducibleDegreeDividesOrder
import CFSG.FeitThompson.Representations.CoherentCoprimePowerEquivariance
import CFSG.FeitThompson.Representations.CyclicTIIsometryPowerEquivariance
import CFSG.FeitThompson.Representations.CyclicTIAxesNonrealConjugatePairs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

theorem IsCyclicTIPair.powOpₗ_basisProdIrr_principal_left {G : Type*} [Group G]
    {W W1 W2 : Subgroup G} (hW : IsCyclicTIPair W W1 W2) {k : ℕ} {j j' : Irr ↥W2}
    (hjj' : ∀ y : ↥W2, (j' : ↥W2 → ℂ) y = (j : ↥W2 → ℂ) (y ^ k)) :
    classFun.powOpₗ ↥W k (hW.basisProdIrr (principalIrr ↥W1, j))
      = hW.basisProdIrr (principalIrr ↥W1, j') := by
  refine Subtype.ext ?_
  rw [classFun.coe_powOpₗ_apply, IsCyclicTIPair.coe_basisProdIrr_apply,
    IsCyclicTIPair.coe_basisProdIrr_apply]
  funext z
  rw [powOp_apply, IsCyclicTIPair.prodChar_apply, IsCyclicTIPair.prodChar_apply, map_pow,
    Prod.pow_fst, Prod.pow_snd, coe_principalIrr, hjj']
  simp

variable {L : Type*} [Group L] {K W₁ W₂ : Subgroup L}
  {σ : classFun ↥(W₁ ⊔ W₂) →ₗ[ℂ] classFun L}

namespace IsPrimeCyclicTIHyp

theorem primeTISignInt_eq_of_primeTISign_eq (h : IsPrimeCyclicTIHyp K W₁ W₂) {j k : Irr ↥W₂}
    (hjk : h.primeTISign σ j = h.primeTISign σ k) :
    h.primeTISignInt σ j = h.primeTISignInt σ k := by
  have hc : ((h.primeTISignInt σ j : ℤ) : ℂ) = ((h.primeTISignInt σ k : ℤ) : ℂ) := by
    rw [h.intCast_primeTISignInt, h.intCast_primeTISignInt, hjk]
  exact_mod_cast hc

theorem exists_ne_principalIrr_right (h : IsPrimeCyclicTIHyp K W₁ W₂) :
    ∃ j : Irr ↥W₂, j ≠ principalIrr ↥W₂ := by
  have hfin := h.isCyclicTIPair.finite_right
  have h1 : 1 < Nat.card ↥W₂ := by
    have h2 : Nat.card ↥W₂ ≠ 1 := fun hc => h.right_ne_bot (Subgroup.card_eq_one.1 hc)
    have := Nat.card_pos (α := ↥W₂)
    omega
  have : Nontrivial (Irr ↥W₂) :=
    Finite.one_lt_card_iff_nontrivial.1 (by rw [h.isCyclicTIPair.card_Irr_right]; exact h1)
  exact exists_ne _

section Fintype

variable [Fintype L] [Fintype ↥(W₁ ⊔ W₂)]

theorem primeTISign_eq_of_ne_principal (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ) (hp : (Nat.card ↥W₂).Prime)
    {j j' : Irr ↥W₂} (hj : j ≠ principalIrr ↥W₂) (hj' : j' ≠ principalIrr ↥W₂) :
    h.primeTISign σ j' = h.primeTISign σ j ∧
      h.primeTIirr σ (principalIrr ↥W₁) j' 1 = h.primeTIirr σ (principalIrr ↥W₁) j 1 := by
  obtain ⟨k, hk1, hkL, hkey⟩ :=
    exists_pow_apply_eq_of_mem_Irr hp Nat.card_pos (Subgroup.card_subgroup_dvd_card W₂) rfl
      j.2 (coe_ne_one_of_ne_principalIrr hj) j'.2 (coe_ne_one_of_ne_principalIrr hj')
  have hpow := h.isCyclicTIPair.powOpₗ_basisProdIrr_principal_left (k := k) (j := j) (j' := j')
    hkey
  have hσpow := hσ.apply_powOpₗ h.isCyclicTIPair hk1 hkL
    (h.isCyclicTIPair.basisProdIrr (principalIrr ↥W₁, j))
  rw [hpow] at hσpow
  have hval : (σ (h.isCyclicTIPair.basisProdIrr (principalIrr ↥W₁, j')) : L → ℂ)
      = h.primeTISign σ j • powOp k (h.primeTIirr σ (principalIrr ↥W₁) j) := by
    rw [hσpow, classFun.coe_powOpₗ_apply,
      h.coe_apply_basisProdIrr_eq_smul_primeTIirr hσ (principalIrr ↥W₁) j, powOp_smul]
  have hIrr : powOp k (h.primeTIirr σ (principalIrr ↥W₁) j) ∈ Irr L :=
    powOp_mem_Irr hk1 hkL (h.primeTIirr_principal_left_mem_Irr hσ j)
  have h1 : h.primeTISign σ j' = h.primeTISign σ j := by
    refine (h.existsUnique_primeTISign hσ j').unique
      ⟨h.primeTISign_eq_one_or_eq_neg_one j', ?_⟩ ⟨h.primeTISign_eq_one_or_eq_neg_one j, ?_⟩
    · rw [← h.primeTIirr_principal_left]
      exact h.primeTIirr_principal_left_mem_Irr hσ j'
    · rw [hval, smul_smul, h.primeTISign_mul_self, one_smul]
      exact hIrr
  refine ⟨h1, ?_⟩
  have h2 : h.primeTIirr σ (principalIrr ↥W₁) j'
      = powOp k (h.primeTIirr σ (principalIrr ↥W₁) j) := by
    rw [h.primeTIirr_principal_left, hval, h1, smul_smul, h.primeTISign_mul_self, one_smul]
  rw [h2, powOp_apply_one]

theorem primeTIirr_one_ne_one (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ) (hW₂ : W₂ ≤ commutator L)
    {j : Irr ↥W₂} (hj : j ≠ principalIrr ↥W₂) :
    h.primeTIirr σ (principalIrr ↥W₁) j 1 ≠ 1 := by
  intro hone
  have hW := h.isCyclicTIPair
  have hcomm2 := hW.isMulCommutative_right
  obtain ⟨ν, hν⟩ := exists_monoidHom_units_eq_of_mem_Irr_of_apply_one_eq_one
    (h.primeTIirr_principal_left_mem_Irr hσ j) hone
  have hker : ∀ y : L, y ∈ W₂ → ν y = 1 :=
    fun y hy => MonoidHom.mem_ker.1 (Abelianization.commutator_subset_ker ν (hW₂ hy))
  obtain hb | ⟨x, hx, hx1⟩ := W₁.bot_or_exists_ne_one
  · exact h.left_ne_bot hb
  have hxW₂ : x ∉ W₂ := by
    intro hc
    have hmem : x ∈ W₁ ⊓ W₂ := Subgroup.mem_inf.2 ⟨hx, hc⟩
    rw [h.inf_left_right_eq_bot] at hmem
    exact hx1 (Subgroup.mem_bot.1 hmem)
  have hxval : h.primeTIirr σ (principalIrr ↥W₁) j x = h.primeTISign σ j := by
    rw [h.primeTIirr_apply_coe_left hσ (principalIrr ↥W₁) j (x := ⟨x, hx⟩)
      (fun hc => hx1 (by simpa using congrArg Subtype.val hc)), coe_principalIrr, Pi.one_apply,
      mul_one]
  have hall : ∀ y : ↥W₂, (j : ↥W₂ → ℂ) y = 1 := by
    intro y
    have hmemW : (x : L) * (y : L) ∈ W₁ ⊔ W₂ := Subgroup.mul_mem_sup hx y.2
    have hnot : (x : L) * (y : L) ∉ W₂ := by
      intro hc
      refine hxW₂ ?_
      have hxe : x = x * (y : L) * (y : L)⁻¹ := by group
      rw [hxe]
      exact W₂.mul_mem hc (W₂.inv_mem y.2)
    have hval := h.primeTIirr_apply_of_mem_primeTIset hσ (principalIrr ↥W₁) j
      (v := ⟨(x : L) * (y : L), hmemW⟩) (mem_primeTIset.2 ⟨hmemW, hnot⟩)
    have hprod : hW.prodChar ((principalIrr ↥W₁ : Irr ↥W₁) : ↥W₁ → ℂ) ((j : Irr ↥W₂) : ↥W₂ → ℂ)
        ⟨(x : L) * (y : L), hmemW⟩
          = ((principalIrr ↥W₁ : Irr ↥W₁) : ↥W₁ → ℂ) ⟨x, hx⟩ * ((j : Irr ↥W₂) : ↥W₂ → ℂ) y :=
      hW.prodChar_apply_mul _ _ hx y.2
    rw [hprod, coe_principalIrr, Pi.one_apply, one_mul] at hval
    have hhom : h.primeTIirr σ (principalIrr ↥W₁) j ((x : L) * (y : L))
        = h.primeTIirr σ (principalIrr ↥W₁) j x := by
      rw [← hν]
      simp only [map_mul, hker (y : L) y.2, mul_one]
    rw [hhom, hxval] at hval
    have hδ : h.primeTISign σ j ≠ 0 := by
      rcases h.primeTISign_eq_one_or_eq_neg_one (σ := σ) j with hd | hd <;> rw [hd] <;> norm_num
    field_simp at hval
    exact hval.symm
  exact hj (Subtype.ext (funext fun y => by rw [coe_principalIrr, Pi.one_apply, hall y]))

theorem exists_primeTIirr_constants (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ) (hLodd : Odd (Nat.card L))
    (hp : (Nat.card ↥W₂).Prime) (hW₂ : W₂ ≤ commutator L) :
    ∃ d : ℤ, Odd d ∧ 1 < d ∧ ∃ δ : ℤ, (δ = 1 ∨ δ = -1) ∧ ∃ n : ℤ, Even n ∧ 2 ≤ n ∧
      d - δ = n * (Nat.card ↥W₁ : ℤ) ∧
      ∀ i : Irr ↥W₁, ∀ j : Irr ↥W₂, j ≠ principalIrr ↥W₂ →
        h.primeTIirr σ i j 1 = (d : ℂ) ∧ h.primeTISignInt σ j = δ ∧
          h.primeTISign σ j = (δ : ℂ) := by
  obtain ⟨j₀, hj₀⟩ := h.exists_ne_principalIrr_right
  obtain ⟨d, -, hdval, hdmod⟩ := h.exists_primeTIirr_one_modEq hσ (principalIrr ↥W₁) j₀
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℤ, h.primeTISignInt σ j₀ = δ := ⟨_, rfl⟩
  rw [hδdef] at hdmod
  have hδpm : δ = 1 ∨ δ = -1 := hδdef ▸ h.primeTISignInt_eq_one_or_eq_neg_one (σ := σ) j₀
  have hδC : h.primeTISign σ j₀ = (δ : ℂ) := by rw [← h.intCast_primeTISignInt (σ := σ) j₀, hδdef]
  obtain ⟨d', -, hd'val, hd'dvd⟩ :=
    Irr.exists_degree (h.primeTIirr_mem_Irr hσ (principalIrr ↥W₁) j₀)
  have hdd' : d = d' := by
    have hc : ((d : ℕ) : ℂ) = ((d' : ℕ) : ℂ) := by rw [← hdval, hd'val]
    exact_mod_cast hc
  have hoddd : Odd d := hLodd.of_dvd_nat (hdd' ▸ hd'dvd)
  have hd1 : d ≠ 1 := fun hc =>
    h.primeTIirr_one_ne_one hσ hW₂ hj₀ (by rw [hdval, hc]; norm_num)
  have hdgt : 1 < (d : ℤ) := by
    obtain ⟨t, ht⟩ := hoddd
    omega
  obtain ⟨m, hm⟩ := hdmod.dvd
  have hn : (d : ℤ) - δ = (-m) * (Nat.card ↥W₁ : ℤ) := by linear_combination -hm
  have hcard1oddZ : Odd ((Nat.card ↥W₁ : ℤ)) := by
    exact_mod_cast Nat.Odd.of_mul_left h.odd_natCard
  have heven : Even ((d : ℤ) - δ) := by
    obtain ⟨t, ht⟩ := hoddd
    rcases hδpm with hp1 | hp1 <;> rw [hp1] <;> [exact ⟨t, by omega⟩; exact ⟨t + 1, by omega⟩]
  have hnEven : Even (-m) := by
    rw [hn] at heven
    rcases Int.even_mul.1 heven with he | he
    · exact he
    · exact absurd he (Int.not_even_iff_odd.2 hcard1oddZ)
  have hcardpos : 0 < (Nat.card ↥W₁ : ℤ) := by exact_mod_cast Nat.card_pos (α := ↥W₁)
  have hnpos : 0 < -m := by
    have hpos : 0 < (-m) * (Nat.card ↥W₁ : ℤ) := by
      rw [← hn]; rcases hδpm with hq | hq <;> omega
    rcases mul_pos_iff.1 hpos with ⟨hx, -⟩ | ⟨-, hy⟩
    · exact hx
    · omega
  refine ⟨(d : ℤ), by exact_mod_cast hoddd, hdgt, δ, hδpm, -m, hnEven, ?_, hn, ?_⟩
  · obtain ⟨t, ht⟩ := hnEven
    omega
  · intro i j hj
    obtain ⟨hs, hone⟩ := h.primeTISign_eq_of_ne_principal hσ hp hj₀ hj
    refine ⟨?_, ?_, by rw [hs, hδC]⟩
    · rw [h.primeTIirr_one i j, hone, hdval]
      push_cast
      ring
    · rw [← hδdef]
      exact h.primeTISignInt_eq_of_primeTISign_eq hs

end Fintype

end IsPrimeCyclicTIHyp

end CFSG.FeitThompson
