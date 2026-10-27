module

public import CFSG.FeitThompson.Representations.CyclicTIIsometryMixedSetValues
public import CFSG.FeitThompson.Representations.CoprimePowerPermutesIrreducibles
import CFSG.FeitThompson.Representations.CyclicTIIsometryUnique
import CFSG.FeitThompson.Representations.InductionCoprimePowerCommutes
import CFSG.FeitThompson.Representations.PowerOperationsPreserveVirtualChars

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

variable {G : Type*} [Group G] {W W1 W2 : Subgroup G} {k b : ℕ}

@[simp]
theorem classFun.powOpₗ_principalClassFun (X : Type*) [Group X] (k : ℕ) :
    classFun.powOpₗ X k (principalClassFun X) = principalClassFun X :=
  Subtype.ext <| by rw [classFun.coe_powOpₗ_apply, coe_principalClassFun, powOp_one_fun]

theorem classFun.powOpₗ_powOpₗ_eq_self [Finite G] (hkb : k * b ≡ 1 [MOD Nat.card G])
    (f : classFun G) : classFun.powOpₗ G b (classFun.powOpₗ G k f) = f :=
  Subtype.ext <| by
    rw [classFun.coe_powOpₗ_apply, classFun.coe_powOpₗ_apply, powOp_powOp_eq_self hkb]

theorem classFun.powOpₗ_powOpₗ_eq_self' [Finite G] (hkb : k * b ≡ 1 [MOD Nat.card G])
    (f : classFun G) : classFun.powOpₗ G k (classFun.powOpₗ G b f) = f :=
  classFun.powOpₗ_powOpₗ_eq_self (mul_comm k b ▸ hkb) f

theorem pow_mem_cyclicTIDiff_iff (hk : (Nat.card G).Coprime k) {x : G} (hx : x ∈ W) :
    x ^ k ∈ cyclicTIDiff W W1 W2 ↔ x ∈ cyclicTIDiff W W1 W2 := by
  simp only [mem_cyclicTIDiff]
  rw [pow_mem_iff_of_coprime_natCard W1 hk, pow_mem_iff_of_coprime_natCard W2 hk]
  simp [W.pow_mem hx, hx]

variable [Fintype G] [Fintype W] {σ : classFun ↥W →ₗ[ℂ] classFun G}

theorem IsCyclicTIIsometry.powOpₗ_comp (hσ : IsCyclicTIIsometry W W1 W2 σ)
    (hk1 : 1 ≤ k) (hk : k.Coprime (Nat.card G)) (hb1 : 1 ≤ b)
    (hkb : k * b ≡ 1 [MOD Nat.card G]) :
    IsCyclicTIIsometry W W1 W2
      ((classFun.powOpₗ G b).comp (σ.comp (classFun.powOpₗ ↥W k))) := by
  have hkW : k.Coprime (Nat.card ↥W) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_subgroup_dvd_card W) hk
  have hb : b.Coprime (Nat.card G) := coprime_right_of_mul_modEq_one hkb
  constructor
  ·
    intro f h
    simp only [LinearMap.comp_apply]
    rw [cfInner_powOpₗ_powOpₗ hb, hσ.inner_eq, cfInner_powOpₗ_powOpₗ hkW]
  ·
    intro f hf
    simp only [LinearMap.comp_apply, classFun.coe_powOpₗ_apply]
    refine mem_virtualChars_of_mem_span_Irr (powOp_mem_span_Irr hb1 ?_)
    refine mem_span_Irr_of_mem_virtualChars (hσ.map_virtualChars _ ?_)
    rw [classFun.coe_powOpₗ_apply]
    exact mem_virtualChars_of_mem_span_Irr
      (powOp_mem_span_Irr hk1 (mem_span_Irr_of_mem_virtualChars hf))
  ·
    simp only [LinearMap.comp_apply]
    rw [classFun.powOpₗ_principalClassFun, hσ.map_principalClassFun,
      classFun.powOpₗ_principalClassFun]
  ·
    intro f hf
    simp only [LinearMap.comp_apply, classFun.coe_powOpₗ_apply]
    have hvan : ∀ x : ↥W, (x : G) ∉ cyclicTIDiff W W1 W2 →
        (classFun.powOpₗ ↥W k f : ↥W → ℂ) x = 0 := by
      intro x hx
      rw [classFun.coe_powOpₗ_apply, powOp_apply]
      refine hf _ fun hmem => hx ?_
      rw [SubgroupClass.coe_pow] at hmem
      exact (pow_mem_cyclicTIDiff_iff hk.symm x.2).1 hmem
    rw [hσ.eq_indClassFun _ hvan, classFun.coe_powOpₗ_apply,
      ← powOp_indClassFun W hk.symm, powOp_powOp_eq_self hkb]

theorem IsCyclicTIIsometry.apply_powOpₗ (hW : IsCyclicTIPair W W1 W2)
    (hσ : IsCyclicTIIsometry W W1 W2 σ) (hk1 : 1 ≤ k) (hk : k.Coprime (Nat.card G))
    (f : classFun ↥W) :
    σ (classFun.powOpₗ ↥W k f) = classFun.powOpₗ G k (σ f) := by
  obtain ⟨b, hb1, hkb⟩ := exists_one_le_mul_modEq_one (G := G) hk1 hk
  have heq := hσ.apply_eq_of_isCyclicTIIsometry hW (hσ.powOpₗ_comp hk1 hk hb1 hkb) f
  simp only [LinearMap.comp_apply] at heq
  rw [heq, classFun.powOpₗ_powOpₗ_eq_self' hkb]

theorem IsCyclicTIIsometry.comp_powOpₗ (hW : IsCyclicTIPair W W1 W2)
    (hσ : IsCyclicTIIsometry W W1 W2 σ) (hk1 : 1 ≤ k) (hk : k.Coprime (Nat.card G)) :
    σ.comp (classFun.powOpₗ ↥W k) = (classFun.powOpₗ G k).comp σ :=
  LinearMap.ext fun f => hσ.apply_powOpₗ hW hk1 hk f

theorem IsCyclicTIIsometry.coe_apply_powOpₗ (hW : IsCyclicTIPair W W1 W2)
    (hσ : IsCyclicTIIsometry W W1 W2 σ) (hk1 : 1 ≤ k) (hk : k.Coprime (Nat.card G))
    (f : classFun ↥W) :
    (σ (classFun.powOpₗ ↥W k f) : G → ℂ) = powOp k (σ f : G → ℂ) := by
  rw [hσ.apply_powOpₗ hW hk1 hk f, classFun.coe_powOpₗ_apply]

theorem IsCyclicTIIsometry.apply_powOpₗ_apply (hW : IsCyclicTIPair W W1 W2)
    (hσ : IsCyclicTIIsometry W W1 W2 σ) (hk1 : 1 ≤ k) (hk : k.Coprime (Nat.card G))
    (f : classFun ↥W) (x : G) :
    (σ (classFun.powOpₗ ↥W k f) : G → ℂ) x = (σ f : G → ℂ) (x ^ k) := by
  rw [hσ.coe_apply_powOpₗ hW hk1 hk f, powOp_apply]

end CFSG.FeitThompson
