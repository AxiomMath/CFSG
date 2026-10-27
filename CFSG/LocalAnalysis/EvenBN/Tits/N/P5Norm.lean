module

public import CFSG.LocalAnalysis.EvenBN.Tits.S56Coprime
public import CFSG.LocalAnalysis.EvenBN.Tits.S56Alg

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P5

open Subgroup
open scoped commutatorElement

theorem fixed_commutator_eq_one {W : Type*} [Group W] [Finite W] (hc : ∀ a b : W, a * b = b * a)
    (h2 : ∀ w : W, w * w = 1) (Q : Subgroup (MulAut W)) (hQ : Odd (Nat.card Q)) {c : W}
    (hcf : ∀ q ∈ Q, q c = c)
    (hcc : c ∈ Subgroup.closure {u : W | ∃ q ∈ Q, ∃ w : W, u = q w * w⁻¹}) : c = 1 := by
  letI : CommGroup W := { ‹Group W› with mul_comm := hc }
  haveI : Fintype Q := Fintype.ofFinite Q
  let Nm : W →* W :=
    { toFun := fun v => ∏ q : Q, (q : MulAut W) v
      map_one' := by simp
      map_mul' := fun a b => by simp [Finset.prod_mul_distrib] }
  have hNm : ∀ v, Nm v = ∏ q : Q, (q : MulAut W) v := fun v => rfl
  have ha : ∀ q' : Q, ∀ v, Nm ((q' : MulAut W) v) = Nm v := by
    intro q' v
    rw [hNm, hNm]
    have : ∀ q : Q, (q : MulAut W) ((q' : MulAut W) v) = ((q * q' : Q) : MulAut W) v := fun q => rfl
    simp only [this]
    exact Equiv.prod_comp (Equiv.mulRight q') (fun q : Q => (q : MulAut W) v)
  have hb : Nm c = c := by
    rw [hNm]
    have : ∀ q : Q, (q : MulAut W) c = c := fun q => hcf q q.2
    simp only [this, Finset.prod_const, Finset.card_univ]
    obtain ⟨k, hk⟩ := hQ
    rw [Fintype.card_eq_nat_card, hk, pow_succ, pow_mul]
    have : c ^ 2 = 1 := by rw [sq]; exact h2 c
    rw [this, one_pow, one_mul]
  have hker : Subgroup.closure {u : W | ∃ q ∈ Q, ∃ w : W, u = q w * w⁻¹} ≤ Nm.ker := by
    rw [Subgroup.closure_le]
    rintro u ⟨q, hq, w, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv]
    have := ha ⟨q, hq⟩ w
    simp only at this
    rw [this]
    exact mul_inv_cancel _
  have h1 : Nm c = 1 := MonoidHom.mem_ker.1 (hker hcc)
  rw [← hb, h1]

variable {Γ : Type*} [Group Γ]

theorem commutator_commutator_eq [Finite Γ] {p r : ℕ} [Fact p.Prime] [Fact r.Prime] (hpr : p ≠ r)
    {P X : Subgroup Γ} (hP : IsPGroup p P) (hX : IsPGroup r X)
    (hXP : X ≤ normalizer (P : Set Γ)) : ⁅(⁅P, X⁆ : Subgroup Γ), X⁆ = ⁅P, X⁆ := by
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro a ha b hb
    have hn : b ∈ normalizer ((⁅P, X⁆ : Subgroup Γ) : Set Γ) :=
      (CFSG.LocalAnalysis.EvenBN.Tits.S56.commutator_normalized P X) (mem_sup_right hb)
    have h1 : b * a⁻¹ * b⁻¹ ∈ (⁅P, X⁆ : Subgroup Γ) :=
      ((mem_normalizer_iff.1 hn) a⁻¹).1 (Subgroup.inv_mem _ ha)
    have e : ⁅a, b⁆ = a * (b * a⁻¹ * b⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact Subgroup.mul_mem _ ha h1
  · rw [Subgroup.commutator_le]
    intro q hq x hx
    obtain ⟨c, hc, k, hk, rfl⟩ :=
      CFSG.LocalAnalysis.EvenBN.Tits.S56.coprime_decomp_mem hpr hP hX hXP hq
    have hkx : k * x = x * k := (mem_centralizer_iff.1 (mem_inf.1 hk).2 x hx).symm
    have e : ⁅c * k, x⁆ = ⁅c, x⁆ := by
      simp only [commutatorElement_def]
      calc c * k * x * (c * k)⁻¹ * x⁻¹ = c * (k * x * k⁻¹) * c⁻¹ * x⁻¹ := by group
        _ = c * x * c⁻¹ * x⁻¹ := by rw [hkx]; group
    rw [e]
    exact Subgroup.commutator_mem_commutator hc hx

theorem centralizer_commutator_eq_bot [Finite Γ] {p r : ℕ} [Fact p.Prime] [Fact r.Prime]
    (hpr : p ≠ r) {P X : Subgroup Γ} (hP : IsPGroup p P) (hX : IsPGroup r X)
    (hXP : X ≤ normalizer (P : Set Γ)) (hab : IsMulCommutative (⁅P, X⁆ : Subgroup Γ)) :
    (⁅P, X⁆ : Subgroup Γ) ⊓ centralizer (X : Set Γ) = ⊥ := by
  have hle : (⁅P, X⁆ : Subgroup Γ) ≤ P := by
    rw [Subgroup.commutator_le]
    intro a ha x hx
    have h1 : x * a⁻¹ * x⁻¹ ∈ P := ((mem_normalizer_iff.1 (hXP hx)) a⁻¹).1 (Subgroup.inv_mem _ ha)
    have e : ⁅a, x⁆ = a * (x * a⁻¹ * x⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact Subgroup.mul_mem _ ha h1
  have hW : IsPGroup p (⁅P, X⁆ : Subgroup Γ) := hP.to_le hle
  have hXW : X ≤ normalizer ((⁅P, X⁆ : Subgroup Γ) : Set Γ) := fun x hx =>
    (CFSG.LocalAnalysis.EvenBN.Tits.S56.commutator_normalized P X) (mem_sup_right hx)
  have h := CFSG.LocalAnalysis.EvenBN.Tits.S56.centralizer_le_derived_of_commutator_eq hpr hW hX hXW
    (commutator_commutator_eq hpr hP hX hXP)
  rw [eq_bot_iff]
  refine h.trans ?_
  rw [Subgroup.commutator_le]
  intro a ha b hb
  have := hab.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
  have e : a * b = b * a := congrArg Subtype.val this
  rw [Subgroup.mem_bot]
  simp only [commutatorElement_def]
  calc a * b * a⁻¹ * b⁻¹ = b * a * a⁻¹ * b⁻¹ := by rw [e]
    _ = 1 := by group

end CFSG.LocalAnalysis.EvenBN.Tits.N.P5
