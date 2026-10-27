module

public import CFSG.LocalAnalysis.EvenBN.U5.CaseBParts
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsU5Base

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Blueprint
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient
open scoped MatrixGroups


namespace CaseBPModelN3

open CFSG.RankThree.PartOne.U5K.Hyp OuterInvolution

section Fixed

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

theorem map_oddUni_zero_of_fixed {σ : K ≃+* K} {Y : Matrix (Fin 2) (Fin 2) K}
    (hY : ∀ i j, σ (Y i j) = Y i j) : (oddUni h 0 Y).map σ = oddUni h 0 Y := by
  ext p q
  rcases p with i | k | j <;> rcases q with i' | k' | j' <;> simp [oddUni, Matrix.one_apply, hY]

@[expose] def symF (t : h.fixedField × h.fixedField × h.fixedField) : Matrix (Fin 2) (Fin 2) K :=
  !![(t.1 : K), (t.2.1 : K); (t.2.1 : K), (t.2.2 : K)]

theorem isHerm_symF (t : h.fixedField × h.fixedField × h.fixedField) : IsHerm h (symF h t) := by
  rw [isHerm_iff]
  have ha : h.bar (t.1 : K) = t.1 := t.1.2
  have hb : h.bar (t.2.1 : K) = t.2.1 := t.2.1.2
  have hc : h.bar (t.2.2 : K) = t.2.2 := t.2.2.2
  simp [symF, ha, hb, hc]

theorem exists_family_Vhat :
    ∃ ι : (h.fixedField × h.fixedField × h.fixedField) → hypPSU h 2 1,
      Function.Injective ι ∧ (∀ t, ι t ∈ (Vsub h).map (hypProj h 2 1)) ∧
      ∀ σ : K ≃+* K, (∀ c, σ c = h.bar c) → ∀ t, Phi h (fieldElt h σ) (ι t) = ι t := by
  choose g hgV hgm using fun t => exists_mem_Vsub (hK := h) (isHerm_symF h t)
  refine ⟨fun t => hypProj h 2 1 (g t), ?_, fun t => ⟨g t, hgV t, rfl⟩, ?_⟩
  · intro t t' e
    have hU : (g t)⁻¹ * g t' ∈ hypUnitriangular h 2 1 :=
      mul_mem (inv_mem (hgV t).1) (hgV t').1
    have hS : (g t)⁻¹ * g t' ∈ hypScalars h 2 1 := by
      rw [← ker_hypProj h 2 1, MonoidHom.mem_ker, map_mul, map_inv]
      exact inv_mul_eq_one.2 e
    have h1 : (g t)⁻¹ * g t' ∈ hypUnitriangular h 2 1 ⊓ hypScalars h 2 1 :=
      Subgroup.mem_inf.2 ⟨hU, hS⟩
    rw [Usub_inf_scalars, Subgroup.mem_bot, inv_mul_eq_one] at h1
    have h3 : oddUni h 0 (symF h t) = oddUni h 0 (symF h t') := by
      rw [← hgm t, ← hgm t', h1]
    have h2 : symF h t = symF h t' := (oddUni_inj h3).2
    have e00 : (t.1 : K) = t'.1 := by simpa [symF] using congrFun (congrFun h2 0) 0
    have e01 : (t.2.1 : K) = t'.2.1 := by simpa [symF] using congrFun (congrFun h2 0) 1
    have e11 : (t.2.2 : K) = t'.2.2 := by simpa [symF] using congrFun (congrFun h2 1) 1
    exact Prod.ext (Subtype.ext e00) (Prod.ext (Subtype.ext e01) (Subtype.ext e11))
  · intro σ hσ t
    have ha : σ (t.1 : K) = t.1 := by rw [hσ]; exact t.1.2
    have hb : σ (t.2.1 : K) = t.2.1 := by rw [hσ]; exact t.2.1.2
    have hc : σ (t.2.2 : K) = t.2.2 := by rw [hσ]; exact t.2.2.2
    have hfix : act h (fieldElt h σ) (g t) = g t := by
      apply mat_injective
      rw [mat_act_fieldElt, hgm]
      exact map_oddUni_zero_of_fixed h (fun i j => by
        fin_cases i <;> fin_cases j <;> simp [symF, ha, hb, hc])
    show Phi h (fieldElt h σ) (hypProj h 2 1 (g t)) = hypProj h 2 1 (g t)
    rw [Phi_apply, hfix]

theorem Vhat_comm_sq :
    (∀ x ∈ (Vsub h).map (hypProj h 2 1), ∀ y ∈ (Vsub h).map (hypProj h 2 1), x * y = y * x) ∧
      ∀ x ∈ (Vsub h).map (hypProj h 2 1), x * x = 1 := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨v, hv, rfl⟩ _ ⟨v', hv', rfl⟩
    rw [← map_mul, ← map_mul, Vsub_comm hv hv']
  · rintro _ ⟨v, hv, rfl⟩
    rw [← map_mul, Vsub_sq hv, map_one]

theorem exists_elemAb_fixed_of_outer {θ : MulAut (hypPSU h 2 1)} (hθ : θ * θ = 1)
    (hθP : θ ∉ Pi h) :
    ∃ E : Subgroup (hypPSU h 2 1), CFSG.IsElementaryAbelian 2 E ∧ (∀ x ∈ E, θ x = x) ∧
      (2 ^ f) ^ 3 ≤ Nat.card E := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := finite_hypPSU h
  obtain ⟨σ, hσ, β, -, rfl⟩ := exists_eq_conj_fieldElt hθ hθP
  obtain ⟨ι, hinj, hιV, hιfix⟩ := exists_family_Vhat h
  set u := Phi h (fieldElt h σ) with hu
  set E₁ : Subgroup (hypPSU h 2 1) :=
    (Vsub h).map (hypProj h 2 1) ⊓ MonoidHom.eqLocus u.toMonoidHom (MonoidHom.id _) with hE₁
  have hmem : ∀ t, ι t ∈ E₁ := fun t => Subgroup.mem_inf.2 ⟨hιV t, hιfix σ hσ t⟩
  haveI hE₁e : CFSG.IsElementaryAbelian 2 E₁ := isElementaryAbelian_of_forall
    (fun x hx y hy => (Vhat_comm_sq h).1 x (Subgroup.mem_inf.1 hx).1 y (Subgroup.mem_inf.1 hy).1)
    (fun x hx => (Vhat_comm_sq h).2 x (Subgroup.mem_inf.1 hx).1)
  refine ⟨E₁.map β.toMonoidHom, CFSG.IsElementaryAbelian.map _, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    have hy' : u y = y := (Subgroup.mem_inf.1 hy).2
    simp [MulAut.mul_apply, MulAut.inv_apply, hy']
  · rw [Subgroup.card_map_of_injective (f := β.toMonoidHom) β.injective]
    calc (2 ^ f) ^ 3 = Nat.card (h.fixedField × h.fixedField × h.fixedField) := by
          rw [Nat.card_prod, Nat.card_prod, h.card_fixedField]; ring
      _ ≤ Nat.card E₁ := Nat.card_le_card_of_injective (fun t => (⟨ι t, hmem t⟩ : E₁))
          (fun a b e => hinj (congrArg Subtype.val e))

theorem exists_elemAb_fixed_of_inner (hf : 2 ≤ f) (hZ : Subgroup.center (hypPSU h 2 1) = ⊥)
    {z : hypPSU h 2 1} (hz : z * z = 1) :
    ∃ E : Subgroup (hypPSU h 2 1), CFSG.IsElementaryAbelian 2 E ∧
      (∀ x ∈ E, MulAut.conj z x = x) ∧ (2 ^ f) ^ 3 ≤ Nat.card E := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := finite_hypPSU h
  obtain ⟨w, hw⟩ := involutionsConjIntoV h hf hZ z hz
  obtain ⟨ι, hinj, hιV, -⟩ := exists_family_Vhat h
  haveI hÊe : CFSG.IsElementaryAbelian 2 ((Vsub h).map (hypProj h 2 1)) :=
    isElementaryAbelian_of_forall (Vhat_comm_sq h).1 (Vhat_comm_sq h).2
  refine ⟨((Vsub h).map (hypProj h 2 1)).map (MulAut.conj w).toMonoidHom,
    CFSG.IsElementaryAbelian.map _, ?_, ?_⟩
  · rintro _ ⟨e, he, rfl⟩
    have hc := (Vhat_comm_sq h).1 _ hw e he
    have key : z * (w * e * w⁻¹) = (w * e * w⁻¹) * z := by
      calc z * (w * e * w⁻¹) = w * ((w⁻¹ * z * w) * e) * w⁻¹ := by group
        _ = w * (e * (w⁻¹ * z * w)) * w⁻¹ := by rw [hc]
        _ = (w * e * w⁻¹) * z := by group
    simpa [MulAut.conj_apply] using mul_inv_eq_iff_eq_mul.2 key
  · rw [Subgroup.card_map_of_injective (f := (MulAut.conj w).toMonoidHom) (MulAut.conj w).injective]
    calc (2 ^ f) ^ 3 = Nat.card (h.fixedField × h.fixedField × h.fixedField) := by
          rw [Nat.card_prod, Nat.card_prod, h.card_fixedField]; ring
      _ ≤ Nat.card ((Vsub h).map (hypProj h 2 1)) :=
          Nat.card_le_card_of_injective (fun t => (⟨ι t, hιV t⟩ : (Vsub h).map (hypProj h 2 1)))
            (fun a b e => hinj (congrArg Subtype.val e))

end Fixed

end CaseBPModelN3

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

theorem involutoryFixedElemAb_of_hyp : CaseBParts.InvolutoryFixedElemAbStatement := by
  intro f K _ h hf θ hθ
  have hZ : Subgroup.center (hypPSU h 2 1) = ⊥ := CFSG.Quasithin.H13.Sec53F.Unit.u5_center_eq_bot h
  by_cases hθP : θ ∈ CFSG.RankThree.PartOne.U5K.Hyp.Pi h
  · obtain ⟨z, rfl⟩ := hθP
    have hz : z * z = 1 := by
      have hc : z * z ∈ Subgroup.center (hypPSU h 2 1) := by
        rw [Subgroup.mem_center_iff]
        intro y
        have := congrArg (fun a : MulAut (hypPSU h 2 1) => a y) hθ
        simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.one_apply] at this
        calc y * (z * z) = (z * (z * y * z⁻¹) * z⁻¹) * (z * z) := by rw [this]
          _ = z * z * y := by group
      rw [hZ, Subgroup.mem_bot] at hc
      exact hc
    obtain ⟨E, hE, hfix, hcard⟩ := CaseBPModelN3.exists_elemAb_fixed_of_inner h hf hZ hz
    exact ⟨E, hE, hfix, hcard⟩
  · obtain ⟨E, hE, hfix, hcard⟩ := CaseBPModelN3.exists_elemAb_fixed_of_outer h hθ hθP
    exact ⟨E, hE, hfix, hcard⟩

end Data

namespace CaseBParts

theorem involutoryFixedElemAb : InvolutoryFixedElemAbStatement :=
  Data.involutoryFixedElemAb_of_hyp

end CaseBParts

end CFSG.LocalAnalysis.EvenBN.U5
