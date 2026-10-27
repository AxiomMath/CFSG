module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesRankPCrit
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesRankPCover
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesRankPElem

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.RankP

open Subgroup
open scoped commutatorElement

theorem three_le_pRank_of_case2 {f p : ℕ} (hf : f.Prime) (hp : p.Prime) (hf3 : 3 ≤ f)
    (hfp : f < p) {X : Type*} [Group X] [Finite X] {O L E : Subgroup X} [O.Normal] [L.Normal]
    (hOp : ¬ p ∣ Nat.card O) (hE : IsPGroup f E)
    (hfrat : ∀ g : X, ∃ n ∈ normalizer (E : Set X), ∃ o ∈ O, g = n * o)
    (hH : ∀ h ∈ L, (∀ e ∈ E, h * e = e * h) → h ∈ O) (P : Sylow p X)
    (hPnc : ¬ ∀ a ∈ (P : Subgroup X), ∀ b ∈ (P : Subgroup X), a * b = b * a)
    (h3 : ∀ w ∈ (P : Subgroup X), (∀ b ∈ (P : Subgroup X), w * b = b * w) → w ^ p = 1 → w ∈ L)
    {y : X} (hy : orderOf y = f) (hyE : y ∈ normalizer (E : Set X)) :
    3 ≤ CFSG.Open.pRank f (Subgroup.centralizer ({y} : Set X)) := by
  haveI := Fact.mk hf
  haveI := Fact.mk hp
  obtain ⟨P', hP'N⟩ := exists_sylow_le_of_cover p hOp hfrat
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X P' P
  have hconj : ∀ a ∈ (P' : Subgroup X), g * a * g⁻¹ ∈ (P : Subgroup X) := by
    intro a ha
    rw [← hg, Sylow.coe_subgroup_smul]
    exact ⟨a, ha, rfl⟩
  have hconj' : ∀ b ∈ (P : Subgroup X), g⁻¹ * b * g ∈ (P' : Subgroup X) := by
    intro b hb
    rw [← hg, Sylow.coe_subgroup_smul] at hb
    obtain ⟨a, ha, rfl⟩ := hb
    show g⁻¹ * (g * a * g⁻¹) * g ∈ (P' : Subgroup X)
    rwa [show g⁻¹ * (g * a * g⁻¹) * g = a by group]
  have hnc' : ¬ ∀ a ∈ (P' : Subgroup X), ∀ b ∈ (P' : Subgroup X), a * b = b * a := by
    intro h
    apply hPnc
    intro a ha b hb
    have h1 := h _ (hconj' a ha) _ (hconj' b hb)
    calc a * b = g * ((g⁻¹ * a * g) * (g⁻¹ * b * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * b * g) * (g⁻¹ * a * g)) * g⁻¹ := by rw [h1]
      _ = b * a := by group
  have h3' : ∀ w ∈ (P' : Subgroup X), (∀ b ∈ (P' : Subgroup X), w * b = b * w) → w ^ p = 1 →
      w ∈ L := by
    intro w hw hcentral hwp
    have hwP : g * w * g⁻¹ ∈ (P : Subgroup X) := hconj w hw
    have hcP : ∀ b ∈ (P : Subgroup X), (g * w * g⁻¹) * b = b * (g * w * g⁻¹) := by
      intro b hb
      have := hcentral _ (hconj' b hb)
      calc (g * w * g⁻¹) * b = g * (w * (g⁻¹ * b * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * b * g) * w) * g⁻¹ := by rw [this]
        _ = b * (g * w * g⁻¹) := by group
    have hpow : (g * w * g⁻¹) ^ p = 1 := by rw [conj_pow, hwp]; simp
    have hL := h3 _ hwP hcP hpow
    have := (inferInstance : L.Normal).conj_mem _ hL g⁻¹
    rwa [show g⁻¹ * (g * w * g⁻¹) * g⁻¹⁻¹ = w by group] at this
  have hfaith : ∀ a ∈ (P' : Subgroup X), (∀ e ∈ E, a * e = e * a) → a = 1 := by
    intro a ha hae
    by_contra hne
    let K : Subgroup (P' : Subgroup X) :=
      { carrier := {k | ∀ e ∈ E, (k : X) * e = e * k}
        mul_mem' := fun {k₁ k₂} h₁ h₂ e he => by
          show (k₁ : X) * k₂ * e = e * (k₁ * k₂)
          rw [mul_assoc, h₂ e he, ← mul_assoc, h₁ e he, mul_assoc]
        one_mem' := fun e he => by simp
        inv_mem' := fun {k} h e he => by
          show (k : X)⁻¹ * e = e * (k : X)⁻¹
          have := h e he
          calc (k : X)⁻¹ * e = (k : X)⁻¹ * (e * k) * (k : X)⁻¹ := by group
            _ = (k : X)⁻¹ * (k * e) * (k : X)⁻¹ := by rw [this]
            _ = e * (k : X)⁻¹ := by group }
    haveI : K.Normal := ⟨fun k hk q e he => by
      show ((q * k * q⁻¹ : P') : X) * e = e * ((q * k * q⁻¹ : P') : X)
      have hq : (q : X) ∈ normalizer (E : Set X) := hP'N q.2
      have he' : (q : X)⁻¹ * e * q ∈ E := by
        have := (Subgroup.mem_normalizer_iff.mp (inv_mem hq) e).mp he
        simpa using this
      have hk' := hk _ he'
      calc ((q * k * q⁻¹ : P') : X) * e = q * (k * ((q : X)⁻¹ * e * q)) * (q : X)⁻¹ := by
            simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
        _ = q * (((q : X)⁻¹ * e * q) * k) * (q : X)⁻¹ := by rw [hk']
        _ = e * ((q * k * q⁻¹ : P') : X) := by
            simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group⟩
    have hKne : K ≠ ⊥ := by
      intro hbot
      have : (⟨a, ha⟩ : (P' : Subgroup X)) ∈ K := fun e he => hae e he
      rw [hbot, Subgroup.mem_bot] at this
      exact hne (congrArg Subtype.val this)
    obtain ⟨w, hwK, hwZ, hwp, hw1⟩ := exists_ne_one_mem_inf_center P'.isPGroup' K hKne
    have hwX : (w : X) ∈ L := h3' w w.2 (fun b hb => by
      have := mem_center_iff.mp hwZ ⟨b, hb⟩
      exact congrArg Subtype.val this.symm) (by simpa using congrArg Subtype.val hwp)
    have hwO : (w : X) ∈ O := hH w hwX hwK
    have hord : orderOf (w : X) = p := by
      refine orderOf_eq_prime (by simpa using congrArg Subtype.val hwp) ?_
      intro h
      exact hw1 (Subtype.ext h)
    apply hOp
    rw [← hord]
    exact Subgroup.orderOf_dvd_natCard O hwO
  obtain ⟨D, hDE, hDnorm, hDexp, hDcl, hDdim⟩ := exists_critical_big hf hp hf3 hfp hE
    (P'.isPGroup') hP'N hfaith hnc'
  exact step0 hf hf3 hDexp hDcl hDdim hy (hDnorm y hyE)

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.RankP
