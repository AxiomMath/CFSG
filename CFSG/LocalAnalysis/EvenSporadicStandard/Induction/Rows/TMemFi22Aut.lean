module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.TMemFi22
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.TMemFi22Facts

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Monster.B.Fischer CFSG.Sporadic.FischerOddCore CFSG.Blueprint.NativeSporadic
  CFSG.Sporadic.SmallOddCore CFSG.EvenSporadicStandard.Solomon78
  CFSG.EvenSporadicStandard.HypOne.Fi22 CFSG.EvenSporadicStandard.Induction.TMemFi22Cert


theorem fi22AutFixInner_proved : Fi22AutFixInner := by
  intro Y _ hY uY hu2 hcard β hβ
  obtain ⟨e⟩ := hY
  have : Finite Y := Finite.of_equiv _ (e.trans fi22PermEquiv).symm.toEquiv
  have hL : IsSporadic ↥(⊤ : Subgroup Y) .Fi22 := ⟨Subgroup.topEquiv.trans e⟩
  have hKu : ∀ k ∈ centralizer ({uY} : Set Y), k * uY = uY * k := fun k hk =>
    mem_centralizer_singleton_iff.1 hk
  obtain ⟨Φ, hΦu, hΦK⟩ := exists_equiv_fi22 (L := (⊤ : Subgroup Y))
    (K := centralizer ({uY} : Set Y)) hL (Subgroup.mem_top uY) hu2 le_top hKu hcard
  let E : Y ≃* ↥fi22P := Subgroup.topEquiv.symm.trans Φ
  have hEu : E uY = ⟨fi22ExtRep 2, fi22ExtRep_two_mem⟩ := hΦu
  have hEC : ∀ y : Y, y ∈ centralizer ({uY} : Set Y) ↔
      E y ∈ centralizer ({(⟨fi22ExtRep 2, fi22ExtRep_two_mem⟩ : ↥fi22P)} : Set ↥fi22P) := by
    intro y
    have := hΦK ⟨y, Subgroup.mem_top y⟩
    rw [Subgroup.mem_subgroupOf] at this
    exact this
  let β' : MulAut ↥fi22P := (E.symm.trans (β.trans E))
  obtain ⟨x, hxR, hx⟩ := (fi22_autModel).surj β'
  have hβ'fix : ∀ c ∈ centralizer ({(⟨fi22ExtRep 2, fi22ExtRep_two_mem⟩ : ↥fi22P)} :
      Set ↥fi22P), β' c = c := by
    intro c hc
    have h1 : E.symm c ∈ centralizer ({uY} : Set Y) := by
      rw [hEC, MulEquiv.apply_symm_apply]
      exact hc
    show E (β (E.symm c)) = c
    rw [hβ _ h1, MulEquiv.apply_symm_apply]
  obtain ⟨c₁, c₂, hc₁P, hc₂P, hc₁t, hc₂t, hcent⟩ := tmFi22_facts
  have hxc : ∀ c ∈ centralizer ({(⟨fi22ExtRep 2, fi22ExtRep_two_mem⟩ : ↥fi22P)} : Set ↥fi22P),
      x * (c : Equiv.Perm (Fin 3510)) = (c : Equiv.Perm (Fin 3510)) * x := by
    intro c hc
    have h1 := hx c
    rw [hβ'fix c hc] at h1
    calc x * (c : Equiv.Perm (Fin 3510)) = (x * (c : Equiv.Perm (Fin 3510)) * x⁻¹) * x := by group
      _ = (c : Equiv.Perm (Fin 3510)) * x := by rw [← h1]
  have hcj : ∀ (c : Equiv.Perm (Fin 3510)) (hcP : c ∈ fi22P),
      c * fi22ExtRep 2 = fi22ExtRep 2 * c →
        x * c = c * x := by
    intro c hcP hct
    exact hxc ⟨c, hcP⟩ (mem_centralizer_singleton_iff.2 (Subtype.ext hct))
  have hxP : x ∈ fi22P := by
    rcases hcent x (hcj c₁ hc₁P hc₁t) (hcj c₂ hc₂P hc₂t) with rfl | rfl
    · exact fi22P.one_mem
    · exact fi22ExtRep_two_mem
  refine ⟨E.symm ⟨x, hxP⟩, ?_⟩
  ext y
  have h1 : (β' (E y) : ↥fi22P) = ⟨x, hxP⟩ * E y * ⟨x, hxP⟩⁻¹ := Subtype.ext (hx (E y))
  have h2 : E (β y) = ⟨x, hxP⟩ * E y * ⟨x, hxP⟩⁻¹ := by
    rw [← h1]
    show E (β y) = E (β (E.symm (E y)))
    rw [MulEquiv.symm_apply_apply]
  have h3 : β y = E.symm (⟨x, hxP⟩ * E y * ⟨x, hxP⟩⁻¹) := by
    rw [← h2, MulEquiv.symm_apply_apply]
  rw [h3, map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply]
  rfl


section Final


theorem tMemOfNotMax_fi22_final :
    TMemOfNotMax [.Fi22] (fun _ => fiLoc 18393661440) :=
  tMemOfNotMax_fi22_proved fi22AutFixInner_proved

end Final

end CFSG.EvenSporadicStandard.Induction
