module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63PCSpecC
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4P1CheckSpecC
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63PCRow

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
  CFSG.ComponentClassification.HarrisLit.P1 Certificates.Asc82Fbar

variable {n : ℕ} {A₀ : Subgroup (Equiv.Perm (Fin n))} {pg : Array Table}
  {gg : ℕ → Equiv.Perm (Fin n)} {sift : Table → Bool} {cap : ℕ} {runs : List Run}
  {good : List (Array Table)}

theorem small_chain_facts (hD : GroupData n A₀ pg gg sift) {r : Row} (hRF : RowFacts A₀ r.row)
    {first : Bool} {gs : List Table} {ord : ℕ} (hk : r.kind = .small gs ord)
    (h : rowOK n cap pg (pg.map (invT n)) sift runs good first r = true) :
    r.row.outer = false ∧ (∀ g ∈ gs, inCOK n sift r.row.rep g = true) ∧
      enumOK n cap ord gs = true ∧
      A₀ ⊓ centralizer ({tp n r.row.rep} : Set (Equiv.Perm (Fin n))) ≤
        normalizer (genOf n gs : Set (Equiv.Perm (Fin n))) := by
  have hn := hD.lt
  simp only [rowOK, hk, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq, beq_iff_eq,
    List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨houter, -⟩, -⟩, -⟩, -⟩, -⟩, hgs⟩, hcg⟩, henum⟩, hnorm⟩ := h
  refine ⟨houter, hgs, henum, ?_⟩
  rw [show A₀ ⊓ centralizer ({tp n r.row.rep} : Set (Equiv.Perm (Fin n))) = _ from
    hRF.cent.symm]
  exact normOK_spec hn (fun g hg => permOK_of_inCOK (hgs g hg)) henum
    (fun c hc => ⟨permOK_of_inCOK (hcg c hc), invOK_of_inCOK (hcg c hc)⟩) hnorm

theorem pocket_of_small (hD : GroupData n A₀ pg gg sift) {r : Row} (hRF : RowFacts A₀ r.row)
    {first : Bool} {gs : List Table} {ord : ℕ} (hk : r.kind = .small gs ord)
    (h : rowOK n cap pg (pg.map (invT n)) sift runs good first r = true) {rho : List Table}
    (hp : pocketOK n cap gs r.row.rep rho = true) : IsI4PlusIn A₀ (tp n r.row.rep) := by
  obtain ⟨-, hgs, henum, hN⟩ := small_chain_facts hD hRF hk h
  obtain ⟨K, hK, hKM, hKn, hSL⟩ := pocketOK_chain hD.lt hRF.rep hgs henum hp
  refine sec63PC_isI4PlusIn_of_chain hRF.ord hK hKM (genOf_le_of_inCOK hD hRF.rep hgs) hKn
    (fun m hm c hc => ?_) hSL
  exact (mem_normalizer_iff.mp (hN hc) m).mp hm

theorem outerOK_fact (hD : GroupData n A₀ pg gg sift) {NP : ℕ} {extra : List Table}
    (hCF : CheckFacts n NP cap pg sift runs extra) (hRun : ∀ R ∈ runs, RunFacts A₀ R)
    {l₁ l₂ : Table} {tg : Equiv.Perm (Fin n)} (hl₁ : permOK n l₁ = true)
    (hl₂ : permOK n l₂ = true) (hA : Sec63PCA6 A₀ tg (genOf n [l₁, l₂]))
    {d : Certificates.Asc82Fbar.OuterData} (h : outerOK n cap sift runs l₁ l₂ d = true) :
    Sec63PCFact A₀ tg := by
  have hn := hD.lt
  have hg2 : ∀ g ∈ [l₁, l₂], permOK n g = true := by
    intro g hg
    rcases List.mem_pair.mp hg with rfl | rfl
    · exact hl₁
    · exact hl₂
  simp only [outerOK] at h
  split at h
  next _ t₂ outer cs co cg op od gs ord heq =>
    obtain ⟨R, hRget, hrowget⟩ := Option.bind_eq_some_iff.mp heq
    obtain ⟨hi, hRi⟩ := List.getElem?_eq_some_iff.mp hRget
    obtain ⟨hj, hrj⟩ := List.getElem?_eq_some_iff.mp hrowget
    have hR : R ∈ runs := by
      rw [← hRi]
      exact List.getElem_mem hi
    have hrmem : (⟨⟨t₂, outer, cs, co, cg, op, od⟩, .small gs ord⟩ : Row) ∈ R.rows := by
      rw [← hrj]
      exact List.getElem_mem hj
    have hRF₂ := (hRun R hR).row _ hrmem
    have hrow := hCF.row d.run hi _ (by rw [List.getD_eq_getElem _ _ hi, hRi]; exact hrmem)
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨henum, hpb⟩, -⟩, -⟩, hall⟩, hpc⟩, hsc⟩, htb⟩, hpock⟩ := h
    have hpocket : IsI4PlusIn A₀ (tp n t₂) :=
      pocket_of_small hD (r := ⟨⟨t₂, outer, cs, co, cg, op, od⟩, .small gs ord⟩) hRF₂ rfl hrow hpock
    have hb : Rep n d.b (tp n d.b) := rep_tp hpb
    have hc : Rep n d.c (tp n d.c) := rep_tp hpc
    have hcA : tp n d.c ∈ A₀ := (hD.sift _ _ hc).1 hsc
    have hct : tp n d.c * tp n t₂ * (tp n d.c)⁻¹ = tp n d.b := by
      rw [mul_inv_eq_iff_eq_mul]
      exact (tblEq_iff_eq (Rep.compT hc hRF₂.rep) (Rep.compT hb hc)).1 htb
    have hpocketb : IsI4PlusIn A₀ (tp n d.b) := by
      have h1 := sec63PC_isI4PlusIn_conj hcA hpocket
      rwa [hct] at h1
    exact sec63PC_fact_outer hA (allInvConj_spec hn hg2 henum hb hall) hpocketb
  next => exact absurd h (by decide)

end CFSG.OddStandard.SmallF3.Omega
