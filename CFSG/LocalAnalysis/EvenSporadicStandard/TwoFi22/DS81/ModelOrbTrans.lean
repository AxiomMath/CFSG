module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelOrbAct
public import Certificates.Certificate25270
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelGenUpper

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Gen

open Subgroup CFSG.Sporadic.Fi23 FrameJ CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open scoped Pointwise

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

set_option linter.unusedSectionVars false

section



@[expose] noncomputable def pg (j : Fin 23) : Fin 3510 :=
  Function.invFun (fun x : Fin 3510 => (ptE x : J)) (fjPt j)

theorem ptE_pg {j : Fin 23} (hj : j ≠ 0) : (ptE (pg j) : J) = fjPt j := by
  obtain ⟨x, hx⟩ := ptE.surjective ⟨fjPt j, fjPt_star hj⟩
  exact Function.invFun_eq (f := fun x : Fin 3510 => (ptE x : J))
    ⟨x, congrArg Subtype.val hx⟩

theorem pg_mem_uPts {j : Fin 23} (hj : j ≠ 0) : pg j ∈ uPts :=
  mem_uPts_iff.2 ⟨j, hj, ptE_pg hj⟩

theorem pg_injOn : Set.InjOn pg {j | j ≠ 0} := by
  intro j hj j' hj' h
  apply fjPt_injective
  rw [← ptE_pg hj, ← ptE_pg hj', h]

theorem image_pg_mem {S : Finset (Fin 23)} (hS : ∀ j ∈ S, j ≠ 0) {k : ℕ} (hk : S.card = k) :
    S.image pg ∈ uPts.powersetCard k := by
  rw [Finset.mem_powersetCard]
  refine ⟨?_, ?_⟩
  · intro x hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hx
    exact pg_mem_uPts (hS j hj)
  · rw [Finset.card_image_of_injOn (fun j hj j' hj' h => pg_injOn (hS j hj) (hS j' hj') h), hk]

theorem image_eq_of_smul {n : normalizer (E0 : Set Cd)} {σ : Equiv.Perm (Fin 23)}
    (hσ : IsPerm (n : Cd) σ) {S S' : Finset (Fin 23)} (hS : ∀ j ∈ S, j ≠ 0)
    (hS' : ∀ j ∈ S', j ≠ 0) (hcard : S.card = S'.card)
    (h : n • S.image pg = S'.image pg) : S.image σ = S' := by
  apply Finset.eq_of_subset_of_card_le
  · intro j' hj'
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hj'
    have h1 : n • pg j ∈ n • S.image pg :=
      Finset.smul_mem_smul_finset (Finset.mem_image_of_mem _ hj)
    rw [h] at h1
    obtain ⟨j'', hj'', hjj⟩ := Finset.mem_image.1 h1
    have e1 : (ptE (n • pg j) : J) = (n : J) * ptE (pg j) * (n : J)⁻¹ :=
      ptE_smul (n : Cd) (pg j)
    rw [← hjj, ptE_pg (hS' j'' hj''), ptE_pg (hS j hj), hσ j] at e1
    have : σ j = j'' := fjPt_injective e1.symm
    rw [this]
    exact hj''
  · rw [hσ.card_image S]
    exact hcard.ge

theorem exists_perm_image_of_trans {k : ℕ}
    (htrans : ∀ U ∈ uPts.powersetCard k, ∀ U' ∈ uPts.powersetCard k,
      ∃ n : normalizer (E0 : Set Cd), n • U = U')
    {S S' : Finset (Fin 23)} (hS : ∀ j ∈ S, j ≠ 0) (hS' : ∀ j ∈ S', j ≠ 0) (hk : S.card = k)
    (hk' : S'.card = k) :
    ∃ (n : Cd) (σ : Equiv.Perm (Fin 23)), n ∈ normalizer (E0 : Set Cd) ∧ IsPerm n σ ∧
      S.image σ = S' := by
  obtain ⟨n, hn⟩ := htrans _ (image_pg_mem hS hk) _ (image_pg_mem hS' hk')
  obtain ⟨σ, hσ⟩ := exists_perm n.2
  exact ⟨n, σ, n.2, hσ, image_eq_of_smul hσ hS hS' (hk.trans hk'.symm) hn⟩

end

section



theorem trans_uPts {k : ℕ} (hk : k ≤ 3) {U U' : Finset (Fin 3510)}
    (hU : U ∈ uPts.powersetCard k) (hU' : U' ∈ uPts.powersetCard k) :
    ∃ n : normalizer (E0 : Set Cd), n • U = U' := by
  rw [Finset.mem_powersetCard] at hU hU'
  have hC : ∀ S S' : Finset (Fin 3510), S ⊆ uPts → S' ⊆ uPts → S.card = S'.card →
      S.card ≤ 3 → ∃ x : CFSG.Sporadic.Fi22.J, x • uPts = uPts ∧ x • S = S' :=
    Certificates.certificate25270
  obtain ⟨x, hxU, hxS⟩ := hC U U' hU.1 hU'.1 (hU.2.trans hU'.2.symm) (hU.2 ▸ hk)
  obtain ⟨c, hc⟩ := piC_surjective x
  have hn : c ∈ normalizer (E0 : Set Cd) := by
    rw [mem_normalizer_iff_mem_stab, mem_stab_iff]
    intro u hu
    rw [smul_eq_piC, hc, ← hxU]
    exact Finset.smul_mem_smul_finset hu
  refine ⟨⟨c, hn⟩, ?_⟩
  rw [← hxS, ← hc, ← smul_finset_eq_piC]
  rfl

theorem exists_perm_image {S S' : Finset (Fin 23)} (hS : ∀ j ∈ S, j ≠ 0) (hS' : ∀ j ∈ S', j ≠ 0)
    (hk : S.card = S'.card) (h3 : S.card ≤ 3) :
    ∃ (n : Cd) (σ : Equiv.Perm (Fin 23)), n ∈ normalizer (E0 : Set Cd) ∧ IsPerm n σ ∧
      S.image σ = S' :=
  exists_perm_image_of_trans (fun _ hU _ hU' => trans_uPts h3 hU hU') hS hS' rfl hk.symm

end

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Gen
