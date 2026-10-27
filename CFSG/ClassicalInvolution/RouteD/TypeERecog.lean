module

public import CFSG.ClassicalInvolution.RouteD.TypeARecognition
public import CFSG.ClassicalInvolution.WeakCT.Exceptional
public import CFSG.ClassicalInvolution.WeakCT.Spin

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.LieType CFSG.Timmesfeld CFSG.LieType.CurtisTits
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)

variable {p f : ℕ} [Fact p.Prime]

section Wrappers

variable {X : Type} [Group X]

theorem card_galoisField_of_four_le (hq : 4 ≤ p ^ f) :
    f ≠ 0 ∧ Nat.card (GaloisField p f) = p ^ f := by
  have hf : f ≠ 0 := by rintro rfl; simp at hq
  exact ⟨hf, GaloisField.card p f hf⟩

theorem chain_subgroupOf {ι : Type} (U : ι → Subgroup X) (i j : ι)
    (hpair : ∃ W : Subgroup X, LinearBlockStandardPair (GaloisField p f) W (U i) (U j)) :
    ∃ W : Subgroup ↥(⨆ k, U k), LinearBlockStandardPair (GaloisField p f) W
      ((U i).subgroupOf (⨆ k, U k)) ((U j).subgroupOf (⨆ k, U k)) := by
  obtain ⟨W, hW⟩ := hpair
  exact ⟨W.subgroupOf _, linearBlockStandardPair_subgroupOf
    ((linearBlockStandardPair_le_sup hW).trans (sup_le (le_iSup U i) (le_iSup U j))) hW⟩

theorem chain_commutes_subgroupOf {ι : Type} (U : ι → Subgroup X) (i j : ι)
    (h : Commutes (U i) (U j)) :
    ∀ a ∈ (U i).subgroupOf (⨆ k, U k), ∀ b ∈ (U j).subgroupOf (⨆ k, U k), a * b = b * a :=
  fun a ha b hb => Subtype.ext (h a.1 ha b.1 hb)

theorem exists_psi_E6 (hadm : StatedLieAdmissible .E6 0 p f) (hq : 4 ≤ p ^ f)
    (U : Fin 6 → Subgroup X)
    (hcomm : ∀ i j : Fin 6, i ≠ j → ¬ edgeE 6 i j → ¬ edgeE 6 j i → Commutes (U i) (U j))
    (hpair : ∀ i j : Fin 6, edgeE 6 i j →
      ∃ W : Subgroup X, LinearBlockStandardPair (GaloisField p f) W (U i) (U j)) :
    ∃ Ψ : (modelUniv .E6 0 p f Fact.out).K →* X, Ψ.ker ≤ Subgroup.center _ ∧
      Ψ.range = ⨆ k, U k ∧
      ∀ k, (rankOne (Steinberg.Minuscule.e6Datum (GaloisField p f)).rootGroup k).map Ψ = U k := by
  obtain ⟨hf, hK⟩ := card_galoisField_of_four_le (p := p) (f := f) hq
  obtain ⟨Ψ', hsurj, hker, -, -, -, hrk⟩ := WeakCT.weakCT_e6 p f hadm (F := GaloisField p f) hK
    (hK ▸ hq) (X := ↥(⨆ k, U k)) (fun k => (U k).subgroupOf (⨆ k, U k))
    (iSup_subgroupOf_self U)
    (fun i j hij h1 h2 => chain_commutes_subgroupOf U i j (hcomm i j hij h1 h2))
    (fun i j h => chain_subgroupOf U i j (hpair i j h))
  have key : ∃ Ψ : ↥(Steinberg.Minuscule.e6Data_valid.minGroup (GaloisField p f)) →* X,
      Ψ.ker ≤ Subgroup.center _ ∧ Ψ.range = ⨆ k, U k ∧
      ∀ k, (rankOne (Steinberg.Minuscule.e6Datum (GaloisField p f)).rootGroup k).map Ψ = U k := by
    refine ⟨(⨆ k, U k).subtype.comp Ψ', ?_, ?_, ?_⟩
    · intro x hx
      exact hker (Subtype.ext (MonoidHom.mem_ker.mp hx))
    · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hsurj, Subgroup.map_top,
        Subgroup.range_subtype]
    · intro k
      rw [← Subgroup.map_map, hrk k, Subgroup.subgroupOf_map_subtype,
        inf_eq_left.mpr (le_iSup U k)]
  exact key

theorem exists_psi_E7(hadm : StatedLieAdmissible .E7 0 p f) (hq : 4 ≤ p ^ f)
    (U : Fin 7 → Subgroup X)
    (hcomm : ∀ i j : Fin 7, i ≠ j → ¬ edgeE 7 i j → ¬ edgeE 7 j i →
      Commutes (U i) (U j))
    (hpair : ∀ i j : Fin 7, edgeE 7 i j →
      ∃ W : Subgroup X, LinearBlockStandardPair (GaloisField p f) W (U i) (U j)) :
    ∃ Ψ : (modelUniv .E7 0 p f Fact.out).K →* X, Ψ.ker ≤ Subgroup.center _ ∧
      Ψ.range = ⨆ k, U k ∧
      ∀ k, (rankOne (Steinberg.Minuscule.e7Datum (GaloisField p f)).rootGroup k).map Ψ = U k := by
  obtain ⟨hf, hK⟩ := card_galoisField_of_four_le (p := p) (f := f) hq
  obtain ⟨Ψ', hsurj, hker, -, -, -, hrk⟩ := WeakCT.weakCT_e7 p f hadm (F := GaloisField p f) hK
    (hK ▸ hq) (X := ↥(⨆ k, U k)) (fun k => (U k).subgroupOf (⨆ k, U k))
    (iSup_subgroupOf_self U)
    (fun i j hij h1 h2 => chain_commutes_subgroupOf U i j (hcomm i j hij h1 h2))
    (fun i j h => chain_subgroupOf U i j (hpair i j h))
  have key : ∃ Ψ : ↥(Steinberg.Minuscule.e7Data_valid.minGroup (GaloisField p f)) →* X,
      Ψ.ker ≤ Subgroup.center _ ∧ Ψ.range = ⨆ k, U k ∧
      ∀ k, (rankOne (Steinberg.Minuscule.e7Datum (GaloisField p f)).rootGroup k).map Ψ = U k := by
    refine ⟨(⨆ k, U k).subtype.comp Ψ', ?_, ?_, ?_⟩
    · intro x hx
      exact hker (Subtype.ext (MonoidHom.mem_ker.mp hx))
    · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hsurj, Subgroup.map_top,
        Subgroup.range_subtype]
    · intro k
      rw [← Subgroup.map_map, hrk k, Subgroup.subgroupOf_map_subtype,
        inf_eq_left.mpr (le_iSup U k)]
  exact key

theorem exists_psi_E8(hadm : StatedLieAdmissible .E8 0 p f) (hq : 4 ≤ p ^ f)
    (U : Fin 8 → Subgroup X)
    (hcomm : ∀ i j : Fin 8, i ≠ j → ¬ edgeE 8 i j → ¬ edgeE 8 j i →
      Commutes (U i) (U j))
    (hpair : ∀ i j : Fin 8, edgeE 8 i j →
      ∃ W : Subgroup X, LinearBlockStandardPair (GaloisField p f) W (U i) (U j)) :
    ∃ Ψ : (modelUniv .E8 0 p f Fact.out).K →* X, Ψ.ker ≤ Subgroup.center _ ∧
      Ψ.range = ⨆ k, U k ∧
      ∀ k, (rankOne (Steinberg.Adjoint.e8Datum (GaloisField p f)).rootGroup k).map Ψ = U k := by
  obtain ⟨hf, hK⟩ := card_galoisField_of_four_le (p := p) (f := f) hq
  obtain ⟨Ψ', hsurj, hker, -, -, -, hrk⟩ := WeakCT.weakCT_e8 p f hadm (F := GaloisField p f) hK
    (hK ▸ hq) (X := ↥(⨆ k, U k)) (fun k => (U k).subgroupOf (⨆ k, U k))
    (iSup_subgroupOf_self U)
    (fun i j hij h1 h2 => chain_commutes_subgroupOf U i j (hcomm i j hij h1 h2))
    (fun i j h => chain_subgroupOf U i j (hpair i j h))
  have key : ∃ Ψ : ↥(CFSG.Blueprint.Chevalley.adjointGroup .E8 (GaloisField p f)) →* X,
      Ψ.ker ≤ Subgroup.center _ ∧ Ψ.range = ⨆ k, U k ∧
      ∀ k, (rankOne (Steinberg.Adjoint.e8Datum (GaloisField p f)).rootGroup k).map Ψ = U k := by
    refine ⟨(⨆ k, U k).subtype.comp Ψ', ?_, ?_, ?_⟩
    · intro x hx
      exact hker (Subtype.ext (MonoidHom.mem_ker.mp hx))
    · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hsurj, Subgroup.map_top,
        Subgroup.range_subtype]
    · intro k
      rw [← Subgroup.map_map, hrk k, Subgroup.subgroupOf_map_subtype,
        inf_eq_left.mpr (le_iSup U k)]
  exact key

theorem exists_psi_D6 (hadm : StatedLieAdmissible .POmegaPlus 6 p f) (hq : 4 ≤ p ^ f)
    (U : Fin 6 → Subgroup X)
    (hcomm : ∀ i j : Fin 6, i ≠ j → ¬ edgeD 6 i j → ¬ edgeD 6 j i → Commutes (U i) (U j))
    (hpair : ∀ i j : Fin 6, edgeD 6 i j →
      ∃ W : Subgroup X, LinearBlockStandardPair (GaloisField p f) W (U i) (U j)) :
    ∃ Ψ : (modelUniv .POmegaPlus 6 p f Fact.out).K →* X, Ψ.ker ≤ Subgroup.center _ ∧
      Ψ.range = ⨆ k, U k ∧
      ∀ k, (rankOne (Spin.plusDatum 6 (GaloisField p f) (by norm_num)).rootGroup k).map Ψ =
        U k := by
  obtain ⟨hf, hK⟩ := card_galoisField_of_four_le (p := p) (f := f) hq
  obtain ⟨Ψ', hsurj, hker, -, -, -, hrk⟩ := WeakCT.weakCT_spinPlus hadm (by norm_num)
    (F := GaloisField p f) hK (hK ▸ hq) (X := ↥(⨆ k, U k))
    (fun k => (U k).subgroupOf (⨆ k, U k)) (iSup_subgroupOf_self U)
    (fun i j hij h1 h2 => chain_commutes_subgroupOf U i j (hcomm i j hij h1 h2))
    (fun i j h => chain_subgroupOf U i j (hpair i j h))
  have key : ∃ Ψ : spinGroup (Spin.quadPlus 6 (GaloisField p f)) →* X,
      Ψ.ker ≤ Subgroup.center _ ∧ Ψ.range = ⨆ k, U k ∧
      ∀ k, (rankOne (Spin.plusDatum 6 (GaloisField p f) (by norm_num)).rootGroup k).map Ψ =
        U k := by
    refine ⟨(⨆ k, U k).subtype.comp Ψ', ?_, ?_, ?_⟩
    · intro x hx
      exact hker (Subtype.ext (MonoidHom.mem_ker.mp hx))
    · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hsurj, Subgroup.map_top,
        Subgroup.range_subtype]
    · intro k
      rw [← Subgroup.map_map, hrk k, Subgroup.subgroupOf_map_subtype,
        inf_eq_left.mpr (le_iSup U k)]
  exact key

end Wrappers

end CFSG.ClassicalInvolution.RouteD
