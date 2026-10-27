module

public import CFSG.GH74.Generic.S45.LEvSporSpec
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAutCentralizers
public import CFSG.Sporadic.SmallOddCore.Assembly

public section

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
  CFSG.ComponentClassification.M12Cover
open scoped commutatorElement

namespace CFSG.GH74.Generic.S45.EvSpor

theorem tp_image_toTable {n : ℕ} (hn : n < 2 ^ 32) (gs : List (Equiv.Perm (Fin n)))
    (hrep : ∀ T ∈ gs.map toTable, Rep n T (tp n T)) :
    tp n '' {x | x ∈ (gs.map toTable).toArray} = {g | g ∈ gs} := by
  ext g
  constructor
  · rintro ⟨T, hT, rfl⟩
    obtain ⟨g₀, hg₀, rfl⟩ := List.mem_map.1 (List.mem_toArray.1 hT)
    have := rep_unique (hrep _ (List.mem_map.2 ⟨g₀, hg₀, rfl⟩)) (rep_toTable hn g₀)
    rw [this]
    exact hg₀
  · intro hg
    refine ⟨toTable g, List.mem_toArray.2 (List.mem_map.2 ⟨g, hg, rfl⟩), ?_⟩
    exact rep_unique (hrep _ (List.mem_map.2 ⟨g, hg, rfl⟩)) (rep_toTable hn g)

theorem innerT_of_mem_blockGroup {g : Equiv.Perm (Fin 24)} (hg : g ∈ blockGroup) :
    ∀ T, Rep 24 T g → innerT T = true := by
  intro T hT
  obtain ⟨⟨p, q⟩, -, rfl⟩ := mem_blockGroup.1 hg
  have h0 := hT 0 (by norm_num)
  rw [idx_of_lt _ (by norm_num)] at h0
  have h1 : blockHom (p, q) • (⟨0, by norm_num⟩ : Fin 24) = Fin.castAdd 12 (p 0) :=
    blockHom_castAdd p q 0
  rw [h1] at h0
  have h2 : (Fin.castAdd 12 (p 0)).val < 12 := (p 0).isLt
  unfold innerT
  unfold ap at h0
  rw [h0]
  exact decide_eq_true h2

theorem autModelConj_bijective' :
    Function.Bijective autModelConj := by
  have h : (autModelConj : ↥autModel → MulAut ↥blockGroup) =
      (MulAut.congr m12EquivD.symm).symm ∘ autModelHom := by
    funext δ
    show autModelConj δ =
      (MulAut.congr m12EquivD.symm).symm ((MulAut.congr m12EquivD.symm) (autModelConj δ))
    rw [MulEquiv.symm_apply_apply]
  rw [h]
  exact (MulAut.congr m12EquivD.symm).symm.bijective.comp autModelHom_bijective

theorem m12_smallAutModel :
    AutModel blockGroup autModel where
  le := blockGroup_le_autModel
  conj_mem x hx p hp := autModel_conj_mem hx p hp
  surj α := by
    obtain ⟨δ, hδ⟩ := autModelConj_bijective'.2 α
    refine ⟨(δ : Equiv.Perm (Fin 24)), δ.2, fun p => ?_⟩
    have := congrArg (fun β : MulAut ↥blockGroup => ((β p : ↥blockGroup) : Equiv.Perm (Fin 24))) hδ
    simpa [autModelConj, conjOn_apply] using this.symm
  inj x hx hxc := by
    have h1 : autModelConj ⟨x, hx⟩ = autModelConj 1 := by
      rw [map_one]
      refine MulEquiv.ext fun p => Subtype.ext ?_
      simp only [autModelConj, MonoidHom.coe_mk, OneHom.coe_mk, conjOn_apply, MulAut.one_apply]
      calc x * (p : Equiv.Perm (Fin 24)) * x⁻¹ = (p : Equiv.Perm (Fin 24)) * x * x⁻¹ := by
            rw [hxc p p.2]
        _ = p := by group
    exact congrArg Subtype.val (autModelConj_bijective'.1 h1)

theorem card_autModel_eq :
    Nat.card autModel = 2 * Nat.card blockGroup := by
  have h := (blockGroup.subgroupOf autModel).card_mul_index
  rw [index_blockGroup, Nat.card_congr (Subgroup.subgroupOfEquivOfLe blockGroup_le_autModel).toEquiv]
    at h
  omega


theorem m12_C2A_enums (h : m12C2AEnumOK = true) :
    EnumsSub 24 m12C2A (autModel ⊓ Subgroup.centralizer
      ({blockHom (permZ, permZ)} : Set (Equiv.Perm (Fin 24)))) ∧ invsOK 24 m12C2A = true := by
  have hn : (24 : ℕ) < 2 ^ 32 := by norm_num
  rw [m12C2AEnumOK, Bool.and_eq_true] at h
  obtain ⟨⟨hE, -, hrep⟩, hinv⟩ := And.intro (enumOK_spec hn h.1) h.2
  refine ⟨?_, hinv⟩
  have himg := tp_image_toTable hn q4Gens hrep
  have hQ := (q4Q_spec).1
  have : q4Q.originalSubgroup = Subgroup.closure {g | g ∈ q4Gens} := by
    rw [q4Q, certificate_originalSubgroup]
  have hE' : EnumsSub 24 m12C2A
      (Subgroup.closure (tp 24 '' {x | x ∈ (q4Gens.map toTable).toArray})) := hE
  rw [himg, ← this, hQ] at hE'
  exact hE'

theorem m12_Ka_facts (hC : m12C2AEnumOK = true) (h : m12KaEnumOK = true) :
    EnumsSub 24 m12Ka (Subgroup.closure (tp 24 '' {x | x ∈ m12KaGens.toArray})) ∧
      Nat.card ↥(Subgroup.closure (tp 24 '' {x | x ∈ m12KaGens.toArray})) = 60 ∧
      Subgroup.closure (tp 24 '' {x | x ∈ m12KaGens.toArray}) ≤ autModel ∧
      (∀ g ∈ m12KaGens, Rep 24 g (tp 24 g)) := by
  have hn : (24 : ℕ) < 2 ^ 32 := by norm_num
  obtain ⟨hEC, -⟩ := m12_C2A_enums hC
  rw [m12KaEnumOK, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  obtain ⟨hE, hc, hrep⟩ := enumOK_spec hn h1
  refine ⟨hE, hc, ?_, hrep⟩
  rw [Subgroup.closure_le]
  rintro _ ⟨x, hx, rfl⟩
  have hx' : x ∈ m12KaGens := List.mem_toArray.mp hx
  have hmem : x = m12AT ∨ x = m12KaB := by
    simpa [m12KaGens] using hx'
  rcases hmem with rfl | rfl
  · exact ((hEC.mem_iff (hrep _ hx')).1 h2).1
  · exact ((hEC.mem_iff (hrep _ hx')).1 h3).1

end CFSG.GH74.Generic.S45.EvSpor
