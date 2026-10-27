module

public import CFSG.ClassicalInvolution.AschTight.S19BStmt
public import CFSG.ClassicalInvolution.AschTight.Sec7Basic
public import CFSG.ClassicalInvolution.Q3.Q3T6MainSylow

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight

section Sylow



variable {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G} {S : Sylow 2 G}
  {W L : Subgroup G} {t : G} {V : Subgroup G}

theorem exists_sylow_conj3 (hd : Sec19DataT3 K z S W L t V) {x : G}
    (hx : x ∈ S19B.sec19BPrime K S W L) {s : G} (hsx : s ∈ Subgroup.centralizer ({x} : Set G))
    (hsz : s ∈ Subgroup.centralizer ({z} : Set G)) (hs2 : IsPGroup 2 (Subgroup.zpowers s)) :
    ∃ S' : Sylow 2 G, Sec19DataT3 K z S' W L t V ∧ x ∈ S19B.sec19BPrime K S' W L ∧
      ∃ c ∈ Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({z} : Set G),
        c * s * c⁻¹ ∈ (S' : Subgroup G) := by
  have hd0 := hd.toSec19Data3
  obtain ⟨⟨⟨hxS, hxR⟩, hxW⟩, hxL⟩ := hx
  set H := Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({z} : Set G) with hH
  have hP₀H : (S : Subgroup G) ⊓ Subgroup.centralizer ({x} : Set G) ≤ H :=
    le_inf inf_le_right (inf_le_left.trans hd0.hSz)
  obtain ⟨T, hT, hP₀T⟩ := IsSylow2In.exists_ge (S.isPGroup'.to_le inf_le_left) hP₀H
  obtain ⟨c, hcH, hsc⟩ := Sec7.exists_conj_le_of_isSylow2In hT hs2
    (Subgroup.zpowers_le.mpr ⟨hsx, hsz⟩)
  have hcs : c⁻¹ * s * c ∈ T := by
    have h := mem_conjSub_iff.mp (hsc (Subgroup.mem_zpowers s))
    exact h
  obtain ⟨T', hT', hTT'⟩ := IsSylow2In.exists_ge hT.2.1 (hT.1.trans inf_le_right)
  have hcard : Nat.card T' = Nat.card (S : Subgroup G) :=
    IsSylow2In.natCard_eq hT' (S1916.isSylow2In_of_le S hd0.hSz)
  set S' : Sylow 2 G := Sylow.ofCard T' (by rw [hcard]; exact S.card_eq_multiplicity) with hS'
  have hS'T' : (S' : Subgroup G) = T' := Sylow.coe_ofCard _ _
  have hxS' : ∀ y ∈ (S : Subgroup G), y * x = x * y → y ∈ (S' : Subgroup G) := fun y hy hyx => by
    rw [hS'T']
    exact hTT' (hP₀T ⟨hy, Subgroup.mem_centralizer_singleton_iff.mpr hyx⟩)
  have hRS' : (S : Subgroup G) ⊓ K ≤ (S' : Subgroup G) := fun r hr =>
    hxS' r hr.1 (Subgroup.mem_centralizer_iff.mp hxR r hr)
  have hR : (S' : Subgroup G) ⊓ K = (S : Subgroup G) ⊓ K := by
    have hRK := hd0.isSylow2In_inf
    exact hRK.2.2 _ inf_le_right (S'.isPGroup'.to_le inf_le_left) (le_inf hRS' inf_le_right)
  have hWS' : W ≤ (S' : Subgroup G) := fun w hw =>
    hxS' w (hd.hWS hw) (Subgroup.mem_centralizer_iff.mp hxW w hw)
  have hS'z : (S' : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G) := by
    rw [hS'T']
    exact hT'.1
  have hsyl : ∃ Q₀ : Sylow 2 K, (Q₀ : Subgroup K).map K.subtype ≤ (S' : Subgroup G) := by
    obtain ⟨Q₀, hQ₀⟩ := hd0.sylow
    exact ⟨Q₀, (le_inf hQ₀ (Subgroup.map_subtype_le _)).trans hRS'⟩
  have hd' : Sec19DataT3 K z S' W L t V :=
    ⟨⟨hd0.tight, hd0.mu, hd0.cex, hsyl, hS'z, hd0.hW, hWS'⟩, hd.memL, hd.invL, hd.ne,
      hd.memV, hd.leW, hd.memT⟩
  refine ⟨S', hd', ⟨⟨⟨hxS' x hxS rfl, by rw [hR]; exact hxR⟩, hxW⟩, hxL⟩, c⁻¹,
    H.inv_mem hcH, ?_⟩
  rw [inv_inv, hS'T']
  exact hTT' hcs

end Sylow

end CFSG.ClassicalInvolution.Q3.Q3T6
