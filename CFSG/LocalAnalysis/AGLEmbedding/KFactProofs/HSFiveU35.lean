
module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.HSFiveU35Base

public import Certificates.Certificate19850

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four CFSG.AGLEmbedding.FusD2
open CFSG.AGLEmbedding.MaxD2 CFSG.RankThree.Native Certificates.MaxD2Perm Certificates.MaxD2Heis
open Certificates.HSOver Certificates.HSU35
open scoped commutatorElement

theorem card_hsOUA :
    Nat.card hsOUA = 126000 :=
  Certificates.certificate19850.1

theorem hsU35_hcard :
    Nat.card (Gsub (D := dataU) hsU35S) = dataU.gOrder := by
  rw [hsU35_Gsub]
  exact card_hsOUA

theorem hsOUA_inf_normalizer :
    hsOUA ⊓ Subgroup.normalizer (hsOR0 : Set (Equiv.Perm (Fin 100))) = hsONU := by
  obtain ⟨hInv, hR, hN, hNorm, hMoves, hZ, hExp, hComm, hTorus, hCent, hMax⟩ := hsU35_parts_heis
  have h := normalizer_inf_eq_H hsU35_gsU hsU35_giU hsU35_len hsU35_hcard hR hN hNorm hMoves hMax
  rw [hsU35_Rsub, hsU35_Gsub, hsU35_Nsub] at h
  rw [inf_comm]
  exact h

theorem hsU35_maximal :
    ∀ Y : Subgroup (Equiv.Perm (Fin 100)), hsONU ≤ Y → Y ≤ hsOUA → Y = hsONU ∨ Y = hsOUA := by
  obtain ⟨hInv, hR, hN, hNorm, hMoves, hZ, hExp, hComm, hTorus, hCent, hMax⟩ := hsU35_parts_heis
  have h := maximal_N hsU35_gsU hsU35_giU hsU35_len hsU35_hcard hN (invsOK_of_checkHNormal hNorm)
    hMax
  rw [hsU35_Nsub, hsU35_Gsub] at h
  exact h

theorem hsOUA_isSimpleGroup :
    IsSimpleGroup ↥hsOUA := by
  classical
  have hNU : hsONU ≤ hsOUA := hsONU_le_UA
  let H : Subgroup ↥hsOUA := hsONU.subgroupOf hsOUA
  have hmemH : ∀ g : ↥hsOUA, g ∈ H ↔ (g : Equiv.Perm (Fin 100)) ∈ hsONU := fun g =>
    Subgroup.mem_subgroupOf
  have hwU : (⟨hsOW, hsOW_mem⟩ : ↥hsOUA) ∉ H := fun h => hsOW_not_mem ((hmemH _).1 h)
  have hcoatom : IsCoatom H := by
    refine ⟨fun htop => hwU (htop ▸ Subgroup.mem_top _), fun K hHK => ?_⟩
    have hNUY : hsONU ≤ K.map hsOUA.subtype := fun n hn =>
      Subgroup.mem_map.2 ⟨⟨n, hNU hn⟩, hHK.le ((hmemH _).2 hn), rfl⟩
    have hYU : K.map hsOUA.subtype ≤ hsOUA := by
      intro y hy
      obtain ⟨k, -, rfl⟩ := Subgroup.mem_map.1 hy
      exact k.2
    rcases hsU35_maximal _ hNUY hYU with h | h
    · exfalso
      refine hHK.not_ge (fun k hk => (hmemH k).2 ?_)
      have : (k : Equiv.Perm (Fin 100)) ∈ K.map hsOUA.subtype := Subgroup.mem_map.2 ⟨k, hk, rfl⟩
      rw [h] at this
      exact this
    · rw [eq_top_iff]
      intro g _
      have : (g : Equiv.Perm (Fin 100)) ∈ K.map hsOUA.subtype := by
        rw [h]
        exact g.2
      obtain ⟨k, hk, hkg⟩ := Subgroup.mem_map.1 this
      have hkg' : k = g := Subtype.ext hkg
      rw [← hkg']
      exact hk
  have hnontriv : Nontrivial (↥hsOUA ⧸ H) := by
    refine ⟨⟨((1 : ↥hsOUA) : ↥hsOUA ⧸ H), ((⟨hsOW, hsOW_mem⟩ : ↥hsOUA) : ↥hsOUA ⧸ H),
      fun h => hwU ?_⟩⟩
    have := QuotientGroup.eq.1 h
    simpa using this
  have hprim : MulAction.IsPreprimitive ↥hsOUA (↥hsOUA ⧸ H) := by
    rw [← MulAction.isCoatom_stabilizer_iff_preprimitive ↥hsOUA
      (((1 : ↥hsOUA)) : ↥hsOUA ⧸ H), MulAction.stabilizer_quotient]
    exact hcoatom
  have key : ∀ g a : ↥hsOUA, g • (a : ↥hsOUA ⧸ H) = (a : ↥hsOUA ⧸ H) → a⁻¹ * g * a ∈ H := by
    intro g a h
    have h' : ((g * a : ↥hsOUA) : ↥hsOUA ⧸ H) = (a : ↥hsOUA ⧸ H) := h
    have := QuotientGroup.eq.1 h'.symm
    simpa [mul_assoc] using this
  have hfaith : FaithfulSMul ↥hsOUA (↥hsOUA ⧸ H) := by
    rw [faithfulSMul_iff]
    intro g hg
    have h1 : g ∈ H := by simpa using key g 1 (hg _)
    have h2 : hsOW⁻¹ * (g : Equiv.Perm (Fin 100)) * hsOW ∈ hsONU := by
      simpa using (hmemH _).1 (key g ⟨hsOW, hsOW_mem⟩ (hg _))
    have h3 : hsOC⁻¹ * (g : Equiv.Perm (Fin 100)) * hsOC ∈ hsONU := by
      simpa using (hmemH _).1 (key g ⟨hsOC, hsU35_mem_U.2.2.1⟩ (hg _))
    exact Subtype.ext (hsU35_kernel g.1 ((hmemH g).1 h1) h2 h3)
  have hx : hsOX ∈ hsOUA := Subgroup.subset_closure (by simp)
  have hy : hsOY ∈ hsOUA := Subgroup.subset_closure (by simp)
  have hgen : Subgroup.closure ({⟨hsOX, hx⟩, ⟨hsOY, hy⟩} : Set ↥hsOUA) = ⊤ := by
    apply Subgroup.map_injective (f := hsOUA.subtype) hsOUA.subtype_injective
    rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, Subgroup.range_subtype, Set.image_pair]
    rfl
  have hox : orderOf (⟨hsOX, hx⟩ : ↥hsOUA) = 8 := by
    rw [← Subgroup.orderOf_coe]
    exact hsU35_orderOf_x
  have hoy : orderOf (⟨hsOY, hy⟩ : ↥hsOUA) = 3 := by
    rw [← Subgroup.orderOf_coe]
    exact hsU35_orderOf_y
  have hoxy : orderOf ((⟨hsOX, hx⟩ : ↥hsOUA) * ⟨hsOY, hy⟩) = 7 := by
    rw [← Subgroup.orderOf_coe]
    exact hsU35_orderOf_xy
  have hstab : Nat.card (MulAction.stabilizer ↥hsOUA (((1 : ↥hsOUA)) : ↥hsOUA ⧸ H)) = 1000 := by
    rw [MulAction.stabilizer_quotient]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNU).toEquiv]
    exact card_hsONU
  refine CFSG.Sporadic.Th.isSimpleGroup_of_primitive_coprime_orders (Ω := ↥hsOUA ⧸ H) ?_
    ⟨hsOX, hx⟩ ⟨hsOY, hy⟩ hgen (((1 : ↥hsOUA)) : ↥hsOUA ⧸ H) ?_ ?_
  · exact Nat.succ_le_of_lt (Finite.one_lt_card_iff_nontrivial.2 hnontriv)
  · rw [hox, hoy]
    norm_num
  · rw [hoxy, hstab]
    norm_num

theorem closure_insert_hsOW :
    Subgroup.closure (insert hsOW (hsONU : Set (Equiv.Perm (Fin 100)))) = hsOUA := by
  have h1 : hsONU ≤ Subgroup.closure (insert hsOW (hsONU : Set (Equiv.Perm (Fin 100)))) :=
    fun x hx => Subgroup.subset_closure (Set.mem_insert_of_mem _ hx)
  have h2 : Subgroup.closure (insert hsOW (hsONU : Set (Equiv.Perm (Fin 100)))) ≤ hsOUA :=
    (Subgroup.closure_le _).2 (Set.insert_subset hsOW_mem hsONU_le_UA)
  rcases hsU35_maximal _ h1 h2 with h | h
  · exfalso
    apply hsOW_not_mem
    rw [← h]
    exact Subgroup.subset_closure (Set.mem_insert _ _)
  · exact h

theorem hsOUA_inf_centralizer_T :
    hsOUA ⊓ Subgroup.centralizer ({hsOT} : Set (Equiv.Perm (Fin 100))) =
      Subgroup.zpowers hsOT :=
  Certificates.certificate19850.2

end CFSG.AGLEmbeddingD2
