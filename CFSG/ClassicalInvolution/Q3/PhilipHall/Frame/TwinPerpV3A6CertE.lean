module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6ModelBasic
public import Certificates.Certificate517611

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S

namespace CertE

open CFSG.EvenSmallLie.OmegaEight Certificates.AE6Model Certificates.AE6CertE

section Letters


theorem mem_eGens_iff {L : List ℕ} (hL : ∀ i ∈ L, i < 8) (g : Equiv.Perm (Fin 360)) :
    g ∈ eGens L ↔ ∃ i : Fin 8, i.val ∈ L ∧ (A6.curtisGen i : Equiv.Perm (Fin 360)) = g := by
  simp only [eGens, List.mem_map]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i, hL i hi⟩, hi, (curtisPerms_getD (hL i hi)).symm⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i.val, hi, curtisPerms_getD i.2⟩

theorem map_letterSub {A : Set (Fin 8)} {L : List ℕ} (hL : ∀ i ∈ L, i < 8)
    (hA : ∀ i : Fin 8, i ∈ A ↔ i.val ∈ L) :
    (ae6LetterSub A).map omegaT.subtype = Subgroup.closure {g | g ∈ eGens L} := by
  rw [ae6LetterSub, MonoidHom.map_closure]
  congr 1
  ext g
  simp only [Set.mem_image, Set.mem_setOf_eq, mem_eGens_iff hL]
  constructor
  · rintro ⟨_, ⟨i, hi, rfl⟩, rfl⟩
    exact ⟨i, (hA i).mp hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨_, ⟨i, (hA i).mpr hi, rfl⟩, rfl⟩

theorem card_letterSub {A : Finset (Fin 8)} {L : List ℕ} (hL : ∀ i ∈ L, i < 8)
    (hA : ∀ i : Fin 8, i ∈ A ↔ i.val ∈ L) {N : ℕ}
    (hN : Nat.card (Subgroup.closure {g | g ∈ eGens L}) = N) :
    Nat.card (ae6LetterSub ↑A) = N := by
  rw [← Subgroup.card_map_of_injective omegaT.subtype_injective,
    map_letterSub hL (fun i => by rw [Finset.mem_coe]; exact hA i), hN]

end Letters

section Orders


theorem card_ae6ModelU : Nat.card ae6ModelU = 4096 := by
  have hc := Certificates.certificate517611.1
  rw [ae6ModelU]
  exact card_letterSub (L := [0, 2, 4, 6]) (by decide) (by decide) (hc ([0, 2, 4, 6], 4096) (by decide))

theorem card_ae6ModelV (k : Fin 3) : Nat.card (ae6ModelV k) = 1290240 := by
  have hc := Certificates.certificate517611.1
  rw [ae6ModelV_eq]
  fin_cases k
  · exact card_letterSub (L := [0, 2, 3, 4, 5, 6, 7]) (by decide) (by decide)
      (hc ([0, 2, 3, 4, 5, 6, 7], 1290240) (by decide))
  · exact card_letterSub (L := [0, 1, 2, 3, 4, 5, 6]) (by decide) (by decide)
      (hc ([0, 1, 2, 3, 4, 5, 6], 1290240) (by decide))
  · exact card_letterSub (L := [0, 1, 2, 3, 4, 6, 7]) (by decide) (by decide)
      (hc ([0, 1, 2, 3, 4, 6, 7], 1290240) (by decide))

end Orders

theorem letterSets (k : Fin 3) (A : Finset (Fin 8)) (hU : ae6ULetters ⊆ A) (hk : ae6Omit k ∉ A) :
    (∃ l, l ≠ k ∧ A = ae6EdgeLetters k l) ∨ A = {0, 2, 4, 6} ∨ A = {0, 2, 3, 4, 5, 6, 7} ∨
      A = {0, 1, 2, 3, 4, 5, 6} ∨ A = {0, 1, 2, 3, 4, 6, 7} ∨ A = {0, 1, 2, 4, 6} ∨
      A = {0, 2, 3, 4, 6} ∨ A = {0, 2, 4, 5, 6} ∨ A = {0, 2, 4, 6, 7} ∨ A = {0, 2, 4, 5, 6, 7} ∨
      A = {0, 1, 2, 4, 5, 6} ∨ A = {0, 1, 2, 4, 6, 7} := by
  revert k A
  decide +kernel

section Edges


theorem e_edges (k : Fin 3) (A : Finset (Fin 8)) (hU : ae6ULetters ⊆ A) (hk : ae6Omit k ∉ A)
    (hA : Nat.card (ae6LetterSub ↑A) = 86016) : ∃ l, l ≠ k ∧ A = ae6EdgeLetters k l := by
  have hc := Certificates.certificate517611.1
  rcases letterSets k A hU hk with he | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl
  · exact he
  · rw [card_letterSub (L := [0, 2, 4, 6]) (by decide) (by decide)
      (hc ([0, 2, 4, 6], 4096) (by decide))] at hA
    omega
  · rw [card_letterSub (L := [0, 2, 3, 4, 5, 6, 7]) (by decide) (by decide)
      (hc ([0, 2, 3, 4, 5, 6, 7], 1290240) (by decide))] at hA
    omega
  · rw [card_letterSub (L := [0, 1, 2, 3, 4, 5, 6]) (by decide) (by decide)
      (hc ([0, 1, 2, 3, 4, 5, 6], 1290240) (by decide))] at hA
    omega
  · rw [card_letterSub (L := [0, 1, 2, 3, 4, 6, 7]) (by decide) (by decide)
      (hc ([0, 1, 2, 3, 4, 6, 7], 1290240) (by decide))] at hA
    omega
  · rw [card_letterSub (L := [0, 1, 2, 4, 6]) (by decide) (by decide)
      (hc ([0, 1, 2, 4, 6], 12288) (by decide))] at hA
    omega
  · rw [card_letterSub (L := [0, 2, 3, 4, 6]) (by decide) (by decide)
      (hc ([0, 2, 3, 4, 6], 12288) (by decide))] at hA
    omega
  · rw [card_letterSub (L := [0, 2, 4, 5, 6]) (by decide) (by decide)
      (hc ([0, 2, 4, 5, 6], 12288) (by decide))] at hA
    omega
  · rw [card_letterSub (L := [0, 2, 4, 6, 7]) (by decide) (by decide)
      (hc ([0, 2, 4, 6, 7], 12288) (by decide))] at hA
    omega
  · rw [card_letterSub (L := [0, 2, 4, 5, 6, 7]) (by decide) (by decide)
      (hc ([0, 2, 4, 5, 6, 7], 36864) (by decide))] at hA
    omega
  · rw [card_letterSub (L := [0, 1, 2, 4, 5, 6]) (by decide) (by decide)
      (hc ([0, 1, 2, 4, 5, 6], 36864) (by decide))] at hA
    omega
  · rw [card_letterSub (L := [0, 1, 2, 4, 6, 7]) (by decide) (by decide)
      (hc ([0, 1, 2, 4, 6, 7], 36864) (by decide))] at hA
    omega

end Edges

theorem getD_map_map {α β : Type*} (L : List (List α)) (f : α → β) (j : ℕ) :
    (L.map (List.map f)).getD j [] = (L.getD j []).map f := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases L[j]? <;> rfl

theorem eWords_eq : eWords = ae6CosetWordsV0.map (List.map Fin.val) := by
  decide +kernel

theorem eVSwap_eq :
    ∀ (k : Fin 3) (c : Fin 8), (eVSwap.getD k.val []).getD c.val 0 = (ae6VertexSwap k c).val := by
  decide

theorem eOmit_eq : ∀ k : Fin 3, (ae6Omit k).val = eOmit.getD k.val 0 := by
  decide

theorem eWordOf_eq (k : Fin 3) (j : Fin 315) :
    eWordOf k.val j.val = (ae6CosetWord k j).map Fin.val := by
  rw [eWordOf, eWords_eq, getD_map_map, List.map_map, ae6CosetWord, List.map_map]
  exact List.map_congr_left fun c _ => eVSwap_eq k c

section Cosets


theorem coe_curtisGen_eq (i : Fin 8) :
    (A6.curtisGen i : Equiv.Perm (Fin 360)) = (curtisPerms ()).getD i.val 1 :=
  (curtisPerms_getD i.2).symm

theorem coe_ae6CosetY (k : Fin 3) (j : Fin 315) :
    ((ae6CosetY k j : AE6Om) : Equiv.Perm (Fin 360)) =
      aeWord (curtisPerms ()) (eWordOf k.val j.val) := by
  rw [eWordOf_eq, ae6CosetY, coe_ae6Word]

theorem map_ae6ModelU :
    ae6ModelU.map omegaT.subtype = Subgroup.closure {g | g ∈ eGens [0, 2, 4, 6]} := by
  rw [ae6ModelU, map_letterSub (L := [0, 2, 4, 6]) (by decide)
    (fun i => by rw [Finset.mem_coe]; revert i; decide)]

theorem e_cosets (k : Fin 3) (j : Fin 315) (x : Fin 8) (hx : x ≠ ae6Omit k) :
    ∃ j' : Fin 315, ae6CosetY k j * A6.curtisGen x * (ae6CosetY k j')⁻¹ ∈ ae6ModelU := by
  have hxo : x.val ≠ eOmit.getD k.val 0 := fun he => hx (Fin.ext (he.trans (eOmit_eq k).symm))
  obtain ⟨j', hj', hm⟩ :=
    Certificates.certificate517611.2.1 k.val k.2 j.val j.2 x.val x.2 hxo
  refine ⟨⟨j', hj'⟩, (Subgroup.mem_map_iff_mem omegaT.subtype_injective).mp ?_⟩
  rw [map_ae6ModelU, map_mul, map_mul, map_inv]
  have e1 : omegaT.subtype (ae6CosetY k j) = aeWord (curtisPerms ()) (eWordOf k.val j.val) :=
    coe_ae6CosetY k j
  have e2 : omegaT.subtype (ae6CosetY k ⟨j', hj'⟩) = aeWord (curtisPerms ()) (eWordOf k.val j') :=
    coe_ae6CosetY k ⟨j', hj'⟩
  have e3 : omegaT.subtype (A6.curtisGen x) = (curtisPerms ()).getD x.val 1 := coe_curtisGen_eq x
  rw [e1, e2, e3]
  exact hm

theorem e_letters (k : Fin 3) (j : Fin 315) (i : Fin 8) (hi : i ∈ ae6CosetWord k j) :
    A6.curtisGen i ∈ ae6ModelU ⊔ Subgroup.zpowers (ae6CosetY k j) := by
  have hi' : i.val ∈ eWordOf k.val j.val := by
    rw [eWordOf_eq]
    exact List.mem_map_of_mem hi
  have h := Certificates.certificate517611.2.2.1 k.val k.2 j.val j.2 i.val hi'
  rw [← Subgroup.mem_map_iff_mem omegaT.subtype_injective, Subgroup.map_sup, map_ae6ModelU,
    MonoidHom.map_zpowers]
  have e1 : omegaT.subtype (ae6CosetY k j) = aeWord (curtisPerms ()) (eWordOf k.val j.val) :=
    coe_ae6CosetY k j
  have e3 : omegaT.subtype (A6.curtisGen i) = (curtisPerms ()).getD i.val 1 := coe_curtisGen_eq i
  rw [e1, e3]
  exact h

end Cosets

theorem e_rels (k : Fin 3) : ∀ r ∈ A6.curtisRels,
    A6.curtisEval (List.ofFn fun i => A6.curtisGen (ae6EdgeSwap k i)) r = 1 :=
  Certificates.certificate517611.2.2.2 k

end CertE

theorem ae6EdgePairsFin_proved :
    AE6EdgePairsFin :=
  ⟨CertE.card_ae6ModelU, CertE.card_ae6ModelV, CertE.e_edges, CertE.e_cosets, CertE.e_letters,
    CertE.e_rels⟩

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S
