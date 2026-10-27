module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6FactDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFCoverSylow

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G H : Type} [Group G] [Group H] {L : Subgroup G}

private lemma ffImg_closure_orders (Φ : ↥L ≃* H) {B : Subgroup G} (hBL : B ≤ L)
    (p : ℕ → Prop) :
    ffImg Φ.toMonoidHom (Subgroup.closure {g | g ∈ B ∧ p (orderOf g)}) =
      Subgroup.closure {h | h ∈ ffImg Φ.toMonoidHom B ∧ p (orderOf h)} := by
  have hsetX :
      {g : G | g ∈ B ∧ p (orderOf g)} =
        L.subtype '' {l : ↥L | (l : G) ∈ B ∧ p (orderOf l)} := by
    ext g
    constructor
    · intro hg
      have hg' : g ∈ B ∧ p (orderOf g) := hg
      refine ⟨⟨g, hBL hg'.1⟩, ?_, rfl⟩
      simpa using hg'
    · rintro ⟨l, hl, rfl⟩
      refine ⟨hl.1, ?_⟩
      rw [orderOf_injective L.subtype L.subtype_injective l]
      exact hl.2
  have hmap :
      Subgroup.closure {g : G | g ∈ B ∧ p (orderOf g)} =
        (Subgroup.closure {l : ↥L | (l : G) ∈ B ∧ p (orderOf l)}).map L.subtype := by
    rw [MonoidHom.map_closure, hsetX]
  have hsub :
      (Subgroup.closure {g : G | g ∈ B ∧ p (orderOf g)}).subgroupOf L =
        Subgroup.closure {l : ↥L | (l : G) ∈ B ∧ p (orderOf l)} := by
    change Subgroup.comap L.subtype
        (Subgroup.closure {g : G | g ∈ B ∧ p (orderOf g)}) =
      Subgroup.closure {l : ↥L | (l : G) ∈ B ∧ p (orderOf l)}
    rw [hmap]
    exact Subgroup.comap_map_eq_self_of_injective L.subtype_injective _
  have hset :
      Φ.toMonoidHom '' {l : ↥L | (l : G) ∈ B ∧ p (orderOf l)} =
        {h : H | h ∈ ffImg Φ.toMonoidHom B ∧ p (orderOf h)} := by
    ext h
    constructor
    · rintro ⟨l, hl, rfl⟩
      have hl' : (l : G) ∈ B ∧ p (orderOf l) := hl
      refine ⟨?_, ?_⟩
      · rw [mem_ffImg_iff]
        exact ⟨l, hl'.1, rfl⟩
      · have ho : orderOf (Φ.toMonoidHom l) = orderOf l := MulEquiv.orderOf_eq Φ l
        rw [ho]
        exact hl'.2
    · rintro ⟨hhB, hhp⟩
      obtain ⟨l, hlB, hlφ⟩ := mem_ffImg_iff.mp hhB
      have ho : orderOf (Φ.toMonoidHom l) = orderOf l := MulEquiv.orderOf_eq Φ l
      refine ⟨l, ⟨hlB, ?_⟩, hlφ⟩
      rw [← hlφ] at hhp
      simpa [ho] using hhp
  change ((Subgroup.closure {g : G | g ∈ B ∧ p (orderOf g)}).subgroupOf L).map
      Φ.toMonoidHom = Subgroup.closure {h : H | h ∈ ffImg Φ.toMonoidHom B ∧ p (orderOf h)}
  rw [hsub]
  rw [MonoidHom.map_closure Φ.toMonoidHom {l : ↥L | (l : G) ∈ B ∧ p (orderOf l)}]
  rw [hset]

theorem ffIso_img_twoRes (Φ : ↥L ≃* H) {B : Subgroup G} (hBL : B ≤ L) :
    ffImg Φ.toMonoidHom (twoRes B) = twoRes (ffImg Φ.toMonoidHom B) :=
  ffImg_closure_orders Φ hBL Odd

theorem ffIso_img_twoPrimeRes (Φ : ↥L ≃* H) {B : Subgroup G} (hBL : B ≤ L) :
    ffImg Φ.toMonoidHom (twoPrimeRes B) = twoPrimeRes (ffImg Φ.toMonoidHom B) :=
  ffImg_closure_orders Φ hBL fun n => ∃ k : ℕ, n = 2 ^ k

theorem ffIso_img_X (Φ : ↥L ≃* H) {B : Subgroup G} (hBL : B ≤ L) :
    ffImg Φ.toMonoidHom (twoPrimeRes (twoRes B)) =
      twoPrimeRes (twoRes (ffImg Φ.toMonoidHom B)) := by
  have hBL' : twoRes B ≤ L := by
    show Subgroup.closure {g : G | g ∈ B ∧ Odd (orderOf g)} ≤ L
    exact (Subgroup.closure_le L).mpr fun _ hg => hBL hg.1
  rw [ffIso_img_twoPrimeRes Φ hBL', ffIso_img_twoRes Φ hBL]

end CFSG.OddStandard.SmallF3.Omega
