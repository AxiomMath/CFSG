module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614K292Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614

open CFSG.Open Subgroup
open CFSG.RankThree.PartTwo.Sec4
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott
open P614K292

namespace P614K292CA

variable {X : Type} [Group X] {L : Subgroup X} {π : Bool} {p f : ℕ} {K : Type} [Field K]

@[expose] def transp (ν : ↥(slPi π 3 (p ^ f) K) →* ↥L) (E : Subgroup (GL (Fin 3) K)) :
    Subgroup X :=
  (E.subgroupOf (slPi π 3 (p ^ f) K)).map (L.subtype.comp ν)

@[expose] def candsX (L : Subgroup X) (x : X) : Set (Subgroup X) :=
  {E | E ≤ L ∧ IsElemAbelian 3 E ∧ Nat.card E = 9 ∧ (center ↥L).map L.subtype ≤ E ∧
    ∀ e ∈ E, x * e * x⁻¹ ∈ E}

variable {ν : ↥(slPi π 3 (p ^ f) K) →* ↥L}

theorem threeFrameIn_eq_transp (y : GL (Fin 3) K) (v : Fin 3 → K) :
    threeFrameIn ν y v = transp ν (threeFrame y v) :=
  rfl

theorem mem_transp {E : Subgroup (GL (Fin 3) K)} {g : X} :
    g ∈ transp ν E ↔
      ∃ s : ↥(slPi π 3 (p ^ f) K), (s : GL (Fin 3) K) ∈ E ∧ ((ν s : ↥L) : X) = g :=
  Iff.rfl

theorem transp_le (E : Subgroup (GL (Fin 3) K)) : transp ν E ≤ L := by
  rintro _ ⟨s, -, rfl⟩
  exact (ν s).2

theorem comp_injective (hν : Function.Injective ν) : Function.Injective (L.subtype.comp ν) :=
  L.subtype_injective.comp hν

theorem card_transp (hν : Function.Injective ν) {E : Subgroup (GL (Fin 3) K)}
    (hE : E ≤ slPi π 3 (p ^ f) K) : Nat.card (transp ν E) = Nat.card E := by
  rw [transp, Subgroup.card_map_of_injective (comp_injective hν)]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE).toEquiv

theorem transp_inj (hν : Function.Injective ν) {E₁ E₂ : Subgroup (GL (Fin 3) K)}
    (h₁ : E₁ ≤ slPi π 3 (p ^ f) K) (h₂ : E₂ ≤ slPi π 3 (p ^ f) K)
    (h : transp ν E₁ = transp ν E₂) : E₁ = E₂ := by
  have h' := Subgroup.map_injective (comp_injective hν) h
  rw [← Subgroup.map_subgroupOf_eq_of_le h₁, ← Subgroup.map_subgroupOf_eq_of_le h₂, h']

theorem isElemAbelian_transp_iff (hν : Function.Injective ν) {n : ℕ}
    {E : Subgroup (GL (Fin 3) K)} (hE : E ≤ slPi π 3 (p ^ f) K) :
    IsElemAbelian n (transp ν E) ↔ IsElemAbelian n E := by
  refine ⟨fun h => ?_, fun h => (h.subgroupOf _).map _⟩
  have h1 := h.comap (comp_injective hν)
  rw [transp, Subgroup.comap_map_eq_self_of_injective (comp_injective hν)] at h1
  have h2 := h1.map (slPi π 3 (p ^ f) K).subtype
  rwa [Subgroup.map_subgroupOf_eq_of_le hE] at h2

theorem exists_transp_eq (M : LModel L π p f K ν) {E : Subgroup X} (hE : E ≤ L) :
    ∃ E' : Subgroup (GL (Fin 3) K), E' ≤ slPi π 3 (p ^ f) K ∧ transp ν E' = E := by
  refine ⟨(E.comap (L.subtype.comp ν)).map (slPi π 3 (p ^ f) K).subtype,
    Subgroup.map_subtype_le _, ?_⟩
  have h1 : ((E.comap (L.subtype.comp ν)).map (slPi π 3 (p ^ f) K).subtype).subgroupOf
      (slPi π 3 (p ^ f) K) = E.comap (L.subtype.comp ν) :=
    Subgroup.comap_map_eq_self_of_injective (slPi π 3 (p ^ f) K).subtype_injective _
  rw [transp, h1]
  refine Subgroup.map_comap_eq_self fun g hg => ?_
  obtain ⟨s, hs⟩ := M.surj ⟨g, hE hg⟩
  exact MonoidHom.mem_range.2 ⟨s, congrArg Subtype.val hs⟩

theorem center_le_transp_iff (M : LModel L π p f K ν) (hν : Function.Injective ν)
    {E : Subgroup (GL (Fin 3) K)} :
    (center ↥L).map L.subtype ≤ transp ν E ↔
      StatedScalars (Fin 3) K ⊓ slPi π 3 (p ^ f) K ≤ E := by
  have hc := CFSG.HardMathSupport.Solomon.Coordinator.center_slPi_eq M.piField M.modThree
  constructor
  · intro h g hg
    have hg' := Subgroup.mem_inf.1 hg
    have hs : (⟨g, hg'.2⟩ : ↥(slPi π 3 (p ^ f) K)) ∈ center ↥(slPi π 3 (p ^ f) K) := by
      rw [hc, Subgroup.mem_subgroupOf]
      exact hg'.1
    obtain ⟨s', hs'E, hs'⟩ := mem_transp.1 (h ⟨ν ⟨g, hg'.2⟩, M.map_mem_center hs, rfl⟩)
    have hss : s' = ⟨g, hg'.2⟩ := hν (Subtype.ext hs')
    rw [hss] at hs'E
    exact hs'E
  · rintro h _ ⟨l, hl, rfl⟩
    obtain ⟨s, rfl⟩ := M.surj l
    have hs := M.mem_center_of_map_mem hl
    rw [hc, Subgroup.mem_subgroupOf] at hs
    exact ⟨s, h (Subgroup.mem_inf.2 ⟨hs, s.2⟩), rfl⟩

theorem conj_mem_transp_iff (M : LModel L π p f K ν) (hν : Function.Injective ν) {x : X}
    {y : GL (Fin 3) K} (hx : IsLiftAt ν x y) {E : Subgroup (GL (Fin 3) K)}
    (hE : E ≤ slPi π 3 (p ^ f) K) :
    (∀ e ∈ transp ν E, x * e * x⁻¹ ∈ transp ν E) ↔ ∀ e ∈ E, y * e * y⁻¹ ∈ E := by
  constructor
  · intro h e he
    have h1 := hx.act ⟨e, hE he⟩ (M.conjBy hx.mem ⟨e, hE he⟩) (M.coe_conjBy hx.mem _)
    obtain ⟨s', hs'E, hs'⟩ := mem_transp.1 (h _ ⟨⟨e, hE he⟩, he, rfl⟩)
    have hss : s' = M.conjBy hx.mem ⟨e, hE he⟩ := hν (Subtype.ext (hs'.trans h1))
    rw [hss, M.coe_conjBy] at hs'E
    exact hs'E
  · rintro h _ ⟨s, hs, rfl⟩
    refine ⟨M.conjBy hx.mem s, ?_, (hx.act s _ (M.coe_conjBy hx.mem s)).symm⟩
    change ((M.conjBy hx.mem s : ↥(slPi π 3 (p ^ f) K)) : GL (Fin 3) K) ∈ E
    rw [M.coe_conjBy]
    exact h _ hs

theorem candsX_eq_image (M : LModel L π p f K ν) (hν : Function.Injective ν) {x : X}
    {y : GL (Fin 3) K} (hx : IsLiftAt ν x y) :
    candsX L x = transp ν '' frameCands π (p ^ f) y := by
  ext E
  constructor
  · rintro ⟨hEL, hEa, hEc, hEZ, hEx⟩
    obtain ⟨E', hE', rfl⟩ := exists_transp_eq M hEL
    exact ⟨E', ⟨hE', (isElemAbelian_transp_iff hν hE').1 hEa,
      (card_transp hν hE').symm.trans hEc, (center_le_transp_iff M hν).1 hEZ,
      (conj_mem_transp_iff M hν hx hE').1 hEx⟩, rfl⟩
  · rintro ⟨E', ⟨hE', hEa, hEc, hEZ, hEy⟩, rfl⟩
    exact ⟨transp_le E', (isElemAbelian_transp_iff hν hE').2 hEa,
      (card_transp hν hE').trans hEc, (center_le_transp_iff M hν).2 hEZ,
      (conj_mem_transp_iff M hν hx hE').2 hEy⟩

theorem card_candsX (M : LModel L π p f K ν) (hν : Function.Injective ν) {x : X}
    {y : GL (Fin 3) K} (hx : IsLiftAt ν x y) :
    Nat.card ↥(candsX L x) = Nat.card ↥(frameCands π (p ^ f) y) := by
  rw [candsX_eq_image M hν hx]
  exact Nat.card_image_of_injOn fun E₁ h₁ E₂ h₂ h => transp_inj hν h₁.1 h₂.1 h

end P614K292CA

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614
