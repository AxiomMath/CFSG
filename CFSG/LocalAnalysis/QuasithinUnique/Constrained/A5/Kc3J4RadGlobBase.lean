
module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4RadBase
public import CFSG.Sporadic.J4.Local

@[expose] public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint CFSG.Sporadic.J4

theorem exists_involution_of_conj_le {Y : Type} [Group Y] (Hy : Subgroup Y)
    (hH : ∀ L : Subgroup Y, L ≤ Hy → D5Plus L → ⁅L, L⁆ = L →
      ∃ y : Y, orderOf y = 2 ∧ ∀ l ∈ L, l * y = y * l)
    {L : Subgroup Y} (hL : D5Plus L) (hLp : ⁅L, L⁆ = L) {g : Y}
    (hg : L ≤ Hy.map (MulAut.conj g).toMonoidHom) :
    ∃ y : Y, orderOf y = 2 ∧ ∀ l ∈ L, l * y = y * l := by
  let c : Y →* Y := (MulAut.conj g⁻¹).toMonoidHom
  have hcinj : Function.Injective c := (MulAut.conj g⁻¹).injective
  have hL'' : D5Plus (L.map c) := d5Plus_map c hcinj hL
  have hLp'' : ⁅L.map c, L.map c⁆ = L.map c := by
    rw [← Subgroup.map_commutator, hLp]
  have hle : L.map c ≤ Hy := by
    rintro _ ⟨l, hl, rfl⟩
    obtain ⟨h, hh, hhl⟩ := hg hl
    have : c l = h := by
      have h1 : g * h * g⁻¹ = l := by simpa [MulAut.conj_apply] using hhl
      show g⁻¹ * l * g⁻¹⁻¹ = h
      rw [← h1]
      group
    rw [this]
    exact hh
  obtain ⟨y, hyo, hyc⟩ := hH (L.map c) hle hL'' hLp''
  refine ⟨g * y * g⁻¹, ?_, fun l hl => ?_⟩
  · have := (MulAut.conj g).orderOf_eq y
    rw [MulAut.conj_apply] at this
    rw [this]
    exact hyo
  · have h1 := hyc (c l) ⟨l, hl, rfl⟩
    have h2 : g⁻¹ * l * g * y = y * (g⁻¹ * l * g) := by simpa [c, MulAut.conj_apply] using h1
    calc l * (g * y * g⁻¹) = g * ((g⁻¹ * l * g) * y) * g⁻¹ := by group
      _ = g * (y * (g⁻¹ * l * g)) * g⁻¹ := by rw [h2]
      _ = g * y * g⁻¹ * l := by group

def J4GlobalRad : Prop :=
  ∀ L : Subgroup ↥J, D5Plus L → ⁅L, L⁆ = L →
    (∀ g : ↥J, ¬ L ≤ Hj.map (MulAut.conj g).toMonoidHom) →
    (¬ ∃ y : ↥J, orderOf y = 2 ∧ ∀ l ∈ L, l * y = y * l) →
    Subgroup.centralizer (blockRadAbs L : Set ↥J) ≤ blockRadAbs L ∧
      ∃ g ∈ L, orderOf g = 5 ∧
        16 < (blockRadAbs L ⊓ Subgroup.centralizer ({g} : Set ↥J)).relIndex (blockRadAbs L)

end CFSG.QuasithinUnique.A5
