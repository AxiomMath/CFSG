module

public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.GlueCen

public section

namespace CFSG.EvenSporadicStandard.RuStd.S2.Glue

open Subgroup

variable {G : Type} [Group G] {L : Subgroup G} {t : G}

theorem card_cen_t_five (hc : Config G L t) (h5 : RuFiveFacts L) {h : G} (hht : h * t = t * h)
    (ho : orderOf h = 5) :
    Nat.card ↥(centralizer ({t} : Set G) ⊓ centralizer ({h} : Set G)) = 600 ∨
      Nat.card ↥(centralizer ({t} : Set G) ⊓ centralizer ({h} : Set G)) = 2000 := by
  have hL : h ∈ L := mem_of_odd_orderOf hc hht (by rw [ho]; decide)
  have hzt : zpowers t ≤ centralizer ((L ⊓ centralizer ({h} : Set G) : Subgroup G) : Set G) := by
    rw [zpowers_le]
    exact mem_centralizer_iff.2 fun l hl => (hc.comm l hl.1)
  have hdisj : Disjoint (L ⊓ centralizer ({h} : Set G)) (zpowers t) :=
    hc.disjoint.mono_left inf_le_left
  have hK : centralizer ({t} : Set G) ⊓ centralizer ({h} : Set G) =
      (L ⊓ centralizer ({h} : Set G)) ⊔ zpowers t := by
    apply le_antisymm
    · intro x hx
      obtain ⟨hxt, hxh⟩ := mem_inf.mp hx
      rcases hc.mem_cases hxt with hxL | ⟨l, hl, rfl⟩
      · exact mem_sup_left ⟨hxL, hxh⟩
      · have hlh : l ∈ centralizer ({h} : Set G) := by
          rw [mem_centralizer_singleton_iff] at hxh ⊢
          have : t * (l * h) = t * (h * l) := by
            calc t * (l * h) = t * l * h := by group
              _ = h * (t * l) := hxh
              _ = t * h * l := by rw [← mul_assoc, hht]
              _ = t * (h * l) := by group
          exact mul_left_cancel this
        exact mul_mem (mem_sup_right (mem_zpowers t)) (mem_sup_left ⟨hl, hlh⟩)
    · apply sup_le
      · exact le_inf (inf_le_left.trans hc.le_centralizer) inf_le_right
      · rw [zpowers_le]
        exact ⟨mem_centralizer_singleton_iff.2 rfl, mem_centralizer_singleton_iff.2 hht.symm⟩
  rw [hK, ← Nat.card_congr (mulEquivProdSup hzt hdisj).toEquiv, Nat.card_prod,
    Nat.card_zpowers, hc.orderOf_z]
  have hcard := card_cen_eq (K := L) ⟨h, hL⟩
  have ho' : orderOf (⟨h, hL⟩ : L) = 5 := by rw [Subgroup.orderOf_mk]; exact ho
  rw [← hcard]
  rcases h5.typeAB _ ho' with ⟨h3, -⟩ | ⟨h1, -⟩
  · left; rw [h3]
  · right; rw [h1]

theorem card_cen_conj_five (hc : Config G L t) (h5 : RuFiveFacts L) {e h : G} (he : IsConj t e)
    (heh : h * e = e * h) (ho : orderOf h = 5) :
    Nat.card ↥(centralizer ({e} : Set G) ⊓ centralizer ({h} : Set G)) = 600 ∨
      Nat.card ↥(centralizer ({e} : Set G) ⊓ centralizer ({h} : Set G)) = 2000 := by
  obtain ⟨g, hg⟩ := isConj_iff.mp he
  set h' := g⁻¹ * h * g
  have hh't : h' * t = t * h' := by
    have : t = g⁻¹ * e * g := by rw [← hg]; group
    rw [this]
    calc g⁻¹ * h * g * (g⁻¹ * e * g) = g⁻¹ * (h * e) * g := by group
      _ = g⁻¹ * (e * h) * g := by rw [heh]
      _ = g⁻¹ * e * g * (g⁻¹ * h * g) := by group
  have ho' : orderOf h' = 5 := by
    rw [show h' = MulAut.conj g⁻¹ h by simp [h', MulAut.conj_apply]]
    rw [MulEquiv.orderOf_eq]; exact ho
  have hmap : (centralizer ({t} : Set G) ⊓ centralizer ({h'} : Set G)).map
      (MulAut.conj g).toMonoidHom = centralizer ({e} : Set G) ⊓ centralizer ({h} : Set G) := by
    ext x
    simp only [mem_map, mem_inf, mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, h']
    constructor
    · rintro ⟨y, ⟨hy1, hy2⟩, rfl⟩
      rw [← hg]
      constructor
      · calc g * y * g⁻¹ * (g * t * g⁻¹) = g * (y * t) * g⁻¹ := by group
          _ = g * (t * y) * g⁻¹ := by rw [hy1]
          _ = g * t * g⁻¹ * (g * y * g⁻¹) := by group
      · calc g * y * g⁻¹ * h = g * (y * (g⁻¹ * h * g)) * g⁻¹ := by group
          _ = g * (g⁻¹ * h * g * y) * g⁻¹ := by rw [hy2]
          _ = h * (g * y * g⁻¹) := by group
    · rintro ⟨hx1, hx2⟩
      refine ⟨g⁻¹ * x * g, ⟨?_, ?_⟩, by group⟩
      · rw [← hg] at hx1
        calc g⁻¹ * x * g * t = g⁻¹ * (x * (g * t * g⁻¹)) * g := by group
          _ = g⁻¹ * (g * t * g⁻¹ * x) * g := by rw [hx1]
          _ = t * (g⁻¹ * x * g) := by group
      · calc g⁻¹ * x * g * (g⁻¹ * h * g) = g⁻¹ * (x * h) * g := by group
          _ = g⁻¹ * (h * x) * g := by rw [hx2]
          _ = g⁻¹ * h * g * (g⁻¹ * x * g) := by group
  rw [← hmap, Subgroup.card_map_of_injective (MulAut.conj g).injective]
  exact card_cen_t_five hc h5 hh't ho'

end CFSG.EvenSporadicStandard.RuStd.S2.Glue
