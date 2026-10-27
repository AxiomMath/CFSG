module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.PropA.Emb

public section

namespace CFSG.EvenSporadicStandard.M12Std.PropA

open Subgroup

theorem exists_isEmb_of_injective {G P : Type*} [Group G] [Group P] {L : Subgroup G} {t x : G}
    {K D : Subgroup P} {t₀ x₀ : P} (ι : ↥(centralizer ({t} : Set G)) →* P)
    (hinj : Function.Injective ι) (hrange : ι.range = K) (hL : push ι L = D)
    (ht : ∀ c : ↥(centralizer ({t} : Set G)), (c : G) = t → ι c = t₀)
    (htL : t ∈ centralizer (L : Set G)) (hxL : x ∈ L) (hx2 : orderOf x = 2)
    (hx : Nat.card ↥(L ⊓ centralizer ({x} : Set G)) = 240)
    (hcent : ∀ k ∈ K, k * t₀ = t₀ * k) (hDK : D ≤ K)
    (hI3 : ∀ y ∈ D, orderOf y = 2 → Nat.card ↥(D ⊓ centralizer ({y} : Set P)) = 240 →
      ∃ a ∈ D, a * y * a⁻¹ = x₀) :
    ∃ ι' : ↥(centralizer ({t} : Set G)) →* P, IsEmb L t x K D t₀ x₀ ι' := by
  have hLC : L ≤ centralizer ({t} : Set G) := by
    intro l hl
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp htL) l hl
  let c₀ : ↥(centralizer ({t} : Set G)) := ⟨x, hLC hxL⟩
  let y : P := ι c₀
  have hc₀val : (c₀ : G) = x := rfl
  have hyD : y ∈ D := by
    rw [← hL]
    exact (mem_push ι).mpr ⟨c₀, hxL, rfl⟩
  have hy2 : orderOf y = 2 := by
    change orderOf (ι c₀) = 2
    rw [orderOf_injective ι hinj c₀, Subgroup.orderOf_mk, hx2]
  have hpushC : push ι (L ⊓ centralizer ({x} : Set G)) =
      D ⊓ centralizer ({y} : Set P) := by
    rw [push_inf hinj L (centralizer ({x} : Set G)),
      push_centralizer_singleton hinj (hLC hxL), hL, hrange]
    rw [show ι ⟨x, hLC hxL⟩ = y from rfl, ← inf_assoc,
      inf_eq_left.mpr (le_trans inf_le_left hDK)]
  have hcard : Nat.card ↥(D ⊓ centralizer ({y} : Set P)) = 240 := by
    rw [← hpushC, card_push hinj (le_trans inf_le_left hLC)]
    exact hx
  obtain ⟨a, haD, hay⟩ := hI3 y hyD hy2 hcard
  let χ : P →* P := (MulAut.conj a).toMonoidHom
  let ι' : ↥(centralizer ({t} : Set G)) →* P := χ.comp ι
  have hχapp : ∀ p : P, χ p = a * p * a⁻¹ := fun p => MulAut.conj_apply a p
  have hχinj : Function.Injective χ := (MulAut.conj a).injective
  have haK : a ∈ K := hDK haD
  have hDconj : D.map χ = D :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer haD)
  have hKconj : K.map χ = K :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer haK)
  have hconjt₀ : a * t₀ * a⁻¹ = t₀ := by
    rw [hcent a haK, mul_assoc, mul_inv_cancel, mul_one]
  refine ⟨ι', ?_, ?_, ?_, ?_, ?_, htL, hxL⟩
  · change Function.Injective (χ.comp ι)
    exact hχinj.comp hinj
  · change (χ.comp ι).range = K
    rw [MonoidHom.range_comp, hrange, hKconj]
  · have hpush : push ι' L = (push ι L).map χ := by
      ext p
      rw [mem_push, Subgroup.mem_map]
      constructor
      · rintro ⟨c, hc, hcp⟩
        exact ⟨ι c, (mem_push ι).mpr ⟨c, hc, rfl⟩, hcp⟩
      · rintro ⟨q, hq, hqp⟩
        rw [mem_push] at hq
        obtain ⟨c, hc, rfl⟩ := hq
        exact ⟨c, hc, hqp⟩
    rw [hpush, hL, hDconj]
  · intro c hc
    change χ (ι c) = t₀
    rw [hχapp, ht c hc]
    exact hconjt₀
  · intro c hc
    have hc_eq : c = c₀ := Subtype.ext (by rw [hc, hc₀val])
    change χ (ι c) = x₀
    rw [hc_eq, hχapp]
    simpa only [y] using hay

end CFSG.EvenSporadicStandard.M12Std.PropA
