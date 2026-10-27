module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7RPr

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] {t : G} {P U : Subgroup G}

theorem Wr7.not_isConj (h : Wr7 t P U) (hU : RankFacts U)
    (hb : ∀ E : Subgroup G, E ≤ centralizer ({t} : Set G) → IsElemAbelian 2 E → Nat.card E ≤ 16) :
    ∀ x ∈ P, ¬ IsConj t x := by
  intro x hx hconj
  obtain ⟨g, hg⟩ := isConj_iff.mp hconj
  have ht : t = g⁻¹ * x * g := by rw [← hg]; group
  have hx2 : x ^ 2 = 1 := by
    have hp := hconj.pow 2
    rw [h.t_sq] at hp
    exact isConj_one_right.mp hp
  obtain ⟨E, _hEP, hEel, hEcard, hEx⟩ := Wr7.rank_cover h hU hx hx2
  have hE'el : IsElemAbelian 2 (conjSub g⁻¹ E) := hEel.map (MulAut.conj g⁻¹).toMonoidHom
  have hE'card : Nat.card (conjSub g⁻¹ E) = 64 := by
    rw [show conjSub g⁻¹ E = E.map (MulAut.conj g⁻¹).toMonoidHom from rfl,
      ← Nat.card_congr (Subgroup.equivMapOfInjective E (MulAut.conj g⁻¹).toMonoidHom
        (MulAut.conj g⁻¹).injective).toEquiv]
    exact hEcard
  have hE'le : conjSub g⁻¹ E ≤ centralizer ({t} : Set G) := by
    intro e he
    rw [Subgroup.mem_centralizer_singleton_iff]
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp he
    have hyx : y * x = x * y := Subgroup.mem_centralizer_singleton_iff.mp (hEx hy)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc (g⁻¹ * y * (g⁻¹)⁻¹) * t = g⁻¹ * (y * x) * g := by rw [ht]; group
      _ = g⁻¹ * (x * y) * g := by rw [hyx]
      _ = t * (g⁻¹ * y * (g⁻¹)⁻¹) := by rw [ht]; group
  have hle := hb (conjSub g⁻¹ E) hE'le hE'el
  omega

end CFSG.OddStandard.HigherRank.YamadaG23
