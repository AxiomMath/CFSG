module

public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Fact1019

open CFSG.Open Subgroup

theorem isElemAbelian_range_of_hom {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    (f : Multiplicative (Fin 4 → ZMod p) →* G) (hf : Function.Injective f) :
    IsElemAbelian p f.range ∧ Nat.card f.range = p ^ 4 := by
  refine ⟨⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩, ?_⟩
  · obtain ⟨a, ha⟩ := x.2
    obtain ⟨b, hb⟩ := y.2
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← ha, ← hb, ← map_mul, ← map_mul, mul_comm]
  · obtain ⟨a, rfl⟩ := MonoidHom.mem_range.1 hx
    have hap : a ^ p = 1 := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow, toAdd_one]
      funext k
      simp [ZMod.natCast_self]
    rw [← map_pow, hap, map_one]
  · rw [← Nat.card_congr (MonoidHom.ofInjective hf).toEquiv,
      Nat.card_congr Multiplicative.toAdd]
    simp [Nat.card_pi, Nat.card_zmod]

theorem exists_subgroup_of_hom {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    (f : Multiplicative (Fin 4 → ZMod p) →* G) (hf : Function.Injective f) (t : G)
    (hc : ∀ a, t * f a = f a * t) :
    ∃ E : Subgroup G, E ≤ Subgroup.centralizer {t} ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 4 := by
  obtain ⟨hE, hcard⟩ := isElemAbelian_range_of_hom f hf
  refine ⟨f.range, ?_, hE, hcard⟩
  rintro x ⟨a, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  rw [Set.mem_singleton_iff.1 hh]
  exact hc a

theorem exists_involution_transport {K G : Type} [Group K] [Group G] (e : K ≃* G) {p : ℕ}
    [Fact p.Prime] {t : G} {E : Subgroup G} (hEc : E ≤ Subgroup.centralizer {t})
    (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ 4) :
    ∃ t' : K, orderOf t' = orderOf t ∧ ∃ E' : Subgroup K, E' ≤ Subgroup.centralizer {t'} ∧
      IsElemAbelian p E' ∧ Nat.card E' = p ^ 4 := by
  refine ⟨e.symm t, ?_, E.map e.symm.toMonoidHom, ?_, ?_, ?_⟩
  · exact orderOf_injective e.symm.toMonoidHom e.symm.injective t
  · rintro x ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.1 hh]
    have hyc : t * y = y * t := Subgroup.mem_centralizer_iff.1 (hEc hy) t (Set.mem_singleton t)
    change e.symm t * e.symm y = e.symm y * e.symm t
    rw [← map_mul, ← map_mul, hyc]
  · exact CFSG.SectionRank.isElemAbelian_map hE e.symm.toMonoidHom
  · rw [Subgroup.card_map_of_injective (f := e.symm.toMonoidHom) e.symm.injective, hcard]

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Fact1019
