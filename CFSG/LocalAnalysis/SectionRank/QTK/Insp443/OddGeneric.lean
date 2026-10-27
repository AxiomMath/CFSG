module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.RankThreeConcl
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.SixteenList
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.SixteenA5
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.SixteenA6
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.CentralKer

public section

namespace CFSG.SectionRank.QTK.Insp443

open Subgroup CFSG.Open

theorem KConfig.conclK_of_card_eq_sixteen
    {G : Type} [Group G] [Finite G] {L V MK : Subgroup G} (h : KConfig G L V MK)
    (hV : Nat.card V = 16) (hC : Subgroup.centralizer (V : Set G) ≤ V)
    (h7 : ∀ n ∈ Subgroup.normalizer (V : Set G),
      (∀ v ∈ V, n ^ 7 * v * (n ^ 7)⁻¹ = v) → ∀ v ∈ V, n * v * n⁻¹ = v) :
    ConclK G L V MK := by
  obtain ⟨hO, h6 | h5⟩ := h.sixteen_list hV hC h7
  · obtain ⟨e⟩ := h6
    exact h.conclK_of_sixteen_a6 hV hO hC e
  · obtain ⟨e⟩ := h5
    exact h.conclK_of_sixteen_a5 hV hO hC e

theorem KConf.conclK_of_rankFour
    {K : Type} [Group K] [Finite K] {L V MK : Subgroup K} (h : KConf K L V MK)
    (hF : CentralKer L V)
    (hle : ∀ E : Subgroup K, IsElemAbelian 2 E → Nat.card E ≤ 16)
    (h16 : ∀ E : Subgroup K, IsElemAbelian 2 E → Nat.card E = 16 →
      Subgroup.centralizer (E : Set K) ≤ E ∧ ∀ n ∈ Subgroup.normalizer (E : Set K),
        (∀ e ∈ E, n ^ 7 * e * (n ^ 7)⁻¹ = e) → ∀ e ∈ E, n * e * n⁻¹ = e) :
    ConclK K L V MK := by
  have hc := h.kConfig
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hc.elemAbelian.isPGroup
  have hV16 := hle V hc.elemAbelian
  have h8 := hc.eight_le_card
  rw [hk] at hV16 h8
  have hk3 : 3 ≤ k := by
    by_contra hlt
    have : 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hk4 : k ≤ 4 := by
    by_contra hlt
    have : 2 ^ 5 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  interval_cases k
  · exact hc.conclK_of_card_le_eight hF (by norm_num [hk])
  · have hV : Nat.card V = 16 := by norm_num [hk]
    obtain ⟨hC, h7⟩ := h16 V hc.elemAbelian hV
    exact hc.conclK_of_card_eq_sixteen hV hC h7

theorem card_le_sixteen_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (hY : ∀ E : Subgroup Y, IsElemAbelian 2 E → Nat.card E ≤ 16) :
    ∀ E : Subgroup X, IsElemAbelian 2 E → Nat.card E ≤ 16 := by
  intro E hE
  have h := hY (E.map e.toMonoidHom) (hE.map _)
  rwa [Subgroup.card_map_of_injective e.injective] at h

theorem sixteen_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (hY : ∀ E : Subgroup Y, IsElemAbelian 2 E → Nat.card E = 16 →
      Subgroup.centralizer (E : Set Y) ≤ E ∧ ∀ n ∈ Subgroup.normalizer (E : Set Y),
        (∀ x ∈ E, n ^ 7 * x * (n ^ 7)⁻¹ = x) → ∀ x ∈ E, n * x * n⁻¹ = x) :
    ∀ E : Subgroup X, IsElemAbelian 2 E → Nat.card E = 16 →
      Subgroup.centralizer (E : Set X) ≤ E ∧ ∀ n ∈ Subgroup.normalizer (E : Set X),
        (∀ x ∈ E, n ^ 7 * x * (n ^ 7)⁻¹ = x) → ∀ x ∈ E, n * x * n⁻¹ = x := by
  intro E hE hE16
  obtain ⟨hC, h7⟩ := hY (E.map e.toMonoidHom) (hE.map _)
    (by rwa [Subgroup.card_map_of_injective e.injective])
  refine ⟨fun c hc => ?_, fun n hn hn7 x hx => ?_⟩
  · have hc' : e c ∈ Subgroup.centralizer ((E.map e.toMonoidHom : Subgroup Y) : Set Y) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨y, hy, rfl⟩
      change e y * e c = e c * e y
      rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hc y hy]
    obtain ⟨y, hy, hyc⟩ := hC hc'
    rwa [show y = c from e.injective hyc] at hy
  · have hn' : e n ∈ Subgroup.normalizer ((E.map e.toMonoidHom : Subgroup Y) : Set Y) := by
      rw [← Subgroup.map_equiv_normalizer_eq]
      exact ⟨n, hn, rfl⟩
    have h7' := h7 (e n) hn' (by
      rintro _ ⟨y, hy, rfl⟩
      change e n ^ 7 * e y * (e n ^ 7)⁻¹ = e y
      rw [← map_pow, ← map_inv, ← map_mul, ← map_mul, hn7 y hy])
      (e x) ⟨x, hx, rfl⟩
    apply e.injective
    rw [map_mul, map_mul, map_inv]
    exact h7'

end CFSG.SectionRank.QTK.Insp443

end
