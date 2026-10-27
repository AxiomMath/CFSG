module

public import CFSG.LocalAnalysis.AGLEmbedding.ConstrainedSLAux
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbedding.ReducedQuotient
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SevenFourTwo

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.PreuniquenessRankFour.Helpers

variable {X : Type} [Group X] [Finite X] {p : ℕ}

theorem le_of_frattini [Fact p.Prime] (P : Sylow p X) {N K Y : Subgroup X}
    (hPN : (P : Subgroup X) ≤ N) (hKN : K ≤ N) (hNK : N ≤ Subgroup.normalizer (K : Set X))
    (hKY : K ≤ Y)
    (hY : Subgroup.normalizer (((P : Subgroup X) ⊓ K : Subgroup X) : Set X) ≤ Y) : N ≤ Y := by
  by_contra hNY
  have hK' : (K.subgroupOf N).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hKN).mpr hNK
  set P' : Sylow p N := P.subtype hPN with hP'
  have hP'map : ((P' : Subgroup N)).map N.subtype = P := by
    rw [hP', Sylow.coe_subtype, Subgroup.map_subgroupOf_eq_of_le hPN]
  have hinf : (((P' : Subgroup N) ⊓ K.subgroupOf N : Subgroup N)).map N.subtype =
      (P : Subgroup X) ⊓ K := by
    rw [Subgroup.map_inf _ _ _ N.subtype_injective, hP'map, Subgroup.map_subgroupOf_eq_of_le hKN]
  have hY' : Y.subgroupOf N ≠ ⊤ := by
    intro htop
    apply hNY
    intro n hn
    have : (⟨n, hn⟩ : N) ∈ Y.subgroupOf N := htop ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp this
  have hN' : Subgroup.normalizer ((((P' : Subgroup N) ⊓ K.subgroupOf N : Subgroup N)) : Set N) ≤
      Y.subgroupOf N := by
    intro g hg
    rw [Subgroup.mem_subgroupOf]
    apply hY
    have h1 := Subgroup.le_normalizer_map (H := ((P' : Subgroup N) ⊓ K.subgroupOf N : Subgroup N))
      N.subtype ⟨g, hg, rfl⟩
    rwa [hinf] at h1
  exact not_le_of_normalizer_inf_le P' hN' hY' fun k hk =>
    Subgroup.mem_subgroupOf.mpr (hKY (Subgroup.mem_subgroupOf.mp hk))

theorem map_ker_centerQuotientAction_le [Fact p.Prime] {D E : Subgroup X}
    (e : D ⧸ Subgroup.center D ≃* Multiplicative (Fin 2 → ZMod p)) (hED : E ≤ D)
    (hZE : (Subgroup.center D).map D.subtype ≤ E) :
    (centerQuotientAction D e).ker.map (Subgroup.normalizer (D : Set X)).subtype ≤
      Subgroup.normalizer (E : Set X) := by
  have key : ∀ g : Subgroup.normalizer (D : Set X), centerQuotientAction D e g = 1 →
      ∀ u ∈ E, (g : X) * u * (g : X)⁻¹ ∈ E := by
    intro g hg u hu
    have hgD : (g : X) * u * (g : X)⁻¹ ∈ D :=
      (Subgroup.mem_normalizer_iff.mp g.2 u).mp (hED hu)
    set u' : D := ⟨u, hED hu⟩
    set v' : D := ⟨(g : X) * u * (g : X)⁻¹, hgD⟩
    have hmv := centerQuotientAction_mulVec D e g (u := u') (v := v') rfl
    rw [hg, Units.val_one, Matrix.one_mulVec] at hmv
    have heq : ((u' : D ⧸ Subgroup.center D)) = (v' : D ⧸ Subgroup.center D) :=
      e.injective (Multiplicative.toAdd.injective hmv)
    have hz : u'⁻¹ * v' ∈ Subgroup.center D := QuotientGroup.eq.mp heq
    have hzE : ((u'⁻¹ * v' : D) : X) ∈ E := hZE ⟨_, hz, rfl⟩
    have : ((u'⁻¹ * v' : D) : X) = u⁻¹ * ((g : X) * u * (g : X)⁻¹) := rfl
    rw [this] at hzE
    have := E.mul_mem hu hzE
    simpa using this
  rintro _ ⟨g, hg, rfl⟩
  have hg : centerQuotientAction D e g = 1 := hg
  rw [Subgroup.mem_normalizer_iff]
  intro u
  refine ⟨key g hg u, fun hu => ?_⟩
  have hg' : centerQuotientAction D e g⁻¹ = 1 := by rw [map_inv, hg, inv_one]
  have := key g⁻¹ hg' _ hu
  simpa [mul_assoc] using this

theorem normalizer_le_of_normal_elemAbelian_sq (hp : p.Prime) (P : Sylow p X) {Y A : Subgroup X}
    (hPY : (P : Subgroup X) ≤ Y) (hW : GLBWeakCore p (P : Subgroup X) ≤ Y)
    (h3 : 3 ≤ Open.pRank p (P : Subgroup X)) (hA : IsElemAbelian p A) (hAc : Nat.card A = p ^ 2)
    (hAP : A ≤ P) (hPA : (P : Subgroup X) ≤ Subgroup.normalizer (A : Set X)) :
    Subgroup.normalizer (A : Set X) ≤ Y := by
  obtain ⟨F, hFP, hF, hFc⟩ := pRank_attained p hp (P : Subgroup X)
  exact normalizer_le_of_elementary_rank_two_normalized_by_rank_three p hp P hPY hW hF _ h3 hFc
    (hFP.trans hPY) hA hAc (hAP.trans hPY) (hFP.trans hPA)

end CFSG.LocalAnalysis.RankThreeTheoremC.SevenFourTwo
