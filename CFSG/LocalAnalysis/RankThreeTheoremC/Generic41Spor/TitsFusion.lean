module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.TitsStruct
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Fusion
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.LinesCore
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.PlaneQuot

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3 (u3S u3T u3ZT u3U0 U3LineWC GenericComponentClass TypeSE
  Lemma33Data U3Lemma33 lemma33_gen u3f_false_of_lines fusion_of_wc_S fus_exists_mul_of_sup_eq
  fus_mem_zpowers_of_isCyclic_of_pow_prime)

variable {G : Type} [Group G] [Finite G]

theorem typeSE_tits : TypeSE IsTitsType 5 := by
  intro K _ _ hK
  obtain ⟨-, hv, ⟨e⟩⟩ := hK
  exact ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inl ⟨hv, ⟨e⟩⟩⟩)))),
    TauCeti.CFSGIndex.lie ⟨.tits, hv⟩, ⟨e⟩⟩

section Plane

variable {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x : G} {J : Subgroup G}
  {Typ : ℕ → ∀ (Q : Type) [Group Q], Prop}

theorem plane_fusion_core (hS : Setting G) (hD1 : TheoremD1 G) (hSig : SignalizerTwoGroupKFact)
    (hsyl : ∀ (K : Type) [Group K] [Finite K], Typ p K → SylowIsPlane p K)
    (hno : ∀ (K : Type) [Group K] [Finite K], Typ p K → NoOuterP p K)
    (htrans : ∀ (K : Type) [Group K] [Finite K], Typ p K → NormalizerTransitive p K)
    (hSE : TypeSE Typ p) (hc : PointConfig Typ G p P M x J) :
    (P : Subgroup G) ≤ Subgroup.centralizer ({x} : Set G) ∧ U3LineWC x (P : Subgroup G) := by
  classical
  have hp : p.Prime := hc.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hx1 : x ≠ 1 := hc.generic.2.1.2.1
  have hxp : x ^ p = 1 := hc.generic.2.1.2.2.1
  obtain ⟨hTcard, hTel, hxJ⟩ := plane_T_structure hsyl hc
  have hSab := plane_abelian hsyl hno hc
  have hΩ := plane_omega hsyl hno hc
  have hL33 := plane_lemma33 hS hD1 hSig hsyl hno hSE hc
  have htr := tits_trans_of_quotient htrans hc
  have hTS : u3T P x J ≤ u3S P x := inf_le_left
  have hTJ : u3T P x J ≤ J := inf_le_right
  have hSC : ∀ s ∈ u3S P x, s * x = x * s := fun s hs =>
    Subgroup.mem_centralizer_singleton_iff.mp hs.2
  have hxT : x ∉ u3T P x J := fun h => hxJ (hTJ h)
  have hSyl : IsSylowOf p (u3S P x) (Subgroup.centralizer ({x} : Set G)) := hc.generic.2.2.1
  have hNtrans := conjLinesIn_normalizer_trans hSyl hSab
  have hΓx : ∀ γ ∈ J ⊓ Subgroup.normalizer ((u3T P x J : Subgroup G) : Set G), γ * x = x * γ :=
    fun γ hγ => Subgroup.mem_centralizer_singleton_iff.mp (hc.le_cent hγ.1)
  have hPow : ∀ t ∈ u3T P x J, t ≠ 1 → ∀ k : ℕ, ¬ p ∣ k →
      ∃ γ ∈ J ⊓ Subgroup.normalizer ((u3T P x J : Subgroup G) : Set G), γ * t * γ⁻¹ = t ^ k := by
    intro t ht ht1 k hk
    have hto : orderOf t = p := orderOf_eq_prime (hTel.2 t ht) ht1
    have hkT : t ^ k ∈ u3T P x J := (u3T P x J).pow_mem ht k
    have hk1 : t ^ k ≠ 1 := by
      intro h
      exact hk (hto ▸ orderOf_dvd_of_pow_eq_one h)
    obtain ⟨n, hn, hnt⟩ := htr t ht ht1 (t ^ k) hkT hk1
    exact ⟨n, hn, hnt⟩
  have hLtrans : ∀ s ∈ u3T P x J, ∀ s' ∈ u3T P x J, s ≠ 1 → s' ≠ 1 →
      Subgroup.zpowers s ∉ (∅ : Finset (Subgroup G)) → Subgroup.zpowers s' ∉ (∅ : Finset (Subgroup G)) →
      ∃ γ ∈ J ⊓ Subgroup.normalizer ((u3T P x J : Subgroup G) : Set G),
        γ * s * γ⁻¹ ∈ Subgroup.zpowers s' := by
    intro s hs s' hs' hs1 hs'1 _ _
    obtain ⟨n, hn, hns⟩ := htr s hs hs1 s' hs' hs'1
    exact ⟨n, hn, hns ▸ Subgroup.mem_zpowers s'⟩
  have hD := lines_core hc.five (∅ : Finset (Subgroup G)) hx1 hxp hTS hSC hTel hTcard hxT hΩ hL33
    hΓx hPow (by simp) hLtrans hNtrans
  refine fusion_of_wc_S hc fun g hg => ?_
  have hmem : (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom ∈ conjLinesIn x (u3S P x) :=
    ⟨g, rfl, hg⟩
  rcases hD _ hmem with h | h
  · exact h
  · exact absurd h (Finset.notMem_empty _)

end Plane

variable {P : Sylow 5 G} {M : Subgroup G} {x : G} {J : Subgroup G}

theorem tits_fusion_core (hS : Setting G) (hD1 : TheoremD1 G) (hU0 : FullCoreLocal G)
    (hSig : SignalizerTwoGroupKFact) (hX : TitsFacts) (hc : PointConfig IsTitsType G 5 P M x J) :
    (P : Subgroup G) ≤ Subgroup.centralizer ({x} : Set G) ∧ U3LineWC x (P : Subgroup G) :=
  plane_fusion_core hS hD1 hSig hX.sylow hX.noOuter hX.trans typeSE_tits hc

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
