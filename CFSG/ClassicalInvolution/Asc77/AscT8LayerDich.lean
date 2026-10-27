module

public import CFSG.ClassicalInvolution.Asc77.AscT8LayerSec
public import CFSG.ClassicalInvolution.Asc77.AscIHSectL
public import CFSG.ClassicalInvolution.Asc77.AscT8Thm4

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped commutatorElement

namespace T8

section Adj

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

theorem omegaNbr_of_commutes {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}
    {K J : Subgroup X} (hJ : J ∈ Φ) (hne : K ≠ J) (h : Commutes K J) : J ∈ omegaNbr Φ K := by
  refine ⟨hJ, hne.symm, ?_⟩
  obtain ⟨P⟩ : Nonempty (Sylow 2 ↥J) := inferInstance
  refine ⟨Subgroup.map J.subtype (P : Subgroup ↥J), ⟨J, hJ, P, rfl⟩, Subgroup.map_subtype_le _, ?_⟩
  rintro _ ⟨r, -, rfl⟩
  refine Subgroup.centralizer_le_normalizer (K : Set X) ?_
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  exact h k hk r r.2

theorem layer_omegaNbr (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω) {x : G}
    (hx : x * x = 1) {K J : Subgroup G} (hK : XMem Ω x K) (hJ : XMem Ω x J)
    (m : ↥(layerJoin Ω x))
    (h : (layerRes x J).subgroupOf (layerJoin Ω x) ∈
      omegaNbr (restrictFamily (layerSet Ω x) (layerJoin Ω x))
        (conjSub m ((layerRes x K).subgroupOf (layerJoin Ω x)))) :
    J ∈ omegaNbr Ω (conjSub (m : G) K) := by
  obtain ⟨-, hne, T', hT'R, hT'J, hT'N⟩ := h
  have hmc : (m : G) ∈ cenZ x := layerJoin_le_cenZ x m.2
  have hKm : XMem Ω x (conjSub (m : G) K) := hK.conj hΩ hmc
  have hLm : layerRes x (conjSub (m : G) K) = conjSub (m : G) (layerRes x K) :=
    (layerRes_conj K hmc).symm
  have hYJ : layerRes x J ≤ layerJoin Ω x := le_layerJoin ⟨J, hJ, rfl⟩
  have hYKm : layerRes x (conjSub (m : G) K) ≤ layerJoin Ω x := le_layerJoin ⟨_, hKm, rfl⟩
  have hTJ : T'.map (layerJoin Ω x).subtype ≤ layerRes x J := by
    have := Subgroup.map_mono (f := (layerJoin Ω x).subtype) hT'J
    rwa [Subgroup.map_subgroupOf_eq_of_le hYJ] at this
  obtain ⟨J₀, ⟨J₀', hJ₀', rfl⟩, hJ₀Y, hTJ₀⟩ := exists_isSylow2In_of_mem_RSet_restrict hT'R
  have hTK₀ : IsSylow2In (T'.map (layerJoin Ω x).subtype) J₀' :=
    hJ₀'.isSylow2In_of_layerRes hp hq hΩ hx hTJ₀
  have h8 := hΩ.eight_le_of_mem_RSet hp (mem_RSet_of_isSylow2In hJ₀'.1 hTK₀)
  have hJJ : J₀' = J := hΩ.eq_of_le_of_le hJ₀'.1 hJ.1 hTK₀.2.1 (by omega) hTK₀.1
    (hTJ.trans (layerRes_le x J))
  subst hJJ
  have hKJ : conjSub (m : G) K ≠ J₀' := by
    intro hKJ
    apply hne
    rw [← hKJ, hLm, conjSub_subgroupOf]
  obtain ⟨z', hz'⟩ := hΩ.exists_uniqueInvolution hp hq hKm.1
  have hz'L := hKm.isUniqueInvolution_layerRes hp hq hΩ hx hz'
  have hYm : conjSub (m : G) (layerRes x K) ≤ layerJoin Ω x := by
    rw [← hLm]
    exact hYKm
  have hTN : T'.map (layerJoin Ω x).subtype ≤
      Subgroup.normalizer (layerRes x (conjSub (m : G) K) : Set G) := by
    rintro _ ⟨u', hu', rfl⟩
    have h1 := hT'N hu'
    rw [conjSub_subgroupOf] at h1
    show (u' : G) ∈ _
    rw [hLm]
    exact (mem_normalizer_subgroupOf_iff hYm).mpr h1
  have hAc : T'.map (layerJoin Ω x).subtype ≤ Subgroup.centralizer ({z'} : Set G) := by
    intro u hu
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := conj_eq_of_conjSub_eq hz' (layerRes_le x (conjSub (m : G) K)) hz'L.mem
      (mem_normalizer_iff_conjSub_eq.mp (hTN hu))
    calc u * z' = (u * z' * u⁻¹) * u := by group
      _ = z' * u := by rw [this]
  have hTNK : T'.map (layerJoin Ω x).subtype ≤ Subgroup.normalizer (conjSub (m : G) K : Set G) :=
    hΩ.le_normalizer_of_le_centralizer hp hq hKm.1 hJ₀'.1 hKJ hz' hTK₀.1 hTK₀.2.1 (by omega) hAc
  exact ⟨hJ₀'.1, fun h => hKJ h.symm, _, mem_RSet_of_isSylow2In hJ₀'.1 hTK₀, 
    hTJ.trans (layerRes_le x J₀'), hTNK⟩

theorem XMem.eq_of_layerRes_eq (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω) {x : G}
    (hx : x * x = 1) {K J : Subgroup G} (hK : XMem Ω x K) (hJ : XMem Ω x J)
    (h : layerRes x K = layerRes x J) : K = J := by
  obtain ⟨V, hV, -⟩ := IsSylow2In.exists_ge (IsPGroup.of_bot : IsPGroup 2 (⊥ : Subgroup G))
    (bot_le : (⊥ : Subgroup G) ≤ layerRes x K)
  have hVK := hK.isSylow2In_of_layerRes hp hq hΩ hx hV
  have hVJ := hJ.isSylow2In_of_layerRes hp hq hΩ hx (h ▸ hV)
  have h8 := hΩ.eight_le_of_mem_RSet hp (mem_RSet_of_isSylow2In hK.1 hVK)
  exact hΩ.eq_of_le_of_le hK.1 hJ.1 hVK.2.1 (by omega) hVK.1 hVJ.1

end Adj

section Dichotomy

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

theorem layer_dichotomy (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hnt : ∀ K ∈ Ω, ∀ K' ∈ twinSet Ω K, K' = K) {x : G} (hx : x * x = 1) {n : ℕ}
    (hn : CITBelowU p f n) (hlt : Nat.card (LayerQuot Ω x) < n) {K J : Subgroup G}
    (hK : XMem Ω x K) (hJ : XMem Ω x J) :
    (∃ y ∈ layerJoin Ω x, J = conjSub y K) ∨
      (∃ m ∈ layerJoin Ω x, J ∈ omegaNbr Ω (conjSub m K)) := by
  have hodd : Odd (Nat.card (classicalInvolutionOddCore ↥(layerJoin Ω x))) :=
    CFSG.ComponentClassification.OddCore.odd_card ↥(layerJoin Ω x)
  have hΛ := hypOmegaMod_layer hp hq hΩ hx
  have hΨ := hypOmegaMod_layerQuot hp hq hΩ hx
  have hKL : layerRes x K ∈ layerSet Ω x := ⟨K, hK, rfl⟩
  have hJL : layerRes x J ∈ layerSet Ω x := ⟨J, hJ, rfl⟩
  have hK'Λ : (layerRes x K).subgroupOf (layerJoin Ω x) ∈
      restrictFamily (layerSet Ω x) (layerJoin Ω x) := ⟨_, hKL, le_layerJoin hKL, rfl⟩
  have hJ'Λ : (layerRes x J).subgroupOf (layerJoin Ω x) ∈
      restrictFamily (layerSet Ω x) (layerJoin Ω x) := ⟨_, hJL, le_layerJoin hJL, rfl⟩
  by_cases hconj : ∃ g : LayerQuot Ω x,
      conjSub g (((layerRes x K).subgroupOf (layerJoin Ω x)).map
        (QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerJoin Ω x)))) =
      ((layerRes x J).subgroupOf (layerJoin Ω x)).map
        (QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerJoin Ω x)))
  · obtain ⟨g, hg⟩ := hconj
    obtain ⟨y₀, rfl⟩ := QuotientGroup.mk_surjective g
    left
    have h1 : (conjSub y₀ ((layerRes x K).subgroupOf (layerJoin Ω x))).map
        (QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerJoin Ω x))) =
        ((layerRes x J).subgroupOf (layerJoin Ω x)).map
          (QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerJoin Ω x))) := by
      rw [AscQuot.map_conjSub]
      exact hg
    obtain ⟨m, hm, hJ'⟩ := exists_conj_of_map_eq hp hq hΛ hodd (hΛ.conjInvariant y₀ _ hK'Λ) hJ'Λ h1
    have hy : ((m * y₀ : ↥(layerJoin Ω x)) : G) ∈ layerJoin Ω x := (m * y₀).2
    have hyc : ((m * y₀ : ↥(layerJoin Ω x)) : G) ∈ cenZ x := layerJoin_le_cenZ x hy
    refine ⟨((m * y₀ : ↥(layerJoin Ω x)) : G), hy, ?_⟩
    rw [← conjSub_mul, conjSub_subgroupOf] at hJ'
    have h2 := Subgroup.subgroupOf_inj.mp hJ'
    rw [inf_eq_left.mpr (le_layerJoin hJL)] at h2
    have h3 : conjSub ((m * y₀ : ↥(layerJoin Ω x)) : G) (layerRes x K) ≤ layerJoin Ω x := by
      rw [layerRes_conj K hyc]
      exact le_layerJoin ⟨_, hK.conj hΩ hyc, rfl⟩
    rw [inf_eq_left.mpr h3] at h2
    exact (XMem.eq_of_layerRes_eq hp hq hΩ hx (hK.conj hΩ hyc) hJ
      ((layerRes_conj K hyc).symm.trans h2.symm)).symm
  · right
    have hcomm := thm4NTBelow_of_citBelow hn hp hq (LayerQuot Ω x) hlt (layerFamQ Ω x) hΨ
      (CFSG.ComponentClassification.OddCore.quotient_corefree ↥(layerJoin Ω x))
      (noTwins_layerQuot hp hq hΩ hnt hx) _ ⟨_, hK'Λ, rfl⟩ _ ⟨_, hJ'Λ, rfl⟩ hconj
    have hne : ((layerRes x K).subgroupOf (layerJoin Ω x)).map
        (QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerJoin Ω x))) ≠
        ((layerRes x J).subgroupOf (layerJoin Ω x)).map
          (QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerJoin Ω x))) := by
      intro h
      exact hconj ⟨1, by rw [conjSub_one]; exact h⟩
    have hadj := omegaNbr_of_commutes (Φ := layerFamQ Ω x) ⟨_, hJ'Λ, rfl⟩ hne hcomm
    obtain ⟨m, -, hm⟩ := exists_conj_omegaNbr hp hq hΛ hΨ hodd hK'Λ hJ'Λ hadj
    exact ⟨(m : G), m.2, layer_omegaNbr hp hq hΩ hx hK hJ m hm⟩

end Dichotomy


end T8

end CFSG.ClassicalInvolution.Asc77
