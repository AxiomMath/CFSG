module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5Lem51
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5OutLift
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5Steps

public section

namespace CFSG.EvenSporadicStandard.HSStd

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.RankThree.Native

theorem hsOuterChoice (M : HS100Model) (Pk : HS100OuterData) : HSOuterChoice := by
  intro G _ _ L hset t ht ht2 hidx
  obtain ⟨v₀, hv₀C, hv₀N, hv₀2⟩ := hs_exists_outer_involution M hset ht ht2 hidx
  obtain ⟨hStd, hL, hCL, hfus, -⟩ := hset
  have hZ : center L = ⊥ := M.center_eq_bot L hL
  have htt : t * t = 1 := by rw [← pow_two]; exact ht2 ▸ pow_orderOf_eq_one t
  have htL : t ∉ L := by
    intro htl
    have h1 : (⟨t, htl⟩ : L) ∈ center L := by
      rw [mem_center_iff]
      intro g
      exact Subtype.ext (mem_centralizer_iff.1 ht g g.2)
    rw [hZ, mem_bot] at h1
    have : t = 1 := congrArg Subtype.val h1
    rw [this, orderOf_one] at ht2
    omega
  have hC : centralizer ({t} : Set G) ≤ normalizer (L : Set G) :=
    hStd.centralizer_le_normalizer ht ht2
  have hker : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t :=
    hStd.centralizer_inf_centralizer_eq_zpowers hCL ht ht2
  have hZ' : ∀ l ∈ L, (∀ x ∈ L, x * l = l * x) → l = 1 := by
    intro l hl hc
    have h1 : (⟨l, hl⟩ : L) ∈ center L := by
      rw [mem_center_iff]
      intro g
      exact Subtype.ext (hc g g.2)
    rw [hZ, mem_bot] at h1
    exact congrArg Subtype.val h1
  obtain ⟨θ⟩ := M.equiv L hL
  obtain ⟨e, he⟩ := M.aut
  let D : AutModelData L ↥hs100R ↥hs100P :=
    { ι := Subgroup.inclusion hs100P_le_R
      ι_injective := Subgroup.inclusion_injective _
      θ := θ
      e := e
      he := fun w x => Subtype.ext (he w x) }
  obtain ⟨S, z, hSC, hS2, hSidx, hzS, hzL, hz2, hzc, n, hn, hnt⟩ := hfus t ht ht2
  obtain ⟨v, s, ψ, hvS, hvN, hv2, hsS, hsv, hψ, hrange, hnn, hnn'⟩ :=
    outer_choice_abstract D ht htt htL hC hker hidx M.card hZ' ⟨v₀, hv₀C, hv₀N, hv₀2⟩
      (fun Sw hp hi zw h2 hc => Pk Sw hp hi zw h2 hc) hSC hS2 hSidx hzL hz2 hzc hn hnt
  have hder : derivedCentralizerIn L v = (alternatingGroup (Fin 8)).map ψ :=
    map_commutator_range ψ hψ _ hrange
  have hrange' : ψ.range = centralizer ({t * v} : Set G) ⊓ L := by
    rw [hrange]
    ext l
    simp only [mem_inf, mem_centralizer_singleton_iff]
    have hcl : ∀ l ∈ L, l * t = t * l := fun l hl => mem_centralizer_iff.1 ht l hl
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      calc l * (t * v) = (l * t) * v := by rw [mul_assoc]
        _ = t * (l * v) := by rw [hcl l h2, mul_assoc]
        _ = t * (v * l) := by rw [h1]
        _ = (t * v) * l := by rw [mul_assoc]
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      have h1' : t * (l * v) = t * (v * l) := by
        calc t * (l * v) = (l * t) * v := by rw [hcl l h2, mul_assoc]
          _ = l * (t * v) := by rw [mul_assoc]
          _ = (t * v) * l := h1
          _ = t * (v * l) := by rw [mul_assoc]
      exact mul_left_cancel h1'
  have hder' : derivedCentralizerIn L (t * v) = (alternatingGroup (Fin 8)).map ψ :=
    map_commutator_range ψ hψ _ hrange'
  refine ⟨S, z, n, v, s, ⟨⟨hSC, hS2, hSidx, hzS, hzL, hz2, hzc, hn, hnt⟩, hvS, hvN, hv2,
    ⟨((MonoidHom.ofInjective hψ).trans (MulEquiv.subgroupCongr hrange)).symm⟩, hsS, hsv⟩, ?_, ?_⟩
  · rw [hder]
    exact hnn
  · rw [hder']
    exact hnn'

theorem hsOuterChoice_cert :
    HSOuterChoice :=
  hsOuterChoice hs100Model hs100Outer

end CFSG.EvenSporadicStandard.HSStd
