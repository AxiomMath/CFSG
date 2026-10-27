module

public import CFSG.ClassicalInvolution.Asc77.AscS16K
public import CFSG.ClassicalInvolution.Asc77.AscS22F

public section

namespace CFSG.ClassicalInvolution.Asc77

namespace S16

set_option linter.unusedSectionVars false

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.S22
open scoped commutatorElement

section Main

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {Ω : Set (Subgroup G)} {K K' K₃ : Subgroup G} {z u₁ u₂ u₃ : G}

theorem false_of_abelianV (hE : ThmEWithSylow p f) (h2 : C22_2V p f)
    (h : Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃) (hb : V3Ab Ω K)
    (hsig : ∀ J ∈ dstarComp Ω K, J ∈ twinSet Ω K)
    (hcent : ∀ {L L' L₃ : Subgroup G} {x y w : G}, Hyp22Setting p f Ω L L' L₃ z x y w →
      Subgroup.centralizer ({x * y} : Set G) ≤
        alphaOf (Subgroup.closure ({x * y, z} : Set G)) ⊔
          (Subgroup.centralizer ({x * y} : Set G) ⊓ Subgroup.centralizer ({z} : Set G))) :
    False := by
  have hp : p ≠ 2 := h.stand.odd
  have hΩ : HypOmegaMod p f Ω := h.stand.hyp
  have hK : K ∈ Ω := h.stand.mem
  have hcentD : ∀ {L L' L₃ : Subgroup G} {x y w : G}, Hyp22Setting p f Ω L L' L₃ z x y w →
      Subgroup.centralizer ({x * y} : Set G) ≤
        Subgroup.normalizer (alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) : Set G) ∧
      (alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) = ⊥ →
        Subgroup.centralizer ({x * y} : Set G) ≤ Subgroup.centralizer ({z} : Set G)) := by
    intro L L' L₃ x y w hd
    have hc := hcent hd
    have heq := (alpha_eq_of_datumV h2 h hd hb).symm
    refine ⟨fun c hcC => ?_, fun hα => ?_⟩
    · have hinf : Subgroup.centralizer ({x * y} : Set G) ⊓ Subgroup.centralizer ({z} : Set G) ≤
          Subgroup.normalizer (alphaOf (Subgroup.closure ({x * y, z} : Set G)) : Set G) := by
        intro c' hc'
        have ha : c' * (x * y) = (x * y) * c' :=
          Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hc').1
        have hb' : c' * z = z * c' :=
          Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hc').2
        exact T7B.centralizer_le_normalizer_alphaOf _
          (T7B.mem_centralizer_closure_pair ha.symm hb'.symm)
      have h1 : c ∈ Subgroup.normalizer
          (alphaOf (Subgroup.closure ({x * y, z} : Set G)) : Set G) :=
        (sup_le Subgroup.le_normalizer hinf) (hc hcC)
      rwa [heq] at h1
    · rw [← heq] at hα
      rw [hα, bot_sup_eq] at hc
      exact hc.trans inf_le_right
  have htwin : ∀ L ∈ twinSet Ω K, ∀ L' ∈ twinSet Ω K, L' ≠ L → ∀ R₁ R₂ : Subgroup G,
      IsSylow2In R₁ L → IsSylow2In R₂ L' → Commutes R₁ R₂ → ∀ x ∈ R₁, ∀ y ∈ R₂,
        orderOf x = 4 → orderOf y = 4 →
          ∃ (L₃ : Subgroup G) (w : G), Hyp22Setting p f Ω L L' L₃ z x y w :=
    fun L hL L' hL' hne R₁ R₂ hR₁ hR₂ hc x hx y hy ox oy =>
      exists_datum_of_pair h hL hL' hne hR₁ hR₂ hc hx hy ox oy
  have hstd1 : StdCent Ω K (Subgroup.normalizer
      (alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) : Set G)) z :=
    stdCent_of_twin h (centralizer_le_normalizer_alphaV h2 h hb)
      fun L hL L' hL' hne R₁ R₂ hR₁ hR₂ hc x hx y hy ox oy => by
        obtain ⟨L₃, w, hd⟩ := htwin L hL L' hL' hne R₁ R₂ hR₁ hR₂ hc x hx y hy ox oy
        exact (hcentD hd).1
  have htrans1 : ∀ J ∈ dstarComp Ω K, ∃ c ∈ Subgroup.normalizer
      (alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) : Set G), conjSub c K = J := by
    intro J hJ
    obtain ⟨c, hc, hcJ⟩ := exists_centralizer_conj h (hsig J hJ)
    exact ⟨c, centralizer_le_normalizer_alphaV h2 h hb hc, hcJ⟩
  have htop1 := thmE_apply hE h.stand h.hz h.hK' h.hne hstd1 htrans1
  have hα : alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) = ⊥ :=
    T7B.eq_bot_of_normalizer_eq_top (h2 G Ω K K' K₃ z u₁ u₂ u₃ h hb).1 htop1
      (T7B.two_dvd_natCard h.hz)
  have hstd2 : StdCent Ω K (Subgroup.centralizer ({z} : Set G)) z :=
    stdCent_of_twin h le_rfl fun L hL L' hL' hne R₁ R₂ hR₁ hR₂ hc x hx y hy ox oy => by
      obtain ⟨L₃, w, hd⟩ := htwin L hL L' hL' hne R₁ R₂ hR₁ hR₂ hc x hx y hy ox oy
      exact (hcentD hd).2 hα
  have htrans2 : ∀ J ∈ dstarComp Ω K, ∃ c ∈ Subgroup.centralizer ({z} : Set G),
      conjSub c K = J := fun J hJ => exists_centralizer_conj h (hsig J hJ)
  have htop2 := thmE_apply hE h.stand h.hz h.hK' h.hne hstd2 htrans2
  obtain ⟨V, hV, -⟩ := IsSylow2In.exists_ge (isPGroup_two_bot (G := G)) (bot_le : ⊥ ≤ K)
  obtain ⟨x, -, y, -, hxy⟩ :=
    (hΩ.isQuatSub_of_mem_RSet hp (mem_RSet_of_isSylow2In hK hV)).exists_not_commute
  have hz1 : z = 1 := T7B.eq_one_of_central ⟨x, y, hxy⟩ fun g => by
    have : g ∈ Subgroup.centralizer ({z} : Set G) := by rw [htop2]; exact Subgroup.mem_top g
    exact Subgroup.mem_centralizer_singleton_iff.mp this
  exact h.hz.ne_one hz1

end Main

end S16

end CFSG.ClassicalInvolution.Asc77
