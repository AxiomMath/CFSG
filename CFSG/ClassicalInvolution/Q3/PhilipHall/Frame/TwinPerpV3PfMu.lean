module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3PfBase
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscThmE
public import CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge.FStarNormal
public import CFSG.ClassicalInvolution.SmallCases.A7T22Main

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp

section Generic

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K K' K₃ : Subgroup G}
  {z u₁ u₂ u₃ : G}

theorem false_of_thmE' (hα : A7T22.AlphaConst Ω z)
    (h : A7T22.Hyp22G Ω K K' K₃ z u₁ u₂ u₃) (hperp : KPerp Ω K = twinSet Ω K)
    (hodd : ∀ A : Subgroup G, A.Normal → Odd (Nat.card A) → A = ⊥)
    (hZ : ∀ c : G, (∀ g : G, g * c = c * g) → c = 1)
    (htr : ∀ J ∈ Ω, ∃ g : G, conjSub g K = J)
    (hsig : ∀ J ∈ dstarComp Ω K, J ∈ twinSet Ω K)
    (hcent : ∀ (L L' L₃ : Subgroup G) (x y w : G), A7T22.Hyp22G Ω L L' L₃ z x y w →
      Subgroup.centralizer ({x * y} : Set G) ≤
        alphaOf (Subgroup.closure ({x * y, z} : Set G)) ⊔
          (Subgroup.centralizer ({x * y} : Set G) ⊓ Subgroup.centralizer ({z} : Set G)))
    (hE : ∀ H : Subgroup G, StdCent Ω K H z →
      (∀ J ∈ dstarComp Ω K, ∃ g ∈ H, conjSub g K = J) → H = ⊤) : False := by
  set α : Subgroup G := alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) with hαdef
  have hcentD : ∀ {L L' L₃ : Subgroup G} {x y w : G}, A7T22.Hyp22G Ω L L' L₃ z x y w →
      Subgroup.centralizer ({x * y} : Set G) ≤ Subgroup.normalizer (α : Set G) ∧
      (α = ⊥ → Subgroup.centralizer ({x * y} : Set G) ≤ Subgroup.centralizer ({z} : Set G)) := by
    intro L L' L₃ x y w hd
    have hc := hcent L L' L₃ x y w hd
    have heq := h.alpha_eq_of_datum hα hd
    refine ⟨fun c hcC => ?_, fun hα1 => ?_⟩
    · have hinf : Subgroup.centralizer ({x * y} : Set G) ⊓ Subgroup.centralizer ({z} : Set G) ≤
          Subgroup.normalizer (alphaOf (Subgroup.closure ({x * y, z} : Set G)) : Set G) := by
        intro c' hc'
        have ha : c' * (x * y) = (x * y) * c' :=
          Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hc').1
        have hb : c' * z = z * c' :=
          Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hc').2
        exact T7B.centralizer_le_normalizer_alphaOf _
          (T7B.mem_centralizer_closure_pair ha.symm hb.symm)
      have h1 : c ∈ Subgroup.normalizer
          (alphaOf (Subgroup.closure ({x * y, z} : Set G)) : Set G) :=
        (sup_le Subgroup.le_normalizer hinf) (hc hcC)
      rwa [← heq] at h1
    · rw [hαdef, heq] at hα1
      rw [hα1, bot_sup_eq] at hc
      exact hc.trans inf_le_right
  have htwin : ∀ L ∈ twinSet Ω K, ∀ L' ∈ twinSet Ω K, L' ≠ L → ∀ R₁ R₂ : Subgroup G,
      IsSylow2In R₁ L → IsSylow2In R₂ L' → Commutes R₁ R₂ → ∀ x ∈ R₁, ∀ y ∈ R₂,
        orderOf x = 4 → orderOf y = 4 → ∃ (L₃ : Subgroup G) (w : G),
          A7T22.Hyp22G Ω L L' L₃ z x y w :=
    fun L hL L' hL' hne R₁ R₂ hR₁ hR₂ hc x hx y hy ox oy =>
      h.exists_datum_of_pair hL hL' hne hR₁ hR₂ hc hx hy ox oy
  have hstd1 : StdCent Ω K (Subgroup.normalizer (α : Set G)) z :=
    h.stdCent_of_twin hperp (h.centralizer_le_normalizer_alpha hα)
      fun L hL L' hL' hne R₁ R₂ hR₁ hR₂ hc x hx y hy ox oy => by
        obtain ⟨L₃, w, hd⟩ := htwin L hL L' hL' hne R₁ R₂ hR₁ hR₂ hc x hx y hy ox oy
        exact (hcentD hd).1
  have htrans1 : ∀ J ∈ dstarComp Ω K, ∃ c ∈ Subgroup.normalizer (α : Set G),
      conjSub c K = J := by
    intro J hJ
    obtain ⟨c, hc, hcJ⟩ := h.exists_centralizer_conj htr (hsig J hJ)
    exact ⟨c, h.centralizer_le_normalizer_alpha hα hc, hcJ⟩
  have hα1 : α = ⊥ := by
    refine hodd α ?_ (hα K K' K₃ u₁ u₂ u₃ h).1
    exact Subgroup.normalizer_eq_top_iff.mp (hE _ hstd1 htrans1)
  have hstd2 : StdCent Ω K (Subgroup.centralizer ({z} : Set G)) z :=
    h.stdCent_of_twin hperp le_rfl fun L hL L' hL' hne R₁ R₂ hR₁ hR₂ hc x hx y hy ox oy => by
      obtain ⟨L₃, w, hd⟩ := htwin L hL L' hL' hne R₁ R₂ hR₁ hR₂ hc x hx y hy ox oy
      exact (hcentD hd).2 hα1
  have htop2 := hE _ hstd2 fun J hJ => h.exists_centralizer_conj htr (hsig J hJ)
  have hz1 : z = 1 := hZ z fun g => by
    have : g ∈ Subgroup.centralizer ({z} : Set G) := by rw [htop2]; exact Subgroup.mem_top g
    exact Subgroup.mem_centralizer_singleton_iff.mp this
  exact h.hz.ne_one hz1

end Generic

section Steps


@[expose] def V3Sigma (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    PerpHypS n Y R S t → ¬ TwoTwins R → ¬ TwinE4 Y →
      ∀ (K K' K₃ : Subgroup Y) (u₁ u₂ u₃ : Y),
        A7T22.Hyp22G (CoreAssembly.conjClass (tightCore R)) K K' K₃ t u₁ u₂ u₃ →
          (¬ ∀ W ∈ WSet (CoreAssembly.conjClass (tightCore R)),
              MuIsoWylD4 (CoreAssembly.conjClass (tightCore R)) W) →
            ∀ J ∈ dstarComp (CoreAssembly.conjClass (tightCore R)) K,
              J ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K

@[expose] def V3ZStar (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    PerpHypS n Y R S t → ¬ TwoTwins R → ¬ TwinE4 Y →
      ∀ (K K' K₃ : Subgroup Y) (u₁ u₂ u₃ : Y),
        A7T22.Hyp22G (CoreAssembly.conjClass (tightCore R)) K K' K₃ t u₁ u₂ u₃ →
          (¬ ∀ W ∈ WSet (CoreAssembly.conjClass (tightCore R)),
              MuIsoWylD4 (CoreAssembly.conjClass (tightCore R)) W) →
            t ∈ zStarOf (Subgroup.centralizer ({u₁ * u₂} : Set Y))

end Steps

section Apply



variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem muWylD4 (hTE : TwinDisc.TwinThmE n) (hV : V3Hyp51B n) (hσ : V3Sigma n)
    (hZ : V3ZStar n) (h : PerpHypS n Y R S t) (h3 : ¬ TwoTwins R) (hE : ¬ TwinE4 Y) :
    ∀ W ∈ WSet (CoreAssembly.conjClass (tightCore R)),
      MuIsoWylD4 (CoreAssembly.conjClass (tightCore R)) W := by
  by_contra hW
  obtain ⟨K', K₃, u₁, u₂, u₃, hd⟩ := exists_hyp22G h h3
  set K := tightCore R with hKdef
  have hα := alphaConst hV h h3 hE
  have hC := CoreData.of_S h.core
  have hU : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hZ1 : Subgroup.center Y = ⊥ :=
    InductionBridge.center_eq_bot_of_fstar_simple hC.simple hC.nonab
  refine false_of_thmE' hα hd h.perp ?_ ?_ ?_ (hσ Y R S t h h3 hE K K' K₃ u₁ u₂ u₃ hd hW) ?_ ?_
  · intro A hAn hAodd
    have hle : A ≤ classicalInvolutionOddCore Y := le_sSup ⟨hAn, hAodd⟩
    rw [hC.oddFree] at hle
    exact le_bot_iff.mp hle
  · intro c hc
    have : c ∈ Subgroup.center Y := Subgroup.mem_center_iff.mpr fun g => hc g
    rw [hZ1] at this
    exact Subgroup.mem_bot.mp this
  · intro J ⟨g, hg⟩
    exact ⟨g, hg⟩
  · intro L L' L₃ x y w hd'
    exact hd'.cent_of_zstar (hZ Y R S t h h3 hE L L' L₃ x y w hd' hW)
  · intro H hstd htrans
    exact TwinDisc.thmE_apply hTE h.core.toHyp (CoreAssembly.mem_conjClass_self _) hU hstd htrans

end Apply

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
