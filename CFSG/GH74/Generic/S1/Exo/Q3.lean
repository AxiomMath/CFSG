module

public import CFSG.GH74.Generic.S1.Exo.Final

public section

namespace CFSG.GH74.Generic.S1.Exo

open CFSG CFSG.GH74 CFSG.GH74.L5U5 Subgroup CFSG.GH74.Generic CFSG.GH74.GLS.IVK CFSG.Assembly.LowTwoRank

@[expose] def S1LayerCmpQ3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (x : G) (K : Subgroup (CentralizerBar x)), S1Setup G x K →
    S1Front G x K → IsSL4ModelAt ↥K 1 3 →
      ∀ (c : G) (hc : c ∈ centralizer ({x} : Set G)), orderOf c = 2 →
        (⟨c, hc⟩ : ↥(centralizer ({x} : Set G))) ∈ liftL x K → barOf hc ≠ xbar x →
        ∀ (t : G) (hxt : x ∈ centralizer ({t} : Set G)), IsConj c t →
          ∀ P : Subgroup (CentralizerBar t), IsSimpleGroup ↥P → Nat.card ↥P = 360 →
            P ≤ layer (CentralizerBar t) →
            P ≤ centralizer ({proj t ⟨x, hxt⟩} : Set (CentralizerBar t)) →
            (∀ M : Subgroup (CentralizerBar t), ⁅M, M⁆ = M →
              M ≤ centralizer ({proj t ⟨x, hxt⟩} : Set (CentralizerBar t)) → M ≤ P) → False

theorem s1ExoticExcludedQ3_of_cmp (hExact : S1LiftExactProp) (hcmp : S1LayerCmpQ3) :
    S1ExoticExcludedQ3 := by
  intro G _ _ x K hset hfront hbig v hv hconj hvx hv2 hvK α hα hExo
  obtain ⟨q, hq⟩ := IsExoticAut.exists_at hExo
  rcases hq with ⟨F, _, _, e, hF, h3, hβ⟩ | ⟨F, _, _, e, hF, hq4, hβ⟩
  · have hq3 : q = 3 := by
      by_contra hne
      have hlt : 3 < Nat.card F := by omega
      exact hbig (Or.inl ⟨F, inferInstance, inferInstance, by omega, hlt, ⟨e⟩⟩)
    subst hq3
    have hF4 : Nat.card F % 4 = 3 := by omega
    have hExo' : IsExoticAutAt 3 α := Or.inl ⟨F, inferInstance, inferInstance, e, hF, h3, hβ⟩
    obtain ⟨wK, w, hwx, h, Dx, Dv, hwv, hvord, hwK2, hwK1, hwKz, hwKα, hw, hwbar, hh, -⟩ :=
      exotic_setup_core (linModelCore hF4) hExact hset hfront e (by norm_num) hv hconj hvx hv2 hvK α hα hExo'
    obtain ⟨hword, hwL, hwbarne⟩ := exotic_w_facts hExact hset hfront e hwx hwK2 hwK1 hwKz hw hwbar
    have hmodel : IsSL4ModelAt ↥K 1 3 := Or.inl ⟨rfl, by norm_num, F, inferInstance, inferInstance, hF, ⟨e⟩⟩
    obtain ⟨t, ht⟩ : ∃ t : G, t = w * v := ⟨_, rfl⟩
    have htx : t ∈ centralizer ({x} : Set G) := by rw [ht]; exact Subgroup.mul_mem _ hwx hv
    have hxt : x ∈ centralizer ({t} : Set G) :=
      mem_centralizer_singleton_iff.2 (mem_centralizer_singleton_iff.1 htx).symm
    obtain ⟨P, hPs, hPcard, hPlayer, hPc, hPmax⟩ :=
      exotic_cmp hExact hset hfront e (by norm_num) hv α hα hExo' hwx hwK2 hwKα hwbar ht hxt
    have hconjwt : IsConj w t := isConj_iff.2 ⟨h, by rw [hh, ht]⟩
    have hP360 : Nat.card ↥P = 360 := by
      norm_num at hPcard
      omega
    exact hcmp G x K hset hfront hmodel w hwx hword hwL hwbarne t hxt hconjwt P hPs hP360 hPlayer hPc hPmax
  · exact hbig (Or.inr ⟨q, F, inferInstance, inferInstance, hF, hq4, ⟨e⟩⟩)

theorem s1FrameExists_of_nbhd_q3 (hExact : S1LiftExactProp) (hNb : NbhdNoPrime)
    (hcmp : S1LayerCmpQ3) : S1FrameExists :=
  s1FrameExists_of_nbhd hExact hNb (s1ExoticExcludedQ3_of_cmp hExact hcmp)

end CFSG.GH74.Generic.S1.Exo
