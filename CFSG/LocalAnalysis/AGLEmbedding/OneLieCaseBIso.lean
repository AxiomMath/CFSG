module

public import CFSG.LocalAnalysis.AGLEmbedding.OneLieCaseBComponent
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNTwoAClassAux
import CFSG.LocalAnalysis.AGLEmbedding.OneLieNormalClosure

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def D1OneLieCompetitorComp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)) (R₁ : Subgroup G) (P' : Sylow p G)
    (H₁ S : Subgroup G), D1OneLieCompetitorData p P M H R Rbar K R₁ P' H₁ S →
    pCorePreimage p M ⊓ d1LiftX p H R K ≠ ⊥ → d1MapPCore p M H ≤ K →
    IsComponentOf (((nclIn H (d1LiftX p H R K)).subgroupOf H₁).map
      (QuotientGroup.mk' (primeComplementCore (G := H₁) p))) ⊤

namespace D1OneLieCompetitorData

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} {R₁ : Subgroup G} {P' : Sylow p G}
  {H₁ S : Subgroup G}

theorem exists_mulEquiv (hc : D1OneLieCompetitorData p P M H R Rbar K R₁ P' H₁ S)
    (hSch : KFactCatalogSchreier)
    (hJc : IsComponentOf (((nclIn H (d1LiftX p H R K)).subgroupOf H₁).map
      (QuotientGroup.mk' (primeComplementCore (G := H₁) p))) ⊤) :
    ∃ L : Subgroup (H₁ ⧸ primeComplementCore (G := H₁) p), IsComponentOf L ⊤ ∧ L.Normal ∧
      ((nclIn H (d1LiftX p H R K)).subgroupOf H₁).map
        (QuotientGroup.mk' (primeComplementCore (G := H₁) p)) = L ∧
      Subgroup.centralizer (L : Set (H₁ ⧸ primeComplementCore (G := H₁) p)) = ⊥ ∧
      (∀ L' : Subgroup (H₁ ⧸ primeComplementCore (G := H₁) p), IsComponentOf L' ⊤ → L' = L) ∧
      ∃ ψ : L ≃* K, ∀ (j : G) (hj : j ∈ nclIn H (d1LiftX p H R K))
        (hjL : QuotientGroup.mk' (primeComplementCore (G := H₁) p) ⟨j, hc.nclIn_le hj⟩ ∈ L),
        ((ψ ⟨_, hjL⟩ : K) : H ⧸ primeComplementCore (G := H) p) =
          QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨j, nclIn_le_self H _ hj⟩ := by
  have hd := hc.data
  obtain ⟨L, hL, hLn, -, hCL, huniq⟩ := hc.exists_normal_component hSch
  have hJLeq := huniq _ hJc
  have hZ : Subgroup.center L = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxC : (x : H₁ ⧸ primeComplementCore (G := H₁) p) ∈
        Subgroup.centralizer (L : Set (H₁ ⧸ primeComplementCore (G := H₁) p)) :=
      Subgroup.mem_centralizer_iff.mpr fun l hl =>
        congrArg Subtype.val (Subgroup.mem_center_iff.mp hx ⟨l, hl⟩)
    rw [hCL, Subgroup.mem_bot] at hxC
    exact Subgroup.mem_bot.mpr (Subtype.ext hxC)
  have hLs : IsSimpleGroup L := isSimpleGroup_of_center_eq_bot hL hZ
  obtain ⟨-, hKnab⟩ := hd.isSimpleGroup
  obtain ⟨φ, hφs, -, hφ⟩ :=
    exists_competitorHom_apply_of_map_eq (hd.map_nclIn_eq le_rfl hd.d1LiftX_ne_bot) hc.nclIn_le
  have hJs : IsSimpleGroup (((nclIn H (d1LiftX p H R K)).subgroupOf H₁).map
      (QuotientGroup.mk' (primeComplementCore (G := H₁) p))) :=
    (MulEquiv.subgroupCongr hJLeq).isSimpleGroup
  have hker : φ.ker = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hKnab
      apply hab
      obtain ⟨a', rfl⟩ := hφs a
      obtain ⟨b', rfl⟩ := hφs b
      have ha' : a' ∈ φ.ker := h ▸ Subgroup.mem_top a'
      have hb' : b' ∈ φ.ker := h ▸ Subgroup.mem_top b'
      rw [MonoidHom.mem_ker] at ha' hb'
      rw [ha', hb']
  have hφinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp hker
  refine ⟨L, hL, hLn, hJLeq, hCL, huniq,
    (MulEquiv.subgroupCongr hJLeq).symm.trans (MulEquiv.ofBijective φ ⟨hφinj, hφs⟩),
    fun j hj hjL => ?_⟩
  exact hφ j hj

end D1OneLieCompetitorData

end CFSG.AGLEmbedding
