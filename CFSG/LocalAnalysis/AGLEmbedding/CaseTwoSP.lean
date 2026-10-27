module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoRee
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoEscapeBlocks
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSP
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallPoszAux

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}

theorem D1CaseTwoData.exists_surjective_of_reducedCentralizer
    (hd : D1CaseTwoData p P M H R Rbar) {L : Subgroup (H ⧸ primeComplementCore (G := H) p)}
    (hL : IsComponentOf L ⊤) {z : H} (hzp : orderOf (z : G) = p)
    (hzL : QuotientGroup.mk' (primeComplementCore (G := H) p) z ∈
      Subgroup.centralizer (L : Set (H ⧸ primeComplementCore (G := H) p)))
    {P' : Sylow p G} {Pbar : Sylow p (D1CzQuot p (z : G))} {KC : Subgroup (D1CzQuot p (z : G))}
    (hRC : D1ReducedCentralizer p P' M (z : G) Pbar KC) (hSch : KFactCatalogSchreier) :
    ∃ (A : Subgroup KC) (f : A →* L), Function.Surjective f := by
  have hred := hd.cfg.red
  have hp := hred.prime
  have hZ := hred.center_eq_bot_of_isCyclic hL (hd.cyclic L hL)
  have : IsSimpleGroup (L ⧸ Subgroup.center L) := hL.2.2.2
  have hLs : IsSimpleGroup L :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.isSimpleGroup
  obtain ⟨t, htRL, ht, -⟩ := exists_mem_sylow_inf_component hp hred.ne_two hred.core_eq_bot Rbar
    hL
  have hx : (⟨t, htRL.2⟩ : L) ≠ 1 := fun h1 =>
    hp.one_lt.ne' (by rw [← ht, show t = 1 from congrArg Subtype.val h1, orderOf_one])
  have hxp : (⟨t, htRL.2⟩ : L) ^ p ^ 1 = 1 := by
    rw [pow_one]
    exact Subtype.ext (by
      rw [Subgroup.coe_pow, orderOf_dvd_iff_pow_eq_one.mp (dvd_of_eq ht), Subgroup.coe_one])
  exact hd.cfg.exists_surjective_of_reducedCentralizer ⟨hL.2.2.1⟩ hLs hx hxp z.2 hzp hzL hRC hSch

theorem d1CaseTwoSP_of (hβ : KFactBeta) (hS : KFactSeitzCyc) (hAE : KFactCaseTwoAlphaElimW)
    (hCM : KFactCaseTwoCM) (hSch : KFactCatalogSchreier) (hId : KFactCaseTwoReeId)
    (hKR4 : KFactReeBorelMaximal) (hKJ : KFactReeInvolution) (hL28 : KFactL28AutThree) :
    D1CaseTwoSP := by
  intro G _ _ p P M H R Rbar hd L hL hLX z hzR hzp hRz hzL hSP
  have hred := hd.cfg.red
  have hiso : IsCaseTwoGroup p L :=
    hred.isCaseTwoGroup_of_not_le hd.cfg.catalog hβ hS hd.cyclic hd.rank hL hLX
  have hp35 : p = 3 ∨ p = 5 := by
    obtain ⟨d, hd' | hd', -⟩ := hiso
    · exact Or.inl hd'.1
    · exact Or.inr hd'.1
  obtain ⟨P', Pbar, KC, -, hP'M, hRP', hRC⟩ :=
    hd.cfg.exists_reducedCentralizer hzp hRz (hd.cfg.centralizer_not_le hLX z.2 hzp hzL) hSP
  obtain ⟨A, f, hf⟩ := hd.exists_surjective_of_reducedCentralizer hL hzp hzL hRC hSch
  obtain ⟨hzZ, hzbarp⟩ :=
    hRC.center ⟨(z : G), Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ rfl
  by_cases hzK : d1CzElt p (z : G) ∈ KC
  · exact hRC.red.false_of_caseTwo_of_mem hRC.four_le_pRank hRC.catalog hzZ hzbarp hRC.comp
      hRC.normal hzK hAE hp35 hiso f hf
  rcases hp35 with rfl | rfl
  · obtain ⟨hs, hn, hc, hAut, T, hTnc, hΓ⟩ := hRC.red.exists_sylow_of_not_mem hRC.four_le_pRank
      hRC.catalog hzZ hzbarp hRC.comp hRC.normal hzK hβ
    obtain ⟨d, hRee, he⟩ := hId KC hs hn hc T hTnc hΓ hAut A L hiso f hf
    exact hd.false_of_ree hKR4 hKJ hL28 hL hLX hiso hzR hzp hRz hzL hP'M hRP' hRC hzK hRee he
  · obtain ⟨h53, -⟩ := hRC.red.caseTwoCM_of_not_mem hRC.four_le_pRank hRC.catalog hzZ hzbarp
      hRC.comp hRC.normal hzK hβ hCM (Or.inr rfl) hiso f hf
    omega

end CFSG.AGLEmbedding
