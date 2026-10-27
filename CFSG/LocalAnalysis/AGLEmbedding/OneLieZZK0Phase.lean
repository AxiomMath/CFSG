module

public import CFSG.LocalAnalysis.AGLEmbedding.OneLieZZK0Iso
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNTwoAClassAux
import CFSG.LocalAnalysis.AGLEmbedding.OneLieConfig
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieCaseBCentralizer

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

namespace D1OneLieKZeroData

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} {P' : Sylow p G} {H₁ S : Subgroup G}

theorem centralizer_le (hc : D1OneLieKZeroData p P M H R Rbar K P' H₁ S)
    {L : Subgroup (H₁ ⧸ primeComplementCore (G := H₁) p)} (hLn : L.Normal)
    (hJL : ((nclIn H (d1LiftX p H R K)).subgroupOf H₁).map
      (QuotientGroup.mk' (primeComplementCore (G := H₁) p)) = L)
    (hZ : Subgroup.center L = ⊥) :
    Subgroup.centralizer (L : Set (H₁ ⧸ primeComplementCore (G := H₁) p)) ≤
      ((H₁ ⊓ M).subgroupOf H₁).map (QuotientGroup.mk' (primeComplementCore (G := H₁) p)) := by
  have hd := hc.data
  have hp := hc.escape.prime
  have : Fact p.Prime := ⟨hp⟩
  have : L.Normal := hLn
  set π₁ := QuotientGroup.mk' (primeComplementCore (G := H₁) p) with hπ₁
  set X := d1LiftX p H R K with hXdef
  set Xt := (X.subgroupOf H₁).map π₁ with hXt
  set St := (S.subgroupOf H₁).map π₁ with hSt
  set C := Subgroup.centralizer (L : Set (H₁ ⧸ primeComplementCore (G := H₁) p)) with hC
  obtain ⟨Rb₁, hRb₁, hred₁⟩ := hc.escape.reducedNongeneration
  have hRbS : (Rb₁ : Subgroup _) = St := hRb₁
  have hXtS : Xt ≤ St := Subgroup.map_mono (Subgroup.comap_mono hc.liftX_le)
  have hXtL : Xt ≤ L := hJL ▸ Subgroup.map_mono (Subgroup.comap_mono
    (le_nclIn (d1LiftX_le_H p H R K)))
  have hnc : ¬ IsCyclic ((Rb₁ : Subgroup _) ⊓ L : Subgroup _) := fun hcyc =>
    hd.not_isCyclic_map hc.liftX_le_H₁ (Subgroup.isCyclic_of_le (le_inf (hRbS ▸ hXtS) hXtL))
  have hLC : ∀ x ∈ L, x ∈ C → x = 1 := by
    intro x hxL hxC
    have hxZ : (⟨x, hxL⟩ : L) ∈ Subgroup.center L := by
      rw [Subgroup.mem_center_iff]
      intro l
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC l l.2)
    rw [hZ, Subgroup.mem_bot] at hxZ
    exact congrArg Subtype.val hxZ
  by_cases hS1 : (Rb₁ : Subgroup _) ⊓ C = ⊥
  ·
    have hcop : p.Coprime (Nat.card C) := by
      rw [Nat.Prime.coprime_iff_not_dvd hp]
      intro hdvd
      obtain ⟨c, hcp⟩ := exists_prime_orderOf_dvd_card' p hdvd
      have hcz : IsPGroup p (Subgroup.zpowers (c : H₁ ⧸ primeComplementCore (G := H₁) p)) :=
        IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, Subgroup.orderOf_coe, hcp, pow_one])
      obtain ⟨Q, hQ⟩ := hcz.exists_le_sylow
      obtain ⟨g, hg⟩ := MulAction.exists_smul_eq
        (H₁ ⧸ primeComplementCore (G := H₁) p) Rb₁ Q
      have hcQ : (c : H₁ ⧸ primeComplementCore (G := H₁) p) ∈ (Q : Subgroup _) :=
        hQ (Subgroup.mem_zpowers _)
      rw [← hg, coe_smul_sylow_eq_map_conj] at hcQ
      obtain ⟨x, hxR, hxc⟩ := hcQ
      have hxC : x ∈ C := by
        have := (inferInstance : C.Normal).conj_mem _ c.2 g⁻¹
        have e : x = g⁻¹ * (c : H₁ ⧸ primeComplementCore (G := H₁) p) * g⁻¹⁻¹ := by
          rw [← hxc]
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
          group
        rw [e]
        exact this
      have hx1 : x ∈ (Rb₁ : Subgroup _) ⊓ C := ⟨hxR, hxC⟩
      rw [hS1, Subgroup.mem_bot] at hx1
      have hc1 : (c : H₁ ⧸ primeComplementCore (G := H₁) p) = 1 := by
        rw [← hxc, hx1, map_one]
      rw [show c = 1 from Subtype.ext hc1, orderOf_one] at hcp
      exact hp.one_lt.ne hcp
    have hCbot : C = ⊥ := le_bot_iff.mp (hred₁.core_eq_bot ▸
      normal_coprime_le_primeComplementCore p C inferInstance hcop)
    rw [hCbot]
    exact bot_le
  ·
    have hRbN : (Rb₁ : Subgroup _) ≤
        Subgroup.normalizer (((Rb₁ : Subgroup _) ⊓ C : Subgroup _) :
          Set (H₁ ⧸ primeComplementCore (G := H₁) p)) := by
      refine (le_inf Subgroup.le_normalizer ?_).trans Subgroup.inf_normalizer_le_normalizer_inf
      rw [Subgroup.normalizer_eq_top_iff.mpr (inferInstance : C.Normal)]
      exact le_top
    obtain ⟨z, ⟨hzR, hzC⟩, -, hzp⟩ :=
      exists_mem_inf_centralizer_orderOf_eq Rb₁.isPGroup' inf_le_left hRbN hS1
    have hzL : z ∉ L := fun hzL => by
      rw [hLC z hzL hzC, orderOf_one] at hzp
      exact hp.one_lt.ne hzp
    exact hred₁.centralizer_le_of_rankOne hnc hzR hzL hzp hzC

theorem toPhaseThree (hc : D1OneLieKZeroData p P M H R Rbar K P' H₁ S) (hK : KFactOneLie)
    (hcon : ¬ HasPrimeConstraint (G := H₁) p)
    {L : Subgroup (H₁ ⧸ primeComplementCore (G := H₁) p)} (hL : IsComponentOf L ⊤)
    (hLn : L.Normal)
    (hJL : ((nclIn H (d1LiftX p H R K)).subgroupOf H₁).map
      (QuotientGroup.mk' (primeComplementCore (G := H₁) p)) = L)
    (hZ : Subgroup.center L = ⊥) (ψ : L ≃* K)
    (hψ : ∀ (j : G) (hj : j ∈ nclIn H (d1LiftX p H R K))
      (hjL : QuotientGroup.mk' (primeComplementCore (G := H₁) p) ⟨j, hc.nclIn_le hj⟩ ∈ L),
      ((ψ ⟨_, hjL⟩ : K) : H ⧸ primeComplementCore (G := H) p) =
        QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨j, nclIn_le_self H _ hj⟩) :
    D1PhaseThree p P' M H₁ S := by
  have hd := hc.data
  have hp := hc.escape.prime
  obtain ⟨Rb₁, -, hred₁, -, hcomp₁, -, -, -, -⟩ :=
    hc.escape.exists_reducedNongeneration_of_not_hasPrimeConstraint hd.cfg.glob.kProper hcon
  obtain ⟨hLs, hLnab, hLcat⟩ := simple_of_center_eq_bot hL hZ (hcomp₁ L hL).2.1
  obtain ⟨T₁, hT₁⟩ := hc.exists_sylow_of_mulEquiv hJL ψ hψ
  obtain ⟨hF, hΓX⟩ := hc.oneLieFacts_of_mulEquiv hK hLs hLnab hLcat hJL ψ hψ T₁ hT₁
  have hCX := hc.centralizer_le hLn hJL hZ
  have hU : UPrimeHyp p (((H₁ ⊓ M).subgroupOf H₁).map
      (QuotientGroup.mk' (primeComplementCore (G := H₁) p))) :=
    uPrimeHyp_of_forall_kFact hp fun L' hL' hL'X => by
      by_cases hL'L : L' = L
      · subst hL'L
        exact ⟨hF.uPrime, T₁, hΓX⟩
      · exact absurd ((le_centralizer_of_component_ne hL' hL hL'L).trans hCX) hL'X
  exact hc.escape.toPhaseThreeU (hd.toPhaseThree hK).glob
    (hc.escape.primeCore_inf_eq_iff.mpr (hred₁.primeComplementCore_eq_bot_of_uPrimeHyp hU))

theorem nclIn_le_and_nclIn_eq (hc : D1OneLieKZeroData p P M H R Rbar K P' H₁ S)
    {L : Subgroup (H₁ ⧸ primeComplementCore (G := H₁) p)} (hL : IsComponentOf L ⊤)
    (hLn : L.Normal)
    (hJL : ((nclIn H (d1LiftX p H R K)).subgroupOf H₁).map
      (QuotientGroup.mk' (primeComplementCore (G := H₁) p)) = L)
    (hZ : Subgroup.center L = ⊥) :
    nclIn H (d1LiftX p H R K) ≤ nclIn H₁ (d1LiftX p H R K) ∧
      nclIn (nclIn H₁ (d1LiftX p H R K)) (d1LiftX p H R K) = nclIn H₁ (d1LiftX p H R K) :=
  hc.toEsc.nclIn_le_and_nclIn_eq_of_simple hLn (isSimpleGroup_of_center_eq_bot hL hZ) hJL

theorem nclIn_eq_of_le (hc : D1OneLieKZeroData p P M H R Rbar K P' H₁ S)
    {L : Subgroup (H₁ ⧸ primeComplementCore (G := H₁) p)} (hL : IsComponentOf L ⊤)
    (hLn : L.Normal)
    (hJL : ((nclIn H (d1LiftX p H R K)).subgroupOf H₁).map
      (QuotientGroup.mk' (primeComplementCore (G := H₁) p)) = L)
    (hZ : Subgroup.center L = ⊥) {Y : Subgroup G} (hYX : Y ≤ d1LiftX p H R K) (hY : Y ≠ ⊥) :
    nclIn H₁ Y = nclIn H₁ (d1LiftX p H R K) :=
  hc.toEsc.nclIn_eq_of_le_of_simple hLn (isSimpleGroup_of_center_eq_bot hL hZ) hJL hYX hY

end D1OneLieKZeroData

end CFSG.AGLEmbedding
