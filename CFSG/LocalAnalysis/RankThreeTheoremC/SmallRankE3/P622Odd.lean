module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P622Simple
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.S622Sylow
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.S622Elem
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.S622Clifford
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62yBasic
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62yCommon
import CFSG.LocalAnalysis.RankThreeUC.TheoremDClauseCCore

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
  (S622IsSimpleSection s622_exists_invariant_sylow_inf_ne_bot s622_card_coprime_odd
    s622_le_sup_normalizer s622_primeCore_two_eq_of_odd s622_centralizer_ne_bot
    s622_exists_central_elemAbelian s622_exists_commuting_of_frobenius)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x z : G}
  {T S : Subgroup G}

theorem p622_inf_eq_bot (hP65 : P622Prop65 G) (hS : Setting G) (c : P622Conf p P M x z T S)
    (hnc : ¬ (centralizer ({x} : Set G) ≤
      (M ⊓ centralizer ({x} : Set G)) ⊔ smallRankD p x))
    (hodd : Odd (Nat.card (smallRankD p x))) : smallRankD p x ⊓ M = ⊥ := by
  by_contra hne
  have hsit := c.failure.situation
  have hprime := c.failure.prime
  haveI : Fact p.Prime := ⟨hprime⟩
  obtain ⟨H, hH⟩ : ∃ H : Subgroup G, H = centralizer ({x} : Set G) := ⟨_, rfl⟩
  obtain ⟨D, hDdef⟩ : ∃ D : Subgroup G, D = smallRankD p x := ⟨_, rfl⟩
  have hspec : D ≤ H ∧ H ≤ normalizer (D : Set G) ∧ Nat.Coprime p (Nat.card D) := by
    rw [hDdef, hH]
    exact CFSG.LocalAnalysis.RankThreeUC.rankThreePrimeCore_spec p _
  obtain ⟨hDH, hHD, hcop⟩ := hspec
  rw [← hDdef] at hne hodd
  rw [← hDdef, ← hH] at hnc
  have hpD : ¬ p ∣ Nat.card D := (Nat.Prime.coprime_iff_not_dvd hprime).mp hcop
  have hDn : (D.subgroupOf H).Normal := (normal_subgroupOf_iff_le_normalizer hDH).mpr hHD
  have hBp : IsPGroup p ↥(zpowers x ⊔ zpowers z) := P.isPGroup'.to_le c.B_le_P
  have hBH : zpowers x ⊔ zpowers z ≤ H := hH ▸ c.B_le_centralizer
  have hBD : zpowers x ⊔ zpowers z ≤ normalizer (D : Set G) := hBH.trans hHD
  have hBM : zpowers x ⊔ zpowers z ≤ M := c.B_le_M hS
  obtain ⟨f, F, hf, hf2, hfp, hFsyl, hBF, hFM⟩ :=
    s622_exists_invariant_sylow_inf_ne_bot hprime hBp hpD hBD hBM hodd hne
  have hFp : IsPGroup f F := hFsyl.isPGroup
  have hB65 : ∀ F' : Subgroup G, F' ≤ F → F' ≠ ⊥ → F' ≤ M →
      zpowers x ⊔ zpowers z ≤ normalizer (F' : Set G) → normalizer (F' : Set G) ≤ M := by
    intro F' hF'F hF'1 hF'M hBF'
    obtain ⟨hc, ho⟩ := s622_card_coprime_odd hf hf2 hfp hprime hFp hF'F
    exact hP65 p P M hsit x z c.failure.point c.failure.central
      (fun hN => hnc (by
        rw [hH, hDdef]
        exact p622_cover_of_hasNormalPComplement hS hsit c.failure.point hN))
      F' hF'1 hF'M hc ho hBF'
  have hBFM : zpowers x ⊔ zpowers z ≤ normalizer ((F ⊓ M : Subgroup G) : Set G) :=
    fun b hb => inf_normalizer_le_normalizer_inf ⟨hBF hb, le_normalizer (hBM hb)⟩
  have hNFM : normalizer ((F ⊓ M : Subgroup G) : Set G) ≤ M :=
    hB65 _ inf_le_left hFM inf_le_right hBFM
  have hFleM : F ≤ M := by
    by_contra hFM'
    have hlt : F ⊓ M < F := lt_of_le_of_ne inf_le_left (fun h => hFM' (h ▸ inf_le_right))
    haveI : Fact f.Prime := ⟨hf⟩
    obtain ⟨y, hyF, hyN, hyQ⟩ :=
      CFSG.LocalAnalysis.RankThreeTheoremC.sr628_exists_mem_normalizer_not_mem hFp hlt
    exact hyQ ⟨hyF, hNFM hyN⟩
  have hNF : normalizer (F : Set G) ≤ M :=
    hB65 F le_rfl (fun h => hFM (by rw [h]; exact bot_inf_eq _)) hFleM hBF
  have hFrat := s622_le_sup_normalizer hf hDH hDn hFsyl
  apply hnc
  rw [sup_comm]
  exact hFrat.trans (sup_le_sup_left (inf_le_inf_right H hNF) D)

theorem p622_primeCore_eq_bot (hK64 : Parrott.P614.KFact64ii) (hP65 : P622Prop65 G)
    (hS : Setting G) (c : P622Conf p P M x z T S) (hnc : ¬ SmallRankCover p M x)
    (hodd : Odd (Nat.card (smallRankD p x))) : smallRankD p x = ⊥ := by
  by_contra hD1
  have hprime := c.failure.prime
  have hp2 : p ≠ 2 := c.failure.ne_two
  haveI : Fact p.Prime := ⟨hprime⟩
  have hz := c.failure.central
  have hOD : rankThreePrimeCore 2 (smallRankD p x) = smallRankD p x :=
    s622_primeCore_two_eq_of_odd hodd
  have hnc'' : ¬ (centralizer ({x} : Set G) ≤
      (M ⊓ centralizer ({x} : Set G)) ⊔ smallRankD p x) := by
    intro h
    apply hnc
    show centralizer ({x} : Set G) ≤ (M ⊓ centralizer ({x} : Set G)) ⊔
      rankThreePrimeCore 2 (smallRankD p x)
    rw [hOD]
    exact h
  have hinf := p622_inf_eq_bot hP65 hS c hnc'' hodd
  obtain ⟨hDH, hHD, hcop⟩ : smallRankD p x ≤ centralizer ({x} : Set G) ∧
      centralizer ({x} : Set G) ≤ normalizer (smallRankD p x : Set G) ∧
      Nat.Coprime p (Nat.card (smallRankD p x)) :=
    CFSG.LocalAnalysis.RankThreeUC.rankThreePrimeCore_spec p _
  have hpD : ¬ p ∣ Nat.card (smallRankD p x) := (Nat.Prime.coprime_iff_not_dvd hprime).mp hcop
  have hzD : z ∈ normalizer (smallRankD p x : Set G) := hHD c.z_mem_centralizer
  have hzord : orderOf z = p := orderOf_eq_prime hz.pow_eq_one hz.ne_one
  obtain ⟨K, hK⟩ := p622_apply_pcomp hK64 hS c hnc''
  obtain ⟨L, hL, hzL, hLN⟩ : ∃ L : Subgroup G, S622IsSimpleSection L (smallRankD p x) ∧
      z ∈ L ∧ centralizer ({x} : Set G) ≤ normalizer (L : Set G) := by
    obtain ⟨hL, -, hzL, -, hLN⟩ := p622_simpleSection_of_pcomp hK
      (le_sup_right : smallRankD p x ≤ (M ⊓ centralizer ({x} : Set G)) ⊔ smallRankD p x)
    exact ⟨K ⊔ smallRankD p x, hL, hzL, hLN⟩
  have hRL : (⁅zpowers z, S⁆ : Subgroup G) ≤ L := by
    refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
    have haL : a ∈ L := (zpowers_le.mpr hzL) ha
    have hbN : b ∈ normalizer (L : Set G) := hLN (c.S_le_centralizer hb)
    have h1 : b * a⁻¹ * b⁻¹ ∈ L := (mem_normalizer_iff.mp hbN a⁻¹).mp (inv_mem haL)
    rw [commutatorElement_def]
    simpa [mul_assoc] using mul_mem haL h1
  have hD2 : ∀ y : G, y ^ 2 = 1 → y ≠ 1 → y ∉ smallRankD p x := by
    intro y hy2 hy1 hyD
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hord : orderOf y = 2 := orderOf_eq_prime hy2 hy1
    have h2 : 2 ∣ Nat.card (smallRankD p x) := hord ▸ Subgroup.orderOf_dvd_natCard _ hyD
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h2)
  have hy : ∀ y ∈ (⁅zpowers z, S⁆ : Subgroup G), y ^ 2 = 1 → y ≠ 1 →
      ∃ d ∈ smallRankD p x, d ≠ 1 ∧ y * d = d * y := fun y hyR hy2 hy1 =>
    s622_centralizer_ne_bot hodd hD1 hL (hRL hyR) hy2 (hD2 y hy2 hy1)
  have hDM : ∀ d ∈ smallRankD p x, d ∈ M → d = 1 := fun d hdD hdM =>
    Subgroup.mem_bot.mp (hinf ▸ (⟨hdD, hdM⟩ : d ∈ smallRankD p x ⊓ M))
  have hfpf : ∀ r ∈ (⁅zpowers z, S⁆ : Subgroup G), z * r = r * z → r = 1 := by
    intro r hrR hrz
    by_contra hr1
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    set C : Subgroup G := (⁅zpowers z, S⁆ : Subgroup G) ⊓ centralizer ({z} : Set G) with hCdef
    have hrC : r ∈ C := ⟨hrR, mem_centralizer_singleton_iff.mpr hrz.symm⟩
    have hC2 : IsPGroup 2 C := c.R_isPGroup.to_le inf_le_left
    have hC1 : C ≠ ⊥ := fun h => hr1 (Subgroup.mem_bot.mp (h ▸ hrC))
    have hdvd : 2 ∣ Nat.card C :=
      hC2.card_eq_or_dvd.resolve_left fun h1 => hC1 (Subgroup.eq_bot_of_card_eq _ h1)
    obtain ⟨y', hy'⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
    have hyord : orderOf (y' : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hy'
    have hy2 : (y' : G) ^ 2 = 1 := by rw [← hyord]; exact pow_orderOf_eq_one _
    have hy1 : (y' : G) ≠ 1 := fun h => by rw [h, orderOf_one] at hyord; omega
    have hyR : (y' : G) ∈ (⁅zpowers z, S⁆ : Subgroup G) := y'.2.1
    have hyz : (y' : G) ∈ centralizer ({z} : Set G) := y'.2.2
    have hzy : z ∈ centralizer ({(y' : G)} : Set G) :=
      mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp hyz).symm
    have hzN : zpowers z ≤ normalizer (zpowers (y' : G) : Set G) :=
      zpowers_le.mpr
        (CFSG.LocalAnalysis.RankThreeTheoremC.sr628_centralizer_le_normalizer_zpowers
          (y' : G) hzy)
    have hyS : zpowers (y' : G) ≤ S := zpowers_le.mpr (c.R_le_S hyR)
    have hne : zpowers (y' : G) ≠ ⊥ := by
      intro h
      exact hy1 (Subgroup.mem_bot.mp (h ▸ mem_zpowers (y' : G)))
    have hNM : normalizer (zpowers (y' : G) : Set G) ≤ M := c.normalizer_le hS hyS hne hzN
    obtain ⟨d, hdD, hd1, hyd⟩ := hy (y' : G) hyR hy2 hy1
    have hdy : d ∈ centralizer ({(y' : G)} : Set G) := mem_centralizer_singleton_iff.mpr hyd.symm
    exact hd1 (hDM d hdD (hNM
      (CFSG.LocalAnalysis.RankThreeTheoremC.sr628_centralizer_le_normalizer_zpowers
        (y' : G) hdy)))
  obtain ⟨R₁, hR₁1, hR₁R, hR₁e, hR₁N⟩ :=
    s622_exists_central_elemAbelian c.R_isPGroup (c.R_ne_bot hS)
  have hzR₁ : z ∈ normalizer (R₁ : Set G) := hR₁N z (c.z_le_normalizer_R (mem_zpowers z))
  have hR₁S : R₁ ≤ S := hR₁R.trans c.R_le_S
  have hR₁M : normalizer (R₁ : Set G) ≤ M :=
    c.normalizer_le hS hR₁S hR₁1 (zpowers_le.mpr hzR₁)
  have hR₁D : R₁ ≤ normalizer (smallRankD p x : Set G) := fun r hr =>
    hHD (c.S_le_centralizer (hR₁S hr))
  obtain ⟨d, hdD, hd1, hdz⟩ := s622_exists_commuting_of_frobenius hprime hp2 hzord hodd hpD hD1
    hR₁e hzR₁ hR₁D hzD (fun r hr hrz => hfpf r (hR₁R hr) hrz)
    (fun d hdD hdc => hDM d hdD (hR₁M (Subgroup.centralizer_le_normalizer (R₁ : Set G)
      (mem_centralizer_iff.mpr hdc))))
  exact hd1 (hDM d hdD (c.centralizer_le_M hS (mem_centralizer_singleton_iff.mpr hdz.symm)))

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
