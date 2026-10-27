module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.S622Basic
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.S622Sylow
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.S622Elem
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.S622Clifford
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Lines
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Frattini
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62yBasic
import CFSG.LocalAnalysis.RankThreeUC.TheoremDClauseCCore
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.S622Defs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC (SmallRankCover smallRankD)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x z : G}
  {T S : Subgroup G}

theorem s622_apply_simple (hSimple : S622KFactSimple) (c : S62Config p P M x z T)
    (hodd : Odd (Nat.card (smallRankD p x)))
    (hnc : ¬ (centralizer ({x} : Set G) ≤
      (M ⊓ centralizer ({x} : Set G)) ⊔ smallRankD p x)) :
    ∃ L : Subgroup G, S622IsSimpleSection L (smallRankD p x) ∧
      L ≤ centralizer ({x} : Set G) ∧ z ∈ L ∧ CFSG.Open.pRank p L ≤ 1 ∧
      ¬ L ≤ (M ⊓ L) ⊔ smallRankD p x ∧
      M ⊓ centralizer ({x} : Set G) ≤ normalizer (L : Set G) := by
  have hS := c.situation
  have hx := c.point
  have hz := c.central
  have hprime := c.prime
  haveI : Fact p.Prime := ⟨hprime⟩
  have hxz : x * z = z * x := mem_centralizer_iff.mp hz.centralizes x hx.mem
  exact hSimple G p x z ((P : Subgroup G) ⊓ centralizer ({x} : Set G)) M
    hprime hS.p_ge (s622_isKGroup_centralizer hS hx) hx.order
    (orderOf_eq_prime hz.pow_eq_one hz.ne_one) hxz (s622_x_not_mem_zpowers hS hx hz)
    hx.sylow (le_inf c.B_le_P c.B_le_centralizer)
    (fun q hq => mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hz.centralizes q hq.1))
    ((pRank_eq_of_isSylowOf hprime hx.sylow).le.trans (hx.pRank_centralizer_le hS))
    (x_not_mem_frattini hS hx hx.sylow.isPGroup)
    (fun g hg => mem_zpowers_of_conj_mem_plane hS hx hz hg)
    (inf_le_left.trans hS.sylow_le) (normalizer_zpowers_le hS hz)
    (fun S' hS'Q hrk => hS.normalizer_le (P.isPGroup'.to_le (hS'Q.trans inf_le_left))
      (hS'Q.trans (inf_le_left.trans hS.sylow_le)) hrk)
    hodd hnc

theorem s622_inf_eq_bot (hP65 : S622Prop65) (c : S62Config p P M x z T)
    (hnc : ¬ (centralizer ({x} : Set G) ≤
      (M ⊓ centralizer ({x} : Set G)) ⊔ smallRankD p x))
    (hodd : Odd (Nat.card (smallRankD p x))) : smallRankD p x ⊓ M = ⊥ := by
  by_contra hne
  have hS := c.situation
  have hprime := c.prime
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
  have hBM : zpowers x ⊔ zpowers z ≤ M := c.B_le_M
  obtain ⟨f, F, hf, hf2, hfp, hFsyl, hBF, hFM⟩ :=
    s622_exists_invariant_sylow_inf_ne_bot hprime hBp hpD hBD hBM hodd hne
  have hFp : IsPGroup f F := hFsyl.isPGroup
  have hB65 : ∀ F' : Subgroup G, F' ≤ F → F' ≠ ⊥ → F' ≤ M →
      zpowers x ⊔ zpowers z ≤ normalizer (F' : Set G) → normalizer (F' : Set G) ≤ M := by
    intro F' hF'F hF'1 hF'M hBF'
    obtain ⟨hc, ho⟩ := s622_card_coprime_odd hf hf2 hfp hprime hFp hF'F
    exact hP65 G p P M x z hS c.point c.central
      (fun hN => hnc (by
        rw [hH, hDdef]
        exact s622_cover_of_hasNormalPComplement hS c.point hN))
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

theorem s622_primeCore_eq_bot (hSimple : S622KFactSimple) (hP65 : S622Prop65)
    (c : S622Conf p P M x z T S) (hnc : ¬ SmallRankCover p M x)
    (hodd : Odd (Nat.card (smallRankD p x))) : smallRankD p x = ⊥ := by
  by_contra hD1
  have hS := c.config.situation
  have hx := c.config.point
  have hz := c.config.central
  have hprime := c.config.prime
  have hp2 : p ≠ 2 := c.config.ne_two
  haveI : Fact p.Prime := ⟨hprime⟩
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
  have hinf := s622_inf_eq_bot hP65 c.config hnc'' hodd
  obtain ⟨hDH, hHD, hcop⟩ : smallRankD p x ≤ centralizer ({x} : Set G) ∧
      centralizer ({x} : Set G) ≤ normalizer (smallRankD p x : Set G) ∧
      Nat.Coprime p (Nat.card (smallRankD p x)) :=
    CFSG.LocalAnalysis.RankThreeUC.rankThreePrimeCore_spec p _
  have hpD : ¬ p ∣ Nat.card (smallRankD p x) := (Nat.Prime.coprime_iff_not_dvd hprime).mp hcop
  have hzD : z ∈ normalizer (smallRankD p x : Set G) := hHD c.config.z_mem_centralizer
  have hzord : orderOf z = p := orderOf_eq_prime hz.pow_eq_one hz.ne_one
  obtain ⟨L, hL, -, hzL, -, -, hLN⟩ := s622_apply_simple hSimple c.config hodd hnc''
  have hRL : (⁅zpowers z, S⁆ : Subgroup G) ≤ L := by
    refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
    have haL : a ∈ L := (zpowers_le.mpr hzL) ha
    have hbN : b ∈ normalizer (L : Set G) := hLN ⟨c.S_le_M hb, c.S_le_centralizer hb⟩
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
    have hNM : normalizer (zpowers (y' : G) : Set G) ≤ M := c.normalizer_le hyS hne hzN
    obtain ⟨d, hdD, hd1, hyd⟩ := hy (y' : G) hyR hy2 hy1
    have hdy : d ∈ centralizer ({(y' : G)} : Set G) := mem_centralizer_singleton_iff.mpr hyd.symm
    exact hd1 (hDM d hdD (hNM
      (CFSG.LocalAnalysis.RankThreeTheoremC.sr628_centralizer_le_normalizer_zpowers
        (y' : G) hdy)))
  obtain ⟨R₁, hR₁1, hR₁R, hR₁e, hR₁N⟩ :=
    s622_exists_central_elemAbelian c.R_isPGroup c.R_ne_bot
  have hzR₁ : z ∈ normalizer (R₁ : Set G) := hR₁N z (c.z_le_normalizer_R (mem_zpowers z))
  have hR₁S : R₁ ≤ S := hR₁R.trans c.R_le_S
  have hR₁M : normalizer (R₁ : Set G) ≤ M := c.normalizer_le hR₁S hR₁1 (zpowers_le.mpr hzR₁)
  have hR₁D : R₁ ≤ normalizer (smallRankD p x : Set G) := fun r hr =>
    hHD (c.S_le_centralizer (hR₁S hr))
  obtain ⟨d, hdD, hd1, hdz⟩ := s622_exists_commuting_of_frobenius hprime hp2 hzord hodd hpD hD1
    hR₁e hzR₁ hR₁D hzD (fun r hr hrz => hfpf r (hR₁R hr) hrz)
    (fun d hdD hdc => hDM d hdD (hR₁M (Subgroup.centralizer_le_normalizer (R₁ : Set G)
      (mem_centralizer_iff.mpr hdc))))
  exact hd1 (hDM d hdD (c.config.centralizer_le_M (mem_centralizer_singleton_iff.mpr hdz.symm)))

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
