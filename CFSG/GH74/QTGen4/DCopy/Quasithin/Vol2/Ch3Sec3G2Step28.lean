module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Lem3328G2
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3StatementsB
public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.Vol2.Ch3Sec3G2Step28
public import Certificates.Certificate431004

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.Quasithin.H13.Ch3Sec3 CFSG.Quasithin.H13.Lem3328
open CFSG.QuasithinUnique.Vol2Native (A38ForSQTKCat A39ForSQTKCat)
open scoped commutatorElement

namespace G2Step28

open CFSG.Quasithin.H13.Orbit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit
open CFSG.Quasithin.H13.G2Three CFSG.Quasithin.H13.G2Dat

variable {G : Type} [Group G]

section Step

open CFSG.Quasithin.H13.G2XS3 CFSG.Quasithin.H13.Par32

variable {L : Subgroup G}

theorem step3_3_28G2_of_F4
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) (h51 : AsB51) (h25 : Stmt3_3_25_F4)
    (h27 : Stmt3_3_27_F4) : Step3_3_28G2_F4 := by
  intro G _ _ T M L D h hG2 hTL hTC d hdD hdM hVd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLTN : L ⊔ T ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hTL
  have hred := Hyp331.vPlus_reduced h.toSetup331
  have hVQ : vPlus L T ≤ qL L T := hred.1.trans inf_le_left
  have hQV : qL L T ≤ Subgroup.centralizer (vPlus L T : Set G) :=
    Subgroup.le_centralizer_iff.mp (hred.1.trans inf_le_right)
  have hLTV : L ⊔ T ≤ Subgroup.normalizer (vPlus L T : Set G) := hred.2.2.2.1
  have hUV : blockU L ≤ vPlus L T := h.blockU_le_vPlus h38 h39 hG2.1 hTL
  have hUQ : blockU L ≤ qL L T := hUV.trans hVQ
  have hQT : qL L T ≤ T := ThreeL32.qL_le h
  have hQLT : qL L T ≤ L ⊔ T := CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hCQ : T ⊓ Subgroup.centralizer (vPlus L T : Set G) = qL L T :=
    (h.centralizer_vPlus h38 h39).2.1
  obtain ⟨ρ, β, hβs, hβk, hβe, hρL, hρL', hρT, hK⟩ := G2Rho.exists_rho h38 h39 h51 h hTL hG2
  have hX := G2XS3.cZ_eq h38 h39 h hTL hG2 ρ β hβk hβe hρL hρL' hρT
  obtain ⟨hXT, -, hRP⟩ := G2XS3.parabolic_of_rho h hTL ρ hρL' hρT hK
  have hPeq : oTwoUpper (L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) ⊔ T =
      pre ρ hLTN (pw w₀) := by
    rw [hX, hXT]
  have hR : rCZ L T = pre ρ hLTN r₀ := by
    show pCoreOf 2 (oTwoUpper (L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) ⊔
      T) = _
    rw [hPeq, hRP]
  have hker : ∀ g (hg : g ∈ qL L T), ρ ⟨g, hLTN (hQLT hg)⟩ = 1 := fun g hg =>
    rho_eq_one_of_mem_centralizer ρ β hβs hβe _
      (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hUV) (hQV hg))
  have hQR : qL L T ≤ rCZ L T := fun q hq => by
    rw [hR]
    exact (mem_pre ρ hLTN).mpr ⟨hQLT hq, by rw [hker q hq]; exact r₀.one_mem⟩
  have hRT : rCZ L T ≤ T := by
    have hTs : IsSylowTwoOf T
        (oTwoUpper (L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) ⊔ T) :=
      ⟨le_sup_right, h.sylow.1, Vol2.Ch10.SecA.not_two_dvd_index_of_le h.sylow le_sup_right⟩
    exact pCoreOf_le_of_isSylowTwoOf hTs
  have hPSL : ¬ IsPSL 3 2 1 ↥(autOn L (vPlus L T)) := by
    intro hP
    have h1 := G2Blk.card_autOn h38 h39 h hTL hG2
    rw [Vol2.Ch11.SecA.card_of_isPSL (by norm_num) hP] at h1
    revert h1
    decide
  obtain ⟨hDX, hDR, -⟩ := (h25 G T M L D h).2.1 hTC hPSL
  have hdR : d ∈ Subgroup.normalizer (rCZ L T : Set G) := hDR hdD
  have hdP : d ∈ Subgroup.normalizer ((oTwoUpper (L ⊓ Subgroup.centralizer
      (quasithinOmegaOneCenter T : Set G)) ⊔ T : Subgroup G) : Set G) :=
    C1.mem_normalizer_sup (hDX hdD) (h.DN hdD)
  have hPLT : oTwoUpper (L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) ⊔ T ≤
      L ⊔ T := sup_le_sup_right ((oTwoUpper_le _).trans inf_le_left) T
  obtain ⟨ℓb, hℓbL, hℓb⟩ := hρL' b₀ b₀_b₁_mem.1.1
  have hℓbP : ℓb ∈
      oTwoUpper (L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) ⊔ T := by
    rw [hPeq]
    refine (mem_pre ρ hLTN).mpr ⟨Subgroup.mem_sup_left hℓbL, ?_⟩
    rw [show ρ ⟨ℓb, hLTN (Subgroup.mem_sup_left hℓbL)⟩ = b₀ from hℓb]
    exact b₀_mem_pw
  have hQLU : ⁅qL L T, L⁆ ≤ blockU L := Hyp331.commutator_qL_le_blockU hG2.1 hTL
  have hΦQ := h.frattini_qL_le_tC h38 h39 hG2.1 hTL
  have hQQ : ∀ a ∈ qL L T, ∀ b ∈ qL L T, a * b * a⁻¹ * b⁻¹ ∈ tC L T := by
    intro a ha b hb
    have : Fact (IsPGroup 2 ↥(qL L T)) := ⟨CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _⟩
    have h1 : ⁅(⟨a, ha⟩ : ↥(qL L T)), ⟨b, hb⟩⁆ ∈ frattini ↥(qL L T) :=
      CFSG.commutator_le_frattini_of_isPGroup (p := 2) (by
        rw [commutator_def]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
    have h2 : ((⁅(⟨a, ha⟩ : ↥(qL L T)), ⟨b, hb⟩⁆ : ↥(qL L T)) : G) ∈ tC L T :=
      hΦQ ⟨_, h1, rfl⟩
    simpa [commutatorElement_def] using h2
  obtain ⟨-, hΦC, -⟩ := h27 G T M L D h d hdD hdM hVd hTC
  have hCe : IsElemAbelian 2 (tC L T) :=
    isElemAbelian_of_frattini_eq_bot (h.sylow.1.to_le inf_le_left) hΦC
  have hQe : IsElemAbelian 2 (qL L T) :=
    isElemAbelian_of ρ β hβs hβk hβe hρL hρL' hLTN hK hR hRT hQR hPLT (hPLT.trans hLTV)
      ⟨ℓb, hℓbP, hℓb⟩ hVQ hQV hUV hQT hCQ hred.2.1 hQLU hQQ hCe hG2.1.1 hdR hdP hVd
  have hRmem : ∀ x, x ∈ rCZ L T ↔ ∃ hx : x ∈ L ⊔ T, ρ ⟨x, hLTN hx⟩ ∈ r₀ := fun x => by
    rw [hR]
    exact mem_pre ρ hLTN
  have hRLT : rCZ L T ≤ L ⊔ T := fun x hx => ((hRmem x).mp hx).1
  have hRN : rCZ L T ≤ Subgroup.normalizer (L : Set G) := hRLT.trans hLTN
  have hRr : ∀ x (hx : x ∈ rCZ L T), ρ ⟨x, hRN hx⟩ ∈ r₀ := fun x hx => ((hRmem x).mp hx).2
  have hRK : ∀ x (hx : x ∈ rCZ L T), ρ ⟨x, hRN hx⟩ = 1 → x ∈ qL L T := fun x hx h1 =>
    hK x (hRLT hx) _ h1
  refine ⟨frattini_eq_bot_of_isElemAbelian hQe,
    fun B hBR hBe => (card_le_of_rho ρ β hβs hβk hβe hUQ hRN hRr hRK hBR hBe).1, ?_, ?_⟩
  · intro B hBm hBQ
    obtain ⟨hidx, hY8⟩ := (card_le_of_rho ρ β hβs hβk hβe hUQ hRN hRr hRK hBm.1 hBm.2.1).2
      (hBm.2.2 _ hQR hQe) hBQ
    exact centralizer_eq_of_rho ρ β hβs hβk hβe hUQ hRN hBm.1 ((hidx 8).mpr (by decide)) hY8
  · intro B B' hBm hB'm hBQ hB'Q
    obtain ⟨hidx, -⟩ := (card_le_of_rho ρ β hβs hβk hβe hUQ hRN hRr hRK hBm.1 hBm.2.1).2
      (hBm.2.2 _ hQR hQe) hBQ
    obtain ⟨hidx', -⟩ := (card_le_of_rho ρ β hβs hβk hβe hUQ hRN hRr hRK hB'm.1 hB'm.2.1).2
      (hB'm.2.2 _ hQR hQe) hB'Q
    exact le_antisymm
      (sup_le (le_sup_of_idx ρ hRN hRr hRK hBm.1 hB'm.1 fun i hi => (hidx' i).mpr ((hidx i).mp hi))
        le_sup_right)
      (sup_le (le_sup_of_idx ρ hRN hRr hRK hB'm.1 hBm.1 fun i hi => (hidx i).mpr ((hidx' i).mp hi))
        le_sup_right)

end Step

end G2Step28

end CFSG.Quasithin.H13

