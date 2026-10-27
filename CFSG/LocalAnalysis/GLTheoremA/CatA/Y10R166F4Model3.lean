module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166F4Model2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166LayerDataB
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcAction
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15ACoreArith
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15ACorePerm
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaPlusEmbed
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotUniqueStep3Basic
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SmallJ
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphLinearEnd
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphLinearGlobal
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphOmegaGlobal
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphUnitaryEnd
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphUnitaryPower
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14BlShape
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14Partner
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14PartnerModel
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14PartnerSp
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14Transfer
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindOmegaNormal
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotOmegaRowUniqueStep
public import CFSG.Quasithin.Background.F918D5

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.StandardType CFSG.StandardType.TableBF4 CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.SeitzReduction.F4Pilot CFSG.RankThree.Chevalley

section Certs



variable {F : Type} [Field F] [Finite F]

theorem f4ModelAt : F4ModelAt := by
  intro F _ _ n p hF hn hp hp2 hpd
  haveI : CharP F 2 := charP_two_of_natCard_eq_two_pow hF
  obtain ⟨q, ζ, hq, hq2, hζ, hqd⟩ := F4Fam.exists_q_zeta (F := F) hF hn
  haveI : NeZero q := ⟨hq.ne_zero⟩
  let x : adjointGroup .F4 F := endNodeElt F ζ
  let J : Subgroup (adjointGroup .F4 F) := C3Levi F
  have hxAt := endNodeAt_torusPow (K := F) (ringChar.eq F 2) hq hq2 hζ
  have hxq : x ^ q = 1 := (mem_torusPow.mp hxAt.1).2
  have hx1 : x ≠ 1 := hxAt.2.1
  have hZK : Subgroup.center (adjointGroup .F4 F) = ⊥ :=
    center_adjointGroup_eq_bot (τ := .F4) (K := F)
  have hev : evenRank (adjointGroup .F4 F) = 4 := evenRank_adjointGroup_F4 hF hn
  have he : 4 ≤ evenRank (adjointGroup .F4 F) := by omega
  have hcomp := endNode_comp (F := F) hq hq2 hζ
  have hJx : J ≤ Subgroup.centralizer ({x} : Set (adjointGroup .F4 F)) := hcomp.1.1
  have hJq : CFSG.IsQuasisimple ↥J := isQuasisimple_C3Levi (K := F)
  have hcomm : ∀ g ∈ Subgroup.centralizer ({x} : Set (adjointGroup .F4 F)),
      ∀ h ∈ Subgroup.centralizer ({x} : Set (adjointGroup .F4 F)),
      g * h * g⁻¹ * h⁻¹ ∈ J := by
    intro g hg h hh
    have h3 : 3 ≤ orderOf ζ := by
      rw [hζ]
      exact lt_of_le_of_ne hq.two_le (Ne.symm hq2)
    obtain ⟨hT, -, -⟩ := toralCentralizer_rDiag_eq_sup (K := F) (ringChar.eq F 2) h3
    have hg' : (g : ModGL .F4 F) ∈ toralCentralizer .F4 F (rDiag ζ) :=
      (mem_centralizer_endNodeElt_iff (K := F)).1 hg
    have hh' : (h : ModGL .F4 F) ∈ toralCentralizer .F4 F (rDiag ζ) :=
      (mem_centralizer_endNodeElt_iff (K := F)).1 hh
    rw [hT] at hg' hh'
    rw [mem_C3Levi_iff]
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, C3Set_eq_c3LeviRoots] using
      commutator_mem_rootSpan_C3Set hg' hh'
  have hJlab : HasLabel ↥J (fun l : GLALabel => l = ⟨.B, 3, n⟩) :=
    hasLabel_c3Levi hF (by omega)
  have hshape : ∀ lab : GLALabel, HasLabel (adjointGroup .F4 F) (fun l : GLALabel => l = lab) →
      JShape lab (3 ∣ Nat.card (Subgroup.center (adjointGroup .F4 F))) ⟨.B, 3, n⟩ :=
    F4Fam.shape_f4 (F := F) hF hn
  have hsym := symplectic_mult (J := ↥J) (m := 3) (n := n) (by norm_num) hn hJlab
    (CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds)
  have hdvd2 : ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ (2 ^ (2 * n) - 1) →
      r ∣ Nat.card (↥J ⧸ Subgroup.center ↥J) := hsym.2.2.2
  have hp2n : p ∣ (2 ^ (2 * n) - 1) := by
    have h1 : p ∣ 2 ^ n + 1 := hpd
    have h2 : 2 ^ n + 1 ∣ (2 ^ n) ^ 2 - 1 := by
      have := Nat.sq_sub_sq (2 ^ n) 1
      rw [one_pow] at this
      rw [this]
      exact dvd_mul_right _ _
    have h3 : 2 ^ (2 * n) - 1 = (2 ^ n) ^ 2 - 1 := by
      rw [show 2 * n = n * 2 by omega, pow_mul]
    rw [h3]
    exact h1.trans h2
  have hq2n : q ∣ (2 ^ (2 * n) - 1) := by
    have h2 : 2 ^ n - 1 ∣ (2 ^ n) ^ 2 - 1 :=
      Nat.sub_one_dvd_pow_sub_one (2 ^ n) 2
    have h3 : 2 ^ (2 * n) - 1 = (2 ^ n) ^ 2 - 1 := by
      rw [show 2 * n = n * 2 by omega, pow_mul]
    rw [h3]
    exact hqd.trans h2
  have hpqdvd : p * q ∣ Nat.card (↥J ⧸ Subgroup.center ↥J) := by
    have hne : p ≠ q := by
      intro hpq_eq
      subst hpq_eq
      have hdiff : p ∣ 2 ^ n + 1 - (2 ^ n - 1) := Nat.dvd_sub hpd hqd
      have h2 : p ∣ 2 := by
        have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
        rwa [show 2 ^ n + 1 - (2 ^ n - 1) = 2 by omega] at hdiff
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2)
    have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).2 hne
    exact hcop.mul_dvd_of_dvd_of_dvd (hdvd2 p hp hp2 hp2n) (hdvd2 q hq hq2 hq2n)
  have hm2 : evenRank (adjointGroup .F4 F) + 2 ≤ twoRank ↥J := by
    rw [hev]
    have := hsym.2.2.1
    omega
  have hD : LayerData166At (⟨.B, 3, n⟩ : GLALabel) :=
    layerData166At_B (m := 3) (n := n) (by norm_num) hn
  have hqn : q ∣ 2 ^ (⟨.B, 3, n⟩ : GLALabel).n - 1 := by
    simpa using hqd
  have hrank : (⟨.B, 3, n⟩ : GLALabel).rank = evenRank (adjointGroup .F4 F) - 1 := by
    rw [hev]
  obtain ⟨B', hConcl⟩ := exists_concl166S_of_layerData166At (K := adjointGroup .F4 F)
    (p := p) (q := q) (x := x) (J := J) hq hq2 hxq hx1 hZK he hJx hJq hcomm
    ⟨.B, 3, n⟩ hJlab hshape hm2 hpqdvd hsym.1.1 hsym.1.2 hD hqn hrank
  exact ⟨q, B', x, J, hConcl⟩

theorem i166On_famF4_of_transport
    (htr : ∀ {K R : Type} [Group K] [Finite K] [Group R] [Finite R], (K ≃* R) → ∀ {p : ℕ},
      (∃ (q : ℕ) (B' : Subgroup R) (x' : R) (J : Subgroup R), Concl166S R p q B' x' J) →
      ∃ (q : ℕ) (B' : Subgroup K) (x' : K) (J : Subgroup K), Concl166S K p q B' x' J) :
    I166On i166FamF4 :=
  i166On_famF4_of_transport_of_model f4ModelAt htr

end Certs

end CFSG.LocalAnalysis.GLTheoremA.Y10F
