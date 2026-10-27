module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166LayerDataD
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166LayerData
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Mult
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2EUp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.TablesHolds
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Cases
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166OmBlocks
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166OmBlocks2Base

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open Subgroup CFSG.Open
open CFSG.SeitzReduction.OmegaPilot
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadPlus plusIndexEquiv)

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem evenRank_coordinatePlus (m n : ℕ) (hF : Nat.card F = 2 ^ n) (hm : 4 ≤ m)
    (hn : 2 ≤ n) :
    evenRank (matrixProjectiveDerived (coordinateQuadPlus m F)) = m := by
  have hlab := hasLabel_coordinatePlus (F := F) m n hF hm hn
  have hK : Rk2IsLabel (matrixProjectiveDerived (coordinateQuadPlus m F)) ⟨.D, m, n⟩ := hlab
  have hlow : m ≤ evenRank (matrixProjectiveDerived (coordinateQuadPlus m F)) :=
    rk2_low_d_ge hK rfl hm hn
  have hup : evenRank (matrixProjectiveDerived (coordinateQuadPlus m F)) ≤ m :=
    (rk2_eUpAt_of_tables rk2KRank rk2Upper_holds (K := matrixProjectiveDerived
      (coordinateQuadPlus m F)) (lab := ⟨.D, m, n⟩) hK).bd (Or.inr rfl) hn
  exact le_antisymm hup hlow


theorem concl166S_pairTorus {p m n q : ℕ} {ζ : Fˣ} (hp : p.Prime) (hp2 : p ≠ 2) (hm : 5 ≤ m)
    (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) (hpvd : p ∣ 2 ^ n + 1) (hq : q.Prime) (hq2 : q ≠ 2)
    (hqdvd : q ∣ Nat.card F - 1) (hζ : orderOf ζ = q)
    (hD : LayerData166At (⟨.D, m - 1, n⟩ : GLALabel)) :
    ∃ (B' : Subgroup (matrixProjectiveDerived (coordinateQuadPlus m F)))
      (x' : matrixProjectiveDerived (coordinateQuadPlus m F))
      (J : Subgroup (matrixProjectiveDerived (coordinateQuadPlus m F))),
      Concl166S (matrixProjectiveDerived (coordinateQuadPlus m F)) p q B' x' J := by
  classical
  have hm4 : 4 ≤ m := by omega
  have hF4 : 4 ≤ Nat.card F := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have heven : evenRank (matrixProjectiveDerived (coordinateQuadPlus m F)) = m :=
    evenRank_coordinatePlus (F := F) m n hF hm4 hn
  obtain ⟨-, hZR⟩ := isQuasisimple_center_coordinatePlus (F := F) (m := m) (by omega)
  have hζ1 : ζ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hζ
    exact hq.ne_one hζ.symm
  have hB : IsElemAbelian q (OmegaPair.qTorus (K := F) m q) :=
    OmegaPair.isElemAbelian_qTorus (K := F) m q hqdvd
  have hxmem : OmegaPair.qTorusElt (K := F) m hm4 ζ ∈ OmegaPair.qTorus (K := F) m q :=
    OmegaPair.qTorusElt_mem_qTorus (K := F) m hm4 (by rw [← hζ]; exact pow_orderOf_eq_one ζ)
  have hxq : (OmegaPair.qTorusElt (K := F) m hm4 ζ) ^ q = 1 := hB.2 _ hxmem
  have hx1 : OmegaPair.qTorusElt (K := F) m hm4 ζ ≠ 1 :=
    OmegaPair.qTorusElt_ne_one (K := F) m hm4 hζ1
  have hxT : OmegaPair.qTorusElt (K := F) m hm4 ζ ∈
      pairTorus (K := F) (n := m) (OmegaPair.zeroIdx m hm4) :=
    OmegaPair.qTorusElt_mem_pairTorus (K := F) m hm4 ζ
  have hJx : pairPerp (K := F) (n := m) (OmegaPair.zeroIdx m hm4) ≤
      Subgroup.centralizer ({OmegaPair.qTorusElt (K := F) m hm4 ζ} :
        Set (matrixProjectiveDerived (coordinateQuadPlus m F))) := by
    refine ((isHypCoord_coordinateQuadPlus (K := F) (OmegaPair.zeroIdx m hm4)).pairPerpOf_le_centralizer
      hF4).trans (Subgroup.centralizer_le ?_)
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    exact hz ▸ hxT
  have hJq : CFSG.IsQuasisimple ↥(pairPerp (K := F) (n := m) (OmegaPair.zeroIdx m hm4)) :=
    isQuasisimple_pairPerp (K := F) (n := m) hm4 (OmegaPair.zeroIdx m hm4)
  have hcomm : ∀ g ∈ Subgroup.centralizer ({OmegaPair.qTorusElt (K := F) m hm4 ζ} :
        Set (matrixProjectiveDerived (coordinateQuadPlus m F))),
      ∀ h ∈ Subgroup.centralizer ({OmegaPair.qTorusElt (K := F) m hm4 ζ} :
        Set (matrixProjectiveDerived (coordinateQuadPlus m F))),
      g * h * g⁻¹ * h⁻¹ ∈ pairPerp (K := F) (n := m) (OmegaPair.zeroIdx m hm4) :=
    commutator_mem_pairPerp_of_mem_centralizer_pairTorus_singleton (K := F) hF4 hxT hx1
  have hJlab : HasLabel ↥(pairPerp (K := F) (n := m) (OmegaPair.zeroIdx m hm4))
      (fun l : GLALabel => l = ⟨.D, m - 1, n⟩) :=
    hasLabel_pairPerp (F := F) (m := m) (n := n) hF (by omega) hn (OmegaPair.zeroIdx m hm4)
  have hshape : ∀ lab : GLALabel,
      HasLabel (matrixProjectiveDerived (coordinateQuadPlus m F)) (fun l : GLALabel => l = lab) →
      JShape lab (3 ∣ Nat.card (Subgroup.center
        (matrixProjectiveDerived (coordinateQuadPlus m F)))) ⟨.D, m - 1, n⟩ := by
    intro lab hlab
    have hlabK : HasLabel (matrixProjectiveDerived (coordinateQuadPlus m F))
        (· = ⟨.D, m, n⟩) := hasLabel_coordinatePlus (F := F) m n hF hm4 hn
    have he4 : 4 ≤ evenRank (matrixProjectiveDerived (coordinateQuadPlus m F)) := by
      rw [heven]; omega
    rcases label_eq_or_BC he4 hlab hlabK with heq | ⟨-, h2, -, -⟩
    · subst heq
      refine ⟨rfl, Or.inr (Or.inl ⟨rfl, rfl, ?_⟩)⟩
      show m - 1 + 1 = m
      omega
    · exact absurd h2 (by simp)
  have hGA : CFSG.Open.GriessAllModelsStatement :=
    CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds
  have hsymp := omegaPlus_mult (J := ↥(pairPerp (K := F) (n := m) (OmegaPair.zeroIdx m hm4)))
    (m := m - 1) (n := n) (by omega) hn hJlab hGA
  have hmul_arith : m + 2 ≤ n * ((m - 1) * ((m - 1) - 1) / 2) := by
    obtain ⟨d, rfl⟩ : ∃ d, m = d + 5 := ⟨m - 5, by omega⟩
    have hdvd : 2 ∣ (d + 5 - 1) * ((d + 5 - 1) - 1) :=
      even_iff_two_dvd.mp (Nat.even_mul_pred_self (d + 5 - 1))
    have h2k : 2 * ((d + 5 - 1) * ((d + 5 - 1) - 1) / 2) =
        (d + 5 - 1) * ((d + 5 - 1) - 1) := Nat.mul_div_cancel' hdvd
    have hge : d + 5 + 2 ≤ 2 * ((d + 5 - 1) * ((d + 5 - 1) - 1) / 2) := by
      rw [h2k]
      have e1 : d + 5 - 1 = d + 4 := by omega
      have e2 : d + 4 - 1 = d + 3 := by omega
      rw [e1, e2]
      nlinarith
    exact hge.trans (Nat.mul_le_mul_right _ hn)
  have hm2 : evenRank (matrixProjectiveDerived (coordinateQuadPlus m F)) + 2 ≤
      twoRank ↥(pairPerp (K := F) (n := m) (OmegaPair.zeroIdx m hm4)) := by
    rw [heven]
    exact hmul_arith.trans hsymp.2.2.1
  have hpdvd : p ∣ 2 ^ (2 * n) - 1 := by
    have hfac : 2 ^ (2 * n) - 1 = (2 ^ n + 1) * (2 ^ n - 1) := by
      rw [show 2 * n = n * 2 by omega, pow_mul, show (1 : ℕ) = 1 ^ 2 by norm_num,
        Nat.sq_sub_sq]
      ring
    rw [hfac]
    exact dvd_mul_of_dvd_left hpvd _
  have hqdvd2 : q ∣ 2 ^ (2 * n) - 1 := by
    have hq' : q ∣ 2 ^ n - 1 := by rwa [hF] at hqdvd
    have hfac : 2 ^ (2 * n) - 1 = (2 ^ n + 1) * (2 ^ n - 1) := by
      rw [show 2 * n = n * 2 by omega, pow_mul, show (1 : ℕ) = 1 ^ 2 by norm_num,
        Nat.sq_sub_sq]
      ring
    rw [hfac]
    exact dvd_mul_of_dvd_right hq' _
  have hpq : p ≠ q := by
    intro hpq
    have hq' : q ∣ 2 ^ n - 1 := by rwa [hF] at hqdvd
    have hp' : q ∣ 2 ^ n + 1 := hpq ▸ hpvd
    have hsub : q ∣ (2 ^ n + 1) - (2 ^ n - 1) := Nat.dvd_sub hp' hq'
    have h2 : (2 ^ n + 1) - (2 ^ n - 1) = 2 := by omega
    rw [h2] at hsub
    exact hp2 (hpq ▸ (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hsub)
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).2 hpq
  have hdvd : p * q ∣ Nat.card
      (↥(pairPerp (K := F) (n := m) (OmegaPair.zeroIdx m hm4)) ⧸
        Subgroup.center ↥(pairPerp (K := F) (n := m) (OmegaPair.zeroIdx m hm4))) :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop
      (hsymp.2.2.2 p hp hp2 hpdvd) (hsymp.2.2.2 q hq hq2 hqdvd2)
  have hZJ : Subgroup.center ↥(pairPerp (K := F) (n := m) (OmegaPair.zeroIdx m hm4)) = ⊥ :=
    center_pairPerp (K := F) (n := m) hm4 (OmegaPair.zeroIdx m hm4)
  have hqn : q ∣ 2 ^ (⟨.D, m - 1, n⟩ : GLALabel).n - 1 := by
    have hq' : q ∣ 2 ^ n - 1 := by rwa [hF] at hqdvd
    simpa using hq'
  have hrank : (⟨.D, m - 1, n⟩ : GLALabel).rank =
      evenRank (matrixProjectiveDerived (coordinateQuadPlus m F)) - 1 := by
    show m - 1 = evenRank (matrixProjectiveDerived (coordinateQuadPlus m F)) - 1
    rw [heven]
  obtain ⟨B', h⟩ := exists_concl166S_of_layerData166At
    (K := matrixProjectiveDerived (coordinateQuadPlus m F)) (p := p) (q := q)
    (x := OmegaPair.qTorusElt (K := F) m hm4 ζ)
    (J := pairPerp (K := F) (n := m) (OmegaPair.zeroIdx m hm4))
    hq hq2 hxq hx1 hZR (by rw [heven]; omega) hJx hJq hcomm ⟨.D, m - 1, n⟩ hJlab hshape hm2
    hdvd hZJ hsymp.1.2 hD hqn hrank
  exact ⟨B', OmegaPair.qTorusElt (K := F) m hm4 ζ,
    pairPerp (K := F) (n := m) (OmegaPair.zeroIdx m hm4), h⟩

theorem exists_concl166S_pairTorus {p m n q : ℕ} {ζ : Fˣ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hm : 5 ≤ m) (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) (hpvd : p ∣ 2 ^ n + 1)
    (hq : q.Prime) (hq2 : q ≠ 2) (hqdvd : q ∣ Nat.card F - 1) (hζ : orderOf ζ = q)
    (hD : LayerData166At (⟨.D, m - 1, n⟩ : GLALabel)) :
    ∃ (q' : ℕ) (B' : Subgroup (matrixProjectiveDerived (coordinateQuadPlus m F)))
      (x' : matrixProjectiveDerived (coordinateQuadPlus m F))
      (J : Subgroup (matrixProjectiveDerived (coordinateQuadPlus m F))),
      Concl166S (matrixProjectiveDerived (coordinateQuadPlus m F)) p q' B' x' J := by
  obtain ⟨B', x', J, h⟩ :=
    concl166S_pairTorus (F := F) hp hp2 hm hn hF hpvd hq hq2 hqdvd hζ hD
  exact ⟨q, B', x', J, h⟩

theorem i166On_famDFive_of_transport
    (htr : ∀ {K R : Type} [Group K] [Finite K] [Group R] [Finite R], (K ≃* R) → ∀ {p : ℕ},
      (∃ (q : ℕ) (B' : Subgroup R) (x' : R) (J : Subgroup R), Concl166S R p q B' x' J) →
      ∃ (q : ℕ) (B' : Subgroup K) (x' : K) (J : Subgroup K), Concl166S K p q B' x' J)
    (hLD : ∀ (m n : ℕ), 4 ≤ m → 2 ≤ n → LayerData166At (⟨.D, m, n⟩ : GLALabel)) :
    I166On (fun lab p z => i166FamD lab p z ∧ 5 ≤ lab.rank) := by
  intro K _ _ lab p hlab hfam hp hp2 hns he hr
  obtain ⟨⟨htag, hn, hpvd⟩, hlab5⟩ := hfam
  have hlab_eq : lab = (⟨.D, lab.rank, lab.n⟩ : GLALabel) := by
    rcases lab with ⟨t, r, s⟩
    simp only at htag
    subst htag
    rfl
  have hlow : lab.rank ≤ evenRank K := rk2_low_d_ge hlab htag (by omega) hn
  have hup : evenRank K ≤ lab.rank :=
    (rk2_eUpAt_of_tables rk2KRank rk2Upper_holds (K := K) (lab := lab) hlab).bd
      (Or.inr htag) hn
  have heven : evenRank K = lab.rank := le_antisymm hup hlow
  have hZ : Subgroup.center K = ⊥ := rk2_center_eq_bot_of_large hlab (Or.inr (Or.inl htag)) hn
  rw [hlab_eq] at hlab
  obtain ⟨F, hfield, hfinite, hchar, hF, ⟨e⟩⟩ :=
    exists_mulEquiv_matrixProjectiveDerived_of_isLabel (K := K) (m := lab.rank) (n := lab.n)
      (by omega) hn hlab hZ
  letI : Field F := hfield
  letI : Finite F := hfinite
  letI : CharP F 2 := hchar
  have hF4 : 4 ≤ Nat.card F := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ lab.n := Nat.pow_le_pow_right (by norm_num) hn
  have hoddF : Odd (Nat.card F - 1) := by
    rw [hF]
    have h2 : Even (2 ^ lab.n) := even_iff_two_dvd.mpr (dvd_pow_self 2 (by omega))
    have hpos : 1 ≤ 2 ^ lab.n := Nat.one_le_two_pow
    exact Nat.Even.sub_odd hpos h2 odd_one
  obtain ⟨q, hq, hqdvd⟩ := Nat.exists_prime_and_dvd (n := Nat.card F - 1) (by omega)
  have hq2 : q ≠ 2 := by
    intro h
    subst h
    exact (Nat.not_even_iff_odd.mpr hoddF) (even_iff_two_dvd.mpr hqdvd)
  haveI : Fact q.Prime := ⟨hq⟩
  have hqdvd' : q ∣ Nat.card Fˣ := by rwa [Nat.card_units]
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) q hqdvd'
  exact htr e (exists_concl166S_pairTorus (F := F) (p := p) (m := lab.rank) (n := lab.n)
    (q := q) (ζ := ζ) hp hp2 (by omega) hn hF hpvd hq hq2 hqdvd hζ
    (hLD (lab.rank - 1) lab.n (by omega) hn))

end CFSG.LocalAnalysis.GLTheoremA.Y10F
