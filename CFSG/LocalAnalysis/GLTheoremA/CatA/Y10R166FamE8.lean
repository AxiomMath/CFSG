module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166LayerData
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166E8Cent
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166E8Levi
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Cases
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Label
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Mult
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2EUp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.TablesHolds
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.KRank
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.LowerSymplecticOrth
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.Shared
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.UpperShared
public import CFSG.LieType.Chevalley.AdjointCenter
public import CFSG.LieType.Chevalley.GraphFixedD4TorusWords
public import CFSG.LieType.Steinberg.Adjoint.Perfect
public import CFSG.LocalAnalysis.StandardType.MarkingChevalley
public import CFSG.LocalAnalysis.ComponentClassification.GoldschmidtTDGriess
public import CFSG.Adapters.TauCetiExceptional.BridgeTransport
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R16ExcLabel
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcAction
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15ACoreArith
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15ACorePerm
public import CFSG.Quasithin.Background.F918D5

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType
  CFSG.LocalAnalysis.GLTheoremA CFSG.StandardType
open CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped commutatorElement


theorem hasLabel_adjointGroup_E8 {n : ℕ} (hn : 2 ≤ n) :
    HasLabel ↥(adjointGroup Tag.E8 (GaloisField 2 n)) (· = ⟨.E8, 0, n⟩) := by
  have hJq : CFSG.IsQuasisimple ↥(adjointGroup Tag.E8 (GaloisField 2 n)) :=
    CFSG.LieType.Steinberg.Adjoint.isQuasisimple_e8 (GaloisField 2 n)
  have hlab : GLAInLambda2 (⟨.E8, 0, n⟩ : GLALabel) := by
    change CFSG.Assembly.LargeEvenInLambda2 (⟨.E8, 0, n⟩ : GLALabel)
    refine ⟨?_, rfl⟩
    show 1 ≤ n
    omega
  refine hasLabel_of_quasisimple_rawDatum hJq hlab ?_
  refine ⟨GaloisField 2 n, inferInstance, inferInstance,
    GaloisField.card 2 n (by omega), ?_⟩
  obtain ⟨e⟩ := CFSG.StandardType.centerQuot_chevGroup_equiv
    (K := GaloisField 2 n) (τ := Tag.E8)
  exact ⟨e.symm⟩

theorem evenRank_adjointGroup_E8 {n : ℕ} (hn : 2 ≤ n) :
    evenRank ↥(adjointGroup Tag.E8 (GaloisField 2 n)) = 8 := by
  have hlab := hasLabel_adjointGroup_E8 hn
  have hK : Rk2IsLabel ↥(adjointGroup Tag.E8 (GaloisField 2 n)) ⟨.E8, 0, n⟩ := hlab
  have hlow : 8 ≤ evenRank ↥(adjointGroup Tag.E8 (GaloisField 2 n)) :=
    (rk2Lower_holds _ ⟨.E8, 0, n⟩ hK).e8 rfl hn
  have hup : evenRank ↥(adjointGroup Tag.E8 (GaloisField 2 n)) ≤ 8 :=
    (rk2_eUpAt_of_tables rk2KRank rk2Upper_holds
      (K := ↥(adjointGroup Tag.E8 (GaloisField 2 n))) (lab := ⟨.E8, 0, n⟩) hK).e8 rfl hn
  exact le_antisymm hup hlow

private def e8NodeZeroToralCoeff : Fin Tag.E8.rank → ℤ := ![4, 5, 7, 10, 8, 6, 4, 2]

private theorem cartan_mul_e8NodeZeroToralCoeff :
    ∀ i : Fin Tag.E8.rank,
      ∑ j, e8NodeZeroToralCoeff j * Tag.cartan .E8 j i = if i = 0 then 1 else 0 := by
  decide +kernel

private theorem e8NodeZeroToral_eq_cartanChar {K : Type} [Field K] (ζ : Kˣ) :
    e8NodeZeroToral ζ = cartanChar (fun i => ζ ^ e8NodeZeroToralCoeff i) := by
  funext l
  rw [e8NodeZeroToral]
  calc (if l = 0 then ζ else 1)
      = ζ ^ (if l = 0 then (1 : ℤ) else 0) := by split <;> simp
    _ = ζ ^ (∑ j, e8NodeZeroToralCoeff j * Tag.cartan .E8 j l) := by
        rw [cartan_mul_e8NodeZeroToralCoeff l]
    _ = ∏ j, ζ ^ (e8NodeZeroToralCoeff j * Tag.cartan .E8 j l) :=
        (Finset.prod_zpow_eq_zpow_sum (Finset.univ : Finset (Fin Tag.E8.rank)) ζ
          (fun j => e8NodeZeroToralCoeff j * Tag.cartan .E8 j l)).symm
    _ = ∏ j, (ζ ^ e8NodeZeroToralCoeff j) ^ (Tag.cartan .E8 j l) := by
        refine Finset.prod_congr rfl fun j _ => ?_
        rw [zpow_mul]
    _ = cartanChar (fun i => ζ ^ e8NodeZeroToralCoeff i) l := by
        simp only [cartanChar]

theorem rootDiagUnit_e8NodeZeroToral_mem_adjointGroup {K : Type} [Field K] (ζ : Kˣ) :
    rootDiagUnit Tag.E8 (e8NodeZeroToral ζ) ∈ adjointGroup Tag.E8 K := by
  rw [e8NodeZeroToral_eq_cartanChar ζ, ← list_prod_torusElt_eq_rootDiagUnit]
  refine Subgroup.list_prod_mem _ ?_
  rintro g hg
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hg
  exact torusElt_mem_adjointGroup j _

private theorem centralizer_subgroupOf_adjointGroup {K : Type} [Field K]
    {x : ModGL Tag.E8 K} (hx : x ∈ adjointGroup Tag.E8 K) :
    Subgroup.centralizer ({⟨x, hx⟩} : Set ↥(adjointGroup Tag.E8 K)) =
      (adjointGroup Tag.E8 K ⊓ Subgroup.centralizer ({x} : Set (ModGL Tag.E8 K))).subgroupOf
        (adjointGroup Tag.E8 K) := by
  ext y
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    exact ⟨y.2, by simpa using congrArg Subtype.val h⟩
  · rintro ⟨-, h⟩
    exact Subtype.ext h

theorem exists_concl166S_of_toral_E8 (n p q : ℕ) (hn : 2 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpdvd : p ∣ 2 ^ n + 1) (hq : q.Prime) (hq2 : q ≠ 2) (hqdvd : q ∣ 2 ^ n - 1)
    {ζ : (GaloisField 2 n)ˣ} (hζ : orderOf ζ = q) (hD7 : LayerData166At ⟨.D, 7, n⟩) :
    ∃ B' : Subgroup ↥(adjointGroup Tag.E8 (GaloisField 2 n)),
      Concl166S ↥(adjointGroup Tag.E8 (GaloisField 2 n)) p q B'
        ⟨rootDiagUnit Tag.E8 (e8NodeZeroToral ζ),
          rootDiagUnit_e8NodeZeroToral_mem_adjointGroup ζ⟩
        ((subsystemGroup Tag.E8 (GaloisField 2 n) {i : Fin Tag.E8.rank | i ≠ 0}).subgroupOf
          (adjointGroup Tag.E8 (GaloisField 2 n))) := by
  classical
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Kf := GaloisField 2 n
  let A : Subgroup (ModGL Tag.E8 Kf) := adjointGroup Tag.E8 Kf
  have hKcard : Nat.card Kf = 2 ^ n := GaloisField.card 2 n (by omega)
  have hζq : ζ ^ q = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
  have hmem : rootDiagUnit Tag.E8 (e8NodeZeroToral ζ) ∈ A :=
    rootDiagUnit_e8NodeZeroToral_mem_adjointGroup ζ
  let x : ↥A := ⟨rootDiagUnit Tag.E8 (e8NodeZeroToral ζ), hmem⟩
  let Q : Subgroup (ModGL Tag.E8 Kf) := subsystemGroup Tag.E8 Kf {i : Fin Tag.E8.rank | i ≠ 0}
  have hQA : Q ≤ A := by
    refine (Subgroup.closure_le _).2 ?_
    rintro g ⟨i, -, c, rfl | rfl⟩
    · exact xUnit_mem_adjointGroup i c
    · exact yUnit_mem_adjointGroup i c
  let J : Subgroup ↥A := Q.subgroupOf A
  have hrange : Set.range e8D7Node = {i : Fin Tag.E8.rank | i ≠ 0} := by
    ext i; rw [mem_range_e8D7Node]; simp
  have hJlabQ : HasLabel ↥Q (· = ⟨.D, 7, n⟩) := by
    have h := hasLabel_subsystemGroup_e8D7 (K := Kf) (f := n) hn hKcard
    rwa [hrange] at h
  have hJlab : HasLabel ↥J (· = ⟨.D, 7, n⟩) :=
    (hasLabel_congr (Subgroup.subgroupOfEquivOfLe hQA) (fun l => l = ⟨.D, 7, n⟩)).2 hJlabQ
  have hJq : CFSG.IsQuasisimple ↥J := by
    have h := (isQuasisimple_and_lieModel_subsystemGroup_e8D7 (K := Kf) (f := n) hn hKcard).1
    rw [hrange] at h
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hQA).symm h
  have hxq : x ^ q = 1 := by
    apply Subtype.ext
    have h1 : (rootDiagUnitHom Tag.E8 Kf (e8NodeZeroToral ζ)) ^ q = 1 := by
      rw [← map_pow, show (e8NodeZeroToral ζ) ^ q = 1 from by
        funext i
        rw [Pi.pow_apply, e8NodeZeroToral]
        by_cases hi : i = 0
        · rw [if_pos hi]; simpa using hζq
        · rw [if_neg hi]; simp, map_one]
    simpa [x, rootDiagUnitHom] using h1
  have hx1 : x ≠ 1 := by
    intro h
    have h1 : rootDiagUnit Tag.E8 (e8NodeZeroToral ζ) = 1 := congrArg Subtype.val h
    have h2 : e8NodeZeroToral ζ = 1 :=
      rootDiagUnit_injective (h1.trans rootDiagUnit_one.symm)
    exact e8NodeZeroToral_ne_one hq hq2 hζ h2
  have hQC : Q ≤ Subgroup.centralizer
      ({rootDiagUnit Tag.E8 (e8NodeZeroToral ζ)} : Set (ModGL Tag.E8 Kf)) := by
    have h1 : Q ≤ toralCentralizer Tag.E8 Kf (e8NodeZeroToral ζ) := by
      rw [toralCentralizer_e8NodeZeroToral_eq_torusGroup_sup_subsystemGroup hq hq2 hζ]
      exact le_sup_right
    exact h1.trans (by rw [toralCentralizer]; exact inf_le_right)
  have hJx : J ≤ Subgroup.centralizer ({x} : Set ↥A) := by
    intro j hj
    rw [centralizer_subgroupOf_adjointGroup hmem]
    refine Subgroup.mem_subgroupOf.2 ⟨j.2, ?_⟩
    exact hQC hj
  have hcomm : ∀ g ∈ Subgroup.centralizer ({x} : Set ↥A),
      ∀ h ∈ Subgroup.centralizer ({x} : Set ↥A), g * h * g⁻¹ * h⁻¹ ∈ J := by
    intro g hg h hh
    rw [centralizer_subgroupOf_adjointGroup hmem] at hg hh
    rw [Subgroup.mem_subgroupOf] at hg hh
    refine Subgroup.mem_subgroupOf.2 ?_
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using
      commutator_mem_toralCentralizer_e8NodeZeroToral hq hq2 hζ
        (g := (g : ModGL Tag.E8 Kf)) (h := (h : ModGL Tag.E8 Kf)) hg hh
  have hZK : Subgroup.center ↥A = ⊥ := center_adjointGroup_eq_bot
  have he8 : evenRank ↥A = 8 := evenRank_adjointGroup_E8 hn
  have he : 4 ≤ evenRank ↥A := by rw [he8]; norm_num
  have hGA : CFSG.Open.GriessAllModelsStatement :=
    CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds
  have hmul := omegaPlus_mult (J := ↥J) (m := 7) (n := n) (by norm_num) hn hJlab hGA
  obtain ⟨⟨hZJ, hmult⟩, -, hm2', hdvd'⟩ := hmul
  have hm2 : evenRank ↥A + 2 ≤ twoRank ↥J := by
    have h21 : 7 * (7 - 1) / 2 = 21 := by norm_num
    rw [h21] at hm2'
    rw [he8]
    have h10 : 10 ≤ n * 21 := by nlinarith
    omega
  have hpq : p ≠ q := by
    intro hpq
    subst hpq
    have h1 : p ∣ (2 ^ n + 1) - (2 ^ n - 1) := Nat.dvd_sub hpdvd hqdvd
    have hp1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    rw [show 2 ^ n + 1 - (2 ^ n - 1) = 2 by omega] at h1
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h1)
  have hfac : 2 ^ (2 * n) - 1 = (2 ^ n - 1) * (2 ^ n + 1) := by
    rw [show 2 * n = n * 2 by omega, pow_mul]
    simpa [mul_comm] using Nat.sq_sub_sq (2 ^ n) 1
  have hpd : p ∣ 2 ^ (2 * n) - 1 := by
    rw [hfac]; exact dvd_mul_of_dvd_right hpdvd _
  have hqd : q ∣ 2 ^ (2 * n) - 1 := by
    rw [hfac]; exact dvd_mul_of_dvd_left hqdvd _
  have hdvd : p * q ∣ Nat.card (↥J ⧸ Subgroup.center ↥J) :=
    (Nat.coprime_primes hp hq).2 hpq |>.mul_dvd_of_dvd_of_dvd
      (hdvd' p hp hp2 hpd) (hdvd' q hq hq2 hqd)
  have hRlabel : HasLabel ↥A (· = ⟨.E8, 0, n⟩) := hasLabel_adjointGroup_E8 hn
  have hshape : ∀ lab : GLALabel, HasLabel ↥A (fun l : GLALabel => l = lab) →
      JShape lab (3 ∣ Nat.card (Subgroup.center ↥A)) ⟨.D, 7, n⟩ := by
    intro lab hlab
    rcases label_eq_or_BC (K := ↥A) he hlab hRlabel with hEq | ⟨-, h2, -, -⟩
    · subst hEq
      refine ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))))⟩
    · exact absurd h2 (by simp)
  have hrank : (⟨.D, 7, n⟩ : GLALabel).rank = evenRank ↥A - 1 := by
    rw [he8]
  obtain ⟨B', hconcl⟩ := exists_concl166S_of_layerData166At (K := ↥A) (p := p) (q := q)
    (x := x) (J := J) hq hq2 hxq hx1 hZK he hJx hJq hcomm ⟨.D, 7, n⟩ hJlab hshape hm2 hdvd
    hZJ hmult hD7 hqdvd hrank
  exact ⟨B', hconcl⟩


theorem exists_concl166S_adjointGroup_E8 (n p : ℕ) (hn : 2 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpdvd : p ∣ 2 ^ n + 1) (hD7 : LayerData166At ⟨.D, 7, n⟩) :
    ∃ (q : ℕ) (B' : Subgroup ↥(adjointGroup Tag.E8 (GaloisField 2 n)))
      (x' : ↥(adjointGroup Tag.E8 (GaloisField 2 n)))
      (J : Subgroup ↥(adjointGroup Tag.E8 (GaloisField 2 n))),
      Concl166S ↥(adjointGroup Tag.E8 (GaloisField 2 n)) p q B' x' J := by
  classical
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Kf := GaloisField 2 n
  have hKcard : Nat.card Kf = 2 ^ n := GaloisField.card 2 n (by omega)
  have hn1 : 1 ≤ n := by omega
  have hN : 2 ^ n - 1 ≠ 1 := by
    have h4 : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  obtain ⟨q, hq, hqdvd⟩ := Nat.exists_prime_and_dvd hN
  have hq2 : q ≠ 2 := by
    rintro rfl
    obtain ⟨k, hk⟩ := hqdvd
    have h1 : 2 ^ n = 2 * 2 ^ (n - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel hn1]
    have hpos : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    omega
  have hqcard : q ∣ Nat.card Kfˣ := by
    rw [Nat.card_units, hKcard]
    exact hqdvd
  letI : Fact q.Prime := ⟨hq⟩
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' q hqcard
  obtain ⟨B', hB'⟩ := exists_concl166S_of_toral_E8 n p q hn hp hp2 hpdvd hq hq2 hqdvd hζ hD7
  exact ⟨q, B', ⟨rootDiagUnit Tag.E8 (e8NodeZeroToral ζ),
      rootDiagUnit_e8NodeZeroToral_mem_adjointGroup ζ⟩,
    (subsystemGroup Tag.E8 (GaloisField 2 n) {i : Fin Tag.E8.rank | i ≠ 0}).subgroupOf
      (adjointGroup Tag.E8 (GaloisField 2 n)), hB'⟩

theorem i166On_famE8_of_transport
    (htr : ∀ {K R : Type} [Group K] [Finite K] [Group R] [Finite R], (K ≃* R) → ∀ {p : ℕ},
      (∃ (q : ℕ) (B' : Subgroup R) (x' : R) (J : Subgroup R), Concl166S R p q B' x' J) →
      ∃ (q : ℕ) (B' : Subgroup K) (x' : K) (J : Subgroup K), Concl166S K p q B' x' J)
    (hD7 : ∀ n : ℕ, 2 ≤ n → LayerData166At ⟨.D, 7, n⟩) :
    I166On i166FamE8 := by
  intro K _ _ lab p hlab hfam hp hp2 _ _ _
  obtain ⟨htag, hn2, hpdvd⟩ := hfam
  have hZ : Subgroup.center K = ⊥ :=
    rk2_center_eq_bot_of_large (lab := lab) hlab
      (Or.inr (Or.inr (Or.inr (Or.inr htag)))) hn2
  obtain ⟨e⟩ := exists_mulEquiv_adjointGroup_of_isLabel_E8 hlab htag hZ
  obtain ⟨q, B', x', J, hc⟩ :=
    exists_concl166S_adjointGroup_E8 lab.n p hn2 hp hp2 hpdvd (hD7 lab.n hn2)
  exact htr e ⟨q, B', x', J, hc⟩

end CFSG.LocalAnalysis.GLTheoremA.Y10F
