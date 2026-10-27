module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614B1Lift
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.L62Situation
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L63Transport

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614DOG

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K2 (Bar barMk)

theorem l62_hasNormalPComplement_centralizer_of_rank (hT : T29.GL83I291Three)
    (hNC : T29.NoncyclicCentreRank) (hQ : KFactThreeComponentsQRank) {X : Type} [Group X]
    [Finite X] {S : Sylow 3 X} {x z : X} (h : L62Data X S x z)
    (hnc : ¬ HasPrimeConstraint (G := X) 3) {w : X} (hw : orderOf w = 3)
    (hrk : CFSG.Open.pRank 3 (centralizer ({w} : Set X)) = 2) :
    CFSG.HasNormalPComplement 3 ↥(centralizer ({w} : Set X)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S', x', z', hB⟩ := l62Data_toBar h
  obtain ⟨L, hL⟩ :=
    Stroth.Bal3.exists_isComponentOf_of_not_hasPrimeConstraint Nat.prime_three hnc
  have huniq := P614B1.l62_unique_component hNC hQ h hB hL
  have hO : ¬ 3 ∣ Nat.card (primeComplementCore (G := X) 3) := K2.qs_not_dvd_core
  have hw1 : barMk X w ≠ 1 := by
    intro h1
    have hk : w ∈ primeComplementCore (G := X) 3 := (QuotientGroup.eq_one_iff w).mp h1
    have := Subgroup.orderOf_dvd_natCard _ hk
    rw [hw] at this
    exact hO this
  have hwbar : orderOf (barMk X w) = 3 := by
    have hw3 : w ^ 3 = 1 := hw ▸ pow_orderOf_eq_one w
    exact orderOf_eq_prime (by rw [← map_pow, hw3, map_one]) hw1
  have hCmap : centralizer ({barMk X w} : Set (Bar X)) =
      (centralizer ({w} : Set X)).map (barMk X) :=
    K2.centralizer_map_quotient _ hO hw
  have hker : ¬ 3 ∣ Nat.card ↥(centralizer ({w} : Set X) ⊓ (barMk X).ker) := by
    intro hdvd
    have h1 : Nat.card ↥(centralizer ({w} : Set X) ⊓ (barMk X).ker) ∣
        Nat.card ↥(primeComplementCore (G := X) 3) :=
      Subgroup.card_dvd_of_le (inf_le_right.trans K2.qs_ker.le)
    exact hO (hdvd.trans h1)
  have hcent : CFSG.Open.pRank 3 (centralizer ({barMk X w} : Set (Bar X))) = 2 := by
    rw [hCmap, K2.pRank_map_eq_of_coprime_ker (barMk X) Nat.prime_three hker, hrk]
  have hrank : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (Bar X)) :=
    hB.rank.ge.trans (pRank_mono 3 (by norm_num) le_top)
  obtain ⟨-, -, -, hconc⟩ :=
    hT (Bar X) hB.catalog hB.core L hL huniq hrank (barMk X w) hwbar hcent
  rcases hconc with ⟨-, -, -, hnpc, -⟩ | hb
  · rw [hCmap] at hnpc
    exact P614B1.hasNormalPComplement_of_map (barMk X) hker hnpc
  · exfalso
    have hsetup : T29.T29Setup (Bar X) L (barMk X w) :=
      ⟨hB.catalog, hB.core, hL, huniq, hrank, hwbar, hcent⟩
    obtain ⟨e', -, -⟩ := id hb
    have hZ : center ↥L = ⊥ := T29.k3_center_eq_bot_of_psl227 hL.2.2.1 e'
    have hC : centralizer (L : Set (Bar X)) = ⊥ := hsetup.centralizer_eq_bot hZ
    haveI : L.Normal := hsetup.normal
    obtain ⟨N, hN, hNi⟩ := K2.exists_index_three_normal hsetup.normal ⟨e'⟩ hC
      (T29.index_eq_of_fieldAut_L227 hC hb)
    exact hB.no_normal_three N hN hNi

theorem eq_one_of_conj_eq_inv_of_isPGroup {Y : Type*} [Group Y] (hY : IsPGroup 3 Y) {a b : Y}
    (hb3 : b ^ 3 = 1) (hab : a * b * a⁻¹ = b⁻¹) : b = 1 := by
  obtain ⟨k, hk⟩ := hY a
  have ha2 : a ^ 2 * b = b * a ^ 2 := by
    have h1 : a * b⁻¹ * a⁻¹ = b := by
      rw [show a * b⁻¹ * a⁻¹ = (a * b * a⁻¹)⁻¹ by group, hab, inv_inv]
    rw [sq]
    calc a * a * b = a * (a * b * a⁻¹) * a := by group
      _ = a * b⁻¹ * a := by rw [hab]
      _ = (a * b⁻¹ * a⁻¹) * (a * a) := by group
      _ = b * (a * a) := by rw [h1]
  have hodd : Odd (3 ^ k) := Odd.pow (by decide)
  obtain ⟨m, hm⟩ := hodd
  have ha : a = (a ^ 2) ^ (m + 1) := by
    rw [← pow_mul, show 2 * (m + 1) = 3 ^ k + 1 by omega, pow_succ, hk, one_mul]
  have hcomm : a * b = b * a := by
    rw [ha]
    exact ((Commute.pow_left (show Commute (a ^ 2) b from ha2) (m + 1)))
  have hbb : b = b⁻¹ := by
    rw [← hab, hcomm, mul_inv_cancel_right]
  have hb2 : b ^ 2 = 1 := by
    rw [sq]
    nth_rewrite 2 [hbb]
    exact mul_inv_cancel b
  calc b = b ^ 3 * (b ^ 2)⁻¹ := by group
    _ = 1 := by rw [hb3, hb2]; group

theorem eq_one_of_conj_eq_inv {C : Type*} [Group C] (h : CFSG.HasNormalPComplement 3 C)
    {t y : C} (hy3 : y ^ 3 = 1) (hty : t * y * t⁻¹ = y⁻¹) : y = 1 := by
  obtain ⟨N, hN, hcop, hq⟩ := h
  have hbar : (y : C ⧸ N) = 1 := by
    refine eq_one_of_conj_eq_inv_of_isPGroup hq (a := (t : C ⧸ N)) ?_ ?_
    · rw [← QuotientGroup.mk_pow, hy3, QuotientGroup.mk_one]
    · rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hty,
        QuotientGroup.mk_inv]
  have hyN : y ∈ N := (QuotientGroup.eq_one_iff y).mp hbar
  have h1 : orderOf (⟨y, hyN⟩ : N) ∣ 3 := orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa))
  have h2 : orderOf (⟨y, hyN⟩ : N) ∣ Nat.card N := orderOf_dvd_natCard _
  have h3 : orderOf (⟨y, hyN⟩ : N) = 1 := Nat.eq_one_of_dvd_coprimes hcop.symm h2 h1
  have := congrArg Subtype.val (orderOf_eq_one_iff.mp h3)
  simpa using this

variable {G : Type} [Group G] [Finite G]

theorem map_subtype_centralizer {M : Subgroup G} (w : ↥M) :
    (centralizer ({w} : Set ↥M)).map M.subtype = M ⊓ centralizer ({(w : G)} : Set G) := by
  ext g
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact mem_inf.mpr ⟨c.2, mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hc))⟩
  · intro hg
    obtain ⟨hgM, hgw⟩ := mem_inf.mp hg
    exact ⟨⟨g, hgM⟩, mem_centralizer_singleton_iff.mpr
      (Subtype.ext (mem_centralizer_singleton_iff.mp hgw)), rfl⟩

theorem centralizer_le_of_inverted (hT : T29.GL83I291Three) (hNC : T29.NoncyclicCentreRank)
    (hQ : KFactThreeComponentsQRank) {P : Sylow 3 G} {M : Subgroup G} {x z : G}
    (hsit : Sit P M x z) (hnα : ¬ HasPrimeConstraint (G := M) 3) {w : G} (hwM : w ∈ M)
    (hw : orderOf w = 3) (h2 : 2 ≤ CFSG.Open.pRank 3 (M ⊓ centralizer ({w} : Set G)))
    {t y : G} (htM : t ∈ M) (htw : t * w = w * t) (hyM : y ∈ M) (hyw : y * w = w * y)
    (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1) (hty : t * y * t⁻¹ = y⁻¹) :
    centralizer ({w} : Set G) ≤ M := by
  have hw3 : w ^ 3 = 1 := hw ▸ pow_orderOf_eq_one w
  have hw1 : w ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hw
    omega
  by_cases h3 : 3 ≤ CFSG.Open.pRank 3 (M ⊓ centralizer ({w} : Set G))
  · by_contra hCM
    exact hsit.situation.largeObstruction_empty w
      ⟨hwM, hw1, hw3, h3.trans (pRank_mono 3 Nat.prime_three.one_lt inf_le_right), hCM⟩
  · exfalso
    have hrk : CFSG.Open.pRank 3 (M ⊓ centralizer ({w} : Set G)) = 2 := by omega
    obtain ⟨S, x', z', hD, -, -, -⟩ := l62Data_of_situation hsit.setting hsit.u0
      hsit.situation hsit.point hsit.central
    set w' : ↥M := ⟨w, hwM⟩ with hw'def
    have hw' : orderOf w' = 3 := by rw [hw'def, Subgroup.orderOf_mk, hw]
    have hrk' : CFSG.Open.pRank 3 (centralizer ({w'} : Set ↥M)) = 2 := by
      rw [← CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.pRank_map_subtype (by norm_num),
        map_subtype_centralizer, hrk]
    have hnpc := l62_hasNormalPComplement_centralizer_of_rank hT hNC hQ hD hnα hw' hrk'
    have htC : (⟨t, htM⟩ : ↥M) ∈ centralizer ({w'} : Set ↥M) :=
      mem_centralizer_singleton_iff.mpr (Subtype.ext htw)
    have hyC : (⟨y, hyM⟩ : ↥M) ∈ centralizer ({w'} : Set ↥M) :=
      mem_centralizer_singleton_iff.mpr (Subtype.ext hyw)
    have h1 := eq_one_of_conj_eq_inv hnpc (t := ⟨_, htC⟩) (y := ⟨_, hyC⟩)
      (Subtype.ext (Subtype.ext (by simpa using hy3)))
      (Subtype.ext (Subtype.ext (by simpa using hty)))
    exact hy1 (by simpa using congrArg (fun c : ↥(centralizer ({w'} : Set ↥M)) =>
      ((c : ↥M) : G)) h1)

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614DOG
