module

public import CFSG.GH74.GLS.TwoThin.Equivariance
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.PrimeTwo
public import CFSG.Foundations.HigherElementaryThompson
public import CFSG.GH74.GLS.C3.Layer1.Th2Defs

public section

namespace CFSG.GH74.GLS.Th2Sig6

open Subgroup

variable {G : Type} [Group G]

theorem card_eq_two_pow_pRank [Finite G] {B : Subgroup G} (hB : CFSG.IsElementaryAbelian 2 ↥B) :
    Nat.card ↥B = 2 ^ CFSG.pRank 2 ↥B := by
  obtain ⟨n, hn⟩ := (CFSG.IsElementaryAbelian.isPGroup 2 ↥B).exists_card_eq
  rw [CFSG.pRank_eq_of_card_eq_pow one_lt_two hn]
  exact hn

theorem two_pow_le_card [Finite G] {B : Subgroup G} (hB : CFSG.IsElementaryAbelian 2 ↥B) {n : ℕ}
    (hn : n ≤ CFSG.pRank 2 ↥B) : 2 ^ n ≤ Nat.card ↥B := by
  rw [card_eq_two_pow_pRank hB]
  exact Nat.pow_le_pow_right (by norm_num) hn

theorem mul_comm_of_isElementaryAbelian {A : Subgroup G} (hA : CFSG.IsElementaryAbelian 2 ↥A)
    {a b : G} (ha : a ∈ A) (hb : b ∈ A) : a * b = b * a :=
  congrArg Subtype.val (hA.toIsMulCommutative.is_comm.comm (⟨a, ha⟩ : A) ⟨b, hb⟩)

theorem isElementaryAbelian_of_le {A B : Subgroup G} (hA : CFSG.IsElementaryAbelian 2 ↥A)
    (hBA : B ≤ A) : CFSG.IsElementaryAbelian 2 ↥B := by
  rw [CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian] at hA ⊢
  exact ⟨⟨⟨fun x y => Subtype.ext (show (x : G) * y = y * x from congrArg Subtype.val
    (hA.1.is_comm.comm (⟨x, hBA x.2⟩ : A) ⟨y, hBA y.2⟩))⟩⟩, fun x hx => hA.2 x (hBA hx)⟩

theorem isE_of_card [Finite G] {A S : Subgroup G} (hA : CFSG.IsElementaryAbelian 2 ↥A)
    (hSA : S ≤ A) {k : ℕ} (hk : Nat.card ↥S = 2 ^ k) : IsE k A S := by
  have hS := isElementaryAbelian_of_le hA hSA
  exact ⟨hSA, hS, (CFSG.pRank_eq_of_card_eq_pow one_lt_two hk).ge⟩

theorem exists_sub_card [Finite G] {D : Subgroup G} (hD : CFSG.IsElementaryAbelian 2 ↥D) {k : ℕ}
    (hk : k ≤ CFSG.pRank 2 ↥D) : ∃ S : Subgroup G, S ≤ D ∧ Nat.card ↥S = 2 ^ k := by
  have hdvd : 2 ^ k ∣ Nat.card ↥D := by
    rw [card_eq_two_pow_pRank hD]
    exact pow_dvd_pow 2 hk
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime 2 hdvd
  refine ⟨K.map D.subtype, Subgroup.map_subtype_le K, ?_⟩
  rw [Subgroup.card_map_of_injective D.subtype_injective, hK]

theorem exists_ne_one_of_card [Finite G] {S : Subgroup G} {k : ℕ} (hk : 1 ≤ k)
    (hS : Nat.card ↥S = 2 ^ k) : ∃ s ∈ S, s ≠ 1 := by
  have hnt : S ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hS
    have h2 : 1 < 2 ^ k := Nat.one_lt_two_pow (by omega)
    omega
  obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hnt
  exact ⟨a, a.2, fun h => ha1 (Subtype.ext h)⟩

theorem AG_le_pPrimeCoreOf {D : Subgroup G} {d : G} (hd : d ∈ D) (hd1 : d ≠ 1) :
    AG D ≤ pPrimeCoreOf 2 (centralizer ({d} : Set G)) :=
  iInf₂_le d ⟨hd, hd1⟩

theorem le_AG {X D : Subgroup G}
    (h : ∀ d ∈ D, d ≠ 1 → X ≤ pPrimeCoreOf 2 (centralizer ({d} : Set G))) : X ≤ AG D :=
  le_iInf₂ fun d hd => h d hd.1 hd.2

theorem AG_anti {S D : Subgroup G} (h : S ≤ D) : AG D ≤ AG S :=
  le_AG fun _ hd hd1 => AG_le_pPrimeCoreOf (h hd) hd1

theorem pPrimeCoreOf_le {K : Subgroup G} : pPrimeCoreOf 2 K ≤ K := by
  rintro _ ⟨c, -, rfl⟩
  exact c.2

theorem AG_le_centralizer {S : Subgroup G} : AG S ≤ centralizer (S : Set G) := by
  intro g hg
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  by_cases hs1 : s = 1
  · rw [hs1, one_mul, mul_one]
  · exact (Subgroup.mem_centralizer_singleton_iff.mp
      (pPrimeCoreOf_le (AG_le_pPrimeCoreOf hs hs1 hg))).symm

theorem coprime_card_AG [Finite G] {D : Subgroup G} {d : G} (hd : d ∈ D) (hd1 : d ≠ 1) :
    Nat.Coprime 2 (Nat.card ↥(AG D)) := by
  have hodd := TwoThin.card_pPrimeCoreOf_odd (centralizer ({d} : Set G))
  have hdvd : Nat.card ↥(AG D) ∣ Nat.card ↥(pPrimeCoreOf 2 (centralizer ({d} : Set G))) :=
    Subgroup.card_dvd_of_le (AG_le_pPrimeCoreOf hd hd1)
  exact Nat.coprime_two_left.mpr (hodd.of_dvd_nat hdvd)

theorem mem_normalizer_AG {D : Subgroup G} {q : G} (hq : ∀ d ∈ D, q * d = d * q) :
    q ∈ normalizer (AG D : Set G) := by
  have key : ∀ d ∈ D, ∀ x : G, x ∈ pPrimeCoreOf 2 (centralizer ({d} : Set G)) ↔
      q * x * q⁻¹ ∈ pPrimeCoreOf 2 (centralizer ({d} : Set G)) := by
    intro d hd x
    have hqC : q ∈ centralizer ({d} : Set G) := Subgroup.mem_centralizer_singleton_iff.mpr (hq d hd)
    exact Subgroup.mem_normalizer_iff.mp
      (TwoThin.mem_normalizer_pPrimeCoreOf (Subgroup.le_normalizer hqC)) x
  rw [Subgroup.mem_normalizer_iff]
  intro x
  simp only [AG, Subgroup.mem_iInf]
  constructor
  · intro hx d hd
    exact (key d hd.1 x).mp (hx d hd)
  · intro hx d hd
    exact (key d hd.1 x).mpr (hx d hd)

theorem AG_inf_centralizer_le {k : ℕ} {A S S' : Subgroup G} (hbal : IsKBal k A) (hS : IsE k A S)
    (hS' : S' ≤ A) : AG S ⊓ centralizer (S' : Set G) ≤ AG S' := by
  refine le_AG fun s hs hs1 => ?_
  exact (inf_le_inf_left (AG S) (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hs))).trans
    (hbal S hS s (hS' hs) hs1)

theorem hypB_two_of_coprime [Finite G] (H : Subgroup G) (h : Nat.Coprime 2 (Nat.card ↥H)) :
    CFSG.Open.signalizerMcBrideHypothesisB 2 H := by
  refine ⟨Nat.prime_two, h, fun K L hKH hLK _ hS hnc => ?_⟩
  exfalso
  have hdvd : Nat.card (↥K ⧸ L.subgroupOf K) ∣ Nat.card ↥H :=
    (Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_dvd_of_le hKH)
  have hodd : Odd (Nat.card (↥K ⧸ L.subgroupOf K)) :=
    Nat.coprime_two_left.mp (Nat.Coprime.coprime_dvd_right hdvd h)
  have hsolv : Group.IsSolvable (↥K ⧸ L.subgroupOf K) := CFSG.Milestones.odd_order_solvable hodd
  obtain ⟨a, b, hab⟩ := hnc
  exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr hsolv a b)

theorem iSup_Ek_eq_thetaK [Finite G] {k : ℕ} {A : Subgroup G} (hA : CFSG.IsElementaryAbelian 2 ↥A) :
    (⨆ (S : Subgroup G) (_ : S ∈ CFSG.Open.signalizerFunctorEk 2 k A), AG S) = thetaK k A := by
  apply le_antisymm
  · refine iSup₂_le fun S hS => ?_
    exact le_iSup₂_of_le S (isE_of_card hA hS.1 hS.2) le_rfl
  · refine iSup₂_le fun D hD => ?_
    obtain ⟨S, hSD, hScard⟩ := exists_sub_card hD.2.1 hD.2.2
    exact (AG_anti hSD).trans (le_iSup₂_of_le S ⟨hSD.trans hD.1, hScard⟩ le_rfl)

end CFSG.GH74.GLS.Th2Sig6

namespace CFSG.GH74.GLS

open Subgroup

theorem b_ig_21_6_int :
    ∀ (G : Type) [Group G] [Finite G] (k : ℕ), 1 ≤ k → ∀ A : Subgroup G,
      IsE (k + 2) ⊤ A → IsKBal k A → Odd (Nat.card ↥(thetaK k A)) := by
  intro G _ _ k hk A hAE hbal
  obtain ⟨-, hAe, hAr⟩ := hAE
  have hAe' : CFSG.Open.IsElemAbelian 2 A :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 A).mp hAe
  have hAcard : 2 ^ (k + 2) ≤ Nat.card ↥A := Th2Sig6.two_pow_le_card hAe hAr
  have hcop : ∀ S ∈ CFSG.Open.signalizerFunctorEk 2 k A, Nat.Coprime 2 (Nat.card ↥(AG S)) := by
    intro S hS
    obtain ⟨s, hsS, hs1⟩ := Th2Sig6.exists_ne_one_of_card hk hS.2
    exact Th2Sig6.coprime_card_AG hsS hs1
  have h := CFSG.SignalizerFunctorTheorem.signalizer_functor_theorem_two G k hk A hAe' hAcard AG
    (fun S _ => Th2Sig6.AG_le_centralizer) hcop
    (fun S hS q hq => Th2Sig6.mem_normalizer_AG fun d hd =>
      Th2Sig6.mul_comm_of_isElementaryAbelian hAe hq (hS.1 hd))
    (fun S hS S' hS' => Th2Sig6.AG_inf_centralizer_le hbal (Th2Sig6.isE_of_card hAe hS.1 hS.2) hS'.1)
    (fun S hS => Th2Sig6.hypB_two_of_coprime _ (hcop S hS))
  obtain ⟨⟨hcopW, -⟩, -, -, -⟩ := h
  rw [Th2Sig6.iSup_Ek_eq_thetaK hAe] at hcopW
  exact Nat.coprime_two_left.mp hcopW

end CFSG.GH74.GLS
