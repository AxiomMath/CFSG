module

public import CFSG.GH74.GLS.C3.Layer1.Th2SigStmt
public import CFSG.GH74.GLS.TwoThin.Equivariance
public import CFSG.Foundations.HigherElementaryThompson

public section

namespace CFSG.GH74.GLS.Th2Sig8

open Subgroup

variable {G : Type} [Group G]

theorem card_eq_two_pow_pRank [Finite G] {B : Subgroup G} (hB : CFSG.IsElementaryAbelian 2 ↥B) :
    Nat.card ↥B = 2 ^ CFSG.pRank 2 ↥B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hB
  obtain ⟨n, hn⟩ := (CFSG.IsElementaryAbelian.isPGroup 2 ↥B).exists_card_eq
  rw [CFSG.pRank_eq_of_card_eq_pow one_lt_two hn]
  exact hn

theorem two_pow_le_card [Finite G] {B : Subgroup G} (hB : CFSG.IsElementaryAbelian 2 ↥B) {n : ℕ}
    (hn : n ≤ CFSG.pRank 2 ↥B) : 2 ^ n ≤ Nat.card ↥B := by
  rw [card_eq_two_pow_pRank hB]
  exact Nat.pow_le_pow_right (by norm_num) hn

theorem isElementaryAbelian_of_le {A B : Subgroup G} (hA : CFSG.IsElementaryAbelian 2 ↥A)
    (hBA : B ≤ A) : CFSG.IsElementaryAbelian 2 ↥B := by
  rw [CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian] at hA ⊢
  exact ⟨⟨⟨fun x y => Subtype.ext (congrArg (fun z : A => (z : G))
    (hA.1.is_comm.comm (⟨x, hBA x.2⟩ : A) ⟨y, hBA y.2⟩))⟩⟩, fun x hx => hA.2 x (hBA hx)⟩

theorem mul_comm_of_isElementaryAbelian {A : Subgroup G} (hA : CFSG.IsElementaryAbelian 2 ↥A)
    {a b : G} (ha : a ∈ A) (hb : b ∈ A) : a * b = b * a :=
  congrArg Subtype.val (hA.toIsMulCommutative.is_comm.comm (⟨a, ha⟩ : A) ⟨b, hb⟩)

theorem exists_ne_one [Finite G] {D : Subgroup G} (hD : CFSG.IsElementaryAbelian 2 ↥D)
    (h : 1 ≤ CFSG.pRank 2 ↥D) : ∃ d ∈ D, d ≠ 1 := by
  by_contra hcon
  have hbot : D = ⊥ :=
    (Subgroup.eq_bot_iff_forall D).mpr fun d hd => by_contra fun hd1 => hcon ⟨d, hd, hd1⟩
  have h2 := two_pow_le_card hD h
  rw [hbot, Subgroup.card_bot] at h2
  omega

theorem isE_of_card [Finite G] {X B S : Subgroup G} (hB : CFSG.IsElementaryAbelian 2 ↥B)
    (hSB : S ≤ B) (hSX : S ≤ X) {k : ℕ} (hk : Nat.card ↥S = 2 ^ k) : IsE k X S := by
  have hS := isElementaryAbelian_of_le hB hSB
  have := hS
  exact ⟨hSX, hS, (CFSG.pRank_eq_of_card_eq_pow one_lt_two hk).ge⟩

theorem AG_le_pPrimeCoreOf {D : Subgroup G} {d : G} (hd : d ∈ D) (hd1 : d ≠ 1) :
    AG D ≤ pPrimeCoreOf 2 (centralizer ({d} : Set G)) :=
  iInf₂_le d ⟨hd, hd1⟩

theorem le_AG {X D : Subgroup G}
    (h : ∀ d ∈ D, d ≠ 1 → X ≤ pPrimeCoreOf 2 (centralizer ({d} : Set G))) : X ≤ AG D :=
  le_iInf₂ fun d hd => h d hd.1 hd.2

theorem coprime_card_AG [Finite G] {D : Subgroup G} {d : G} (hd : d ∈ D) (hd1 : d ≠ 1) :
    Nat.Coprime 2 (Nat.card ↥(AG D)) := by
  have hodd := TwoThin.card_pPrimeCoreOf_odd (centralizer ({d} : Set G))
  have hdvd : Nat.card ↥(AG D) ∣ Nat.card ↥(pPrimeCoreOf 2 (centralizer ({d} : Set G))) :=
    Subgroup.card_dvd_of_le (AG_le_pPrimeCoreOf hd hd1)
  exact Nat.coprime_two_left.mpr (hodd.of_dvd_nat hdvd)

theorem mem_normalizer_AG {A D : Subgroup G} (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hDA : D ≤ A)
    {q : G} (hq : q ∈ A) : q ∈ normalizer (AG D : Set G) := by
  have key : ∀ d ∈ D, ∀ x : G, x ∈ pPrimeCoreOf 2 (centralizer ({d} : Set G)) ↔
      q * x * q⁻¹ ∈ pPrimeCoreOf 2 (centralizer ({d} : Set G)) := by
    intro d hd x
    have hqC : q ∈ centralizer ({d} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hA y (hDA hd) q hq
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

theorem thetaK_le_of_le (k : ℕ) {A B : Subgroup G} (hBA : B ≤ A) : thetaK k B ≤ thetaK k A :=
  iSup₂_le fun D hD => le_iSup₂_of_le D ⟨hD.1.trans hBA, hD.2.1, hD.2.2⟩ le_rfl

theorem AG_le_thetaK [Finite G] {k : ℕ} (hk : 1 ≤ k) {A B D : Subgroup G}
    (hA : CFSG.IsElementaryAbelian 2 ↥A) (hbal : IsKBal k A) (hB : IsE (k + 1) A B)
    (hD : IsE k A D) : AG D ≤ thetaK k B := by
  obtain ⟨hBA, hBe, hBr⟩ := hB
  obtain ⟨d, hdD, hd1⟩ := exists_ne_one hD.2.1 (hk.trans hD.2.2)
  have hcop : Nat.Coprime 2 (Nat.card ↥(AG D)) := coprime_card_AG hdD hd1
  have hnorm : B ≤ normalizer (AG D : Set G) := fun q hq =>
    mem_normalizer_AG (fun a ha b hb => mul_comm_of_isElementaryAbelian hA ha hb) hD.1 (hBA hq)
  have hBe' : CFSG.Open.IsElemAbelian 2 B :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 B).mp hBe
  have hlarge : 2 ^ (k + 1) ≤ Nat.card ↥B := two_pow_le_card hBe hBr
  have hgen := CFSG.SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation 2 k
    Nat.prime_two B (AG D) hBe' hlarge hnorm hcop
  rw [← hgen]
  refine iSup₂_le fun S hS => ?_
  obtain ⟨hSB, hScard⟩ := hS
  have hSE : IsE k B S := isE_of_card hBe hSB hSB hScard
  refine le_trans ?_ (le_iSup₂_of_le S hSE le_rfl)
  refine le_AG fun s hs hs1 => ?_
  exact (inf_le_inf_left (AG D)
    (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hs))).trans
    (hbal D hD s (hBA (hSB hs)) hs1)

end CFSG.GH74.GLS.Th2Sig8

namespace CFSG.GH74.GLS

theorem b_ig_21_8 : B_IG_21_8 := by
  intro G _ _ k hk A B hA hbal hB
  refine le_antisymm (Th2Sig8.thetaK_le_of_le k hB.1) (iSup₂_le fun D hD => ?_)
  exact Th2Sig8.AG_le_thetaK hk hA.2.1 hbal hB hD

end CFSG.GH74.GLS
