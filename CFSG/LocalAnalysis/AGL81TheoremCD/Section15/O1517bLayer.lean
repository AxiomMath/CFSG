module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.O1517bDefs

import CFSG.GroupTheory.LocalCores.Layer
import CFSG.LocalAnalysis.RankThreeTheoremC.ObstructionElements
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2T_Two
import CFSG.Quasithin.Vol2.Ch11SKFIto
import CFSG.GroupTheory.PGroup.ElemAbelianSq
import CFSG.GH74.GLS.C3.Layer2.FusionTools
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section15

open Subgroup

variable {X : Type} [Group X] [Finite X]

private lemma eq_zpowers_of_card_eq_three {T : Subgroup X} {z : X}
    (hzT : z ∈ T) (hzc : ∀ y ∈ T, z * y = y * z) (hzord : orderOf z = 3)
    (hrk : CFSG.Open.pRank 3 T ≤ 1) {B : Subgroup X} (hBT : B ≤ T)
    (hBcard : Nat.card B = 3) :
    B = Subgroup.zpowers z := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hT₁card : Nat.card (Subgroup.zpowers z) = 3 := by
    rw [Nat.card_zpowers, hzord]
  have hB3 : 3 ∣ Nat.card B := by rw [hBcard]
  obtain ⟨u₀, hu₀⟩ := exists_prime_orderOf_dvd_card' (G := ↥B) 3 hB3
  let u : X := (u₀ : B)
  have huB : u ∈ B := u₀.2
  have huord : orderOf u = 3 := by
    rw [Subgroup.orderOf_coe]
    exact hu₀
  have hBeq : B = Subgroup.zpowers u := by
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr huB) ?_).symm
    rw [hBcard, Nat.card_zpowers, huord]
  have hcomm : ∀ w ∈ Subgroup.zpowers z, w * u = u * w := by
    intro w hw
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hw
    rw [← hn]
    exact (Commute.zpow_left (hzc u (hBT huB)) n).eq
  by_cases huT₁ : u ∈ Subgroup.zpowers z
  · exact hBeq.trans (Subgroup.eq_of_le_of_card_ge
      (Subgroup.zpowers_le.mpr huT₁)
      (by rw [hT₁card, Nat.card_zpowers, huord]))
  · have hE9 := CFSG.GroupTheory.isElemAbelian_sup_zpowers_of_commute
      (r := 3) hT₁card huord huT₁ hcomm
    have hle : Subgroup.zpowers z ⊔ Subgroup.zpowers u ≤ T :=
      sup_le (Subgroup.zpowers_le.mpr hzT) (Subgroup.zpowers_le.mpr (hBT huB))
    have h2 : 2 ≤ CFSG.Open.pRank 3 T :=
      CFSG.SectionRank.le_pRank (p := 3) (k := 2) (by norm_num) hle hE9.1 hE9.2
    omega

private lemma eq_of_card_three_of_isSylowOf {E T A : Subgroup X}
    (hTE : CFSG.ABGLocalTools.IsSylowOf 3 T E)
    (huniq : ∀ B : Subgroup X, B ≤ T → Nat.card B = 3 → B = A)
    (hAn : A.Normal) (hAcard : Nat.card A = 3) {B : Subgroup X} (hBE : B ≤ E)
    (hBcard : Nat.card B = 3) :
    B = A := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hBp : IsPGroup 3 B := IsPGroup.of_card (n := 1) (by rw [hBcard, pow_one])
  obtain ⟨g, -, hg⟩ :=
    CFSG.GH74.GLS.C3.Layer2.exists_mem_conj_le_of_isSylowOf hTE hBE hBp
  have hBA : B ≤ A := by
    intro b hb
    by_cases hb1 : b = 1
    · rw [hb1]
      exact A.one_mem
    have hbo : orderOf b = 3 := by
      have hdiv : orderOf b ∣ 3 := by
        rw [← Nat.card_zpowers]
        exact (Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hb)).trans
          (by rw [hBcard])
      rcases (Nat.dvd_prime Nat.prime_three).mp hdiv with h1 | h3
      · exact absurd (orderOf_eq_one_iff.mp h1) hb1
      · exact h3
    have hco : orderOf (g⁻¹ * b * g) = 3 := by
      rw [← MulAut.conj_inv_apply, MulEquiv.orderOf_eq, hbo]
    have hcT : g⁻¹ * b * g ∈ T := hg b hb
    have hcA : g⁻¹ * b * g ∈ A := by
      rw [← huniq (Subgroup.zpowers (g⁻¹ * b * g)) (Subgroup.zpowers_le.mpr hcT)
        (by rw [Nat.card_zpowers, hco])]
      exact Subgroup.mem_zpowers _
    rw [show b = g * (g⁻¹ * b * g) * g⁻¹ by group]
    exact hAn.conj_mem _ hcA g
  exact Subgroup.eq_of_le_of_card_ge hBA (by rw [hBcard, hAcard])

theorem O1517bRed.le_centralizer_A {X : Type} [Group X] [Finite X] {p : ℕ}
    {P A Y : Subgroup X} (h : O1517bRed X p P A Y) {L : Subgroup X}
    (hL : CFSG.IsComponent L) :
    L ≤ Subgroup.centralizer (A : Set X) := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hsolv : Group.IsSolvable ↥A := by
    haveI : IsCyclic ↥A := isCyclic_of_prime_card h.card_A
    exact Group.isSolvable_of_comm fun a b => (IsCyclic.commGroup).mul_comm a b
  have hcomm := (CFSG.LocalCores.component_solvable_centralizer hsolv
    h.normal_A.isSubnormal).1 L hL
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm

private lemma le_normalizer_layer :
    (⊤ : Subgroup X) ≤ Subgroup.normalizer ((CFSG.layer X : Subgroup X) : Set X) := by
  haveI : (CFSG.layer X).Characteristic := CFSG.LocalCores.layer_characteristic
  haveI : (CFSG.layer X).Normal := Subgroup.normal_of_characteristic (H := CFSG.layer X)
  rw [Subgroup.normalizer_eq_top]

private lemma isSylowOf_inf_layer {p : ℕ} {P A Y : Subgroup X}
    (h : O1517bRed X p P A Y) :
    CFSG.ABGLocalTools.IsSylowOf 3 (P ⊓ CFSG.layer X) (CFSG.layer X) := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have h := h.sylow.inf_of_le_normalizer (p := 3) (P := P) (K := ⊤)
    (N := CFSG.layer X) le_top le_normalizer_layer
  simpa using h

private lemma ne_bot_inf_layer {p : ℕ} {P A Y : Subgroup X}
    (h : O1517bRed X p P A Y) {L : Subgroup X} (hL : CFSG.IsComponent L) :
    P ⊓ CFSG.layer X ≠ ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have h3L : 3 ∣ Nat.card L :=
    CFSG.LocalAnalysis.RankThreeTheoremC.thc_dvd_card Nat.prime_three h.core hL
  have h3E : 3 ∣ Nat.card (CFSG.layer X) :=
    h3L.trans (Subgroup.card_dvd_of_le (CFSG.LocalCores.component_le_layer hL))
  have hTcard : Nat.card ((P ⊓ CFSG.layer X : Subgroup X)) =
      3 ^ (Nat.card (CFSG.layer X)).factorization 3 := (isSylowOf_inf_layer h).card_eq
  have hfact : 0 < (Nat.card (CFSG.layer X)).factorization 3 :=
    Nat.prime_three.factorization_pos_of_dvd (Nat.card_pos.ne') h3E
  intro hbot
  have hlt : 1 < Nat.card ((P ⊓ CFSG.layer X : Subgroup X)) := by
    rw [hTcard]
    exact Nat.one_lt_pow hfact.ne' (by norm_num)
  rw [hbot, Subgroup.card_bot] at hlt
  omega

private lemma false_of_le_inf_layer {p : ℕ} {P A Y : Subgroup X}
    (h : O1517bRed X p P A Y) {L : Subgroup X} (hL : CFSG.IsComponent L)
    {z : X} (hzT : z ∈ P ⊓ CFSG.layer X)
    (hzc : ∀ y ∈ P ⊓ CFSG.layer X, z * y = y * z) (hzord : orderOf z = 3)
    (hrk : CFSG.Open.pRank 3 (P ⊓ CFSG.layer X) ≤ 1)
    (hAT : A ≤ P ⊓ CFSG.layer X) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hTsyl : CFSG.ABGLocalTools.IsSylowOf 3 (P ⊓ CFSG.layer X) (CFSG.layer X) :=
    isSylowOf_inf_layer h
  have huniq : ∀ B : Subgroup X, B ≤ P ⊓ CFSG.layer X → Nat.card B = 3 →
      B = Subgroup.zpowers z :=
    fun B hBT hBcard => eq_zpowers_of_card_eq_three hzT hzc hzord hrk hBT hBcard
  have hAeq : A = Subgroup.zpowers z := huniq A hAT h.card_A
  have hAE : ∀ B : Subgroup X, B ≤ CFSG.layer X → Nat.card B = 3 → B = A :=
    fun B hBE hBcard => eq_of_card_three_of_isSylowOf hTsyl
      (fun C hCT hCcard => (huniq C hCT hCcard).trans hAeq.symm)
      h.normal_A h.card_A hBE hBcard
  have h3L : 3 ∣ Nat.card L :=
    CFSG.LocalAnalysis.RankThreeTheoremC.thc_dvd_card Nat.prime_three h.core hL
  haveI : Group.IsPerfect ↥L := hL.1.1
  obtain ⟨x, hx3, hxnc⟩ :=
    CFSG.Quasithin.Vol2.Ch11.SecS.KF.exists_pow_eq_one_not_mem_center
      (p := 3) (L := ↥L) (by norm_num) h3L
  have hx1 : (x : X) ≠ 1 := by
    intro hx1
    have hxL1 : x = 1 := Subtype.ext hx1
    exact hxnc (by rw [hxL1]; exact Subgroup.one_mem _)
  have hx3' : (x : X) ^ 3 = 1 := by
    have h := congrArg (fun y : ↥L => (y : X)) hx3
    simpa using h
  have hxord : orderOf (x : X) = 3 := orderOf_eq_prime hx3' hx1
  have hBE : Subgroup.zpowers (x : X) ≤ CFSG.layer X :=
    Subgroup.zpowers_le.mpr (CFSG.LocalCores.component_le_layer hL x.2)
  have hBcard : Nat.card (Subgroup.zpowers (x : X)) = 3 := by
    rw [Nat.card_zpowers, hxord]
  have hBA : Subgroup.zpowers (x : X) = A := hAE _ hBE hBcard
  have hxA : (x : X) ∈ A := by
    rw [← hBA]
    exact Subgroup.mem_zpowers _
  have hcentA : L ≤ Subgroup.centralizer (A : Set X) := h.le_centralizer_A hL
  have hxZ : x ∈ Subgroup.center L := by
    rw [Subgroup.mem_center_iff]
    intro l
    apply Subtype.ext
    have h1 : (x : X) * (l : X) = (l : X) * (x : X) :=
      Subgroup.mem_centralizer_iff.mp (hcentA l.2) (x : X) hxA
    simpa using h1.symm
  exact hxnc hxZ

private lemma normalizer_le_of_rank_le_one {p : ℕ} {P A Y : Subgroup X}
    (h : O1517bRed X p P A Y) {z : X}
    (hzT : z ∈ P ⊓ CFSG.layer X) (hzord : orderOf z = 3)
    (hNT₁ : Subgroup.normalizer ((P ⊓ CFSG.layer X : Subgroup X) : Set X) ≤
      Subgroup.normalizer ((Subgroup.zpowers z : Subgroup X) : Set X))
    (hAT : ¬ A ≤ P ⊓ CFSG.layer X) :
    Subgroup.normalizer ((P ⊓ CFSG.layer X : Subgroup X) : Set X) ≤ Y := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨a, haA, haT₁⟩ : ∃ a ∈ A, a ∉ Subgroup.zpowers z := by
    by_contra hno
    push Not at hno
    exact hAT (le_trans hno (Subgroup.zpowers_le.mpr hzT))
  have haord : orderOf a = 3 := by
    have hdiv : orderOf a ∣ 3 := by
      rw [← Nat.card_zpowers]
      exact (Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr haA)).trans
        (by rw [h.card_A])
    rcases (Nat.dvd_prime Nat.prime_three).mp hdiv with h1 | h3
    · exact absurd (orderOf_eq_one_iff.mp h1)
        (fun h1a => haT₁ (h1a ▸ (Subgroup.zpowers z).one_mem))
    · exact h3
  have hzpowA : Subgroup.zpowers a = A := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr haA) ?_
    rw [Nat.card_zpowers, haord, h.card_A]
  have hsolv : Group.IsSolvable ↥A := by
    haveI : IsCyclic ↥A := isCyclic_of_prime_card h.card_A
    exact Group.isSolvable_of_comm fun a b => (IsCyclic.commGroup).mul_comm a b
  have hEA : ⁅CFSG.layer X, A⁆ = ⊥ :=
    (CFSG.LocalCores.component_solvable_centralizer hsolv h.normal_A.isSubnormal).2
  have hEcentA : CFSG.layer X ≤ Subgroup.centralizer (A : Set X) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hEA
  have hza : z * a = a * z :=
    (Subgroup.mem_centralizer_iff.mp (hEcentA hzT.2) a haA).symm
  have hcomm : ∀ w ∈ Subgroup.zpowers z, w * a = a * w := by
    intro w hw
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hw
    rw [← hn]
    exact (Commute.zpow_left hza n).eq
  have hE9 := CFSG.GroupTheory.isElemAbelian_sup_zpowers_of_commute
    (r := 3) (by rw [Nat.card_zpowers, hzord]) haord haT₁ hcomm
  have hDea : CFSG.Open.IsElemAbelian 3 (Subgroup.zpowers z ⊔ A) := by
    simpa [hzpowA] using hE9.1
  have hDcard : Nat.card (Subgroup.zpowers z ⊔ A : Subgroup X) = 3 ^ 2 := by
    simpa [hzpowA] using hE9.2
  have hDp : 2 ≤ CFSG.Open.pRank 3 (Subgroup.zpowers z ⊔ A) :=
    CFSG.SectionRank.le_pRank (p := 3) (k := 2) (by norm_num) le_rfl hDea hDcard
  have hDP : Subgroup.zpowers z ⊔ A ≤ P :=
    sup_le ((Subgroup.zpowers_le.mpr hzT).trans inf_le_left) h.le_P
  have hND : Subgroup.normalizer ((Subgroup.zpowers z ⊔ A : Subgroup X) : Set X) ≤ Y := by
    calc Subgroup.normalizer ((Subgroup.zpowers z ⊔ A : Subgroup X) : Set X)
        ≤ CFSG.Open.rankThreeGamma 2 3 P := by
          change _ ≤ CFSG.Open.GLBCore 3 2 P
          exact le_sSup ⟨_, hDP, hDp, rfl⟩
      _ ≤ Y := h.gamma
  have hNT : Subgroup.normalizer ((P ⊓ CFSG.layer X : Subgroup X) : Set X) ≤
      Subgroup.normalizer ((Subgroup.zpowers z ⊔ A : Subgroup X) : Set X) := by
    intro g hg
    have hg₁ : g ∈ Subgroup.normalizer
        ((Subgroup.zpowers z : Subgroup X) : Set X) := hNT₁ hg
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hg₁ ⊢
    have hgA : A.map (MulAut.conj g) = A :=
      Subgroup.normal_iff_map_conj_eq.mp h.normal_A g
    calc (Subgroup.zpowers z ⊔ A).map (MulAut.conj g).toMonoidHom
        = (Subgroup.zpowers z).map (MulAut.conj g).toMonoidHom ⊔
          A.map (MulAut.conj g).toMonoidHom := Subgroup.map_sup _ _ _
      _ = Subgroup.zpowers z ⊔ A := by simpa [hg₁, hgA]
  exact hNT.trans hND

private lemma normalizer_le_of_two_le_pRank {p : ℕ} {P A Y : Subgroup X}
    (h : O1517bRed X p P A Y)
    (h2 : 2 ≤ CFSG.Open.pRank 3 (P ⊓ CFSG.layer X)) :
    Subgroup.normalizer ((P ⊓ CFSG.layer X : Subgroup X) : Set X) ≤ Y := by
  calc Subgroup.normalizer ((P ⊓ CFSG.layer X : Subgroup X) : Set X)
      ≤ CFSG.Open.rankThreeGamma 2 3 P := by
        change Subgroup.normalizer ((P ⊓ CFSG.layer X : Subgroup X) : Set X)
          ≤ CFSG.Open.GLBCore 3 2 P
        exact le_sSup ⟨P ⊓ CFSG.layer X, inf_le_left, h2, rfl⟩
    _ ≤ Y := h.gamma

private lemma normalizer_le_inf_layer_of_rank_le_one {p : ℕ} {P A Y : Subgroup X}
    (h : O1517bRed X p P A Y) {L : Subgroup X} (hL : CFSG.IsComponent L)
    (hrk : CFSG.Open.pRank 3 (P ⊓ CFSG.layer X) ≤ 1) :
    Subgroup.normalizer ((P ⊓ CFSG.layer X : Subgroup X) : Set X) ≤ Y := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hTne : P ⊓ CFSG.layer X ≠ ⊥ := ne_bot_inf_layer h hL
  obtain ⟨z, hzT, hzcent, hzord⟩ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.exists_mem_centralizer_orderOf_eq
      (isSylowOf_inf_layer h).isPGroup hTne
  have hzc : ∀ y ∈ P ⊓ CFSG.layer X, z * y = y * z := fun y hy =>
    (Subgroup.mem_centralizer_iff.mp hzcent y hy).symm
  have huniq : ∀ B : Subgroup X, B ≤ P ⊓ CFSG.layer X → Nat.card B = 3 →
      B = Subgroup.zpowers z :=
    fun B hBT hBcard => eq_zpowers_of_card_eq_three hzT hzc hzord hrk hBT hBcard
  have hNT₁ : Subgroup.normalizer ((P ⊓ CFSG.layer X : Subgroup X) : Set X) ≤
      Subgroup.normalizer ((Subgroup.zpowers z : Subgroup X) : Set X) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hg ⊢
    have hle : (Subgroup.zpowers z).map (MulAut.conj g).toMonoidHom ≤
        P ⊓ CFSG.layer X := by
      rw [← hg]
      exact Subgroup.map_mono (Subgroup.zpowers_le.mpr hzT)
    have hcard : Nat.card ((Subgroup.zpowers z).map
        (MulAut.conj g).toMonoidHom) = 3 := by
      rw [Subgroup.card_map_of_injective (MulAut.conj g).injective,
        Nat.card_zpowers, hzord]
    exact huniq _ hle hcard
  by_cases hAT : A ≤ P ⊓ CFSG.layer X
  · exact (false_of_le_inf_layer h hL hzT hzc hzord hrk hAT).elim
  · exact normalizer_le_of_rank_le_one h hzT hzord hNT₁ hAT

theorem O1517bRed.exists_component_not_le {X : Type} [Group X] [Finite X] {p : ℕ}
    {P A Y : Subgroup X} (h : O1517bRed X p P A Y) :
    ∃ L : Subgroup X, CFSG.IsComponent L ∧ ¬ L ≤ Y := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  by_contra hcon
  push Not at hcon
  have hE_le_Y : CFSG.layer X ≤ Y := by
    rw [CFSG.layer.eq_sSup]
    exact sSup_le hcon
  have hex : ∃ L : Subgroup X, CFSG.IsComponent L := by
    by_contra hno
    push Not at hno
    exact h.layer_ne (CFSG.LocalCores.layer_eq_bot_of_forall hno)
  obtain ⟨L, hL⟩ := hex
  have hFrattini : (⊤ : Subgroup X) ≤ CFSG.layer X ⊔
      Subgroup.normalizer ((P ⊓ CFSG.layer X : Subgroup X) : Set X) :=
    CFSG.LocalAnalysis.RankThreeTheoremC.le_sup_normalizer_of_isSylowOf
      (H := ⊤) (Y := CFSG.layer X) (S := P ⊓ CFSG.layer X)
      le_normalizer_layer (isSylowOf_inf_layer h)
  have key : Subgroup.normalizer ((P ⊓ CFSG.layer X : Subgroup X) : Set X) ≤ Y := by
    by_cases h2 : 2 ≤ CFSG.Open.pRank 3 (P ⊓ CFSG.layer X)
    · exact normalizer_le_of_two_le_pRank h h2
    · exact normalizer_le_inf_layer_of_rank_le_one h hL (by omega)
  have htop : (⊤ : Subgroup X) ≤ Y :=
    hFrattini.trans (sup_le hE_le_Y key)
  exact h.strong.1 (top_le_iff.mp htop)

end CFSG.LocalAnalysis.AGL81TheoremCD.Section15
