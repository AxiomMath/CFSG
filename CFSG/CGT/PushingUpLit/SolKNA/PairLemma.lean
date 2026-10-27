module

public import CFSG.CGT.PushingUpLit.SolKNA.Analysis
public import CFSG.CGT.PushingUpLit.SolKNA.Dichotomy
public import CFSG.CGT.PushingUpLit.SolKNA.FinalCase
import CFSG.CGT.PushingUpLit.SolKNA.BranchC3
import CFSG.Dihedral.DisconnectedInvolutionGraph.InvolutionRootSupport

public section

namespace CFSG.CGT.PushingUpLit.SolKNA

set_option linter.unusedSectionVars false

open CFSG CFSG.CGT.Timmesfeld75 CFSG.CGT.PushingUpLit.SolKAb CFSG.RankThree.GF2n
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.Open (IsElemAbelian)
open CFSG.Assembly (pCoreOf)
open CFSG.ComponentClassification.AS76b (oUpperTwoPrime)
open CFSG.ComponentClassification.AschbacherTightEmbedding (TightlyEmbedded rightConjugate)
open CFSG.ComponentClassification.AschbacherTheorem5.SectionSix (tightlyEmbedded_subgroupOf_iff)
open scoped commutatorElement

variable {G : Type} [Group G]

theorem eq_one_or_eq_of_mem_zpowers {c x : G} (hc : c * c = 1) (hx : x ∈ Subgroup.zpowers c) :
    x = 1 ∨ x = c := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have hc2 : c ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hc
  obtain ⟨n, hn | hn⟩ := Int.even_or_odd' k
  · left
    rw [hn, zpow_mul, hc2, one_zpow]
  · right
    rw [hn, zpow_add_one, zpow_mul, hc2, one_zpow, one_mul]

structure QuatInv (R : Subgroup G) (c : G) : Prop where
  mem : c ∈ R
  ne : c ≠ 1
  sq : c * c = 1
  central : ∀ r ∈ R, r * c = c * r
  comm : ⁅R, R⁆ = Subgroup.zpowers c
  sq_central : ∀ y ∈ R, y ∈ zCenter R → y * y = 1
  sq_noncentral : ∀ y ∈ R, y ∉ zCenter R → y * y = c
  relIndex : (zCenter R).relIndex R = 4
  card : 4 ≤ Nat.card ↥(zCenter R)

namespace QuatInv

variable {R : Subgroup G} {c : G} (Q : QuatInv R c)
include Q

theorem mem_zCenter_of_sq {y : G} (hy : y ∈ R) (h : y * y = 1) : y ∈ zCenter R := by
  by_contra hyZ
  exact Q.ne ((Q.sq_noncentral y hy hyZ).symm.trans h)

theorem conj_c {m : G} (hm : m ∈ Subgroup.normalizer (R : Set G)) : m * c * m⁻¹ = c := by
  have hR : R.map (MulAut.conj m).toMonoidHom = R := Subgroup.mem_normalizer_iff_map_conj_eq.mp hm
  have h1 : (⁅R, R⁆).map (MulAut.conj m).toMonoidHom = ⁅R, R⁆ := by
    rw [Subgroup.map_commutator, hR]
  have h2 : m * c * m⁻¹ ∈ Subgroup.zpowers c := by
    have hc : c ∈ ⁅R, R⁆ := by rw [Q.comm]; exact Subgroup.mem_zpowers c
    have := Subgroup.mem_map_of_mem (MulAut.conj m).toMonoidHom hc
    rw [h1, Q.comm] at this
    simpa [MulAut.conj_apply] using this
  rcases eq_one_or_eq_of_mem_zpowers Q.sq h2 with h3 | h3
  · exfalso
    apply Q.ne
    calc c = m⁻¹ * (m * c * m⁻¹) * m := by group
      _ = m⁻¹ * 1 * m := by rw [h3]
      _ = 1 := by group
  · exact h3

theorem sq_conj {h y : G} (hy : y ∈ conjSubgroup h R) (hyZ : y ∉ conjSubgroup h (zCenter R)) :
    y * y = h * c * h⁻¹ := by
  rw [mem_conjSubgroup] at hy hyZ
  have := Q.sq_noncentral _ hy hyZ
  calc y * y = h * ((h⁻¹ * y * h) * (h⁻¹ * y * h)) * h⁻¹ := by group
    _ = h * c * h⁻¹ := by rw [this]

theorem mem_conj_zCenter_of_sq {h t : G} (ht : t ∈ conjSubgroup h R) (h2 : t * t = 1) :
    t ∈ conjSubgroup h (zCenter R) := by
  rw [mem_conjSubgroup] at ht ⊢
  apply Q.mem_zCenter_of_sq ht
  calc (h⁻¹ * t * h) * (h⁻¹ * t * h) = h⁻¹ * (t * t) * h := by group
    _ = 1 := by rw [h2]; group

theorem card_R [Finite G] : Nat.card ↥R = 4 * Nat.card ↥(zCenter R) := by
  have h := Subgroup.relIndex_mul_card (zCenter R) R
  rw [Q.relIndex, inf_of_le_left (inf_le_left : zCenter R ≤ R)] at h
  exact h.symm

theorem centralizer_eq [Finite G] (S : STSetting G R) :
    Subgroup.centralizer ({c} : Set G) = Subgroup.normalizer (R : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf c = 2 := orderOf_eq_prime (by rw [pow_two]; exact Q.sq) Q.ne
  have hle : Subgroup.normalizer (R : Set G) ≤ Subgroup.centralizer ({c} : Set G) := by
    intro m hm
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    have := Q.conj_c hm
    calc x * m = (m * x * m⁻¹) * m := by rw [this]
      _ = m * x := by group
  have hcn : Subgroup.normalizer ((Subgroup.zpowers c : Subgroup G) : Set G) =
      Subgroup.centralizer ({c} : Set G) :=
    CFSG.DisconnectedInvolutionGraph.Helpers.involution_zpowers_normalizer_eq_centralizer
      ⟨c, hord⟩
  by_contra hne
  refine S.max.2 _ (lt_of_le_of_ne hle (Ne.symm hne)) ?_
  refine ⟨Subgroup.zpowers c, fun h => Q.ne (Subgroup.zpowers_eq_bot.mp h), ?_, hcn.symm⟩
  exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])

end QuatInv

section Index

variable [Finite G]

theorem mem_or_mul_inv_mem {X A : Subgroup G} (hidx : A.relIndex X = 2) {x z : G} (hx : x ∈ X)
    (hz : z ∈ X) (hzA : z ∉ A) : x ∈ A ∨ x * z⁻¹ ∈ A := by
  by_cases hxA : x ∈ A
  · exact Or.inl hxA
  · right
    have h2 : (A.subgroupOf X).index = 2 := hidx
    have h3 : (⟨x, hx⟩ : X) * (⟨z, hz⟩ : X)⁻¹ ∈ A.subgroupOf X := by
      refine (Subgroup.mul_mem_iff_of_index_two h2).mpr ⟨fun h => absurd h hxA, fun h => ?_⟩
      exfalso
      apply hzA
      have h4 : ((⟨z, hz⟩ : X)⁻¹ : X) ∈ A.subgroupOf X := h
      have h5 := A.inv_mem (Subgroup.mem_subgroupOf.mp h4)
      simpa using h5
    simpa [Subgroup.mem_subgroupOf] using h3

theorem centralizer_le_of_index_two {X A : Subgroup G} (hAX : A ≤ X) (hidx : A.relIndex X = 2)
    (hA : IsCommSubgroup A) (hX : ¬ IsCommSubgroup X) :
    X ⊓ Subgroup.centralizer (X : Set G) ≤ A := by
  intro z hz
  by_contra hzA
  apply hX
  have hzX : z ∈ X := hz.1
  have hzc : ∀ x ∈ X, Commute z x := fun x hx =>
    (Subgroup.mem_centralizer_iff.mp hz.2 x hx).symm
  have hAA : ∀ a ∈ A, ∀ b ∈ A, Commute a b := fun a ha b hb => hA a ha b hb
  have hAz : ∀ a ∈ A, Commute a z := fun a ha => (hzc a (hAX ha)).symm
  intro x₁ hx₁ x₂ hx₂
  have e₁ : x₁ = (x₁ * z⁻¹) * z := by group
  have e₂ : x₂ = (x₂ * z⁻¹) * z := by group
  rcases mem_or_mul_inv_mem hidx hx₁ hzX hzA with h1 | h1 <;>
    rcases mem_or_mul_inv_mem hidx hx₂ hzX hzA with h2 | h2
  · exact hA x₁ h1 x₂ h2
  · have : Commute x₁ x₂ := by
      rw [e₂]
      exact (hAA x₁ h1 _ h2).mul_right (hAz x₁ h1)
    exact this.eq
  · have : Commute x₁ x₂ := by
      rw [e₁]
      exact (hAA _ h1 x₂ h2).mul_left (hzc x₂ (hAX h2))
    exact this.eq
  · have : Commute x₁ x₂ := by
      rw [e₁, e₂]
      exact ((hAA _ h1 _ h2).mul_right (hAz _ h1)).mul_left
        ((hAz _ h2).symm.mul_right (Commute.refl z))
    exact this.eq

end Index

section Pair

variable [Finite G] {R : Subgroup G} {c : G}

theorem conjSubgroup_mono {A B : Subgroup G} (h : A ≤ B) (g : G) :
    conjSubgroup g A ≤ conjSubgroup g B := Subgroup.map_mono h

theorem not_isCommSubgroup_conjSubgroup (h : G) (hR : ¬ IsCommSubgroup R) :
    ¬ IsCommSubgroup (conjSubgroup h R) := by
  intro hB
  apply hR
  intro a ha b hb
  have ha' : h * a * h⁻¹ ∈ conjSubgroup h R := by
    rw [mem_conjSubgroup, show h⁻¹ * (h * a * h⁻¹) * h = a by group]
    exact ha
  have hb' : h * b * h⁻¹ ∈ conjSubgroup h R := by
    rw [mem_conjSubgroup, show h⁻¹ * (h * b * h⁻¹) * h = b by group]
    exact hb
  have := hB _ ha' _ hb'
  calc a * b = h⁻¹ * ((h * a * h⁻¹) * (h * b * h⁻¹)) * h := by group
    _ = h⁻¹ * ((h * b * h⁻¹) * (h * a * h⁻¹)) * h := by rw [this]
    _ = b * a := by group

theorem exists_mem_not_conj_zCenter {X : Subgroup G} (h : G)
    (hX : Nat.card ↥(zCenter R) < Nat.card ↥X) :
    ∃ y ∈ X, y ∉ conjSubgroup h (zCenter R) := by
  by_contra hcon
  have hle : X ≤ conjSubgroup h (zCenter R) := fun y hy => by
    by_contra hy'
    exact hcon ⟨y, hy, hy'⟩
  have := Subgroup.card_le_of_le hle
  rw [RankThree.GF2n.card_conjSubgroup] at this
  omega

theorem P_of_normalizes {h : G} (hBN : conjSubgroup h R ≤ Subgroup.normalizer (R : Set G))
    (hcomm : ∀ a ∈ R, ∀ b ∈ conjSubgroup h R, a * b = b * a) :
    conjSubgroup h (zCenter R) ≤ Subgroup.normalizer (R : Set G) ∧
      ∀ a ∈ zCenter R, ∀ b ∈ conjSubgroup h (zCenter R), a * b = b * a :=
  ⟨fun _ hx => hBN (conjSubgroup_mono inf_le_left h hx),
    fun a ha b hb => hcomm a ha.1 b (conjSubgroup_mono inf_le_left h hb)⟩

theorem P_of_halved (hRnc : ¬ IsCommSubgroup R) {h : G} {N : Subgroup G} (hNR : N ≤ R)
    (hNidx : N.relIndex R = 2) (hNc : IsCommSubgroup N)
    (hTidx : (conjSubgroup h R ⊓ Subgroup.normalizer (R : Set G)).relIndex (conjSubgroup h R) = 2)
    (hTc : IsCommSubgroup (conjSubgroup h R ⊓ Subgroup.normalizer (R : Set G)))
    (hNT : ∀ a ∈ N, ∀ b ∈ conjSubgroup h R ⊓ Subgroup.normalizer (R : Set G), a * b = b * a) :
    conjSubgroup h (zCenter R) ≤ Subgroup.normalizer (R : Set G) ∧
      ∀ a ∈ zCenter R, ∀ b ∈ conjSubgroup h (zCenter R), a * b = b * a := by
  have hBnc := not_isCommSubgroup_conjSubgroup h hRnc
  have hZB : conjSubgroup h (zCenter R) ≤
      conjSubgroup h R ⊓ Subgroup.normalizer (R : Set G) := by
    rw [conjSubgroup_zCenter]
    exact centralizer_le_of_index_two inf_le_left hTidx hTc hBnc
  have hZR : zCenter R ≤ N := centralizer_le_of_index_two hNR hNidx hNc hRnc
  exact ⟨fun x hx => (hZB hx).2, fun a ha b hb => hNT a (hZR ha) b (hZB hb)⟩

theorem sq_of_normalizes (Q : QuatInv R c) {h : G}
    (hBN : conjSubgroup h R ≤ Subgroup.normalizer (R : Set G)) :
    ∃ y ∈ conjSubgroup h R ⊓ Subgroup.normalizer (R : Set G), y * y = h * c * h⁻¹ := by
  have hcard : Nat.card ↥(zCenter R) <
      Nat.card ↥(conjSubgroup h R ⊓ Subgroup.normalizer (R : Set G)) := by
    rw [inf_of_le_left hBN, RankThree.GF2n.card_conjSubgroup, Q.card_R]
    have := Q.card
    omega
  obtain ⟨y, hy, hyZ⟩ := exists_mem_not_conj_zCenter h hcard
  exact ⟨y, hy, Q.sq_conj hy.1 hyZ⟩

theorem sq_of_halved (Q : QuatInv R c) {h : G}
    (hTidx : (conjSubgroup h R ⊓ Subgroup.normalizer (R : Set G)).relIndex (conjSubgroup h R) = 2) :
    ∃ y ∈ conjSubgroup h R ⊓ Subgroup.normalizer (R : Set G), y * y = h * c * h⁻¹ := by
  have h1 := Subgroup.relIndex_mul_card (conjSubgroup h R ⊓ Subgroup.normalizer (R : Set G))
    (conjSubgroup h R)
  rw [hTidx, inf_of_le_left (inf_le_left : conjSubgroup h R ⊓ Subgroup.normalizer (R : Set G) ≤
    conjSubgroup h R), RankThree.GF2n.card_conjSubgroup, Q.card_R] at h1
  have hcard : Nat.card ↥(zCenter R) <
      Nat.card ↥(conjSubgroup h R ⊓ Subgroup.normalizer (R : Set G)) := by
    have := Q.card
    omega
  obtain ⟨y, hy, hyZ⟩ := exists_mem_not_conj_zCenter h hcard
  exact ⟨y, hy, Q.sq_conj hy.1 hyZ⟩

end Pair

section Commute

variable [Finite G] {R : Subgroup G}

theorem commute_of_le_normalizer (hR2 : IsPGroup 2 R) (hTI : IsTI R) {h : G}
    (hh : conjSubgroup h R ≠ R) (hB1 : conjSubgroup h R ≠ ⊥)
    (hBN : conjSubgroup h R ≤ Subgroup.normalizer (R : Set G)) :
    ∀ a ∈ R, ∀ b ∈ conjSubgroup h R, a * b = b * a := by
  have hB2 : IsPGroup 2 (conjSubgroup h R) := hR2.map (MulAut.conj h).toMonoidHom
  have hS2 : IsPGroup 2 (R ⊔ conjSubgroup h R : Subgroup G) :=
    hR2.to_sup_of_normal_left' hB2 hBN
  have hTIB : IsTI (conjSubgroup h R) := isTI_conjSubgroup hTI h
  have hinf : conjSubgroup h R ⊓ R = ⊥ := by
    rw [inf_comm]
    exact inf_conjSubgroup_eq_bot_of_isTI hTI hh
  have heven : Even (Nat.card ↥(conjSubgroup h R)) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hB2
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hB1 (Subgroup.eq_bot_of_card_eq _ (by rw [hn, pow_zero]))
    rw [hn]
    exact Nat.even_pow.mpr ⟨even_two, hn0⟩
  have hte : TightlyEmbedded ((conjSubgroup h R).subgroupOf (R ⊔ conjSubgroup h R)) := by
    refine (tightlyEmbedded_subgroupOf_iff le_sup_right).mpr ⟨heven, fun g _ hgN => ?_⟩
    have hne : conjSubgroup g⁻¹ (conjSubgroup h R) ≠ conjSubgroup h R := fun heq =>
      hgN (by simpa using Subgroup.inv_mem _ (conjSubgroup_eq_self_iff.mp heq))
    have hbot : conjSubgroup h R ⊓ rightConjugate (conjSubgroup h R) g = ⊥ :=
      inf_conjSubgroup_eq_bot_of_isTI hTIB hne
    rw [hbot, Subgroup.card_bot]
    exact odd_one
  have hcomm := CFSG.ComponentClassification.Asc76X.asc76Lemma23 G (R ⊔ conjSubgroup h R)
    (conjSubgroup h R) R hS2 le_sup_right hte le_sup_left hBN
    (by rw [RankThree.GF2n.card_conjSubgroup]) hinf
  intro a ha b hb
  have := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm hb
  exact Subgroup.mem_centralizer_iff.mp this a ha

end Commute

section Certified

variable [Finite G] {R : Subgroup G}

theorem pair_halved (B : Branches G) (S : STSetting G R) (hR2 : IsPGroup 2 R)
    (hncomm : ¬ IsCommSubgroup R) (hrk : 2 ≤ CFSG.Open.pRank 2 R) {h : G}
    (hBN : ¬ conjSubgroup h R ≤ Subgroup.normalizer (R : Set G))
    (hT : conjSubgroup h R ⊓ Subgroup.normalizer (R : Set G) ≠ ⊥) :
    ∃ N : Subgroup G, N ≤ R ∧ N.relIndex R = 2 ∧ IsCommSubgroup N ∧
      (conjSubgroup h R ⊓ Subgroup.normalizer (R : Set G)).relIndex (conjSubgroup h R) = 2 ∧
      IsCommSubgroup (conjSubgroup h R ⊓ Subgroup.normalizer (R : Set G)) ∧
      ∀ a ∈ N, ∀ b ∈ conjSubgroup h R ⊓ Subgroup.normalizer (R : Set G), a * b = b * a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hrc : rightConjugate R h⁻¹ = conjSubgroup h R := by
    show conjSubgroup (h⁻¹)⁻¹ R = conjSubgroup h R
    rw [inv_inv]
  have hB2 : IsPGroup 2 (conjSubgroup h R) := hR2.map (MulAut.conj h).toMonoidHom
  have hT2 : IsPGroup 2 (conjSubgroup h R ⊓ Subgroup.normalizer (R : Set G) : Subgroup G) :=
    hB2.to_le inf_le_left
  have hhR : conjSubgroup h R ≠ R := fun heq => hBN (by rw [heq]; exact Subgroup.le_normalizer)
  have hgN : h⁻¹ ∉ Subgroup.normalizer (R : Set G) := fun hmem =>
    hhR (conjSubgroup_eq_self_iff.mpr (by simpa using Subgroup.inv_mem _ hmem))
  have hTlt : Nat.card ↥(conjSubgroup h R ⊓ Subgroup.normalizer (R : Set G)) < Nat.card ↥R := by
    by_contra hge
    rw [not_lt] at hge
    have hBle : Nat.card ↥(conjSubgroup h R) ≤
        Nat.card ↥(conjSubgroup h R ⊓ Subgroup.normalizer (R : Set G)) := by
      rw [RankThree.GF2n.card_conjSubgroup]
      exact hge
    exact hBN ((Subgroup.eq_of_le_of_card_ge inf_le_left hBle) ▸ inf_le_right)
  have cfgB : NAConfig G R R (conjSubgroup h R ⊓ Subgroup.normalizer (R : Set G)) h⁻¹ :=
    { stSetting := S
      perfect := oUpperTwoPrime_eq_of_isPGroup hR2
      sylowR := isSylowOf_self hR2
      noncomm := hncomm
      rank := hrk
      g_not := hgN
      sylowT := by rw [hrc]; exact isSylowOf_self hT2
      T_ne := hT
      T_lt := hTlt
      T_norm := inf_le_right
      T_le := by rw [hrc]; exact inf_le_left }
  obtain ⟨hel, -⟩ := analysis_core B cfgB
  have I := cfgB.caseI hel
  obtain ⟨-, -, hcard, hNC, -, hTcomm, -, -, -⟩ := cfgB.basic
  have hNR : R ⊓ Subgroup.normalizer ((conjSubgroup h R ⊓ Subgroup.normalizer (R : Set G) :
      Subgroup G) : Set G) ≤ R := inf_le_left
  have hcardR : 2 * Nat.card ↥(R ⊓ Subgroup.normalizer ((conjSubgroup h R ⊓
      Subgroup.normalizer (R : Set G) : Subgroup G) : Set G)) = Nat.card ↥R := by
    have h1 := Subgroup.relIndex_mul_card (R ⊓ Subgroup.normalizer ((conjSubgroup h R ⊓
      Subgroup.normalizer (R : Set G) : Subgroup G) : Set G)) R
    rw [I.relIndex_two, inf_of_le_left hNR] at h1
    exact h1
  refine ⟨R ⊓ Subgroup.normalizer ((conjSubgroup h R ⊓ Subgroup.normalizer (R : Set G) :
    Subgroup G) : Set G), hNR, I.relIndex_two, I.comm, ?_, hTcomm, ?_⟩
  · have h1 := Subgroup.relIndex_mul_card
      (conjSubgroup h R ⊓ Subgroup.normalizer (R : Set G)) (conjSubgroup h R)
    rw [inf_of_le_left (inf_le_left : conjSubgroup h R ⊓ Subgroup.normalizer (R : Set G) ≤
      conjSubgroup h R), RankThree.GF2n.card_conjSubgroup, ← hcardR, hcard] at h1
    have hpos : 0 < Nat.card ↥(conjSubgroup h R ⊓ Subgroup.normalizer (R : Set G)) :=
      Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hpos (by rw [h1, mul_comm])
  · intro a ha b hb
    have ha' : a ∈ R ⊓ Subgroup.centralizer ((conjSubgroup h R ⊓ Subgroup.normalizer
        (R : Set G) : Subgroup G) : Set G) := hNC ▸ ha
    exact (Subgroup.mem_centralizer_iff.mp ha'.2 b hb).symm

theorem finalCase_of (B : Branches G) (S : STSetting G R) (hR2 : IsPGroup 2 R)
    (hncomm : ¬ IsCommSubgroup R) (hrk : 2 ≤ CFSG.Open.pRank 2 R) {c : G} (Q : QuatInv R c) :
    FinalCase G R c := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRpc : R ≤ pCoreOf 2 R := le_pCoreOf_of_normal le_rfl hR2 Subgroup.le_normalizer
  have hTI : IsTI R := isTI_of_normal_le_pCoreOf S.tight hRpc le_rfl
  exact
    { simple := S.simple
      nonab := S.nonab
      two := hR2
      ti := hTI
      max := S.max
      fstar := (isCharacteristicP_iff_generalizedFitting_eq_pCore _ 2).mp S.isCharacteristicP
      z_mem := ⟨Q.mem, Subgroup.mem_centralizer_iff.mpr fun r hr => Q.central r hr⟩
      z_ne := Q.ne
      cent_z := Q.centralizer_eq S
      Z_sq := fun x hx => Q.sq_central x hx.1 hx
      Z_card := Q.card
      P := fun h hh hT => by
        by_cases hBN : conjSubgroup h R ≤ Subgroup.normalizer (R : Set G)
        · exact P_of_normalizes hBN (commute_of_le_normalizer hR2 hTI hh
            (fun hb => hT (by rw [hb, bot_inf_eq])) hBN)
        · obtain ⟨N, hNR, hNidx, hNc, hTidx, hTc, hNT⟩ :=
            pair_halved B S hR2 hncomm hrk hBN hT
          exact P_of_halved hncomm hNR hNidx hNc hTidx hTc hNT
      sq_mem := fun h hT => by
        by_cases hBN : conjSubgroup h R ≤ Subgroup.normalizer (R : Set G)
        · exact sq_of_normalizes Q hBN
        · obtain ⟨N, hNR, hNidx, hNc, hTidx, hTc, hNT⟩ :=
            pair_halved B S hR2 hncomm hrk hBN hT
          exact sq_of_halved Q hTidx
      invol_mem := fun h t ht ht2 => Q.mem_conj_zCenter_of_sq ht.1 ht2 }

theorem analysis (B : Branches G) {K R T : Subgroup G} {g : G} (cfg : NAConfig G K R T g) :
    False := by
  obtain ⟨hel, hM⟩ := analysis_core B cfg
  obtain ⟨hKR, -, c, hcR, hc1, hcsq, hcc, hcom, hZ1, hZ2, hrel, hcard, -⟩ :=
    cfg.caseI_not_normal (cfg.caseI hel) hM
  subst hKR
  exact (finalCase_of B cfg.stSetting cfg.sylowR.isPGroup cfg.noncomm cfg.rank (c := c)
    ⟨hcR, hc1, hcsq, hcc, hcom, hZ1, hZ2, hrel, hcard⟩).false

end Certified

end CFSG.CGT.PushingUpLit.SolKNA
