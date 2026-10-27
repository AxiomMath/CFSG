module

public import CFSG.ClassicalInvolution.RouteD.GapsFrBNodes
public import CFSG.ClassicalInvolution.Balance.LayerGenerationPairSpinFrame
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
public import CFSG.ClassicalInvolution.RouteD.GapsFrNodes
public import CFSG.ClassicalInvolution.RouteD.LocalTwinBRecognition

public section

namespace CFSG.ClassicalInvolution.RouteD.Gaps

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.LieType.Universal.Spin CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.RouteD CFSG.LieType CFSG.LieType.RootSystem CFSG.LieType.Universal
  CFSG.LieType.CurtisTits CFSG.Timmesfeld
open scoped MatrixGroups

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

section Frame

variable {m : ℕ} {F : Type} [Field F]

theorem commutes_zpowers_of {X : Type} [Group X] {s : X} {L : Subgroup X}
    (h : ∀ y ∈ L, s * y = y * s) : Commutes (Subgroup.zpowers s) L := by
  rintro _ ⟨n, rfl⟩ y hy
  exact (Commute.zpow_left (h y hy) n).eq

theorem commutes_zpowers_shortRoot_rootSL2 (k : Fin m) {a b : ℕ} (ha : a < m) (hb : b < m)
    (hab : a ≠ b) (hka : k.val ≠ a) (hkb : k.val ≠ b) (s t u : Bool) (c : F) :
    Commutes (Subgroup.zpowers ((oddFrame m F).shortRoot k u (Multiplicative.ofAdd c)))
      (rootSL2 (oddFrame m F).toHypFrame a b ha hb hab s t) := by
  have hij : (⟨a, ha⟩ : Fin m) ≠ ⟨b, hb⟩ := fun h => hab (congrArg Fin.val h)
  have hka' : k ≠ ⟨a, ha⟩ := fun h => hka (congrArg Fin.val h)
  have hkb' : k ≠ ⟨b, hb⟩ := fun h => hkb (congrArg Fin.val h)
  unfold rootSL2
  rw [longSL2_range_eq_sup]
  refine (commutes_sup_right).mpr ⟨commutes_zpowers_of ?_, commutes_zpowers_of ?_⟩
  · rintro _ ⟨x, rfl⟩
    obtain ⟨x, rfl⟩ : ∃ x', x = Multiplicative.ofAdd x' := ⟨Multiplicative.toAdd x, rfl⟩
    exact ((oddFrame m F).commute_longRoot_shortRoot_of_ne hij hka' hkb' s t u x c).symm.eq
  · rintro _ ⟨x, rfl⟩
    obtain ⟨x, rfl⟩ : ∃ x', x = Multiplicative.ofAdd x' := ⟨Multiplicative.toAdd x, rfl⟩
    exact ((oddFrame m F).commute_longRoot_shortRoot_of_ne hij.symm hkb' hka' (!t) (!s) u x
      c).symm.eq

end Frame

section Involution

variable {m : ℕ} {F V : Type} [Field F] [Finite F] [AddCommGroup V] [Module F V]
  {Q : QuadraticForm F V}

open CFSG.ClassicalInvolution.Balance.Bootstrap (La_neg_one_toFrame_vec La_neg_one_of_mem_perp)

theorem short_not_commute_involution (hodd : Odd (Nat.card F)) (Fr : OddFrame Q m) {i j : Fin m}
    (hij : i ≠ j) (s t : Bool) :
    spinAction Q (Fr.shortRoot j true (Multiplicative.ofAdd 1)) *
        (Fr.toHypFrame.toFrame hij s t).La (-1) ≠
      (Fr.toHypFrame.toFrame hij s t).La (-1) *
        spinAction Q (Fr.shortRoot j true (Multiplicative.ofAdd 1)) := by
  intro h
  have h2 : (2 : F) ≠ 0 := IsFundamental.two_ne_zero_of_odd hodd
  have hz0 : ∀ a r, polar Q Fr.z (Fr.vec a r) = 0 := fun a r => by
    rw [polar_comm]
    exact Fr.polar_vec_z a r
  have hzperp : Fr.z ∈ (Fr.toHypFrame.toFrame hij s t).perp := by
    rw [Frame.mem_perp_iff]
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [Frame.coords_apply, CFSG.LieType.Universal.Spin.HypFrame.toFrame, Frame.f₁,
        Frame.f₂, Frame.e₁, Frame.e₂, hz0]
  have hι_f : (Fr.toHypFrame.toFrame hij s t).La (-1) (Fr.vec j false) = -Fr.vec j false := by
    rw [La_neg_one_toFrame_vec Fr.toHypFrame hij s t j false]
    simp
  have hι_e : (Fr.toHypFrame.toFrame hij s t).La (-1) (Fr.vec j true) = -Fr.vec j true := by
    rw [La_neg_one_toFrame_vec Fr.toHypFrame hij s t j true]
    simp
  have hι_z : (Fr.toHypFrame.toFrame hij s t).La (-1) Fr.z = Fr.z :=
    La_neg_one_of_mem_perp _ hzperp
  have hEf : spinAction Q (Fr.shortRoot j true (Multiplicative.ofAdd 1)) (Fr.vec j false) =
      Fr.vec j false + Fr.z - Fr.vec j true := by
    have hw : polar Q (Fr.vec j true) ((1 : F) • Fr.z) = 0 := by
      rw [polar_smul_right, Fr.polar_vec_z, smul_zero]
    rw [Fr.spinAction_shortRoot_eq_eichler j true 1, eichler_apply (Fr.map_vec j true) hw]
    have e1 : polar Q (Fr.vec j false) (Fr.vec j true) = 1 := Fr.polar_vec_not j false
    have e2 : polar Q (Fr.vec j false) ((1 : F) • Fr.z) = 0 := by
      rw [polar_smul_right, Fr.polar_vec_z, smul_zero]
    rw [e1, e2, QuadraticMap.map_smul, Fr.map_z]
    simp
  have h' := LinearEquiv.congr_fun h (Fr.vec j false)
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hι_f, map_neg, hEf, map_sub, map_add, hι_f,
    hι_z, hι_e] at h'
  have h3 : (2 : F) • Fr.z = 0 := by
    have e : (2 : F) • Fr.z = -((-(Fr.vec j false + Fr.z - Fr.vec j true)) -
        (-Fr.vec j false + Fr.z - -Fr.vec j true)) := by module
    rw [e, h', sub_self, neg_zero]
  rcases smul_eq_zero.mp h3 with h4 | h4
  · exact h2 h4
  · have := Fr.map_z
    rw [h4, QuadraticMap.map_zero] at this
    exact zero_ne_one this

theorem conjSub_short_ne (hodd : Odd (Nat.card F)) (Fr : OddFrame Q m) {i j : Fin m}
    (hij : i ≠ j) :
    conjSub (Fr.shortRoot j true (Multiplicative.ofAdd 1))
        (Fr.toHypFrame.longSL2 hij true false).range ≠
        (Fr.toHypFrame.longSL2 hij true false).range ∧
      conjSub (Fr.shortRoot j true (Multiplicative.ofAdd 1))
        (Fr.toHypFrame.longSL2 hij true false).range ≠
        (Fr.toHypFrame.longSL2 hij true true).range := by
  have h2 : (2 : F) ≠ 0 := IsFundamental.two_ne_zero_of_odd hodd
  set s₀ := Fr.shortRoot j true (Multiplicative.ofAdd 1) with hs₀
  set g := spinAction Q s₀ with hg
  have hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => map_spinAction _ s₀ v
  have hS : IsFundamental Q (Fr.toHypFrame.toFrame hij true false).La.range
      ((Fr.toHypFrame.toFrame hij true false).La (-1)) := IsFundamental.of_frame _
  have hS₂ : IsFundamental Q (Fr.toHypFrame.toFrame hij true true).La.range
      ((Fr.toHypFrame.toFrame hij true true).La (-1)) := IsFundamental.of_frame _
  have hι₂ : (Fr.toHypFrame.toFrame hij true true).La (-1) =
      (Fr.toHypFrame.toFrame hij true false).La (-1) := by
    have e := CFSG.ClassicalInvolution.ModelFacts.OrthAut.swap_toFrame Fr.toHypFrame hij true false
    rw [Bool.not_false] at e
    rw [← e, Frame.La_swap_neg_one]
  have hmapS : (Fr.toHypFrame.longSL2 hij true false).range.map (spinAction Q) =
      (Fr.toHypFrame.toFrame hij true false).La.range :=
    CFSG.ClassicalInvolution.ModelFacts.map_longSL2_range Fr.toHypFrame hij true false
  have hmapS₂ : (Fr.toHypFrame.longSL2 hij true true).range.map (spinAction Q) =
      (Fr.toHypFrame.toFrame hij true true).La.range :=
    CFSG.ClassicalInvolution.ModelFacts.map_longSL2_range Fr.toHypFrame hij true true
  have hconj := IsFundamental.conj hgO hS
  have hL : (conjSub s₀ (Fr.toHypFrame.longSL2 hij true false).range).map (spinAction Q) =
      (Fr.toHypFrame.toFrame hij true false).La.range.map (MulAut.conj g).toMonoidHom := by
    unfold conjSub
    rw [CFSG.ClassicalInvolution.ModelFacts.map_conj_map, hmapS]
  have hnc := short_not_commute_involution hodd Fr hij true false
  refine ⟨fun heq => ?_, fun heq => ?_⟩
  · have himg : (Fr.toHypFrame.toFrame hij true false).La.range.map (MulAut.conj g).toMonoidHom =
        (Fr.toHypFrame.toFrame hij true false).La.range := by rw [← hL, heq, hmapS]
    rw [himg] at hconj
    have := IsFundamental.involution_unique hodd hconj hS
    refine hnc ?_
    calc g * (Fr.toHypFrame.toFrame hij true false).La (-1) =
        (g * (Fr.toHypFrame.toFrame hij true false).La (-1) * g⁻¹) * g := by group
      _ = _ := by rw [this]
  · have himg : (Fr.toHypFrame.toFrame hij true false).La.range.map (MulAut.conj g).toMonoidHom =
        (Fr.toHypFrame.toFrame hij true true).La.range := by rw [← hL, heq, hmapS₂]
    rw [himg] at hconj
    have := IsFundamental.involution_unique hodd hconj hS₂
    rw [hι₂] at this
    refine hnc ?_
    calc g * (Fr.toHypFrame.toFrame hij true false).La (-1) =
        (g * (Fr.toHypFrame.toFrame hij true false).La (-1) * g⁻¹) * g := by group
      _ = _ := by rw [this]

theorem conjSub_short_ne_rootSL2 (hodd : Odd (Nat.card F)) (Fr : OddFrame Q m) {a b : ℕ}
    (ha : a < m) (hb : b < m) (hab : a ≠ b) :
    conjSub (Fr.shortRoot ⟨b, hb⟩ true (Multiplicative.ofAdd 1))
        (rootSL2 Fr.toHypFrame a b ha hb hab true false) ≠
        rootSL2 Fr.toHypFrame a b ha hb hab true false ∧
      conjSub (Fr.shortRoot ⟨b, hb⟩ true (Multiplicative.ofAdd 1))
        (rootSL2 Fr.toHypFrame a b ha hb hab true false) ≠
        rootSL2 Fr.toHypFrame a b ha hb hab true true :=
  conjSub_short_ne hodd Fr (fun h => hab (congrArg Fin.val h))

end Involution

section Main

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G}

theorem exists_dnodes_extra_leaf_odd {m : ℕ} (hm : 8 ≤ m) (c : TCtx p f .POmegaOdd m Ω K z)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hshape : LocalShapeT p f 2 .POmegaOdd m Ω z) {β : Subgroup G} {t : G} (hβ : β ∈ Ω)
    (ht : IsClassicalMember p f β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField p f) W K β) {M : Subgroup G} (hMΩ : M ∈ Ω)
    (hKM : Commutes K M) (hβM : Commutes β M) :
    ∃ nd : DNodes p f m Ω M, nd.J ⟨0, by omega⟩ = K ∧ nd.J ⟨1, by omega⟩ = β ∧
      ∃ N₁ : Subgroup G, N₁ ∈ Ω ∧ Commutes K N₁ ∧ Commutes β N₁ ∧ Commutes M N₁ ∧
        (∀ a (h : a < m), 3 ≤ a → a + 4 ≤ m → Commutes (nd.J ⟨a, h⟩) N₁) ∧
        (∃ W, LinearBlockStandardPair (GaloisField p f) W (nd.J ⟨m - 3, by omega⟩) N₁) ∧
        N₁ ≠ nd.J ⟨m - 2, by omega⟩ ∧ N₁ ≠ nd.J ⟨m - 1, by omega⟩ := by
  classical
  have hm3 : 3 ≤ m := by omega
  have hm4 : 4 ≤ m := by omega
  have hq4 : 4 ≤ p ^ f := by have := c.hq; omega
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f c.hp2
  have : Invertible (2 : GaloisField p f) := invertibleOfNonzero h2
  obtain ⟨xM, hxM⟩ := c.hΩ.classical M hMΩ
  obtain ⟨cx⟩ := exists_ctx_member c hsingle hshape hMΩ hxM
  obtain ⟨W, hW⟩ := hKβ
  have hnKβ : ¬ Commutes K β := not_commutes_of_linearBlockStandardPair hW
  have hKne : K ≠ β := ne_of_linearBlockStandardPair hW
  have hzt : Commute z t :=
    standardPair_involutions_commute h2 hW c.hz.mem ht.mem c.hz.orderOf_eq_two ht.orderOf_eq_two
  have hnormK : conjSub t K = K := conjSub_eq_of_standardPair h2 hW ht.mem ht.orderOf_eq_two
  have hKx : K ∈ centralizingMembers Ω {xM} :=
    mem_centralizingMembers_of_commutes c.hK hxM.mem hKM
  have hβx : β ∈ centralizingMembers Ω {xM} :=
    mem_centralizingMembers_of_commutes hβ hxM.mem hβM
  have hKL := IsLayerMember.of_not_commutes cx hKx hβx hKne hnKβ
  have hβL := IsLayerMember.of_not_commutes cx hβx hKx hKne.symm
    (fun h => hnKβ (commutes_symm h))
  obtain ⟨RK, hRK, hKR⟩ := hKL.exists_fund
  obtain ⟨Rβ, hRβ, hβR⟩ := hβL.exists_fund
  have hadj : ModelAdj (Subgroup.center (modelUniv .POmegaOdd m p f Fact.out).K) RK Rβ :=
    modelAdj_of_adj cx hKx hβx hRK hRβ hKR hβR c.hz ht hKne hnKβ hzt hnormK
  obtain ⟨W', hW'⟩ := linearBlockStandardPair_locImg_of_members cx.hP1 hKx hβx hW
  rw [hKR, hβR] at hW'
  have hF := orthFacts_odd c.hp2 hm4 c.hq
  have hlinR := hF.lift cx.d.ψ cx.d.ker_le RK hRK Rβ hRβ ⟨W', hW'⟩
  have cq := centralQuot_odd (m := m) (f := f) c.hp2 hm3 c.hq
  have hdim : 9 ≤ Module.finrank (GaloisField p f) (Fin m ⊕ Fin m ⊕ Unit → GaloisField p f) := by
    rw [finrank_odd]
    omega
  have hQ : (quadOdd m (GaloisField p f)).Nondegenerate :=
    QuadraticMap.nondegenerate_polar_iff.mp
      (nondegenerate_polarBilin_quadOdd m (GaloisField p f) h2)
  let F₀ : HypFrame (quadOdd m (GaloisField p f)) m := (oddFrame m (GaloisField p f)).toHypFrame
  obtain ⟨x₀, hx0, hx1⟩ := exists_spin_pair_gen c.hp2 c.hq hQ hm4 F₀ hdim cq hRK hRβ hadj hlinR
  let a0 : Fin m := ⟨0, by omega⟩
  let a1 : Fin m := ⟨1, by omega⟩
  have hRfund : ∀ k, dNode hm3 F₀ x₀ k ∈ fundamentalSubgroups .POmegaOdd
      (modelUniv .POmegaOdd m p f Fact.out).D := by
    intro k
    by_cases h : k.val + 1 < m
    · rw [dNode_lt hm3 F₀ x₀ k h]
      exact rootSL2_conj_mem_gen hq4 cq F₀ _ _ _ _ _ x₀
    · rw [dNode_last hm3 F₀ x₀ k h]
      exact rootSL2_conj_mem_gen hq4 cq F₀ _ _ _ _ _ x₀
  obtain ⟨j, hj, hjc, hjp, hjM⟩ := cx.exists_nodes (fun k => dNode hm3 F₀ x₀ k) hRfund
    (fun a b => edgeD m a b) (fun a b hab h1 h2' => commutes_dNode hm3 F₀ x₀ hab h1 h2')
    (fun a b h => stdPair_dNode_odd hm3 x₀ h)
  have hR0 : dNode hm3 F₀ x₀ a0 = RK := by
    rw [dNode_lt hm3 F₀ x₀ a0 (by show 0 + 1 < m; omega)]
    exact hx0.symm
  have hR1 : dNode hm3 F₀ x₀ a1 = Rβ := by
    rw [dNode_lt hm3 F₀ x₀ a1 (by show 1 + 1 < m; omega)]
    exact hx1.symm
  have hex : ∀ a, ∃ w, IsClassicalMember p f (j a) w := fun a =>
    c.hΩ.classical _ (hj a).1.1
  choose w hw using hex
  let nd : DNodes p f m Ω M :=
    { J := j
      w := w
      mem := fun a => (hj a).1.1
      cl := hw
      commK := hjM
      comm := hjc
      pair := hjp }
  let kk : Fin m := ⟨m - 2 + 1, by omega⟩
  let s₀ : spinGroup (quadOdd m (GaloisField p f)) :=
    (oddFrame m (GaloisField p f)).shortRoot kk true (Multiplicative.ofAdd 1)
  let s' : spinGroup (quadOdd m (GaloisField p f)) := x₀ * s₀ * x₀⁻¹
  have hs'x : s' * x₀ = x₀ * s₀ := by simp only [s']; group
  let bn : Fin m := ⟨m - 2, by omega⟩
  let R₁ := conjSub s' (dNode hm3 F₀ x₀ bn)
  have hR₁ : R₁ ∈ fundamentalSubgroups .POmegaOdd (modelUniv .POmegaOdd m p f Fact.out).D :=
    conjSub_mem_fundamentalSubgroups (hRfund bn) s'
  obtain ⟨N₁, hN₁x, hN₁M, -, hN₁R⟩ := cx.exists_member_of_fund hR₁
  have hconjT : ∀ a : Fin m, a.val + 2 < m →
      conjSub s' (dNode hm3 F₀ x₀ a) = dNode hm3 F₀ x₀ a := by
    intro a ha
    have ha1 : a.val + 1 < m := by omega
    have hT : conjSub s₀ (rootSL2 F₀ a.val (a.val + 1) a.isLt ha1 (by omega) true false) =
        rootSL2 F₀ a.val (a.val + 1) a.isLt ha1 (by omega) true false :=
      conjSub_eq_of_mem_of_commutes (Subgroup.mem_zpowers s₀)
        (commutes_zpowers_shortRoot_rootSL2 kk a.isLt ha1 (by omega)
          (by simp only [kk]; omega) (by simp only [kk]; omega) true false true 1)
    rw [dNode_lt hm3 F₀ x₀ a ha1]
    show conjSub s' (conjSub x₀ _) = conjSub x₀ _
    rw [← conjSub_mul, hs'x, conjSub_mul, hT]
  have hR₁eq : R₁ = conjSub x₀ (conjSub s₀
      (rootSL2 F₀ (m - 2) (m - 2 + 1) (by omega) (by omega) (by omega) true false)) := by
    show conjSub s' (dNode hm3 F₀ x₀ bn) = _
    rw [dNode_lt hm3 F₀ x₀ bn (by show m - 2 + 1 < m; omega)]
    show conjSub s' (conjSub x₀ _) = _
    rw [← conjSub_mul, hs'x, conjSub_mul]
  obtain ⟨hne1, hne2⟩ := conjSub_short_ne_rootSL2 c.hodd (oddFrame m (GaloisField p f))
    (a := m - 2) (b := m - 2 + 1) (by omega) (by omega) (by omega)
  have hinjc : ∀ A B : Subgroup (spinGroup (quadOdd m (GaloisField p f))),
      conjSub x₀ A = conjSub x₀ B → A = B := by
    intro A B e
    have := congrArg (conjSub x₀⁻¹) e
    rwa [conjSub_inv_conjSub, conjSub_inv_conjSub] at this
  have hbn : dNode hm3 F₀ x₀ bn = conjSub x₀
      (rootSL2 F₀ (m - 2) (m - 2 + 1) (by omega) (by omega) (by omega) true false) :=
    dNode_lt hm3 F₀ x₀ bn (by show m - 2 + 1 < m; omega)
  let fn : Fin m := ⟨m - 1, by omega⟩
  have hfn : dNode hm3 F₀ x₀ fn = conjSub x₀
      (rootSL2 F₀ (m - 2) (m - 2 + 1) (by omega) (by omega) (by omega) true true) :=
    dNode_last hm3 F₀ x₀ fn (by show ¬ m - 1 + 1 < m; omega)
  have hR₁b : R₁ ≠ dNode hm3 F₀ x₀ bn := by
    intro e
    rw [hR₁eq, hbn] at e
    exact hne1 (hinjc _ _ e)
  have hR₁f : R₁ ≠ dNode hm3 F₀ x₀ fn := by
    intro e
    rw [hR₁eq, hfn] at e
    exact hne2 (hinjc _ _ e)
  have hmodelc : ∀ a : Fin m, a.val + 3 < m → Commutes (dNode hm3 F₀ x₀ a) R₁ := by
    intro a ha
    have h1 : Commutes (dNode hm3 F₀ x₀ a) (dNode hm3 F₀ x₀ bn) :=
      commutes_dNode hm3 F₀ x₀ (fin_ne_of_val_ne (by simp only [bn]; omega))
        (by intro h; unfold edgeD at h; simp only [bn] at h; omega)
        (by intro h; unfold edgeD at h; simp only [bn] at h; omega)
    have h2 := h1.conjSub s'
    rwa [hconjT a (by omega)] at h2
  have hN₁Ω : N₁ ∈ Ω := hN₁x.1
  have hN₁K : Commutes K N₁ := (cx.commutes_iff_fund hKx hN₁x hRK hKR hN₁R).mpr (by
    rw [← hR0]
    exact hmodelc a0 (by show 0 + 3 < m; omega))
  have hN₁β : Commutes β N₁ := (cx.commutes_iff_fund hβx hN₁x hRβ hβR hN₁R).mpr (by
    rw [← hR1]
    exact hmodelc a1 (by show 1 + 3 < m; omega))
  have hN₁Mc : Commutes M N₁ := cx.commutes_K_of_ne hN₁x hN₁M
  have hN₁c : ∀ a (h : a < m), 3 ≤ a → a + 4 ≤ m → Commutes (nd.J ⟨a, h⟩) N₁ :=
    fun a h ha3 ha4 =>
      (cx.commutes_iff_fund (hj ⟨a, h⟩).1 hN₁x (hRfund ⟨a, h⟩) (hj ⟨a, h⟩).2.2.2 hN₁R).mpr
        (hmodelc ⟨a, h⟩ (by show a + 3 < m; omega))
  obtain ⟨W₁, hW₁⟩ : ∃ W, LinearBlockStandardPair (GaloisField p f) W
      (dNode hm3 F₀ x₀ ⟨m - 3, by omega⟩) (dNode hm3 F₀ x₀ bn) :=
    stdPair_dNode_odd hm3 x₀ (a := ⟨m - 3, by omega⟩) (b := bn)
      (Or.inl ⟨by show m - 3 + 1 = m - 2; omega, by show m - 2 + 1 < m; omega⟩)
  have hW₂ : LinearBlockStandardPair (GaloisField p f) _
      (conjSub s' (dNode hm3 F₀ x₀ ⟨m - 3, by omega⟩)) R₁ :=
    CFSG.ClassicalInvolution.ModelFacts.linearBlockStandardPair_map_conj hW₁ s'
  rw [hconjT ⟨m - 3, by omega⟩ (by show m - 3 + 2 < m; omega)] at hW₂
  have hN₁adj : ∃ W, LinearBlockStandardPair (GaloisField p f) W (nd.J ⟨m - 3, by omega⟩) N₁ :=
    cx.stdPair_of_fund (hj ⟨m - 3, by omega⟩).1 hN₁x hW₂ (hj ⟨m - 3, by omega⟩).2.2.2 hN₁R
  have hperf : ∀ R ∈ fundamentalSubgroups .POmegaOdd (oddDatum m (GaloisField p f)),
      ⁅R, R⁆ = R := cq.perf
  have hN₁2 : N₁ ≠ nd.J ⟨m - 2, by omega⟩ := by
    intro e
    have hloc : locImg Ω xM N₁ = locImg Ω xM (j ⟨m - 2, by omega⟩) := by
      rw [show N₁ = j ⟨m - 2, by omega⟩ from e]
    rw [hN₁R, (hj ⟨m - 2, by omega⟩).2.2.2] at hloc
    exact hR₁b (CFSG.ClassicalInvolution.ModelFacts.eq_of_map_eq_of_isPerfect cx.d.ψ
      cx.d.ker_le (hperf _ hR₁) (hperf _ (hRfund bn)) hloc)
  have hN₁1 : N₁ ≠ nd.J ⟨m - 1, by omega⟩ := by
    intro e
    have hloc : locImg Ω xM N₁ = locImg Ω xM (j ⟨m - 1, by omega⟩) := by
      rw [show N₁ = j ⟨m - 1, by omega⟩ from e]
    rw [hN₁R, (hj ⟨m - 1, by omega⟩).2.2.2] at hloc
    exact hR₁f (CFSG.ClassicalInvolution.ModelFacts.eq_of_map_eq_of_isPerfect cx.d.ψ
      cx.d.ker_le (hperf _ hR₁) (hperf _ (hRfund fn)) hloc)
  refine ⟨nd, ?_, ?_, N₁, hN₁Ω, hN₁K, hN₁β, hN₁Mc, hN₁c, hN₁adj, hN₁2, hN₁1⟩
  · exact cx.eq_of_locImg_eq (hj a0).1 hKx (by rw [(hj a0).2.2.2, hR0, hKR])
  · exact cx.eq_of_locImg_eq (hj a1).1 hβx (by rw [(hj a1).2.2.2, hR1, hβR])

end Main

end CFSG.ClassicalInvolution.RouteD.Gaps
