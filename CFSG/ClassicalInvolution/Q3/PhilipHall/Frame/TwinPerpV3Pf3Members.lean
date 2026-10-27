module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdgeSecDatum
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.SectionIH
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3PfBase
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3PfDefs
public import CFSG.ClassicalInvolution.SmallCases.A7T22Main

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
open scoped commutatorElement

theorem q8_exists_diff {n : ℕ} [NeZero n] (hn : 2 * n = 4) (b : QuaternionGroup n) :
    ∃ p q : QuaternionGroup n, orderOf p = 4 ∧ orderOf q = 4 ∧ p⁻¹ * q = b := by
  cases b with
  | a i =>
    refine ⟨QuaternionGroup.xa 0, QuaternionGroup.xa 0 * QuaternionGroup.a i,
      QuaternionGroup.orderOf_xa _, ?_, by group⟩
    rw [QuaternionGroup.xa_mul_a]
    exact QuaternionGroup.orderOf_xa _
  | xa i =>
    refine ⟨QuaternionGroup.a 1, QuaternionGroup.a 1 * QuaternionGroup.xa i, ?_, ?_, by group⟩
    · rw [QuaternionGroup.orderOf_a_one, hn]
    · rw [QuaternionGroup.a_mul_xa]
      exact QuaternionGroup.orderOf_xa _

section Comm

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K K' K₃ : Subgroup G}
  {t u₁ u₂ u₃ : G}

theorem oddCore_comm_of_alpha1 (hα : A7T22.AlphaConst Ω t)
    (hd : A7T22.Hyp22G Ω K K' K₃ t u₁ u₂ u₃)
    (hα1 : alphaOf (Subgroup.closure ({u₁ * u₂, t} : Set G)) = ⊥)
    {L L' L₃ : Subgroup G} {x y w : G} (hd' : A7T22.Hyp22G Ω L L' L₃ t x y w) :
    ∀ g ∈ oddCoreOf (Subgroup.centralizer ({t} : Set G)), g * (x * y) = (x * y) * g := by
  intro g hg
  have heq := hd.alpha_eq_of_datum hα hd'
  have hα' : alphaOf (Subgroup.closure ({x * y, t} : Set G)) = ⊥ := by rw [← heq]; exact hα1
  have hxy : x * y ∈ Subgroup.closure ({x * y, t} : Set G) := Subgroup.subset_closure (by simp)
  have ht : t ∈ Subgroup.closure ({x * y, t} : Set G) := Subgroup.subset_closure (by simp)
  have hc : ⁅g, x * y⁆ ∈ ⁅oddCoreOf (Subgroup.centralizer ({t} : Set G)),
      Subgroup.closure ({x * y, t} : Set G)⁆ := Subgroup.commutator_mem_commutator hg hxy
  have hle : ⁅oddCoreOf (Subgroup.centralizer ({t} : Set G)),
      Subgroup.closure ({x * y, t} : Set G)⁆ ≤ alphaOf (Subgroup.closure ({x * y, t} : Set G)) := by
    unfold alphaOf
    refine le_sup_of_le_left ?_
    exact le_iSup₂_of_le t ht
      (le_iSup (fun _ : t ≠ 1 => ⁅oddCoreOf (Subgroup.centralizer ({t} : Set G)),
        Subgroup.closure ({x * y, t} : Set G)⁆) hd.hz.ne_one)
  have := hle hc
  rw [hα', Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
  exact this

theorem oddCore_centralizes_twoElt (hα : A7T22.AlphaConst Ω t)
    (hd : A7T22.Hyp22G Ω K K' K₃ t u₁ u₂ u₃)
    (hα1 : alphaOf (Subgroup.closure ({u₁ * u₂, t} : Set G)) = ⊥)
    (hcard8 : ∀ P : Subgroup G, IsSylow2In P K → Nat.card ↥P = 8)
    {a : G} (ha : a ∈ K) (ha2 : IsPGroup 2 (Subgroup.zpowers a)) :
    ∀ g ∈ oddCoreOf (Subgroup.centralizer ({t} : Set G)), g * a = a * g := by
  intro g hg
  have hΩ := hd.hyp
  obtain ⟨R₁, hR₁, hzle⟩ := IsSylow2In.exists_ge ha2 (Subgroup.zpowers_le.mpr ha)
  have haR : a ∈ R₁ := hzle (Subgroup.mem_zpowers a)
  have hR₁N : R₁ ≤ Subgroup.normalizer (K' : Set G) :=
    hR₁.1.trans (Sec6Gen.le_normalizer_of_twin hΩ hd.mem hd.hK'.1 hd.hne.symm hd.hz hd.hzK')
  obtain ⟨R₂, hR₂, hfix₂⟩ := exists_sylow_normalized hR₁.2.1 hR₁N
  have hR₁R₂ : R₁ ≤ Subgroup.normalizer (R₂ : Set G) := fun r hr =>
    mem_normalizer_iff_conjSub_eq.mpr (hfix₂ r hr)
  have hP : IsPGroup 2 ↥(R₁ ⊔ R₂) := hR₁.2.1.to_sup_of_normal_right' hR₂.2.1 hR₁R₂
  have c12 : Commutes R₁ R₂ :=
    Sec6Gen.commutes_of_twin_of_isPGroup hΩ hd.mem hd.hK'.1 hd.hne.symm hd.hz hd.hzK' hR₁.1 hR₂.1 hP
  obtain ⟨y, hyR, hy4⟩ := A7T22.exists_orderOf_eq_four_of_isSylow2In hΩ hd.hK'.1 hR₂
  obtain ⟨k, -, ⟨e⟩⟩ := Sec6Gen.isQuatSub_of_mem_RSet hΩ (mem_RSet_of_isSylow2In hd.mem hR₁)
  have : NeZero (2 ^ k) := ⟨pow_ne_zero k two_ne_zero⟩
  have hcardR := hcard8 R₁ hR₁
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card] at hcardR
  have hn : 2 * 2 ^ k = 4 := by omega
  obtain ⟨p, q, hp, hq, hpq⟩ := q8_exists_diff hn (e ⟨a, haR⟩)
  set x : G := ((e.symm p : R₁) : G) with hxdef
  set x' : G := ((e.symm q : R₁) : G) with hx'def
  have hxR : x ∈ R₁ := (e.symm p).2
  have hx'R : x' ∈ R₁ := (e.symm q).2
  have hx4 : orderOf x = 4 := by rw [hxdef, Subgroup.orderOf_coe, MulEquiv.orderOf_eq]; exact hp
  have hx'4 : orderOf x' = 4 := by rw [hx'def, Subgroup.orderOf_coe, MulEquiv.orderOf_eq]; exact hq
  have hxx' : x⁻¹ * x' = a := by
    have h1 : (e.symm p)⁻¹ * e.symm q = ⟨a, haR⟩ := by
      rw [← map_inv, ← map_mul, hpq]; simp
    have := congrArg (fun r : R₁ => (r : G)) h1
    simpa [hxdef, hx'def] using this
  have hKK : K ∈ twinSet Ω K := mem_twinSet_self hd.mem hd.hz
  obtain ⟨L₃, w, hd1⟩ := hd.exists_datum_of_pair hKK hd.hK' hd.hne hR₁ hR₂ c12 hxR hyR hx4 hy4
  obtain ⟨L₃', w', hd2⟩ := hd.exists_datum_of_pair hKK hd.hK' hd.hne hR₁ hR₂ c12 hx'R hyR hx'4 hy4
  have g1 := oddCore_comm_of_alpha1 hα hd hα1 hd1 g hg
  have g2 := oddCore_comm_of_alpha1 hα hd hα1 hd2 g hg
  have hcom : Commute g (x * y)⁻¹ ∧ True := ⟨(show Commute g (x * y) from g1).inv_right, trivial⟩
  have hc3 : Commute g ((x * y)⁻¹ * (x' * y)) :=
    hcom.1.mul_right (show Commute g (x' * y) from g2)
  have hay : a * y = y * a := c12 a haR y hyR
  have e2 : (x * y)⁻¹ * (x' * y) = a := by
    have : (x * y)⁻¹ * (x' * y) = y⁻¹ * (x⁻¹ * x') * y := by group
    rw [this, hxx']
    calc y⁻¹ * a * y = y⁻¹ * (a * y) := by group
      _ = y⁻¹ * (y * a) := by rw [hay]
      _ = a := by group
  rw [e2] at hc3
  exact hc3.eq

end Comm

section Members

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem oddCore_centralizes_core (hV : V3Hyp51B n) (h : PerpHypS n Y R S t) (h3 : ¬ TwoTwins R)
    (hE : ¬ TwinE4 Y) {K' K₃ : Subgroup Y} {u₁ u₂ u₃ : Y}
    (hd : A7T22.Hyp22G (CoreAssembly.conjClass (tightCore R)) (tightCore R) K' K₃ t u₁ u₂ u₃)
    (hα1 : alphaOf (Subgroup.closure ({u₁ * u₂, t} : Set Y)) = ⊥) :
    ∀ g ∈ oddCoreOf (Subgroup.centralizer ({t} : Set Y)), ∀ k ∈ tightCore R,
      g * k = k * g := by
  have hC := CoreData.of_S h.core
  have hα := alphaConst hV h h3 hE
  have hΩ := hC.hyp
  have hmem : tightCore R ∈ CoreAssembly.conjClass (tightCore R) :=
    CoreAssembly.mem_conjClass_self _
  have hcard8 : ∀ P : Subgroup Y, IsSylow2In P (tightCore R) → Nat.card ↥P = 8 := by
    intro P hP
    have hS' : IsSylow2In ((S : Subgroup R).map R.subtype) (tightCore R) := hC.datum.sylow_core
    have hc : Nat.card ↥((S : Subgroup R).map R.subtype) = 8 := by
      obtain ⟨e⟩ := hC.q8
      rw [← Nat.card_congr (Subgroup.equivMapOfInjective (S : Subgroup R) R.subtype
        R.subtype_injective).toEquiv, Nat.card_congr e.toEquiv]
      simp [QuaternionGroup.card]
    rw [← hc]
    exact hΩ.omega3 _ hmem _ hmem P _ hP hS'
  intro g hg
  have : tightCore R ≤ Subgroup.centralizer ({g} : Set Y) := by
    refine (Subgroup.closure_le _).mpr fun x hx => ?_
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    exact (oddCore_centralizes_twoElt hα hd hα1 hcard8 (Subgroup.subset_closure hx) hx.2 g hg).symm
  intro k hk
  exact (Subgroup.mem_centralizer_singleton_iff.mp (this hk)).symm

theorem members_isPGroup_of_alpha1 (hV : V3Hyp51B n) (h : PerpHypS n Y R S t) (h3 : ¬ TwoTwins R)
    (hE : ¬ TwinE4 Y) {K' K₃ : Subgroup Y} {u₁ u₂ u₃ : Y}
    (hd : A7T22.Hyp22G (CoreAssembly.conjClass (tightCore R)) (tightCore R) K' K₃ t u₁ u₂ u₃)
    (hα1 : alphaOf (Subgroup.closure ({u₁ * u₂, t} : Set Y)) = ⊥) :
    ∀ J ∈ CoreAssembly.conjClass (tightCore R), IsPGroup 2 ↥J := by
  have hC := CoreData.of_S h.core
  have hΩ := hC.hyp
  have hmem : tightCore R ∈ CoreAssembly.conjClass (tightCore R) :=
    CoreAssembly.mem_conjClass_self _
  have hU : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hθ := oddCore_centralizes_core hV h h3 hE hd hα1
  have hcent : classicalInvolutionOddCore ↥(tightCore R) ≤ Subgroup.center ↥(tightCore R) := by
    intro m hm
    have hsub : Balance.oddCoreIn (tightCore R) ≤
        Balance.oddCoreIn (Subgroup.centralizer ({t} : Set Y)) :=
      Balance.oddCoreIn_le_of_isSubnormal (isSubnormal_of_hypOmegaGen hΩ hmem hU)
    have hmem' : (m : Y) ∈ Balance.oddCoreIn (tightCore R) := ⟨m, hm, rfl⟩
    have hmθ := hsub hmem'
    rw [Subgroup.mem_center_iff]
    intro k
    exact Subtype.ext (hθ _ hmθ k k.2).symm
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2q : IsPGroup 2 (↥(tightCore R) ⧸ classicalInvolutionOddCore ↥(tightCore R)) :=
    TwinEdge.isPGroup_two_quotient_of_le (tightCore_le R) hC.datum.twoGroup
  have : Group.IsNilpotent (↥(tightCore R) ⧸ classicalInvolutionOddCore ↥(tightCore R)) :=
    h2q.isNilpotent
  have : Group.IsNilpotent ↥(tightCore R) :=
    Subgroup.isNilpotent_of_ker_le_center (QuotientGroup.mk' (classicalInvolutionOddCore ↥(tightCore R)))
      (by rw [QuotientGroup.ker_mk']; exact hcent)
  obtain ⟨P⟩ : Nonempty (Sylow 2 ↥(tightCore R)) := inferInstance
  have : Subsingleton (Sylow 2 ↥(tightCore R)) := (Sylow.unique_of_normal P inferInstance).instSubsingleton
  have hP2 : ∀ x : ↥(tightCore R), IsPGroup 2 (Subgroup.zpowers x) → x ∈ P := by
    intro x hx
    obtain ⟨Q, hQ⟩ := hx.exists_le_sylow
    rw [Subsingleton.elim Q P] at hQ
    exact hQ (Subgroup.mem_zpowers x)
  have hK2 : IsPGroup 2 ↥(tightCore R) := by
    have hle : tightCore R ≤ (P : Subgroup ↥(tightCore R)).map (tightCore R).subtype := by
      refine (Subgroup.closure_le _).mpr fun x hx => ?_
      have hxK : x ∈ tightCore R := Subgroup.subset_closure hx
      refine ⟨⟨x, hxK⟩, hP2 _ ?_, rfl⟩
      obtain ⟨m, hm⟩ := hx.2 ⟨x, Subgroup.mem_zpowers x⟩
      have : (⟨x, hxK⟩ : ↥(tightCore R)) ^ 2 ^ m = 1 := by
        apply Subtype.ext
        have := congrArg Subtype.val hm
        simpa using this
      exact OddQuot.isPGroup_zpowers_of_pow this
    intro k
    obtain ⟨p, hp, hpk⟩ := hle k.2
    have hpk' : p = k := Subtype.ext hpk
    subst hpk'
    obtain ⟨m, hm⟩ := P.isPGroup' ⟨p, hp⟩
    exact ⟨m, by simpa using congrArg Subtype.val hm⟩
  rintro _ ⟨g, rfl⟩
  exact isPGroup_conjSub g hK2

theorem members_isPGroup_of_std (hV : V3Hyp51B n) {K K' K₃ : Subgroup Y} {u₁ u₂ u₃ : Y}
    (hStd : V3Std n Y R S t K K' K₃ u₁ u₂ u₃)
    (hα1 : alphaOf (Subgroup.closure ({u₁ * u₂, t} : Set Y)) = ⊥) :
    ∀ J ∈ CoreAssembly.conjClass (tightCore R), IsPGroup 2 ↥J := by
  have hd := hStd.datum
  have hα := alphaConst hV hStd.perp hStd.two hStd.exit
  obtain ⟨K'', K₃', v₁, v₂, v₃, hd0⟩ := exists_hyp22G hStd.perp hStd.two
  have hα0 : alphaOf (Subgroup.closure ({v₁ * v₂, t} : Set Y)) = ⊥ := by
    rw [← hd.alpha_eq_of_datum hα hd0]; exact hα1
  exact members_isPGroup_of_alpha1 hV hStd.perp hStd.two hStd.exit hd0 hα0

end Members

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
