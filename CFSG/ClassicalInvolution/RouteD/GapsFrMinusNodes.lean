module

public import CFSG.ClassicalInvolution.RouteD.GapsFrBNodes
public import CFSG.ClassicalInvolution.RouteD.GapsFrMinusChain

public section

namespace CFSG.ClassicalInvolution.RouteD.Gaps

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.RouteD CFSG.Assembly.LowTwoRank CFSG.LieType CFSG.LieType.RootSystem
  CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.LieType.CurtisTits CFSG.Timmesfeld
open CFSG.ClassicalGroups.Orthogonal QuadraticMap

section Weyl

variable {K : Type} [Field K] {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {n : ℕ}

theorem map_conj_shortWeyl_rootSL2 (k : Fin (n - 1)) {a b' : ℕ} (ha : a < n - 1) (hb : b' < n - 1)
    (hab : a ≠ b') (s t : Bool) :
    (rootSL2 (minusFrame n b c).toHypFrame a b' ha hb hab s t).map
        (MulAut.conj (shortWeyl n hirr k)).toMonoidHom =
      rootSL2 (minusFrame n b c).toHypFrame a b' ha hb hab (shortWeylBool k ⟨a, ha⟩ s)
        (shortWeylBool k ⟨b', hb⟩ t) := by
  have key : ∀ {i j : Fin (n - 1)} (hij : i ≠ j) (s t : Bool),
      ((minusFrame n b c).longRoot hij s t).range.map
          (MulAut.conj (shortWeyl n hirr k)).toMonoidHom =
        ((minusFrame n b c).longRoot hij (shortWeylBool k i s) (shortWeylBool k j t)).range := by
    intro i j hij s t
    have hε : (longWeylSign k i : K) * longWeylSign k j ≠ 0 := by
      unfold longWeylSign
      split_ifs <;> simp
    ext y
    constructor
    · rintro ⟨_, ⟨c', rfl⟩, rfl⟩
      refine ⟨Multiplicative.ofAdd ((longWeylSign k i : K) * longWeylSign k j *
        Multiplicative.toAdd c'), ?_⟩
      exact (shortWeyl_conj_longRoot n hirr k hij s t (Multiplicative.toAdd c')).symm
    · rintro ⟨c', rfl⟩
      refine ⟨_, ⟨Multiplicative.ofAdd (((longWeylSign k i : K) * longWeylSign k j)⁻¹ *
        Multiplicative.toAdd c'), rfl⟩, ?_⟩
      have h := shortWeyl_conj_longRoot n hirr k hij s t
        (((longWeylSign k i : K) * longWeylSign k j)⁻¹ * Multiplicative.toAdd c')
      rw [← mul_assoc, mul_inv_cancel₀ hε, one_mul] at h
      exact h
  have hnot : ∀ (j : Fin (n - 1)) (t : Bool), shortWeylBool k j (!t) = !(shortWeylBool k j t) := by
    intro j t
    unfold shortWeylBool
    split_ifs <;> simp
  have hij : (⟨a, ha⟩ : Fin (n - 1)) ≠ ⟨b', hb⟩ := fun h => hab (congrArg Fin.val h)
  unfold rootSL2
  rw [longSL2_range_eq_sup, longSL2_range_eq_sup, Subgroup.map_sup, key hij s t,
    key hij.symm (!t) (!s), hnot, hnot]

end Weyl

section Std

variable {p f : ℕ} [Fact p.Prime] {m : ℕ}

theorem stdPair_dNode_minus (hm : 5 ≤ m) (hp2 : p ≠ 2)
    (x : spinGroup (quadMinus m (GaloisField p f) (minusCoeffs p f).1 (minusCoeffs p f).2))
    {a b : Fin (m - 1)} (h : edgeD (m - 1) a b) :
    ∃ W, LinearBlockStandardPair (GaloisField p f) W
      (dNode (by omega : 3 ≤ m - 1)
        (minusFrame m (minusCoeffs p f).1 (minusCoeffs p f).2).toHypFrame x a)
      (dNode (by omega : 3 ≤ m - 1)
        (minusFrame m (minusCoeffs p f).1 (minusCoeffs p f).2).toHypFrame x b) := by
  have hm3 : 3 ≤ m - 1 := by omega
  have hirr := minusCoeffs_irr p f
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f hp2
  unfold edgeD at h
  rcases h with ⟨h1, h2'⟩ | ⟨h1, h2'⟩
  ·
    have ha : a.val + 1 < m - 1 := by omega
    rw [dNode_lt hm3 _ x a ha, dNode_lt hm3 _ x b h2']
    obtain ⟨W₁, hW₁⟩ := linearBlockStandardPair_minusDatum hirr h2 (by omega : 4 ≤ m) (i := a)
      (j := b) h1 h2'
    rw [rankOne_minusDatum_of_lt hirr ha, rankOne_minusDatum_of_lt hirr h2'] at hW₁
    exact ⟨_, CFSG.ClassicalInvolution.ModelFacts.linearBlockStandardPair_map_conj hW₁ x⟩
  ·
    have ha : a.val + 1 < m - 1 := by omega
    have hb : ¬ b.val + 1 < m - 1 := by omega
    rw [dNode_lt hm3 _ x a ha, dNode_last hm3 _ x b hb]
    obtain ⟨W₁, hW₁⟩ := linearBlockStandardPair_minusDatum hirr h2 (by omega : 4 ≤ m)
      (i := (⟨m - 4, by omega⟩ : Fin (m - 1))) (j := (⟨m - 3, by omega⟩ : Fin (m - 1)))
      (by show m - 4 + 1 = m - 3; omega) (by show m - 3 + 1 < m - 1; omega)
    let k : Fin (m - 1) := ⟨m - 2, by omega⟩
    rw [rankOne_minusDatum_of_lt hirr (by show m - 4 + 1 < m - 1; omega),
      rankOne_minusDatum_of_lt hirr (by show m - 3 + 1 < m - 1; omega)] at hW₁
    have hW₂ := CFSG.ClassicalInvolution.ModelFacts.linearBlockStandardPair_map_conj hW₁
      (shortWeyl m hirr k)
    rw [map_conj_shortWeyl_rootSL2 hirr k, map_conj_shortWeyl_rootSL2 hirr k] at hW₂
    rw [shortWeylBool_of_ne (by simp [k, Fin.ext_iff]; omega),
      shortWeylBool_of_ne (by simp [k, Fin.ext_iff]; omega),
      shortWeylBool_of_ne (by simp [k, Fin.ext_iff]; omega)] at hW₂
    have e : ∀ j : Fin (m - 1), j.val = m - 2 → shortWeylBool k j false = true := fun j hj => by
      have : j = k := Fin.ext (by simp [k, hj])
      rw [this, shortWeylBool_self]
      rfl
    rw [e _ (by simp; omega)] at hW₂
    have e1 := rootSL2_congr (minusFrame m (minusCoeffs p f).1 (minusCoeffs p f).2).toHypFrame
      a.isLt ha (by omega) (by omega : m - 4 < m - 1) (by omega : m - 4 + 1 < m - 1) (by omega)
      (by omega : a.val = m - 4) (by omega : a.val + 1 = m - 4 + 1) true false
    rw [e1]
    exact ⟨_, CFSG.ClassicalInvolution.ModelFacts.linearBlockStandardPair_map_conj hW₂ x⟩

end Std



section Main

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G}

theorem exists_dnodes_of_pair_minus {m : ℕ} (hm : 6 ≤ m) (c : TCtx p f .POmegaMinus m Ω K z)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hshape : LocalShapeT p f 2 .POmegaMinus m Ω z) {β : Subgroup G} {t : G} (hβ : β ∈ Ω)
    (ht : IsClassicalMember p f β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField p f) W K β) {M : Subgroup G} (hMΩ : M ∈ Ω)
    (hKM : Commutes K M) (hβM : Commutes β M) :
    ∃ nd : DNodes p f (m - 1) Ω M, nd.J ⟨0, by omega⟩ = K ∧ nd.J ⟨1, by omega⟩ = β := by
  classical
  have hm3 : 3 ≤ m - 1 := by omega
  have hm4 : 4 ≤ m - 1 := by omega
  have hm5 : 5 ≤ m := by omega
  have hq4 : 4 ≤ p ^ f := by have := c.hq; omega
  have hf1 : 1 ≤ f := Nat.one_le_iff_ne_zero.mpr c.hf
  have hadm : StatedLieAdmissible .POmegaMinus m p f := ⟨Fact.out, hf1, by show 4 ≤ m; omega⟩
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
  have hadj : ModelAdj (Subgroup.center (modelUniv .POmegaMinus m p f Fact.out).K) RK Rβ :=
    modelAdj_of_adj cx hKx hβx hRK hRβ hKR hβR c.hz ht hKne hnKβ hzt hnormK
  obtain ⟨W', hW'⟩ := linearBlockStandardPair_locImg_of_members cx.hP1 hKx hβx hW
  rw [hKR, hβR] at hW'
  have hF := orthFacts_minus c.hp2 hm5 c.hq
  have hlinR := hF.lift cx.d.ψ cx.d.ker_le RK hRK Rβ hRβ ⟨W', hW'⟩
  have cq := Exotic.centralQuot_minus c.hp2 c.hq hadm
  have hdim : 9 ≤ Module.finrank (GaloisField p f)
      (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → GaloisField p f) := by
    rw [finrank_minus p f m (by omega)]
    omega
  have hQ : (quadMinus m (GaloisField p f) (minusCoeffs p f).1 (minusCoeffs p f).2).Nondegenerate :=
    QuadraticMap.nondegenerate_polar_iff.mp
      (nondegenerate_polarBilin_quadMinus_of_finite m (GaloisField p f) (minusCoeffs_irr p f))
  let F₀ : HypFrame (quadMinus m (GaloisField p f) (minusCoeffs p f).1 (minusCoeffs p f).2)
      (m - 1) := (minusFrame m (minusCoeffs p f).1 (minusCoeffs p f).2).toHypFrame
  obtain ⟨x₀, hx0, hx1⟩ := exists_spin_pair_gen c.hp2 c.hq hQ hm4 F₀ hdim cq hRK hRβ hadj hlinR
  let a0 : Fin (m - 1) := ⟨0, by omega⟩
  let a1 : Fin (m - 1) := ⟨1, by omega⟩
  have hRfund : ∀ k, dNode hm3 F₀ x₀ k ∈ fundamentalSubgroups .POmegaMinus
      (modelUniv .POmegaMinus m p f Fact.out).D := by
    intro k
    by_cases h : k.val + 1 < m - 1
    · rw [dNode_lt hm3 F₀ x₀ k h]
      exact rootSL2_conj_mem_gen hq4 cq F₀ _ _ _ _ _ x₀
    · rw [dNode_last hm3 F₀ x₀ k h]
      exact rootSL2_conj_mem_gen hq4 cq F₀ _ _ _ _ _ x₀
  obtain ⟨j, hj, hjc, hjp, hjM⟩ := cx.exists_nodes (fun k => dNode hm3 F₀ x₀ k) hRfund
    (fun a b => edgeD (m - 1) a b) (fun a b hab h1 h2' => commutes_dNode hm3 F₀ x₀ hab h1 h2')
    (fun a b h => stdPair_dNode_minus hm5 c.hp2 x₀ h)
  have hR0 : dNode hm3 F₀ x₀ a0 = RK := by
    rw [dNode_lt hm3 F₀ x₀ a0 (by show 0 + 1 < m - 1; omega)]
    exact hx0.symm
  have hR1 : dNode hm3 F₀ x₀ a1 = Rβ := by
    rw [dNode_lt hm3 F₀ x₀ a1 (by show 1 + 1 < m - 1; omega)]
    exact hx1.symm
  have hex : ∀ a, ∃ w, IsClassicalMember p f (j a) w := fun a =>
    c.hΩ.classical _ (hj a).1.1
  choose w hw using hex
  let nd : DNodes p f (m - 1) Ω M :=
    { J := j
      w := w
      mem := fun a => (hj a).1.1
      cl := hw
      commK := hjM
      comm := hjc
      pair := hjp }
  refine ⟨nd, ?_, ?_⟩
  · exact cx.eq_of_locImg_eq (hj a0).1 hKx (by rw [(hj a0).2.2.2, hR0, hKR])
  · exact cx.eq_of_locImg_eq (hj a1).1 hβx (by rw [(hj a1).2.2.2, hR1, hβR])

end Main

end CFSG.ClassicalInvolution.RouteD.Gaps
