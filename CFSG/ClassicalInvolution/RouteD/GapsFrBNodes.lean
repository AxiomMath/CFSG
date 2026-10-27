module

public import CFSG.ClassicalInvolution.RouteD.GapsFrBRel
public import CFSG.ClassicalInvolution.RouteD.GapsFrOdd
public import CFSG.ClassicalInvolution.RouteD.GapsPatternD

public section

namespace CFSG.ClassicalInvolution.RouteD.Gaps

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.LieType CFSG.LieType.RootSystem CFSG.LieType.Universal
  CFSG.LieType.Universal.Spin CFSG.LieType.CurtisTits CFSG.Timmesfeld
open CFSG.ClassicalGroups.Orthogonal QuadraticMap

section DNode

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V} {m : ℕ}

@[expose] noncomputable def dNode (hm : 3 ≤ m) (F₀ : HypFrame Q m) (x : spinGroup Q) (k : Fin m) :
    Subgroup (spinGroup Q) :=
  if h : k.val + 1 < m then
    (rootSL2 F₀ k.val (k.val + 1) k.isLt h (by omega) true false).map (MulAut.conj x).toMonoidHom
  else
    (rootSL2 F₀ (m - 2) (m - 2 + 1) (by omega) (by omega) (by omega) true true).map
      (MulAut.conj x).toMonoidHom

theorem dNode_lt (hm : 3 ≤ m) (F₀ : HypFrame Q m) (x : spinGroup Q) (k : Fin m)
    (h : k.val + 1 < m) : dNode hm F₀ x k =
      (rootSL2 F₀ k.val (k.val + 1) k.isLt h (by omega) true false).map
        (MulAut.conj x).toMonoidHom := by
  simp [dNode, h]

theorem dNode_last (hm : 3 ≤ m) (F₀ : HypFrame Q m) (x : spinGroup Q) (k : Fin m)
    (h : ¬ k.val + 1 < m) : dNode hm F₀ x k =
      (rootSL2 F₀ (m - 2) (m - 2 + 1) (by omega) (by omega) (by omega) true true).map
        (MulAut.conj x).toMonoidHom := by
  simp [dNode, h]

theorem commutes_dNode (hm : 3 ≤ m) (F₀ : HypFrame Q m) (x : spinGroup Q) {a b : Fin m}
    (hab : a ≠ b) (h1 : ¬ edgeD m a b) (h2 : ¬ edgeD m b a) :
    Commutes (dNode hm F₀ x a) (dNode hm F₀ x b) := by
  unfold edgeD at h1 h2
  have hab' : a.val ≠ b.val := fun e => hab (Fin.ext e)
  have av := a.isLt
  have bv := b.isLt
  by_cases ha : a.val + 1 < m
  · by_cases hb : b.val + 1 < m
    · rw [dNode_lt hm F₀ x a ha, dNode_lt hm F₀ x b hb]
      exact (commutes_rootSL2_disjoint F₀ a.isLt ha b.isLt hb (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) true false true false).conjSub x
    · rw [dNode_lt hm F₀ x a ha, dNode_last hm F₀ x b hb]
      by_cases hae : a.val = m - 2
      · have e1 := rootSL2_congr F₀ a.isLt ha (by omega) (by omega : m - 2 < m)
          (by omega : m - 2 + 1 < m) (by omega) hae (by omega : a.val + 1 = m - 2 + 1) true false
        rw [e1]
        exact (commutes_rootSL2_twin F₀ (by omega) (by omega) (by omega) true).conjSub x
      · exact (commutes_rootSL2_disjoint F₀ a.isLt ha (by omega : m - 2 < m)
          (by omega : m - 2 + 1 < m) (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega) true false true true).conjSub x
  · by_cases hb : b.val + 1 < m
    · rw [dNode_last hm F₀ x a ha, dNode_lt hm F₀ x b hb]
      by_cases hbe : b.val = m - 2
      · have e1 := rootSL2_congr F₀ b.isLt hb (by omega) (by omega : m - 2 < m)
          (by omega : m - 2 + 1 < m) (by omega) hbe (by omega : b.val + 1 = m - 2 + 1) true false
        rw [e1]
        exact (commutes_rootSL2_twin F₀ (by omega) (by omega) (by omega) true).symm.conjSub x
      · exact (commutes_rootSL2_disjoint F₀ b.isLt hb (by omega : m - 2 < m)
          (by omega : m - 2 + 1 < m) (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega) true false true true).symm.conjSub x
    · exact absurd (Fin.ext (by omega)) hab

end DNode


section Std

variable {p f : ℕ} [Fact p.Prime] {m : ℕ}

theorem shortWeylBool_of_ne {n : ℕ} {i j : Fin n} (h : j ≠ i) (r : Bool) :
    shortWeylBool i j r = r := by
  simp [shortWeylBool, h]

theorem shortWeylBool_self {n : ℕ} (i : Fin n) (r : Bool) : shortWeylBool i i r = !r := by
  simp [shortWeylBool]

theorem stdPair_dNode_odd (hm3 : 3 ≤ m) (x : spinGroup (quadOdd m (GaloisField p f)))
    {a b : Fin m} (h : edgeD m a b) :
    ∃ W, LinearBlockStandardPair (GaloisField p f) W
      (dNode hm3 (oddFrame m (GaloisField p f)).toHypFrame x a)
      (dNode hm3 (oddFrame m (GaloisField p f)).toHypFrame x b) := by
  unfold edgeD at h
  rcases h with ⟨h1, h2'⟩ | ⟨h1, h2'⟩
  ·
    have ha : a.val + 1 < m := by omega
    rw [dNode_lt hm3 _ x a ha, dNode_lt hm3 _ x b h2']
    obtain ⟨W₁, hW₁⟩ := standardPair_oddDatum_edge' (F := GaloisField p f) hm3
      (i := (⟨a.val, by show a.val < m; omega⟩ : Fin m))
      (j := (⟨b.val, by show b.val < m; omega⟩ : Fin m)) h1 (by show b.val + 1 < m; omega)
    rw [rankOne_oddDatum_of_lt ha, rankOne_oddDatum_of_lt h2'] at hW₁
    exact ⟨_, CFSG.ClassicalInvolution.ModelFacts.linearBlockStandardPair_map_conj hW₁ x⟩
  ·
    have ha : a.val + 1 < m := by omega
    have hb : ¬ b.val + 1 < m := by omega
    rw [dNode_lt hm3 _ x a ha, dNode_last hm3 _ x b hb]
    obtain ⟨W₁, hW₁⟩ := standardPair_oddDatum_edge' (F := GaloisField p f) hm3
      (i := (⟨m - 3, by show m - 3 < m; omega⟩ : Fin m))
      (j := (⟨m - 2, by show m - 2 < m; omega⟩ : Fin m)) (by show m - 3 + 1 = m - 2; omega)
      (by show m - 2 + 1 < m; omega)
    let k : Fin m := ⟨m - 1, by omega⟩
    have hk : ¬ k.val + 1 < m := by
      show ¬ m - 1 + 1 < m
      omega
    rw [rankOne_oddDatum_of_lt (by show m - 3 + 1 < m; omega),
      rankOne_oddDatum_of_lt (by show m - 2 + 1 < m; omega)] at hW₁
    have hW₂ := CFSG.ClassicalInvolution.ModelFacts.linearBlockStandardPair_map_conj hW₁
      (weylB (GaloisField p f) k)
    rw [map_conj_weylB_rootSL2 hk, map_conj_weylB_rootSL2 hk] at hW₂
    rw [shortWeylBool_of_ne (by simp [k, Fin.ext_iff]; omega),
      shortWeylBool_of_ne (by simp [k, Fin.ext_iff]; omega),
      shortWeylBool_of_ne (by simp [k, Fin.ext_iff]; omega)] at hW₂
    have e : ∀ j : Fin m, j.val = m - 1 → shortWeylBool k j false = true := fun j hj => by
      have : j = k := Fin.ext (by simp [k, hj])
      rw [this, shortWeylBool_self]
      rfl
    rw [e _ (by simp; omega)] at hW₂
    have e1 := rootSL2_congr (oddFrame m (GaloisField p f)).toHypFrame a.isLt ha (by omega)
      (by omega : m - 3 < m) (by omega : m - 3 + 1 < m) (by omega) (by omega : a.val = m - 3)
      (by omega : a.val + 1 = m - 3 + 1) true false
    rw [e1]
    exact ⟨_, CFSG.ClassicalInvolution.ModelFacts.linearBlockStandardPair_map_conj hW₂ x⟩

end Std


section Main

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G}

theorem exists_dnodes_of_pair_odd {m : ℕ} (hm : 5 ≤ m) (c : TCtx p f .POmegaOdd m Ω K z)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hshape : LocalShapeT p f 2 .POmegaOdd m Ω z) {β : Subgroup G} {t : G} (hβ : β ∈ Ω)
    (ht : IsClassicalMember p f β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField p f) W K β) {M : Subgroup G} (hMΩ : M ∈ Ω)
    (hKM : Commutes K M) (hβM : Commutes β M) :
    ∃ nd : DNodes p f m Ω M, nd.J ⟨0, by omega⟩ = K ∧ nd.J ⟨1, by omega⟩ = β := by
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
  refine ⟨nd, ?_, ?_⟩
  · exact cx.eq_of_locImg_eq (hj a0).1 hKx (by rw [(hj a0).2.2.2, hR0, hKR])
  · exact cx.eq_of_locImg_eq (hj a1).1 hβx (by rw [(hj a1).2.2.2, hR1, hβR])

end Main

end CFSG.ClassicalInvolution.RouteD.Gaps
