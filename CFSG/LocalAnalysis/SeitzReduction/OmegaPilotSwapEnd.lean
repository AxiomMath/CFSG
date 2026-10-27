module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotSwapParam
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotSwapFamily
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotNotLongRoot

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup CFSG.Open
open CFSG.Quasithin (perfectCore perfectCore_le)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (coordinateQuadPlus coordinateQuadMinus plusIndexEquiv minusIndexEquiv)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.SeitzQ2 (SwapParam SwapPairExclusion)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)

section Transport

variable {G : Type} [Group G] {L : Subgroup G} {P : Type} [Group P] (e : L ≃* P)

theorem modelToG_inf (A B : Subgroup P) :
    modelToG e (A ⊓ B) = modelToG e A ⊓ modelToG e B := by
  rw [UnitaryPilot.modelToG_def, UnitaryPilot.modelToG_def, UnitaryPilot.modelToG_def,
    Subgroup.map_inf_eq _ _ _ e.symm.injective, Subgroup.map_inf_eq _ _ _ L.subtype_injective]

theorem modelToG_inf_centralizer (A B : Subgroup P) :
    modelToG e A ⊓ centralizer (modelToG e B : Set G) =
      modelToG e (A ⊓ centralizer (B : Set P)) := by
  rw [modelToG_inf, ← UnitaryPilot.inf_centralizer_modelToG, ← inf_assoc,
    inf_eq_left.2 (UnitaryPilot.modelToG_le e A)]

theorem perfectCore_modelToG [Finite G] (H : Subgroup P) :
    perfectCore (modelToG e H) = modelToG e (perfectCore H) := by
  have : Finite P := Finite.of_equiv L e.toEquiv
  rw [UnitaryPilot.modelToG_def, UnitaryPilot.modelToG_def, ← CFSG.Quasithin.map_perfectCore,
    ← CFSG.Quasithin.map_perfectCore]

theorem perfectCore_modelToG_inf_centralizer [Finite G] (A B : Subgroup P) :
    perfectCore (modelToG e A ⊓ centralizer (modelToG e B : Set G)) =
      modelToG e (perfectCore (A ⊓ centralizer (B : Set P))) := by
  rw [modelToG_inf_centralizer, perfectCore_modelToG]

theorem isSimpleGroup_modelToG {H : Subgroup P} (hH : IsSimpleGroup H) :
    IsSimpleGroup (modelToG e H) :=
  (UnitaryPilot.modelToGEquiv e H).symm.isSimpleGroup

theorem center_modelToG_eq_bot {H : Subgroup P} (hH : center H = ⊥) :
    center (modelToG e H) = ⊥ :=
  F4Pilot.center_eq_bot_congr (UnitaryPilot.modelToGEquiv e H) hH

theorem exists_ne_one_mem_modelToG {H₁ H₂ H₃ : Subgroup P}
    (h : ∃ x : P, x ≠ 1 ∧ x ∈ H₁ ∧ x ∈ H₂ ∧ x ∈ H₃) :
    ∃ y : G, y ≠ 1 ∧ y ∈ modelToG e H₁ ∧ y ∈ modelToG e H₂ ∧ y ∈ modelToG e H₃ := by
  obtain ⟨x, hx1, h1, h2, h3⟩ := h
  refine ⟨((e.symm x : L) : G), fun hy => hx1 ?_, UnitaryPilot.symm_mem_modelToG e h1,
    UnitaryPilot.symm_mem_modelToG e h2, UnitaryPilot.symm_mem_modelToG e h3⟩
  have h' : e.symm x = 1 := Subtype.ext hy
  rw [← e.apply_symm_apply x, h', map_one]

end Transport

theorem commutator_eq_self_of_isQuasisimple_open {Y : Type*} [Group Y] {D : Subgroup Y}
    (h : CFSG.Open.IsQuasisimple D) : ⁅D, D⁆ = D := by
  have : Group.IsPerfect D := ⟨h.1⟩
  exact isPerfect_iff.mp this

theorem exists_ne_ne_fin {n : ℕ} (hn : 3 ≤ n) (i j : Fin n) : ∃ k : Fin n, k ≠ i ∧ k ≠ j := by
  classical
  obtain ⟨k, -, hk⟩ : ∃ k ∈ (Finset.univ : Finset (Fin n)), k ∉ ({i, j} : Finset (Fin n)) :=
    Finset.exists_mem_notMem_of_card_lt_card (by
      have h := Finset.card_insert_le i ({j} : Finset (Fin n))
      rw [Finset.card_singleton] at h
      rw [Finset.card_univ, Fintype.card_fin]
      omega)
  exact ⟨k, fun h => hk (by simp [h]), fun h => hk (by simp [h])⟩

section TorusPerp

variable {K : Type} [Field K] {d : ℕ}

theorem torusLin_mem_stabSub {a b a' b' : Fin d} (h1 : a' ≠ a) (h2 : a' ≠ b) (h3 : b' ≠ a)
    (h4 : b' ≠ b) (c : Kˣ) : torusLin a b c ∈ stabSub (K := K) a' b' := by
  refine ⟨?_, ?_⟩
  · funext i
    rw [torusLin_apply]
    by_cases hi : i = a'
    · subst hi
      simp [torusEntry, h1, h2]
    · simp [hi]
  · funext i
    rw [torusLin_apply]
    by_cases hi : i = b'
    · subst hi
      simp [torusEntry, h3, h4]
    · simp [hi]

theorem pairTorusOf_le_pairPerpOf (Q : QuadraticForm K (Fin d → K)) {a b a' b' : Fin d}
    (h1 : a' ≠ a) (h2 : a' ≠ b) (h3 : b' ≠ a) (h4 : b' ≠ b) :
    pairTorusOf Q a b ≤ pairPerpOf Q a' b' := by
  refine Subgroup.map_mono fun x hx => ?_
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  obtain ⟨c, hc⟩ := hx
  rw [← hc]
  exact torusLin_mem_stabSub h1 h2 h3 h4 c

theorem pairTorus_le_pairPerp {n : ℕ} {a b : Fin n} (hab : a ≠ b) :
    pairTorus (K := K) b ≤ pairPerp a := by
  have hinj := (plusIndexEquiv n).injective
  refine pairTorusOf_le_pairPerpOf _ (fun h => ?_) (fun h => ?_) (fun h => ?_) (fun h => ?_)
  · have := hinj h
    simp only [Sum.inl.injEq] at this
    exact hab this
  · exact absurd (hinj h) (by simp)
  · exact absurd (hinj h) (by simp)
  · have := hinj h
    simp only [Sum.inr.injEq] at this
    exact hab this

theorem minusPairTorus_le_minusPairPerp {n : ℕ} (hn : 1 ≤ n) (b c : K) {a a' : Fin (n - 1)}
    (h : a ≠ a') : minusPairTorus (K := K) hn b c a' ≤ minusPairPerp hn b c a := by
  have hinj := (minusIndexEquiv n hn).injective
  refine pairTorusOf_le_pairPerpOf _ (fun h' => ?_) (fun h' => ?_) (fun h' => ?_) (fun h' => ?_)
  · have := hinj h'
    simp only [Sum.inl.injEq] at this
    exact h this
  · exact absurd (hinj h') (by simp)
  · exact absurd (hinj h') (by simp)
  · have := hinj h'
    simp only [Sum.inr.injEq, Sum.inl.injEq] at this
    exact h this

end TorusPerp

section Plus

variable {K : Type} [Field K] {n : ℕ}

@[expose] noncomputable def plusOverlap (a b : Fin n) :
    Subgroup (matrixProjectiveDerived (coordinateQuadPlus n K)) :=
  perfectCore (pairPerp (K := K) a ⊓ centralizer (pairTorus (K := K) b : Set _))

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

end Plus

section Minus

variable {K : Type} [Field K] {n : ℕ}

@[expose] noncomputable def minusOverlap (hn : 1 ≤ n) (b c : K) (a a' : Fin (n - 1)) :
    Subgroup (matrixProjectiveDerived (coordinateQuadMinus n K hn b c)) :=
  perfectCore (minusPairPerp (K := K) hn b c a ⊓
    centralizer (minusPairTorus (K := K) hn b c a' : Set _))

structure MinusSwapOverlapInput (n : ℕ) (K : Type) [Field K] (hn : 1 ≤ n) (b c : K) : Prop where
  isSimpleGroup : ∀ a a' : Fin (n - 1), a ≠ a' → IsSimpleGroup (minusOverlap (K := K) hn b c a a')
  center_eq_bot : ∀ a a' : Fin (n - 1), a ≠ a' → center (minusOverlap (K := K) hn b c a a') = ⊥
  le_sup : ∀ a a' a'' : Fin (n - 1), a ≠ a' → a ≠ a'' → a' ≠ a'' →
    minusPairPerp (K := K) hn b c a ≤ minusOverlap hn b c a a' ⊔ minusOverlap hn b c a a''
  triple : ∀ o k l : Fin (n - 1), o ≠ k → o ≠ l → k ≠ l → ∃ x, x ≠ 1 ∧
    x ∈ minusOverlap (K := K) hn b c o k ∧ x ∈ minusOverlap (K := K) hn b c o l ∧
      x ∈ minusOverlap (K := K) hn b c k l
  iSup_eq_top : ⨆ a : Fin (n - 1), minusPairPerp (K := K) hn b c a = ⊤

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem false_of_swapCase_omega_minus (hset : SeitzSetting G L) {f : ℕ}
    (hKc : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K) (hn : 5 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus n K (one_le_of_five_le hn) b c))
    {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {m f' : ℕ}
    (hS : ∀ k : Fin (n - 1), ∀ htX : t ∈ centralizer
        (modelToG e (minusPairTorus (K := K) (one_le_of_five_le hn) b c k) : Set G),
      ∃ Kc : Subgroup (centralizer
            (modelToG e (minusPairTorus (K := K) (one_le_of_five_le hn) b c k) : Set G) ⧸
          oddCore (centralizer
            (modelToG e (minusPairTorus (K := K) (one_le_of_five_le hn) b c k) : Set G))),
        IsComponent Kc ∧
        OmegaNeighbourAlternative (QuotientGroup.mk' (oddCore (centralizer
            (modelToG e (minusPairTorus (K := K) (one_le_of_five_le hn) b c k) : Set G)))
              ⟨t, htX⟩)
          (((modelToG e (minusPairPerp (K := K) (one_le_of_five_le hn) b c k)).subgroupOf
              (centralizer (modelToG e (minusPairTorus (K := K) (one_le_of_five_le hn) b c k) :
                Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer
              (modelToG e (minusPairTorus (K := K) (one_le_of_five_le hn) b c k) :
                Set G))))) Kc m f' ∧
        Kc.map (MulAut.conj (QuotientGroup.mk' (oddCore (centralizer
            (modelToG e (minusPairTorus (K := K) (one_le_of_five_le hn) b c k) : Set G)))
              ⟨t, htX⟩)).toMonoidHom ≠ Kc)
    (hO : MinusSwapOverlapInput n K (one_le_of_five_le hn) b c)
    (hP : SwapPairExclusion
      (matrixProjectiveDerived (coordinateQuadMinus n K (one_le_of_five_le hn) b c))) :
    False := by
  have := LinearPilot.finite_of_card_eq_two_pow hKc
  have := LinearPilot.charP_two_of_card_eq_two_pow hKc
  have htC := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  set X : Fin (n - 1) → Subgroup G :=
    fun k => modelToG e (minusPairTorus (K := K) (one_le_of_five_le hn) b c k) with hXdef
  set D : Fin (n - 1) → Subgroup G :=
    fun k => modelToG e (minusPairPerp (K := K) (one_le_of_five_le hn) b c k) with hDdef
  have hdata : ∀ k : Fin (n - 1), X k ≤ L ∧ t ∈ centralizer (X k : Set G) ∧
      D k ≤ centralizer (X k : Set G) ∧ ⁅D k, D k⁆ = D k ∧ center (D k) = ⊥ := by
    intro k
    obtain ⟨hXL, htX, -, -, -, -, hDXt, hDq, hZ, -, -⟩ :=
      neighbour_data_minusPairTorus hKc hq hn hirr k e htC (X := X k) rfl (D := D k) rfl
    exact ⟨hXL, htX, hDXt.trans inf_le_left, isPerfect_iff.mp hDq.1, hZ⟩
  have hpar : ∀ k : Fin (n - 1), ∃ P : SwapParam t (D k), Function.Injective P.Ψ ∧
      P.Ψ.range = centralizerPerfectCore (X k) := fun k =>
    exists_swapParam_minusPairTorus hset hKc hq hn hirr k e htC ht rfl (hdata k).2.1 rfl
      (hS k (hdata k).2.1)
  choose Ψ hinj hrange using hpar
  have hOut : Group.IsSolvable (Outer L) :=
    isSolvable_outer_of_mulEquiv_minus (by omega) (LinearPilot.one_le_of_card_eq_two_pow hKc)
      hKc hirr e
  have hO' : ∀ a a', perfectCore (D a ⊓ centralizer (X a' : Set G)) =
      modelToG e (minusOverlap (K := K) (one_le_of_five_le hn) b c a a') := fun a a' =>
    perfectCore_modelToG_inf_centralizer e _ _
  have hgen : ⨆ a, D a = L :=
    (UnitaryPilot.modelToG_iSup e _).symm.trans
      (by rw [hO.iSup_eq_top, UnitaryPilot.modelToG_top])
  exact false_of_swapParam_family hset hOut e hP ht hKt Ψ hinj hrange (fun k => (hdata k).1)
    (fun k => (hdata k).2.2.1) (fun k => (hdata k).2.2.2.1) (fun k => (hdata k).2.2.2.2) hgen
    (fun a a' h => UnitaryPilot.modelToG_mono e (minusPairTorus_le_minusPairPerp _ b c h))
    (fun a a' h => by rw [hO']; exact isSimpleGroup_modelToG e (hO.isSimpleGroup a a' h))
    (fun a a' h => by rw [hO']; exact center_modelToG_eq_bot e (hO.center_eq_bot a a' h))
    (exists_ne_ne_fin (by omega))
    (fun a a' a'' h1 h2 h3 => by
      rw [hO', hO', ← UnitaryPilot.modelToG_sup]
      exact UnitaryPilot.modelToG_mono e (hO.le_sup a a' a'' h1 h2 h3))
    ⟨0, by omega⟩
    (fun k l hk hl hkl => by
      rw [hO', hO', hO']
      exact exists_ne_one_mem_modelToG e (hO.triple _ k l (Ne.symm hk) (Ne.symm hl) hkl))

theorem false_of_swapRow_omega_minus (hset : SeitzSetting G L) {f : ℕ}
    (hKc : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K) (hn : 5 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus n K (one_le_of_five_le hn) b c))
    {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {m f' : ℕ}
    (hHR8 : ∀ k : Fin (n - 1), ∀ htX : t ∈ centralizer
        (modelToG e (minusPairTorus (K := K) (one_le_of_five_le hn) b c k) : Set G),
      NeighbourOvergroupOmega (QuotientGroup.mk' (oddCore (centralizer
          (modelToG e (minusPairTorus (K := K) (one_le_of_five_le hn) b c k) : Set G)))
            ⟨t, htX⟩)
        (((modelToG e (minusPairPerp (K := K) (one_le_of_five_le hn) b c k)).subgroupOf
            (centralizer (modelToG e (minusPairTorus (K := K) (one_le_of_five_le hn) b c k) :
              Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer
            (modelToG e (minusPairTorus (K := K) (one_le_of_five_le hn) b c k) :
              Set G))))) m f')
    (hrow : ∀ k : Fin (n - 1),
      OmegaRowAt t (modelToG e (minusPairTorus (K := K) (one_le_of_five_le hn) b c k))
        (modelToG e (minusPairPerp (K := K) (one_le_of_five_le hn) b c k)) .swap)
    (hO : MinusSwapOverlapInput n K (one_le_of_five_le hn) b c)
    (hP : SwapPairExclusion
      (matrixProjectiveDerived (coordinateQuadMinus n K (one_le_of_five_le hn) b c))) :
    False := by
  have htC := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  refine false_of_swapCase_omega_minus hset hKc hq hn hirr e ht hKt (m := m) (f' := f')
    (fun k htX => ?_) hO hP
  obtain ⟨hcomp, -, -⟩ := neighbour_standard_minusPairTorus_of_seitzSetting hset hKc hq hn hirr
    k e htC ht rfl htX rfl
  obtain ⟨htX', hr⟩ := hrow k
  have hs : (QuotientGroup.mk' (oddCore (centralizer
      (modelToG e (minusPairTorus (K := K) (one_le_of_five_le hn) b c k) : Set G)))
        ⟨t, htX⟩) ^ 2 = 1 := by
    rw [← map_pow, sq, LinearPilot.mk_mul_mk_eq_one ht htX, map_one]
  exact swapCase_of_neighbourOvergroupOmega hs (commutator_eq_self_of_isQuasisimple_open hcomp.2.2)
    (ne_bot_of_isQuasisimple hcomp.2.2) (hHR8 k htX) hr

end Minus

end CFSG.SeitzReduction.OmegaPilot
