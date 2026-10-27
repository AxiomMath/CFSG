module

public import CFSG.FeitThompson.Representations.ScalarCoreDetectingFamilyCoherentLines
public import CFSG.FeitThompson.Representations.ScalarEqualityPermutationTest
public import CFSG.FeitThompson.Representations.ScalarAxisWeightsMinimumDegree

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace ScalarLineModel

open SemidirectProduct Subgroup Module ChiefLineDictionary ChiefFactorLinearAction
  ChiefFactorFaithfulImage ScalarAxis

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

universe u

def shiftPerm (q : ℕ) [NeZero q] : Equiv.Perm (Fin q) :=
  (ZMod.finEquiv q).toEquiv.symm.permCongr (Equiv.addRight 1)

theorem finEquiv_shiftPerm (q : ℕ) [NeZero q] (i : Fin q) :
    (ZMod.finEquiv q) (shiftPerm q i) = (ZMod.finEquiv q) i + 1 := by
  simp [shiftPerm, Equiv.permCongr_apply]

theorem shiftPerm_eq_finRotate (q : ℕ) [NeZero q] : shiftPerm q = finRotate q := by
  refine Equiv.ext fun i => (ZMod.finEquiv q).injective ?_
  rw [finEquiv_shiftPerm, finRotate_apply, map_add, map_one]

theorem isCycle_shiftPerm (q : ℕ) (hq : 2 ≤ q) [NeZero q] : (shiftPerm q).IsCycle := by
  obtain ⟨n, rfl⟩ : ∃ n, q = n + 2 := ⟨q - 2, by omega⟩
  rw [shiftPerm_eq_finRotate]
  exact isCycle_finRotate

theorem support_shiftPerm (q : ℕ) (hq : 2 ≤ q) [NeZero q] :
    (shiftPerm q).support = Finset.univ := by
  obtain ⟨n, rfl⟩ : ∃ n, q = n + 2 := ⟨q - 2, by omega⟩
  rw [shiftPerm_eq_finRotate]
  exact support_finRotate

variable {L : Type u} [Group L] {p q : ℕ} [Fact p.Prime] {H U B H0 : Subgroup L}
  [H.Normal] [H0.Normal] {Eline : ZMod q → Subgroup (↥H ⧸ H0.subgroupOf H)}
  {W : Type u} [AddCommGroup W] [Module (ZMod p) W]

noncomputable def factorLinearActOn (p : ℕ) [Module (ZMod p) W] (B : Subgroup L)
    (H H0 : Subgroup L) [H.Normal] [H0.Normal]
    (e : (↥H ⧸ H0.subgroupOf H) ≃* Multiplicative W) : ↥B →* (W ≃ₗ[ZMod p] W) :=
  (factorLinearAut p H H0 e).comp B.subtype

theorem factorLinearActOn_apply (e : (↥H ⧸ H0.subgroupOf H) ≃* Multiplicative W) (g : ↥B) :
    factorLinearActOn p B H H0 e g = factorLinearAut p H H0 e (g : L) := (rfl)

noncomputable def autBOfNormalizer (U : Subgroup L) {B : Subgroup L}
    (hB : B ≤ Subgroup.normalizer (U : Set L)) : ↥B →* MulAut ↥U :=
  (U.normalizerMonoidHom).comp (Subgroup.inclusion hB)

theorem coe_autBOfNormalizer_apply {hB : B ≤ Subgroup.normalizer (U : Set L)} (g : ↥B) (u : ↥U) :
    ((autBOfNormalizer U hB g u : ↥U) : L) = (g : L) * (u : L) * (g : L)⁻¹ :=
  Subgroup.normalizerMonoidHom_apply_apply_coe U _ u

noncomputable def scalarCoordinateSystemOfLines [NeZero q] (U : Subgroup L) (hq : 2 ≤ q)
    (e : (↥H ⧸ H0.subgroupOf H) ≃* Multiplicative W)
    (hcard : ∀ i, Nat.card (Eline i) = p) (hindep : iSupIndep Eline)
    (hsup : ⨆ i, Eline i = ⊤)
    (hinv : ∀ u ∈ U, ∀ i, Subgroup.map (conjQuotientAut H H0 u) (Eline i) = Eline i)
    (hcop : Nat.Coprime p (Nat.card ↥U)) :
    ScalarCoordinateSystem p q W ↥U where
  two_le_q := hq
  line i := subgroupOrderIsoSubmodule p e (Eline ((ZMod.finEquiv q) i))
  finrank_line i := finrank_subgroupOrderIsoSubmodule Fact.out e (hcard _)
  indep_line := iSupIndep_subgroupOrderIsoSubmodule e (hindep.comp (ZMod.finEquiv q).injective)
  iSup_line := by
    refine iSup_subgroupOrderIsoSubmodule_eq_top e ?_
    rw [← hsup]
    exact (ZMod.finEquiv q).toEquiv.iSup_comp (g := Eline)
  act := (factorLinearAut p H H0 e).comp U.subtype
  map_line u i v hv := by
    have hinv' : Subgroup.map (factorConjAut H H0 (u : L)) (Eline ((ZMod.finEquiv q) i))
        = Eline ((ZMod.finEquiv q) i) := by
      rw [← conjQuotientAut_eq_factorConjAut' H H0]
      exact hinv (u : L) u.2 _
    rw [← map_subgroupOrderIsoSubmodule_of_map_eq (p := p) e hinv']
    exact Submodule.mem_map_of_mem hv
  coprime_card := hcop

section System

variable [NeZero q] (U : Subgroup L) (hq : 2 ≤ q)
  (e : (↥H ⧸ H0.subgroupOf H) ≃* Multiplicative W)
  (hcard : ∀ i, Nat.card (Eline i) = p) (hindep : iSupIndep Eline)
  (hsup : ⨆ i, Eline i = ⊤)
  (hinv : ∀ u ∈ U, ∀ i, Subgroup.map (conjQuotientAut H H0 u) (Eline i) = Eline i)
  (hcop : Nat.Coprime p (Nat.card ↥U))

theorem scalarCoordinateSystemOfLines_line (i : Fin q) :
    (scalarCoordinateSystemOfLines U hq e hcard hindep hsup hinv hcop).line i
      = subgroupOrderIsoSubmodule p e (Eline ((ZMod.finEquiv q) i)) := (rfl)

theorem scalarCoordinateSystemOfLines_act (u : ↥U) :
    (scalarCoordinateSystemOfLines U hq e hcard hindep hsup hinv hcop).act u
      = factorLinearAut p H H0 e (u : L) := (rfl)

theorem lineCentralizer_scalarCoordinateSystemOfLines (i : Fin q) :
    (scalarCoordinateSystemOfLines U hq e hcard hindep hsup hinv hcop).lineCentralizer i
      = (lineFixer H H0 U (Eline ((ZMod.finEquiv q) i))).subgroupOf U := by
  have hconj : ∀ g : L, ∀ v, conjQuotientAut H H0 g v = factorConjAut H H0 g v := fun g v => by
    rw [conjQuotientAut_eq_factorConjAut' H H0]
  ext u
  rw [ScalarCoordinateSystem.mem_lineCentralizer, Subgroup.mem_subgroupOf, mem_lineFixer]
  refine ⟨fun h => ⟨u.2, fun v hv => ?_⟩, fun h v hv => ?_⟩
  · have hmem : Multiplicative.toAdd (e v)
        ∈ (scalarCoordinateSystemOfLines U hq e hcard hindep hsup hinv hcop).line i := by
      rw [scalarCoordinateSystemOfLines_line, mem_subgroupOrderIsoSubmodule]
      simpa using hv
    have hfix := h _ hmem
    rw [scalarCoordinateSystemOfLines_act, factorLinearAut_apply p e (u : L) v] at hfix
    exact e.injective (Multiplicative.toAdd.injective (by rw [hconj, hfix]))
  · rw [scalarCoordinateSystemOfLines_line, mem_subgroupOrderIsoSubmodule] at hv
    rw [scalarCoordinateSystemOfLines_act, factorLinearAut_apply' p e (u : L) v]
    have hfix : factorConjAut H H0 (u : L) (e.symm (Multiplicative.ofAdd v))
        = e.symm (Multiplicative.ofAdd v) := by
      rw [← hconj]; exact h.2 _ hv
    rw [hfix]
    simp

theorem index_lineCentralizer_scalarCoordinateSystemOfLines
    (hrel : ∀ i, (lineFixer H H0 U (Eline i)).relIndex U
      = (lineFixer H H0 U (Eline 0)).relIndex U) (i : Fin q) :
    ((scalarCoordinateSystemOfLines U hq e hcard hindep hsup hinv hcop).lineCentralizer i).index
      = (lineFixer H H0 U (Eline 0)).relIndex U := by
  rw [lineCentralizer_scalarCoordinateSystemOfLines, ← Subgroup.relIndex,
    hrel ((ZMod.finEquiv q) i)]

theorem compat_actB {hB : B ≤ Subgroup.normalizer (U : Set L)} (g : ↥B) (u : ↥U) (v : W) :
    factorLinearActOn p B H H0 e g
        ((scalarCoordinateSystemOfLines U hq e hcard hindep hsup hinv hcop).act u v)
      = (scalarCoordinateSystemOfLines U hq e hcard hindep hsup hinv hcop).act
        (autBOfNormalizer U hB g u) (factorLinearActOn p B H H0 e g v) := by
  have h1 : (factorLinearAut p H H0 e (g : L)) * (factorLinearAut p H H0 e (u : L))
      = (factorLinearAut p H H0 e ((autBOfNormalizer U hB g u : ↥U) : L)) *
        (factorLinearAut p H H0 e (g : L)) := by
    rw [coe_autBOfNormalizer_apply, ← map_mul, ← map_mul]
    congr 1
    group
  have h2 := congrArg (fun σ : W ≃ₗ[ZMod p] W => σ v) h1
  simpa [factorLinearActOn_apply, scalarCoordinateSystemOfLines_act] using h2

end System

noncomputable def axisSystemOfLines [NeZero q] (U : Subgroup L) (hq : 2 ≤ q)
    (e : (↥H ⧸ H0.subgroupOf H) ≃* Multiplicative W)
    (hcard : ∀ i, Nat.card (Eline i) = p) (hindep : iSupIndep Eline)
    (hsup : ⨆ i, Eline i = ⊤)
    (hinv : ∀ u ∈ U, ∀ i, Subgroup.map (conjQuotientAut H H0 u) (Eline i) = Eline i)
    (hcop : Nat.Coprime p (Nat.card ↥U))
    (hrel : ∀ i, (lineFixer H H0 U (Eline i)).relIndex U
      = (lineFixer H H0 U (Eline 0)).relIndex U)
    (hlt : 1 < (lineFixer H H0 U (Eline 0)).relIndex U)
    (hB : B ≤ Subgroup.normalizer (U : Set L)) (hcardB : Nat.card ↥B = q)
    {b : L} (hbB : b ∈ B) (hbgen : B = Subgroup.zpowers b)
    (hb : ∀ i, Subgroup.map (conjQuotientAut H H0 b) (Eline i) = Eline (i + 1)) :
    AxisSystem p q W ↥U ↥B where
  scalar := scalarCoordinateSystemOfLines U hq e hcard hindep hsup hinv hcop
  a := (lineFixer H H0 U (Eline 0)).relIndex U
  one_lt_a := hlt
  index_lineCentralizer i :=
    index_lineCentralizer_scalarCoordinateSystemOfLines U hq e hcard hindep hsup hinv hcop hrel i
  actB := factorLinearActOn p B H H0 e
  autB := autBOfNormalizer U hB
  compat g u v := compat_actB U hq e hcard hindep hsup hinv hcop g u v
  gen := ⟨b, hbB⟩
  card_B := hcardB
  mem_zpowers_gen x := by
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 (hbgen ▸ x.2 : (x : L) ∈ Subgroup.zpowers b)
    exact Subgroup.mem_zpowers_iff.2 ⟨n, Subtype.ext (by simpa using hn)⟩
  perm := shiftPerm q
  isCycle_perm := isCycle_shiftPerm q hq
  support_perm := support_shiftPerm q hq
  map_line_gen i := by
    rw [scalarCoordinateSystemOfLines_line, scalarCoordinateSystemOfLines_line,
      factorLinearActOn_apply, map_subgroupOrderIsoSubmodule,
      ← conjQuotientAut_eq_factorConjAut' H H0, hb, finEquiv_shiftPerm]

section AxisAPI

variable [NeZero q] (U : Subgroup L) (hq : 2 ≤ q)
  (e : (↥H ⧸ H0.subgroupOf H) ≃* Multiplicative W)
  (hcard : ∀ i, Nat.card (Eline i) = p) (hindep : iSupIndep Eline)
  (hsup : ⨆ i, Eline i = ⊤)
  (hinv : ∀ u ∈ U, ∀ i, Subgroup.map (conjQuotientAut H H0 u) (Eline i) = Eline i)
  (hcop : Nat.Coprime p (Nat.card ↥U))
  (hrel : ∀ i, (lineFixer H H0 U (Eline i)).relIndex U
    = (lineFixer H H0 U (Eline 0)).relIndex U)
  (hlt : 1 < (lineFixer H H0 U (Eline 0)).relIndex U)
  (hB : B ≤ Subgroup.normalizer (U : Set L)) (hcardB : Nat.card ↥B = q)
  {b : L} (hbB : b ∈ B) (hbgen : B = Subgroup.zpowers b)
  (hb : ∀ i, Subgroup.map (conjQuotientAut H H0 b) (Eline i) = Eline (i + 1))

@[simp] theorem axisSystemOfLines_a :
    (axisSystemOfLines U hq e hcard hindep hsup hinv hcop hrel hlt hB hcardB hbB hbgen hb).a
      = (lineFixer H H0 U (Eline 0)).relIndex U := (rfl)

theorem axisSystemOfLines_scalar :
    (axisSystemOfLines U hq e hcard hindep hsup hinv hcop hrel hlt hB hcardB hbB hbgen hb).scalar
      = scalarCoordinateSystemOfLines U hq e hcard hindep hsup hinv hcop := (rfl)

theorem axisSystemOfLines_actB :
    (axisSystemOfLines U hq e hcard hindep hsup hinv hcop hrel hlt hB hcardB hbB hbgen hb).actB
      = factorLinearActOn p B H H0 e := (rfl)

theorem axisSystemOfLines_autB :
    (axisSystemOfLines U hq e hcard hindep hsup hinv hcop hrel hlt hB hcardB hbB hbgen hb).autB
      = autBOfNormalizer U hB := (rfl)

end AxisAPI

end ScalarLineModel

end CFSG.FeitThompson
