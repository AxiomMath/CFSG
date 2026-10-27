module

public import CFSG.LieType.Steinberg.G2.Extras
public import CFSG.LieType.Steinberg.RankTwo.G2CommData
import CFSG.LieType.Steinberg.RankTwo.G2CommCheck
import CFSG.Timmesfeld.RankTwo.ModelG2Comm

public section

namespace CFSG.LieType.Steinberg.RankTwo

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps
open CFSG.LieType.Chevalley.RootWalk CFSG.LieType.Steinberg.Adjoint
open scoped commutatorElement

theorem g2CommRoot_length : (Tag.rootCertificate .G2).roots.length = 12 :=
  rfl

theorem g2CommPairOk_of {a b : ℕ} (ha : a < 12) (hb : b < 12) :
    g2CommPairOk a b = true ∧ g2CommNatAbs (g2CommFactors a b) = true ∧
      g2CommNatAbs (g2CommSwapFactors a b) = true := by
  have h := g2CommAllOk_eq
  simp only [g2CommAllOk, List.all_eq_true, List.mem_range, Bool.and_eq_true] at h
  exact ⟨(h.2 a ha b hb).1.1, (h.2 a ha b hb).1.2, (h.2 a ha b hb).2⟩

theorem g2CommPairOk_spec
    {a b : ℕ} (ha : a < 12) (hb : b < 12) (hab : a ≠ b)
    (hs : g2CommRoot a + g2CommRoot b ≠ 0) :
    g2CommDet a b ≠ 0 ∧ g2CommListOk a b (g2CommFactors a b) = true ∧ g2CommSwapOk a b = true := by
  have h := (g2CommPairOk_of ha hb).1
  have h1 : (a == b) = false := beq_false_of_ne hab
  have h2 : CFSG.LieType.Ree.vecBEq (g2CommRoot a + g2CommRoot b) 0 = false := by
    cases hv : CFSG.LieType.Ree.vecBEq (g2CommRoot a + g2CommRoot b) 0
    · rfl
    · exact absurd (CFSG.LieType.Ree.vecBEq_iff.1 hv) hs
  simp only [g2CommPairOk, h1, h2, Bool.false_or, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem g2CommListOk_spec {a b : ℕ} {fs : List Factor} (h : g2CommListOk a b fs = true) :
    fs.all (coneOk .G2 a b) = true ∧ g2CommComplete a b (g2CommExps fs) = true ∧
      (g2CommExps fs).Nodup ∧ g2CommCommute a b fs = true := by
  simp only [g2CommListOk, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem g2CommSwapOk_spec
    {a b : ℕ} (ha : a < 12) (hb : b < 12) (hab : a ≠ b)
    (hs : g2CommRoot a + g2CommRoot b ≠ 0) (h4 : (g2CommFactors a b).length = 4) :
    g2CommListOk a b (g2CommSwapFactors a b) = true ∧
      ((g2CommExps (g2CommFactors a b)).filter (g2CommNonCentral a b)).length = 2 ∧
      (g2CommExps (g2CommSwapFactors a b)).filter (g2CommNonCentral a b) =
        ((g2CommExps (g2CommFactors a b)).filter (g2CommNonCentral a b)).reverse := by
  have h := (g2CommPairOk_spec ha hb hab hs).2.2
  simp only [g2CommSwapOk, h4, bne_self_eq_false, Bool.false_or, Bool.and_eq_true,
    beq_iff_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem g2CommCoeff_of_mem {fs : List Factor} (hnd : (g2CommExps fs).Nodup) {f : Factor}
    (hf : f ∈ fs) : g2CommCoeff fs (f.1, f.2.1) = f.2.2.2 := by
  induction fs with
  | nil => simp at hf
  | cons f₀ fs ih =>
    rw [g2CommExps, List.map_cons, List.nodup_cons] at hnd
    obtain ⟨hn0, hnd⟩ := hnd
    rcases List.mem_cons.1 hf with rfl | hf
    · simp [g2CommCoeff]
    · have hne : (f₀.1, f₀.2.1) ≠ (f.1, f.2.1) := fun h =>
        hn0 (h ▸ List.mem_map_of_mem hf)
      have := ih hnd hf
      simp only [g2CommCoeff, List.find?_cons] at this ⊢
      rw [show ((f₀.1, f₀.2.1) == (f.1, f.2.1)) = false from beq_false_of_ne hne]
      exact this

theorem natAbs_g2CommCoeff {fs : List Factor} (h : g2CommNatAbs fs = true) (p : ℕ × ℕ) :
    (g2CommCoeff fs p).natAbs ∈ ({1, 2, 3} : Set ℕ) := by
  unfold g2CommCoeff
  rcases hf : fs.find? (fun f => (f.1, f.2.1) == p) with _ | f
  · rw [hf]
    simp
  · have hmem := List.mem_of_find?_eq_some hf
    simp only [g2CommNatAbs, List.all_eq_true, Bool.or_eq_true, beq_iff_eq] at h
    rw [hf]
    rcases h f hmem with (h | h) | h <;> simp [h]

theorem g2CommRoot_apply {a b g i j : ℕ}
    (h : g2CommRoot g = i • g2CommRoot a + j • g2CommRoot b) (t : Fin (Tag.rank .G2)) :
    g2CommRoot g t = i * g2CommRoot a t + j * g2CommRoot b t := by
  rw [h]
  simp [nsmul_eq_mul]

theorem g2CommCramer_eq {a b g i j : ℕ} (hd : g2CommDet a b ≠ 0)
    (h : g2CommRoot g = i • g2CommRoot a + j • g2CommRoot b) : g2CommCramer a b g = (i, j) := by
  have h0 := g2CommRoot_apply h ⟨0, by decide⟩
  have h1 := g2CommRoot_apply h ⟨1, by decide⟩
  have e1 : g2CommRoot g ⟨0, by decide⟩ * g2CommRoot b ⟨1, by decide⟩ -
      g2CommRoot g ⟨1, by decide⟩ * g2CommRoot b ⟨0, by decide⟩ = (i : ℤ) * g2CommDet a b := by
    rw [h0, h1, g2CommDet]
    ring
  have e2 : g2CommRoot a ⟨0, by decide⟩ * g2CommRoot g ⟨1, by decide⟩ -
      g2CommRoot a ⟨1, by decide⟩ * g2CommRoot g ⟨0, by decide⟩ = (j : ℤ) * g2CommDet a b := by
    rw [h0, h1, g2CommDet]
    ring
  rw [g2CommCramer, e1, e2, Int.mul_ediv_cancel _ hd, Int.mul_ediv_cancel _ hd, Int.toNat_natCast,
    Int.toNat_natCast]

theorem linIndepPair_of_g2CommDet {a b : ℕ} (hd : g2CommDet a b ≠ 0) :
    LinIndepPair (g2CommRoot a) (g2CommRoot b) := by
  intro u v huv
  have h0 := congrFun huv ⟨0, by decide⟩
  have h1 := congrFun huv ⟨1, by decide⟩
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h0 h1
  have hu : u * g2CommDet a b = 0 := by
    rw [g2CommDet]
    linear_combination g2CommRoot b ⟨1, by decide⟩ * h0 - g2CommRoot b ⟨0, by decide⟩ * h1
  have hv : v * g2CommDet a b = 0 := by
    rw [g2CommDet]
    linear_combination g2CommRoot a ⟨0, by decide⟩ * h1 - g2CommRoot a ⟨1, by decide⟩ * h0
  exact ⟨(mul_eq_zero.1 hu).resolve_right hd, (mul_eq_zero.1 hv).resolve_right hd⟩

theorem mem_g2CommExps_iff
    {a b : ℕ} (hd : g2CommDet a b ≠ 0) {fs : List Factor}
    (hcone : fs.all (coneOk .G2 a b) = true)
    (hcomp : g2CommComplete a b (g2CommExps fs) = true) (p : ℕ × ℕ) :
    p ∈ g2CommExps fs ↔
      0 < p.1 ∧ 0 < p.2 ∧ IsRoot .G2 (p.1 • g2CommRoot a + p.2 • g2CommRoot b) := by
  constructor
  · intro hp
    obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hp
    have hc := List.all_eq_true.1 hcone f hf
    simp only [coneOk, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at hc
    obtain ⟨⟨⟨hg, hp1⟩, hp2⟩, hv⟩ := hc
    rw [CFSG.LieType.Ree.vecBEq_iff] at hv
    exact ⟨hp1, hp2, hv ▸ isRoot_rootCertificate_root hg⟩
  · obtain ⟨i, j⟩ := p
    rintro ⟨h1, h2, hr⟩
    obtain ⟨g, hg, hgr⟩ := exists_rootPos (⟨_, hr⟩ : Root .G2)
    have hc := g2CommCramer_eq hd hgr
    have hv : CFSG.LieType.Ree.vecBEq (g2CommRoot g) (i • g2CommRoot a + j • g2CommRoot b) =
        true :=
      CFSG.LieType.Ree.vecBEq_iff.2 hgr
    have := List.all_eq_true.1 hcomp g (List.mem_range.2 hg)
    have e1 : Nat.blt 0 i = true := Nat.blt_eq.mpr h1
    have e2 : Nat.blt 0 j = true := Nat.blt_eq.mpr h2
    simp only [hc, hv, e1, e2, Bool.and_true, Bool.not_true, Bool.false_or] at this
    simpa using this

theorem prod_map_eq_filter_mul_filter_not {X G : Type*} [Monoid G] (L : List X) (q : X → Bool)
    (f : X → G) (h : ∀ x ∈ L, q x = false → ∀ y ∈ L, Commute (f x) (f y)) :
    (L.map f).prod = ((L.filter q).map f).prod * ((L.filter fun x => !q x).map f).prod := by
  induction L with
  | nil => simp
  | cons a L ih =>
    have ih' := ih fun x hx hq y hy =>
      h x (List.mem_cons_of_mem a hx) hq y (List.mem_cons_of_mem a hy)
    by_cases ha : q a = true
    · rw [List.filter_cons_of_pos ha, List.filter_cons_of_neg (by simp [ha]), List.map_cons,
        List.map_cons, List.prod_cons, List.prod_cons, ih', mul_assoc]
    · have ha' : q a = false := by simpa using ha
      rw [List.filter_cons_of_neg ha, List.filter_cons_of_pos (by simp [ha']), List.map_cons,
        List.map_cons, List.prod_cons, List.prod_cons, ih']
      have hc : Commute (f a) ((L.filter q).map f).prod :=
        Commute.list_prod_right _ _ fun y hy => by
          obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
          exact h a (List.mem_cons_self ..) ha' z
            (List.mem_cons_of_mem a (List.mem_filter.1 hz).1)
      rw [← mul_assoc, hc.eq, mul_assoc]

section Group

variable {K : Type} [Field K]

variable (K) in
def G2CommHolds
    (a b : ℕ) (fs : List Factor) : Prop :=
  ∀ c d : K, ⁅xPar (rootOperatorFamily .G2) (g2CommRoot a) c,
      xPar (rootOperatorFamily .G2) (g2CommRoot b) d⁆ =
    (fs.map fun f => xPar (rootOperatorFamily .G2) (g2CommRoot f.2.2.1)
      ((f.2.2.2 : K) * c ^ f.1 * d ^ f.2.1)).prod

theorem g2CommHolds_of_repCheck
    {a b : ℕ} {fs : List Factor} (h : repCheck .G2 a b fs = true) :
    G2CommHolds K a b fs :=
  CFSG.Timmesfeld.RankTwo.commutator_xPar_of_repCheck h

theorem G2CommHolds.inv
    {a b : ℕ} {fs : List Factor} (h : G2CommHolds K b a fs) :
    G2CommHolds K a b (g2CommInv fs) := by
  intro c d
  rw [← commutatorElement_inv, h d c, List.prod_inv_reverse, g2CommInv, List.map_map,
    List.map_map, List.map_reverse]
  congr 2
  refine List.map_congr_left fun f _ => ?_
  simp only [Function.comp_apply, xPar_neg]
  congr 1
  push_cast
  ring

theorem g2CommHolds_lookup
    {T : List ((ℕ × ℕ) × List Factor)}
    (hT : ∀ e ∈ T, G2CommHolds K e.1.1 e.1.2 e.2) {a b : ℕ} (hne : g2CommLookup T a b ≠ []) :
    G2CommHolds K a b (g2CommLookup T a b) := by
  unfold g2CommLookup at hne ⊢
  rcases h1 : T.find? (fun e => e.1 == (a, b)) with _ | e
  · rw [h1] at hne ⊢
    rcases h2 : T.find? (fun e => e.1 == (b, a)) with _ | e
    · rw [h2] at hne
      exact absurd rfl hne
    · rw [h2]
      have hkey : e.1 = (b, a) := by simpa using List.find?_some h2
      have := hT e (List.mem_of_find?_eq_some h2)
      rw [hkey] at this
      exact this.inv
  · rw [h1]
    have hkey : e.1 = (a, b) := by simpa using List.find?_some h1
    have := hT e (List.mem_of_find?_eq_some h1)
    rwa [hkey] at this

theorem commutator_g2CommRoot_eq_one
    {a b : ℕ} (ha : a < 12) (hb : b < 12)
    (hd : g2CommDet a b ≠ 0) (hcomp : g2CommComplete a b [] = true) (c d : K) :
    ⁅xPar (rootOperatorFamily .G2) (g2CommRoot a) c,
        xPar (rootOperatorFamily .G2) (g2CommRoot b) d⁆ = 1 := by
  have hα := isRoot_rootCertificate_root (τ := .G2) (k := a) (by rw [g2CommRoot_length]; exact ha)
  have hβ := isRoot_rootCertificate_root (τ := .G2) (k := b) (by rw [g2CommRoot_length]; exact hb)
  have hmem := commutator_mem_openCone_of_linIndepPair hα hβ (linIndepPair_of_g2CommDet hd)
    (xPar_mem hα c) (xPar_mem hβ d)
  have hbot : (⨆ ε ∈ openCone (adjDatum (rootOperatorFamily .G2) K).roots (g2CommRoot a)
      (g2CommRoot b), (adjDatum (rootOperatorFamily .G2) K).rootGroup ε) = ⊥ := by
    refine iSup₂_eq_bot.2 fun ε hε => absurd hε ?_
    rintro ⟨hεr, i, j, hi, hj, rfl⟩
    have := (mem_g2CommExps_iff hd (fs := []) rfl hcomp (i, j)).2
      ⟨hi, hj, mem_adjDatum_roots.1 hεr⟩
    simp [g2CommExps] at this
  rw [hbot] at hmem
  exact Subgroup.mem_bot.1 hmem

theorem g2CommHolds_factors
    {a b : ℕ} (ha : a < 12) (hb : b < 12) (hab : a ≠ b)
    (hs : g2CommRoot a + g2CommRoot b ≠ 0) : G2CommHolds K a b (g2CommFactors a b) := by
  obtain ⟨hd, hok, -⟩ := g2CommPairOk_spec ha hb hab hs
  by_cases h0 : g2CommFactors a b = []
  · intro c d
    rw [h0, List.map_nil, List.prod_nil]
    have hcomp := (g2CommListOk_spec hok).2.1
    rw [h0] at hcomp
    exact commutator_g2CommRoot_eq_one ha hb hd hcomp c d
  · exact g2CommHolds_lookup (fun e he => g2CommHolds_of_repCheck
      (List.all_eq_true.1 g2CommPairs_check e he)) h0

theorem commute_of_g2CommCommutes
    {g g' : ℕ} (hg : g < 12) (hg' : g' < 12)
    (h : g2CommCommutes g g' = true) (u v : K) :
    Commute (xPar (rootOperatorFamily .G2) (g2CommRoot g) u)
      (xPar (rootOperatorFamily .G2) (g2CommRoot g') v) := by
  by_cases heq : g = g'
  · rw [← heq, Commute, SemiconjBy, ← xPar_add, ← xPar_add, add_comm]
  · have hb : (g == g') = false := beq_false_of_ne heq
    simp only [g2CommCommutes, hb, Bool.false_or, Bool.and_eq_true, Bool.not_eq_true',
      List.isEmpty_iff] at h
    obtain ⟨hv, hnil⟩ := h
    have hs : g2CommRoot g + g2CommRoot g' ≠ 0 := fun h0 => by
      rw [← CFSG.LieType.Ree.vecBEq_iff] at h0
      rw [h0] at hv
      cases hv
    rw [← commutatorElement_eq_one_iff_commute, g2CommHolds_factors hg hg' heq hs u v, hnil,
      List.map_nil, List.prod_nil]

theorem g2CommDeriveOk_pairs : g2CommPairs.all (fun e => g2CommDeriveOk e.2) = true := by
  have h := g2CommAllOk_eq
  simp only [g2CommAllOk, Bool.and_eq_true] at h
  exact h.1

theorem g2CommHolds_swapOf
    {a b : ℕ} {fA fB fZ fW : Factor}
    (h : G2CommHolds K a b [fA, fB, fZ, fW]) (hder : g2CommDeriveOk [fA, fB, fZ, fW] = true) :
    G2CommHolds K a b (g2CommSwapOf [fA, fB, fZ, fW]) := by
  simp only [g2CommDeriveOk, Bool.and_eq_true, Nat.blt_eq, bne_iff_ne, ne_eq, beq_iff_eq,
    Bool.not_eq_true'] at hder
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hA, hB⟩, hZ⟩, hW⟩, hAB⟩, hv⟩, hF⟩, hp⟩, hq⟩, hcA⟩, hcB⟩, hcZ⟩ := hder
  have hs : g2CommRoot fA.2.2.1 + g2CommRoot fB.2.2.1 ≠ 0 := fun h0 => by
    rw [← CFSG.LieType.Ree.vecBEq_iff] at h0
    rw [h0] at hv
    cases hv
  intro c d
  obtain ⟨C, hC⟩ : ∃ C, C = g2CommCoeff (g2CommFactors fA.2.2.1 fB.2.2.1) (1, 1) := ⟨_, rfl⟩
  rw [← hC] at hF
  have hAB' := g2CommHolds_factors (K := K) hA hB hAB hs ((fA.2.2.2 : K) * c ^ fA.1 * d ^ fA.2.1)
    ((fB.2.2.2 : K) * c ^ fB.1 * d ^ fB.2.1)
  rw [hF] at hAB'
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, pow_one]
    at hAB'
  rw [h c d]
  simp only [g2CommSwapOf, ← hC, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one]
  generalize hXA : xPar (rootOperatorFamily .G2) (g2CommRoot fA.2.2.1)
    ((fA.2.2.2 : K) * c ^ fA.1 * d ^ fA.2.1) = XA at hAB'
  generalize hXB : xPar (rootOperatorFamily .G2) (g2CommRoot fB.2.2.1)
    ((fB.2.2.2 : K) * c ^ fB.1 * d ^ fB.2.1) = XB at hAB'
  have hW' : xPar (rootOperatorFamily .G2) (g2CommRoot fW.2.2.1)
      (((fW.2.2.2 + C * fA.2.2.2 * fB.2.2.2 : ℤ) : K) * c ^ fW.1 * d ^ fW.2.1) =
      xPar (rootOperatorFamily .G2) (g2CommRoot fW.2.2.1)
        ((C : K) * ((fA.2.2.2 : K) * c ^ fA.1 * d ^ fA.2.1) *
          ((fB.2.2.2 : K) * c ^ fB.1 * d ^ fB.2.1)) *
      xPar (rootOperatorFamily .G2) (g2CommRoot fW.2.2.1)
        ((fW.2.2.2 : K) * c ^ fW.1 * d ^ fW.2.1) := by
    rw [← xPar_add, hp, hq]
    congr 1
    push_cast
    ring
  rw [hW']
  generalize hXZ : xPar (rootOperatorFamily .G2) (g2CommRoot fZ.2.2.1)
    ((fZ.2.2.2 : K) * c ^ fZ.1 * d ^ fZ.2.1) = XZ
  generalize hXW : xPar (rootOperatorFamily .G2) (g2CommRoot fW.2.2.1)
    ((fW.2.2.2 : K) * c ^ fW.1 * d ^ fW.2.1) = XW
  generalize hT : xPar (rootOperatorFamily .G2) (g2CommRoot fW.2.2.1)
    ((C : K) * ((fA.2.2.2 : K) * c ^ fA.1 * d ^ fA.2.1) *
      ((fB.2.2.2 : K) * c ^ fB.1 * d ^ fB.2.1)) = T at hAB'
  have cA : Commute T XA := by
    rw [← hT, ← hXA]
    exact commute_of_g2CommCommutes hW hA hcA _ _
  have cB : Commute T XB := by
    rw [← hT, ← hXB]
    exact commute_of_g2CommCommutes hW hB hcB _ _
  have cZ : Commute T XZ := by
    rw [← hT, ← hXZ]
    exact commute_of_g2CommCommutes hW hZ hcZ _ _
  have e1 : XA * XB = T * XB * XA := by
    rw [← hAB', commutatorElement_def]
    group
  calc XA * (XB * (XZ * XW)) = XA * XB * (XZ * XW) := by rw [mul_assoc]
    _ = T * XB * XA * (XZ * XW) := by rw [e1]
    _ = XB * (XA * (XZ * (T * XW))) := by
      rw [cB.eq, mul_assoc XB T XA, cA.eq, ← mul_assoc XZ T XW, ← cZ.eq]
      simp only [mul_assoc]

theorem g2CommHolds_swaps
    {e : (ℕ × ℕ) × List Factor} (he : e ∈ g2CommSwaps) :
    G2CommHolds K e.1.1 e.1.2 e.2 := by
  obtain ⟨⟨k, fs⟩, he', rfl⟩ := List.mem_map.1 he
  have h := g2CommHolds_of_repCheck (K := K) (List.all_eq_true.1 g2CommPairs_check _ he')
  have hder : g2CommDeriveOk fs = true := List.all_eq_true.1 g2CommDeriveOk_pairs _ he'
  rcases fs with _ | ⟨f₁, _ | ⟨f₂, _ | ⟨f₃, _ | ⟨f₄, _ | ⟨f₅, fs⟩⟩⟩⟩⟩
  all_goals first
    | exact h
    | exact g2CommHolds_swapOf h hder

theorem g2CommHolds_swapFactors
    {a b : ℕ} (ha : a < 12) (hb : b < 12) (hab : a ≠ b)
    (hs : g2CommRoot a + g2CommRoot b ≠ 0) (h4 : (g2CommFactors a b).length = 4) :
    G2CommHolds K a b (g2CommSwapFactors a b) := by
  obtain ⟨-, h2, hrev⟩ := g2CommSwapOk_spec ha hb hab hs h4
  refine g2CommHolds_lookup (fun e he => g2CommHolds_swaps he) fun h0 => ?_
  have : ((g2CommExps (g2CommSwapFactors a b)).filter (g2CommNonCentral a b)).length = 2 := by
    rw [hrev, List.length_reverse, h2]
  rw [g2CommSwapFactors, h0] at this
  simp [g2CommExps] at this

theorem commute_of_g2CommCommute
    {a b : ℕ} {fs : List Factor}
    (hcone : fs.all (coneOk .G2 a b) = true) (hc : g2CommCommute a b fs = true) {f f' : Factor}
    (hf : f ∈ fs) (hf' : f' ∈ fs) (hq : g2CommNonCentral a b (f.1, f.2.1) = false) (u v : K) :
    Commute (xPar (rootOperatorFamily .G2) (g2CommRoot f.2.2.1) u)
      (xPar (rootOperatorFamily .G2) (g2CommRoot f'.2.2.1) v) := by
  have h := List.all_eq_true.1 hc f hf
  rw [hq, Bool.false_or] at h
  have hlt : ∀ g ∈ fs, g.2.2.1 < 12 := fun g hg => by
    have := List.all_eq_true.1 hcone g hg
    simp only [coneOk, Bool.and_eq_true, Nat.blt_eq] at this
    exact this.1.1.1
  exact commute_of_g2CommCommutes (hlt f hf) (hlt f' hf') (List.all_eq_true.1 h f' hf') u v

theorem prod_g2CommFactors_eq
    {a b : ℕ} (hd : g2CommDet a b ≠ 0) {fs : List Factor}
    (hok : g2CommListOk a b fs = true) {L : List (ℕ × ℕ)} (hL : L.Nodup)
    (hmem : ∀ p, p ∈ L ↔
      0 < p.1 ∧ 0 < p.2 ∧ IsRoot .G2 (p.1 • g2CommRoot a + p.2 • g2CommRoot b))
    (hnc : L.filter (g2CommNonCentral a b) = (g2CommExps fs).filter (g2CommNonCentral a b))
    (c d : K) :
    (fs.map fun f => xPar (rootOperatorFamily .G2) (g2CommRoot f.2.2.1)
        ((f.2.2.2 : K) * c ^ f.1 * d ^ f.2.1)).prod =
      (L.map fun p => xPar (rootOperatorFamily .G2) (p.1 • g2CommRoot a + p.2 • g2CommRoot b)
        ((g2CommCoeff fs p : K) * c ^ p.1 * d ^ p.2)).prod := by
  obtain ⟨hcone, hcomp, hnd, hcomm⟩ := g2CommListOk_spec hok
  have hroot : ∀ f ∈ fs, g2CommRoot f.2.2.1 = f.1 • g2CommRoot a + f.2.1 • g2CommRoot b :=
    fun f hf => by
      have hc := List.all_eq_true.1 hcone f hf
      simp only [coneOk, Bool.and_eq_true] at hc
      exact CFSG.LieType.Ree.vecBEq_iff.1 hc.2
  have h1 : (fs.map fun f => xPar (rootOperatorFamily .G2) (g2CommRoot f.2.2.1)
      ((f.2.2.2 : K) * c ^ f.1 * d ^ f.2.1)) = (g2CommExps fs).map fun p =>
        xPar (rootOperatorFamily .G2) (p.1 • g2CommRoot a + p.2 • g2CommRoot b)
          ((g2CommCoeff fs p : K) * c ^ p.1 * d ^ p.2) := by
    rw [g2CommExps, List.map_map]
    refine List.map_congr_left fun f hf => ?_
    simp only [Function.comp_apply, g2CommCoeff_of_mem hnd hf, hroot f hf]
  have hcomm' : ∀ x ∈ g2CommExps fs, g2CommNonCentral a b x = false → ∀ y ∈ g2CommExps fs,
      Commute (xPar (rootOperatorFamily .G2) (x.1 • g2CommRoot a + x.2 • g2CommRoot b)
          ((g2CommCoeff fs x : K) * c ^ x.1 * d ^ x.2))
        (xPar (rootOperatorFamily .G2) (y.1 • g2CommRoot a + y.2 • g2CommRoot b)
          ((g2CommCoeff fs y : K) * c ^ y.1 * d ^ y.2)) := by
    intro x hx hq y hy
    obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hx
    obtain ⟨f', hf', rfl⟩ := List.mem_map.1 hy
    rw [← hroot f hf, ← hroot f' hf']
    exact commute_of_g2CommCommute hcone hcomm hf hf' hq _ _
  have hperm : L.Perm (g2CommExps fs) := (List.perm_ext_iff_of_nodup hL hnd).2 fun p => by
    rw [hmem p, mem_g2CommExps_iff hd hcone hcomp p]
  rw [h1, prod_map_eq_filter_mul_filter_not _ (g2CommNonCentral a b) _ hcomm',
    prod_map_eq_filter_mul_filter_not L (g2CommNonCentral a b) _ fun x hx hq y hy =>
      hcomm' x (hperm.subset hx) hq y (hperm.subset hy), hnc]
  congr 1
  refine ((hperm.symm.filter _).map _).prod_eq' (List.pairwise_map.2
    (List.pairwise_of_forall_mem_list fun x hx y hy => ?_))
  have hx' := List.mem_filter.1 hx
  exact hcomm' x hx'.1 (by simpa using hx'.2) y (List.mem_filter.1 hy).1

end Group

open _root_.Classical in
noncomputable def g2CommConst
    (l : (Fin (Tag.rank .G2) → ℤ) → (Fin (Tag.rank .G2) → ℤ) → List (ℕ × ℕ))
    (α β : Fin (Tag.rank .G2) → ℤ) (p : ℕ × ℕ) : ℤ :=
  if h : IsRoot .G2 α ∧ IsRoot .G2 β then
    g2CommCoeff (g2CommChoose (l α β) (rootPos ⟨α, h.1⟩) (rootPos ⟨β, h.2⟩)) p
  else 1

theorem natAbs_g2CommConst
    (l : (Fin (Tag.rank .G2) → ℤ) → (Fin (Tag.rank .G2) → ℤ) → List (ℕ × ℕ))
    (α β : Fin (Tag.rank .G2) → ℤ) (p : ℕ × ℕ) :
    (g2CommConst l α β p).natAbs ∈ ({1, 2, 3} : Set ℕ) := by
  unfold g2CommConst
  split_ifs with h
  · have ha := rootPos_lt (⟨α, h.1⟩ : Root .G2)
    have hb := rootPos_lt (⟨β, h.2⟩ : Root .G2)
    rw [g2CommRoot_length] at ha hb
    obtain ⟨-, h1, h2⟩ := g2CommPairOk_of ha hb
    unfold g2CommChoose
    split_ifs
    · exact natAbs_g2CommCoeff h1 p
    · exact natAbs_g2CommCoeff h2 p
  · simp

theorem g2_exists_commutatorFormula
    (k : Type) [Field k]
    (O : CommOrder (RootSystem.ofCartan (g2Datum k).isFiniteType (g2Datum k).divisible)) :
    ∃ C : (Fin (g2Datum k).rank → ℤ) → (Fin (g2Datum k).rank → ℤ) → ℕ × ℕ → ℤ,
      (∀ α ∈ (RootSystem.ofCartan (g2Datum k).isFiniteType (g2Datum k).divisible).roots,
        ∀ β ∈ (RootSystem.ofCartan (g2Datum k).isFiniteType (g2Datum k).divisible).roots,
          ∀ p ∈ expPairs (RootSystem.ofCartan (g2Datum k).isFiniteType (g2Datum k).divisible) α β,
            (C α β p).natAbs ∈ ({1, 2, 3} : Set ℕ)) ∧
      CommutatorFormula (xPar (rootOperatorFamily .G2) (K := k)) O C := by
  have hΦ : (RootSystem.ofCartan (g2Datum k).isFiniteType (g2Datum k).divisible).roots =
      {γ | IsRoot .G2 γ} := adjDatum_roots _ k
  refine ⟨g2CommConst O.list, fun α _ β _ p _ => natAbs_g2CommConst O.list α β p, ?_⟩
  intro α hα β hβ hsum c d
  have hα' : IsRoot .G2 α := by rw [hΦ] at hα; exact hα
  have hβ' : IsRoot .G2 β := by rw [hΦ] at hβ; exact hβ
  by_cases hne : α = β
  · subst hne
    have hnil : O.list α α = [] := List.eq_nil_iff_forall_not_mem.2 fun p hp => by
      rw [O.mem_iff α hα α hα hsum] at hp
      obtain ⟨h1, h2, h3⟩ := hp
      rw [hΦ, ← add_nsmul] at h3
      have := eq_one_of_isRoot_nsmul (τ := .G2) h3
      omega
    rw [hnil, List.map_nil, List.prod_nil, commutatorElement_eq_one_iff_commute, Commute,
      SemiconjBy, ← xPar_add, ← xPar_add, add_comm]
  obtain ⟨a, ha⟩ : ∃ a, a = rootPos (⟨α, hα'⟩ : Root .G2) := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = rootPos (⟨β, hβ'⟩ : Root .G2) := ⟨_, rfl⟩
  have ha12 : a < 12 := by rw [ha, ← g2CommRoot_length]; exact rootPos_lt _
  have hb12 : b < 12 := by rw [hb, ← g2CommRoot_length]; exact rootPos_lt _
  have hra : g2CommRoot a = α := by rw [ha]; exact root_rootPos _
  have hrb : g2CommRoot b = β := by rw [hb]; exact root_rootPos _
  have hab : a ≠ b := fun h => hne (by rw [← hra, ← hrb, h])
  have hs : g2CommRoot a + g2CommRoot b ≠ 0 := by rw [hra, hrb]; exact hsum
  obtain ⟨hd, hok, -⟩ := g2CommPairOk_spec ha12 hb12 hab hs
  have hC : ∀ p, g2CommConst O.list α β p = g2CommCoeff (g2CommChoose (O.list α β) a b) p :=
    fun p => by rw [g2CommConst, dite_eq_left ⟨hα', hβ'⟩, ← ha, ← hb]
  simp only [hC]
  have hmem : ∀ p, p ∈ O.list α β ↔
      0 < p.1 ∧ 0 < p.2 ∧ IsRoot .G2 (p.1 • g2CommRoot a + p.2 • g2CommRoot b) := fun p => by
    rw [O.mem_iff α hα β hβ hsum, hra, hrb]
    change (_ ∧ _ ∧ _ ∈ _) ↔ _
    rw [hΦ]
    rfl
  unfold g2CommChoose
  split_ifs with hch
  · have hcomm := g2CommHolds_factors (K := k) ha12 hb12 hab hs c d
    rw [hra, hrb] at hcomm
    rw [hcomm, prod_g2CommFactors_eq hd hok (O.nodup α β) hmem hch c d, hra, hrb]
  · have h4 : (g2CommFactors a b).length = 4 := by
      by_contra h4
      have hq : g2CommNonCentral a b = fun _ => false :=
        funext fun p => by simp [g2CommNonCentral, h4]
      exact hch (by rw [hq]; simp)
    obtain ⟨hok', h2, hrev⟩ := g2CommSwapOk_spec ha12 hb12 hab hs h4
    have hsw : (O.list α β).filter (g2CommNonCentral a b) =
        (g2CommExps (g2CommSwapFactors a b)).filter (g2CommNonCentral a b) := by
      obtain ⟨x, y, hxy⟩ := List.length_eq_two.1 h2
      have hperm : ((O.list α β).filter (g2CommNonCentral a b)).Perm [x, y] := by
        rw [← hxy]
        refine (List.perm_ext_iff_of_nodup ((O.nodup α β).filter _)
          ((g2CommListOk_spec hok).2.2.1.filter _)).2 fun p => ?_
        rw [List.mem_filter, List.mem_filter, hmem p,
          mem_g2CommExps_iff hd (g2CommListOk_spec hok).1 (g2CommListOk_spec hok).2.1 p]
      rw [hrev, hxy]
      rcases List.perm_pair.1 hperm with h | h
      · exact absurd (h.trans hxy.symm) hch
      · exact h
    have hcomm := g2CommHolds_swapFactors (K := k) ha12 hb12 hab hs h4 c d
    rw [hra, hrb] at hcomm
    rw [hcomm, prod_g2CommFactors_eq hd hok' (O.nodup α β) hmem hsw c d, hra, hrb]

end CFSG.LieType.Steinberg.RankTwo
