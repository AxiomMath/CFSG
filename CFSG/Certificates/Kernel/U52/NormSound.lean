module

public import Certificates.Data.Kernel.U52.Norm
public import CFSG.Certificates.Kernel.Spor.RawOrbHead
import CFSG.Certificates.Kernel.F3152.SortSound
public import Mathlib.Algebra.Group.Action.Pointwise.Finset
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.KS.U52N

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw.Orb
open scoped Pointwise

theorem memN_iff {x : Nat} {s : List Nat} : memN x s = true ↔ x ∈ s := by
  induction s with
  | nil => exact ⟨fun h => absurd h Bool.false_ne_true, fun h => absurd h List.not_mem_nil⟩
  | cons p s ih =>
    change (Nat.beq x p || memN x s) = true ↔ x ∈ p :: s
    rw [Bool.or_eq_true, ih, Nat.beq_eq, List.mem_cons]

theorem testBit_keyOf (s : List Nat) (i : Nat) : (keyOf s).testBit i = true ↔ i ∈ s := by
  induction s with
  | nil =>
    change (0 : Nat).testBit i = true ↔ i ∈ ([] : List Nat)
    simp
  | cons p s ih =>
    change ((1 <<< p) ||| keyOf s).testBit i = true ↔ i ∈ p :: s
    rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow, Bool.or_eq_true,
      decide_eq_true_iff, ih, List.mem_cons]
    exact or_congr eq_comm Iff.rfl

theorem mem_iff_of_keyOf_eq {s t : List Nat} (h : keyOf s = keyOf t) (i : Nat) :
    i ∈ s ↔ i ∈ t := by
  rw [← testBit_keyOf, ← testBit_keyOf, h]

theorem keyOf_eq_of_mem_iff {s t : List Nat} (h : ∀ i, i ∈ s ↔ i ∈ t) : keyOf s = keyOf t :=
  Nat.eq_of_testBit_eq fun i => Bool.eq_iff_iff.2 (by rw [testBit_keyOf, testBit_keyOf]; exact h i)

variable {n w : Nat}

theorem prep_evP (hn : n < 16777216) (hw : n + 1 < 2 ^ w) {G : Nat → Nat}
    {g : Nat → Equiv.Perm (Fin n)} {cs : List Nat} (h : ∀ c ∈ cs, PRep n w (G c) (g c)) :
    PRep n w (evP n w (mask w) (pidn n w) G cs) (cs.map g).prod := by
  induction cs with
  | nil => exact prep_pidn hn hw
  | cons c cs ih =>
    change PRep n w (pcomp n w (mask w) (G c) (evP n w (mask w) (pidn n w) G cs))
      (g c * (cs.map g).prod)
    exact prep_pcomp (by omega) (h c List.mem_cons_self)
      (ih fun c' hc' => h c' (List.mem_cons_of_mem _ hc'))

theorem PRep.unique' {P : Nat} {g h : Equiv.Perm (Fin n)} (hg : PRep n w P g) (hh : PRep n w P h) :
    g = h :=
  Equiv.ext fun x => Fin.ext ((hg x).symm.trans (hh x))

theorem card_mul_card_inf_stab_le {α β : Type*} [Finite α] [Finite β] [MulAction (Equiv.Perm α) β]
    (K : Subgroup (Equiv.Perm α)) (b : β) (S : Finset β) (hS : ∀ p ∈ S, ∃ g ∈ K, g • b = p) :
    S.card * Nat.card ↥(K ⊓ MulAction.stabilizer (Equiv.Perm α) b) ≤ Nat.card K := by
  rw [← Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup K b), Nat.card_prod]
  apply Nat.mul_le_mul
  · have hsub : (S : Set β) ⊆ MulAction.orbit K b := by
      intro p hp
      obtain ⟨g, hg, rfl⟩ := hS p hp
      exact ⟨⟨g, hg⟩, rfl⟩
    calc S.card = Nat.card (S : Set β) := (Nat.card_coe_set_eq _).symm ▸ by simp
      _ ≤ Nat.card (MulAction.orbit K b) := Nat.card_mono (Set.toFinite _) hsub
  · apply le_of_eq
    refine Nat.card_congr
      { toFun := fun g => ⟨⟨g.1, g.2.1⟩, g.2.2⟩
        invFun := fun g => ⟨g.1.1, g.1.2, g.2⟩
        left_inv := fun g => rfl
        right_inv := fun g => rfl }

@[expose] noncomputable def fixSet (K : Subgroup (Equiv.Perm (Fin n))) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun p => ∀ k ∈ K, k p = p

theorem mem_fixSet {K : Subgroup (Equiv.Perm (Fin n))} {p : Fin n} :
    p ∈ fixSet K ↔ ∀ k ∈ K, k p = p := by
  classical
  unfold fixSet
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

theorem mem_stabilizer_fixSet {K : Subgroup (Equiv.Perm (Fin n))} {x : Equiv.Perm (Fin n)}
    (hx : ∀ k ∈ K, x * k * x⁻¹ ∈ K) : x ∈ MulAction.stabilizer (Equiv.Perm (Fin n)) (fixSet K) := by
  classical
  have hsub : x⁻¹ • fixSet K ⊆ fixSet K := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_smul_finset.1 hq
    rw [mem_fixSet] at hp ⊢
    intro k hk
    have h1 := hp _ (hx k hk)
    rw [Equiv.Perm.smul_def]
    calc k (x⁻¹ p) = x⁻¹ ((x * k * x⁻¹) p) := by simp [Equiv.Perm.mul_apply]
      _ = x⁻¹ p := by rw [h1]
  have heq : x⁻¹ • fixSet K = fixSet K :=
    Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_smul_finset])
  rw [MulAction.mem_stabilizer_iff]
  calc x • fixSet K = x • (x⁻¹ • fixSet K) := by rw [heq]
    _ = fixSet K := by rw [smul_inv_smul]

theorem mem_stabilizer_of_maps {s : Finset (Fin n)} {x : Equiv.Perm (Fin n)}
    (hx : ∀ p ∈ s, x p ∈ s) : x ∈ MulAction.stabilizer (Equiv.Perm (Fin n)) s := by
  have hsub : x • s ⊆ s := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_smul_finset.1 hq
    exact hx p hp
  rw [MulAction.mem_stabilizer_iff]
  exact Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_smul_finset])

@[expose] def finOf (n : Nat) (s : List Nat) : Finset (Fin n) :=
  Finset.univ.filter fun x => (x : Nat) ∈ s

theorem mem_finOf {s : List Nat} {x : Fin n} : x ∈ finOf n s ↔ (x : Nat) ∈ s := by
  simp [finOf]

theorem evP_shr (hn : n < 16777216) (hw : n + 1 < 2 ^ w) (G : Nat → Nat) (cs : List Nat) :
    evP n w (mask w) (pidn n w) G cs >>> (n * w) = 0 := by
  cases cs with
  | nil => exact CFSG.KS.PF.pidn_shr hn hw
  | cons c cs => exact CFSG.KS.PF.pcomp_shr _ _ (by omega) (CFSG.KS.PF.w_pos hw)

theorem eq_of_prep (hw : n + 1 < 2 ^ w) {P Q : Nat} {g : Equiv.Perm (Fin n)}
    (hP0 : P >>> (n * w) = 0) (hQ0 : Q >>> (n * w) = 0) (hP : PRep n w P g)
    (hQ : PRep n w Q g) : P = Q :=
  CFSG.KS.PF.eq_of_fields (CFSG.KS.PF.w_pos hw) hP0 hQ0 fun i hi =>
    (hP ⟨i, hi⟩).trans (hQ ⟨i, hi⟩).symm

theorem gensOK_sound (hn : n < 16777216) (hw : n + 1 < 2 ^ w) {LP : Nat → Nat}
    {ok : Nat → Bool} {g : Nat → Equiv.Perm (Fin n)}
    (hg : ∀ c, ok c = true → PRep n w (LP c) (g c)) :
    ∀ {vs : List Nat} {wss : List (List Nat)},
      gensOK n w (mask w) (pidn n w) LP ok vs wss = true → vs.length = wss.length ∧
        ∀ j < vs.length, PRep n w (vs.getD j 0) ((wss.getD j []).map g).prod ∧
          ∀ c ∈ wss.getD j [], ok c = true
  | [], [], _ => ⟨rfl, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  | [], _ :: _, h => by simp [gensOK] at h
  | _ :: _, [], h => by simp [gensOK] at h
  | v :: vs, ws :: wss, h => by
    simp only [gensOK, Bool.and_eq_true, Nat.beq_eq, List.all_eq_true] at h
    obtain ⟨⟨rfl, hok⟩, hrest⟩ := h
    obtain ⟨hlen, ih⟩ := gensOK_sound hn hw hg hrest
    refine ⟨by simp [hlen], fun j hj => ?_⟩
    cases j with
    | zero => exact ⟨prep_evP hn hw fun c hc => hg c (hok c hc), hok⟩
    | succ j => exact ih j (by simpa using hj)

theorem stabOK_sound (hn : n < 16777216) (hw : n + 1 < 2 ^ w) {F SV : List Nat}
    {EW : List (List Nat)} {sv : Nat → Equiv.Perm (Fin n)}
    (hsv : ∀ j < SV.length, PRep n w (SV.getD j 0) (sv j))
    (h : stabOK n w (mask w) (pidn n w) F SV EW = true) :
    (∀ i < EW.length, PRep n w ((elems n w (mask w) (pidn n w) SV EW).getD i 0)
        ((EW.getD i []).map sv).prod ∧
      (elems n w (mask w) (pidn n w) SV EW).getD i 0 >>> (n * w) = 0) ∧
    (∀ i < EW.length, ∀ c ∈ EW.getD i [], c < SV.length) ∧
    (∀ i < EW.length, ∀ x : Fin n, (x : Nat) ∈ F → (((EW.getD i []).map sv).prod x : Nat) ∈ F) ∧
    (∀ i < EW.length, ∀ j < EW.length,
      ((EW.getD i []).map sv).prod = ((EW.getD j []).map sv).prod → i = j) := by
  unfold stabOK at h
  simp only [Bool.and_eq_true, List.all_eq_true, Nat.blt_eq] at h
  obtain ⟨hc, hmaps, hsort⟩ := h
  have hlt : ∀ i < EW.length, ∀ c ∈ EW.getD i [], c < SV.length := fun i hi c hc' =>
    hc _ (by rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem _) c hc'
  have hel : ∀ i < EW.length, (elems n w (mask w) (pidn n w) SV EW).getD i 0 =
      evP n w (mask w) (pidn n w) (fun c => SV.getD c 0) (EW.getD i []) := fun i hi => by
    rw [elems, List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map,
      List.getD_eq_getElem _ _ hi]
  have hprep : ∀ i < EW.length, PRep n w ((elems n w (mask w) (pidn n w) SV EW).getD i 0)
      ((EW.getD i []).map sv).prod := fun i hi => by
    rw [hel i hi]
    exact prep_evP hn hw fun c hc' => hsv c (hlt i hi c hc')
  have hshr : ∀ i < EW.length,
      (elems n w (mask w) (pidn n w) SV EW).getD i 0 >>> (n * w) = 0 := fun i hi => by
    rw [hel i hi]
    exact evP_shr hn hw _ _
  have hmem : ∀ i < EW.length, (elems n w (mask w) (pidn n w) SV EW).getD i 0 ∈
      elems n w (mask w) (pidn n w) SV EW := fun i hi => by
    rw [List.getD_eq_getElem _ _ (by simpa [elems] using hi)]
    exact List.getElem_mem _
  refine ⟨fun i hi => ⟨hprep i hi, hshr i hi⟩, hlt, fun i hi x hx => ?_, fun i hi j hj he => ?_⟩
  · have := memN_iff.1 (hmaps _ (hmem i hi) x hx)
    rwa [hprep i hi x] at this
  · have hnd := CFSG.KS.F3152.nodup_of_sortedK hsort
    have heq : (elems n w (mask w) (pidn n w) SV EW).getD i 0 =
        (elems n w (mask w) (pidn n w) SV EW).getD j 0 :=
      eq_of_prep hw (hshr i hi) (hshr j hj) (hprep i hi) (by rw [he]; exact hprep j hj)
    have hli : i < (elems n w (mask w) (pidn n w) SV EW).length := by simpa [elems] using hi
    have hlj : j < (elems n w (mask w) (pidn n w) SV EW).length := by simpa [elems] using hj
    rw [List.getD_eq_getElem _ _ hli, List.getD_eq_getElem _ _ hlj] at heq
    exact (List.Nodup.getElem_inj_iff hnd).1 heq

theorem kOK_sound (hn : n < 16777216) (hw : n + 1 < 2 ^ w) {KL KG F : List Nat}
    {κ kg : Nat → Equiv.Perm (Fin n)} (hκ : ∀ m < KL.length, PRep n w (KL.getD m 0) (κ m))
    (hkg : ∀ j < KG.length, PRep n w (KG.getD j 0) (kg j))
    (h : kOK n w (mask w) (pidn n w) KL KG F = true) :
    (∃ m < KL.length, κ m = 1) ∧
    (∀ m < KL.length, ∀ j < KG.length, ∃ m' < KL.length, κ m * kg j = κ m') ∧
    (∀ x : Fin n, (x : Nat) ∈ F ↔ ∀ j < KG.length, kg j x = x) := by
  unfold kOK at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨hid, hcl⟩, -, hfix⟩ := h
  have hidx : ∀ {P : Nat}, P ∈ KL → ∃ m < KL.length, KL.getD m 0 = P := fun hP => by
    obtain ⟨m, hm, he⟩ := List.mem_iff_getElem.1 hP
    exact ⟨m, hm, by rw [List.getD_eq_getElem _ _ hm, he]⟩
  have hmemKL : ∀ m < KL.length, KL.getD m 0 ∈ KL := fun m hm => by
    rw [List.getD_eq_getElem _ _ hm]
    exact List.getElem_mem _
  have hmemKG : ∀ j < KG.length, KG.getD j 0 ∈ KG := fun j hj => by
    rw [List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem _
  refine ⟨?_, fun m hm j hj => ?_, fun x => ?_⟩
  · obtain ⟨m, hm, he⟩ := hidx (memN_iff.1 hid)
    exact ⟨m, hm, PRep.unique' (hκ m hm) (by rw [he]; exact prep_pidn hn hw)⟩
  · obtain ⟨m', hm', he⟩ := hidx (memN_iff.1 (hcl _ (hmemKL m hm) _ (hmemKG j hj)))
    refine ⟨m', hm', PRep.unique' (prep_pcomp (by omega) (hκ m hm) (hkg j hj)) ?_⟩
    rw [← he]
    exact hκ m' hm'
  · have hx := CFSG.KS.allN_spec hfix x x.2
    beta_reduce at hx
    have key : ∀ a b : Bool, Bool.rec (motive := fun _ => Bool) (!a) a b = true ↔ b = a := by
      decide
    rw [key] at hx
    have hA : (KG.all fun g => Nat.beq (pg w (mask w) g x) x) = true ↔
        ∀ j < KG.length, kg j x = x := by
      rw [List.all_eq_true]
      constructor
      · intro H j hj
        have := H _ (hmemKG j hj)
        rw [Nat.beq_eq, hkg j hj x] at this
        exact Fin.ext this
      · intro H g hg
        obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hg
        rw [Nat.beq_eq, ← List.getD_eq_getElem _ 0 hj, hkg j hj x, H j hj]
    rw [← hA, ← memN_iff, hx]

theorem treeGo_spec {m : Nat} {LP : Nat → Nat} {ok : Nat → Bool} {nodes : List (List Nat)} :
    ∀ {t : Nat} {ns : List (List Nat)} {ps gs : List Nat},
      treeGo w m LP ok nodes t ns ps gs = true → ∀ j < ns.length, ps.getD j 0 < t + j ∧
        ok (gs.getD j 0) = true ∧
        keyOf (imgL w m (LP (gs.getD j 0)) (nodes.getD (ps.getD j 0) [])) = keyOf (ns.getD j [])
  | t, s :: ns, p :: ps, g :: gs, h, j, hj => by
    simp only [treeGo, Bool.and_eq_true, Nat.blt_eq] at h
    obtain ⟨⟨⟨hp, hok⟩, hk⟩, hrest⟩ := h
    cases j with
    | zero =>
      simp only [List.getD_cons_zero]
      exact ⟨by omega, hok, Nat.eq_of_beq_eq_true hk⟩
    | succ j =>
      obtain ⟨a, b, c⟩ := treeGo_spec hrest j (by simp only [List.length_cons] at hj; omega)
      simp only [List.getD_cons_succ]
      exact ⟨by omega, b, c⟩
  | _, [], _, _, _, j, hj => absurd hj (Nat.not_lt_zero _)
  | _, _ :: _, [], _, h, _, _ => by simp [treeGo] at h
  | _, _ :: _, _ :: _, [], h, _, _ => by simp [treeGo] at h

theorem treeOK_sound (hn : n < 16777216) (hw : n + 1 < 2 ^ w) {LP : Nat → Nat}
    {ok : Nat → Bool} {g : Nat → Equiv.Perm (Fin n)} (H : Subgroup (Equiv.Perm (Fin n)))
    (hg : ∀ c, ok c = true → PRep n w (LP c) (g c) ∧ g c ∈ H) {F : List Nat}
    {nodes : List (List Nat)} {par gen : List Nat}
    (h : treeOK n w (mask w) LP ok F nodes par gen = true) :
    ∃ S : Finset (Finset (Fin n)), S.card = nodes.length ∧
      ∀ s ∈ S, ∃ k ∈ H, k • finOf n F = s := by
  classical
  rcases nodes with _ | ⟨s, ns⟩ <;> rcases par with _ | ⟨p0, ps⟩ <;>
    rcases gen with _ | ⟨g0, gs⟩ <;> try (simp [treeOK] at h; done)
  simp only [treeOK] at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨hkey0, hF⟩, htree, hsort⟩ := h
  replace hkey0 := Nat.eq_of_beq_eq_true hkey0
  replace hF : ∀ p ∈ F, p < n := fun p hp => Nat.le_of_ble_eq_true ((List.all_eq_true.1 hF) p hp)
  have hspec := treeGo_spec htree
  have hinv : ∀ t < (s :: ns).length, ∃ k ∈ H, ∀ i,
      i ∈ (s :: ns).getD t [] ↔ ∃ x : Fin n, (x : ℕ) ∈ F ∧ (k x : ℕ) = i := by
    intro t
    induction t using Nat.strong_induction_on with
    | _ t ih =>
      intro ht
      rcases t with _ | j
      · refine ⟨1, H.one_mem, fun i => ?_⟩
        rw [List.getD_cons_zero, mem_iff_of_keyOf_eq hkey0 i]
        constructor
        · intro hi
          exact ⟨⟨i, hF i hi⟩, hi, rfl⟩
        · rintro ⟨x, hx, rfl⟩
          exact hx
      · have hj : j < ns.length := by simpa using ht
        obtain ⟨hp, hok, hk⟩ := hspec j hj
        obtain ⟨k, hkH, hk'⟩ := ih (ps.getD j 0) (by omega) (by simp only [List.length_cons]; omega)
        obtain ⟨hgP, hgH⟩ := hg _ hok
        refine ⟨g (gs.getD j 0) * k, H.mul_mem hgH hkH, fun i => ?_⟩
        rw [List.getD_cons_succ, ← mem_iff_of_keyOf_eq hk i, imgL, List.mem_map]
        constructor
        · rintro ⟨y, hy, rfl⟩
          obtain ⟨x, hx, rfl⟩ := (hk' y).1 hy
          exact ⟨x, hx, (hgP (k x)).symm⟩
        · rintro ⟨x, hx, rfl⟩
          exact ⟨_, (hk' _).2 ⟨x, hx, rfl⟩, hgP (k x)⟩
  have hmem : ∀ a ∈ s :: ns, ∃ k ∈ H, ∀ i,
      i ∈ a ↔ ∃ x : Fin n, (x : ℕ) ∈ F ∧ (k x : ℕ) = i := by
    intro a ha
    obtain ⟨t, ht, rfl⟩ := List.mem_iff_getElem.1 ha
    have := hinv t ht
    rwa [List.getD_eq_getElem _ _ ht] at this
  have hlt : ∀ c ∈ s :: ns, ∀ i ∈ c, i < n := fun c hc i hi => by
    obtain ⟨k, -, hk⟩ := hmem c hc
    obtain ⟨x, -, rfl⟩ := (hk i).1 hi
    exact (k x).2
  have key : ∀ {a b : List Nat}, a ∈ s :: ns → finOf n a = finOf n b → ∀ i ∈ a, i ∈ b := by
    intro a b ha he i hi
    have hb : (⟨i, hlt a ha i hi⟩ : Fin n) ∈ finOf n b := he ▸ mem_finOf.2 hi
    exact mem_finOf.1 hb
  have hnd := CFSG.KS.F3152.nodup_of_sortedK hsort
  refine ⟨((s :: ns).map (finOf n)).toFinset, ?_, ?_⟩
  · rw [List.toFinset_card_of_nodup, List.length_map]
    refine List.Nodup.map_on ?_ (List.Nodup.of_map _ hnd)
    intro a ha b hb he
    exact List.inj_on_of_nodup_map hnd ha hb (keyOf_eq_of_mem_iff fun i =>
      ⟨fun hi => key ha he i hi, fun hi => key hb he.symm i hi⟩)
  · intro t ht
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 ht)
    obtain ⟨k, hkH, hk⟩ := hmem a ha
    refine ⟨k, hkH, Finset.ext fun x => ?_⟩
    rw [Finset.mem_smul_finset, mem_finOf (s := a), hk]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, mem_finOf.1 hy, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      exact ⟨y, mem_finOf.2 hy, Fin.ext hyx⟩

end CFSG.KS.U52N

end
