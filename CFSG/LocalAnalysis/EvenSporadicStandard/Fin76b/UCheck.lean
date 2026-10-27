module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.UTableSpec
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.AutETableSound

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open AutETable

namespace UCheckAux

@[expose] def peqB (m : ℕ → ℕ → ℕ) (tI : ℕ) (x y : ℕ × ℕ) : Bool :=
  decide (x = y) || decide (y = (dMul x.1 2, m x.2 tI))

@[expose] def uVerify (m : ℕ → ℕ → ℕ) (tI : ℕ) (u : ℕ × ℕ) (φ : Array (ℕ × ℕ)) : Bool :=
  let f : ℕ → ℕ × ℕ := fun a => φ.getD a (0, 0)
  (List.range 32).all (fun a => decide ((f a).1 < 8) && decide ((f a).2 < 32)) &&
  (List.range 32).all (fun a => (List.range 32).all fun b =>
    peqB m tI (f (m a b)) (dMul (f a).1 (f b).1, m (f a).2 (f b).2)) &&
  (List.range 32).all (fun a => (List.range 32).all fun b =>
    !peqB m tI (f a) (f b) || decide (a = b)) &&
  (List.range 32).all (fun a =>
    peqB m tI (dMul (f a).1 u.1, m (f a).2 u.2) (dMul u.1 (f a).1, m u.2 (f a).2)) &&
  (List.range 32).all (fun a => !peqB m tI (f a) u)

@[expose] def uGlobal (m : ℕ → ℕ → ℕ) (tI : ℕ) : Bool :=
  decide (tI < 32) && decide (tI ≠ 0) && decide (m tI tI = 0) &&
  (List.range 32).all (fun a => (List.range 32).all fun b => decide (m a b < 32)) &&
  (List.range 32).all (fun a =>
    !((List.range 32).all fun b => m a b == m b a) || decide (a = 0) || decide (a = tI))

@[expose] def ucanon (m : ℕ → ℕ → ℕ) (tI p : ℕ) : ℕ :=
  if (p / 32) % 4 < 2 then p else 32 * dMul (p / 32) 2 + m (p % 32) tI

@[expose] def umul (m : ℕ → ℕ → ℕ) (tI p q : ℕ) : ℕ :=
  ucanon m tI (32 * dMul (p / 32) (q / 32) + m (p % 32) (q % 32))

@[expose] def ulvl (E NU : Array (Array ℕ)) (gens : List ℕ) (W : Array (List ℕ)) (p0 d : ℕ)
    (q : List ℕ) : Bool :=
  let X := tab 32 fun k => if inLv W d k then ev NU (fun i => q.getD i 0) (wd W k) else 0
  (List.range 32).all fun k => !inLv W d k ||
    ((k == 0 || ix X k != 0) && ix X k != p0 && mt NU (ix X k) p0 == mt NU p0 (ix X k) &&
      (List.range (d + 1)).all fun i =>
        !inLv W d (mt E k (gens.getD i 0)) ||
          ix X (mt E k (gens.getD i 0)) == mt NU (ix X k) (q.getD i 0))

@[expose] def udfs (E NU : Array (Array ℕ)) (gens : List ℕ) (W : Array (List ℕ)) (p0 : ℕ)
    (cands : List ℕ) : ℕ → List ℕ → Option (List ℕ)
  | 0, q => some q
  | f + 1, q => cands.findSome? fun c =>
      if ulvl E NU gens W p0 q.length (q ++ [c]) then udfs E NU gens W p0 cands f (q ++ [c])
      else none

@[expose] def usearch (m : ℕ → ℕ → ℕ) (tI : ℕ) (E NU : Array (Array ℕ)) (gens : List ℕ)
    (W : Array (List ℕ)) (u : ℕ × ℕ) : Option (Array (ℕ × ℕ)) :=
  let p0 := ucanon m tI (32 * u.1 + u.2)
  let cands := (List.range 256).filter fun c =>
    c != 0 && ucanon m tI c == c && c != p0 && mt NU c p0 == mt NU p0 c
  (udfs E NU gens W p0 cands gens.length []).map fun q =>
    (Array.range 32).map fun a =>
      let v := ev NU (fun i => q.getD i 0) (wd W a)
      (v / 32, v % 32)

@[expose] def uCheckAux (m : ℕ → ℕ → ℕ) (tI : ℕ) : Bool :=
  uGlobal m tI &&
    let E := tab2 32 m
    let gw := mkGens 32 E
    let W := gw.2.map fun o => o.getD []
    let NU := tab2 256 (umul m tI)
    (List.range 8).all fun i => (List.range 32).all fun k =>
      !(peqB m tI (dMul i i, m k k) (0, 0) && !peqB m tI (i, k) (0, 0) &&
          !peqB m tI (i, k) (0, tI)) ||
        (usearch m tI E NU gw.1 W (i, k)).any (uVerify m tI (i, k))

end UCheckAux

open UCheckAux

@[expose] def uCheck (mulE : ℕ → ℕ → ℕ) (tI : ℕ) : Bool :=
  uCheckAux (mt (tab2 32 mulE)) tI


namespace UCheckAux

theorem peqB_iff {m : ℕ → ℕ → ℕ} {tI : ℕ} {x y : ℕ × ℕ} :
    peqB m tI x y = true ↔ UPeq m tI x y := by
  simp [peqB, UPeq]

theorem uVerify_spec {m : ℕ → ℕ → ℕ} {tI : ℕ} {u : ℕ × ℕ} {φ : Array (ℕ × ℕ)}
    (h : uVerify m tI u φ = true) : UWitness m tI u (fun a => φ.getD a (0, 0)) := by
  unfold uVerify at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨fun a ha => ?_, fun a ha b hb => ?_, fun a ha b hb hab => ?_, fun a ha => ?_,
    fun a ha hu => ?_⟩
  · have := List.all_eq_true.1 h1 a (List.mem_range.2 ha)
    simpa using this
  · exact peqB_iff.1 (List.all_eq_true.1 (List.all_eq_true.1 h2 a (List.mem_range.2 ha)) b
      (List.mem_range.2 hb))
  · have := List.all_eq_true.1 (List.all_eq_true.1 h3 a (List.mem_range.2 ha)) b
      (List.mem_range.2 hb)
    have hp : peqB m tI (φ.getD a (0, 0)) (φ.getD b (0, 0)) = true := peqB_iff.2 hab
    rw [hp] at this
    simpa only [Bool.not_true, Bool.false_or, decide_eq_true_eq] using this
  · exact peqB_iff.1 (List.all_eq_true.1 h4 a (List.mem_range.2 ha))
  · have := List.all_eq_true.1 h5 a (List.mem_range.2 ha)
    have hp : peqB m tI (φ.getD a (0, 0)) u = true := peqB_iff.2 hu
    rw [hp] at this
    exact absurd this (by simp)

theorem uGlobal_spec {m : ℕ → ℕ → ℕ} {tI : ℕ} (h : uGlobal m tI = true) :
    tI < 32 ∧ tI ≠ 0 ∧ m tI tI = 0 ∧ (∀ a < 32, ∀ b < 32, m a b < 32) ∧
      ∀ a < 32, (∀ b < 32, m a b = m b a) → a = 0 ∨ a = tI := by
  unfold uGlobal at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨h1, h2, h3, fun a ha b hb => ?_, fun a ha hc => ?_⟩
  · have := List.all_eq_true.1 (List.all_eq_true.1 h4 a (List.mem_range.2 ha)) b
      (List.mem_range.2 hb)
    simpa using this
  · have := List.all_eq_true.1 h5 a (List.mem_range.2 ha)
    have hcen : ((List.range 32).all fun b => m a b == m b a) = true := by
      simp only [List.all_eq_true, List.mem_range, beq_iff_eq]
      exact hc
    simpa [hcen] using this


theorem any_exists {α : Type} {p : α → Bool} {o : Option α} (h : o.any p = true) :
    ∃ x, p x = true := by
  cases o with
  | none => simp at h
  | some x => exact ⟨x, h⟩

theorem uCheckAux_spec {m : ℕ → ℕ → ℕ} {tI : ℕ} (h : uCheckAux m tI = true) :
    (∀ a < 32, ∀ b < 32, m a b < 32) ∧ UTableSpec m tI := by
  unfold uCheckAux at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨hg, hall⟩ := h
  obtain ⟨htlt, htne, htsq, hclos, hcen⟩ := uGlobal_spec hg
  refine ⟨hclos, ⟨htlt, htne, htsq, hcen, ?_⟩⟩
  intro i hi k hk hg1 hg2 hg3
  have h2 := List.all_eq_true.1 (List.all_eq_true.1 hall i (List.mem_range.2 hi)) k
    (List.mem_range.2 hk)
  have e1 : peqB m tI (dMul i i, m k k) (0, 0) = true := peqB_iff.2 hg1
  have e2 : peqB m tI (i, k) (0, 0) = false := by
    cases hh : peqB m tI (i, k) (0, 0)
    · rfl
    · exact absurd (peqB_iff.1 hh) hg2
  have e3 : peqB m tI (i, k) (0, tI) = false := by
    cases hh : peqB m tI (i, k) (0, tI)
    · rfl
    · exact absurd (peqB_iff.1 hh) hg3
  rw [e1, e2, e3] at h2
  simp only [Bool.not_false, Bool.and_self, Bool.not_true, Bool.false_or] at h2
  obtain ⟨φ, hφ⟩ := any_exists h2
  exact ⟨_, uVerify_spec hφ⟩

end UCheckAux

open UCheckAux

theorem UPeq_congr {m m' : ℕ → ℕ → ℕ} {tI : ℕ} (htI : tI < 32)
    (hmm : ∀ a < 32, ∀ b < 32, m a b = m' a b) {x y : ℕ × ℕ} (hx : x.2 < 32) :
    UPeq m tI x y ↔ UPeq m' tI x y := by
  simp only [UPeq, hmm x.2 hx tI htI]

theorem UTableSpec_congr {m m' : ℕ → ℕ → ℕ} {tI : ℕ} (hlt : ∀ a < 32, ∀ b < 32, m a b < 32)
    (hmm : ∀ a < 32, ∀ b < 32, m a b = m' a b) (h : UTableSpec m tI) : UTableSpec m' tI where
  tI_lt := h.tI_lt
  tI_ne := h.tI_ne
  tI_sq := by rw [← hmm _ h.tI_lt _ h.tI_lt]; exact h.tI_sq
  center := fun a ha hc => h.center a ha fun b hb => by
    rw [hmm a ha b hb, hmm b hb a ha]; exact hc b hb
  wit := by
    intro i hi k hk g1 g2 g3
    have htI := h.tI_lt
    have hkk : m k k < 32 := hlt k hk k hk
    rw [← hmm k hk k hk] at g1
    have g1' : UPeq m tI (dMul i i, m k k) (0, 0) := (UPeq_congr htI hmm hkk).2 g1
    have g2' : ¬ UPeq m tI (i, k) (0, 0) := fun hh => g2 ((UPeq_congr htI hmm hk).1 hh)
    have g3' : ¬ UPeq m tI (i, k) (0, tI) := fun hh => g3 ((UPeq_congr htI hmm hk).1 hh)
    obtain ⟨φ, hφ⟩ := h.wit i hi k hk g1' g2' g3'
    refine ⟨φ, hφ.range, fun a ha b hb => ?_, fun a ha b hb hab => ?_, fun a ha => ?_,
      fun a ha hu => ?_⟩
    · have hc : m a b < 32 := hlt a ha b hb
      have := hφ.mul a ha b hb
      rw [hmm _ (hφ.range a ha).2 _ (hφ.range b hb).2] at this
      rw [← hmm a ha b hb]
      exact (UPeq_congr htI hmm (hφ.range _ hc).2).1 this
    · exact hφ.inj a ha b hb ((UPeq_congr htI hmm (hφ.range a ha).2).2 hab)
    · have hr := (hφ.range a ha).2
      have := hφ.comm a ha
      dsimp only at this
      rw [hmm _ hr k hk, hmm k hk _ hr] at this
      dsimp only
      have hx : (m' (φ a).2 k) < 32 := by
        rw [← hmm _ hr k hk]; exact hlt _ hr k hk
      exact (UPeq_congr htI hmm (x := (dMul (φ a).1 i, m' (φ a).2 k)) hx).1 this
    · exact hφ.ne a ha ((UPeq_congr htI hmm (hφ.range a ha).2).2 hu)

theorem uCheck_spec {mulE : ℕ → ℕ → ℕ} {tI : ℕ} (h : uCheck mulE tI = true) :
    UTableSpec mulE tI := by
  obtain ⟨hlt, hs⟩ := uCheckAux_spec h
  refine UTableSpec_congr hlt (fun a ha b hb => ?_) hs
  exact mt_tab2 mulE ha hb

end CFSG.EvenSporadicStandard.Fin76b
