module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.M11Check
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.M11Glue
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.CheckSpec

public section

namespace CFSG.EvenSporadicStandard.HNRecog

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native

@[expose] noncomputable def m11K : Subgroup (Equiv.Perm (Fin 1408)) :=
  closure (elemW '' {w | w ∈ [y0Word, vWord]})

@[expose] def probeG {G : Type*} [Group G] (y j : G) (p : List ℕ) : G :=
  (p.map fun e => y ^ e * j).prod

@[expose] noncomputable def m11Prop (g : Equiv.Perm (Fin 1408)) : Prop :=
  (∃ p ∈ m11Probes, ¬ TwoHSData.M11Order (orderOf (probeG (elemW y0Word) g p))) ∨
    g ∈ m11K ∨ elemW n1Word * g * (elemW n1Word)⁻¹ ∈ m11K

theorem ordInS_iff {idt x : Table} {g : Equiv.Perm (Fin 1408)}
    (hi : Rep 1408 idt (1 : Equiv.Perm (Fin 1408))) (hx : Rep 1408 x g) :
    ordInS idt x = true ↔ TwoHSData.M11Order (orderOf g) := by
  have key : ∀ k : ℕ, tblEq 1408 (powT 1408 k x) idt = true ↔ orderOf g ∣ k := fun k => by
    rw [tblEq_iff_eq (Rep.powT (by norm_num) hx k) hi, orderOf_dvd_iff_pow_eq_one]
  simp only [ordInS, Bool.or_eq_true, key]
  unfold TwoHSData.M11Order
  generalize orderOf g = n
  constructor
  · rintro (((h | h) | h) | h) <;>
      (have := Nat.le_of_dvd (by norm_num) h; interval_cases n <;> omega)
  · rintro (h | h | h | h | h | h | h | h) <;> subst h <;> decide

theorem ordAllOK_iff {idt : Table} {L : Array Table} {S : Set (Equiv.Perm (Fin 1408))}
    (hi : Rep 1408 idt (1 : Equiv.Perm (Fin 1408))) (hL : IsEnumSet 1408 L S) :
    ordAllOK idt L = true ↔ ∀ g ∈ S, TwoHSData.M11Order (orderOf g) :=
  hL.forall_iff (ordInS idt) _ (fun _ _ hx => ordInS_iff hi hx)

private theorem rep_foldl_probe {ys : Array Table} {tj : Table} {y j : Equiv.Perm (Fin 1408)}
    (hys : ∀ e < ys.size, Rep 1408 ys[e]! (y ^ e)) (hj : Rep 1408 tj j) :
    ∀ (p : List ℕ), (∀ e ∈ p, e < ys.size) → ∀ (acc : Table) (accG : Equiv.Perm (Fin 1408)),
      Rep 1408 acc accG →
      Rep 1408 (p.foldl (fun acc e => compT 1408 acc (compT 1408 ys[e]! tj)) acc)
        (accG * probeG y j p) := by
  intro p
  induction p with
  | nil => intro _ acc accG h; simpa [probeG] using h
  | cons e p ih =>
    intro hp acc accG h
    have he : e < ys.size := hp e (by simp)
    have h' : Rep 1408 (compT 1408 acc (compT 1408 ys[e]! tj)) (accG * (y ^ e * j)) :=
      Rep.compT h (Rep.compT (hys e he) hj)
    have := ih (fun e' he' => hp e' (by simp [he'])) _ _ h'
    simpa [probeG, mul_assoc] using this

theorem rep_probeT {ys : Array Table} {tj : Table} {y j : Equiv.Perm (Fin 1408)}
    (hys : ∀ e < ys.size, Rep 1408 ys[e]! (y ^ e)) (hj : Rep 1408 tj j) (p : List ℕ)
    (hp : ∀ e ∈ p, e < ys.size) : Rep 1408 (probeT ys tj p) (probeG y j p) := by
  have := rep_foldl_probe hys hj p hp _ 1 (Rep.idT (by norm_num))
  simpa [probeT] using this

theorem m11ClassOK_iff {idt n1 n1i : Table} {ys L0 Lc : Array Table}
    {y n : Equiv.Perm (Fin 1408)} {K S : Set (Equiv.Perm (Fin 1408))}
    (hi : Rep 1408 idt (1 : Equiv.Perm (Fin 1408))) (hn : Rep 1408 n1 n)
    (hni : Rep 1408 n1i n⁻¹)
    (hys : ∀ e < ys.size, Rep 1408 ys[e]! (y ^ e)) (hysz : ys.size = 6)
    (hL0 : IsEnumSet 1408 L0 K) (hLc : IsEnumSet 1408 Lc S) :
    m11ClassOK idt n1 n1i ys L0 Lc = true ↔ ∀ g ∈ S,
      (∃ p ∈ m11Probes, ¬ TwoHSData.M11Order (orderOf (probeG y g p))) ∨ g ∈ K ∨
        n * g * n⁻¹ ∈ K := by
  refine hLc.forall_iff (m11JOK idt n1 n1i ys L0) _ ?_
  intro x g hx
  have hp : ∀ p ∈ m11Probes, ∀ e ∈ p, e < ys.size := by
    rw [hysz]
    unfold m11Probes
    decide
  have hb : ∀ p ∈ m11Probes, ((!ordInS idt (probeT ys x p)) = true ↔
      ¬ TwoHSData.M11Order (orderOf (probeG y g p))) := by
    intro p hpm
    rw [← ordInS_iff hi (rep_probeT hys hx p (hp p hpm))]
    simp
  simp only [m11JOK, Bool.or_eq_true, List.any_eq_true]
  rw [hL0.memT_iff hx, hL0.memT_iff (rep_conjT hn hni hx)]
  constructor
  · rintro ((⟨p, hpm, h⟩ | h) | h)
    · exact Or.inl ⟨p, hpm, (hb p hpm).1 h⟩
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · rintro (⟨p, hpm, h⟩ | h | h)
    · exact Or.inl (Or.inl ⟨p, hpm, (hb p hpm).2 h⟩)
    · exact Or.inl (Or.inr h)
    · exact Or.inr h

theorem rep_powsT {ty : Table} {y : Equiv.Perm (Fin 1408)} (hy : Rep 1408 ty y) :
    (powsT ty).size = 6 ∧ ∀ e < (powsT ty).size, Rep 1408 (powsT ty)[e]! (y ^ e) := by
  refine ⟨by simp [powsT], fun e he => ?_⟩
  have he6 : e < 6 := by simpa [powsT] using he
  have key : (powsT ty)[e]! = powT 1408 e ty := by
    interval_cases e <;> simp [powsT]
  rw [key]
  exact Rep.powT (by norm_num) hy e

theorem conjEqOK_parts {c : List ℕ} {tx ty : Table} (h : conjEqOK c tx ty = true) :
    wordOK c = true ∧ invOK 1408 (tabW c) (invT 1408 (tabW c)) = true := by
  simp only [conjEqOK, Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2⟩

private theorem rep_foldl_rel {ta tb tai tbi : Table} {α β : Equiv.Perm (Fin 1408)}
    (ha : Rep 1408 ta α) (hb : Rep 1408 tb β) (hai : Rep 1408 tai α⁻¹)
    (hbi : Rep 1408 tbi β⁻¹) :
    ∀ (w : List (ℕ × Bool)) (acc : Table) (accG : Equiv.Perm (Fin 1408)), Rep 1408 acc accG →
      Rep 1408 (w.foldl (fun acc l => compT 1408 acc
        (if l.1 = 0 then (if l.2 then ta else tai) else if l.1 = 1 then (if l.2 then tb else tbi)
          else idT 1408)) acc)
        (accG * CFSG.Sporadic.Bridge.wordProd
          (fun i => if i = 0 then α else if i = 1 then β else 1) w) := by
  intro w
  induction w with
  | nil => intro acc accG h; simpa [CFSG.Sporadic.Bridge.wordProd] using h
  | cons l w ih =>
    intro acc accG h
    have hl : Rep 1408 (if l.1 = 0 then (if l.2 then ta else tai) else if l.1 = 1 then
        (if l.2 then tb else tbi) else idT 1408)
        (if l.2 then (if l.1 = 0 then α else if l.1 = 1 then β else 1)
          else (if l.1 = 0 then α else if l.1 = 1 then β else 1)⁻¹) := by
      by_cases h0 : l.1 = 0
      · cases hl2 : l.2 <;> simp [h0, ha, hai, hl2]
      · by_cases h1 : l.1 = 1
        · cases hl2 : l.2 <;> simp [h0, h1, hb, hbi, hl2]
        · cases hl2 : l.2 <;> simp [h0, h1, hl2, Rep.idT (by norm_num : 1408 < 2 ^ 32)]
    have := ih _ _ (Rep.compT h hl)
    simpa [CFSG.Sporadic.Bridge.wordProd, mul_assoc] using this

theorem rep_relTab {ta tb tai tbi : Table} {α β : Equiv.Perm (Fin 1408)}
    (ha : Rep 1408 ta α) (hb : Rep 1408 tb β) (hai : Rep 1408 tai α⁻¹) (hbi : Rep 1408 tbi β⁻¹)
    (w : List (ℕ × Bool)) :
    Rep 1408 (relTab ta tb tai tbi w) (CFSG.Sporadic.Bridge.wordProd
      (fun i => if i = 0 then α else if i = 1 then β else 1) w) := by
  have := rep_foldl_rel ha hb hai hbi w _ 1 (Rep.idT (by norm_num))
  simpa [relTab] using this

end CFSG.EvenSporadicStandard.HNRecog
