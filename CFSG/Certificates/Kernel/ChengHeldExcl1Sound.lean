module

public import Certificates.Data.Kernel.ChengHeldCentK
public import Certificates.Data.ChengHeldExcl1Facts
public import CFSG.LocalAnalysis.OddStandard.ChengHeldModelStruct4
public import CFSG.Certificates.Kernel.Spor.PEnumSound
import CFSG.Certificates.Kernel.L34KSnd.Tab
public import CFSG.LocalAnalysis.OddStandard.ChengHeldModelMk

public section

namespace CFSG.KC.ChengHeld

open CFSG.OddStandard.ChengHeldData CFSG.OddStandard.ChengHeldData.RegModel
open CFSG.OddStandard.ChengHeld.Model
open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KS.PEnum CFSG.KC.L34KSnd
open CFSG.KLie.CT (andB orB notB)
open Subgroup

variable {n w : ℕ}

theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem tabRep_pcomp {x y : ℕ} {a b : Equiv.Perm (Fin n)} (hx : canonK n w (mask w) (n * w) x = true)
    (hy : canonK n w (mask w) (n * w) y = true) (ha : TabRep (unpack n w x) a)
    (hb : TabRep (unpack n w y) b) : TabRep (unpack n w (pcomp n w (mask w) x y)) (a * b) := by
  rw [← comp_unpack' hx hy]
  exact ha.comp hb

theorem beq_iff_perm {x y : ℕ} {a b : Equiv.Perm (Fin n)}
    (hx : canonK n w (mask w) (n * w) x = true) (hy : canonK n w (mask w) (n * w) y = true)
    (ha : TabRep (unpack n w x) a) (hb : TabRep (unpack n w y) b) : Nat.beq x y = true ↔ a = b := by
  rw [← beq_unpack hx hy]
  exact ha.beq_iff hb

variable {gens : Array Tab} {E : Enum} {p : ℕ → Equiv.Perm (Fin n)} {T PL G : ℕ → ℕ}

theorem exclXiM_of_centSqK (hd : RegData n gens E p) (hgs : gens.size = 7)
    (hE : E = penumRec n w n T PL) (hT : ∀ i < n, canonK n w (mask w) (n * w) (T i) = true)
    (hG : GensOK n w 7 G gens) (hsz : szOK n w = true)
    (hc : centSqK n w n T [pcomp n w (mask w) (G 0) (G 0), G 1, pcomp n w (mask w) (G 0) (G 2), G 6]
      [pidn n w, G 0, pcomp n w (mask w) (G 0) (G 0),
        pcomp n w (mask w) (pcomp n w (mask w) (G 0) (G 0)) (G 0)] = true) :
    exclXiM (mkRegGen n gens E) = true := by
  set M := mkRegGen n gens E with hM
  let R : Rep M ↥(permGroup n p gens.size) := hd.rep
  have hj7 : ∀ j < 7, j < gens.size := fun j hj => by omega
  let x : ℕ → ↥(permGroup n p gens.size) := fun j =>
    if hj : j < gens.size then ⟨p j, subset_closure ⟨j, hj, rfl⟩⟩ else 1
  have hx : ∀ j (hj : j < gens.size), ((x j : ↥(permGroup n p gens.size)) : Equiv.Perm (Fin n)) = p j :=
    fun j hj => by simp only [x, hj, ↓reduceDIte]
  have hpt : ∀ j < gens.size, R.pt (x j) = M.g j := by
    intro j hj
    change (((x j : ↥(permGroup n p gens.size)) : Equiv.Perm (Fin n)) ⟨0, hd.pos⟩ : ℕ) =
      (gens.map fun g => g[0]!)[j]!
    rw [hx j hj, getElem!_pos _ _ (by simpa using hj), Array.getElem_map, ← getElem!_pos gens j hj]
    exact ((hd.gensRep j hj).apply ⟨0, hd.pos⟩).symm
  have eV : R.set (secV M) =
      (closure {x 0 ^ 2, x 1, x 0 * x 2} : Set ↥(permGroup n p gens.size)) := by
    unfold secV
    rw [← hpt 0 (hj7 0 (by omega)), ← hpt 1 (hj7 1 (by omega)), ← hpt 2 (hj7 2 (by omega)),
      ← R.pt_pow, ← R.pt_mul]
    exact S4Aux.set_cl3 R _ _ _
  have nV : (secV M).size = M.N := by
    unfold secV
    rw [← hpt 0 (hj7 0 (by omega)), ← hpt 1 (hj7 1 (by omega)), ← hpt 2 (hj7 2 (by omega)),
      ← R.pt_pow, ← R.pt_mul]
    exact S4Aux.size_cl3 R _ _ _
  have eW := S4Aux.set_cent_of R nV eV
  have nW := Rep.cent_size (M := M) (secV M)
  have eZ : R.set (secZ M) = (zpowers (x 0) : Set ↥(permGroup n p gens.size)) := by
    unfold secZ
    rw [← hpt 0 (hj7 0 (by omega))]
    exact S4Aux.set_cl1 R _
  have hrec : ∀ h : ↥(permGroup n p gens.size), ∃ i < n,
      TabRep (unpack n w (T i)) (h : Equiv.Perm (Fin n)) := by
    intro h
    obtain ⟨i, hi, hti⟩ := hd.exists_idx h.2
    refine ⟨i, hi, ?_⟩
    have e : E.tabs[i]! = unpack n w (T i) := by
      subst hE
      rw [penumRec_eq, getElem!_pos _ _ (by simpa using hi), Array.getElem_ofFn]
    rw [← e]
    exact hti
  have hgen : ∀ j < 7, TabRep (unpack n w (G j)) (p j) ∧ canonK n w (mask w) (n * w) (G j) = true := by
    intro j hj
    obtain ⟨e, hcan⟩ := hG.2 j hj
    exact ⟨e ▸ hd.gensRep j (hj7 j hj), hcan⟩
  obtain ⟨g0, c0⟩ := hgen 0 (by omega)
  obtain ⟨g1, c1⟩ := hgen 1 (by omega)
  obtain ⟨g2, c2⟩ := hgen 2 (by omega)
  obtain ⟨g6, c6⟩ := hgen 6 (by omega)
  have c00 := canonK_pcomp c0 c0
  have g00 := tabRep_pcomp c0 c0 g0 g0
  have key : ∀ h : ↥(permGroup n p gens.size),
      h ∈ centralizer ((closure {x 0 ^ 2, x 1, x 0 * x 2} : Subgroup _) : Set _) →
      h * x 6 = x 6 * h → h * h ∈ zpowers (x 0) := by
    intro h hh h6
    have hcomm : ∀ y ∈ ({x 0 ^ 2, x 1, x 0 * x 2} : Set ↥(permGroup n p gens.size)),
        (y : Equiv.Perm (Fin n)) * h = h * y := fun y hy => by
      have := mem_centralizer_iff.1 hh y (subset_closure hy)
      exact congrArg Subtype.val this
    obtain ⟨i, hi, hti⟩ := hrec h
    have hci := hT i hi
    have hk := allN_spec hc i hi
    rw [strictB_eq, orB_iff, notB_iff] at hk
    have hcomm' : ∀ c ∈ [pcomp n w (mask w) (G 0) (G 0), G 1, pcomp n w (mask w) (G 0) (G 2), G 6],
        commP n w (T i) c = true := by
      intro c hc'
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc'
      have hgen' : ∀ {c : ℕ} {a : Equiv.Perm (Fin n)}, canonK n w (mask w) (n * w) c = true →
          TabRep (unpack n w c) a → (h : Equiv.Perm (Fin n)) * a = a * h → commP n w (T i) c = true :=
        fun hcc hta he => (beq_iff_perm (canonK_pcomp hci hcc) (canonK_pcomp hcc hci)
          (tabRep_pcomp hci hcc hti hta) (tabRep_pcomp hcc hci hta hti)).2 he
      rcases hc' with rfl | rfl | rfl | rfl
      · refine hgen' c00 g00 ?_
        have := hcomm (x 0 ^ 2) (by simp)
        rw [Subgroup.coe_pow, hx 0 (hj7 0 (by omega)), pow_two] at this
        exact this.symm
      · refine hgen' c1 g1 ?_
        have := hcomm (x 1) (by simp)
        rw [hx 1 (hj7 1 (by omega))] at this
        exact this.symm
      · refine hgen' (canonK_pcomp c0 c2) (tabRep_pcomp c0 c2 g0 g2) ?_
        have := hcomm (x 0 * x 2) (by simp)
        rw [Subgroup.coe_mul, hx 0 (hj7 0 (by omega)), hx 2 (hj7 2 (by omega))] at this
        exact this.symm
      · refine hgen' c6 g6 ?_
        have := congrArg Subtype.val h6
        rw [Subgroup.coe_mul, Subgroup.coe_mul, hx 6 (hj7 6 (by omega))] at this
        exact this
    rcases hk with hk | hk
    · rw [List.all_eq_true.2 hcomm'] at hk
      exact absurd hk (by decide)
    obtain ⟨z, hz, hzb⟩ := List.any_eq_true.1 hk
    have hsq := tabRep_pcomp hci hci hti hti
    have hpow : ∀ (k : ℕ) {z : ℕ}, canonK n w (mask w) (n * w) z = true →
        TabRep (unpack n w z) (p 0 ^ k) → Nat.beq (pcomp n w (mask w) (T i) (T i)) z = true →
        h * h ∈ zpowers (x 0) := by
      intro k z hzc htz hb
      have e := (beq_iff_perm (canonK_pcomp hci hci) hzc hsq htz).1 hb
      refine ⟨(k : ℤ), Subtype.ext ?_⟩
      change ((x 0 ^ (k : ℤ) : ↥(permGroup n p gens.size)) : Equiv.Perm (Fin n)) = _
      rw [zpow_natCast, Subgroup.coe_pow, hx 0 (hj7 0 (by omega)), Subgroup.coe_mul, e]
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact hpow 0 (canon_pidn hsz) (by rw [pow_zero, ← idTab_unpack' hsz]; exact TabRep.idTab) hzb
    · exact hpow 1 c0 (by rw [pow_one]; exact g0) hzb
    · exact hpow 2 c00 (by rw [pow_two]; exact g00) hzb
    · exact hpow 3 (canonK_pcomp c00 c0)
        (by rw [pow_succ, pow_two]; exact tabRep_pcomp c00 c0 g00 g0) hzb
  unfold exclXiM
  simp only [List.all_eq_true]
  intro a ha
  obtain ⟨h, rfl, hh⟩ := (R.mem_elems_iff_exists_pt nW).1 ha
  rw [eW] at hh
  rw [← hpt 6 (hj7 6 (by omega)), ← R.pt_mul, ← R.pt_mul, ← R.pt_mul]
  by_cases h6 : h * x 6 = x 6 * h
  · have hz : (secZ M)[R.pt (h * h)]! = true := by
      rw [← R.mem_set, eZ]
      exact key h hh h6
    rw [hz, Bool.or_true]
  · have hne : R.pt (h * x 6) ≠ R.pt (x 6 * h) := fun e => h6 (R.pt_inj e)
    simp [hne]

end CFSG.KC.ChengHeld

end
