module

public import Certificates.Data.Kernel.M24G.KzeroDeriv
import CFSG.Certificates.Kernel.M24G.FixOctSound
import CFSG.Certificates.Kernel.M24G.KzeroSound
import CFSG.Certificates.Kernel.M24G.OrbitsSound
import Mathlib.Algebra.Order.Ring.Nat

public section

namespace CFSG.KC.M24G

open CFSG.Quasithin.H13.AS91.M24G

theorem duadEqT_iff {a b : Array Nat} : duadEqT a b = true ↔ a = b := by
  unfold duadEqT
  rw [beq_iff_eq, Array.toList_inj]

@[expose] def kzToArr (D : List KzE) : Array Native.KzEntry :=
  (D.map fun e => (⟨e.1, e.2.1, e.2.2.1, e.2.2.2⟩ : Native.KzEntry)).toArray

theorem kzToArr_get (D : List KzE) {j : Nat} (hj : j < D.length) :
    (kzToArr D)[j]! = ⟨D[j].1, D[j].2.1, D[j].2.2.1, D[j].2.2.2⟩ := by
  unfold kzToArr
  rw [toArray_getElem! _ (by simpa using hj), List.getElem_map]

theorem kzRowsOK_get (hs : List (Array Nat × Array Nat)) (D : List KzE) :
    ∀ (es : List KzE) (i : Nat), kzRowsOK hs D es i = true →
      ∀ m (hm : m < es.length), kzRowOK hs D (i + m) es[m] = true
  | [], _, _, _, hm => absurd hm (by simp)
  | e :: es, i, h, m, hm => by
    simp only [kzRowsOK, Bool.and_eq_true] at h
    cases m with
    | zero => simpa using h.1
    | succ m =>
      have := kzRowsOK_get hs D es (i + 1) h.2 m (by simpa using hm)
      rw [show i + (m + 1) = i + 1 + m by omega]
      simpa using this

theorem kzDeriv_sound {hs : List (Array Nat × Array Nat)} {K : List (Array Nat)} {k : Array Nat}
    {D : List KzE} (h : kzDerivF hs K k D = true) :
    ∃ D' : Array Native.KzEntry, Native.kzeroDerivValid hs k D' = true ∧
      ∀ x ∈ K, ∃ j < D'.size, D'[j]!.tab = x := by
  cases D with
  | nil => simp [kzDerivF] at h
  | cons e es =>
    simp only [kzDerivF, Bool.and_eq_true, List.all_eq_true, List.any_eq_true] at h
    obtain ⟨⟨h0, hrows⟩, hcov⟩ := h
    have hrow := kzRowsOK_get hs (e :: es) es 1 hrows
    have hsz : (kzToArr (e :: es)).size = es.length + 1 := by simp [kzToArr]
    have hget : ∀ j (hj : j < es.length + 1),
        (kzToArr (e :: es))[j]!.tab = ((e :: es)[j]'(by simpa using hj)).1 :=
      fun j hj => by rw [kzToArr_get _ (by simpa using hj)]
    have hgetD : ∀ b (hb : b < es.length + 1),
        ((e :: es).getD b default).1 = ((e :: es)[b]'(by simpa using hb)).1 :=
      fun b hb => by rw [duad_getD_lt _ _ (by simpa using hb)]
    refine ⟨kzToArr (e :: es), ?_, ?_⟩
    · unfold Native.kzeroDerivValid
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, allLt_iff', Bool.or_eq_true]
      refine ⟨⟨by omega, ?_⟩, fun j hj => ?_⟩
      · rw [hget 0 (by omega)]
        exact duadEqT_iff.1 h0
      · rw [hsz] at hj
        rcases Nat.eq_zero_or_pos j with rfl | hj0
        · exact Or.inl (Or.inl rfl)
        · obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
          have hm : m < es.length := by omega
          have hr := hrow m hm
          rw [Nat.add_comm 1 m] at hr
          rw [kzToArr_get (e :: es) (j := m + 1) (by simp; omega)]
          simp only [List.getElem_cons_succ]
          unfold kzRowOK at hr
          simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hr
          rcases hr with ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ | ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
          · refine Or.inl (Or.inr ⟨⟨⟨h1, h2⟩, h3⟩, ?_⟩)
            rw [hget es[m].2.2.2 (by omega), ← hgetD es[m].2.2.2 (by omega), duadEqT_iff.1 h4,
              Native.kzeroConj, kzeroMul_eq, kzeroMul_eq]
            rfl
          · refine Or.inr ⟨⟨⟨h1, h2⟩, h3⟩, ?_⟩
            rw [hget es[m].2.2.1 (by omega), hget es[m].2.2.2 (by omega),
              ← hgetD es[m].2.2.1 (by omega), ← hgetD es[m].2.2.2 (by omega), duadEqT_iff.1 h4,
              kzeroMul_eq]
    · intro x hx
      obtain ⟨f, hf, hfx⟩ := hcov x hx
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hf
      refine ⟨j, by rw [hsz]; simpa using hj, ?_⟩
      rw [hget j (by simpa using hj)]
      exact duadEqT_iff.1 hfx

theorem kzDerivAll_sound {hs : List (Array Nat × Array Nat)} {K : List (Array Nat)}
    {Ds : List (List KzE)} (h : kzDerivAllF hs K Ds = true) :
    ∀ k ∈ K, k = Native.kzeroId ∨ ∃ D' : Array Native.KzEntry,
      Native.kzeroDerivValid hs k D' = true ∧ ∀ x ∈ K, ∃ j < D'.size, D'[j]!.tab = x := by
  unfold kzDerivAllF at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Bool.or_eq_true] at h
  obtain ⟨hlen, hall⟩ := h
  intro k hk
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hk
  have hmem : (K[i], Ds[i]'(by omega)) ∈ K.zip Ds := by
    have := List.getElem_mem (show i < (K.zip Ds).length by simp; omega)
    simpa [List.getElem_zip] using this
  rcases hall _ hmem with h1 | h2
  · exact Or.inl (duadEqT_iff.1 h1)
  · exact Or.inr (kzDeriv_sound h2)

theorem treeValid_inst {α : Type} [Inhabited α] (i1 i2 : DecidableEq α) (valid : α → Bool)
    (steps : List (α → α)) (base : α) (r : Array α × Array Nat × Array Nat) :
    @Native.treeValid α _ i1 valid steps base r = @Native.treeValid α _ i2 valid steps base r := by
  have e : i1 = i2 := funext fun a => funext fun b => Subsingleton.elim (i1 a b) (i2 a b)
  rw [e]

theorem kzeroUFix_eq : Native.kzeroUFix () = kzeroUFixF := by
  have hg : ∀ g ∈ Native.uTabs, ∀ x ∈ g.toList, x < 24 := by decide
  unfold Native.kzeroUFix kzeroUFixF
  rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  exact forall₂_congr fun g hg' => by rw [imgSext_eq (hg g hg')]

end CFSG.KC.M24G
