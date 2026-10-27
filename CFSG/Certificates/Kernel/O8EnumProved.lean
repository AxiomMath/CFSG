module

public import CFSG.Certificates.Kernel.O8EnumDefs
import CFSG.Certificates.Kernel.O8MulProved

namespace CFSG.KC.O8

open CFSG.KLie.CT CFSG.KC.Loop CFSG.EvenSmallLie.OmegaEight.Stage2

theorem andB_eq_and' (a b : Bool) : andB a b = (a && b) := by cases a <;> rfl

theorem orB_eq_or' (a b : Bool) : orB a b = (a || b) := by cases a <;> rfl

theorem notB_eq_not' (a : Bool) : notB a = !a := by cases a <;> rfl

theorem strictN_eq_k (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

theorem beq_one_nIf (c : Bool) : Nat.beq 1 (Bool.rec (motive := fun _ => Nat) 0 1 c) = c := by
  cases c <;> rfl

theorem allN_iff' {n : Nat} {f : Nat → Bool} : allN n f = true ↔ ∀ i < n, f i = true := by
  induction n with
  | zero =>
    constructor
    · intro _ i hi
      omega
    · intro _
      rfl
  | succ n ih =>
    have e : allN (n + 1) f = andB (f n) (allN n f) := rfl
    rw [e, andB_eq_and', Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact h2 i hi
      · exact h1
    · intro h
      exact ⟨h n (by omega), fun i hi => h i (by omega)⟩

theorem maskN144 : maskN 144 = 2 ^ 144 - 1 := by decide

theorem enKey_lt (D : Nat → Nat) (i : Nat) : enKey D i < 2 ^ 144 := by
  unfold enKey vKey
  rw [maskN144]
  have h : Nat.land (D i) (2 ^ 144 - 1) ≤ 2 ^ 144 - 1 := Nat.and_le_right
  have h2 : (0 : Nat) < 2 ^ 144 := by positivity
  omega

theorem entry_facts {G : Nat → Nat} {ng m nb : Nat} {D : Nat → Nat} (hm : m ≤ 256 * nb)
    (hb : ∀ b < nb, enumBlockOK G ng m D b = true) {i : Nat} (hi : i < m) :
    (enKey D i = ID12 ∨ (enPar D i < m ∧ enGen D i < ng ∧ enDep D (enPar D i) < enDep D i ∧
      enKey D i = mul12K (enKey D (enPar D i)) (G (enGen D i)))) ∧
    (∀ j < ng, vCl (D i) j < m ∧ enKey D (vCl (D i) j) = mul12K (enKey D i) (G j)) ∧
    (i + 1 < m → enKey D i < enKey D (i + 1)) := by
  have hbk := hb (i / 256) (by omega)
  unfold enumBlockOK at hbk
  have h1 := allN_iff'.1 hbk (i % 256) (Nat.mod_lt _ (by norm_num))
  have e : 256 * (i / 256) + i % 256 = i := Nat.div_add_mod i 256
  simp only [Nat.add_eq, Nat.mul_eq, e] at h1
  simp only [strictN_eq_k, beq_one_nIf, andB_eq_and', orB_eq_or', notB_eq_not', Bool.and_eq_true,
    Bool.or_eq_true, Nat.blt_eq, Nat.beq_eq, Bool.not_eq_eq_eq_not, Bool.not_true, allN_iff',
    Nat.succ_eq_add_one] at h1
  rcases h1 with h1 | h1
  · have h2 : Nat.blt i m = true := Nat.blt_eq.mpr hi
    rw [h2] at h1
    exact absurd h1 (by decide)
  obtain ⟨htree, hcl, hs⟩ := h1
  refine ⟨?_, fun j hj => ?_, fun hi1 => ?_⟩
  · rcases htree with h | ⟨h2, h3, h4, h5⟩
    · exact Or.inl h
    · exact Or.inr ⟨h2, h3, h4, h5⟩
  · exact hcl j hj
  · rcases hs with h | h
    · have h2 : Nat.blt (i + 1) m = true := Nat.blt_eq.mpr hi1
      rw [h2] at h
      exact absurd h (by decide)
    · exact h

theorem decE_getD_par {D : Nat → Nat} {m i : Nat} (hi : i < m) :
    (decE D m).par.getD i 0 = enPar D i := by
  simp [decE, Array.getD_eq_getD_getElem?, hi]

theorem decE_getD_gen {D : Nat → Nat} {m i : Nat} (hi : i < m) :
    (decE D m).gen.getD i 0 = enGen D i := by
  simp [decE, Array.getD_eq_getD_getElem?, hi]

theorem decE_getD_dep {D : Nat → Nat} {m i : Nat} (hi : i < m) :
    (decE D m).dep.getD i 0 = enDep D i := by
  simp [decE, Array.getD_eq_getD_getElem?, hi]

theorem genPairsK_size (G GI : Nat → Nat) (ng : Nat) : (genPairsK G GI ng).size = ng := by
  simp [genPairsK]

theorem genK_genPairsK {G GI : Nat → Nat} {ng j : Nat} (hj : j < ng) :
    genK (genPairsK G GI ng) j = (G j, GI j) := by
  simp [genK, genPairsK, Array.getD_eq_getD_getElem?, hj]

public theorem enum_sound_proved {G GI D : Nat → Nat} {ng m z nb : Nat} (hm : m ≤ 256 * nb)
    (hm' : m < 2 ^ 17) (hh : enumHeadOK G GI ng m D z = true)
    (hb : ∀ b < nb, enumBlockOK G ng m D b = true) :
    enumOK (genPairsK G GI ng) (decE D m) = true := by
  unfold enumHeadOK at hh
  simp only [andB_eq_and', Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq, allN_iff'] at hh
  obtain ⟨hinv, hz, hzk⟩ := hh
  have hsz := decE_keys_size D m
  have hsorted : sortedK (decE D m).keys = true := by
    unfold sortedK
    rw [List.all_eq_true]
    intro i hi
    rw [List.mem_range, hsz] at hi
    rw [decE_keys_getD (by omega), decE_keys_getD (by omega), decide_eq_true_eq]
    exact (entry_facts hm hb (by omega)).2.2 (by omega)
  have hmem : ∀ {i k : Nat}, i < m → enKey D i = k → memK (decE D m).keys k = true :=
    fun {i k} hi hk => memK_of_mem hsorted (by rw [hsz]; omega) (by rw [hsz]; exact hi)
      (by rw [decE_keys_getD hi, hk])
  unfold enumOK
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq]
  refine ⟨⟨⟨⟨?_, hsorted⟩, hmem hz (by rw [hzk, idK_eq])⟩, fun i hi => ?_⟩, ?_⟩
  · unfold gensOK
    rw [Array.all_eq_true]
    intro j hj
    rw [genPairsK_size] at hj
    simp only [genPairsK, Array.getElem_ofFn]
    unfold invPair
    rw [mulK_eq_proved, mulK_eq_proved, idK_eq]
    simp [(hinv j hj).1, (hinv j hj).2]
  · rw [hsz] at hi
    rw [decE_keys_getD hi]
    refine ⟨enKey_lt D i, ?_⟩
    unfold treeAt
    rcases (entry_facts hm hb hi).1 with h | ⟨h2, h3, h4, h5⟩
    · rw [decE_keys_getD hi, h, ← idK_eq]
      simp
    · rw [decE_getD_par hi, decE_getD_gen hi, decE_getD_dep hi, decE_getD_dep h2, hsz,
        genPairsK_size, decE_keys_getD hi, decE_keys_getD h2,
        tabs_getD _ (by rw [genPairsK_size]; exact h3), genK_genPairsK h3, mulT_tab,
        mulK_eq_proved]
      simp [h2, h3, h4, h5]
  · unfold closedAll
    rw [List.all_eq_true]
    intro j hj
    rw [List.mem_range, genPairsK_size] at hj
    rw [List.all_eq_true]
    intro i hi
    rw [List.mem_range, hsz] at hi
    rw [genK_genPairsK hj, decE_keys_getD hi, mulT_tab, mulK_eq_proved]
    obtain ⟨hc1, hc2⟩ := (entry_facts hm hb hi).2.1 j hj
    exact hmem hc1 hc2

end CFSG.KC.O8
