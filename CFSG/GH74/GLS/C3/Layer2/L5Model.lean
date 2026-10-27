module

public import CFSG.GH74.GLS.C3.Layer2.L5Fin
public meta import Mathlib.GroupTheory.SpecificGroups.Alternating
public meta import CFSG.GH74.GLS.C3.Prop121.ModelFive
public meta import CFSG.GH74.GLS.C3.Prop121.ModelFiveS
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelDefs
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelEmb
public meta import CFSG.GH74.GLS.C3.Layer2.NumMoved
public meta import CFSG.GH74.GLS.C3.Layer2.L5Fin
public import CFSG.GH74.GLS.C3.Layer2.L5ModelInputs
public meta import CFSG.GH74.GLS.C3.Layer2.L5ModelInputs
public import Certificates.Certificate5072
public import Certificates.Certificate5073
public import Certificates.Certificate5091

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5

open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2
  CFSG.GH74.GLS.C3.Layer2.Model

structure Adm (b : Amb 5 → Amb 5) : Prop where
  aut : IsAutOn b
  H1 : b f1 = f1
  H2 : ∀ w ∈ T5, ∀ w' ∈ T5, w * w = 1 → w ≠ 1 → w' * w' = 1 → w' ≠ 1 →
    (∃ g ∈ Fgrp 5, g * w * g⁻¹ = w') → nmE (b w) = nmE (b w')
  H3 : ∀ q ∈ T5, q.1 = 1 → q ≠ 1 → nmE (b q) = 4

theorem Adm.gens {b : Amb 5 → Amb 5} (h : Adm b) :
    b e1 = e1 ∧ (b e2 = e2 ∨ b e2 = e1 * e2) ∧ (b f2 = f2 ∨ b f2 = f1 * f2) := by
  obtain ⟨hb, H1, H2, H3⟩ := h
  obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8⟩ := elt_mem
  have he1 : e1 ∈ T5 := mem_T5_of_b m1
  have he2 : e2 ∈ T5 := mem_T5_of_b m2
  have hf1 : f1 ∈ T5 := mem_T5_of_b m3
  have hf2 : f2 ∈ T5 := mem_T5_of_b m4
  have he1f1 : e1 * f1 ∈ T5 := mem_T5_of_b m5
  have he2f1 : e2 * f1 ∈ T5 := mem_T5_of_b m6
  have he12 : e1 * e2 ∈ T5 := mem_T5_of_b m7
  have hf12 : f1 * f2 ∈ T5 := mem_T5_of_b m8
  obtain ⟨i1, i2, i3, i4, i5⟩ := elt_invol
  obtain ⟨n1, n2, n3, n4, n5⟩ := elt_ne
  obtain ⟨-, n7, n8, n9, -⟩ := elt_ne'
  obtain ⟨-, n12⟩ := elt_ne''
  obtain ⟨c1, -, -, c4, c5⟩ := elt_misc
  have hinj : ∀ {p q : Amb 5}, p ∈ T5 → q ∈ T5 → b p = b q → p = q :=
    fun hp hq h => hb.inj _ hp _ hq h
  have hb1 : b 1 = 1 := hb.one
  have hcen : ∀ s ∈ T5, b e1 * s = s * b e1 := by
    intro s hs
    obtain ⟨t, ht, rfl⟩ := hb.surj s hs
    rw [← hb.mul e1 he1 t ht, ← hb.mul t ht e1 he1]
    congr 1
    exact e1_central t (mem_allT5.2 ht)
  have hbe1 : b e1 = e1 ∨ b e1 = e1 * f1 := by
    have hbe1T : b e1 ∈ T5 := hb.mem _ he1
    rcases center_T5 (b e1) (mem_allT5.2 hbe1T) (fun s hs => hcen s (mem_allT5.1 hs)) with
      h | h | h | h
    · exact absurd (hinj he1 (one_mem _) (h.trans hb1.symm)) n1
    · exact Or.inl h
    · exact absurd (hinj he1 hf1 (h.trans H1.symm)) n9
    · exact Or.inr h
  have hbmul1 : ∀ p ∈ T5, b (p * f1) = b p * f1 := fun p hp => by
    rw [hb.mul p hp f1 hf1, H1]
  have h2a : nmE (b e1) = nmE (b e2) := by
    obtain ⟨g1, g2, g3⟩ := conj_e1_e2
    exact H2 e1 he1 e2 he2 i1 n1 i2 n2 ⟨_, mem_Fgrp5.2 g1, g2⟩
  have h2b : nmE (b e1 * f1) = nmE (b e2 * f1) := by
    obtain ⟨g1, g2, g3⟩ := conj_e1_e2
    have := H2 (e1 * f1) he1f1 (e2 * f1) he2f1 i3 n3 i4 n4 ⟨_, mem_Fgrp5.2 g1, g3⟩
    rwa [hbmul1 e1 he1, hbmul1 e2 he2] at this
  have h2c : nmE (b e1) = nmE (b e1 * b e2) := by
    obtain ⟨g1, g2⟩ := conj_e1_e12
    have := H2 e1 he1 (e1 * e2) he12 i1 n1 i5 n5 ⟨_, mem_Fgrp5.2 g1, g2⟩
    rwa [hb.mul e1 he1 e2 he2] at this
  have hW := W1 (b e1) (by rcases hbe1 with h | h <;> simp [h]) (b e2)
    (mem_allT5.2 (hb.mem _ he2))
  obtain ⟨hbe1', hbe2⟩ := hW ⟨h2a, h2b, h2c⟩
  have hne1 : b f2 ≠ 1 := fun h => n7 (hinj hf2 (one_mem _) (h.trans hb1.symm))
  have hne2 : b f2 ≠ f1 := fun h => n12 (hinj hf2 hf1 (h.trans H1.symm)).symm
  have h4a : nmE (b f2) = 4 := H3 f2 hf2 c4 n7
  have h4b : nmE (f1 * b f2) = 4 := by
    have := H3 (f1 * f2) hf12 c5 n8
    rwa [hb.mul f1 hf1 f2 hf2, H1] at this
  have hcomm : b f2 * b e2 = b e2 * b f2 := by
    rw [← hb.mul f2 hf2 e2 he2, ← hb.mul e2 he2 f2 hf2, c1]
  have hU := U1 (b e2) (by rcases hbe2 with h | h <;> simp [h]) (b f2)
    (mem_allT5.2 (hb.mem _ hf2))
  exact ⟨hbe1', hbe2, hU ⟨hne1, hne2, h4a, h4b, hcomm⟩⟩

theorem mk4_mem_Rlist5 :
    ∀ a b c d : Bool, mk4 e1 e2 f1 f2 a b c d ∈ Rlist5 :=
  Certificates.certificate5073.1

theorem Rlist5_mk4_chk :
    Rlist5.all (fun r => decide (∃ a b c d : Bool,
    r = mk4 e1 e2 f1 f2 a b c d)) = true :=
  Certificates.certificate5073.2.1

theorem Rlist5_mk4 :
    ∀ r ∈ Rlist5, ∃ a b c d : Bool, r = mk4 e1 e2 f1 f2 a b c d := by
  have h := Rlist5_mk4_chk
  simpa only [List.all_eq_true, decide_eq_true_eq] using h

theorem R_check_chk :
    [e2, e1 * e2].all (fun β => [f2, f1 * f2].all fun γ =>
    decide (∀ a b c d : Bool, nmE (mk4 e1 β f1 γ a b c d) = nmE (mk4 e1 e2 f1 f2 a b c d) ∧
      mk4 e1 β f1 γ a b c d ∈ Rlist5)) = true :=
  Certificates.certificate5073.2.2.1

theorem R_check :
    ∀ β ∈ [e2, e1 * e2], ∀ γ ∈ [f2, f1 * f2], ∀ a b c d : Bool,
    nmE (mk4 e1 β f1 γ a b c d) = nmE (mk4 e1 e2 f1 f2 a b c d) ∧
      mk4 e1 β f1 γ a b c d ∈ Rlist5 := by
  have h := R_check_chk
  simpa only [List.all_eq_true, decide_eq_true_eq] using h

theorem R_check'
    (β γ : Amb 5) (hβ : β ∈ [e2, e1 * e2]) (hγ : γ ∈ [f2, f1 * f2])
    (a b c d : Bool) :
    mk4 e1 β f1 γ a b c d ∈ Rlist5 ∧
      nmE (mk4 e1 β f1 γ a b c d) = nmE (mk4 e1 e2 f1 f2 a b c d) :=
  (R_check β hβ γ hγ a b c d).symm

theorem R_surj_chk :
    [e2, e1 * e2].all (fun β => [f2, f1 * f2].all fun γ => Rlist5.all fun q =>
    decide (∃ a b c d : Bool, q = mk4 e1 β f1 γ a b c d)) = true :=
  Certificates.certificate5073.2.2.2.1

theorem R_surj :
    ∀ β ∈ [e2, e1 * e2], ∀ γ ∈ [f2, f1 * f2], ∀ q ∈ Rlist5,
    ∃ a b c d : Bool, q = mk4 e1 β f1 γ a b c d := by
  have h := R_surj_chk
  simpa only [List.all_eq_true, decide_eq_true_eq] using h

theorem nm_outside_R_chk :
    allT5.all (fun t => imp (decide (t * t = 1)) (imp (decide (t ≠ 1))
    (imp (decide (t ∉ Rlist5)) (decide (nmE t = 4))))) = true :=
  Certificates.certificate5073.2.2.2.2

theorem nm_outside_R :
    ∀ t ∈ allT5, t * t = 1 → t ≠ 1 → t ∉ Rlist5 → nmE t = 4 := by
  have h := nm_outside_R_chk
  simpa only [List.all_eq_true, imp_eq_true, decide_eq_true_eq] using h

theorem autMk4 {b : Amb 5 → Amb 5} (hb : IsAutOn b) {g1 g2 g3 g4 : Amb 5} (h1 : g1 ∈ T5)
    (h2 : g2 ∈ T5) (h3 : g3 ∈ T5) (h4 : g4 ∈ T5) (a b' c d : Bool) :
    mk4 g1 g2 g3 g4 a b' c d ∈ T5 ∧
      b (mk4 g1 g2 g3 g4 a b' c d) = mk4 (b g1) (b g2) (b g3) (b g4) a b' c d := by
  have hc : ∀ (a : Bool) (g : Amb 5), g ∈ T5 →
      cond a g 1 ∈ T5 ∧ b (cond a g 1) = cond a (b g) 1 := by
    intro a g hg
    cases a
    · exact ⟨one_mem _, hb.one⟩
    · exact ⟨hg, rfl⟩
  obtain ⟨m1, e1'⟩ := hc a g1 h1
  obtain ⟨m2, e2'⟩ := hc b' g2 h2
  obtain ⟨m3, e3'⟩ := hc c g3 h3
  obtain ⟨m4, e4'⟩ := hc d g4 h4
  refine ⟨mul_mem (mul_mem (mul_mem m1 m2) m3) m4, ?_⟩
  unfold mk4
  rw [hb.mul _ (mul_mem (mul_mem m1 m2) m3) _ m4, hb.mul _ (mul_mem m1 m2) _ m3,
    hb.mul _ m1 _ m2, e1', e2', e3', e4']

theorem e2_mem_T5 : e2 ∈ T5 := mem_T5_of_b elt_mem.2.1

theorem e1_mem_T5 : e1 ∈ T5 := mem_T5_of_b elt_mem.1

theorem f2_mem_T5 : f2 ∈ T5 := mem_T5_of_b elt_mem.2.2.2.1

theorem Adm.R
    {b : Amb 5 → Amb 5} (h : Adm b) :
    ∀ r ∈ Rlist5, b r ∈ Rlist5 ∧ nmE (b r) = nmE r := by
  obtain ⟨hbe1, hbe2, hbf2⟩ := h.gens
  intro r hr
  obtain ⟨a, b', c, d, rfl⟩ := Rlist5_mk4 r hr
  have h1 := (autMk4 h.aut e1_mem_T5 e2_mem_T5 f1_mem_T5 f2_mem_T5 a b' c d).2
  have hβ : b e2 ∈ [e2, e1 * e2] := by rcases hbe2 with h2 | h2 <;> simp [h2]
  have hγ : b f2 ∈ [f2, f1 * f2] := by rcases hbf2 with h3 | h3 <;> simp [h3]
  rw [h1, hbe1, h.H1]
  exact R_check' _ _ hβ hγ a b' c d

theorem Adm.not_R
    {b : Amb 5 → Amb 5} (h : Adm b) {t : Amb 5} (ht : t ∈ T5)
    (hbt : b t ∈ Rlist5) : t ∈ Rlist5 := by
  obtain ⟨hbe1, hbe2, hbf2⟩ := h.gens
  have hb2 : b e2 ∈ [e2, e1 * e2] := by rcases hbe2 with h2 | h2 <;> simp [h2]
  have hf2' : b f2 ∈ [f2, f1 * f2] := by rcases hbf2 with h2 | h2 <;> simp [h2]
  obtain ⟨a, b', c, d, hq⟩ := R_surj (b e2) hb2 (b f2) hf2' (b t) hbt
  have h1 := (autMk4 h.aut e1_mem_T5 e2_mem_T5 f1_mem_T5 f2_mem_T5 a b' c d)
  have h2 : b t = b (mk4 e1 e2 f1 f2 a b' c d) := by
    rw [h1.2, hbe1, h.H1]
    exact hq
  have h3 : t = mk4 e1 e2 f1 f2 a b' c d := h.aut.inj t ht _ h1.1 h2
  rw [h3]
  exact mk4_mem_Rlist5 a b' c d

theorem Adm.keyB
    {b : Amb 5 → Amb 5} (h : Adm b) {t : Amb 5} (ht : t ∈ T5) (hsq : t * t = 1)
    (ht1 : t ≠ 1) : nmE (b t) = nmE t := by
  by_cases htR : t ∈ Rlist5
  · exact (h.R t htR).2
  · have hbR : b t ∉ Rlist5 := fun hh => htR (h.not_R ht hh)
    have hbt : b t ∈ T5 := h.aut.mem t ht
    have hsq' : b t * b t = 1 := by rw [← h.aut.mul t ht t ht, hsq, h.aut.one]
    have hne' : b t ≠ 1 := fun h1 =>
      ht1 (h.aut.inj t ht 1 (one_mem _) (h1.trans h.aut.one.symm))
    rw [nm_outside_R (b t) (mem_allT5.2 hbt) hsq' hne' hbR,
      nm_outside_R t (mem_allT5.2 ht) hsq ht1 htR]

theorem Adm.vhat
    {b : Amb 5 → Amb 5} (h : Adm b) : b vhat5 = vhat5 := by
  have he1 : e1 ∈ T5 := e1_mem_T5
  have hf1 : f1 ∈ T5 := f1_mem_T5
  show b (e1 * f1) = e1 * f1
  rw [h.aut.mul e1 he1 f1 hf1, h.gens.1, h.H1]

theorem vhat5_central
    {t : Amb 5} (ht : t ∈ T5) : t * vhat5 = vhat5 * t := T5_comm_vhat5 ht

theorem sq_mul_vhat5 {p : Amb 5} (hp : p ∈ T5) (hsq : p * p = 1) :
    (p * vhat5) * (p * vhat5) = 1 := by
  calc p * vhat5 * (p * vhat5) = p * (vhat5 * p) * vhat5 := by group
    _ = p * (p * vhat5) * vhat5 := by rw [← vhat5_central hp]
    _ = (p * p) * (vhat5 * vhat5) := by group
    _ = 1 := by rw [hsq, vhat5_sq, one_mul]

theorem mul_vhat5_ne
    {p : Amb 5} (hp : p ≠ vhat5) : p * vhat5 ≠ 1 := by
  intro h
  apply hp
  calc p = p * vhat5 * vhat5⁻¹ := by group
    _ = vhat5⁻¹ := by rw [h, one_mul]
    _ = vhat5 := inv_eq_of_mul_eq_one_right vhat5_sq

theorem Adm.mem_E5_iff
    {b : Amb 5 → Amb 5} (h : Adm b) {p : Amb 5} (hp : p ∈ T5) :
    b p ∈ E5 ↔ p ∈ E5 := by
  by_cases hp1 : p = 1
  · subst hp1
    rw [h.aut.one]
  by_cases hpv : p = vhat5
  · subst hpv
    rw [h.vhat]
  have hpv' : p * vhat5 ∈ T5 := mul_mem hp vhat5_mem_T5
  have hbp : b p ∈ T5 := h.aut.mem p hp
  have hbv : b (p * vhat5) = b p * vhat5 := by rw [h.aut.mul p hp _ vhat5_mem_T5, h.vhat]
  constructor
  · intro hbE
    have hsq : p * p = 1 := by
      have hbsq : b p * b p = 1 := E5_sq _ hbE
      exact h.aut.inj _ (mul_mem hp hp) 1 (one_mem _)
        (by rw [h.aut.mul p hp p hp, hbsq, h.aut.one])
    have hbne : b p ≠ 1 := fun h1 => hp1 (h.aut.inj p hp 1 (one_mem _) (h1.trans h.aut.one.symm))
    have hbnv : b p ≠ vhat5 := fun h1 =>
      hpv (h.aut.inj p hp vhat5 vhat5_mem_T5 (h1.trans h.vhat.symm))
    have hc := (E5_char hbp (E5_sq _ hbE) hbne).1 ⟨hbE, hbnv⟩
    have hsq2 := sq_mul_vhat5 hp hsq
    have hn1 : nmE p = 4 := (h.keyB hp hsq hp1).symm.trans hc.1
    have hn2 : nmE (p * vhat5) = 4 := by
      rw [← h.keyB hpv' hsq2 (mul_vhat5_ne hpv), hbv]
      exact hc.2
    exact ((E5_char hp hsq hp1).2 ⟨hn1, hn2⟩).1
  · intro hE
    have hsq : p * p = 1 := E5_sq _ hE
    have hsq2 := sq_mul_vhat5 hp hsq
    have hc := (E5_char hp hsq hp1).1 ⟨hE, hpv⟩
    have hbsq : b p * b p = 1 := by rw [← h.aut.mul p hp p hp, hsq, h.aut.one]
    have hbne : b p ≠ 1 := fun h1 => hp1 (h.aut.inj p hp 1 (one_mem _) (h1.trans h.aut.one.symm))
    have hbnv : b p ≠ vhat5 := fun h1 =>
      hpv (h.aut.inj p hp vhat5 vhat5_mem_T5 (h1.trans h.vhat.symm))
    have hn1 : nmE (b p) = 4 := (h.keyB hp hsq hp1).trans hc.1
    have hn2 : nmE (b p * vhat5) = 4 := by
      rw [← hbv, h.keyB hpv' hsq2 (mul_vhat5_ne hpv)]
      exact hc.2
    exact ((E5_char hbp hbsq hbne).2 ⟨hn1, hn2⟩).1

end CFSG.GH74.GLS.C3.Layer2.L5
