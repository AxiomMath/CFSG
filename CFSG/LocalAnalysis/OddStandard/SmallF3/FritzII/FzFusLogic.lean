module

public import Certificates.Data.FzFusCls

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Certificates.FzFus

@[expose] def FzfRow {X : Type} (T Z A B u v : X) : Prop :=
  (u = Z ∧ v = T) ∨ (u = T ∧ v = Z) ∨ (u = A ∧ v = B) ∨ (u = B ∧ v = A)

theorem FzfRow.swap {X : Type} {T Z A B u v : X} (h : FzfRow T Z A B u v) :
    FzfRow T Z B A u v := by
  unfold FzfRow at *
  grind

theorem fzFus_core {X : Type} (cl : Cls → X) (T Z A B : X)
    (hTZ : T ≠ Z)
    (hRZ : ∀ c ∈ rzList, cl c ≠ Z)
    (hz : cl .z12 = Z ∧ cl .z3 = Z ∧ cl .lam = Z)
    (hIII : cl .III = T) (hoI : cl .oI = T)
    (hoJ : cl .oJ = A) (hoK : cl .oK = A ∨ cl .oK = B)
    (rows : ∀ e u v, (e, u, v) ∈ rowTable → cl e = T → FzfRow T Z A B (cl u) (cl v))
    (trans : ∀ s ∈ subTable, ∃ c ∈ s.2.2, cl c = T) :
    A = T ∧ B = T := by
  have zz1 := hRZ .III (by decide)
  have zz2 := hRZ .IIJ (by decide)
  have zz3 := hRZ .IIK (by decide)
  have zz4 := hRZ .JJI (by decide)
  have zz5 := hRZ .JJJ (by decide)
  have zz6 := hRZ .JJK (by decide)
  have zz7 := hRZ .KKI (by decide)
  have zz8 := hRZ .KKJ (by decide)
  have zz9 := hRZ .KKK (by decide)
  have zz10 := hRZ .IJI (by decide)
  have zz11 := hRZ .IJJ (by decide)
  have zz12 := hRZ .IJK (by decide)
  have zz13 := hRZ .IKI (by decide)
  have zz14 := hRZ .IKJ (by decide)
  have zz15 := hRZ .IKK (by decide)
  have zz16 := hRZ .JKI (by decide)
  have zz17 := hRZ .JKJ (by decide)
  have zz18 := hRZ .JKK (by decide)
  have r1 : FzfRow T Z A B (cl .KKK) (cl .JJJ) := rows .III .KKK .JJJ (by decide) hIII
  have r2 : FzfRow T Z A B (cl .JJK) (cl .KKJ) := rows .III .JJK .KKJ (by decide) hIII
  have r3 : FzfRow T Z A B (cl .JKK) (cl .JKJ) := rows .III .JKK .JKJ (by decide) hIII
  have r4 : FzfRow T Z A B (cl .oJ) (cl .oK) := rows .III .oJ .oK (by decide) hIII
  have r5 : FzfRow T Z A B (cl .lam) (cl .KKI) := rows .oI .lam .KKI (by decide) hoI
  have r6 : FzfRow T Z A B (cl .lam) (cl .JJI) := rows .oI .lam .JJI (by decide) hoI
  have r7 : FzfRow T Z A B (cl .oK) (cl .IIJ) := rows .oI .oK .IIJ (by decide) hoI
  have r8 : FzfRow T Z A B (cl .oJ) (cl .IIK) := rows .oI .oJ .IIK (by decide) hoI
  have r9 : FzfRow T Z A B (cl .oK) (cl .JJJ) := rows .oI .oK .JJJ (by decide) hoI
  have r10 : FzfRow T Z A B (cl .oK) (cl .KKJ) := rows .oI .oK .KKJ (by decide) hoI
  have r11 : FzfRow T Z A B (cl .oJ) (cl .KKK) := rows .oI .oJ .KKK (by decide) hoI
  have r12 : FzfRow T Z A B (cl .oJ) (cl .JJK) := rows .oI .oJ .JJK (by decide) hoI
  have r13 : cl .KKI = T → FzfRow T Z A B (cl .IJJ) (cl .IJK) := rows .KKI .IJJ .IJK (by decide)
  have r14 : cl .JJI = T → FzfRow T Z A B (cl .IKK) (cl .IKJ) := rows .JJI .IKK .IKJ (by decide)
  have r15 : cl .KKK = T → FzfRow T Z A B (cl .IJJ) (cl .IJI) := rows .KKK .IJJ .IJI (by decide)
  have r16 : cl .JJK = T → FzfRow T Z A B (cl .IKI) (cl .IKJ) := rows .JJK .IKI .IKJ (by decide)
  have r17 : cl .IIK = T → FzfRow T Z A B (cl .JKJ) (cl .JKI) := rows .IIK .JKJ .JKI (by decide)
  have r18 : cl .JKJ = T → FzfRow T Z A B (cl .IKI) (cl .IJK) := rows .JKJ .IKI .IJK (by decide)
  have r19 : cl .JKJ = T → FzfRow T Z A B (cl .IJI) (cl .IKK) := rows .JKJ .IJI .IKK (by decide)
  have r20 : cl .JKK = T → FzfRow T Z A B (cl .IJI) (cl .IKJ) := rows .JKK .IJI .IKJ (by decide)
  have r21 : cl .JKK = T → FzfRow T Z A B (cl .IKI) (cl .IJJ) := rows .JKK .IKI .IJJ (by decide)
  have r22 : cl .JKI = T → FzfRow T Z A B (cl .IJJ) (cl .IKK) := rows .JKI .IJJ .IKK (by decide)
  have r23 : cl .JKI = T → FzfRow T Z A B (cl .IKJ) (cl .IJK) := rows .JKI .IKJ .IJK (by decide)
  have r24 : cl .JJJ = T → FzfRow T Z A B (cl .IKK) (cl .IKI) := rows .JJJ .IKK .IKI (by decide)
  have r25 : cl .KKJ = T → FzfRow T Z A B (cl .IJI) (cl .IJK) := rows .KKJ .IJI .IJK (by decide)
  have r26 : cl .IIJ = T → FzfRow T Z A B (cl .JKK) (cl .JKI) := rows .IIJ .JKK .JKI (by decide)
  have t1 := trans (0, 2, [.z12, .z3, .lam, .oJ, .IIJ, .JJJ, .KKJ, .IJJ, .IKJ, .JKJ])
    (by decide)
  have t2 := trans (0, 3, [.z12, .z3, .lam, .oK, .IIK, .KKK, .JJK, .IKK, .IJK, .JKK])
    (by decide)
  have t3 := trans (2, 2, [.z12, .z3, .lam, .oJ, .IIJ, .JJJ, .KKJ, .JKK, .JKI, .IJI, .IKJ, .IJK])
    (by decide)
  have t4 := trans (3, 2, [.z12, .z3, .lam, .oJ, .IIJ, .JJJ, .KKJ, .JKK, .JKI, .IJJ, .IKI, .IKK])
    (by decide)
  have t5 := trans (1, 2, [.z12, .z3, .lam, .oJ, .IIJ, .JJJ, .KKJ, .JKJ, .IJI, .IJK, .IKI, .IKK])
    (by decide)
  have t6 := trans (3, 3, [.z12, .z3, .lam, .oK, .IIK, .KKK, .JJK, .JKJ, .JKI, .IKI, .IJK, .IKJ])
    (by decide)
  have t7 := trans (2, 3, [.z12, .z3, .lam, .oK, .IIK, .KKK, .JJK, .JKJ, .JKI, .IKK, .IJJ, .IJI])
    (by decide)
  have t8 := trans (1, 3, [.z12, .z3, .lam, .oK, .IIK, .KKK, .JJK, .JKK, .IKI, .IKJ, .IJI, .IJJ])
    (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left]
    at t1 t2 t3 t4 t5 t6 t7 t8
  clear rows hRZ trans
  unfold FzfRow at *
  grind (splits := 400)

theorem fzFus_step4 {X : Type} (cl : Cls → X) (T Z A B : X) (hA : A = T) (hB : B = T)
    (hRZ : ∀ c ∈ rzList, cl c ≠ Z)
    (hJJJ : cl .JJJ = T) (hJJK : cl .JJK = T) (hKKJ : cl .KKJ = T) (hKKK : cl .KKK = T)
    (hJKJ : cl .JKJ = T) (hJKK : cl .JKK = T)
    (rows : ∀ e u v, (e, u, v) ∈ rowTable → cl e = T → FzfRow T Z A B (cl u) (cl v)) :
    ∀ c ∈ rzList, cl c = T := by
  intro c hc
  have h1 := rows .JJJ .III .KKK (by decide) hJJJ
  have h2 := rows .JJK .IIJ .KKI (by decide) hJJK
  have h3 := rows .JJJ .IIK .KKI (by decide) hJJJ
  have h4 := rows .KKJ .JJI .IIK (by decide) hKKJ
  have h5 := rows .KKK .JJJ .III (by decide) hKKK
  have h6 := rows .KKJ .JJK .III (by decide) hKKJ
  have h7 := rows .JJJ .KKI .IIK (by decide) hJJJ
  have h8 := rows .JJK .KKJ .III (by decide) hJJK
  have h9 := rows .JJJ .KKK .III (by decide) hJJJ
  have h10 := rows .JKJ .IJI .IKK (by decide) hJKJ
  have h11 := rows .JKK .IJJ .IKI (by decide) hJKK
  have h12 := rows .JKJ .IJK .IKI (by decide) hJKJ
  have h13 := rows .JJJ .IKI .IKK (by decide) hJJJ
  have h14 := rows .JJK .IKJ .IKI (by decide) hJJK
  have h15 := rows .JJJ .IKK .IKI (by decide) hJJJ
  have h16 := rows .JKJ .JKI .IIK (by decide) hJKJ
  have h17 := rows .JKK .JKJ .III (by decide) hJKK
  have h18 := rows .JKJ .JKK .III (by decide) hJKJ
  have zz1 := hRZ .III (by decide)
  have zz2 := hRZ .IIJ (by decide)
  have zz3 := hRZ .IIK (by decide)
  have zz4 := hRZ .JJI (by decide)
  have zz5 := hRZ .JJJ (by decide)
  have zz6 := hRZ .JJK (by decide)
  have zz7 := hRZ .KKI (by decide)
  have zz8 := hRZ .KKJ (by decide)
  have zz9 := hRZ .KKK (by decide)
  have zz10 := hRZ .IJI (by decide)
  have zz11 := hRZ .IJJ (by decide)
  have zz12 := hRZ .IJK (by decide)
  have zz13 := hRZ .IKI (by decide)
  have zz14 := hRZ .IKJ (by decide)
  have zz15 := hRZ .IKK (by decide)
  have zz16 := hRZ .JKI (by decide)
  have zz17 := hRZ .JKJ (by decide)
  have zz18 := hRZ .JKK (by decide)
  subst hA hB
  unfold FzfRow at *
  simp only [rzList, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl <;> grind

theorem fzFus_logic {X : Type} (cl : Cls → X) (T Z A B : X)
    (hTZ : T ≠ Z)
    (hRZ : ∀ c ∈ rzList, cl c ≠ Z)
    (hz : cl .z12 = Z ∧ cl .z3 = Z ∧ cl .lam = Z)
    (hIII : cl .III = T) (hoI : cl .oI = T)
    (hoJ : cl .oJ = A ∨ cl .oJ = B) (hoK : cl .oK = A ∨ cl .oK = B)
    (rows : ∀ e u v, (e, u, v) ∈ rowTable → cl e = T → FzfRow T Z A B (cl u) (cl v))
    (trans : ∀ s ∈ subTable, ∃ c ∈ s.2.2, cl c = T) :
    A = T ∧ B = T ∧ (∀ c ∈ rzList, cl c = T) ∧ cl .oI = T ∧ cl .oJ = T ∧ cl .oK = T := by
  have hAB : A = T ∧ B = T := by
    rcases hoJ with hoJ | hoJ
    · exact fzFus_core cl T Z A B hTZ hRZ hz hIII hoI hoJ hoK rows trans
    · obtain ⟨h1, h2⟩ := fzFus_core cl T Z B A hTZ hRZ hz hIII hoI hoJ (hoK.symm)
        (fun e u v hr he => (rows e u v hr he).swap) trans
      exact ⟨h2, h1⟩
  obtain ⟨hA, hB⟩ := hAB
  have h1 := rows .III .KKK .JJJ (by decide) hIII
  have h2 := rows .III .JJK .KKJ (by decide) hIII
  have h3 := rows .III .JKK .JKJ (by decide) hIII
  have zz5 := hRZ .JJJ (by decide)
  have zz6 := hRZ .JJK (by decide)
  have zz8 := hRZ .KKJ (by decide)
  have zz9 := hRZ .KKK (by decide)
  have zz17 := hRZ .JKJ (by decide)
  have zz18 := hRZ .JKK (by decide)
  have hall : ∀ c ∈ rzList, cl c = T := by
    refine fzFus_step4 cl T Z A B hA hB hRZ ?_ ?_ ?_ ?_ ?_ ?_ rows
    all_goals (subst hA hB; unfold FzfRow at *; grind)
  subst hA hB
  refine ⟨rfl, rfl, hall, hoI, ?_, ?_⟩
  · rcases hoJ with h | h <;> exact h
  · rcases hoK with h | h <;> exact h

end CFSG.OddStandard.SmallF3.FritzII
