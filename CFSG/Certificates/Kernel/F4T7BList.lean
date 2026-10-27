module

public import CFSG.Certificates.Kernel.F4T7BPlane
public import CFSG.RankThree.PartTwo.Sec10.KS1012GL34.ChecksT7
public import CFSG.RankThree.PartTwo.Sec10.KS1012GL34.Bridge

public section

namespace CFSG.KC.F4T7B

open CFSG.Fischer CFSG.KC.F4M3B CFSG.RankThree.PartTwo.Sec10.KS1012GL34
  CFSG.RankThree.PartTwo.Sec10.KS1012GL34.Light

@[expose] def decL (c : Nat) : M3 :=
  ⟨f4 c, f4 (c / 4), f4 (c / 16), f4 (c / 64), f4 (c / 256), f4 (c / 1024), f4 (c / 4096),
    f4 (c / 16384), f4 (c / 65536)⟩

theorem codeL_decL (c : Nat) (hc : c < 2 ^ 18) : codeL (decL c) = c := by
  simp only [codeL, codeM, toL, decL, f4, Nat.reducePow] at hc ⊢
  omega

theorem decL_codeL (A : M3) : decL (codeL A) = A := by
  obtain ⟨⟨⟨a0, h0⟩⟩, ⟨⟨a1, h1⟩⟩, ⟨⟨a2, h2⟩⟩, ⟨⟨a3, h3⟩⟩, ⟨⟨a4, h4⟩⟩, ⟨⟨a5, h5⟩⟩, ⟨⟨a6, h6⟩⟩,
    ⟨⟨a7, h7⟩⟩, ⟨⟨a8, h8⟩⟩⟩ := A
  simp only [decL, codeL, codeM, toL, f4, M3.mk.injEq, F4.mk.injEq, Fin.mk.injEq]
  omega

theorem codeL_injective : Function.Injective codeL :=
  fun A B h => by rw [← decL_codeL A, h, decL_codeL]

theorem length_allM3L : (allM3L ()).length = 2 ^ 18 := by
  have h4 : allF4.length = 4 := rfl
  simp only [allM3L, List.length_flatMap, List.length_map, h4, List.map_const', List.sum_replicate,
    smul_eq_mul, Nat.reduceMul, Nat.reducePow]

theorem nodup_allM3L : (allM3L ()).Nodup := by
  have hsub : (List.range (2 ^ 18)).Subperm ((allM3L ()).map codeL) := by
    refine (List.nodup_range).subperm fun c hc => ?_
    rw [List.mem_range] at hc
    exact List.mem_map.2 ⟨decL c, Bridge.mem_allM3L _, codeL_decL c hc⟩
  have hp := hsub.perm_of_length_le (by rw [List.length_map, length_allM3L, List.length_range])
  exact List.Nodup.of_map codeL (hp.nodup_iff.1 List.nodup_range)

theorem incB_spec (C : List Nat) (B : Nat) :
    (C.foldr (fun c (acc : Bool × Nat) => (acc.1 && Nat.blt c acc.2, c)) (true, B)).2 =
        C.headD B ∧
      ((C.foldr (fun c (acc : Bool × Nat) => (acc.1 && Nat.blt c acc.2, c)) (true, B)).1 = true →
        C.Pairwise (· < ·) ∧ ∀ c ∈ C, C.headD B ≤ c ∧ c < B) := by
  induction C with
  | nil => simp
  | cons a l ih =>
    obtain ⟨ih2, ih1⟩ := ih
    refine ⟨rfl, fun h => ?_⟩
    simp only [List.foldr_cons, Bool.and_eq_true, Nat.blt_eq] at h
    rw [ih2] at h
    obtain ⟨hl, hlt⟩ := ih1 h.1
    have hB : l.headD B ≤ B ∨ l ≠ [] := by
      cases l with
      | nil => exact Or.inl (Nat.le_refl _)
      | cons b l => exact Or.inr (List.cons_ne_nil _ _)
    have haB : a < B := by
      cases l with
      | nil => exact h.2
      | cons b l => exact Nat.lt_trans h.2 (hlt b List.mem_cons_self).2
    refine ⟨List.pairwise_cons.2 ⟨fun c hc => Nat.lt_of_lt_of_le h.2 (hlt c hc).1, hl⟩, ?_⟩
    intro c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · exact ⟨Nat.le_refl _, haB⟩
    · exact ⟨Nat.le_of_lt (Nat.lt_of_lt_of_le h.2 (hlt c hc).1), (hlt c hc).2⟩

theorem incB_of {C : List Nat} (h : incB C = true) :
    C.Nodup ∧ ∀ c ∈ C, c < 2 ^ 18 := by
  obtain ⟨-, h1⟩ := incB_spec C 262144
  obtain ⟨hp, hlt⟩ := h1 h
  exact ⟨hp.imp Nat.ne_of_lt, fun c hc => (hlt c hc).2⟩

theorem mem_piLS (i : Fin 6) (A : M3) :
    A ∈ piLS (slL ()) i ↔ (decide (Light.detL A = 1) && stabLn i.val A) = true := by
  simp only [piLS, slL, List.mem_filter, Bridge.mem_allM3L, true_and, Bool.and_eq_true]

theorem nodup_piLS (i : Fin 6) : (piLS (slL ()) i).Nodup :=
  (nodup_allM3L.filter _).filter _

theorem piLS_codes_perm {i : Fin 6} {C K : List Nat} (h : chkAll (omC i.val) C K = true)
    (hC : incB C = true) : List.Perm ((piLS (slL ()) i).map codeL) C := by
  obtain ⟨hnd, hlt⟩ := incB_of hC
  refine (List.perm_ext_iff_of_nodup ((nodup_piLS i).map codeL_injective) hnd).2 fun c => ?_
  constructor
  · intro hc
    obtain ⟨A, hA, rfl⟩ := List.mem_map.1 hc
    rw [mem_piLS, mem_C_iff h] at hA
    exact of_decide_eq_true hA
  · intro hc
    refine List.mem_map.2 ⟨decL c, ?_, codeL_decL c (hlt c hc)⟩
    rw [mem_piLS, mem_C_iff h, codeL_decL c (hlt c hc)]
    exact decide_eq_true hc

theorem piLS_length {i : Fin 6} {C K : List Nat} (h : chkAll (omC i.val) C K = true)
    (hC : incB C = true) : (piLS (slL ()) i).length = C.length := by
  rw [← (piLS_codes_perm h hC).length_eq, List.length_map]

end CFSG.KC.F4T7B

end
