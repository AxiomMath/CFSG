module

public import Certificates.Certificate12616

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Census219

open CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer
  CFSG.Monster.B.Mathieu CFSG.AGLEmbeddingD2.Wilson.ThreeCore.M24 CFSG.AGLEmbeddingD2.Wilson.ThreeCore
  CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.Blueprint Subgroup Equiv

theorem m24Tc_parts :
    tcOK 24 6 (List.range 24) m24xA m24TcD (m24TcCQ ()) (m24TcCK ()) (m24TcCS ()) = true ∧
    enumOK 24 m24caA (List.range 24) (m24CC ()) = true ∧
    allLt m24TcD.gQ.size (fun l => (m24CC ()).pts.toList.any (eqA 24 m24TcD.gQ[l]!)) = true ∧
    enumOK 24 m24sA (List.range 24) (m24SC ()) = true ∧ (m24SC ()).pts.size = 27 ∧
    allLt (m24SC ()).pts.size (fun k => eqA 24 (powArr 24 (m24SC ()).pts[k]! 3) (idA 24)) = true := by
  have h := Certificates.certificate12616
  simp only [m24TcOK, Bool.and_eq_true, beq_iff_eq, and_assoc] at h
  exact h

theorem m24_keys_lt : ∀ p ∈ List.range 24, p < 24 := fun _ hp => List.mem_range.1 hp

theorem m24_sylowGens_eq :
    tp 24 '' {x | x ∈ ([wT s1W, wT s2W] : List Table).toArray} = permsA 24 m24sA := by
  ext g
  constructor
  · rintro ⟨T, hT, rfl⟩
    simp only [Set.mem_ofPred_eq, List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hT
    rcases hT with rfl | rfl
    · exact ⟨0, by simp [m24sA], rfl⟩
    · exact ⟨1, by simp [m24sA], rfl⟩
  · rintro ⟨k, hk, rfl⟩
    have hk2 : k < 2 := by simpa [m24sA] using hk
    interval_cases k
    · exact ⟨wT s1W, by simp, rfl⟩
    · exact ⟨wT s2W, by simp, rfl⟩

theorem m24_centGens_eq :
    tp 24 '' {x | x ∈ ([wT ca1W, wT ca2W] : List Table).toArray} = permsA 24 m24caA := by
  ext g
  constructor
  · rintro ⟨T, hT, rfl⟩
    simp only [Set.mem_ofPred_eq, List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hT
    rcases hT with rfl | rfl
    · exact ⟨0, by simp [m24caA], rfl⟩
    · exact ⟨1, by simp [m24caA], rfl⟩
  · rintro ⟨k, hk, rfl⟩
    have hk2 : k < 2 := by simpa [m24caA] using hk
    interval_cases k
    · exact ⟨wT ca1W, by simp, rfl⟩
    · exact ⟨wT ca2W, by simp, rfl⟩


section Spec


theorem m24_threeSpec_rowA :
    tp 24 m24Row3A.rep ∈ NativeSporadic.M24 ∧ orderOf (tp 24 m24Row3A.rep) = 3 ∧
      closure (permsA 24 m24caA) =
        NativeSporadic.M24 ⊓ centralizer ({permOfArr 24 m24xA} : Set (Perm (Fin 24))) ∧
      Nat.card ↥(NativeSporadic.M24 ⊓ centralizer ({permOfArr 24 m24xA} : Set (Perm (Fin 24)))) =
        1080 := by
  obtain ⟨h1, h2, h4, -⟩ := m24ThreeSpec.2.2.1 m24Row3A (by simp)
  have h3 := m24ThreeSpec.2.2.2.2.2
  have e : m24Row3A.centGens = [wT ca1W, wT ca2W] := rfl
  rw [e, m24_centGens_eq] at h3
  exact ⟨h1, h2, h3, h4⟩

theorem m24_threeSpec_rowB :
    Nat.card ↥(NativeSporadic.M24 ⊓ centralizer ({tp 24 m24Row3B.rep} : Set (Perm (Fin 24)))) =
      504 := by
  exact (m24ThreeSpec.2.2.1 m24Row3B (by simp)).2.2.1

theorem m24_cover {t : Perm (Fin 24)} (ht : t ∈ NativeSporadic.M24) (ht3 : orderOf t = 3) :
    ∃ r ∈ [m24Row3A, m24Row3B], ∃ g ∈ NativeSporadic.M24, t = g * tp 24 r.rep * g⁻¹ :=
  m24ThreeSpec.2.2.2.1 t ht ht3

theorem m24_sylow_le_card :
    closure (permsA 24 m24sA) ≤ NativeSporadic.M24 ∧ Nat.card ↥(closure (permsA 24 m24sA)) = 27 := by
  have h := m24ThreeSpec
  rw [m24_sylowGens_eq] at h
  exact ⟨h.1, h.2.1⟩

end Spec

section Facts


theorem m24_sylow_exp {q : Perm (Fin 24)} (hq : q ∈ closure (permsA 24 m24sA)) : q ^ 3 = 1 := by
  obtain ⟨-, -, -, hSe, -, hpow⟩ := m24Tc_parts
  obtain ⟨k, hk, hkg⟩ := enumOK_exists_rep m24_keys_lt hSe hq
  exact (eqA_iff (rep_powArr hkg 3) rep_idA).1 (allLt_spec hpow hk)

@[expose] noncomputable def m24TcQ : Subgroup (Perm (Fin 24)) := closure (permsA 24 m24TcD.gQ)

theorem m24Tc_spec :
    permOfArr 24 m24xA ∈ m24TcQ ∧ CFSG.IsQuasisimple ↥m24TcQ ∧
      CFSG.RankThree.PartTwo.Sec4.IsTripleCover ↥m24TcQ (alternatingGroup (Fin 6)) :=
  tcOK_spec m24_keys_lt (by norm_num) m24Tc_parts.1

theorem card_m24TcQ : Nat.card m24TcQ = 1080 := by
  have h := (tcOK_parts m24Tc_parts.1).1
  rw [m24TcQ, (enumOK_spec m24_keys_lt h).2.1, (tcOK_parts m24Tc_parts.1).2.1]
  decide

theorem m24TcQ_le : m24TcQ ≤ closure (permsA 24 m24caA) :=
  le_of_gens_mem m24_keys_lt m24Tc_parts.2.1 (tcOK_parts m24Tc_parts.1).1 m24Tc_parts.2.2.1

end Facts

end CFSG.AGLEmbeddingD2.Wilson.Census219
