module

public import CFSG.Sporadic.Schreier.M22

public section

namespace CFSG.ComponentClassification.WittDesign

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Certificates

abbrev M22 : Subgroup (Equiv.Perm (Fin 22)) := CFSG.Blueprint.NativeSporadic.M22

@[expose] def tf (T : Table) (x : Fin 22) : Fin 22 := ⟨ap T x % 22, Nat.mod_lt _ (by norm_num)⟩

theorem tf_eq {T : Table} {g : Equiv.Perm (Fin 22)} (h : Rep 22 T g) : tf T = ⇑g := by
  funext x
  refine Fin.ext ?_
  change ap T x % 22 = (g x : ℕ)
  rw [h x x.2, idx_of_lt g x.2, Nat.mod_eq_of_lt (g • (⟨x, x.2⟩ : Fin 22)).isLt]
  rfl

@[expose] def m22Count (Q : (Fin 22 → Fin 22) → Prop) [DecidablePred Q] : ℕ :=
  countProducts 22 (fun T => decide (Q (tf T))) (levelTables m22Certificate) (idT 22)

theorem card_m22_subtype (Q : (Fin 22 → Fin 22) → Prop) [DecidablePred Q] :
    Nat.card {x : M22 // Q ⇑(x : Equiv.Perm (Fin 22))} = m22Count Q := by
  have hQ : ValidSchreier m22Certificate := m22Certificate_check
  have hf : ∀ (T : Table) (g : Equiv.Perm (Fin 22)), Rep 22 T g →
      (decide (Q (tf T)) = true ↔ Q ⇑g) := fun T g hT => by
    rw [tf_eq hT, decide_eq_true_iff]
  have h := countProducts_spec (P := fun g : Equiv.Perm (Fin 22) => Q ⇑g) hf
    (forall₂_levelTables (by norm_num) m22Certificate) (Rep.idT (by norm_num))
  simp only [one_mul, List.map_id'] at h
  rw [m22Count, h]
  have e := card_subtype_eq_countP m22Certificate.originalSubgroup (enumeration m22Certificate)
    (enumeration_nodup _ hQ) (mem_enumeration_iff _ hQ) (fun g => Q ⇑g)
  rw [m22Certificate_originalSubgroup] at e
  exact e

theorem exists_m22_of_count (Q : (Fin 22 → Fin 22) → Prop) [DecidablePred Q]
    (h : 0 < m22Count Q) : ∃ x : M22, Q ⇑(x : Equiv.Perm (Fin 22)) := by
  rw [← card_m22_subtype] at h
  obtain ⟨x⟩ := (Nat.card_pos_iff.1 h).1
  exact ⟨x.1, x.2⟩

end CFSG.ComponentClassification.WittDesign
