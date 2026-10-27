module

public import CFSG.Literature.GL52Basic
public import CFSG.Sporadic.Schreier.CountSpec
public meta import CFSG.Literature.GL52Basic
public meta import CFSG.Sporadic.Schreier.CountSpec
public import CFSG.Literature.GL52ChainInputs
public import Certificates.Certificate2000

public section

namespace CFSG.Literature.GL52

open Matrix CFSG.Certificates CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native

theorem rep_iff_rep_glPerm (T : Table) (g : G) : Rep 31 T g ↔ Rep 31 T (glPerm g) := Iff.rfl

theorem glCert_check : glCert.check = true :=
  Certificates.certificate2000.1

theorem glCert_orbitSizes : List.ofFn glCert.orbitSize = [31, 30, 28, 24, 16] :=
  Certificates.certificate2000.2

theorem glCert_valid : ValidSchreier glCert := glCert_check

theorem card_glCert : Nat.card glCert.originalSubgroup = 9999360 := by
  rw [← glCert.orderCertificate_eq_card glCert_valid, RawSchreierDatum.orderCertificate,
    ← List.ofFn_eq_map, glCert_orbitSizes]
  rfl

theorem glCert_originalSubgroup_eq :
    glCert.originalSubgroup = Subgroup.closure {glPerm glA, glPerm glB} := by
  rw [glCert, certificate_originalSubgroup, tab_eq, tab_eq]
  congr 1
  ext x
  simp

theorem glCert_original : glCert.originalSubgroup = glPerm.range := by
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rw [glCert_originalSubgroup_eq, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact ⟨glA, rfl⟩
    · exact ⟨glB, rfl⟩
  · rw [card_glCert, ← Nat.card_congr (MonoidHom.ofInjective glPerm_injective).toEquiv,
      card_GL52]
    norm_num

theorem mem_glCert_iff (π : Equiv.Perm (Fin 31)) :
    π ∈ glCert.originalSubgroup ↔ ∃ g, glPerm g = π := by
  rw [glCert_original]
  rfl

@[expose] noncomputable def subtypeEquiv (Q : Equiv.Perm (Fin 31) → Prop) :
    {g : G // Q (glPerm g)} ≃ {x : glCert.originalSubgroup // Q x} :=
  Equiv.ofBijective (fun g => ⟨⟨glPerm g.1, (mem_glCert_iff _).2 ⟨g.1, rfl⟩⟩, g.2⟩)
    ⟨fun g h hgh => Subtype.ext (glPerm_injective
        (congrArg (fun x : {x : glCert.originalSubgroup // Q x} => (x.1 : Equiv.Perm (Fin 31)))
          hgh)),
      fun x => by
        obtain ⟨g, hg⟩ := (mem_glCert_iff _).1 x.1.2
        exact ⟨⟨g, hg ▸ x.2⟩, Subtype.ext (Subtype.ext hg)⟩⟩

theorem card_subtype_glPerm (Q : Equiv.Perm (Fin 31) → Prop) [DecidablePred Q] (f : Table → Bool)
    (hf : ∀ (T : Table) (π : Equiv.Perm (Fin 31)), Rep 31 T π → (f T = true ↔ Q π)) :
    Nat.card {g : G // Q (glPerm g)} = countProducts 31 f (levelTables glCert) (idT 31) := by
  rw [Nat.card_congr (subtypeEquiv Q)]
  have h := countProducts_spec (P := Q) hf (forall₂_levelTables (by norm_num) glCert)
    (Rep.idT (G := Equiv.Perm (Fin 31)) (by norm_num))
  simp only [one_mul, List.map_id'] at h
  rw [h]
  exact card_subtype_eq_countP glCert.originalSubgroup (enumeration glCert)
    (enumeration_nodup _ glCert_valid) (mem_enumeration_iff _ glCert_valid) Q

end CFSG.Literature.GL52
