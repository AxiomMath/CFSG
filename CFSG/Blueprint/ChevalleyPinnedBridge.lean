module

public import CFSG.Blueprint.ChevalleyPinnedLemmas
public import Certificates.Certificate113

public section

namespace CFSG.Blueprint.Chevalley

variable {τ : Tag}

@[expose] def certWalk (τ : Tag) (w : List ℕ) (p : ℕ) : ℕ :=
  w.foldl (fun q i => τ.rootCertificate.image q (τ.idx i)) p

@[expose] def witnessCheck (τ : Tag) : Bool :=
  ((List.range τ.witnesses.roots.length).all fun a =>
      τ.rootCertificate.roots.getD
          (certWalk τ (decodeWord (τ.witnesses.words.getD a 0))
            (τ.idx (τ.witnesses.seeds.getD a 0)))
          0 ==
        τ.witnesses.roots.getD a 0) &&
    τ.rootCertificate.roots.all fun c => τ.witnesses.roots.contains c

theorem witnessCheck_G2 : witnessCheck .G2 = true := by decide +kernel

theorem witnessCheck_F4 : witnessCheck .F4 = true := by decide +kernel

theorem witnessCheck_D4 : witnessCheck .D4 = true := by decide +kernel

theorem witnessCheck_E6 : witnessCheck .E6 = true := by decide +kernel

theorem witnessCheck_E7 : witnessCheck .E7 = true := by decide +kernel

theorem witnessCheck_E8 : witnessCheck .E8 = true := by decide +kernel

theorem witnessCheck_eq_true : ∀ τ : Tag, witnessCheck τ = true
  | .G2 => witnessCheck_G2
  | .F4 => witnessCheck_F4
  | .D4 => witnessCheck_D4
  | .E6 => witnessCheck_E6
  | .E7 => witnessCheck_E7
  | .E8 => witnessCheck_E8

theorem witnessCheck_spec :
    (∀ a < τ.witnesses.roots.length,
      τ.rootCertificate.roots.getD
          (certWalk τ (decodeWord (τ.witnesses.words.getD a 0))
            (τ.idx (τ.witnesses.seeds.getD a 0))) 0 =
        τ.witnesses.roots.getD a 0) ∧
      ∀ c ∈ τ.rootCertificate.roots, c ∈ τ.witnesses.roots := by
  have h := witnessCheck_eq_true τ
  simp only [witnessCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq,
    List.contains_iff_mem] at h
  exact h

private theorem cert_basis_table :
    τ.rank ≤ τ.rootCertificate.roots.length ∧
      (∀ j : Fin τ.rank, τ.rootCertificate.root j = Pi.single j 1) ∧
      ∀ k < τ.rootCertificate.roots.length, ∀ i : Fin τ.rank,
        τ.rootCertificate.image k i < τ.rootCertificate.roots.length ∧
          τ.rootCertificate.root (τ.rootCertificate.image k i) =
            reflect τ i (τ.rootCertificate.root k) := by
  have h := τ.rootCertificate_check
  simp only [RootCertificate.check, RootCertificate.checkBasis, RootCertificate.checkTable,
    Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_finRange, List.mem_range,
    true_implies] at h
  exact ⟨h.1.1.1, fun j => RootCertificate.eq_of_ofFn_beq (h.1.1.2 j),
    fun k hk i => ⟨(h.2 k hk i).1, RootCertificate.eq_of_ofFn_beq (h.2 k hk i).2⟩⟩

theorem certWalk_spec (w : List ℕ) {p : ℕ} (hp : p < τ.rootCertificate.roots.length) :
    certWalk τ w p < τ.rootCertificate.roots.length ∧
      τ.rootCertificate.root (certWalk τ w p) =
        w.foldl (fun v i => reflect τ (τ.idx i) v) (τ.rootCertificate.root p) := by
  induction w generalizing p with
  | nil => exact ⟨hp, rfl⟩
  | cons i w ih =>
    obtain ⟨hlt, hroot⟩ := cert_basis_table.2.2 p hp (τ.idx i)
    obtain ⟨h₁, h₂⟩ := ih hlt
    refine ⟨h₁, ?_⟩
    rw [List.foldl_cons, ← hroot]
    exact h₂

private theorem foldl_reflect_witness {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) (p : ℕ → Bool)
    (hp : ∀ c, p c = true ↔ decodeVec c = α) :
    (decodeWord (τ.witnesses.words.getD (τ.witnesses.roots.findIdx p) 0)).foldl
        (fun v i => reflect τ (τ.idx i) v)
        (Pi.single (τ.idx (τ.witnesses.seeds.getD (τ.witnesses.roots.findIdx p) 0)) 1) = α := by
  obtain ⟨hwalk, hall⟩ := witnessCheck_spec (τ := τ)
  obtain ⟨m, hm, rfl⟩ := RootCertificate.exists_root_eq τ.rootCertificate_check hα
  have hmem : τ.rootCertificate.roots.getD m 0 ∈ τ.witnesses.roots := by
    rw [List.getD_eq_getElem _ _ hm]
    exact hall _ (List.getElem_mem hm)
  have hk : τ.witnesses.roots.findIdx p < τ.witnesses.roots.length :=
    List.findIdx_lt_length_of_exists ⟨_, hmem, (hp _).2 rfl⟩
  have hdec : decodeVec (τ.witnesses.roots.getD (τ.witnesses.roots.findIdx p) 0) =
      τ.rootCertificate.root m := by
    rw [List.getD_eq_getElem _ _ hk]
    exact (hp _).1 (List.findIdx_getElem (w := hk))
  have hseed : ((τ.idx (τ.witnesses.seeds.getD (τ.witnesses.roots.findIdx p) 0) : Fin τ.rank) :
      ℕ) < τ.rootCertificate.roots.length :=
    lt_of_lt_of_le (Fin.is_lt _) cert_basis_table.1
  obtain ⟨-, hroot⟩ := certWalk_spec (decodeWord (τ.witnesses.words.getD
    (τ.witnesses.roots.findIdx p) 0)) hseed
  rw [cert_basis_table.2.1] at hroot
  rw [← hroot, ← hdec, ← hwalk _ hk]
  rfl

theorem foldl_reflect_pinnedData {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    (pinnedData τ α).2.1.foldl (fun v i => reflect τ (τ.idx i) v)
      (Pi.single (pinnedData τ α).1 1) = α := by
  by_cases h₁ : ∃ j, α = Pi.single j 1
  · obtain ⟨j, rfl⟩ := h₁
    rw [pinnedData_single]
    rfl
  by_cases h₂ : ∃ j, α = -Pi.single j 1
  · obtain ⟨j, rfl⟩ := h₂
    have hidx : τ.idx (j : ℕ) = j := Fin.ext (Nat.mod_eq_of_lt j.2)
    rw [pinnedData_neg_single]
    simp only [List.foldl_cons, List.foldl_nil, hidx, reflect_single_self]
  rw [pinnedData, dite_eq_right h₁, dite_eq_right h₂]
  exact foldl_reflect_witness hα _ fun c => decide_eq_true_iff

end CFSG.Blueprint.Chevalley
