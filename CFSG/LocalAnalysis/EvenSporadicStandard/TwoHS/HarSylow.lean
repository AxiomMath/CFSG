module

public import Certificates.Certificate26131
public import Certificates.Certificate26134

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native

@[expose] noncomputable def harT0 : Subgroup (Equiv.Perm (Fin 11200)) := genOf 11200 harU

@[expose] noncomputable def harT0' : Subgroup (Equiv.Perm (Fin 11200)) := genOf 11200 harCgens

@[expose] noncomputable def harW0 : Subgroup (Equiv.Perm (Fin 11200)) := genOf 11200 harWgens

theorem hn11200 : (11200 : ℕ) < 2 ^ 32 := by norm_num

theorem harU_length' : harU.length = 3 := rfl

section Parts

theorem harU_perm' : ∀ g ∈ harU, permOK 11200 g = true := fun g hg =>
  Certificates.certificate26131.1 g (List.mem_append_left _ hg)

theorem harWgens_perm : ∀ g ∈ harWgens, permOK 11200 g = true := fun g hg =>
  Certificates.certificate26131.1 g (List.mem_append_right _ hg)

theorem harCgens_perm : ∀ g ∈ harCgens, permOK 11200 g = true := fun g hg =>
  harWgens_perm g (by rw [harWgens]; exact List.mem_append_left _ hg)

theorem harT0_card : Nat.card harT0 = 1024 := Certificates.certificate26131.2.1

theorem harT0'_card : Nat.card harT0' = 128 := Certificates.certificate26131.2.2.1

theorem harT0_sq_c {c : Equiv.Perm (Fin 11200)} (hc : Rep 11200 harC0 c) :
    Nat.card {y : harT0 // (y : Equiv.Perm (Fin 11200)) ^ 2 = c} = 80 :=
  (Certificates.certificate26131.2.2.2.2.2.1 c hc).1

theorem harT0_sq_z2 {z : Equiv.Perm (Fin 11200)} (hz : Rep 11200 harZ2 z) :
    Nat.card {y : harT0 // (y : Equiv.Perm (Fin 11200)) ^ 2 = z} = 48 :=
  (Certificates.certificate26131.2.2.2.2.2.2.2.1 z hz).1

theorem harT0'_sq_c {c : Equiv.Perm (Fin 11200)} (hc : Rep 11200 harC0 c) :
    Nat.card {y : harT0' // (y : Equiv.Perm (Fin 11200)) ^ 2 = c} = 16 :=
  (Certificates.certificate26131.2.2.2.2.2.1 c hc).2.1

theorem harT0'_sq_z1 {z : Equiv.Perm (Fin 11200)} (hz : Rep 11200 harZ1 z) :
    Nat.card {y : harT0' // (y : Equiv.Perm (Fin 11200)) ^ 2 = z} = 32 :=
  (Certificates.certificate26131.2.2.2.2.2.2.1 z hz).2.1

theorem harT0'_sq_z2 {z : Equiv.Perm (Fin 11200)} (hz : Rep 11200 harZ2 z) :
    Nat.card {y : harT0' // (y : Equiv.Perm (Fin 11200)) ^ 2 = z} = 16 :=
  (Certificates.certificate26131.2.2.2.2.2.2.2.1 z hz).2.1

theorem harW0_sq_c {c : Equiv.Perm (Fin 11200)} (hc : Rep 11200 harC0 c) :
    Nat.card {y : harW0 // (y : Equiv.Perm (Fin 11200)) ^ 2 = c} = 48 :=
  (Certificates.certificate26131.2.2.2.2.2.1 c hc).2.2.1

theorem harW0_sq_z2 {z : Equiv.Perm (Fin 11200)} (hz : Rep 11200 harZ2 z) :
    Nat.card {y : harW0 // (y : Equiv.Perm (Fin 11200)) ^ 2 = z} = 16 :=
  (Certificates.certificate26131.2.2.2.2.2.2.2.1 z hz).2.2

theorem harT0_centre_card :
    Nat.card ↥(harT0 ⊓ centralizer (harT0 : Set (Equiv.Perm (Fin 11200)))) = 4 :=
  Certificates.certificate26131.2.2.2.2.1

theorem harC_mem_harT0' {c : Equiv.Perm (Fin 11200)} (hc : Rep 11200 harC0 c) : c ∈ harT0' :=
  (Certificates.certificate26131.2.2.2.2.2.1 c hc).2.2.2.1

theorem sq_eq_one_mem_harW0 {y : Equiv.Perm (Fin 11200)} (hy : y ∈ harT0) (hy2 : y ^ 2 = 1) :
    y ∈ harW0 :=
  Certificates.certificate26131.2.2.2.2.2.2.2.2.2 y hy hy2

theorem harC_sq {c : Equiv.Perm (Fin 11200)} (hc : Rep 11200 harC0 c) : c * c = 1 ∧ c ≠ 1 :=
  (Certificates.certificate26131.2.2.2.2.2.1 c hc).2.2.2.2

theorem harZ1_order {z : Equiv.Perm (Fin 11200)} (hz : Rep 11200 harZ1 z) : orderOf z = 2 :=
  (Certificates.certificate26131.2.2.2.2.2.2.1 z hz).2.2.1

theorem harZ_distinct {c z : Equiv.Perm (Fin 11200)} (hc : Rep 11200 harC0 c)
    (hz : Rep 11200 harZ1 z) : z ≠ c ∧ c * z ≠ z ∧ z ≠ 1 ∧ c * z ≠ c ∧ c * z ≠ 1 :=
  Certificates.certificate26131.2.2.2.2.2.2.2.2.1 c z hc hz

theorem harZ1_comm {z : Equiv.Perm (Fin 11200)} (hz : Rep 11200 harZ1 z) :
    ∀ g ∈ harU, z * tp 11200 g = tp 11200 g * z :=
  (Certificates.certificate26131.2.2.2.2.2.2.1 z hz).2.2.2

theorem mem_harT0_of_rep {w : List ℕ} (hw : ∀ l ∈ w, 1 ≤ l ∧ l ≤ 3)
    {x : Equiv.Perm (Fin 11200)} (hx : Rep 11200 (tU w) x) : x ∈ harT0 := by
  obtain ⟨y, hy, hyrep⟩ := rep_wordTbl hn11200 harU_perm' w (by rwa [harU_length'])
  rw [rep_unique hx hyrep]
  exact hy

theorem harC_mem_harT0 {c : Equiv.Perm (Fin 11200)} (hc : Rep 11200 harC0 c) : c ∈ harT0 :=
  mem_harT0_of_rep (w := [1, 2, 1, 2, 3, 1, 2, 1, 2, 3]) (by decide) hc

theorem harZ1_mem_harT0 {z : Equiv.Perm (Fin 11200)} (hz : Rep 11200 harZ1 z) : z ∈ harT0 :=
  mem_harT0_of_rep (w := [3, 3, 3, 3]) (by decide) hz

theorem harT0'_le_harW0 : harT0' ≤ harW0 := by
  apply Subgroup.closure_mono
  apply Set.image_mono
  intro x hx
  have hx' : x ∈ harCgens := by simpa using hx
  have : x ∈ harWgens := by
    rw [harWgens]
    exact List.mem_append_left _ hx'
  simpa using this

end Parts

section WGenerators

theorem harWInvOK_true : harWInvOK = true := Certificates.certificate26134

theorem harW0_eq : harW0 =
    Subgroup.closure ((harT0' : Set (Equiv.Perm (Fin 11200))) ∪ {y | y ∈ harT0 ∧ y ^ 2 = 1}) := by
  apply le_antisymm
  · show Subgroup.closure _ ≤ _
    rw [Subgroup.closure_le]
    rintro _ ⟨g, hg, rfl⟩
    have hg' : g ∈ harWgens := by simpa using hg
    have hperm := harWgens_perm g hg'
    have hrep := rep_tp hperm
    rw [harWgens, List.mem_append] at hg'
    rcases hg' with hgC | hgE
    · exact Subgroup.subset_closure (Or.inl (tp_mem_genOf hgC))
    · have hinv := harWInvOK_true
      simp only [harWInvOK, Bool.and_eq_true, Bool.not_eq_true'] at hinv
      obtain ⟨⟨⟨hs1, -⟩, hs2⟩, -⟩ := hinv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hgE
      rcases hgE with h | h
      · have hrep' : Rep 11200 (tU [1]) (tp 11200 g) := by
          rw [← h]
          exact hrep
        have hmem : tp 11200 g ∈ harT0 := mem_harT0_of_rep (w := [1]) (by decide) hrep'
        have hsq : tp 11200 g ^ 2 = 1 := by
          rw [pow_two]
          exact (tblEq_iff_eq (Rep.compT hrep' hrep') (Rep.idT hn11200)).1
            (by rw [← h] at hs1 ⊢; exact hs1)
        exact Subgroup.subset_closure (Or.inr ⟨hmem, hsq⟩)
      · have hrep' : Rep 11200 (tU [2, 3, 3]) (tp 11200 g) := by
          rw [← h]
          exact hrep
        have hmem : tp 11200 g ∈ harT0 := mem_harT0_of_rep (w := [2, 3, 3]) (by decide) hrep'
        have hsq : tp 11200 g ^ 2 = 1 := by
          rw [pow_two]
          exact (tblEq_iff_eq (Rep.compT hrep' hrep') (Rep.idT hn11200)).1
            (by rw [← h] at hs2 ⊢; exact hs2)
        exact Subgroup.subset_closure (Or.inr ⟨hmem, hsq⟩)
  · rw [Subgroup.closure_le]
    rintro y (hy | ⟨hyT, hy2⟩)
    · exact harT0'_le_harW0 hy
    · exact sq_eq_one_mem_harW0 hyT hy2

end WGenerators

end CFSG.EvenSporadicStandard.TwoHS
