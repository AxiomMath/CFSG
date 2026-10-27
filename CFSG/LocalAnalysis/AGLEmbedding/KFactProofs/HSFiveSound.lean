module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.MaxD2HeisSound

public section

namespace CFSG.AGLEmbedding.MaxD2

open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four CFSG.AGLEmbedding.FusD2
open Certificates.MaxD2Perm Certificates.MaxD2Heis
open Certificates.FusD2Perm (powT wordT)
open scoped commutatorElement

section ClassCount

variable {Q : Type*} [Group Q]

theorem mem_normalizer_inf_centralizer [Finite Q] {R : Subgroup Q} {g : Q}
    (hg : g ∈ Subgroup.normalizer (R : Set Q)) :
    g ∈ Subgroup.normalizer ((R ⊓ Subgroup.centralizer (R : Set Q) : Subgroup Q) : Set Q) := by
  refine Subgroup.mem_normalizer_fintype fun z hz => ?_
  obtain ⟨hzR, hzC⟩ := hz
  have hzC' : z ∈ Subgroup.centralizer (R : Set Q) := hzC
  refine ⟨(Subgroup.mem_normalizer_iff.1 hg z).1 hzR, ?_⟩
  show g * z * g⁻¹ ∈ Subgroup.centralizer (R : Set Q)
  rw [Subgroup.mem_centralizer_iff]
  intro r hr
  have hr' : g⁻¹ * r * g⁻¹⁻¹ ∈ R :=
    (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hg) r).1 hr
  have hcomm : g⁻¹ * r * g * z = z * (g⁻¹ * r * g) := by
    have := Subgroup.mem_centralizer_iff.1 hzC' (g⁻¹ * r * g⁻¹⁻¹) hr'
    simpa using this
  calc r * (g * z * g⁻¹) = g * (g⁻¹ * r * g * z) * g⁻¹ := by group
    _ = g * (z * (g⁻¹ * r * g)) * g⁻¹ := by rw [hcomm]
    _ = g * z * g⁻¹ * r := by group

end ClassCount

@[expose] def HeisDataEq (p m lam e : ℕ) {Q : Type*} [Group Q] (G R : Subgroup Q) : Prop :=
  R ≤ G ∧ Nat.card R = p ^ 3 ∧
  (∀ g ∈ G, (∀ r ∈ R, g * r = r * g) → g ∈ R) ∧
  Nat.card (R ⊓ Subgroup.centralizer (R : Set Q) : Subgroup Q) = p ∧
  ⁅R, R⁆ = R ⊓ Subgroup.centralizer (R : Set Q) ∧
  (∀ r ∈ R, r ^ p = 1) ∧
  Group.IsSolvable ↥(Subgroup.normalizer (R : Set Q) ⊓ G) ∧
  ∃ t ∈ Subgroup.normalizer (R : Set Q) ⊓ G,
    (∀ x ∈ R, ∃ z ∈ R ⊓ Subgroup.centralizer (R : Set Q), t ^ m * x * (t ^ m)⁻¹ = x ^ lam * z) ∧
    (∀ x ∈ R, ∃ z ∈ R ⊓ Subgroup.centralizer (R : Set Q), t ^ e * x * (t ^ e)⁻¹ = x⁻¹ * z) ∧
    ∀ k : ℕ, 0 < k → k < m → ∀ F : Subgroup Q, R ⊓ Subgroup.centralizer (R : Set Q) ≤ F →
      F ≤ R → F.relIndex R = p → t ^ k ∉ Subgroup.normalizer (F : Set Q)

section Perm

variable {D : Data} {S : List (Equiv.Perm (Fin D.n))}

variable (hgs : ∀ j, TabRep (D.gT.getD j (idTab D.n)) (S.getD j 1))
  (hgi : ∀ j, TabRep ((giT D).getD j (idTab D.n)) (S.getD j 1)⁻¹)

include hgs hgi

theorem centralizer_le_Eq (hNeq : Subgroup.normalizer (Rsub D S :
      Set (Equiv.Perm (Fin D.n))) ⊓ Gsub S = Nsub D S)
    (hR : checkHR D = true) (hN : checkN D = true) (hCent : checkHCent D = true) :
    ∀ g ∈ Gsub S, (∀ r ∈ Rsub D S, g * r = r * g) → g ∈ Rsub D S := by
  intro g hgG hgc
  have hR' := enum_RH hgs hgi hR
  have hN' := enum_N hgs hgi hN
  have hRok : enumOK D.n (rGens D) (hrEnum D) = true := by
    simp only [checkHR, Bool.and_eq_true] at hR
    exact hR.1
  have hgN : g ∈ Nsub D S := by
    rw [← hNeq]
    refine ⟨Subgroup.mem_normalizer_fintype (S := (Rsub D S : Set (Equiv.Perm (Fin D.n))))
      (fun r hr => ?_), hgG⟩
    rw [hgc r hr, mul_inv_cancel_right]
    exact hr
  obtain ⟨k, hk, hgk⟩ := hN'.exists_pos hgN
  simp only [checkHCent, allBelow_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hCent
  rcases hCent k hk with h | h
  · exfalso
    have hc := (commutesUV_iff (rep_u hgs hgi) (rep_v hgs hgi) hgk).2
      ⟨(hgc _ uW_mem), (hgc _ vW_mem)⟩
    rw [hc] at h
    exact absurd h (by decide)
  · exact (found_iff_mem hRok hR' hgk).1 h

end Perm

end CFSG.AGLEmbedding.MaxD2
