module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11AutQTIso
public import Certificates.Data.OmegaAutQ

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup Certificates.OmegaAutQ

theorem thetaHom_spec : ∀ A B : SL23, A ^ 4 = 1 → B ^ 4 = 1 →
    (thetaHom (A, B) = 1 ↔ (A = 1 ∧ B = 1) ∨ (A = -1 ∧ B = -1)) := by
  decide +kernel

@[expose] def qm0 : Subgroup S81 :=
  (sl23Q8.prod sl23Q8).map thetaHom

theorem mem_q8List (A : SL23) : A ∈ q8List () ↔ A ^ 4 = 1 :=
  (by decide : ∀ A : SL23, A ∈ q8List () ↔ A ^ 4 = 1) A

theorem mem_qm0 (y : S81) : y ∈ qm0 ↔ y ∈ qmList () := by
  simp only [qm0, qmList, Subgroup.mem_map, Subgroup.mem_prod, mem_sl23Q8, List.mem_dedup,
    List.mem_flatMap, List.mem_map, tabP_eq, Prod.exists, ← mem_q8List]
  constructor
  · rintro ⟨A, B, ⟨hA, hB⟩, rfl⟩
    exact ⟨_, ⟨A, hA, rfl⟩, _, ⟨B, hB, rfl⟩, by rw [← map_mul]; simp⟩
  · rintro ⟨_, ⟨A, hA, rfl⟩, _, ⟨B, hB, rfl⟩, rfl⟩
    exact ⟨A, B, ⟨hA, hB⟩, by rw [← map_mul]; simp⟩

theorem twoCore_iso_qm0 {G : Type} [Group G] [Finite G] (K1 K2 : Subgroup G)
    (hc : ⁅K1, K2⁆ = ⊥) (hcard : Nat.card ↥(K1 ⊔ K2) = 288) (e1 : ↥K1 ≃* SL23)
    (e2 : ↥K2 ≃* SL23) : Nonempty (↥(twoCoreIn (K1 ⊔ K2)) ≃* ↥qm0) :=
  twoCore_iso_of_theta K1 K2 hc hcard e1 e2 thetaHom thetaHom_spec

end CFSG.OddStandard.SmallF3.Omega
