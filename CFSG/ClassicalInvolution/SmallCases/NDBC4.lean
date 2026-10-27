module

public import CFSG.ClassicalInvolution.SmallCases.NDBC3
import CFSG.ClassicalInvolution.Asc77.WP3SCSModel
import CFSG.ClassicalInvolution.Asc77.WP3SCUNGa

public section

namespace CFSG.ClassicalInvolution.NDB

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Asc77.ExactLayer

namespace Cover

section Twin

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G}

omit [Fact p.Prime] in
theorem oddCoreIn_exactLayer_le (hΩ : ConjInvariant Ω) (z : G) :
    oddCoreIn (exactLayer Ω z) ≤ oddCoreIn (Subgroup.centralizer ({z} : Set G)) :=
  le_oddCoreIn_of_normalizes ((oddCoreIn_le _).trans (exactLayer_le_centralizer Ω z))
    (fun _ hn => Asc77.mem_normalizer_oddCoreIn_exactLayer hΩ hn) (odd_card_oddCoreIn _)

theorem exists_twin_of_eq (C : Asc77.XCtx p f Ω z) (htrans : ∀ M ∈ Ω, ∃ g : G, conjSub g C.K = M)
    {N₁ N₂ : Subgroup G} (h₁ : N₁ ∈ tqMembers Ω z) (h₂ : N₂ ∈ tqMembers Ω z) {n₁ n₂ : G}
    (hn₁ : IsClassicalMember p f N₁ n₁) (hn₂ : IsClassicalMember p f N₂ n₂)
    (hne : modOdd z (exactCore z N₁) ≠ modOdd z (exactCore z N₂))
    (heq : oddQuotMk z ⟨n₁, C.involution_mem_centralizer h₁ hn₁⟩ =
      oddQuotMk z ⟨n₂, C.involution_mem_centralizer h₂ hn₂⟩) :
    ∃ T ∈ Ω, T ≠ C.K ∧ IsClassicalMember p f T z := by
  have hf : 0 < f := Nat.pos_of_ne_zero (by rintro rfl; have := C.hq; simp at this)
  have hΩ := C.hΩ.conjInvariant
  have hY₁ : n₁ ∈ exactLayer Ω z :=
    exactCore_le_exactLayer h₁ (C.involution_mem_exactCore h₁ hn₁)
  have hY₂ : n₂ ∈ exactLayer Ω z :=
    exactCore_le_exactLayer h₂ (C.involution_mem_exactCore h₂ hn₂)
  obtain ⟨o, ho, hno⟩ := C.exists_conj_of_oddQuotMk_eq hY₂ hY₁ hn₂.isCentralInvolution.sq
    hn₁.isCentralInvolution.sq heq.symm
  have hoO : o ∈ oddCoreIn (Subgroup.centralizer ({z} : Set G)) :=
    oddCoreIn_exactLayer_le hΩ z ho
  have hoC := oddCoreIn_le _ hoO
  have hN' : IsClassicalMember p f (conjSub o⁻¹ N₂) n₁ := by
    have h := hn₂.conj o⁻¹
    rwa [hno, show o⁻¹ * (o * n₁ * o⁻¹) * o⁻¹⁻¹ = n₁ by group] at h
  have hN'Ω : conjSub o⁻¹ N₂ ∈ Ω := hΩ o⁻¹ N₂ h₂.1
  have hne' : conjSub o⁻¹ N₂ ≠ N₁ := by
    intro h
    apply hne
    rw [← h]
    have e := exactCore_conjSub o⁻¹ z N₂
    rw [Bootstrap.conj_eq_of_mem_centralizer_singleton (Subgroup.inv_mem _ hoC)] at e
    rw [e, Asc77.modOdd_conjSub_of_mem_oddCoreIn (Subgroup.inv_mem _ hoO)]
  obtain ⟨g, hg⟩ := htrans N₁ h₁.1
  have hgz : g * z * g⁻¹ = n₁ := by
    have h := C.K_cl.conj g
    rw [hg] at h
    exact (h.eq_of_isCentralInvolution C.hp hf hn₁.isCentralInvolution).symm
  refine ⟨conjSub g⁻¹ (conjSub o⁻¹ N₂), hΩ _ _ hN'Ω, fun h => hne' ?_, ?_⟩
  · rw [← hg, ← h, conjSub_conjSub_inv]
  · have h := hN'.conj g⁻¹
    rwa [← hgz, show g⁻¹ * (g * z * g⁻¹) * g⁻¹⁻¹ = z by group] at h

theorem modOdd_ne_of_ne (C : Asc77.XCtx p f Ω z) {j : Fin C.D.card}
    (hD4 : C.D.tag j ≠ .trialityD4) {R₁ R₂ : Subgroup (compModel C.D j).K}
    (hR₁ : R₁ ∈ fundamentalSubgroups (C.D.tag j) (compModel C.D j).D)
    (hR₂ : R₂ ∈ fundamentalSubgroups (C.D.tag j) (compModel C.D j).D) (hne : R₁ ≠ R₂) :
    R₁.map (C.psi j) ≠ R₂.map (C.psi j) := fun h =>
  hne (RouteD.eq_of_map_eq_of_perfect (C.psi j) (C.psi_ker j)
    (C.fund_perfect j hD4 hR₁).ge (C.fund_perfect j hD4 hR₂).ge h)

theorem mul_eq_of_pair (C : Asc77.XCtx p f Ω z) (htrans : ∀ M ∈ Ω, ∃ g : G, conjSub g C.K = M)
    (hnoF : ∀ A : Subgroup G, ¬ Theorem5.FuzzyFrameOn p f Ω A)
    (hnoT : ¬ ∃ T ∈ Ω, T ≠ C.K ∧ IsClassicalMember p f T z) {j : Fin C.D.card}
    (hj : ¬ (C.D.tag j = .PSL ∧ C.D.rank j = 2)) (hD4 : C.D.tag j ≠ .trialityD4)
    {R₁ R₂ : Subgroup (compModel C.D j).K}
    (hR₁ : R₁ ∈ fundamentalSubgroups (C.D.tag j) (compModel C.D j).D)
    (hR₂ : R₂ ∈ fundamentalSubgroups (C.D.tag j) (compModel C.D j).D) (hne : R₁ ≠ R₂)
    (hc : Commutes R₁ R₂) {N₁ N₂ : Subgroup G} (h₁ : N₁ ∈ tqMembers Ω z)
    (h₂ : N₂ ∈ tqMembers Ω z) (hN₁ : modOdd z (exactCore z N₁) = R₁.map (C.psi j))
    (hN₂ : modOdd z (exactCore z N₂) = R₂.map (C.psi j)) {n₁ n₂ : G}
    (hn₁ : IsClassicalMember p f N₁ n₁) (hn₂ : IsClassicalMember p f N₂ n₂) :
    oddQuotMk z ⟨n₁, C.involution_mem_centralizer h₁ hn₁⟩ *
        oddQuotMk z ⟨n₂, C.involution_mem_centralizer h₂ hn₂⟩ =
      oddQuotMk z ⟨z, Asc77.XCtx.hzC z⟩ := by
  have hx₁ : oddQuotMk z ⟨n₁, C.involution_mem_centralizer h₁ hn₁⟩ ∈ R₁.map (C.psi j) :=
    hN₁ ▸ oddQuotMk_mem_modOdd (C.involution_mem_exactCore h₁ hn₁) _
  have hx₂ : oddQuotMk z ⟨n₂, C.involution_mem_centralizer h₂ hn₂⟩ ∈ R₂.map (C.psi j) :=
    hN₂ ▸ oddQuotMk_mem_modOdd (C.involution_mem_exactCore h₂ hn₂) _
  obtain ⟨y₁, -, hxy₁⟩ :=
    exists_not_commute C hj hR₁ hx₁ (C.isUniqueInvolution_modOdd h₁ hn₁).ne_one
  obtain ⟨y₂, -, hxy₂⟩ :=
    exists_not_commute C hj hR₂ hx₂ (C.isUniqueInvolution_modOdd h₂ hn₂).ne_one
  have hcomm : ∀ x ∈ modOdd z (exactCore z N₁), ∀ y ∈ modOdd z (exactCore z N₂),
      x * y = y * x := by
    rw [hN₁, hN₂]
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hc a ha b hb]
  rcases eq_or_mul_eq C hnoF h₁ h₂ hn₁ hn₂ hcomm
    (fun h => hxy₁ (by rw [h]; exact zbar_comm y₁))
    (fun h => hxy₂ (by rw [h]; exact zbar_comm y₂)) with h | h
  · refine absurd (exists_twin_of_eq C htrans h₁ h₂ hn₁ hn₂ ?_ h) hnoT
    rw [hN₁, hN₂]
    exact modOdd_ne_of_ne C hD4 hR₁ hR₂ hne
  · exact h

theorem zbar_mem_of_pair (C : Asc77.XCtx p f Ω z) (htrans : ∀ M ∈ Ω, ∃ g : G, conjSub g C.K = M)
    (hnoF : ∀ A : Subgroup G, ¬ Theorem5.FuzzyFrameOn p f Ω A)
    (hnoT : ¬ ∃ T ∈ Ω, T ≠ C.K ∧ IsClassicalMember p f T z) {j : Fin C.D.card}
    (hj : ¬ (C.D.tag j = .PSL ∧ C.D.rank j = 2)) (hG2 : C.D.tag j ≠ .G2)
    (hD4 : C.D.tag j ≠ .trialityD4) {R₁ R₂ : Subgroup (compModel C.D j).K}
    (hR₁ : R₁ ∈ fundamentalSubgroups (C.D.tag j) (compModel C.D j).D)
    (hR₂ : R₂ ∈ fundamentalSubgroups (C.D.tag j) (compModel C.D j).D) (hne : R₁ ≠ R₂)
    (hc : Commutes R₁ R₂) : oddQuotMk z ⟨z, Asc77.XCtx.hzC z⟩ ∈ (C.psi j).range := by
  obtain ⟨N₁, h₁, hN₁⟩ := C.exists_member_of_fund j (C.single j hG2 hD4) hR₁
  obtain ⟨N₂, h₂, hN₂⟩ := C.exists_member_of_fund j (C.single j hG2 hD4) hR₂
  obtain ⟨n₁, hn₁⟩ := C.hΩ.classical N₁ h₁.1
  obtain ⟨n₂, hn₂⟩ := C.hΩ.classical N₂ h₂.1
  rw [← mul_eq_of_pair C htrans hnoF hnoT hj hD4 hR₁ hR₂ hne hc h₁ h₂ hN₁ hN₂ hn₁ hn₂]
  have hx₁ : oddQuotMk z ⟨n₁, C.involution_mem_centralizer h₁ hn₁⟩ ∈ (C.psi j).range :=
    Subgroup.map_le_range _ _ (hN₁ ▸ oddQuotMk_mem_modOdd (C.involution_mem_exactCore h₁ hn₁) _)
  have hx₂ : oddQuotMk z ⟨n₂, C.involution_mem_centralizer h₂ hn₂⟩ ∈ (C.psi j).range :=
    Subgroup.map_le_range _ _ (hN₂ ▸ oddQuotMk_mem_modOdd (C.involution_mem_exactCore h₂ hn₂) _)
  exact Subgroup.mul_mem _ hx₁ hx₂

theorem false_of_triangle (C : Asc77.XCtx p f Ω z) (htrans : ∀ M ∈ Ω, ∃ g : G, conjSub g C.K = M)
    (hnoF : ∀ A : Subgroup G, ¬ Theorem5.FuzzyFrameOn p f Ω A)
    (hnoT : ¬ ∃ T ∈ Ω, T ≠ C.K ∧ IsClassicalMember p f T z) {j : Fin C.D.card}
    (hj : ¬ (C.D.tag j = .PSL ∧ C.D.rank j = 2)) (hG2 : C.D.tag j ≠ .G2)
    (hD4 : C.D.tag j ≠ .trialityD4) {R₁ R₂ R₃ : Subgroup (compModel C.D j).K}
    (hR₁ : R₁ ∈ fundamentalSubgroups (C.D.tag j) (compModel C.D j).D)
    (hR₂ : R₂ ∈ fundamentalSubgroups (C.D.tag j) (compModel C.D j).D)
    (hR₃ : R₃ ∈ fundamentalSubgroups (C.D.tag j) (compModel C.D j).D) (h12 : R₁ ≠ R₂)
    (h13 : R₁ ≠ R₃) (h23 : R₂ ≠ R₃) (c12 : Commutes R₁ R₂) (c13 : Commutes R₁ R₃)
    (c23 : Commutes R₂ R₃) : False := by
  obtain ⟨N₁, h₁, hN₁⟩ := C.exists_member_of_fund j (C.single j hG2 hD4) hR₁
  obtain ⟨N₂, h₂, hN₂⟩ := C.exists_member_of_fund j (C.single j hG2 hD4) hR₂
  obtain ⟨N₃, h₃, hN₃⟩ := C.exists_member_of_fund j (C.single j hG2 hD4) hR₃
  obtain ⟨n₁, hn₁⟩ := C.hΩ.classical N₁ h₁.1
  obtain ⟨n₂, hn₂⟩ := C.hΩ.classical N₂ h₂.1
  obtain ⟨n₃, hn₃⟩ := C.hΩ.classical N₃ h₃.1
  have e12 := mul_eq_of_pair C htrans hnoF hnoT hj hD4 hR₁ hR₂ h12 c12 h₁ h₂ hN₁ hN₂ hn₁ hn₂
  have e13 := mul_eq_of_pair C htrans hnoF hnoT hj hD4 hR₁ hR₃ h13 c13 h₁ h₃ hN₁ hN₃ hn₁ hn₃
  have e23 := mul_eq_of_pair C htrans hnoF hnoT hj hD4 hR₂ hR₃ h23 c23 h₂ h₃ hN₂ hN₃ hn₂ hn₃
  have e : oddQuotMk z ⟨n₂, C.involution_mem_centralizer h₂ hn₂⟩ =
      oddQuotMk z ⟨n₃, C.involution_mem_centralizer h₃ hn₃⟩ :=
    mul_left_cancel (e12.trans e13.symm)
  rw [e, (C.isUniqueInvolution_modOdd h₃ hn₃).sq] at e23
  exact (C.isUniqueInvolution_modOdd h₃ hn₃).ne_one
    (by have hz1 := eq_one_of_oddQuotMk_eq_one (Subtype.ext C.hKz.sq) e23.symm
        exact absurd (congrArg Subtype.val hz1) C.hKz.ne_one)

end Twin

end Cover

end CFSG.ClassicalInvolution.NDB
