module

public import CFSG.ClassicalInvolution.Asc77.WP2Thm7c

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

namespace T7T

variable {G : Type} [Group G] [Finite G]

theorem conj_zpow {x a : G} {y : G} (h : a * x * a⁻¹ = y) (j : ℤ) : a * x ^ j * a⁻¹ = y ^ j := by
  rw [← h]; simp [← MulAut.conj_apply, ← map_zpow]

theorem exists_cyclic_of_isFAut {R : Subgroup G} {z a : G} (hR : IsQuatSub R)
    (hz : IsUniqueInvolution R z) (hF : IsFAut R a) (ha2 : IsPGroup 2 (Subgroup.zpowers a)) :
    ∃ x : G, x ∈ R ∧ Nat.card R = 2 * Nat.card (Subgroup.zpowers x) ∧
      a * x * a⁻¹ ∈ Subgroup.zpowers x ∧ a * x * a⁻¹ ≠ x ∧ a * x * a⁻¹ ≠ x⁻¹ := by
  obtain ⟨haN, ha2c, Q, R₀, hQ, hQq, hR₀, hcard⟩ := hF
  obtain ⟨k, hk, hRk⟩ := hR.natCard_eq
  have hR2 : IsPGroup 2 R := IsPGroup.of_card (n := k + 2) hRk
  have hR₀R : R₀ = R := (hR₀.2.2 R le_rfl hR2 hR₀.1).symm
  have hQeq : Q = R ⊓ Subgroup.centralizer ({a} : Set G) :=
    (hQ.2.2 (R ⊓ Subgroup.centralizer ({a} : Set G)) le_rfl (hR2.to_le inf_le_left) hQ.1).symm
  have hVR : ∀ y ∈ Subgroup.zpowers a, conjSub y R = R := fun y hy =>
    mem_normalizer_iff_conjSub_eq.mp ((Subgroup.zpowers_le.mpr haN) hy)
  obtain ⟨C, hCR, hCc, hCcard, hCinv⟩ := AscL62.exists_invariant_cyclic hR hz ha2 hVR
  obtain ⟨x, hxC⟩ : ∃ x : G, Subgroup.zpowers x = C := by
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥C)
    refine ⟨g, le_antisymm (Subgroup.zpowers_le.mpr g.2) fun y hy => ?_⟩
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨y, hy⟩)
    exact ⟨j, congrArg Subtype.val hj⟩
  have hxCm : x ∈ C := hxC ▸ Subgroup.mem_zpowers x
  have hcardx : Nat.card R = 2 * Nat.card (Subgroup.zpowers x) := by rw [hxC]; exact hCcard
  have hQcard : Nat.card R = 2 * Nat.card Q := by rw [← hR₀R]; exact hcard
  have haC : conjSub a C = C := hCinv a (Subgroup.mem_zpowers a)
  have hmem : a * x * a⁻¹ ∈ Subgroup.zpowers x := by
    have := conj_mem_conjSub (n := a) hxCm
    rw [haC, ← hxC] at this
    exact this
  refine ⟨x, hCR hxCm, hcardx, hmem, ?_, ?_⟩
  · intro hxa
    have hCQ : C ≤ Q := by
      intro c hc
      rw [← hxC] at hc
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
      have h1 : a * x ^ j * a⁻¹ = x ^ j := conj_zpow hxa j
      rw [hQeq]
      refine ⟨hCR (hxC ▸ Subgroup.zpow_mem _ (Subgroup.mem_zpowers x) j),
        Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      calc x ^ j * a = (a * x ^ j * a⁻¹) * a := by rw [h1]
        _ = a * x ^ j := by group
    have hCQeq : C = Q := Subgroup.eq_of_le_of_card_ge hCQ (by
      have : Nat.card R = 2 * Nat.card C := by rw [← hxC]; exact hcardx
      omega)
    obtain ⟨u, hu, v, hv, huv⟩ := hQq.exists_not_commute
    rw [← hCQeq, ← hxC] at hu hv
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    exact huv (((Commute.refl x).zpow_zpow i j).eq)
  · intro hxa
    have hz2 : z * z = 1 := hz.sq
    have hQR : Q ≤ R := hQeq ▸ inf_le_left
    have hinf : C ⊓ Q ≤ Subgroup.zpowers z := by
      intro c hc
      obtain ⟨hcC, hcQ⟩ := Subgroup.mem_inf.mp hc
      rw [← hxC] at hcC
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hcC
      have hcQ' := hcQ
      rw [hQeq] at hcQ'
      have hcomm : x ^ j * a = a * x ^ j := Subgroup.mem_centralizer_singleton_iff.mp hcQ'.2
      have h1 : a * x ^ j * a⁻¹ = x⁻¹ ^ j := conj_zpow hxa j
      have h2 : a * x ^ j * a⁻¹ = x ^ j := by
        calc a * x ^ j * a⁻¹ = (x ^ j * a) * a⁻¹ := by rw [hcomm]
          _ = x ^ j := by group
      have hsq : x ^ j * x ^ j = 1 := by
        have h3 : x⁻¹ ^ j = x ^ j := h1.symm.trans h2
        rw [inv_zpow'] at h3
        calc x ^ j * x ^ j = x ^ j * (x ^ (-j)) ^ (1 : ℤ) := by rw [h3, zpow_one]
          _ = 1 := by rw [zpow_one, ← zpow_add]; simp
      have hRm : x ^ j ∈ R := hcQ'.1
      rcases hz.unique (x ^ j) hRm hsq with h | h
      · rw [h]; exact one_mem _
      · rw [h]; exact Subgroup.mem_zpowers z
    have hordz : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz2) hz.ne_one
    have hcardinf : Nat.card ↥(C ⊓ Q) ≤ 2 := by
      calc Nat.card ↥(C ⊓ Q) ≤ Nat.card ↥(Subgroup.zpowers z) := Subgroup.card_le_of_le hinf
        _ = 2 := by rw [Nat.card_zpowers, hordz]
    have hCpos : 0 < Nat.card ↥C := Nat.card_pos
    have hrelR : C.relIndex R = 2 := by
      have h1 : C.relIndex R * Nat.card ↥(C ⊓ R) = Nat.card R := Subgroup.relIndex_mul_card C R
      rw [inf_of_le_left hCR, hCcard] at h1
      have : C.relIndex R * Nat.card ↥C = 2 * Nat.card ↥C := by rw [h1]
      exact Nat.eq_of_mul_eq_mul_right hCpos this
    have hrel : C.relIndex Q ≤ 2 := by
      calc C.relIndex Q ≤ C.relIndex R := Subgroup.relIndex_le_of_le_right hQR (by omega)
        _ = 2 := hrelR
    have h3 : C.relIndex Q * Nat.card ↥(C ⊓ Q) = Nat.card Q := Subgroup.relIndex_mul_card C Q
    have h8 := hQq.eight_le
    have h4 : Nat.card Q ≤ 2 * 2 := by
      rw [← h3]
      exact Nat.mul_le_mul hrel hcardinf
    omega

end T7T

end CFSG.ClassicalInvolution.Asc77
