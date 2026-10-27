module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51QFAt

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P51Q

open CFSG Subgroup DihedralGroup

theorem dihedral_comm {k : ℕ} (x y : DihedralGroup k) (hx : x * x ≠ 1) (hy : y * y ≠ 1) :
    x * y = y * x := by
  cases x with
  | r i =>
    cases y with
    | r j => rw [r_mul_r, r_mul_r, add_comm]
    | sr j => exact absurd (sr_mul_self j) hy
  | sr i => exact absurd (sr_mul_self i) hx

theorem card_two_nsmul_eq_zero_le {k : ℕ} [NeZero k] :
    (Finset.univ.filter fun j : ZMod k => j + j = 0).card ≤ 2 := by
  classical
  have h := IsAddCyclic.card_nsmul_eq_zero_le (α := ZMod k) (n := 2) (by norm_num)
  convert h using 3 with j
  rw [two_nsmul]

theorem card_le_four_of_dihedral {k : ℕ} [NeZero k] (P : Subgroup (DihedralGroup k))
    (hP : ∀ x ∈ P, x * x = 1) : Nat.card P ≤ 4 := by
  classical
  set S := Finset.univ.filter fun j : ZMod k => j + j = 0 with hSdef
  have hS : S.card ≤ 2 := card_two_nsmul_eq_zero_le
  have hcard : Nat.card P = (Finset.univ.filter fun x => x ∈ P).card := by
    rw [Nat.card_eq_fintype_card, ← Fintype.card_subtype]
  have hrot : ∀ j : ZMod k, r j ∈ P → j ∈ S := fun j hj => by
    have h1 := hP _ hj
    rw [r_mul_r, ← r_zero] at h1
    simpa [hSdef] using r.inj h1
  by_cases hrefl : ∃ i, sr i ∈ P
  · obtain ⟨i, hi⟩ := hrefl
    have hsub : (Finset.univ.filter fun x => x ∈ P) ⊆
        S.image r ∪ S.image fun j => sr (j + i) := by
      intro x hx
      rw [Finset.mem_filter] at hx
      have hx2 := hx.2
      cases x with
      | r j => exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨j, hrot j hx2, rfl⟩)
      | sr j =>
        refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j - i, ?_, by rw [sub_add_cancel]⟩)
        have h1 := hP _ (mul_mem hi hx2)
        rw [sr_mul_sr, r_mul_r, ← r_zero] at h1
        simpa [hSdef] using r.inj h1
    calc Nat.card P = (Finset.univ.filter fun x => x ∈ P).card := hcard
      _ ≤ (S.image r ∪ S.image fun j => sr (j + i)).card := Finset.card_le_card hsub
      _ ≤ (S.image r).card + (S.image fun j => sr (j + i)).card := Finset.card_union_le _ _
      _ ≤ S.card + S.card := add_le_add Finset.card_image_le Finset.card_image_le
      _ ≤ 4 := by omega
  · simp only [not_exists] at hrefl
    have hsub : (Finset.univ.filter fun x => x ∈ P) ⊆ S.image r := by
      intro x hx
      rw [Finset.mem_filter] at hx
      cases x with
      | r j => exact Finset.mem_image.mpr ⟨j, hrot j hx.2, rfl⟩
      | sr j => exact absurd hx.2 (hrefl j)
    calc Nat.card P = (Finset.univ.filter fun x => x ∈ P).card := hcard
      _ ≤ (S.image r).card := Finset.card_le_card hsub
      _ ≤ S.card := Finset.card_image_le
      _ ≤ 4 := by omega

theorem fAt_of_dihedral {X : Type} [Group X] {z : X} {k : ℕ} [NeZero k]
    (φ : centralizer ({z} : Set X) ≃* DihedralGroup k) : FAt X z := by
  intro P hPC _ h8 _
  refine ⟨fun ⟨⟨u, hu, v, hv, huv⟩, huniq⟩ => ?_, fun hall => ?_⟩
  · have hsq : ∀ w ∈ P, w * w = 1 → ∀ y ∈ P, w * y = y * w := by
      intro w hw hww y hy
      rcases huniq w hw hww with rfl | rfl
      · rw [one_mul, mul_one]
      · exact (mem_centralizer_singleton_iff.mp (hPC hy)).symm
    have hφ : ∀ (w : X) (hw : w ∈ P), w * w ≠ 1 →
        φ ⟨w, hPC hw⟩ * φ ⟨w, hPC hw⟩ ≠ 1 := by
      intro w hw hww h1
      rw [← map_mul, MulEquiv.map_eq_one_iff] at h1
      exact hww (congrArg Subtype.val h1)
    have hu2 : u * u ≠ 1 := fun h => huv (hsq u hu h v hv)
    have hv2 : v * v ≠ 1 := fun h => huv (hsq v hv h u hu).symm
    have h1 := dihedral_comm _ _ (hφ u hu hu2) (hφ v hv hv2)
    rw [← map_mul, ← map_mul] at h1
    exact huv (congrArg Subtype.val (φ.injective h1))
  · set P' := (P.subgroupOf (centralizer ({z} : Set X))).map φ.toMonoidHom
    have h1 : Nat.card P' = 8 := by
      rw [Nat.card_congr ((P.subgroupOf _).equivMapOfInjective _ φ.injective).symm.toEquiv,
        ← h8]
      exact Nat.card_congr (subgroupOfEquivOfLe hPC).toEquiv
    have h2 : ∀ x ∈ P', x * x = 1 := by
      rintro _ ⟨w, hw, rfl⟩
      rw [← map_mul]
      have : w * w = 1 := Subtype.ext (hall w (mem_subgroupOf.mp hw))
      rw [this, map_one]
    have := card_le_four_of_dihedral P' h2
    omega

theorem map_centralizer_singleton {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (z : X) :
    (centralizer ({z} : Set X)).map e.toMonoidHom = centralizer ({e z} : Set Y) := by
  ext y
  obtain ⟨x, rfl⟩ := e.surjective y
  rw [mem_map_equiv, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff,
    MulEquiv.symm_apply_apply, ← map_mul, ← map_mul, e.injective.eq_iff]

theorem fAt_psl_two {X : Type} [Group X] {K : Type} [Field K] [Finite K] {p f : ℕ}
    [Fact p.Prime] (hK : Nat.card K = p ^ f) (hp : Odd p) (hf : 0 < f) (h5 : 5 ≤ p ^ f)
    (e : X ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) {z : X} (hz : orderOf z = 2) :
    FAt X z := by
  have ht : orderOf (e z) = 2 := by rw [MulEquiv.orderOf_eq]; exact hz
  have ψ : centralizer ({z} : Set X) ≃* centralizer ({e z} : Set _) :=
    (e.subgroupMap _).trans (MulEquiv.subgroupCongr (map_centralizer_singleton e z))
  obtain ⟨h1, h3⟩ := Walter.psl2_centralizer_involution K hK hp hf ht
  have hq : Odd (p ^ f) := hp.pow
  rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hq) with h | h
  · obtain ⟨-, ⟨φ⟩⟩ := h1 h
    have : NeZero ((p ^ f - 1) / 2) := ⟨by omega⟩
    exact fAt_of_dihedral (ψ.trans φ)
  · obtain ⟨-, ⟨φ⟩⟩ := h3 h
    have : NeZero ((p ^ f + 1) / 2) := ⟨by omega⟩
    exact fAt_of_dihedral (ψ.trans φ)

end CFSG.ComponentClassification.HarrisLit.T1.P51Q
