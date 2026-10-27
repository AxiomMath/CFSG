module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

theorem gzNo_isElemAbelian {K : Type*} [Group K] {E : Subgroup K} (hE : ∀ e ∈ E, e ^ 2 = 1) :
    CFSG.Open.IsElemAbelian 2 E := by
  have hinv : ∀ e ∈ E, e⁻¹ = e := fun e he =>
    inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hE e he)
  refine ⟨⟨⟨fun a b => ?_⟩⟩, hE⟩
  apply Subtype.ext
  have h1 := hinv ((a : K) * b) (mul_mem a.2 b.2)
  rw [mul_inv_rev, hinv a a.2, hinv b b.2] at h1
  exact h1.symm

private theorem commute_of_mul_left {K : Type*} [Group K] {z w g : K} (hz2 : z ^ 2 = 1)
    (hzw : z * w = w * z) (hg : (z * g) * w = w * (z * g)) : g * w = w * g := by
  have hzz : z * z = 1 := by rw [← sq]; exact hz2
  have hg' : g = z * (z * g) := by rw [← mul_assoc, hzz, one_mul]
  rw [hg']
  calc z * (z * g) * w = z * ((z * g) * w) := by group
    _ = z * (w * (z * g)) := by rw [hg]
    _ = (z * w) * (z * g) := by group
    _ = (w * z) * (z * g) := by rw [hzw]
    _ = w * (z * (z * g)) := by group

theorem gzNo_adjoin {K : Type*} [Group K] [Finite K] {E M : Subgroup K}
    (hE : ∀ e ∈ E, e ^ 2 = 1) (hEM : E ≤ M) {y : K} (hyM : y ∈ M) (hy2 : y ^ 2 = 1)
    (hyE : y ∉ E) (hc : ∀ e ∈ E, e * y = y * e) :
    ∃ E' : Subgroup K, E ≤ E' ∧ E' ≤ M ∧ y ∈ E' ∧ (∀ e ∈ E', e ^ 2 = 1) ∧
      2 * Nat.card E ≤ Nat.card E' ∧ ∀ g ∈ E', g ∈ E ∨ y * g ∈ E := by
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hy2)
  have hyy : y * y = 1 := by rw [← sq]; exact hy2
  have hyyg : ∀ g : K, y * (y * g) = g := fun g => by rw [← mul_assoc, hyy, one_mul]
  have hcy : ∀ g : K, y * g ∈ E → g * y = y * g := fun g hg =>
    commute_of_mul_left hy2 rfl (hc (y * g) hg)
  let E' : Subgroup K :=
    { carrier := {g | g ∈ E ∨ y * g ∈ E}
      one_mem' := Or.inl E.one_mem
      mul_mem' := by
        rintro g h (hg | hg) (hh | hh)
        · exact Or.inl (mul_mem hg hh)
        · refine Or.inr ?_
          rw [← mul_assoc, ← hc g hg, mul_assoc]
          exact mul_mem hg hh
        · refine Or.inr ?_
          rw [← mul_assoc]
          exact mul_mem hg hh
        · refine Or.inl ?_
          have h1 : g * h = (y * g) * (y * h) := by
            calc g * h = (y * y) * (g * h) := by rw [hyy, one_mul]
              _ = y * (y * g) * h := by group
              _ = y * (g * y) * h := by rw [hcy g hg]
              _ = (y * g) * (y * h) := by group
          rw [h1]
          exact mul_mem hg hh
      inv_mem' := by
        rintro g (hg | hg)
        · exact Or.inl (inv_mem hg)
        · refine Or.inr ?_
          have h1 : g⁻¹ * y = y * g⁻¹ := Commute.inv_left (hcy g hg)
          have h2 : y * g⁻¹ = (y * g)⁻¹ := by rw [mul_inv_rev, hyinv, h1]
          rw [h2]
          exact inv_mem hg }
  have memE' : ∀ g : K, g ∈ E' ↔ g ∈ E ∨ y * g ∈ E := fun g => Iff.rfl
  have hyE' : ∀ e : ↥E, y * (e : K) ∈ E' := fun e =>
    (memE' _).mpr (Or.inr (by rw [hyyg]; exact e.2))
  let F : ↥E ⊕ ↥E → ↥E' :=
    Sum.elim (fun e => ⟨e, (memE' _).mpr (Or.inl e.2)⟩) (fun e => ⟨y * e, hyE' e⟩)
  have hinj : Function.Injective F := by
    rintro (e | e) (e' | e') h <;> have h' := congrArg Subtype.val h
    · exact congrArg Sum.inl (Subtype.ext h')
    · exfalso
      apply hyE
      have h3 : y = (e : K) * (e' : K)⁻¹ := by
        change (e : K) = y * e' at h'
        rw [h', mul_inv_cancel_right]
      rw [h3]
      exact mul_mem e.2 (inv_mem e'.2)
    · exfalso
      apply hyE
      have h3 : y = (e' : K) * (e : K)⁻¹ := by
        change y * (e : K) = e' at h'
        rw [← h', mul_inv_cancel_right]
      rw [h3]
      exact mul_mem e'.2 (inv_mem e.2)
    · change y * (e : K) = y * e' at h'
      exact congrArg Sum.inr (Subtype.ext (mul_left_cancel h'))
  have hcard : Nat.card (↥E ⊕ ↥E) ≤ Nat.card ↥E' := Nat.card_le_card_of_injective F hinj
  rw [Nat.card_sum, ← two_mul] at hcard
  refine ⟨E', fun g hg => Or.inl hg, ?_, ?_, ?_, hcard, fun g hg => hg⟩
  · rintro g (hg | hg)
    · exact hEM hg
    · rw [← hyyg g]
      exact mul_mem hyM (hEM hg)
  · exact (memE' y).mpr (Or.inr (by rw [hyy]; exact E.one_mem))
  · rintro g (hg | hg)
    · exact hE g hg
    · have h1 := (Commute.mul_pow (hcy g hg).symm 2).symm.trans (hE _ hg)
      rwa [hy2, one_mul] at h1

theorem gzNo_exists_elem_sixtyfour {K : Type*} [Group K] [Finite K] {M N T : Subgroup K}
    (hT : ∀ t ∈ T, t ^ 2 = 1) (hT8 : 8 ≤ Nat.card T) (hTM : T ≤ M) (hTN : T ≤ N)
    {z x y : K} (hzM : z ∈ M) (hxM : x ∈ M) (hyM : y ∈ M) (hz2 : z ^ 2 = 1) (hx2 : x ^ 2 = 1)
    (hy2 : y ^ 2 = 1) (hzN : z ∈ N) (hzT : z ∉ T) (hxN : x ∉ N) (hyN : y ∉ N)
    (hxyN : x * y ∉ N) (hzx : z * x = x * z) (hzy : z * y = y * z) (hxy : x * y = y * x)
    (hTz : ∀ t ∈ T, t * z = z * t) (hTx : ∀ t ∈ T, t * x = x * t)
    (hTy : ∀ t ∈ T, t * y = y * t) :
    ∃ E : Subgroup K, E ≤ M ∧ CFSG.Open.IsElemAbelian 2 E ∧ 2 ^ 6 ≤ Nat.card E := by
  obtain ⟨E₁, -, hE₁MN, -, hE₁2, hE₁c, hE₁⟩ :=
    gzNo_adjoin hT (le_inf hTM hTN) (Subgroup.mem_inf.mpr ⟨hzM, hzN⟩) hz2 hzT hTz
  have hE₁M : E₁ ≤ M := hE₁MN.trans inf_le_left
  have hE₁N : E₁ ≤ N := hE₁MN.trans inf_le_right
  have hcomm₁ : ∀ w : K, (∀ t ∈ T, t * w = w * t) → z * w = w * z →
      ∀ g ∈ E₁, g * w = w * g := by
    intro w hTw hzw g hg
    rcases hE₁ g hg with hgT | hgT
    · exact hTw g hgT
    · exact commute_of_mul_left hz2 hzw (hTw _ hgT)
  obtain ⟨E₂, -, hE₂M, -, hE₂2, hE₂c, hE₂⟩ :=
    gzNo_adjoin hE₁2 hE₁M hxM hx2 (fun h => hxN (hE₁N h)) (hcomm₁ x hTx hzx)
  have hyE₂ : y ∉ E₂ := by
    intro h
    rcases hE₂ y h with h1 | h1
    · exact hyN (hE₁N h1)
    · exact hxyN (hE₁N h1)
  have hE₂y : ∀ g ∈ E₂, g * y = y * g := by
    intro g hg
    rcases hE₂ g hg with h1 | h1
    · exact hcomm₁ y hTy hzy g h1
    · exact commute_of_mul_left hx2 hxy (hcomm₁ y hTy hzy _ h1)
  obtain ⟨E₃, -, hE₃M, -, hE₃2, hE₃c, -⟩ := gzNo_adjoin hE₂2 hE₂M hyM hy2 hyE₂ hE₂y
  refine ⟨E₃, hE₃M, gzNo_isElemAbelian hE₃2, ?_⟩
  have h64 : (2 : ℕ) ^ 6 = 64 := by norm_num
  rw [h64]
  omega

end CFSG.EvenSporadicStandard.HNRecog.Section3
