module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open CFSG.Open

theorem sec44_comm {S : Type} [Group S] {H : Subgroup S} (hH : IsElemAbelian 2 H) {x y : S}
    (hx : x ∈ H) (hy : y ∈ H) : x * y = y * x :=
  congrArg Subtype.val (hH.1.is_comm.comm (⟨x, hx⟩ : ↥H) ⟨y, hy⟩)

theorem sec44_relIndex_two {S : Type} [Group S] [Finite S] {K H : Subgroup S} (hKH : K ≤ H)
    (h : Nat.card H = 2 * Nat.card K) : K.relIndex H = 2 := by
  have h1 := Subgroup.relIndex_mul_card (H := K) (K := H)
  rw [inf_eq_left.mpr hKH, h] at h1
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1

theorem sec44_inv_mul_mem {S : Type} [Group S] {K H : Subgroup S} (h2 : K.relIndex H = 2)
    {g x : S} (hg : g ∈ H) (hgK : g ∉ K) (hx : x ∈ H) (hxK : x ∉ K) : g⁻¹ * x ∈ K := by
  obtain ⟨a, -, ha⟩ := Subgroup.relIndex_eq_two_iff'.mp h2
  have hag : a * g ∈ K := (xor_iff_iff_not.mp (ha g hg)).mpr hgK
  have hax : a * x ∈ K := (xor_iff_iff_not.mp (ha x hx)).mpr hxK
  have h3 : g⁻¹ * x = (a * g)⁻¹ * (a * x) := by group
  rw [h3]
  exact mul_mem (inv_mem hag) hax

theorem sec44_central {S : Type} [Group S] {A E : Subgroup S} (hA : IsElemAbelian 2 A)
    (hE : IsElemAbelian 2 E) {z : S} (hz : z ∈ A ⊓ E) {g : S} (hg : g ∈ A ⊔ E) :
    z * g = g * z := by
  have hsupC : A ⊔ E ≤ Subgroup.centralizer ((A ⊓ E : Subgroup S) : Set S) := by
    refine sup_le ?_ ?_
    · intro g' hg'
      rw [Subgroup.mem_centralizer_iff]
      intro z' hz'
      exact sec44_comm hA (Subgroup.mem_inf.mp hz').1 hg'
    · intro g' hg'
      rw [Subgroup.mem_centralizer_iff]
      intro z' hz'
      exact sec44_comm hE (Subgroup.mem_inf.mp hz').2 hg'
  exact Subgroup.mem_centralizer_iff.mp (hsupC hg) z hz

theorem sec44_ae_ne {S : Type} [Group S] {A E : Subgroup S}
    (hE : IsElemAbelian 2 E) (hCA : Subgroup.centralizer (A : Set S) ≤ A) {a e : S}
    (hdecA : ∀ x ∈ A, x ∈ A ⊓ E ∨ ∃ z ∈ A ⊓ E, x = a * z) (heE : e ∈ E) (heA : e ∉ A) :
    a * e ≠ e * a := by
  intro hcomm
  apply heA
  apply hCA
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  rcases hdecA h hh with hz | ⟨z, hz, rfl⟩
  · exact sec44_comm hE (Subgroup.mem_inf.mp hz).2 heE
  · have hze : z * e = e * z := sec44_comm hE (Subgroup.mem_inf.mp hz).2 heE
    calc a * z * e = a * (z * e) := mul_assoc a z e
      _ = a * (e * z) := by rw [hze]
      _ = a * e * z := (mul_assoc a e z).symm
      _ = e * a * z := by rw [hcomm]
      _ = e * (a * z) := mul_assoc e a z

theorem sec44_sq_ne {S : Type} [Group S] {A E : Subgroup S} (hA : IsElemAbelian 2 A) {a e : S}
    (hae : a * e ≠ e * a) (ha2 : a * a = 1) (he2 : e * e = 1) {z : S} (hz : z ∈ A ⊓ E)
    (hza : z * a = a * z) (hze : z * e = e * z) :
    e * (a * z) * (e * (a * z)) ≠ 1 := by
  intro h
  have hzz : z * z = 1 := by
    rw [← pow_two]
    exact hA.2 z (Subgroup.mem_inf.mp hz).1
  have hzx : z * (e * a) = e * a * z := by
    rw [← mul_assoc, hze, mul_assoc, hza, ← mul_assoc]
  have h1 : e * a * z * (e * a * z) = e * a * (e * a) * (z * z) := by
    calc e * a * z * (e * a * z) = e * a * (z * (e * a)) * z := by simp only [mul_assoc]
      _ = e * a * (e * a * z) * z := by rw [hzx]
      _ = e * a * (e * a) * (z * z) := by simp only [mul_assoc]
  have h2 : e * a * z * (e * a * z) = 1 := by
    rw [mul_assoc e a z]
    exact h
  rw [h1, hzz, mul_one] at h2
  have hi : (e * a)⁻¹ = e * a := inv_eq_of_mul_eq_one_right h2
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have hei : e⁻¹ = e := inv_eq_of_mul_eq_one_right he2
  have h4 : e * a = a * e := by
    rw [← hi, mul_inv_rev, hai, hei]
  exact hae h4.symm

theorem sec44_cross {S : Type} [Group S] {A E : Subgroup S} (hA : IsElemAbelian 2 A) {a e : S}
    (hae : a * e ≠ e * a) (hzE : ∀ z ∈ A ⊓ E, z * e = e * z)
    (hza : ∀ z ∈ A ⊓ E, z * a = a * z) {z₁ z₂ : S} (hz₁ : z₁ ∈ A ⊓ E) (hz₂ : z₂ ∈ A ⊓ E)
    (hcomm : a * z₁ * (e * z₂) = e * z₂ * (a * z₁)) : False := by
  have hz12 : z₁ * z₂ = z₂ * z₁ :=
    sec44_comm hA (Subgroup.mem_inf.mp hz₁).1 (Subgroup.mem_inf.mp hz₂).1
  have L : a * z₁ * (e * z₂) = a * e * (z₁ * z₂) := by
    rw [mul_assoc a z₁, ← mul_assoc z₁ e z₂, hzE z₁ hz₁, mul_assoc e z₁ z₂,
      ← mul_assoc a e (z₁ * z₂)]
  have R : e * z₂ * (a * z₁) = e * a * (z₁ * z₂) := by
    rw [mul_assoc e z₂ (a * z₁), ← mul_assoc z₂ a z₁, hza z₂ hz₂, mul_assoc a z₂ z₁,
      ← mul_assoc e a (z₂ * z₁), hz12]
  have key : a * e * (z₁ * z₂) = e * a * (z₁ * z₂) := by
    rw [← L, hcomm, R]
  exact hae (mul_right_cancel key)

theorem sub_E8_of_AE {S : Type} [Group S] [Finite S] {A E : Subgroup S}
    (hA : IsElemAbelian 2 A) (hA8 : Nat.card A = 8)
    (hE : IsElemAbelian 2 E) (hE8 : Nat.card E = 8) (hEn : E.Normal)
    (hAE4 : Nat.card (A ⊓ E : Subgroup S) = 4)
    (hCA : Subgroup.centralizer (A : Set S) ≤ A) :
    (E ≤ Subgroup.normalizer (A : Set S)) ∧ Nat.card (A ⊔ E : Subgroup S) = 16 ∧
      ∀ B : Subgroup S, B ≤ A ⊔ E → IsElemAbelian 2 B → Nat.card B = 8 → B = A ∨ B = E := by
  have hEA : E.relIndex A = 2 := by
    have h1 := Subgroup.relIndex_mul_card (H := E) (K := A)
    rw [inf_comm E A, hAE4, hA8] at h1
    omega
  have hG : Nat.card (A ⊔ E : Subgroup S) = 16 := by
    have hrel : E.relIndex (A ⊔ E) = E.relIndex A := Subgroup.relIndex_sup_right A E
    have hEG : E ⊓ (A ⊔ E) = E := inf_eq_left.mpr le_sup_right
    have h2 := Subgroup.relIndex_mul_card (H := E) (K := A ⊔ E)
    rw [hEG, hrel, hEA, hE8] at h2
    omega
  have hAG : A.relIndex (A ⊔ E) = 2 := sec44_relIndex_two le_sup_left (by omega)
  have hZA : (A ⊓ E).relIndex A = 2 := sec44_relIndex_two inf_le_left (by omega)
  have hZE : (A ⊓ E).relIndex E = 2 := sec44_relIndex_two inf_le_right (by omega)
  obtain ⟨a, haA, haE⟩ : ∃ a ∈ A, a ∉ E := by
    by_contra h
    push Not at h
    have hle : A ≤ A ⊓ E := fun x hx => Subgroup.mem_inf.mpr ⟨hx, h x hx⟩
    have := Subgroup.card_le_of_le hle
    omega
  obtain ⟨e, heE, heA⟩ : ∃ e ∈ E, e ∉ A := by
    by_contra h
    push Not at h
    have hle : E ≤ A ⊓ E := fun x hx => Subgroup.mem_inf.mpr ⟨h x hx, hx⟩
    have := Subgroup.card_le_of_le hle
    omega
  have haG : a ∈ A ⊔ E := Subgroup.mem_sup_left haA
  have heG : e ∈ A ⊔ E := Subgroup.mem_sup_right heE
  have ha2 : a * a = 1 := by
    rw [← pow_two]
    exact hA.2 a haA
  have he2 : e * e = 1 := by
    rw [← pow_two]
    exact hE.2 e heE
  have hdecA : ∀ x ∈ A, x ∈ A ⊓ E ∨ ∃ z ∈ A ⊓ E, x = a * z := by
    intro x hx
    by_cases hxZ : x ∈ A ⊓ E
    · exact Or.inl hxZ
    · exact Or.inr ⟨a⁻¹ * x, sec44_inv_mul_mem hZA haA
        (fun h => haE (Subgroup.mem_inf.mp h).2) hx hxZ, (mul_inv_cancel_left a x).symm⟩
  have hdecG : ∀ x ∈ A ⊔ E, x ∈ A ∨ ∃ α ∈ A, x = e * α := by
    intro x hx
    by_cases hxA : x ∈ A
    · exact Or.inl hxA
    · exact Or.inr ⟨e⁻¹ * x, sec44_inv_mul_mem hAG heG heA hx hxA,
        (mul_inv_cancel_left e x).symm⟩
  have hdecG' : ∀ x ∈ A ⊔ E, x ∈ A ⊓ E ∨ (∃ z ∈ A ⊓ E, x = a * z) ∨
      (∃ z ∈ A ⊓ E, x = e * z) ∨ (∃ z ∈ A ⊓ E, x = e * (a * z)) := by
    intro x hx
    rcases hdecG x hx with hxA | ⟨α, hα, rfl⟩
    · rcases hdecA x hxA with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · rcases hdecA α hα with h | ⟨z, hz, rfl⟩
      · exact Or.inr (Or.inr (Or.inl ⟨α, h, rfl⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨z, hz, rfl⟩))
  have hzE : ∀ z ∈ A ⊓ E, z * e = e * z := fun z hz => sec44_central hA hE hz heG
  have hza : ∀ z ∈ A ⊓ E, z * a = a * z := fun z hz => sec44_central hA hE hz haG
  have hae : a * e ≠ e * a := sec44_ae_ne hE hCA hdecA heE heA
  have hsq : ∀ z ∈ A ⊓ E, e * (a * z) * (e * (a * z)) ≠ 1 := fun z hz =>
    sec44_sq_ne hA hae ha2 he2 hz (hza z hz) (hzE z hz)
  have hconj : ∀ g ∈ A ⊔ E, ∀ h ∈ A, g * h * g⁻¹ ∈ A := by
    intro g hg h hh
    by_cases hgA : g ∈ A
    · exact mul_mem (mul_mem hgA hh) (inv_mem hgA)
    · by_contra hxA
      have hx : g * h * g⁻¹ ∈ A ⊔ E :=
        mul_mem (mul_mem hg (Subgroup.mem_sup_left hh)) (inv_mem hg)
      have h3 := sec44_inv_mul_mem hAG hg hgA hx hxA
      have h4 : g⁻¹ * (g * h * g⁻¹) = h * g⁻¹ := by group
      rw [h4] at h3
      have h5 : g⁻¹ ∈ A := by
        have h6 := mul_mem (inv_mem hh) h3
        rwa [inv_mul_cancel_left] at h6
      exact hgA (by simpa using h5)
  have hEN : E ≤ Subgroup.normalizer (A : Set S) := by
    intro g hg
    have hgG : g ∈ A ⊔ E := Subgroup.mem_sup_right hg
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      exact hconj g hgG h hh
    · intro hh
      have h6 := hconj g⁻¹ (inv_mem hgG) (g * h * g⁻¹) hh
      have h7 : g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h := by group
      rwa [h7] at h6
  refine ⟨hEN, hG, ?_⟩
  intro B hBG hB hB8
  have hBcases : ∀ x ∈ B, x ∈ A ⊓ E ∨ (∃ z ∈ A ⊓ E, x = a * z) ∨ (∃ z ∈ A ⊓ E, x = e * z) := by
    intro x hx
    rcases hdecG' x (hBG hx) with h | h | h | ⟨z, hz, rfl⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · exact (hsq z hz (by rw [← pow_two]; exact hB.2 _ hx)).elim
  have hdisj : (∀ x ∈ B, ¬ ∃ z ∈ A ⊓ E, x = a * z) ∨
      (∀ x ∈ B, ¬ ∃ z ∈ A ⊓ E, x = e * z) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨⟨x, hxB, z₁, hz₁, rfl⟩, ⟨y, hyB, z₂, hz₂, rfl⟩⟩ := hcon
    exact sec44_cross hA hae hzE hza hz₁ hz₂ (sec44_comm hB hxB hyB)
  rcases hdisj with h1 | h2
  · right
    have hBE : B ≤ E := by
      intro x hx
      rcases hBcases x hx with h | ⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩
      · exact (Subgroup.mem_inf.mp h).2
      · exact (h1 _ hx ⟨z, hz, rfl⟩).elim
      · exact mul_mem heE (Subgroup.mem_inf.mp hz).2
    exact Subgroup.eq_of_le_of_card_ge hBE (by omega)
  · left
    have hBA : B ≤ A := by
      intro x hx
      rcases hBcases x hx with h | ⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩
      · exact (Subgroup.mem_inf.mp h).1
      · exact mul_mem haA (Subgroup.mem_inf.mp hz).1
      · exact (h2 _ hx ⟨z, hz, rfl⟩).elim
    exact Subgroup.eq_of_le_of_card_ge hBA (by omega)

end CFSG.EvenSporadicStandard.Fin76b
