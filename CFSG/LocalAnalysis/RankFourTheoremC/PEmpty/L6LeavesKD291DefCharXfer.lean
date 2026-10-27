module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291Level
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291R3ExRank

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291DC

open Subgroup CFSG.Open

theorem eq_of_dvd_add_sub {p i i' : ℕ} (hi : i < p) (hi' : i' < p) (h : p ∣ i + (p - i')) :
    i = i' := by
  rcases le_or_gt i' i with hle | hlt
  · have h1 : i + (p - i') = p + (i - i') := by omega
    rw [h1] at h
    have h2 : p ∣ i - i' := (Nat.dvd_add_right (dvd_refl p)).mp h
    have h3 : i - i' < p := by omega
    have := Nat.eq_zero_of_dvd_of_lt h2 h3
    omega
  · have h1 : 0 < i + (p - i') := by omega
    have h2 : i + (p - i') < p := by omega
    exact absurd (Nat.le_of_dvd h1 h) (by omega)

theorem card_mul_le_of_independent {p : ℕ} [hp : Fact p.Prime] {G : Type} [Group G] [Finite G]
    {A B : Subgroup G} (hA : IsElemAbelian p A) (hBA : B ≤ A) {a₁ a₂ : G} (h₁ : a₁ ∈ A)
    (h₂ : a₂ ∈ A) (hind : ∀ i j : ℕ, a₁ ^ i * a₂ ^ j ∈ B → p ∣ i ∧ p ∣ j) :
    Nat.card B * p ^ 2 ≤ Nat.card A := by
  classical
  have hp1 := hp.out.one_lt
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    intro a ha b hb
    have := hA.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
    simpa using congrArg Subtype.val this
  letI : CommGroup A :=
    { (inferInstance : Group A) with mul_comm := fun a b => Subtype.ext (hAc _ a.2 _ b.2) }
  let x : A := ⟨a₁, h₁⟩
  let y : A := ⟨a₂, h₂⟩
  have hx : x ^ p = 1 := Subtype.ext (by simpa [x] using hA.2 a₁ h₁)
  have hy : y ^ p = 1 := Subtype.ext (by simpa [y] using hA.2 a₂ h₂)
  let β : B → A := fun b => ⟨b, hBA b.2⟩
  let f : Fin p × Fin p × B → A := fun t => x ^ (t.1 : ℕ) * y ^ (t.2.1 : ℕ) * β t.2.2
  have hxy : ∀ i j : ℕ, x ^ i * y ^ j = (⟨a₁ ^ i * a₂ ^ j, mul_mem (pow_mem h₁ _)
      (pow_mem h₂ _)⟩ : A) := fun i j => rfl
  have hinj : Function.Injective f := by
    rintro ⟨i, j, b⟩ ⟨i', j', b'⟩ h
    have h' : x ^ (i : ℕ) * y ^ (j : ℕ) * β b = x ^ (i' : ℕ) * y ^ (j' : ℕ) * β b' := h
    have key : x ^ ((i : ℕ) + (p - i')) * y ^ ((j : ℕ) + (p - j')) = β b' * (β b)⁻¹ := by
      have hp1' : x ^ (i' : ℕ) * x ^ (p - (i' : ℕ)) = 1 := by
        rw [← pow_add, Nat.add_sub_cancel' (by omega : (i' : ℕ) ≤ p), hx]
      have hp2' : y ^ (j' : ℕ) * y ^ (p - (j' : ℕ)) = 1 := by
        rw [← pow_add, Nat.add_sub_cancel' (by omega : (j' : ℕ) ≤ p), hy]
      have e1 : x ^ (i : ℕ) * y ^ (j : ℕ) * β b * (x ^ (p - (i' : ℕ)) * y ^ (p - (j' : ℕ))) =
          x ^ (i' : ℕ) * y ^ (j' : ℕ) * β b' * (x ^ (p - (i' : ℕ)) * y ^ (p - (j' : ℕ))) := by
        rw [h']
      have e2 : x ^ (i' : ℕ) * y ^ (j' : ℕ) * β b' * (x ^ (p - (i' : ℕ)) * y ^ (p - (j' : ℕ))) =
          β b' := by
        calc _ = (x ^ (i' : ℕ) * x ^ (p - (i' : ℕ))) * (y ^ (j' : ℕ) * y ^ (p - (j' : ℕ))) *
              β b' := by
              simp only [mul_comm, mul_left_comm, mul_assoc]
          _ = β b' := by rw [hp1', hp2', one_mul, one_mul]
      have e3 : x ^ (i : ℕ) * y ^ (j : ℕ) * β b * (x ^ (p - (i' : ℕ)) * y ^ (p - (j' : ℕ))) =
          x ^ ((i : ℕ) + (p - i')) * y ^ ((j : ℕ) + (p - j')) * β b := by
        rw [pow_add, pow_add]
        simp only [mul_comm, mul_left_comm, mul_assoc]
      rw [e2, e3] at e1
      exact (eq_mul_inv_iff_mul_eq.mpr e1)
    have hmem : a₁ ^ ((i : ℕ) + (p - i')) * a₂ ^ ((j : ℕ) + (p - j')) ∈ B := by
      have := congrArg Subtype.val key
      have e4 : ((x ^ ((i : ℕ) + (p - i')) * y ^ ((j : ℕ) + (p - j')) : A) : G) =
          a₁ ^ ((i : ℕ) + (p - i')) * a₂ ^ ((j : ℕ) + (p - j')) := rfl
      rw [e4] at this
      rw [this]
      exact mul_mem b'.2 (inv_mem b.2)
    obtain ⟨hi, hj⟩ := hind _ _ hmem
    have hii : (i : ℕ) = i' := eq_of_dvd_add_sub i.2 i'.2 hi
    have hjj : (j : ℕ) = j' := eq_of_dvd_add_sub j.2 j'.2 hj
    have hi' : i = i' := Fin.ext hii
    have hj' : j = j' := Fin.ext hjj
    subst hi' hj'
    have : β b = β b' := mul_left_cancel (a := x ^ (i : ℕ) * y ^ (j : ℕ)) h'
    have hbb : b = b' := Subtype.ext (by simpa [β] using congrArg Subtype.val this)
    rw [hbb]
  have h := Nat.card_le_card_of_injective f hinj
  simp only [Nat.card_prod, Nat.card_fin] at h
  nlinarith [h]


@[expose] def RankThreeCent (p : ℕ) (G : Type) [Group G] [Finite G] : Prop :=
  ∀ y : G, orderOf y = p → 3 ≤ pRank p (centralizer ({y} : Set G))

theorem rankThreeCent_of_witness_map {p : ℕ} [hp : Fact p.Prime] {G S : Type} [Group G] [Finite G]
    [Group S] [Finite S] (π : G →* S) (hπ : Function.Surjective π) {U A B : Subgroup G}
    (hU : IsPGroup p U) (hidx : ¬ p ∣ U.index) (hAU : A ≤ U) (hBA : B ≤ A)
    (hA : IsElemAbelian p A) (hcomm : ∀ u ∈ U, ∀ a ∈ A, u * a * u⁻¹ * a⁻¹ ∈ B)
    (hcard : Nat.card B * p ^ 2 ≤ Nat.card A)
    (hbig : p ^ 3 ≤ Nat.card A ∨
      ((∀ u ∈ U, ∀ a ∈ A, u * a = a * u) ∧ 3 ≤ pRank p (⊤ : Subgroup S)))
    (hinj : ∀ u ∈ U, π u = 1 → u = 1) : RankThreeCent p S := by
  intro y hy
  set P : Sylow p S := (hU.toSylow hidx).mapSurjective hπ with hP
  have hPc : (P : Subgroup S) = U.map π := by
    rw [hP, Sylow.coe_mapSurjective, IsPGroup.toSylow_coe]
  have hcA : Nat.card (A.map π) = Nat.card A :=
    card_map_eq_of_injOn_subgroup π (fun u hu => hinj u (hAU hu))
  have hcB : Nat.card (B.map π) = Nat.card B :=
    card_map_eq_of_injOn_subgroup π (fun u hu => hinj u (hAU (hBA hu)))
  refine KD291Lvl.three_le_pRank_of_witness P (A := A.map π) (B := B.map π) ?_
    (CFSG.SectionRank.isElemAbelian_map hA π) (Subgroup.map_mono hBA) ?_ ?_ ?_ hy
  · rw [hPc]
    exact Subgroup.map_mono hAU
  · rw [hPc]
    rintro _ ⟨u, hu, rfl⟩ _ ⟨a, ha, rfl⟩
    exact ⟨u * a * u⁻¹ * a⁻¹, hcomm u hu a ha, by simp⟩
  · rw [hcA, hcB]
    exact hcard
  · rcases hbig with h | ⟨hc, h3⟩
    · exact Or.inl (by rwa [hcA])
    · refine Or.inr ⟨?_, h3⟩
      rw [hPc]
      rintro _ ⟨u, hu, rfl⟩ _ ⟨a, ha, rfl⟩
      rw [← map_mul, ← map_mul, hc u hu a ha]

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291DC
