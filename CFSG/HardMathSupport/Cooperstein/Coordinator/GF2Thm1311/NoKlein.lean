module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311.Reduction

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311

open CFSG.RankThree.PartOne.OutStructure

@[expose] def NoKlein (Y : Type) [Group Y] : Prop :=
  ∀ B : Subgroup (MulAut Y), (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) → (∀ a ∈ B, a * a = 1) →
    Nat.card B = 4 → B ⊓ Inn Y ≠ ⊥

theorem KleinBigInv.of_noKlein {Y : Type} [Group Y] (h : NoKlein Y) : KleinBigInv Y :=
  fun B hc hs hcard hinn => absurd hinn (h B hc hs hcard)

theorem NoKlein.of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (h : NoKlein X) :
    NoKlein Y := by
  intro B hcomm hsq hcard hinn
  set φ : MulAut Y ≃* MulAut X := MulAut.congr e.symm with hφ
  refine h (B.map φ.toMonoidHom)
    (by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨c, hc, rfl⟩
      rw [← map_mul, ← map_mul, hcomm a ha c hc])
    (by
      rintro _ ⟨a, ha, rfl⟩
      rw [← map_mul, hsq a ha, map_one])
    (by rw [Subgroup.card_map_of_injective φ.injective]; exact hcard) ?_
  refine eq_bot_iff.mpr ?_
  rintro _ ⟨⟨b, hb, rfl⟩, ⟨u, hu⟩⟩
  have hbI : b ∈ Inn Y := by
    refine ⟨e u, ?_⟩
    apply φ.injective
    have hu' : MulAut.conj u = φ b := hu
    rw [← hu']
    ext x
    simp [hφ, MulAut.congr_apply, MulAut.conj_apply]
  have : b = 1 := by
    have hb1 : b ∈ B ⊓ Inn Y := ⟨hb, hbI⟩
    rw [hinn] at hb1
    simpa using hb1
  rw [this]
  simp

theorem exists_two_ne_one_of_card_eq_four {G : Type*} [Group G] (h : Nat.card G = 4) :
    ∃ u v : G, u ≠ 1 ∧ v ≠ 1 ∧ u ≠ v := by
  have : Finite G := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype G := Fintype.ofFinite G
  rw [Nat.card_eq_fintype_card] at h
  classical
  by_contra hcon
  push Not at hcon
  have h1 : ∃ u : G, u ≠ 1 := by
    by_contra h1
    push Not at h1
    have : Fintype.card G ≤ 1 := Fintype.card_le_one_iff.mpr fun a b => (h1 a).trans (h1 b).symm
    omega
  obtain ⟨u, hu⟩ := h1
  have hsub : (Finset.univ : Finset G) ⊆ {1, u} := by
    intro x _
    by_cases hx : x = 1
    · simp [hx]
    · have := hcon u x hu hx
      simp [this]
  have := Finset.card_le_card hsub
  rw [Finset.card_univ] at this
  have h2 : ({1, u} : Finset G).card ≤ 2 := Finset.card_le_two
  omega

theorem noKlein_of_outPNice_two {Y : Type} [Group Y] (h : OutPNice 2 Y) : NoKlein Y := by
  intro B hcomm hsq hcard hB
  obtain ⟨D, E, -, hD2, hpE, -, hcmp⟩ := h
  obtain ⟨u', v', hu', hv', huv'⟩ := exists_two_ne_one_of_card_eq_four hcard
  have hD0 : ∀ w ∈ B, w * w = 1 → w ∈ D → w = 1 := by
    intro w hwB hw hwD
    have : w ∈ Inn Y := by
      refine hD2 w hwD 1 ?_
      rw [pow_one, pow_two, hw]
      exact Subgroup.one_mem _
    have h1 : w ∈ B ⊓ Inn Y := ⟨hwB, this⟩
    rw [hB] at h1
    simpa using h1
  have hE : ∀ w ∈ B, w ∈ E := by
    intro w hw
    refine hpE w ⟨1, ?_⟩
    rw [pow_one, pow_two, hsq w hw]
    exact D.one_mem
  have hzpow : ∀ (w : MulAut Y), w * w = 1 → ∀ m : ℤ, w ^ m = 1 ∨ w ^ m = w := by
    intro w hw m
    have hw2 : w ^ 2 = 1 := by rw [pow_two]; exact hw
    obtain ⟨q, hq | hq⟩ := Int.even_or_odd' m
    · left; rw [hq, zpow_mul]; simp [hw2]
    · right; rw [hq, zpow_add, zpow_mul]; simp [hw2]
  have key : ∀ a ∈ B, ∀ b ∈ B, a ≠ 1 → b ≠ 1 → a ≠ b → (∃ m : ℤ, a * b ^ m ∈ D) → False := by
    intro a ha b hb ha1 hb1 hab ⟨m, hm⟩
    rcases hzpow b (hsq b hb) m with h1 | h1
    · rw [h1, mul_one] at hm
      exact ha1 (hD0 a ha (hsq a ha) hm)
    · rw [h1] at hm
      have hab1 : a * b = 1 := by
        refine hD0 _ (B.mul_mem ha hb) ?_ hm
        calc a * b * (a * b) = a * (b * a) * b := by group
          _ = a * (a * b) * b := by rw [hcomm b hb a ha]
          _ = (a * a) * (b * b) := by group
          _ = 1 := by rw [hsq a ha, hsq b hb, one_mul]
      apply hab
      have : a = b⁻¹ := eq_inv_of_mul_eq_one_left hab1
      rw [this]
      exact (inv_eq_of_mul_eq_one_right (hsq b hb)).symm ▸ rfl
  have hu1 : (u' : MulAut Y) ≠ 1 := fun h => hu' (Subtype.ext h)
  have hv1 : (v' : MulAut Y) ≠ 1 := fun h => hv' (Subtype.ext h)
  have huv : (u' : MulAut Y) ≠ v' := fun h => huv' (Subtype.ext h)
  have hD1 : ∀ w ∈ B, ∃ k : ℕ, w ^ (2 ^ k) ∈ D := fun w hw =>
    ⟨1, by rw [pow_one, pow_two, hsq w hw]; exact D.one_mem⟩
  rcases hcmp u' (hE u' u'.2) v' (hE v' v'.2) (hD1 u' u'.2) (hD1 v' v'.2) with h1 | h1
  · exact key u' u'.2 v' v'.2 hu1 hv1 huv h1
  · exact key v' v'.2 u' u'.2 hv1 hu1 huv.symm h1

theorem noKlein_of_index_le_two {Y : Type} [Group Y] [Finite Y] (h : (Inn Y).index ≤ 2) : NoKlein Y := by
  intro B hcomm hsq hcard hB
  have : (Inn Y).Normal := CFSG.ComponentClassification.OuterAutomorphisms.inner_normal Y
  have hinj : Function.Injective (fun b : B => (QuotientGroup.mk (b : MulAut Y) : MulAut Y ⧸ Inn Y)) := by
    intro a b hab
    have h1 : (a : MulAut Y)⁻¹ * b ∈ Inn Y := QuotientGroup.eq.mp hab
    have h2 : (a : MulAut Y)⁻¹ * b ∈ B ⊓ Inn Y := ⟨B.mul_mem (B.inv_mem a.2) b.2, h1⟩
    rw [hB] at h2
    have : (a : MulAut Y)⁻¹ * b = 1 := by simpa using h2
    exact Subtype.ext (inv_mul_eq_one.mp this)
  have h3 := Nat.card_le_card_of_injective _ hinj
  have h4 : Nat.card (MulAut Y ⧸ Inn Y) = (Inn Y).index := (Subgroup.index_eq_card _).symm
  have : Finite (MulAut Y) := inferInstance
  have : Finite (MulAut Y ⧸ Inn Y) := inferInstance
  omega

theorem exists_mem_inf_of_index_le_two {Γ : Type*} [Group Γ] [Finite Γ] (B E : Subgroup Γ)
    (hE : E.index ≤ 2) (hB : 2 < Nat.card B) : ∃ b ∈ B ⊓ E, b ≠ 1 := by
  have : Finite (Γ ⧸ E) := inferInstance
  have hc : Nat.card (Γ ⧸ E) ≤ 2 := by rw [← Subgroup.index_eq_card]; exact hE
  have : Fintype B := Fintype.ofFinite B
  have : Fintype (Γ ⧸ E) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card] at hc hB
  obtain ⟨a, b, hab, h⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun b : B => (QuotientGroup.mk (b : Γ) : Γ ⧸ E)) (by omega)
  have h1 : (a : Γ)⁻¹ * b ∈ E := QuotientGroup.eq.mp h
  refine ⟨(a : Γ)⁻¹ * b, ⟨B.mul_mem (B.inv_mem a.2) b.2, h1⟩, ?_⟩
  intro h0
  exact hab (Subtype.ext (inv_mul_eq_one.mp h0))


end CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311
