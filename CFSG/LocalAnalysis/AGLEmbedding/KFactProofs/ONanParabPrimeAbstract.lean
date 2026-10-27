module

public import Mathlib.GroupTheory.Index
public import Mathlib.Data.Nat.Prime.Defs

public section

namespace CFSG.AGLEmbedding.ParabPrime

open scoped commutatorElement

variable {G : Type*} [Group G]

def perfectJoin (J : Subgroup G) : Subgroup G :=
  sSup {U : Subgroup G | U ≤ J ∧ ⁅U, U⁆ = U}

theorem le_perfectJoin {J U : Subgroup G} (hUJ : U ≤ J) (hU : ⁅U, U⁆ = U) : U ≤ perfectJoin J :=
  le_sSup ⟨hUJ, hU⟩

theorem perfectJoin_le (J : Subgroup G) : perfectJoin J ≤ J :=
  sSup_le fun _ h => h.1

theorem commutator_self_le (Z : Subgroup G) : ⁅Z, Z⁆ ≤ Z :=
  Subgroup.commutator_le.2 fun _ h₁ _ h₂ =>
    Z.mul_mem (Z.mul_mem (Z.mul_mem h₁ h₂) (Z.inv_mem h₁)) (Z.inv_mem h₂)

theorem perfectJoin_perfect (J : Subgroup G) :
    ⁅perfectJoin J, perfectJoin J⁆ = perfectJoin J := by
  refine le_antisymm (commutator_self_le _) (sSup_le fun U hU => ?_)
  calc U = ⁅U, U⁆ := hU.2.symm
    _ ≤ ⁅perfectJoin J, perfectJoin J⁆ :=
      Subgroup.commutator_mono (le_perfectJoin hU.1 hU.2) (le_perfectJoin hU.1 hU.2)

theorem conj_mem_perfectJoin {J : Subgroup G} {g : G} (hg : g ∈ J) {x : G}
    (hx : x ∈ perfectJoin J) : g * x * g⁻¹ ∈ perfectJoin J := by
  have h : (perfectJoin J).map (MulAut.conj g).toMonoidHom ≤ perfectJoin J := by
    rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun U hU => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    refine le_perfectJoin ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      exact J.mul_mem (J.mul_mem hg (hU.1 hy)) (J.inv_mem hg)
    · rw [← Subgroup.map_commutator, hU.2]
  exact h ⟨x, hx, rfl⟩

theorem le_normalizer_perfectJoin (J : Subgroup G) :
    J ≤ Subgroup.normalizer (perfectJoin J : Set G) := by
  intro g hg
  rw [Subgroup.mem_set_normalizer_iff]
  intro h
  refine ⟨fun hh => conj_mem_perfectJoin hg hh, fun hh => ?_⟩
  simpa [mul_assoc] using conj_mem_perfectJoin (J.inv_mem hg) hh

theorem commutatorElement_mul_central {a b z₁ z₂ : G} (h₁ : z₁ ∈ Subgroup.center G)
    (h₂ : z₂ ∈ Subgroup.center G) : ⁅a * z₁, b * z₂⁆ = ⁅a, b⁆ := by
  have c1 := Subgroup.mem_center_iff.1 h₁
  have c2 := Subgroup.mem_center_iff.1 h₂
  simp only [commutatorElement_def, mul_inv_rev, mul_assoc]
  congr 1
  calc z₁ * (b * (z₂ * (z₁⁻¹ * (a⁻¹ * (z₂⁻¹ * b⁻¹)))))
      = b * (z₁ * (z₂ * (z₁⁻¹ * (a⁻¹ * (z₂⁻¹ * b⁻¹))))) := by rw [← mul_assoc, ← c1 b, mul_assoc]
    _ = b * (z₂ * (z₁ * (z₁⁻¹ * (a⁻¹ * (z₂⁻¹ * b⁻¹))))) := by
        rw [← mul_assoc z₁, ← c1 z₂, mul_assoc]
    _ = b * (z₂ * (a⁻¹ * (z₂⁻¹ * b⁻¹))) := by rw [← mul_assoc z₁, mul_inv_cancel, one_mul]
    _ = b * (a⁻¹ * b⁻¹) := by
        rw [← mul_assoc z₂, ← c2 a⁻¹, mul_assoc, mul_inv_cancel_left]

theorem exists_perfect_map_eq {G' : Type*} [Group G'] (π : G →* G')
    (hker : π.ker ≤ Subgroup.center G) {V : Subgroup G'} (hV : ⁅V, V⁆ = V)
    (hVπ : V ≤ π.range) :
    ∃ W : Subgroup G, ⁅W, W⁆ = W ∧ W ≤ V.comap π ∧ W.map π = V := by
  set P : Subgroup G := V.comap π with hP
  have hPV : P.map π = V := by
    rw [hP, Subgroup.map_comap_eq]
    exact inf_eq_right.2 hVπ
  have hWV : (⁅P, P⁆).map π = V := by
    rw [Subgroup.map_commutator, hPV, hV]
  have hdecomp : ∀ x ∈ P, ∃ w ∈ ⁅P, P⁆, ∃ z ∈ Subgroup.center G, x = w * z := by
    intro x hx
    have hx' : π x ∈ (⁅P, P⁆).map π := by
      rw [hWV]
      exact hx
    obtain ⟨w, hw, hwx⟩ := hx'
    refine ⟨w, hw, w⁻¹ * x, hker ?_, by simp⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hwx, inv_mul_cancel]
  refine ⟨⁅P, P⁆, le_antisymm (commutator_self_le _) ?_, commutator_self_le P, hWV⟩
  refine Subgroup.commutator_le.2 fun x hx y hy => ?_
  obtain ⟨w₁, hw₁, z₁, hz₁, rfl⟩ := hdecomp x hx
  obtain ⟨w₂, hw₂, z₂, hz₂, rfl⟩ := hdecomp y hy
  rw [commutatorElement_mul_central hz₁ hz₂]
  exact Subgroup.commutator_mem_commutator hw₁ hw₂

theorem card_sup_dvd_mul [Finite G] (B Z : Subgroup G)
    (h : B ≤ Subgroup.normalizer (Z : Set G)) :
    Nat.card ↥(B ⊔ Z) ∣ Nat.card B * Nat.card Z := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer h
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer h
  have e : ↥B ⧸ Z.subgroupOf B ≃* ↥(B ⊔ Z) ⧸ Z.subgroupOf (B ⊔ Z) :=
    QuotientGroup.quotientInfEquivProdNormalizerQuotient B Z h
  have h1 : (Z.subgroupOf (B ⊔ Z)).index = (Z.subgroupOf B).index :=
    (Nat.card_congr e.toEquiv).symm
  have h2 : Nat.card (Z.subgroupOf (B ⊔ Z)) = Nat.card Z :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
  have h3 := Subgroup.index_mul_card (Z.subgroupOf (B ⊔ Z))
  rw [h1, h2] at h3
  rw [← h3]
  exact mul_dvd_mul (Subgroup.index_dvd_card _) dvd_rfl

theorem dvd_card_of_generated [Finite G] {p : ℕ} (hp : p.Prime) {J B : Subgroup G}
    (hBJ : B ≤ J) (hgen : J ≤ B ⊔ perfectJoin J) (hJ : p ∣ Nat.card J) :
    p ∣ Nat.card B ∨ p ∣ Nat.card (perfectJoin J) := by
  have hJeq : J = B ⊔ perfectJoin J := le_antisymm hgen (sup_le hBJ (perfectJoin_le J))
  have hBN : B ≤ Subgroup.normalizer (perfectJoin J : Set G) :=
    hBJ.trans (le_normalizer_perfectJoin J)
  have hdvd := card_sup_dvd_mul B (perfectJoin J) hBN
  rw [← hJeq] at hdvd
  exact hp.dvd_mul.1 (hJ.trans hdvd)

theorem not_dvd_card_of_generated [Finite G] {p : ℕ} (hp : p.Prime) {J B : Subgroup G}
    (hBJ : B ≤ J) (hgen : J ≤ B ⊔ perfectJoin J)
    (hperf : ∀ U : Subgroup G, U ≤ J → ⁅U, U⁆ = U → ¬ p ∣ Nat.card U)
    (hB : p ∣ Nat.card B → ∃ U : Subgroup G, U ≤ J ∧ ⁅U, U⁆ = U ∧ p ∣ Nat.card U) :
    ¬ p ∣ Nat.card J := by
  intro hJ
  rcases dvd_card_of_generated hp hBJ hgen hJ with h | h
  · obtain ⟨U, hUJ, hU, hpU⟩ := hB h
    exact hperf U hUJ hU hpU
  · exact hperf _ (perfectJoin_le J) (perfectJoin_perfect J) h

end CFSG.AGLEmbedding.ParabPrime
