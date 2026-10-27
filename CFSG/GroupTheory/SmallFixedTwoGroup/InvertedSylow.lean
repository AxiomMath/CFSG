module

public import CFSG.GroupTheory.SmallFixedTwoGroup.InvertedPGroup
public import CFSG.GroupTheory.SmallFixedTwoGroup.InvertedTranslate

public section

namespace CFSG.GroupTheory.SmallFixedTwoGroup

variable {G : Type*} [Group G]

theorem exists_inverting_automorphism_of_sylow [Finite G] {θ : MulAut G} (hθ : θ * θ = 1)
    (hS : Nat.card G ≤ 4 * Nat.card {g : G // θ g = g⁻¹}) {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p)
    (P : Sylow p G) :
    ∃ θ' : MulAut G, θ' * θ' = 1 ∧
      Nat.card {g : G // θ' g = g⁻¹} = Nat.card {g : G // θ g = g⁻¹} ∧
        ∀ x ∈ (P : Subgroup G), θ' x = x⁻¹ := by
  classical
  obtain ⟨x, hx, hineq⟩ := exists_inverted_translate (P : Subgroup G)
  set θ' : MulAut G := MulAut.conj x * θ with hθ'def
  have hθ' : θ' * θ' = 1 := by
    rw [hθ'def]
    exact translate_mul_self hθ hx
  have hScard : Nat.card {g : G // θ' g = g⁻¹} = Nat.card {g : G // θ g = g⁻¹} := by
    rw [hθ'def]
    exact card_inverted_translate hx
  let Sθ := {g : G // θ g = g⁻¹}
  let A := {h : (P : Subgroup G) // θ' (h : G) = (h : G)⁻¹}
  have hineq' : Nat.card (P : Subgroup G) * Nat.card Sθ ≤ Nat.card G * Nat.card A := hineq
  have hSpos : 0 < Nat.card Sθ := by
    haveI : Nonempty Sθ := ⟨⟨1, by simp [Sθ]⟩⟩
    exact Nat.card_pos
  have step2 : Nat.card (P : Subgroup G) ≤ 4 * Nat.card A := by
    apply Nat.le_of_mul_le_mul_right _ hSpos
    calc Nat.card (P : Subgroup G) * Nat.card Sθ
        ≤ Nat.card G * Nat.card A := hineq'
      _ ≤ (4 * Nat.card Sθ) * Nat.card A := Nat.mul_le_mul_right _ hS
      _ = (4 * Nat.card A) * Nat.card Sθ := by ring
  let T : Set G := {g | g ∈ (P : Subgroup G) ∧ θ' g = g⁻¹}
  let R : Subgroup G := Subgroup.closure T
  have hRP : R ≤ (P : Subgroup G) := by
    change Subgroup.closure T ≤ (P : Subgroup G)
    rw [Subgroup.closure_le]
    exact fun g hg => hg.1
  have hRθ' : ∀ r ∈ R, θ' r ∈ R := by
    have hle : R ≤ R.comap θ'.toMonoidHom := by
      change Subgroup.closure T ≤ R.comap θ'.toMonoidHom
      rw [Subgroup.closure_le]
      rintro t ⟨htP, htinv⟩
      change θ' t ∈ R
      rw [htinv]
      exact R.inv_mem (Subgroup.subset_closure ⟨htP, htinv⟩)
    intro r hr
    exact hle hr
  have hRp : IsPGroup p R := P.isPGroup'.to_le hRP
  let SR := {r : R // θ' (r : G) = (r : G)⁻¹}
  have hASR : Nat.card A ≤ Nat.card SR := by
    apply Nat.card_le_card_of_injective
      (fun a : A => (⟨⟨a.1.1, Subgroup.subset_closure ⟨a.1.2, a.2⟩⟩, a.2⟩ : SR))
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun t : SR => ((t : SR).1 : G)) hab
  have hSRR : Nat.card SR ≤ Nat.card R :=
    Nat.card_le_card_of_injective (fun a : SR => (a : R)) (fun _ _ h => Subtype.ext h)
  have hRcard : Nat.card R ≤ Nat.card (P : Subgroup G) := Subgroup.card_le_of_le hRP
  have hcard : Nat.card R ≤ 4 * Nat.card SR :=
    le_trans hRcard (le_trans step2 (Nat.mul_le_mul_left 4 hASR))
  have step5 : ∀ r ∈ R, θ' r = r⁻¹ :=
    inverted_of_card_inverted_ge (θ := θ') hθ' hp hRp hRθ' hcard
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hRp
  obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp P.isPGroup'
  have hdiv : p ^ a ∣ p ^ b := by
    rw [← ha, ← hb]
    exact Subgroup.card_dvd_of_le hRP
  have hab : a ≤ b := (Nat.pow_dvd_pow_iff_le_right (Fact.out : p.Prime).one_lt).mp hdiv
  have hba : b ≤ a := by
    by_contra h
    replace h := not_le.mp h
    have hpb : p ^ b ≤ 4 * p ^ a := by
      calc p ^ b = Nat.card (P : Subgroup G) := hb.symm
        _ ≤ 4 * Nat.card SR := le_trans step2 (Nat.mul_le_mul_left 4 hASR)
        _ ≤ 4 * Nat.card R := Nat.mul_le_mul_left 4 hSRR
        _ = 4 * p ^ a := by rw [ha]
    have hlt : p ^ (a + 1) ≤ p ^ b :=
      Nat.pow_le_pow_right (le_of_lt (Fact.out : p.Prime).one_lt) (Nat.succ_le_of_lt h)
    have hle : p * p ^ a ≤ 4 * p ^ a := by
      calc p * p ^ a = p ^ (a + 1) := (pow_succ' p a).symm
        _ ≤ p ^ b := hlt
        _ ≤ 4 * p ^ a := hpb
    have hposa : 0 < p ^ a := by
      rw [← ha]
      haveI : Nonempty R := ⟨1, R.one_mem⟩
      exact Nat.card_pos
    have hp4 : p ≤ 4 := Nat.le_of_mul_le_mul_right hle hposa
    omega
  have habEq : a = b := le_antisymm hab hba
  have hcardEq : Nat.card R = Nat.card (P : Subgroup G) := by rw [ha, hb, habEq]
  have hReq : R = (P : Subgroup G) :=
    Subgroup.eq_of_le_of_card_ge hRP (le_of_eq hcardEq.symm)
  exact ⟨θ', hθ', hScard, fun y hy => step5 y (le_of_eq hReq.symm hy)⟩

end CFSG.GroupTheory.SmallFixedTwoGroup
