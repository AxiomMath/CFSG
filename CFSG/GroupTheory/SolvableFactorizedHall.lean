module

public import CFSG.GroupTheory.SolvableHallNodes
public import CFSG.GroupTheory.SteinbergCBFTFactorization

public section

open scoped Pointwise
open Subgroup

namespace CFSG

universe u

variable {G : Type u} [Group G] [Finite G]

lemma IsHallSubgroup.factorization_eq_card_of_mem {π : Set Nat.Primes} {H : Subgroup G}
    (hH : IsHallSubgroup π H) {p : ℕ} (hp : p.Prime)
    (hmem : (⟨p, hp⟩ : Nat.Primes) ∈ π) :
    (Nat.card H).factorization p = (Nat.card G).factorization p := by
  have hnotdvd : ¬ p ∣ H.index := fun h =>
    hH.p_in_pi_of_p_dvd_index ⟨p, hp⟩ h hmem
  have hfac_index : H.index.factorization p = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hnotdvd
  calc
    (Nat.card H).factorization p
        = (Nat.card H).factorization p + H.index.factorization p := by
            rw [hfac_index, add_zero]
    _ = (Nat.card H * H.index).factorization p := by
          rw [Nat.factorization_mul Nat.card_pos.ne' Subgroup.index_ne_zero_of_finite]
          rw [Finsupp.add_apply]
    _ = (Nat.card G).factorization p := by
          rw [Subgroup.card_mul_index]

lemma IsHallSubgroup.factorization_eq_zero_of_not_mem {π : Set Nat.Primes} {H : Subgroup G}
    (hH : IsHallSubgroup π H) {p : ℕ} (hp : p.Prime)
    (hmem : (⟨p, hp⟩ : Nat.Primes) ∉ π) :
    (Nat.card H).factorization p = 0 := by
  have hnotdvd : ¬ p ∣ Nat.card H := fun h =>
    hmem (hH.p_in_pi_of_p_dvd_card ⟨p, hp⟩ h)
  exact Nat.factorization_eq_zero_of_not_dvd hnotdvd

lemma exists_conj_mul_eq_of_mul_eq_top {A B : Subgroup G}
    (hAB : (A : Set G) * (B : Set G) = Set.univ) (g₁ g₂ : G) :
    ∃ h : G,
      A.map (MulAut.conj (g₁ * h)⁻¹).toMonoidHom = A ∧
      B.map (MulAut.conj (g₂ * h)⁻¹).toMonoidHom = B := by
  classical
  have hmem : g₁ * g₂⁻¹ ∈ (A : Set G) * (B : Set G) := by
    rw [hAB]
    exact Set.mem_univ _
  rw [Set.mem_mul] at hmem
  obtain ⟨a, ha, b, hb, hab⟩ := hmem
  refine ⟨g₁⁻¹ * a, ?_, ?_⟩
  · have hg₁ : g₁ * (g₁⁻¹ * a) = a := by group
    rw [hg₁]
    exact (Subgroup.mem_normalizer_iff_map_conj_eq).1 (Subgroup.le_normalizer (A.inv_mem ha))
  · have hg₂ : g₂ * (g₁⁻¹ * a) = b⁻¹ := by
      have hg₂' : g₂ = b⁻¹ * a⁻¹ * g₁ := by
        calc
          g₂ = (g₁ * g₂⁻¹)⁻¹ * g₁ := by group
          _ = (a * b)⁻¹ * g₁ := by rw [hab]
          _ = b⁻¹ * a⁻¹ * g₁ := by group
      rw [hg₂']
      group
    rw [hg₂]
    exact (Subgroup.mem_normalizer_iff_map_conj_eq).1
      (Subgroup.le_normalizer (by simpa using hb))

lemma card_mul_card_inf_dvd_of_pi_part {A B H H₁ H₂ : Subgroup G} {π : Set Nat.Primes}
    (hAB : (A : Set G) * (B : Set G) = Set.univ)
    (hH : IsHallSubgroup π H)
    (hH₁π : ∀ p (hp : p.Prime), (⟨p, hp⟩ : Nat.Primes) ∈ π →
      (Nat.card H₁).factorization p = (Nat.card A).factorization p)
    (hH₁π' : ∀ p (hp : p.Prime), (⟨p, hp⟩ : Nat.Primes) ∉ π →
      (Nat.card H₁).factorization p = 0)
    (hH₂π : ∀ p (hp : p.Prime), (⟨p, hp⟩ : Nat.Primes) ∈ π →
      (Nat.card H₂).factorization p = (Nat.card B).factorization p)
    (hH₂π' : ∀ p (hp : p.Prime), (⟨p, hp⟩ : Nat.Primes) ∉ π →
      (Nat.card H₂).factorization p = 0)
    (hH₁A : H₁ ≤ A) (hH₂B : H₂ ≤ B) :
    Nat.card H * Nat.card ↥(H₁ ⊓ H₂) ∣ Nat.card H₁ * Nat.card H₂ := by
  classical
  have hcardAB : Nat.card G * Nat.card ↥(A ⊓ B) = Nat.card A * Nat.card B := by
    have h := CFSG.GroupTheory.FT63ChII.card_setMul_mul_card_inf (A := A) (B := B)
    rw [hAB] at h
    simpa using h
  have hk_dvd : Nat.card ↥(H₁ ⊓ H₂) ∣ Nat.card ↥(A ⊓ B) :=
    Subgroup.card_dvd_of_le (inf_le_inf hH₁A hH₂B)
  refine (Nat.factorization_prime_le_iff_dvd ?_ ?_).1 ?_
  · exact Nat.mul_ne_zero Nat.card_pos.ne' Nat.card_pos.ne'
  · exact Nat.mul_ne_zero Nat.card_pos.ne' Nat.card_pos.ne'
  intro p hp
  have hk_le : (Nat.card ↥(H₁ ⊓ H₂)).factorization p ≤
      (Nat.card ↥(A ⊓ B)).factorization p :=
    (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').2 hk_dvd p
  have hABfac : (Nat.card G).factorization p + (Nat.card ↥(A ⊓ B)).factorization p =
      (Nat.card A).factorization p + (Nat.card B).factorization p := by
    calc
      (Nat.card G).factorization p + (Nat.card ↥(A ⊓ B)).factorization p
          = (Nat.card G * Nat.card ↥(A ⊓ B)).factorization p := by
              rw [Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne']
              rw [Finsupp.add_apply]
      _ = (Nat.card A * Nat.card B).factorization p := by rw [hcardAB]
      _ = (Nat.card A).factorization p + (Nat.card B).factorization p := by
              rw [Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne']
              rw [Finsupp.add_apply]
  have hleft : (Nat.card H * Nat.card ↥(H₁ ⊓ H₂)).factorization p =
      (Nat.card H).factorization p + (Nat.card ↥(H₁ ⊓ H₂)).factorization p := by
    rw [Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne']
    rw [Finsupp.add_apply]
  have hright : (Nat.card H₁ * Nat.card H₂).factorization p =
      (Nat.card H₁).factorization p + (Nat.card H₂).factorization p := by
    rw [Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne']
    rw [Finsupp.add_apply]
  by_cases hmem : (⟨p, hp⟩ : Nat.Primes) ∈ π
  · have hHp := IsHallSubgroup.factorization_eq_card_of_mem hH hp hmem
    have hH₁p := hH₁π p hp hmem
    have hH₂p := hH₂π p hp hmem
    rw [hleft, hright, hHp, hH₁p, hH₂p]
    omega
  · have hHp := IsHallSubgroup.factorization_eq_zero_of_not_mem hH hp hmem
    have hH₁p := hH₁π' p hp hmem
    have hH₂p := hH₂π' p hp hmem
    have hk0 : (Nat.card ↥(H₁ ⊓ H₂)).factorization p = 0 := by
      have hle : (Nat.card ↥(H₁ ⊓ H₂)).factorization p ≤ (Nat.card H₁).factorization p :=
        (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').2
          (Subgroup.card_dvd_of_le inf_le_left) p
      omega
    rw [hleft, hright, hHp, hH₁p, hH₂p, hk0]

theorem exists_isHallSubgroup_factorized (hG : Group.IsSolvable G) {A B : Subgroup G}
    (hAB : (A : Set G) * (B : Set G) = Set.univ) (π : Set Nat.Primes) :
    ∃ H : Subgroup G, IsHallSubgroup π H ∧
      (H : Set G) = ((H ⊓ A : Subgroup G) : Set G) *
        ((H ⊓ B : Subgroup G) : Set G) := by
  classical
  letI : Group.IsSolvable G := hG
  obtain ⟨H, hH⟩ := SolvableHall.solvable_hall_existence hG π
  obtain ⟨K₁, hK₁⟩ := SolvableHall.solvable_hall_existence
    (inferInstance : Group.IsSolvable A) π
  obtain ⟨K₂, hK₂⟩ := SolvableHall.solvable_hall_existence
    (inferInstance : Group.IsSolvable B) π
  set K₁G : Subgroup G := K₁.map A.subtype with hK₁G
  set K₂G : Subgroup G := K₂.map B.subtype with hK₂G
  have hK₁Gπ : IsPiSubgroup π K₁G := by
    intro p hp
    apply hK₁.p_in_pi_of_p_dvd_card p
    rwa [hK₁G, Subgroup.card_map_of_injective A.subtype_injective] at hp
  have hK₂Gπ : IsPiSubgroup π K₂G := by
    intro p hp
    apply hK₂.p_in_pi_of_p_dvd_card p
    rwa [hK₂G, Subgroup.card_map_of_injective B.subtype_injective] at hp
  obtain ⟨L₁, hL₁, hK₁L₁⟩ :=
    SolvableHall.solvable_hall_containment hG π K₁G hK₁Gπ
  obtain ⟨g₁, hg₁⟩ :=
    exists_conj_eq_of_isHallSubgroup_of_solvable hG hH hL₁
  obtain ⟨L₂, hL₂, hK₂L₂⟩ :=
    SolvableHall.solvable_hall_containment hG π K₂G hK₂Gπ
  obtain ⟨g₂, hg₂⟩ :=
    exists_conj_eq_of_isHallSubgroup_of_solvable hG hH hL₂
  have hx₁ : K₁G.map (MulAut.conj g₁⁻¹).toMonoidHom ≤ H := by
    intro x hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    have hkL : k ∈ L₁ := hK₁L₁ hk
    rw [hg₁, Subgroup.mem_map] at hkL
    obtain ⟨h, hh, hkh⟩ := hkL
    rw [← hkh]
    simpa [MulAut.conj_apply, mul_assoc] using hh
  have hx₂ : K₂G.map (MulAut.conj g₂⁻¹).toMonoidHom ≤ H := by
    intro x hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    have hkL : k ∈ L₂ := hK₂L₂ hk
    rw [hg₂, Subgroup.mem_map] at hkL
    obtain ⟨h, hh, hkh⟩ := hkL
    rw [← hkh]
    simpa [MulAut.conj_apply, mul_assoc] using hh
  obtain ⟨h, hAh, hBh⟩ := exists_conj_mul_eq_of_mul_eq_top hAB g₁ g₂
  set Hnew : Subgroup G := H.map (MulAut.conj h⁻¹).toMonoidHom with hHnew
  set H₁ : Subgroup G := K₁G.map (MulAut.conj (g₁ * h)⁻¹).toMonoidHom with hH₁
  set H₂ : Subgroup G := K₂G.map (MulAut.conj (g₂ * h)⁻¹).toMonoidHom with hH₂
  have hH₁A : H₁ ≤ A := by
    rw [hH₁]
    calc
      K₁G.map (MulAut.conj (g₁ * h)⁻¹).toMonoidHom ≤
          A.map (MulAut.conj (g₁ * h)⁻¹).toMonoidHom :=
        Subgroup.map_mono (by rw [hK₁G]; exact Subgroup.map_subtype_le K₁)
      _ = A := hAh
  have hH₂B : H₂ ≤ B := by
    rw [hH₂]
    calc
      K₂G.map (MulAut.conj (g₂ * h)⁻¹).toMonoidHom ≤
          B.map (MulAut.conj (g₂ * h)⁻¹).toMonoidHom :=
        Subgroup.map_mono (by rw [hK₂G]; exact Subgroup.map_subtype_le K₂)
      _ = B := hBh
  have hH₁H : H₁ ≤ Hnew := by
    rw [hH₁, hHnew]
    calc
      K₁G.map (MulAut.conj (g₁ * h)⁻¹).toMonoidHom
          = (K₁G.map (MulAut.conj g₁⁻¹).toMonoidHom).map
              (MulAut.conj h⁻¹).toMonoidHom := by
            have hcomp : (MulAut.conj h⁻¹).toMonoidHom.comp
                (MulAut.conj g₁⁻¹).toMonoidHom =
                (MulAut.conj (g₁ * h)⁻¹).toMonoidHom := by
              ext z
              simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
              rw [mul_inv_rev, map_mul, MulAut.mul_apply]
            conv_rhs => rw [Subgroup.map_map]
            rw [hcomp]
      _ ≤ H.map (MulAut.conj h⁻¹).toMonoidHom := Subgroup.map_mono hx₁
  have hH₂H : H₂ ≤ Hnew := by
    rw [hH₂, hHnew]
    calc
      K₂G.map (MulAut.conj (g₂ * h)⁻¹).toMonoidHom
          = (K₂G.map (MulAut.conj g₂⁻¹).toMonoidHom).map
              (MulAut.conj h⁻¹).toMonoidHom := by
            have hcomp : (MulAut.conj h⁻¹).toMonoidHom.comp
                (MulAut.conj g₂⁻¹).toMonoidHom =
                (MulAut.conj (g₂ * h)⁻¹).toMonoidHom := by
              ext z
              simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
              rw [mul_inv_rev, map_mul, MulAut.mul_apply]
            conv_rhs => rw [Subgroup.map_map]
            rw [hcomp]
      _ ≤ H.map (MulAut.conj h⁻¹).toMonoidHom := Subgroup.map_mono hx₂
  have hH₁card : Nat.card H₁ = Nat.card K₁ := by
    rw [hH₁, hK₁G]
    rw [Subgroup.card_map_of_injective (MulAut.conj (g₁ * h)⁻¹).injective]
    exact Subgroup.card_map_of_injective A.subtype_injective
  have hH₂card : Nat.card H₂ = Nat.card K₂ := by
    rw [hH₂, hK₂G]
    rw [Subgroup.card_map_of_injective (MulAut.conj (g₂ * h)⁻¹).injective]
    exact Subgroup.card_map_of_injective B.subtype_injective
  have hH₁π : ∀ p (hp : p.Prime), (⟨p, hp⟩ : Nat.Primes) ∈ π →
      (Nat.card H₁).factorization p = (Nat.card A).factorization p := by
    intro p hp hmem
    rw [hH₁card]
    exact IsHallSubgroup.factorization_eq_card_of_mem (G := A) hK₁ hp hmem
  have hH₁π' : ∀ p (hp : p.Prime), (⟨p, hp⟩ : Nat.Primes) ∉ π →
      (Nat.card H₁).factorization p = 0 := by
    intro p hp hmem
    rw [hH₁card]
    exact IsHallSubgroup.factorization_eq_zero_of_not_mem (G := A) hK₁ hp hmem
  have hH₂π : ∀ p (hp : p.Prime), (⟨p, hp⟩ : Nat.Primes) ∈ π →
      (Nat.card H₂).factorization p = (Nat.card B).factorization p := by
    intro p hp hmem
    rw [hH₂card]
    exact IsHallSubgroup.factorization_eq_card_of_mem (G := B) hK₂ hp hmem
  have hH₂π' : ∀ p (hp : p.Prime), (⟨p, hp⟩ : Nat.Primes) ∉ π →
      (Nat.card H₂).factorization p = 0 := by
    intro p hp hmem
    rw [hH₂card]
    exact IsHallSubgroup.factorization_eq_zero_of_not_mem (G := B) hK₂ hp hmem
  have hHnew : IsHallSubgroup π Hnew :=
    hH.map_mulAut (MulAut.conj h⁻¹)
  have hdiv : Nat.card Hnew * Nat.card ↥(H₁ ⊓ H₂) ∣ Nat.card H₁ * Nat.card H₂ :=
    card_mul_card_inf_dvd_of_pi_part hAB hHnew hH₁π hH₁π' hH₂π hH₂π' hH₁A hH₂B
  have hcard_prod : Nat.card ↥((H₁ : Set G) * (H₂ : Set G)) *
      Nat.card ↥(H₁ ⊓ H₂) = Nat.card H₁ * Nat.card H₂ :=
    CFSG.GroupTheory.FT63ChII.card_setMul_mul_card_inf (A := H₁) (B := H₂)
  have hle_mul : Nat.card Hnew * Nat.card ↥(H₁ ⊓ H₂) ≤
      Nat.card ↥((H₁ : Set G) * (H₂ : Set G)) * Nat.card ↥(H₁ ⊓ H₂) := by
    rw [hcard_prod]
    exact Nat.le_of_dvd (Nat.mul_pos Nat.card_pos Nat.card_pos) hdiv
  have hle : Nat.card Hnew ≤ Nat.card ↥((H₁ : Set G) * (H₂ : Set G)) :=
    Nat.le_of_mul_le_mul_right hle_mul (Nat.card_pos (α := ↥(H₁ ⊓ H₂)))
  have hsub : ((H₁ : Set G) * (H₂ : Set G)) ⊆ (Hnew : Set G) := by
    intro x hx
    rw [Set.mem_mul] at hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    exact Hnew.mul_mem (hH₁H ha) (hH₂H hb)
  have hprod_eq : ((H₁ : Set G) * (H₂ : Set G)) = (Hnew : Set G) := by
    refine Set.eq_of_subset_of_ncard_le hsub ?_
    rwa [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
  have hH₁inf : H₁ ≤ Hnew ⊓ A := le_inf hH₁H hH₁A
  have hH₂inf : H₂ ≤ Hnew ⊓ B := le_inf hH₂H hH₂B
  have hfinal : (Hnew : Set G) =
      ((Hnew ⊓ A : Subgroup G) : Set G) * ((Hnew ⊓ B : Subgroup G) : Set G) := by
    rw [← hprod_eq]
    refine Set.Subset.antisymm ?_ ?_
    · intro x hx
      rw [Set.mem_mul] at hx ⊢
      obtain ⟨a, ha, b, hb, rfl⟩ := hx
      exact ⟨a, hH₁inf ha, b, hH₂inf hb, rfl⟩
    · intro x hx
      rw [Set.mem_mul] at hx
      obtain ⟨a, ha, b, hb, rfl⟩ := hx
      have hmem : a * b ∈ (Hnew : Set G) :=
        Hnew.mul_mem (mem_inf.1 ha).1 (mem_inf.1 hb).1
      rwa [← hprod_eq] at hmem
  exact ⟨Hnew, hHnew, hfinal⟩

theorem exists_isHallSubgroup_eq_sup_inf (hG : Group.IsSolvable G) {A B : Subgroup G}
    (hAB : (A : Set G) * (B : Set G) = Set.univ) (π : Set Nat.Primes) :
    ∃ H : Subgroup G, IsHallSubgroup π H ∧ H = H ⊓ A ⊔ H ⊓ B := by
  obtain ⟨H, hH, hfac⟩ := exists_isHallSubgroup_factorized hG hAB π
  refine ⟨H, hH, le_antisymm ?_
    (sup_le (show H ⊓ A ≤ H from inf_le_left) (show H ⊓ B ≤ H from inf_le_left))⟩
  intro x hx
  have hx' : x ∈ ((H ⊓ A : Subgroup G) : Set G) * ((H ⊓ B : Subgroup G) : Set G) := by
    rw [← hfac]
    exact hx
  rw [Set.mem_mul] at hx'
  obtain ⟨a, ha, b, hb, rfl⟩ := hx'
  exact Subgroup.mul_mem_sup ha hb

end CFSG
