module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.IVK812PermDefs
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.IVK812

open Equiv Equiv.Perm Subgroup

private def syl_e8 : Fin 8 ≃ {x : Fin 11 // x.val < 8} where
  toFun a := ⟨⟨a.val, by omega⟩, a.isLt⟩
  invFun y := ⟨y.1.val, y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private def syl_ext : Perm (Fin 8) →* Perm (Fin 11) := Equiv.Perm.extendDomainHom syl_e8

private lemma syl_ext_apply (α : Perm (Fin 8)) (x : Fin 11) (hx : x.val < 8) :
    (syl_ext α x).val = (α ⟨x.val, hx⟩).val :=
  congrArg Fin.val (Equiv.Perm.extendDomain_apply_image α syl_e8 ⟨x.val, hx⟩)

private lemma syl_ext_ge (α : Perm (Fin 8)) (x : Fin 11) (hx : ¬ x.val < 8) :
    syl_ext α x = x :=
  Equiv.Perm.extendDomain_apply_not_subtype α syl_e8 hx

private lemma syl_sign_ext (α : Perm (Fin 8)) : sign (syl_ext α) = sign α :=
  Equiv.Perm.sign_extendDomain α syl_e8

private def syl_corr (α : Perm (Fin 8)) : Perm (Fin 11) := if sign α = 1 then 1 else swap 8 9

private lemma syl_corr_mul (α β : Perm (Fin 8)) :
    syl_corr (α * β) = syl_corr α * syl_corr β := by
  unfold syl_corr
  rcases Int.units_eq_one_or (sign α) with ha | ha <;>
  rcases Int.units_eq_one_or (sign β) with hb | hb <;>
  simp [ha, hb, sign_mul]

private lemma syl_corr_comm (α β : Perm (Fin 8)) :
    syl_corr α * syl_ext β = syl_ext β * syl_corr α := by
  unfold syl_corr
  split_ifs
  · simp
  · rw [Equiv.mul_swap_eq_swap_mul, syl_ext_ge β 8 (by decide), syl_ext_ge β 9 (by decide)]

private def syl_iota : Perm (Fin 8) →* Perm (Fin 11) where
  toFun α := syl_ext α * syl_corr α
  map_one' := by simp [syl_corr]
  map_mul' α β := by
    calc syl_ext (α * β) * syl_corr (α * β)
        = syl_ext α * syl_ext β * (syl_corr α * syl_corr β) := by rw [map_mul, syl_corr_mul]
      _ = syl_ext α * (syl_ext β * syl_corr α) * syl_corr β := by simp only [mul_assoc]
      _ = syl_ext α * (syl_corr α * syl_ext β) * syl_corr β := by rw [syl_corr_comm]
      _ = syl_ext α * syl_corr α * (syl_ext β * syl_corr β) := by simp only [mul_assoc]

private lemma syl_corr_lt (α : Perm (Fin 8)) (x : Fin 11) (hx : x.val < 8) :
    syl_corr α x = x := by
  unfold syl_corr
  split_ifs
  · rfl
  · exact swap_apply_of_ne_of_ne (by intro h; subst h; exact absurd hx (by decide))
      (by intro h; subst h; exact absurd hx (by decide))

private lemma syl_corr_ge (α : Perm (Fin 8)) (x : Fin 11) (hx : ¬ x.val < 8) :
    ¬ (syl_corr α x).val < 8 := by
  unfold syl_corr
  split_ifs
  · exact hx
  · exact (by decide : ∀ y : Fin 11, ¬ y.val < 8 → ¬ (swap (8 : Fin 11) 9 y).val < 8) x hx

private lemma syl_iota_lt (α : Perm (Fin 8)) (x : Fin 11) (hx : x.val < 8) :
    (syl_iota α x).val = (α ⟨x.val, hx⟩).val := by
  show (syl_ext α (syl_corr α x)).val = _
  rw [syl_corr_lt α x hx]
  exact syl_ext_apply α x hx

private lemma syl_iota_ge (α : Perm (Fin 8)) (x : Fin 11) (hx : ¬ x.val < 8) :
    ¬ (syl_iota α x).val < 8 := by
  show ¬ (syl_ext α (syl_corr α x)).val < 8
  rw [syl_ext_ge α _ (syl_corr_ge α x hx)]
  exact syl_corr_ge α x hx

private lemma syl_iota_ten (α : Perm (Fin 8)) : syl_iota α 10 = 10 := by
  show syl_ext α (syl_corr α 10) = 10
  have : syl_corr α 10 = 10 := by
    unfold syl_corr
    split_ifs
    · rfl
    · decide
  rw [this]
  exact syl_ext_ge α 10 (by decide)

private lemma syl_iota_eight (α : Perm (Fin 8)) (h : sign α ≠ 1) : syl_iota α 8 = 9 := by
  show syl_ext α (syl_corr α 8) = 9
  have : syl_corr α 8 = 9 := by
    unfold syl_corr
    split_ifs with h'
    · exact absurd h' h
    · exact swap_apply_left _ _
  rw [this]
  exact syl_ext_ge α 9 (by decide)

private lemma syl_sign_iota (α : Perm (Fin 8)) : sign (syl_iota α) = 1 := by
  show sign (syl_ext α * syl_corr α) = 1
  rw [sign_mul, syl_sign_ext]
  unfold syl_corr
  split_ifs with h
  · simp [h]
  · have : sign (swap (8 : Fin 11) 9) = -1 := sign_swap (by decide)
    rw [this]
    rcases Int.units_eq_one_or (sign α) with h' | h'
    · exact absurd h' h
    · rw [h']
      rfl

private lemma syl_iota_injective : Function.Injective syl_iota := by
  rw [injective_iff_map_eq_one]
  intro α hα
  refine Equiv.ext fun a => Fin.ext ?_
  have h := syl_iota_lt α ⟨a.val, by omega⟩ a.isLt
  have h1 : syl_iota α ⟨a.val, by omega⟩ = ⟨a.val, by omega⟩ := by rw [hα]; rfl
  rw [h1] at h
  exact h.symm

private lemma syl_card_perm8 : Nat.card (Perm (Fin 8)) = 40320 := by
  rw [Nat.card_perm]
  simp [Nat.factorial]

private lemma syl_exists_sub : ∃ T₁ : Subgroup (Perm (Fin 8)), Nat.card T₁ = 2 ^ 7 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine Sylow.exists_subgroup_card_pow_prime 2 ?_
  rw [syl_card_perm8]
  norm_num

private lemma syl_trans (T₁ : Subgroup (Perm (Fin 8))) (h : Nat.card T₁ = 2 ^ 7) (x y : Fin 8) :
    ∃ t ∈ T₁, t x = y := by
  have h1 : Nat.card (MulAction.stabilizer T₁ x) * (MulAction.orbit T₁ x).ncard = 2 ^ 7 := by
    rw [← MulAction.index_stabilizer, Subgroup.card_mul_index, h]
  have h2 : Nat.card (MulAction.stabilizer (Perm (Fin 8)) x) * 8 = 40320 := by
    have := Subgroup.card_mul_index (MulAction.stabilizer (Perm (Fin 8)) x)
    rwa [MulAction.index_stabilizer_of_transitive, Nat.card_fin, syl_card_perm8] at this
  have h3 : Nat.card (MulAction.stabilizer T₁ x) ∣
      Nat.card (MulAction.stabilizer (Perm (Fin 8)) x) := by
    have hK : (MulAction.stabilizer T₁ x).map T₁.subtype ≤
        MulAction.stabilizer (Perm (Fin 8)) x := by
      rintro _ ⟨a, ha, rfl⟩
      exact ha
    rw [← Subgroup.card_map_of_injective T₁.subtype_injective]
    exact Subgroup.card_dvd_of_le hK
  have h4 : Nat.card (MulAction.stabilizer T₁ x) ∣ 16 := by
    have h5 : Nat.card (MulAction.stabilizer T₁ x) ∣ 2 ^ 7 := Dvd.intro _ h1
    have h6 : Nat.card (MulAction.stabilizer (Perm (Fin 8)) x) = 5040 := by omega
    rw [h6] at h3
    exact (Nat.dvd_gcd h5 h3 : _ ∣ Nat.gcd (2 ^ 7) 5040)
  have h7 : Nat.card (MulAction.stabilizer T₁ x) ≤ 16 := Nat.le_of_dvd (by norm_num) h4
  have h8 : 8 ≤ (MulAction.orbit T₁ x).ncard := by
    by_contra hlt
    push Not at hlt
    have : Nat.card (MulAction.stabilizer T₁ x) * (MulAction.orbit T₁ x).ncard ≤ 16 * 7 :=
      Nat.mul_le_mul h7 (by omega)
    omega
  have h9 : MulAction.orbit T₁ x = Set.univ := by
    apply Set.eq_of_subset_of_ncard_le (Set.subset_univ _) _ Set.finite_univ
    rw [Set.ncard_univ, Nat.card_fin]
    exact h8
  have hy : y ∈ MulAction.orbit T₁ x := by rw [h9]; exact Set.mem_univ _
  obtain ⟨t, ht⟩ := MulAction.mem_orbit_iff.1 hy
  exact ⟨t.1, t.2, ht⟩

private lemma syl_odd (T₁ : Subgroup (Perm (Fin 8))) (h : Nat.card T₁ = 2 ^ 7) :
    ∃ α ∈ T₁, sign α ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have hle : T₁ ≤ alternatingGroup (Fin 8) := fun α hα => mem_alternatingGroup.2 (hcon α hα)
  have := Subgroup.card_dvd_of_le hle
  rw [h, Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin] at this
  revert this
  decide

theorem exists_sylData : ∃ T : Subgroup (Perm (Fin 11)), SylData T := by
  obtain ⟨T₁, hcard⟩ := syl_exists_sub
  obtain ⟨α₀, hα₀, hodd⟩ := syl_odd T₁ hcard
  refine ⟨T₁.map syl_iota, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨α, -, rfl⟩
    exact syl_sign_iota α
  · rw [Subgroup.card_map_of_injective syl_iota_injective, hcard]
  · rintro _ ⟨α, -, rfl⟩
    exact syl_iota_ten α
  · rintro _ ⟨α, -, rfl⟩ x
    by_cases hx : x.val < 8
    · rw [syl_iota_lt α x hx]
      exact iff_of_true (α _).isLt hx
    · exact iff_of_false (syl_iota_ge α x hx) hx
  · intro x y hx hy
    obtain ⟨t, ht, hxy⟩ := syl_trans T₁ hcard ⟨x.val, hx⟩ ⟨y.val, hy⟩
    refine ⟨syl_iota t, ⟨t, ht, rfl⟩, ?_⟩
    apply Fin.ext
    rw [syl_iota_lt t x hx, hxy]
  · exact ⟨syl_iota α₀, ⟨α₀, hα₀, rfl⟩, syl_iota_eight α₀ hodd⟩

end CFSG.GH74.GLS.Stage2.Bender.Thm2.IVK812
