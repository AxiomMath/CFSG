module

public import CFSG.LocalAnalysis.Mason73.Extremal
public import CFSG.LocalAnalysis.Mason73.Powers2

public section

namespace CFSG.LocalAnalysis.Mason73

open CFSG.CGT.Stroth77.L4Sylow CFSG.GH74.GLS.Stage1.Thm3.Sec8 Equiv Subgroup

variable {n : ℕ}

theorem R0_mul_self_cases_V : ∀ σ : Fin81.R0, σ * σ = 1 → σ ≠ s01 → σ ≠ s23 →
    σ = 1 ∨ σ = zP ∨ σ = tP ∨ σ = tzP := by
  decide

theorem R0_comm_zP_tP : ∀ σ : Fin81.R0, σ * zP = zP * σ → σ * tP = tP * σ →
    σ = 1 ∨ σ = zP ∨ σ = tP ∨ σ = tzP := by
  decide

theorem card_finset_V : ({1, zP, tP, tzP} : Finset Fin81.R0).card = 4 := by
  decide

theorem card_patFix_zP_tP_le :
    (Finset.univ.filter fun p : Fin 2 × Fin 2 × Fin 2 =>
      PatFix (zP : Perm (Fin 4)) (pat p) ∧ PatFix (tP : Perm (Fin 4)) (pat p)).card ≤ 4 := by
  decide

theorem eq_four_of_mul_eq_sixteen {a b : ℕ} (ha : a ≤ 4) (hb : b ≤ 4) (h : a * b = 16) :
    a = 4 ∧ b = 4 := by
  interval_cases a <;> interval_cases b <;> omega

theorem mem_of_commute_of_card_eq_sixteen (hn : 3 ≤ n) (E : Subgroup (L4Model n))
    (hE : ∀ x ∈ E, x * x = 1) (h16 : Nat.card E = 16) {c : L4Model n}
    (hc : ∀ x ∈ E, c * x = x * c) : c ∈ E := by
  classical
  have hsplit := card_eq_card_inf_A_mul E
  obtain ⟨g, hg, hg1⟩ : ∃ g ∈ E, piT g ≠ 1 := by
    by_contra hall
    push Not at hall
    have h1 : Nat.card (E.map piT) ≤ 1 := by
      rw [Subgroup.card_le_one_iff_eq_bot, eq_bot_iff]
      rintro _ ⟨x, hx, rfl⟩
      exact (Subgroup.mem_bot).2 (hall x hx)
    have h8 := card_inf_A_le_eight hn E hE
    have : Nat.card E ≤ 8 * 1 := hsplit ▸ Nat.mul_le_mul h8 h1
    omega
  have hA4 : Nat.card (E ⊓ A n : Subgroup (L4Model n)) ≤ 4 :=
    card_inf_A_le_four hn E hE hg1 fun x hx => mul_comm_of_mul_self hE hg (Subgroup.mem_inf.1 hx).1
  obtain ⟨hA, hP⟩ := eq_four_of_mul_eq_sixteen hA4 (card_map_piT_le_four E hE)
    (hsplit ▸ h16)
  have hcent : ∀ x ∈ E, E ≤ centralizer {x} := fun x hx y hy =>
    Subgroup.mem_centralizer_singleton_iff.2 (mul_comm_of_mul_self hE hy hx)
  have hno01 : ∀ x ∈ E, (piT x : Perm (Fin 4)) ≠ swap 0 1 := fun x hx h => by
    have := card_le_eight_of_le_centralizer_s01 hn h E hE (hcent x hx)
    omega
  have hno23 : ∀ x ∈ E, (piT x : Perm (Fin 4)) ≠ swap 2 3 := fun x hx h => by
    have := card_le_eight_of_le_centralizer hn h E hE (hcent x hx)
    omega
  set V : Finset Fin81.R0 := {1, zP, tP, tzP} with hVdef
  have hsubV : ((E.map piT : Subgroup Fin81.R0) : Set Fin81.R0) ⊆ (V : Set Fin81.R0) := by
    rintro _ ⟨x, hx, rfl⟩
    have h1 : piT x * piT x = 1 := by rw [← map_mul, hE x hx, map_one]
    rcases R0_mul_self_cases_V (piT x) h1 (fun h => hno01 x hx (congrArg Subtype.val h))
        (fun h => hno23 x hx (congrArg Subtype.val h)) with h | h | h | h <;>
      simp [hVdef, h]
  have hEV : ((E.map piT : Subgroup Fin81.R0) : Set Fin81.R0) = (V : Set Fin81.R0) := by
    have hP' : ((E.map piT : Subgroup Fin81.R0) : Set Fin81.R0).ncard = 4 :=
      (Nat.card_coe_set_eq _).symm.trans hP
    refine Set.eq_of_subset_of_ncard_le hsubV ?_ (Finset.finite_toSet V)
    rw [Set.ncard_coe_finset, card_finset_V, hP']
  have hmemV : ∀ σ ∈ V, σ ∈ E.map piT := fun σ hσ => by
    have : σ ∈ ((E.map piT : Subgroup Fin81.R0) : Set Fin81.R0) := hEV ▸ hσ
    exact this
  obtain ⟨g₁, hg₁, hg₁π⟩ := Subgroup.mem_map.1 (hmemV zP (by simp [hVdef]))
  obtain ⟨g₂, hg₂, hg₂π⟩ := Subgroup.mem_map.1 (hmemV tP (by simp [hVdef]))
  have hcz : piT c * zP = zP * piT c := by
    rw [← hg₁π, ← map_mul, ← map_mul, hc g₁ hg₁]
  have hct : piT c * tP = tP * piT c := by
    rw [← hg₂π, ← map_mul, ← map_mul, hc g₂ hg₂]
  have hcV : piT c ∈ V := by
    rcases R0_comm_zP_tP (piT c) hcz hct with h | h | h | h <;> simp [hVdef, h]
  obtain ⟨e, he, heπ⟩ := Subgroup.mem_map.1 (hmemV _ hcV)
  set a := e⁻¹ * c with ha
  have haA : a ∈ A n := by
    rw [mem_A_iff, ha, map_mul, map_inv, heπ, inv_mul_cancel]
  have hacomm : ∀ x ∈ E, x * a = a * x := by
    intro x hx
    have hex : e * x = x * e := mul_comm_of_mul_self hE he hx
    have hcx := hc x hx
    rw [ha]
    calc x * (e⁻¹ * c) = e⁻¹ * (e * x) * e⁻¹ * c := by group
      _ = e⁻¹ * (x * e) * e⁻¹ * c := by rw [hex]
      _ = e⁻¹ * (x * c) := by group
      _ = e⁻¹ * (c * x) := by rw [hcx]
      _ = e⁻¹ * c * x := by group
  have ha2 : a * a = 1 :=
    mul_self_eq_one_of_comm_zP_tP (by omega) haA hg₁π hg₂π (hacomm g₁ hg₁) (hacomm g₂ hg₂)
  set P : Finset (Fin 2 × Fin 2 × Fin 2) := Finset.univ.filter fun p =>
    PatFix (zP : Perm (Fin 4)) (pat p) ∧ PatFix (tP : Perm (Fin 4)) (pat p) with hPdef
  have hpatA : ∀ x ∈ A n, x * x = 1 → g₁ * x = x * g₁ → g₂ * x = x * g₂ →
      x ∈ (P.image (omegaEl hn) : Set (L4Model n)) := by
    intro x hxA hx2 hx₁ hx₂
    obtain ⟨p, rfl⟩ := exists_eq_omegaEl hn hxA hx2
    have p₁ := patFix_of_comm hn hx₁
    have p₂ := patFix_of_comm hn hx₂
    rw [hg₁π] at p₁
    rw [hg₂π] at p₂
    rw [Finset.coe_image]
    exact ⟨p, by simp [hPdef, p₁, p₂], rfl⟩
  have hsubA : ((E ⊓ A n : Subgroup (L4Model n)) : Set (L4Model n)) ⊆
      (P.image (omegaEl hn) : Set (L4Model n)) := by
    intro x hx
    have hx' := Subgroup.mem_inf.1 hx
    exact hpatA x hx'.2 (hE x hx'.1) (mul_comm_of_mul_self hE hg₁ hx'.1)
      (mul_comm_of_mul_self hE hg₂ hx'.1)
  have hcardP : ((P.image (omegaEl hn) : Finset (L4Model n)) : Set (L4Model n)).ncard ≤ 4 := by
    rw [Set.ncard_coe_finset]
    exact Finset.card_image_le.trans card_patFix_zP_tP_le
  have hEA : ((E ⊓ A n : Subgroup (L4Model n)) : Set (L4Model n)) =
      (P.image (omegaEl hn) : Set (L4Model n)) := by
    have hA' : ((E ⊓ A n : Subgroup (L4Model n)) : Set (L4Model n)).ncard = 4 :=
      (Nat.card_coe_set_eq _).symm.trans hA
    refine Set.eq_of_subset_of_ncard_le hsubA ?_ (Finset.finite_toSet _)
    rw [hA']
    exact hcardP
  have haE : a ∈ E := by
    have : a ∈ ((E ⊓ A n : Subgroup (L4Model n)) : Set (L4Model n)) := by
      rw [hEA]
      exact hpatA a haA ha2 (hacomm g₁ hg₁) (hacomm g₂ hg₂)
    exact (Subgroup.mem_inf.1 this).1
  have hc' : c = e * a := by rw [ha, mul_inv_cancel_left]
  rw [hc']
  exact E.mul_mem he haE

@[expose] def dblZMod (x : ZMod 2) : ZMod 4 := 2 * (x.val : ZMod 4)

theorem dblZMod_add : ∀ x y : ZMod 2, dblZMod (x + y) = dblZMod x + dblZMod y := by
  decide

theorem dblZMod_zero : dblZMod 0 = 0 := by
  decide

theorem dblZMod_injective : Function.Injective dblZMod := by
  decide

theorem dblZMod_two_mul : ∀ x : ZMod 2, dblZMod x + dblZMod x = 0 := by
  decide

@[expose] def dblVec : Multiplicative (Fin 4 → ZMod 2) →* Multiplicative (Fin 4 → ZMod 4) where
  toFun b := Multiplicative.ofAdd fun i => dblZMod (Multiplicative.toAdd b i)
  map_one' := by
    apply Multiplicative.toAdd.injective
    funext i
    exact dblZMod_zero
  map_mul' b c := by
    apply Multiplicative.toAdd.injective
    funext i
    exact dblZMod_add _ _

theorem dblVec_injective : Function.Injective dblVec := by
  intro b c h
  apply Multiplicative.toAdd.injective
  funext i
  exact dblZMod_injective
    (congrArg (fun x : Multiplicative (Fin 4 → ZMod 4) => Multiplicative.toAdd x i) h)

theorem dblVec_mul_self (b : Multiplicative (Fin 4 → ZMod 2)) : dblVec b * dblVec b = 1 := by
  apply Multiplicative.toAdd.injective
  funext i
  exact dblZMod_two_mul _

theorem not_injective_zmod_four_pow (hn : 3 ≤ n)
    (φ : Multiplicative (Fin 4 → ZMod 4) →* L4Model n) : ¬ Function.Injective φ := by
  intro hφ
  let E : Subgroup (L4Model n) := (φ.comp dblVec).range
  have hE2 : ∀ x ∈ E, x * x = 1 := by
    rintro _ ⟨b, rfl⟩
    rw [MonoidHom.comp_apply, ← map_mul, dblVec_mul_self, map_one]
  have hcardE : Nat.card E = 16 := by
    show Nat.card (φ.comp dblVec).range = 16
    have hinj : Function.Injective (φ.comp dblVec) := hφ.comp dblVec_injective
    rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hinj, Subgroup.card_top,
      Nat.card_eq_fintype_card]
    rfl
  let e₀ : Multiplicative (Fin 4 → ZMod 4) := Multiplicative.ofAdd (Pi.single 0 1)
  have hcomm : ∀ x ∈ E, φ e₀ * x = x * φ e₀ := by
    rintro _ ⟨b, rfl⟩
    rw [MonoidHom.comp_apply, ← map_mul, ← map_mul, mul_comm]
  have hmem := mem_of_commute_of_card_eq_sixteen hn E hE2 hcardE hcomm
  have h2 := hE2 _ hmem
  rw [← map_mul] at h2
  have h3 : e₀ * e₀ = 1 := hφ (by rw [h2, map_one])
  have h4 := congrArg (fun b : Multiplicative (Fin 4 → ZMod 4) => Multiplicative.toAdd b 0) h3
  simp only [e₀, toAdd_mul, toAdd_ofAdd, toAdd_one, Pi.add_apply, Pi.single_eq_same,
    Pi.zero_apply] at h4
  exact absurd h4 (by decide)

end CFSG.LocalAnalysis.Mason73
