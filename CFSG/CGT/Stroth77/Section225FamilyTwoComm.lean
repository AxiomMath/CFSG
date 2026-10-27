module

public import CFSG.CGT.Stroth77.Section225FamilyTwo
public import CFSG.CGT.Stroth77.Section224UniformSq

public section

namespace CFSG.CGT.Stroth77

open Matrix
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {X : StrothAmbient G}

theorem familyTwo_disjunction (τ : StrothTypeIndex) (hrel : τ.m + 2 = τ.n) :
    (∃ m : ℕ, τ = StrothTypeIndex.t200 m) ∨
    (∃ m : ℕ, τ = StrothTypeIndex.t201 m) ∨
    (∃ (m : ℕ) (hm : 2 ≤ m), τ = StrothTypeIndex.t210 m hm) ∨
    (∃ (m : ℕ) (hm : 2 ≤ m), τ = StrothTypeIndex.t211 m hm) ∨
    (∃ (s : ℕ) (hs : 1 ≤ s), τ = StrothTypeIndex.t220 s hs) ∨
    (∃ (s : ℕ) (hs : 1 ≤ s), τ = StrothTypeIndex.t221 s hs) ∨
    (∃ (s : ℕ) (hs : 1 ≤ s), τ = StrothTypeIndex.t230 s hs) ∨
    (∃ (s : ℕ) (hs : 1 ≤ s), τ = StrothTypeIndex.t231 s hs) := by
  cases τ with
  | t100 m =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type100.k] at hrel
  | t101 s =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type101.k] at hrel
  | t110 t =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type110.k] at hrel
  | t111 t =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type111.k] at hrel
  | t120 m hm =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type120.k] at hrel
  | t121 m hm =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type121.k] at hrel
  | t130 m hm =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type130.k] at hrel
  | t131 m hm =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type131.k] at hrel
  | t200 m => exact Or.inl ⟨m, rfl⟩
  | t201 m => exact Or.inr (Or.inl ⟨m, rfl⟩)
  | t210 m hm => exact Or.inr (Or.inr (Or.inl ⟨m, hm, rfl⟩))
  | t211 m hm => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨m, hm, rfl⟩)))
  | t220 s hs => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨s, hs, rfl⟩))))
  | t221 s hs =>
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨s, hs, rfl⟩)))))
  | t230 s hs =>
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨s, hs, rfl⟩))))))
  | t231 s hs =>
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨s, hs, rfl⟩))))))
  | t300 n =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type300.k] at hrel
  | t310 m hm =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type310.k] at hrel
  | t320 m hm =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type320.k,
      Type32x.k] at hrel
  | t330 m hm =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type330.k,
      Type32x.k] at hrel
  | t321 =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type321.k] at hrel
  | t331 =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type331.k] at hrel

theorem action_rho_eq_type200 (τ : StrothTypeIndex) (hrel : τ.m + 2 = τ.n) :
    τ.action.ρ = Type200.ρM := by
  cases τ with
  | t100 m =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type100.k] at hrel
  | t101 s =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type101.k] at hrel
  | t110 t =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type110.k] at hrel
  | t111 t =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type111.k] at hrel
  | t120 m hm =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type120.k] at hrel
  | t121 m hm =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type121.k] at hrel
  | t130 m hm =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type130.k] at hrel
  | t131 m hm =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type131.k] at hrel
  | t200 m => rfl
  | t201 m => rfl
  | t210 m hm => rfl
  | t211 m hm => rfl
  | t220 s hs => rfl
  | t221 s hs => rfl
  | t230 s hs => rfl
  | t231 s hs => rfl
  | t300 n =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type300.k] at hrel
  | t310 m hm =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type310.k] at hrel
  | t320 m hm =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type320.k,
      Type32x.k] at hrel
  | t330 m hm =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type330.k,
      Type32x.k] at hrel
  | t321 =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type321.k] at hrel
  | t331 =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type331.k] at hrel

theorem map_rho_sub_omegaOne_type200_coeff (m : ℕ) (hm : 2 ≤ m) (z : ℤ) :
    AddSubgroup.map ((Type200.action m).φρ - AddMonoidHom.id (Torus (Type200.k m)))
      (AddSubgroup.closure ({ z • Torus.c, (2 : ℤ) ^ (m + 1) • Torus.a,
        (2 : ℤ) ^ (m + 1) • Torus.b } : Set (Torus (Type200.k m))))
      = AddSubgroup.closure ({ (2 : ℤ) ^ (m + 1) • Torus.a,
        (2 : ℤ) ^ (m + 1) • Torus.b } : Set (Torus (Type200.k m))) := by
  let f : Torus (Type200.k m) →+ Torus (Type200.k m) :=
    (Type200.action m).φρ - AddMonoidHom.id _
  let Ω : AddSubgroup (Torus (Type200.k m)) :=
    AddSubgroup.closure ({ z • Torus.c, (2 : ℤ) ^ (m + 1) • Torus.a,
      (2 : ℤ) ^ (m + 1) • Torus.b } : Set (Torus (Type200.k m)))
  let W : AddSubgroup (Torus (Type200.k m)) :=
    AddSubgroup.closure ({ (2 : ℤ) ^ (m + 1) • Torus.a,
      (2 : ℤ) ^ (m + 1) • Torus.b } : Set (Torus (Type200.k m)))
  change AddSubgroup.map f Ω = W
  have hf_ofInt (v : Fin 3 → ℤ) :
      f (Torus.ofInt (Type200.k m) v) =
        Torus.ofInt (Type200.k m) (Type200.ρM *ᵥ v - v) := by
    dsimp [f]
    rw [matAct_ofInt, Torus.ofInt_sub]
    rfl
  have hc_coord : z • Torus.c = Torus.ofInt (Type200.k m) ![z, 0, 0] := by
    have h : Torus.c = Torus.ofInt (Type200.k m) (![1, 0, 0] : Fin 3 → ℤ) := by
      rw [Torus.ofInt_eq_zsmul_gens]
      simp [Torus.c]
    rw [h, ← Torus.ofInt_zsmul]
    congr 1
    funext i
    fin_cases i <;> simp
  have ha_coord : (2 : ℤ) ^ (m + 1) • Torus.a =
      Torus.ofInt (Type200.k m) ![0, (2 : ℤ) ^ (m + 1), 0] := by
    have h : Torus.a = Torus.ofInt (Type200.k m) (![0, 1, 0] : Fin 3 → ℤ) := by
      rw [Torus.ofInt_eq_zsmul_gens]
      simp [Torus.a]
    rw [h, ← Torus.ofInt_zsmul]
    congr 1
    funext i
    fin_cases i <;> simp
  have hb_coord : (2 : ℤ) ^ (m + 1) • Torus.b =
      Torus.ofInt (Type200.k m) ![0, 0, (2 : ℤ) ^ (m + 1)] := by
    have h : Torus.b = Torus.ofInt (Type200.k m) (![0, 0, 1] : Fin 3 → ℤ) := by
      rw [Torus.ofInt_eq_zsmul_gens]
      simp [Torus.b]
    rw [h, ← Torus.ofInt_zsmul]
    congr 1
    funext i
    fin_cases i <;> simp
  have hfc : f (z • Torus.c) = 0 := by
    rw [hc_coord, hf_ofInt]
    apply Torus.ofInt_eq_zero_iff.mpr
    intro i
    fin_cases i <;>
      simp [Type200.ρM, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring
  have hfa : f ((2 : ℤ) ^ (m + 1) • Torus.a) =
      (2 : ℤ) ^ (m + 1) • Torus.b - (2 : ℤ) ^ (m + 1) • Torus.a := by
    calc f ((2 : ℤ) ^ (m + 1) • Torus.a)
        = Torus.ofInt (Type200.k m)
            (Type200.ρM *ᵥ (![0, (2 : ℤ) ^ (m + 1), 0] : Fin 3 → ℤ) -
              ![0, (2 : ℤ) ^ (m + 1), 0]) := by
          rw [ha_coord, hf_ofInt]
      _ = Torus.ofInt (Type200.k m) ![0, 0, (2 : ℤ) ^ (m + 1)] -
          Torus.ofInt (Type200.k m) ![0, (2 : ℤ) ^ (m + 1), 0] := by
          rw [← Torus.ofInt_sub]
          congr 1
          funext i
          fin_cases i <;>
            simp [Type200.ρM, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
      _ = (2 : ℤ) ^ (m + 1) • Torus.b - (2 : ℤ) ^ (m + 1) • Torus.a := by
          rw [hb_coord, ha_coord]
  have hfb : f ((2 : ℤ) ^ (m + 1) • Torus.b) =
      -((2 : ℤ) ^ (m + 1) • Torus.a) := by
    calc f ((2 : ℤ) ^ (m + 1) • Torus.b)
        = Torus.ofInt (Type200.k m)
            (Type200.ρM *ᵥ (![0, 0, (2 : ℤ) ^ (m + 1)] : Fin 3 → ℤ) -
              ![0, 0, (2 : ℤ) ^ (m + 1)]) := by
          rw [hb_coord, hf_ofInt]
      _ = -Torus.ofInt (Type200.k m) ![0, (2 : ℤ) ^ (m + 1), 0] := by
          rw [← Torus.ofInt_neg]
          apply Torus.ofInt_eq_ofInt_iff.mpr
          intro i
          fin_cases i <;>
            simp [Type200.ρM, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Type200.k]
          · rw [Int.modEq_zero_iff_dvd]
            refine dvd_neg.mpr ?_
            rw [show (2 : ℤ) ^ (m + 1) = (2 : ℤ) ^ m * 2 by rw [pow_succ]]
            exact dvd_mul_right _ _
          · rw [Int.modEq_zero_iff_dvd]
            have hp : (2 : ℤ) ^ (m + 2) = (2 : ℤ) ^ (m + 1) + (2 : ℤ) ^ (m + 1) := by
              rw [show m + 2 = (m + 1) + 1 by omega, pow_succ]
              ring
            rw [hp]
            rw [show -((2 : ℤ) ^ (m + 1)) - (2 : ℤ) ^ (m + 1) =
              -((2 : ℤ) ^ (m + 1) + (2 : ℤ) ^ (m + 1)) by ring]
            exact dvd_neg.mpr (dvd_refl _)
      _ = -((2 : ℤ) ^ (m + 1) • Torus.a) := by rw [ha_coord]
  apply le_antisymm
  · rw [AddSubgroup.map_le_iff_le_comap, AddSubgroup.closure_le]
    intro x hx
    change f x ∈ W
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · rw [hfc]; exact W.zero_mem
    · rw [hfa]
      exact W.sub_mem (AddSubgroup.subset_closure (by simp))
        (AddSubgroup.subset_closure (by simp))
    · rw [hfb]
      exact W.neg_mem (AddSubgroup.subset_closure (by simp))
  · rw [AddSubgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    have h2ma_mem : (2 : ℤ) ^ (m + 1) • Torus.a ∈ Ω :=
      AddSubgroup.subset_closure (by simp)
    have h2mb_mem : (2 : ℤ) ^ (m + 1) • Torus.b ∈ Ω :=
      AddSubgroup.subset_closure (by simp)
    rcases hx with rfl | rfl
    · refine AddSubgroup.mem_map.mpr
        ⟨-((2 : ℤ) ^ (m + 1) • Torus.b), Ω.neg_mem h2mb_mem, ?_⟩
      rw [map_neg, hfb, neg_neg]
    · refine AddSubgroup.mem_map.mpr
        ⟨(2 : ℤ) ^ (m + 1) • Torus.a - (2 : ℤ) ^ (m + 1) • Torus.b,
          Ω.sub_mem h2ma_mem h2mb_mem, ?_⟩
      rw [map_sub, hfa, hfb]
      abel


theorem map_rho_sub_omegaOne_type200 (m : ℕ) (hm : 2 ≤ m) :
    AddSubgroup.map ((Type200.action m).φρ - AddMonoidHom.id (Torus (Type200.k m)))
      (AddSubgroup.closure ({ (2 : ℤ) • Torus.c, (2 : ℤ) ^ (m + 1) • Torus.a,
        (2 : ℤ) ^ (m + 1) • Torus.b } : Set (Torus (Type200.k m))))
      = AddSubgroup.closure ({ (2 : ℤ) ^ (m + 1) • Torus.a,
        (2 : ℤ) ^ (m + 1) • Torus.b } : Set (Torus (Type200.k m))) :=
  map_rho_sub_omegaOne_type200_coeff m hm 2

theorem map_rho_sub_omegaOne_type200_omega (m : ℕ) (hm : 2 ≤ m) :
    AddSubgroup.map ((Type200.action m).φρ - AddMonoidHom.id (Torus (Type200.k m)))
      (AddSubgroup.closure ({ (2 : ℤ) ^ (m - 1) • Torus.c,
        (2 : ℤ) ^ (m + 1) • Torus.a,
        (2 : ℤ) ^ (m + 1) • Torus.b } : Set (Torus (Type200.k m))))
      = AddSubgroup.closure ({ (2 : ℤ) ^ (m + 1) • Torus.a,
        (2 : ℤ) ^ (m + 1) • Torus.b } : Set (Torus (Type200.k m))) :=
  map_rho_sub_omegaOne_type200_coeff m hm ((2 : ℤ) ^ (m - 1))

theorem map_rho_sub_omegaOne_familyTwo (Z : StrothDatum X)
    (hk : ∀ i, 2 ≤ Z.τ.k i) (hrel : Z.τ.m + 2 = Z.τ.n) :
    AddSubgroup.map
        (matAct Z.τ.k Z.τ.action.ρ Z.τ.action.compat_ρ -
          AddMonoidHom.id (Torus Z.τ.k))
        (AddSubgroup.closure ({(2 : ℤ) • (Torus.c : Torus Z.τ.k),
          (2 : ℤ) ^ (Z.τ.m + 1) • (Torus.a : Torus Z.τ.k),
          (2 : ℤ) ^ (Z.τ.m + 1) • (Torus.b : Torus Z.τ.k)} : Set (Torus Z.τ.k))) =
      AddSubgroup.closure ({(2 : ℤ) ^ (Z.τ.m + 1) • (Torus.a : Torus Z.τ.k),
        (2 : ℤ) ^ (Z.τ.m + 1) • (Torus.b : Torus Z.τ.k)} :
          Set (Torus Z.τ.k)) := by
  obtain ⟨D, hAD, hDS, τ, dataD, hL, hcentS⟩ := Z
  rcases familyTwo_disjunction τ hrel with
    ⟨m, hτ⟩ | ⟨m, hτ⟩ | ⟨m, hm, hτ⟩ | ⟨m, hm, hτ⟩ |
      ⟨s, hs, hτ⟩ | ⟨s, hs, hτ⟩ | ⟨s, hs, hτ⟩ | ⟨s, hs, hτ⟩
  · subst hτ
    have hm2 : 2 ≤ m := by simpa [StrothTypeIndex.k, Type200.k] using hk 0
    have h := map_rho_sub_omegaOne_type200 m hm2
    convert h using 2 <;> rfl
  · subst hτ
    have hm2 : 2 ≤ m := by simpa [StrothTypeIndex.k, Type201.k] using hk 0
    have h := map_rho_sub_omegaOne_type200 m hm2
    convert h using 2 <;> rfl
  · subst hτ
    have h := map_rho_sub_omegaOne_type200 m hm
    convert h using 2 <;> rfl
  · subst hτ
    have h := map_rho_sub_omegaOne_type200 m hm
    convert h using 2 <;> rfl
  · subst hτ
    have h := map_rho_sub_omegaOne_type200 (s + 2) (by omega)
    convert h using 2 <;> rfl
  · subst hτ
    have h := map_rho_sub_omegaOne_type200 (s + 2) (by omega)
    convert h using 2 <;> rfl
  · subst hτ
    have h := map_rho_sub_omegaOne_type200 (s + 2) (by omega)
    convert h using 2 <;> rfl
  · subst hτ
    have h := map_rho_sub_omegaOne_type200 (s + 2) (by omega)
    convert h using 2 <;> rfl

theorem map_rho_sub_omegaOne_familyTwo_omega (Z : StrothDatum X)
    (hk : ∀ i, 2 ≤ Z.τ.k i) (hrel : Z.τ.m + 2 = Z.τ.n) :
    AddSubgroup.map
        (matAct Z.τ.k Z.τ.action.ρ Z.τ.action.compat_ρ -
          AddMonoidHom.id (Torus Z.τ.k))
        (AddSubgroup.closure ({(2 : ℤ) ^ (Z.τ.m - 1) • (Torus.c : Torus Z.τ.k),
          (2 : ℤ) ^ (Z.τ.m + 1) • (Torus.a : Torus Z.τ.k),
          (2 : ℤ) ^ (Z.τ.m + 1) • (Torus.b : Torus Z.τ.k)} : Set (Torus Z.τ.k))) =
      AddSubgroup.closure ({(2 : ℤ) ^ (Z.τ.m + 1) • (Torus.a : Torus Z.τ.k),
        (2 : ℤ) ^ (Z.τ.m + 1) • (Torus.b : Torus Z.τ.k)} :
          Set (Torus Z.τ.k)) := by
  obtain ⟨D, hAD, hDS, τ, dataD, hL, hcentS⟩ := Z
  rcases familyTwo_disjunction τ hrel with
    ⟨m, hτ⟩ | ⟨m, hτ⟩ | ⟨m, hm, hτ⟩ | ⟨m, hm, hτ⟩ |
      ⟨s, hs, hτ⟩ | ⟨s, hs, hτ⟩ | ⟨s, hs, hτ⟩ | ⟨s, hs, hτ⟩
  · subst hτ
    have hm2 : 2 ≤ m := by simpa [StrothTypeIndex.k, Type200.k] using hk 0
    have h := map_rho_sub_omegaOne_type200_omega m hm2
    convert h using 2 <;> rfl
  · subst hτ
    have hm2 : 2 ≤ m := by simpa [StrothTypeIndex.k, Type201.k] using hk 0
    have h := map_rho_sub_omegaOne_type200_omega m hm2
    convert h using 2 <;> rfl
  · subst hτ
    have h := map_rho_sub_omegaOne_type200_omega m hm
    convert h using 2 <;> rfl
  · subst hτ
    have h := map_rho_sub_omegaOne_type200_omega m hm
    convert h using 2 <;> rfl
  · subst hτ
    have h := map_rho_sub_omegaOne_type200_omega (s + 2) (by omega)
    convert h using 2 <;> rfl
  · subst hτ
    have h := map_rho_sub_omegaOne_type200_omega (s + 2) (by omega)
    convert h using 2 <;> rfl
  · subst hτ
    have h := map_rho_sub_omegaOne_type200_omega (s + 2) (by omega)
    convert h using 2 <;> rfl
  · subst hτ
    have h := map_rho_sub_omegaOne_type200_omega (s + 2) (by omega)
    convert h using 2 <;> rfl

theorem closure_deviation_range_eq_of_deviation_form_familyTwo (Z : StrothDatum X)
    (F : Subgroup G) (hF : F ≤ Z.centralizerInMho) {s : G} (hsF : s ∈ F)
    (hφc : ((deviation Z s (hF hsF)
      (Additive.ofMul ⟨Z.dataD.c, Z.dataD.c.2⟩)).toMul : G) = 1)
    (hφa : ((deviation Z s (hF hsF)
      (Additive.ofMul ⟨Z.dataD.a, Z.dataD.a.2⟩)).toMul : G) =
      (Z.dataD.a : G) ^ (2 ^ (Z.τ.m + 1)))
    (hφb : ((deviation Z s (hF hsF)
      (Additive.ofMul ⟨Z.dataD.b, Z.dataD.b.2⟩)).toMul : G) =
      (Z.dataD.b : G) ^ (2 ^ (Z.τ.m + 1))) :
    Subgroup.closure
        (Set.range (fun d : Z.D =>
          ((deviation Z s (hF hsF) (Additive.ofMul d)).toMul : G))) =
      Subgroup.closure
        ({(Z.dataD.a : G) ^ (2 ^ (Z.τ.m + 1)),
          (Z.dataD.b : G) ^ (2 ^ (Z.τ.m + 1))} : Set G) := by
  classical
  let H : Subgroup G :=
    Subgroup.closure ({(Z.dataD.a : G) ^ (2 ^ (Z.τ.m + 1)),
      (Z.dataD.b : G) ^ (2 ^ (Z.τ.m + 1))} : Set G)
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro y ⟨d, rfl⟩
    change ((deviation Z s (hF hsF) (Additive.ofMul d)).toMul : G) ∈ H
    obtain ⟨i, j, l, hd⟩ := Z.dataD.exists_zpow_c_a_b d
    have hdev_mul : ∀ x y : Z.D,
        ((deviation Z s (hF hsF) (Additive.ofMul (x * y))).toMul : G) =
          ((deviation Z s (hF hsF) (Additive.ofMul x)).toMul : G) *
            ((deviation Z s (hF hsF) (Additive.ofMul y)).toMul : G) := by
      intro x y
      rw [ofMul_mul, map_add, toMul_add]
      rfl
    have hdev_zpow : ∀ (x : Z.D) (z : ℤ),
        ((deviation Z s (hF hsF) (Additive.ofMul (x ^ z))).toMul : G) =
          ((deviation Z s (hF hsF) (Additive.ofMul x)).toMul : G) ^ z := by
      intro x z
      rw [ofMul_zpow, map_zsmul, toMul_zsmul]
      rfl
    have hy : ((deviation Z s (hF hsF) (Additive.ofMul d)).toMul : G) =
        ((deviation Z s (hF hsF)
          (Additive.ofMul ⟨Z.dataD.c, Z.dataD.c.2⟩)).toMul : G) ^ i *
          ((deviation Z s (hF hsF)
            (Additive.ofMul ⟨Z.dataD.a, Z.dataD.a.2⟩)).toMul : G) ^ j *
            ((deviation Z s (hF hsF)
              (Additive.ofMul ⟨Z.dataD.b, Z.dataD.b.2⟩)).toMul : G) ^ l := by
      conv_lhs => rw [hd]
      rw [hdev_mul, hdev_mul, hdev_zpow, hdev_zpow, hdev_zpow]
    rw [hy, hφa, hφb, hφc]
    have haH : (Z.dataD.a : G) ^ (2 ^ (Z.τ.m + 1)) ∈ H :=
      Subgroup.subset_closure (by simp [H])
    have hbH : (Z.dataD.b : G) ^ (2 ^ (Z.τ.m + 1)) ∈ H :=
      Subgroup.subset_closure (by simp [H])
    simpa using H.mul_mem (H.mul_mem (H.one_mem) (H.zpow_mem haH j)) (H.zpow_mem hbH l)
  · rw [Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact Subgroup.subset_closure ⟨⟨Z.dataD.a, Z.dataD.a.2⟩, hφa⟩
    · exact Subgroup.subset_closure ⟨⟨Z.dataD.b, Z.dataD.b.2⟩, hφb⟩

theorem commutator_zpowers_s_eq_of_deviation_form_familyTwo (Z : StrothDatum X)
    (hk : ∀ i, 2 ≤ Z.τ.k i)
    (F : Subgroup G) (hF : F ≤ Z.centralizerInMho) {s : G} (hsF : s ∈ F)
    (hφc : ((deviation Z s (hF hsF)
      (Additive.ofMul ⟨Z.dataD.c, Z.dataD.c.2⟩)).toMul : G) = 1)
    (hφa : ((deviation Z s (hF hsF)
      (Additive.ofMul ⟨Z.dataD.a, Z.dataD.a.2⟩)).toMul : G) =
      (Z.dataD.a : G) ^ (2 ^ (Z.τ.m + 1)))
    (hφb : ((deviation Z s (hF hsF)
      (Additive.ofMul ⟨Z.dataD.b, Z.dataD.b.2⟩)).toMul : G) =
      (Z.dataD.b : G) ^ (2 ^ (Z.τ.m + 1))) :
    ⁅Subgroup.zpowers s, Z.D⁆ =
      Subgroup.closure ({(Z.dataD.a : G) ^ (2 ^ (Z.τ.m + 1)),
        (Z.dataD.b : G) ^ (2 ^ (Z.τ.m + 1))} : Set G) := by
  classical
  let H : Subgroup G :=
    Subgroup.closure ({(Z.dataD.a : G) ^ (2 ^ (Z.τ.m + 1)),
      (Z.dataD.b : G) ^ (2 ^ (Z.τ.m + 1))} : Set G)
  have hH : Subgroup.closure
      (Set.range (fun d : Z.D =>
        ((deviation Z s (hF hsF) (Additive.ofMul d)).toMul : G))) = H :=
    closure_deviation_range_eq_of_deviation_form_familyTwo Z F hF hsF hφc hφa hφb
  apply le_antisymm
  · have himg : ∀ d ∈ Z.D, ⁅s, d⁆ ∈ H := by
      intro d hd
      have hdval : ((deviation Z s (hF hsF) (Additive.ofMul ⟨d, hd⟩)).toMul : G) = ⁅s, d⁆ := by
        rw [deviation_apply]
        rfl
      rw [← hdval, ← hH]
      exact Subgroup.subset_closure ⟨⟨d, hd⟩, rfl⟩
    have hcomm : ∀ d ∈ Z.D, Commute s ⁅s, d⁆ := by
      intro d hd
      have hmem : ⁅s, d⁆ ∈ omegaIn 1 Z.D := by
        have h := commutator_mem_omegaIn_one_of_mem_centralizerInMho (Z := Z) (x := s) (hF hsF) hd
        simpa [commutatorElement_def] using h
      have hmho : ⁅s, d⁆ ∈ mhoOne Z.D := omegaIn_one_le_mhoOne_of_two_le_k Z hk hmem
      exact (Subgroup.mem_centralizer_iff.mp (hF hsF).2 _ hmho).symm
    exact commutator_zpowers_le_of_image himg hcomm
  · rw [Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · rw [← hφa]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers s) Z.dataD.a.2
    · rw [← hφb]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers s) Z.dataD.b.2

theorem commutator_zpowers_s_eq_familyTwo_t200 (Z : StrothDatum X)
    (hk : ∀ i, 2 ≤ Z.τ.k i) (hrel : Z.τ.m + 2 = Z.τ.n) {m : ℕ}
    (hτ : Z.τ = StrothTypeIndex.t200 m)
    (F : Subgroup G) (hDF : Z.D ≤ F) (hF : F ≤ Z.centralizerInMho)
    (hN : X.L ≤ Subgroup.normalizer (F : Set G))
    (hidx : (Z.D.subgroupOf F).index = 2)
    (hcent : F ≤ Subgroup.centralizer ((omegaIn (Z.τ.n - 2) Z.D : Subgroup G) : Set G))
    {s : G} (hsF : s ∈ F) (hsD : s ∉ Z.D) :
    ⁅Subgroup.zpowers s, Z.D⁆ =
      Subgroup.closure ({(Z.dataD.a : G) ^ (2 ^ (Z.τ.m + 1)),
        (Z.dataD.b : G) ^ (2 ^ (Z.τ.m + 1))} : Set G) := by
  obtain ⟨hφc, hφa, hφb, -⟩ :=
    deviation_form_diag_familyTwo_t200 Z hk hrel hτ F hDF hF hN hidx hcent hsF hsD
  exact commutator_zpowers_s_eq_of_deviation_form_familyTwo Z hk F hF hsF hφc hφa hφb

theorem commutator_zpowers_s_eq_familyTwo_t201 (Z : StrothDatum X)
    (hk : ∀ i, 2 ≤ Z.τ.k i) (hrel : Z.τ.m + 2 = Z.τ.n) {m : ℕ}
    (hτ : Z.τ = StrothTypeIndex.t201 m)
    (F : Subgroup G) (hDF : Z.D ≤ F) (hF : F ≤ Z.centralizerInMho)
    (hN : X.L ≤ Subgroup.normalizer (F : Set G))
    (hidx : (Z.D.subgroupOf F).index = 2)
    (hcent : F ≤ Subgroup.centralizer ((omegaIn (Z.τ.n - 2) Z.D : Subgroup G) : Set G))
    {s : G} (hsF : s ∈ F) (hsD : s ∉ Z.D) :
    ⁅Subgroup.zpowers s, Z.D⁆ =
      Subgroup.closure ({(Z.dataD.a : G) ^ (2 ^ (Z.τ.m + 1)),
        (Z.dataD.b : G) ^ (2 ^ (Z.τ.m + 1))} : Set G) := by
  obtain ⟨hφc, hφa, hφb, -⟩ :=
    deviation_form_diag_familyTwo_t201 Z hk hrel hτ F hDF hF hN hidx hcent hsF hsD
  exact commutator_zpowers_s_eq_of_deviation_form_familyTwo Z hk F hF hsF hφc hφa hφb

theorem phi_rho_sq_sub_ofInt_familyTwo (Z : StrothDatum X)
    (hrel : Z.τ.m + 2 = Z.τ.n) (v : Fin 3 → ℤ) :
    Z.τ.action.φρ (Z.τ.action.φρ (Torus.ofInt Z.τ.k v)) - Torus.ofInt Z.τ.k v =
      Torus.ofInt Z.τ.k
        (fun i => (Type200.ρM *ᵥ (Type200.ρM *ᵥ v) - v) i) := by
  rw [show Z.τ.action.φρ =
      matAct Z.τ.k Z.τ.action.ρ Z.τ.action.compat_ρ from rfl]
  rw [matAct_ofInt, matAct_ofInt]
  rw [show Z.τ.action.ρ = Type200.ρM from action_rho_eq_type200 Z.τ hrel]
  rw [← Torus.ofInt_sub]

theorem e_commutator_rho_familyTwo (Z : StrothDatum X) (x : Z.D) :
    Z.dataD.e (Additive.ofMul
        (conjBy (Subgroup.inv_mem (Subgroup.normalizer (Z.D : Set G))
      Z.dataD.ρ_mem) x * x⁻¹)) =
      (Z.τ.action.φρ - AddMonoidHom.id (Torus Z.τ.k))
        (-(Z.τ.action.φρ (Z.τ.action.φρ (Z.dataD.e (Additive.ofMul x))))) := by
  let hρinv : Z.dataD.ρ⁻¹ ∈ Subgroup.normalizer (Z.D : Set G) :=
    Subgroup.inv_mem (Subgroup.normalizer (Z.D : Set G)) Z.dataD.ρ_mem
  have hconj : conjBy Z.dataD.ρ_mem (conjBy hρinv x) = x := by
    apply Subtype.ext
    simp only [conjBy, Subtype.coe_mk]
    group
  have h1 : Z.τ.action.φρ (Z.dataD.e (Additive.ofMul
        (conjBy hρinv x))) =
      Z.dataD.e (Additive.ofMul x) := by
    rw [← Z.dataD.ρ_conj]
    rw [hconj]
  have h2 : Z.dataD.e (Additive.ofMul
        (conjBy hρinv x)) =
      Z.τ.action.φρ (Z.τ.action.φρ (Z.dataD.e (Additive.ofMul x))) := by
    have h3 : Z.τ.action.φρ (Z.τ.action.φρ (Z.τ.action.φρ
          (Z.dataD.e (Additive.ofMul
            (conjBy hρinv x))))) =
        Z.dataD.e (Additive.ofMul
          (conjBy hρinv x)) := by
      have := DFunLike.congr_fun Z.τ.action.rels.rho_cube
        (Z.dataD.e (Additive.ofMul
          (conjBy hρinv x)))
      simpa using this
    calc Z.dataD.e (Additive.ofMul
          (conjBy hρinv x))
        = Z.τ.action.φρ (Z.τ.action.φρ (Z.τ.action.φρ
            (Z.dataD.e (Additive.ofMul
              (conjBy hρinv x))))) := h3.symm
      _ = Z.τ.action.φρ (Z.τ.action.φρ (Z.dataD.e (Additive.ofMul x))) := by rw [h1]
  rw [ofMul_mul, map_add, h2, ofMul_inv, map_neg]
  rw [sub_eq_add_neg]
  rw [show Z.τ.action.φρ (Z.τ.action.φρ (Z.dataD.e (Additive.ofMul x))) +
      -Z.dataD.e (Additive.ofMul x) =
      (Z.τ.action.φρ + -AddMonoidHom.id (Torus Z.τ.k))
        (-(Z.τ.action.φρ (Z.τ.action.φρ (Z.dataD.e (Additive.ofMul x))))) from by
    rw [AddMonoidHom.add_apply, AddMonoidHom.neg_apply, AddMonoidHom.id_apply, map_neg]
    have hcube := DFunLike.congr_fun Z.τ.action.rels.rho_cube
      (Z.dataD.e (Additive.ofMul x))
    simp only [AddMonoidHom.comp_apply, AddMonoidHom.id_apply] at hcube
    rw [hcube]
    abel]

theorem phi_rho_sq_sub_two_torsion_familyTwo (Z : StrothDatum X)
    (hk : ∀ i, 2 ≤ Z.τ.k i) (hrel : Z.τ.m + 2 = Z.τ.n) (ε : Fin 3 → ℤ)
    (hε : ∀ i, ε i = 0 ∨ ε i = 1) :
    Z.τ.action.φρ (Z.τ.action.φρ
        (Torus.ofInt Z.τ.k (fun i => ε i * 2 ^ (Z.τ.k i - 1)))) -
        Torus.ofInt Z.τ.k (fun i => ε i * 2 ^ (Z.τ.k i - 1)) =
      Torus.ofInt Z.τ.k
        ![-ε 1 * (2 : ℤ) ^ (Z.τ.m + 1),
          (ε 2 - 2 * ε 1) * (2 : ℤ) ^ (Z.τ.m + 1),
          -(ε 1 + ε 2) * (2 : ℤ) ^ (Z.τ.m + 1)] := by
  have hk1 : Z.τ.k 1 = Z.τ.m + 2 := by
    rw [StrothTypeIndex.k_eq]
    simp [hrel]
  have hk2 : Z.τ.k 2 = Z.τ.m + 2 := by
    rw [StrothTypeIndex.k_two, hrel]
  set v : Fin 3 → ℤ := fun i => ε i * 2 ^ (Z.τ.k i - 1) with hv
  rw [phi_rho_sq_sub_ofInt_familyTwo Z hrel v]
  have hvec : (fun i => (Type200.ρM *ᵥ (Type200.ρM *ᵥ v) - v) i) =
      ![-ε 1 * (2 : ℤ) ^ (Z.τ.m + 1),
        (ε 2 - 2 * ε 1) * (2 : ℤ) ^ (Z.τ.m + 1),
        -(ε 1 + ε 2) * (2 : ℤ) ^ (Z.τ.m + 1)] := by
    funext i
    fin_cases i <;>
      simp [v, hk1, hk2, type200_rhoM_mulVec, Matrix.mulVec, dotProduct,
        Fin.sum_univ_three] <;> ring
  rw [hvec]

theorem e_commutator_rho_ofInt_familyTwo (Z : StrothDatum X)
    (hrel : Z.τ.m + 2 = Z.τ.n)
    (v : Fin 3 → ℤ) (y : Z.D)
    (hy : Z.dataD.e (Additive.ofMul y) = Torus.ofInt Z.τ.k v) :
    Z.dataD.e (Additive.ofMul
        (conjBy (Subgroup.inv_mem (Subgroup.normalizer (Z.D : Set G))
          Z.dataD.ρ_mem) y * y⁻¹)) =
      Torus.ofInt Z.τ.k
        (fun i => (Type200.ρM *ᵥ (Type200.ρM *ᵥ v) - v) i) := by
  have hcube := DFunLike.congr_fun Z.τ.action.rels.rho_cube
    (Z.dataD.e (Additive.ofMul y))
  simp only [AddMonoidHom.comp_apply, AddMonoidHom.id_apply] at hcube
  rw [e_commutator_rho_familyTwo]
  rw [show (Z.τ.action.φρ - AddMonoidHom.id (Torus Z.τ.k))
      (-(Z.τ.action.φρ (Z.τ.action.φρ (Z.dataD.e (Additive.ofMul y))))) =
      (Z.τ.action.φρ (Z.τ.action.φρ (Z.dataD.e (Additive.ofMul y))) -
        Z.dataD.e (Additive.ofMul y)) from by
    rw [AddMonoidHom.sub_apply, AddMonoidHom.id_apply, map_neg]
    rw [hcube]
    abel]
  rw [hy, phi_rho_sq_sub_ofInt_familyTwo Z hrel v]

theorem rho_commutator_mem_closure_familyTwo (Z : StrothDatum X)
    (hk : ∀ i, 2 ≤ Z.τ.k i) (hrel : Z.τ.m + 2 = Z.τ.n)
    {x : G} (hx : x ∈ omegaIn 1 Z.D) :
    ⁅(Z.dataD.ρ : G), x⁆ ∈
      Subgroup.closure ({(Z.dataD.a : G) ^ (2 ^ (Z.τ.m + 1)),
        (Z.dataD.b : G) ^ (2 ^ (Z.τ.m + 1))} : Set G) := by
  classical
  let H : Subgroup G :=
    Subgroup.closure ({(Z.dataD.a : G) ^ (2 ^ (Z.τ.m + 1)),
      (Z.dataD.b : G) ^ (2 ^ (Z.τ.m + 1))} : Set G)
  let W : AddSubgroup (Torus Z.τ.k) :=
    AddSubgroup.closure ({(2 : ℤ) ^ (Z.τ.m + 1) • (Torus.a : Torus Z.τ.k),
      (2 : ℤ) ^ (Z.τ.m + 1) • (Torus.b : Torus Z.τ.k)} : Set (Torus Z.τ.k))
  have hcomm : ∀ a ∈ Z.D, ∀ b ∈ Z.D, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (Z.dataD.isMulCommutative.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  obtain ⟨hxD, hx2⟩ := (mem_omegaIn_iff_of_comm hcomm).mp hx
  let d : Z.D := ⟨x, hxD⟩
  have hd2 : d * d = 1 := by
    apply Subtype.ext
    simpa [d, pow_two] using hx2
  have h2 : (2 : ℤ) • Z.dataD.e (Additive.ofMul d) = 0 := by
    rw [show (2 : ℤ) • Z.dataD.e (Additive.ofMul d) =
        Z.dataD.e (Additive.ofMul (d * d)) from by
      rw [ofMul_mul, map_add, two_zsmul]]
    rw [hd2, ofMul_one, map_zero]
  have hk1all : ∀ i, 1 ≤ Z.τ.k i := fun i => by have := hk i; omega
  obtain ⟨ε, hε, hεd⟩ := (Torus.two_zsmul_eq_zero_iff hk1all _).mp h2
  let hρinv : Z.dataD.ρ⁻¹ ∈ Subgroup.normalizer (Z.D : Set G) :=
    Subgroup.inv_mem (Subgroup.normalizer (Z.D : Set G)) Z.dataD.ρ_mem
  have hρinv_val : ((conjBy hρinv d * d⁻¹ : Z.D) : G) = ⁅(Z.dataD.ρ : G), x⁆ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, conjBy, Subtype.coe_mk,
      commutatorElement_def]
    simp only [d, Subtype.coe_mk]
    group
  have hcube := DFunLike.congr_fun Z.τ.action.rels.rho_cube
    (Z.dataD.e (Additive.ofMul d))
  simp only [AddMonoidHom.comp_apply, AddMonoidHom.id_apply] at hcube
  have heq : Z.dataD.e (Additive.ofMul (conjBy hρinv d * d⁻¹)) =
      Torus.ofInt Z.τ.k
        ![-ε 1 * (2 : ℤ) ^ (Z.τ.m + 1),
          (ε 2 - 2 * ε 1) * (2 : ℤ) ^ (Z.τ.m + 1),
          -(ε 1 + ε 2) * (2 : ℤ) ^ (Z.τ.m + 1)] := by
    rw [e_commutator_rho_familyTwo]
    rw [show (Z.τ.action.φρ - AddMonoidHom.id (Torus Z.τ.k))
        (-(Z.τ.action.φρ (Z.τ.action.φρ (Z.dataD.e (Additive.ofMul d))))) =
        (Z.τ.action.φρ (Z.τ.action.φρ (Z.dataD.e (Additive.ofMul d))) -
          Z.dataD.e (Additive.ofMul d)) from by
      rw [AddMonoidHom.sub_apply, AddMonoidHom.id_apply, map_neg]
      rw [hcube]
      abel]
    rw [hεd]
    exact phi_rho_sq_sub_two_torsion_familyTwo Z hk hrel ε hε
  have hczero : (-ε 1 * (2 : ℤ) ^ (Z.τ.m + 1)) • (Torus.c : Torus Z.τ.k) = 0 := by
    rw [← addOrderOf_dvd_iff_zsmul_eq_zero, addOrderOf_c]
    have hdm : (2 : ℤ) ^ Z.τ.m ∣ -ε 1 * (2 : ℤ) ^ (Z.τ.m + 1) := by
      rw [show (2 : ℤ) ^ (Z.τ.m + 1) = (2 : ℤ) ^ Z.τ.m * 2 by rw [pow_succ]]
      exact dvd_mul_of_dvd_right (dvd_mul_right ((2 : ℤ) ^ Z.τ.m) 2) (-ε 1)
    simpa [StrothTypeIndex.m] using hdm
  have hW : Z.dataD.e (Additive.ofMul (conjBy hρinv d * d⁻¹)) ∈ W := by
    rw [heq]
    refine AddSubgroup.mem_closure_pair.mpr
      ⟨ε 2 - 2 * ε 1, -(ε 1 + ε 2), ?_⟩
    rw [Torus.ofInt_eq_zsmul_gens]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Pi.zero_apply, zero_smul, zero_add]
    rw [hczero, zero_add]
    rw [show (ε 2 - 2 * ε 1) •
        ((2 : ℤ) ^ (Z.τ.m + 1) • (Torus.a : Torus Z.τ.k)) =
        ((ε 2 - 2 * ε 1) * (2 : ℤ) ^ (Z.τ.m + 1)) • Torus.a from by
      rw [← mul_zsmul']; ring]
    rw [show (-(ε 1 + ε 2)) •
        ((2 : ℤ) ^ (Z.τ.m + 1) • (Torus.b : Torus Z.τ.k)) =
        (-(ε 1 + ε 2) * (2 : ℤ) ^ (Z.τ.m + 1)) • Torus.b from by
      rw [← mul_zsmul']; ring]
  have hmem : ⁅(Z.dataD.ρ : G), x⁆ ∈ H := by
    rw [← hρinv_val]
    obtain ⟨p, q, hpq⟩ := AddSubgroup.mem_closure_pair.mp hW
    set g : Z.D := ((⟨Z.dataD.a, Z.dataD.a.2⟩ : Z.D) ^ ((2 : ℕ) ^ (Z.τ.m + 1))) ^ p *
        ((⟨Z.dataD.b, Z.dataD.b.2⟩ : Z.D) ^ ((2 : ℕ) ^ (Z.τ.m + 1))) ^ q with hg_def
    have hg_e : Z.dataD.e (Additive.ofMul g) =
        p • ((2 : ℤ) ^ (Z.τ.m + 1) • (Torus.a : Torus Z.τ.k)) +
          q • ((2 : ℤ) ^ (Z.τ.m + 1) • (Torus.b : Torus Z.τ.k)) := by
      rw [hg_def, ofMul_mul, map_add, ofMul_zpow, ofMul_zpow, map_zsmul, map_zsmul]
      rw [Z.dataD.e_pow, Z.dataD.e_pow, Z.dataD.e_a, Z.dataD.e_b]
      rw [show ((2 : ℕ) ^ (Z.τ.m + 1)) • (Torus.a : Torus Z.τ.k) =
          ((2 : ℤ) ^ (Z.τ.m + 1)) • Torus.a from by
        rw [← natCast_zsmul]; push_cast; ring]
      rw [show ((2 : ℕ) ^ (Z.τ.m + 1)) • (Torus.b : Torus Z.τ.k) =
          ((2 : ℤ) ^ (Z.τ.m + 1)) • Torus.b from by
        rw [← natCast_zsmul]; push_cast; ring]
    have heq_g : Z.dataD.e (Additive.ofMul (conjBy hρinv d * d⁻¹)) =
        Z.dataD.e (Additive.ofMul g) := by rw [hg_e, hpq]
    have hg_eq : (conjBy hρinv d * d⁻¹ : Z.D) = g :=
      Additive.ofMul.injective (Z.dataD.e.injective heq_g)
    rw [hg_eq]
    show (((Z.dataD.a : G) ^ ((2 : ℕ) ^ (Z.τ.m + 1))) ^ p *
        ((Z.dataD.b : G) ^ ((2 : ℕ) ^ (Z.τ.m + 1))) ^ q) ∈ H
    exact H.mul_mem
      (H.zpow_mem (Subgroup.subset_closure (Set.mem_insert _ _)) p)
      (H.zpow_mem (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))) q)
  exact hmem

theorem commutator_zpowers_rho_le_familyTwo (Z : StrothDatum X)
    (hk : ∀ i, 2 ≤ Z.τ.k i) (hrel : Z.τ.m + 2 = Z.τ.n) :
    ⁅Subgroup.zpowers (Z.dataD.ρ : G), omegaIn 1 Z.D⁆ ≤
      Subgroup.closure ({(Z.dataD.a : G) ^ (2 ^ (Z.τ.m + 1)),
        (Z.dataD.b : G) ^ (2 ^ (Z.τ.m + 1))} : Set G) := by
  apply commutator_zpowers_le_of_pow_three_central
  · intro x hx
    simpa only [inv_inv] using conj_mem_omegaIn_one (inv_mem Z.dataD.ρ_mem) hx
  · exact Subgroup.centralizer_le (omegaIn_le 1 Z.D) Z.dataD.rho_cube_mem
  · intro x hx
    exact rho_commutator_mem_closure_familyTwo Z hk hrel hx

theorem rho_commutator_a_pow_familyTwo (Z : StrothDatum X)
    (hk : ∀ i, 2 ≤ Z.τ.k i) (hrel : Z.τ.m + 2 = Z.τ.n) :
    ⁅(Z.dataD.ρ : G), (Z.dataD.a : G) ^ (2 ^ (Z.τ.m + 1))⁆ =
      ((Z.dataD.b : G)⁻¹) ^ (2 ^ (Z.τ.m + 1)) := by
  classical
  let ya : Z.D := ⟨(Z.dataD.a : G) ^ (2 ^ (Z.τ.m + 1)),
    Z.D.pow_mem Z.dataD.a.2 _⟩
  let bb : Z.D := ((⟨Z.dataD.b, Z.dataD.b.2⟩ : Z.D)⁻¹) ^ ((2 : ℕ) ^ (Z.τ.m + 1))
  let hρinv : Z.dataD.ρ⁻¹ ∈ Subgroup.normalizer (Z.D : Set G) :=
    Subgroup.inv_mem (Subgroup.normalizer (Z.D : Set G)) Z.dataD.ρ_mem
  have hval : ((conjBy hρinv ya * ya⁻¹ : Z.D) : G) =
      ⁅(Z.dataD.ρ : G), (Z.dataD.a : G) ^ (2 ^ (Z.τ.m + 1))⁆ := by
    simp only [conjBy, ya, Subtype.coe_mk, Subgroup.coe_mul, Subgroup.coe_inv,
      commutatorElement_def]
    group
  have hk1 : Z.τ.k 1 = Z.τ.m + 2 := by
    rw [StrothTypeIndex.k_eq]; simp [hrel]
  have hk1sub : Z.τ.k 1 - 1 = Z.τ.m + 1 := by
    rw [hk1]; omega
  have hya : Z.dataD.e (Additive.ofMul ya) =
      Torus.ofInt Z.τ.k (fun i => (![0, 1, 0] : Fin 3 → ℤ) i * 2 ^ (Z.τ.k i - 1)) := by
    have hya_eq : ya = (⟨Z.dataD.a, Z.dataD.a.2⟩ : Z.D) ^ ((2 : ℕ) ^ (Z.τ.m + 1)) := by
      apply Subtype.ext
      rfl
    rw [hya_eq, Z.dataD.e_pow, Z.dataD.e_a]
    rw [Torus.ofInt_eq_zsmul_gens]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Pi.zero_apply, zero_smul, zero_add, one_mul,
      hk1sub, Torus.a, gen, Pi.single_apply]
    module
  have hbb : Z.dataD.e (Additive.ofMul bb) =
      Torus.ofInt Z.τ.k ![0, 0, -(2 : ℤ) ^ (Z.τ.m + 1)] := by
    have hbb_eq : bb = ((⟨Z.dataD.b, Z.dataD.b.2⟩ : Z.D)⁻¹) ^ ((2 : ℕ) ^ (Z.τ.m + 1)) := by
      apply Subtype.ext
      rfl
    rw [hbb_eq, Z.dataD.e_pow, ofMul_inv, map_neg, Z.dataD.e_b]
    rw [Torus.ofInt_eq_zsmul_gens]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Pi.zero_apply, zero_smul, zero_add,
      Torus.b, gen, Pi.single_apply]
    module
  have heq : Z.dataD.e (Additive.ofMul (conjBy hρinv ya * ya⁻¹)) =
      Z.dataD.e (Additive.ofMul bb) := by
    rw [e_commutator_rho_ofInt_familyTwo Z hrel
      (fun i => (![0, 1, 0] : Fin 3 → ℤ) i * 2 ^ (Z.τ.k i - 1)) ya hya, hbb]
    apply Torus.ofInt_eq_ofInt_iff.mpr
    intro i
    fin_cases i
    · simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons, type200_rhoM_mulVec, hk1,
        Matrix.mulVec, dotProduct, Fin.sum_univ_three]
      rw [Int.modEq_zero_iff_dvd]
      exact dvd_neg.mpr (pow_dvd_pow (2 : ℤ) (by omega : Z.τ.m ≤ Z.τ.m + 1))
    · simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons, type200_rhoM_mulVec, hk1,
        Matrix.mulVec, dotProduct, Fin.sum_univ_three]
      rw [Int.modEq_zero_iff_dvd]
      refine ⟨-1, ?_⟩
      rw [show (2 : ℤ) ^ (Z.τ.m + 2) =
          (2 : ℤ) ^ (Z.τ.m + 1) + (2 : ℤ) ^ (Z.τ.m + 1) by
        rw [show Z.τ.m + 2 = (Z.τ.m + 1) + 1 by omega, pow_succ]; ring]
      ring
    · simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons, type200_rhoM_mulVec, hk1,
        Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  have hEqD : (conjBy hρinv ya * ya⁻¹ : Z.D) = bb :=
    Additive.ofMul.injective (Z.dataD.e.injective heq)
  rw [← hval, hEqD]
  rfl

theorem rho_commutator_ab_pow_familyTwo (Z : StrothDatum X)
    (hk : ∀ i, 2 ≤ Z.τ.k i) (hrel : Z.τ.m + 2 = Z.τ.n) :
    ⁅(Z.dataD.ρ : G),
        (Z.dataD.a : G) ^ (2 ^ (Z.τ.m + 1)) *
          (Z.dataD.b : G) ^ (2 ^ (Z.τ.m + 1))⁆ =
      ((Z.dataD.a : G)⁻¹) ^ (2 ^ (Z.τ.m + 1)) := by
  classical
  let ya : Z.D := ⟨(Z.dataD.a : G) ^ (2 ^ (Z.τ.m + 1)),
    Z.D.pow_mem Z.dataD.a.2 _⟩
  let yb : Z.D := ⟨(Z.dataD.b : G) ^ (2 ^ (Z.τ.m + 1)),
    Z.D.pow_mem Z.dataD.b.2 _⟩
  let y2 : Z.D := ya * yb
  let aa : Z.D := ((⟨Z.dataD.a, Z.dataD.a.2⟩ : Z.D)⁻¹) ^ ((2 : ℕ) ^ (Z.τ.m + 1))
  let hρinv : Z.dataD.ρ⁻¹ ∈ Subgroup.normalizer (Z.D : Set G) :=
    Subgroup.inv_mem (Subgroup.normalizer (Z.D : Set G)) Z.dataD.ρ_mem
  have hval : ((conjBy hρinv y2 * y2⁻¹ : Z.D) : G) =
      ⁅(Z.dataD.ρ : G),
        (Z.dataD.a : G) ^ (2 ^ (Z.τ.m + 1)) *
          (Z.dataD.b : G) ^ (2 ^ (Z.τ.m + 1))⁆ := by
    simp only [conjBy, y2, ya, yb, Subtype.coe_mk, Subgroup.coe_mul, Subgroup.coe_inv,
      commutatorElement_def]
    group
  have hk1 : Z.τ.k 1 = Z.τ.m + 2 := by
    rw [StrothTypeIndex.k_eq]; simp [hrel]
  have hk2 : Z.τ.k 2 = Z.τ.m + 2 := by
    rw [StrothTypeIndex.k_two, hrel]
  have hk1sub : Z.τ.k 1 - 1 = Z.τ.m + 1 := by
    rw [hk1]; omega
  have hk2sub : Z.τ.k 2 - 1 = Z.τ.m + 1 := by
    rw [hk2]; omega
  have hy2 : Z.dataD.e (Additive.ofMul y2) =
      Torus.ofInt Z.τ.k (fun i => (![0, 1, 1] : Fin 3 → ℤ) i * 2 ^ (Z.τ.k i - 1)) := by
    have hya_eq : ya = (⟨Z.dataD.a, Z.dataD.a.2⟩ : Z.D) ^ ((2 : ℕ) ^ (Z.τ.m + 1)) := by
      apply Subtype.ext
      rfl
    have hyb_eq : yb = (⟨Z.dataD.b, Z.dataD.b.2⟩ : Z.D) ^ ((2 : ℕ) ^ (Z.τ.m + 1)) := by
      apply Subtype.ext
      rfl
    rw [show y2 = ya * yb from rfl, ofMul_mul, map_add,
      hya_eq, hyb_eq, Z.dataD.e_pow, Z.dataD.e_pow, Z.dataD.e_a, Z.dataD.e_b]
    rw [Torus.ofInt_eq_zsmul_gens]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Pi.zero_apply, zero_smul, zero_add, one_mul,
      hk1sub, hk2sub, Torus.a, Torus.b, gen, Pi.single_apply]
    module
  have haa : Z.dataD.e (Additive.ofMul aa) =
      Torus.ofInt Z.τ.k ![0, -(2 : ℤ) ^ (Z.τ.m + 1), 0] := by
    have haa_eq : aa = ((⟨Z.dataD.a, Z.dataD.a.2⟩ : Z.D)⁻¹) ^
        ((2 : ℕ) ^ (Z.τ.m + 1)) := by
      apply Subtype.ext
      rfl
    rw [haa_eq, Z.dataD.e_pow, ofMul_inv, map_neg, Z.dataD.e_a]
    rw [Torus.ofInt_eq_zsmul_gens]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Pi.zero_apply, zero_smul, zero_add,
      Torus.a, gen, Pi.single_apply]
    module
  have heq : Z.dataD.e (Additive.ofMul (conjBy hρinv y2 * y2⁻¹)) =
      Z.dataD.e (Additive.ofMul aa) := by
    rw [e_commutator_rho_ofInt_familyTwo Z hrel
      (fun i => (![0, 1, 1] : Fin 3 → ℤ) i * 2 ^ (Z.τ.k i - 1)) y2 hy2, haa]
    apply Torus.ofInt_eq_ofInt_iff.mpr
    intro i
    fin_cases i
    · simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons, type200_rhoM_mulVec, hk1, hk2,
        Matrix.mulVec, dotProduct, Fin.sum_univ_three]
      rw [Int.modEq_zero_iff_dvd]
      exact dvd_neg.mpr (pow_dvd_pow (2 : ℤ) (by omega : Z.τ.m ≤ Z.τ.m + 1))
    · simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons, type200_rhoM_mulVec, hk1, hk2,
        Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    · simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons, type200_rhoM_mulVec, hk1, hk2,
        Matrix.mulVec, dotProduct, Fin.sum_univ_three]
      rw [Int.modEq_zero_iff_dvd]
      refine ⟨-1, ?_⟩
      rw [show (2 : ℤ) ^ (Z.τ.m + 2) =
          (2 : ℤ) ^ (Z.τ.m + 1) + (2 : ℤ) ^ (Z.τ.m + 1) by
        rw [show Z.τ.m + 2 = (Z.τ.m + 1) + 1 by omega, pow_succ]; ring]
      ring
  have hEqD : (conjBy hρinv y2 * y2⁻¹ : Z.D) = aa :=
    Additive.ofMul.injective (Z.dataD.e.injective heq)
  rw [← hval, hEqD]
  rfl

theorem omegaIn_a_pow_familyTwo (Z : StrothDatum X)
    (hk : ∀ i, 2 ≤ Z.τ.k i) (hrel : Z.τ.m + 2 = Z.τ.n) :
    (Z.dataD.a : G) ^ (2 ^ (Z.τ.m + 1)) ∈ omegaIn 1 Z.D := by
  classical
  let ya : Z.D := ⟨(Z.dataD.a : G) ^ (2 ^ (Z.τ.m + 1)),
    Z.D.pow_mem Z.dataD.a.2 _⟩
  have hk1 : Z.τ.k 1 = Z.τ.m + 2 := by
    rw [StrothTypeIndex.k_eq]; simp [hrel]
  have hk1sub : Z.τ.k 1 - 1 = Z.τ.m + 1 := by
    rw [hk1]; omega
  have hya : Z.dataD.e (Additive.ofMul ya) =
      Torus.ofInt Z.τ.k (fun i => (![0, 1, 0] : Fin 3 → ℤ) i * 2 ^ (Z.τ.k i - 1)) := by
    have hya_eq : ya = (⟨Z.dataD.a, Z.dataD.a.2⟩ : Z.D) ^ ((2 : ℕ) ^ (Z.τ.m + 1)) := by
      apply Subtype.ext
      rfl
    rw [hya_eq, Z.dataD.e_pow, Z.dataD.e_a]
    rw [Torus.ofInt_eq_zsmul_gens]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Pi.zero_apply, zero_smul, zero_add, one_mul,
      hk1sub, Torus.a, gen, Pi.single_apply]
    module
  have hk1all : ∀ i, 1 ≤ Z.τ.k i := fun i => by have := hk i; omega
  have h2 : (2 : ℤ) • Z.dataD.e (Additive.ofMul ya) = 0 := by
    rw [hya]
    exact (Torus.two_zsmul_eq_zero_iff hk1all _).mpr
      ⟨![0, 1, 0], by intro i; fin_cases i <;> simp, rfl⟩
  have hya2 : ya * ya = 1 := by
    apply Additive.ofMul.injective
    apply Z.dataD.e.injective
    rw [show Additive.ofMul (ya * ya) = Additive.ofMul ya + Additive.ofMul ya from by
      rw [ofMul_mul]]
    rw [map_add, ← two_zsmul, h2, ofMul_one, map_zero]
  simpa [ya] using mem_omegaIn_one_of_mul_self ya.2 (congrArg Subtype.val hya2)

theorem omegaIn_b_pow_familyTwo (Z : StrothDatum X)
    (hk : ∀ i, 2 ≤ Z.τ.k i) (hrel : Z.τ.m + 2 = Z.τ.n) :
    (Z.dataD.b : G) ^ (2 ^ (Z.τ.m + 1)) ∈ omegaIn 1 Z.D := by
  classical
  let yb : Z.D := ⟨(Z.dataD.b : G) ^ (2 ^ (Z.τ.m + 1)),
    Z.D.pow_mem Z.dataD.b.2 _⟩
  have hk2 : Z.τ.k 2 = Z.τ.m + 2 := by
    rw [StrothTypeIndex.k_two, hrel]
  have hk2sub : Z.τ.k 2 - 1 = Z.τ.m + 1 := by
    rw [hk2]; omega
  have hyb : Z.dataD.e (Additive.ofMul yb) =
      Torus.ofInt Z.τ.k (fun i => (![0, 0, 1] : Fin 3 → ℤ) i * 2 ^ (Z.τ.k i - 1)) := by
    have hyb_eq : yb = (⟨Z.dataD.b, Z.dataD.b.2⟩ : Z.D) ^ ((2 : ℕ) ^ (Z.τ.m + 1)) := by
      apply Subtype.ext
      rfl
    rw [hyb_eq, Z.dataD.e_pow, Z.dataD.e_b]
    rw [Torus.ofInt_eq_zsmul_gens]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Pi.zero_apply, zero_smul, zero_add, one_mul,
      hk2sub, Torus.b, gen, Pi.single_apply]
    module
  have hk1all : ∀ i, 1 ≤ Z.τ.k i := fun i => by have := hk i; omega
  have h2 : (2 : ℤ) • Z.dataD.e (Additive.ofMul yb) = 0 := by
    rw [hyb]
    exact (Torus.two_zsmul_eq_zero_iff hk1all _).mpr
      ⟨![0, 0, 1], by intro i; fin_cases i <;> simp, rfl⟩
  have hyb2 : yb * yb = 1 := by
    apply Additive.ofMul.injective
    apply Z.dataD.e.injective
    rw [show Additive.ofMul (yb * yb) = Additive.ofMul yb + Additive.ofMul yb from by
      rw [ofMul_mul]]
    rw [map_add, ← two_zsmul, h2, ofMul_one, map_zero]
  simpa [yb] using mem_omegaIn_one_of_mul_self yb.2 (congrArg Subtype.val hyb2)

theorem omegaIn_ab_pow_familyTwo (Z : StrothDatum X)
    (hk : ∀ i, 2 ≤ Z.τ.k i) (hrel : Z.τ.m + 2 = Z.τ.n) :
    ((Z.dataD.a : G) ^ (2 ^ (Z.τ.m + 1)) *
      (Z.dataD.b : G) ^ (2 ^ (Z.τ.m + 1))) ∈ omegaIn 1 Z.D :=
  (omegaIn 1 Z.D).mul_mem (omegaIn_a_pow_familyTwo Z hk hrel)
    (omegaIn_b_pow_familyTwo Z hk hrel)

theorem commutator_zpowers_rho_ge_familyTwo (Z : StrothDatum X)
    (hk : ∀ i, 2 ≤ Z.τ.k i) (hrel : Z.τ.m + 2 = Z.τ.n) :
    Subgroup.closure ({(Z.dataD.a : G) ^ (2 ^ (Z.τ.m + 1)),
        (Z.dataD.b : G) ^ (2 ^ (Z.τ.m + 1))} : Set G) ≤
      ⁅Subgroup.zpowers (Z.dataD.ρ : G), omegaIn 1 Z.D⁆ := by
  rw [Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · have h := Subgroup.commutator_mem_commutator
      (Subgroup.mem_zpowers (Z.dataD.ρ : G)) (omegaIn_ab_pow_familyTwo Z hk hrel)
    rw [rho_commutator_ab_pow_familyTwo Z hk hrel] at h
    have hinv := Subgroup.inv_mem _ h
    simpa [inv_pow] using hinv
  · have h := Subgroup.commutator_mem_commutator
      (Subgroup.mem_zpowers (Z.dataD.ρ : G)) (omegaIn_a_pow_familyTwo Z hk hrel)
    rw [rho_commutator_a_pow_familyTwo Z hk hrel] at h
    have hinv := Subgroup.inv_mem _ h
    simpa [inv_pow] using hinv

theorem commutator_zpowers_rho_eq_familyTwo (Z : StrothDatum X)
    (hk : ∀ i, 2 ≤ Z.τ.k i) (hrel : Z.τ.m + 2 = Z.τ.n) :
    ⁅Subgroup.zpowers (Z.dataD.ρ : G), omegaIn 1 Z.D⁆ =
      Subgroup.closure ({(Z.dataD.a : G) ^ (2 ^ (Z.τ.m + 1)),
        (Z.dataD.b : G) ^ (2 ^ (Z.τ.m + 1))} : Set G) :=
  le_antisymm (commutator_zpowers_rho_le_familyTwo Z hk hrel)
    (commutator_zpowers_rho_ge_familyTwo Z hk hrel)

theorem exists_sq_eq_c_and_commutator_familyTwo_t200 (Z : StrothDatum X)
    (hk : ∀ i, 2 ≤ Z.τ.k i) (hrel : Z.τ.m + 2 = Z.τ.n) {m : ℕ}
    (hτ : Z.τ = StrothTypeIndex.t200 m)
    (F : Subgroup G) (hDF : Z.D ≤ F) (hF : F ≤ Z.centralizerInMho)
    (hN : X.L ≤ Subgroup.normalizer (F : Set G))
    (hidx : (Z.D.subgroupOf F).index = 2)
    (hcent : F ≤ Subgroup.centralizer ((omegaIn (Z.τ.n - 2) Z.D : Subgroup G) : Set G)) :
    ∃ s : G, s ∈ F ∧ s ∉ Z.D ∧ s * s = (Z.dataD.c : G) ∧
      ⁅Subgroup.zpowers s, Z.D⁆ =
        Subgroup.closure ({(Z.dataD.a : G) ^ (2 ^ (Z.τ.m + 1)),
          (Z.dataD.b : G) ^ (2 ^ (Z.τ.m + 1))} : Set G) := by
  obtain ⟨s, hsF, hsD, hsq⟩ :=
    exists_sq_eq_c_of_index_two_of_centOmega_familyTwo_t200 Z hk hrel hτ F hDF hF hN hidx hcent
  exact ⟨s, hsF, hsD, hsq,
    commutator_zpowers_s_eq_familyTwo_t200 Z hk hrel hτ F hDF hF hN hidx hcent hsF hsD⟩

theorem exists_sq_eq_c_and_commutator_familyTwo_t201 (Z : StrothDatum X)
    (hk : ∀ i, 2 ≤ Z.τ.k i) (hrel : Z.τ.m + 2 = Z.τ.n) {m : ℕ}
    (hτ : Z.τ = StrothTypeIndex.t201 m)
    (F : Subgroup G) (hDF : Z.D ≤ F) (hF : F ≤ Z.centralizerInMho)
    (hN : X.L ≤ Subgroup.normalizer (F : Set G))
    (hidx : (Z.D.subgroupOf F).index = 2)
    (hcent : F ≤ Subgroup.centralizer ((omegaIn (Z.τ.n - 2) Z.D : Subgroup G) : Set G)) :
    ∃ s : G, s ∈ F ∧ s ∉ Z.D ∧ s * s = (Z.dataD.c : G) ∧
      ⁅Subgroup.zpowers s, Z.D⁆ =
        Subgroup.closure ({(Z.dataD.a : G) ^ (2 ^ (Z.τ.m + 1)),
          (Z.dataD.b : G) ^ (2 ^ (Z.τ.m + 1))} : Set G) := by
  obtain ⟨s, hsF, hsD, hsq⟩ :=
    exists_sq_eq_c_of_index_two_of_centOmega_familyTwo_t201 Z hk hrel hτ F hDF hF hN hidx hcent
  exact ⟨s, hsF, hsD, hsq,
    commutator_zpowers_s_eq_familyTwo_t201 Z hk hrel hτ F hDF hF hN hidx hcent hsF hsD⟩

end CFSG.CGT.Stroth77

end
