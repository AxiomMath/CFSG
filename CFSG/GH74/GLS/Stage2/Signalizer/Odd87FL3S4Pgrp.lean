module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL3S4Defs
public import CFSG.GH74.KGroups.L3EpsOrder

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups commutatorElement

@[expose] def conjOnHomOfNormalizing {G : Type*} [Group G] (Y H : Subgroup G) (hH : ∀ h ∈ H, ∀ y ∈ Y, h * y * h⁻¹ ∈ Y) :
    H →* MulAut Y where
  toFun h :=
    { toFun := fun y => ⟨h * y * h⁻¹, hH h h.2 y y.2⟩
      invFun := fun y => ⟨h⁻¹ * y * h, by simpa using hH (h⁻¹ : G) (inv_mem h.2) y y.2⟩
      left_inv := fun y => Subtype.ext (by simp [mul_assoc])
      right_inv := fun y => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun x y => Subtype.ext (by simp [mul_assoc]) }
  map_one' := by ext; simp
  map_mul' a b := by ext y; simp [mul_assoc]

theorem comm_mul_comm_of_cyclic {G : Type*} [Group G] (Y H : Subgroup G) [IsCyclic Y]
    (hH : ∀ h ∈ H, ∀ y ∈ Y, h * y * h⁻¹ ∈ Y) {a b : G} (ha : a ∈ H) (hb : b ∈ H) {y : G}
    (hy : y ∈ Y) : ⁅a, b⁆ * y = y * ⁅a, b⁆ := by
  set κ := conjOnHomOfNormalizing Y H hH with hκ
  have hcomm : ∀ x z : H, κ x * κ z = κ z * κ x := by
    intro x z
    apply (IsCyclic.mulAutMulEquiv Y).injective
    rw [map_mul, map_mul, mul_comm]
  have h1 : κ ⁅(⟨a, ha⟩ : H), (⟨b, hb⟩ : H)⁆ = 1 := by
    rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv, hcomm ⟨a, ha⟩ ⟨b, hb⟩]
    simp [mul_assoc]
  have h2 := congrArg (fun φ : MulAut Y => ((φ ⟨y, hy⟩ : Y) : G)) h1
  simp only [hκ, conjOnHomOfNormalizing, MonoidHom.coe_mk, OneHom.coe_mk, MulAut.one_apply] at h2
  have h3 : (⁅a, b⁆ : G) * y * (⁅a, b⁆ : G)⁻¹ = y := h2
  exact mul_inv_eq_iff_eq_mul.1 h3



section Vec

variable {F : Type} [Field F]

theorem s4Da_mulVec (v : Fin 3 → F) :
    ((s4Da : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ v = ![v 0, -v 1, -v 2] := by
  funext i
  fin_cases i <;> simp [coe_s4Da, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem s4Db_mulVec (v : Fin 3 → F) :
    ((s4Db : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ v = ![-v 0, v 1, -v 2] := by
  funext i
  fin_cases i <;> simp [coe_s4Db, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem s4P_mulVec (v : Fin 3 → F) :
    ((s4P : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ v = ![v 2, v 0, v 1] := by
  funext i
  fin_cases i <;> simp [coe_s4P, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem s4P_e0 : ((s4P : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ (Pi.single 0 1 : Fin 3 → F) = Pi.single 1 1 := by
  rw [s4P_mulVec]
  funext i
  fin_cases i <;> simp

theorem s4P_e1 : ((s4P : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ (Pi.single 1 1 : Fin 3 → F) = Pi.single 2 1 := by
  rw [s4P_mulVec]
  funext i
  fin_cases i <;> simp

theorem s4P_e2 : ((s4P : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ (Pi.single 2 1 : Fin 3 → F) = Pi.single 0 1 := by
  rw [s4P_mulVec]
  funext i
  fin_cases i <;> simp

theorem s4_eq_top_of_invariant (h2 : (2 : F) ≠ 0) (W : Submodule F (Fin 3 → F))
    (hDa : ∀ w ∈ W, ((s4Da : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ w ∈ W)
    (hDb : ∀ w ∈ W, ((s4Db : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ w ∈ W)
    (hP : ∀ w ∈ W, ((s4P : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ w ∈ W) {v : Fin 3 → F}
    (hv : v ∈ W) (hv0 : v ≠ 0) : W = ⊤ := by
  have c0 : v 0 • (Pi.single 0 1 : Fin 3 → F) ∈ W := by
    have h := W.smul_mem (2⁻¹ : F) (W.add_mem hv (hDa v hv))
    convert h using 1
    rw [s4Da_mulVec]
    funext i
    fin_cases i <;> simp [Matrix.vecHead, Matrix.vecTail]
    rw [← two_mul, inv_mul_cancel_left₀ h2]
  have c1 : v 1 • (Pi.single 1 1 : Fin 3 → F) ∈ W := by
    have h := W.smul_mem (2⁻¹ : F) (W.add_mem hv (hDb v hv))
    convert h using 1
    rw [s4Db_mulVec]
    funext i
    fin_cases i <;> simp [Matrix.vecHead, Matrix.vecTail]
    rw [← two_mul, inv_mul_cancel_left₀ h2]
  have c2 : v 2 • (Pi.single 2 1 : Fin 3 → F) ∈ W := by
    have h := W.sub_mem (W.sub_mem hv c0) c1
    convert h using 1
    funext i
    fin_cases i <;> simp
  have hex : (Pi.single 0 1 : Fin 3 → F) ∈ W ∨ (Pi.single 1 1 : Fin 3 → F) ∈ W ∨
      (Pi.single 2 1 : Fin 3 → F) ∈ W := by
    by_contra hcon
    simp only [not_or] at hcon
    have z0 : v 0 = 0 := by
      by_contra h
      have := W.smul_mem ((v 0)⁻¹) c0
      rw [inv_smul_smul₀ h] at this
      exact hcon.1 this
    have z1 : v 1 = 0 := by
      by_contra h
      have := W.smul_mem ((v 1)⁻¹) c1
      rw [inv_smul_smul₀ h] at this
      exact hcon.2.1 this
    have z2 : v 2 = 0 := by
      by_contra h
      have := W.smul_mem ((v 2)⁻¹) c2
      rw [inv_smul_smul₀ h] at this
      exact hcon.2.2 this
    apply hv0
    funext i
    fin_cases i
    · exact z0
    · exact z1
    · exact z2
  have hall : (Pi.single 0 1 : Fin 3 → F) ∈ W ∧ (Pi.single 1 1 : Fin 3 → F) ∈ W ∧
      (Pi.single 2 1 : Fin 3 → F) ∈ W := by
    rcases hex with h | h | h
    · have h1 := s4P_e0 (F := F) ▸ hP _ h
      exact ⟨h, h1, s4P_e1 (F := F) ▸ hP _ h1⟩
    · have h1 := s4P_e1 (F := F) ▸ hP _ h
      exact ⟨s4P_e2 (F := F) ▸ hP _ h1, h, h1⟩
    · have h1 := s4P_e2 (F := F) ▸ hP _ h
      exact ⟨h1, s4P_e0 (F := F) ▸ hP _ h1, h⟩
  rw [eq_top_iff]
  intro w _
  have hw : w = w 0 • (Pi.single 0 1 : Fin 3 → F) + w 1 • (Pi.single 1 1 : Fin 3 → F) +
      w 2 • (Pi.single 2 1 : Fin 3 → F) := by
    funext i
    fin_cases i <;> simp
  rw [hw]
  exact W.add_mem (W.add_mem (W.smul_mem _ hall.1) (W.smul_mem _ hall.2.1)) (W.smul_mem _ hall.2.2)

end Vec


section PThree

variable {F : Type} [Field F]

@[expose] noncomputable def s4SlAct : SL(3, F) →* Module.End F (Fin 3 → F) where
  toFun g := Matrix.toLin' (g : Matrix (Fin 3) (Fin 3) F)
  map_one' := by rw [Matrix.SpecialLinearGroup.coe_one, Matrix.toLin'_one]; rfl
  map_mul' a b := by rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.toLin'_mul]; rfl

theorem s4SlAct_apply (g : SL(3, F)) (v : Fin 3 → F) :
    s4SlAct g v = (g : Matrix (Fin 3) (Fin 3) F) *ᵥ v := by
  simp [s4SlAct, Matrix.toLin'_apply]

variable [Finite F]

theorem s4_charP_three (hF : Nat.card F = 9) : CharP F 3 := by
  have : Fintype F := Fintype.ofFinite F
  exact charP_of_card_eq_prime_pow (p := 3) (f := 2) (by rw [← Nat.card_eq_fintype_card, hF]; norm_num)

theorem pgroup_three_trivial_sl (hF : Nat.card F = 9) (R : Subgroup SL(3, F)) (hR : IsPGroup 3 R)
    (hDa : ∀ r ∈ R, (s4Da : SL(3, F))⁻¹ * r * s4Da ∈ R) (hDb : ∀ r ∈ R, (s4Db : SL(3, F))⁻¹ * r * s4Db ∈ R)
    (hP : ∀ r ∈ R, (s4P : SL(3, F))⁻¹ * r * s4P ∈ R) : R = ⊥ := by
  have hchar := s4_charP_three hF
  have h2 := two_ne_zero_of_card_nine hF
  obtain ⟨v, hv0, hvfix⟩ := CFSG.LieType.BorelTits.exists_fixed_ne_zero s4SlAct 3 R hR
  let W : Submodule F (Fin 3 → F) :=
    { carrier := {w | ∀ r ∈ R, (r : Matrix (Fin 3) (Fin 3) F) *ᵥ w = w}
      add_mem' := fun {a b} ha hb r hr => by rw [Matrix.mulVec_add, ha r hr, hb r hr]
      zero_mem' := fun r hr => by simp
      smul_mem' := fun c w hw r hr => by rw [Matrix.mulVec_smul, hw r hr] }
  have hinv : ∀ h : SL(3, F), (∀ r ∈ R, h⁻¹ * r * h ∈ R) →
      ∀ w ∈ W, (h : Matrix (Fin 3) (Fin 3) F) *ᵥ w ∈ W := by
    intro h hh w hw r hr
    calc (r : Matrix (Fin 3) (Fin 3) F) *ᵥ ((h : Matrix (Fin 3) (Fin 3) F) *ᵥ w)
        = ((r * h : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ w := by
          rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mulVec_mulVec]
      _ = ((h * (h⁻¹ * r * h) : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ w := by
          rw [show h * (h⁻¹ * r * h) = r * h by group]
      _ = (h : Matrix (Fin 3) (Fin 3) F) *ᵥ (((h⁻¹ * r * h : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ w) := by
          rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mulVec_mulVec]
      _ = (h : Matrix (Fin 3) (Fin 3) F) *ᵥ w := by rw [hw _ (hh r hr)]
  have hv : v ∈ W := fun r hr => by rw [← s4SlAct_apply]; exact hvfix r hr
  have hW : W = ⊤ := s4_eq_top_of_invariant h2 W (hinv _ hDa) (hinv _ hDb) (hinv _ hP) hv hv0
  rw [eq_bot_iff]
  intro r hr
  rw [Subgroup.mem_bot]
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  have h := (hW ▸ Submodule.mem_top : (Pi.single j 1 : Fin 3 → F) ∈ W) r hr
  have h' := congrFun h i
  rw [Matrix.mulVec_single_one] at h'
  rw [Matrix.SpecialLinearGroup.coe_one]
  simpa [Matrix.one_apply, Pi.single_apply] using h'

theorem pgroup_three_trivial (hF : Nat.card F = 9) (Y : Subgroup (projectiveSL 3 F)) (hY : IsPGroup 3 Y)
    (hnorm : ∀ g ∈ S4img F, ∀ y ∈ Y, g * y * g⁻¹ ∈ Y) : Y = ⊥ := by
  have inj := proj_injective_of_card_nine hF
  set R : Subgroup SL(3, F) := Y.comap (proj 3 F) with hRdef
  have hR : IsPGroup 3 R := by
    intro r
    obtain ⟨k, hk⟩ := hY ⟨proj 3 F r, r.2⟩
    refine ⟨k, Subtype.ext (inj ?_)⟩
    have := congrArg Subtype.val hk
    simpa using this
  have hconj : ∀ h : SL(3, F), proj 3 F h ∈ S4img F → ∀ r ∈ R, h⁻¹ * r * h ∈ R := by
    intro h hh r hr
    have := hnorm _ (inv_mem hh) _ hr
    simpa [hRdef] using this
  have hR1 : R = ⊥ :=
    pgroup_three_trivial_sl hF R hR (hconj _ proj_s4Da_mem) (hconj _ proj_s4Db_mem) (hconj _ proj_s4P_mem)
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨r, rfl⟩ := proj_surjective 3 F y
  have hr : r ∈ R := hy
  rw [hR1, Subgroup.mem_bot] at hr
  rw [hr, map_one]
  exact Subgroup.one_mem _

end PThree


section PGen

variable {F : Type} [Field F] [Finite F]

theorem card_projectiveSL_three_nine (hF : Nat.card F = 9) : Nat.card (projectiveSL 3 F) = 42456960 := by
  have hSL := CFSG.GH74.KGroups.L3Eps.card_specialLinear_three (F := F)
  rw [hF] at hSL
  have h : Nat.card (projectiveSL 3 F) = Nat.card SL(3, F) :=
    (Nat.card_congr (Equiv.ofBijective (proj 3 F)
      ⟨proj_injective_of_card_nine hF, proj_surjective 3 F⟩)).symm
  rw [h, hSL]
  norm_num

theorem pgroup_ne_three_trivial (hF : Nat.card F = 9) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (Y : Subgroup (projectiveSL 3 F)) (hY : IsPGroup p Y)
    (hnorm : ∀ g ∈ S4img F, ∀ y ∈ Y, g * y * g⁻¹ ∈ Y) : Y = ⊥ := by
  have hp : p.Prime := Fact.out
  have hcard := card_projectiveSL_three_nine hF
  obtain ⟨n, hn⟩ := hY.exists_card_eq
  have hdvd : Nat.card Y ∣ 42456960 := hcard ▸ Subgroup.card_subgroup_dvd_card Y
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · exact Subgroup.card_eq_one.1 (by simpa using hn)
  have hpd : p ∣ 42456960 := (dvd_pow_self p hn0.ne').trans (hn ▸ hdvd)
  have h5713 : p = 5 ∨ p = 7 ∨ p = 13 := by
    have h : (42456960 : ℕ) = 2 ^ 7 * 3 ^ 6 * 5 * 7 * 13 := by norm_num
    rw [h] at hpd
    rcases (Nat.Prime.dvd_mul hp).1 hpd with h1 | h1
    · rcases (Nat.Prime.dvd_mul hp).1 h1 with h2 | h2
      · rcases (Nat.Prime.dvd_mul hp).1 h2 with h3 | h3
        · rcases (Nat.Prime.dvd_mul hp).1 h3 with h4 | h4
          · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h4)) hp2
          · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h4)) hp3
        · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h3)
      · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h2))
    · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h1))
  have hn1 : n = 1 := by
    by_contra h
    have h2 : 2 ≤ n := by omega
    have hsq : p ^ 2 ∣ 42456960 := (pow_dvd_pow p h2).trans (hn ▸ hdvd)
    rcases h5713 with rfl | rfl | rfl <;> norm_num at hsq
  have hYp : Nat.card Y = p := by rw [hn, hn1, pow_one]
  have : IsCyclic Y := isCyclic_of_prime_card hYp
  have hmem : ∀ a b : projectiveSL 3 F, a ∈ S4img F → b ∈ S4img F → ∀ y ∈ Y,
      ⁅a, b⁆ * y = y * ⁅a, b⁆ := fun a b ha hb y hy =>
    comm_mul_comm_of_cyclic Y (S4img F) hnorm ha hb hy
  rw [eq_bot_iff]
  intro y hy
  have c1 : ⁅proj 3 F s4P, proj 3 F s4Db⁆ * y = y * ⁅proj 3 F s4P, proj 3 F s4Db⁆ :=
    hmem _ _ proj_s4P_mem proj_s4Db_mem y hy
  have c2 : ⁅proj 3 F s4P, proj 3 F s4Da * proj 3 F s4Db⁆ * y = y * ⁅proj 3 F s4P, proj 3 F s4Da * proj 3 F s4Db⁆ :=
    hmem _ _ proj_s4P_mem (mul_mem proj_s4Da_mem proj_s4Db_mem) y hy
  have c3 : ⁅proj 3 F s4S, proj 3 F s4P⁆ * y = y * ⁅proj 3 F s4S, proj 3 F s4P⁆ :=
    hmem _ _ proj_s4S_mem proj_s4P_mem y hy
  rw [← map_commutatorElement, comm_s4P_s4Db] at c1
  rw [← map_mul, ← map_commutatorElement, comm_s4P_sDc] at c2
  rw [← map_commutatorElement, comm_s4S_s4P] at c3
  have := s4_eq_one_of_commute_proj_gens hF c1.symm c2.symm c3.symm
  rw [this]
  exact Subgroup.one_mem _

end PGen

section Combine

theorem pgroup_trivial_of_s4_normal {F : Type} [Field F] [Finite F] (hF : Nat.card F = 9) {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) (Y : Subgroup (projectiveSL 3 F)) (hY : IsPGroup p Y)
    (hnorm : ∀ g ∈ S4img F, ∀ y ∈ Y, g * y * g⁻¹ ∈ Y) : Y = ⊥ := by
  by_cases hp3 : p = 3
  · subst hp3
    exact pgroup_three_trivial hF Y hY hnorm
  · exact pgroup_ne_three_trivial hF hp2 hp3 Y hY hnorm

end Combine

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
