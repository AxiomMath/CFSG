module

public import CFSG.GroupTheory.WreathThree
public import CFSG.ClassicalInvolution.Asc77.AscSCH17

public section

namespace CFSG.GroupTheory.WeirSylow

open CFSG.GroupTheory.WreathThree CFSG.SectionRank.OddCover CFSG.ClassicalInvolution.Asc77.SCH
open CFSG.Open

variable {K : Type} [Field K]

@[expose] noncomputable def glFourWreathFactor (m : Kˣ) : Subgroup (GL (Fin 4) K) :=
  Subgroup.zpowers (diagHom 4 ![m, 1, 1, m⁻¹])

private theorem diagHom_mmm_eq_torusPsi (m : Kˣ) :
    (diagHom 4 ![m, 1, 1, m⁻¹] : GL (Fin 4) K) = torusPsi (m, m, m) := by
  show _ = diagHom 4 (psiDiag (m, m, m))
  congr 1
  funext i
  fin_cases i <;> simp [psiDiag]

private theorem diagHom_omm_eq_torusPsi (m : Kˣ) :
    (diagHom 4 ![1, m, 1, m⁻¹] : GL (Fin 4) K) = torusPsi (1, m, m) := by
  show _ = diagHom 4 (psiDiag (1, m, m))
  congr 1
  funext i
  fin_cases i <;> simp [psiDiag]

private theorem diagHom_oom_eq_torusPsi (m : Kˣ) :
    (diagHom 4 ![1, 1, m, m⁻¹] : GL (Fin 4) K) = torusPsi (1, 1, m) := by
  show _ = diagHom 4 (psiDiag (1, 1, m))
  congr 1
  funext i
  fin_cases i <;> simp [psiDiag]

theorem card_glFourWreathFactor (m : Kˣ) :
    Nat.card (glFourWreathFactor (K := K) m) = orderOf m := by
  rw [glFourWreathFactor, Nat.card_zpowers, diagHom_mmm_eq_torusPsi,
    orderOf_injective torusPsi torusPsi_injective, Prod.orderOf, Prod.orderOf]
  simp

private theorem map_conj_cyc4GL_glFourWreathFactor (m : Kˣ) :
    (glFourWreathFactor (K := K) m).map (MulAut.conj (cyc4GL : GL (Fin 4) K)).toMonoidHom =
      Subgroup.zpowers (diagHom 4 ![1, m, 1, m⁻¹]) := by
  rw [glFourWreathFactor, MonoidHom.map_zpowers]
  congr 1
  simp [MulAut.conj_apply, cyc4GL_conj_diag]

private theorem map_conj_cyc4GL_sq_glFourWreathFactor (m : Kˣ) :
    (glFourWreathFactor (K := K) m).map
        (MulAut.conj ((cyc4GL : GL (Fin 4) K) ^ 2)).toMonoidHom =
      Subgroup.zpowers (diagHom 4 ![1, 1, m, m⁻¹]) := by
  rw [glFourWreathFactor, MonoidHom.map_zpowers]
  congr 1
  have h1 : (cyc4GL : GL (Fin 4) K) * diagHom 4 ![m, 1, 1, m⁻¹] * cyc4GL⁻¹ =
      diagHom 4 ![1, m, 1, m⁻¹] := by
    simp [cyc4GL_conj_diag]
  have h2 : (cyc4GL : GL (Fin 4) K) * diagHom 4 ![1, m, 1, m⁻¹] * cyc4GL⁻¹ =
      diagHom 4 ![1, 1, m, m⁻¹] := by
    simp [cyc4GL_conj_diag]
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [show (cyc4GL : GL (Fin 4) K) ^ 2 * diagHom 4 ![m, 1, 1, m⁻¹] *
        ((cyc4GL : GL (Fin 4) K) ^ 2)⁻¹ =
      cyc4GL * (cyc4GL * diagHom 4 ![m, 1, 1, m⁻¹] * cyc4GL⁻¹) * cyc4GL⁻¹ by
    rw [pow_two, mul_inv_rev]; simp only [mul_assoc], h1, h2]

private theorem base_glFourWreathFactor_eq_torusM (m : Kˣ) :
    base (glFourWreathFactor (K := K) m) cyc4GL = torusM m := by
  rw [base, map_conj_cyc4GL_glFourWreathFactor, map_conj_cyc4GL_sq_glFourWreathFactor,
    glFourWreathFactor, diagHom_mmm_eq_torusPsi, diagHom_omm_eq_torusPsi,
    diagHom_oom_eq_torusPsi]
  have hm : m ∈ Subgroup.zpowers m := Subgroup.mem_zpowers m
  have h1 : (1 : Kˣ) ∈ Subgroup.zpowers m := Subgroup.one_mem _
  apply le_antisymm
  · refine sup_le (sup_le ?_ ?_) ?_ <;> rw [Subgroup.zpowers_le]
    · exact ⟨(m, m, m), ⟨hm, hm, hm⟩, rfl⟩
    · exact ⟨(1, m, m), ⟨h1, hm, hm⟩, rfl⟩
    · exact ⟨(1, 1, m), ⟨h1, h1, hm⟩, rfl⟩
  · refine (torusM_le_closure m).trans ((Subgroup.closure_le _).2 ?_)
    have g1 : torusPsi (m, m, m) ∈ (Subgroup.zpowers (torusPsi (m, m, m) : GL (Fin 4) K) ⊔
        Subgroup.zpowers (torusPsi (1, m, m)) ⊔ Subgroup.zpowers (torusPsi (1, 1, m))) :=
      Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
    have g2 : torusPsi (1, m, m) ∈ (Subgroup.zpowers (torusPsi (m, m, m) : GL (Fin 4) K) ⊔
        Subgroup.zpowers (torusPsi (1, m, m)) ⊔ Subgroup.zpowers (torusPsi (1, 1, m))) :=
      Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
    have g3 : torusPsi (1, 1, m) ∈ (Subgroup.zpowers (torusPsi (m, m, m) : GL (Fin 4) K) ⊔
        Subgroup.zpowers (torusPsi (1, m, m)) ⊔ Subgroup.zpowers (torusPsi (1, 1, m))) :=
      Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    have e1 : (torY₁ m : GL (Fin 4) K) = torusPsi (m, m, m) * (torusPsi (1, m, m))⁻¹ := by
      rw [← map_inv, ← map_mul]
      show diagHom 4 _ = diagHom 4 _
      congr 1
      funext i
      fin_cases i <;> simp [psiDiag]
    have e2 : (torY₂ m : GL (Fin 4) K) = torusPsi (1, m, m) * (torusPsi (1, 1, m))⁻¹ := by
      rw [← map_inv, ← map_mul]
      show diagHom 4 _ = diagHom 4 _
      congr 1
      funext i
      fin_cases i <;> simp [psiDiag]
    have e3 : (torY₃ m : GL (Fin 4) K) = torusPsi (1, 1, m) := by
      show diagHom 4 _ = diagHom 4 _
      congr 1
      funext i
      fin_cases i <;> simp [psiDiag]
    rintro _ (rfl | rfl | rfl)
    · rw [e1]; exact Subgroup.mul_mem _ g1 (Subgroup.inv_mem _ g2)
    · rw [e2]; exact Subgroup.mul_mem _ g2 (Subgroup.inv_mem _ g3)
    · rw [e3]; exact g3

theorem isWreathThree_glFourWreathFactor {m : Kˣ} {a : ℕ} (ha : 1 ≤ a) (hm : orderOf m = 3 ^ a) :
    IsWreathThree (glFourWreathFactor (K := K) m) (cyc4GL : GL (Fin 4) K) := by
  have hcard : Nat.card (glFourWreathFactor (K := K) m) = 3 ^ a := by
    rw [card_glFourWreathFactor, hm]
  refine ⟨IsPGroup.of_card hcard, ?_, ?_, ?_, ?_, ?_⟩
  · exact Subgroup.isCyclic_zpowers _
  · intro h
    rw [h, Subgroup.card_bot] at hcard
    have : 3 ^ 1 ∣ 3 ^ a := pow_dvd_pow 3 ha
    rw [← hcard] at this
    omega
  · intro x hx y hy
    rw [base_glFourWreathFactor_eq_torusM] at hx hy
    obtain ⟨d₁, rfl⟩ := torusM_diag m hx
    obtain ⟨d₂, rfl⟩ := torusM_diag m hy
    rw [← map_mul, ← map_mul, mul_comm]
  · rw [base_glFourWreathFactor_eq_torusM, card_torusM, hcard, hm]
  · rw [cyc4GL_pow_three]
    exact Subgroup.one_mem _

theorem exists_units_orderOf_eq_of_dvd [Finite K] {d : ℕ} (hd : d ∣ Nat.card K - 1) :
    ∃ m : Kˣ, orderOf m = d := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  rw [Nat.card_units] at hg
  obtain ⟨k, hk⟩ := hd
  have hK : 1 < Nat.card K := Finite.one_lt_card
  have hk0 : k ≠ 0 := by
    rintro rfl
    omega
  refine ⟨g ^ k, ?_⟩
  rw [orderOf_pow_of_dvd hk0 (by rw [hg, hk]; exact Dvd.intro_left d rfl), hg, hk,
    Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hk0)]

theorem scalar_pow_four_eq_one_of_mem_statedSL {c : Kˣ}
    (h : Matrix.GeneralLinearGroup.scalar (Fin 4) c ∈ StatedSL 4 K) : c ^ 4 = 1 := by
  have h1 := StatedAPI.det_of_mem_statedSL h
  rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h1
  exact Units.ext (by simpa using h1)

end CFSG.GroupTheory.WeirSylow
