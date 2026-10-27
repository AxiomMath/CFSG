module

public import CFSG.LargeExtraspecial.AS35QThGamL
public import CFSG.Fischer.Classification.Unitary.Model

public section

namespace CFSG.LargeExtraspecial.AS35QTh

open Matrix CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary
  CFSG.Fischer.Classification.Unitary
open CFSG.Blueprint.Fischer (K)

theorem eq_one_of_mem_center_SU5 {g : SUid frob 5} (hg : g ∈ Subgroup.center (SUid frob 5)) :
    g = 1 := by
  rw [center_SUid (by norm_num)] at hg
  obtain ⟨c, hc⟩ := exists_smul_eq_of_mem_scalars hg
  have hmat : ((g : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
      c • (1 : Matrix (Fin 5) (Fin 5) K) :=
    Matrix.ext_of_mulVec_single fun j => by
      rw [← smul_def, hc, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hdet : (c • (1 : Matrix (Fin 5) (Fin 5) K)).det = 1 := by
    rw [← hmat]
    exact ((mem_SUid_iff frob).mp g.2).1
  rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at hdet
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num)] at hdet
    exact zero_ne_one hdet
  have h2 : c ^ 2 = 1 := by
    rw [← hdet, show c ^ 5 = c ^ 3 * c ^ 2 by ring, pow_three_K hc0, one_mul]
  have hc1 := eq_one_of_sq_K h2
  refine ext_smul _ fun v => ?_
  rw [hc, hc1, one_smul, one_smul]

theorem center_SU5 : Subgroup.center (SUid frob 5) = ⊥ :=
  (Subgroup.eq_bot_iff_forall _).mpr fun _ hg => eq_one_of_mem_center_SU5 hg

theorem mk_injective_PG5 :
    Function.Injective (QuotientGroup.mk : SUid frob 5 → PG 5) := by
  intro a b h
  rw [QuotientGroup.eq, center_SU5, Subgroup.mem_bot, inv_mul_eq_one] at h
  exact h

@[expose] noncomputable def betaG (ε : ZMod 2) (a : Fin 3 → K) : K :=
  frob ω * herm frob a a + toK ε

theorem betaG_valid (ε : ZMod 2) (a : Fin 3 → K) :
    betaG ε a + frob (betaG ε a) = herm frob a a := by
  rw [betaG, map_add, map_mul, frob_frob, frob_toK, herm_self_fixed frob frob_frob a]
  linear_combination herm frob a a * omega_add_frob + toK ε * two_eq_zero

theorem betaG_add (ε ε' : ZMod 2) (a b : Fin 3 → K) :
    betaG ε a + betaG ε' b + herm frob a b = betaG (ε + ε' + beta a b) (a + b) := by
  rw [betaG, betaG, betaG, beta, map_add, map_add, toK_tr2, herm_add_left, herm_add_right,
    herm_add_right, herm_conj frob frob_frob a b, map_mul]
  linear_combination (-herm frob a b) * omega_add_frob -
    (frob ω * frob (herm frob a b)) * two_eq_zero

@[expose] noncomputable def PsiS (x : Model) : SUid frob (3 + 2) :=
  Usu x.2.1 (betaG x.1 x.2.1) (betaG_valid x.1 x.2.1) * Lsu x.2.2

theorem Usu_congr {d : Fin 3 → K} {β β' : K} (h : β = β') (hβ : β + frob β = herm frob d d)
    (hβ' : β' + frob β' = herm frob d d) : Usu d β hβ = Usu d β' hβ' := by
  subst h
  rfl

theorem Usu_congr' {d d' : Fin 3 → K} {β β' : K} (hd : d = d') (h : β = β')
    (hβ : β + frob β = herm frob d d) (hβ' : β' + frob β' = herm frob d' d') :
    Usu d β hβ = Usu d' β' hβ' := by
  subst hd
  subst h
  rfl

theorem psiS_mul (x y : Model) : PsiS (mulM x y) = PsiS x * PsiS y := by
  obtain ⟨ε, a, A⟩ := x
  obtain ⟨ε', a', A'⟩ := y
  have hb' : betaG ε' a' + frob (betaG ε' a') = herm frob (gv A a') (gv A a') := by
    rw [herm_gv]; exact betaG_valid ε' a'
  simp only [PsiS, mulM]
  rw [show Usu a (betaG ε a) (betaG_valid ε a) * Lsu A *
      (Usu a' (betaG ε' a') (betaG_valid ε' a') * Lsu A') =
      Usu a (betaG ε a) (betaG_valid ε a) *
        (Lsu A * Usu a' (betaG ε' a') (betaG_valid ε' a')) * Lsu A' by group,
    Lsu_mul_Usu A a' _ _ hb',
    show Usu a (betaG ε a) (betaG_valid ε a) * (Usu (gv A a') (betaG ε' a') hb' * Lsu A) *
      Lsu A' = Usu a (betaG ε a) (betaG_valid ε a) * Usu (gv A a') (betaG ε' a') hb' *
        (Lsu A * Lsu A') by group, Lsu_mul]
  congr 1
  have hval : betaG ε a + betaG ε' a' + herm frob a (gv A a') +
      frob (betaG ε a + betaG ε' a' + herm frob a (gv A a')) =
        herm frob (a + gv A a') (a + gv A a') := by
    have h := betaG_add ε ε' a (gv A a')
    rw [show betaG ε' (gv A a') = betaG ε' a' by rw [betaG, betaG, herm_gv]] at h
    rw [h]
    exact betaG_valid _ _
  rw [Usu_mul a (gv A a') _ _ (betaG_valid ε a) hb' hval]
  refine Usu_congr ?_ _ _
  have h := betaG_add ε ε' a (gv A a')
  rw [show betaG ε' (gv A a') = betaG ε' a' by rw [betaG, betaG, herm_gv]] at h
  exact h.symm

@[expose] noncomputable def Psi (x : Model) : PG 5 := QuotientGroup.mk (PsiS x)

theorem Usu_smul_v₀ (d : Fin 3 → K) (β : K) (hβ : β + frob β = herm frob d d) :
    Usu d β hβ • v₀ 3 = v₀ 3 := by
  rw [Usu_smul, uLin_apply, herm_v₀_v₀, herm_ι_v₀, mul_zero, add_zero, zero_smul, add_zero,
    zero_smul, add_zero]

theorem tvU_mul_Usu (d : Fin 3 → K) (β : K) (hβ : β + frob β = herm frob d d) :
    tvU (v₀ 3) * Usu d β hβ = Usu d β hβ * tvU (v₀ 3) := by
  rw [← Usu_zero_one]
  have h1 : (1 : K) + β + herm frob 0 d + frob (1 + β + herm frob 0 d) =
      herm frob (0 + d) (0 + d) := by
    rw [herm_zero_left, add_zero, zero_add, map_add, map_one]
    linear_combination hβ + two_eq_zero
  have h2 : β + 1 + herm frob d 0 + frob (β + 1 + herm frob d 0) =
      herm frob (d + 0) (d + 0) := by
    rw [herm_zero_right, add_zero, add_zero, map_add, map_one]
    linear_combination hβ + two_eq_zero
  rw [Usu_mul _ _ _ _ _ _ h1, Usu_mul _ _ _ _ _ _ h2]
  exact Usu_congr' (by rw [zero_add, add_zero])
    (by rw [herm_zero_left, herm_zero_right, add_comm (1 : K) β]) _ _

theorem PsiS_commute (x : Model) : tvU (v₀ 3) * PsiS x = PsiS x * tvU (v₀ 3) := by
  obtain ⟨ε, a, A⟩ := x
  have hL : Lsu A * tvU (v₀ 3) = tvU (v₀ 3) * Lsu A := by
    rw [← Usu_zero_one]
    have h' : (1 : K) + frob 1 = herm frob (gv A 0) (gv A 0) := by
      rw [gv_zero]; exact herm_one_zero
    rw [Lsu_mul_Usu A 0 1 herm_one_zero h', Usu_congr' (gv_zero A) rfl h' herm_one_zero]
  simp only [PsiS]
  rw [← mul_assoc, tvU_mul_Usu, mul_assoc, ← hL, mul_assoc]

theorem Psi_mem_centralizer (x : Model) :
    Psi x ∈ Subgroup.centralizer ({tq (v₀ 3)} : Set (PG 5)) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  change (QuotientGroup.mk (PsiS x) : PG 5) * QuotientGroup.mk (tvU (v₀ 3)) =
    QuotientGroup.mk (tvU (v₀ 3)) * QuotientGroup.mk (PsiS x)
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, PsiS_commute]

@[expose] noncomputable def psiC (x : Model) :
    Subgroup.centralizer ({tq (v₀ 3)} : Set (PG 5)) :=
  ⟨Psi x, Psi_mem_centralizer x⟩

theorem psiC_mul (x y : Model) : psiC (mulM x y) = psiC x * psiC y := by
  apply Subtype.ext
  change (QuotientGroup.mk (PsiS (mulM x y)) : PG 5) =
    QuotientGroup.mk (PsiS x) * QuotientGroup.mk (PsiS y)
  rw [psiS_mul, QuotientGroup.mk_mul]

end CFSG.LargeExtraspecial.AS35QTh
