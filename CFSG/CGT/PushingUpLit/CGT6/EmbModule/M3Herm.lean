module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk111cTFinrank
public import CFSG.CGT.PushingUpLit.CGT6.TwoEightMinus
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk111cAFun

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG.GH74.GLS.Stage4.Rest CFSG.CGT.PushingUpLit.CGT6.TwoEight

section Herm

variable (k : ℕ)

@[expose] noncomputable def hermForm (M : Matrix (Fin 2) (Fin 2) (Fq (2 * k))) :
    (Fin 2 → Fq (2 * k)) → Fq (2 * k) := fun v =>
  v 1 * M 0 0 * sigR k (v 1) + v 1 * M 0 1 * sigR k (-v 0) +
    (-v 0) * M 1 0 * sigR k (v 1) + (-v 0) * M 1 1 * sigR k (-v 0)

theorem hermForm_add (M M' : Matrix (Fin 2) (Fin 2) (Fq (2 * k))) :
    hermForm k (M + M') = hermForm k M + hermForm k M' := by
  funext v
  simp only [hermForm, Matrix.add_apply, Pi.add_apply]
  ring

theorem hermForm_funRep (g : SLm (Fq (2 * k))) (M : Matrix (Fin 2) (Fin 2) (Fq (2 * k))) :
    funRep (Fq (2 * k)) (Fq (2 * k)) g (hermForm k M) =
      hermForm k ((g : Matrix (Fin 2) (Fin 2) (Fq (2 * k))) * M *
        cstar k (g : Matrix (Fin 2) (Fin 2) (Fq (2 * k)))) := by
  funext v
  rw [funRep_apply]
  simp only [hermForm]
  rw [inv_mulVec_zero, inv_mulVec_one]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, cstar_apply, map_mul, map_neg, map_sub]
  ring

variable [NeZero k]

theorem hermForm_mem [Fintype (Fq (2 * k))] (hF : Fintype.card (Fq (2 * k)) = 2 ^ (2 * k))
    (M : Matrix (Fin 2) (Fin 2) (Fq (2 * k))) :
    hermForm k M ∈ steinbergSub (Fq (2 * k)) (Fq (2 * k)) (1 + 2 ^ k) := by
  have hk : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr (NeZero.ne k)
  have hlt : 2 ^ k < 2 ^ (2 * k) := Nat.pow_lt_pow_right Nat.one_lt_two (by omega)
  have hA : 1 + 2 ^ k < 2 ^ (2 * k) := by
    have h2 : 2 ≤ 2 ^ k := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    have h3 : 2 ^ (2 * k) = 2 ^ k * 2 ^ k := by rw [two_mul, pow_add]
    nlinarith
  have hodd : ¬ 2 ∣ Nat.choose (1 + 2 ^ k) 1 := by
    rw [Nat.choose_one_right]
    intro h
    have : 2 ∣ 2 ^ k := dvd_pow_self 2 (by omega)
    omega
  have hm0 : 0 ∈ monoIdx 2 (2 * k) (1 + 2 ^ k) := by
    rw [mem_monoIdx]
    exact ⟨by positivity, by simp⟩
  have hm1 : 1 ∈ monoIdx 2 (2 * k) (1 + 2 ^ k) := by
    rw [mem_monoIdx]
    exact ⟨(Nat.le_add_right 1 (2 ^ k)).trans_lt hA, hodd⟩
  have hm2 : 2 ^ k ∈ monoIdx 2 (2 * k) (1 + 2 ^ k) := by
    rw [mem_monoIdx]
    refine ⟨hlt, ?_⟩
    have h := Nat.choose_symm (n := 1 + 2 ^ k) (k := 2 ^ k) (Nat.le_add_left _ _)
    have h' : 1 + 2 ^ k - 2 ^ k = 1 := Nat.add_sub_cancel _ _
    rw [h'] at h
    rw [← h]
    exact hodd
  have hm3 : 1 + 2 ^ k ∈ monoIdx 2 (2 * k) (1 + 2 ^ k) := by
    rw [mem_monoIdx]
    exact ⟨hA, by simp⟩
  have e0 := monoFun_mem_steinbergSub (L := Fq (2 * k)) hF (1 + 2 ^ k) hA hm0
  have e1 := monoFun_mem_steinbergSub (L := Fq (2 * k)) hF (1 + 2 ^ k) hA hm1
  have e2 := monoFun_mem_steinbergSub (L := Fq (2 * k)) hF (1 + 2 ^ k) hA hm2
  have e3 := monoFun_mem_steinbergSub (L := Fq (2 * k)) hF (1 + 2 ^ k) hA hm3
  have h1 : 1 + 2 ^ k - 0 = 1 + 2 ^ k := Nat.sub_zero _
  have h2 : 1 + 2 ^ k - 1 = 2 ^ k := Nat.add_sub_cancel_left _ _
  have h3 : 1 + 2 ^ k - 2 ^ k = 1 := Nat.add_sub_cancel _ _
  have h4 : 1 + 2 ^ k - (1 + 2 ^ k) = 0 := Nat.sub_self _
  rw [h1] at e0
  rw [h2] at e1
  rw [h3] at e2
  rw [h4] at e3
  have hform : hermForm k M = M 0 0 • monoFun (Fq (2 * k)) (Fq (2 * k)) 0 (1 + 2 ^ k) +
      (-M 0 1) • monoFun (Fq (2 * k)) (Fq (2 * k)) (2 ^ k) 1 +
      (-M 1 0) • monoFun (Fq (2 * k)) (Fq (2 * k)) 1 (2 ^ k) +
      M 1 1 • monoFun (Fq (2 * k)) (Fq (2 * k)) (1 + 2 ^ k) 0 := by
    funext v
    simp only [hermForm, monoFun, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_neg,
      sigR_apply, Algebra.algebraMap_self, RingHom.id_apply, pow_zero, one_mul, pow_one,
      mul_one, pow_add]
    ring
  rw [hform]
  exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
    (Submodule.smul_mem _ _ e0) (Submodule.smul_mem _ _ e2)) (Submodule.smul_mem _ _ e1))
    (Submodule.smul_mem _ _ e3)

@[expose] noncomputable def hermHom [Fintype (Fq (2 * k))]
    (hF : Fintype.card (Fq (2 * k)) = 2 ^ (2 * k)) :
    ↥(hermSub k) →+ ↥(steinbergSub (Fq (2 * k)) (Fq (2 * k)) (1 + 2 ^ k)) :=
  AddMonoidHom.mk' (fun M => ⟨hermForm k M.1, hermForm_mem k hF M.1⟩) (fun M M' =>
    Subtype.ext (hermForm_add k M.1 M'.1))

theorem hermHom_equivariant [Fintype (Fq (2 * k))]
    (hF : Fintype.card (Fq (2 * k)) = 2 ^ (2 * k)) (g : SLm (Fq (2 * k))) (M : ↥(hermSub k)) :
    hermHom k hF ⟨(g : Matrix (Fin 2) (Fin 2) (Fq (2 * k))) * M.1 *
        cstar k (g : Matrix (Fin 2) (Fin 2) (Fq (2 * k))), herm_act_mem k g M⟩ =
      steinbergRep (Fq (2 * k)) (Fq (2 * k)) (1 + 2 ^ k) g (hermHom k hF M) :=
  Subtype.ext (hermForm_funRep k g M.1).symm

theorem hermHom_ne_zero [Fintype (Fq (2 * k))] (hF : Fintype.card (Fq (2 * k)) = 2 ^ (2 * k)) :
    hermHom k hF ≠ 0 := by
  intro h
  let M₀ : ↥(hermSub k) := ⟨!![((1 : Fz k) : Fq (2 * k)), 0; sigR k 0, ((0 : Fz k) : Fq (2 * k))],
    herm_mk_mem k 1 0 0⟩
  have h1 := congrArg Subtype.val (DFunLike.congr_fun h M₀)
  have h2 := congrFun h1 ![0, 1]
  simp [hermHom, hermForm, M₀] at h2

theorem card_hermSub : Nat.card ↥(hermSub k) = 2 ^ (4 * k) := by
  rw [Nat.card_congr (minusCoord k).toEquiv]
  show Nat.card (Fz k × Fq (2 * k) × Fz k) = _
  rw [Nat.card_prod, Nat.card_prod, card_Fz, GaloisField.card 2 (2 * k)
    (by have := NeZero.ne k; omega)]
  rw [← pow_add, ← pow_add]
  congr 1
  ring

end Herm

end CFSG.CGT.PushingUpLit.CGT6
