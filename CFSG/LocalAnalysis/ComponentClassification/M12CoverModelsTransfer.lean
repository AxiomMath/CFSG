module

public import CFSG.LocalAnalysis.ComponentClassification.M12CoverModelsTransversal
public import CFSG.LocalAnalysis.ComponentClassification.CentralCoverTransferComparison

public section

namespace CFSG.ComponentClassification.M12Cover.InternalSylow

open CFSG.Blueprint CFSG.ComponentClassification.CentralCover

theorem sum_fin_eq_sum_range (n : ℕ) (g : ℕ → ℕ) :
    ∑ i : Fin n, ((g i : ℕ) : ZMod 2) = ((((List.range n).map g).sum : ℕ) : ZMod 2) := by
  rw [Fin.sum_univ_eq_sum_range (fun i => ((g i : ℕ) : ZMod 2)) n]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, List.range_succ, List.map_append, List.sum_append]
    simp

theorem fIdx_lt (i j : ℕ) : fIdx i j < 2 := packEntry_lt _ 1 _

theorem lamIdx_lt (j : ℕ) : lamIdx j < 2 := packEntry_lt _ 1 _

theorem tp_lt {i h : ℕ} (hi : i < 1485) (hh : h < 64) : tp i h < 64 := (decompCheck_spec hi hh).1

theorem tih_lt {i h : ℕ} (hi : i < 1485) (hh : h < 64) : tih i h < 1485 :=
  (decompCheck_spec hi hh).2.1

theorem taIdx_lt {i : ℕ} (hi : i < 1485) : taIdx i < 64 := (betaCheck_spec.2 i hi).1

theorem pS_d' (i : Fin 1485) (j : Fin 64) : pS i (d j) = d ⟨tp i j, tp_lt i.2 j.2⟩ := by
  rw [pS_d]
  congr 2
  exact Nat.mod_eq_of_lt (tp_lt i.2 j.2)

theorem iS_d' (i : Fin 1485) (j : Fin 64) : iS i (d j) = ⟨tih i j, tih_lt i.2 j.2⟩ :=
  Fin.ext (val_iS i j)

theorem aS_eq (i : Fin 1485) : aS i = d ⟨taIdx i, taIdx_lt i.2⟩ := by
  rw [aS]
  congr 2
  exact Nat.mod_eq_of_lt (taIdx_lt i.2)

theorem isRightTransversal : IsRightTransversal S r := by
  intro x
  obtain ⟨⟨s, i⟩, hsi, huniq⟩ := existsUnique_mul_r x
  simp only at hsi
  refine ⟨i, ?_, fun j hj => ?_⟩
  · change x * (r i)⁻¹ ∈ S
    rw [← hsi, mul_inv_cancel_right]
    exact s.2
  · have := huniq (⟨x * (r j)⁻¹, hj⟩, j) (by simp)
    exact congrArg Prod.snd this

theorem act_eq (i : Fin 1485) (h : S) :
    isRightTransversal.act i (h : NativeSporadic.M12) = iS i h :=
  isRightTransversal.act_eq_of_eq (pS i h).2 (r_mul i h)

theorem coef_eq (i : Fin 1485) (h : S) :
    isRightTransversal.coef i (h : NativeSporadic.M12) = pS i h :=
  Subtype.ext (isRightTransversal.coe_coef_eq_of_eq (pS i h).2 (r_mul i h))

@[expose] noncomputable def F (h k : S) : ZMod 2 :=
  isRightTransversal.transfer₂ f (h : NativeSporadic.M12) (k : NativeSporadic.M12)

theorem F_eq (h k : S) : F h k = ∑ i : Fin 1485, f (pS i h) (pS (iS i h) k) := by
  rw [F, IsRightTransversal.transfer₂_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coef_eq, act_eq, coef_eq]

theorem F_d (j l : Fin 64) : F (d j) (d l) = ((FSum j l : ℕ) : ZMod 2) := by
  rw [F_eq, FSum, ← sum_fin_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pS_d', iS_d', pS_d', f_d]

theorem transferCheck_spec {h k : ℕ} (hh : h < 64) (hk : k < 64) :
    (FSum h k + muIdx h + muIdx k + muIdx (mIdx h k)) % 2 = fIdx h k :=
  Nat.eq_of_beq_eq_true (all_range (all_range transferCheck_eq hh) hk)

theorem F_add_mu (h k : S) : F h k + mu h + mu k + mu (h * k) = f h k := by
  obtain ⟨j, rfl⟩ := d_surjective h
  obtain ⟨l, rfl⟩ := d_surjective k
  rw [← d_mul, F_d, mu_d, mu_d, mu_d, f_d, ← Nat.cast_add, ← Nat.cast_add, ← Nat.cast_add]
  refine zmod2_eq_of_mod ?_
  rw [Nat.mod_eq_of_lt (fIdx_lt j l)]
  exact transferCheck_spec j.2 l.2

theorem transfer₂_add_coboundary_mu (s t : S) :
    isRightTransversal.transfer₂ fN s t + coboundary mu s t = fN s t := by
  change F s t + (mu s + mu t + mu (s * t)) = f s t
  rw [← F_add_mu s t]
  ring

@[expose] noncomputable def A (i : Fin 1485) : R := ⟨0, aS i⟩

@[expose] noncomputable def coef (i : Fin 1485) (h : S) : ZMod 2 :=
  ((A i)⁻¹ * tau0 ⟨0, pS i h⟩ * A (iS i h)).fst

theorem A_conj (i : Fin 1485) (h : S) :
    (A i)⁻¹ * tau0 ⟨0, pS i h⟩ * A (iS i h) = ⟨coef i h, pS (σI i) (βS h)⟩ := by
  refine CocycleExtension.ext rfl ?_
  simp only [A, CocycleExtension.mul_snd, CocycleExtension.inv_snd, tau0_apply]
  exact quotient_eq i h

@[expose] noncomputable def Λ (h : S) : ZMod 2 := ∑ i : Fin 1485, coef i h

theorem coef_d (i : Fin 1485) (j : Fin 64) : coef i (d j) = ((cIdx i j : ℕ) : ZMod 2) := by
  have ha := taIdx_lt i.2
  have hi' := tih_lt i.2 j.2
  simp only [coef, A, CocycleExtension.mul_fst, CocycleExtension.mul_snd,
    CocycleExtension.inv_fst, CocycleExtension.inv_snd, tau0_apply, fN_apply]
  rw [pS_d', iS_d', aS_eq, aS_eq, d_inv, βS_d, ← d_mul, f_d, f_d, f_d, lam0_d]
  simp only [cIdx, zero_add, add_zero, Nat.cast_add]
  rfl

theorem lambdaCheck_spec {h : ℕ} (hh : h < 64) :
    (LamSum h + muIdx h + muIdx (bIdx h)) % 2 = lamIdx h :=
  Nat.eq_of_beq_eq_true (all_range lambdaCheck_eq hh)

theorem lam_eq (h : S) : lam h = Λ h + mu h + mu (βS h) := by
  obtain ⟨j, rfl⟩ := d_surjective h
  have hsum : Λ (d j) = ((LamSum j : ℕ) : ZMod 2) := by
    rw [Λ, LamSum, ← sum_fin_eq_sum_range]
    exact Finset.sum_congr rfl fun i _ => coef_d i j
  rw [hsum, βS_d, lam_d, mu_d, mu_d, ← Nat.cast_add, ← Nat.cast_add]
  refine zmod2_eq_of_mod ?_
  rw [Nat.mod_eq_of_lt (lamIdx_lt j)]
  exact (lambdaCheck_spec j.2).symm

end CFSG.ComponentClassification.M12Cover.InternalSylow
