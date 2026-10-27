module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshExt

public section

namespace CFSG.EvenSporadicStandard.M12Std.Yosh

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.SmallOddCore
open CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native
open CFSG.ComponentClassification.M12Cover CFSG.GH74.M12 CFSG.GH74.M12.Hyp CFSG.Blueprint Subgroup

theorem kapP_injective : Function.Injective kapP := by
  rw [injective_iff_map_eq_one]
  rintro ⟨a, σ⟩ h
  rw [kapP_apply] at h
  by_cases ha : a = 1
  · subst ha
    have h1 : extHom σ = 1 := by simpa [tauPow] using h
    have : σ = 1 := extHom_injective (by rw [h1, map_one])
    simp [this]
  · exfalso
    have hv : a.toAdd = 1 := by
      rcases zmod_two_cases a.toAdd with h0 | h1
      · exact absurd (Multiplicative.toAdd.injective (by simpa using h0)) ha
      · exact h1
    have h12 := congrArg (fun f : Equiv.Perm (Fin 14) => f ⟨12, by omega⟩) h
    simp only [Equiv.Perm.coe_mul, Function.comp_apply, Equiv.Perm.coe_one, id_eq] at h12
    have hfix : extHom σ ⟨12, by omega⟩ = ⟨12, by omega⟩ := extHom_apply_ge σ _ (by simp)
    rw [hfix] at h12
    have hv1 : (a.toAdd).val = 1 := by rw [hv]; rfl
    simp [tauPow, hv1, tauP] at h12

theorem tauPow_ofAdd_one : tauPow (Multiplicative.ofAdd 1) = tauP := by
  have : (1 : ZMod 2).val = 1 := rfl
  simp [tauPow, this]

theorem tp14_eq_of_rep {T : Table} {g : Equiv.Perm (Fin 14)} (hT : Rep 14 T g) : tp 14 T = g := by
  have h := co2Rep_natArr_iff.2 hT
  have hc : (∀ i < 14, (natArr T)[i]! < 14) ∧
      ∀ i < 14, ∀ j < 14, (natArr T)[i]! = (natArr T)[j]! → i = j :=
    ⟨fun i hi => h.lt hi, fun i hi j hj hij => by
      rw [h.apply hi, h.apply hj] at hij
      have := g.injective (Fin.ext hij)
      simpa using this⟩
  ext x
  rw [tp, CFSG.Monster.B.Co2.permOfArr, dite_eq_left hc]
  change (natArr T)[(x : ℕ)]! = _
  exact h x

theorem tp_tbl14_eq (σ : Equiv.Perm (Fin 12)) : tp 14 (tbl14 σ) = extHom σ :=
  tp14_eq_of_rep (rep_tbl14 σ)

theorem tp_tauT_eq : tp 14 tauT = tauP := tp14_eq_of_rep rep_tauT

theorem eK_coe : (Spec.eK : Equiv.Perm (Fin 14)) = tauP := tp_tauT_eq

theorem sK_coe : (Spec.sK : Equiv.Perm (Fin 14)) = extHom sP := tp_tbl14_eq sP

theorem cK_coe : (Spec.cK : Equiv.Perm (Fin 14)) = extHom bfJ := by
  change ((Spec.fK ^ 4 : ↥Spec.yK) : Equiv.Perm (Fin 14)) = extHom (bfF ^ 4)
  rw [Subgroup.coe_pow, map_pow]
  exact congrArg (· ^ 4) (tp_tbl14_eq bfF)

theorem u_coe : tp 14 tauT * tp 14 u1T = tauP * extHom u1P := by
  rw [tp_tauT_eq, u1T, tp_tbl14_eq]

@[expose] def pv (σ : Equiv.Perm (Fin 12)) (j : ℕ) : ℕ :=
  if h : j < 12 then (σ ⟨j, h⟩).val else j

@[expose] def lamP (σ : Equiv.Perm (Fin 12)) : ℕ :=
  (((List.range 4).flatMap fun i => (List.range 4).filter fun j =>
    i < j && pv σ j < pv σ i).length) % 2

theorem yv_kapP (a : Multiplicative (ZMod 2)) (σ : Equiv.Perm (Fin 12)) {i : ℕ} (hi : i < 12) :
    Spec.yv (kapP (a, σ)) i = pv σ i := by
  have h1 : (extHom σ ⟨i, by omega⟩).val = (σ ⟨i, hi⟩).val :=
    extHom_apply_lt σ ⟨i, by omega⟩ hi
  have h2 : (extHom σ ⟨i, by omega⟩ : Fin 14).val < 12 := by rw [h1]; exact (σ _).2
  simp only [Spec.yv, dif_pos (by omega : i < 14), kapP_apply, Equiv.Perm.coe_mul,
    Function.comp_apply]
  rw [tauPow_apply_lt a _ h2, h1]
  simp [pv, hi]

theorem epsY_kapP (a : Multiplicative (ZMod 2)) (σ : Equiv.Perm (Fin 12)) :
    Spec.epsY (kapP (a, σ)) = (Multiplicative.toAdd a).val := by
  have h1 : ((kapP (a, σ) 12 : Fin 14) : ℕ) = 12 + (Multiplicative.toAdd a).val := by
    have h12 : (12 : Fin 14) = ⟨12, by omega⟩ := rfl
    rw [h12, kapP_apply, Equiv.Perm.coe_mul, Function.comp_apply,
      extHom_apply_ge σ ⟨12, by omega⟩ (by simp), tauPow_apply_twelve]
  have hv : (Multiplicative.toAdd a).val = 0 ∨ (Multiplicative.toAdd a).val = 1 := by
    rcases zmod_two_cases (Multiplicative.toAdd a) with h | h
    · left; rw [h]; rfl
    · right; rw [h]; rfl
  unfold Spec.epsY
  rw [h1]
  rcases hv with hv | hv <;> simp [hv]

theorem lam_sum_mod (f : ℕ → ℕ) :
    (∑ j ∈ Finset.range 4, ∑ i ∈ Finset.range j, if f j < f i then 1 else 0) % 2 =
      (((List.range 4).flatMap fun i => (List.range 4).filter fun j =>
        i < j && f j < f i).length) % 2 := by
  by_cases h10 : f 1 < f 0 <;> by_cases h20 : f 2 < f 0 <;> by_cases h21 : f 2 < f 1 <;>
    by_cases h30 : f 3 < f 0 <;> by_cases h31 : f 3 < f 1 <;> by_cases h32 : f 3 < f 2 <;>
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, h10, h20, h21, h30, h31, h32,
      ↓reduceIte] <;>
    simp [List.range_succ, List.filter_cons, h10, h20, h21, h30, h31, h32]

theorem lamY_kapP (a : Multiplicative (ZMod 2)) (σ : Equiv.Perm (Fin 12)) :
    Spec.lamY (kapP (a, σ)) % 2 = lamP σ := by
  have hp : ∀ j, j < 4 → Spec.yv (kapP (a, σ)) j = pv σ j := fun j hj => yv_kapP a σ (by omega)
  unfold Spec.lamY lamP
  rw [← lam_sum_mod]
  congr 1
  refine Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun i hi => ?_
  have hj' := Finset.mem_range.1 hj
  have hi' := Finset.mem_range.1 hi
  rw [hp j hj', hp i (by omega)]

section Certified

set_option linter.unusedSectionVars false

theorem pB_mem : pB ∈ NativeSporadic.M12 := Subgroup.subset_closure (by simp [pB])

theorem bfN_mem_M12 : bfN ∈ NativeSporadic.M12 := bfS_le_M12 bfN_mem
theorem bfE_mem_M12 : bfE ∈ NativeSporadic.M12 := bfS_le_M12 bfE_mem
theorem bfF_mem_M12 : bfF ∈ NativeSporadic.M12 := bfS_le_M12 bfF_mem

theorem sP_mem_M12 : sP ∈ NativeSporadic.M12 :=
  mul_mem (mul_mem (mul_mem pB_mem bfF_mem_M12) bfF_mem_M12) pB_mem

set_option maxRecDepth 100000 in
theorem sP_comm_bfJ : sP * bfJ = bfJ * sP := by decide

set_option maxRecDepth 100000 in
theorem sP_cube : sP ^ 3 = 1 := by decide

set_option maxRecDepth 100000 in
theorem sP_ne_one : sP ≠ 1 := by decide

theorem orderOf_sP : orderOf sP = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime sP_cube sP_ne_one

theorem bfS_comm_bfJ {x : Equiv.Perm (Fin 12)} (hx : x ∈ bfS) : x * bfJ = bfJ * x := by
  have h := bfS'_comm_Jelt (s := ⟨x, bfS_le_M12 hx⟩) hx
  exact congrArg Subtype.val h

@[expose] def Cgen : Subgroup (Equiv.Perm (Fin 12)) := closure {bfE, bfN, bfF, sP}

theorem Cgen_le : Cgen ≤ centralizerIn NativeSporadic.M12 bfJ := by
  rw [Cgen, closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rw [SetLike.mem_coe, mem_centralizerIn]
  rcases hx with rfl | rfl | rfl | rfl
  · exact ⟨bfE_mem_M12, bfS_comm_bfJ bfE_mem⟩
  · exact ⟨bfN_mem_M12, bfS_comm_bfJ bfN_mem⟩
  · exact ⟨bfF_mem_M12, bfS_comm_bfJ bfF_mem⟩
  · exact ⟨sP_mem_M12, sP_comm_bfJ⟩

theorem card_centralizerIn_bfJ : Nat.card (centralizerIn NativeSporadic.M12 bfJ) = 192 := by
  obtain ⟨c, hc, hJ⟩ := exists_conj_Jelt_m12Rep1
  have hJ' : bfJ = c * m12Rep1 * c⁻¹ := hJ
  rw [hJ', centralizerIn_conj _ hc, Subgroup.card_map_of_injective (MulAut.conj c).injective,
    card_centralizerIn_m12Rep1]

theorem bfS_le_Cgen : bfS ≤ Cgen := by
  rw [bfS, Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · exact subset_closure (by simp)
  · exact subset_closure (by simp)
  · exact subset_closure (by simp)

theorem sP_mem_Cgen : sP ∈ Cgen := subset_closure (by simp)

theorem Cgen_eq : Cgen = centralizerIn NativeSporadic.M12 bfJ := by
  apply le_antisymm Cgen_le
  have h64 : 64 ∣ Nat.card Cgen := by
    rw [← card_bfS]
    exact Subgroup.card_dvd_of_le bfS_le_Cgen
  have h3 : 3 ∣ Nat.card Cgen := by
    rw [← orderOf_sP]
    exact orderOf_dvd_natCard (⟨sP, sP_mem_Cgen⟩ : Cgen) |> fun h => by
      simpa [Subgroup.orderOf_mk] using h
  have h192 : 192 ∣ Nat.card Cgen := by
    have := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 64 3) h64 h3
    simpa using this
  have hpos : 0 < Nat.card Cgen := Nat.card_pos
  have hge : 192 ≤ Nat.card Cgen := Nat.le_of_dvd hpos h192
  exact (Subgroup.eq_of_le_of_card_ge Cgen_le (by rw [card_centralizerIn_bfJ]; exact hge)).ge

theorem tp_mem_yK {x : Table} (hx : x ∈ yGens) : tp 14 x ∈ yK := Spec.tp_mem_yK hx

theorem extHom_mem_yK_of (σ : Equiv.Perm (Fin 12)) (hx : tbl14 σ ∈ yGens) : extHom σ ∈ yK := by
  rw [← tp_tbl14_eq σ]
  exact tp_mem_yK hx

theorem tauP_mem_yK : tauP ∈ yK := by
  rw [← tp_tauT_eq]
  exact tp_mem_yK (by simp [yGens])

theorem tauPow_mem_yK (a : Multiplicative (ZMod 2)) : tauPow a ∈ yK :=
  pow_mem tauP_mem_yK _

theorem extHom_mem_yK {σ : Equiv.Perm (Fin 12)} (hσ : σ ∈ Cgen) : extHom σ ∈ yK := by
  refine Subgroup.closure_induction (p := fun x _ => extHom x ∈ yK) ?_ ?_ ?_ ?_ hσ
  · intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact extHom_mem_yK_of _ (by simp [yGens])
    · exact extHom_mem_yK_of _ (by simp [yGens])
    · exact extHom_mem_yK_of _ (by simp [yGens])
    · exact extHom_mem_yK_of _ (by simp [yGens])
  · rw [map_one]; exact one_mem _
  · intro x y _ _ hx hy
    rw [map_mul]; exact mul_mem hx hy
  · intro x _ hx
    rw [map_inv]; exact inv_mem hx

theorem gens_repr {x : Table} (hx : x ∈ yGens) :
    ∃ (a : Multiplicative (ZMod 2)) (σ : Equiv.Perm (Fin 12)), σ ∈ Cgen ∧
      tp 14 x = kapP (a, σ) := by
  have hx' := hx
  simp only [yGens, Array.mem_def, List.mem_cons, List.not_mem_nil, or_false,
    List.toList_toArray] at hx'
  have hext : ∀ σ : Equiv.Perm (Fin 12), x = tbl14 σ → tp 14 x = extHom σ := by
    intro σ hσ
    subst hσ
    exact tp_tbl14_eq σ
  have hgen : ∀ σ ∈ ({bfE, bfN, bfF, sP} : Set (Equiv.Perm (Fin 12))), x = tbl14 σ →
      ∃ (a : Multiplicative (ZMod 2)) (σ : Equiv.Perm (Fin 12)), σ ∈ Cgen ∧
        tp 14 x = kapP (a, σ) := by
    intro σ hσ hxσ
    refine ⟨1, σ, subset_closure hσ, ?_⟩
    rw [hext σ hxσ, kapP_apply, tauPow,
      show (Multiplicative.toAdd (1 : Multiplicative (ZMod 2))).val = 0 from rfl, pow_zero,
      one_mul]
  rcases hx' with rfl | rfl | rfl | rfl | rfl
  · refine ⟨Multiplicative.ofAdd 1, 1, one_mem _, ?_⟩
    rw [kapP_apply, tauPow_ofAdd_one, map_one, mul_one]
    exact tp_tauT_eq
  · exact hgen _ (by simp) rfl
  · exact hgen _ (by simp) rfl
  · exact hgen _ (by simp) rfl
  · exact hgen _ (by simp) rfl

theorem mem_yK_iff (z : Equiv.Perm (Fin 14)) :
    z ∈ yK ↔ ∃ (a : Multiplicative (ZMod 2)) (σ : Equiv.Perm (Fin 12)), σ ∈ Cgen ∧
      z = kapP (a, σ) := by
  constructor
  · intro hz
    refine Subgroup.closure_induction
      (p := fun z _ => ∃ (a : Multiplicative (ZMod 2)) (σ : Equiv.Perm (Fin 12)), σ ∈ Cgen ∧
        z = kapP (a, σ)) ?_ ?_ ?_ ?_ hz
    · rintro _ ⟨x, hx, rfl⟩
      exact gens_repr hx
    · exact ⟨1, 1, one_mem _, (map_one kapP).symm⟩
    · rintro _ _ _ _ ⟨a, σ, hσ, rfl⟩ ⟨b, τ, hτ, rfl⟩
      exact ⟨a * b, σ * τ, mul_mem hσ hτ, by rw [← map_mul]; rfl⟩
    · rintro _ _ ⟨a, σ, hσ, rfl⟩
      exact ⟨a⁻¹, σ⁻¹, inv_mem hσ, by rw [← map_inv]; rfl⟩
  · rintro ⟨a, σ, hσ, rfl⟩
    rw [kapP_apply]
    exact mul_mem (tauPow_mem_yK a) (extHom_mem_yK hσ)

end Certified

end CFSG.EvenSporadicStandard.M12Std.Yosh
