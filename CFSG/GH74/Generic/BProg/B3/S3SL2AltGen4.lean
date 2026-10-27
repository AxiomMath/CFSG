module

public import CFSG.GH74.Generic.BProg.B3.S3SL2AltTw
public import CFSG.GH74.Generic.BProg.B3.S3SL2AltV

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.Blueprint Subgroup Equiv Equiv.Perm
open scoped commutatorElement

namespace S3SL2AltGen4

open S3SL2AltTw S3SL2AltV

variable {Y : Type} [Group Y] [Finite Y] {H : Subgroup Y} {n : ℕ} {s : Y}
  {hsN : s ∈ normalizer (H : Set Y)}

theorem not_gen4_of_outer (S : AltSetting H n hsN) (hn : 8 ≤ n) (hss : s * s = 1) (hsH : s ∉ H)
    (τ : Perm (Fin n)) (hτ2 : τ * τ = 1) (hτpar : Perm.sign τ = Perm.sign S.σ)
    (hτc : ∀ i : Fin 4, τ * ((vEmb hn i : alternatingGroup (Fin n)) : Perm (Fin n)) =
      ((vEmb hn i : alternatingGroup (Fin n)) : Perm (Fin n)) * τ) :
    ¬ Gen4 Y := by
  classical
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
  obtain ⟨xs, hxs⟩ : ∃ xs : Fin 4 → ↥H, ∀ i, S.π (xs i) = vEmb hn i :=
    ⟨fun i => (S.surj (vEmb hn i)).choose, fun i => (S.surj _).choose_spec⟩
  have hapar : Perm.sign (τ * S.σ) = 1 := by
    rw [Perm.sign_mul, hτpar]
    exact Int.units_mul_self _
  obtain ⟨wa, hwa⟩ := S.surj ⟨τ * S.σ, (Equiv.Perm.mem_alternatingGroup).2 hapar⟩
  have hwa' : ((S.π wa : alternatingGroup (Fin n)) : Perm (Fin n)) = τ * S.σ := by rw [hwa]
  set x5 : Y := (wa : Y) * s with hx5
  have T5 : Tw S x5 τ := by
    have h := tw_mul_s (S := S) wa
    have e : ((S.π wa : alternatingGroup (Fin n)) : Perm (Fin n)) * S.σ = τ := by
      rw [hwa', mul_assoc, S.σ_sq, mul_one]
    rwa [e] at h
  have T4 : ∀ i : Fin 4, Tw S (xs i : Y) (vEmb hn i : Perm (Fin n)) := fun i => by
    have h := tw_of_mem (S := S) (xs i)
    rwa [hxs i] at h
  let x : Fin 5 → Y := Fin.snoc (fun i : Fin 4 => (xs i : Y)) x5
  let τx : Fin 5 → Perm (Fin n) := Fin.snoc (fun i : Fin 4 => (vEmb hn i : Perm (Fin n))) τ
  have hxl : x (Fin.last 4) = x5 := Fin.snoc_last _ _
  have hxc : ∀ j : Fin 4, x (Fin.castSucc j) = (xs j : Y) := fun j => Fin.snoc_castSucc _ _ _
  have hτl : τx (Fin.last 4) = τ := Fin.snoc_last _ _
  have hτc' : ∀ j : Fin 4, τx (Fin.castSucc j) = (vEmb hn j : Perm (Fin n)) :=
    fun j => Fin.snoc_castSucc _ _ _
  have hTx : ∀ i, Tw S (x i) (τx i) := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [hxl, hτl]; exact T5
    · rw [hxc, hτc']; exact T4 j
  have hnorm : ∀ i, x i ∈ normalizer (Nsub H : Set Y) := fun i => (hTx i).normalizer
  have hsq4 : ∀ i : Fin 4, (xs i : Y) ^ 2 ∈ Nsub H := by
    intro i
    have : (xs i : Y) ^ 2 = (((xs i) ^ 2 : ↥H) : Y) := rfl
    rw [this, mem_Nsub_iff S, map_pow, hxs i]
    apply Subtype.ext
    simpa [pow_two] using congrArg Subtype.val (vEmb_sq hn i)
  have hsq5 : x5 ^ 2 ∈ Nsub H := by
    have h1 : x5 ^ 2 = ((wa * S3SL2Basic.actH H hsN wa : ↥H) : Y) := by
      rw [hx5, pow_two]
      simp only [Subgroup.coe_mul, S3SL2Basic.actH_apply, hsinv, mul_assoc]
    rw [h1, mem_Nsub_iff S, map_mul]
    apply Subtype.ext
    simp only [Subgroup.coe_mul, S.act, hwa', OneMemClass.coe_one, S.σ_inv]
    calc τ * S.σ * (S.σ * (τ * S.σ) * S.σ) = τ * (S.σ * S.σ) * τ * (S.σ * S.σ) := by group
      _ = 1 := by rw [S.σ_sq]; simpa using hτ2
  have hsq : ∀ i, x i ^ 2 ∈ Nsub H := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [hxl]; exact hsq5
    · rw [hxc]; exact hsq4 j
  have hcomm_aux : ∀ (i : Fin 5) (j : Fin 4), ⁅x i, (xs j : Y)⁆ ∈ Nsub H := by
    intro i j
    refine (hTx i).comm_mem (xs j) ?_
    rw [hxs j]
    refine Fin.lastCases ?_ (fun k => ?_) i
    · rw [hτl]; exact hτc j
    · rw [hτc']; exact congrArg Subtype.val (vEmb_comm hn k j)
  have hcomm : ∀ i j, ⁅x i, x j⁆ ∈ Nsub H := by
    intro i j
    refine Fin.lastCases ?_ (fun k => ?_) j
    · refine Fin.lastCases ?_ (fun l => ?_) i
      · rw [hxl, commutatorElement_self]; exact Subgroup.one_mem _
      · have h := Subgroup.inv_mem _ (hcomm_aux (Fin.last 4) l)
        rw [commutatorElement_inv, hxl] at h
        rw [hxl, hxc]; exact h
    · rw [hxc]; exact hcomm_aux i k
  have hker : ∀ a : Fin 5 → Fin 2, a ≠ 0 →
      (List.ofFn fun i => x i ^ (a i : ℕ)).prod ∉ Nsub H := by
    intro a ha hmem
    set w : ↥H := (List.ofFn fun i : Fin 4 => (xs i) ^ ((a (Fin.castSucc i) : Fin 2) : ℕ)).prod
      with hw
    have hwY : (w : Y) =
        (List.ofFn fun i : Fin 4 => (xs i : Y) ^ ((a (Fin.castSucc i) : Fin 2) : ℕ)).prod := by
      simp [hw]
    have hprod : (List.ofFn fun i => x i ^ (a i : ℕ)).prod =
        (w : Y) * x5 ^ ((a (Fin.last 4) : Fin 2) : ℕ) := by
      rw [List.ofFn_succ', List.prod_concat, hwY]
      simp only [hxc, hxl]
    rw [hprod] at hmem
    rcases Fin.exists_fin_two.1 ⟨a (Fin.last 4), rfl⟩ with he | he
    ·
      rw [he] at hmem
      simp only [Fin.val_zero, pow_zero, mul_one] at hmem
      have h1 : S.π w = 1 := (mem_Nsub_iff S w).1 hmem
      have h2 : (List.ofFn fun i : Fin 4 =>
          (vEmb hn i) ^ ((a (Fin.castSucc i) : Fin 2) : ℕ)).prod = 1 := by
        rw [← h1, hw, map_list_prod, List.map_ofFn]
        refine congrArg (fun f => (List.ofFn f).prod) (funext fun i => ?_)
        simp [hxs]
      have h3 : (fun i : Fin 4 => a (Fin.castSucc i)) = 0 := by
        by_contra hne
        exact vEmb_ker hn _ hne h2
      apply ha
      funext i
      refine Fin.lastCases ?_ (fun k => ?_) i
      · simpa using he
      · simpa using congrFun h3 k
    ·
      rw [he] at hmem
      simp only [Fin.val_one, pow_one] at hmem
      have hmemH : (w : Y) * x5 ∈ H := Nsub_le H hmem
      have hx5H : x5 ∈ H := by
        have := mul_mem (inv_mem w.2) hmemH
        simpa using this
      apply hsH
      have := mul_mem (inv_mem wa.2) hx5H
      simpa [hx5, mul_assoc] using this
  exact (rankCertified_of_section_involutions (Nsub H) x hnorm hsq hcomm hker (s := 4)
    (by norm_num)).not_gen4 le_rfl

end S3SL2AltGen4

end CFSG.GH74.Generic.BProg.B3
