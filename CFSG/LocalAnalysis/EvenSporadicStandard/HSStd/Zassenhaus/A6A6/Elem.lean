module

public import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut
public import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.A6A6

open Subgroup

variable {W : Type*} [Group W]

@[expose] def fixSub (α : MulAut W) : Subgroup W where
  carrier := {w | α w = w}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at *
    rw [map_mul, ha, hb]
  one_mem' := map_one α
  inv_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq] at *
    rw [map_inv, ha]

theorem mem_fixSub {α : MulAut W} {w : W} : w ∈ fixSub α ↔ α w = w := Iff.rfl

theorem pow_apply_succ (α : MulAut W) (k : ℕ) (w : W) : (α ^ (k + 1)) w = α ((α ^ k) w) := by
  rw [pow_succ', MulAut.mul_apply]

theorem card_modEq_of_invariant [Finite W] {p n : ℕ} [Fact p.Prime] {α : MulAut W}
    (h : α ^ (p ^ n) = 1) (S : Set W) (hS : ∀ w ∈ S, α w ∈ S) :
    Nat.card S ≡ Nat.card ↥{w | w ∈ S ∧ α w = w} [MOD p] := by
  classical
  let f : Function.End S := fun s => ⟨α s, hS s s.2⟩
  have hf : ∀ (k : ℕ) (s : S), (((f ^ k) s : S) : W) = (α ^ k) s.1 := by
    intro k
    induction k with
    | zero => intro s; rfl
    | succ k ih =>
      intro s
      rw [pow_apply_succ, pow_succ', Function.End.mul_def]
      show ((f ((f ^ k) s) : S) : W) = _
      simp only [f]
      rw [ih]
  have hfp : f ^ (p ^ n) = 1 := by
    funext s
    apply Subtype.ext
    rw [hf, h]
    rfl
  have : Fintype S := Fintype.ofFinite S
  have := Equiv.Perm.card_fixedPoints_modEq (p := p) (n := n) hfp
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card] at this
  have e : ↥{w | w ∈ S ∧ α w = w} ≃ ↑f.fixedPoints :=
    { toFun := fun w => ⟨⟨w.1, w.2.1⟩, Subtype.ext w.2.2⟩
      invFun := fun s => ⟨s.1.1, s.1.2, congrArg Subtype.val s.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e]
  exact this

theorem card_modEq_fixSub [Finite W] {p n : ℕ} [Fact p.Prime] {α : MulAut W}
    (h : α ^ (p ^ n) = 1) : Nat.card W ≡ Nat.card (fixSub α) [MOD p] := by
  have := card_modEq_of_invariant h Set.univ (fun w _ => Set.mem_univ _)
  rw [Nat.card_univ] at this
  have hset : {w | w ∈ (Set.univ : Set W) ∧ α w = w} = ↑(fixSub α) := by
    ext; simp [fixSub]
  rwa [show Nat.card ↥{w | w ∈ (Set.univ : Set W) ∧ α w = w} = Nat.card (fixSub α) from
    Nat.card_congr (Equiv.subtypeEquivRight fun w => Set.ext_iff.1 hset w)] at this

theorem card_modEq_subgroup [Finite W] {p n : ℕ} [Fact p.Prime] {α : MulAut W}
    (h : α ^ (p ^ n) = 1) (K : Subgroup W) (hK : ∀ w ∈ K, α w ∈ K) :
    Nat.card K ≡ Nat.card ↥(K ⊓ fixSub α) [MOD p] := by
  have := card_modEq_of_invariant h (K : Set W) hK
  have hset : {w | w ∈ (K : Set W) ∧ α w = w} = ↑(K ⊓ fixSub α) := by
    ext; simp [fixSub]
  rwa [show Nat.card ↥{w | w ∈ (K : Set W) ∧ α w = w} = Nat.card ↥(K ⊓ fixSub α) from
    Nat.card_congr (Equiv.subtypeEquivRight fun w => Set.ext_iff.1 hset w)] at this

theorem card_subgroup_eq_two_pow [Finite W] {k : ℕ} (hW : Nat.card W = 2 ^ k) (K : Subgroup W) :
    ∃ j, j ≤ k ∧ Nat.card K = 2 ^ j := by
  have h := K.card_subgroup_dvd_card
  rw [hW] at h
  exact (Nat.dvd_prime_pow Nat.prime_two).1 h

theorem card_dvd_two_pow {K : Subgroup W} [Finite W] {k : ℕ} (hK : Nat.card K = 2 ^ k)
    (L : Subgroup W) (hL : L ≤ K) : ∃ j, j ≤ k ∧ Nat.card L = 2 ^ j := by
  have h := Subgroup.card_dvd_of_le hL
  rw [hK] at h
  exact (Nat.dvd_prime_pow Nat.prime_two).1 h

theorem card_fixSub_five_256 [Finite W] (hW : Nat.card W = 256) {α : MulAut W} (h : α ^ 5 = 1) :
    Nat.card (fixSub α) = 1 ∨ Nat.card (fixSub α) = 16 ∨ Nat.card (fixSub α) = 256 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hm := card_modEq_fixSub (p := 5) (n := 1) (α := α) (by simpa using h)
  obtain ⟨j, hj, hjc⟩ := card_subgroup_eq_two_pow (k := 8) (by rw [hW]; norm_num) (fixSub α)
  rw [hW, hjc] at hm
  rw [hjc]
  interval_cases j <;> simp_all [Nat.ModEq]

theorem card_fixSub_five_16 [Finite W] (hW : Nat.card W = 16) {α : MulAut W} (h : α ^ 5 = 1) :
    Nat.card (fixSub α) = 1 ∨ Nat.card (fixSub α) = 16 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hm := card_modEq_fixSub (p := 5) (n := 1) (α := α) (by simpa using h)
  obtain ⟨j, hj, hjc⟩ := card_subgroup_eq_two_pow (k := 4) (by rw [hW]; norm_num) (fixSub α)
  rw [hW, hjc] at hm
  rw [hjc]
  interval_cases j <;> simp_all [Nat.ModEq]

theorem card_fixSub_seven_16 [Finite W] (hW : Nat.card W = 16) {α : MulAut W} (h : α ^ 7 = 1) :
    Nat.card (fixSub α) = 2 ∨ Nat.card (fixSub α) = 16 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hm := card_modEq_fixSub (p := 7) (n := 1) (α := α) (by simpa using h)
  obtain ⟨j, hj, hjc⟩ := card_subgroup_eq_two_pow (k := 4) (by rw [hW]; norm_num) (fixSub α)
  rw [hW, hjc] at hm
  rw [hjc]
  interval_cases j <;> simp_all [Nat.ModEq]

theorem eq_one_of_card_fixSub [Finite W] {α : MulAut W} (h : Nat.card (fixSub α) = Nat.card W) :
    α = 1 := by
  have : fixSub α = ⊤ := Subgroup.card_eq_iff_eq_top _ |>.1 h
  ext w
  have hw : w ∈ fixSub α := this ▸ Subgroup.mem_top w
  exact hw

theorem α_pow_five {α : MulAut W} (h5 : α ^ 5 = 1) (w : W) :
    α (α (α (α (α w)))) = w := by
  have h := congrArg (fun f : MulAut W => f w) h5
  simpa [pow_succ, MulAut.mul_apply] using h

abbrev commGroupOfComm (hc : ∀ x y : W, x * y = y * x) : CommGroup W :=
  { (inferInstance : Group W) with mul_comm := hc }

@[expose] def norm5 (hc : ∀ x y : W, x * y = y * x) (α : MulAut W) : W →* W :=
  letI := commGroupOfComm hc
  { toFun := fun w => w * α w * α (α w) * α (α (α w)) * α (α (α (α w)))
    map_one' := by simp
    map_mul' := by
      intro x y
      simp only [map_mul]
      simp only [mul_assoc, mul_comm, mul_left_comm] }

theorem norm5_apply (hc : ∀ x y : W, x * y = y * x) (α : MulAut W) (w : W) :
    norm5 hc α w = w * α w * α (α w) * α (α (α w)) * α (α (α (α w))) := rfl

@[expose] def normSub (hc : ∀ x y : W, x * y = y * x) (α : MulAut W) : Subgroup W :=
  (norm5 hc α).ker

theorem mem_normSub (hc : ∀ x y : W, x * y = y * x) {α : MulAut W} {w : W} :
    w ∈ normSub hc α ↔ norm5 hc α w = 1 := MonoidHom.mem_ker

set_option linter.style.haveILetI false in
theorem apply_norm5 (hc : ∀ x y : W, x * y = y * x) {α : MulAut W} (h5 : α ^ 5 = 1) (w : W) :
    α (norm5 hc α w) = norm5 hc α w := by
  letI := commGroupOfComm hc
  rw [norm5_apply, map_mul, map_mul, map_mul, map_mul, α_pow_five h5]
  simp only [mul_comm, mul_left_comm]

theorem norm5_of_mem_fixSub (hc : ∀ x y : W, x * y = y * x) (hs : ∀ x : W, x * x = 1)
    {α : MulAut W} {w : W} (hw : w ∈ fixSub α) : norm5 hc α w = w := by
  rw [mem_fixSub] at hw
  rw [norm5_apply, hw, hw, hw, hw]
  have h1 := hs w
  calc w * w * w * w * w = (w * w) * (w * w) * w := by simp only [mul_assoc]
    _ = w := by rw [h1]; simp

theorem range_norm5 (hc : ∀ x y : W, x * y = y * x) (hs : ∀ x : W, x * x = 1)
    {α : MulAut W} (h5 : α ^ 5 = 1) : (norm5 hc α).range = fixSub α := by
  apply le_antisymm
  · rintro _ ⟨w, rfl⟩
    exact apply_norm5 hc h5 w
  · intro w hw
    exact ⟨w, norm5_of_mem_fixSub hc hs hw⟩

theorem card_fixSub_mul_card_normSub [Finite W] (hc : ∀ x y : W, x * y = y * x)
    (hs : ∀ x : W, x * x = 1) {α : MulAut W} (h5 : α ^ 5 = 1) :
    Nat.card (fixSub α) * Nat.card (normSub hc α) = Nat.card W := by
  have := Subgroup.card_ker_mul_card_range (norm5 hc α)
  rw [range_norm5 hc hs h5] at this
  rw [mul_comm]
  exact this

set_option linter.unusedVariables false in
theorem le_normSub (hc : ∀ x y : W, x * y = y * x) (hs : ∀ x : W, x * x = 1)
    {α : MulAut W} (h5 : α ^ 5 = 1) {U : Subgroup W}
    (hU : ∀ u ∈ U, α u ∈ U) (hfix : U ⊓ fixSub α = ⊥) : U ≤ normSub hc α := by
  intro u hu
  rw [mem_normSub]
  have h1 : norm5 hc α u ∈ U := by
    rw [norm5_apply]
    exact U.mul_mem (U.mul_mem (U.mul_mem (U.mul_mem hu (hU _ hu)) (hU _ (hU _ hu)))
      (hU _ (hU _ (hU _ hu)))) (hU _ (hU _ (hU _ (hU _ hu))))
  have h2 : norm5 hc α u ∈ fixSub α := apply_norm5 hc h5 u
  have h3 : norm5 hc α u ∈ U ⊓ fixSub α := ⟨h1, h2⟩
  rw [hfix] at h3
  exact h3

theorem apply_mem_fixSub_of_comm {α β : MulAut W} (h : α * β = β * α) {w : W}
    (hw : w ∈ fixSub α) : β w ∈ fixSub α := by
  rw [mem_fixSub] at hw ⊢
  have := congrArg (fun f : MulAut W => f w) h
  simp only [MulAut.mul_apply, hw] at this
  exact this

theorem apply_mem_normSub_of_comm (hc : ∀ x y : W, x * y = y * x) {α β : MulAut W}
    (h : α * β = β * α) {w : W} (hw : w ∈ normSub hc α) : β w ∈ normSub hc α := by
  rw [mem_normSub] at hw ⊢
  have h' : ∀ x, α (β x) = β (α x) := fun x => by
    have := congrArg (fun f : MulAut W => f x) h
    simpa [MulAut.mul_apply] using this
  rw [norm5_apply] at hw ⊢
  simp only [h', ← map_mul]
  rw [hw, map_one]

theorem card_modEq_one_of_fixSub_eq_bot [Finite W] {p n : ℕ} [Fact p.Prime] {α : MulAut W}
    (h : α ^ (p ^ n) = 1) (hfix : fixSub α = ⊥) (K : Subgroup W) (hK : ∀ w ∈ K, α w ∈ K) :
    Nat.card K ≡ 1 [MOD p] := by
  have := card_modEq_subgroup h K hK
  rwa [hfix, inf_bot_eq, Subgroup.card_bot] at this

@[expose] def diffHom (hc : ∀ x y : W, x * y = y * x) (β : MulAut W) : W →* W :=
  letI := commGroupOfComm hc
  { toFun := fun w => β w * w⁻¹
    map_one' := by simp
    map_mul' := by
      intro x y
      simp only [map_mul, mul_inv_rev]
      simp only [mul_assoc, mul_comm, mul_left_comm] }

theorem diffHom_apply (hc : ∀ x y : W, x * y = y * x) (β : MulAut W) (w : W) :
    diffHom hc β w = β w * w⁻¹ := rfl

theorem mem_ker_diffHom (hc : ∀ x y : W, x * y = y * x) {β : MulAut W} {w : W} :
    w ∈ (diffHom hc β).ker ↔ w ∈ fixSub β := by
  rw [MonoidHom.mem_ker, diffHom_apply, mem_fixSub, mul_inv_eq_one]

theorem sq_eq_one_of_comm_of_fixSub_eq_bot [Finite W] (hc : ∀ x y : W, x * y = y * x)
    (hs : ∀ x : W, x * x = 1) (hW : Nat.card W = 256) {α β : MulAut W}
    (h5 : α ^ 5 = 1) (hfix : fixSub α = ⊥) (hcomm : α * β = β * α) {n : ℕ}
    (h2 : β ^ (2 ^ n) = 1) : β ^ 2 = 1 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h5' : α ^ (5 ^ 1) = 1 := by simpa using h5
  have hKinv : ∀ w ∈ fixSub β, α w ∈ fixSub β := fun w hw =>
    apply_mem_fixSub_of_comm (α := β) (β := α) hcomm.symm hw
  have hK5 := card_modEq_one_of_fixSub_eq_bot h5' hfix (fixSub β) hKinv
  have hK2 := card_modEq_fixSub (p := 2) (n := n) (α := β) h2
  rw [hW] at hK2
  obtain ⟨j, hj, hjc⟩ := card_subgroup_eq_two_pow (k := 8) (by rw [hW]; norm_num) (fixSub β)
  rw [hjc] at hK5 hK2
  have hj' : j = 0 ∨ j = 4 ∨ j = 8 := by
    interval_cases j <;> simp_all [Nat.ModEq]
  have hj0 : j ≠ 0 := by
    rintro rfl
    simp [Nat.ModEq] at hK2
  rcases hj' with h0 | h4 | h8
  · exact absurd h0 hj0
  swap
  · have : Nat.card (fixSub β) = Nat.card W := by rw [hjc, hW, h8]; norm_num
    have := eq_one_of_card_fixSub this
    rw [this]; simp
  ·
    have hK : Nat.card (fixSub β) = 16 := by rw [hjc, h4]; norm_num
    set ν := diffHom hc β with hν
    have hker : ν.ker = fixSub β := by
      ext w; exact mem_ker_diffHom hc
    have hI := Subgroup.card_ker_mul_card_range ν
    rw [hker, hK, hW] at hI
    have hIc : Nat.card ν.range = 16 := by omega
    have hcom : ∀ x, β (α x) = α (β x) := fun x => by
      have := congrArg (fun f : MulAut W => f x) hcomm
      simpa [MulAut.mul_apply] using this.symm
    have hνα : ∀ x, ν (α x) = α (ν x) := fun x => by
      simp only [hν, diffHom_apply, map_mul, map_inv, hcom]
    have hνβ : ∀ x, ν (β x) = β (ν x) := fun x => by
      simp only [hν, diffHom_apply, map_mul, map_inv]
    have hIα : ∀ w ∈ ν.range, α w ∈ ν.range := by
      rintro _ ⟨x, rfl⟩
      exact ⟨α x, hνα x⟩
    have hIβ : ∀ w ∈ ν.range, β w ∈ ν.range := by
      rintro _ ⟨x, rfl⟩
      exact ⟨β x, hνβ x⟩
    set J := ν.range ⊓ fixSub β with hJ
    have hJα : ∀ w ∈ J, α w ∈ J := fun w hw =>
      ⟨hIα w hw.1, hKinv w hw.2⟩
    have hJ5 : Nat.card J ≡ 1 [MOD 5] :=
      card_modEq_one_of_fixSub_eq_bot h5' hfix J hJα
    have hJ2 : Nat.card ν.range ≡ Nat.card J [MOD 2] :=
      card_modEq_subgroup (α := β) (p := 2) (n := n) h2 ν.range hIβ
    rw [hIc] at hJ2
    obtain ⟨i, hi, hic⟩ := card_dvd_two_pow (K := fixSub β) (k := 4) (by rw [hK]; norm_num)
      J inf_le_right
    rw [hic] at hJ5 hJ2
    have hi4 : i = 4 := by
      interval_cases i <;> simp_all [Nat.ModEq]
    have hJc : Nat.card J = 16 := by rw [hic, hi4]; norm_num
    have hJI : J = ν.range := by
      apply Subgroup.eq_of_le_of_card_ge inf_le_left
      rw [hJc, hIc]
    have hIK : ν.range ≤ fixSub β := by
      rw [← hJI]; exact inf_le_right
    ext w
    have h1 : β (ν w) = ν w := hIK ⟨w, rfl⟩
    rw [pow_two, MulAut.mul_apply, MulAut.one_apply]
    simp only [hν, diffHom_apply, map_mul, map_inv] at h1
    have hw1 : (w : W)⁻¹ = w := inv_eq_of_mul_eq_one_right (hs w)
    have hw2 : (β w)⁻¹ = β w := inv_eq_of_mul_eq_one_right (hs (β w))
    rw [hw1, hw2] at h1
    have h3 : β (β w) * β w = w * β w := by
      rw [h1, hc]
    exact mul_right_cancel h3

theorem fixSub_eq_bot_of_comm [Finite W] (hW : Nat.card W = 16) {α β : MulAut W}
    (h5 : α ^ 5 = 1) (hα : α ≠ 1) (hcomm : α * β = β * α) (hβ : β ≠ 1) : fixSub β = ⊥ := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h5' : α ^ (5 ^ 1) = 1 := by simpa using h5
  have hfa : fixSub α = ⊥ := by
    rcases card_fixSub_five_16 hW h5 with h | h
    · exact Subgroup.eq_bot_of_card_eq _ h
    · exact absurd (eq_one_of_card_fixSub (by rw [h, hW])) hα
  have hKinv : ∀ w ∈ fixSub β, α w ∈ fixSub β := fun w hw =>
    apply_mem_fixSub_of_comm (α := β) (β := α) hcomm.symm hw
  have hK5 := card_modEq_one_of_fixSub_eq_bot h5' hfa (fixSub β) hKinv
  obtain ⟨j, hj, hjc⟩ := card_subgroup_eq_two_pow (k := 4) (by rw [hW]; norm_num) (fixSub β)
  rw [hjc] at hK5
  have hj04 : j = 0 ∨ j = 4 := by
    interval_cases j <;> simp_all [Nat.ModEq]
  have hj0 : j = 0 := by
    rcases hj04 with h | h
    · exact h
    · exact absurd (eq_one_of_card_fixSub (by rw [hjc, hW, h]; norm_num)) hβ
  exact Subgroup.eq_bot_of_card_eq _ (by rw [hjc, hj0]; norm_num)

theorem eq_one_of_perfect_of_comm [Finite W] (hW : Nat.card W = 16) {α : MulAut W}
    (h5 : α ^ 5 = 1) (hα : α ≠ 1) {H : Type*} [Group H] [Finite H] (hH : commutator H = ⊤)
    (ψ : H →* MulAut W) (hcomm : ∀ h, α * ψ h = ψ h * α) : ∀ h, ψ h = 1 := by
  have : Group.IsPerfect H := ⟨hH⟩
  have : Finite ψ.range := Finite.of_surjective ψ.rangeRestrict ψ.rangeRestrict_surjective
  have hodd : Odd (Nat.card ψ.range) := by
    by_contra hne
    have h2 : 2 ∣ Nat.card ψ.range := by
      rw [Nat.not_odd_iff_even] at hne
      exact even_iff_two_dvd.1 hne
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2
    obtain ⟨h, hh⟩ := x.2
    have hβ1 : (x : MulAut W) ≠ 1 := by
      intro h1
      have : x = 1 := Subtype.ext h1
      rw [this, orderOf_one] at hx
      omega
    have hβ2 : (x : MulAut W) ^ (2 ^ 1) = 1 := by
      have := pow_orderOf_eq_one x
      rw [hx] at this
      have := congrArg Subtype.val this
      simpa using this
    have hfb : fixSub (x : MulAut W) = ⊥ :=
      fixSub_eq_bot_of_comm hW h5 hα (by rw [← hh]; exact hcomm h) hβ1
    have hm := card_modEq_fixSub (p := 2) (n := 1) (α := (x : MulAut W)) hβ2
    rw [hfb, Subgroup.card_bot, hW] at hm
    simp [Nat.ModEq] at hm
  have hsolv : Group.IsSolvable ψ.range := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have : Group.IsPerfect ψ.range := Group.IsPerfect.range ψ
  have htriv : Subsingleton ψ.range := by
    by_contra hns
    rw [not_subsingleton_iff_nontrivial] at hns
    exact Group.IsPerfect.not_isSolvable ψ.range hsolv
  intro h
  have := htriv.elim (⟨ψ h, h, rfl⟩ : ψ.range) 1
  exact congrArg Subtype.val this

@[expose] def restrictAut {H : Type*} [Group H] (ψ : H →* MulAut W) (U : Subgroup W)
    (hU : ∀ h : H, ∀ u ∈ U, ψ h u ∈ U) : H →* MulAut U where
  toFun h :=
    { toFun := fun u => ⟨ψ h u, hU h u u.2⟩
      invFun := fun u => ⟨ψ h⁻¹ u, hU h⁻¹ u u.2⟩
      left_inv := fun u => by
        apply Subtype.ext
        show ψ h⁻¹ (ψ h u) = u
        rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]
      right_inv := fun u => by
        apply Subtype.ext
        show ψ h (ψ h⁻¹ u) = u
        rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
      map_mul' := fun x y => by
        apply Subtype.ext
        show ψ h (x * y : W) = ψ h x * ψ h y
        rw [map_mul] }
  map_one' := by
    ext u
    show ψ 1 u = u
    rw [map_one, MulAut.one_apply]
  map_mul' := fun x y => by
    ext u
    show ψ (x * y) u = ψ x (ψ y u)
    rw [map_mul, MulAut.mul_apply]

theorem restrictAut_apply {H : Type*} [Group H] (ψ : H →* MulAut W) (U : Subgroup W)
    (hU : ∀ h : H, ∀ u ∈ U, ψ h u ∈ U) (h : H) (u : U) :
    ((restrictAut ψ U hU h u : U) : W) = ψ h u := rfl

theorem card_mulAut_sixteen [Finite W] (hc : ∀ x y : W, x * y = y * x)
    (hs : ∀ x : W, x * x = 1) (hW : Nat.card W = 16) : Nat.card (MulAut W) = 20160 := by
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2) (W := W) hc
    (fun a => by rw [pow_two]; exact hs a) (n := 4) (by rw [hW]; norm_num)
  rw [CFSG.SectionRank.Ccomm.card_mulAut_eq_card_GL e, CFSG.SectionRank.Ccomm.card_GL_zmod]
  simp [Fin.prod_univ_four]

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.A6A6
