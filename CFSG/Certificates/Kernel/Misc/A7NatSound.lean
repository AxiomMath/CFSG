module

public import Certificates.Data.Kernel.Misc.A7Nat
public import CFSG.Certificates.Kernel.LocalQTPermSound
public import CFSG.Quasithin.Vol2.Ch12Sec8OneA7Raw
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.KC.A7Nat

open Equiv Finset CFSG.KD.A7Nat CFSG.KC.LQT.P CFSG.KC.Ord CFSG.Quasithin.H13.A7Mod

theorem h7 : (7 : ℕ) ≤ 32 := by norm_num

theorem iffB_iff {a b : Bool} : iffB a b = true ↔ (a = true ↔ b = true) := by
  cases a <;> cases b <;> simp [iffB, notB]

theorem memL_iff (x : ℕ) (L : List ℕ) : memL x L = true ↔ x ∈ L := by
  rw [memL, anyL_iff]
  simp [beq_iff]

theorem nodupL_iff : ∀ L : List ℕ, nodupL L = true → L.Nodup
  | [] => fun _ => List.nodup_nil
  | x :: t => fun h => by
    change andB (notB (memL x t)) (nodupL t) = true at h
    rw [andB_iff, notB_iff, memL_iff] at h
    exact List.nodup_cons.2 ⟨h.1, nodupL_iff t h.2⟩

theorem cntL_eq (f : ℕ → Bool) : ∀ L : List ℕ, cntL f L = L.countP f
  | [] => rfl
  | x :: t => by
    change Nat.add (Bool.rec (motive := fun _ => ℕ) 0 1 (f x)) (cntL f t) = _
    rw [cntL_eq f t, List.countP_cons]
    cases f x <;> simp [Nat.add_comm]

@[expose] def vv (u : Fin 7 → ZMod 2) (i : ℕ) : ℕ := if h : i < 7 then (u ⟨i, h⟩).val else 0

@[expose] noncomputable def vcode (u : Fin 7 → ZMod 2) : ℕ := ofFn 7 (vv u)

theorem vv_lt (u : Fin 7 → ZMod 2) : ∀ i < 7, vv u i < 2 := fun i hi => by
  simp only [vv, hi, ↓reduceDIte]
  exact ZMod.val_lt _

theorem vcode_eq (u : Fin 7 → ZMod 2) : vcode u = E (vv u) 7 := ofFn_eq 7 (vv u)

theorem img_vcode' (u : Fin 7 → ZMod 2) {i : ℕ} (hi : i < 7) : img (vcode u) i = vv u i := by
  rw [img_eq, vcode_eq, E_digit (fun j hj => by have := vv_lt u j hj; omega) hi]

theorem img_vcode (u : Fin 7 → ZMod 2) (i : Fin 7) : img (vcode u) i = (u i).val := by
  rw [img_vcode' u i.isLt]
  simp [vv, i.isLt]

theorem vcode_inj {u w : Fin 7 → ZMod 2} (h : vcode u = vcode w) : u = w := by
  funext i
  apply ZMod.val_injective
  rw [← img_vcode, ← img_vcode, h]

theorem allVd_iff (f : ℕ → Bool) : ∀ (k acc : ℕ),
    allVd f k acc = true ↔ ∀ b : ℕ → ℕ, (∀ i < k, b i < 2) → f (acc + E b k) = true
  | 0, acc => by
    change f acc = true ↔ _
    simp only [E_zero, add_zero]
    exact ⟨fun h _ _ => h, fun h => h (fun _ => 0) (fun i hi => absurd hi (Nat.not_lt_zero i))⟩
  | k + 1, acc => by
    change andB (allVd f k acc) (allVd f k (Nat.add acc (Nat.shiftLeft 1 (Nat.mul 5 k)))) = true ↔ _
    rw [andB_iff, shl_eq, allVd_iff f k, allVd_iff f k]
    constructor
    · rintro ⟨h0, h1⟩ b hb
      have hb' : ∀ i < k, b i < 2 := fun i hi => hb i (by omega)
      have hk := hb k (by omega)
      rw [E_succ]
      rcases (by omega : b k = 0 ∨ b k = 1) with e | e
      · rw [e, zero_mul, add_zero]
        exact h0 b hb'
      · have := h1 b hb'
        rw [e]
        rwa [show Nat.add acc (1 * 32 ^ k) + E b k = acc + (E b k + 1 * 32 ^ k) by
          change acc + 1 * 32 ^ k + E b k = _
          ring] at this
    · intro h
      refine ⟨fun b hb => ?_, fun b hb => ?_⟩
      · have := h (fun i => if i < k then b i else 0)
          (fun i hi => by by_cases hik : i < k <;> simp [hik, hb])
        rwa [E_succ, if_neg (lt_irrefl k), zero_mul, add_zero,
          E_congr (g := b) (fun i hi => by simp [hi])] at this
      · have := h (fun i => if i < k then b i else 1)
          (fun i hi => by by_cases hik : i < k <;> simp [hik, hb])
        rw [E_succ, if_neg (lt_irrefl k), E_congr (g := b) (fun i hi => by simp [hi])] at this
        rwa [show Nat.add acc (1 * 32 ^ k) + E b k = acc + (E b k + 1 * 32 ^ k) by
          change acc + 1 * 32 ^ k + E b k = _
          ring]

theorem allV_iff (f : ℕ → Bool) : allV f = true ↔ ∀ u : Fin 7 → ZMod 2, f (vcode u) = true := by
  rw [allV, allVd_iff]
  constructor
  · intro h u
    have := h (vv u) (vv_lt u)
    rwa [zero_add, ← vcode_eq] at this
  · intro h b hb
    have e : vcode (fun i => (b i : ZMod 2)) = E b 7 := by
      rw [vcode_eq]
      refine E_congr fun i hi => ?_
      simp only [vv, hi, ↓reduceDIte, ZMod.val_natCast]
      exact Nat.mod_eq_of_lt (hb i hi)
    rw [zero_add, ← e]
    exact h _

theorem natCast_two_eq_zero (k : ℕ) : ((k : ℕ) : ZMod 2) = 0 ↔ k % 2 = 0 := by
  rw [← Nat.cast_zero, ZMod.natCast_eq_natCast_iff']

theorem sum_val (u : Fin 7 → ZMod 2) : ∑ i, u i = ((∑ i, (u i).val : ℕ) : ZMod 2) := by
  simp [Nat.cast_sum, ZMod.natCast_zmod_val]

theorem evenV_iff (u : Fin 7 → ZMod 2) : evenV (vcode u) = true ↔ ∑ i, u i = 0 := by
  have e : ones (vcode u) 7 = ∑ i, (u i).val := by
    rw [ones, rec_sum, ← Fin.sum_univ_eq_sum_range (fun i => img (vcode u) i)]
    exact sum_congr rfl fun i _ => img_vcode u i
  rw [evenV, beq_iff, sum_val, natCast_two_eq_zero, ← e]
  rfl

theorem fix_inv_iff (σ : Perm (Fin 7)) (u : Fin 7 → ZMod 2) :
    (∀ i, u (σ⁻¹ i) = u i) ↔ ∀ i, u (σ i) = u i := by
  constructor
  · intro h i
    simpa using (h (σ i)).symm
  · intro h i
    simpa using (h (σ⁻¹ i)).symm

theorem fixV_iff (σ : Perm (Fin 7)) (u : Fin 7 → ZMod 2) :
    fixV (code σ) (vcode u) = true ↔ ∀ i, u (σ⁻¹ i) = u i := by
  rw [fixV, allN_fin, fix_inv_iff]
  refine forall_congr' fun i => ?_
  rw [img_code h7, img_vcode, img_vcode, beq_iff]
  exact ZMod.val_injective _ |>.eq_iff

theorem zeroOn_iff {J : Finset (Fin 7)} {j : ℕ} (hJ : ∀ i : Fin 7, i ∈ J ↔ bitJ j i = true)
    (u : Fin 7 → ZMod 2) : zeroOn j (vcode u) = true ↔ ∀ i ∈ J, u i = 0 := by
  rw [zeroOn, allN_fin]
  refine forall_congr' fun i => ?_
  rw [impB_iff, hJ, img_vcode, beq_iff, ZMod.val_eq_zero]

theorem dotV_iff (w u : Fin 7 → ZMod 2) :
    Nat.beq (Nat.mod (dotV (vcode w) (vcode u)) 2) 0 = true ↔ ∑ i, w i * u i = 0 := by
  have e : dotV (vcode w) (vcode u) = ∑ i, (w i).val * (u i).val := by
    change Nat.rec (motive := fun _ => ℕ) 0
      (fun i acc => Nat.add acc (Nat.mul (img (vcode w) i) (img (vcode u) i))) 7 = _
    rw [rec_sum (fun i => Nat.mul (img (vcode w) i) (img (vcode u) i)),
      ← Fin.sum_univ_eq_sum_range (fun i => Nat.mul (img (vcode w) i) (img (vcode u) i))]
    exact sum_congr rfl fun i _ => by rw [img_vcode, img_vcode]; rfl
  have e2 : ∑ i, w i * u i = ((∑ i, (w i).val * (u i).val : ℕ) : ZMod 2) := by
    simp [Nat.cast_sum, ZMod.natCast_zmod_val]
  rw [beq_iff, e, e2, natCast_two_eq_zero]
  rfl

theorem vcomp_code (u : Fin 7 → ZMod 2) (π : Perm (Fin 7)) :
    vcomp (vcode u) (code π) = vcode (u ∘ π) := by
  rw [vcomp, ofFn_eq, vcode_eq (u ∘ π)]
  refine E_congr fun i hi => ?_
  have e : img (code π) i = (π ⟨i, hi⟩ : ℕ) := img_code h7 π ⟨i, hi⟩
  rw [e, img_vcode]
  simp [vv, hi]

def six (p : Fin 7) : Fin 7 → ZMod 2 := fun i => if i = p then 0 else 1

theorem vcode_six (p : Fin 7) :
    vcode (six p) = Nat.sub 1108378657 (Nat.shiftLeft 1 (Nat.mul 5 p)) := by
  fin_cases p <;> decide +kernel

theorem sixB_iff (u : Fin 7 → ZMod 2) :
    sixB (vcode u) = true ↔ ∃ p : Fin 7, ∀ i, u i = if i = p then 0 else 1 := by
  rw [sixB, anyN_fin]
  refine exists_congr fun p => ?_
  rw [beq_iff, ← vcode_six]
  exact ⟨fun h i => congrFun (vcode_inj h) i, fun h => congrArg vcode (funext h)⟩

def St (u : Fin 7 → ZMod 2) : ℕ :=
  (univ.filter fun σ : Perm (Fin 7) => Perm.sign σ = 1 ∧ ∀ i, u (σ⁻¹ i) = u i).card

theorem stab_comp (u : Fin 7 → ZMod 2) (π : Perm (Fin 7)) : St (u ∘ π) = St u := by
  refine card_bij' (fun σ _ => π * σ * π⁻¹) (fun τ _ => π⁻¹ * τ * π) ?_ ?_ ?_ ?_
  · intro σ hσ
    simp only [mem_filter, mem_univ, true_and] at hσ ⊢
    refine ⟨by rw [Perm.sign_mul, Perm.sign_mul, Perm.sign_inv, hσ.1, mul_one,
      Int.units_mul_self], fun j => ?_⟩
    have := hσ.2 (π⁻¹ j)
    simpa [mul_inv_rev, Perm.mul_apply] using this
  · intro τ hτ
    simp only [mem_filter, mem_univ, true_and] at hτ ⊢
    refine ⟨by rw [Perm.sign_mul, Perm.sign_mul, Perm.sign_inv, hτ.1, mul_one,
      Int.units_mul_self], fun j => ?_⟩
    have := hτ.2 (π j)
    simpa [mul_inv_rev, Perm.mul_apply] using this
  · intro σ _
    simp [mul_assoc]
  · intro τ _
    simp [mul_assoc]

theorem stabK_eq (u : Fin 7 → ZMod 2) : stabK (vcode u) = St u := by
  rw [stabK, cntP_eq h7, St]
  refine congrArg card (filter_congr fun σ _ => ?_)
  rw [andB_iff, even_code h7, fixV_iff, and_comm]

theorem vcode_zero : vcode 0 = 0 := by decide +kernel

theorem stabK_zero : stabK 0 = 2520 := by
  rw [← vcode_zero, stabK_eq, St]
  have e : (univ.filter fun σ : Perm (Fin 7) =>
      Perm.sign σ = 1 ∧ ∀ i, (0 : Fin 7 → ZMod 2) (σ⁻¹ i) = (0 : Fin 7 → ZMod 2) i) =
      univ.filter fun σ => Perm.sign σ = 1 :=
    filter_congr fun σ _ => by simp
  have h := card_alternatingGroup (α := Fin 7)
  rw [Fintype.card_fin] at h
  rw [e, ← Fintype.card_subtype]
  exact (Fintype.card_congr (Equiv.subtypeEquivRight fun σ => Equiv.Perm.mem_alternatingGroup)).symm.trans
    (h.trans (by decide))

theorem stabT_eq (h2 : stabK 33 = 120) (h4 : stabK 33825 = 72)
    (h6 : stabK 34636833 = 360) {r : ℕ} (hr : r ∈ reps) : stabT r = stabK r := by
  simp only [reps, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [stabK_zero]
    rfl
  · rw [h2]
    rfl
  · rw [h4]
    rfl
  · rw [h6]
    rfl

theorem stab_conj (h2 : stabK 33 = 120) (h4 : stabK 33825 = 72)
    (h6 : stabK 34636833 = 360) (ho : orbK = true) :
    ∀ v : Fin 7 → ZMod 2, ∑ i, v i = 0 →
      ((Finset.univ.filter fun σ : Equiv.Perm (Fin 7) =>
          Equiv.Perm.sign σ = 1 ∧ ∀ i, v (σ⁻¹ i) = v i).card = 360 ↔
        ∃ p : Fin 7, ∀ i, v i = if i = p then 0 else 1) := by
  intro v hv
  have h := (allV_iff _).1 ho v
  rw [orbFW, impB_iff, letB_eq] at h
  have h' := h ((evenV_iff v).2 hv)
  rw [andB_iff] at h'
  obtain ⟨hp, hr⟩ := h'
  obtain ⟨π, hπ⟩ := exists_of_permK hp
  rw [← hπ, letB_eq, vcomp_code, andB_iff, memL_iff, iffB_iff, beq_iff, sixB_iff] at hr
  obtain ⟨hmem, hiff⟩ := hr
  rw [stabT_eq h2 h4 h6 hmem, stabK_eq, stab_comp] at hiff
  exact hiff

theorem grp_of {L : List (Perm (Fin 7))} {c : List ℕ} (hc : L.map code = c) (h : grpK c = true) :
    1 ∈ L ∧ (∀ a ∈ L, ∀ b ∈ L, a * b ∈ L) ∧ (∀ a ∈ L, a⁻¹ ∈ L) ∧ L.Nodup := by
  subst hc
  rw [grpK, andB_iff, andB_iff, andB_iff, memL_iff, code_one, mem_map_code h7, allL_map,
    allL_map] at h
  obtain ⟨h1, hm, hi, hn⟩ := h
  refine ⟨h1, fun a ha b hb => ?_, fun a ha => ?_, (nodupL_iff _ hn).of_map _⟩
  · have := (allL_map L _).1 (hm a ha) b hb
    rwa [memL_iff, code_mul h7, mem_map_code h7] at this
  · have := hi a ha
    rwa [memL_iff, code_inv h7, mem_map_code h7] at this

theorem count_code (L : List (Perm (Fin 7))) (p : Perm (Fin 7) → Prop) [DecidablePred p]
    (f : ℕ → Bool) (hf : ∀ g, p g ↔ f (code g) = true) :
    (L.filter fun s => decide (p s)).length = cntL f (L.map code) := by
  rw [cntL_eq, List.countP_map, ← List.countP_eq_length_filter]
  refine List.countP_congr fun g _ => ?_
  simp [hf g]

theorem s0_codes : S0list.map code = s0L := by
  have e : ∀ a b c : ℕ, code (rr ^ a * tt ^ b * kk ^ c) =
      mul 7 (mul 7 (pow 7 6614420545 a) (pow 7 6614515746 b)) (pow 7 6582011936 c) := by
    intro a b c
    have cr : code rr = 6614420545 := by decide
    have ct : code tt = 6614515746 := by decide
    have ck : code kk = 6582011936 := by decide
    rw [← cr, ← ct, ← ck, code_pow h7, code_pow h7, code_pow h7, code_mul h7, code_mul h7]
  simp only [S0list, List.map_flatMap, List.map_map, Function.comp_def, e]
  decide +kernel

theorem y_codes : Ylist.map code = yL := by
  have e : ∀ i j : ℕ, code (y1 ^ i * y2 ^ j) =
      mul 7 (pow 7 (code y1) i) (pow 7 (code y2) j) := by
    intro i j
    rw [← code_mul h7, ← code_pow h7, ← code_pow h7]
  have c1 : code y1 = 6614515777 := by decide
  have c2 : code y2 = 4501637152 := by decide
  simp only [Ylist, List.map_flatMap, List.map_map, Function.comp_def, e, c1, c2]
  decide +kernel

theorem vcode_w1 : vcode w1 = 33825 := by decide +kernel

theorem vcode_w2 : vcode w2 = 34603008 := by decide +kernel

theorem vcode_w3 : vcode w3 = 34636833 := by decide +kernel

theorem hJ1 : ∀ i : Fin 7, i ∈ J1 ↔ bitJ 15 i = true := by decide +kernel

theorem hJ2 : ∀ i : Fin 7, i ∈ J2 ↔ bitJ 48 i = true := by decide +kernel

theorem hJ3 : ∀ i : Fin 7, i ∈ J3 ↔ bitJ 112 i = true := by decide +kernel

theorem fixed_of (hf : fixK = true) : ∀ v : Fin 7 → ZMod 2, ∑ i, v i = 0 →
    (∀ s ∈ S0list, Equiv.Perm.sign s = 1 → ∀ i, v (s⁻¹ i) = v i) →
      v = 0 ∨ v = w1 ∨ v = w2 ∨ v = w3 := by
  intro v hv hs
  rw [fixK, fixKW] at hf
  have h := (allV_iff _).1 hf v
  rw [impB_iff, impB_iff, ← s0_codes, allL_map] at h
  have h' := h ((evenV_iff v).2 hv) fun g hg => by
    rw [impB_iff, even_code h7, fixV_iff]
    exact hs g hg
  rw [memL_iff, ← vcode_zero, ← vcode_w1, ← vcode_w2, ← vcode_w3] at h'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h'
  rcases h' with e | e | e | e
  exacts [Or.inl (vcode_inj e), Or.inr (Or.inl (vcode_inj e)), Or.inr (Or.inr (Or.inl (vcode_inj e))),
    Or.inr (Or.inr (Or.inr (vcode_inj e)))]

theorem ufacts_of {w : Fin 7 → ZMod 2} {J : Finset (Fin 7)} {j c : ℕ}
    (hJ : ∀ i : Fin 7, i ∈ J ↔ bitJ j i = true) (hw : vcode w = c) (hn : ∃ i ∈ J, w i ≠ 0)
    (h : uK j c = true) : UFacts w J := by
  subst hw
  rw [uK, andB_iff, ← s0_codes, allL_map] at h
  refine ⟨fun s hs i hi => ?_, fun u hu hz => ?_, hn⟩
  · have := h.1 s hs
    rw [letB_eq, code_inv h7, allN_fin] at this
    have := this i
    rw [impB_iff, ← hJ, img_code h7, ← hJ] at this
    exact this hi
  · have := (allV_iff _).1 h.2 u
    rw [impB_iff, impB_iff, evenV_iff, zeroOn_iff hJ, dotV_iff] at this
    exact this hu hz

theorem cen_iff {J : Finset (Fin 7)} {j : ℕ} (hJ : ∀ i : Fin 7, i ∈ J ↔ bitJ j i = true)
    (s : Perm (Fin 7)) : (∀ u : Fin 7 → ZMod 2, ∑ i, u i = 0 → (∀ i ∈ J, u i = 0) →
      ∀ i, u (s⁻¹ i) = u i) ↔ cenB j (code s) = true := by
  rw [cenB, allV_iff]
  refine forall_congr' fun u => ?_
  rw [impB_iff, impB_iff, evenV_iff, zeroOn_iff hJ, fixV_iff]

theorem cen_len {J : Finset (Fin 7)} {j : ℕ} (hJ : ∀ i : Fin 7, i ∈ J ↔ bitJ j i = true) :
    (cenList J).length = cntL (cenB j) s0L := by
  rw [← s0_codes]
  exact count_code S0list _ (cenB j) (cen_iff hJ)

theorem mem_cen {J : Finset (Fin 7)} {j : ℕ} (hJ : ∀ i : Fin 7, i ∈ J ↔ bitJ j i = true)
    {s : Perm (Fin 7)} (hs : s ∈ S0list) (h : cenB j (code s) = true) : s ∈ cenList J := by
  rw [cenList, List.mem_filter, decide_eq_true_iff, cen_iff hJ]
  exact ⟨hs, h⟩

theorem a7Raw_of (h2 : Nat.beq (stabK 33) 120 = true)
    (h4 : Nat.beq (stabK 33825) 72 = true) (h6 : Nat.beq (stabK 34636833) 360 = true)
    (ho : orbK = true) (hs : s0K = true) (hf : fixK = true) (hu1 : uK 15 33825 = true)
    (hu2 : uK 48 34603008 = true) (hu3 : uK 112 34636833 = true) (hc : cenK = true)
    (hy : yK = true) : A7Raw := by
  rw [beq_iff] at h2 h4 h6
  rw [s0K, s0KW, andB_iff, beq_iff] at hs
  rw [yK, yKW, andB_iff, ← y_codes, allL_map] at hy
  rw [cenK, andB_iff, andB_iff, andB_iff, Nat.ble_eq, Nat.ble_eq, Nat.ble_eq, ← s0_codes,
    anyL_map] at hc
  obtain ⟨hc2, hc3, hc1, a, ha, hab⟩ := hc
  rw [andB_iff, anyL_map] at hab
  obtain ⟨hca, b, hb, hcb⟩ := hab
  rw [andB_iff, notB_iff, comm_code h7] at hcb
  rw [s0_codes] at hc2 hc3 hc1
  have hlen : S0list.length = 16 := by
    rw [← List.length_map (f := code), s0_codes]
    rfl
  have hylen : Ylist.length = 9 := by
    rw [← List.length_map (f := code), y_codes]
    rfl
  obtain ⟨hy1, hym, hyi, hyn⟩ := grp_of y_codes hy.1
  refine ⟨stab_conj h2 h4 h6 ho, ?_, fixed_of hf,
    ufacts_of hJ1 vcode_w1 (by decide +kernel) hu1, ufacts_of hJ2 vcode_w2 (by decide +kernel) hu2,
    ufacts_of hJ3 vcode_w3 (by decide +kernel) hu3,
    by rw [cen_len hJ2]; exact hc2, by rw [cen_len hJ3]; exact hc3, by rw [cen_len hJ1]; exact hc1,
    ⟨a, mem_cen hJ1 ha hca, b, mem_cen hJ1 hb hcb.1, hcb.2⟩, hy1, hym, hyi, hyn, hylen, ?_, ?_⟩
  · obtain ⟨h1, hm, hi, hn⟩ := grp_of s0_codes hs.1
    refine ⟨h1, hm, hi, hn, hlen, ?_⟩
    rw [count_code S0list (fun s => Perm.sign s = 1) (even 7) (fun g => (even_code h7 g).symm),
      s0_codes]
    exact hs.2
  · intro a ha b hb
    have := hy.2 a ha
    rw [andB_iff, allL_map] at this
    exact (comm_code h7 a b).1 (this.1 b hb)
  · intro a ha
    have := hy.2 a ha
    rw [andB_iff, andB_iff, andB_iff, beq_iff, code_pow h7, code_one, code_eq_iff h7,
      even_code h7, ← vcode_w1, fixV_iff] at this
    exact this.2

end CFSG.KC.A7Nat

end
