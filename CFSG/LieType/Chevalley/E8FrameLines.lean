module

public import Certificates.Data.E8Frame
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitGen
public import CFSG.GH74.Defs

public section

namespace CFSG.LieType.Chevalley.E8Lines

open CFSG.GH74 CFSG.LieType.Chevalley.E8Frame

theorem sectionalTwoRankLE_two_of_card_eq_eight {X : Type*} [Group X] [Finite X]
    (hX : Nat.card X = 8) {x : X} (hx : x ^ 2 ≠ 1) : SectionalTwoRankLE X 2 := by
  classical
  intro P _
  by_cases hP4 : Nat.card P ≤ 2 ^ 2
  · exact CFSG.ComponentClassification.HSFLit.exists_finset_closure_eq_of_card_le P hP4
  have hdvd : Nat.card P ∣ 8 := hX ▸ Subgroup.card_subgroup_dvd_card P
  have hP8 : Nat.card P = 8 := by
    have hle : Nat.card P ≤ 8 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases h : Nat.card P <;> simp_all
  have hPtop : P = ⊤ := Subgroup.eq_top_of_card_eq P (hP8.trans hX.symm)
  subst hPtop
  have hox : orderOf x ∣ 8 := hX ▸ orderOf_dvd_natCard x
  have hox2 : ¬ orderOf x ∣ 2 := fun h => hx (orderOf_dvd_iff_pow_eq_one.1 h)
  have hox4 : 4 ≤ orderOf x := by
    have hpos : 0 < orderOf x := Nat.pos_of_dvd_of_pos hox (by norm_num)
    have hle : orderOf x ≤ 8 := Nat.le_of_dvd (by norm_num) hox
    interval_cases h : orderOf x <;> simp_all
  by_cases hz : Subgroup.zpowers x = ⊤
  · refine ⟨{x}, by simp, ?_⟩
    rw [Finset.coe_singleton, ← Subgroup.zpowers_eq_closure, hz]
  · obtain ⟨y, hy⟩ : ∃ y, y ∉ Subgroup.zpowers x := by
      by_contra h
      push Not at h
      exact hz (eq_top_iff.2 fun y _ => h y)
    refine ⟨{x, y}, Finset.card_le_two, ?_⟩
    set H := Subgroup.closure ((({x, y} : Finset X)) : Set X)
    have hxH : Subgroup.zpowers x ≤ H := by
      rw [Subgroup.zpowers_eq_closure]
      exact Subgroup.closure_mono (by simp)
    have hyH : y ∈ H := Subgroup.subset_closure (by simp)
    have hlt : Subgroup.zpowers x < H := lt_of_le_of_ne hxH fun h => hy (h ▸ hyH)
    have hcard : orderOf x < Nat.card H := by
      rw [← Nat.card_zpowers]
      exact Subgroup.card_lt_of_lt hlt
    have hHdvd : Nat.card H ∣ 8 := hX ▸ Subgroup.card_subgroup_dvd_card H
    have hH8 : Nat.card H = 8 := by
      have hle : Nat.card H ≤ 8 := Nat.le_of_dvd (by norm_num) hHdvd
      interval_cases h : Nat.card H <;> omega
    exact Subgroup.eq_top_of_card_eq H (hH8.trans hX.symm)

abbrev lo (i : Fin 8) : Fin 16 := Fin.castLE (by norm_num) i

@[simp] theorem lo_val (i : Fin 8) : (lo i).val = i.val := rfl

theorem frameNeg_val (k : Fin 16) : (frameNeg k).val = (k.val + 8) % 16 := rfl

theorem frameNeg_frameNeg (k : Fin 16) : frameNeg (frameNeg k) = k := by
  ext
  rw [frameNeg_val, frameNeg_val]
  omega

theorem frameNeg_lo_ne (i : Fin 8) : frameNeg (lo i) ≠ lo i := by
  intro h
  have := congrArg Fin.val h
  rw [frameNeg_val, lo_val] at this
  have := i.isLt
  omega

theorem eq_lo_or_eq_frameNeg_lo (k : Fin 16) :
    k = lo ⟨k.val % 8, Nat.mod_lt _ (by norm_num)⟩ ∨
      k = frameNeg (lo ⟨k.val % 8, Nat.mod_lt _ (by norm_num)⟩) := by
  have hk := k.isLt
  rcases Nat.lt_or_ge k.val 8 with h | h
  · left
    apply Fin.ext
    rw [lo_val]
    show k.val = k.val % 8
    omega
  · right
    apply Fin.ext
    rw [frameNeg_val, lo_val]
    show k.val = (k.val % 8 + 8) % 16
    omega

@[expose] def lineFun (g : Equiv.Perm (Fin 16)) (i : Fin 8) : Fin 8 :=
  ⟨(g (lo i)).val % 8, Nat.mod_lt _ (by norm_num)⟩

theorem lineFun_one (i : Fin 8) : lineFun 1 i = i := by
  apply Fin.ext
  show (lo i).val % 8 = i.val
  rw [lo_val]
  exact Nat.mod_eq_of_lt i.isLt

theorem apply_frameNeg {g : Equiv.Perm (Fin 16)} (hg : g * frameNeg = frameNeg * g) (k : Fin 16) :
    g (frameNeg k) = frameNeg (g k) :=
  congrFun (congrArg DFunLike.coe hg) k

theorem apply_val_mod {g : Equiv.Perm (Fin 16)} (hg : g * frameNeg = frameNeg * g)
    (k : Fin 16) : (g k).val % 8 = (lineFun g ⟨k.val % 8, Nat.mod_lt _ (by norm_num)⟩).val := by
  have h := eq_lo_or_eq_frameNeg_lo k
  generalize (⟨k.val % 8, Nat.mod_lt _ (by norm_num)⟩ : Fin 8) = i at h ⊢
  rcases h with rfl | rfl
  · rfl
  · rw [apply_frameNeg hg, frameNeg_val]
    simp only [lineFun]
    omega

theorem lineFun_mul {g : Equiv.Perm (Fin 16)} (hg : g * frameNeg = frameNeg * g)
    (h : Equiv.Perm (Fin 16)) (i : Fin 8) : lineFun (g * h) i = lineFun g (lineFun h i) := by
  ext
  exact apply_val_mod hg (h (lo i))

abbrev negCent : Subgroup (Equiv.Perm (Fin 16)) := Subgroup.centralizer {frameNeg}

theorem comm_of_mem_negCent {g : Equiv.Perm (Fin 16)} (hg : g ∈ negCent) :
    g * frameNeg = frameNeg * g :=
  Subgroup.mem_centralizer_singleton_iff.1 hg

@[expose] def lineHom : negCent →* Equiv.Perm (Fin 8) where
  toFun g :=
    { toFun := lineFun g
      invFun := lineFun (g⁻¹ : negCent)
      left_inv := fun i => by
        rw [← lineFun_mul (comm_of_mem_negCent (g⁻¹).2), Subgroup.coe_inv, inv_mul_cancel,
          lineFun_one]
      right_inv := fun i => by
        rw [← lineFun_mul (comm_of_mem_negCent g.2), Subgroup.coe_inv, mul_inv_cancel,
          lineFun_one] }
  map_one' := Equiv.ext fun i => lineFun_one i
  map_mul' g h := Equiv.ext fun i => lineFun_mul (comm_of_mem_negCent g.2) h i

theorem lineHom_eq_one_iff (g : negCent) : lineHom g = 1 ↔ ∀ i, lineFun g i = i := by
  rw [Equiv.ext_iff]
  rfl

@[expose] def signVec (g : Equiv.Perm (Fin 16)) (i : Fin 8) : ZMod 2 :=
  if g (lo i) = lo i then 0 else 1

theorem apply_lo_eq_or {g : Equiv.Perm (Fin 16)} (hg : ∀ i, lineFun g i = i) (i : Fin 8) :
    g (lo i) = lo i ∨ g (lo i) = frameNeg (lo i) := by
  have h : (g (lo i)).val % 8 = i.val := congrArg Fin.val (hg i)
  have hlt := (g (lo i)).isLt
  have hi := i.isLt
  rcases Nat.lt_or_ge (g (lo i)).val 8 with h8 | h8
  · left
    apply Fin.ext
    rw [lo_val]
    omega
  · right
    apply Fin.ext
    rw [frameNeg_val, lo_val]
    omega

theorem apply_lo_of_signVec {g : Equiv.Perm (Fin 16)} (hg : ∀ i, lineFun g i = i) (i : Fin 8) :
    g (lo i) = if signVec g i = 0 then lo i else frameNeg (lo i) := by
  by_cases h1 : g (lo i) = lo i
  · simp [signVec, h1]
  · have h2 : signVec g i = 1 := by simp [signVec, h1]
    rw [h2, if_neg (by decide)]
    exact (apply_lo_eq_or hg i).resolve_left h1

theorem signVec_mul {a b : Equiv.Perm (Fin 16)} (ha : a * frameNeg = frameNeg * a)
    (ha1 : ∀ i, lineFun a i = i) (hb1 : ∀ i, lineFun b i = i) :
    signVec (a * b) = signVec a + signVec b := by
  funext i
  have hne := frameNeg_lo_ne i
  have hab : (a * b) (lo i) = a (b (lo i)) := rfl
  rcases apply_lo_eq_or hb1 i with hb | hb <;> rcases apply_lo_eq_or ha1 i with ha' | ha'
  · have h : (a * b) (lo i) = lo i := by rw [hab, hb, ha']
    simp [signVec, h, hb, ha']
  · have h : (a * b) (lo i) = frameNeg (lo i) := by rw [hab, hb, ha']
    simp [signVec, h, hb, ha', hne]
  · have h : (a * b) (lo i) = frameNeg (lo i) := by rw [hab, hb, apply_frameNeg ha, ha']
    simp [signVec, h, hb, ha', hne]
  · have h : (a * b) (lo i) = lo i := by
      rw [hab, hb, apply_frameNeg ha, ha', frameNeg_frameNeg]
    simp [signVec, h, hb, ha', hne]
    decide

theorem eq_of_signVec_eq {a b : Equiv.Perm (Fin 16)} (ha : a * frameNeg = frameNeg * a)
    (hb : b * frameNeg = frameNeg * b) (ha1 : ∀ i, lineFun a i = i)
    (hb1 : ∀ i, lineFun b i = i) (h : signVec a = signVec b) : a = b := by
  have hlo : ∀ i, a (lo i) = b (lo i) := fun i => by
    rw [apply_lo_of_signVec ha1, apply_lo_of_signVec hb1, h]
  ext k
  rcases eq_lo_or_eq_frameNeg_lo k with hk | hk <;> rw [hk]
  · rw [hlo]
  · rw [apply_frameNeg ha, apply_frameNeg hb, hlo]

theorem signVec_comp_lineFun {a t : Equiv.Perm (Fin 16)} (ha : a * frameNeg = frameNeg * a)
    (ha1 : ∀ i, lineFun a i = i) (ht : t * frameNeg = frameNeg * t) (hat : a * t = t * a) :
    signVec a ∘ lineFun t = signVec a := by
  funext i
  simp only [Function.comp_apply]
  set j := lineFun t i
  have hcomm : ∀ k, a (t k) = t (a k) := fun k => congrFun (congrArg DFunLike.coe hat) k
  have htj : t (lo i) = lo j ∨ t (lo i) = frameNeg (lo j) := by
    have h := eq_lo_or_eq_frameNeg_lo (t (lo i))
    have hj : (⟨(t (lo i)).val % 8, Nat.mod_lt _ (by norm_num)⟩ : Fin 8) = j := rfl
    rwa [hj] at h
  have hne : ∀ l : Fin 8, frameNeg (lo l) ≠ lo l := frameNeg_lo_ne
  unfold signVec
  rcases apply_lo_eq_or ha1 i with hai | hai <;> rcases htj with htj | htj
  · have : a (lo j) = lo j := by rw [← htj, hcomm, hai]
    simp [this, hai]
  · have : a (lo j) = lo j := by
      have h1 : a (frameNeg (lo j)) = frameNeg (lo j) := by rw [← htj, hcomm, hai]
      rw [apply_frameNeg ha] at h1
      have h2 := congrArg frameNeg h1
      rwa [frameNeg_frameNeg, frameNeg_frameNeg] at h2
    simp [this, hai]
  · have : a (lo j) = frameNeg (lo j) := by
      rw [← htj, hcomm, hai, apply_frameNeg ht]
    simp [this, hai, hne]
  · have : a (lo j) = frameNeg (lo j) := by
      have h1 : a (frameNeg (lo j)) = lo j := by
        rw [← htj, hcomm, hai, apply_frameNeg ht, htj, frameNeg_frameNeg]
      rw [apply_frameNeg ha] at h1
      have h2 := congrArg frameNeg h1
      rwa [frameNeg_frameNeg] at h2
    simp [this, hai, hne]

end CFSG.LieType.Chevalley.E8Lines

end
