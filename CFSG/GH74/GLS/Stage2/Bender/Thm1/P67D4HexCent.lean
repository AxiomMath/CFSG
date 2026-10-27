module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4A2FoldGen
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4A2FoldChain
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4HexLong

public section

open CFSG.GH74.BNPair
open scoped Pointwise

namespace CFSG.GH74.GLS.SP

variable {X : Type*} [Group X] {H : Subgroup X} {r₁ r₂ : X} {U : Subgroup X}
  {root : ℤ → Subgroup X}

theorem Rt_inj_mod (n : ℕ) [NeZero n] {p p' : ℤ} (h : Rt n p = Rt n p') :
    p % (2 * (n : ℤ)) = p' % (2 * (n : ℤ)) := by
  have hn : 0 < n := Nat.pos_of_neZero n
  have h0 := Int.emod_nonneg p (show (2 * (n : ℤ)) ≠ 0 by omega)
  have h1 := Int.emod_lt_of_pos p (show 0 < 2 * (n : ℤ) by omega)
  have h0' := Int.emod_nonneg p' (show (2 * (n : ℤ)) ≠ 0 by omega)
  have h1' := Int.emod_lt_of_pos p' (show 0 < 2 * (n : ℤ) by omega)
  unfold Rt at h
  generalize p % (2 * (n : ℤ)) = v at *
  generalize p' % (2 * (n : ℤ)) = v' at *
  split_ifs at h <;> omega

private theorem Rt_one_six : Rt 6 1 = 2 := by decide

private theorem Rt_five_six : Rt 6 5 = 6 := by decide

private theorem intList_one_six : intList 1 ((6 : ℕ) : ℤ) = [1, 2, 3, 4, 5, 6] := by decide

private theorem list_prod_map_ite_single {l : List ℤ} (hl : l.Nodup) {k : ℤ} (hk : k ∈ l)
    (x : X) : (l.map (fun j => if j = k then x else 1)).prod = x := by
  induction l with
  | nil => simp at hk
  | cons a l ih =>
    rw [List.nodup_cons] at hl
    rw [List.map_cons, List.prod_cons]
    by_cases hak : a = k
    · subst hak
      have h1 : (l.map (fun j => if j = a then x else 1)).prod = 1 := by
        apply List.prod_eq_one
        intro y hy
        obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hy
        rw [ite_eq_right (fun h : j = a => hl.1 (h ▸ hj))]
      rw [h1, ite_eq_left rfl, mul_one]
    · have hk' : k ∈ l := (List.mem_cons.1 hk).resolve_left (fun h => hak h.symm)
      rw [ite_eq_right hak, one_mul]
      exact ih hl.2 hk'

theorem mem_foldFix_conj_iff {z x : X} : x ∈ foldFix (MulAut.conj z) ↔ z * x * z⁻¹ = x := by
  rw [mem_foldFix, MulAut.conj_apply]

theorem RGD2.eq_one_of_mem_root_root (R : RGD2 6 H r₁ r₂ U root) {k k' : ℤ}
    (hk : 1 ≤ k ∧ k ≤ 6) (hk' : IsRoot 6 k') (hne : k ≠ k') {x : X}
    (hx : x ∈ root k) (hx' : x ∈ root k') : x = 1 := by
  have hk'2 := hk'.2
  have hk'1 := hk'.1
  rcases lt_or_gt_of_ne hk'1 with hneg | hpos
  · have hxU : x ∈ H ⊔ U := (le_sup_right : U ≤ H ⊔ U) (R.root_le_U hk.1 (by omega) hx)
    have hxneg : x ∈ negGen 6 root :=
      mem_negGen_of_mem (k := -k') (by omega) (by omega) (by rw [neg_neg]; exact hx')
    exact R.meet_one x hxU hxneg
  · have hnd := chain_intList_nodup 1 ((6 : ℕ) : ℤ)
    have hkm : k ∈ intList 1 ((6 : ℕ) : ℤ) := mem_intList_iff.2 ⟨hk.1, by simpa using hk.2⟩
    have hkm' : k' ∈ intList 1 ((6 : ℕ) : ℤ) :=
      mem_intList_iff.2 ⟨by omega, by simpa using (by omega : k' ≤ 6)⟩
    have hf : ∀ j ∈ intList 1 ((6 : ℕ) : ℤ), (fun j => if j = k then x else 1) j ∈ root j := by
      intro j _
      show (if j = k then x else 1) ∈ root j
      by_cases h : j = k
      · rw [ite_eq_left h, h]; exact hx
      · rw [ite_eq_right h]; exact (root j).one_mem
    have hg : ∀ j ∈ intList 1 ((6 : ℕ) : ℤ), (fun j => if j = k' then x else 1) j ∈ root j := by
      intro j _
      show (if j = k' then x else 1) ∈ root j
      by_cases h : j = k'
      · rw [ite_eq_left h, h]; exact hx'
      · rw [ite_eq_right h]; exact (root j).one_mem
    have := R.unique _ _ hf hg
      (by rw [list_prod_map_ite_single hnd hkm, list_prod_map_ite_single hnd hkm']) k hkm
    simpa [hne] using this

theorem RGD2.hZ_of_center_bot (R : RGD2 6 H r₁ r₂ U root) (hgen : (H ⊔ U) ⊔ R.N = ⊤)
    (hcen : Subgroup.center X = ⊥) :
    ∀ g ∈ H, (∀ i, IsRoot 6 i → ∀ x ∈ root i, g * x = x * g) → g = 1 := by
  intro g hg hcomm
  set K : Subgroup X := Subgroup.centralizer ({g} : Set X) with hK
  have hmemK : ∀ {y : X}, y ∈ K ↔ y * g = g * y := fun {y} =>
    Subgroup.mem_centralizer_singleton_iff
  have hH : H ≤ K := fun h hh => hmemK.2 (R.comm_H h hh g hg)
  have hroot : ∀ i, IsRoot 6 i → root i ≤ K := fun i hi x hx => hmemK.2 (hcomm i hi x hx).symm
  have hU : U ≤ K := by
    intro u hu
    have hu' : u ∈ chainProd root (intList 1 ((6 : ℕ) : ℤ)) := by rw [← R.carrier_eq]; exact hu
    exact chainProd_subset root K _ (fun k hk =>
      hroot k (isRoot_of_pos_le (mem_intList_iff.1 hk).1 (mem_intList_iff.1 hk).2)) hu'
  have hr₁ : r₁ ∈ K := by
    obtain ⟨⟨y, hy⟩, hy1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1
      (R.ne_bot (-1) ⟨by norm_num, by norm_num⟩)
    have hy1' : y ≠ 1 := fun h => hy1 (Subtype.ext h)
    obtain ⟨w, hw, x', hx', hyw⟩ := Set.mem_mul.1 (R.rank₁ y hy hy1')
    obtain ⟨w', hw', r, hr, hwr⟩ := Set.mem_mul.1 hw
    obtain ⟨x, hx, h, hh, hxh⟩ := Set.mem_mul.1 hw'
    rw [Set.mem_singleton_iff] at hr
    have hxK : x ∈ K := hroot 1 ⟨by norm_num, by norm_num⟩ hx
    have hx'K : x' ∈ K := hroot 1 ⟨by norm_num, by norm_num⟩ hx'
    have hyK : y ∈ K := hroot (-1) ⟨by norm_num, by norm_num⟩ hy
    have e : r₁ = (x * h)⁻¹ * y * x'⁻¹ := by
      rw [← hyw, ← hwr, ← hxh, hr]; group
    rw [e]
    exact K.mul_mem (K.mul_mem (K.inv_mem (K.mul_mem hxK (hH hh))) hyK) (K.inv_mem hx'K)
  have hr₂ : r₂ ∈ K := by
    have hroot6 : IsRoot 6 (-((6 : ℕ) : ℤ)) := ⟨by norm_num, by norm_num⟩
    have hroot6' : IsRoot 6 ((6 : ℕ) : ℤ) := ⟨by norm_num, by norm_num⟩
    obtain ⟨⟨y, hy⟩, hy1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 (R.ne_bot _ hroot6)
    have hy1' : y ≠ 1 := fun h => hy1 (Subtype.ext h)
    obtain ⟨w, hw, x', hx', hyw⟩ := Set.mem_mul.1 (R.rank₂ y hy hy1')
    obtain ⟨w', hw', r, hr, hwr⟩ := Set.mem_mul.1 hw
    obtain ⟨x, hx, h, hh, hxh⟩ := Set.mem_mul.1 hw'
    rw [Set.mem_singleton_iff] at hr
    have hxK : x ∈ K := hroot _ hroot6' hx
    have hx'K : x' ∈ K := hroot _ hroot6' hx'
    have hyK : y ∈ K := hroot _ hroot6 hy
    have e : r₂ = (x * h)⁻¹ * y * x'⁻¹ := by
      rw [← hyw, ← hwr, ← hxh, hr]; group
    rw [e]
    exact K.mul_mem (K.mul_mem (K.inv_mem (K.mul_mem hxK (hH hh))) hyK) (K.inv_mem hx'K)
  have hN : R.N ≤ K := by
    unfold RGD2.N
    rw [Subgroup.closure_le]
    intro y hy
    rcases hy with hy | hy | hy
    · exact hH hy
    · rw [hy]; exact hr₁
    · rw [hy]; exact hr₂
  have htop : (⊤ : Subgroup X) ≤ K := by
    rw [← hgen]
    exact sup_le (sup_le hH hU) hN
  have hgc : g ∈ Subgroup.center X :=
    Subgroup.mem_center_iff.2 (fun y => hmemK.1 (htop (Subgroup.mem_top y)))
  rw [hcen] at hgc
  exact Subgroup.mem_bot.1 hgc

theorem RGD2.triple_unique (R : RGD2 6 H r₁ r₂ U root) {a b c a' b' c' : X}
    (ha : a ∈ root 2) (hb : b ∈ root 4) (hc : c ∈ root 6)
    (ha' : a' ∈ root 2) (hb' : b' ∈ root 4) (hc' : c' ∈ root 6)
    (h : a * b * c = a' * b' * c') : a = a' ∧ b = b' ∧ c = c' := by
  have hF : ∀ (a b c : X), a ∈ root 2 → b ∈ root 4 → c ∈ root 6 →
      ∀ j ∈ intList 1 ((6 : ℕ) : ℤ),
        (fun j => if j = 2 then a else if j = 4 then b else if j = 6 then c else 1) j ∈ root j := by
    intro a b c ha hb hc j _
    show (if j = 2 then a else if j = 4 then b else if j = 6 then c else 1) ∈ root j
    by_cases h2 : j = 2
    · rw [ite_eq_left h2, h2]; exact ha
    · rw [ite_eq_right h2]
      by_cases h4 : j = 4
      · rw [ite_eq_left h4, h4]; exact hb
      · rw [ite_eq_right h4]
        by_cases h6 : j = 6
        · rw [ite_eq_left h6, h6]; exact hc
        · rw [ite_eq_right h6]; exact (root j).one_mem
  have key := R.unique _ _ (hF a b c ha hb hc) (hF a' b' c' ha' hb' hc')
    (by rw [intList_one_six]; simpa [mul_assoc] using h)
  have k2 := key 2 (by rw [intList_one_six]; simp)
  have k4 := key 4 (by rw [intList_one_six]; simp)
  have k6 := key 6 (by rw [intList_one_six]; simp)
  simp at k2 k4 k6
  exact ⟨k2, k4, k6⟩

theorem RGD2.mem_H_of_fixes_two (R : RGD2 6 H r₁ r₂ U root) {c : X} (hc : c ∈ R.N)
    {x x' : X} (hx : x ∈ root 2) (hx1 : x ≠ 1) (hx' : x' ∈ root 6) (hx'1 : x' ≠ 1)
    (hcx : c * x * c⁻¹ = x) (hcx' : c * x' * c⁻¹ = x') : c ∈ H := by
  have key : ∀ f : ℤ → ℤ, ActsPos 6 root c f → f 1 % 12 = 1 ∧ f 5 % 12 = 5 := by
    intro f hf
    have h1 := hf 1 x (by rw [Rt_one_six]; exact hx)
    rw [hcx] at h1
    have e1 : Rt 6 (f 1) = 2 := by
      by_contra hne
      exact hx1 (R.eq_one_of_mem_root_root ⟨by norm_num, by norm_num⟩ (Rt_isRoot (by norm_num) _)
        (Ne.symm hne) hx h1)
    have h5 := hf 5 x' (by rw [Rt_five_six]; exact hx')
    rw [hcx'] at h5
    have e5 : Rt 6 (f 5) = 6 := by
      by_contra hne
      exact hx'1 (R.eq_one_of_mem_root_root ⟨by norm_num, by norm_num⟩ (Rt_isRoot (by norm_num) _)
        (Ne.symm hne) hx' h5)
    have m1 := Rt_inj_mod 6 (e1.trans Rt_one_six.symm)
    have m5 := Rt_inj_mod 6 (e5.trans Rt_five_six.symm)
    norm_num at m1 m5
    exact ⟨m1, m5⟩
  obtain ⟨k, h, hh, hcase⟩ := R.exists_normal_form hc
  rcases hcase with hcase | hcase
  · have hact : ActsPos 6 root c (fun q => q + 2 * (k : ℤ)) := by
      rw [hcase]
      exact (R.actsPos_pow k).mul (R.actsPos_of_mem_H hh)
    obtain ⟨m1, -⟩ := key _ hact
    have m1' : (1 + 2 * (k : ℤ)) % 12 = 1 := m1
    have hk6 : 6 ∣ k := by omega
    obtain ⟨j, rfl⟩ := hk6
    have : (r₁ * r₂) ^ (6 * j) ∈ H := by
      rw [pow_mul]
      exact H.pow_mem R.pow j
    rw [hcase]
    exact H.mul_mem this hh
  · have hact : ActsPos 6 root c (fun q => ((6 : ℕ) : ℤ) - (q + 2 * (k : ℤ))) := by
      rw [hcase]
      exact (R.actsPos_r₁.mul (R.actsPos_pow k)).mul (R.actsPos_of_mem_H hh)
    obtain ⟨m1, m5⟩ := key _ hact
    have m1' : (((6 : ℕ) : ℤ) - (1 + 2 * (k : ℤ))) % 12 = 1 := m1
    have m5' : (((6 : ℕ) : ℤ) - (5 + 2 * (k : ℤ))) % 12 = 5 := m5
    exfalso
    push_cast at m1' m5'
    omega

structure LongCent (R : RGD2 6 H r₁ r₂ U root) (z : X) : Prop where
  mem_H : z ∈ H
  long_cent : ∀ k, IsRoot 6 k → k % 2 = 0 → ∀ x ∈ root k, z * x * z⁻¹ = x
  short_fix : ∀ k, IsRoot 6 k → k % 2 ≠ 0 → ∀ x ∈ root k, z * x * z⁻¹ = x → x = 1

namespace LongCent

variable {R : RGD2 6 H r₁ r₂ U root} {z : X}

theorem fixed_U (hz : LongCent R z) {u : X} (hu : u ∈ U) (hzu : z * u * z⁻¹ = u) :
    ∃ a ∈ root 2, ∃ b ∈ root 4, ∃ c ∈ root 6, u = a * b * c := by
  have hu' : u ∈ chainProd root (intList 1 ((6 : ℕ) : ℤ)) := by rw [← R.carrier_eq]; exact hu
  obtain ⟨f, hf, hfu⟩ := (chain_mem_chainProd_iff root _ (chain_intList_nodup _ _) u).1 hu'
  have hfix : (MulAut.conj z) ((intList 1 ((6 : ℕ) : ℤ)).map f).prod =
      ((intList 1 ((6 : ℕ) : ℤ)).map f).prod := by
    rw [hfu, MulAut.conj_apply]; exact hzu
  have hfk := (FoldStab.conj_of_mem_H (R := R) hz.mem_H).chain_factors_fixed hf hfix
  have hmem : ∀ k : ℤ, 1 ≤ k → k ≤ 6 → k ∈ intList 1 ((6 : ℕ) : ℤ) :=
    fun k h1 h2 => mem_intList_iff.2 ⟨h1, by simpa using h2⟩
  have hfk' : ∀ k : ℤ, 1 ≤ k → k ≤ 6 → z * f k * z⁻¹ = f k := fun k h1 h2 => by
    have := hfk k (hmem k h1 h2)
    rwa [MulAut.conj_apply] at this
  have hshort : ∀ k : ℤ, 1 ≤ k → k ≤ 6 → k % 2 ≠ 0 → f k = 1 := fun k h1 h2 h3 =>
    hz.short_fix k ⟨by omega, by omega⟩ h3 (f k) (hf k (hmem k h1 h2)) (hfk' k h1 h2)
  have e1 := hshort 1 (by norm_num) (by norm_num) (by norm_num)
  have e3 := hshort 3 (by norm_num) (by norm_num) (by norm_num)
  have e5 := hshort 5 (by norm_num) (by norm_num) (by norm_num)
  refine ⟨f 2, hf 2 (hmem 2 (by norm_num) (by norm_num)), f 4,
    hf 4 (hmem 4 (by norm_num) (by norm_num)), f 6, hf 6 (hmem 6 (by norm_num) (by norm_num)), ?_⟩
  rw [← hfu, intList_one_six]
  simp [e1, e3, e5, mul_assoc]

theorem fixed_U_mem_longSub (hz : LongCent R z) {u : X} (hu : u ∈ U) (hzu : z * u * z⁻¹ = u) :
    u ∈ longSub 6 root := by
  obtain ⟨a, ha, b, hb, c, hc, rfl⟩ := hz.fixed_U hu hzu
  have h2 : IsRoot 6 2 := ⟨by norm_num, by norm_num⟩
  have h4 : IsRoot 6 4 := ⟨by norm_num, by norm_num⟩
  have h6 : IsRoot 6 6 := ⟨by norm_num, by norm_num⟩
  exact (longSub 6 root).mul_mem ((longSub 6 root).mul_mem (root_le_longSub h2 (by norm_num) ha)
    (root_le_longSub h4 (by norm_num) hb)) (root_le_longSub h6 (by norm_num) hc)

theorem normalizes_longSub (hz : LongCent R z) (hgen : (H ⊔ U) ⊔ R.N = ⊤)
    (hZ : ∀ g ∈ H, (∀ i, IsRoot 6 i → ∀ x ∈ root i, g * x = x * g) → g = 1)
    {c : X} (hc : z * c * z⁻¹ = c) {x : X} (hx : x ∈ longSub 6 root) :
    c * x * c⁻¹ ∈ longSub 6 root := by
  obtain ⟨v, hv, n, hn, u, hu, hcvnu⟩ := (FoldStab.conj_of_mem_H (R := R) hz.mem_H).cell hgen hZ
    (by rw [MulAut.conj_apply]; exact hc)
  have hvL : v ∈ longSub 6 root := hz.fixed_U_mem_longSub hv.1 (mem_foldFix_conj_iff.1 hv.2)
  have huL : u ∈ longSub 6 root := hz.fixed_U_mem_longSub hu.1 (mem_foldFix_conj_iff.1 hu.2)
  have h1 : u * x * u⁻¹ ∈ longSub 6 root :=
    (longSub 6 root).mul_mem ((longSub 6 root).mul_mem huL hx) ((longSub 6 root).inv_mem huL)
  have h2 : n * (u * x * u⁻¹) * n⁻¹ ∈ longSub 6 root :=
    conj_mem_longSub (by norm_num) (by norm_num) (R.goodActEven_of_mem_N (by norm_num) hn.1) h1
  have h3 : v * (n * (u * x * u⁻¹) * n⁻¹) * v⁻¹ ∈ longSub 6 root :=
    (longSub 6 root).mul_mem ((longSub 6 root).mul_mem hvL h2) ((longSub 6 root).inv_mem hvL)
  have e : c * x * c⁻¹ = v * (n * (u * x * u⁻¹) * n⁻¹) * v⁻¹ := by
    rw [hcvnu]; group
  rw [e]
  exact h3

theorem centralizer_le_H (hz : LongCent R z) (hgen : (H ⊔ U) ⊔ R.N = ⊤)
    (hZ : ∀ g ∈ H, (∀ i, IsRoot 6 i → ∀ x ∈ root i, g * x = x * g) → g = 1)
    {t : X} (htH : t ∈ H) (htL : t ∈ longSub 6 root)
    (hfree : ∀ k, IsRoot 6 k → 0 < k → k % 2 = 0 → ∀ x ∈ root k, t * x * t⁻¹ = x → x = 1)
    {c : X} (hc : z * c * z⁻¹ = c) (hcL : ∀ x ∈ longSub 6 root, c * x = x * c) : c ∈ H := by
  obtain ⟨v, hv, n, hn, u, hu, hcvnu⟩ := (FoldStab.conj_of_mem_H (R := R) hz.mem_H).cell hgen hZ
    (by rw [MulAut.conj_apply]; exact hc)
  have hvL : v ∈ longSub 6 root := hz.fixed_U_mem_longSub hv.1 (mem_foldFix_conj_iff.1 hv.2)
  have huL : u ∈ longSub 6 root := hz.fixed_U_mem_longSub hu.1 (mem_foldFix_conj_iff.1 hu.2)
  set ℓ : X := v⁻¹ * u⁻¹ with hℓ
  have hℓU : ℓ ∈ U := U.mul_mem (U.inv_mem hv.1) (U.inv_mem hu.1)
  have hℓfix : z * ℓ * z⁻¹ = ℓ :=
    mem_foldFix_conj_iff.1 ((foldFix (MulAut.conj z)).mul_mem ((foldFix _).inv_mem hv.2)
      ((foldFix _).inv_mem hu.2))
  have hℓL : ℓ ∈ longSub 6 root :=
    (longSub 6 root).mul_mem ((longSub 6 root).inv_mem hvL) ((longSub 6 root).inv_mem huL)
  have hcv' : c * v⁻¹ = v⁻¹ * c := Commute.inv_right (show Commute c v from hcL v hvL)
  have hnc : n = c * ℓ := by
    have e1 : n = v⁻¹ * c * u⁻¹ := by rw [hcvnu]; group
    rw [e1, ← hcv', mul_assoc]
  have hnt : n * t * n⁻¹ ∈ H := (R.N_normalizes_H hn.1 t htH).1
  have hcw : c * (ℓ * t * ℓ⁻¹) * c⁻¹ = ℓ * t * ℓ⁻¹ := by
    have hw : ℓ * t * ℓ⁻¹ ∈ longSub 6 root :=
      (longSub 6 root).mul_mem ((longSub 6 root).mul_mem hℓL htL) ((longSub 6 root).inv_mem hℓL)
    rw [hcL _ hw]
    group
  have hnt' : n * t * n⁻¹ = ℓ * t * ℓ⁻¹ := by
    calc n * t * n⁻¹ = c * (ℓ * t * ℓ⁻¹) * c⁻¹ := by rw [hnc]; group
      _ = ℓ * t * ℓ⁻¹ := hcw
  have hℓtH : ℓ * t * ℓ⁻¹ ∈ H := hnt' ▸ hnt
  have h1 : t⁻¹ * (ℓ * t * ℓ⁻¹) ∈ U ⊓ H := by
    refine ⟨?_, H.mul_mem (H.inv_mem htH) hℓtH⟩
    have h2 := R.conj_mem_U (H.inv_mem htH) hℓU
    have e : t⁻¹ * (ℓ * t * ℓ⁻¹) = (t⁻¹ * ℓ * t⁻¹⁻¹) * ℓ⁻¹ := by group
    rw [e]
    exact U.mul_mem h2 (U.inv_mem hℓU)
  rw [R.U_inf_H, Subgroup.mem_bot] at h1
  have h3 : t = ℓ * t * ℓ⁻¹ := inv_mul_eq_one.1 h1
  have htℓ : t * ℓ * t⁻¹ = ℓ := by
    calc t * ℓ * t⁻¹ = (ℓ * t * ℓ⁻¹) * ℓ * t⁻¹ := by rw [← h3]
      _ = ℓ := by group
  obtain ⟨a, ha, b, hb, c', hc', hℓabc⟩ := hz.fixed_U hℓU hℓfix
  have h2r : IsRoot 6 2 := ⟨by norm_num, by norm_num⟩
  have h4r : IsRoot 6 4 := ⟨by norm_num, by norm_num⟩
  have h6r : IsRoot 6 6 := ⟨by norm_num, by norm_num⟩
  have hta : t * a * t⁻¹ ∈ root 2 := R.invariant 2 h2r t htH a ha
  have htb : t * b * t⁻¹ ∈ root 4 := R.invariant 4 h4r t htH b hb
  have htc : t * c' * t⁻¹ ∈ root 6 := R.invariant 6 h6r t htH c' hc'
  obtain ⟨e1, e2, e3⟩ := R.triple_unique hta htb htc ha hb hc' (by
    calc t * a * t⁻¹ * (t * b * t⁻¹) * (t * c' * t⁻¹) = t * (a * b * c') * t⁻¹ := by group
      _ = t * ℓ * t⁻¹ := by rw [hℓabc]
      _ = ℓ := htℓ
      _ = a * b * c' := hℓabc)
  have ha1 : a = 1 := hfree 2 h2r (by norm_num) (by norm_num) a ha e1
  have hb1 : b = 1 := hfree 4 h4r (by norm_num) (by norm_num) b hb e2
  have hc1 : c' = 1 := hfree 6 h6r (by norm_num) (by norm_num) c' hc' e3
  have hℓ1 : ℓ = 1 := by rw [hℓabc, ha1, hb1, hc1]; simp
  have hcN : c ∈ R.N := by
    have : n = c := by rw [hnc, hℓ1, mul_one]
    exact this ▸ hn.1
  obtain ⟨x, hx, hx1⟩ : ∃ x ∈ root 2, x ≠ 1 := by
    obtain ⟨⟨x, hx⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 (R.ne_bot 2 h2r)
    exact ⟨x, hx, fun h => hx1 (Subtype.ext h)⟩
  obtain ⟨x', hx', hx'1⟩ : ∃ x ∈ root 6, x ≠ 1 := by
    obtain ⟨⟨x, hx⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 (R.ne_bot 6 h6r)
    exact ⟨x, hx, fun h => hx1 (Subtype.ext h)⟩
  have hcx : c * x * c⁻¹ = x := by
    rw [hcL x (root_le_longSub h2r (by norm_num) hx)]; group
  have hcx' : c * x' * c⁻¹ = x' := by
    rw [hcL x' (root_le_longSub h6r (by norm_num) hx')]; group
  exact R.mem_H_of_fixes_two hcN hx hx1 hx' hx'1 hcx hcx'

theorem card_fixed_U (hz : LongCent R z) :
    Nat.card ↥(U ⊓ foldFix (MulAut.conj z)) =
      Nat.card ↥(root 2) * Nat.card ↥(root 4) * Nat.card ↥(root 6) := by
  have h2r : IsRoot 6 2 := ⟨by norm_num, by norm_num⟩
  have h4r : IsRoot 6 4 := ⟨by norm_num, by norm_num⟩
  have h6r : IsRoot 6 6 := ⟨by norm_num, by norm_num⟩
  have hmem : ∀ a b c : X, a ∈ root 2 → b ∈ root 4 → c ∈ root 6 →
      a * b * c ∈ U ⊓ foldFix (MulAut.conj z) := by
    intro a b c ha hb hc
    refine ⟨U.mul_mem (U.mul_mem (R.root_le_U (by norm_num) (by norm_num) ha)
      (R.root_le_U (by norm_num) (by norm_num) hb)) (R.root_le_U (by norm_num) (by norm_num) hc),
      mem_foldFix_conj_iff.2 ?_⟩
    have e2 := hz.long_cent 2 h2r (by norm_num) a ha
    have e4 := hz.long_cent 4 h4r (by norm_num) b hb
    have e6 := hz.long_cent 6 h6r (by norm_num) c hc
    calc z * (a * b * c) * z⁻¹ = (z * a * z⁻¹) * (z * b * z⁻¹) * (z * c * z⁻¹) := by group
      _ = a * b * c := by rw [e2, e4, e6]
  let F : (↥(root 2) × ↥(root 4)) × ↥(root 6) → ↥(U ⊓ foldFix (MulAut.conj z)) := fun p =>
    ⟨(p.1.1 : X) * p.1.2 * p.2, hmem _ _ _ p.1.1.2 p.1.2.2 p.2.2⟩
  have hF : Function.Bijective F := by
    constructor
    · rintro ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, ⟨c, hc⟩⟩ ⟨⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩, ⟨c', hc'⟩⟩ h
      have h' : a * b * c = a' * b' * c' := congrArg Subtype.val h
      obtain ⟨e1, e2, e3⟩ := R.triple_unique ha hb hc ha' hb' hc' h'
      subst e1 e2 e3
      rfl
    · rintro ⟨y, hyU, hyfix⟩
      obtain ⟨a, ha, b, hb, c, hc, rfl⟩ := hz.fixed_U hyU (mem_foldFix_conj_iff.1 hyfix)
      exact ⟨⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, ⟨c, hc⟩⟩, rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective F hF), Nat.card_prod, Nat.card_prod]

end LongCent

end CFSG.GH74.GLS.SP
