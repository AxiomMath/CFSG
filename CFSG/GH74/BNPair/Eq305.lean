module

public import CFSG.GH74.BNPair.Lemma305
public import CFSG.GH74.BNPair.Dihedral
public import CFSG.GH74.BNPair.RootCalc

public section

namespace CFSG.GH74.BNPair

universe u

open scoped Pointwise

theorem intList_append {a b c : ℤ} (h1 : a ≤ b + 1) (h2 : b ≤ c) :
    intList a b ++ intList (b + 1) c = intList a c := by
  apply List.ext_getElem
  · simp only [intList, List.length_append, List.length_map, List.length_range]
    omega
  · intro t ht1 ht2
    simp only [intList, List.length_map, List.length_range] at ht1 ht2 ⊢
    by_cases ht : t < (b + 1 - a).toNat
    · rw [List.getElem_append_left (by simpa using ht)]
      simp
    · rw [List.getElem_append_right (by simp; omega)]
      simp only [List.getElem_map, List.getElem_range, List.length_map, List.length_range]
      omega

theorem intList_eq_nil {a b : ℤ} (h : b < a) : intList a b = [] := by
  simp only [intList, List.map_eq_nil_iff, List.range_eq_nil]
  omega

@[expose] def tauA (n i : ℕ) (q : ℤ) : ℤ :=
  if Even i then q - i else (n : ℤ) + i - 1 - q

@[expose] def tauB (n i : ℕ) (q : ℤ) : ℤ :=
  if Even i then q + i else (n : ℤ) - 1 - i - q

theorem Rt_tauA_neg {n i : ℕ} {q : ℤ} (hq0 : 0 ≤ q) (hq : q < i) (hi : i ≤ n) :
    -(n : ℤ) ≤ Rt n (tauA n i q) ∧ Rt n (tauA n i q) ≤ -1 := by
  unfold tauA
  split_ifs with he
  · rw [Rt_of_neg (by omega) (by omega)]
    omega
  · rw [Rt_of_ge (by omega) (by omega)]
    omega

theorem Rt_tauA_pos {n i : ℕ} {q : ℤ} (hq : (i : ℤ) ≤ q) (hqn : q < n) :
    1 ≤ Rt n (tauA n i q) ∧ Rt n (tauA n i q) ≤ n := by
  unfold tauA
  split_ifs with he
  · rw [Rt_of_lt (by omega) (by omega)]
    omega
  · rw [Rt_of_lt (by omega) (by omega)]
    omega

theorem Rt_tauB_neg {n i : ℕ} {q : ℤ} (hq : (n : ℤ) - i ≤ q) (hqn : q < n) (hi : i ≤ n) :
    -(n : ℤ) ≤ Rt n (tauB n i q) ∧ Rt n (tauB n i q) ≤ -1 := by
  unfold tauB
  split_ifs with he
  · rw [Rt_of_ge (by omega) (by omega)]
    omega
  · rw [Rt_of_neg (by omega) (by omega)]
    omega

theorem Rt_tauB_pos {n i : ℕ} {q : ℤ} (hq0 : 0 ≤ q) (hq : q < (n : ℤ) - i) :
    1 ≤ Rt n (tauB n i q) ∧ Rt n (tauB n i q) ≤ n := by
  unfold tauB
  split_ifs with he
  · rw [Rt_of_lt (by omega) (by omega)]
    omega
  · rw [Rt_of_lt (by omega) (by omega)]
    omega

theorem Rt_pos_idx {n : ℕ} {k : ℤ} (h1 : 1 ≤ k) (h2 : k ≤ n) : Rt n (k - 1) = k := by
  rw [Rt_of_lt (by omega) (by omega)]
  ring

namespace RankTwoSystem

variable {X : Type u} [Group X] {n : ℕ} {D : RankTwoSystem X n}

theorem actsPos_altWord₁ : ∀ i : ℕ, ∀ m : D.N, (m : D.Weyl) = altWord D.w₁ D.w₂ i →
    D.ActsPos (m : X) (tauA n i)
  | 0, m, hm => by
    have hn := D.three_le
    have h1 : D.ActsPos (((1 : D.N)) : X) id := by simpa using ActsPos.one (D := D)
    have := ActsPos.of_mk_eq (c := (1 : D.N)) h1
      (by rw [hm, altWord_zero]; rfl) (by omega)
    have e : tauA n 0 = id := by
      funext q
      simp [tauA]
    rwa [e]
  | i + 1, m, hm => by
    have hn := D.three_le
    obtain ⟨m', hm'⟩ := QuotientGroup.mk_surjective (altWord D.w₁ D.w₂ i)
    have ih := actsPos_altWord₁ i m' hm'
    by_cases he : Even i
    · obtain ⟨ms, hms⟩ := QuotientGroup.mk_surjective D.w₁
      have h2 := (D.actsPos_lift₁ ms hms).mul ih
      have hc : ((ms * m' : D.N) : D.Weyl) = (m : D.Weyl) := by
        rw [QuotientGroup.mk_mul, hms, hm', hm, altWord_succ_left]
        simp [he]
      have h3 := ActsPos.of_mk_eq (c := ms * m') (by simpa using h2) hc (by omega)
      have e : (fun q => (n : ℤ) - tauA n i q) = tauA n (i + 1) := by
        funext q
        simp [tauA, he, Nat.even_add_one]
        ring
      rwa [e] at h3
    · obtain ⟨ms, hms⟩ := QuotientGroup.mk_surjective D.w₂
      have h2 := (D.actsPos_lift₂ ms hms).mul ih
      have hc : ((ms * m' : D.N) : D.Weyl) = (m : D.Weyl) := by
        rw [QuotientGroup.mk_mul, hms, hm', hm, altWord_succ_left]
        simp [he]
      have h3 := ActsPos.of_mk_eq (c := ms * m') (by simpa using h2) hc (by omega)
      have e : (fun q => (n : ℤ) - 2 - tauA n i q) = tauA n (i + 1) := by
        funext q
        simp [tauA, he, Nat.even_add_one]
        ring
      rwa [e] at h3

theorem actsPos_altWord₂ : ∀ i : ℕ, ∀ m : D.N, (m : D.Weyl) = altWord D.w₂ D.w₁ i →
    D.ActsPos (m : X) (tauB n i)
  | 0, m, hm => by
    have hn := D.three_le
    have h1 : D.ActsPos (((1 : D.N)) : X) id := by simpa using ActsPos.one (D := D)
    have := ActsPos.of_mk_eq (c := (1 : D.N)) h1
      (by rw [hm, altWord_zero]; rfl) (by omega)
    have e : tauB n 0 = id := by
      funext q
      simp [tauB]
    rwa [e]
  | i + 1, m, hm => by
    have hn := D.three_le
    obtain ⟨m', hm'⟩ := QuotientGroup.mk_surjective (altWord D.w₂ D.w₁ i)
    have ih := actsPos_altWord₂ i m' hm'
    by_cases he : Even i
    · obtain ⟨ms, hms⟩ := QuotientGroup.mk_surjective D.w₂
      have h2 := (D.actsPos_lift₂ ms hms).mul ih
      have hc : ((ms * m' : D.N) : D.Weyl) = (m : D.Weyl) := by
        rw [QuotientGroup.mk_mul, hms, hm', hm, altWord_succ_left]
        simp [he]
      have h3 := ActsPos.of_mk_eq (c := ms * m') (by simpa using h2) hc (by omega)
      have e : (fun q => (n : ℤ) - 2 - tauB n i q) = tauB n (i + 1) := by
        funext q
        simp [tauB, he, Nat.even_add_one]
        ring
      rwa [e] at h3
    · obtain ⟨ms, hms⟩ := QuotientGroup.mk_surjective D.w₁
      have h2 := (D.actsPos_lift₁ ms hms).mul ih
      have hc : ((ms * m' : D.N) : D.Weyl) = (m : D.Weyl) := by
        rw [QuotientGroup.mk_mul, hms, hm', hm, altWord_succ_left]
        simp [he]
      have h3 := ActsPos.of_mk_eq (c := ms * m') (by simpa using h2) hc (by omega)
      have e : (fun q => (n : ℤ) - tauB n i q) = tauB n (i + 1) := by
        funext q
        simp [tauB, he, Nat.even_add_one]
        ring
      rwa [e] at h3

theorem plist_map_Rt_neg {n : ℕ} (hn : 0 < n) :
    (plist (n : ℤ) (n - 1)).map (Rt n) = (intList 1 n).map Neg.neg := by
  apply List.ext_getElem
  · simp only [plist, intList, List.length_map, List.length_range]
    omega
  · intro t h1 h2
    have ht : t < n := by
      simp only [plist, List.length_map, List.length_range] at h1
      omega
    simp only [plist, intList, List.getElem_map, List.getElem_range]
    rw [Rt_of_ge (by omega) (by omega)]
    ring

variable (D)

theorem Uminus_isSubgroup : ∃ V : Subgroup X, (V : Set X) = D.Uminus := by
  have hn := D.three_le
  obtain ⟨⟨V, hV⟩, -⟩ := D.good_plist (k := n - 1) (by omega) (n : ℤ)
  refine ⟨V, ?_⟩
  rw [hV, pprod_eq_chainProd, plist_map_Rt_neg (by omega)]
  rfl

variable {D}

theorem root_le_V {V : Subgroup X} (hV : (V : Set X) = D.Uminus) {k : ℤ} (h1 : -(n : ℤ) ≤ k)
    (h2 : k ≤ -1) : D.root k ≤ V := by
  intro x hx
  rw [← SetLike.mem_coe, hV]
  refine mem_chainProd_of_mem D.root ?_ hx
  rw [List.mem_map]
  exact ⟨-k, mem_intList_iff.2 ⟨by omega, by omega⟩, by simp⟩

variable (D)

theorem eq305_core_I {m : X} {V : Subgroup X} (hV : (V : Set X) = D.Uminus) {A C : Set X}
    (hAU : A ⊆ D.U) (hCU : C ⊆ D.U) (hdec : ∀ x ∈ D.U, ∃ a ∈ A, ∃ c ∈ C, x = a * c)
    (hA : ∀ a ∈ A, m * a * m⁻¹ ∈ V) (hC : ∀ c ∈ C, m * c * m⁻¹ ∈ D.U) :
    {x | x ∈ D.U ∧ m * x * m⁻¹ ∈ D.Uminus} = A ∧ {x | x ∈ D.U ∧ m * x * m⁻¹ ∈ D.U} = C := by
  have key : ∀ z : X, z ∈ D.U → z ∈ V → z = 1 := fun z hzU hzV =>
    D.roots.meet_one z (D.U_le_B hzU) (by rwa [← SetLike.mem_coe, hV] at hzV)
  have hone : ∀ z : X, m * z * m⁻¹ = 1 → z = 1 := by
    intro z hz
    have : z = m⁻¹ * (m * z * m⁻¹) * m := by group
    rw [this, hz]
    group
  refine ⟨Set.ext fun x => ⟨?_, ?_⟩, Set.ext fun x => ⟨?_, ?_⟩⟩
  · rintro ⟨hxU, hxV⟩
    obtain ⟨a, ha, c, hc, rfl⟩ := hdec x hxU
    have hxV' : m * (a * c) * m⁻¹ ∈ V := by
      rw [← SetLike.mem_coe, hV]
      exact hxV
    have h1 : m * c * m⁻¹ ∈ V := by
      have := V.mul_mem (V.inv_mem (hA a ha)) hxV'
      have e : (m * a * m⁻¹)⁻¹ * (m * (a * c) * m⁻¹) = m * c * m⁻¹ := by group
      rwa [e] at this
    have hc1 : c = 1 := hone c (key _ (hC c hc) h1)
    simpa [hc1] using ha
  · intro ha
    exact ⟨hAU ha, by rw [← hV]; exact hA x ha⟩
  · rintro ⟨hxU, hxU'⟩
    obtain ⟨a, ha, c, hc, rfl⟩ := hdec x hxU
    have h1 : m * a * m⁻¹ ∈ D.U := by
      have := D.U.mul_mem hxU' (D.U.inv_mem (hC c hc))
      have e : (m * (a * c) * m⁻¹) * (m * c * m⁻¹)⁻¹ = m * a * m⁻¹ := by group
      rwa [e] at this
    have ha1 : a = 1 := hone a (key _ h1 (hA a ha))
    simpa [ha1] using hc
  · intro hc
    exact ⟨hCU hc, hC x hc⟩

theorem eq305_core_II {m : X} {V : Subgroup X} (hV : (V : Set X) = D.Uminus) {A C : Set X}
    (hAU : A ⊆ D.U) (hCU : C ⊆ D.U) (hdec : ∀ x ∈ D.U, ∃ a ∈ A, ∃ c ∈ C, x = a * c)
    (hA : ∀ a ∈ A, m * a * m⁻¹ ∈ D.U) (hC : ∀ c ∈ C, m * c * m⁻¹ ∈ V) :
    {x | x ∈ D.U ∧ m * x * m⁻¹ ∈ D.Uminus} = C ∧ {x | x ∈ D.U ∧ m * x * m⁻¹ ∈ D.U} = A := by
  have key : ∀ z : X, z ∈ D.U → z ∈ V → z = 1 := fun z hzU hzV =>
    D.roots.meet_one z (D.U_le_B hzU) (by rwa [← SetLike.mem_coe, hV] at hzV)
  have hone : ∀ z : X, m * z * m⁻¹ = 1 → z = 1 := by
    intro z hz
    have : z = m⁻¹ * (m * z * m⁻¹) * m := by group
    rw [this, hz]
    group
  refine ⟨Set.ext fun x => ⟨?_, ?_⟩, Set.ext fun x => ⟨?_, ?_⟩⟩
  · rintro ⟨hxU, hxV⟩
    obtain ⟨a, ha, c, hc, rfl⟩ := hdec x hxU
    have hxV' : m * (a * c) * m⁻¹ ∈ V := by
      rw [← SetLike.mem_coe, hV]
      exact hxV
    have h1 : m * a * m⁻¹ ∈ V := by
      have := V.mul_mem hxV' (V.inv_mem (hC c hc))
      have e : (m * (a * c) * m⁻¹) * (m * c * m⁻¹)⁻¹ = m * a * m⁻¹ := by group
      rwa [e] at this
    have ha1 : a = 1 := hone a (key _ (hA a ha) h1)
    simpa [ha1] using hc
  · intro hc
    exact ⟨hCU hc, by rw [← hV]; exact hC x hc⟩
  · rintro ⟨hxU, hxU'⟩
    obtain ⟨a, ha, c, hc, rfl⟩ := hdec x hxU
    have h1 : m * c * m⁻¹ ∈ D.U := by
      have := D.U.mul_mem (D.U.inv_mem (hA a ha)) hxU'
      have e : (m * a * m⁻¹)⁻¹ * (m * (a * c) * m⁻¹) = m * c * m⁻¹ := by group
      rwa [e] at this
    have hc1 : c = 1 := hone c (key _ h1 (hC c hc))
    simpa [hc1] using ha
  · intro ha
    exact ⟨hAU ha, hA x ha⟩

variable {D}

theorem chainProd_intList_reverse (D : RankTwoSystem X n) {a b : ℤ} (ha : 1 ≤ a) (hb : b ≤ n) :
    chainProd D.root (intList a b) = chainProd D.root (intList a b).reverse := by
  by_cases hab : a ≤ b
  · exact D.roots.reverse_eq a b ha hab hb
  · rw [intList_eq_nil (by omega)]
    rfl

theorem chainProd_subset_U {a b : ℤ} (ha : 1 ≤ a) (hb : b ≤ n) :
    chainProd D.root (intList a b) ⊆ D.U := by
  refine chainProd_subset D.root D.U _ (fun k hk => ?_)
  obtain ⟨hk1, hk2⟩ := mem_intList_iff.1 hk
  exact D.root_le_U (by omega) (by omega)

theorem U_decomp {i : ℕ} (hi : i ≤ n) :
    ∀ x ∈ D.U, ∃ a ∈ chainProd D.root (intList 1 i), ∃ c ∈ chainProd D.root (intList (i + 1) n),
      x = a * c := by
  intro x hx
  have hx' : x ∈ chainProd D.root (intList 1 n) := by
    rw [← D.roots.carrier_eq]
    exact hx
  rw [← intList_append (a := 1) (b := (i : ℤ)) (c := n) (by omega) (by omega),
    chainProd_append] at hx'
  obtain ⟨a, ha, c, hc, rfl⟩ := Set.mem_mul.1 hx'
  exact ⟨a, ha, c, hc, rfl⟩

theorem U_decomp' {i : ℕ} (hi : i ≤ n) :
    ∀ x ∈ D.U, ∃ a ∈ chainProd D.root (intList 1 ((n : ℤ) - i)),
      ∃ c ∈ chainProd D.root (intList ((n : ℤ) - i + 1) n), x = a * c := by
  intro x hx
  have hx' : x ∈ chainProd D.root (intList 1 n) := by
    rw [← D.roots.carrier_eq]
    exact hx
  rw [← intList_append (a := 1) (b := (n : ℤ) - i) (c := n) (by omega) (by omega),
    chainProd_append] at hx'
  obtain ⟨a, ha, c, hc, rfl⟩ := Set.mem_mul.1 hx'
  exact ⟨a, ha, c, hc, rfl⟩

theorem eq30_5_A {i : ℕ} (hi : i ≤ n) (m : D.N) (hm : (m : D.Weyl) = altWord D.w₁ D.w₂ i) :
    D.UwMinus m = chainProd D.root (intList 1 i) ∧
      D.UwPlus m = chainProd D.root (intList ((i : ℤ) + 1) n) := by
  have hn := D.three_le
  obtain ⟨V, hV⟩ := D.Uminus_isSubgroup
  have hact := actsPos_altWord₁ i m hm
  have hA : ∀ a ∈ chainProd D.root (intList 1 i), (m : X) * a * (m : X)⁻¹ ∈ V := by
    intro a ha
    refine chainProd_conj_mem D.root V (m : X) (intList 1 i) (fun k hk y hy => ?_) a ha
    obtain ⟨hk1, hk2⟩ := mem_intList_iff.1 hk
    have hy' : y ∈ D.root (Rt n (k - 1)) := by rwa [Rt_pos_idx hk1 (by omega)]
    have h1 := hact (k - 1) y hy'
    obtain ⟨hr1, hr2⟩ := Rt_tauA_neg (n := n) (i := i) (q := k - 1) (by omega) (by omega) hi
    exact D.root_le_V hV hr1 hr2 h1
  have hC : ∀ c ∈ chainProd D.root (intList ((i : ℤ) + 1) n), (m : X) * c * (m : X)⁻¹ ∈ D.U := by
    intro c hc
    refine chainProd_conj_mem D.root D.U (m : X) (intList ((i : ℤ) + 1) n)
      (fun k hk y hy => ?_) c hc
    obtain ⟨hk1, hk2⟩ := mem_intList_iff.1 hk
    have hy' : y ∈ D.root (Rt n (k - 1)) := by rwa [Rt_pos_idx (by omega) hk2]
    have h1 := hact (k - 1) y hy'
    obtain ⟨hr1, hr2⟩ := Rt_tauA_pos (n := n) (i := i) (q := k - 1) (by omega) (by omega)
    exact D.root_le_U hr1 hr2 h1
  exact D.eq305_core_I hV (chainProd_subset_U (by omega) (by omega))
    (chainProd_subset_U (by omega) le_rfl) (U_decomp hi) hA hC

theorem eq30_5_B {i : ℕ} (hi : i ≤ n) (m : D.N) (hm : (m : D.Weyl) = altWord D.w₂ D.w₁ i) :
    D.UwMinus m = chainProd D.root (intList ((n : ℤ) - i + 1) n).reverse ∧
      D.UwPlus m = chainProd D.root (intList 1 ((n : ℤ) - i)).reverse := by
  have hn := D.three_le
  obtain ⟨V, hV⟩ := D.Uminus_isSubgroup
  have hact := actsPos_altWord₂ i m hm
  have hA : ∀ a ∈ chainProd D.root (intList 1 ((n : ℤ) - i)), (m : X) * a * (m : X)⁻¹ ∈ D.U := by
    intro a ha
    refine chainProd_conj_mem D.root D.U (m : X) (intList 1 ((n : ℤ) - i))
      (fun k hk y hy => ?_) a ha
    obtain ⟨hk1, hk2⟩ := mem_intList_iff.1 hk
    have hy' : y ∈ D.root (Rt n (k - 1)) := by rwa [Rt_pos_idx hk1 (by omega)]
    have h1 := hact (k - 1) y hy'
    obtain ⟨hr1, hr2⟩ := Rt_tauB_pos (n := n) (i := i) (q := k - 1) (by omega) (by omega)
    exact D.root_le_U hr1 hr2 h1
  have hC : ∀ c ∈ chainProd D.root (intList ((n : ℤ) - i + 1) n),
      (m : X) * c * (m : X)⁻¹ ∈ V := by
    intro c hc
    refine chainProd_conj_mem D.root V (m : X) (intList ((n : ℤ) - i + 1) n)
      (fun k hk y hy => ?_) c hc
    obtain ⟨hk1, hk2⟩ := mem_intList_iff.1 hk
    have hy' : y ∈ D.root (Rt n (k - 1)) := by rwa [Rt_pos_idx (by omega) hk2]
    have h1 := hact (k - 1) y hy'
    obtain ⟨hr1, hr2⟩ := Rt_tauB_neg (n := n) (i := i) (q := k - 1) (by omega) (by omega) hi
    exact D.root_le_V hV hr1 hr2 h1
  obtain ⟨h1, h2⟩ := D.eq305_core_II hV (chainProd_subset_U (by omega) (by omega))
    (chainProd_subset_U (by omega) le_rfl) (U_decomp' hi) hA hC
  refine ⟨?_, ?_⟩
  · exact h1.trans (chainProd_intList_reverse D (by omega) le_rfl)
  · exact h2.trans (chainProd_intList_reverse D (by omega) (by omega))

end RankTwoSystem

theorem eq30_5 : Eq30_5.{u} := by
  intro X _ n D i hi
  exact ⟨fun m hm => D.eq30_5_A hi m hm, fun m hm => D.eq30_5_B hi m hm⟩

end CFSG.GH74.BNPair
