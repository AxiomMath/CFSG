module

public import CFSG.GH74.Tits83.Nu

public section

namespace CFSG.GH74.Tits83

open CFSG.GH74.BNPair

open scoped commutatorElement Pointwise

universe u

variable {G : Type u} [Group G] {n : ℕ}

namespace TitsSystem

variable (T : TitsSystem G n)

theorem lemma212_conj (hn : 3 ≤ n) {i j : ℤ} (hij : i < j) (hj : j < i + n) {u x : G}
    (hu : u ∈ T.U i) (hu1 : u ≠ 1) (hx : x ∈ win T.U j (i + n - 1))
    (hux : u * x = x * u) :
    T.nu i u * x * (T.nu i u)⁻¹ ∈ win T.U j (2 * i + n - j) := by
  set v := T.nu i u
  set m := T.mu i u
  set vb := m * T.nu' i u * m⁻¹
  have hv : v ∈ T.U (i + n) := (T.isMu_nu hu hu1).1
  have hv' : T.nu' i u ∈ T.U (i + n) := (T.isMu_nu hu hu1).2.1
  have hm : m = v * u * T.nu' i u := by simp only [m, v, mu]
  have hvb : vb ∈ T.U i := by
    have h := Moves.conj_mem T (T.moves_mu hu hu1) (j := i + n) hv'
    have e : 2 * i + n - (i + n) = i := by ring
    rwa [e] at h
  have hvb' : vb⁻¹ ∈ T.U i := (T.U i).inv_mem hvb
  have hmx : m * x * m⁻¹ ∈ win T.U (i + 1) (2 * i + n - j) := by
    have hmap := Moves.map_win_refl T (T.moves_mu hu hu1) (a := j) (b := i + n - 1)
    have hmem : m * x * m⁻¹ ∈ (win T.U j (i + n - 1)).map
        (MulAut.conj m).toMonoidHom := ⟨x, hx, rfl⟩
    rw [hmap] at hmem
    have e1 : 2 * i + n - (i + n - 1) = i + 1 := by ring
    have e2 : 2 * i + n - j = 2 * i + n - j := rfl
    rwa [e1, e2] at hmem
  have hrel : m * x * m⁻¹ = vb * (v * x * v⁻¹) * vb⁻¹ := by
    have hdecomp : m = vb * v * u := by
      simp only [m, vb, v, mu]
      group
    rw [hdecomp]
    rw [show vb * v * u * x * (vb * v * u)⁻¹ = vb * (v * (u * x * u⁻¹) * v⁻¹) * vb⁻¹ by
      group]
    rw [hux]
    group
  have hzA : v * x * v⁻¹ ∈ win T.U (i + 1) (2 * i + n - j) := by
    have hnorm : vb⁻¹ ∈ Subgroup.normalizer
        (win T.U (i + 1) (2 * i + n - j) : Set G) := by
      have h := (T.le_normalizer_win (a := i + 1) (b := 2 * i + n - j) (by omega)).1
      exact h (by simpa using hvb')
    have hmem : vb⁻¹ * (m * x * m⁻¹) * vb ∈ win T.U (i + 1) (2 * i + n - j) := by
      have h := (Subgroup.mem_normalizer_iff.mp hnorm (m * x * m⁻¹)).mp hmx
      simpa using h
    simpa [hrel, mul_assoc] using hmem
  have hzB : v * x * v⁻¹ ∈ win T.U j (i + n - 1) := by
    have hnormv : v ∈ Subgroup.normalizer (win T.U j (i + n - 1) : Set G) := by
      have h := (T.le_normalizer_win (a := j) (b := i + n - 1) (by omega)).2
      have hv' : v ∈ T.U (i + n - 1 + 1) := by
        rwa [show i + n - 1 + 1 = i + n by ring]
      exact h hv'
    exact (Subgroup.mem_normalizer_iff.mp hnormv x).mp hx
  have hinter := win_inf_win (T := T) (a := i + 1) (b := 2 * i + n - j) (c := j)
    (d := i + n - 1) (by omega)
  have hmem : v * x * v⁻¹ ∈ win T.U (i + 1) (2 * i + n - j) ⊓
      win T.U j (i + n - 1) := ⟨hzA, hzB⟩
  rw [hinter] at hmem
  convert hmem using 2 <;> omega

theorem lemma212_i (hn : 3 ≤ n) {i j : ℤ} (hij : i < j) (hj : j < i + n)
    (hj2 : 2 * i + n < 2 * j) {u x : G} (hu : u ∈ T.U i) (hu1 : u ≠ 1)
    (hx : x ∈ win T.U j (i + n - 1)) (hux : u * x = x * u) : x = 1 := by
  have hconj := T.lemma212_conj hn hij hj hu hu1 hx hux
  have hbot : win T.U j (2 * i + n - j) = ⊥ := by
    simp [win, show ¬ j ≤ 2 * i + n - j by omega]
  rw [hbot] at hconj
  have hz : T.nu i u * x * (T.nu i u)⁻¹ = 1 := by simpa using hconj
  have h := congrArg (fun y => (T.nu i u)⁻¹ * y * T.nu i u) hz
  simpa [mul_assoc] using h

private theorem commute_nu_of_mid (hn : 3 ≤ n) {i j : ℤ} (hj2 : 2 * j = 2 * i + n)
    {u x : G} (hu : u ∈ T.U i) (hu1 : u ≠ 1) (hx : x ∈ T.U j)
    (hux : u * x = x * u) : x * T.nu i u = T.nu i u * x := by
  set v := T.nu i u
  have hij : i < j := by omega
  have hj : j < i + n := by omega
  have hv : v ∈ T.U (i + n) := (T.isMu_nu hu hu1).1
  have hxwin : x ∈ win T.U j (i + n - 1) :=
    (le_iSup₂_of_le j ⟨le_rfl, by omega⟩ le_rfl : T.U j ≤ win T.U j (i + n - 1)) hx
  have hzUj : v * x * v⁻¹ ∈ T.U j := by
    have h := T.lemma212_conj hn hij hj hu hu1 hxwin hux
    rw [show 2 * i + n - j = j by omega, win] at h
    simpa using h
  have hcomm : ⁅v, x⁆ ∈ win T.U (j + 1) (i + n - 1) := by
    have hx' : ⁅x, v⁆ ∈ win T.U (j + 1) (i + n - 1) := by
      have h := T.comm j (i + n) hj (by omega) x hx v hv
      refine SetLike.le_def.mp ?_ h
      refine iSup₂_le fun k hk => ?_
      have hk1 : j + 1 ≤ k := by linarith [hk.1]
      have hk2 : k ≤ i + n - 1 := by linarith [hk.2]
      exact le_iSup₂_of_le k ⟨hk1, hk2⟩ le_rfl
    have hinv := (win T.U (j + 1) (i + n - 1)).inv_mem hx'
    have e : ⁅v, x⁆ = ⁅x, v⁆⁻¹ := by
      simp only [commutatorElement_def]
      group
    rwa [e]
  have hz_eq : v * x * v⁻¹ = ⁅v, x⁆ * x := by
    simp only [commutatorElement_def]
    group
  have hwUj : ⁅v, x⁆ ∈ T.U j := by
    have hmem : (v * x * v⁻¹) * x⁻¹ ∈ T.U j :=
      (T.U j).mul_mem hzUj ((T.U j).inv_mem hx)
    have e : (v * x * v⁻¹) * x⁻¹ = ⁅v, x⁆ := by
      rw [hz_eq]
      group
    rwa [e] at hmem
  have hbot : win T.U j j ⊓ win T.U (j + 1) (i + n - 1) = ⊥ := by
    rw [win_inf_win (T := T) (a := j) (b := j) (c := j + 1) (d := i + n - 1) (by omega)]
    simp [win, show ¬ j + 1 ≤ j by omega]
  have hw1 : ⁅v, x⁆ = 1 := by
    have hmem : ⁅v, x⁆ ∈ win T.U j j ⊓ win T.U (j + 1) (i + n - 1) :=
      ⟨by simpa [win] using hwUj, hcomm⟩
    rw [hbot] at hmem
    simpa using hmem
  have hzx : v * x * v⁻¹ = x := by
    rw [hz_eq, hw1, one_mul]
  have hcomm' : v * x = x * v := by
    have h := congrArg (fun y => y * v) hzx
    simpa [mul_assoc] using h
  exact hcomm'.symm

theorem lemma212_ii (hn : 3 ≤ n) {i j : ℤ} (hj2 : 2 * j = 2 * i + n) {u x : G}
    (hu : u ∈ T.U i) (hu1 : u ≠ 1) (hx : x ∈ T.U j) (hux : u * x = x * u) :
    x * T.nu i u = T.nu i u * x ∧ x * T.mu i u = T.mu i u * x := by
  have hv := T.commute_nu_of_mid hn hj2 hu hu1 hx hux
  have hu' : u⁻¹ ∈ T.U i := (T.U i).inv_mem hu
  have hu1' : u⁻¹ ≠ 1 := inv_ne_one.mpr hu1
  have hux' : u⁻¹ * x = x * u⁻¹ := by
    have h1 : u⁻¹ * x * u = x := by
      calc u⁻¹ * x * u = u⁻¹ * (x * u) := by group
        _ = u⁻¹ * (u * x) := by rw [← hux]
        _ = x := by group
    have h2 : u⁻¹ * x = x * u⁻¹ := by
      have := congrArg (fun y => y * u⁻¹) h1
      simpa [mul_assoc] using this
    exact h2
  have hv' := T.commute_nu_of_mid hn hj2 hu' hu1' hx hux'
  have hnu' : x * T.nu' i u = T.nu' i u * x := by
    have h : x * T.nu i u⁻¹ = T.nu i u⁻¹ * x := hv'
    rw [T.nu_inv hn hu hu1] at h
    have h2 : T.nu' i u * x = x * T.nu' i u := by
      have := congrArg (fun y => T.nu' i u * y * T.nu' i u) h
      simpa [mul_assoc] using this
    exact h2.symm
  have hvu : x * (T.nu i u * u) = (T.nu i u * u) * x := by
    calc x * (T.nu i u * u) = (x * T.nu i u) * u := by group
      _ = (T.nu i u * x) * u := by rw [hv]
      _ = T.nu i u * (x * u) := by group
      _ = T.nu i u * (u * x) := by rw [← hux]
      _ = (T.nu i u * u) * x := by group
  have hm : x * (T.nu i u * u * T.nu' i u) =
      (T.nu i u * u * T.nu' i u) * x := by
    calc x * (T.nu i u * u * T.nu' i u) = (x * (T.nu i u * u)) * T.nu' i u := by group
      _ = ((T.nu i u * u) * x) * T.nu' i u := by rw [hvu]
      _ = (T.nu i u * u) * (x * T.nu' i u) := by group
      _ = (T.nu i u * u) * (T.nu' i u * x) := by rw [hnu']
      _ = (T.nu i u * u * T.nu' i u) * x := by group
  refine ⟨hv, ?_⟩
  simpa only [mu] using hm

theorem lemma212_ii' (hn : 3 ≤ n) {i j : ℤ} (hj2 : 2 * j = 2 * i - n) {u x : G}
    (hu : u ∈ T.U i) (hu1 : u ≠ 1) (hx : x ∈ T.U j) (hux : u * x = x * u) :
    x * T.nu i u = T.nu i u * x ∧ x * T.mu i u = T.mu i u * x := by
  have huS : u ∈ (T.refl 0).U (-i) := by
    rw [refl_U]
    simpa using hu
  have hxS : x ∈ (T.refl 0).U (-j) := by
    rw [refl_U]
    simpa using hx
  have hj2S : 2 * (-j) = 2 * (-i) + (n : ℤ) := by omega
  have hii := lemma212_ii (T := T.refl 0) hn (i := -i) (j := -j) hj2S huS hu1 hxS hux
  have hnu : (T.refl 0).nu (-i) u = T.nu i u := by
    rw [T.nu_refl hn 0 (-i) u]
    ring_nf
  have hmu : (T.refl 0).mu (-i) u = T.mu i u := by
    have h1 : (T.refl 0).IsMu (-i) u ((T.refl 0).nu (-i) u)
        ((T.refl 0).nu' (-i) u) := isMu_nu (T := T.refl 0) huS hu1
    have h2 : T.IsMu i u (T.nu i u) (T.nu' i u) := T.isMu_nu hu hu1
    have h3 : T.IsMu i u ((T.refl 0).nu (-i) u) ((T.refl 0).nu' (-i) u) := by
      have := (T.isMu_refl_iff 0 (-i) u _ _).1 h1
      simpa using this
    have huniq := T.isMu_unique hn hu hu1 h3 h2
    simp only [mu]
    rw [huniq.1, huniq.2]
  rw [hnu, hmu] at hii
  exact hii

theorem lemma212_iii (hn : 3 ≤ n) {i j : ℤ} (hij : i < j) (hj : 2 * j < 2 * i + n)
    {u x : G} (hu : u ∈ T.U i) (hu1 : u ≠ 1) (hx : x ∈ T.U j) (hux : u * x = x * u) :
    ∃ y ∈ win T.U (j + 1) (2 * i + n - j - 1),
      x⁻¹ * T.nu i u * x * (T.nu i u)⁻¹ =
        y * (T.mu i u * x * (T.mu i u)⁻¹) := by
  have happ : ∀ {x y z : ℤ}, x ≤ y + 1 → y ≤ z →
      intList x z = intList x y ++ intList (y + 1) z := by
    intro x y z h1 h2
    apply List.ext_getElem
    · simp only [intList, List.length_append, List.length_map, List.length_range]
      omega
    · intro t ht1 ht2
      simp only [intList, List.length_map, List.length_range] at ht1 ht2 ⊢
      by_cases ht : t < (y + 1 - x).toNat
      · rw [List.getElem_append_left (by simpa using ht)]
        simp
      · rw [List.getElem_append_right (by simp; omega)]
        simp only [List.getElem_map, List.getElem_range, List.length_map, List.length_range]
        omega
  have pad : ∀ {l a b r : ℤ}, l ≤ a → a ≤ b → b ≤ r → ∀ f : ℤ → G,
      ((intList l r).map (fun k => if a ≤ k ∧ k ≤ b then f k else 1)).prod =
        ((intList a b).map f).prod := by
    intro l a b r hl ha hb f
    classical
    have e1 : intList l r = intList l (a - 1) ++ (intList a b ++ intList (b + 1) r) := by
      have h1 := happ (x := l) (y := a - 1) (z := r) (by omega) (by omega)
      have h2 := happ (x := a) (y := b) (z := r) (by omega) hb
      rw [show a - 1 + 1 = a by ring, h2] at h1
      exact h1
    rw [e1, List.map_append, List.map_append, List.prod_append, List.prod_append]
    have hA : ((intList l (a - 1)).map
        (fun k => if a ≤ k ∧ k ≤ b then f k else (1 : G))).prod = 1 := by
      apply List.prod_eq_one
      intro y hy
      obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hy
      have := mem_intList_iff.1 hk
      have hk' : ¬(a ≤ k ∧ k ≤ b) := by omega
      simp [hk']
    have hC : ((intList (b + 1) r).map
        (fun k => if a ≤ k ∧ k ≤ b then f k else (1 : G))).prod = 1 := by
      apply List.prod_eq_one
      intro y hy
      obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hy
      have := mem_intList_iff.1 hk
      have hk' : ¬(a ≤ k ∧ k ≤ b) := by omega
      simp [hk']
    have hB : (intList a b).map
        (fun k => if a ≤ k ∧ k ≤ b then f k else (1 : G)) = (intList a b).map f := by
      apply List.map_congr_left
      intro k hk
      have := mem_intList_iff.1 hk
      simp [this]
    rw [hA, hC, hB, one_mul, mul_one]
  set v := T.nu i u
  set m := T.mu i u
  set vb := m * T.nu' i u * m⁻¹
  set z := v * x * v⁻¹
  set mx := m * x * m⁻¹
  have hv : v ∈ T.U (i + n) := (T.isMu_nu hu hu1).1
  have hvb : vb ∈ T.U i := by
    have h := Moves.conj_mem T (T.moves_mu hu hu1) (j := i + n) (T.isMu_nu hu hu1).2.1
    have e : 2 * i + n - (i + n) = i := by ring
    rwa [e] at h
  have hvb' : vb⁻¹ ∈ T.U i := (T.U i).inv_mem hvb
  have hmx : mx ∈ T.U (2 * i + n - j) := by
    have h := Moves.conj_mem T (T.moves_mu hu hu1) (j := j) hx
    simpa [mx, m] using h
  have hxwin : x ∈ win T.U j (i + n - 1) :=
    (le_iSup₂_of_le j ⟨le_rfl, by omega⟩ le_rfl : T.U j ≤ win T.U j (i + n - 1)) hx
  have hzwin := T.lemma212_conj hn hij (by omega) hu hu1 hxwin hux
  have hrel : mx = vb * z * vb⁻¹ := by
    simp only [mx, z]
    have hdecomp : m = vb * v * u := by
      simp only [m, vb, v, mu]
      group
    rw [hdecomp]
    rw [show vb * v * u * x * (vb * v * u)⁻¹ =
      vb * (v * (u * x * u⁻¹) * v⁻¹) * vb⁻¹ by group]
    rw [hux]
    group
  have hzA : z = ⁅vb⁻¹, mx⁆ * mx := by
    rw [hrel]
    simp only [commutatorElement_def]
    group
  have hA : ⁅vb⁻¹, mx⁆ ∈ win T.U (i + 1) (2 * i + n - j - 1) := by
    have h := T.comm i (2 * i + n - j) (by omega) (by omega) vb⁻¹ hvb' mx hmx
    refine SetLike.le_def.mp ?_ h
    refine iSup₂_le fun k hk => ?_
    have hk1 : i + 1 ≤ k := by linarith [hk.1]
    have hk2 : k ≤ 2 * i + n - j - 1 := by linarith [hk.2]
    exact le_iSup₂_of_le k ⟨hk1, hk2⟩ le_rfl
  let B : G := x⁻¹ * z
  have hBwin : B ∈ win T.U (j + 1) (i + n - 1) := by
    have hcomm : ⁅v, x⁆ ∈ win T.U (j + 1) (i + n - 1) := by
      have hx' : ⁅x, v⁆ ∈ win T.U (j + 1) (i + n - 1) := by
        have h := T.comm j (i + n) (by omega) (by omega) x hx v hv
        refine SetLike.le_def.mp ?_ h
        refine iSup₂_le fun k hk => ?_
        have hk1 : j + 1 ≤ k := by linarith [hk.1]
        have hk2 : k ≤ i + n - 1 := by linarith [hk.2]
        exact le_iSup₂_of_le k ⟨hk1, hk2⟩ le_rfl
      have hinv := (win T.U (j + 1) (i + n - 1)).inv_mem hx'
      have e : ⁅v, x⁆ = ⁅x, v⁆⁻¹ := by
        simp only [commutatorElement_def]
        group
      rwa [e]
    have hWnorm : win T.U j (i + n - 1) ≤
        Subgroup.normalizer (win T.U (j + 1) (i + n - 1) : Set G) := by
      refine iSup₂_le fun k hk => ?_
      by_cases hkj : k = j
      · rw [hkj]
        simpa using (T.le_normalizer_win (a := j + 1) (b := i + n - 1) (by omega)).1
      · have hklt : j < k := lt_of_le_of_ne hk.1 (Ne.symm hkj)
        have hkW : T.U k ≤ win T.U (j + 1) (i + n - 1) :=
          le_iSup₂_of_le k ⟨by omega, hk.2⟩ le_rfl
        exact hkW.trans Subgroup.le_normalizer
    have hxN := (Subgroup.normalizer (win T.U (j + 1) (i + n - 1) : Set G)).inv_mem
      (hWnorm hxwin)
    have hconj : x⁻¹ * ⁅v, x⁆ * x ∈ win T.U (j + 1) (i + n - 1) := by
      simpa using (Subgroup.mem_normalizer_iff.mp hxN ⁅v, x⁆).mp hcomm
    have hz_eq : z = ⁅v, x⁆ * x := by
      simp only [z, commutatorElement_def]
      group
    have : B = x⁻¹ * ⁅v, x⁆ * x := by
      simp only [B]
      rw [hz_eq]
      group
    rwa [this]
  have hz_eq_xB : z = x * B := by
    simp only [B]
    group
  obtain ⟨a, ha_mem, ha_prod⟩ :=
    (T.mem_win_iff_prod (a := i + 1) (b := 2 * i + n - j - 1) (by omega)).1 hA
  obtain ⟨b, hb_mem, hb_prod⟩ :=
    (T.mem_win_iff_prod (a := j + 1) (b := i + n - 1) (by omega)).1 hBwin
  let F : ℤ → G := fun k =>
    if k = j then x else if j + 1 ≤ k ∧ k ≤ i + n - 1 then b k else 1
  let Gcoords : ℤ → G := fun k =>
    if i + 1 ≤ k ∧ k ≤ 2 * i + n - j - 1 then a k
    else if k = 2 * i + n - j then mx else 1
  have hF : ∀ k ∈ intList (i + 1) (i + n), F k ∈ T.U k := by
    intro k hk
    have hk' := mem_intList_iff.1 hk
    by_cases hkj : k = j
    · rw [hkj]
      have hFj : F j = x := by
        change (if j = j then x else if j + 1 ≤ j ∧ j ≤ i + n - 1 then b j else 1) = x
        rw [if_pos rfl]
      rw [hFj]
      exact hx
    · by_cases hkr : j + 1 ≤ k ∧ k ≤ i + n - 1
      · rw [show F k = b k by simp [F, hkj, hkr]]
        exact hb_mem k (mem_intList_iff.2 hkr)
      · rw [show F k = 1 by simp [F, hkj, hkr]]
        exact (T.U k).one_mem
  have hG : ∀ k ∈ intList (i + 1) (i + n), Gcoords k ∈ T.U k := by
    intro k hk
    have hk' := mem_intList_iff.1 hk
    by_cases hkl : i + 1 ≤ k ∧ k ≤ 2 * i + n - j - 1
    · rw [show Gcoords k = a k by simp [Gcoords, hkl]]
      exact ha_mem k (mem_intList_iff.2 hkl)
    · by_cases hkj : k = 2 * i + n - j
      · rw [hkj]
        have hGj : Gcoords (2 * i + n - j) = mx := by
          change (if i + 1 ≤ 2 * i + n - j ∧ 2 * i + n - j ≤ 2 * i + n - j - 1
            then a (2 * i + n - j) else if 2 * i + n - j = 2 * i + n - j
              then mx else 1) = mx
          rw [if_neg (by omega), if_pos rfl]
        rw [hGj]
        exact hmx
      · rw [show Gcoords k = 1 by simp [Gcoords, hkl, hkj]]
        exact (T.U k).one_mem
  have hFprod : ((intList (i + 1) (i + n)).map F).prod = z := by
    let F' : ℤ → G := fun k => if k = j then x else b k
    have hmap : (intList (i + 1) (i + n)).map F =
        (intList (i + 1) (i + n)).map
          (fun k => if j ≤ k ∧ k ≤ i + n - 1 then F' k else 1) := by
      apply List.map_congr_left
      intro k hk
      have hk' := mem_intList_iff.1 hk
      by_cases hkj : k = j
      · simp [F, F', hkj, show j ≤ i + n - 1 by omega]
      · by_cases hkr : j + 1 ≤ k ∧ k ≤ i + n - 1
        · have hjk : j ≤ k := by omega
          simp [F, F', hkj, hkr, hjk]
        · have hnot : ¬(j ≤ k ∧ k ≤ i + n - 1) := by omega
          simp [F, F', hkj, hkr, hnot]
    rw [hmap, pad (l := i + 1) (a := j) (b := i + n - 1) (r := i + n)
      (by omega) (by omega) (by omega) F']
    rw [happ (x := j) (y := j) (z := i + n - 1) (by omega) (by omega),
      List.map_append, List.prod_append]
    have hsingle : ((intList j j).map F').prod = x := by simp [intList, F']
    have htail : (intList (j + 1) (i + n - 1)).map F' =
        (intList (j + 1) (i + n - 1)).map b := by
      apply List.map_congr_left
      intro k hk
      have hk' := mem_intList_iff.1 hk
      simp [F', show k ≠ j by omega]
    rw [hsingle, htail, ← hb_prod]
    exact hz_eq_xB.symm
  have hGprod : ((intList (i + 1) (i + n)).map Gcoords).prod = z := by
    let G' : ℤ → G := fun k => if k = 2 * i + n - j then mx else a k
    have hmap : (intList (i + 1) (i + n)).map Gcoords =
        (intList (i + 1) (i + n)).map
          (fun k => if i + 1 ≤ k ∧ k ≤ 2 * i + n - j then G' k else 1) := by
      apply List.map_congr_left
      intro k hk
      have hk' := mem_intList_iff.1 hk
      by_cases hkl : i + 1 ≤ k ∧ k ≤ 2 * i + n - j - 1
      · have hle : k ≤ 2 * i + n - j := by omega
        have hne : k ≠ 2 * i + n - j := by omega
        simp [Gcoords, G', hkl, hle, hne]
      · by_cases hkj : k = 2 * i + n - j
        · simp [Gcoords, G', hkl, hkj, show i + 1 ≤ 2 * i + n - j by omega]
        · have hnot : ¬(i + 1 ≤ k ∧ k ≤ 2 * i + n - j) := by omega
          simp [Gcoords, G', hkl, hkj, hnot]
    rw [hmap, pad (l := i + 1) (a := i + 1) (b := 2 * i + n - j) (r := i + n)
      (by omega) (by omega) (by omega) G']
    rw [happ (x := i + 1) (y := 2 * i + n - j - 1) (z := 2 * i + n - j)
      (by omega) (by omega), List.map_append, List.prod_append]
    have htail : ((intList (2 * i + n - j - 1 + 1) (2 * i + n - j)).map G').prod = mx := by
      rw [show 2 * i + n - j - 1 + 1 = 2 * i + n - j by ring]
      simp [intList, G']
    have hfirst : (intList (i + 1) (2 * i + n - j - 1)).map G' =
        (intList (i + 1) (2 * i + n - j - 1)).map a := by
      apply List.map_congr_left
      intro k hk
      have hk' := mem_intList_iff.1 hk
      simp [G', show k ≠ 2 * i + n - j by omega]
    rw [hfirst, htail, ← ha_prod]
    exact hzA.symm
  have hprod : ((intList (i + 1) (i + n)).map F).prod =
      ((intList (i + 1) (i + n)).map Gcoords).prod := hFprod.trans hGprod.symm
  have huniq := T.unique i F Gcoords hF hG hprod
  have hbj' : b (2 * i + n - j) = mx := by
    have hk : 2 * i + n - j ∈ intList (i + 1) (i + n) := mem_intList_iff.2 ⟨by omega, by omega⟩
    have := huniq (2 * i + n - j) hk
    have hle : j + 1 ≤ 2 * i + n - j := by omega
    have hle2 : 2 * i + n - j ≤ i + n - 1 := by omega
    simpa [F, Gcoords, show 2 * i + n - j ≠ j by omega, hle, hle2,
      show ¬(i + 1 ≤ 2 * i + n - j ∧ 2 * i + n - j ≤ 2 * i + n - j - 1) by omega] using this
  have hb_gt : ∀ k, 2 * i + n - j < k → k ≤ i + n - 1 → b k = 1 := by
    intro k hk1 hk2
    have hk : k ∈ intList (i + 1) (i + n) := mem_intList_iff.2 ⟨by omega, by omega⟩
    have := huniq k hk
    have hle : j + 1 ≤ k := by omega
    have hle2 : k ≤ i + n - 1 := hk2
    simpa [F, Gcoords, show k ≠ j by omega, show k ≠ 2 * i + n - j by omega, hle, hle2,
      show ¬(i + 1 ≤ k ∧ k ≤ 2 * i + n - j - 1) by omega] using this
  let y : G := ((intList (j + 1) (2 * i + n - j - 1)).map b).prod
  have hy : y ∈ win T.U (j + 1) (2 * i + n - j - 1) := by
    refine (T.mem_win_iff_prod (a := j + 1) (b := 2 * i + n - j - 1) (by omega)).2
      ⟨b, ?_, rfl⟩
    intro k hk
    have hk' := mem_intList_iff.1 hk
    have hj'le : 2 * i + n - j ≤ i + n - 1 := by omega
    exact hb_mem k (mem_intList_iff.2 ⟨hk'.1, by linarith [hk'.2]⟩)
  let H : ℤ → G := fun k =>
    if j + 1 ≤ k ∧ k ≤ 2 * i + n - j then
      (if k = 2 * i + n - j then mx else b k) else 1
  have hbH : (intList (j + 1) (i + n - 1)).map b =
      (intList (j + 1) (i + n - 1)).map H := by
    apply List.map_congr_left
    intro k hk
    have hk' := mem_intList_iff.1 hk
    by_cases hklt : k < 2 * i + n - j
    · have hle : j + 1 ≤ k := hk'.1
      have hne : k ≠ 2 * i + n - j := by omega
      simp [H, hle, hklt.le, hne]
    · by_cases hkeq : k = 2 * i + n - j
      · rw [hkeq]
        have hle : j + 1 ≤ 2 * i + n - j := by omega
        simp [H, hbj', hle]
      · have hkgt : 2 * i + n - j < k := by omega
        have hb1 := hb_gt k hkgt hk'.2
        have hnotle : ¬ k ≤ 2 * i + n - j := by omega
        simp [H, hb1, hnotle]
  have hB_eq : B = y * mx := by
    rw [hb_prod]
    calc ((intList (j + 1) (i + n - 1)).map b).prod
        = ((intList (j + 1) (i + n - 1)).map H).prod := by rw [hbH]
      _ = ((intList (j + 1) (2 * i + n - j)).map
            (fun k => if k = 2 * i + n - j then mx else b k)).prod := by
          rw [pad (l := j + 1) (a := j + 1) (b := 2 * i + n - j) (r := i + n - 1)
            (by omega) (by omega) (by omega)]
      _ = y * mx := by
          rw [happ (x := j + 1) (y := 2 * i + n - j - 1) (z := 2 * i + n - j)
            (by omega) (by omega), List.map_append, List.prod_append]
          have h1 : ((intList (j + 1) (2 * i + n - j - 1)).map
              (fun k => if k = 2 * i + n - j then mx else b k)).prod = y := by
            apply congrArg List.prod
            apply List.map_congr_left
            intro k hk
            have hk' := mem_intList_iff.1 hk
            simp [show k ≠ 2 * i + n - j by omega]
          have h2 : ((intList (2 * i + n - j - 1 + 1) (2 * i + n - j)).map
              (fun k => if k = 2 * i + n - j then mx else b k)).prod = mx := by
            rw [show 2 * i + n - j - 1 + 1 = 2 * i + n - j by ring]
            simp [intList]
          rw [h1, h2]
  refine ⟨y, hy, ?_⟩
  change x⁻¹ * v * x * v⁻¹ = y * mx
  have hL : x⁻¹ * v * x * v⁻¹ = B := by
    simp only [B, z]
    group
  rw [hL, hB_eq]


theorem lemma29 (hn : 3 ≤ n) {u v : G} (hu : u ∈ T.U 1) (hu1 : u ≠ 1) (hv : v ∈ T.U n)
    (hv1 : v ≠ 1) :
    ∃ s : ℕ → G, s 1 = u⁻¹ ∧ s n = v ∧ (∀ k : ℕ, 1 ≤ k → s k ∈ T.U (k : ℤ) ∧ s k ≠ 1) ∧
      (∀ k : ℕ, 1 ≤ k → s (k + n) = T.nu' (k : ℤ) (s k)) ∧
      (∀ k : ℕ, 1 ≤ k →
        ⁅(s k)⁻¹, s (k + n - 1)⁆ = ((List.range' (k + 1) (n - 2)).map s).prod) ∧
      (∀ k : ℕ, 1 ≤ k →
        s (k + n - 1) = T.mu (k : ℤ) (s k) * s (k + 1) * (T.mu (k : ℤ) (s k))⁻¹) := by
  classical
  have hnZ : (3 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
  have hcomm_mem : ⁅u, v⁆ ∈ win T.U (2 : ℤ) ((n : ℤ) - 1) := by
    have h := T.comm (1 : ℤ) (n : ℤ) (by omega) (by omega) u hu v hv
    have he : u * v * u⁻¹ * v⁻¹ = ⁅u, v⁆ := by simp [commutatorElement_def]
    rw [he] at h
    refine SetLike.le_def.mp ?_ h
    refine iSup₂_le fun j hj => ?_
    obtain ⟨hj1, hj2⟩ := hj
    exact le_iSup₂_of_le j ⟨by omega, by omega⟩ le_rfl
  obtain ⟨f, hf, hfprod⟩ :=
    (T.mem_win_iff_prod (a := (2 : ℤ)) (b := (n : ℤ) - 1) (by omega)).1 hcomm_mem
  let ind : (m : ℕ) → (∀ m' < m, G) → G := fun m ih =>
    if m = 1 then u⁻¹ else if m = n then v
    else if 2 ≤ m ∧ m ≤ n - 1 then f (m : ℤ)
    else if h : n < m then T.nu' ((m - n : ℕ) : ℤ) (ih (m - n) (by omega)) else 1
  let s : ℕ → G := fun m => Nat.strongRecOn m ind
  have hs_one : s 1 = u⁻¹ := by
    unfold s
    rw [Nat.strongRecOn_eq]
    simp [ind]
  have hs_n : s n = v := by
    unfold s
    rw [Nat.strongRecOn_eq]
    have hn1 : n ≠ 1 := by omega
    simp [ind, hn1]
  have hs_mid : ∀ m : ℕ, 2 ≤ m → m ≤ n - 1 → s m = f (m : ℤ) := by
    intro m h2 hmn
    unfold s
    rw [Nat.strongRecOn_eq]
    have hm1 : m ≠ 1 := by omega
    have hmn' : m ≠ n := by omega
    have hcond : 2 ≤ m ∧ m ≤ n - 1 := ⟨h2, hmn⟩
    simp [ind, hm1, hmn', hcond]
  have hs_rec : ∀ k : ℕ, 1 ≤ k → s (k + n) = T.nu' (k : ℤ) (s k) := by
    intro k hk
    unfold s
    rw [Nat.strongRecOn_eq]
    simp only [ind]
    have h1 : ¬ (k + n = 1) := by omega
    have h2 : ¬ (k + n = n) := by omega
    have h3 : ¬ (2 ≤ k + n ∧ k + n ≤ n - 1) := by omega
    have h4 : n < k + n := by omega
    rw [if_neg h1, if_neg h2, if_neg h3, dif_pos h4]
    have hkn : k + n - n = k := by omega
    rw [hkn]
  have hbase_mem : ∀ m : ℕ, 1 ≤ m → m ≤ n → s m ∈ T.U (m : ℤ) := by
    intro m h1 hmn
    rcases eq_or_lt_of_le hmn with rfl | hlt
    · rw [hs_n]; exact hv
    · by_cases hm1 : m = 1
      · rw [hm1, hs_one]; exact (T.U (1 : ℤ)).inv_mem hu
      · have h2 : 2 ≤ m := by omega
        rw [hs_mid m h2 (by omega)]
        exact hf (m : ℤ) (mem_intList_iff.2 ⟨by omega, by omega⟩)
  have hs1_ne : s 1 ≠ 1 := by
    rw [hs_one]
    exact inv_ne_one.mpr hu1
  have hsn_ne : s n ≠ 1 := by
    rw [hs_n]
    exact hv1
  have hncast : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    norm_num
  let S : ℤ → G := fun z => s z.toNat
  have range'_intList : ∀ (a N : ℕ), 1 ≤ N →
      (List.range' a N).map (fun m : ℕ => (m : ℤ)) =
        intList (a : ℤ) (((a + N - 1 : ℕ)) : ℤ) := by
    intro a N hN
    apply List.ext_getElem
    · simp only [List.length_map, List.length_range', intList, List.length_map, List.length_range]
      have hlen : (((a + N - 1 : ℕ) : ℤ) + 1 - (a : ℤ)) = (N : ℤ) := by
        push_cast
        omega
      rw [hlen]
      simp
    · intro i h1 h2
      simp only [List.getElem_map, List.getElem_range', intList, List.length_map,
        List.length_range, List.getElem_map, List.getElem_range]
      push_cast
      ring
  have hbridge : ∀ k : ℕ, 1 ≤ k →
      ((List.range' (k + 1) (n - 2)).map s).prod =
        ((intList (((k + 1 : ℕ) : ℤ)) (((k + n - 2 : ℕ) : ℤ))).map S).prod := by
    intro k hk
    have hlist := range'_intList (k + 1) (n - 2) (by omega)
    have hSs : (List.range' (k + 1) (n - 2)).map s =
        (List.range' (k + 1) (n - 2)).map (fun m : ℕ => S ((m : ℕ) : ℤ)) := by
      apply List.map_congr_left
      intro m hm
      simp [S]
    have hlist' : (List.map (fun m : ℕ => (m : ℤ)) (List.range' (k + 1) (n - 2))) =
        intList ((k + 1 : ℕ) : ℤ) ((k + n - 2 : ℕ) : ℤ) := by
      simpa [show k + 1 + (n - 2) - 1 = k + n - 2 by omega] using hlist
    calc
      ((List.range' (k + 1) (n - 2)).map s).prod
          = ((List.range' (k + 1) (n - 2)).map
              (fun m : ℕ => S ((m : ℕ) : ℤ))).prod := by
            rw [hSs]
      _ = (((List.range' (k + 1) (n - 2)).map
              (fun m : ℕ => (m : ℤ))).map S).prod := by
            rw [List.map_map]
            rfl
      _ = ((intList ((k + 1 : ℕ) : ℤ) ((k + n - 2 : ℕ) : ℤ)).map S).prod := by
            rw [hlist']
  have hC1 : ⁅(s 1)⁻¹, s (1 + n - 1)⁆ =
      ((List.range' (1 + 1) (n - 2)).map s).prod := by
    have hleft : ⁅(s 1)⁻¹, s (1 + n - 1)⁆ = ⁅u, v⁆ := by
      rw [hs_one, show 1 + n - 1 = n by omega, hs_n]
      simp
    rw [hleft, hfprod, hbridge 1 (by omega)]
    have h2cast : ((1 + n - 2 : ℕ) : ℤ) = (n : ℤ) - 1 := by
      have hn1 : 1 + n - 2 = n - 1 := by omega
      rw [hn1, Nat.cast_sub (by omega : 1 ≤ n)]
      norm_num
    rw [show ((1 + 1 : ℕ) : ℤ) = (2 : ℤ) by norm_num, h2cast]
    congr 1
    apply List.map_congr_left
    intro j hj
    have hj' := mem_intList_iff.1 hj
    have h0 : 0 ≤ j := by omega
    have hcast : ((j.toNat : ℕ) : ℤ) = j := Int.toNat_of_nonneg h0
    have h2 : 2 ≤ j.toNat := by
      have : (2 : ℤ) ≤ ((j.toNat : ℕ) : ℤ) := by rw [hcast]; exact hj'.1
      exact_mod_cast this
    have hle : j.toNat ≤ n - 1 := by
      have : ((j.toNat : ℕ) : ℤ) ≤ ((n - 1 : ℕ) : ℤ) := by
        rw [hcast, hncast]; exact hj'.2
      exact_mod_cast this
    rw [show S j = s j.toNat from rfl, hs_mid j.toNat h2 hle]
    congr 1
    exact hcast.symm
  have commute_adj : ∀ {i : ℤ} {x y : G}, x ∈ T.U i → y ∈ T.U (i + 1) → x * y = y * x := by
    intro i x y hx hy
    have hzero : ⁅x, y⁆ ∈ (⊥ : Subgroup G) := by
      have h := T.comm i (i + 1) (by omega) (by omega) x hx y hy
      have hempty : Set.Ioo i (i + 1) = (∅ : Set ℤ) := by
        ext j
        simp only [Set.mem_Ioo, Set.mem_empty_iff_false, iff_false]
        omega
      rw [hempty] at h
      simpa [commutatorElement_def] using h
    rw [Subgroup.mem_bot] at hzero
    exact commutatorElement_eq_one_iff_mul_comm.mp hzero
  have intList_append : ∀ {x y z : ℤ}, x ≤ y + 1 → y ≤ z →
      intList x z = intList x y ++ intList (y + 1) z := by
    intro x y z h1 h2
    apply List.ext_getElem
    · simp only [intList, List.length_append, List.length_map, List.length_range]
      omega
    · intro t ht1 ht2
      simp only [intList, List.length_map, List.length_range] at ht1 ht2 ⊢
      by_cases ht : t < (y + 1 - x).toNat
      · rw [List.getElem_append_left (by simpa using ht)]
        simp
      · rw [List.getElem_append_right (by simp; omega)]
        simp only [List.getElem_map, List.getElem_range, List.length_map, List.length_range]
        omega
  have pad : ∀ {l a b r : ℤ}, l ≤ a → a ≤ b → b ≤ r → ∀ f : ℤ → G,
      ((intList l r).map (fun k => if a ≤ k ∧ k ≤ b then f k else 1)).prod =
        ((intList a b).map f).prod := by
    intro l a b r hl ha hb f
    classical
    have e1 : intList l r = intList l (a - 1) ++ (intList a b ++ intList (b + 1) r) := by
      have h1 := intList_append (x := l) (y := a - 1) (z := r) (by omega) (by omega)
      have h2 := intList_append (x := a) (y := b) (z := r) (by omega) hb
      rw [show a - 1 + 1 = a by ring, h2] at h1
      exact h1
    rw [e1, List.map_append, List.map_append, List.prod_append, List.prod_append]
    have hA : ((intList l (a - 1)).map
        (fun k => if a ≤ k ∧ k ≤ b then f k else (1 : G))).prod = 1 := by
      apply List.prod_eq_one
      intro y hy
      obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hy
      have := mem_intList_iff.1 hk
      have hk' : ¬(a ≤ k ∧ k ≤ b) := by omega
      simp [hk']
    have hC : ((intList (b + 1) r).map
        (fun k => if a ≤ k ∧ k ≤ b then f k else (1 : G))).prod = 1 := by
      apply List.prod_eq_one
      intro y hy
      obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hy
      have := mem_intList_iff.1 hk
      have hk' : ¬(a ≤ k ∧ k ≤ b) := by omega
      simp [hk']
    have hB : (intList a b).map
        (fun k => if a ≤ k ∧ k ≤ b then f k else (1 : G)) = (intList a b).map f := by
      apply List.map_congr_left
      intro k hk
      have := mem_intList_iff.1 hk
      simp [this]
    rw [hA, hC, hB, one_mul, mul_one]
  have Cnext : ∀ k : ℕ, 1 ≤ k →
      s k ∈ T.U (k : ℤ) → s k ≠ 1 →
      s (k + n - 1) ∈ T.U ((k : ℤ) + n - 1) →
      s (k + n) = T.nu' (k : ℤ) (s k) →
      ⁅(s k)⁻¹, s (k + n - 1)⁆ = ((List.range' (k + 1) (n - 2)).map s).prod →
      s (k + n - 1) = T.mu (k : ℤ) (s k) * s (k + 1) * (T.mu (k : ℤ) (s k))⁻¹ →
      ⁅(s (k + 1))⁻¹, s (k + n)⁆ = ((List.range' (k + 2) (n - 2)).map s).prod := by
    intro k hk ha ha1 hb hrec hC hR
    let a : G := s k
    let b : G := s (k + n - 1)
    let c : G := s (k + n)
    let ν : G := T.nu (k : ℤ) a
    let m : G := T.mu (k : ℤ) a
    let P : G := ((List.range' (k + 1) (n - 2)).map s).prod
    let Q : G := ((List.range' (k + 2) (n - 2)).map s).prod
    let Middle : G := ((List.range' (k + 2) (n - 3)).map s).prod
    have hPfac : P = s (k + 1) * Middle := by
      have hlist : List.range' (k + 1) (n - 2) =
          (k + 1) :: List.range' (k + 2) (n - 3) := by
        rw [show n - 2 = (n - 3) + 1 by omega, List.range'_succ]
      change ((List.range' (k + 1) (n - 2)).map s).prod =
        s (k + 1) * ((List.range' (k + 2) (n - 3)).map s).prod
      rw [hlist, List.map_cons, List.prod_cons]
    have hQfac : Q = Middle * b := by
      have hlist : List.range' (k + 2) (n - 2) =
          List.range' (k + 2) (n - 3) ++ [k + n - 1] := by
        rw [show n - 2 = (n - 3) + 1 by omega, List.range'_concat]
        rw [show k + 2 + 1 * (n - 3) = k + n - 1 by omega]
      change ((List.range' (k + 2) (n - 2)).map s).prod =
        ((List.range' (k + 2) (n - 3)).map s).prod * b
      rw [hlist, List.map_append, List.prod_append]
      congr 1
      simp [b]
    have hE : P * b = a⁻¹ * b * a := by
      dsimp only [P, b, a]
      rw [← hC]
      simp only [commutatorElement_def]
      group
    have hm : m = ν * a * c := by
      change T.nu (k : ℤ) a * a * T.nu' (k : ℤ) a =
        T.nu (k : ℤ) a * a * c
      rw [← hrec]
    have hcommνb : ν * b = b * ν := by
      have hνmem : ν ∈ T.U ((k : ℤ) + n) := (T.isMu_nu ha ha1).1
      have hνmem' : ν ∈ T.U ((k : ℤ) + n - 1 + 1) := by
        simpa [show (k : ℤ) + n - 1 + 1 = (k : ℤ) + n by ring] using hνmem
      have hbmem : b ∈ T.U ((k : ℤ) + n - 1) := hb
      exact (commute_adj (i := (k : ℤ) + n - 1) hbmem hνmem').symm
    have hF : c * m⁻¹ * b * m * c⁻¹ = a⁻¹ * b * a := by
      rw [hm]
      have h1 : c * (ν * a * c)⁻¹ * b * (ν * a * c) * c⁻¹ =
          a⁻¹ * ν⁻¹ * b * ν * a := by group
      rw [h1]
      have h2 : ν⁻¹ * b = b * ν⁻¹ := by
        have h3 : b * ν⁻¹ = ν⁻¹ * b := by
          calc b * ν⁻¹ = ν⁻¹ * (ν * b) * ν⁻¹ := by group
            _ = ν⁻¹ * (b * ν) * ν⁻¹ := by rw [hcommνb]
            _ = ν⁻¹ * b := by group
        exact h3.symm
      calc
        a⁻¹ * ν⁻¹ * b * ν * a = a⁻¹ * (ν⁻¹ * b) * ν * a := by group
        _ = a⁻¹ * (b * ν⁻¹) * ν * a := by rw [h2]
        _ = a⁻¹ * b * a := by group
    have hz : m⁻¹ * b * m = s (k + 1) := by
      dsimp only [b, m, a]
      rw [hR]
      group
    have hmain1 : P * b = c * s (k + 1) * c⁻¹ := by
      calc
        P * b = a⁻¹ * b * a := hE
        _ = c * m⁻¹ * b * m * c⁻¹ := hF.symm
        _ = c * (m⁻¹ * b * m) * c⁻¹ := by group
        _ = c * s (k + 1) * c⁻¹ := by rw [hz]
    have hPfac2 : P * b = s (k + 1) * Q := by
      rw [hPfac, hQfac]
      group
    have hcomm2 : c * s (k + 1) * c⁻¹ =
        s (k + 1) * ⁅(s (k + 1))⁻¹, c⁆ := by
      simp only [commutatorElement_def]
      group
    have hQeq : Q = ⁅(s (k + 1))⁻¹, c⁆ := by
      rw [hPfac2, hcomm2] at hmain1
      exact mul_left_cancel hmain1
    change ⁅(s (k + 1))⁻¹, c⁆ = Q
    exact hQeq.symm
  have R_of_C : ∀ k : ℕ, 1 ≤ k →
      s k ∈ T.U (k : ℤ) → s k ≠ 1 →
      s (k + n) = T.nu' (k : ℤ) (s k) →
      (∀ j : ℤ, (k : ℤ) + 1 ≤ j → j ≤ (k : ℤ) + n - 1 → S j ∈ T.U j) →
      ⁅(s k)⁻¹, s (k + n - 1)⁆ = ((List.range' (k + 1) (n - 2)).map s).prod →
      s (k + n - 1) = T.mu (k : ℤ) (s k) * s (k + 1) * (T.mu (k : ℤ) (s k))⁻¹ := by
    intro k hk ha ha1 hrec hmem_range hC
    let a : G := s k
    let b : G := s (k + n - 1)
    let c : G := s (k + n)
    let ν : G := T.nu (k : ℤ) a
    let m : G := T.mu (k : ℤ) a
    let z : G := m⁻¹ * b * m
    let P : G := ((List.range' (k + 1) (n - 2)).map s).prod
    have hbmem : b ∈ T.U ((k : ℤ) + n - 1) := by
      have h := hmem_range ((k : ℤ) + n - 1) (by omega) (by omega)
      have hjnat : (((k : ℤ) + n - 1).toNat) = k + n - 1 := by omega
      simpa [S, b, hjnat] using h
    have hcmem : c ∈ T.U ((k : ℤ) + n) := by
      have h := (T.isMu_nu ha ha1).2.1
      simpa [c, hrec] using h
    have hνmem : ν ∈ T.U ((k : ℤ) + n) := (T.isMu_nu ha ha1).1
    have hcommνb : ν * b = b * ν := by
      have hν' : ν ∈ T.U (((k : ℤ) + n - 1) + 1) := by
        simpa [show (k : ℤ) + n - 1 + 1 = (k : ℤ) + n by ring] using hνmem
      exact (commute_adj (i := (k : ℤ) + n - 1) hbmem hν').symm
    have hmov : T.Moves m (fun j => 2 * (k : ℤ) + n - j) := T.moves_mu ha ha1
    have hmov_inv : T.Moves m⁻¹ (fun j => 2 * (k : ℤ) + n - j) :=
      Moves.inv_refl T hmov
    have hzmem : z ∈ T.U ((k : ℤ) + 1) := by
      have h := Moves.conj_mem T hmov_inv hbmem
      have e : 2 * (k : ℤ) + n - ((k : ℤ) + n - 1) = (k : ℤ) + 1 := by ring
      simpa [z, e] using h
    have hczmem : ⁅c, z⁆ ∈ win T.U ((k : ℤ) + 2) ((k : ℤ) + n - 1) := by
      have h := T.comm ((k : ℤ) + 1) ((k : ℤ) + n) (by omega) (by omega)
        z hzmem c hcmem
      have h' : ⁅z, c⁆ ∈ win T.U ((k : ℤ) + 2) ((k : ℤ) + n - 1) := by
        refine SetLike.le_def.mp ?_ h
        refine iSup₂_le fun t ht => ?_
        obtain ⟨ht1, ht2⟩ := ht
        exact le_iSup₂_of_le t ⟨by omega, by omega⟩ le_rfl
      have he : ⁅c, z⁆ = ⁅z, c⁆⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [he]
      exact (win T.U ((k : ℤ) + 2) ((k : ℤ) + n - 1)).inv_mem h'
    have hznorm : z ∈ Subgroup.normalizer
        (win T.U ((k : ℤ) + 2) ((k : ℤ) + n - 1) : Set G) := by
      have h := (T.le_normalizer_win (a := (k : ℤ) + 2)
        (b := (k : ℤ) + n - 1) (by omega)).1
      have hzU : z ∈ T.U (((k : ℤ) + 2) - 1) := by
        rw [show (k : ℤ) + 2 - 1 = (k : ℤ) + 1 by ring]
        exact hzmem
      exact h hzU
    have hwinmem : z⁻¹ * ⁅c, z⁆ * z ∈
        win T.U ((k : ℤ) + 2) ((k : ℤ) + n - 1) := by
      have hzN : z⁻¹ ∈ Subgroup.normalizer
          (win T.U ((k : ℤ) + 2) ((k : ℤ) + n - 1) : Set G) :=
        (Subgroup.normalizer _).inv_mem hznorm
      have := (Subgroup.mem_normalizer_iff.mp hzN ⁅c, z⁆).mp hczmem
      simpa using this
    obtain ⟨hcoord, hcoord_mem, hcoord_prod⟩ :=
      (T.mem_win_iff_prod (a := (k : ℤ) + 2) (b := (k : ℤ) + n - 1)
        (by omega)).1 hwinmem
    let F : ℤ → G := fun j =>
      if (k : ℤ) + 1 ≤ j ∧ j ≤ (k : ℤ) + n - 1 then S j else 1
    let Gfun : ℤ → G := fun j =>
      if j = (k : ℤ) + 1 then z
      else if (k : ℤ) + 2 ≤ j ∧ j ≤ (k : ℤ) + n - 1 then hcoord j else 1
    have hFmem : ∀ j ∈ intList ((k : ℤ) + 1) ((k : ℤ) + n), F j ∈ T.U j := by
      intro j hj
      have hj' := mem_intList_iff.1 hj
      by_cases hcond : (k : ℤ) + 1 ≤ j ∧ j ≤ (k : ℤ) + n - 1
      · have hmem := hmem_range j hcond.1 hcond.2
        simpa [F, hcond] using hmem
      · have hjn : j = (k : ℤ) + n := by omega
        have hFone : F j = 1 := by simp [F, hcond]
        rw [hFone, hjn]
        exact (T.U ((k : ℤ) + n)).one_mem
    have hGmem : ∀ j ∈ intList ((k : ℤ) + 1) ((k : ℤ) + n), Gfun j ∈ T.U j := by
      intro j hj
      have hj' := mem_intList_iff.1 hj
      by_cases hjs : j = (k : ℤ) + 1
      · have hGz : Gfun j = z := by simp [Gfun, hjs]
        rw [hGz, hjs]
        exact hzmem
      · by_cases hcond : (k : ℤ) + 2 ≤ j ∧ j ≤ (k : ℤ) + n - 1
        · have hGh : Gfun j = hcoord j := by simp [Gfun, hjs, hcond]
          rw [hGh]
          exact hcoord_mem j (mem_intList_iff.2 hcond)
        · have hjn : j = (k : ℤ) + n := by omega
          have hGone : Gfun j = 1 := by simp [Gfun, hjs, hcond]
          rw [hGone, hjn]
          exact (T.U ((k : ℤ) + n)).one_mem
    have hFprod : ((intList ((k : ℤ) + 1) ((k : ℤ) + n)).map F).prod = P * b := by
      have hpad := pad (l := (k : ℤ) + 1) (a := (k : ℤ) + 1)
        (b := (k : ℤ) + n - 1) (r := (k : ℤ) + n) (by omega) (by omega)
        (by omega) S
      have hFeq : (intList ((k : ℤ) + 1) ((k : ℤ) + n)).map F =
          (intList ((k : ℤ) + 1) ((k : ℤ) + n)).map
            (fun j => if (k : ℤ) + 1 ≤ j ∧ j ≤ (k : ℤ) + n - 1 then S j else 1) := by
        apply List.map_congr_left
        intro j hj
        simp [F]
      rw [hFeq, hpad]
      have hsplit := intList_append (x := (k : ℤ) + 1) (y := (k : ℤ) + n - 2)
        (z := (k : ℤ) + n - 1) (by omega) (by omega)
      rw [hsplit, show (k : ℤ) + n - 2 + 1 = (k : ℤ) + n - 1 by ring,
        List.map_append, List.prod_append]
      have hPb : ((intList ((k : ℤ) + 1) ((k : ℤ) + n - 2)).map S).prod = P := by
        have h1 : (((k + 1 : ℕ)) : ℤ) = (k : ℤ) + 1 := by push_cast; ring
        have h2 : (((k + n - 2 : ℕ)) : ℤ) = (k : ℤ) + n - 2 := by
          rw [show k + n - 2 = k + (n - 2) by omega, Nat.cast_add,
            show ((n - 2 : ℕ) : ℤ) = (n : ℤ) - 2 by omega]
          ring
        rw [← h1, ← h2]
        exact (hbridge k hk).symm
      have hjnat : (((k : ℤ) + n - 1).toNat) = k + n - 1 := by omega
      have hlast : ((intList ((k : ℤ) + n - 1) ((k : ℤ) + n - 1)).map S).prod = b := by
        simp [intList, S, b, hjnat]
      rw [hPb, hlast]
    have hGprod : ((intList ((k : ℤ) + 1) ((k : ℤ) + n)).map Gfun).prod =
        z * (z⁻¹ * ⁅c, z⁆ * z) := by
      have hsplit := intList_append (x := (k : ℤ) + 1) (y := (k : ℤ) + 1)
        (z := (k : ℤ) + n) (by omega) (by omega)
      rw [hsplit, show (k : ℤ) + 1 + 1 = (k : ℤ) + 2 by ring,
        List.map_append, List.prod_append]
      have hsingle : ((intList ((k : ℤ) + 1) ((k : ℤ) + 1)).map Gfun).prod = z := by
        simp [intList, Gfun]
      rw [hsingle]
      have hpad := pad (l := (k : ℤ) + 2) (a := (k : ℤ) + 2)
        (b := (k : ℤ) + n - 1) (r := (k : ℤ) + n) (by omega) (by omega)
        (by omega) hcoord
      have hGeq : (intList ((k : ℤ) + 2) ((k : ℤ) + n)).map Gfun =
          (intList ((k : ℤ) + 2) ((k : ℤ) + n)).map
            (fun j => if (k : ℤ) + 2 ≤ j ∧ j ≤ (k : ℤ) + n - 1 then hcoord j else 1) := by
        apply List.map_congr_left
        intro j hj
        have hj' := mem_intList_iff.1 hj
        by_cases hcond : (k : ℤ) + 2 ≤ j ∧ j ≤ (k : ℤ) + n - 1
        · have hne : j ≠ (k : ℤ) + 1 := by omega
          simp [Gfun, hcond, hne]
        · have hjn : j = (k : ℤ) + n := by omega
          have hne : j ≠ (k : ℤ) + 1 := by omega
          have hn1 : n ≠ 1 := by omega
          simp [Gfun, hcond, hne, hjn, hn1]
      rw [hGeq, hpad, hcoord_prod]
    have hE : P * b = a⁻¹ * b * a := by
      dsimp only [P, b, a]
      rw [← hC]
      simp only [commutatorElement_def]
      group
    have hm : m = ν * a * c := by
      change T.nu (k : ℤ) a * a * T.nu' (k : ℤ) a =
        T.nu (k : ℤ) a * a * c
      rw [← hrec]
    have hF : c * m⁻¹ * b * m * c⁻¹ = a⁻¹ * b * a := by
      rw [hm]
      have h1 : c * (ν * a * c)⁻¹ * b * (ν * a * c) * c⁻¹ =
          a⁻¹ * ν⁻¹ * b * ν * a := by group
      rw [h1]
      have h2 : ν⁻¹ * b = b * ν⁻¹ := by
        have h3 : b * ν⁻¹ = ν⁻¹ * b := by
          calc b * ν⁻¹ = ν⁻¹ * (ν * b) * ν⁻¹ := by group
            _ = ν⁻¹ * (b * ν) * ν⁻¹ := by rw [hcommνb]
            _ = ν⁻¹ * b := by group
        exact h3.symm
      calc
        a⁻¹ * ν⁻¹ * b * ν * a = a⁻¹ * (ν⁻¹ * b) * ν * a := by group
        _ = a⁻¹ * (b * ν⁻¹) * ν * a := by rw [h2]
        _ = a⁻¹ * b * a := by group
    have hcz_eq : c * z * c⁻¹ = ⁅c, z⁆ * z := by
      simp only [commutatorElement_def]
      group
    have hRHS : z * (z⁻¹ * ⁅c, z⁆ * z) = a⁻¹ * b * a := by
      rw [show z * (z⁻¹ * ⁅c, z⁆ * z) = ⁅c, z⁆ * z by group]
      rw [← hcz_eq]
      have hF' : c * (m⁻¹ * b * m) * c⁻¹ = a⁻¹ * b * a := by
        calc c * (m⁻¹ * b * m) * c⁻¹ = c * m⁻¹ * b * m * c⁻¹ := by group
          _ = a⁻¹ * b * a := hF
      simpa [z] using hF'
    have hprod_eq : ((intList ((k : ℤ) + 1) ((k : ℤ) + n)).map F).prod =
        ((intList ((k : ℤ) + 1) ((k : ℤ) + n)).map Gfun).prod := by
      rw [hFprod, hGprod, hE, hRHS]
    have huniq := T.unique k F Gfun hFmem hGmem hprod_eq
    have hk1mem : (k : ℤ) + 1 ∈ intList ((k : ℤ) + 1) ((k : ℤ) + n) :=
      mem_intList_iff.2 ⟨by omega, by omega⟩
    have heq := huniq ((k : ℤ) + 1) hk1mem
    have hjnat : (((k : ℤ) + 1).toNat) = k + 1 := by omega
    have hFval : F ((k : ℤ) + 1) = s (k + 1) := by
      have hcond : (k : ℤ) + 1 ≤ (k : ℤ) + 1 ∧
          (k : ℤ) + 1 ≤ (k : ℤ) + n - 1 := by omega
      simp [F, hcond, S, hjnat]
    have hGval : Gfun ((k : ℤ) + 1) = z := by simp [Gfun]
    have hzs : s (k + 1) = z := by
      rw [hFval, hGval] at heq
      exact heq
    change b = m * s (k + 1) * m⁻¹
    rw [hzs]
    dsimp only [z]
    group

  have hmain : ∀ k : ℕ, 1 ≤ k →
      (s k ∈ T.U (k : ℤ) ∧ s k ≠ 1) ∧
      (⁅(s k)⁻¹, s (k + n - 1)⁆ = ((List.range' (k + 1) (n - 2)).map s).prod) ∧
      (s (k + n - 1) = T.mu (k : ℤ) (s k) * s (k + 1) * (T.mu (k : ℤ) (s k))⁻¹) := by
    intro k hk
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      have hmem_k : s k ∈ T.U (k : ℤ) := by
        by_cases hkn : k ≤ n
        · exact hbase_mem k hk hkn
        · have hkgt : n < k := by omega
          have hk' : 1 ≤ k - n := by omega
          have hkm : k - n < k := by omega
          have hmem' := (ih (k - n) hkm hk').1.1
          have hne' := (ih (k - n) hkm hk').1.2
          have hrec' := hs_rec (k - n) hk'
          have hmemnu : s (k - n + n) ∈ T.U (((k - n : ℕ) : ℤ) + n) := by
            rw [hrec']
            exact (T.isMu_nu hmem' hne').2.1
          have hkn' : k - n + n = k := by omega
          simpa [hkn', show (((k - n : ℕ) : ℤ) + n) = (k : ℤ) by omega] using hmemnu
      have hne_k : s k ≠ 1 := by
        by_cases hk1 : k = 1
        · rw [hk1]; exact hs1_ne
        · have hk2 : 2 ≤ k := by omega
          have hprev := (ih (k - 1) (by omega) (by omega)).2.2
          have hidx : (k - 1) + n - 1 = k + n - 2 := by omega
          have hbne : s (k + n - 2) ≠ 1 := by
            by_cases hk2' : k = 2
            · rw [hk2', show 2 + n - 2 = n by omega]; exact hsn_ne
            · have hk3 : 3 ≤ k := by omega
              have hk'' : 1 ≤ k - 2 := by omega
              have hklt : k - 2 < k := by omega
              have hmem2 := (ih (k - 2) hklt hk'').1.1
              have hne2 := (ih (k - 2) hklt hk'').1.2
              have hrec2 := hs_rec (k - 2) hk''
              have hidx2 : k - 2 + n = k + n - 2 := by omega
              rw [hidx2] at hrec2
              rw [hrec2]
              exact T.nu'_ne_one hn hmem2 hne2
          have hcast : ((k - 1 : ℕ) : ℤ) = (k : ℤ) - 1 := by
            rw [Nat.cast_sub (by omega : 1 ≤ k)]
            norm_num
          have hprev' : s (k + n - 2) =
              T.mu ((k : ℤ) - 1) (s (k - 1)) * s k *
                (T.mu ((k : ℤ) - 1) (s (k - 1)))⁻¹ := by
            simpa [hcast, show k - 1 + 1 = k by omega,
              show k - 1 + n - 1 = k + n - 2 by omega] using hprev
          intro hone
          rw [hone] at hprev'
          simp at hprev'
          exact hbne hprev'
      have hmem_range_nat : ∀ m : ℕ, k + 1 ≤ m → m ≤ k + n - 1 →
          s m ∈ T.U (m : ℤ) := by
        intro m hm1 hm2
        by_cases hmn : m ≤ n
        · exact hbase_mem m (by omega) hmn
        · have hmg : n < m := by omega
          have hm'1 : 1 ≤ m - n := by omega
          have hm'lt : m - n < k := by omega
          have hmem' := (ih (m - n) hm'lt hm'1).1.1
          have hne' := (ih (m - n) hm'lt hm'1).1.2
          have hrec' := hs_rec (m - n) hm'1
          have hidx : m - n + n = m := by omega
          rw [hidx] at hrec'
          rw [hrec']
          have hmemnu := (T.isMu_nu hmem' hne').2.1
          have hcast2 : (((m - n : ℕ) : ℤ) + n) = (m : ℤ) := by
            rw [← Nat.cast_add, hidx]
          simpa [hcast2] using hmemnu
      have hmem_range : ∀ j : ℤ, (k : ℤ) + 1 ≤ j → j ≤ (k : ℤ) + n - 1 →
          S j ∈ T.U j := by
        intro j hj1 hj2
        have h0 : 0 ≤ j := by omega
        have hcast : ((j.toNat : ℕ) : ℤ) = j := Int.toNat_of_nonneg h0
        have hj1' : k + 1 ≤ j.toNat := by
          have : (((k + 1 : ℕ)) : ℤ) ≤ ((j.toNat : ℕ) : ℤ) := by
            rw [hcast]
            exact hj1
          exact_mod_cast this
        have hkncast : ((k + n - 1 : ℕ) : ℤ) = (k : ℤ) + n - 1 := by
          rw [show k + n - 1 = k + (n - 1) by omega, Nat.cast_add, hncast]
          ring
        have hj2' : j.toNat ≤ k + n - 1 := by
          have : ((j.toNat : ℕ) : ℤ) ≤ ((k + n - 1 : ℕ) : ℤ) := by
            rw [hcast, hkncast]
            exact hj2
          exact_mod_cast this
        have h := hmem_range_nat j.toNat hj1' hj2'
        simpa [S, hcast] using h
      have hC_k : ⁅(s k)⁻¹, s (k + n - 1)⁆ =
          ((List.range' (k + 1) (n - 2)).map s).prod := by
        by_cases hk1 : k = 1
        · rw [hk1]
          exact hC1
        · have hk2 : 2 ≤ k := by omega
          have hprev := ih (k - 1) (by omega) (by omega)
          have hmem_prev := hprev.1.1
          have hne_prev := hprev.1.2
          have hCprev := hprev.2.1
          have hRprev := hprev.2.2
          have hb_mem : s ((k - 1) + n - 1) ∈
              T.U (((k - 1 : ℕ) : ℤ) + n - 1) := by
            have hm1 : k + 1 ≤ (k - 1) + n - 1 := by omega
            have hm2 : (k - 1) + n - 1 ≤ k + n - 1 := by omega
            have h := hmem_range_nat ((k - 1) + n - 1) hm1 hm2
            have hcast : ((((k - 1) + n - 1 : ℕ)) : ℤ) =
                ((k - 1 : ℕ) : ℤ) + n - 1 := by
              rw [show (k - 1) + n - 1 = (k - 1) + (n - 1) by omega,
                Nat.cast_add, hncast]
              ring
            simpa [hcast] using h
          have hrec_prev := hs_rec (k - 1) (by omega)
          have hCn := Cnext (k - 1) (by omega) hmem_prev hne_prev hb_mem
            hrec_prev hCprev hRprev
          simpa [show k - 1 + 1 = k by omega,
            show k - 1 + 2 = k + 1 by omega,
            show k - 1 + n = k + n - 1 by omega] using hCn
      have hR_k : s (k + n - 1) =
          T.mu (k : ℤ) (s k) * s (k + 1) * (T.mu (k : ℤ) (s k))⁻¹ :=
        R_of_C k hk hmem_k hne_k (hs_rec k hk) hmem_range hC_k
      exact ⟨⟨hmem_k, hne_k⟩, hC_k, hR_k⟩
  refine ⟨s, hs_one, hs_n, ?_, hs_rec, ?_, ?_⟩
  · intro k hk
    exact (hmain k hk).1
  · intro k hk
    exact (hmain k hk).2.1
  · intro k hk
    exact (hmain k hk).2.2


theorem braid (hn : 3 ≤ n) {u v : G} (hu : u ∈ T.U 1) (hu1 : u ≠ 1) (hv : v ∈ T.U n)
    (hv1 : v ≠ 1) :
    altWord (T.mu 1 u) (T.mu n v) n = altWord (T.mu n v) (T.mu 1 u) n := by
  classical
  obtain ⟨s, hs1, hsn, hmem, hrec, hC, hR⟩ :=
    lemma29 (T := T) hn ((T.U 1).inv_mem hu) (inv_ne_one.mpr hu1) hv hv1
  have hs1' : s 1 = u := by rw [hs1]; simp
  have hncast : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    norm_num
  let m : ℕ → G := fun k => T.mu (k : ℤ) (s k)
  let g : ℕ → G := fun r => altWord (m 1) (m n) r
  have hmper : ∀ k : ℕ, 1 ≤ k → m (k + n) = m k := by
    intro k hk
    have hkrec := hrec k hk
    have h := (T.mu_nu' hn (hmem k hk).1 (hmem k hk).2).1
    have hcast : ((k + n : ℕ) : ℤ) = (k : ℤ) + n := by push_cast; ring
    have hm : T.mu ((k + n : ℕ) : ℤ) (s (k + n)) = T.mu (k : ℤ) (s k) := by
      rw [hkrec]
      simpa [hcast] using h
    simpa [m] using hm
  have hm2 : m 2 = (m 1)⁻¹ * m n * m 1 := by
    have hm1mem : s 1 ∈ T.U (1 : ℤ) := (hmem 1 (by omega)).1
    have hm1ne : s 1 ≠ 1 := (hmem 1 (by omega)).2
    have hmov : T.Moves (m 1) (fun j => -1 * j + ((n : ℤ) + 2)) := by
      have h := T.moves_mu hm1mem hm1ne
      simpa [m, neg_one_mul, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h
    have h := (T.mu_conj hn (g := m 1) (ε := -1) (c := (n : ℤ) + 2)
      (Or.inr rfl) hmov (hmem 2 (by omega)).1 (hmem 2 (by omega)).2).1
    have hR1 := hR 1 (by omega)
    have hinput : m 1 * s 2 * (m 1)⁻¹ = s n := by
      simpa [m, show 1 + n - 1 = n by omega] using hR1.symm
    have h' := h
    rw [hinput] at h'
    have hmn : m n = m 1 * m 2 * (m 1)⁻¹ := by
      simpa [m, show -1 * (2 : ℤ) + ((n : ℤ) + 2) = (n : ℤ) by ring] using h'
    rw [hmn]
    group
  have hmrec : ∀ k : ℕ, 2 ≤ k → m (k + 1) = (m k)⁻¹ * m (k - 1) * m k := by
    intro k hk2
    have hk1 : 1 ≤ k := by omega
    have hk' : 1 ≤ k - 1 := by omega
    have hmov : T.Moves (m k) (fun j => -1 * j + (2 * (k : ℤ) + n)) := by
      have h := T.moves_mu (hmem k hk1).1 (hmem k hk1).2
      simpa [m, neg_one_mul, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h
    have h := (T.mu_conj hn (g := m k) (ε := -1) (c := 2 * (k : ℤ) + n)
      (Or.inr rfl) hmov (hmem (k + 1) (by omega)).1 (hmem (k + 1) (by omega)).2).1
    have hRk := hR k hk1
    have hinput : m k * s (k + 1) * (m k)⁻¹ = s (k + n - 1) := by
      simpa [m] using hRk.symm
    have h' := h
    rw [hinput] at h'
    have hkncast : (((k + n - 1 : ℕ)) : ℤ) = (k : ℤ) + n - 1 := by
      rw [show k + n - 1 = k + (n - 1) by omega, Nat.cast_add, hncast]
      ring
    have hidx : -1 + -(k : ℤ) + (2 * (k : ℤ) + n) = (k : ℤ) + n - 1 := by ring
    have h''' : m (k + n - 1) = m k * m (k + 1) * (m k)⁻¹ := by
      simpa [m, hkncast, hidx] using h'
    have hper := hmper (k - 1) hk'
    have hL : m (k + n - 1) = m (k - 1) := by
      simpa [show k - 1 + n = k + n - 1 by omega] using hper
    have hmn : m (k - 1) = m k * m (k + 1) * (m k)⁻¹ := by
      rw [hL] at h'''
      exact h'''
    rw [hmn]
    group
  have g_succ_succ : ∀ r : ℕ, g (r + 2) = g r * m n * m 1 := by
    intro r
    simp [g, altWord, mul_assoc]
  have hformula : ∀ r : ℕ, 1 ≤ r → m r = (g (r - 1))⁻¹ * g r := by
    intro r hr
    induction r using Nat.strong_induction_on with
    | _ r ih =>
      rcases r with _ | _ | s
      · omega
      · simp [g, altWord]
      · rcases s with _ | s
        · simpa [g, altWord, mul_assoc] using hm2
        · have hstep := hmrec (s + 2) (by omega)
          have h1 := ih (s + 2) (by omega) (by omega)
          have h0 := ih (s + 1) (by omega) (by omega)
          have h1' : m (s + 2) = (g (s + 1))⁻¹ * g (s + 2) := by
            simpa using h1
          have h0' : m (s + 1) = (g s)⁻¹ * g (s + 1) := by
            simpa using h0
          calc
            m (s + 3) = (m (s + 2))⁻¹ * m (s + 1) * m (s + 2) := hstep
            _ = ((g (s + 1))⁻¹ * g (s + 2))⁻¹ *
                ((g s)⁻¹ * g (s + 1)) *
                ((g (s + 1))⁻¹ * g (s + 2)) := by rw [h1', h0']
            _ = (g (s + 2))⁻¹ * g (s + 3) := by
              rw [g_succ_succ (s + 1), g_succ_succ s]
              group
  have hformula_n1 := hformula (n + 1) (by omega)
  have hper1 : m (n + 1) = m 1 := by
    simpa [show 1 + n = n + 1 by omega] using hmper 1 (by omega)
  have hgn1 : g (n + 1) = g (n - 1) * m n * m 1 := by
    have := g_succ_succ (n - 1)
    simpa [show n - 1 + 2 = n + 1 by omega] using this
  have hmain : m 1 = (g n)⁻¹ * (g (n - 1) * m n * m 1) := by
    simpa [hper1, hgn1] using hformula_n1
  have hcancel : (1 : G) = (g n)⁻¹ * (g (n - 1) * m n) := by
    have := congrArg (fun y => y * (m 1)⁻¹) hmain
    simpa [mul_assoc] using this
  have hgn : g n = g (n - 1) * m n := by
    have := congrArg (fun y => g n * y) hcancel
    simpa [mul_assoc] using this
  have hbraid : g n = altWord (m n) (m 1) n := by
    have halter : altWord (m n) (m 1) n = altWord (m 1) (m n) (n - 1) * m n := by
      conv_lhs => rw [show n = n - 1 + 1 by omega]
      rw [altWord, show n - 1 + 1 = n by omega]
    rw [halter]
    exact hgn
  have hm1 : m 1 = T.mu 1 u := by simp [m, hs1']
  have hmn : m n = T.mu n v := by simp [m, hsn]
  simpa [g, hm1, hmn] using hbraid


end TitsSystem

end CFSG.GH74.Tits83
