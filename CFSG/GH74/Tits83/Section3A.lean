module

public import CFSG.GH74.Tits83.Octagon
public import CFSG.GH74.Tits83.Section2B
public import CFSG.GH74.Tits83.Section2

public section

namespace CFSG.GH74.Tits83

open CFSG.GH74.BNPair

open scoped commutatorElement Pointwise

universe u

variable {G : Type u} [Group G] {n : ℕ}

namespace TitsSystem

variable (T : TitsSystem G n)

theorem lemma212_i' (hn : 3 ≤ n) {i j : ℤ} (hji : j < i) (hj2 : 2 * j < 2 * i - n) {u x : G}
    (hu : u ∈ T.U i) (hu1 : u ≠ 1) (hx : x ∈ win T.U (i - n + 1) j) (hux : u * x = x * u) :
    x = 1 := by
  by_cases hle : i - n + 1 ≤ j
  · have huS : u ∈ (T.refl (2 * i)).U i := by
      rw [refl_U]
      simpa [show 2 * i - i = i by ring] using hu
    have hxS : x ∈ win (T.refl (2 * i)).U (2 * i - j) (i + n - 1) := by
      rw [win_refl]
      rw [show 2 * i - (i + n - 1) = i - n + 1 by ring,
        show 2 * i - (2 * i - j) = j by ring]
      exact hx
    exact lemma212_i (T := T.refl (2 * i)) hn (i := i) (j := 2 * i - j)
      (by omega) (by omega) (by omega) huS hu1 hxS hux
  · have hbot : win T.U (i - n + 1) j = ⊥ := T.win_eq_bot (by omega)
    rw [hbot] at hx
    simpa using hx

theorem lemma212_iii' (hn : 3 ≤ n) {i j : ℤ} (hji : j < i) (hj : 2 * i - n < 2 * j)
    {u x : G} (hu : u ∈ T.U i) (hu1 : u ≠ 1) (hx : x ∈ T.U j) (hux : u * x = x * u) :
    ∃ y ∈ win T.U (2 * i - n - j + 1) (j - 1),
      x⁻¹ * T.nu i u * x * (T.nu i u)⁻¹ = y * (T.mu i u * x * (T.mu i u)⁻¹) := by
  have huS : u ∈ (T.refl (2 * i)).U i := by
    rw [refl_U]
    simpa [show 2 * i - i = i by ring] using hu
  have hxS : x ∈ (T.refl (2 * i)).U (2 * i - j) := by
    rw [refl_U]
    simpa [show 2 * i - (2 * i - j) = j by ring] using hx
  obtain ⟨y, hy, hyeq⟩ := lemma212_iii (T := T.refl (2 * i)) hn (i := i) (j := 2 * i - j)
    (by omega) (by omega) huS hu1 hxS hux
  refine ⟨y, ?_, ?_⟩
  · rw [win_refl] at hy
    rwa [show 2 * i - (2 * i + n - (2 * i - j) - 1) = 2 * i - n - j + 1 by ring,
      show 2 * i - (2 * i - j + 1) = j - 1 by ring] at hy
  · rw [T.nu_refl hn (2 * i) i u, T.mu_refl hn (2 * i) i u] at hyeq
    simpa [show 2 * i - i = i by ring] using hyeq

theorem lemma29_five (hn : 3 ≤ n) {u v : G} (hu : u ∈ T.U 1) (hu1 : u ≠ 1) (hv : v ∈ T.U n)
    (hv1 : v ≠ 1) : ⁅u, v⁆ ∉ win T.U 3 (n - 1) := by
  intro hx
  obtain ⟨s, hs1, hsn, hmem, hrec, hC, hR⟩ := T.lemma29 hn hu hu1 hv hv1
  have hC1 : ⁅u, v⁆ = ((List.range' 2 (n - 2)).map s).prod := by
    have h := hC 1 (by norm_num)
    rw [hs1, show 1 + n - 1 = n by omega, hsn] at h
    simpa using h
  have hsplit : List.range' 2 (n - 2) = 2 :: List.range' 3 (n - 3) := by
    rw [show n - 2 = (n - 3) + 1 by omega, List.range'_succ]
  set rest : G := ((List.range' 3 (n - 3)).map s).prod with hrestdef
  have hprod : ((List.range' 2 (n - 2)).map s).prod = s 2 * rest := by
    rw [hsplit, List.map_cons, List.prod_cons]
  have hrest : rest ∈ win T.U 3 (n - 1) := by
    refine (win T.U 3 (n - 1)).list_prod_mem ?_
    intro y hy
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hy
    obtain ⟨m, hm, hk'⟩ := List.mem_range'.1 hk
    have hklt : k < n := by
      rw [hk']
      omega
    have hk1 : (3 : ℤ) ≤ k := by omega
    have hk2 : (k : ℤ) ≤ n - 1 := by omega
    exact T.U_le_win hk1 hk2 (hmem k (by omega)).1
  have hs2win : s 2 ∈ win T.U 3 (n - 1) := by
    have hmemwin : s 2 * rest ∈ win T.U 3 (n - 1) := by
      rw [← hprod, ← hC1]
      exact hx
    have h2 : s 2 = (s 2 * rest) * rest⁻¹ := by group
    rw [h2]
    exact (win T.U 3 (n - 1)).mul_mem hmemwin ((win T.U 3 (n - 1)).inv_mem hrest)
  have hbot : T.U 2 ⊓ win T.U 3 (n - 1) = ⊥ := by
    rw [← T.win_self 2,
      win_inf_win (T := T) (a := 2) (b := 2) (c := 3) (d := n - 1) (by omega)]
    rw [show max (2 : ℤ) 3 = 3 by norm_num,
      show min (2 : ℤ) ((n : ℤ) - 1) = 2 by omega]
    exact T.win_eq_bot (by omega)
  have hs2mem : s 2 ∈ T.U 2 ⊓ win T.U 3 (n - 1) :=
    ⟨(hmem 2 (by norm_num)).1, hs2win⟩
  rw [hbot] at hs2mem
  exact (hmem 2 (by norm_num)).2 (by simpa using hs2mem)

end TitsSystem

namespace TitsSystem

variable {G : Type u} [Group G]

theorem le_normClosure2 (A B X : Subgroup G) : X ≤ normClosure2 A B X :=
  le_sInf fun _ hY => hY.1

theorem normClosure2_le {A B X Y : Subgroup G} (hX : X ≤ Y)
    (hA : A ≤ Subgroup.normalizer (Y : Set G)) (hB : B ≤ Subgroup.normalizer (Y : Set G)) :
    normClosure2 A B X ≤ Y :=
  sInf_le ⟨hX, hA, hB⟩

theorem normClosure2_normalized_left (A B X : Subgroup G) :
    A ≤ Subgroup.normalizer (normClosure2 A B X : Set G) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro x
  simp only [normClosure2, Subgroup.mem_sInf]
  constructor
  · intro hx Y hY
    exact (Subgroup.mem_normalizer_iff.mp (hY.2.1 ha) x).mp (hx Y hY)
  · intro hx Y hY
    exact (Subgroup.mem_normalizer_iff.mp (hY.2.1 ha) x).mpr (hx Y hY)

theorem normClosure2_normalized_right (A B X : Subgroup G) :
    B ≤ Subgroup.normalizer (normClosure2 A B X : Set G) := by
  intro b hb
  rw [Subgroup.mem_normalizer_iff]
  intro x
  simp only [normClosure2, Subgroup.mem_sInf]
  constructor
  · intro hx Y hY
    exact (Subgroup.mem_normalizer_iff.mp (hY.2.2 hb) x).mp (hx Y hY)
  · intro hx Y hY
    exact (Subgroup.mem_normalizer_iff.mp (hY.2.2 hb) x).mpr (hx Y hY)

theorem normClosure2_comm (A B X : Subgroup G) : normClosure2 A B X = normClosure2 B A X := by
  simp only [normClosure2]
  congr 1
  ext Y
  exact ⟨fun h => ⟨h.1, h.2.2, h.2.1⟩, fun h => ⟨h.1, h.2.2, h.2.1⟩⟩

end TitsSystem

namespace TitsSystem

variable (T : TitsSystem G 8)

theorem lemma31 {i : ℤ} {u : G} (hu : u ∈ T.U i) (hu1 : u ≠ 1)
    (hZ : u ∈ Subgroup.centralizer (win T.U (i - 4) (i + 4) : Set G)) :
    T.nu i u ∉ Subgroup.centralizer (win T.U (i + 4) (i + 12) : Set G) := by
  intro hnuZ
  obtain ⟨x, hxU, hx1⟩ := Subgroup.exists_mem_ne_one_of_ne_bot (T.ne_bot (i + 3))
  have hxwin : x ∈ win T.U (i - 4) (i + 4) := T.U_le_win (by omega) (by omega) hxU
  have hux : u * x = x * u := ((Subgroup.mem_centralizer_iff.1 hZ) x hxwin).symm
  obtain ⟨y, hy, hw⟩ := T.lemma212_iii (n := 8) (by norm_num) (i := i) (j := i + 3)
    (by omega) (by omega) hu hu1 hxU hux
  have hy' : y ∈ T.U (i + 4) := by
    rw [← T.win_self (i + 4)]
    convert hy using 2 <;> ring
  have hmx : T.mu i u * x * (T.mu i u)⁻¹ ∈ T.U (i + 5) := by
    have h := Moves.conj_mem T (T.moves_mu (n := 8) hu hu1) (j := i + 3) hxU
    convert h using 2 <;> ring
  set w : G := x⁻¹ * T.nu i u * x * (T.nu i u)⁻¹ with hwdef
  have hweq : w = y * (T.mu i u * x * (T.mu i u)⁻¹) := by
    rw [hwdef]
    exact hw
  have hwmem : w ∈ win T.U (i + 3) (i + 5) := by
    rw [hweq]
    exact (win T.U (i + 3) (i + 5)).mul_mem
      (T.U_le_win (by omega) (by omega) hy') (T.U_le_win (by omega) (by omega) hmx)
  have hxnorm : x ∈ Subgroup.normalizer (win T.U (i + 4) (i + 10) : Set G) := by
    have h := (T.le_normalizer_win (a := i + 4) (b := i + 10) (by norm_num)).1
    rw [show i + 4 - 1 = i + 3 by ring] at h
    exact h hxU
  obtain ⟨z, hzU, hz1⟩ := Subgroup.exists_mem_ne_one_of_ne_bot (T.ne_bot (i + 10))
  have hzwin : z ∈ win T.U (i + 4) (i + 10) := T.U_le_win (by omega) (by omega) hzU
  have hxzx : x * z * x⁻¹ ∈ win T.U (i + 4) (i + 10) :=
    (Subgroup.mem_normalizer_iff.mp hxnorm z).mp hzwin
  have hnuZz : T.nu i u * (x * z * x⁻¹) = (x * z * x⁻¹) * T.nu i u :=
    ((Subgroup.mem_centralizer_iff.1 hnuZ) (x * z * x⁻¹)
      (T.win_mono (by omega) (by omega) hxzx)).symm
  have hνz : T.nu i u * z = z * T.nu i u :=
    ((Subgroup.mem_centralizer_iff.1 hnuZ) z
      (T.win_mono (a := i + 4) (b := i + 10) (c := i + 4) (d := i + 12)
        (by omega) (by omega) hzwin)).symm
  have hconjz : w * z * w⁻¹ = z := by
    have h1 : (T.nu i u)⁻¹ * z * T.nu i u = z := by
      calc (T.nu i u)⁻¹ * z * T.nu i u = (T.nu i u)⁻¹ * (z * T.nu i u) := by group
        _ = (T.nu i u)⁻¹ * (T.nu i u * z) := by rw [← hνz]
        _ = z := by group
    calc w * z * w⁻¹ =
        x⁻¹ * (T.nu i u * (x * ((T.nu i u)⁻¹ * z * T.nu i u) * x⁻¹) *
          (T.nu i u)⁻¹) * x := by
          rw [hwdef]; group
      _ = x⁻¹ * (T.nu i u * (x * z * x⁻¹) * (T.nu i u)⁻¹) * x := by rw [h1]
      _ = x⁻¹ * (x * z * x⁻¹) * x := by rw [hnuZz]; group
      _ = z := by group
  have hzw : w * z = z * w := by
    have h := congrArg (fun t => t * w) hconjz
    simpa [mul_assoc] using h
  have hw1 : w = 1 := T.lemma212_i' (n := 8) (by norm_num) (i := i + 10) (j := i + 5)
    (by omega) (by omega) hzU hz1 (by convert hwmem using 2 <;> ring) hzw.symm
  have hmx1 : T.mu i u * x * (T.mu i u)⁻¹ = 1 := by
    have hprod : y * (T.mu i u * x * (T.mu i u)⁻¹) = 1 := by
      rw [← hweq, hw1]
    have hmxinv : T.mu i u * x * (T.mu i u)⁻¹ = y⁻¹ := eq_inv_of_mul_eq_one_right hprod
    have hmem : T.mu i u * x * (T.mu i u)⁻¹ ∈ T.U (i + 4) ⊓ T.U (i + 5) := by
      refine ⟨?_, hmx⟩
      rw [hmxinv]
      exact (T.U (i + 4)).inv_mem hy'
    have hbot : T.U (i + 4) ⊓ T.U (i + 5) = ⊥ := by
      refine T.U_inf_U (by omega) ?_
      rw [show (i + 4) - (i + 5) = -1 by ring, abs_neg, abs_one]
      norm_num
    rw [hbot] at hmem
    simpa using hmem
  have hxone : x = 1 := by
    have h := congrArg (fun t => (T.mu i u)⁻¹ * t * T.mu i u) hmx1
    simpa [mul_assoc] using h
  exact hx1 hxone

theorem nu_not_mem_Uprime {j : ℤ} {u : G} (hu : u ∈ T.Uprime j) (hu1 : u ≠ 1) :
    T.nu j u ∉ T.Uprime (j + 8) := by
  intro h
  have hu' := (T.mem_Uprime_iff (j := j) (x := u)).1 hu
  have hnu := T.lemma31 hu'.1 hu1
    ((T.mem_centralizer_win_iff (a := j - 4) (b := j + 4)).2 hu'.2)
  refine hnu ((T.mem_centralizer_win_iff (a := j + 4) (b := j + 12)).2 ?_)
  intro k hk1 hk2 y hy
  have h' := (T.mem_Uprime_iff (j := j + 8) (x := T.nu j u)).1 h
  exact h'.2 k (by omega) (by omega) y hy

end TitsSystem

namespace TitsSystem

variable (T : TitsSystem G 8)

theorem Uprime_le_of_le_normalizer {i j : ℤ} {Y : Subgroup G}
    (hA : T.U (i - 4) ≤ Subgroup.normalizer (Y : Set G))
    (hB : T.U (i + 4) ≤ Subgroup.normalizer (Y : Set G)) (h : T.Uprime j ≤ Y) :
    T.Uprime (2 * i - j) ≤ Y := by
  obtain ⟨u, hu, hu1⟩ := Subgroup.exists_mem_ne_one_of_ne_bot (T.ne_bot (i - 4))
  have hν : T.nu (i - 4) u ∈ T.U (i + 4) := by
    have h' := T.nu_mem hu hu1
    simpa only [show (i - 4) + ((8 : ℕ) : ℤ) = i + 4 by ring] using h'
  have hν' : T.nu' (i - 4) u ∈ T.U (i + 4) := by
    have h' := T.nu'_mem hu hu1
    simpa only [show (i - 4) + ((8 : ℕ) : ℤ) = i + 4 by ring] using h' 
  have hmN : T.mu (i - 4) u ∈ Subgroup.normalizer (Y : Set G) := by
    have hmu : T.mu (i - 4) u = T.nu (i - 4) u * u * T.nu' (i - 4) u := rfl
    rw [hmu]
    exact (Subgroup.normalizer (Y : Set G)).mul_mem
      ((Subgroup.normalizer (Y : Set G)).mul_mem (hB hν) (hA hu)) (hB hν')
  have hg : T.Moves (T.mu (i - 4) u) (fun k => 2 * i - k) := by
    have h' := T.moves_mu (n := 8) hu hu1
    simpa only [show 2 * (i - 4) + ((8 : ℕ) : ℤ) = 2 * i by ring] using h'
  have hmaps : (T.Uprime j).map (MulAut.conj (T.mu (i - 4) u)).toMonoidHom =
      T.Uprime (2 * i - j) := by
    rw [Moves.map_Uprime_refl T hg j]
  intro x hx
  have hx' : x ∈ (T.Uprime j).map (MulAut.conj (T.mu (i - 4) u)).toMonoidHom := by
    rw [hmaps]
    exact hx
  obtain ⟨y, hy, rfl⟩ := hx'
  exact (Subgroup.mem_normalizer_iff.mp hmN y).mp (h hy)

@[expose] def Ybar (i : ℤ) : Subgroup G :=
  normClosure2 (T.U (i - 4)) (T.U (i + 4)) (T.Uprime (i - 1))

@[expose] def Vmid (i : ℤ) : Subgroup G := T.Ybar i ⊓ T.U i

theorem Uprime_le_Ybar_left (i : ℤ) : T.Uprime (i - 1) ≤ T.Ybar i :=
  le_normClosure2 (T.U (i - 4)) (T.U (i + 4)) (T.Uprime (i - 1))

theorem Uprime_le_Ybar_right (i : ℤ) : T.Uprime (i + 1) ≤ T.Ybar i := by
  have h := T.Uprime_le_of_le_normalizer (i := i) (j := i - 1) (Y := T.Ybar i)
    (by simpa [Ybar] using
      normClosure2_normalized_left (T.U (i - 4)) (T.U (i + 4)) (T.Uprime (i - 1)))
    (by simpa [Ybar] using
      normClosure2_normalized_right (T.U (i - 4)) (T.U (i + 4)) (T.Uprime (i - 1)))
    (T.Uprime_le_Ybar_left i)
  rwa [show 2 * i - (i - 1) = i + 1 by ring] at h

theorem Ybar_symm (i : ℤ) :
    normClosure2 (T.U (i - 4)) (T.U (i + 4)) (T.Uprime (i + 1)) = T.Ybar i := by
  apply le_antisymm
  · refine normClosure2_le (T.Uprime_le_Ybar_right i) ?_ ?_
    · simpa [Ybar] using
        normClosure2_normalized_left (T.U (i - 4)) (T.U (i + 4)) (T.Uprime (i - 1))
    · simpa [Ybar] using
        normClosure2_normalized_right (T.U (i - 4)) (T.U (i + 4)) (T.Uprime (i - 1))
  · refine normClosure2_le ?_ (normClosure2_normalized_left _ _ _)
      (normClosure2_normalized_right _ _ _)
    have h := T.Uprime_le_of_le_normalizer (i := i) (j := i + 1)
      (Y := normClosure2 (T.U (i - 4)) (T.U (i + 4)) (T.Uprime (i + 1)))
      (normClosure2_normalized_left _ _ _) (normClosure2_normalized_right _ _ _)
      (le_normClosure2 _ _ _)
    rwa [show 2 * i - (i + 1) = i - 1 by ring] at h

theorem Ybar_refl (c i : ℤ) : (T.refl c).Ybar i = T.Ybar (c - i) := by
  simp only [Ybar, refl_U, Uprime_refl]
  rw [show c - (i - 1) = c - i + 1 by ring, show c - (i + 4) = c - i - 4 by ring,
    show c - (i - 4) = c - i + 4 by ring]
  rw [normClosure2_comm, Ybar_symm]
  rfl

theorem Vmid_refl (c i : ℤ) : (T.refl c).Vmid i = T.Vmid (c - i) := by
  simp only [Vmid, Ybar_refl, refl_U]

theorem Vmid_le (i : ℤ) : T.Vmid i ≤ T.U i :=
  inf_le_right

theorem Ybar_subset (i : ℤ) :
    (T.Ybar i : Set G) ⊆
      (T.Uprime (i - 1) : Set G) * (T.U i : Set G) * (T.Uprime (i + 1) : Set G) := by
  have hVi : T.Uprime (i - 1) ≤ (T.shift (i - 4)).U 3 := by
    rw [shift_U, show (3 : ℤ) + (i - 4) = i - 1 by ring]
    exact T.Uprime_le (i - 1)
  have hVni : T.Uprime (i + 1) ≤ (T.shift (i - 4)).U (8 - 3) := by
    rw [shift_U, show (8 : ℤ) - 3 + (i - 4) = i + 1 by ring]
    exact T.Uprime_le (i + 1)
  have hconj : ∀ u ∈ (T.shift (i - 4)).U 0, u ≠ 1 →
      (T.Uprime (i - 1)).map (MulAut.conj ((T.shift (i - 4)).mu 0 u)).toMonoidHom =
        T.Uprime (i + 1) := by
    intro u hu hu1
    have hu' : u ∈ T.U (i - 4) := by
      rw [shift_U] at hu
      simpa using hu
    rw [T.mu_shift (by norm_num) (i - 4) 0 u,
      show (0 : ℤ) + (i - 4) = i - 4 by ring]
    have hg : T.Moves (T.mu (i - 4) u) (fun k => 2 * i - k) := by
      have h' := T.moves_mu (n := 8) hu' hu1
      simpa only [show 2 * (i - 4) + ((8 : ℕ) : ℤ) = 2 * i by ring] using h'
    rw [Moves.map_Uprime_refl T hg]
    rw [show 2 * i - (i - 1) = i + 1 by ring]
  have hX : (T.Uprime (i - 1) : Set G) ⊆ (T.Uprime (i - 1) : Set G) *
      (win (T.shift (i - 4)).U (3 + 1) (8 - 3 - 1) : Set G) * (T.Uprime (i + 1) : Set G) := by
    intro x hx
    have h1 : x * 1 ∈ (T.Uprime (i - 1) : Set G) *
        (win (T.shift (i - 4)).U (3 + 1) (8 - 3 - 1) : Set G) :=
      Set.mul_mem_mul hx (Subgroup.one_mem _)
    have h2 : x * 1 * 1 ∈ ((T.Uprime (i - 1) : Set G) *
        (win (T.shift (i - 4)).U (3 + 1) (8 - 3 - 1) : Set G)) *
        (T.Uprime (i + 1) : Set G) :=
      Set.mul_mem_mul h1 (Subgroup.one_mem _)
    simpa using h2
  have hX0 : (T.shift (i - 4)).U 0 ≤ Subgroup.normalizer (T.Uprime (i - 1) : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro y hy x hx
    have hy' : y ∈ T.U (i - 4) := by
      rw [shift_U] at hy
      simpa using hy
    have hywin : y ∈ win T.U (i - 4) (i + 3) := T.U_le_win (by omega) (by omega) hy'
    have hxy : x * y = y * x :=
      T.Uprime_comm_win (j := i - 1) (by omega) (by omega) hx hywin
    have hconj : y * x * y⁻¹ = x := by
      calc y * x * y⁻¹ = x * y * y⁻¹ := by rw [hxy]
        _ = x := by group
    rw [hconj]
    exact hx
  have h := lemma214 (T := T.shift (i - 4)) (n := 8) (by norm_num) (i := 3) (by norm_num)
    (by norm_num) (T.Uprime (i - 1)) (T.Uprime (i + 1)) (T.Uprime (i - 1))
    hVi hVni hconj hX hX0
  have hL : normClosure2 ((T.shift (i - 4)).U 0) ((T.shift (i - 4)).U ((8 : ℕ) : ℤ))
      (T.Uprime (i - 1)) = T.Ybar i := by
    simp only [Ybar, shift_U]
    rw [show (0 : ℤ) + (i - 4) = i - 4 by ring,
      show ((8 : ℕ) : ℤ) + (i - 4) = i + 4 by ring]
  have hR : (win (T.shift (i - 4)).U (3 + 1) (((8 : ℕ) : ℤ) - 3 - 1) : Set G) =
      (T.U i : Set G) := by
    rw [win_shift]
    rw [show (3 : ℤ) + 1 + (i - 4) = i by ring,
      show ((8 : ℕ) : ℤ) - 3 - 1 + (i - 4) = i by ring]
    exact congrArg (fun H : Subgroup G => (H : Set G)) (T.win_self i)
  rw [hL, hR] at h
  exact h

theorem Ybar_eq (i : ℤ) :
    (T.Ybar i : Set G) =
      (T.Uprime (i - 1) : Set G) * (T.Vmid i : Set G) * (T.Uprime (i + 1) : Set G) := by
  apply Set.Subset.antisymm
  · intro x hx
    have hx' := T.Ybar_subset i hx
    rw [Set.mem_mul] at hx'
    obtain ⟨ab, hab, c, hc, rfl⟩ := hx'
    obtain ⟨a, ha, b, hb, rfl⟩ := hab
    have hbY : b ∈ T.Ybar i := by
      have h1 : b = a⁻¹ * (a * b * c) * c⁻¹ := by group
      rw [h1]
      exact (T.Ybar i).mul_mem ((T.Ybar i).mul_mem
        ((T.Ybar i).inv_mem (T.Uprime_le_Ybar_left i ha)) hx)
        ((T.Ybar i).inv_mem (T.Uprime_le_Ybar_right i hc))
    have h1 : a * b ∈ (T.Uprime (i - 1) : Set G) * (T.Vmid i : Set G) :=
      Set.mul_mem_mul ha ⟨hbY, hb⟩
    have h2 : a * b * c ∈ ((T.Uprime (i - 1) : Set G) * (T.Vmid i : Set G)) *
        (T.Uprime (i + 1) : Set G) :=
      Set.mul_mem_mul h1 hc
    simpa using h2
  · intro x hx
    have hx' := hx
    rw [Set.mem_mul] at hx'
    obtain ⟨ab, hab, c, hc, rfl⟩ := hx'
    obtain ⟨a, ha, b, hb, rfl⟩ := hab
    exact (T.Ybar i).mul_mem ((T.Ybar i).mul_mem (T.Uprime_le_Ybar_left i ha) hb.1)
      (T.Uprime_le_Ybar_right i hc)

theorem mem_Uprime_of_mem_Ybar {i : ℤ} {y : G} (hy : y ∈ T.Ybar i)
    (hw : y ∈ win T.U (i + 1) (i + 3)) : y ∈ T.Uprime (i + 1) := by
  have hy' := T.Ybar_subset i hy
  rw [Set.mem_mul] at hy'
  obtain ⟨ab, hab, c, hc, rfl⟩ := hy'
  obtain ⟨a, ha, b, hb, rfl⟩ := hab
  have hcwin : c ∈ win T.U (i + 1) (i + 3) :=
    T.U_le_win (by omega) (by omega) (T.Uprime_le (i + 1) hc)
  have habwin : a * b ∈ win T.U (i - 1) i :=
    (win T.U (i - 1) i).mul_mem
      (T.U_le_win (by omega) (by omega) (T.Uprime_le (i - 1) ha))
      (T.U_le_win (by omega) (by omega) hb)
  have heq : (a * b) * c = 1 * (a * b * c) := by group
  have huniq := T.eq_of_mul_eq_mul (a := i - 1) (c := i) (b := i + 3)
    (by omega) (by omega) (by omega) habwin (Subgroup.one_mem _) hcwin hw heq
  rw [← huniq.2]
  exact hc

end TitsSystem

end CFSG.GH74.Tits83
