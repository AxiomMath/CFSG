module

public import CFSG.Blueprint.ChevalleyRoots
public import CFSG.GH74.GLS.SP.SpRoots

public section

namespace CFSG.GH74.GLS.Stage4.Hex

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg


@[expose] def rootsG2 : Finset (Fin 2 → ℤ) := rootFinset .G2

theorem isRoot_iff_mem_rootsG2
    {γ : Fin 2 → ℤ} : IsRoot .G2 γ ↔ γ ∈ rootsG2 :=
  mem_rootFinset.symm

@[expose] def hexPos (i : ℤ) : Fin 2 → ℤ :=
  if i = 1 then ![0, 1] else if i = 2 then ![1, 3] else if i = 3 then ![1, 2]
  else if i = 4 then ![2, 3] else if i = 5 then ![1, 1] else if i = 6 then ![1, 0]
  else if i = -1 then ![0, -1] else if i = -2 then ![-1, -3] else if i = -3 then ![-1, -2]
  else if i = -4 then ![-2, -3] else if i = -5 then ![-1, -1] else if i = -6 then ![-1, 0]
  else 0

@[expose] def hexIdx : List ℤ := [1, 2, 3, 4, 5, 6, -1, -2, -3, -4, -5, -6]

theorem mem_hexIdx_iff {i : ℤ} : i ∈ hexIdx ↔ i ≠ 0 ∧ i.natAbs ≤ 6 := by
  simp only [hexIdx, List.mem_cons, List.not_mem_nil, or_false]
  omega

theorem hexPos_neg {i : ℤ} (h : 1 ≤ i) (h6 : i ≤ 6) : hexPos (-i) = -hexPos i := by
  interval_cases i <;> exact CFSG.GH74.GLS.SP.ext_fin_two (by simp [hexPos]) (by simp [hexPos])

theorem mem_rootsG2_iff {γ : Fin 2 → ℤ} : γ ∈ rootsG2 ↔ ∃ i ∈ hexIdx, γ = hexPos i := by
  have h1 : ∀ v ∈ rootsG2, ∃ i ∈ hexIdx, v = hexPos i := by decide +kernel
  have h2 : ∀ i ∈ hexIdx, hexPos i ∈ rootsG2 := by decide +kernel
  exact ⟨h1 γ, fun ⟨i, hi, e⟩ => e ▸ h2 i hi⟩

theorem isRoot_iff
    {γ : Fin 2 → ℤ} : IsRoot .G2 γ ↔ ∃ i ∈ hexIdx, γ = hexPos i := by
  rw [isRoot_iff_mem_rootsG2, mem_rootsG2_iff]

theorem isRoot_hexPos
    {i : ℤ} (h0 : i ≠ 0) (h6 : i.natAbs ≤ 6) : IsRoot .G2 (hexPos i) :=
  isRoot_iff.2 ⟨i, mem_hexIdx_iff.2 ⟨h0, h6⟩, rfl⟩


open CFSG.GH74.GLS.SP in
theorem ht_hexPos (i : ℤ) : ht (hexPos i) = hexPos i 0 + hexPos i 1 := ht_fin_two _

theorem ht_hexPos_pos {i : ℤ} (h1 : 1 ≤ i) (h6 : i ≤ 6) : 0 < ht (hexPos i) := by
  rw [ht_hexPos]
  interval_cases i <;> simp [hexPos]

theorem ht_hexPos_neg {i : ℤ} (h1 : 1 ≤ i) (h6 : i ≤ 6) : ht (hexPos (-i)) < 0 := by
  rw [ht_hexPos]
  interval_cases i <;> simp [hexPos]

theorem ht_hexPos_values : ht (hexPos 1) = 1 ∧ ht (hexPos 2) = 4 ∧ ht (hexPos 3) = 3 ∧
    ht (hexPos 4) = 5 ∧ ht (hexPos 5) = 2 ∧ ht (hexPos 6) = 1 := by
  simp only [ht_hexPos]
  simp [hexPos]

theorem pos_root_cases
    {γ : Fin 2 → ℤ} (h : IsRoot .G2 γ) (hp : 0 < ht γ) :
    ∃ k : ℤ, 1 ≤ k ∧ k ≤ 6 ∧ γ = hexPos k := by
  obtain ⟨i, hi, rfl⟩ := isRoot_iff.1 h
  rw [ht_hexPos] at hp
  simp only [hexIdx, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
    | (exfalso; simp [hexPos] at hp; done)
    | exact ⟨_, by norm_num, by norm_num, rfl⟩

theorem hexPos_inj {a b : ℤ} (ha1 : 1 ≤ a) (ha6 : a ≤ 6) (hb1 : 1 ≤ b) (hb6 : b ≤ 6)
    (h : hexPos a = hexPos b) : a = b := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  interval_cases a <;> interval_cases b <;> simp [hexPos] at h0 h1 ⊢

theorem hexPos_ne_two_smul {k : ℤ} (h1 : 1 ≤ k) (h6 : k ≤ 6) (δ : Fin 2 → ℤ) :
    hexPos k ≠ 2 • δ := by
  intro h
  have h0 := congrFun h 0
  have h1' := congrFun h 1
  interval_cases k <;> simp [hexPos] at h0 h1' <;> omega

theorem linIndep_hexPos {a b : ℤ} (ha1 : 1 ≤ a) (ha6 : a ≤ 6) (hb1 : 1 ≤ b) (hb6 : b ≤ 6)
    (hab : a ≠ b) : LinIndepPair (hexPos a) (hexPos b) := by
  refine CFSG.GH74.GLS.SP.linIndep_of fun x y h0 h1 => ?_
  interval_cases a <;> interval_cases b <;> simp [hexPos] at h0 h1 hab ⊢ <;> omega


theorem cone_between
    {a b : ℤ} (ha : 1 ≤ a) (hab : a < b) (hb : b ≤ 6) {ε : Fin 2 → ℤ}
    (hε : IsRoot .G2 ε) {i j : ℕ} (hi : 0 < i) (hj : 0 < j)
    (he : ε = i • hexPos a + j • hexPos b) : ∃ c : ℤ, a < c ∧ c < b ∧ ε = hexPos c := by
  obtain ⟨e, he', rfl⟩ := isRoot_iff.1 hε
  have h0 := congrFun he 0
  have h1 := congrFun he 1
  simp only [Pi.add_apply, nsmul_eq_mul] at h0 h1
  simp only [hexIdx, List.mem_cons, List.not_mem_nil, or_false] at he'
  have ha5 : a ≤ 5 := by omega
  have hb2 : 2 ≤ b := by omega
  clear hε he
  interval_cases a <;> interval_cases b <;>
    rcases he' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [hexPos] at h0 h1 <;>
    first
    | omega
    | exact ⟨_, by norm_num, by norm_num, rfl⟩


@[expose] def cartanG2 : Matrix (Fin 2) (Fin 2) ℤ := !![2, -1; -3, 2]

theorem cartanG2_eq : cartanG2 = Tag.cartan .G2 := rfl

open CFSG.LieType.RootSystem in
theorem reflection_zero_apply (v : Fin 2 → ℤ) :
    reflection cartanG2 0 v = ![v 1 - v 0, v 1] := by
  refine CFSG.GH74.GLS.SP.ext_fin_two ?_ ?_
  all_goals simp [reflection_apply, cartanG2, Fin.sum_univ_two]
  all_goals ring

open CFSG.LieType.RootSystem in
theorem reflection_one_apply (v : Fin 2 → ℤ) :
    reflection cartanG2 1 v = ![v 0, 3 * v 0 - v 1] := by
  refine CFSG.GH74.GLS.SP.ext_fin_two ?_ ?_
  all_goals simp [reflection_apply, cartanG2, Fin.sum_univ_two]
  all_goals ring

open CFSG.LieType.RootSystem in
theorem reflection_one_hexPos {i : ℤ} (h2 : 2 ≤ i) (h6 : i ≤ 6) :
    reflection cartanG2 1 (hexPos i) = hexPos (8 - i) ∧
      reflection cartanG2 1 (hexPos (-i)) = hexPos (-(8 - i)) := by
  rw [reflection_one_apply, reflection_one_apply]
  interval_cases i <;>
    exact ⟨CFSG.GH74.GLS.SP.ext_fin_two (by simp [hexPos]) (by simp [hexPos]),
      CFSG.GH74.GLS.SP.ext_fin_two (by simp [hexPos]) (by simp [hexPos])⟩

open CFSG.LieType.RootSystem in
theorem reflection_one_hexPos_one :
    reflection cartanG2 1 (hexPos 1) = hexPos (-1) ∧
      reflection cartanG2 1 (hexPos (-1)) = hexPos 1 := by
  rw [reflection_one_apply, reflection_one_apply]
  exact ⟨CFSG.GH74.GLS.SP.ext_fin_two (by simp [hexPos]) (by simp [hexPos]),
    CFSG.GH74.GLS.SP.ext_fin_two (by simp [hexPos]) (by simp [hexPos])⟩

open CFSG.LieType.RootSystem in
theorem reflection_zero_hexPos {i : ℤ} (h1 : 1 ≤ i) (h5 : i ≤ 5) :
    reflection cartanG2 0 (hexPos i) = hexPos (6 - i) ∧
      reflection cartanG2 0 (hexPos (-i)) = hexPos (-(6 - i)) := by
  rw [reflection_zero_apply, reflection_zero_apply]
  interval_cases i <;>
    exact ⟨CFSG.GH74.GLS.SP.ext_fin_two (by simp [hexPos]) (by simp [hexPos]),
      CFSG.GH74.GLS.SP.ext_fin_two (by simp [hexPos]) (by simp [hexPos])⟩

open CFSG.LieType.RootSystem in
theorem reflection_zero_hexPos_six :
    reflection cartanG2 0 (hexPos 6) = hexPos (-6) ∧
      reflection cartanG2 0 (hexPos (-6)) = hexPos 6 := by
  rw [reflection_zero_apply, reflection_zero_apply]
  exact ⟨CFSG.GH74.GLS.SP.ext_fin_two (by simp [hexPos]) (by simp [hexPos]),
    CFSG.GH74.GLS.SP.ext_fin_two (by simp [hexPos]) (by simp [hexPos])⟩


end CFSG.GH74.GLS.Stage4.Hex
