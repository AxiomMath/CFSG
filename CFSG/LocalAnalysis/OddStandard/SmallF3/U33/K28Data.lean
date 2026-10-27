module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.K28Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.TabAlg

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.K28

open CFSG.GH74.KGroups CFSG.GH74.KGroups.U33 CFSG.Sporadic.Schreier CFSG.Certificates

@[expose] def zConjWords : List (List (Fin 4)) :=
  [[1, 2, 3, 2, 1], [2, 3, 2], [3, 2, 1], [1, 0, 3, 2], [3], [1, 0, 1, 0], [0, 3, 0, 1, 2, 1],
   [2, 1, 0], [0, 1, 2, 1], [3, 2, 1, 0], [3, 0], [0, 3, 2, 3, 0], [2, 3, 0, 3, 0, 1, 0],
   [0, 1, 2, 3, 0], [1, 0, 3, 0, 1, 0], [2, 1, 2, 1], [1, 2, 3, 2], [0, 1, 2, 1, 0], [0, 1, 0],
   [2, 1, 2, 1, 2, 3, 0], [3, 0, 3, 0, 1, 0], [1, 0], [0, 1, 2, 1, 2, 1, 2, 1], [],
   [2, 1, 2, 3, 0], [3, 2, 1, 2, 1], [1, 2, 1], [2, 3, 2, 1, 0], [2, 3, 0], [3, 2, 3, 2, 1, 0],
   [3, 2, 3, 0], [1, 2, 3, 0], [1, 2, 3, 2, 1, 0], [3, 2], [3, 0, 3, 2], [0, 3, 0, 1, 0],
   [2, 3, 2, 1], [1, 2, 1, 2, 3, 0], [0, 1, 0, 3, 0, 1, 0], [0, 3, 2, 1], [2, 1, 2, 1, 0], [0],
   [2, 3, 2, 3, 0], [1, 2, 1, 2, 1, 2, 1], [0, 3, 2], [3, 0, 1, 2, 1], [1, 2], [1, 2, 1, 2, 1],
   [0, 3, 0, 3, 2], [0, 3, 0, 3, 2, 1], [1, 2, 1, 0], [2, 1], [3, 0, 3, 2, 1], [1],
   [1, 0, 3, 2, 3, 0], [2, 1, 2, 1, 2, 1, 2, 1], [2], [0, 1, 0, 1, 0], [2, 1, 2, 1, 2, 1],
   [3, 0, 1, 0], [3, 0, 3, 2, 3, 0], [3, 2, 3, 2], [3, 2, 1, 2, 3, 0]]

@[expose] def tauConjWords : List (List (Fin 4)) :=
  [[0, 1, 2, 3, 2, 3, 2, 1, 0], [3, 2, 1, 0, 1, 0, 3], [2, 1, 2, 1, 0, 3],
   [0, 3, 2, 1, 2, 3, 0], [1, 0, 1, 2, 3], [3, 2, 3, 2, 3, 2, 1, 0], [0, 1, 0, 1, 2],
   [1, 0, 3, 2, 1, 2, 1], [2, 1, 2, 1, 2, 1, 0, 1], [3, 2, 3, 2, 1, 0], [1, 2, 3, 0, 1, 2],
   [2, 3, 2, 3, 0], [1, 2, 1, 2], [0, 3, 0, 3], [], [2, 1, 2, 3], [3, 0, 3, 0, 3, 2, 3, 0],
   [3, 2, 1, 0, 3, 0, 3, 0, 1], [1, 2], [1, 0, 3, 0, 3, 0], [0, 3], [3, 0, 1, 2],
   [3, 2, 1, 2, 3, 0], [3, 0, 3, 2, 3, 0], [2, 1, 2, 3, 0], [2, 1, 0, 3, 0, 1],
   [1, 0, 3, 2, 3, 0], [1, 2, 3, 2, 3, 2, 1, 0], [2, 1, 0, 1, 0, 3], [3, 0, 1, 0, 1, 0, 3, 0],
   [0, 1, 0, 1, 0, 3, 0, 3], [2, 3, 2, 1, 2, 1], [3, 2, 3, 0, 3], [3, 2, 1, 0, 3],
   [1, 0, 1, 2, 3, 0], [1, 0, 1, 0, 3, 0, 1], [3, 0, 1, 0, 1], [2, 1, 2], [3, 2, 1, 0],
   [2, 1, 0, 1, 0, 3, 0], [1, 2, 3, 2, 3, 0, 1], [1, 2, 1, 2, 3, 2, 1, 0, 1],
   [2, 1, 0, 1, 0, 1, 2], [2, 3, 0, 1, 2, 1], [0, 3, 2, 3, 2, 1, 0], [0, 3, 0, 1, 2],
   [1, 0, 3, 0, 1], [0, 3, 0, 1, 0, 1, 0, 3, 0], [1, 0, 1, 2, 1], [1, 2, 3, 0, 3],
   [3, 0, 1, 0, 3, 0, 1], [2, 1, 2, 1, 0, 1], [0, 3, 0, 3, 2, 3, 0], [1, 0, 1, 0, 3],
   [1, 2, 3, 0, 3, 0, 1, 2], [1, 2, 3, 0], [3, 0, 1, 2, 1, 2, 3, 0, 1], [3, 2, 3, 2, 3, 0],
   [2, 3, 0, 1, 0, 3], [1, 2, 3, 2, 1], [3, 2, 3, 0, 3, 0, 3], [3, 0], [0, 1, 2, 3, 2, 3, 0],
   [3, 0, 3, 0, 1, 2], [3, 0, 1, 2, 1, 2, 3], [3, 2, 1], [2, 1, 0, 3], [1, 0, 3, 0, 3, 2, 3, 0],
   [3, 0, 1, 2, 3], [3, 2, 3, 0, 1], [3, 2, 3], [1, 2, 3, 2, 1, 0, 1], [1, 0, 1, 0, 3, 0, 3],
   [0, 1, 2, 1, 0], [3, 0, 3, 0, 3, 0, 3, 0], [1, 0, 3, 0], [0, 1, 0, 1, 0, 3, 0, 1],
   [1, 0, 3, 0, 3], [0, 1, 2, 3, 2, 3, 0, 1], [2, 1, 2, 1], [2, 3, 0, 1], [0, 3, 0, 3, 0, 1, 2],
   [3, 0, 3], [2, 1, 2, 1, 2, 3, 0, 1], [0], [3, 0, 1, 0, 3, 0, 3, 0, 1], [1, 2, 3, 0, 3, 0, 3],
   [2, 3, 2, 1, 0, 1], [3, 0, 3, 0, 1, 0, 1], [1, 0, 3], [3, 2, 1, 2, 3], [2, 3, 2, 1],
   [3, 2, 1, 2, 1], [1, 0, 3, 0, 3, 0, 3, 0], [1, 0, 1, 0, 1, 2], [1, 0, 3, 0, 3, 0, 1], [1, 0],
   [3, 2, 3, 0, 3, 0, 3, 0], [3, 2, 1, 2, 3, 2, 3, 0], [3, 0, 1, 2, 3, 2, 3, 2, 1, 0],
   [2, 1, 2, 3, 0, 1, 0, 1], [1, 0, 1], [1, 2, 3, 0, 1], [2, 3, 2, 1, 0, 3],
   [0, 1, 2, 1, 2, 1, 0, 3], [1, 0, 3, 0, 1, 2], [0, 3, 0, 3, 0, 3, 0, 3, 0], [3, 2, 1, 2],
   [0, 1, 2], [1, 2, 1, 0, 1, 2, 1], [1, 0, 1, 2, 1, 0, 1], [0, 1, 0, 1, 0, 3, 0],
   [2, 3, 2, 1, 0], [2, 3, 0, 1, 0, 1], [1, 2, 3, 0, 1, 0, 3, 0, 1], [0, 3, 0, 1, 2, 1],
   [2, 1, 2, 3, 0, 3], [1, 2, 1, 0, 1, 0, 3], [0, 3, 2, 3, 0], [0, 1, 2, 1, 0, 1],
   [2, 3, 0, 1, 0, 3, 0, 1], [2, 1, 0, 1, 2, 1], [1, 2, 1, 2, 3, 0], [2, 3, 2, 3, 2, 1, 0],
   [0, 3, 2, 3, 0, 3], [1, 0, 1, 2], [1, 2, 3, 2, 1, 0], [2, 1, 2, 3, 2, 1], [0, 3, 0, 1, 0, 3],
   [3, 2, 3, 0, 1, 0, 3, 0, 1], [1, 0, 1, 0, 1, 0, 3, 0], [1, 2, 3, 0, 1, 0, 1],
   [1, 0, 3, 2, 1, 0], [2, 3, 0, 3, 0, 1, 2], [3, 2], [2, 1, 2, 3, 2, 1, 0, 1], [0, 1, 2, 1],
   [1, 0, 3, 0, 1, 0, 1], [3, 0, 1, 0, 1, 2], [3, 0, 1, 0, 3, 0], [0, 1, 0, 1, 2, 3],
   [2, 1, 0, 3, 0, 3], [2, 3, 0, 3, 0, 1, 0, 3, 0], [2, 3, 0], [0, 1, 2, 3], [3, 2, 1, 0, 1],
   [2, 3, 2, 3, 0, 1], [3, 0, 1, 2, 3, 0], [2, 3, 0, 3], [2, 1, 2, 3, 0, 3, 0, 3, 0],
   [0, 3, 2, 1, 2, 1], [3, 2, 3, 0, 3, 0, 1, 2], [3, 0, 1, 0, 1, 2, 1], [0, 1, 0, 3],
   [3, 0, 1, 2, 1, 0], [3, 2, 1, 0, 1, 0, 1, 2], [3, 2, 1, 0, 1, 0, 3, 0], [1, 2, 1],
   [1, 2, 3, 0, 1, 0, 3], [1, 2, 1, 2, 1, 0, 3], [2, 1, 0], [2, 1, 2, 3, 2, 3, 0],
   [2, 1, 2, 1, 0], [0, 1, 0, 3, 0, 1], [1, 0, 3, 2, 1, 2, 3, 0, 1], [2, 1, 0, 1, 0, 3, 0, 1],
   [1, 0, 1, 2, 3, 2, 3, 2, 1, 0], [3, 0, 1, 2, 1], [0, 1, 2, 1, 2, 3, 0, 1], [0, 3, 2, 1],
   [0, 1, 0, 3, 0], [0, 1, 0, 1], [1, 2, 1, 2, 1, 0, 1], [0, 1, 0, 3, 0, 3],
   [3, 0, 3, 0, 1, 0, 3, 0], [1, 2, 1, 2, 1, 2, 3, 0, 1], [0, 3, 0, 3, 0],
   [1, 2, 1, 0, 1, 0, 3, 0], [0, 3, 2, 3], [2, 1, 0, 1], [2, 1, 2, 3, 2, 3, 2, 1, 0],
   [2, 1, 2, 1, 2, 3, 2, 3, 0], [1, 2, 3, 2, 1, 2, 1], [0, 3, 0, 1, 0, 1],
   [0, 3, 0, 1, 0, 3, 0], [1, 2, 1, 0], [1, 2, 1, 0, 1, 0, 1, 2], [0, 1, 0, 1, 2, 1],
   [2, 3, 2, 1, 2, 3, 0], [1, 2, 1, 2, 3, 0, 1], [3, 0, 3, 2, 1, 0], [1, 0, 1, 0, 3, 0],
   [1, 0, 3, 0, 1, 0, 3, 0], [0, 3, 0, 3, 0, 3, 0], [0, 1, 2, 3, 2, 1], [1, 2, 1, 0, 1],
   [1, 2, 1, 0, 3], [3, 2, 3, 0, 1, 0, 3], [2, 3, 0, 1, 0, 1, 2, 1], [0, 3, 2, 1, 0], [1],
   [1, 0, 3, 2, 1], [3, 0, 1, 0, 3], [0, 3, 0, 1, 0, 3, 0, 1], [2, 1, 0, 1, 2], [3, 0, 3, 0, 1],
   [1, 0, 1, 2, 3, 2, 3, 0], [1, 2, 1, 2, 1], [2, 3, 0, 3, 0, 3, 0],
   [0, 1, 2, 1, 2, 3, 2, 3, 0], [2], [1, 2, 1, 2, 1, 2, 1, 0, 3], [3, 0, 3, 0], [3, 0, 1],
   [2, 1], [1, 0, 1, 0, 1, 0, 3, 0, 1], [3, 2, 3, 2, 3, 2, 1, 0, 1], [2, 1, 0, 3, 0, 3, 0, 1],
   [3, 2, 1, 2, 3, 0, 1], [2, 3, 0, 1, 2], [2, 3], [2, 3, 2, 3], [0, 1, 2, 1, 2, 3],
   [3, 0, 3, 0, 3], [0, 1, 0, 3, 0, 1, 0, 1], [0, 3, 2, 3, 2, 1, 0, 1], [0, 3, 0],
   [2, 1, 2, 1, 2, 1, 0, 3], [3, 2, 3, 0], [1, 2, 3, 2, 3, 2, 1, 0, 1], [1, 2, 1, 2, 3],
   [2, 1, 2, 1, 2, 3], [0, 3, 2, 1, 2, 3, 0, 1], [0, 1], [0, 3, 2, 3, 0, 3, 0, 3],
   [1, 2, 3, 0, 3, 0, 3, 0], [2, 3, 0, 3, 0, 3], [0, 3, 0, 3, 0, 1], [2, 1, 2, 3, 0, 1], [3],
   [3, 2, 1, 2, 3, 0, 1, 0, 1], [1, 2, 3, 2, 3, 0], [3, 2, 1, 2, 1, 2, 1, 0, 3],
   [1, 0, 1, 2, 1, 2, 3], [1, 2, 3], [3, 0, 3, 0, 3, 0], [0, 1, 0, 3, 0, 3, 0, 1],
   [2, 3, 2, 3, 2, 1, 0, 1], [0, 3, 0, 1], [3, 2, 3, 2, 1, 0, 1], [1, 2, 1, 2, 3, 2, 3, 0],
   [0, 1, 2, 3, 0]]

@[expose] def outerW : List (List (Fin 4)) :=
  [[], [3, 2, 3, 2, 3, 2, 1, 0, 1], [1, 2, 3, 2, 3, 2, 1, 0, 1], [1], [0, 1, 2],
   [1, 2, 3, 0, 3, 0, 3], [1, 0, 3, 2, 1, 2, 3, 0, 1], [3, 2, 3], [0, 3, 0, 3, 0],
   [3, 0, 3, 0, 3, 0], [1, 0, 3, 0, 3, 0, 1], [0, 3, 0, 3, 0, 1], [2, 3, 0], [1, 0, 3, 0, 1],
   [1, 2, 1, 2, 1, 0, 3], [2, 1, 2, 3, 0, 1, 0, 1]]

@[expose] def outerL : List (List (Fin 4)) :=
  [[2, 1, 2, 1, 2, 1, 0, 1], [3, 2, 1, 2, 3], [3, 2, 3, 0, 3, 0, 3, 0], [1, 0, 1]]


@[expose] def letterTab : Fin 4 → List ℕ
  | 0 => permTab pa
  | 1 => permTab pb
  | 2 => invTab 28 (permTab pa)
  | 3 => invTab 28 (permTab pb)

@[expose] def wordTab (w : List (Fin 4)) : List ℕ :=
  (w.map letterTab).foldr compTab (List.range 28)

@[expose] def conjTab (t w : List ℕ) : List ℕ := compTab (compTab w t) (invTab 28 w)

theorem permTab_letterP (i : Fin 4) : permTab (letterP i) = letterTab i := by
  fin_cases i
  · rfl
  · rfl
  · exact permTab_inv pa
  · exact permTab_inv pb

theorem permTab_wordP (w : List (Fin 4)) : permTab (wordP w) = wordTab w := by
  unfold wordP wordTab
  rw [permTab_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  exact permTab_letterP i

theorem permTab_conj (z : Pm) (w : List (Fin 4)) :
    permTab (wordP w * z * (wordP w)⁻¹) = conjTab (permTab z) (wordTab w) := by
  unfold conjTab
  rw [permTab_mul, permTab_mul, permTab_inv, permTab_wordP]

theorem zConjWords_length : zConjWords.length = 63 := by decide +kernel

theorem zConj_tab_nodup :
    (zConjWords.map fun w => conjTab (permTab fz) (wordTab w)).Nodup := by decide +kernel

theorem zConjWords_nodup : ((zConjWords.map wordP).map fun w => w * fz * w⁻¹).Nodup := by
  apply nodup_of_nodup_permTab
  have h : ((zConjWords.map wordP).map fun w => w * fz * w⁻¹).map permTab
      = zConjWords.map fun v => conjTab (permTab fz) (wordTab v) := by
    rw [List.map_map, List.map_map]
    apply List.map_congr_left
    intro v _
    exact permTab_conj fz v
  rw [h]
  exact zConj_tab_nodup

theorem tauConjWords_length : tauConjWords.length = 252 := by decide +kernel

theorem tauConj_tab_nodup :
    (tauConjWords.map fun w => conjTab (permTab ftau) (wordTab w)).Nodup := by decide +kernel

theorem tauConjWords_nodup :
    ((tauConjWords.map wordP).map fun w => w * ftau * w⁻¹).Nodup := by
  apply nodup_of_nodup_permTab
  have h : ((tauConjWords.map wordP).map fun w => w * ftau * w⁻¹).map permTab
      = tauConjWords.map fun v => conjTab (permTab ftau) (wordTab v) := by
    rw [List.map_map, List.map_map]
    apply List.map_congr_left
    intro v _
    exact permTab_conj ftau v
  rw [h]
  exact tauConj_tab_nodup

theorem outerW_tab_spec : ∀ a b : Fin 4,
    conjTab (permTab ftau) (wordTab (outerW.getD (4 * a.val + b.val) [])) =
      permTab (fx₁ ^ a.val * fx₂ ^ b.val * ftau) := by
  decide +kernel

theorem outerL_tab_spec : ∀ a : Fin 4,
    conjTab (permTab ftau) (wordTab (outerL.getD a.val [])) =
      permTab (fx₁ ^ a.val * fx₂ ^ a.val * flam * ftau) := by
  decide +kernel

theorem outerW_spec : ∀ a b : Fin 4, wordP (outerW.getD (4 * a.val + b.val) []) * ftau *
    (wordP (outerW.getD (4 * a.val + b.val) []))⁻¹ = fx₁ ^ a.val * fx₂ ^ b.val * ftau := by
  intro a b
  apply permTab_injective
  rw [permTab_conj]
  exact outerW_tab_spec a b

theorem outerL_spec : ∀ a : Fin 4, wordP (outerL.getD a.val []) * ftau *
    (wordP (outerL.getD a.val []))⁻¹ = fx₁ ^ a.val * fx₂ ^ a.val * flam * ftau := by
  intro a
  apply permTab_injective
  rw [permTab_conj]
  exact outerL_tab_spec a

@[expose] def d8List : List Pm :=
  [1, flam, fz, fz * flam, fy, fy * flam, fy * fz, fy * fz * flam]

theorem d8List_nodup : d8List.Nodup := by decide +kernel

@[expose] def d8Tabs : List (List ℕ) := d8List.map permTab

theorem d8_tab_closed : ∀ t ∈ d8Tabs, compTab t (permTab fy) ∈ d8Tabs ∧
    compTab t (permTab fz) ∈ d8Tabs ∧ compTab t (permTab flam) ∈ d8Tabs := by
  decide +kernel

theorem d8List_closed : ∀ e ∈ d8List, e * fy ∈ d8List ∧ e * fz ∈ d8List ∧ e * flam ∈ d8List := by
  intro e he
  have he' : permTab e ∈ d8Tabs := List.mem_map_of_mem he
  obtain ⟨h1, h2, h3⟩ := d8_tab_closed (permTab e) he'
  refine ⟨?_, ?_, ?_⟩
  · have : permTab (e * fy) ∈ d8List.map permTab := by
      rw [permTab_mul]; exact h1
    exact (List.mem_map_of_injective permTab_injective).mp this
  · have : permTab (e * fz) ∈ d8List.map permTab := by
      rw [permTab_mul]; exact h2
    exact (List.mem_map_of_injective permTab_injective).mp this
  · have : permTab (e * flam) ∈ d8List.map permTab := by
      rw [permTab_mul]; exact h3
    exact (List.mem_map_of_injective permTab_injective).mp this

theorem d8_comm_ftau :
    fy * ftau = ftau * fy ∧ fz * ftau = ftau * fz ∧ flam * ftau = ftau * flam := by
  decide +kernel

theorem frame_comm_fz : fx₁ * fz = fz * fx₁ ∧ fx₂ * fz = fz * fx₂ ∧ flam * fz = fz * flam := by
  decide +kernel

theorem frho_conj_fy_fz : frho * fy * frho⁻¹ = fz ∧ frho * fz * frho⁻¹ = fy * fz := by
  decide +kernel

theorem flam_conj_fy : flam * fy * flam⁻¹ = fy * fz := by decide +kernel

theorem fy_fz_comm : fy * fz = fz * fy := by decide +kernel

theorem involT_conj_fz :
    frho * fy * frho⁻¹ = fz ∧ frho⁻¹ * fx₂ ^ 2 * (frho⁻¹)⁻¹ = fz ∧
    ∀ a : Fin 4, (fk0⁻¹ * (fx₁⁻¹) ^ a.val) * (fx₁ ^ a.val * fx₂ ^ (4 - a.val) * flam) *
      (fk0⁻¹ * (fx₁⁻¹) ^ a.val)⁻¹ = fz := by
  decide +kernel

end CFSG.OddStandard.SmallF3.HarrisU33.K28
