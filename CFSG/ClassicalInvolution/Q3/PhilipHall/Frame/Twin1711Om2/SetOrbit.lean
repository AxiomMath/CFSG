module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Om2.Basic

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om2

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
open CFSG.EvenSmallLie.OmegaEight CFSG.EvenSmallLie.OmegaEight.Weyl
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om2Data
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om2Check
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1Check (reflTab wA wordOK eA keyF)
open CFSG.ClassicalInvolution.Generic
open scoped Pointwise

set_option linter.unusedSectionVars false

noncomputable instance : MulAction HY (Finset (Fin 480)) := MulAction.compHom _ phi

theorem smul_def (u : HY) (S : Finset (Fin 480)) : u • S = phi u • S := rfl

@[expose] noncomputable def decFY (F : Array ℕ) : Finset (Fin 480) :=
  Finset.univ.filter fun r => (r : ℕ) ∈ F.toList

private theorem so2_mem_decFY {F : Array ℕ} {r : Fin 480} :
    r ∈ decFY F ↔ (r : ℕ) ∈ F.toList := by
  simp [decFY]

private theorem so2_validFY_iff {F : Array ℕ} :
    validFY F = true ↔ (∀ x ∈ F.toList, x < 480) ∧ F.toList.Pairwise (· < ·) := by
  have hadj : (∀ i < F.size - 1, F[i]! < F[i + 1]!) ↔ F.toList.Pairwise (· < ·) := by
    rw [List.pairwise_iff_getElem]
    constructor
    · intro h i j hi hj hij
      simp only [Array.length_toList] at hi hj
      simp only [Array.getElem_toList]
      induction j, (Nat.succ_le_of_lt hij) using Nat.le_induction with
      | base =>
        have := h i (by omega)
        rwa [getElem!_pos F i hi, getElem!_pos F (i + 1) hj] at this
      | succ j hij ih =>
        have h1 := ih (by omega) (by omega)
        have h2 := h j (by omega)
        rw [getElem!_pos F j (by omega), getElem!_pos F (j + 1) hj] at h2
        exact h1.trans h2
    · intro h i hi
      have hi1 : i < F.size := by omega
      have hi2 : i + 1 < F.size := by omega
      have := h i (i + 1) (by simpa using hi1) (by simpa using hi2) (Nat.lt_succ_self i)
      rw [getElem!_pos F i hi1, getElem!_pos F (i + 1) hi2]
      simpa using this
  simp only [validFY, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq,
    Array.all_eq_true', hadj, Array.mem_toList_iff]

theorem decFY_actFY {g : Array ℕ} {G : Equiv.Perm (Fin 480)} (hg : Rep 480 g G) {F : Array ℕ}
    (hF : validFY F = true) : decFY (actFY g F) = G • decFY F := by
  obtain ⟨hlt, -⟩ := so2_validFY_iff.1 hF
  ext r
  rw [so2_mem_decFY, Finset.mem_smul_finset]
  simp only [actFY, List.toList_toArray, List.mem_mergeSort, List.mem_map, so2_mem_decFY,
    Equiv.Perm.smul_def]
  constructor
  · rintro ⟨i, hi, hir⟩
    refine ⟨⟨i, hlt i hi⟩, hi, Fin.ext ?_⟩
    rw [← hir, hg.apply (hlt i hi)]
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, hg y⟩

theorem decFY_inj {F F' : Array ℕ} (h : validFY F = true) (h' : validFY F' = true)
    (e : decFY F = decFY F') : F = F' := by
  obtain ⟨hlt, hp⟩ := so2_validFY_iff.1 h
  obtain ⟨hlt', hp'⟩ := so2_validFY_iff.1 h'
  refine Array.toList_inj.1 (hp.eq_of_mem_iff hp' fun x => ?_)
  by_cases hx : x < 480
  · have := Finset.ext_iff.1 e ⟨x, hx⟩
    rwa [so2_mem_decFY, so2_mem_decFY] at this
  · exact ⟨fun hx' => absurd (hlt x hx') hx, fun hx' => absurd (hlt' x hx') hx⟩

theorem decFY_fCodeY {t : Array ℕ} {T : Equiv.Perm (Fin 480)} (ht : Rep 480 t T) :
    decFY (fCodeY t) = Finset.univ.filter fun r => T r = phi (cK 2) r := by
  ext r
  simp only [so2_mem_decFY, fCodeY, List.toList_toArray, List.mem_filter, List.mem_range,
    beq_iff_eq, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [ht.apply r.2, (rep_cK (by norm_num : 2 < 3)).apply r.2]
  exact ⟨fun h => Fin.ext h.2, fun h => ⟨r.2, congrArg Fin.val h⟩⟩

theorem arrCertFY_spec {gs : Array (Array ℕ)} {gens : ℕ → HY}
    (hgens : ∀ k < gs.size, Rep 480 gs[k]! (phi (gens k))) {root : Array ℕ} {c : ArrCert}
    (h : arrCertOK (fun k X => actFY gs[k]! X) gs.size validFY keyF root c = true) :
    MulAction.orbit (Subgroup.closure (gens '' {k | k < gs.size})) (decFY root) =
        (fun i => decFY c.pts[i]!) '' {i | i < c.pts.size} ∧
      (MulAction.orbit (Subgroup.closure (gens '' {k | k < gs.size})) (decFY root)).ncard =
        c.pts.size ∧
      ∀ i < c.pts.size, validFY c.pts[i]! = true := by
  have hact : ∀ k < gs.size, ∀ a, validFY a = true →
      decFY (actFY gs[k]! a) = gens k • decFY a := fun k hk a ha => by
    rw [decFY_actFY (hgens k hk) ha]
    rfl
  have hkey : ∀ a b, validFY a = true → validFY b = true → decFY a = decFY b →
      keyF a = keyF b := fun a b ha hb e => by rw [decFY_inj ha hb e]
  exact ⟨orbit_of_arrCertOK (dec := decFY) h hact,
    ncard_orbit_of_arrCertOK (dec := decFY) h hact hkey, fun i hi => arrCertOK_valid h hi⟩

theorem orbSizeY_spec {gs : Array (Array ℕ)} {gens : ℕ → HY}
    (hgens : ∀ k < gs.size, Rep 480 gs[k]! (phi (gens k))) {F : Array ℕ} {sz : ℕ}
    (h : orbSizeY gs F sz = true) :
    MulAction.orbit (Subgroup.closure (gens '' {k | k < gs.size})) (decFY F) =
        (fun i => decFY (orbFY gs F (sz + 1)).pts[i]!) '' {i | i < (orbFY gs F (sz + 1)).pts.size} ∧
      (MulAction.orbit (Subgroup.closure (gens '' {k | k < gs.size})) (decFY F)).ncard = sz ∧
      (orbFY gs F (sz + 1)).pts.size = sz ∧
      ∀ i < (orbFY gs F (sz + 1)).pts.size, validFY (orbFY gs F (sz + 1)).pts[i]! = true := by
  simp only [orbSizeY, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨hok, hsz⟩ := h
  obtain ⟨h1, h2, h3⟩ := arrCertFY_spec hgens hok
  exact ⟨h1, h2.trans hsz, hsz, h3⟩

@[expose] noncomputable def gensOfY (ws : List (List ℕ)) (k : ℕ) : HY := wordE (ws.getD k [])

theorem rep_gensOfY {ws : List (List ℕ)} (hws : ∀ w ∈ ws, wordYOK w = true) {k : ℕ}
    (hk : k < (ws.map (wY (lettersY (reflTab ())))).toArray.size) :
    Rep 480 (ws.map (wY (lettersY (reflTab ())))).toArray[k]! (phi (gensOfY ws k)) := by
  have hk' : k < ws.length := by simpa using hk
  have e : (ws.map (wY (lettersY (reflTab ())))).toArray[k]! =
      wY (lettersY (reflTab ())) ws[k] := by
    rw [getElem!_pos _ k hk, List.getElem_toArray, List.getElem_map]
  rw [e, gensOfY, List.getD_eq_getElem _ _ hk']
  exact rep_wordE (hws _ (List.getElem_mem hk'))

theorem closure_gensOfY {ws : List (List ℕ)} :
    Subgroup.closure (gensOfY ws '' {k | k < (ws.map (wY (lettersY (reflTab ())))).toArray.size}) =
      closureY ws := by
  rw [closureY]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_setOf_eq, List.size_toArray, List.length_map, gensOfY]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨ws[k], List.getElem_mem hk, by rw [List.getD_eq_getElem _ _ hk]⟩
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hw
    exact ⟨k, hk, by rw [List.getD_eq_getElem _ _ hk]⟩

theorem rep_genY {k : ℕ} (hk : k < (genY (reflTab ())).size) :
    Rep 480 (genY (reflTab ()))[k]! (phi (genE k)) := by
  have hk8 : k < 8 := by simpa [genY] using hk
  exact rep_genE hk8

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om2
