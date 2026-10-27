module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.OrbitRowDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.FixSpec
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.TableKSpec

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3Model

open Subgroup CFSG.EvenSporadicStandard.HNRecog CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.SmallOddCore.Native

local notation "𝒞" => CFSG.Sporadic.SmallOddCore.conjClass

@[expose] noncomputable def OrbRow.repElem (wy : List ℕ) (r : OrbRow) : Equiv.Perm (Fin 1408) :=
  elemW r.conj * elemW wy * (elemW r.conj)⁻¹

private theorem wordOK_append (u v : List ℕ) : wordOK (u ++ v) = (wordOK u && wordOK v) := by
  simp only [wordOK, List.all_append]

private theorem wordOK_flatten_replicate (e : ℕ) {w : List ℕ} (h : wordOK w = true) :
    wordOK (List.replicate e w).flatten = true := by
  induction e with
  | zero => simp [wordOK]
  | succ e ih => rw [List.replicate_succ, List.flatten_cons, wordOK_append, h, ih]; rfl

private theorem wordOK_getD {gs : List (List ℕ)} (h : gs.all wordOK = true) (i : ℕ) :
    wordOK (gs.getD i []) = true := by
  by_cases hi : i < gs.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact List.all_eq_true.1 h _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (by omega)]
    simp [wordOK]

theorem wordOK_specWord {gs : List (List ℕ)} (h : gs.all wordOK = true) (s : List (ℕ × ℕ)) :
    wordOK (specWord gs s) = true := by
  induction s with
  | nil => simp [specWord, wordOK]
  | cons p ps ih =>
    have e : specWord gs (p :: ps) =
        (List.replicate p.2 (gs.getD (p.1 - 1) [])).flatten ++ specWord gs ps := by
      simp [specWord, List.flatMap_cons]
    rw [e, wordOK_append, wordOK_flatten_replicate _ (wordOK_getD h _), ih]
    rfl

theorem wgens_spec (hgens : gensOK = true) {ws : List (List ℕ)} (hw : ws.all wordOK = true) :
    ∀ l < (p0Tabs ws).size, Rep 1408 (p0Tabs ws)[l]! (tablePerm 1408 (p0Tabs ws)[l]!) ∧
      tablePerm 1408 (p0Tabs ws)[l]! ∈ closure (elemW '' {w | w ∈ ws}) := by
  intro l hl
  have hmem : (p0Tabs ws)[l]! ∈ tabsW ws := by
    have := getElem!_mem_array hl
    simpa [p0Tabs] using this
  obtain ⟨w, hwm, hwl⟩ := List.mem_map.1 hmem
  have hr : Rep 1408 (tabW w) (elemW w) :=
    rep_elemW_of_gensOK hgens (List.all_eq_true.1 hw w hwm)
  have hr' : Rep 1408 (p0Tabs ws)[l]! (elemW w) := by rw [← hwl]; exact hr
  rw [tablePerm_eq hr']
  exact ⟨hr', subset_closure ⟨w, hwm, rfl⟩⟩

theorem kgens_spec (hgens : gensOK = true) {kg : List (List ℕ)} (hw : kg.all wordOK = true)
    (hinv : kg.all (fun w => invOK 1408 (tabW w) (invT 1408 (tabW w))) = true) :
    ∀ l < (p0Tabs kg).size, Rep 1408 (p0Tabs kg)[l]! (tablePerm 1408 (p0Tabs kg)[l]!) ∧
      Rep 1408 (p0Invs kg)[l]! (tablePerm 1408 (p0Tabs kg)[l]!)⁻¹ ∧
        tablePerm 1408 (p0Tabs kg)[l]! ∈ closure (elemW '' {w | w ∈ kg}) := by
  intro l hl
  obtain ⟨h1, h2, -⟩ := p0_gens_spec hgens hw hinv l hl
  exact ⟨h1, h2, (wgens_spec hgens hw l hl).2⟩

theorem rep_repTab (hgens : gensOK = true) {wy : List ℕ} (hwy : wordOK wy = true) {r : OrbRow}
    (hconj : wordOK r.conj = true)
    (hconjinv : invOK 1408 (tabW r.conj) (invT 1408 (tabW r.conj)) = true) :
    Rep 1408 (r.repTab wy) (r.repElem wy) :=
  rep_conjTab hgens hconj hconjinv (rep_elemW_of_gensOK hgens hwy)

theorem orbRowOK_spec_closure {cap : ℕ} {kg : List (List ℕ)} {wy : List ℕ} {korder : ℕ}
    {r : OrbRow} (h : orbRowOK cap kg wy korder r = true)
    (hKcard : Nat.card ↥(closure (elemW '' {w | w ∈ kg})) = korder) :
    Rep 1408 (r.repTab wy) (r.repElem wy) ∧
      (𝒞 (closure (elemW '' {w | w ∈ kg})) (r.repElem wy)).ncard = r.m ∧
      Nat.card ↥(closure (elemW '' {w | w ∈ kg}) ⊓
        centralizer ({r.repElem wy} : Set (Equiv.Perm (Fin 1408)))) = r.n ∧
      closure (elemW '' {w | w ∈ r.stabWords kg}) =
        closure (elemW '' {w | w ∈ kg}) ⊓
          centralizer ({r.repElem wy} : Set (Equiv.Perm (Fin 1408))) := by
  simp only [orbRowOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hgens, hwy⟩, hconj⟩, hkg⟩, hkginv⟩, hconjinv⟩, htree⟩, hodist⟩, hosize⟩,
    hcomm⟩, hStree⟩, hSdist⟩, hSsize⟩, hmn⟩ := h
  set K : Subgroup (Equiv.Perm (Fin 1408)) := closure (elemW '' {w | w ∈ kg}) with hKdef
  set c : Equiv.Perm (Fin 1408) := r.repElem wy with hcdef
  set sw : List (List ℕ) := r.stabWords kg with hsw
  set o := conjClosureH 1408 (p0Tabs kg) (p0Invs kg) (r.repTab wy) cap with ho
  set S := mulClosureH 1408 (p0Tabs sw) cap with hS
  have hrc : Rep 1408 (r.repTab wy) c := rep_repTab hgens hwy hconj hconjinv
  have hconjSpec := conjTreeOK_spec K (kgens_spec hgens hkg hkginv) hrc htree
  have horep : ∀ k < o.1.size, Rep 1408 o.1[k]! (tablePerm 1408 o.1[k]!) := by
    intro k hk
    obtain ⟨c', -, hrep⟩ := hconjSpec k hk
    rw [tablePerm_eq hrep]
    exact hrep
  have honodup : (o.1.toList.map (tablePerm 1408)).Nodup :=
    nodup_of_hkeysDistinct (forall₂_tablePerm horep) hodist
  have hm_le : r.m ≤ (𝒞 K c).ncard := by
    have := length_le_ncard_of_nodup honodup (S := 𝒞 K c) fun x hx => by
      obtain ⟨k, hk, rfl⟩ := mem_map_tablePerm horep hx
      obtain ⟨c', hc', hrep⟩ := hconjSpec k hk
      rw [tablePerm_eq hrep]
      exact ⟨c', hc', rfl⟩
    rwa [List.length_map, Array.length_toList, hosize] at this
  have hswOK : sw.all wordOK = true := by
    rw [List.all_eq_true]
    intro w hw
    obtain ⟨s, -, rfl⟩ := List.mem_map.1 hw
    exact wordOK_specWord hkg s
  have hswmem : ∀ w ∈ sw, elemW w ∈ K := by
    intro w hw
    obtain ⟨s, -, rfl⟩ := List.mem_map.1 hw
    exact elemW_specWord_mem kg s
  have hswcomm : ∀ w ∈ sw, elemW w * c = c * elemW w := fun w hw =>
    (commTT_iff (rep_elemW_of_gensOK hgens (List.all_eq_true.1 hswOK w hw)) hrc).1
      (List.all_eq_true.1 hcomm w hw)
  set S0 : Subgroup (Equiv.Perm (Fin 1408)) := closure (elemW '' {w | w ∈ sw}) with hS0
  have hS0le : S0 ≤ K ⊓ centralizer ({c} : Set (Equiv.Perm (Fin 1408))) := by
    rw [hS0, closure_le]
    rintro _ ⟨w, hw, rfl⟩
    refine mem_inf.mpr ⟨hswmem w hw, ?_⟩
    rw [mem_centralizer_singleton_iff]
    exact hswcomm w hw
  have hSspec := mulTreeOK_spec (n := 1408) (by norm_num) S0
    (gg := fun l => tablePerm 1408 (p0Tabs sw)[l]!) (wgens_spec hgens hswOK) hStree
  have hSrep : ∀ k < S.1.size, Rep 1408 S.1[k]! (tablePerm 1408 S.1[k]!) := by
    intro k hk
    obtain ⟨c', -, hrep⟩ := hSspec k hk
    rw [tablePerm_eq hrep]
    exact hrep
  have hSmem : ∀ k < S.1.size, tablePerm 1408 S.1[k]! ∈ S0 := by
    intro k hk
    obtain ⟨c', hc', hrep⟩ := hSspec k hk
    rw [tablePerm_eq hrep]
    exact hc'
  have hSnodup : (S.1.toList.map (tablePerm 1408)).Nodup :=
    nodup_of_hkeysDistinct (forall₂_tablePerm hSrep) hSdist
  have hn_le : r.n ≤ Nat.card S0 := by
    have := length_le_card_of_nodup hSnodup fun x hx => by
      obtain ⟨k, hk, rfl⟩ := mem_map_tablePerm hSrep hx
      exact hSmem k hk
    rwa [List.length_map, Array.length_toList, hSsize] at this
  have hn_le' : r.n ≤ Nat.card ↥(K ⊓ centralizer ({c} : Set (Equiv.Perm (Fin 1408)))) :=
    hn_le.trans (card_le_of_le hS0le)
  have hKcard' : Nat.card K = korder := hKcard
  have hos := CFSG.Sporadic.SmallOddCore.ncard_conjClass_mul_card K c
  rw [hKcard', ← hmn] at hos
  have hKpos : 0 < Nat.card K := Nat.card_pos
  rw [hKcard', ← hmn] at hKpos
  have hm_pos : 0 < r.m := Nat.pos_of_mul_pos_right hKpos
  have hn_pos : 0 < r.n := Nat.pos_of_mul_pos_left hKpos
  have hA : (𝒞 K c).ncard = r.m := by
    by_contra hne
    have hlt : r.m < (𝒞 K c).ncard := lt_of_le_of_ne hm_le (Ne.symm hne)
    have h1 : r.m * r.n < (𝒞 K c).ncard * r.n := Nat.mul_lt_mul_of_pos_right hlt hn_pos
    have h2 : (𝒞 K c).ncard * r.n ≤ (𝒞 K c).ncard *
        Nat.card ↥(K ⊓ centralizer ({c} : Set (Equiv.Perm (Fin 1408)))) :=
      Nat.mul_le_mul_left _ hn_le'
    omega
  have hB : Nat.card ↥(K ⊓ centralizer ({c} : Set (Equiv.Perm (Fin 1408)))) = r.n := by
    by_contra hne
    have hlt : r.n < Nat.card ↥(K ⊓ centralizer ({c} : Set (Equiv.Perm (Fin 1408)))) :=
      lt_of_le_of_ne hn_le' (Ne.symm hne)
    have h1 : r.m * r.n < r.m * Nat.card ↥(K ⊓ centralizer ({c} : Set (Equiv.Perm (Fin 1408)))) :=
      Nat.mul_lt_mul_of_pos_left hlt hm_pos
    rw [hA] at hos
    omega
  have hS0eq : S0 = K ⊓ centralizer ({c} : Set (Equiv.Perm (Fin 1408))) :=
    Subgroup.eq_of_le_of_card_ge hS0le (by rw [hB]; exact hn_le)
  exact ⟨hrc, hA, hB, hS0eq⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3Model
