
module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListA7LatticeBase

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListA7Enc
public meta import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListA7Enc
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListA7LatticeInputs
public import Certificates.Certificate4058
public import Certificates.Certificate4058Base

public section

namespace CFSG.QuasithinUnique.Vol2Native.A312L.Seven

open Equiv CFSG.QuasithinUnique.Unc25K1.Six

theorem closed_lat :
    latGens.all (fun G => closedH (G.map R7.enc) (elts G)) = true :=
  Certificates.certificate4058.1

theorem sizes_lat : latGens.map (fun G => (elts G).size) =
    [8, 24, 24, 24, 24, 24, 72, 120, 168, 168, 360, 2520] :=
  Certificates.certificate4058.2.1

theorem cover_ok :
    ∀ x : P7, Perm.sign x = 1 → ∃ p ∈ dcSets, R7.enc x ∈ p.2 :=
  Certificates.certificate4058.2.2.1

theorem rep_ok :
    reps.all (fun r => isLatCheck (dGens ++ [r])) = true :=
  Certificates.certificate4058.2.2.2.1

theorem join_ok :
    latGens.all (fun G₁ => latGens.all fun G₂ => isLatCheck (G₁ ++ G₂)) = true :=
  Certificates.certificate4058.2.2.2.2

theorem mem_closure_lat {G : List P7} (hG : G ∈ latGens) (x : P7) :
    x ∈ Subgroup.closure {g | g ∈ G} ↔ R7.enc x ∈ elts G :=
  mem_closure_iff_H rawIsEnc7 G depth (List.all_eq_true.mp closed_lat G hG) x

theorem isLat_of_check {G : List P7} (h : isLatCheck G = true) :
    IsLat (Subgroup.closure {g | g ∈ G}) := by
  simp only [isLatCheck, Bool.and_eq_true, List.any_eq_true] at h
  obtain ⟨hc, Z, hZ, hset⟩ := h
  obtain ⟨G', hG', rfl⟩ := List.mem_map.mp hZ
  refine ⟨G', hG', Subgroup.ext fun x => ?_⟩
  rw [mem_closure_iff_H rawIsEnc7 G depth hc x]
  exact (setEq_spec hset _).trans (mem_closure_lat hG' x).symm

theorem lat_join {G₁ G₂ : List P7} (h₁ : G₁ ∈ latGens) (h₂ : G₂ ∈ latGens) :
    IsLat (Subgroup.closure {g | g ∈ G₁} ⊔ Subgroup.closure {g | g ∈ G₂}) := by
  have h := (List.all_eq_true.mp (List.all_eq_true.mp join_ok G₁ h₁) G₂ h₂)
  have := isLat_of_check h
  have hset : {g | g ∈ G₁ ++ G₂} = {g | g ∈ G₁} ∪ {g | g ∈ G₂} := by
    ext g
    simp
  rw [hset, Subgroup.closure_union] at this
  exact this

theorem lat_rep {r : P7} (hr : r ∈ reps) : IsLat (Subgroup.closure {g | g ∈ dGens ++ [r]}) :=
  isLat_of_check (List.all_eq_true.mp rep_ok r hr)

theorem lat_cyc (x : P7) (hx : Perm.sign x = 1) :
    IsLat (Subgroup.closure {g | g ∈ dGens ++ [x]}) := by
  obtain ⟨⟨r, S⟩, hp, hxS⟩ := cover_ok x hx
  obtain ⟨r', hr', hrS⟩ := List.mem_map.mp hp
  simp only [Prod.mk.injEq] at hrS
  obtain ⟨rfl, rfl⟩ := hrS
  simp only [dcSet, Std.HashSet.mem_ofList, List.contains_iff_exists_mem_beq, List.mem_flatMap,
    List.mem_map, beq_iff_eq] at hxS
  obtain ⟨_, ⟨d', hd', e', he', rfl⟩, hxeq⟩ := hxS
  have hdmem := bfsSet_sound rawIsEnc7 dGens depth d' (Std.HashSet.mem_toList.mp hd')
  have hemem := bfsSet_sound rawIsEnc7 dGens depth e' (Std.HashSet.mem_toList.mp he')
  obtain ⟨d, hd, rfl⟩ := hdmem
  obtain ⟨e, he, rfl⟩ := hemem
  have hxe : x = d * r' * e := R7.enc_inj (by rw [R7.enc_mul, R7.enc_mul]; exact hxeq)
  have hD : D7 ≤ Subgroup.closure {g | g ∈ dGens ++ [x]} := D7_le_closure _
  have hD' : D7 ≤ Subgroup.closure {g | g ∈ dGens ++ [r']} := D7_le_closure _
  have heq : Subgroup.closure {g | g ∈ dGens ++ [x]} = Subgroup.closure {g | g ∈ dGens ++ [r']} := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      intro g hg
      rcases List.mem_append.mp hg with hg | hg
      · exact Subgroup.subset_closure (List.mem_append_left _ hg)
      · rw [List.mem_singleton.mp hg, hxe]
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hD' hd)
          (Subgroup.subset_closure (List.mem_append_right _ (List.mem_singleton_self _))))
          (hD' he)
    · rw [Subgroup.closure_le]
      intro g hg
      rcases List.mem_append.mp hg with hg | hg
      · exact Subgroup.subset_closure (List.mem_append_left _ hg)
      · rw [List.mem_singleton.mp hg]
        have : r' = d⁻¹ * x * e⁻¹ := by rw [hxe]; group
        rw [this]
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (hD hd))
          (Subgroup.subset_closure (List.mem_append_right _ (List.mem_singleton_self _))))
          (Subgroup.inv_mem _ (hD he))
  rw [heq]
  exact lat_rep hr'

theorem lat_list (l : List P7) (hl : ∀ x ∈ l, Perm.sign x = 1) :
    IsLat (Subgroup.closure {g | g ∈ dGens ++ l}) := by
  induction l with
  | nil =>
    refine ⟨dGens, dGens_mem_lat, ?_⟩
    simp
  | cons x l ih =>
    have ih' := ih (fun y hy => hl y (List.mem_cons_of_mem _ hy))
    have hx := lat_cyc x (hl x List.mem_cons_self)
    obtain ⟨G₁, h₁, e₁⟩ := ih'
    obtain ⟨G₂, h₂, e₂⟩ := hx
    have hset : {g | g ∈ dGens ++ x :: l} = {g | g ∈ dGens ++ l} ∪ {g | g ∈ dGens ++ [x]} := by
      ext g
      simp only [Set.mem_ofPred_eq, List.mem_append, List.mem_cons, Set.mem_union]
      tauto
    rw [hset, Subgroup.closure_union, e₁, e₂]
    exact lat_join h₁ h₂

theorem overgroups_A7 {Y : Subgroup P7} (hDY : D7 ≤ Y) (hY : ∀ y ∈ Y, Perm.sign y = 1) :
    ∃ i, i < 12 ∧ Y = Z i := by
  classical
  let l : List P7 := (Set.toFinite (Y : Set P7)).toFinset.toList
  have hl : ∀ x ∈ l, Perm.sign x = 1 := fun x hx => hY x (by
    simpa [l] using hx)
  obtain ⟨G, hG, hYG⟩ := lat_list l hl
  have hY' : Subgroup.closure {g | g ∈ dGens ++ l} = Y := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      intro g hg
      rcases List.mem_append.mp hg with hg | hg
      · exact hDY (Subgroup.subset_closure hg)
      · simpa [l] using hg
    · intro y hy
      exact Subgroup.subset_closure (List.mem_append_right _ (by simpa [l] using hy))
  rw [hY'] at hYG
  obtain ⟨i, hi, hiG⟩ := List.mem_iff_getElem.mp hG
  refine ⟨i, by simpa [latGens] using hi, ?_⟩
  have hget : latGens.getD i [] = G := by rw [List.getD_eq_getElem _ _ hi, hiG]
  rw [hYG, Z, hget]

end CFSG.QuasithinUnique.Vol2Native.A312L.Seven
