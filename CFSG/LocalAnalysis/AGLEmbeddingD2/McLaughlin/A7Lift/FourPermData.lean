module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.A7Six.PermTools
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.A7Six.PermData
public import CFSG.Quasithin.Background.B6Defs
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.A7Lift.FourPermDataK

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.A7Lift

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.AGLEmbeddingD2.McLaughlin.A7Six PermTools Equiv Equiv.Perm FourK
open CFSG.Permutation.FinPack (memK_iff allK_iff anyK_iff)

@[expose] def gD : List (Perm (Fin 7)) :=
  [swap 0 1 * swap 1 2 * swap 2 3 * swap 4 5, swap 0 2 * swap 4 5]

@[expose] def gPb : List (Perm (Fin 7)) := gD ++ [swap 4 5 * swap 5 6]

@[expose] def gPc : List (Perm (Fin 7)) :=
  gD ++ [(swap 0 1 * swap 1 4) * (swap 2 3 * swap 3 5)]

@[expose] def gPS : List (Perm (Fin 7)) :=
  gD ++ [swap 0 1 * swap 1 2 * swap 2 3 * swap 3 6]

@[expose] def gPa : List (Perm (Fin 7)) := gD ++ [swap 0 1 * swap 1 2]

@[expose] def gA5 : List (Perm (Fin 7)) :=
  [swap 0 1 * swap 1 2, swap 0 1 * swap 1 2 * swap 2 3 * swap 3 6]

@[expose] def fourD : Subgroup (Perm (Fin 7)) := Subgroup.closure {σ | σ ∈ gD}

@[expose] def fourPb : Subgroup (Perm (Fin 7)) := Subgroup.closure {σ | σ ∈ gPb}

@[expose] def fourPc : Subgroup (Perm (Fin 7)) := Subgroup.closure {σ | σ ∈ gPc}

@[expose] def fourPS : Subgroup (Perm (Fin 7)) := Subgroup.closure {σ | σ ∈ gPS}

@[expose] def fourPa : Subgroup (Perm (Fin 7)) := Subgroup.closure {σ | σ ∈ gPa}

@[expose] def fourA5 : Subgroup (Perm (Fin 7)) := Subgroup.closure {σ | σ ∈ gA5}

private def gsD : List ℕ := [1724625, 1725962]

private def gsPb : List ℕ := [1724625, 1725962, 1267336]

private def gsPc : List ℕ := [1724625, 1725962, 1641185]

private def gsPS : List ℕ := [1724625, 1725962, 183505]

private def gsPa : List ℕ := [1724625, 1725962, 1754641]

private def gsA5 : List ℕ := [1754641, 183505]

private theorem hgD : gD.map enc = gsD := by decide +kernel
private theorem hgPb : gPb.map enc = gsPb := by decide +kernel
private theorem hgPc : gPc.map enc = gsPc := by decide +kernel
private theorem hgPS : gPS.map enc = gsPS := by decide +kernel
private theorem hgPa : gPa.map enc = gsPa := by decide +kernel
private theorem hgA5 : gA5.map enc = gsA5 := by decide +kernel

private theorem mem_fourD (x : Perm (Fin 7)) : x ∈ fourD ↔ enc x ∈ LD :=
  mem_closure_iff_reachL gD (fun _ => Iff.rfl) gsD hgD LD id_LD cl_LD reach_LD x

private theorem mem_fourPS (x : Perm (Fin 7)) : x ∈ fourPS ↔ enc x ∈ LPS :=
  mem_closure_iff_reachL gPS (fun _ => Iff.rfl) gsPS hgPS LPS id_LPS cl_LPS reach_LPS x

private theorem mem_fourPa (x : Perm (Fin 7)) : x ∈ fourPa ↔ enc x ∈ LPa :=
  mem_closure_iff_reachL gPa (fun _ => Iff.rfl) gsPa hgPa LPa id_LPa cl_LPa reach_LPa x

private theorem mem_fourA5 (x : Perm (Fin 7)) : x ∈ fourA5 ↔ enc x ∈ LA5 :=
  mem_closure_iff_reachL gA5 (fun _ => Iff.rfl) gsA5 hgA5 LA5 id_LA5 cl_LA5 reach_LA5 x

theorem card_fourD : Nat.card fourD = 8 :=
  (card_closure_reachL gD (S := {σ | σ ∈ gD}) (fun _ => Iff.rfl) gsD hgD LD id_LD cl_LD
    reach_LD nd_LD).trans (by decide +kernel)

theorem card_fourPb : Nat.card fourPb = 24 :=
  (card_closure_reachL gPb (S := {σ | σ ∈ gPb}) (fun _ => Iff.rfl) gsPb hgPb LPb id_LPb cl_LPb
    reach_LPb nd_LPb).trans (by decide +kernel)

theorem card_fourPc : Nat.card fourPc = 24 :=
  (card_closure_reachL gPc (S := {σ | σ ∈ gPc}) (fun _ => Iff.rfl) gsPc hgPc LPc id_LPc cl_LPc
    reach_LPc nd_LPc).trans (by decide +kernel)

theorem card_fourPS : Nat.card fourPS = 120 :=
  (card_closure_reachL gPS (S := {σ | σ ∈ gPS}) (fun _ => Iff.rfl) gsPS hgPS LPS id_LPS cl_LPS
    reach_LPS nd_LPS).trans (by decide +kernel)

theorem card_fourA5 : Nat.card fourA5 = 60 :=
  (card_closure_reachL gA5 (S := {σ | σ ∈ gA5}) (fun _ => Iff.rfl) gsA5 hgA5 LA5 id_LA5 cl_LA5
    reach_LA5 nd_LA5).trans (by decide +kernel)

theorem fourD_le_fourPb : fourD ≤ fourPb :=
  Subgroup.closure_mono fun _ hg => List.mem_append_left _ hg

theorem fourD_le_fourPc : fourD ≤ fourPc :=
  Subgroup.closure_mono fun _ hg => List.mem_append_left _ hg

theorem fourD_le_fourPS : fourD ≤ fourPS :=
  Subgroup.closure_mono fun _ hg => List.mem_append_left _ hg

theorem fourD_le_fourPa : fourD ≤ fourPa :=
  Subgroup.closure_mono fun _ hg => List.mem_append_left _ hg

theorem fourPa_le_fourPS : fourPa ≤ fourPS := by
  refine (Subgroup.closure_le _).2 fun g hg => ?_
  simp only [Set.mem_setOf_eq] at hg
  rw [gPa, List.mem_append] at hg
  rcases hg with hg | hg
  · exact Subgroup.subset_closure (List.mem_append_left _ hg)
  · rw [List.mem_singleton] at hg
    subst g
    exact (mem_fourPS _).2 (by decide +kernel)

private theorem isThreeCycle_fourPb_extra :
    IsThreeCycle (swap 4 5 * swap 5 6 : Perm (Fin 7)) := by
  have h := isThreeCycle_swap_mul_swap_same (a := (5 : Fin 7)) (b := 4) (c := 6)
    (by decide) (by decide) (by decide)
  rwa [swap_comm 5 4] at h

private theorem isThreeCycle_four012 :
    IsThreeCycle (swap 0 1 * swap 1 2 : Perm (Fin 7)) := by
  have h := isThreeCycle_swap_mul_swap_same (a := (1 : Fin 7)) (b := 0) (c := 2)
    (by decide) (by decide) (by decide)
  rwa [swap_comm 1 0] at h

private theorem fourD1_mem_alt :
    (swap 0 1 * swap 1 2 * swap 2 3 * swap 4 5 : Perm (Fin 7)) ∈
      alternatingGroup (Fin 7) := by
  rw [mem_alternatingGroup]
  simp [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap]

private theorem fourD2_mem_alt :
    (swap 0 2 * swap 4 5 : Perm (Fin 7)) ∈ alternatingGroup (Fin 7) := by
  rw [mem_alternatingGroup]
  simp [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap]

private theorem fourPb_extra_mem_alt :
    (swap 4 5 * swap 5 6 : Perm (Fin 7)) ∈ alternatingGroup (Fin 7) :=
  isThreeCycle_fourPb_extra.mem_alternatingGroup

private theorem fourPc_extra_mem_alt :
    ((swap 0 1 * swap 1 4) * (swap 2 3 * swap 3 5) : Perm (Fin 7)) ∈
      alternatingGroup (Fin 7) := by
  have h1 : IsThreeCycle (swap 0 1 * swap 1 4 : Perm (Fin 7)) := by
    have h := isThreeCycle_swap_mul_swap_same (a := (1 : Fin 7)) (b := 0) (c := 4)
      (by decide) (by decide) (by decide)
    rwa [swap_comm 1 0] at h
  have h2 : IsThreeCycle (swap 2 3 * swap 3 5 : Perm (Fin 7)) := by
    have h := isThreeCycle_swap_mul_swap_same (a := (3 : Fin 7)) (b := 2) (c := 5)
      (by decide) (by decide) (by decide)
    rwa [swap_comm 3 2] at h
  exact Subgroup.mul_mem (alternatingGroup (Fin 7)) h1.mem_alternatingGroup
    h2.mem_alternatingGroup

private theorem fourPS_extra_mem_alt :
    (swap 0 1 * swap 1 2 * swap 2 3 * swap 3 6 : Perm (Fin 7)) ∈
      alternatingGroup (Fin 7) := by
  rw [mem_alternatingGroup]
  simp [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap]

theorem fourPb_le_alt : fourPb ≤ alternatingGroup (Fin 7) := by
  refine (Subgroup.closure_le _).2 fun g hg => ?_
  simp only [Set.mem_setOf_eq] at hg
  rw [gPb, List.mem_append] at hg
  rcases hg with hg | hg
  · rw [gD, List.mem_cons, List.mem_singleton] at hg
    rcases hg with rfl | rfl
    · exact fourD1_mem_alt
    · exact fourD2_mem_alt
  · rw [List.mem_singleton] at hg
    subst g
    exact fourPb_extra_mem_alt

theorem fourPc_le_alt : fourPc ≤ alternatingGroup (Fin 7) := by
  refine (Subgroup.closure_le _).2 fun g hg => ?_
  simp only [Set.mem_setOf_eq] at hg
  rw [gPc, List.mem_append] at hg
  rcases hg with hg | hg
  · rw [gD, List.mem_cons, List.mem_singleton] at hg
    rcases hg with rfl | rfl
    · exact fourD1_mem_alt
    · exact fourD2_mem_alt
  · rw [List.mem_singleton] at hg
    subst g
    exact fourPc_extra_mem_alt

theorem fourPS_le_alt : fourPS ≤ alternatingGroup (Fin 7) := by
  refine (Subgroup.closure_le _).2 fun g hg => ?_
  simp only [Set.mem_setOf_eq] at hg
  rw [gPS, List.mem_append] at hg
  rcases hg with hg | hg
  · rw [gD, List.mem_cons, List.mem_singleton] at hg
    rcases hg with rfl | rfl
    · exact fourD1_mem_alt
    · exact fourD2_mem_alt
  · rw [List.mem_singleton] at hg
    subst g
    exact fourPS_extra_mem_alt

theorem fourPb_notNormal : ∃ g ∈ fourPb ⊓ alternatingGroup (Fin 7), ∃ e ∈ fourD,
    g * e * g⁻¹ ∉ fourD := by
  refine ⟨swap 4 5 * swap 5 6, Subgroup.mem_inf.2 ⟨?_, fourPb_extra_mem_alt⟩,
    swap 0 1 * swap 1 2 * swap 2 3 * swap 4 5, ?_, ?_⟩
  · exact Subgroup.subset_closure (by simp [gPb])
  · exact Subgroup.subset_closure (by simp [gD])
  · rw [mem_fourD]
    decide +kernel

theorem fourPc_notNormal : ∃ g ∈ fourPc ⊓ alternatingGroup (Fin 7), ∃ e ∈ fourD,
    g * e * g⁻¹ ∉ fourD := by
  refine ⟨(swap 0 1 * swap 1 4) * (swap 2 3 * swap 3 5),
    Subgroup.mem_inf.2 ⟨?_, fourPc_extra_mem_alt⟩,
    swap 0 1 * swap 1 2 * swap 2 3 * swap 4 5, ?_, ?_⟩
  · exact Subgroup.subset_closure (by simp [gPc])
  · exact Subgroup.subset_closure (by simp [gD])
  · rw [mem_fourD]
    decide +kernel

private theorem isPGroup_fourD : IsPGroup 2 ↥fourD :=
  IsPGroup.of_card (n := 3) (by rw [card_fourD]; rfl)

theorem isSolvable_fourPb : Group.IsSolvable ↥fourPb :=
  isSolvable_of_three_mul fourD_le_fourPb isPGroup_fourD
    (by rw [card_fourPb, card_fourD])

theorem isSolvable_fourPc : Group.IsSolvable ↥fourPc :=
  isSolvable_of_three_mul fourD_le_fourPc isPGroup_fourD
    (by rw [card_fourPc, card_fourD])

theorem gen_bc : alternatingGroup (Fin 7) ≤
    Subgroup.closure ((fourPb : Set (Perm (Fin 7))) ∪ fourPc) := by
  set H := Subgroup.closure ((fourPb : Set (Perm (Fin 7))) ∪ fourPc)
  have hc : (swap 4 5 * swap 5 6 : Perm (Fin 7)) ∈ H :=
    Subgroup.subset_closure (Or.inl (Subgroup.subset_closure (by simp [gPb])))
  have hc2 : (swap 4 5 * swap 5 6) * (swap 4 5 * swap 5 6) ∈ H := H.mul_mem hc hc
  have hg : ((swap 0 1 * swap 1 4) * (swap 2 3 * swap 3 5) : Perm (Fin 7)) ∈ H :=
    Subgroup.subset_closure (Or.inr (Subgroup.subset_closure (by simp [gPc])))
  have hg2 : ((swap 0 1 * swap 1 4) * (swap 2 3 * swap 3 5)) *
      ((swap 0 1 * swap 1 4) * (swap 2 3 * swap 3 5)) ∈ H := H.mul_mem hg hg
  refine alternatingGroup_le_of_orbit H ⟨_, hc, isThreeCycle_fourPb_extra⟩ ?_
  intro x
  fin_cases x
  · exact ⟨_, H.mul_mem hg hc, by decide⟩
  · exact ⟨_, H.mul_mem hg2 hc, by decide⟩
  · exact ⟨_, H.mul_mem hg hc2, by decide⟩
  · exact ⟨_, H.mul_mem hg2 hc2, by decide⟩
  · exact ⟨_, hc, by decide⟩
  · exact ⟨_, hc2, by decide⟩
  · exact ⟨1, H.one_mem, by decide⟩

theorem gen_bS : alternatingGroup (Fin 7) ≤
    Subgroup.closure ((fourPb : Set (Perm (Fin 7))) ∪ fourPS) := by
  set H := Subgroup.closure ((fourPb : Set (Perm (Fin 7))) ∪ fourPS)
  have hc : (swap 4 5 * swap 5 6 : Perm (Fin 7)) ∈ H :=
    Subgroup.subset_closure (Or.inl (Subgroup.subset_closure (by simp [gPb])))
  have hc2 : (swap 4 5 * swap 5 6) * (swap 4 5 * swap 5 6) ∈ H := H.mul_mem hc hc
  have hp : (swap 0 1 * swap 1 2 * swap 2 3 * swap 3 6 : Perm (Fin 7)) ∈ H :=
    Subgroup.subset_closure (Or.inr (Subgroup.subset_closure (by simp [gPS])))
  have hp2 : (swap 0 1 * swap 1 2 * swap 2 3 * swap 3 6) *
      (swap 0 1 * swap 1 2 * swap 2 3 * swap 3 6) ∈ H := H.mul_mem hp hp
  have hp3 : (swap 0 1 * swap 1 2 * swap 2 3 * swap 3 6) *
      ((swap 0 1 * swap 1 2 * swap 2 3 * swap 3 6) *
        (swap 0 1 * swap 1 2 * swap 2 3 * swap 3 6)) ∈ H := H.mul_mem hp hp2
  have hp4 : ((swap 0 1 * swap 1 2 * swap 2 3 * swap 3 6) *
      (swap 0 1 * swap 1 2 * swap 2 3 * swap 3 6)) *
      ((swap 0 1 * swap 1 2 * swap 2 3 * swap 3 6) *
        (swap 0 1 * swap 1 2 * swap 2 3 * swap 3 6)) ∈ H := H.mul_mem hp2 hp2
  refine alternatingGroup_le_of_orbit H ⟨_, hc, isThreeCycle_fourPb_extra⟩ ?_
  intro x
  fin_cases x
  · exact ⟨_, hp, by decide⟩
  · exact ⟨_, hp2, by decide⟩
  · exact ⟨_, hp3, by decide⟩
  · exact ⟨_, hp4, by decide⟩
  · exact ⟨_, hc, by decide⟩
  · exact ⟨_, hc2, by decide⟩
  · exact ⟨1, H.one_mem, by decide⟩

theorem gen_cS : alternatingGroup (Fin 7) ≤
    Subgroup.closure ((fourPc : Set (Perm (Fin 7))) ∪ fourPS) := by
  set H := Subgroup.closure ((fourPc : Set (Perm (Fin 7))) ∪ fourPS)
  have hp : (swap 0 1 * swap 1 2 * swap 2 3 * swap 3 6 : Perm (Fin 7)) ∈ H :=
    Subgroup.subset_closure (Or.inr (Subgroup.subset_closure (by simp [gPS])))
  have hp2 : (swap 0 1 * swap 1 2 * swap 2 3 * swap 3 6) *
      (swap 0 1 * swap 1 2 * swap 2 3 * swap 3 6) ∈ H := H.mul_mem hp hp
  have hg : ((swap 0 1 * swap 1 4) * (swap 2 3 * swap 3 5) : Perm (Fin 7)) ∈ H :=
    Subgroup.subset_closure (Or.inl (Subgroup.subset_closure (by simp [gPc])))
  have hD1 : (swap 0 1 * swap 1 2 * swap 2 3 * swap 4 5 : Perm (Fin 7)) ∈ H :=
    Subgroup.subset_closure (Or.inl (Subgroup.subset_closure (by simp [gPc, gD])))
  have hD2 : (swap 0 2 * swap 4 5 : Perm (Fin 7)) ∈ H :=
    Subgroup.subset_closure (Or.inl (Subgroup.subset_closure (by simp [gPc, gD])))
  have h012 : (swap 0 1 * swap 1 2 : Perm (Fin 7)) ∈ H :=
    Subgroup.subset_closure (Or.inr ((mem_fourPS _).2 (by decide +kernel)))
  refine alternatingGroup_le_of_orbit H ⟨_, h012, isThreeCycle_four012⟩ ?_
  intro x
  fin_cases x
  · exact ⟨_, hp, by decide⟩
  · exact ⟨_, hp2, by decide⟩
  · exact ⟨_, H.mul_mem hD2 hp, by decide⟩
  · exact ⟨_, H.mul_mem hp (H.mul_mem hD2 hp), by decide⟩
  · exact ⟨_, H.mul_mem hg hp2, by decide⟩
  · exact ⟨_, H.mul_mem hD1 (H.mul_mem hg hp2), by decide⟩
  · exact ⟨1, H.one_mem, by decide⟩

private theorem fourA5_le_fourPS : fourA5 ≤ fourPS := by
  refine (Subgroup.closure_le _).2 fun g hg => ?_
  simp only [Set.mem_setOf_eq, gA5, List.mem_cons, List.mem_singleton, List.not_mem_nil,
    or_false] at hg
  rcases hg with rfl | rfl
  · exact (mem_fourPS _).2 (by decide +kernel)
  · exact Subgroup.subset_closure (by simp [gPS])

private theorem fourPS_le_sup : fourPS ≤ fourA5 ⊔ fourD := by
  refine (Subgroup.closure_le _).2 fun g hg => ?_
  simp only [Set.mem_setOf_eq] at hg
  rw [gPS, List.mem_append] at hg
  rcases hg with hg | hg
  · exact (le_sup_right : fourD ≤ fourA5 ⊔ fourD) (Subgroup.subset_closure hg)
  · rw [List.mem_singleton] at hg
    subst g
    exact (le_sup_left : fourA5 ≤ fourA5 ⊔ fourD)
      (Subgroup.subset_closure (by simp [gA5]))

theorem fourPS_eq : fourPS = fourA5 ⊔ fourD :=
  le_antisymm fourPS_le_sup (sup_le fourA5_le_fourPS fourD_le_fourPS)

theorem fourD_le_normalizer_fourA5 :
    fourD ≤ Subgroup.normalizer (fourA5 : Set (Perm (Fin 7))) := by
  refine (Subgroup.closure_le _).2 fun d hd => ?_
  have hd' : d = swap 0 1 * swap 1 2 * swap 2 3 * swap 4 5 ∨
      d = swap 0 2 * swap 4 5 := by
    simpa [gD, List.mem_cons, List.not_mem_nil, or_false] using hd
  have hle : fourA5.map (MulAut.conj d).toMonoidHom ≤ fourA5 := by
    rcases hd' with rfl | rfl
    · rw [fourA5, MonoidHom.map_closure]
      refine (Subgroup.closure_le _).2 fun x hx => ?_
      obtain ⟨a, ha, rfl⟩ := hx
      simp only [gA5, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · exact (mem_fourA5 _).2 (by decide +kernel)
      · exact (mem_fourA5 _).2 (by decide +kernel)
    · rw [fourA5, MonoidHom.map_closure]
      refine (Subgroup.closure_le _).2 fun x hx => ?_
      obtain ⟨a, ha, rfl⟩ := hx
      simp only [gA5, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · exact (mem_fourA5 _).2 (by decide +kernel)
      · exact (mem_fourA5 _).2 (by decide +kernel)
  have hcard : Nat.card (fourA5.map (MulAut.conj d).toMonoidHom) = Nat.card fourA5 :=
    Subgroup.card_map_of_injective (K := fourA5) (MulAut.conj d).injective
  exact (Subgroup.mem_normalizer_iff_map_conj_eq).2
    (Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard.symm))

private def fiveEmb : Fin 5 ≃ {i : Fin 7 // (i : ℕ) < 5} :=
  Fin.castLEquiv (by norm_num : 5 ≤ 7)

private def extendFive : Perm (Fin 5) →* Perm (Fin 7) :=
  (MulAut.conj (swap 4 6)).toMonoidHom.comp
    ((Equiv.Perm.ofSubtype (p := fun i : Fin 7 => (i : ℕ) < 5)).comp
      fiveEmb.permCongrHom.toMonoidHom)

private theorem extendFive_injective : Function.Injective extendFive :=
  (MulAut.conj (swap 4 6)).injective.comp
    (Equiv.Perm.ofSubtype_injective.comp fiveEmb.permCongrHom.injective)

private theorem extendFive_cycle3 :
    extendFive (swap 0 1 * swap 1 2) = swap 0 1 * swap 1 2 := by
  decide +kernel

private theorem extendFive_cycle5 :
    extendFive (swap 0 1 * swap 1 2 * swap 2 3 * swap 3 4) =
      swap 0 1 * swap 1 2 * swap 2 3 * swap 3 6 := by
  decide +kernel

private theorem fourA5_le_map :
    fourA5 ≤ (alternatingGroup (Fin 5)).map extendFive := by
  refine (Subgroup.closure_le _).2 fun g hg => ?_
  simp only [Set.mem_setOf_eq, gA5, List.mem_cons, List.mem_singleton, List.not_mem_nil,
    or_false] at hg
  rcases hg with rfl | rfl
  · rw [← extendFive_cycle3]
    exact Subgroup.mem_map_of_mem extendFive (by
      rw [mem_alternatingGroup]
      simp [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap])
  · rw [← extendFive_cycle5]
    exact Subgroup.mem_map_of_mem extendFive (by
      rw [mem_alternatingGroup]
      simp [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap])

private theorem fourA5_eq_map :
    fourA5 = (alternatingGroup (Fin 5)).map extendFive := by
  refine Subgroup.eq_of_le_of_card_ge fourA5_le_map ?_
  rw [Subgroup.card_map_of_injective extendFive_injective, card_fourA5,
    nat_card_alternatingGroup]
  norm_num

theorem nonempty_fourA5_equiv :
    Nonempty (↥fourA5 ≃* alternatingGroup (Fin 5)) := by
  refine ⟨((Subgroup.equivMapOfInjective (alternatingGroup (Fin 5)) extendFive
    extendFive_injective).trans (MulEquiv.subgroupCongr fourA5_eq_map.symm)).symm⟩

private theorem fourPa_six : ∀ c ∈ LPa, dig c 6 = 6 := fun c hc =>
  Nat.eq_of_beq_eq_true (allK_iff.1 six_LPa c hc)

private theorem fourPS_six_mem_fourPa : ∀ c ∈ LPS, dig c 6 = 6 → c ∈ LPa := by
  intro c hc h6
  have h : (!Nat.beq (dig c 6) 6 || CFSG.Permutation.FinPack.memK c LPa) = true :=
    allK_iff.1 six_LPS c hc
  rw [Bool.or_eq_true] at h
  rcases h with h | h
  · rw [h6] at h
    exact absurd h (by decide)
  · exact memK_iff.1 h

private theorem mem_fourPa_iff_six {g : Perm (Fin 7)} (hg : g ∈ fourPS) :
    g ∈ fourPa ↔ g 6 = 6 := by
  constructor
  · intro h
    have h' := fourPa_six _ ((mem_fourPa g).1 h)
    rw [dig_enc g 6 (by norm_num)] at h'
    exact Fin.ext h'
  · intro h
    refine (mem_fourPa g).2 (fourPS_six_mem_fourPa _ ((mem_fourPS g).1 hg) ?_)
    rw [dig_enc g 6 (by norm_num)]
    simpa using congrArg Fin.val h

private def r1 : Perm (Fin 7) := swap 3 6 * swap 4 5

private def r2 : Perm (Fin 7) := swap 2 3 * swap 3 6

private theorem enc_r1 : enc r1 = 941192 := by decide +kernel
private theorem enc_r2 : enc r2 = 707784 := by decide +kernel

private theorem fourD_mem_of_code {c : ℕ} (hc : c ∈ LD) :
    ∃ x ∈ fourD, enc x = c :=
  exists_of_mem_reachL (S := {σ | σ ∈ gD}) (gs := gsD) (by
    intro g hg
    rw [← hgD] at hg
    obtain ⟨s, hs, hse⟩ := List.mem_map.1 hg
    exact ⟨s, hs, hse⟩) reach_LD c hc

private theorem fourPS_le_closure_rep1 :
    fourPS ≤ Subgroup.closure (insert r1 (fourD : Set (Perm (Fin 7)))) := by
  set H := Subgroup.closure (insert r1 (fourD : Set (Perm (Fin 7))))
  have hD : fourD ≤ H := fun x hx => Subgroup.subset_closure (Set.mem_insert_of_mem _ hx)
  have hgen : (swap 0 1 * swap 1 2 * swap 2 3 * swap 3 6 : Perm (Fin 7)) ∈ H := by
    have hS : ∀ s : Perm (Fin 7),
        s ∈ insert r1 {σ : Perm (Fin 7) | σ ∈ gD} ↔ s ∈ gD ++ [r1] := by
      intro s
      simp only [Set.mem_insert_iff, Set.mem_setOf_eq, List.mem_append, List.mem_singleton]
      tauto
    have hcode : enc (swap 0 1 * swap 1 2 * swap 2 3 * swap 3 6 : Perm (Fin 7)) ∈ LR1 := by
      decide +kernel
    have hgs : (gD ++ [r1]).map enc = gsD ++ [941192] := by
      rw [List.map_append, hgD]
      simp [enc_r1]
    have hmem := (mem_closure_iff_reachL (gD ++ [r1]) hS (gsD ++ [941192]) hgs LR1 id_LR1
      cl_LR1 reach_LR1 (swap 0 1 * swap 1 2 * swap 2 3 * swap 3 6)).2 hcode
    have hle : Subgroup.closure (insert r1 {σ : Perm (Fin 7) | σ ∈ gD}) ≤ H := by
      refine Subgroup.closure_mono ?_
      intro x hx
      rcases Set.mem_insert_iff.1 hx with rfl | hx
      · exact Set.mem_insert_iff.2 (Or.inl rfl)
      · exact Set.mem_insert_iff.2 (Or.inr (Subgroup.subset_closure hx))
    exact hle hmem
  refine (Subgroup.closure_le _).2 fun g hg => ?_
  simp only [Set.mem_setOf_eq] at hg
  rw [gPS, List.mem_append] at hg
  rcases hg with hg | hg
  · exact hD (Subgroup.subset_closure hg)
  · rw [List.mem_singleton] at hg
    subst g
    exact hgen

private theorem fourPS_le_closure_rep2 :
    fourPS ≤ Subgroup.closure (insert r2 (fourD : Set (Perm (Fin 7)))) := by
  set H := Subgroup.closure (insert r2 (fourD : Set (Perm (Fin 7))))
  have hD : fourD ≤ H := fun x hx => Subgroup.subset_closure (Set.mem_insert_of_mem _ hx)
  have hgen : (swap 0 1 * swap 1 2 * swap 2 3 * swap 3 6 : Perm (Fin 7)) ∈ H := by
    have hS : ∀ s : Perm (Fin 7),
        s ∈ insert r2 {σ : Perm (Fin 7) | σ ∈ gD} ↔ s ∈ gD ++ [r2] := by
      intro s
      simp only [Set.mem_insert_iff, Set.mem_setOf_eq, List.mem_append, List.mem_singleton]
      tauto
    have hcode : enc (swap 0 1 * swap 1 2 * swap 2 3 * swap 3 6 : Perm (Fin 7)) ∈ LR2 := by
      decide +kernel
    have hgs : (gD ++ [r2]).map enc = gsD ++ [707784] := by
      rw [List.map_append, hgD]
      simp [enc_r2]
    have hmem := (mem_closure_iff_reachL (gD ++ [r2]) hS (gsD ++ [707784]) hgs LR2 id_LR2
      cl_LR2 reach_LR2 (swap 0 1 * swap 1 2 * swap 2 3 * swap 3 6)).2 hcode
    have hle : Subgroup.closure (insert r2 {σ : Perm (Fin 7) | σ ∈ gD}) ≤ H := by
      refine Subgroup.closure_mono ?_
      intro x hx
      rcases Set.mem_insert_iff.1 hx with rfl | hx
      · exact Set.mem_insert_iff.2 (Or.inl rfl)
      · exact Set.mem_insert_iff.2 (Or.inr (Subgroup.subset_closure hx))
    exact hle hmem
  refine (Subgroup.closure_le _).2 fun g hg => ?_
  simp only [Set.mem_setOf_eq] at hg
  rw [gPS, List.mem_append] at hg
  rcases hg with hg | hg
  · exact hD (Subgroup.subset_closure hg)
  · rw [List.mem_singleton] at hg
    subst g
    exact hgen

private theorem fourPS_double_coset_moving {g : Perm (Fin 7)} (hg : g ∈ fourPS)
    (hg6 : g 6 ≠ 6) :
    (∃ a ∈ fourD, ∃ b ∈ fourD, g = a * r1 * b) ∨
      (∃ a ∈ fourD, ∃ b ∈ fourD, g = a * r2 * b) := by
  have hcover : ∀ c ∈ LPS, dig c 6 ≠ 6 →
      (∃ a ∈ LD, ∃ b ∈ LD, c = mulC (mulC a 941192) b) ∨
      (∃ a ∈ LD, ∃ b ∈ LD, c = mulC (mulC a 707784) b) := by
    intro c hc h6
    have h : (Nat.beq (dig c 6) 6 ||
        CFSG.Permutation.FinPack.anyK (fun a => CFSG.Permutation.FinPack.anyK
          (fun b => Nat.beq (mulC (mulC a 941192) b) c) LD) LD ||
        CFSG.Permutation.FinPack.anyK (fun a => CFSG.Permutation.FinPack.anyK
          (fun b => Nat.beq (mulC (mulC a 707784) b) c) LD) LD) = true :=
      allK_iff.1 cover_LPS c hc
    rw [Bool.or_eq_true, Bool.or_eq_true] at h
    rcases h with (h | h) | h
    · exact absurd (Nat.eq_of_beq_eq_true h) h6
    · obtain ⟨a, ha, h⟩ := anyK_iff.1 h
      obtain ⟨b, hb, h⟩ := anyK_iff.1 h
      exact Or.inl ⟨a, ha, b, hb, (Nat.eq_of_beq_eq_true h).symm⟩
    · obtain ⟨a, ha, h⟩ := anyK_iff.1 h
      obtain ⟨b, hb, h⟩ := anyK_iff.1 h
      exact Or.inr ⟨a, ha, b, hb, (Nat.eq_of_beq_eq_true h).symm⟩
  have hdig : dig (enc g) 6 ≠ 6 := by
    rw [dig_enc g 6 (by norm_num)]
    exact fun h => hg6 (Fin.ext h)
  rcases hcover (enc g) ((mem_fourPS g).1 hg) hdig with
    ⟨a, ha, b, hb, heq⟩ | ⟨a, ha, b, hb, heq⟩
  · obtain ⟨a', ha', hainv⟩ := fourD_mem_of_code ha
    obtain ⟨b', hb', hbinv⟩ := fourD_mem_of_code hb
    refine Or.inl ⟨a', ha', b', hb', ?_⟩
    apply enc_injective
    rw [enc_mul, enc_mul, heq, hainv, hbinv, enc_r1]
  · obtain ⟨a', ha', hainv⟩ := fourD_mem_of_code ha
    obtain ⟨b', hb', hbinv⟩ := fourD_mem_of_code hb
    refine Or.inr ⟨a', ha', b', hb', ?_⟩
    apply enc_injective
    rw [enc_mul, enc_mul, heq, hainv, hbinv, enc_r2]

private theorem isMaxSubgroupIn_fourPS_fourPa : IsMaxSubgroupIn fourPS fourPa := by
  have hPa_lt : fourPa < fourPS := by
    refine lt_of_le_of_ne fourPa_le_fourPS ?_
    intro hle
    have hgen : (swap 0 1 * swap 1 2 * swap 2 3 * swap 3 6 : Perm (Fin 7)) ∈ fourPa :=
      le_of_eq hle.symm (Subgroup.subset_closure (by simp [gPS]))
    have h6 : (swap 0 1 * swap 1 2 * swap 2 3 * swap 3 6 : Perm (Fin 7)) 6 = 6 :=
      (mem_fourPa_iff_six (Subgroup.subset_closure (by simp [gPS]))).1 hgen
    revert h6
    decide
  refine ⟨hPa_lt, ?_⟩
  intro K hK hKle
  have hnot : ¬ K ≤ fourPa := fun h => hK.ne (le_antisymm hK.le h)
  obtain ⟨g, hgK, hgPa⟩ := Set.not_subset.1 hnot
  have hgPS : g ∈ fourPS := hKle hgK
  have hg6 : g 6 ≠ 6 := fun h => hgPa ((mem_fourPa_iff_six hgPS).2 h)
  rcases fourPS_double_coset_moving hgPS hg6 with ⟨a, ha, b, hb, hg_eq⟩ |
    ⟨a, ha, b, hb, hg_eq⟩
  · have haK : a ∈ K := hK.le (fourD_le_fourPa ha)
    have hbK : b ∈ K := hK.le (fourD_le_fourPa hb)
    have hrK : r1 ∈ K := by
      have h : a⁻¹ * g * b⁻¹ ∈ K :=
        K.mul_mem (K.mul_mem (K.inv_mem haK) hgK) (K.inv_mem hbK)
      have hr : a⁻¹ * g * b⁻¹ = r1 := by
        rw [hg_eq]
        group
      rwa [hr] at h
    have hclosure : fourPS ≤ Subgroup.closure (insert r1 (fourD : Set (Perm (Fin 7)))) :=
      fourPS_le_closure_rep1
    have hsub : Subgroup.closure (insert r1 (fourD : Set (Perm (Fin 7)))) ≤ K := by
      refine (Subgroup.closure_le _).2 fun x hx => ?_
      rcases Set.mem_insert_iff.1 hx with rfl | hx
      · exact hrK
      · exact hK.le (fourD_le_fourPa hx)
    exact (le_antisymm (hclosure.trans hsub) hKle).symm
  · have haK : a ∈ K := hK.le (fourD_le_fourPa ha)
    have hbK : b ∈ K := hK.le (fourD_le_fourPa hb)
    have hrK : r2 ∈ K := by
      have h : a⁻¹ * g * b⁻¹ ∈ K :=
        K.mul_mem (K.mul_mem (K.inv_mem haK) hgK) (K.inv_mem hbK)
      have hr : a⁻¹ * g * b⁻¹ = r2 := by
        rw [hg_eq]
        group
      rwa [hr] at h
    have hclosure : fourPS ≤ Subgroup.closure (insert r2 (fourD : Set (Perm (Fin 7)))) :=
      fourPS_le_closure_rep2
    have hsub : Subgroup.closure (insert r2 (fourD : Set (Perm (Fin 7)))) ≤ K := by
      refine (Subgroup.closure_le _).2 fun x hx => ?_
      rcases Set.mem_insert_iff.1 hx with rfl | hx
      · exact hrK
      · exact hK.le (fourD_le_fourPa hx)
    exact (le_antisymm (hclosure.trans hsub) hKle).symm

private theorem maxOver_fourPS_fourD : maxOver fourPS fourD = {fourPa} := by
  ext N
  constructor
  · intro hN
    obtain ⟨hNmax, hND⟩ := hN
    have hNlePa : N ≤ fourPa := by
      by_contra hnot
      obtain ⟨g, hgN, hgPa⟩ := Set.not_subset.1 hnot
      have hgPS : g ∈ fourPS := hNmax.le hgN
      have hg6 : g 6 ≠ 6 := fun h => hgPa ((mem_fourPa_iff_six hgPS).2 h)
      rcases fourPS_double_coset_moving hgPS hg6 with ⟨a, ha, b, hb, hg_eq⟩ |
        ⟨a, ha, b, hb, hg_eq⟩
      · have haN : a ∈ N := hND ha
        have hbN : b ∈ N := hND hb
        have hrN : r1 ∈ N := by
          have h : a⁻¹ * g * b⁻¹ ∈ N :=
            N.mul_mem (N.mul_mem (N.inv_mem haN) hgN) (N.inv_mem hbN)
          have hr : a⁻¹ * g * b⁻¹ = r1 := by
            rw [hg_eq]
            group
          rwa [hr] at h
        have hclosure : fourPS ≤
            Subgroup.closure (insert r1 (fourD : Set (Perm (Fin 7)))) :=
          fourPS_le_closure_rep1
        have hsub : Subgroup.closure (insert r1 (fourD : Set (Perm (Fin 7)))) ≤ N := by
          refine (Subgroup.closure_le _).2 fun x hx => ?_
          rcases Set.mem_insert_iff.1 hx with rfl | hx
          · exact hrN
          · exact hND hx
        exact (not_lt_of_ge (hclosure.trans hsub)) hNmax.1
      · have haN : a ∈ N := hND ha
        have hbN : b ∈ N := hND hb
        have hrN : r2 ∈ N := by
          have h : a⁻¹ * g * b⁻¹ ∈ N :=
            N.mul_mem (N.mul_mem (N.inv_mem haN) hgN) (N.inv_mem hbN)
          have hr : a⁻¹ * g * b⁻¹ = r2 := by
            rw [hg_eq]
            group
          rwa [hr] at h
        have hclosure : fourPS ≤
            Subgroup.closure (insert r2 (fourD : Set (Perm (Fin 7)))) :=
          fourPS_le_closure_rep2
        have hsub : Subgroup.closure (insert r2 (fourD : Set (Perm (Fin 7)))) ≤ N := by
          refine (Subgroup.closure_le _).2 fun x hx => ?_
          rcases Set.mem_insert_iff.1 hx with rfl | hx
          · exact hrN
          · exact hND hx
        exact (not_lt_of_ge (hclosure.trans hsub)) hNmax.1
    rcases lt_or_eq_of_le hNlePa with hlt | heq
    · exact absurd (hNmax.2 fourPa hlt fourPa_le_fourPS)
        (ne_of_lt isMaxSubgroupIn_fourPS_fourPa.1)
    · exact heq
  · intro hN
    rw [Set.mem_singleton_iff] at hN
    subst N
    exact ⟨isMaxSubgroupIn_fourPS_fourPa, fourD_le_fourPa⟩

private theorem fourPS_not_le_normalizer_fourD :
    ¬ fourPS ≤ Subgroup.normalizer (fourD : Set (Perm (Fin 7))) := by
  intro h
  have hp : (swap 0 1 * swap 1 2 * swap 2 3 * swap 3 6 : Perm (Fin 7)) ∈
      Subgroup.normalizer (fourD : Set (Perm (Fin 7))) :=
    h (Subgroup.subset_closure (by simp [gPS]))
  have hd1 : (swap 0 1 * swap 1 2 * swap 2 3 * swap 4 5 : Perm (Fin 7)) ∈ fourD :=
    Subgroup.subset_closure (by simp [gD])
  have hconj : (swap 0 1 * swap 1 2 * swap 2 3 * swap 3 6) *
      (swap 0 1 * swap 1 2 * swap 2 3 * swap 4 5) *
      (swap 0 1 * swap 1 2 * swap 2 3 * swap 3 6)⁻¹ ∈ fourD :=
    (Subgroup.mem_normalizer_iff.1 hp _).1 hd1
  rw [mem_fourD] at hconj
  have hcode : enc ((swap 0 1 * swap 1 2 * swap 2 3 * swap 3 6) *
      (swap 0 1 * swap 1 2 * swap 2 3 * swap 4 5) *
      (swap 0 1 * swap 1 2 * swap 2 3 * swap 3 6)⁻¹) = 416976 := by
    decide +kernel
  rw [hcode] at hconj
  revert hconj
  decide +kernel

private theorem isSylowTwoOf_fourD_fourPS : IsSylowTwoOf fourD fourPS := by
  refine ⟨fourD_le_fourPS, isPGroup_fourD, ?_⟩
  have h1 := Subgroup.card_mul_index (fourD.subgroupOf fourPS)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe fourD_le_fourPS).toEquiv,
    card_fourD, card_fourPS] at h1
  have hidx : (fourD.subgroupOf fourPS).index = 15 := by omega
  rw [hidx]
  norm_num

theorem minParabolic_fourPS : MinParabolic fourPS fourD fourPa where
  isSylow := isSylowTwoOf_fourD_fourPS
  not_normal := fourPS_not_le_normalizer_fourD
  uniqueMax := maxOver_fourPS_fourD

end CFSG.AGLEmbeddingD2.McLaughlin.A7Lift
