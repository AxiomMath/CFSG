module

public import Mathlib.GroupTheory.GroupAction.Jordan

public section

namespace GL83

open Equiv Equiv.Perm
open scoped Pointwise

section Points

variable {Ω : Type*}

theorem exists_other {S : Set Ω} (hS : 2 ≤ S.ncard) (a : Ω) : ∃ c ∈ S, c ≠ a := by
  by_contra hcon
  have hsub : S ⊆ {a} := fun c hc => by
    by_contra hne
    exact hcon ⟨c, hc, hne⟩
  have h1 := Set.ncard_le_ncard hsub
  rw [Set.ncard_singleton] at h1
  omega

theorem exists_third {S : Set Ω} (hS : 3 ≤ S.ncard) {a c : Ω} (hac : a ≠ c) :
    ∃ z ∈ S, z ≠ a ∧ z ≠ c := by
  by_contra hcon
  have hsub : S ⊆ {a, c} := fun z hz => by
    by_contra hne
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hne
    exact hcon ⟨z, hz, hne.1, hne.2⟩
  have h1 := Set.ncard_le_ncard hsub
  rw [Set.ncard_pair hac] at h1
  omega

end Points

section Cyc

variable {Ω : Type*} [DecidableEq Ω]

def cyc3 (a b c : Ω) : Perm Ω := swap a c * swap a b

theorem cyc3_apply_left {a b c : Ω} (h : a ≠ b ∧ a ≠ c ∧ b ≠ c) : cyc3 a b c a = b := by
  obtain ⟨hab, hac, hbc⟩ := h
  simp [cyc3, swap_apply_of_ne_of_ne hab.symm hbc]

theorem cyc3_apply_mid {a b c : Ω} (h : a ≠ b ∧ a ≠ c ∧ b ≠ c) : cyc3 a b c b = c := by
  obtain ⟨hab, hac, hbc⟩ := h
  simp [cyc3]

theorem cyc3_apply_right {a b c : Ω} (h : a ≠ b ∧ a ≠ c ∧ b ≠ c) : cyc3 a b c c = a := by
  obtain ⟨hab, hac, hbc⟩ := h
  simp [cyc3, swap_apply_of_ne_of_ne hac.symm hbc.symm]

theorem cyc3_apply_of_ne {a b c x : Ω} (hxa : x ≠ a) (hxb : x ≠ b) (hxc : x ≠ c) :
    cyc3 a b c x = x := by
  simp [cyc3, swap_apply_of_ne_of_ne hxa hxb, swap_apply_of_ne_of_ne hxa hxc]

end Cyc

section Main

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

@[expose] def altOn (S : Set Ω) : Subgroup (Perm Ω) :=
  alternatingGroup Ω ⊓ fixingSubgroup (Perm Ω) Sᶜ

theorem mem_altOn {S : Set Ω} {g : Perm Ω} :
    g ∈ altOn S ↔ g ∈ alternatingGroup Ω ∧ ∀ x, x ∉ S → g x = x := by
  rw [altOn, Subgroup.mem_inf, mem_fixingSubgroup_iff]
  exact and_congr_right fun _ => ⟨fun h x hx => h x hx, fun h x hx => h x hx⟩

theorem cyc3_mem_altOn {S : Set Ω} {a b c : Ω} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S)
    (h : a ≠ b ∧ a ≠ c ∧ b ≠ c) : cyc3 a b c ∈ altOn S := by
  obtain ⟨hab, hac, hbc⟩ := h
  refine mem_altOn.2 ⟨?_, fun x hx => ?_⟩
  · exact (isThreeCycle_swap_mul_swap_same hac hab hbc.symm).mem_alternatingGroup
  · exact cyc3_apply_of_ne (fun h => hx (h ▸ ha)) (fun h => hx (h ▸ hb)) (fun h => hx (h ▸ hc))

theorem isThreeCycle_cyc3 {a b c : Ω} (h : a ≠ b ∧ a ≠ c ∧ b ≠ c) : (cyc3 a b c).IsThreeCycle :=
  isThreeCycle_swap_mul_swap_same h.2.1 h.1 h.2.2.symm

section Family

variable {ι : Type*} (S : ι → Set Ω)

abbrev genAlt : Subgroup (Perm Ω) := ⨆ i, altOn (S i)

theorem altOn_le_genAlt (i : ι) : altOn (S i) ≤ genAlt S := le_iSup (fun i => altOn (S i)) i

theorem genAlt_le : genAlt S ≤ alternatingGroup Ω := iSup_le fun _ => inf_le_left

variable {S}

theorem mem_orbit_of_mem {i : ι} (hS3 : 3 ≤ (S i).ncard) {x y : Ω} (hx : x ∈ S i)
    (hy : y ∈ S i) : y ∈ MulAction.orbit (genAlt S) x := by
  by_cases hxy : x = y
  · rw [← hxy]; exact MulAction.mem_orbit_self x
  obtain ⟨z, hz, hzx, hzy⟩ := exists_third hS3 hxy
  have hd : x ≠ y ∧ x ≠ z ∧ y ≠ z := ⟨hxy, hzx.symm, hzy.symm⟩
  have hg : cyc3 x y z ∈ genAlt S := altOn_le_genAlt S i (cyc3_mem_altOn hx hy hz hd)
  exact ⟨⟨cyc3 x y z, hg⟩, cyc3_apply_left hd⟩

theorem genAlt_isPretransitive (hS3 : ∀ i, 3 ≤ (S i).ncard) (hcover : (⋃ i, S i) = Set.univ)
    (hconn : ∀ i j, Relation.ReflTransGen (fun a b => (S a ∩ S b).Nonempty) i j) :
    MulAction.IsPretransitive (genAlt S) Ω := by
  have key : ∀ i j, ∀ x ∈ S i, ∀ y ∈ S j, y ∈ MulAction.orbit (genAlt S) x := by
    intro i j x hx y hy
    induction hconn i j generalizing y with
    | refl => exact mem_orbit_of_mem (hS3 i) hx hy
    | tail _ hbc ih =>
      obtain ⟨w, hwb, hwc⟩ := hbc
      have h1 := ih w hwb
      have h2 := mem_orbit_of_mem (hS3 _) hwc hy
      rw [MulAction.orbit_eq_iff.2 h1] at h2
      exact h2
  refine ⟨fun x y => ?_⟩
  obtain ⟨i, hx⟩ := Set.mem_iUnion.1 (hcover ▸ Set.mem_univ x)
  obtain ⟨j, hy⟩ := Set.mem_iUnion.1 (hcover ▸ Set.mem_univ y)
  exact MulAction.mem_orbit_iff.1 (key i j x hx y hy)

theorem block_cyc3_mem {B : Set Ω} (hB : MulAction.IsBlock (genAlt S) B) {i : ι} {a b c : Ω}
    (ha : a ∈ S i) (hb : b ∈ S i) (hc : c ∈ S i) (h : a ≠ b ∧ a ≠ c ∧ b ≠ c) {x : Ω}
    (hxB : x ∈ B) (hgx : cyc3 a b c x ∈ B) {y : Ω} (hyB : y ∈ B) : cyc3 a b c y ∈ B := by
  have hg : cyc3 a b c ∈ genAlt S := altOn_le_genAlt S i (cyc3_mem_altOn ha hb hc h)
  have h1 : (⟨cyc3 a b c, hg⟩ : genAlt S) • B = B :=
    hB.smul_eq_of_mem (g := ⟨cyc3 a b c, hg⟩) hxB hgx
  have h2 : (⟨cyc3 a b c, hg⟩ : genAlt S) • y ∈ (⟨cyc3 a b c, hg⟩ : genAlt S) • B :=
    Set.smul_mem_smul_set hyB
  rw [h1] at h2
  exact h2

theorem eq_of_mem_inter {B : Set Ω} (hB : MulAction.IsBlock (genAlt S) B) {i : ι}
    (hnot : ¬ S i ⊆ B) {a b : Ω} (haB : a ∈ B) (haS : a ∈ S i) (hbB : b ∈ B) (hbS : b ∈ S i) :
    a = b := by
  by_contra hab
  obtain ⟨c, hcS, hcB⟩ := Set.not_subset.1 hnot
  have hca : a ≠ c := fun h => hcB (h ▸ haB)
  have hcb : c ≠ b := fun h => hcB (h ▸ hbB)
  have hd : a ≠ c ∧ a ≠ b ∧ c ≠ b := ⟨hca, hab, hcb⟩
  have h1 : cyc3 a c b b = a := cyc3_apply_right hd
  have h2 := block_cyc3_mem hB haS hcS hbS hd hbB (by rw [h1]; exact haB) haB
  rw [cyc3_apply_left hd] at h2
  exact hcB h2

theorem exists_subset_block (hS3 : ∀ i, 3 ≤ (S i).ncard) (hcover : (⋃ i, S i) = Set.univ)
    {B : Set Ω} (hB : MulAction.IsBlock (genAlt S) B) (hnot : ¬ B.Subsingleton) :
    ∃ i, S i ⊆ B := by
  by_contra hcon
  have hcon' : ∀ i, ¬ S i ⊆ B := fun i hi => hcon ⟨i, hi⟩
  obtain ⟨a, haB, b, hbB, hab⟩ := Set.not_subsingleton_iff.1 hnot
  obtain ⟨i, haS⟩ := Set.mem_iUnion.1 (hcover ▸ Set.mem_univ a)
  have hbS : b ∉ S i := fun hbS => hab (eq_of_mem_inter hB (hcon' i) haB haS hbB hbS)
  obtain ⟨c, hcS, hca⟩ := exists_other ((by omega : 2 ≤ 3).trans (hS3 i)) a
  obtain ⟨z, hzS, hza, hzc⟩ := exists_third (hS3 i) hca.symm
  have hd : a ≠ c ∧ a ≠ z ∧ c ≠ z := ⟨hca.symm, hza.symm, hzc.symm⟩
  have hgb : cyc3 a c z b = b :=
    cyc3_apply_of_ne (fun h => hbS (h ▸ haS)) (fun h => hbS (h ▸ hcS)) (fun h => hbS (h ▸ hzS))
  have h1 := block_cyc3_mem hB haS hcS hzS hd hbB (by rw [hgb]; exact hbB) haB
  rw [cyc3_apply_left hd] at h1
  exact hca (eq_of_mem_inter hB (hcon' i) h1 hcS haB haS)

theorem subset_block_of_adj (hS3 : ∀ i, 3 ≤ (S i).ncard) {B : Set Ω}
    (hB : MulAction.IsBlock (genAlt S) B) {a b : ι} (hadj : (S a ∩ S b).Nonempty)
    (hSa : S a ⊆ B) : S b ⊆ B := by
  by_contra hnot
  obtain ⟨w, hwa, hwb⟩ := hadj
  have hwB : w ∈ B := hSa hwa
  have huniq : ∀ y, y ∈ B → y ∈ S b → w = y := fun y hyB hyb =>
    eq_of_mem_inter hB hnot hwB hwb hyB hyb
  obtain ⟨u, huS, huw⟩ := exists_other ((by omega : 2 ≤ 3).trans (hS3 a)) w
  have hub : u ∉ S b := fun hub => huw (huniq u (hSa huS) hub).symm
  obtain ⟨c, hcS, hcw⟩ := exists_other ((by omega : 2 ≤ 3).trans (hS3 b)) w
  obtain ⟨z, hzS, hzw, hzc⟩ := exists_third (hS3 b) hcw.symm
  have hd : w ≠ c ∧ w ≠ z ∧ c ≠ z := ⟨hcw.symm, hzw.symm, hzc.symm⟩
  have hgu : cyc3 w c z u = u :=
    cyc3_apply_of_ne (fun h => hub (h ▸ hwb)) (fun h => hub (h ▸ hcS)) (fun h => hub (h ▸ hzS))
  have h1 := block_cyc3_mem hB hwb hcS hzS hd (hSa huS) (by rw [hgu]; exact hSa huS) hwB
  rw [cyc3_apply_left hd] at h1
  exact hcw (huniq c h1 hcS).symm

theorem isTrivialBlock_genAlt (hS3 : ∀ i, 3 ≤ (S i).ncard) (hcover : (⋃ i, S i) = Set.univ)
    (hconn : ∀ i j, Relation.ReflTransGen (fun a b => (S a ∩ S b).Nonempty) i j) {B : Set Ω}
    (hB : MulAction.IsBlock (genAlt S) B) : MulAction.IsTrivialBlock B := by
  by_cases hsub : B.Subsingleton
  · exact Or.inl hsub
  right
  obtain ⟨i₀, hi₀⟩ := exists_subset_block hS3 hcover hB hsub
  have hall : ∀ j, S j ⊆ B := fun j => by
    induction hconn i₀ j with
    | refl => exact hi₀
    | tail _ hbc ih => exact subset_block_of_adj hS3 hB hbc ih
  ext x
  simp only [Set.mem_univ, iff_true]
  obtain ⟨j, hj⟩ := Set.mem_iUnion.1 (hcover ▸ Set.mem_univ x)
  exact hall j hj

theorem genAlt_isPreprimitive (hS3 : ∀ i, 3 ≤ (S i).ncard) (hcover : (⋃ i, S i) = Set.univ)
    (hconn : ∀ i j, Relation.ReflTransGen (fun a b => (S a ∩ S b).Nonempty) i j) :
    MulAction.IsPreprimitive (genAlt S) Ω := by
  have := genAlt_isPretransitive hS3 hcover hconn
  exact ⟨fun {_} hB => isTrivialBlock_genAlt hS3 hcover hconn hB⟩

theorem iSup_altOn_eq_alternatingGroup [Nonempty Ω] (hS3 : ∀ i, 3 ≤ (S i).ncard)
    (hcover : (⋃ i, S i) = Set.univ)
    (hconn : ∀ i j, Relation.ReflTransGen (fun a b => (S a ∩ S b).Nonempty) i j) :
    (⨆ i, altOn (S i)) = alternatingGroup Ω := by
  refine le_antisymm (genAlt_le S) ?_
  have := genAlt_isPreprimitive hS3 hcover hconn
  obtain ⟨x₀⟩ := ‹Nonempty Ω›
  obtain ⟨i₀, hx₀⟩ := Set.mem_iUnion.1 (hcover ▸ Set.mem_univ x₀)
  obtain ⟨b, hb, hbx⟩ := exists_other ((by omega : 2 ≤ 3).trans (hS3 i₀)) x₀
  obtain ⟨z, hz, hzx, hzb⟩ := exists_third (hS3 i₀) hbx.symm
  have hd : x₀ ≠ b ∧ x₀ ≠ z ∧ b ≠ z := ⟨hbx.symm, hzx.symm, hzb.symm⟩
  exact alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem this (isThreeCycle_cyc3 hd)
    (altOn_le_genAlt S i₀ (cyc3_mem_altOn hx₀ hb hz hd))

end Family

theorem I_23_1_1_proved :
    ∀ (Ω : Type) [Fintype Ω] [DecidableEq Ω], 5 ≤ Fintype.card Ω →
      ∀ (ι : Type) [Finite ι] (S : ι → Set Ω), (⋃ i, S i) = Set.univ → (∀ i, 3 ≤ (S i).ncard) →
        (∀ i j, Relation.ReflTransGen (fun a b => (S a ∩ S b).Nonempty) i j) →
          (⨆ i, altOn (S i)) = alternatingGroup Ω := by
  intro Ω _ _ hn ι _ S hcover hS3 hconn
  have : Nonempty Ω := Fintype.card_pos_iff.1 (by omega)
  exact iSup_altOn_eq_alternatingGroup hS3 hcover hconn

end Main

end GL83
