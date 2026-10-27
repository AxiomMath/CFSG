module

public import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.GroupTheory.AltCore

open Equiv Equiv.Perm Subgroup

variable {α : Type} [Fintype α] [DecidableEq α]

@[expose] def setStab (O : Set α) : Subgroup (Perm α) where
  carrier := {g | ∀ x, g x ∈ O ↔ x ∈ O}
  mul_mem' {a b} ha hb x := by
    simp only [Set.mem_setOf_eq, Perm.mul_apply] at *
    rw [ha, hb]
  one_mem' _ := Iff.rfl
  inv_mem' {a} ha x := by
    simp only [Set.mem_setOf_eq] at *
    have := ha (a⁻¹ x)
    rwa [show a (a⁻¹ x) = x from a.apply_symm_apply x, Iff.comm] at this

omit [Fintype α] [DecidableEq α] in
theorem mem_setStab {O : Set α} {g : Perm α} : g ∈ setStab O ↔ ∀ x, g x ∈ O ↔ x ∈ O :=
  Iff.rfl

omit [Fintype α] [DecidableEq α] in
theorem setStab_compl (O : Set α) : setStab Oᶜ = setStab O := by
  ext g
  simp only [mem_setStab, Set.mem_compl_iff, not_iff_not]

variable (O : Set α) [DecidablePred (· ∈ O)]

noncomputable def restrHom : setStab O →* Perm α where
  toFun g := ofSubtype (g.1.subtypePerm g.2)
  map_one' := by
    rw [show (1 : setStab O).1.subtypePerm (1 : setStab O).2 = 1 from rfl, map_one]
  map_mul' a b := by
    rw [← map_mul]
    rfl

variable {O}

omit [Fintype α] [DecidableEq α] in
theorem restrHom_apply_of_mem (g : setStab O) {x : α} (hx : x ∈ O) :
    restrHom O g x = (g : Perm α) x :=
  ofSubtype_apply_of_mem _ hx

omit [Fintype α] [DecidableEq α] in
theorem restrHom_apply_of_not_mem (g : setStab O) {x : α} (hx : x ∉ O) : restrHom O g x = x :=
  ofSubtype_apply_of_not_mem _ hx

omit [Fintype α] [DecidableEq α] in
theorem restrHom_mul_restrHom_compl (g : setStab O) :
    restrHom O g * restrHom Oᶜ ⟨g.1, (setStab_compl O).symm ▸ g.2⟩ = g := by
  ext x
  rw [Perm.mul_apply]
  by_cases hx : x ∈ O
  · rw [restrHom_apply_of_not_mem (O := Oᶜ) _ (by simpa using hx), restrHom_apply_of_mem g hx]
  · rw [restrHom_apply_of_mem (O := Oᶜ) _ hx,
      restrHom_apply_of_not_mem g (fun h => hx ((g.2 x).1 h))]

omit [Fintype α] [DecidableEq α] in
theorem restrHom_commute_compl (a : setStab O) (b : setStab Oᶜ) :
    Commute (restrHom O a) (restrHom Oᶜ b) := by
  ext x
  simp only [Perm.mul_apply]
  by_cases hx : x ∈ O
  · have hax : (a : Perm α) x ∈ O := (a.2 x).2 hx
    rw [restrHom_apply_of_not_mem (O := Oᶜ) b (by simpa using hx), restrHom_apply_of_mem a hx,
      restrHom_apply_of_not_mem (O := Oᶜ) b (by simpa using hax)]
  · have hx' : x ∈ Oᶜ := hx
    have hbx : (b : Perm α) x ∉ O := (b.2 x).2 hx'
    rw [restrHom_apply_of_not_mem a hx, restrHom_apply_of_mem (O := Oᶜ) b hx',
      restrHom_apply_of_not_mem a hbx]

omit [Fintype α] [DecidableEq α] in
theorem conj_restrHom (n g : setStab O) :
    (n : Perm α) * restrHom O g * (n : Perm α)⁻¹ = restrHom O (n * g * n⁻¹) := by
  ext x
  simp only [Perm.mul_apply]
  by_cases hx : x ∈ O
  · have hnx : (n : Perm α)⁻¹ x ∈ O := ((n⁻¹ : setStab O).2 x).2 hx
    rw [restrHom_apply_of_mem g hnx, restrHom_apply_of_mem _ hx]
    rfl
  · have hnx : (n : Perm α)⁻¹ x ∉ O := fun h => hx (((n⁻¹ : setStab O).2 x).1 h)
    rw [restrHom_apply_of_not_mem g hnx, restrHom_apply_of_not_mem _ hx]
    exact (n : Perm α).apply_symm_apply x

theorem le_normalizer_of_conj_mem {G : Type*} [Group G] {N D : Subgroup G}
    (h : ∀ n ∈ N, ∀ d ∈ D, n * d * n⁻¹ ∈ D) : N ≤ normalizer (D : Set G) := by
  intro n hn
  refine mem_normalizer_iff.mpr fun d => ⟨h n hn d, fun hd => ?_⟩
  have := h n⁻¹ (inv_mem hn) _ hd
  rwa [show n⁻¹ * (n * d * n⁻¹) * n⁻¹⁻¹ = d by group] at this

theorem le_of_inf_normalizer_le_of_isPGroup {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {H D : Subgroup G} (hD : IsPGroup p D) (hHD : H ≤ D)
    (hN : D ⊓ normalizer (H : Set G) ≤ H) : D ≤ H := by
  have : Group.IsNilpotent D := hD.isNilpotent
  have hnc := normalizerCondition_iff_only_full_group_self_normalizing.mp
    (normalizerCondition_of_isNilpotent (G := D))
  have hself : normalizer ((H.subgroupOf D : Subgroup D) : Set D) = H.subgroupOf D := by
    refine le_antisymm (fun d hd => ?_) le_normalizer
    rw [mem_subgroupOf]
    refine hN ⟨d.2, mem_normalizer_iff.mpr fun g => ⟨fun hg => ?_, fun hg => ?_⟩⟩
    · have := (mem_normalizer_iff.mp hd ⟨g, hHD hg⟩).mp (by rwa [mem_subgroupOf])
      rwa [mem_subgroupOf] at this
    · have hgD : g ∈ D := by
        have := mul_mem (mul_mem (inv_mem d.2) (hHD hg)) d.2
        rwa [show (d : G)⁻¹ * ((d : G) * g * (d : G)⁻¹) * d = g by group] at this
      have := (mem_normalizer_iff.mp hd ⟨g, hgD⟩).mpr (by rwa [mem_subgroupOf])
      rwa [mem_subgroupOf] at this
  have htop := hnc _ hself
  intro x hx
  have : (⟨x, hx⟩ : D) ∈ H.subgroupOf D := htop ▸ mem_top _
  rwa [mem_subgroupOf] at this

variable (O)

@[expose] noncomputable def restrSub (H : Subgroup (Perm α)) : Subgroup (Perm α) :=
  (H.subgroupOf (setStab O)).map (restrHom O)

variable {O}

omit [Fintype α] [DecidableEq α] in
theorem restrHom_mem_restrSub {H : Subgroup (Perm α)} {h : setStab O} (hh : (h : Perm α) ∈ H) :
    restrHom O h ∈ restrSub O H :=
  ⟨h, mem_subgroupOf.mpr hh, rfl⟩

omit [Fintype α] [DecidableEq α] in
theorem isPGroup_restrSub {p : ℕ} {H : Subgroup (Perm α)} (hH : IsPGroup p H) :
    IsPGroup p (restrSub O H) :=
  (hH.comap_subtype (K := setStab O)).map _

omit [Fintype α] [DecidableEq α] in
theorem conj_mem_restrSub {H : Subgroup (Perm α)} {n : Perm α} (hnH : n ∈ normalizer (H : Set _))
    (hnO : n ∈ setStab O) {d : Perm α} (hd : d ∈ restrSub O H) : n * d * n⁻¹ ∈ restrSub O H := by
  obtain ⟨g, hg, rfl⟩ := hd
  have hg' : (g : Perm α) ∈ H := mem_subgroupOf.mp hg
  have e := conj_restrHom ⟨n, hnO⟩ g
  simp only at e
  rw [e]
  refine restrHom_mem_restrSub ?_
  exact (mem_normalizer_iff.mp hnH _).mp hg'

omit [Fintype α] [DecidableEq α] in
private theorem map_conj_le_restrSub {H : Subgroup (Perm α)} {n : Perm α}
    (hnH : n ∈ normalizer (H : Set _)) (hnO : n ∈ setStab O) :
    (restrSub O H).map (MulAut.conj n).toMonoidHom ≤ restrSub O H := by
  rintro _ ⟨d, hd, rfl⟩
  exact conj_mem_restrSub hnH hnO hd

omit [Fintype α] [DecidableEq α] in
private theorem restrSub_le_normalizer_compl (H : Subgroup (Perm α)) :
    restrSub O H ≤ normalizer (restrSub Oᶜ H : Set (Perm α)) := by
  refine le_normalizer_of_conj_mem fun n hn d hd => ?_
  obtain ⟨a, -, rfl⟩ := hn
  obtain ⟨b, hb, rfl⟩ := hd
  rw [(restrHom_commute_compl a b).eq, mul_assoc, mul_inv_cancel, mul_one]
  exact ⟨b, hb, rfl⟩

omit [DecidableEq α] in
theorem restrHom_mem {p : ℕ} [Fact p.Prime] {H : Subgroup (Perm α)} (hH : IsPGroup p H)
    (hrad : ∀ P : Subgroup (Perm α), IsPGroup p P → P ≤ normalizer (H : Set (Perm α)) →
      normalizer (H : Set (Perm α)) ≤ normalizer (P : Set (Perm α)) → P ≤ H)
    (hO : normalizer (H : Set (Perm α)) ≤ setStab O) {h : Perm α} (hh : h ∈ H) :
    restrHom O ⟨h, hO (le_normalizer hh)⟩ ∈ H := by
  set N := normalizer (H : Set (Perm α))
  have hOc : N ≤ setStab Oᶜ := (setStab_compl O).symm ▸ hO
  set D := restrSub O H ⊔ restrSub Oᶜ H with hDdef
  have hDp : IsPGroup p D := (isPGroup_restrSub hH).to_sup_of_normal_right'
    (isPGroup_restrSub hH) (restrSub_le_normalizer_compl H)
  have hHD : H ≤ D := fun x hx => by
    have e : restrHom O ⟨x, hO (le_normalizer hx)⟩ *
        restrHom Oᶜ ⟨x, (setStab_compl O).symm ▸ hO (le_normalizer hx)⟩ = x :=
      restrHom_mul_restrHom_compl (⟨x, hO (le_normalizer hx)⟩ : setStab O)
    rw [← e]
    exact mul_mem (mem_sup_left (restrHom_mem_restrSub hx))
      (mem_sup_right (restrHom_mem_restrSub (O := Oᶜ) hx))
  have hND : ∀ n ∈ N, ∀ d ∈ D, n * d * n⁻¹ ∈ D := fun n hn d hd => by
    have hmap : D.map (MulAut.conj n).toMonoidHom ≤ D := by
      rw [hDdef, Subgroup.map_sup]
      exact sup_le_sup (map_conj_le_restrSub hn (hO hn)) (map_conj_le_restrSub hn (hOc hn))
    exact hmap ⟨d, hd, rfl⟩
  have hNP : N ≤ normalizer ((D ⊓ N : Subgroup (Perm α)) : Set (Perm α)) :=
    le_normalizer_of_conj_mem fun n hn d hd => mem_inf.mpr
      ⟨hND n hn d (mem_inf.mp hd).1, mul_mem (mul_mem hn (mem_inf.mp hd).2) (inv_mem hn)⟩
  have hPH := hrad (D ⊓ N) (hDp.to_le inf_le_left) inf_le_right hNP
  exact le_of_inf_normalizer_le_of_isPGroup hDp hHD hPH
    (mem_sup_left (restrHom_mem_restrSub hh))

end CFSG.GroupTheory.AltCore
