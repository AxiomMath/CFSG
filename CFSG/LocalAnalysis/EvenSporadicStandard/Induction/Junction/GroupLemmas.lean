module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.H35Normal
public import CFSG.GroupTheory.SubnormalJoin
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Conj
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Relations

public section

namespace CFSG.EvenSporadicStandard.Induction.Junction

open Subgroup CFSG.EvenSporadicStandard.Induction CFSG.EvenSporadicStandard.Solomon78
open scoped commutatorElement

variable {G : Type} [Group G]

theorem le_normalizer_of_commutator_le {S T : Subgroup G} (h : ⁅S, T⁆ ≤ S ⊓ T) :
    S ≤ normalizer (T : Set G) := by
  have key : ∀ y ∈ S, ∀ t ∈ T, y * t * y⁻¹ ∈ T := fun y hy t ht => by
    have h1 : y * t * y⁻¹ * t⁻¹ ∈ T := (h (Subgroup.commutator_mem_commutator hy ht)).2
    have : y * t * y⁻¹ = (y * t * y⁻¹ * t⁻¹) * t := by group
    rw [this]
    exact mul_mem h1 ht
  intro s hs
  rw [Subgroup.mem_normalizer_iff]
  intro t
  constructor
  · exact key s hs t
  · intro ht
    have := key s⁻¹ (S.inv_mem hs) _ ht
    simpa [mul_assoc] using this

theorem map_conj_le_conjClosure {L S : Subgroup G} {g : G} (hg : g ∈ S) :
    L.map (MulAut.conj g).toMonoidHom ≤ conjClosure L S :=
  le_iSup₂_of_le g hg le_rfl

theorem le_conjClosure (L S : Subgroup G) : L ≤ conjClosure L S := by
  intro x hx
  exact map_conj_le_conjClosure S.one_mem ⟨x, hx, by simp⟩

theorem conjClosure_mono {L L' S S' : Subgroup G} (hL : L ≤ L') (hS : S ≤ S') :
    conjClosure L S ≤ conjClosure L' S' :=
  iSup₂_le fun _ hg => (Subgroup.map_mono hL).trans (map_conj_le_conjClosure (hS hg))

theorem conjClosure_le_of_le_normalizer {L Q S : Subgroup G} (hL : L ≤ Q)
    (hS : S ≤ normalizer (Q : Set G)) : conjClosure L S ≤ Q := by
  refine iSup₂_le fun g hg => ?_
  rintro _ ⟨x, hx, rfl⟩
  exact (Subgroup.mem_normalizer_iff.1 (hS hg) x).1 (hL hx)

theorem le_normalizer_conjClosure (L S : Subgroup G) :
    S ≤ normalizer (conjClosure L S : Set G) := by
  have key : ∀ h ∈ S, (conjClosure L S).map (MulAut.conj h).toMonoidHom ≤ conjClosure L S := by
    intro h hh
    rw [conjClosure, Subgroup.map_iSup]
    refine iSup_le fun g => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hg => ?_
    rw [map_conj_map_conj L g h]
    exact map_conj_le_conjClosure (S.mul_mem hh hg)
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact key h hh ⟨x, hx, rfl⟩
  · intro hx
    have := key h⁻¹ (S.inv_mem hh) ⟨_, hx, rfl⟩
    simpa [mul_assoc] using this

theorem commutator_conjClosure {L S : Subgroup G} (hL : ⁅L, L⁆ = L) :
    ⁅conjClosure L S, conjClosure L S⁆ = conjClosure L S := by
  refine le_antisymm (commutator_le.2 fun a ha b hb => ?_) ?_
  · exact (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb)
      (Subgroup.inv_mem _ ha)) (Subgroup.inv_mem _ hb))
  · refine iSup₂_le fun g hg => ?_
    have h1 : (⁅L, L⁆).map (MulAut.conj g).toMonoidHom = L.map (MulAut.conj g).toMonoidHom := by
      rw [hL]
    rw [← h1, Subgroup.map_commutator]
    exact Subgroup.commutator_mono (map_conj_le_conjClosure hg) (map_conj_le_conjClosure hg)

theorem commutator_sup_of_perfect {A B : Subgroup G} (hA : ⁅A, A⁆ = A) (hB : ⁅B, B⁆ = B) :
    ⁅A ⊔ B, A ⊔ B⁆ = A ⊔ B := by
  refine le_antisymm (commutator_le.2 fun a ha b hb => ?_) (sup_le ?_ ?_)
  · exact (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb)
      (Subgroup.inv_mem _ ha)) (Subgroup.inv_mem _ hb))
  · calc A = ⁅A, A⁆ := hA.symm
      _ ≤ ⁅A ⊔ B, A ⊔ B⁆ := Subgroup.commutator_mono le_sup_left le_sup_left
  · calc B = ⁅B, B⁆ := hB.symm
      _ ≤ ⁅A ⊔ B, A ⊔ B⁆ := Subgroup.commutator_mono le_sup_right le_sup_right

theorem commutator_map_of_perfect {A B : Type*} [Group A] [Group B] (f : A →* B) {P : Subgroup A}
    (hP : ⁅P, P⁆ = P) : ⁅P.map f, P.map f⁆ = P.map f := by
  rw [← Subgroup.map_commutator, hP]

theorem le_layerIn_of_isCompIn {Z X : Subgroup G} (h : IsCompIn Z X) : Z ≤ layerIn X :=
  le_sSup h

theorem layerIn_le_iff {X Q : Subgroup G} :
    layerIn X ≤ Q ↔ ∀ Z : Subgroup G, IsCompIn Z X → Z ≤ Q :=
  sSup_le_iff.trans ⟨fun h Z hZ => h Z hZ, fun h Z hZ => h Z hZ⟩

theorem mem_centralizer_sup {A B : Subgroup G} {x : G} :
    x ∈ centralizer ((A ⊔ B : Subgroup G) : Set G) ↔
      x ∈ centralizer (A : Set G) ∧ x ∈ centralizer (B : Set G) := by
  constructor
  · intro h
    exact ⟨Subgroup.centralizer_le (by exact_mod_cast (le_sup_left : A ≤ A ⊔ B)) h,
      Subgroup.centralizer_le (by exact_mod_cast (le_sup_right : B ≤ A ⊔ B)) h⟩
  · rintro ⟨hA, hB⟩
    have : A ⊔ B ≤ centralizer ({x} : Set G) := sup_le
      (fun a ha => mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hA a ha))
      (fun b hb => mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hB b hb))
    exact mem_centralizer_iff.2 fun g hg => mem_centralizer_singleton_iff.1 (this hg)

theorem le_centralizer_sup {A B U : Subgroup G} (hA : U ≤ centralizer (A : Set G))
    (hB : U ≤ centralizer (B : Set G)) : U ≤ centralizer ((A ⊔ B : Subgroup G) : Set G) :=
  fun _ hx => mem_centralizer_sup.2 ⟨hA hx, hB hx⟩

theorem mem_normalizer_sup {A B : Subgroup G} {g : G} (hA : g ∈ normalizer (A : Set G))
    (hB : g ∈ normalizer (B : Set G)) : g ∈ normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  rw [Solomon78.mem_normalizer_iff_map_conj_eq] at hA hB ⊢
  rw [Subgroup.map_sup, hA, hB]

theorem conjClosure_eq_iSup_subtype (L S : Subgroup G) :
    conjClosure L S = ⨆ g : S, L.map (MulAut.conj (g : G)).toMonoidHom := by
  rw [conjClosure, iSup_subtype']

theorem subgroupOf_iSup {C : Subgroup G} {ι : Type*} {A : ι → Subgroup G} (hAC : ∀ i, A i ≤ C) :
    (⨆ i, A i).subgroupOf C = ⨆ i, (A i).subgroupOf C := by
  apply Subgroup.map_injective C.subtype_injective
  rw [Subgroup.map_iSup, map_subgroupOf_eq_of_le (iSup_le hAC)]
  exact (iSup_congr fun i => (map_subgroupOf_eq_of_le (hAC i)).symm)

theorem isSubnormal_subgroupOf_iSup [Finite G] {C : Subgroup G} {ι : Type*} [Finite ι]
    {A : ι → Subgroup G} (hAC : ∀ i, A i ≤ C) (hA : ∀ i, ((A i).subgroupOf C).IsSubnormal) :
    ((⨆ i, A i).subgroupOf C).IsSubnormal := by
  rw [subgroupOf_iSup hAC]
  exact CFSG.GroupTheory.isSubnormal_iSup_of_pair
    (fun _ _ hA hB => CFSG.GroupTheory.isSubnormal_sup hA hB) _ hA

section Hom

variable {A B : Type*} [Group A] [Group B]

theorem isSubnormal_subgroupOf_map (f : A →* B) {L D : Subgroup A} (hLD : L ≤ D)
    (h : (L.subgroupOf D).IsSubnormal) : ((L.map f).subgroupOf (D.map f)).IsSubnormal := by
  let g : ↥D →* ↥(D.map f) := (f.comp D.subtype).codRestrict (D.map f) (fun x => ⟨x, x.2, rfl⟩)
  have hg : Function.Surjective g := by
    rintro ⟨_, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  have := h.map hg
  convert this using 1
  ext y
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, hxy⟩
    exact ⟨⟨x, hLD hx⟩, hx, Subtype.ext hxy⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩

theorem isSubnormal_subgroupOf_comap (f : A →* B) {D : Subgroup A} {N : Subgroup B}
    (hDN : D.map f ≤ N) {L : Subgroup B} (h : (L.subgroupOf N).IsSubnormal) :
    ((L.comap f).subgroupOf D).IsSubnormal := by
  let g : ↥D →* ↥N := (f.comp D.subtype).codRestrict N (fun x => hDN ⟨x, x.2, rfl⟩)
  have := h.comap g
  convert this using 1
  ext x
  rfl

end Hom

end CFSG.EvenSporadicStandard.Induction.Junction
