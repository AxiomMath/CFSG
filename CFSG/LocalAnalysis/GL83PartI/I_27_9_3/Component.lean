module

public import CFSG.LocalAnalysis.GL83PartI.I_22_5.Setup
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension

public section

namespace GL83.PiGen

open CFSG.Open

section Subnormal

variable {G : Type*} [Group G]

theorem isSubnormal_inf_right {A B : Subgroup G} (h : IsSubnormal A B) (L : Subgroup G) :
    IsSubnormal (A ⊓ L) (B ⊓ L) :=
  h.inf L

theorem eq_bot_or_eq_of_isSubnormal {L : Subgroup G} [IsSimpleGroup L] :
    ∀ {A K : Subgroup G}, IsSubnormal A K → K = L → A = ⊥ ∨ A = L := by
  intro A K h
  induction h with
  | refl H => exact fun hH => Or.inr hH
  | @step H M K hHM hn _ ih =>
    intro hK
    rcases ih hK with hM | hM
    · exact Or.inl (le_bot_iff.1 (hM ▸ hHM))
    · have hHL : H ≤ L := hM ▸ hHM
      have hnL : (H.subgroupOf L).Normal := by
        rw [← hM]
        exact hn
      have := hnL
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (H.subgroupOf L) with h0 | h1
      · left
        rw [← Subgroup.map_subgroupOf_eq_of_le hHL, h0, Subgroup.map_bot]
      · right
        rw [← Subgroup.map_subgroupOf_eq_of_le hHL, h1, Subgroup.map_top, Subgroup.range_subtype]

end Subnormal

section Component

variable {G : Type*} [Group G] [Finite G]

theorem isQuasisimple_of_simple_nonabelian {Q : Type*} [Group Q] [IsSimpleGroup Q]
    (hnc : ∃ a b : Q, a * b ≠ b * a) : IsQuasisimple Q := by
  have hP : Group.IsPerfect Q := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnc).1.1
  exact CFSG.ComponentClassification.Quasisimple.simple_of_perfect Q

theorem coprime_card_glaPPrimeCore {p : ℕ} (hp : p.Prime) (Y : Type*) [Group Y] [Finite Y] :
    Nat.Coprime p (Nat.card (GLAPPrimeCore p Y)) := by
  rw [GL83.CompFam.coprime_iff_isPiSubgroup hp, GL83.CompFam.glaPPrimeCore_eq_piCore hp]
  exact CFSG.LocalCores.piCore_isPiSubgroup _

theorem glaPComponent_of_normal_simple {p : ℕ} (hp : p.Prime) {Y L : Subgroup G} (hLY : L ≤ Y)
    (hn : (L.subgroupOf Y).Normal) [IsSimpleGroup L] (hnc : ∃ a b : L, a * b ≠ b * a)
    (hpL : p ∣ Nat.card L) : GLAPComponent p Y L := by
  classical
  let O : Subgroup ↥Y := GLAPPrimeCore p ↥Y
  let Lb : Subgroup ↥Y := L.subgroupOf Y
  let π : ↥Y →* ↥Y ⧸ O := QuotientGroup.mk' O
  let e0 : ↥Lb ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLY
  have : IsSimpleGroup ↥Lb := e0.isSimpleGroup
  have hcop : Nat.Coprime p (Nat.card O) := coprime_card_glaPPrimeCore hp ↥Y
  have hOb : O.subgroupOf Lb = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (O.subgroupOf Lb) with h0 | h1
    · exact h0
    · exfalso
      have hLbO : Lb ≤ O := fun x hx => by
        have : (⟨x, hx⟩ : ↥Lb) ∈ O.subgroupOf Lb := by rw [h1]; trivial
        exact Subgroup.mem_subgroupOf.1 this
      have hdvd : p ∣ Nat.card O :=
        hpL.trans ((Nat.card_congr e0.toEquiv).symm ▸ Subgroup.card_dvd_of_le hLbO)
      exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hcop hdvd)
  let f : ↥Lb →* ↥Y ⧸ O := π.comp Lb.subtype
  have hf : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have hxO : ((x : ↥Y)) ∈ O := (QuotientGroup.eq_one_iff _).1 (MonoidHom.mem_ker.1 hx)
    have : x ∈ O.subgroupOf Lb := Subgroup.mem_subgroupOf.2 hxO
    rw [hOb] at this
    exact this
  have hrange : Lb.map π = f.range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  let e1 : ↥(Lb.map π) ≃* ↥L :=
    ((MulEquiv.subgroupCongr hrange).trans (MonoidHom.ofInjective hf).symm).trans e0
  have : IsSimpleGroup ↥(Lb.map π) := e1.isSimpleGroup
  have hnc1 : ∃ a b : ↥(Lb.map π), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnc
    exact ⟨e1.symm a, e1.symm b, fun h => hab (e1.symm.injective (by rw [map_mul, map_mul, h]))⟩
  refine ⟨hLY, IsSubnormal.step hLY hn (IsSubnormal.refl Y), ⟨le_top, ?_, ?_⟩, ?_⟩
  · refine IsSubnormal.step le_top ?_ (IsSubnormal.refl _)
    have : (Lb.map π).Normal := Subgroup.Normal.map hn π (QuotientGroup.mk'_surjective O)
    infer_instance
  · exact isQuasisimple_of_simple_nonabelian hnc1
  · intro J hJL hJsn heq
    have hJsn' : IsSubnormal J L := by
      have := isSubnormal_inf_right hJsn L
      rwa [inf_eq_left.2 hJL.le, inf_eq_right.2 hLY] at this
    rcases eq_bot_or_eq_of_isSubnormal hJsn' rfl with hJ | hJ
    · have hne : Lb.map π ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot _).1
        e1.symm.injective.nontrivial
      refine hne ?_
      change (J.subgroupOf Y).map π = Lb.map π at heq
      rw [← heq, hJ, Subgroup.bot_subgroupOf, Subgroup.map_bot]
    · exact hJL.ne hJ

end Component

end GL83.PiGen
