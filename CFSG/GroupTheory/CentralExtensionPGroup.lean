module

public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.GroupTheory

variable {Y : Type*} [Group Y] [Finite Y] {p : ℕ} [Fact p.Prime]

theorem mem_sylow_of_pow_eq_one {P : Sylow p Y} (hP : (P : Subgroup Y).Normal) {s : Y} {k : ℕ}
    (hs : s ^ p ^ k = 1) : s ∈ P := by
  have hz : IsPGroup p (Subgroup.zpowers s) := by
    rintro ⟨g, hg⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    refine ⟨k, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hs, one_zpow]
  obtain ⟨Q, hQ⟩ := hz.exists_le_sylow
  haveI := Sylow.unique_of_normal P hP
  have hQP : Q = P := Subsingleton.elim Q P
  rw [← hQP]
  exact hQ (Subgroup.mem_zpowers s)

theorem isPGroup_closure_of_isNilpotent [Group.IsNilpotent Y] {S : Set Y}
    (hS : ∀ s ∈ S, ∃ k : ℕ, s ^ p ^ k = 1) : IsPGroup p (Subgroup.closure S) := by
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow p Y))
  have hle : Subgroup.closure S ≤ P := by
    rw [Subgroup.closure_le]
    intro s hs
    obtain ⟨k, hk⟩ := hS s hs
    exact mem_sylow_of_pow_eq_one inferInstance hk
  exact P.isPGroup'.to_le hle

theorem isPGroup_closure_of_map_center {S : Set Y} (hS : ∀ s ∈ S, ∃ k : ℕ, s ^ p ^ k = 1)
    (hmap : IsPGroup p
      ((Subgroup.closure S).map (QuotientGroup.mk' (Subgroup.center Y)))) :
    IsPGroup p (Subgroup.closure S) := by
  set K := Subgroup.closure S
  let f : K →* K.map (QuotientGroup.mk' (Subgroup.center Y)) :=
    (QuotientGroup.mk' (Subgroup.center Y)).subgroupMap K
  have hker : f.ker ≤ Subgroup.center K := by
    intro x hx
    have hx' : (x : Y) ∈ Subgroup.center Y := by
      have h1 : f x = 1 := hx
      have h2 : (QuotientGroup.mk' (Subgroup.center Y)) (x : Y) = 1 :=
        congrArg Subtype.val h1
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext ((Subgroup.mem_center_iff.mp hx') y)
  haveI : Group.IsNilpotent (K.map (QuotientGroup.mk' (Subgroup.center Y))) := hmap.isNilpotent
  haveI : Group.IsNilpotent K := Subgroup.isNilpotent_of_ker_le_center f hker
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow p K))
  have hle : K ≤ (P : Subgroup K).map K.subtype := by
    change Subgroup.closure S ≤ _
    rw [Subgroup.closure_le]
    intro s hs
    obtain ⟨k, hk⟩ := hS s hs
    have hsK : s ∈ K := Subgroup.subset_closure hs
    have hmem : (⟨s, hsK⟩ : K) ∈ P :=
      mem_sylow_of_pow_eq_one inferInstance (k := k) (Subtype.ext (by simpa using hk))
    exact ⟨⟨s, hsK⟩, hmem, rfl⟩
  intro g
  obtain ⟨h, hh, hhg⟩ := hle g.2
  have hg : g = h := Subtype.ext hhg.symm
  obtain ⟨n, hn⟩ := P.isPGroup' ⟨h, hh⟩
  exact ⟨n, by rw [hg]; exact congrArg Subtype.val hn⟩

end CFSG.GroupTheory
