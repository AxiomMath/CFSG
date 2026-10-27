module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76S4ADefs

public section

namespace CFSG.ComponentClassification.Asc76.Sec4

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.AS76b

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {S : Subgroup G}

omit [Finite G] in
theorem sec4W_isPGroup (hS : IsSylowOf 2 S ⊤) : IsPGroup 2 (sec4W Ω S) :=
  hS.isPGroup.to_le (sec4W_le S)

theorem sec4W_comm (hΩ : Assumption41 Ω) (hS : IsSylowOf 2 S ⊤) {a b : G}
    (ha : a ∈ sec4W Ω S) (hb : b ∈ sec4W Ω S) : a * b = b * a :=
  congrArg Subtype.val ((isMulCommutative_sec4W hΩ hS.isPGroup).is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

theorem sec4W_le_centralizer (hΩ : Assumption41 Ω) (hS : IsSylowOf 2 S ⊤) :
    sec4W Ω S ≤ centralizer (sec4W Ω S : Set G) := fun _ ha =>
  mem_centralizer_iff.mpr fun _ hb => sec4W_comm hΩ hS hb ha

namespace DSet

variable {W T : Subgroup G}

theorem exists_rot (hΩ : Assumption41 Ω) (hT : T ∈ DSet Ω W) : ∃ V, IsDihedralRot V T := by
  obtain ⟨⟨J, hJ, hTJ⟩, -⟩ := hT
  exact Assumption41.exists_rot hΩ hJ hTJ

theorem rot_le (hΩ : Assumption41 Ω) (hS : IsSylowOf 2 S ⊤) (hT : T ∈ DSet Ω (sec4W Ω S))
    {V : Subgroup G} (hV : IsDihedralRot V T) : V ≤ sec4W Ω S := by
  obtain ⟨⟨J, hJ, hTJ⟩, hTW⟩ := hT
  exact rot_le_sec4W hΩ hS hJ hTJ hV hTW

theorem rightConjugate_mem (hΩ : Assumption41 Ω) (hT : T ∈ DSet Ω W) {g : G}
    (hg : g ∈ normalizer (W : Set G)) : rightConjugate T g ∈ DSet Ω W := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨J, hJ, hTJ⟩, hTW⟩ := hT
  refine ⟨⟨_, hΩ.conj_mem J hJ g, isSylowOf_rightConjugate hTJ g⟩, fun x hx => ?_⟩
  rw [mem_rightConjugate_iff] at hx
  have : x = g⁻¹ * (g * x * g⁻¹) * g := by group
  rw [this]
  exact mul_mem (mul_mem (inv_mem hg) (hTW hx)) hg

end DSet

namespace IsZOf

variable {T : Subgroup G} {z : G}

theorem exists_of_rot {V : Subgroup G} (hV : IsDihedralRot V T) : ∃ z, IsZOf T z := by
  obtain ⟨z, hzV, hz1, hzz, -, -⟩ := hV.exists_involution
  exact ⟨z, V, hV, hzV, hz1, hzz⟩

theorem mem_rot (hz : IsZOf T z) {V : Subgroup G} (hV : IsDihedralRot V T) :
    z ∈ V ∧ ∀ y ∈ V, y * y = 1 → y = 1 ∨ y = z := by
  obtain ⟨V', hV', hzV', hz1, hzz⟩ := hz
  have hVV : V' = V := hV.eq_of_isCyclic hV'.le hV'.isCyclic hV'.relIndex_eq
  subst hVV
  obtain ⟨z', hz'V, -, -, hz'uniq, -⟩ := hV.exists_involution
  have hzz' : z = z' := (hz'uniq z hzV' hzz).resolve_left hz1
  subst hzz'
  exact ⟨hzV', hz'uniq⟩

theorem unique (hz : IsZOf T z) {z' : G} (hz' : IsZOf T z') : z = z' := by
  obtain ⟨V, hV, hzV, hz1, hzz⟩ := hz
  exact ((hz'.mem_rot hV).2 z hzV hzz).resolve_left hz1

omit [Finite G] in
theorem mem (hz : IsZOf T z) : z ∈ T := by
  obtain ⟨V, hV, hzV, -, -⟩ := hz
  exact hV.le hzV

theorem commute (hz : IsZOf T z) {x : G} (hx : x ∈ T) : x * z = z * x := by
  obtain ⟨V, hV, hzV, hz1, hzz⟩ := hz
  obtain ⟨z', -, -, -, hz'uniq, hz'c⟩ := hV.exists_involution
  rw [(hz'uniq z hzV hzz).resolve_left hz1]
  exact hz'c x hx

omit [Finite G] in
theorem mul_self (hz : IsZOf T z) : z * z = 1 := by
  obtain ⟨-, -, -, -, h⟩ := hz
  exact h

omit [Finite G] in
theorem ne_one (hz : IsZOf T z) : z ≠ 1 := by
  obtain ⟨-, -, -, h, -⟩ := hz
  exact h

end IsZOf

namespace IsBarOf

variable {W T : Subgroup G} {d : NBar W}

omit [Finite G] in
theorem mk_eq_mk {V : Subgroup G} (hV : IsDihedralRot V T) (hVC : V ≤ centralizer (W : Set G))
    {x y : normalizer (W : Set G)} (hxT : (x : G) ∈ T) (hxV : (x : G) ∉ V) (hyT : (y : G) ∈ T)
    (hyV : (y : G) ∉ V) : (x : NBar W) = (y : NBar W) := by
  rw [QuotientGroup.eq, mem_subgroupOf]
  simp only [coe_mul, coe_inv]
  exact hVC (hV.mul_mem_of_not_mem (inv_mem hxT) hyT (fun h => hxV (by simpa using inv_mem h))
    hyV)

theorem eq_mk (hΩ : Assumption41 Ω) (hS : IsSylowOf 2 S ⊤) (hT : T ∈ DSet Ω (sec4W Ω S))
    {d : NBar (sec4W Ω S)} (hd : IsBarOf (sec4W Ω S) T d) {V : Subgroup G}
    (hV : IsDihedralRot V T) {x : normalizer (sec4W Ω S : Set G)} (hxT : (x : G) ∈ T)
    (hxV : (x : G) ∉ V) : d = (x : NBar (sec4W Ω S)) := by
  obtain ⟨V', hV', t, htT, htV', rfl⟩ := hd
  have hVV : V' = V := hV.eq_of_isCyclic hV'.le hV'.isCyclic hV'.relIndex_eq
  subst hVV
  exact mk_eq_mk hV' ((DSet.rot_le hΩ hS hT hV').trans (sec4W_le_centralizer hΩ hS)) htT htV'
    hxT hxV

theorem unique (hΩ : Assumption41 Ω) (hS : IsSylowOf 2 S ⊤) (hT : T ∈ DSet Ω (sec4W Ω S))
    {d d' : NBar (sec4W Ω S)} (hd : IsBarOf (sec4W Ω S) T d)
    (hd' : IsBarOf (sec4W Ω S) T d') : d = d' := by
  obtain ⟨V, hV, t, htT, htV, rfl⟩ := hd'
  exact eq_mk hΩ hS hT hd hV htT htV

theorem exists_of_mem (hΩ : Assumption41 Ω) (hT : T ∈ DSet Ω W) : ∃ d, IsBarOf W T d := by
  obtain ⟨V, hV⟩ := DSet.exists_rot hΩ hT
  obtain ⟨s, hsT, hsV⟩ := hV.exists_not_mem
  exact ⟨_, V, hV, ⟨s, hT.2 hsT⟩, hsT, hsV, rfl⟩

omit [Finite G] in
theorem mem_dBar (hT : T ∈ DSet Ω W) (hd : IsBarOf W T d) : d ∈ DBar Ω W := by
  obtain ⟨⟨J, hJ, hTJ⟩, hTW⟩ := hT
  obtain ⟨V, hV, t, htT, htV, rfl⟩ := hd
  exact ⟨J, hJ, T, V, hTJ, hV, hTW, t, htT, htV, rfl⟩

end IsBarOf

omit [Finite G] in
theorem DBar.exists_isBarOf {W : Subgroup G} {d : NBar W} (hd : d ∈ DBar Ω W) :
    ∃ T ∈ DSet Ω W, IsBarOf W T d := by
  obtain ⟨J, hJ, T, V, hTJ, hV, hTW, t, htT, htV, rfl⟩ := hd
  exact ⟨T, ⟨⟨J, hJ, hTJ⟩, hTW⟩, V, hV, t, htT, htV, rfl⟩

end CFSG.ComponentClassification.Asc76.Sec4
