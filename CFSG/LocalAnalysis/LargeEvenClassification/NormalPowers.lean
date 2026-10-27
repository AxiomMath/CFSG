module

public import CFSG.LocalAnalysis.LargeEvenClassification.FrattiniExact

public section

namespace CFSG.LargeEvenClassification.Helpers

universe groupUniverse

@[expose] def normalPowerSubgroup {Ambient : Type groupUniverse} [Group Ambient]
    (Normal : Subgroup Ambient) (hcommutative : IsMulCommutative Normal) (prime : ℕ) :
    Subgroup Ambient := by
  let : CommGroup Normal := { (inferInstance : Group Normal) with
    mul_comm := @mul_comm' Normal _ hcommutative }
  exact (powMonoidHom prime : Normal →* Normal).range.map Normal.subtype

theorem normalPowerSubgroup_mem {Ambient : Type groupUniverse} [Group Ambient]
    (Normal : Subgroup Ambient) (hcommutative : IsMulCommutative Normal) (prime : ℕ)
    (element : Ambient) : element ∈ normalPowerSubgroup Normal hcommutative prime ↔
      ∃ entry : Normal, (entry : Ambient) ^ prime = element := by
  constructor
  · intro helement
    obtain ⟨entry, ⟨source, hsource⟩, hentry⟩ := Subgroup.mem_map.mp helement
    exact ⟨source, (congrArg (fun entry : Normal => (entry : Ambient)) hsource).trans hentry⟩
  · rintro ⟨entry, rfl⟩
    exact Subgroup.mem_map.mpr ⟨entry ^ prime, ⟨entry, rfl⟩, rfl⟩

theorem normalPowerSubgroup_le {Ambient : Type groupUniverse} [Group Ambient]
    (Normal : Subgroup Ambient) (hcommutative : IsMulCommutative Normal) (prime : ℕ) :
    normalPowerSubgroup Normal hcommutative prime ≤ Normal := Subgroup.map_subtype_le _

theorem normalPowerSubgroup_normal {Ambient : Type groupUniverse} [Group Ambient]
    (Normal : Subgroup Ambient) [Normal.Normal] (hcommutative : IsMulCommutative Normal)
    (prime : ℕ) : (normalPowerSubgroup Normal hcommutative prime).Normal := by
  constructor
  intro element helement conjugator
  obtain ⟨entry, rfl⟩ := (normalPowerSubgroup_mem Normal hcommutative prime element).mp helement
  apply (normalPowerSubgroup_mem Normal hcommutative prime _).mpr
  refine ⟨MulAut.conjNormal conjugator entry, ?_⟩
  have heq := MulAut.conjNormal_apply conjugator (entry ^ prime)
  rw [map_pow] at heq
  exact heq

theorem normalPowerSubgroup_eq_frattini_image {Ambient : Type groupUniverse} [Group Ambient]
    [Finite Ambient] {prime : ℕ} (hprime : prime.Prime) (hpgroup : IsPGroup prime Ambient)
    (Normal : Subgroup Ambient) (hcommutative : IsMulCommutative Normal) :
    normalPowerSubgroup Normal hcommutative prime = (frattini Normal).map Normal.subtype := by
  let : CommGroup Normal := { (inferInstance : Group Normal) with
    mul_comm := @mul_comm' Normal _ hcommutative }
  change (powMonoidHom prime : Normal →* Normal).range.map Normal.subtype = _
  rw [commutative_frattini_eq_power_range hprime (hpgroup.to_subgroup Normal)]

theorem normalPowerSubgroup_le_frattini {Ambient : Type groupUniverse} [Group Ambient]
    [Finite Ambient] {prime : ℕ} (hprime : prime.Prime) (hpgroup : IsPGroup prime Ambient)
    (Normal : Subgroup Ambient) (hcommutative : IsMulCommutative Normal) :
    normalPowerSubgroup Normal hcommutative prime ≤ frattini Ambient := by
  intro element helement
  obtain ⟨entry, rfl⟩ := (normalPowerSubgroup_mem Normal hcommutative prime element).mp helement
  exact pGroup_pow_mem_frattini hprime hpgroup entry

end CFSG.LargeEvenClassification.Helpers
