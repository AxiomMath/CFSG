module

public import CFSG.LieType.Steinberg.CentralExt.SUThree
public import CFSG.LieType.Steinberg.CentralExt.PerfectCover

public section

namespace CFSG.LieType.Steinberg

open CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]

theorem exists_lift_SU_three (hF : Nat.card F = (p ^ f) ^ 2) (hp2 : p ≠ 2) {E G : Type*}
    [Group E] [Group G] [Finite E] {π : E →* G} (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) (h2 : IsPGroup 2 π.ker)
    (α : SU (unitaryInvolution F p f) 3 →* G) :
    ∃ β : SU (unitaryInvolution F p f) 3 →* E, π.comp β = α := by
  obtain ⟨s, hs⟩ := exists_section_SU_three hF hp2 (π := pullbackFst α π)
    (pullbackFst_surjective hπ) (ker_pullbackFst_le_center hcen) (isPGroup_ker_pullbackFst h2)
  refine ⟨(MonoidHom.snd _ E).comp ((pullback α π).subtype.comp s), ?_⟩
  ext x
  have h1 : ((s x : pullback α π) : SU (unitaryInvolution F p f) 3 × E).1 = x := hs x
  have h2' := mem_pullback.1 (s x).2
  rw [h1] at h2'
  exact h2'.symm

end CFSG.LieType.Steinberg
