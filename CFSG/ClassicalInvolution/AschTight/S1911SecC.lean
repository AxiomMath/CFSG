module

public import CFSG.ClassicalInvolution.AschTight.S1911SecB

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S1911

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.RankThreeCoreUniqueness CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] {K : Subgroup G} {a : G}

theorem conjSub_ne_of_ne {c₁ c₂ : ↥(Subgroup.centralizer ({a} : Set G))}
    (hne : conjSub c₁ (perfectCoreIn K a) ≠
      conjSub c₂ (perfectCoreIn K a)) :
    conjSub (c₁ : G) K ≠ conjSub (c₂ : G) K := by
  intro h
  apply hne
  apply Subgroup.map_injective (Subgroup.centralizer ({a} : Set G)).subtype_injective
  rw [map_conjSub_perfectCore, map_conjSub_perfectCore, conjSub_perfectCore_eq c₁.2 c₂.2 h]

theorem conjSub_perfectCore_of_mem_normalizer {c n : G}
    (hc : c ∈ Subgroup.centralizer ({a} : Set G)) (hn : n ∈ Subgroup.centralizer ({a} : Set G))
    (hnJ : n ∈ Subgroup.normalizer ((conjSub c K : Subgroup G) : Set G)) :
    conjSub n (conjSub c (perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G)))) =
      conjSub c (perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G))) := by
  rw [← conjSub_mul]
  exact conjSub_perfectCore_eq (Subgroup.mul_mem _ hn hc) hc
    (by rw [conjSub_mul, conjSub_eq_of_mem_normalizer hnJ])

theorem mem_normalizer_conjSub_of (c v : ↥(Subgroup.centralizer ({a} : Set G)))
    (hv : (v : G) ∈ Subgroup.normalizer ((conjSub (c : G) K : Subgroup G) : Set G)) :
    v ∈ Subgroup.normalizer ((conjSub c (perfectCoreIn K a) :
        Subgroup ↥(Subgroup.centralizer ({a} : Set G))) :
          Set ↥(Subgroup.centralizer ({a} : Set G))) := by
  refine mem_normalizer_iff_conjSub_eq.mpr ?_
  apply Subgroup.map_injective (Subgroup.centralizer ({a} : Set G)).subtype_injective
  rw [← conjSub_mul, map_conjSub_perfectCore, map_conjSub_perfectCore, Subgroup.coe_mul,
    conjSub_mul]
  exact conjSub_perfectCore_of_mem_normalizer c.2 v.2 hv

theorem le_conjSub_of_mem (c : ↥(Subgroup.centralizer ({a} : Set G)))
    {x : ↥(Subgroup.centralizer ({a} : Set G))}
    (hx : x ∈ conjSub c (perfectCoreIn K a)) :
    (x : G) ∈ conjSub (c : G) K := by
  have h : (x : G) ∈
      (conjSub c (perfectCoreIn K a)).map (Subgroup.centralizer ({a} : Set G)).subtype :=
    ⟨x, hx, rfl⟩
  rw [map_conjSub_perfectCore] at h
  exact Subgroup.map_mono ((perfectResidualOf_le _).trans inf_le_left) h

end CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
