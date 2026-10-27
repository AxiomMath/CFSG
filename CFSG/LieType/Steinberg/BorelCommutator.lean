module

public import CFSG.LieType.Steinberg.BruhatWeyl

public section

namespace CFSG.LieType.Steinberg

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
open scoped commutatorElement

variable {K : Type*} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

theorem iSup_torus_le_centralizer (hext : SteinbergExtras D n H) :
    (⨆ i, H i) ≤ Subgroup.centralizer ((⨆ i, H i : Subgroup K) : Set K) := by
  refine iSup_le fun i => Subgroup.le_centralizer_iff.2 (iSup_le fun j h' hh' => ?_)
  exact Subgroup.mem_centralizer_iff.2 fun h hh => (hext.torus_commute i j h hh h' hh').eq

theorem commutator_mem_posUnipotent_of_mem_borel
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) :
    ∀ b ∈ borel D H, ∀ b' ∈ borel D H, ⁅b, b'⁆ ∈ posUnipotent D := by
  intro b hb b' hb'
  have hUB : posUnipotent D ≤ borel D H := le_sup_right
  have hTB : (⨆ i, H i) ≤ borel D H := le_sup_left
  have : ((posUnipotent D).subgroupOf (borel D H)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUB).2 (borel_le_normalizer_posUnipotent hct)
  have hsup : (posUnipotent D).subgroupOf (borel D H) ⊔ (⨆ i, H i).subgroupOf (borel D H) =
      ⊤ := by
    rw [sup_comm, ← Subgroup.subgroupOf_sup hTB hUB]
    exact Subgroup.subgroupOf_self (borel D H)
  have hcomm : IsMulCommutative ↥((⨆ i, H i).subgroupOf (borel D H)) :=
    isMulCommutative_iff.2 fun x y => Subtype.ext (Subtype.ext
      (Subgroup.mem_centralizer_iff.1
        (iSup_torus_le_centralizer hext (Subgroup.mem_subgroupOf.1 x.2)) _
        (Subgroup.mem_subgroupOf.1 y.2)).symm)
  have hle := Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hsup hcomm
  have hmem : ⁅(⟨b, hb⟩ : borel D H), ⟨b', hb'⟩⁆ ∈ _root_.commutator (borel D H) :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  exact Subgroup.mem_subgroupOf.1 (hle hmem)

end CFSG.LieType.Steinberg
