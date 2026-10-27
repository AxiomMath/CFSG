module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit35AltPerm
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitTwoComp
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.L35

open CFSG Subgroup Equiv Equiv.Perm CFSG.ComponentClassification.GSThmB.Catalog82A10
open CFSG.ComponentClassification.HarrisLit.Hin
open scoped commutatorElement

theorem isTwoComponentIn_map_of_injective {G H : Type*} [Group G] [Group H] (ι : G →* H)
    (hι : Function.Injective ι) {J A : Subgroup G} (h : IsTwoComponentIn J A) :
    IsTwoComponentIn (J.map ι) (A.map ι) := by
  refine ⟨map_mono h.1, ?_, isTwoQuasisimple_of_mulEquiv (J.equivMapOfInjective ι hι) h.2.2⟩
  let eA : ↥A ≃* ↥(A.map ι) := A.equivMapOfInjective ι hι
  have hmap : (J.subgroupOf A).map eA.toMonoidHom = (J.map ι).subgroupOf (A.map ι) := by
    ext y
    rw [mem_map, mem_subgroupOf]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, hxy⟩
      exact ⟨⟨x, h.1 hx⟩, hx, Subtype.ext hxy⟩
  rw [← hmap]
  exact h.2.1.map eA.surjective

theorem commutator_self_of_isPerfect {G : Type*} [Group G] {J : Subgroup G}
    (hp : Group.IsPerfect ↥J) : ⁅J, J⁆ = J := by
  have hc := congrArg (Subgroup.map J.subtype) hp.commutator_eq_top
  rwa [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype] at hc

theorem le_altOn_of_isTwoComponentIn {m : ℕ} {π : Perm (Fin m)} (hππ : π * π = 1)
    {J : Subgroup (Perm (Fin m))}
    (hJ : IsTwoComponentIn J (centralizer {π} ⊓ alternatingGroup (Fin m))) :
    J ≤ altOn π.supportᶜ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C' := centralizer ({π} : Set (Perm (Fin m))) ⊓ alternatingGroup (Fin m) with hC'
  have hpc : IsPComponent 2 (J.subgroupOf C') := (isTwoComponentIn_iff hJ.1).mp hJ
  set P : Subgroup ↥C' := (pairSub hππ ⊓ alternatingGroup (Fin m)).subgroupOf C' with hP
  have hPn : P.Normal := ⟨fun x hx c => by
    rw [hP, mem_subgroupOf] at hx ⊢
    have hc : (c : Perm (Fin m)) * π = π * c :=
      mem_centralizer_singleton_iff.mp (mem_inf.mp c.2).1
    refine ⟨conj_mem_pairSub hππ hc (mem_inf.mp hx).1, ?_⟩
    have hA : (alternatingGroup (Fin m)).Normal := inferInstance
    simpa using hA.conj_mem _ (mem_inf.mp hx).2 (c : Perm (Fin m))⟩
  have hP2 : IsPGroup 2 P := by
    refine IsPGroup.iff_orderOf.mpr fun x => ?_
    have hx2 : x * x = 1 :=
      Subtype.ext (Subtype.ext (pairSub_sq hππ (mem_inf.mp (mem_subgroupOf.mp x.2)).1))
    have hdvd : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hx2)
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
    · exact ⟨0, by rw [h1, pow_zero]⟩
    · exact ⟨1, by rw [h2, pow_one]⟩
  have hcomm := CatalogueBAlternating.pComponent_commutes_normal_p 2 (J.subgroupOf C') P hpc hP2
  have hJperf : ⁅J, J⁆ = J := commutator_self_of_isPerfect hJ.2.2.1
  have hJC : ∀ g ∈ J, g * π = π * g := fun g hg =>
    mem_centralizer_singleton_iff.mp (mem_inf.mp (hJ.1 hg)).1
  refine le_altOn_of_comm hππ hJperf hJC fun g hg x hx hxA => ?_
  have hxC : x ∈ C' := ⟨pairSub_le_centralizer hππ hx, hxA⟩
  have hgC : g ∈ C' := hJ.1 hg
  have h1 : ⁅(⟨g, hgC⟩ : ↥C'), (⟨x, hxC⟩ : ↥C')⁆ ∈ ⁅J.subgroupOf C', P⁆ :=
    commutator_mem_commutator (mem_subgroupOf.mpr hg) (mem_subgroupOf.mpr (mem_inf.mpr ⟨hx, hxA⟩))
  rw [hcomm, mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
  exact congrArg Subtype.val h1

end CFSG.ComponentClassification.HarrisLit.L35
