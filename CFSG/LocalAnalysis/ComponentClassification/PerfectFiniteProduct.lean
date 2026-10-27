module

public import CFSG.LocalAnalysis.ComponentClassification.PerfectAutomorphisms
public import CFSG.Assembly.Defs

public section

namespace CFSG.ComponentClassification.PerfectFiniteProduct

theorem perfect {Index : Type*} [Finite Index] (factors : Index → Type*)
    [∀ index, Group (factors index)] [∀ index, Group.IsPerfect (factors index)] :
    Group.IsPerfect ((index : Index) → factors index) := by
  classical
  let product := (index : Index) → factors index
  let projection := Abelianization.of (G := product)
  have htrivial : projection = 1 := by
    apply MonoidHom.pi_ext
    intro index member
    have heq := PerfectAutomorphisms.hom_eq_one_of_commutative
      (projection.comp (MonoidHom.mulSingle factors index))
    exact congrArg (fun homomorphism : factors index →* Abelianization product =>
      homomorphism member) heq
  constructor
  apply top_unique
  intro member _
  have hone := congrArg (fun homomorphism : product →* Abelianization product =>
    homomorphism member) htrivial
  have hkernel : member ∈ projection.ker := MonoidHom.mem_ker.mpr hone
  rwa [Abelianization.ker_of] at hkernel

end CFSG.ComponentClassification.PerfectFiniteProduct
