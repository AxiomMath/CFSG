module

public import CFSG.CGT.PushingUpLit.CGT6.EmbNatLift
public import CFSG.CGT.PushingUpLit.CGT6.EmbNatMod
public import CFSG.CGT.PushingUpLit.CGT6.EmbNatOrbit

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.Quasithin CFSG.CGT.PushingUp

theorem natRecog_holds : NatRecogStatement := by
  intro V _ _ hV X a ha θ hX i₀ v hv hJ
  have hm : Odd (2 * a + 1) := odd_two_mul_add_one a
  have hJ' : ∀ x : X, ((θ x : alternatingGroup (Fin (2 * a + 1))) :
      Equiv.Perm (Fin (2 * a + 1))) i₀ = i₀ → (x : MulAut V) v = v := by
    intro x hx
    apply hJ
    simp only [altStabilizer, Finset.mem_singleton, Subgroup.mem_iInf, forall_eq,
      MulAction.mem_stabilizer_iff]
    exact hx
  obtain ⟨Φ, hrange, hker, hequiv⟩ := exists_orbitHom hV (by omega) θ hX i₀ hv hJ'
  rw [← hrange]
  exact natSectionWith_of_orbitHom hm θ Φ rfl hker hequiv

end CFSG.CGT.PushingUpLit.CGT6
