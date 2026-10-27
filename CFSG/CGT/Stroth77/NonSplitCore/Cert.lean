module

public import Certificates.Certificate778705

public section

namespace CFSG.CGT.Stroth77.Core


theorem rel_eq_one : ∀ j, evalW sw (rel j) = 1 :=
  Certificates.certificate778705.1

theorem cycles_even : ∀ i, ∀ e ∈ ((cycles i).map fun c => (vtx c.1, rel c.2)).flatMap
    (fun c => walk sw c.1 c.2), Even ((((cycles i).map fun c => (vtx c.1, rel c.2)).flatMap
      (fun c => walk sw c.1 c.2)).count e) :=
  Certificates.certificate778705.2.1

theorem certLHS_eq_certRHS : certLHS = certRHS :=
  Certificates.certificate778705.2.2

theorem normalize (v : Fin 15 → U4) (hv : ∀ i, cycHom i v = 0) (j : Fin 15) :
    Ext.fox actC sw (rel j) (corr v) + v j = lamHom v • titsVal j := by
  have h := congrArg (fun f => f v j) certLHS_eq_certRHS
  have h0 : (Pi.addMonoidHom cycHom) v = 0 := funext hv
  simp only [certRHS, AddMonoidHom.comp_apply, h0, map_zero, Pi.zero_apply] at h
  simp only [certLHS, AddMonoidHom.add_apply, AddMonoidHom.id_apply, AddMonoidHom.comp_apply,
    AddMonoidHom.flip_apply, smulAddHom_apply, Pi.add_apply, Pi.smul_apply] at h
  have h2 : ∀ a : U4, a + a = 0 := fun a => funext fun i => zmod2_add_self _
  change v j + Ext.fox actC sw (rel j) (corr v) + lamHom v • titsVal j = 0 at h
  calc Ext.fox actC sw (rel j) (corr v) + v j
      = Ext.fox actC sw (rel j) (corr v) + v j + (lamHom v • titsVal j + lamHom v • titsVal j) := by
        rw [h2, add_zero]
    _ = (v j + Ext.fox actC sw (rel j) (corr v) + lamHom v • titsVal j) + lamHom v • titsVal j := by
        abel
    _ = lamHom v • titsVal j := by rw [h, zero_add]

end CFSG.CGT.Stroth77.Core
