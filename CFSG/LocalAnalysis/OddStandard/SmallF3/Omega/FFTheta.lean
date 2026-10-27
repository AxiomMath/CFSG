module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SEInd1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFInduces

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {G : Type} [Group G] {L : Subgroup G}

@[expose] noncomputable def ffTheta (hQ : Q.Nondegenerate)
    (h : (Module.finrank (ZMod 3) V = 5 ∧ quadSign Q = 1) ∨
      (Module.finrank (ZMod 3) V = 6 ∧ (quadSign Q = 1 ∨ quadSign Q = -1)))
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) :
    ↥(Subgroup.normalizer (L : Set G)) →* ProjSim Q where
  toFun s := Classical.choose (ff_exists_induces hQ h e s.2)
  map_one' := by
    have h5 : 5 ≤ Module.finrank (ZMod 3) V := by rcases h with ⟨h5, -⟩ | ⟨h6, -⟩ <;> omega
    exact ff_induces_unique hQ h5 e
      (Classical.choose_spec (ff_exists_induces hQ h e (Subgroup.one_mem _)))
      (inducesViaP_one_of_centralizer (Subgroup.one_mem _))
  map_mul' s s' := by
    have h5 : 5 ≤ Module.finrank (ZMod 3) V := by rcases h with ⟨h5, -⟩ | ⟨h6, -⟩ <;> omega
    exact ff_induces_unique hQ h5 e
      (Classical.choose_spec (ff_exists_induces hQ h e (mul_mem s.2 s'.2)))
      (inducesViaP_mul (Classical.choose_spec (ff_exists_induces hQ h e s.2))
        (Classical.choose_spec (ff_exists_induces hQ h e s'.2)))

theorem ffTheta_induces (hQ : Q.Nondegenerate)
    (h : (Module.finrank (ZMod 3) V = 5 ∧ quadSign Q = 1) ∨
      (Module.finrank (ZMod 3) V = 6 ∧ (quadSign Q = 1 ∨ quadSign Q = -1)))
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) (s : ↥(Subgroup.normalizer (L : Set G))) :
    InducesViaP L (Subgroup.center ↥L) hQ e (s : G) (ffTheta hQ h e s) :=
  Classical.choose_spec (ff_exists_induces hQ h e s.2)

theorem ffTheta_eq_iff (hQ : Q.Nondegenerate)
    (h : (Module.finrank (ZMod 3) V = 5 ∧ quadSign Q = 1) ∨
      (Module.finrank (ZMod 3) V = 6 ∧ (quadSign Q = 1 ∨ quadSign Q = -1)))
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) (s : ↥(Subgroup.normalizer (L : Set G)))
    (x : ProjSim Q) :
    ffTheta hQ h e s = x ↔ InducesViaP L (Subgroup.center ↥L) hQ e (s : G) x := by
  have h5 : 5 ≤ Module.finrank (ZMod 3) V := by rcases h with ⟨h5, -⟩ | ⟨h6, -⟩ <;> omega
  constructor
  · rintro rfl
    exact ffTheta_induces hQ h e s
  · intro hx
    exact ff_induces_unique hQ h5 e (ffTheta_induces hQ h e s) hx

theorem ffTheta_of_mem (hQ : Q.Nondegenerate)
    (h : (Module.finrank (ZMod 3) V = 5 ∧ quadSign Q = 1) ∨
      (Module.finrank (ZMod 3) V = 6 ∧ (quadSign Q = 1 ∨ quadSign Q = -1)))
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) (l : ↥L) :
    ffTheta hQ h e ⟨(l : G), Subgroup.le_normalizer l.2⟩ =
      projOrthToProjSim Q ((e (QuotientGroup.mk l) : omegaProj hQ) : ProjOrth Q) :=
  (ffTheta_eq_iff hQ h e _ _).mpr (inducesViaP_of_mem e l)

theorem ffTheta_eq_one_iff (hQ : Q.Nondegenerate)
    (h : (Module.finrank (ZMod 3) V = 5 ∧ quadSign Q = 1) ∨
      (Module.finrank (ZMod 3) V = 6 ∧ (quadSign Q = 1 ∨ quadSign Q = -1)))
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) (hL : commutator ↥L = ⊤)
    (s : ↥(Subgroup.normalizer (L : Set G))) :
    ffTheta hQ h e s = 1 ↔ (s : G) ∈ Subgroup.centralizer (L : Set G) := by
  rw [ffTheta_eq_iff]
  exact ⟨mem_centralizer_of_inducesViaP_one hL, inducesViaP_one_of_centralizer⟩

theorem ffTheta_conj (hQ : Q.Nondegenerate)
    (h : (Module.finrank (ZMod 3) V = 5 ∧ quadSign Q = 1) ∨
      (Module.finrank (ZMod 3) V = 6 ∧ (quadSign Q = 1 ∨ quadSign Q = -1)))
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) (s : ↥(Subgroup.normalizer (L : Set G)))
    (l l' : ↥L) (hl : (l' : G) = (s : G) * l * (s : G)⁻¹) :
    projSimAct Q (ffTheta hQ h e s) ((e (QuotientGroup.mk l) : omegaProj hQ) : ProjOrth Q) =
      ((e (QuotientGroup.mk l') : omegaProj hQ) : ProjOrth Q) :=
  ((ffTheta_induces hQ h e s).2 l l' hl).symm

theorem ffTheta_surjective_of_mem (hQ : Q.Nondegenerate)
    (h : (Module.finrank (ZMod 3) V = 5 ∧ quadSign Q = 1) ∨
      (Module.finrank (ZMod 3) V = 6 ∧ (quadSign Q = 1 ∨ quadSign Q = -1)))
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) (w : ↥(omegaProj hQ)) :
    ∃ l : ↥L, ffTheta hQ h e ⟨(l : G), Subgroup.le_normalizer l.2⟩ =
      projOrthToProjSim Q (w : ProjOrth Q) := by
  obtain ⟨q, rfl⟩ := e.surjective w
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
  exact ⟨l, ffTheta_of_mem hQ h e l⟩

end CFSG.OddStandard.SmallF3.Omega
