module

public import CFSG.RankThree.PartTwo.Sec8.Item8KFacts3ProofReeConj
public import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofReeCent

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.ReeF4ThreeAux

open CFSG.LieType.Ree CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartTwo.Sec8.Item8KFacts3Ree CFSG.RankThree.PartTwo.Sec8.Item8KFacts2Proof

theorem centralizer_conj_eq_map {G : Type*} [Group G] (g z : G) :
    Subgroup.centralizer ({g * z * g⁻¹} : Set G) =
      (Subgroup.centralizer ({z} : Set G)).map (MulAut.conj g).toMonoidHom := by
  ext x
  rw [Subgroup.mem_map]
  constructor
  · intro hx
    refine ⟨g⁻¹ * x * g, ?_, by simp [MulAut.conj_apply]; group⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
    calc g⁻¹ * x * g * z = g⁻¹ * (x * (g * z * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * z * g⁻¹) * x) * g := by rw [hx]
      _ = z * (g⁻¹ * x * g) := by group
  · rintro ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * y * g⁻¹ * (g * z * g⁻¹) = g * (y * z) * g⁻¹ := by group
      _ = g * (z * y) * g⁻¹ := by rw [hy]
      _ = g * z * g⁻¹ * (g * y * g⁻¹) := by group


theorem reeGamma_centralizer_su3 {a : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1))
    {y : ReeTag.F4.reeGamma K a} (hy : orderOf y = 3) :
    Nonempty (Subgroup.centralizer ({y} : Set (ReeTag.F4.reeGamma K a)) ≃*
      unitarySU 2 (2 * a + 1) (GaloisField 2 (2 * (2 * a + 1))) 3) := by
  obtain ⟨y₀, hy₀, ⟨e₀⟩⟩ := exists_centralizer_mulEquiv_unitarySU a K hK
  obtain ⟨g, hg⟩ := reeGamma_orderThree_conj a K hK y₀ y hy₀ hy
  have hcent : Subgroup.centralizer ({y} : Set (ReeTag.F4.reeGamma K a)) =
      (Subgroup.centralizer ({y₀} : Set (ReeTag.F4.reeGamma K a))).map
        (MulAut.conj g).toMonoidHom := by
    rw [← hg]
    exact centralizer_conj_eq_map g y₀
  exact ⟨(MulEquiv.subgroupCongr hcent).trans
    ((Subgroup.equivMapOfInjective _ (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective).symm.trans e₀)⟩

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.ReeF4ThreeAux
