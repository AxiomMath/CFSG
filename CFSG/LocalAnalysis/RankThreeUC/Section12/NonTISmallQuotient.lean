module



public import CFSG.LinearAlgebra.CoprimeActions.BinarySmallAutomorphismOddRank
public import CFSG.LocalAnalysis.RankThreeUC.WeakModules
public import CFSG.LocalAnalysis.SectionRank.AmbientRank

public section

namespace CFSG.LocalAnalysis.RankThreeUC.Section12.NonTISmallQuotient

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def conjAction (M V : Subgroup G) (hn : M ≤ Subgroup.normalizer (V : Set G)) :
    M →* MulAut V where
  toFun m :=
    { toFun := fun v => ⟨(m : G) * v * (m : G)⁻¹, by
        have := (Subgroup.mem_normalizer_iff.mp (hn m.2) v).mp v.2
        simpa using this⟩
      invFun := fun v => ⟨(m : G)⁻¹ * v * (m : G), by
        have := (Subgroup.mem_normalizer_iff.mp (hn (M.inv_mem m.2)) v).mp v.2
        simpa using this⟩
      left_inv := fun v => by ext; simp [mul_assoc]
      right_inv := fun v => by ext; simp [mul_assoc]
      map_mul' := fun a b => by ext; simp [mul_assoc] }
  map_one' := by ext; simp
  map_mul' := fun a b => by ext; simp [mul_assoc]

theorem conjAction_ker (M V : Subgroup G) (hn : M ≤ Subgroup.normalizer (V : Set G)) :
    (conjAction M V hn).ker = centralizerInSubgroup M V := by
  ext m
  simp only [MonoidHom.mem_ker, centralizerInSubgroup, Subgroup.mem_subgroupOf,
    Subgroup.mem_centralizer_iff]
  constructor
  · intro h v hv
    have := congrArg (fun σ : MulAut V => (σ ⟨v, hv⟩ : G)) h
    simp only [conjAction, MonoidHom.coe_mk, OneHom.coe_mk, MulEquiv.coe_mk, Equiv.coe_fn_mk,
      MulAut.one_apply] at this
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this.symm
  · intro h
    ext v
    simp only [conjAction, MonoidHom.coe_mk, OneHom.coe_mk, MulEquiv.coe_mk, Equiv.coe_fn_mk,
      MulAut.one_apply]
    rw [mul_inv_eq_iff_eq_mul]
    exact (h v v.2).symm

theorem quotient_rank_le_of_small {M V : Subgroup G} (hV : V ∈ normalElemAbelian2 M)
    [(centralizerInSubgroup M V).Normal] (hV3 : CFSG.Assembly.pRank 2 V ≤ 3)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    CFSG.pRank p (M ⧸ centralizerInSubgroup M V) ≤ 1 := by
  obtain ⟨-, hab, -, hn⟩ := CFSG.LocalAnalysis.RankThreeUC.mem_normalElemAbelian2.mp hV
  haveI : CFSG.IsElementaryAbelian 2 V :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 V).2 hab
  have h3 : CFSG.pRank 2 V ≤ 3 := by
    rw [SectionRank.pRank_coe_eq_openPRank]; exact hV3
  have hker := conjAction_ker M V hn
  let f : M ⧸ centralizerInSubgroup M V →* MulAut V :=
    QuotientGroup.lift _ (conjAction M V hn) (by rw [← hker])
  refine CFSG.LinearAlgebra.CoprimeActions.BinarySmallAutomorphismOddRank.pRank_le_one_of_injective h3 f ?_ hp hp2
  rw [injective_iff_map_eq_one]
  intro x hx
  induction x using QuotientGroup.induction_on with
  | H m =>
    have : conjAction M V hn m = 1 := hx
    have hm : m ∈ (conjAction M V hn).ker := this
    rw [hker] at hm
    exact (QuotientGroup.eq_one_iff m).2 hm

end CFSG.LocalAnalysis.RankThreeUC.Section12.NonTISmallQuotient
