module

public import CFSG.GH74.Generic.BProg.B3.S3T2L291D
public import CFSG.GH74.Generic.BProg.B1.NontrivNonsolv
public import CFSG.GH74.Generic.BProg.B3.S3T2L291B

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.S3 CFSG.GH74.Generic.BProg
  Subgroup CFSG.GH74.Generic.BProg.B1.PilotS3
open scoped commutatorElement

namespace S3T2L291

variable {G : Type} [Group G] [Finite G]

theorem nbhdSemisimple_of_nonsolvAdm (hB2 : B_B2_g4) (hyp : Hyp2 G) {F : Type} [Field F]
    [Finite F] {x y : G} {K A E E₀ : Subgroup G} {Lb Ib : Subgroup (CentralizerBar x)}
    (hx : orderOf x = 2) (hK : IsPCompIn 2 (centralizer ({x} : Set G)) K)
    (hY : Split3Like F (imgBar x K)) (hEK : E ≤ K) (hAE : A = E ⊔ zpowers x)
    (hEel : CFSG.IsElementaryAbelian 2 ↥E) (hE₀A : E₀ ≤ A) (hnon : NonsolvAdm x y K E₀ Lb Ib)
    (hall : ∀ e ∈ E, e ≠ 1 → NbhdSemisimple x e (Lbar x e K)) : NbhdSemisimple x y Lb := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨L, I, ⟨hL, -, hlift⟩, hI, hIL, hI1, hIb⟩ := B1.exists_lift_comp_E_of_nonsolvAdm hK hnon
  have hS := hnon.setup
  set D : Subgroup G := closure ({x, y} : Set G) with hD
  have hxy : x * y = y * x := (Subgroup.mem_centralizer_singleton_iff.1 hS.y_mem).symm
  have hy2 := hS.y_ord
  have hDel : CFSG.IsElementaryAbelian 2 ↥D := B1.isElementaryAbelian_closure_pair hxy
    (by rw [← hx]; exact pow_orderOf_eq_one x) (by rw [← hy2]; exact pow_orderOf_eq_one y)
  have hE₀el := hS.E_ea
  have hRp : IsPGroup 2 ↥(D ⊔ E₀) := IsPGroup.to_sup_of_normal_right'
    (IsElementaryAbelian.isPGroup 2 D) (IsElementaryAbelian.isPGroup 2 E₀) hS.E_norm
  have hIY : I ≤ centralizer ((D ⊔ E₀ : Subgroup G) : Set G) := hI.1
  have hIperf₀ : Group.IsPerfect ↥(I.subgroupOf (centralizer ((D ⊔ E₀ : Subgroup G) : Set G))) :=
    CFSG.ComponentClassification.CatalogueBAlternating.pComponent_perfect hI.2
  have hIperf : Group.IsPerfect ↥I :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hIY).toMonoidHom)
      (MulEquiv.surjective _)
  have hI2 : oPrimeResidualOf 2 I = I := by
    have htop : oPrimeResidual 2 ↥I = ⊤ := oPrimeResidual_eq_top_of_isPerfect
    unfold oPrimeResidualOf
    rw [htop, Subgroup.map_top, Subgroup.range_subtype]
  have hIc : ∀ g ∈ D ⊔ E₀, I ≤ centralizer ({g} : Set G) := fun g hg i hi =>
    Subgroup.mem_centralizer_singleton_iff.2 ((Subgroup.mem_centralizer_iff.1 (hIY hi) g hg).symm)
  set E₁ : Subgroup G := E₀ ⊓ centralizer (D : Set G) with hE₁
  have hE₁el : CFSG.IsElementaryAbelian 2 ↥E₁ :=
    Th2Sig6.isElementaryAbelian_of_le hE₀el inf_le_left
  have hIE₁ : I ≤ centralizer (E₁ : Set G) :=
    hIY.trans (centralizer_le ((inf_le_left.trans le_sup_right : E₁ ≤ D ⊔ E₀) : _))
  have hIbperf : ⁅Ib, Ib⁆ = Ib := TwoThin.commutator_self_of_isTwoComponent hnon.compI.1
    (TwoThin.isPCompIn_two_iff.mp hnon.compI).2
  have hIbK : Ib ≤ imgBar x K := hnon.compI.1.trans ((sSup_le fun _ h => h.1).trans
    (inf_le_right.trans (hnon.compL.1.trans inf_le_right)))
  have hlift' : ∀ e ∈ E, e ≠ 1 → (e ∈ E₁ ∨ e * x ∈ E₁) → I ≤ centralizer ({e} : Set G) →
      I ≤ liftAt x e (Lbar x e K) := by
    intro e he he1 _ hIe
    have heC : e ∈ centralizer ({x} : Set G) := hK.1 (hEK he)
    have hSe := isSplit3_Lbar hK.1 hY (hEK he) (orderOf_eq_two_of_mem hEel he he1)
    have hIbL : Ib ≤ Lbar x e K := by
      refine hSe.le_of_perfect' (le_inf ?_ hIbK) hIbperf
      rintro _ hg'
      rw [← hIb] at hg'
      obtain ⟨g, hg, rfl⟩ := hg'
      rw [Subgroup.mem_centralizer_singleton_iff, bar_of_mem heC, ← map_mul, ← map_mul]
      exact congrArg (proj x) (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1
        (hIe (Subgroup.mem_subgroupOf.1 hg))))
    refine (le_of_eq hI2.symm).trans (oPrimeResidualOf_le_liftAt
      (le_inf (hIc x (mem_sup_left (subset_closure (by simp)))) hIe) fun g hg _ hgx => hIbL ?_)
    rw [← hIb]
    exact ⟨⟨g, hgx⟩, Subgroup.mem_subgroupOf.2 hg, rfl⟩
  have hB := comm_of_semisimple hx hK.1 hEK hAE (inf_le_left.trans hE₀A) hE₁el hS.E_rank
    (hIc x (mem_sup_left (subset_closure (by simp)))) hIE₁ hlift' hall
  have hleft : ∀ d ∈ D, d ≠ 1 → ⁅I, pPrimeCoreOf 2 (centralizer ({d} : Set G))⁆ = ⊥ := by
    intro d hd hd1
    have hd2 := orderOf_eq_two_of_mem hDel hd hd1
    refine comm_eq_bot_of_hyperplanes hI2 hE₁el hS.E_rank (fun b hb => ?_)
      (hIc d (mem_sup_left hd)) hIE₁ (fun b hb hb1 => ?_) hB
    · exact Subgroup.mem_centralizer_singleton_iff.2
        (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hb).2 d hd).symm
    · have hIle : I ≤ pLayerOf 2 (centralizer ((D ⊔ E₀ : Subgroup G) : Set G)) := le_sSup hI
      refine (commutator_mono hIle le_rfl).trans (lemma22_gen hB2 (B1.kgroup_centralizers hyp) hRp
        (mem_sup_left hd) (mem_sup_right (Subgroup.mem_inf.1 hb).1) hd2
        (orderOf_eq_two_of_mem hE₁el hb hb1) ?_)
      exact (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hb).2 d hd)
  exact B1.nbhdSemisimple_of_dsemisimple hlift (dsemisimple_of_centralizes hL hIL hI1 hleft)

end S3T2L291

end CFSG.GH74.Generic.BProg.B3
