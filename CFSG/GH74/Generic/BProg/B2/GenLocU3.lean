module

public import CFSG.GH74.Generic.BProg.B2.GenLocU3Blk
public import CFSG.GH74.Generic.BProg.B2.GenLocU3NF
public import CFSG.GH74.Generic.BProg.B2.GenLocL2SLAll
public import CFSG.GH74.Generic.BProg.B2.GenLocBasicExc

public section

namespace CFSG.GH74.Generic.BProg.B2

open Matrix CFSG CFSG.GH74 CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.GH74.KGroups.L3Eps.Uni CFSG.GH74.Generic.BProg.B2.GenLocU3Lift CFSG.GH74.Generic.BProg.B2.GenLocU3Blk
  CFSG.GH74.Generic.BProg.B2.GenLocU3NF CFSG.LieType.Steinberg
  CFSG.ClassicalInvolution.ModelFacts.UnitaryAut CFSG.ClassicalInvolution.Phan
open scoped MatrixGroups

namespace GenLocU3

theorem stated_PSU {J : Type} [Group J] {n p f : ℕ} (h : LieModel J .PSU n p f) :
    StatedClassicalModel J .PSU n p f :=
  CFSG.Blueprint.LieModel.statedClassicalModel h (by decide)

theorem gammaAct_su2_of_ge11
    {p f : ℕ} [Fact p.Prime] {F : Type} [Field F] [Finite F] [CharP F p]
    (h : UnitaryFieldData p f F) (hp2 : p ≠ 2) (h11 : 11 ≤ p ^ f) {A : Type} [Group A] [Finite A]
    (hA : IsRank23 A) (β : A →* MulAut (Su F p f 2)) : gammaAct β = ⊤ := by
  obtain ⟨e0⟩ := CFSG.RankThree.SubgroupLists.nonempty_sl2_mulEquiv_statedSU_two (K := F) (r := p)
    (f := f) h.card_eq_sq
  let E : SL(2, fixedSubfield F p f) ≃* Su F p f 2 := e0.trans (suEquiv h 2).symm
  let β' : A →* MulAut SL(2, fixedSubfield F p f) := (MulAut.congr E.symm).toMonoidHom.comp β
  have hc : ∀ a x, β a (E x) = E (β' a x) := by
    intro a x
    simp [β', MulAut.congr_apply]
  have h1 : gammaAct β' = ⊤ :=
    gammaAct_sl2_of_ge11 h.prime hp2 (card_fixedSubfield h.card_eq_sq) h11 β' hA
  have := GenLocBasic.gammaAct_map_equiv E β' β hc
  rw [this, h1, Subgroup.map_top_of_surjective _ E.surjective]

end GenLocU3

theorem gammaAct_psu3
    {J : Type} [Group J] [Finite J] {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (h11 : 11 ≤ p ^ f) (hJ : LieModel J .PSU 3 p f)
    {A : Type} [Group A] [Finite A] (α : A →* MulAut J) (hA : IsRank23 A) : gammaAct α = ⊤ := by
  classical
  obtain ⟨hadm, F, _, _, hF, ⟨e₀⟩⟩ := GenLocU3.stated_PSU hJ
  have hf : 1 ≤ f := hadm.2.1
  have hud : UnitaryFieldData p f F := ⟨hp, hf, by rw [hF, ← pow_mul, mul_comm]⟩
  have : Fact p.Prime := ⟨hp⟩
  have : CharP F p := hud.charP
  have : Finite F := hud.finite
  let ψ : J ≃* unitaryPSU hud 3 := e₀.trans (unitaryPSUEquiv hud (by norm_num)).symm
  let θ : ↥(unitarySU p f F 3) →* J := ψ.symm.toMonoidHom.comp (unitaryProj hud 3)
  have hθs : Function.Surjective θ := ψ.symm.surjective.comp (unitaryProj_surjective hud 3)
  have hθ1 : ∀ g : ↥(unitarySU p f F 3), θ g = 1 ↔ g ∈ unitaryScalars hud 3 := by
    intro g
    change ψ.symm (unitaryProj hud 3 g) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, ← MonoidHom.mem_ker, ker_unitaryProj]
  have hθ : IsCover hud θ := ⟨hθs, by ext g; exact hθ1 g⟩
  have hker : θ.ker ≤ Subgroup.center ↥(unitarySU p f F 3) := by
    rw [hθ.ker]; exact unitaryScalars_le_center hud 3
  obtain ⟨hPerf, hcen⟩ := CFSG.GH74.Generic.S45.isPerfect_and_center_unitarySU' hud hp2 (le_refl 3)
  have hZ : ∀ z : J, (∀ g : J, g * z = z * g) → z = 1 := by
    intro z hz
    have hzc : z ∈ Subgroup.center J := Subgroup.mem_center_iff.2 fun g => hz g
    rw [← map_center_eq_center_of_perfect hθs hker, hcen] at hzc
    obtain ⟨w, hw, rfl⟩ := hzc
    have : w ∈ θ.ker := by rw [hθ.ker]; exact hw
    exact this
  have hinj : Function.Injective (MulAut.conj : J →* MulAut J) :=
    GenLocBasic.conj_injective_of_center_trivial hZ
  have hq : p ^ f ≠ 2 := by omega
  have hq3 : 3 ≤ p ^ f := by omega
  have hD : CFSG.IsElementaryAbelian 2 ↥α.range :=
    GenLocBasic.isEA_of_surjective hA.1 α.rangeRestrict α.rangeRestrict_surjective
  have hblk : ∀ β : A →* MulAut (Su F p f 2), gammaAct β = ⊤ := fun β =>
    GenLocU3.gammaAct_su2_of_ge11 hud hp2 h11 hA β
  by_cases hout : ∃ a : A, ∀ y : J, MulAut.conj y ≠ α a
  · obtain ⟨a0, ha0⟩ := hout
    obtain ⟨C, hCu, hC⟩ := exists_frame hud hp2 hq3 hθ hinj hD (u := α a0) ⟨a0, rfl⟩ ha0
    exact gammaAct_eq_top_of_frame hud hq hθ hCu α (fun a => hC (α a) ⟨a, rfl⟩) hblk
  · push Not at hout
    obtain ⟨C, hCu, hC⟩ := exists_frame_inner hud hp2 hθ hinj hD (fun x hx => by
      obtain ⟨a, rfl⟩ := hx
      exact hout a)
    exact gammaAct_eq_top_of_frame hud hq hθ hCu α (fun a => hC (α a) ⟨a, rfl⟩) hblk

end CFSG.GH74.Generic.BProg.B2
