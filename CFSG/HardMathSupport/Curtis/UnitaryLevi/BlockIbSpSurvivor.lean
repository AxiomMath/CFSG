module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.BlockIbSpClassify
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.OutRankY
public import CFSG.RankThree.PartTwo.Sec19.Step1919EndProof
public import CFSG.CharacterTheory.Semidihedral.OddFieldLift
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.SpResidual.Main
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.BlockIbGeneric
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.OutRank
public import CFSG.LocalAnalysis.AGLEmbedding.A9MSideBlocks
public import CFSG.LocalAnalysis.AGLEmbedding.BlockFoundationsPLType
public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusDispatchIb
public import CFSG.LocalAnalysis.AGLEmbedding.GapROneBS
public import CFSG.LocalAnalysis.AGLEmbedding.J3InSitu
public import CFSG.LocalAnalysis.AGLEmbedding.J3MSide
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrCore
public import CFSG.LocalAnalysis.AGLEmbedding.KFactsAlphaWeakCentral
public import CFSG.LocalAnalysis.AGLEmbedding.MonomialWeightsOne
public import CFSG.LocalAnalysis.AGLEmbedding.OddCoreRank
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieMDataAux2
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieMSideCore
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieUnitaryZAux
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieUnitaryZPCore
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVCoverAux
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLZeroThreeSplit
public import CFSG.LocalAnalysis.AGLEmbedding.ReeData
public import CFSG.LocalAnalysis.AGLEmbedding.ReeF4CompPerfect
public import CFSG.LocalAnalysis.AGLEmbedding.SurvivorBarM
public import CFSG.LocalAnalysis.AGLEmbedding.SurvivorCommutator
public import CFSG.LocalAnalysis.AGLEmbedding.SurvivorTransfer
public import CFSG.LocalAnalysis.AGLEmbedding.TorusDataAux
public import CFSG.LocalAnalysis.AGLEmbedding.TorusIrreducible
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Survivor
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.Permutation.UnitaryThreeRecognition.Model
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.CTP.StrongPSylow
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.RankThree.PartTwo.Sec19.Item194Used
public import CFSG.RankThree.PartTwo.Sec19.Step1914E
public import CFSG.RankThree.PartTwo.Sec19.Steps195
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.RankThree.PartTwo.Sec5.Hyp
public import CFSG.StronglyEmbedded.BenderUnitaryCenter
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_1_12
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import Certificates.Certificate2201
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement

public noncomputable section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial CFSG.QuasithinUnique
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (flagStabilizer)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (flag isoFlag)
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus.Symplectic (spMat)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section SelfNormalizing

variable {X : Type*} [Group X] [Finite X]

theorem mem_of_normalizes_parabolic {T J : Subgroup X} (hT : IsSylowTwoOf T ⊤)
    (hNJ : Subgroup.normalizer (T : Set X) ≤ J) {a : X}
    (ha : ∀ x, x ∈ J ↔ a * x * a⁻¹ ∈ J) : a ∈ J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTJ : T ≤ J := Subgroup.le_normalizer.trans hNJ
  set T' : Subgroup X := T.map (MulAut.conj a).toMonoidHom with hT'
  have hT'J : T' ≤ J := by
    rintro _ ⟨x, hx, rfl⟩
    exact (ha x).1 (hTJ hx)
  have hidx : ¬ 2 ∣ T.index := by
    have h2 := hT.2.2
    rwa [show (T.subgroupOf ⊤).index = T.index from Subgroup.relIndex_top_right T] at h2
  have hP1 : IsPGroup 2 (T.subgroupOf J) := hT.2.1.comap_subtype
  have hP2 : IsPGroup 2 (T'.subgroupOf J) :=
    (hT.2.1.map (MulAut.conj a).toMonoidHom).comap_subtype
  have hi1 : ¬ 2 ∣ (T.subgroupOf J).index := fun h =>
    hidx (h.trans (Subgroup.relIndex_dvd_index_of_le hTJ))
  have hi2 : ¬ 2 ∣ (T'.subgroupOf J).index := fun h => by
    have h1 := h.trans (Subgroup.relIndex_dvd_index_of_le hT'J)
    rw [hT', Subgroup.index_map_of_bijective (f := (MulAut.conj a).toMonoidHom)
      (MulAut.conj a).bijective T] at h1
    exact hidx h1
  let S1 : Sylow 2 ↥J := hP1.toSylow hi1
  let S2 : Sylow 2 ↥J := hP2.toSylow hi2
  obtain ⟨j, hj⟩ := MulAction.exists_smul_eq (↥J) S2 S1
  have hjS : (T.subgroupOf J) = (T'.subgroupOf J).map (MulAut.conj j).toMonoidHom := by
    have h1 : ((j • S2 : Sylow 2 ↥J) : Subgroup ↥J) = (S1 : Subgroup ↥J) := by rw [hj]
    rw [Sylow.coe_subgroup_smul] at h1
    exact h1.symm
  have hjmem : (j : X) * a ∈ Subgroup.normalizer (T : Set X) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have hy : (⟨a * x * a⁻¹, hT'J ⟨x, hx, rfl⟩⟩ : ↥J) ∈ T'.subgroupOf J := ⟨x, hx, rfl⟩
      have h1 : MulAut.conj j (⟨a * x * a⁻¹, hT'J ⟨x, hx, rfl⟩⟩ : ↥J) ∈ T.subgroupOf J := by
        rw [hjS]; exact ⟨_, hy, rfl⟩
      have h2 : (j : X) * (a * x * a⁻¹) * (j : X)⁻¹ ∈ T := h1
      have : (j : X) * a * x * ((j : X) * a)⁻¹ = (j : X) * (a * x * a⁻¹) * (j : X)⁻¹ := by group
      rw [this]; exact h2
    · intro hx
      have h0 : (j : X) * (a * x * a⁻¹) * (j : X)⁻¹ ∈ T := by
        have : (j : X) * (a * x * a⁻¹) * (j : X)⁻¹ = (j : X) * a * x * ((j : X) * a)⁻¹ := by group
        rw [this]; exact hx
      have hzJ : a * x * a⁻¹ ∈ J := by
        have h1 := hTJ h0
        have := J.mul_mem (J.mul_mem (J.inv_mem j.2) h1) j.2
        simpa [mul_assoc] using this
      have h1 : MulAut.conj j (⟨a * x * a⁻¹, hzJ⟩ : ↥J) ∈ T.subgroupOf J := h0
      rw [hjS] at h1
      obtain ⟨y, hy, hyz⟩ := h1
      have hyeq : y = ⟨a * x * a⁻¹, hzJ⟩ := (MulAut.conj j).injective hyz
      rw [hyeq] at hy
      obtain ⟨x', hx', hxx'⟩ := hy
      have : x' = x := by
        have h3 : a * x' * a⁻¹ = a * x * a⁻¹ := hxx'
        simpa using h3
      rw [← this]; exact hx'
  have := hNJ hjmem
  have h2 := J.mul_mem (J.inv_mem j.2) this
  simpa using h2

end SelfNormalizing

section Out

open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
local notation "innerAut" => CFSG.ComponentClassification.OuterAutomorphisms.inner

theorem out_trivial_statedSp_three (φ : MulAut (StatedSp 3 (ZMod 2))) :
    ∃ a : StatedSp 3 (ZMod 2), φ = MulAut.conj a := by
  have hK : Nat.card (ZMod 2)ˣ = 1 := by
    rw [Nat.card_units, Nat.card_zmod]
  have h1 := CFSG.RankThree.PartTwo.Sec19.Step1919EndProof.card_outer_statedSp_le (r := 3)
    le_rfl hK
  have h2 : Nat.card (ZMod 2 ≃+* ZMod 2) ≤ 1 := by
    have : Subsingleton (ZMod 2 ≃+* ZMod 2) :=
      ⟨fun σ τ => RingEquiv.ext fun x => by
        have h := congrArg (fun φ : ZMod 2 →+* ZMod 2 => φ x)
          (Subsingleton.elim (σ : ZMod 2 →+* ZMod 2) (τ : ZMod 2 →+* ZMod 2))
        exact h⟩
    exact Finite.card_le_one_iff_subsingleton.mpr this
  have hpos : 0 < Nat.card (Outer (StatedProj (StatedSp 3 (ZMod 2)))) := Nat.card_pos
  have hone : (innerAut (StatedProj (StatedSp 3 (ZMod 2)))).index = 1 := by
    have : Nat.card (Outer (StatedProj (StatedSp 3 (ZMod 2)))) =
        (innerAut (StatedProj (StatedSp 3 (ZMod 2)))).index := rfl
    omega
  have hinner : innerAut (StatedProj (StatedSp 3 (ZMod 2))) = ⊤ := Subgroup.index_eq_one.mp hone
  let π : StatedSp 3 (ZMod 2) ≃* StatedProj (StatedSp 3 (ZMod 2)) :=
    MulEquiv.ofBijective (SymplecticFlag.proj 3 (ZMod 2))
      ⟨CFSG.AGLEmbedding.ToralCensus.proj_injective_of_charTwo (by norm_num),
        SymplecticHigher.proj_surjective⟩
  have hψ : MulAut.congr π φ ∈ innerAut (StatedProj (StatedSp 3 (ZMod 2))) := by
    rw [hinner]; trivial
  obtain ⟨b, hb⟩ := hψ
  obtain ⟨a, rfl⟩ := π.surjective b
  refine ⟨a, MulEquiv.ext fun x => ?_⟩
  apply π.injective
  have := congrArg (fun α : MulAut (StatedProj (StatedSp 3 (ZMod 2))) => α (π x)) hb
  simpa [MulAut.conj_apply, MulAut.congr_apply] using this.symm

end Out

section Lagrangian

open CFSG.HardMathSupport.Curtis.NaturalModuleCensus.Symplectic (spMat_mulVec_mem_of_mem_stabilizer)

theorem sq_eq_one_of_fixes_lagrangian {g : StatedSp 3 (ZMod 2)}
    (hfix : ∀ x ∈ flag 3 (ZMod 2) 3, spMat g *ᵥ x = x) : g ^ 2 = 1 := by
  apply Symplectic.spMat_injective
  rw [Symplectic.spMat_pow, Symplectic.spMat_one, pow_two]
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun y => ?_
  simp only [Matrix.toLin'_apply, Matrix.one_mulVec, ← Matrix.mulVec_mulVec]
  set n : Fin 3 ⊕ Fin 3 → ZMod 2 := spMat g *ᵥ y - y with hn
  have hnF : n ∈ flag 3 (ZMod 2) 3 := by
    rw [SymplecticFlag.mem_flag_of_le le_rfl, SymplecticFlag.mem_isoFlag]
    refine ⟨fun j => ?_, fun j hj => absurd j.2 (by omega)⟩
    have hek : (Pi.single (Sum.inl j) 1 : Fin 3 ⊕ Fin 3 → ZMod 2) ∈ flag 3 (ZMod 2) 3 :=
      Symplectic.single_mem_flag le_rfl j j.2 j.2
    have h1 := Symplectic.pairedSympForm_spMat_mulVec g (Pi.single (Sum.inl j) 1) y
    rw [hfix _ hek] at h1
    have h2 : pairedSympForm (ZMod 2) 3 (Pi.single (Sum.inl j) 1) n = 0 := by
      rw [hn, map_sub, h1, sub_self]
    rwa [SymplecticFlag.pairedSympForm_single_inl] at h2
  have hgn : spMat g *ᵥ n = n := hfix n hnF
  have hgy : spMat g *ᵥ y = y + n := by rw [hn]; abel
  calc spMat g *ᵥ (spMat g *ᵥ y) = spMat g *ᵥ (y + n) := by rw [← hgy]
    _ = spMat g *ᵥ y + n := by rw [Matrix.mulVec_add, hgn]
    _ = y + n + n := by rw [hgy]
    _ = y + (n + n) := by abel
    _ = y := by rw [add_self_vec, add_zero]

@[expose] def resEnd (g : StatedSp 3 (ZMod 2))
    (hg : ∀ x ∈ flag 3 (ZMod 2) 3, spMat g *ᵥ x ∈ flag 3 (ZMod 2) 3) :
    Module.End (ZMod 2) ↥(flag 3 (ZMod 2) 3) :=
  (Matrix.mulVecLin (spMat g)).restrict hg

theorem stab_mem_lagrangian (g : ↥(flagStabilizer 3 (ZMod 2) {3})) :
    ∀ x ∈ flag 3 (ZMod 2) 3, spMat g.1 *ᵥ x ∈ flag 3 (ZMod 2) 3 := fun _ hx =>
  spMat_mulVec_mem_of_mem_stabilizer
    (SymplecticHigher.mem_flagStabilizer.mp g.2 3 (Set.mem_singleton 3)) hx

theorem resEnd_apply (g : StatedSp 3 (ZMod 2))
    (hg : ∀ x ∈ flag 3 (ZMod 2) 3, spMat g *ᵥ x ∈ flag 3 (ZMod 2) 3)
    (x : ↥(flag 3 (ZMod 2) 3)) : ((resEnd g hg x : ↥(flag 3 (ZMod 2) 3)) : Fin 3 ⊕ Fin 3 → ZMod 2) =
      spMat g *ᵥ (x : Fin 3 ⊕ Fin 3 → ZMod 2) := rfl

@[expose] def resUnit (g : ↥(flagStabilizer 3 (ZMod 2) {3})) :
    (Module.End (ZMod 2) ↥(flag 3 (ZMod 2) 3))ˣ :=
  ⟨resEnd g.1 (stab_mem_lagrangian g), resEnd g.1⁻¹ (stab_mem_lagrangian g⁻¹),
    LinearMap.ext fun x => Subtype.ext (by
      simp only [Module.End.mul_apply, resEnd_apply, Matrix.mulVec_mulVec,
        Symplectic.spMat_mul_inv, Matrix.one_mulVec, Module.End.one_apply]),
    LinearMap.ext fun x => Subtype.ext (by
      simp only [Module.End.mul_apply, resEnd_apply, Matrix.mulVec_mulVec,
        Symplectic.spMat_inv_mul, Matrix.one_mulVec, Module.End.one_apply])⟩

@[expose] def resHom : ↥(flagStabilizer 3 (ZMod 2) {3}) →*
    (Module.End (ZMod 2) ↥(flag 3 (ZMod 2) 3))ˣ :=
  MonoidHom.mk' resUnit (fun g h => Units.ext (LinearMap.ext fun x => Subtype.ext (by
    show spMat (g * h).1 *ᵥ (x : Fin 3 ⊕ Fin 3 → ZMod 2) =
      spMat g.1 *ᵥ (spMat h.1 *ᵥ (x : Fin 3 ⊕ Fin 3 → ZMod 2))
    rw [Subgroup.coe_mul, Symplectic.spMat_mul, Matrix.mulVec_mulVec])))

theorem card_units_end_lagrangian :
    Nat.card (Module.End (ZMod 2) ↥(flag 3 (ZMod 2) 3))ˣ = 168 := by
  have hfr : Module.finrank (ZMod 2) ↥(flag 3 (ZMod 2) 3) = 3 :=
    SymplecticHigher.finrank_flag (r := 3) (K := ZMod 2) (by norm_num)
  let b := Module.finBasisOfFinrankEq (ZMod 2) ↥(flag 3 (ZMod 2) 3) hfr
  let e : Matrix (Fin 3) (Fin 3) (ZMod 2) ≃* Module.End (ZMod 2) ↥(flag 3 (ZMod 2) 3) :=
    (Matrix.toLinAlgEquiv b).toMulEquiv
  have h1 : Nat.card (Module.End (ZMod 2) ↥(flag 3 (ZMod 2) 3))ˣ =
      Nat.card (GL (Fin 3) (ZMod 2)) := Nat.card_congr (Units.mapEquiv e).toEquiv.symm
  rw [h1, Matrix.card_GL_field]
  simp [Fin.prod_univ_three]

theorem card_pGroup_le_three_lagrangian (A : Subgroup (StatedSp 3 (ZMod 2)))
    (hA : A ≤ flagStabilizer 3 (ZMod 2) {3}) (hA3 : IsPGroup 3 A) : Nat.card A ≤ 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let ρ : ↥A →* (Module.End (ZMod 2) ↥(flag 3 (ZMod 2) 3))ˣ :=
    resHom.comp (Subgroup.inclusion hA)
  have hinj : Function.Injective ρ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro g hg
    rw [MonoidHom.mem_ker] at hg
    have hfix : ∀ x ∈ flag 3 (ZMod 2) 3, spMat g.1 *ᵥ x = x := by
      intro x hx
      have := congrArg (fun u : (Module.End (ZMod 2) ↥(flag 3 (ZMod 2) 3))ˣ =>
        ((u.val ⟨x, hx⟩ : ↥(flag 3 (ZMod 2) 3)) : Fin 3 ⊕ Fin 3 → ZMod 2)) hg
      exact this
    have hsq : g.1 ^ 2 = 1 := sq_eq_one_of_fixes_lagrangian hfix
    obtain ⟨k, hk⟩ := hA3 g
    have hk' : g.1 ^ (3 ^ k) = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have hord : orderOf g.1 ∣ Nat.gcd 2 (3 ^ k) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hsq) (orderOf_dvd_of_pow_eq_one hk')
    have hcop : Nat.gcd 2 (3 ^ k) = 1 := Nat.Coprime.pow_right k (by norm_num)
    rw [hcop, Nat.dvd_one, orderOf_eq_one_iff] at hord
    rw [Subgroup.mem_bot]
    exact Subtype.ext hord
  have hdvd := Subgroup.card_dvd_of_injective ρ hinj
  rw [card_units_end_lagrangian] at hdvd
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hA3
  rw [hn] at hdvd ⊢
  rcases n with _ | _ | n
  · norm_num
  · norm_num
  · exfalso
    have h9 : 9 ∣ 3 ^ (n + 2) := ⟨3 ^ n, by rw [pow_add]; ring⟩
    have := h9.trans hdvd
    omega

theorem card_pGroup_le_three_conj {g : StatedSp 3 (ZMod 2)} {J : Subgroup (StatedSp 3 (ZMod 2))}
    (hJ : ∀ x, x ∈ J ↔ g * x * g⁻¹ ∈ flagStabilizer 3 (ZMod 2) {3})
    (A : Subgroup (StatedSp 3 (ZMod 2))) (hA : A ≤ J) (hA3 : IsPGroup 3 A) : Nat.card A ≤ 3 := by
  have h1 : A.map (MulAut.conj g).toMonoidHom ≤ flagStabilizer 3 (ZMod 2) {3} := by
    rintro _ ⟨x, hx, rfl⟩
    exact (hJ x).1 (hA hx)
  have h2 := card_pGroup_le_three_lagrangian _ h1 (hA3.map _)
  rwa [Subgroup.card_map_of_injective (MulAut.conj g).injective] at h2

end Lagrangian

section Outer

variable {Y : Type} [Group Y] [Finite Y] {Lb Pb : Subgroup Y}

omit [Finite Y] in
theorem exists_outer_hom (hperf : Group.IsPerfect ↥Lb) {X : Type} [Group X] [Finite X]
    (e : ↥Lb ⧸ Subgroup.center ↥Lb ≃* X) (hOut : ∀ φ : MulAut X, ∃ a : X, φ = MulAut.conj a)
    {J : Subgroup X}
    (hJ : J = (Pb.subgroupOf Lb).map
      (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥Lb))))
    (hself : ∀ a : X, (∀ x, x ∈ J ↔ a * x * a⁻¹ ∈ J) → a ∈ J)
    (hcard : ∀ A : Subgroup X, A ≤ J → IsPGroup 3 A → Nat.card A ≤ 3)
    (U : Subgroup Y) (hUL : U ≤ Subgroup.normalizer (Lb : Set Y))
    (hUP : U ≤ Subgroup.normalizer (Pb : Set Y)) (hU3 : IsPGroup 3 U) :
    ∃ φ : ↥U →* MulAut X, (∀ u : ↥U, φ u = 1 → (u : Y) ∈ Subgroup.centralizer (Lb : Set Y)) ∧
      (∀ a b : ↥U, φ a * φ b = φ b * φ a) ∧ Nat.card φ.range ≤ 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set φ : ↥U →* MulAut X := (descendHom e).comp (Subgroup.inclusion hUL) with hφ
  have hφapply : ∀ u : ↥U, φ u = descendAut e (u : Y) (hUL u.2) := fun u => rfl
  have hker : ∀ u : ↥U, φ u = 1 → (u : Y) ∈ Subgroup.centralizer (Lb : Set Y) := by
    intro u hu
    rw [hφapply] at hu
    have := hperf
    have h := inv_mul_mem_centralizer_of_descendAut_eq_conj e (hUL u.2) 1 (by
      rw [hu]
      have : e (QuotientGroup.mk (1 : ↥Lb)) = 1 := by
        rw [QuotientGroup.mk_one, map_one]
      rw [this, map_one])
    simpa using h
  have hmaps : ∀ u : ↥U, ∀ x ∈ J, φ u x ∈ J := by
    intro u x hx
    rw [hJ] at hx ⊢
    obtain ⟨l, hl, rfl⟩ := hx
    rw [hφapply]
    show descendAut e (u : Y) (hUL u.2)
      (e (QuotientGroup.mk l)) ∈ _
    rw [descendAut_apply]
    refine ⟨conjL (u : Y) (hUL u.2) l, ?_, rfl⟩
    have hl' : l ∈ Pb.subgroupOf Lb := hl
    show conjL (u : Y) (hUL u.2) l ∈ Pb.subgroupOf Lb
    rw [Subgroup.mem_subgroupOf] at hl' ⊢
    simpa using (Subgroup.mem_normalizer_iff.1 (hUP u.2) (l : Y)).1 hl'
  have hinner : ∀ u : ↥U, ∃ a ∈ J, φ u = MulAut.conj a := by
    intro u
    obtain ⟨a, ha⟩ := hOut (φ u)
    refine ⟨a, hself a fun x => ⟨fun hx => ?_, fun hx => ?_⟩, ha⟩
    · have := hmaps u x hx
      rwa [ha, MulAut.conj_apply] at this
    · have := hmaps u⁻¹ _ hx
      rw [map_inv, ha] at this
      simpa [MulAut.conj_apply, mul_assoc] using this
  set ψ0 : ↥J →* MulAut X := (MulAut.conj : X →* MulAut X).comp J.subtype with hψ0
  have hRle : φ.range ≤ ψ0.range := by
    rintro _ ⟨u, rfl⟩
    obtain ⟨a, ha, hua⟩ := hinner u
    exact ⟨⟨a, ha⟩, hua.symm⟩
  have hRp : IsPGroup 3 ↥φ.range := hU3.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  have hPmap : (φ.range.comap ψ0).map ψ0 = φ.range := by
    rw [Subgroup.map_comap_eq]
    exact inf_eq_right.2 hRle
  obtain ⟨R', -, hR'3, hR'map⟩ := exists_pSubgroup_map_eq Nat.prime_three hPmap hRp
  have hR'J : R'.map J.subtype ≤ J := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hc1 := hcard _ hR'J (hR'3.map _)
  rw [Subgroup.card_map_of_injective J.subtype_injective] at hc1
  have hc2 : Nat.card φ.range ≤ Nat.card R' := by
    rw [← hR'map]
    exact Nat.card_le_card_of_surjective _ (ψ0.subgroupMap_surjective R')
  have hcardR : Nat.card φ.range ≤ 3 := hc2.trans hc1
  refine ⟨φ, hker, ?_, hcardR⟩
  have hcyc : IsCyclic ↥φ.range := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hRp
    rcases n with _ | _ | n
    · have : Nat.card ↥φ.range = 1 := by simpa using hn
      have := (Nat.card_eq_one_iff_unique.1 this).1
      infer_instance
    · exact isCyclic_of_prime_card (p := 3) (by simpa using hn)
    · exfalso
      rw [hn] at hcardR
      have h9 : 9 ≤ 3 ^ (n + 1 + 1) := by
        calc 9 = 3 ^ 2 := by norm_num
          _ ≤ 3 ^ (n + 1 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
  intro a b
  let _ := hcyc
  let _ : CommGroup ↥φ.range := IsCyclic.commGroup
  have := mul_comm (⟨φ a, a, rfl⟩ : ↥φ.range) ⟨φ b, b, rfl⟩
  exact congrArg Subtype.val this

end Outer

end CFSG.HardMathSupport.Curtis.UnitaryLevi
