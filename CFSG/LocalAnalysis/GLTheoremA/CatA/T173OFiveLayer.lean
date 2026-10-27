module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OFiveDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcAssemblyE
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcAssemblyTw
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeBlock
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeDiagTwisted
public import CFSG.LocalAnalysis.StandardType.GGSixBstarE6ThreeFaithful
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotNeighbourParam
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcLeviToral
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4TorusFrame
public import CFSG.HardMathSupport.Solomon.Coordinator.B3FamPC
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Graph.Transfer
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma28
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Interface
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeDiag
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwRigid
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.PlanesSetup
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidCriterion
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidNorm
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.ExcInnerTorus
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LangFrame
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs16
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsCE
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsElim
public import CFSG.LocalAnalysis.GLTheoremA.S3.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4.Assembly
public import CFSG.LocalAnalysis.GLTheoremA.S4.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4S.Inputs
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
public import CFSG.RankThree.PartOne.KE.E7FiveBlock
public import CFSG.RankThree.PartTwo.Sec8.Item87Proof84
public import Certificates.Certificate13659
public import Certificates.Certificate13660
public import Certificates.Certificate17002
public import Certificates.Certificate17951

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173O

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.StandardType
open CFSG.StandardType.TableBExc.E6Three
open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.HardMathSupport.Timmesfeld.CrossChar

theorem eq_of_lift_perfect {S G L : Type} [Group S] [Group G] [Group L] [Group.IsPerfect L]
    (π : S →* G) (hπ : π.ker ≤ Subgroup.center S) (ψ : L →* S)
    (hψ : Function.Injective (π.comp ψ)) (α : MulAut S) (ᾱ : MulAut G)
    (hαπ : ∀ s, π (α s) = ᾱ (π s)) (hN : ∀ l, ∃ l', ᾱ (π (ψ l)) = π (ψ l')) {g : L}
    (hg : ᾱ (π (ψ g)) = π (ψ g)) : α (ψ g) = ψ g := by
  let f : L → L := fun l => (hN l).choose
  have hf : ∀ l, ᾱ (π (ψ l)) = π (ψ (f l)) := fun l => (hN l).choose_spec
  let β : L →* L :=
    { toFun := f
      map_one' := by
        apply hψ
        have h := hf 1
        simpa [MonoidHom.comp_apply] using h.symm
      map_mul' := by
        intro l m
        apply hψ
        have hlm := hf (l * m)
        have hl := hf l
        have hm := hf m
        simp only [MonoidHom.comp_apply, map_mul]
        rw [← hlm, ← hl, ← hm]
        simp only [map_mul] }
  have hβg : β g = g := by
    apply hψ
    have h : ᾱ (π (ψ g)) = π (ψ (β g)) := (hN g).choose_spec
    rw [hg] at h
    simpa [MonoidHom.comp_apply] using h.symm
  have hcomm : α.toMonoidHom.comp ψ = ψ.comp β := by
    refine CFSG.SeitzReduction.LinearPilot.eq_of_comp_eq_of_ker_le_center hπ ?_
    intro l
    have hl : ᾱ (π (ψ l)) = π (ψ (β l)) := (hN l).choose_spec
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [hαπ, hl]
  have h := DFunLike.congr_fun hcomm g
  simpa [MonoidHom.comp_apply, hβg] using h

section E6Layer


private theorem map_fixSubgroup_hatAut_eq {F : Type} [Field F] {d : ModGL Tag.E6 F}
    (hd : d ∈ hatGroup Tag.E6 F) :
    (fixSubgroup (hatAut Tag.E6 F ⟨d, hd⟩)).map (adjointGroup Tag.E6 F).subtype =
      adjointGroup Tag.E6 F ⊓ Subgroup.centralizer ({d} : Set (ModGL Tag.E6 F)) := by
  ext x
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.2, ?_⟩
    change (y : ModGL Tag.E6 F) ∈ Subgroup.centralizer ({d} : Set (ModGL Tag.E6 F))
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : d * (y : ModGL Tag.E6 F) * d⁻¹ = (y : ModGL Tag.E6 F) := by
      simpa [coe_hatAut_apply] using congrArg Subtype.val hy
    calc (y : ModGL Tag.E6 F) * d = (d * (y : ModGL Tag.E6 F) * d⁻¹) * d := by rw [h1]
      _ = d * (y : ModGL Tag.E6 F) := by group
  · rintro ⟨hxG, hxc⟩
    refine ⟨⟨x, hxG⟩, ?_, rfl⟩
    rw [mem_fixSubgroup]
    refine Subtype.ext ?_
    rw [coe_hatAut_apply]
    change x ∈ Subgroup.centralizer ({d} : Set (ModGL Tag.E6 F)) at hxc
    rw [Subgroup.mem_centralizer_singleton_iff] at hxc
    calc d * x * d⁻¹ = (x * d) * d⁻¹ := by rw [← hxc]
      _ = x := by group

theorem le_stdLayerD_E6_of_perfect {F : Type} [Field F] [Finite F] [CharP F 2]
    {d : ModGL Tag.E6 F} (hd : d ∈ hatGroup Tag.E6 F) (hd1 : d ≠ 1)
    (hd3 : d ^ 3 = 1) {X : Subgroup (ModGL Tag.E6 F)} (hXG : X ≤ adjointGroup Tag.E6 F)
    (hXd : X ≤ Subgroup.centralizer ({d} : Set (ModGL Tag.E6 F))) (hX : ⁅X, X⁆ = X) :
    X ≤ stdLayerD (adjointGroup Tag.E6 F) d := by
  set β : MulAut ↥(adjointGroup Tag.E6 F) := hatAut Tag.E6 F ⟨d, hd⟩ with hβdef
  have hd3' : (⟨d, hd⟩ : ↥(hatGroup Tag.E6 F)) ^ 3 = 1 := by
    refine Subtype.ext ?_
    simpa using hd3
  have hβ : β ^ 3 = 1 := by
    rw [hβdef, ← map_pow, hd3', map_one]
  have hβ1 : β ≠ 1 := by
    rw [hβdef]
    intro h
    have h1 : (⟨d, hd⟩ : ↥(hatGroup Tag.E6 F)) = 1 :=
      CFSG.StandardType.NoOffE6Three.hatAut_injective (τ := Tag.E6) (K := F)
        (by rw [h, map_one])
    exact hd1 (by simpa using congrArg Subtype.val h1)
  have h3F : ¬ 3 ∣ Nat.card F := by
    haveI : Fintype F := Fintype.ofFinite F
    obtain ⟨n, -, hcard⟩ := FiniteField.card F 2
    intro h3
    rw [Nat.card_eq_fintype_card, hcard] at h3
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)
  have hmon : MonomialToralAt Tag.E6 3 := monomialToralAt_E6_three
  have hPI : PerfectInLayer β :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.perfectInLayer_exc_E
      (τ := Tag.E6) (K := F) (p := 3) (Or.inl rfl) Nat.prime_three (by norm_num) h3F hmon β hβ
      hβ1
  let P : Subgroup ↥(adjointGroup Tag.E6 F) := X.subgroupOf (adjointGroup Tag.E6 F)
  have hPfix : P ≤ fixSubgroup β := by
    intro x hx
    rw [mem_fixSubgroup]
    refine Subtype.ext ?_
    rw [hβdef, coe_hatAut_apply]
    have hxc : (x : ModGL Tag.E6 F) ∈ Subgroup.centralizer ({d} : Set (ModGL Tag.E6 F)) :=
      hXd hx
    rw [Subgroup.mem_centralizer_singleton_iff] at hxc
    calc d * (x : ModGL Tag.E6 F) * d⁻¹ = ((x : ModGL Tag.E6 F) * d) * d⁻¹ := by rw [← hxc]
      _ = (x : ModGL Tag.E6 F) := by group
  have hPperf : ⁅P, P⁆ = P := by
    have hmap : Subgroup.map (adjointGroup Tag.E6 F).subtype ⁅P, P⁆ =
        Subgroup.map (adjointGroup Tag.E6 F).subtype P := by
      rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hXG, hX]
    exact Subgroup.map_injective (adjointGroup Tag.E6 F).subtype_injective hmap
  have hle : P.map (adjointGroup Tag.E6 F).subtype ≤
      (GLALayer (fixSubgroup β)).map (adjointGroup Tag.E6 F).subtype :=
    Subgroup.map_mono (hPI P hPfix hPperf)
  rw [Subgroup.map_subgroupOf_eq_of_le hXG,
    ← CFSG.LocalAnalysis.GLTheoremA.Y10F.glaLayer_map (adjointGroup Tag.E6 F).subtype_injective,
    map_fixSubgroup_hatAut_eq hd] at hle
  simpa [stdLayerD] using hle

end E6Layer

section TwE6Layer

local notation "Γ₂" F => ModGL TwistTag.E6.tag F


private theorem map_fixSubgroup_twistedE6InndiagConj_eq {F : Type} [Field F] {σ : F ≃+* F}
    {d : Γ₂ F} (hd : d ∈ twistedE6InndiagGL F σ) :
    (fixSubgroup (twistedE6InndiagConj F σ ⟨d, hd⟩)).map (twistedE6RootGroup F σ).subtype =
      twistedE6RootGroup F σ ⊓ Subgroup.centralizer ({d} : Set (Γ₂ F)) := by
  ext x
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.2, ?_⟩
    change (y : Γ₂ F) ∈ Subgroup.centralizer ({d} : Set (Γ₂ F))
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : d * (y : Γ₂ F) * d⁻¹ = (y : Γ₂ F) := by
      simpa [twistedE6InndiagConj_apply] using congrArg Subtype.val hy
    calc (y : Γ₂ F) * d = (d * (y : Γ₂ F) * d⁻¹) * d := by rw [h1]
      _ = d * (y : Γ₂ F) := by group
  · rintro ⟨hxG, hxc⟩
    refine ⟨⟨x, hxG⟩, ?_, rfl⟩
    rw [mem_fixSubgroup]
    refine Subtype.ext ?_
    rw [twistedE6InndiagConj_apply]
    change x ∈ Subgroup.centralizer ({d} : Set (Γ₂ F)) at hxc
    rw [Subgroup.mem_centralizer_singleton_iff] at hxc
    calc d * x * d⁻¹ = (x * d) * d⁻¹ := by rw [← hxc]
      _ = x := by group

theorem le_stdLayerD_twE6_of_perfect {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 1 ≤ n)
    (hF : Nat.card F = (2 ^ n) ^ 2) (σ : F ≃+* F) (hσ : ∀ c, σ c = c ^ 2 ^ n) {d : Γ₂ F}
    (hd : d ∈ twistedE6InndiagGL F σ) (hd1 : d ≠ 1) (hd3 : d ^ 3 = 1) {X : Subgroup (Γ₂ F)}
    (hXG : X ≤ twistedE6RootGroup F σ) (hXd : X ≤ Subgroup.centralizer ({d} : Set (Γ₂ F)))
    (hX : ⁅X, X⁆ = X) : X ≤ stdLayerD (twistedE6RootGroup F σ) d := by
  set β : MulAut ↥(twistedE6RootGroup F σ) := twistedE6InndiagConj F σ ⟨d, hd⟩ with hβdef
  have hd3' : (⟨d, hd⟩ : ↥(twistedE6InndiagGL F σ)) ^ 3 = 1 := by
    refine Subtype.ext ?_
    simpa using hd3
  have hβ : β ^ 3 = 1 := by
    rw [hβdef, ← map_pow, hd3', map_one]
  have hβ1 : β ≠ 1 := by
    rw [hβdef]
    intro h
    have h1 : (⟨d, hd⟩ : ↥(twistedE6InndiagGL F σ)) = 1 :=
      twistedE6InndiagConj_injective (ℓ := 2) (f := n) Nat.prime_two hn hF σ hσ
        (by rw [h, map_one])
    exact hd1 (by simpa using congrArg Subtype.val h1)
  have hmon : MonomialToralAt Tag.E6 3 := monomialToralAt_E6_three
  have hPI : PerfectInLayer β :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.perfectInLayer_exc_twE6
      (ℓ := 2) (f := n) Nat.prime_two hn hF σ hσ (p := 3) Nat.prime_three (by norm_num)
      (by norm_num) hmon β hβ hβ1
  let P : Subgroup ↥(twistedE6RootGroup F σ) := X.subgroupOf (twistedE6RootGroup F σ)
  have hPfix : P ≤ fixSubgroup β := by
    intro x hx
    rw [mem_fixSubgroup]
    refine Subtype.ext ?_
    rw [hβdef, twistedE6InndiagConj_apply]
    have hxc : (x : Γ₂ F) ∈ Subgroup.centralizer ({d} : Set (Γ₂ F)) := hXd hx
    rw [Subgroup.mem_centralizer_singleton_iff] at hxc
    calc d * (x : Γ₂ F) * d⁻¹ = ((x : Γ₂ F) * d) * d⁻¹ := by rw [← hxc]
      _ = (x : Γ₂ F) := by group
  have hPperf : ⁅P, P⁆ = P := by
    have hmap : Subgroup.map (twistedE6RootGroup F σ).subtype ⁅P, P⁆ =
        Subgroup.map (twistedE6RootGroup F σ).subtype P := by
      rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hXG, hX]
    exact Subgroup.map_injective (twistedE6RootGroup F σ).subtype_injective hmap
  have hle : P.map (twistedE6RootGroup F σ).subtype ≤
      (GLALayer (fixSubgroup β)).map (twistedE6RootGroup F σ).subtype :=
    Subgroup.map_mono (hPI P hPfix hPperf)
  rw [Subgroup.map_subgroupOf_eq_of_le hXG,
    ← CFSG.LocalAnalysis.GLTheoremA.Y10F.glaLayer_map (twistedE6RootGroup F σ).subtype_injective,
    map_fixSubgroup_twistedE6InndiagConj_eq hd] at hle
  simpa [stdLayerD] using hle

end TwE6Layer

end CFSG.LocalAnalysis.GLTheoremA.T173O

end
