module

public import CFSG.ClassicalInvolution.SmallCases.G2SNorm2
public import CFSG.ClassicalInvolution.Asc77.AscT3TypedG2GenMax

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.NDB.G2S

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Gaps
  CFSG.ClassicalInvolution.RouteD.G2D4
open CFSG.Open (classicalInvolutionOddCore)

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

theorem exists_fund_of_involution_model (hp2 : p ≠ 2) {t : StatedLieTag} {n e : ℕ}
    (hadm : StatedLieAdmissible t n p e) (ht : t = .G2 ∨ t = .trialityD4)
    {u : (modelUniv t n p e Fact.out).K} (hu : u * u = 1) (hu1 : u ≠ 1) :
    ∃ R ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D, IsUniqueInvolution R u := by
  rcases ht with rfl | rfl
  · obtain ⟨hk, -⟩ := hadm.2.2
    subst hk
    exact Asc77.T3Typed.exists_fund_of_involution_g2 hp2 hadm hu hu1
  · have hk : n = 0 := hadm.2.2
    subst hk
    obtain ⟨R, hR, -, hRu⟩ := G2D4Models.exists_perfect_fund_of_involution hp2 hadm hu hu1
    exact ⟨R, hR, hRu⟩

namespace Ctx

variable {Ω : Set (Subgroup G)} {L : Subgroup G} {w : G}

theorem exists_member_of_involution (C : Ctx p f Ω L w)
    (D : LieSystemData p f (locQuot Ω w) (locFamily Ω w)) (i₁ : Fin D.card) (hcard : D.card = 2)
    (htag : D.tag i₁ = .G2 ∨ D.tag i₁ = .trialityD4)
    (hrest : ∀ i, i ≠ i₁ → D.tag i = .PSL ∧ D.rank i = 2)
    {x : (modelUniv (D.tag i₁) (D.rank i₁) p (D.exp i₁) Fact.out).K} (hx2 : x * x = 1)
    (hx1 : x ≠ 1) :
    ∃ (N : Subgroup G) (u : G) (hu : u ∈ locLayer Ω w), N ∈ nbhd Ω L ∧
      IsClassicalMember p f N u ∧
      QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω w)) ⟨u, hu⟩ = D.hom i₁ x := by
  classical
  obtain ⟨N₀, hN₀⟩ := C.nbhd_nonempty D i₁ htag
  obtain ⟨t₀, ht₀⟩ := C.inClass.classical N₀ hN₀.1
  obtain ⟨R, hR, -, r, hrR, hr2, hr1, hrc, hr⟩ :=
    C.exists_model_involution D i₁ hcard htag hrest hN₀ ht₀
  obtain ⟨R', hR', hR'u⟩ := exists_fund_of_involution_model C.odd (D.admissible i₁) htag hx2 hx1
  obtain ⟨g, hg⟩ := C.inv (D.tag i₁) (D.rank i₁) (D.exp i₁) C.odd htag (D.admissible i₁) R hR R'
    hR' r hrR x hR'u.mem hr2 hx2 hr1 hx1 hrc (fun y hy => hR'u.commute_of_mem hy)
  obtain ⟨y, hyL, hy⟩ := C.range_le_map_layer D i₁ hcard htag hrest ⟨g, rfl⟩
  have hyY : (y : G) ∈ centralizingLayer Ω {w} := y.2
  have ht₀Y : t₀ ∈ locLayer Ω w :=
    le_centralizingLayer (C.nbhd_mem_centralizingMembers hN₀) ht₀.mem
  have huY : (y : G) * t₀ * (y : G)⁻¹ ∈ locLayer Ω w :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ y.2 ht₀Y) (Subgroup.inv_mem _ y.2)
  refine ⟨conjSub (y : G) N₀, (y : G) * t₀ * (y : G)⁻¹, huY, C.conj_mem_nbhd hyY hN₀,
    ht₀.conj _, ?_⟩
  have e1 : (⟨(y : G) * t₀ * (y : G)⁻¹, huY⟩ : ↥(locLayer Ω w)) = y * ⟨t₀, ht₀Y⟩ * y⁻¹ :=
    Subtype.ext rfl
  rw [e1, map_mul, map_mul, map_inv]
  have hy' : QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω w)) y = D.hom i₁ g := hy
  have hr' : D.hom i₁ r = QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω w))
      ⟨t₀, ht₀Y⟩ := hr
  rw [hy', ← hr', ← map_inv, ← map_mul, ← map_mul, hg]

end Ctx

end CFSG.ClassicalInvolution.NDB.G2S
