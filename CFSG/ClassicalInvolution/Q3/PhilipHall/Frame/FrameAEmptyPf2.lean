module

public import CFSG.ClassicalInvolution.Q3.Q3T6DSetupB
public import CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge.FrameCore
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TightFamily

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

namespace FrameAEmptyPf

open CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge (FrameSimple FrameCore)

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3CII CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3.Q3T6D

section Defs

variable {G : Type} [Group G] [Finite G]

structure FrameIIHyp (K J : Subgroup G) (z t a g : G) : Prop where
  nonabelian : ∃ x y : G, x * y ≠ y * x
  gen : (⨆ M ∈ CoreAssembly.conjClass K, M) = ⊤
  hyp : HypOmegaGen (CoreAssembly.conjClass K)
  cls : Q3CL.ClassicalClause (CoreAssembly.conjClass K)
  twoGroup : IsPGroup 2 (↥K ⧸ classicalInvolutionOddCore ↥K)
  sylow8 : ∀ P : Subgroup G, IsSylow2In P K → Nat.card ↥P = 8
  viol : AViol (CoreAssembly.conjClass K) K J z t
  ha : a ∈ pairNormalizers K J z t
  haz : a * t * a⁻¹ = z
  hne : conjSub a J ≠ K
  hg : conjSub g K = conjSub a J
  hgz : g * z * g⁻¹ = z
  star : aStar (CoreAssembly.conjClass K) K = CoreAssembly.conjClass K

structure Std20Frame (K K' J : Subgroup G) (S : Sylow 2 G) (R R' W V : Subgroup G) (z t : G) :
    Prop where
  nonabelian : ∃ x y : G, x * y ≠ y * x
  gen : (⨆ M ∈ CoreAssembly.conjClass K, M) = ⊤
  hyp : HypOmegaGen (CoreAssembly.conjClass K)
  cls : Q3CL.ClassicalClause (CoreAssembly.conjClass K)
  twoGroup : IsPGroup 2 (↥K ⧸ classicalInvolutionOddCore ↥K)
  card8 : Nat.card ↥R = 8
  viol : AViol (CoreAssembly.conjClass K) K J z t
  ne : K' ≠ K
  twins : twinSet (CoreAssembly.conjClass K) K = {K, K'}
  swap : ∃ g ∈ Subgroup.centralizer ({z} : Set G), conjSub g K = K'
  htKK : t ∈ K ⊔ K'
  star : aStar (CoreAssembly.conjClass K) K = CoreAssembly.conjClass K
  hSz : (S : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G)
  hR : IsSylow2In R K
  hRS : R ≤ (S : Subgroup G)
  hR' : IsSylow2In R' K'
  hR'S : R' ≤ (S : Subgroup G)
  hRG : ∀ T ∈ RSet (CoreAssembly.conjClass K), T ≤ (S : Subgroup G) → T = R ∨ T = R'
  hW : W ∈ WSet (CoreAssembly.conjClass K)
  hWS : W ≤ (S : Subgroup G)
  hWN : (S : Subgroup G) ≤ Subgroup.normalizer (W : Set G)
  hV : V ∈ USet (CoreAssembly.conjClass K)
  hVS : V ≤ (S : Subgroup G)
  hVW : V ≤ W
  htV : t ∈ V

end Defs

section Datum

variable {T : Type} [Group T] [Finite T]

theorem card_sylow_of_datum {R : Subgroup T} {t : T} (hD : FrameTightDatum R t) {P : Subgroup T}
    (hP : IsSylow2In P R) : Nat.card ↥P = 8 := by
  obtain ⟨e⟩ := hD.quat P hP
  have h1 : Nat.card ↥P = Fintype.card (QuaternionGroup 2) := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
  rw [h1, QuaternionGroup.card]

end Datum

section Setup

theorem aviol_ne_involution {Y : Type} [Group Y] [Finite Y] {Λ : Set (Subgroup Y)}
    (hΩ : HypOmegaGen Λ) {K J : Subgroup Y} {zK zJ : Y} (hK : K ∈ Λ)
    (h : AViol Λ K J zK zJ) : zJ ≠ zK := by
  intro he
  subst he
  refine h.not_nbr ?_
  obtain ⟨R, hR, hRJ, -⟩ := exists_mem_RSet_ge h.mem (isPGroup_two_bot' (G := Y)) bot_le
  exact ⟨h.mem, h.ne, R, hR, hRJ.1,
    hRJ.1.trans (Sec6Gen.le_normalizer_of_twin hΩ h.mem hK h.ne h.hzJ h.hzK)⟩

variable {G : Type} [Group G] [Finite G] {K J : Subgroup G} {z t a g : G}

theorem std20Frame_of_nbrTwin (h : FrameIIHyp K J z t a g)
    (hn : ∀ L ∈ omegaNbr (CoreAssembly.conjClass K) K, L ∈ twinSet (CoreAssembly.conjClass K) K) :
    ∃ (K' : Subgroup G) (S : Sylow 2 G) (R R' W V : Subgroup G),
      Std20Frame K K' J S R R' W V z t := by
  have hΩ : HypOmegaGen (CoreAssembly.conjClass K) := h.hyp
  have hKΩ : K ∈ CoreAssembly.conjClass K := CoreAssembly.mem_conjClass_self K
  have hJΩ : J ∈ CoreAssembly.conjClass K := h.viol.mem
  have hzK := h.viol.hzK
  have hzJ := h.viol.hzJ
  obtain ⟨v, Ks, hVU, hVJ, hVsyl, -, htw, hvv⟩ :=
    exists_hexagon_data3 hΩ hKΩ hJΩ hzK hzJ h.viol.star h.viol.not_nbr h.viol.no_conj
  set K' : Subgroup G := conjSub a J with hK'
  have hK'Ω : K' ∈ CoreAssembly.conjClass K := hΩ.conjInvariant a J hJΩ
  have hzK' : IsUniqueInvolution K' z := by
    have := hzJ.conj a
    rwa [h.haz] at this
  have hK'tw : K' ∈ twinSet (CoreAssembly.conjClass K) K := ⟨hK'Ω, z, hzK, hzK'⟩
  have hK's : K' = Ks := by
    rw [htw] at hK'tw
    rcases hK'tw with h1 | h1
    · exact absurd h1 h.hne
    · exact h1
  have htw' : twinSet (CoreAssembly.conjClass K) K = {K, K'} := by rw [htw, hK's]
  have hvv' : v * v ∈ K ⊔ K' := by rw [hK's]; exact hvv
  have hV2 : IsPGroup 2 (Subgroup.zpowers v) := Sec6Gen.isPGroup_of_mem_USet hΩ hVU
  obtain ⟨-, -, -, -, -, -, hVc, -, h4V⟩ := Sec6Gen.exists_data_of_mem_USet hΩ hVU
  have htV : t ∈ Subgroup.zpowers v :=
    mem_of_isPGroup hzJ hVJ hV2 (by omega)
  have htKK : t ∈ K ⊔ K' := by
    obtain ⟨w, hw, hww⟩ := exists_sq_eq_of_cyclic hzJ hVJ hVc hV2 h4V
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    rw [← hww, ← (Commute.refl v).mul_zpow]
    exact Subgroup.zpow_mem _ hvv' k
  have hswap : ∃ g' ∈ Subgroup.centralizer ({z} : Set G), conjSub g' K = K' :=
    ⟨g, Subgroup.mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp h.hgz), h.hg⟩
  have hKN : K ≤ Subgroup.normalizer (K' : Set G) :=
    Sec6Gen.le_normalizer_of_twin hΩ hKΩ hK'Ω (Ne.symm h.hne) hzK hzK'
  have hK'N : K' ≤ Subgroup.normalizer (K : Set G) :=
    Sec6Gen.le_normalizer_of_twin hΩ hK'Ω hKΩ h.hne hzK' hzK
  obtain ⟨S, hVS, hR, hR'⟩ := exists_sylow_setup hΩ.conjInvariant hzK hzK' htw' h.hne hKN hK'N
    hV2 (hVsyl.1.trans inf_le_right)
  have hRset : K ⊓ (S : Subgroup G) ∈ RSet (CoreAssembly.conjClass K) :=
    mem_RSet_of_isSylow2In hKΩ hR
  have hrset := rset_inf_sylow3 hΩ hKΩ hzK htw' hn S hR hR'
  have h8 := Sec6Gen.eight_le_of_mem_RSet hΩ hRset
  have hzR : z ∈ K ⊓ (S : Subgroup G) := mem_of_isPGroup hzK hR.1 hR.2.1 (by omega)
  have hRset' : K' ⊓ (S : Subgroup G) ∈ RSet (CoreAssembly.conjClass K) :=
    mem_RSet_of_isSylow2In hK'Ω hR'
  have h8' := Sec6Gen.eight_le_of_mem_RSet hΩ hRset'
  have hzR' : z ∈ K' ⊓ (S : Subgroup G) := mem_of_isPGroup hzK' hR'.1 hR'.2.1 (by omega)
  have hSz := sylow_le_centralizer hΩ.conjInvariant hzK hzK' S hR hR' hRset hzR hzR' hrset
  obtain ⟨η, hηS, hinv, hW, hWS, hWN⟩ := exists_W_setup3 hΩ S
  have hηS' : ∀ V ∈ η, V ≤ (S : Subgroup G) := fun V hV => (hηS.1 hV).2
  have hVW : Subgroup.zpowers v ≤ ⨆ U ∈ η, U := by
    obtain ⟨V', ⟨hV'η, hcase⟩, -⟩ := Sec6Gen.six_eight hΩ S hVU hVS ⟨S, hηS, hinv⟩ hηS'
    rcases hcase with h1 | h1
    · rw [h1]
      exact le_iSup₂ (f := fun U (_ : U ∈ η) => U) V' hV'η
    · exfalso
      have hle : Subgroup.zpowers v ⊔ V' ≤ (S : Subgroup G) := sup_le hVS (hηS' V' hV'η)
      rcases hrset _ h1 hle with h2 | h2
      · have hmem : t ∈ Subgroup.zpowers v ⊔ V' := Subgroup.mem_sup_left htV
        rw [h2] at hmem
        have htK : t ∈ K := (Subgroup.mem_inf.mp hmem).1
        rcases hzK.unique t htK hzJ.sq with h3 | h3
        · exact hzJ.ne_one h3
        · exact aviol_ne_involution hΩ hKΩ h.viol h3
      · have hmem : t ∈ Subgroup.zpowers v ⊔ V' := Subgroup.mem_sup_left htV
        rw [h2] at hmem
        have htK : t ∈ K' := (Subgroup.mem_inf.mp hmem).1
        rcases hzK'.unique t htK hzJ.sq with h3 | h3
        · exact hzJ.ne_one h3
        · exact aviol_ne_involution hΩ hKΩ h.viol h3
  exact ⟨K', S, K ⊓ (S : Subgroup G), K' ⊓ (S : Subgroup G), ⨆ U ∈ η, U, Subgroup.zpowers v,
    ⟨h.nonabelian, h.gen, h.hyp, h.cls, h.twoGroup, h.sylow8 _ hR, h.viol, h.hne, htw', hswap, htKK,
      h.star, hSz, hR, inf_le_right, hR', inf_le_right, hrset, hW, hWS, hWN, hVU, hVS, hVW, htV⟩⟩

end Setup

section Steps

@[expose] def FrameC204 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [FrameCore G] (K K' J : Subgroup G) (S : Sylow 2 G)
    (R R' W V : Subgroup G) (z t : G), Std20Frame K K' J S R R' W V z t →
      Concl20_4 S K K' J z

@[expose] def FrameC208 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [FrameCore G] (K K' J : Subgroup G) (S : Sylow 2 G)
    (R R' W V : Subgroup G) (z t : G), Std20Frame K K' J S R R' W V z t →
      Concl20_7 S K K' z → Concl20_8 S K' R

end Steps

end FrameAEmptyPf

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
