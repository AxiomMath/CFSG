module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Tools
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87ReeCent
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvRee
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoOddLieReeCover
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Defs

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.Blueprint CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Local
open scoped commutatorElement

theorem reeTitsModel_of_mulEquiv {G G' : Type} [Group G] [Group G'] (e : G ≃* G') {f : ℕ}
    (h : ReeTitsModel G .twistedG2 3 f) : ReeTitsModel G' .twistedG2 3 f := by
  have h' := CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e (t := .twistedG2) (n := 0) (p := 3)
    (f := f) (Or.inr (Or.inr (Or.inl ⟨rfl, by simp [reeTitsTags], h⟩)))
  rcases h' with ⟨hh, -⟩ | ⟨-, hh, -⟩ | ⟨-, -, hR⟩ | ⟨-, hh, -⟩
  · exact absurd hh (by decide)
  · exact absurd hh (by decide)
  · exact hR
  · exact absurd hh (by decide)

theorem reeTitsModel_of_FRee {Y : Type} [Group Y] (h : FRee Y) : ∃ f : ℕ, ReeTitsModel Y .twistedG2 3 f := by
  obtain ⟨f, -, hlie⟩ := h
  refine ⟨f, ?_⟩
  rcases hlie with ⟨hh, -⟩ | ⟨-, hh, -⟩ | ⟨-, -, hR⟩ | ⟨-, hh, -⟩
  · exact absurd hh (by decide)
  · exact absurd hh (by decide)
  · exact hR
  · exact absurd hh (by decide)

theorem cell87_FRee :
    Cell87 FRee := by
  intro _ _ G _ _ z k S hctx H₀ H₁ _ hz p X hsig hyp hF
  classical
  exfalso
  have hz2 : z * z = 1 := by
    have h1 := pow_orderOf_eq_one z
    rw [hctx.central.1] at h1
    simpa [pow_two] using h1
  set zb : Sec H₀ H₁ := zSec z H₀ hz H₁ with hzb
  have hzb2 : zb * zb = 1 := by
    have hz0 : (⟨z, hz⟩ : ↥H₀) * ⟨z, hz⟩ = 1 := Subtype.ext hz2
    rw [hzb, zSec, ← QuotientGroup.mk_mul, hz0, QuotientGroup.mk_one]
  set K : Subgroup (Sec H₀ H₁) := layer (Sec H₀ H₁) with hK
  have hKc : K.Characteristic := LocalCores.layer_characteristic
  have hKn : K.Normal := inferInstance
  obtain ⟨hgen, hq, hcen, -⟩ := hyp
  obtain ⟨f, hR⟩ := reeTitsModel_of_FRee hF
  have hKq : CFSG.Open.IsQuasisimple ↥K := ⟨hq.1.commutator_eq_top, hq.2.1⟩
  have hZ2 : IsPGroup 2 ↥(center ↥K) := by rw [hcen]; exact CFSG.pCore_isPGroup
  have hZ : center ↥K = ⊥ :=
    CFSG.ComponentClassification.RankTwoOddLie.smallReeTwoMultiplierTrivial ↥K hKq hZ2 ⟨f, hR⟩
  let eq0 : (↥K ⧸ center ↥K) ≃* ↥K :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have hR' : ReeTitsModel ↥K .twistedG2 3 f := reeTitsModel_of_mulEquiv eq0 hR
  have hsimple : IsSimpleGroup ↥K := (eq0.isSimpleGroup_congr).1 hq.2.1
  have hnonab : ∃ a b : ↥K, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hq.2.2
    exact ⟨eq0 a, eq0 b, fun h => hab (eq0.injective (by simpa [map_mul] using h))⟩
  let ρ : Sec H₀ H₁ →* MulAut ↥K := MulAut.conjNormal
  have hα2 : ρ zb * ρ zb = 1 := by rw [← map_mul, hzb2, map_one]
  let ā : CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥K := QuotientGroup.mk (ρ zb)
  have hā2 : ā * ā = 1 := by rw [← QuotientGroup.mk_mul, hα2, QuotientGroup.mk_one]
  have hā2' : ā ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hā2
  have hcardE : Nat.card (Subgroup.zpowers ā) ≤ 2 ^ 0 :=
    CFSG.GH74.GLS.IVK.GHInv.ree_card_outer_elementary hR' (Subgroup.zpowers ā) (by
      intro e he
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp he
      calc ā ^ n * ā ^ n = ā ^ (2 * n) := by rw [two_mul, zpow_add]
        _ = 1 := by rw [zpow_mul, hā2', one_zpow])
  have hfinAut : Finite (MulAut ↥K) :=
    Finite.of_injective (fun f : MulAut ↥K => (f : ↥K → ↥K)) DFunLike.coe_injective
  have hfinOut : Finite (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥K) :=
    inferInstanceAs (Finite (MulAut ↥K ⧸ CFSG.ComponentClassification.OuterAutomorphisms.inner ↥K))
  have hE : Subgroup.zpowers ā = ⊥ :=
    Subgroup.card_eq_one.mp (le_antisymm (by simpa using hcardE) Nat.card_pos)
  have hā1 : ā = 1 := by
    have : ā ∈ Subgroup.zpowers ā := Subgroup.mem_zpowers ā
    rw [hE] at this
    exact Subgroup.mem_bot.mp this
  have hinner : ρ zb ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner ↥K :=
    (QuotientGroup.eq_one_iff _).mp hā1
  obtain ⟨g, hg⟩ := hinner
  have hconj : ∀ y : ↥K, zb * (y : Sec H₀ H₁) * zb⁻¹ = (g : Sec H₀ H₁) * y * (g : Sec H₀ H₁)⁻¹ := by
    intro y
    have := congrArg (fun σ : MulAut ↥K => ((σ y : ↥K) : Sec H₀ H₁)) hg
    simpa [ρ, MulAut.conjNormal_apply] using this.symm
  set c : Sec H₀ H₁ := (g : Sec H₀ H₁)⁻¹ * zb with hc
  have hzbgc : zb = (g : Sec H₀ H₁) * c := by rw [hc]; simp
  have hcK : c ∈ centralizer ((K : Subgroup (Sec H₀ H₁)) : Set (Sec H₀ H₁)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h1 := hconj ⟨y, hy⟩
    have h2 : c * y = y * c := by
      calc c * y = (g : Sec H₀ H₁)⁻¹ * (zb * y * zb⁻¹) * zb := by rw [hc]; group
        _ = (g : Sec H₀ H₁)⁻¹ * ((g : Sec H₀ H₁) * y * (g : Sec H₀ H₁)⁻¹) * zb := by rw [h1]
        _ = y * c := by rw [hc]; group
    exact h2.symm
  have hDn : (K ⊔ centralizer ((K : Subgroup (Sec H₀ H₁)) : Set (Sec H₀ H₁))).Normal := by
    have : (centralizer ((K : Subgroup (Sec H₀ H₁)) : Set (Sec H₀ H₁))).Normal :=
      normal_centralizer_of_normal K
    exact Subgroup.sup_normal _ _
  have hzbD : zb ∈ K ⊔ centralizer ((K : Subgroup (Sec H₀ H₁)) : Set (Sec H₀ H₁)) := by
    rw [hzbgc]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left g.2) (Subgroup.mem_sup_right hcK)
  have hcomm : ∀ x ∈ X, ⁅x, zb⁆ ∈ K ⊔ centralizer ((K : Subgroup (Sec H₀ H₁)) : Set (Sec H₀ H₁)) := by
    intro x _
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ (hDn.conj_mem zb hzbD x) (Subgroup.inv_mem _ hzbD)
  have hXK : X ≤ K := x_le_layer_of_comm hzb2 hsig.A hsig.op hgen hcomm
  have hgc : (g : Sec H₀ H₁) * c = c * g := Subgroup.mem_centralizer_iff.mp hcK g g.2
  have hcc : c * c ∈ centralizer ((K : Subgroup (Sec H₀ H₁)) : Set (Sec H₀ H₁)) := mul_mem hcK hcK
  have hgg_eq : (g : Sec H₀ H₁) * g = (c * c)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    calc (g : Sec H₀ H₁) * g * (c * c) = g * (g * c) * c := by group
      _ = g * (c * g) * c := by rw [hgc]
      _ = zb * zb := by rw [hzbgc]; group
      _ = 1 := hzb2
  have hgg : g * g = (1 : ↥K) := by
    have hmem : (g * g : ↥K) ∈ center ↥K := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      show (y : Sec H₀ H₁) * ((g : Sec H₀ H₁) * g) = ((g : Sec H₀ H₁) * g) * y
      rw [hgg_eq]
      exact Subgroup.mem_centralizer_iff.mp (Subgroup.inv_mem _ hcc) y y.2
    rw [hZ] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hg1 : g ≠ 1 := by
    intro hg1
    have hzbc : zb = c := by rw [hzbgc, hg1]; simp
    have hXbot : ⁅X, Subgroup.zpowers zb⁆ = ⊥ := by
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro x hx y hy
      have hxc : x * zb = zb * x := by
        rw [hzbc]; exact Subgroup.mem_centralizer_iff.mp hcK x (hXK hx)
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      have h2 : Commute x (zb ^ n) := (show Commute x zb from hxc).zpow_right n
      rw [commutatorElement_def, h2.eq]
      simp
    exact hsig.A.ne_bot (by rw [← hsig.A.comm]; exact hXbot)
  have hord : orderOf g = 2 := orderOf_eq_prime (by rw [pow_two]; exact hgg) hg1
  obtain ⟨hco, hOp⟩ := ree_involution_centralizer hR' hord
  have : Fact p.Prime := ⟨hsig.A.prime⟩
  let XT : Subgroup ↥K := X.subgroupOf K
  have hXp : IsPGroup p ↥XT := hsig.A.pgroup.of_equiv (Subgroup.subgroupOfEquivOfLe hXK).symm
  have hXne : XT ≠ ⊥ := by
    intro h
    apply hsig.A.ne_bot
    rw [eq_bot_iff]
    intro x hx
    have h1 : (⟨x, hXK hx⟩ : ↥K) ∈ XT := hx
    rw [h] at h1
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val (Subgroup.mem_bot.mp h1))
  have hN : centralizer ({g} : Set ↥K) ≤ normalizer (XT : Set ↥K) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hyg : (y : Sec H₀ H₁) * g = g * y :=
      congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hy)
    have hyc : (y : Sec H₀ H₁) * c = c * y := Subgroup.mem_centralizer_iff.mp hcK y y.2
    have hyz : (y : Sec H₀ H₁) ∈ centralizer ({zb} : Set (Sec H₀ H₁)) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc (y : Sec H₀ H₁) * zb = y * (g * c) := by rw [← hzbgc]
        _ = (y * g) * c := (mul_assoc _ _ _).symm
        _ = (g * y) * c := by rw [hyg]
        _ = g * (y * c) := mul_assoc _ _ _
        _ = g * (c * y) := by rw [hyc]
        _ = (g * c) * y := (mul_assoc _ _ _).symm
        _ = zb * y := by rw [← hzbgc]
    have hyN : (y : Sec H₀ H₁) ∈ normalizer (X : Set (Sec H₀ H₁)) :=
      hsig.A.inv _ (Subgroup.mem_top _) hyz
    exact Subgroup.mem_normalizer_iff.mp hyN (x : Sec H₀ H₁)
  have := hsimple
  exact false_of_coatom_centralizer hnonab g hco (hOp p hsig.A.prime hsig.A.odd) hXp hXne hN

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
