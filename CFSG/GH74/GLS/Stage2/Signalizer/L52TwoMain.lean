module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.GLS.Stage1.Main.Out
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Basic
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Defs
public import CFSG.GH74.GLS.Stage2.Signalizer.L52Gen
public import CFSG.GH74.GLS.Stage2.Signalizer.L52Split
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.L52Two

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Bender.Thm1 CFSG.GH74.GLS.Stage1.Main CFSG.ABGLocalTools
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def DBar (H P : Subgroup G) : Prop :=
  ∀ D ∈ pCore 2 (HBar H), ∀ g : ↥H, g ∈ P.subgroupOf H →
    D * (QuotientGroup.mk g : HBar H) = (QuotientGroup.mk g : HBar H) * D

variable {k : Kind} {z : G} {S T Tstar : Subgroup G} {p : ℕ} {H P : Subgroup G}

theorem part_b_two (hctx : Ctx51 k z S T Tstar p H P) : Op p H ≤ P := by
  have hTH : T ≤ H := hctx.T_le
  have hmax := hctx.maxi
  obtain ⟨hPH, hPp, hTP, hcov⟩ := hmax.1
  have hQp : IsPGroup p ↥(Op p H ⊔ P) :=
    IsPGroup.to_sup_of_normal_left' (isPGroup_Op p hctx.prime H) hPp
      (hPH.trans (le_normalizer_Op p H))
  have hTQ : T ≤ normalizer ((Op p H ⊔ P : Subgroup G) : Set G) :=
    fun t ht => Subgroup.inf_normalizer_le_normalizer_sup (Op p H) P
      ⟨le_normalizer_Op p H (hTH ht), hTP ht⟩
  have hNN : H ⊓ normalizer (P : Set G) ≤ H ⊓ normalizer ((Op p H ⊔ P : Subgroup G) : Set G) := by
    rintro h ⟨hhH, hhP⟩
    exact ⟨hhH, Subgroup.inf_normalizer_le_normalizer_sup (Op p H) P
      ⟨le_normalizer_Op p H hhH, hhP⟩⟩
  have hinv : InvCover p H T Tstar (Op p H ⊔ P) := by
    exact ⟨sup_le (Op_le p H) hPH, hQp, hTQ,
      hcov.trans (sup_le_sup_right (inf_le_inf_right Tstar hNN) _)⟩
  have := hmax.2 _ hinv le_sup_right
  exact le_sup_left.trans this.le


omit [Finite G] in
theorem part_d_of_dbar (hPH : P ≤ H) (hd : DBar H P) : ⁅O22Of H, P⁆ ≤ pPrimeCoreOf 2 H := by
  rw [Subgroup.commutator_le]
  rintro d ⟨d', hd', rfl⟩ g hg
  have hd'' : (QuotientGroup.mk d' : HBar H) ∈ pCore 2 (HBar H) := hd'
  have hg' : (⟨g, hPH hg⟩ : ↥H) ∈ P.subgroupOf H := hg
  have hcomm := hd _ hd'' _ hg'
  have hk : ⁅d', (⟨g, hPH hg⟩ : ↥H)⁆ ∈ pPrimeCore 2 ↥H := by
    rw [← QuotientGroup.ker_mk' (pPrimeCore 2 ↥H), MonoidHom.mem_ker, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm]
    exact hcomm
  exact ⟨_, hk, rfl⟩

theorem part_e_of_dbar (hp : p.Prime) (hp2 : p ≠ 2) (hPp : IsPGroup p ↥P) (hd : DBar H P) :
    barIn H P ≤ centralizer ((centralizer ((layer (HBar H) : Subgroup (HBar H)) : Set (HBar H)) :
      Subgroup (HBar H)) : Set (HBar H)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO : pPrimeCore 2 (HBar H) = ⊥ := CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot 2
  have hpodd : Odd p := hp.eq_two_or_odd'.resolve_left hp2
  rintro a ⟨g', hg', rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  obtain ⟨n, hn⟩ := (hPp.comap_subtype) ⟨g', hg'⟩
  have hn' : g' ^ (p ^ n) = 1 := by
    have h2 := congrArg (fun y : ↥(P.subgroupOf H) => (y : ↥H)) hn
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at h2
    exact h2
  have ham : (QuotientGroup.mk' (pPrimeCore 2 ↥H) g') ^ (p ^ n) = 1 := by
    rw [← map_pow, hn', map_one]
  have hD : ∀ d ∈ pCore 2 (HBar H), d * QuotientGroup.mk' (pPrimeCore 2 ↥H) g' =
      QuotientGroup.mk' (pPrimeCore 2 ↥H) g' * d := fun d hd' => hd d hd' g' hg'
  exact centralizes_centralizer_layer hO (hpodd.pow) ham hD x (Subgroup.mem_centralizer_iff.mpr
    (fun h hh => Subgroup.mem_centralizer_iff.mp hx h hh))

end CFSG.GH74.GLS.Stage2.Signalizer.L52Two

namespace CFSG.GH74.GLS.Stage2.Signalizer

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local

theorem lemma5_2Two_of_dbar
    (hdb : ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G), Stage2Ctx G z k S →
      ∀ (T Tstar : Subgroup G) (p : ℕ) (H P : Subgroup G), Ctx51 k z S T Tstar p H P →
        ¬ TypeOneCase G k → ¬ Concl51 k S p H P → L52Two.DBar H P) : Lemma5_2Two := by
  intro G _ _ z k S ctx T Tstar p H P hctx hnt hnc
  have hdbar := hdb G z k S ctx T Tstar p H P hctx hnt hnc
  obtain ⟨hPH, hPp, -, -⟩ := hctx.maxi.1
  exact ⟨L52Two.part_b_two hctx, fun h => absurd h.1 hnt,
    L52Two.part_d_of_dbar hPH hdbar, L52Two.part_e_of_dbar hctx.prime hctx.odd hPp hdbar⟩

end CFSG.GH74.GLS.Stage2.Signalizer
