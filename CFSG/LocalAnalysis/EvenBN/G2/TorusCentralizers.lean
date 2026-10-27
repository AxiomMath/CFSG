module

public import CFSG.LocalAnalysis.EvenBN.G2.Torus
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8G2LeviA2
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3NativeBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Native
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.Reduced
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Containment
public import CFSG.Quasithin.Background.A3Structure312
public import CFSG.Quasithin.Background.SmithB42G2FNat
public import CFSG.Quasithin.Background.SmithB42G2FOff
public import CFSG.Quasithin.H13.J4Order
public import CFSG.Quasithin.H13.J4OrderBase
public import CFSG.Quasithin.Vol2.Ch11G2Q8LineGen
public import CFSG.Quasithin.Vol2.Ch11SecBFacts22
public import CFSG.Quasithin.Vol2.Ch11SecBFacts22G
public import CFSG.Quasithin.Vol2.Ch11StatementsF
public import CFSG.Quasithin.Vol2.Ch11StatementsG
public import CFSG.Quasithin.Vol2.Ch11StatementsH
public import CFSG.Quasithin.Vol2.Ch11StatementsInputs
public import CFSG.RankThree.PartTwo.Sec12.Notation
public import CFSG.RankThree.PartTwo.Sec8.Pairs
public import CFSG.RankThree.PartTwo.Sec8.Statements
public import CFSG.Sporadic.Schreier.J4SProfileNode
public import Certificates.Certificate8026Base

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.G2

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional

theorem map_subtype_center_eq {X : Type*} [Group X] (H : Subgroup X) :
    (center H).map H.subtype = H ⊓ centralizer (H : Set X) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, mem_centralizer_iff.2 fun z hz =>
      congrArg Subtype.val (mem_center_iff.1 hy ⟨z, hz⟩)⟩
  · rintro ⟨hxH, hxc⟩
    exact ⟨⟨x, hxH⟩, mem_center_iff.2 fun z => Subtype.ext (mem_centralizer_iff.1 hxc z z.2),
      rfl⟩

theorem map_center_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) :
    (center X).map (e : X →* Y) = center Y := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine mem_center_iff.2 fun z => ?_
    rw [← e.apply_symm_apply z]
    change e (e.symm z) * e x = e x * e (e.symm z)
    rw [← map_mul, ← map_mul, mem_center_iff.1 hx]
  · intro hy
    refine ⟨e.symm y, mem_center_iff.2 fun z => e.injective ?_, e.apply_symm_apply y⟩
    rw [map_mul, map_mul, e.apply_symm_apply]
    exact mem_center_iff.1 hy (e z)

theorem le_center_of_map_le_centralizer {Q X : Type*} [Group Q] [Group X]
    (hQ : IsSimpleGroup (Q ⧸ center Q)) (φ : Q →* X) (hperf : ⁅φ.range, φ.range⁆ = φ.range)
    (hne : φ.range ≠ ⊥) {M : Subgroup Q} (hM : M.Normal)
    (hMc : M.map φ ≤ centralizer (φ.range : Set X)) : M ≤ center Q := by
  have hN : (M.map (QuotientGroup.mk' (center Q))).Normal :=
    hM.map _ (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (M.map (QuotientGroup.mk' (center Q))) with
    h | h
  · rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
  · exfalso
    have hsup : M ⊔ center Q = ⊤ := by
      have := comap_map_eq (QuotientGroup.mk' (center Q)) M
      rw [h, comap_top, QuotientGroup.ker_mk'] at this
      exact this.symm
    have hZ : (center Q).map φ ≤ centralizer (φ.range : Set X) := by
      rintro _ ⟨z, hz, rfl⟩
      refine mem_centralizer_iff.2 ?_
      rintro _ ⟨q, rfl⟩
      rw [← map_mul, ← map_mul, mem_center_iff.1 hz q]
    have hr : φ.range = M.map φ ⊔ (center Q).map φ := by
      rw [MonoidHom.range_eq_map, ← hsup, Subgroup.map_sup]
    have hle : φ.range ≤ centralizer (φ.range : Set X) := fun x hx => by
      rw [hr] at hx
      exact sup_le hMc hZ hx
    have hab : ⁅φ.range, φ.range⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.2 hle
    exact hne (hperf.symm.trans hab)

namespace Model

theorem pow_three_eq_one_of_card_four {K : Type} [Field K] (hK : Nat.card K = 4) (β : Kˣ) :
    β ^ 3 = 1 := by
  have h := pow_card_eq_one' (x := β)
  rwa [Nat.card_units, hK] at h

section Basic

variable {K : Type} [Field K]

theorem torusElt_a_mem_J₂ (β : Kˣ) : torusElt .G2 K g2ia β ∈ J₂ K := by
  have h := hCo_mem_Ji (K := K) 1 β
  change hCo K 1 0 β ∈ J₂ K at h
  rwa [hCo_apply, zpow_one, zpow_zero, torusElt_one, mul_one] at h

theorem torusElt_r_mem_J₁ (β : Kˣ) : torusElt .G2 K g2ir β ∈ J₁ K := by
  have h := hCo_mem_Ji (K := K) 0 β
  change hCo K 0 1 β ∈ J₁ K at h
  rwa [hCo_apply, zpow_one, zpow_zero, torusElt_one, one_mul] at h

theorem J₁_eq_g2TorusR : J₁ K = g2TorusR K := by
  ext x
  rw [show x ∈ J₁ K ↔ x ∈ Ji K 0 from Iff.rfl, mem_Ji_iff, MonoidHom.mem_range]
  refine exists_congr fun β => ?_
  change hCo K 0 1 β = x ↔ torusElt .G2 K g2ir β = x
  rw [hCo_apply, zpow_zero, zpow_one, torusElt_one, one_mul]

theorem torusElt_conj_mem_rootSubgroup (i : Fin Tag.G2.rank) (t : Kˣ) {s : Fin Tag.G2.rank → ℤ}
    (hs : IsRoot .G2 s) {x : ModGL .G2 K} (hx : x ∈ rootSubgroup .G2 K s) :
    torusElt .G2 K i t * x * (torusElt .G2 K i t)⁻¹ ∈ rootSubgroup .G2 K s := by
  obtain ⟨y, rfl⟩ := mem_rootSubgroup.1 hx
  rw [root_torus_conjugation i hs]
  exact mem_rootSubgroup.2 ⟨_, rfl⟩

end Basic

section CentralizerS

variable {K : Type} [Field K]

theorem yamada_3_9_4_four [Finite K] (hK : Nat.card K = 4) :
    J₁ K = J₄ K ∧ J₁ K = J₅ K ∧
      S K ⊓ centralizer (J₁ K : Set (ModGL .G2 K)) =
        rootSubgroup .G2 K g2a ⊔ rootSubgroup .G2 K g2b ⊔ rootSubgroup .G2 K g2c ∧
      ∀ i ∈ ({1, 2, 5} : Finset (Fin 6)),
        S K ⊓ centralizer (Ji K i : Set (ModGL .G2 K)) = rootSubgroup .G2 K (yamadaRoot i) := by
  have h3 : 3 ∣ Nat.card K - 1 := by rw [hK]
  obtain ⟨h14, h15, hc, -⟩ := yamada_3_9_3 (K := K) h3
  have hc1 : Nat.card (J₁ K) = 3 := (yamada_3_9_1 (K := K) 0).2.trans (by rw [hK])
  have hc4 : Nat.card (J₄ K) = 3 := (yamada_3_9_1 (K := K) 3).2.trans (by rw [hK])
  have hc5 : Nat.card (J₅ K) = 3 := (yamada_3_9_1 (K := K) 4).2.trans (by rw [hK])
  have e1 : J₁ K ⊓ J₄ K = J₁ K := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hc, hc1])
  have e4 : J₁ K ⊓ J₄ K = J₄ K := Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hc, hc4])
  have hc' : Nat.card (J₁ K ⊓ J₅ K : Subgroup (ModGL .G2 K)) = 3 := by rw [← h14, hc]
  have e5 : J₁ K ⊓ J₅ K = J₅ K := Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hc', hc5])
  refine ⟨e1.symm.trans e4, (e1.symm.trans h14).trans e5, le_antisymm (fun x hx => ?_) ?_,
    fun i hi => S_inf_centralizer_Ji (by rw [hK]) i (Or.inr (by revert hi; revert i; decide))⟩
  · obtain ⟨hxS, hxC⟩ := hx
    obtain ⟨A, B, C, D, E, F, rfl⟩ := mem_S.1 hxS
    have hnd : ∀ k : Fin 6, k ∈ ({1, 2, 5} : Finset (Fin 6)) →
        ¬ ((Nat.card K - 1 : ℕ) : ℤ) ∣ yamadaExp 0 k := by
      rw [hK]
      decide
    obtain rfl := (coords_of_mem_centralizer_Ji 0 hxC (hnd 2 (by decide))).1 rfl
    obtain rfl := (coords_of_mem_centralizer_Ji 0 hxC (hnd 5 (by decide))).2.2.1 rfl
    obtain rfl := (coords_of_mem_centralizer_Ji 0 hxC (hnd 1 (by decide))).2.2.2.1 rfl
    have e : g2N (0 : K) B 0 0 E F = pinnedX .G2 K g2a B * pinnedX .G2 K g2b E *
        pinnedX .G2 K g2c F := by
      simp only [g2N, pinnedX_zero, one_mul, mul_one]
    rw [e]
    exact mul_mem (mul_mem (mem_sup_left (mem_sup_left (mem_rootSubgroup.2 ⟨B, rfl⟩)))
      (mem_sup_left (mem_sup_right (mem_rootSubgroup.2 ⟨E, rfl⟩))))
      (mem_sup_right (mem_rootSubgroup.2 ⟨F, rfl⟩))
  · have key : ∀ {s : Fin Tag.G2.rank → ℤ}, IsRoot .G2 s → rootSubgroup .G2 K s ≤ S K →
        (∃ e : ℤ, 0 * pairB s + 1 * pairA s = 3 * e) →
          rootSubgroup .G2 K s ≤ S K ⊓ centralizer (J₁ K : Set (ModGL .G2 K)) := by
      intro s hs hsS ⟨e, he⟩ x hx
      refine ⟨hsS hx, mem_centralizer_iff.2 fun z hz => ?_⟩
      obtain ⟨y, rfl⟩ := mem_rootSubgroup.1 hx
      obtain ⟨β, rfl⟩ := (mem_Ji_iff 0).1 hz
      have h1 := hCo_conj hs 0 1 β y
      rw [he, zpow_mul, show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast,
        pow_three_eq_one_of_card_four hK, one_zpow, Units.val_one, one_mul] at h1
      change hCo K 0 1 β * pinnedX .G2 K s y = pinnedX .G2 K s y * hCo K 0 1 β
      calc hCo K 0 1 β * pinnedX .G2 K s y =
          hCo K 0 1 β * pinnedX .G2 K s y * (hCo K 0 1 β)⁻¹ * hCo K 0 1 β := by group
        _ = _ := by rw [h1]
    refine sup_le (sup_le (key isRoot_g2a (rootSubgroup_yamadaRoot_le_S 3) ⟨-1, by decide⟩)
      (key isRoot_g2b (rootSubgroup_yamadaRoot_le_S 4) ⟨1, by decide⟩))
      (key isRoot_g2c (rootSubgroup_yamadaRoot_le_S 0) ⟨0, by decide⟩)

end CentralizerS

section WeylConj

variable {K : Type} [Field K] [CharP K 2]

theorem rankOne_cells (i : Fin Tag.G2.rank) {Jr : Subgroup (ModGL .G2 K)}
    (hJr : ∀ h, h ∈ Jr ↔ ∃ t : Kˣ, torusElt .G2 K i t = h) :
    (∃ ρ : SL2 K →* ModGL .G2 K, Function.Injective ρ ∧ ρ.range = g2RankOne K i ∧
        (∀ c, ρ (uSL c) = pinnedX .G2 K (Pi.single i 1) c) ∧
        ∀ c, ρ (vSL c) = pinnedX .G2 K (-Pi.single i 1) c) ∧
    ∀ g, g ∈ g2RankOne K i ↔
      (∃ x ∈ rootSubgroup .G2 K (Pi.single i 1), ∃ h ∈ Jr, g = x * h) ∨
        ∃ x ∈ rootSubgroup .G2 K (Pi.single i 1), ∃ h ∈ Jr,
          ∃ y ∈ rootSubgroup .G2 K (Pi.single i 1), g = x * h * weylElt .G2 K i 1 * y := by
  obtain ⟨ρ, hu, hv, -, -, hrange, hinj, hcell0, hcell⟩ := g2_rank_one (K := K) i
  have hroot : IsRoot .G2 (Pi.single i 1) := isRoot_single .G2 i
  have hSr : ∀ x ∈ rootSubgroup .G2 K (Pi.single i 1), x ∈ g2RankOne K i := by
    intro x hx
    obtain ⟨y, rfl⟩ := mem_rootSubgroup.1 hx
    rw [pinnedX_single]
    exact xUnit_mem_g2RankOne i y
  have hJ : ∀ h ∈ Jr, h ∈ g2RankOne K i := by
    intro h hh
    obtain ⟨t, rfl⟩ := (hJr h).1 hh
    exact torusElt_mem_g2RankOne i t
  refine ⟨⟨ρ, hinj, hrange, fun c => by rw [hu, pinnedX_single],
    fun c => by rw [hv, pinnedX_neg_single]⟩, fun g => ⟨fun hg => ?_, ?_⟩⟩
  · rw [← hrange] at hg
    obtain ⟨m, rfl⟩ := hg
    by_cases hc : (m : Matrix (Fin 2) (Fin 2) K) 1 0 = 0
    · left
      rw [hcell0 m hc]
      set d := torusElt .G2 K i (Units.mk0 _ (SL2_apply_zero_zero_ne_zero hc))
      refine ⟨d * xUnit .G2 K i ((m : Matrix (Fin 2) (Fin 2) K) 0 1 /
          (m : Matrix (Fin 2) (Fin 2) K) 0 0) * d⁻¹, ?_, d, (hJr d).2 ⟨_, rfl⟩, by group⟩
      exact torusElt_conj_mem_rootSubgroup i _ hroot
        (mem_rootSubgroup.2 ⟨_, pinnedX_single .G2 K i _⟩)
    · right
      rw [hcell m hc]
      exact ⟨_, mem_rootSubgroup.2 ⟨_, pinnedX_single .G2 K i _⟩, _, (hJr _).2 ⟨_, rfl⟩, _,
        mem_rootSubgroup.2 ⟨_, pinnedX_single .G2 K i _⟩, rfl⟩
  · rintro (⟨x, hx, h, hh, rfl⟩ | ⟨x, hx, h, hh, y, hy, rfl⟩)
    · exact mul_mem (hSr x hx) (hJ h hh)
    · exact mul_mem (mul_mem (mul_mem (hSr x hx) (hJ h hh)) (weylElt_mem_g2RankOne i 1))
        (hSr y hy)

theorem yamada_3_11 :
    ((∃ ρ : SL2 K →* ModGL .G2 K, Function.Injective ρ ∧ ρ.range = leviA K ∧
        (∀ c, ρ (uSL c) = pinnedX .G2 K g2r c) ∧ ∀ c, ρ (vSL c) = pinnedX .G2 K (-g2r) c) ∧
      ∀ g, g ∈ leviA K ↔ (∃ x ∈ rootSubgroup .G2 K g2r, ∃ h ∈ J₁ K, g = x * h) ∨
        ∃ x ∈ rootSubgroup .G2 K g2r, ∃ h ∈ J₁ K, ∃ y ∈ rootSubgroup .G2 K g2r,
          g = x * h * wa K * y) ∧
    ((∃ ρ : SL2 K →* ModGL .G2 K, Function.Injective ρ ∧ ρ.range = leviB K ∧
        (∀ c, ρ (uSL c) = pinnedX .G2 K g2a c) ∧ ∀ c, ρ (vSL c) = pinnedX .G2 K (-g2a) c) ∧
      ∀ g, g ∈ leviB K ↔ (∃ x ∈ rootSubgroup .G2 K g2a, ∃ h ∈ J₂ K, g = x * h) ∨
        ∃ x ∈ rootSubgroup .G2 K g2a, ∃ h ∈ J₂ K, ∃ y ∈ rootSubgroup .G2 K g2a,
          g = x * h * wb K * y) := by
  have hJ1 : ∀ h, h ∈ J₁ K ↔ ∃ t : Kˣ, torusElt .G2 K g2ir t = h := fun h => by
    rw [J₁_eq_g2TorusR]
    rfl
  have hJ2 : ∀ h, h ∈ J₂ K ↔ ∃ t : Kˣ, torusElt .G2 K g2ia t = h := fun h => by
    rw [show h ∈ J₂ K ↔ h ∈ Ji K 1 from Iff.rfl, mem_Ji_iff]
    refine exists_congr fun t => ?_
    change hCo K 1 0 t = h ↔ _
    rw [hCo_apply, zpow_one, zpow_zero, torusElt_one, mul_one]
  have ea := rankOne_cells (K := K) g2ir hJ1
  have eb := rankOne_cells (K := K) g2ia hJ2
  rw [← g2r_eq_single] at ea
  rw [← g2a_eq_single] at eb
  exact ⟨ea, eb⟩

end WeylConj

section Centralizers

variable {K : Type} [Field K] [CharP K 2]

theorem yamada_3_10_J₁ [Finite K] (hK : 8 ≤ Nat.card K) :
    adjointGroup .G2 K ⊓ centralizer (J₁ K : Set (ModGL .G2 K)) = g2LongC K ⊔ J₁ K ∧
      g2LongC K ≤ centralizer (J₁ K : Set (ModGL .G2 K)) ∧ g2LongC K ⊓ J₁ K = ⊥ ∧
      ∃ ρ : SL2 K →* ModGL .G2 K, Function.Injective ρ ∧ ρ.range = g2LongC K := by
  rw [J₁_eq_g2TorusR]
  have hHC : g2TorusR K ≤ adjointGroup .G2 K := by
    rintro _ ⟨t, rfl⟩
    exact torusElt_mem_adjointGroup _ _
  obtain ⟨ρ, hinj, hrange, -⟩ := exists_sl2_g2LongC (K := K)
  refine ⟨le_antisymm (fun x hx => ?_) (sup_le (le_inf g2LongC_le_adjointGroup
    g2LongC_le_centralizer) (le_inf hHC fun z hz => mem_centralizer_iff.2 fun y hy =>
      g2TorusR_comm hy hz)), g2LongC_le_centralizer, ?_, ρ, hinj, hrange⟩
  · obtain ⟨h, hh, hhx⟩ := exists_mem_g2TorusR_mul_g2LongC hK hx
    rw [show x = h * (h⁻¹ * x) by group]
    exact mul_mem (mem_sup_right hh) (mem_sup_left hhx)
  · refine eq_bot_iff.2 fun z ⟨hzL, hzH⟩ => ?_
    have hc : (⟨z, hzL⟩ : g2LongC K) ∈ center (g2LongC K) := mem_center_iff.2 fun y =>
      Subtype.ext (mem_centralizer_iff.1 (g2LongC_le_centralizer y.2) z hzH).symm
    rw [center_g2LongC, mem_bot] at hc
    exact mem_bot.2 (congrArg Subtype.val hc)

theorem exists_sl3_mulEquiv_g2LongA2
    [Finite K] (hK : Nat.card K = 4) :
    ∃ e : Matrix.SpecialLinearGroup (Fin (2 + 1)) K ≃* g2LongA2 K,
      ∀ γ ∈ CFSG.LieType.RootSystem.roots (CFSG.LieType.Universal.SpecialLinear.isFiniteType_A 2)
        (∅ : Set (Fin 2)), ∀ c : K,
          (e (CFSG.LieType.Steinberg.SL.x 2 K γ c) : ModGL .G2 K) = pinnedX .G2 K (a2Long γ) c := by
  obtain ⟨φ, hφ⟩ := exists_sl3_hom (K := K)
  have hrange : φ.range = g2LongA2 K := range_sl3_hom hφ
  obtain ⟨hperf, -, -⟩ := g2LongA2_sl3 hK
  have hQ := (CFSG.LieType.Universal.SpecialLinear.isQuasisimple 2 K le_rfl).2.1
  have hperf' : ⁅φ.range, φ.range⁆ = φ.range := by rw [hrange]; exact hperf
  have hne : φ.range ≠ ⊥ := by
    rw [hrange]
    intro h
    have h1 := pinnedX_c_mem_g2LongA2 (K := K) 1
    rw [h, mem_bot] at h1
    exact one_ne_zero (pinnedX_injective .G2 K _ (h1.trans (pinnedX_zero .G2 K _).symm))
  have hker : φ.ker ≤ center (Matrix.SpecialLinearGroup (Fin (2 + 1)) K) := by
    refine le_center_of_map_le_centralizer hQ φ hperf' hne φ.normal_ker ?_
    rw [(Subgroup.map_eq_bot_iff φ.ker).2 le_rfl]
    exact bot_le
  set M := (centralizer (φ.range : Set (ModGL .G2 K))).comap φ with hM
  have hMn : M.Normal := by
    refine ⟨fun x hx q => ?_⟩
    have hx' := mem_centralizer_iff.1 (show φ x ∈ centralizer (φ.range : Set (ModGL .G2 K)) from hx)
    refine mem_centralizer_iff.2 fun r hr => ?_
    have hr' : (φ q)⁻¹ * r * φ q ∈ φ.range := mul_mem (mul_mem (inv_mem ⟨q, rfl⟩) hr) ⟨q, rfl⟩
    have h1 := hx' _ hr'
    rw [map_mul, map_mul, map_inv]
    calc r * (φ q * φ x * (φ q)⁻¹) = φ q * ((φ q)⁻¹ * r * φ q * φ x) * (φ q)⁻¹ := by group
      _ = φ q * (φ x * ((φ q)⁻¹ * r * φ q)) * (φ q)⁻¹ := by rw [h1]
      _ = φ q * φ x * (φ q)⁻¹ * r := by group
  have hMZ := le_center_of_map_le_centralizer hQ φ hperf' hne hMn (map_comap_le _ _)
  have hcardZQ : Nat.card (center (Matrix.SpecialLinearGroup (Fin (2 + 1)) K)) = 3 := by
    have htop : rootsOfUnity 3 K = ⊤ :=
      eq_top_iff.2 fun x _ => (mem_rootsOfUnity 3 x).2 (pow_three_eq_one_of_card_four hK x)
    rw [Nat.card_congr (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' (0 : Fin (2 + 1))
      ).toEquiv]
    rw [show Fintype.card (Fin (2 + 1)) = 3 from rfl, htop, Subgroup.card_top, Nat.card_units, hK]
  have hcardZL : Nat.card (φ.range ⊓ centralizer (φ.range : Set (ModGL .G2 K)) :
      Subgroup (ModGL .G2 K)) = 3 := by
    rw [hrange, ← map_subtype_center_eq, center_g2LongA2 hK, ← J₁_eq_g2TorusR]
    exact (yamada_3_9_1 (K := K) 0).2.trans (by rw [hK])
  have hsub : φ.range ⊓ centralizer (φ.range : Set (ModGL .G2 K)) ≤ (center _).map φ := by
    rintro y ⟨⟨x, rfl⟩, hy⟩
    exact ⟨x, hMZ hy, rfl⟩
  let f : center (Matrix.SpecialLinearGroup (Fin (2 + 1)) K) → (center _).map φ :=
    fun z => ⟨φ z, z, z.2, rfl⟩
  have hf : Function.Surjective f := by
    rintro ⟨_, z, hz, rfl⟩
    exact ⟨⟨z, hz⟩, rfl⟩
  have hcardle : Nat.card (center (Matrix.SpecialLinearGroup (Fin (2 + 1)) K)) ≤
      Nat.card ((center (Matrix.SpecialLinearGroup (Fin (2 + 1)) K)).map φ) := by
    rw [hcardZQ, ← hcardZL]
    exact Subgroup.card_le_of_le hsub
  have hfi := (hf.bijective_of_nat_card_le hcardle).1
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro z hz
    have hzc := hker hz
    have h1 : f ⟨z, hzc⟩ = f ⟨1, one_mem _⟩ := Subtype.ext (by
      change φ z = φ 1
      rw [hz, map_one])
    exact congrArg Subtype.val (hfi h1)
  exact ⟨(MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange),
    fun γ hγ c => hφ γ hγ c⟩

theorem yamada_3_10_J₁_four [Finite K]
    (hK : Nat.card K = 4) :
    adjointGroup .G2 K ⊓ centralizer (J₁ K : Set (ModGL .G2 K)) = g2LongA2 K ∧
      ⁅g2LongA2 K, g2LongA2 K⁆ = g2LongA2 K ∧
      (center (g2LongA2 K)).map (g2LongA2 K).subtype = J₁ K ∧
      CFSG.Assembly.LowTwoRank.StatedClassicalModel
        (CFSG.ComponentClassification.RankTwoStandard.rankTwoQuot (g2LongA2 K)) .PSL 3 2 2 ∧
      ∃ e : Matrix.SpecialLinearGroup (Fin (2 + 1)) K ≃* g2LongA2 K,
        ∀ γ ∈ CFSG.LieType.RootSystem.roots (CFSG.LieType.Universal.SpecialLinear.isFiniteType_A 2)
          (∅ : Set (Fin 2)), ∀ c : K,
          (e (CFSG.LieType.Steinberg.SL.x 2 K γ c) : ModGL .G2 K) = pinnedX .G2 K (a2Long γ) c := by
  obtain ⟨e, he⟩ := exists_sl3_mulEquiv_g2LongA2 hK
  rw [J₁_eq_g2TorusR]
  obtain ⟨hperf, hmodel, -⟩ := g2LongA2_sl3 hK
  exact ⟨g2Centralizer_g2TorusR_eq_g2LongA2 hK, hperf, center_g2LongA2 hK, hmodel, e, he⟩

end Centralizers

end Model

namespace G2Data

variable {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] (d : G2Data L K)

theorem image_inf_centralizer_singleton (H : Subgroup (ModGL .G2 K)) (g : adjointGroup .G2 K) :
    d.image (H ⊓ centralizer {(g : ModGL .G2 K)}) = d.image H ⊓ centralizer {d.emb g} := by
  ext x
  simp only [mem_inf, d.mem_image, mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨k, ⟨hk, hkg⟩, rfl⟩
    refine ⟨⟨k, hk, rfl⟩, ?_⟩
    rw [← map_mul, ← map_mul]
    exact congrArg d.emb (Subtype.ext hkg)
  · rintro ⟨⟨k, hk, rfl⟩, hc⟩
    refine ⟨k, ⟨hk, ?_⟩, rfl⟩
    rw [← map_mul, ← map_mul] at hc
    exact congrArg Subtype.val (d.emb_injective hc)

theorem image_le_centralizer {H H' : Subgroup (ModGL .G2 K)} (hH : H ≤ adjointGroup .G2 K)
    (h : H' ≤ centralizer (H : Set (ModGL .G2 K))) :
    d.image H' ≤ centralizer (d.image H : Set G) := by
  intro x hx
  have hx' : x ∈ d.image (H' ⊓ centralizer (H : Set (ModGL .G2 K))) := by
    rwa [inf_eq_left.2 h]
  rw [d.image_inf_centralizer _ hH] at hx'
  exact hx'.2

theorem nonempty_sl2_equiv_image {H : Subgroup (ModGL .G2 K)} (hH : H ≤ adjointGroup .G2 K)
    {ρ : SL2 K →* ModGL .G2 K} (hinj : Function.Injective ρ) (hρ : ρ.range = H) :
    Nonempty (SL2 K ≃* d.image H) :=
  ⟨((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hρ)).trans (d.imageEquiv hH)⟩

theorem inf_centralizer_image {H : Subgroup (ModGL .G2 K)} (hH : H ≤ adjointGroup .G2 K) :
    L ⊓ centralizer (d.image H : Set G) =
      d.image (adjointGroup .G2 K ⊓ centralizer (H : Set (ModGL .G2 K))) := by
  rw [d.image_inf_centralizer _ hH, d.image_adjointGroup]

section TorusG

theorem Ji_le_adjointGroup (i : Fin 6) : Model.Ji K i ≤ adjointGroup .G2 K :=
  Model.torusFix_le_adjointGroup K _

theorem yamada_3_9_1_G [Finite K] (i : Fin 6) :
    IsCyclic (d.Ji i) ∧ Nat.card (d.Ji i) = Nat.card K - 1 := by
  have := (Model.yamada_3_9_1 (K := K) i).1
  exact ⟨isCyclic_of_surjective (d.imageEquiv (Ji_le_adjointGroup i)).toMonoidHom
      (d.imageEquiv (Ji_le_adjointGroup i)).surjective,
    (d.card_image (Ji_le_adjointGroup i)).trans (Model.yamada_3_9_1 i).2⟩

theorem yamada_3_9_2_G [Finite K] [CharP K 2] {i k : Fin 6} (hik : i ≠ k) :
    (∀ x ∈ d.rootGroup (Model.yamadaRoot k), x ≠ 1 →
      d.Ji i ⊓ centralizer {x} = d.Ji i ⊓ d.Ji k) ∧
    ((¬ 3 ∣ Nat.card K - 1 ∨
        ¬ (i ∈ ({0, 3, 4} : Finset (Fin 6)) ∧ k ∈ ({0, 3, 4} : Finset (Fin 6)))) →
      d.Ji i ⊓ d.Ji k = ⊥ ∧ ∀ x ∈ d.rootGroup (Model.yamadaRoot k), x ≠ 1 →
        ∀ y ∈ d.rootGroup (Model.yamadaRoot k), y ≠ 1 → ∃ h ∈ d.Ji i, h * x * h⁻¹ = y) := by
  obtain ⟨h1, h2⟩ := Model.yamada_3_9_2 (K := K) hik
  have hne : ∀ {g : adjointGroup .G2 K}, d.emb g ≠ 1 → (g : ModGL .G2 K) ≠ 1 := by
    intro g hg h0
    exact hg (by rw [show g = 1 from Subtype.ext h0, map_one])
  refine ⟨fun x hx hx1 => ?_, fun hc => ⟨?_, fun x hx hx1 y hy hy1 => ?_⟩⟩
  · obtain ⟨g, hg, rfl⟩ := d.mem_image.1 hx
    rw [Ji, Ji, ← d.image_inf_centralizer_singleton, h1 _ hg (hne hx1), d.image_inf]
  · rw [Ji, Ji, ← d.image_inf, (h2 hc).1, d.image_bot]
  · obtain ⟨g, hg, rfl⟩ := d.mem_image.1 hx
    obtain ⟨g', hg', rfl⟩ := d.mem_image.1 hy
    obtain ⟨h, hh, hconj⟩ := (h2 hc).2 _ hg (hne hx1) _ hg' (hne hy1)
    refine ⟨d.emb ⟨h, Ji_le_adjointGroup i hh⟩, d.emb_mem_image hh, ?_⟩
    exact d.emb_conj_eq_iff.2 hconj

@[expose] def leviC : Subgroup G := d.image (g2LongC K)

@[expose] def leviA2 : Subgroup G := d.image (g2LongA2 K)

end TorusG

section CentralizerSG

theorem yamada_3_9_4_four_G [Finite K] (hK : Nat.card K = 4) :
    d.J₁ = d.J₄ ∧ d.J₁ = d.J₅ ∧
      d.S ⊓ centralizer (d.J₁ : Set G) = d.rootGroup g2a ⊔ d.rootGroup g2b ⊔ d.rootGroup g2c ∧
      ∀ i ∈ ({1, 2, 5} : Finset (Fin 6)),
        d.S ⊓ centralizer (d.Ji i : Set G) = d.rootGroup (Model.yamadaRoot i) := by
  obtain ⟨e4, e5, hc, hi⟩ := Model.yamada_3_9_4_four (K := K) hK
  have hr := fun s => rootSubgroup_le_adjointGroup (K := K) (τ := .G2) s
  refine ⟨by rw [J₁, J₄, e4], by rw [J₁, J₅, e5], ?_, fun i hi' => ?_⟩
  · rw [S, J₁, ← d.image_inf_centralizer _ (Model.torusFix_le_adjointGroup K g2c), hc,
      d.image_sup (sup_le (hr _) (hr _)) (hr _), d.image_sup (hr _) (hr _)]
    rfl
  · rw [S, Ji, ← d.image_inf_centralizer _ (Ji_le_adjointGroup i), hi i hi']
    rfl

end CentralizerSG

section WeylConjG

variable [CharP K 2]

theorem yamada_3_11_G :
    Nonempty (SL2 K ≃* d.leviA) ∧ Nonempty (SL2 K ≃* d.leviB) ∧
      (∀ g : G, g ∈ d.leviA ↔ (∃ x ∈ d.rootGroup g2r, ∃ h ∈ d.J₁, g = x * h) ∨
        ∃ x ∈ d.rootGroup g2r, ∃ h ∈ d.J₁, ∃ y ∈ d.rootGroup g2r, g = x * h * d.wa * y) ∧
      ∀ g : G, g ∈ d.leviB ↔ (∃ x ∈ d.rootGroup g2a, ∃ h ∈ d.J₂, g = x * h) ∨
        ∃ x ∈ d.rootGroup g2a, ∃ h ∈ d.J₂, ∃ y ∈ d.rootGroup g2a, g = x * h * d.wb * y := by
  obtain ⟨⟨⟨ρa, hinja, hρa, -⟩, hca⟩, ⟨⟨ρb, hinjb, hρb, -⟩, hcb⟩⟩ := Model.yamada_3_11 (K := K)
  have key : ∀ {s : Fin Tag.G2.rank → ℤ} {T Jr : Subgroup (ModGL .G2 K)} {w : ModGL .G2 K}
      (hw : w ∈ adjointGroup .G2 K) (hT : T ≤ adjointGroup .G2 K)
      (hJr : Jr ≤ adjointGroup .G2 K),
      (∀ g, g ∈ T ↔ (∃ x ∈ rootSubgroup .G2 K s, ∃ h ∈ Jr, g = x * h) ∨
        ∃ x ∈ rootSubgroup .G2 K s, ∃ h ∈ Jr, ∃ y ∈ rootSubgroup .G2 K s, g = x * h * w * y) →
      ∀ g : G, g ∈ d.image T ↔ (∃ x ∈ d.rootGroup s, ∃ h ∈ d.image Jr, g = x * h) ∨
        ∃ x ∈ d.rootGroup s, ∃ h ∈ d.image Jr, ∃ y ∈ d.rootGroup s,
          g = x * h * d.emb ⟨w, hw⟩ * y := by
    intro s T Jr w hw hT hJr hc g
    have hr := rootSubgroup_le_adjointGroup (K := K) (τ := .G2) s
    constructor
    · intro hg
      obtain ⟨g', hg', rfl⟩ := d.mem_image.1 hg
      rcases (hc g').1 hg' with ⟨x, hx, h, hh, he⟩ | ⟨x, hx, h, hh, y, hy, he⟩
      · refine Or.inl ⟨d.emb ⟨x, hr hx⟩, d.emb_mem_image hx, d.emb ⟨h, hJr hh⟩,
          d.emb_mem_image hh, ?_⟩
        rw [← map_mul]
        exact congrArg d.emb (Subtype.ext he)
      · refine Or.inr ⟨d.emb ⟨x, hr hx⟩, d.emb_mem_image hx, d.emb ⟨h, hJr hh⟩,
          d.emb_mem_image hh, d.emb ⟨y, hr hy⟩, d.emb_mem_image hy, ?_⟩
        rw [← map_mul, ← map_mul, ← map_mul]
        exact congrArg d.emb (Subtype.ext he)
    · rintro (⟨x, hx, h, hh, rfl⟩ | ⟨x, hx, h, hh, y, hy, rfl⟩)
      · obtain ⟨x', hx', rfl⟩ := d.mem_image.1 hx
        obtain ⟨h', hh', rfl⟩ := d.mem_image.1 hh
        rw [← map_mul]
        exact d.emb_mem_image ((hc _).2 (Or.inl ⟨x', hx', h', hh', rfl⟩))
      · obtain ⟨x', hx', rfl⟩ := d.mem_image.1 hx
        obtain ⟨h', hh', rfl⟩ := d.mem_image.1 hh
        obtain ⟨y', hy', rfl⟩ := d.mem_image.1 hy
        rw [← map_mul, ← map_mul, ← map_mul]
        exact d.emb_mem_image ((hc _).2 (Or.inr ⟨x', hx', h', hh', y', hy', rfl⟩))
  exact ⟨d.nonempty_sl2_equiv_image (Model.leviA_le_adjointGroup K) hinja hρa,
    d.nonempty_sl2_equiv_image (Model.leviB_le_adjointGroup K) hinjb hρb,
    key (Model.wa_mem_adjointGroup K) (Model.leviA_le_adjointGroup K)
      (Model.torusFix_le_adjointGroup K g2c) hca,
    key (Model.wb_mem_adjointGroup K) (Model.leviB_le_adjointGroup K)
      (Model.torusFix_le_adjointGroup K g2v) hcb⟩

end WeylConjG

section CentralizersG

variable [CharP K 2]

theorem yamada_3_10_J₁_G [Finite K] (hK : 8 ≤ Nat.card K) :
    L ⊓ centralizer (d.J₁ : Set G) = d.leviC ⊔ d.J₁ ∧
      d.leviC ≤ centralizer (d.J₁ : Set G) ∧ d.leviC ⊓ d.J₁ = ⊥ ∧
      Nonempty (SL2 K ≃* d.leviC) := by
  have hJ := Model.torusFix_le_adjointGroup K g2c
  obtain ⟨h1, h2, h3, ρ, hinj, hρ⟩ := Model.yamada_3_10_J₁ (K := K) hK
  refine ⟨?_, d.image_le_centralizer hJ h2, ?_,
    d.nonempty_sl2_equiv_image g2LongC_le_adjointGroup hinj hρ⟩
  · rw [J₁, d.inf_centralizer_image hJ, h1, d.image_sup g2LongC_le_adjointGroup hJ]
    rfl
  · rw [leviC, J₁, ← d.image_inf, h3, d.image_bot]

theorem yamada_3_10_J₁_four_G
    [Finite K] (hK : Nat.card K = 4) :
    L ⊓ centralizer (d.J₁ : Set G) = d.leviA2 ∧ ⁅d.leviA2, d.leviA2⁆ = d.leviA2 ∧
      (center d.leviA2).map d.leviA2.subtype = d.J₁ ∧
      (∃ (K' : Type) (_ : Field K') (_ : Finite K'), Nat.card K' = 2 ^ 2 ∧
        Nonempty ((d.leviA2 ⧸ center d.leviA2) ≃*
          CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL 3 K'))) ∧
      Nonempty (Matrix.SpecialLinearGroup (Fin (2 + 1)) K ≃* d.leviA2) := by
  have hJ := Model.torusFix_le_adjointGroup K g2c
  have hA := g2LongA2_le_adjointGroup (K := K)
  obtain ⟨h1, h2, h3, ⟨-, K', hK'1, hK'2, hK'3, ⟨e'⟩⟩, e, -⟩ :=
    Model.yamada_3_10_J₁_four (K := K) hK
  have hZ : (center (g2LongA2 K)).map (g2LongA2 K).subtype =
      g2LongA2 K ⊓ centralizer (g2LongA2 K : Set (ModGL .G2 K)) := map_subtype_center_eq _
  refine ⟨?_, ?_, ?_, ⟨K', hK'1, hK'2, hK'3, ⟨?_⟩⟩, ⟨e.trans (d.imageEquiv hA)⟩⟩
  · rw [J₁, d.inf_centralizer_image hJ, h1]
    rfl
  · rw [leviA2, ← d.image_commutator hA hA, h2]
  · rw [map_subtype_center_eq, leviA2, ← d.image_inf_centralizer _ hA, ← hZ, h3]
    rfl
  · refine (QuotientGroup.congr (center d.leviA2) (center (g2LongA2 K))
      (d.imageEquiv hA).symm ?_).trans e'
    exact map_center_mulEquiv _

end CentralizersG

end G2Data

end CFSG.LocalAnalysis.EvenBN.G2
