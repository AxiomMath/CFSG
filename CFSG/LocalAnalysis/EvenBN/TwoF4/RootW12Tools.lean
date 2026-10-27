module

public import CFSG.LocalAnalysis.EvenBN.TwoF4.ModelRadicalR
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.EvenBN.TwoF4.RootCentralizer

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.TwoF4

open Subgroup
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution
open CFSG.LieType.Ree.LargeReeCover (torusPair)
open scoped commutatorElement

section Model

variable {K : Type} [Field K] (a : ℕ)

open Classical in
@[expose] def r1Coord (g : ModGL F4.tag K) : Idx → K :=
  if hg : ∃ u : Idx → K, g = r1Elt K a u then fun k => if k.isR1 then hg.choose k else 0 else 0

variable {a} [Finite K] [CharP K F4.prime]

theorem r1Elt_r1Coord (hK : Nat.card K = 2 ^ (2 * a + 1)) {g : ModGL F4.tag K}
    (hg : g ∈ R1 K a) : r1Elt K a (r1Coord a g) = g := by
  have hex := exists_r1Elt_eq hK hg
  rw [r1Coord, dite_eq_left hex]
  calc r1Elt K a (fun k => if k.isR1 = true then hex.choose k else 0) = r1Elt K a hex.choose :=
        (r1Elt_eq_iff hK).2 fun k hk => by rw [ite_eq_left hk]
    _ = g := hex.choose_spec.symm

theorem r1Coord_r1Elt (hK : Nat.card K = 2 ^ (2 * a + 1)) (u : Idx → K) {k : Idx}
    (hk : k.isR1 = true) : r1Coord a (r1Elt K a u) k = u k := by
  have hex : ∃ v : Idx → K, r1Elt K a u = r1Elt K a v := ⟨u, rfl⟩
  rw [r1Coord, dite_eq_left hex, ite_eq_left hk]
  exact ((r1Elt_eq_iff hK).1 hex.choose_spec k hk).symm

theorem r1Coord_mul (hK : Nat.card K = 2 ^ (2 * a + 1)) {x y : ModGL F4.tag K}
    (hx : x ∈ R1 K a) (hy : y ∈ R1 K a) {k : Idx} (hk : k.isR1 = true) :
    r1Coord a (x * y) k = r1Coord a x k + r1Coord a y k := by
  conv_lhs => rw [← r1Elt_r1Coord hK hx, ← r1Elt_r1Coord hK hy, ← r1Elt_add hK]
  rw [r1Coord_r1Elt hK _ hk, Pi.add_apply]

theorem r1Coord_eq_zero_of_mem_rootJoin (hK : Nat.card K = 2 ^ (2 * a + 1)) {S : Finset Idx}
    (hS : ∀ l ∈ S, l.isR1 = true) {g : ModGL F4.tag K} (hg : g ∈ rootJoin K a S) {k : Idx}
    (hk : k.isR1 = true) (hkS : k ∉ S) : r1Coord a g k = 0 := by
  let T : Subgroup (ModGL F4.tag K) :=
    { carrier := {x | x ∈ R1 K a ∧ r1Coord a x k = 0}
      mul_mem' := fun {x y} hx hy => ⟨mul_mem hx.1 hy.1, by
        rw [r1Coord_mul hK hx.1 hy.1 hk, hx.2, hy.2, add_zero]⟩
      one_mem' := ⟨one_mem _, by
        rw [← r1Elt_zero (K := K) (a := a), r1Coord_r1Elt hK _ hk, Pi.zero_apply]⟩
      inv_mem' := fun {x} hx => ⟨inv_mem hx.1, by
        have h1 := r1Coord_mul hK (inv_mem hx.1) hx.1 hk
        rw [inv_mul_cancel, ← r1Elt_zero (K := K) (a := a), r1Coord_r1Elt hK _ hk,
          Pi.zero_apply, hx.2, add_zero] at h1
        exact h1.symm⟩ }
  have hle : rootJoin K a S ≤ T := iSup₂_le fun l hl => by
    rw [rootV, closure_le]
    rintro _ ⟨c, rfl⟩
    have hl' := hS l hl
    refine ⟨rootElt_mem_R1 hl' c, ?_⟩
    rw [rootElt_eq_r1Elt hl', r1Coord_r1Elt hK _ hk, Pi.single_eq_of_ne]
    rintro rfl
    exact hkS hl
  exact (hle hg).2

end Model

section Generic

variable {X : Type*} [Group X]

theorem commutator_ne_of_isPGroup [Finite X] {p : ℕ} [Fact p.Prime] {Y N : Subgroup X}
    (hY : IsPGroup p Y) (hNY : N ≤ Y) (hN1 : N ≠ ⊥) : ⁅N, Y⁆ ≠ N := by
  intro heq
  have hYn : Group.IsNilpotent Y := hY.isNilpotent
  obtain ⟨n, hn⟩ := (Subgroup.isNilpotent_iff_lowerCentralSeries Y).1 hYn
  have hle : ∀ m : ℕ, N ≤ Y.lowerCentralSeries m := by
    intro m
    induction m with
    | zero => exact hNY
    | succ m ih =>
      rw [Subgroup.lowerCentralSeries_succ, ← heq]
      exact commutator_mono ih le_rfl
  exact hN1 (le_bot_iff.1 (hn ▸ hle n))

end Generic

namespace Setup

variable {G : Type} [Group G] [Finite G]
  (h : Setup G)

theorem pull_commutator {M M' : Subgroup (ModGL F4.tag h.K)} (hM : M ≤ F4.reeGamma h.K h.a)
    (hM' : M' ≤ F4.reeGamma h.K h.a) : h.pull ⁅M, M'⁆ = ⁅h.pull M, h.pull M'⁆ := by
  have e : ∀ {N : Subgroup (ModGL F4.tag h.K)}, N ≤ F4.reeGamma h.K h.a →
      N = (N.subgroupOf (F4.reeGamma h.K h.a)).map (F4.reeGamma h.K h.a).subtype := fun hN => by
    rw [subgroupOf_map_subtype, inf_eq_left.2 hN]
  have hc : ⁅M, M'⁆.subgroupOf (F4.reeGamma h.K h.a) =
      ⁅M.subgroupOf (F4.reeGamma h.K h.a), M'.subgroupOf (F4.reeGamma h.K h.a)⁆ := by
    conv_lhs => rw [e hM, e hM', ← map_commutator]
    exact comap_map_eq_self_of_injective (F4.reeGamma h.K h.a).subtype_injective _
  rw [pull, hc, map_commutator]
  rfl

theorem radR_le_reeGamma : radR h.K h.a ≤ F4.reeGamma h.K h.a := by
  rw [(radR_spec h.card_K).1]
  exact inf_le_right

theorem R1_le_reeGamma : R1 h.K h.a ≤ F4.reeGamma h.K h.a :=
  (R1_le_radR h.card_K).trans h.radR_le_reeGamma

theorem R₁_le_R : h.R₁ ≤ h.R := h.pull_mono (R1_le_radR h.card_K)

theorem commutator_R_R : ⁅h.R, h.R⁆ = h.R₁ := by
  rw [R, R₁, ← h.pull_commutator h.radR_le_reeGamma h.radR_le_reeGamma,
    commutator_radR_radR h.card_K]

theorem commutator_R_R₁ : ⁅h.R, h.R₁⁆ = h.V .i12 := by
  rw [R, R₁, V, ← h.pull_commutator h.radR_le_reeGamma h.R1_le_reeGamma,
    commutator_radR_R1 h.card_K]

theorem comm_mem_V12 {r x : G} (hr : r ∈ h.R) (hx : x ∈ h.R₁) : ⁅r, x⁆ ∈ h.V .i12 := by
  rw [← h.commutator_R_R₁]
  exact commutator_mem_commutator hr hx

theorem R_inf_centralizer_R₁ : h.R ⊓ centralizer (h.R₁ : Set G) = h.V .i5 ⊔ h.R₁ := by
  have e : h.R ⊓ (h.L ⊓ centralizer (h.R₁ : Set G)) = h.V .i5 ⊔ h.R₁ := by
    have e := congrArg h.pull (radR_inf_centralizer_R1 h.card_K)
    rw [h.pull_inf, h.pull_centralizer_subgroup h.R1_le_reeGamma,
      h.pull_sup (rootV_le_reeGamma h.card_K _) h.R1_le_reeGamma] at e
    exact e
  have hRL : h.R ⊓ h.L = h.R := inf_eq_left.2 (h.pull_le_L _)
  rw [← e, ← inf_assoc, hRL]

theorem R₁_inf_centralizer_R_le : h.R₁ ⊓ centralizer (h.R : Set G) ≤ h.V .i12 := by
  have e : h.R₁ ⊓ (h.L ⊓ centralizer (h.R : Set G)) ≤ h.V .i12 := by
    have e := h.pull_mono (R1_inf_centralizer_radR_le h.card_K)
    rw [h.pull_inf, h.pull_centralizer_subgroup h.radR_le_reeGamma] at e
    exact e
  have hRL : h.R₁ ⊓ h.L = h.R₁ := inf_eq_left.2 (h.pull_le_L _)
  rwa [← inf_assoc, hRL] at e

theorem P_le_R_sup_V1 : h.P ≤ h.R ⊔ h.V .i1 := by
  have e := h.pull_mono (sylowP_le_radR_sup h.card_K)
  rwa [h.pull_sup h.radR_le_reeGamma (rootV_le_reeGamma h.card_K _)] at e

theorem torusPair_mem_reeGamma (t : h.Kˣ × h.Kˣ) : torusPair h.a t ∈ F4.reeGamma h.K h.a :=
  torusH_le_reeGamma h.card_K ⟨t, rfl⟩

theorem elt_torusPair_mem_H (t : h.Kˣ × h.Kˣ) : h.elt (torusPair h.a t) ∈ h.H :=
  (h.elt_mem_pull (h.torusPair_mem_reeGamma t)).2 ⟨t, rfl⟩

theorem elt_torusPair_mem_Ht_iff {i : Idx} (t : h.Kˣ × h.Kˣ) :
    h.elt (torusPair h.a t) ∈ h.Ht i ↔ torusPair h.a t ∈ torusHi h.K h.a i :=
  h.elt_mem_pull (h.torusPair_mem_reeGamma t)

theorem elt_torusPair_conj_rootElt (t : h.Kˣ × h.Kˣ) (k : Idx) (c : h.K) :
    h.elt (torusPair h.a t) * h.elt (rootElt h.K h.a k c) * (h.elt (torusPair h.a t))⁻¹ =
      h.elt (rootElt h.K h.a k ((rootChar h.K h.a k t : h.K) * c)) := by
  rw [← h.elt_conj' (h.torusPair_mem_reeGamma t)
    (rootV_le_reeGamma h.card_K k (rootElt_mem_rootV _ _)), torusPair_conj_rootElt h.card_K]

theorem eq_one_of_H5_invariant_R {X : Type*} [Group X] {f : G → X}
    (hf : ∀ x ∈ h.R, ∀ y ∈ h.R, f (x * y) = f x * f y)
    (hinv : ∀ b ∈ h.Ht .i5, ∀ x ∈ h.R, f (b * x * b⁻¹) = f x)
    (h5 : ∀ v ∈ h.V .i5, f v = 1) : ∀ x ∈ h.R, f x = 1 := by
  have hRΓ := h.radR_le_reeGamma
  have key := eq_one_of_torusHi_five_invariant_radR (f := fun g => f (h.elt g)) h.one_le_a
    h.card_K (fun x hx y hy => by
      rw [h.elt_mul' (hRΓ hx) (hRΓ hy)]
      exact hf _ ((h.elt_mem_pull (hRΓ hx)).2 hx) _ ((h.elt_mem_pull (hRΓ hy)).2 hy))
    (fun t ht x hx => by
      rw [h.elt_conj' (h.torusPair_mem_reeGamma t) (hRΓ hx)]
      exact hinv _ ((h.elt_torusPair_mem_Ht_iff t).2 ht) _ ((h.elt_mem_pull (hRΓ hx)).2 hx))
    (fun c => h5 _ (h.elt_rootElt_mem_V _ c))
  intro x hx
  obtain ⟨g, hg, -, rfl⟩ := h.mem_pull_iff_elt.1 hx
  exact key g hg

theorem eq_one_of_H5_invariant_R₁ {X : Type*} [Group X] {f : G → X}
    (hf : ∀ x ∈ h.R₁, ∀ y ∈ h.R₁, f (x * y) = f x * f y)
    (hinv : ∀ b ∈ h.Ht .i5, ∀ x ∈ h.R₁, f (b * x * b⁻¹) = f x)
    (h12 : ∀ v ∈ h.V .i12, f v = 1) : ∀ x ∈ h.R₁, f x = 1 := by
  have hRΓ := h.R1_le_reeGamma
  have key := eq_one_of_torusHi_five_invariant_R1 (f := fun g => f (h.elt g)) h.one_le_a
    h.card_K (fun x hx y hy => by
      rw [h.elt_mul' (hRΓ hx) (hRΓ hy)]
      exact hf _ ((h.elt_mem_pull (hRΓ hx)).2 hx) _ ((h.elt_mem_pull (hRΓ hy)).2 hy))
    (fun t ht x hx => by
      rw [h.elt_conj' (h.torusPair_mem_reeGamma t) (hRΓ hx)]
      exact hinv _ ((h.elt_torusPair_mem_Ht_iff t).2 ht) _ ((h.elt_mem_pull (hRΓ hx)).2 hx))
    (fun c => h12 _ (h.elt_rootElt_mem_V _ c))
  intro x hx
  obtain ⟨g, hg, -, rfl⟩ := h.mem_pull_iff_elt.1 hx
  exact key g hg

@[expose] def unpull (M : Subgroup G) : Subgroup (ModGL F4.tag h.K) :=
  (M.comap h.emb).map (F4.reeGamma h.K h.a).subtype

theorem pull_unpull {M : Subgroup G} (hM : M ≤ h.L) : h.pull (h.unpull M) = M := by
  rw [pull, unpull, subgroupOf, comap_map_eq_self_of_injective (subtype_injective _),
    map_comap_eq, range_emb, inf_eq_right.2 hM]

theorem mem_unpull {M : Subgroup G} {g : ModGL F4.tag h.K} (hg : g ∈ F4.reeGamma h.K h.a) :
    g ∈ h.unpull M ↔ h.elt g ∈ M := by
  rw [h.elt_of_mem hg]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hgM
    exact ⟨⟨g, hg⟩, hgM, rfl⟩

theorem unpull_le_reeGamma (M : Subgroup G) : h.unpull M ≤ F4.reeGamma h.K h.a := by
  rintro _ ⟨y, -, rfl⟩
  exact y.2

theorem conj_mem_unpull {M : Subgroup G} {g : ModGL F4.tag h.K} (hg : g ∈ F4.reeGamma h.K h.a)
    (hgM : h.elt g ∈ normalizer (M : Set G)) {x : ModGL F4.tag h.K} (hx : x ∈ h.unpull M) :
    g * x * g⁻¹ ∈ h.unpull M := by
  have hxΓ := h.unpull_le_reeGamma M hx
  rw [h.mem_unpull (mul_mem (mul_mem hg hxΓ) (inv_mem hg)), h.elt_conj' hg hxΓ]
  exact (mem_normalizer_iff.1 hgM _).1 ((h.mem_unpull hxΓ).1 hx)

theorem le_V12_of_invariant {M : Subgroup G} (hMR : M ≤ h.R₁)
    (hH : h.H ≤ normalizer (M : Set G))
    (h1 : h.elt (rootElt h.K h.a .i1 1) ∈ normalizer (M : Set G))
    (hr : h.r ∈ normalizer (M : Set G)) (hne : M ≠ h.R₁) : M ≤ h.V .i12 := by
  have hML : M ≤ h.L := hMR.trans (h.pull_le_L _)
  have h1Γ : rootElt h.K h.a .i1 1 ∈ F4.reeGamma h.K h.a :=
    rootV_le_reeGamma h.card_K _ (rootElt_mem_rootV _ _)
  have hrΓ : weylR h.K ∈ F4.reeGamma h.K h.a := weylR_mem_reeGamma
  have hr' : h.elt (weylR h.K) = h.r := h.elt_of_mem hrΓ
  have hle : h.unpull M ≤ R1 h.K h.a := fun x hx => by
    have hxΓ := h.unpull_le_reeGamma M hx
    exact (h.elt_mem_pull hxΓ).1 (hMR ((h.mem_unpull hxΓ).1 hx))
  have key := le_rootV_twelve_of_invariant h.one_le_a h.card_K hle
    (fun t x hx => h.conj_mem_unpull (h.torusPair_mem_reeGamma t)
      (hH (h.elt_torusPair_mem_H t)) hx)
    (fun x hx => h.conj_mem_unpull h1Γ h1 hx)
    (fun x hx => h.conj_mem_unpull hrΓ (hr' ▸ hr) hx)
    (fun heq => hne (by rw [← h.pull_unpull hML, heq]; rfl))
  have := h.pull_mono key
  rwa [h.pull_unpull hML] at this

open Classical in
@[expose] def toΓ (x : G) : ModGL F4.tag h.K :=
  if hx : x ∈ h.L then ((h.ι.symm ⟨x, hx⟩ : F4.reeGamma h.K h.a) : ModGL F4.tag h.K) else 1

theorem toΓ_mem (x : G) : h.toΓ x ∈ F4.reeGamma h.K h.a := by
  unfold toΓ
  split_ifs
  · exact Subtype.property _
  · exact one_mem _

theorem elt_toΓ {x : G} (hx : x ∈ h.L) : h.elt (h.toΓ x) = x := by
  rw [h.elt_of_mem (h.toΓ_mem x)]
  have e : (⟨h.toΓ x, h.toΓ_mem x⟩ : F4.reeGamma h.K h.a) = h.ι.symm ⟨x, hx⟩ :=
    Subtype.ext (show h.toΓ x = _ by unfold toΓ; exact dite_eq_left hx)
  rw [e]
  exact h.emb_symm ⟨x, hx⟩

theorem toΓ_elt {g : ModGL F4.tag h.K} (hg : g ∈ F4.reeGamma h.K h.a) : h.toΓ (h.elt g) = g :=
  h.elt_injOn (h.toΓ_mem _) hg (h.elt_toΓ (h.elt_mem hg))

theorem toΓ_mem_iff {M : Subgroup (ModGL F4.tag h.K)} {x : G} (hx : x ∈ h.L) :
    h.toΓ x ∈ M ↔ x ∈ h.pull M := by
  rw [← h.elt_mem_pull (h.toΓ_mem x), h.elt_toΓ hx]

theorem toΓ_mul {x y : G} (hx : x ∈ h.L) (hy : y ∈ h.L) :
    h.toΓ (x * y) = h.toΓ x * h.toΓ y := by
  conv_lhs => rw [← h.elt_toΓ hx, ← h.elt_toΓ hy, ← h.elt_mul' (h.toΓ_mem x) (h.toΓ_mem y)]
  exact h.toΓ_elt (mul_mem (h.toΓ_mem x) (h.toΓ_mem y))

@[expose] def r1c (x : G) : Idx → h.K := r1Coord h.a (h.toΓ x)

theorem elt_r1Elt_r1c {x : G} (hx : x ∈ h.R₁) : h.elt (r1Elt h.K h.a (h.r1c x)) = x := by
  rw [r1c, r1Elt_r1Coord h.card_K ((h.toΓ_mem_iff (h.pull_le_L _ hx)).2 hx),
    h.elt_toΓ (h.pull_le_L _ hx)]

theorem r1c_elt_r1Elt (u : Idx → h.K) {k : Idx} (hk : k.isR1 = true) :
    h.r1c (h.elt (r1Elt h.K h.a u)) k = u k := by
  rw [r1c, h.toΓ_elt (h.R1_le_reeGamma (r1Elt_mem u)), r1Coord_r1Elt h.card_K _ hk]

theorem r1c_mul {x y : G} (hx : x ∈ h.R₁) (hy : y ∈ h.R₁) {k : Idx} (hk : k.isR1 = true) :
    h.r1c (x * y) k = h.r1c x k + h.r1c y k := by
  rw [r1c, r1c, r1c, h.toΓ_mul (h.pull_le_L _ hx) (h.pull_le_L _ hy),
    r1Coord_mul h.card_K ((h.toΓ_mem_iff (h.pull_le_L _ hx)).2 hx)
      ((h.toΓ_mem_iff (h.pull_le_L _ hy)).2 hy) hk]

theorem r1c_one {k : Idx} (hk : k.isR1 = true) : h.r1c 1 k = 0 := by
  rw [← h.elt_one', ← r1Elt_zero (K := h.K) (a := h.a), h.r1c_elt_r1Elt _ hk, Pi.zero_apply]

theorem r1c_inv {x : G} (hx : x ∈ h.R₁) {k : Idx} (hk : k.isR1 = true) :
    h.r1c x⁻¹ k = h.r1c x k := by
  have e := h.r1c_mul (inv_mem hx) hx hk
  rw [inv_mul_cancel, h.r1c_one hk] at e
  have h2 : h.r1c x k + h.r1c x k = 0 := CharTwo.add_self_eq_zero _
  linear_combination -e - h2

theorem eq_of_r1c_eq {x y : G} (hx : x ∈ h.R₁) (hy : y ∈ h.R₁)
    (hxy : ∀ k : Idx, k.isR1 = true → h.r1c x k = h.r1c y k) : x = y := by
  rw [← h.elt_r1Elt_r1c hx, ← h.elt_r1Elt_r1c hy, (r1Elt_eq_iff h.card_K).2 hxy]

theorem r1c_eq_zero_of_mem {S : Finset Idx} (hS : ∀ l ∈ S, l.isR1 = true) {x : G}
    (hx : x ∈ h.pull (rootJoin h.K h.a S)) {k : Idx} (hk : k.isR1 = true) (hkS : k ∉ S) :
    h.r1c x k = 0 :=
  r1Coord_eq_zero_of_mem_rootJoin h.card_K hS ((h.toΓ_mem_iff (h.pull_le_L _ hx)).2 hx) hk hkS

theorem r1c_eq_zero_of_mem_V12 {v : G} (hv : v ∈ h.V .i12) {k : Idx} (hk : k.isR1 = true)
    (hk12 : k ≠ .i12) : h.r1c v k = 0 := by
  refine h.r1c_eq_zero_of_mem (S := {.i12}) (by decide) ?_ hk (by simpa using hk12)
  have e : rootJoin h.K h.a {.i12} = rootV h.K h.a .i12 := by
    rw [rootJoin]
    simp
  rw [e]
  exact hv

theorem mem_of_r1c_eq_zero {S : Finset Idx} {x : G} (hx : x ∈ h.R₁)
    (h0 : ∀ k : Idx, k.isR1 = true → k ∉ S → h.r1c x k = 0) :
    x ∈ h.pull (rootJoin h.K h.a S) := by
  rw [← h.elt_r1Elt_r1c hx, h.elt_mem_pull (h.R1_le_reeGamma (r1Elt_mem _))]
  have hm : ∀ k : Idx, k.isR1 = true → rootElt h.K h.a k (h.r1c x k) ∈ rootJoin h.K h.a S :=
    fun k hk => by
      by_cases hkS : k ∈ S
      · exact rootV_le_rootJoin hkS (rootElt_mem_rootV _ _)
      · rw [h0 k hk hkS, rootElt_zero]
        exact one_mem _
  exact mul_mem (mul_mem (mul_mem (mul_mem (hm .i8 rfl) (hm .i11 rfl)) (hm .i12 rfl))
    (hm .i9 rfl)) (hm .i10 rfl)

theorem r1c_conj_R {g x : G} (hg : g ∈ h.R) (hx : x ∈ h.R₁) {k : Idx} (hk : k.isR1 = true)
    (hk12 : k ≠ .i12) : h.r1c (g * x * g⁻¹) k = h.r1c x k := by
  have hc := h.comm_mem_V12 hg hx
  have hcR : ⁅g, x⁆ ∈ h.R₁ := h.pull_mono (rootV_le_rootJoin (by decide)) hc
  have e : g * x * g⁻¹ = ⁅g, x⁆ * x := by simp only [commutatorElement_def]; group
  rw [e, h.r1c_mul hcR hx hk, h.r1c_eq_zero_of_mem_V12 hc hk hk12, zero_add]

theorem r1c_torus {x : G} (hx : x ∈ h.R₁) (t : h.Kˣ × h.Kˣ) {k : Idx} (hk : k.isR1 = true) :
    h.r1c (h.elt (torusPair h.a t) * x * (h.elt (torusPair h.a t))⁻¹) k =
      (rootChar h.K h.a k t : h.K) * h.r1c x k := by
  conv_lhs => rw [← h.elt_r1Elt_r1c hx, ← h.elt_conj' (h.torusPair_mem_reeGamma t)
    (h.R1_le_reeGamma (r1Elt_mem _)), torusPair_conj_r1Elt h.card_K]
  rw [h.r1c_elt_r1Elt _ hk]

theorem r1c_eq_zero_of_brace_ne {i j : Idx} (hi : i.isCenter = false) {Ψ : h.K → G}
    (hadd : ∀ c d : h.K, ∀ k : Idx, k.isR1 = true → k ≠ .i12 →
      h.r1c (Ψ (c + d)) k = h.r1c (Ψ c) k + h.r1c (Ψ d) k)
    (hequiv : ∀ t : h.Kˣ × h.Kˣ, torusPair h.a t ∈ torusHi h.K h.a i → ∀ c : h.K,
      ∀ k : Idx, k.isR1 = true → k ≠ .i12 →
        h.r1c (Ψ ((rootChar h.K h.a j t : h.K) * c)) k =
          (rootChar h.K h.a k t : h.K) * h.r1c (Ψ c) k)
    {k : Idx} (hk : k.isR1 = true) (hk12 : k ≠ .i12) (hb : Idx.brace i j ≠ Idx.brace i k)
    (c : h.K) : h.r1c (Ψ c) k = 0 := by
  classical
  let φ : h.K → Idx → h.K := fun c l => if l.isR1 = true ∧ l ≠ .i12 then h.r1c (Ψ c) l else 0
  have hφ := miyamoto_2_1_pi (ρ := id) (φ := φ) h.one_le_a h.card_K hi
    (fun x y => funext fun l => by
      simp only [φ, Pi.add_apply]
      split_ifs with hl
      · exact hadd x y l hl.1 hl.2
      · rw [add_zero])
    (fun t ht x l => by
      simp only [φ, id]
      split_ifs with hl
      · exact hequiv t ht x l hl.1 hl.2
      · rw [mul_zero])
    (l := k) hb c
  simpa [φ, hk, hk12] using hφ

end Setup

end CFSG.LocalAnalysis.EvenBN.TwoF4
