module

public import CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialProduct
public import CFSG.LocalAnalysis.EvenBN.Sp4.ProductModelGen

public section

namespace CFSG.LocalAnalysis.EvenBN.Sp4

namespace BothTrivialProduct

open Subgroup CFSG.Blueprint CFSG.Open
open CFSG.LocalAnalysis.SymplecticFourStandard
open GomiFusion RootAxisTwoCore FullCenter FullCenterRadical FullCenterParabolic
  FullCenterTorus FullCenterWeyl FullCenterMutual BothTrivial BothTrivialHeisenberg
  BothTrivialClosure BothTrivialLayer BothTrivialRankOne BothTrivialSlice BothTrivialField
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis
open scoped MatrixGroups

section Abstract

variable {G : Type*} [Group G]

theorem conj_mem_ncl {N A : Subgroup G} {m : G} (hm : m ∈ N) {z : G}
    (hz : z ∈ closure {x : G | ∃ g ∈ N, ∃ y ∈ A, x = g⁻¹ * y * g}) :
    m * z * m⁻¹ ∈ closure {x : G | ∃ g ∈ N, ∃ y ∈ A, x = g⁻¹ * y * g} := by
  have hle : closure {x : G | ∃ g ∈ N, ∃ y ∈ A, x = g⁻¹ * y * g} ≤
      (closure {x : G | ∃ g ∈ N, ∃ y ∈ A, x = g⁻¹ * y * g}).comap
        (MulAut.conj m).toMonoidHom := by
    refine (closure_le _).mpr ?_
    rintro _ ⟨g, hg, y, hy, rfl⟩
    refine subset_closure ⟨g * m⁻¹, mul_mem hg (inv_mem hm), y, hy, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  exact hle hz

theorem ncl_eq_of_le {N A B : Subgroup G}
    (hAB : A ≤ closure {x : G | ∃ g ∈ N, ∃ y ∈ B, x = g⁻¹ * y * g})
    (hBA : B ≤ closure {x : G | ∃ g ∈ N, ∃ y ∈ A, x = g⁻¹ * y * g}) :
    closure {x : G | ∃ g ∈ N, ∃ y ∈ A, x = g⁻¹ * y * g} =
      closure {x : G | ∃ g ∈ N, ∃ y ∈ B, x = g⁻¹ * y * g} := by
  refine le_antisymm ((closure_le _).mpr ?_) ((closure_le _).mpr ?_)
  · rintro _ ⟨g, hg, y, hy, rfl⟩
    have := conj_mem_ncl (inv_mem hg) (hAB hy)
    rwa [inv_inv] at this
  · rintro _ ⟨g, hg, y, hy, rfl⟩
    have := conj_mem_ncl (inv_mem hg) (hBA hy)
    rwa [inv_inv] at this

theorem mem_ncl_iff {N N' A A' : Subgroup G} {g : G}
    (hN : ∀ m, m ∈ N ↔ g * m * g⁻¹ ∈ N') (hA : ∀ y, y ∈ A ↔ g * y * g⁻¹ ∈ A') (z : G) :
    z ∈ closure {x : G | ∃ m ∈ N, ∃ y ∈ A, x = m⁻¹ * y * m} ↔
      g * z * g⁻¹ ∈ closure {x : G | ∃ m ∈ N', ∃ y ∈ A', x = m⁻¹ * y * m} := by
  have key : ∀ {N N' A A' : Subgroup G} {g : G}, (∀ m ∈ N, g * m * g⁻¹ ∈ N') →
      (∀ y ∈ A, g * y * g⁻¹ ∈ A') → ∀ z ∈ closure {x : G | ∃ m ∈ N, ∃ y ∈ A, x = m⁻¹ * y * m},
        g * z * g⁻¹ ∈ closure {x : G | ∃ m ∈ N', ∃ y ∈ A', x = m⁻¹ * y * m} := by
    intro N N' A A' g hN hA z hz
    have hle : closure {x : G | ∃ m ∈ N, ∃ y ∈ A, x = m⁻¹ * y * m} ≤
        (closure {x : G | ∃ m ∈ N', ∃ y ∈ A', x = m⁻¹ * y * m}).comap
          (MulAut.conj g).toMonoidHom := by
      refine (closure_le _).mpr ?_
      rintro _ ⟨m, hm, y, hy, rfl⟩
      refine subset_closure ⟨g * m * g⁻¹, hN m hm, g * y * g⁻¹, hA y hy, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    exact hle hz
  refine ⟨key (fun m hm => (hN m).mp hm) (fun y hy => (hA y).mp hy) z, fun hz => ?_⟩
  have hN' : ∀ m ∈ N', g⁻¹ * m * g⁻¹⁻¹ ∈ N := fun m hm => by
    refine (hN _).mpr ?_
    rwa [show g * (g⁻¹ * m * g⁻¹⁻¹) * g⁻¹ = m by group]
  have hA' : ∀ y ∈ A', g⁻¹ * y * g⁻¹⁻¹ ∈ A := fun y hy => by
    refine (hA _).mpr ?_
    rwa [show g * (g⁻¹ * y * g⁻¹⁻¹) * g⁻¹ = y by group]
  have h2 := key hN' hA' _ hz
  rwa [show g⁻¹ * (g * z * g⁻¹) * g⁻¹⁻¹ = z by group] at h2

theorem mem_iff_of_map_conj_eq {H H' : Subgroup G} {g : G}
    (h : H.map (MulAut.conj g).toMonoidHom = H') (x : G) : x ∈ H ↔ g * x * g⁻¹ ∈ H' := by
  rw [← h]
  refine ⟨fun hx => ⟨x, hx, rfl⟩, ?_⟩
  rintro ⟨y, hy, hyx⟩
  have hyx' : g * y * g⁻¹ = g * x * g⁻¹ := hyx
  have : y = x := by simpa using hyx'
  rwa [← this]

theorem mem_normalizer_iff_of_map_conj_eq {H H' : Subgroup G} {g : G}
    (h : H.map (MulAut.conj g).toMonoidHom = H') (m : G) :
    m ∈ normalizer (H : Set G) ↔ g * m * g⁻¹ ∈ normalizer (H' : Set G) := by
  have e := mem_iff_of_map_conj_eq h
  rw [mem_normalizer_iff, mem_normalizer_iff]
  constructor
  · intro hm y
    have h1 := e (g⁻¹ * y * g)
    have h2 := hm (g⁻¹ * y * g)
    have h3 := e (m * (g⁻¹ * y * g) * m⁻¹)
    rw [show g * (g⁻¹ * y * g) * g⁻¹ = y by group] at h1
    rw [show g * (m * (g⁻¹ * y * g) * m⁻¹) * g⁻¹ = g * m * g⁻¹ * y * (g * m * g⁻¹)⁻¹ by group]
      at h3
    exact h1.symm.trans (h2.trans h3)
  · intro hm x
    have h1 := e x
    have h2 := hm (g * x * g⁻¹)
    have h3 := e (m * x * m⁻¹)
    rw [show g * m * g⁻¹ * (g * x * g⁻¹) * (g * m * g⁻¹)⁻¹ = g * (m * x * m⁻¹) * g⁻¹ by group]
      at h2
    exact h1.trans (h2.trans h3.symm)

theorem pull_le_of_le_sup_conj {X : Type*} [Group X] {L : Subgroup G} (φ : L ≃* X)
    {U C : Subgroup X} {w : X} {M : Subgroup G}
    (hC : C ≤ U ⊔ U.map (MulAut.conj w).toMonoidHom) (hU : pull φ U ≤ M)
    (hw : ∀ z ∈ M, ((φ.symm w : L) : G) * z * ((φ.symm w : L) : G)⁻¹ ∈ M) :
    pull φ C ≤ M := by
  intro x hx
  obtain ⟨c, hc, rfl⟩ := exists_eq_symm_of_mem_pull hx
  have hle : U ⊔ U.map (MulAut.conj w).toMonoidHom ≤
      M.comap (L.subtype.comp φ.symm.toMonoidHom) := by
    refine sup_le (fun u hu => ?_) ?_
    · exact hU (symm_mem_pull.mpr hu)
    · rintro _ ⟨u, hu, rfl⟩
      show ((φ.symm (w * u * w⁻¹) : L) : G) ∈ M
      rw [← symm_conj_eq φ w u]
      exact hw _ (hU (symm_mem_pull.mpr hu))
  exact hle (hC hc)

end Abstract

section Setting

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]
  [Finite K] {n : ℕ} {φ : L ≃* antiSp K} {t : G}

local notation "𝐀[" i "]" => pull φ (rootA K i)
local notation "𝐔[" i "]" => pull φ (rootU K i)
set_option quotPrecheck false in
local notation "𝐃[" i "]" => (CFSG.pCore 2 (normalizer
  (((zpowers t ⊔ pull φ (rootU K i) : Subgroup G) : Subgroup G) : Set G))).map
  (normalizer (((zpowers t ⊔ pull φ (rootU K i) : Subgroup G) : Subgroup G) : Set G)).subtype
set_option quotPrecheck false in
local notation "𝐄[" i "]" => (CFSG.pCore 2 (normalizer
  (((zpowers t ⊔ pull φ (rootA K i) : Subgroup G) : Subgroup G) : Set G))).map
  (normalizer (((zpowers t ⊔ pull φ (rootA K i) : Subgroup G) : Subgroup G) : Set G)).subtype
set_option quotPrecheck false in
local notation "𝐄₀" => (𝐄[Axis.one] ⊓ 𝐄[Axis.two] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐅" => closure {x : G | ∃ e ∈ 𝐄₀, ∃ j ∈ pull φ (diagTorus K),
  x = e⁻¹ * (j⁻¹ * e * j)}
local notation "𝐰[" i "]" => ((φ.symm (weylElt K i) : L) : G)
set_option quotPrecheck false in
local notation "𝐗[" i "]" => (𝐅 ⊔ 𝐅.map (MulAut.conj 𝐰[i]⁻¹).toMonoidHom : Subgroup G)
set_option quotPrecheck false in
local notation "𝐒" => (𝐗[Axis.one] ⊔ 𝐗[Axis.two] : Subgroup G)
local notation "𝐐" => (pull φ (antiUnipotent K) ⊔ zpowers t : Subgroup G)
set_option quotPrecheck false in
local notation "𝐍𝐂[" i "]" => closure {x : G | ∃ g ∈ normalizer (𝐗[i] : Set G),
  ∃ y ∈ (L ⊓ centralizer (𝐔[i] : Set G) : Subgroup G) ⊔ 𝐗[i], x = g⁻¹ * y * g}

theorem NC_eq_closure_conj_S (h : FCHyp L K n φ t)
    (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥) (i : Axis) :
    𝐍𝐂[i] = closure {x : G | ∃ g ∈ normalizer (𝐗[i] : Set G), ∃ s ∈ 𝐒, x = g⁻¹ * s * g} := by
  refine ncl_eq_of_le (fun y hy => ?_) (S_le_NC h hbt i)
  have hw : 𝐰[i] ∈ normalizer (𝐗[i] : Set G) := by
    have h1 := s_mem_CU h i (BothTrivialProductAxis.weylSL2 K)
    rw [BothTrivialProductAxis.sHom_weylSL2] at h1
    exact CU_le_normalizer_X h i h1
  have hSM : 𝐒 ≤ closure {x : G | ∃ g ∈ normalizer (𝐗[i] : Set G), ∃ s ∈ 𝐒, x = g⁻¹ * s * g} :=
    fun s hs => subset_closure ⟨1, one_mem _, s, hs, by group⟩
  have hPS : pull φ (antiUnipotent K) ≤ 𝐒 := ((S_inf_C h hbt).symm.le).trans inf_le_left
  have hCM : L ⊓ centralizer (𝐔[i] : Set G) ≤
      closure {x : G | ∃ g ∈ normalizer (𝐗[i] : Set G), ∃ s ∈ 𝐒, x = g⁻¹ * s * g} := by
    rw [CU_eq i]
    exact pull_le_of_le_sup_conj φ (ProductModel.rootC_le_antiUnipotent_sup i) (hPS.trans hSM)
      fun z hz => conj_mem_ncl hw hz
  exact sup_le hCM ((X_le_S i).trans hSM) hy

theorem map_conj_NC (h : FCHyp L K n φ t) (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥)
    {g : G} (hg : g ∈ normalizer (𝐐 : Set G)) (j : Axis) :
    ∃ k : Axis, (𝐍𝐂[j]).map (MulAut.conj g).toMonoidHom = 𝐍𝐂[k] := by
  have hS : ∀ y, y ∈ 𝐒 ↔ g * y * g⁻¹ ∈ 𝐒 :=
    mem_normalizer_iff.mp (normalizer_Q_le_normalizer_S h hbt hg)
  have key : ∀ k : Axis, 𝐗[j].map (MulAut.conj g).toMonoidHom = 𝐗[k] →
      (𝐍𝐂[j]).map (MulAut.conj g).toMonoidHom = 𝐍𝐂[k] := by
    intro k hX
    have hN := mem_normalizer_iff_of_map_conj_eq hX
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [NC_eq_closure_conj_S h hbt j] at hz
      rw [NC_eq_closure_conj_S h hbt k]
      exact (mem_ncl_iff hN hS z).mp hz
    · intro hx
      refine ⟨g⁻¹ * x * g, ?_, ?_⟩
      swap
      · show g * (g⁻¹ * x * g) * g⁻¹ = x
        group
      rw [NC_eq_closure_conj_S h hbt k] at hx
      rw [NC_eq_closure_conj_S h hbt j]
      refine (mem_ncl_iff hN hS _).mpr ?_
      rwa [show g * (g⁻¹ * x * g) * g⁻¹ = x by group]
  rcases h.map_B hg j with hk | hk
  · exact ⟨Axis.one, key _ (map_X_eq h hbt hk)⟩
  · exact ⟨Axis.two, key _ (map_X_eq h hbt hk)⟩

theorem normalizer_Q_le_normalizer_NC (h : FCHyp L K n φ t)
    (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥) :
    normalizer (𝐐 : Set G) ≤
      normalizer ((𝐍𝐂[Axis.one] ⊔ 𝐍𝐂[Axis.two] : Subgroup G) : Set G) := by
  intro g hg
  have hX : ∀ j : Axis, ∀ z ∈ 𝐍𝐂[j],
      g * z * g⁻¹ ∈ (𝐍𝐂[Axis.one] ⊔ 𝐍𝐂[Axis.two] : Subgroup G) := by
    intro j z hz
    obtain ⟨k, hk⟩ := map_conj_NC h hbt hg j
    have hz' : g * z * g⁻¹ ∈ (𝐍𝐂[j]).map (MulAut.conj g).toMonoidHom := ⟨z, hz, rfl⟩
    rw [hk] at hz'
    cases k
    · exact mem_sup_left hz'
    · exact mem_sup_right hz'
  exact mem_normalizer_of_conj_le fun x hx => conj_mem_of_sup (hX Axis.one) (hX Axis.two) hx

theorem isSylowOf_Q (h : FCHyp L K n φ t) :
    CFSG.ABGLocalTools.IsSylowOf 2 𝐐 (L ⊔ zpowers t) := by
  have hle : (𝐐 : Subgroup G) ≤ L ⊔ zpowers t :=
    sup_le (le_sup_of_le_left (pull_le φ _)) le_sup_right
  have hQ : Nat.card (𝐐 : Subgroup G) = 2 * Nat.card K ^ 4 := h.card_Q
  have hLt : Nat.card (L ⊔ zpowers t : Subgroup G) =
      2 * (Nat.card K ^ 4 * ((Nat.card K ^ 2 - 1) * (Nat.card K ^ 4 - 1))) := by
    rw [sup_comm, card_sup_of_commute (fun x hx y hy => h.twoCore.zpowers_comm hx hy)
      (h.twoCore.zpowers_inf le_rfl), Nat.card_zpowers, h.setup.order_t,
      Nat.card_congr φ.toEquiv, card_antiSp rfl]
  rw [CFSG.ABGLocalTools.isSylowOf_iff]
  refine ⟨hle, IsPGroup.of_card (by rw [hQ, h.setup.card_K, ← pow_mul, ← pow_succ']), ?_⟩
  have h1 := Subgroup.relIndex_mul_card (𝐐 : Subgroup G) (L ⊔ zpowers t)
  rw [inf_eq_left.mpr hle, hQ, hLt] at h1
  have hq0 : 0 < 2 * Nat.card K ^ 4 := by
    have : 0 < Nat.card K := Nat.card_pos
    positivity
  have h2 : (𝐐 : Subgroup G).relIndex (L ⊔ zpowers t) =
      (Nat.card K ^ 2 - 1) * (Nat.card K ^ 4 - 1) :=
    Nat.eq_of_mul_eq_mul_right hq0 (by rw [h1]; ring)
  have hodd : Odd ((Nat.card K ^ 2 - 1) * (Nat.card K ^ 4 - 1)) := by
    have he2 : Even (Nat.card K) := by
      rw [h.setup.card_K, Nat.even_pow]
      exact ⟨even_two, by have := h.setup.two_le; omega⟩
    have hq1 : 1 ≤ Nat.card K := Nat.card_pos
    refine Odd.mul ?_ ?_
    · exact Nat.Even.sub_odd (Nat.one_le_pow _ _ hq1) (Even.pow_of_ne_zero he2 (by norm_num))
        odd_one
    · exact Nat.Even.sub_odd (Nat.one_le_pow _ _ hq1) (Even.pow_of_ne_zero he2 (by norm_num))
        odd_one
  rw [h2]
  exact fun hdvd => (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)

end Setting

end BothTrivialProduct

end CFSG.LocalAnalysis.EvenBN.Sp4
