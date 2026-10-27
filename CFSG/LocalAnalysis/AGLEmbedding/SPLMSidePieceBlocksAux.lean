module

public import CFSG.LocalAnalysis.AGLEmbedding.SPLMSidePieces
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBZeroAb
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLK0NN
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLK0SmallKFact
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLHatAssembly

public section

namespace CFSG.AGLEmbedding.SPLMSide

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Components

variable {Y : Type} [Group Y] [Finite Y]

theorem commute_of_mem_pCore_of_isComponent {p : ℕ} [Fact p.Prime] {Λ : Subgroup Y}
    (hΛ : CFSG.IsComponent Λ) {x : Y} (hx : x ∈ CFSG.pCore p Y) {a : Y} (ha : a ∈ Λ) :
    x * a = a * x := by
  have : Group.IsNilpotent (CFSG.pCore p Y) :=
    (CFSG.pCore_isPGroup (p := p) (G := Y)).isNilpotent
  have h := (CFSG.LocalCores.component_solvable_centralizer (R := CFSG.pCore p Y) inferInstance
    CFSG.pCore_normal.isSubnormal).1 Λ hΛ
  have h2 := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h ha
  exact Subgroup.mem_centralizer_iff.mp h2 x hx

theorem commute_conj_of_mem_center_isComponent {Λ : Subgroup Y} (hΛ : CFSG.IsComponent Λ)
    {φ : Y} (hφ : φ ∈ Λ) (hc : ∀ a ∈ Λ, a * φ = φ * a) (g h : Y) :
    Commute (g * φ * g⁻¹) (h * φ * h⁻¹) := by
  have hg := CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj g) hΛ
  have hh := CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj h) hΛ
  have hgφ : g * φ * g⁻¹ ∈ Λ.map (MulAut.conj g).toMonoidHom := ⟨φ, hφ, by simp⟩
  have hhφ : h * φ * h⁻¹ ∈ Λ.map (MulAut.conj h).toMonoidHom := ⟨φ, hφ, by simp⟩
  rcases CFSG.LocalCores.distinct_components_commute hg hh with he | hbot
  · rw [← he] at hhφ
    obtain ⟨a, ha, hae⟩ := hhφ
    have : (MulAut.conj g).toMonoidHom a * (MulAut.conj g).toMonoidHom φ =
        (MulAut.conj g).toMonoidHom φ * (MulAut.conj g).toMonoidHom a := by
      rw [← map_mul, ← map_mul, hc a ha]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this hae
    rw [Commute, SemiconjBy, ← hae]
    simpa [mul_assoc] using this.symm
  · have h2 := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot hgφ
    exact (Subgroup.mem_centralizer_iff.mp h2 _ hhφ).symm

theorem mem_pCore_of_mem_center_isComponent {p : ℕ} {Λ : Subgroup Y}
    (hΛ : CFSG.IsComponent Λ) {φ : Y} (hφ : φ ∈ Λ) (hc : ∀ a ∈ Λ, a * φ = φ * a)
    (hp : ∃ k : ℕ, φ ^ p ^ k = 1) : φ ∈ CFSG.pCore p Y := by
  set N := Subgroup.normalClosure ({φ} : Set Y) with hN
  have hconj : ∀ b ∈ Group.conjugatesOfSet ({φ} : Set Y), ∃ g : Y, g * φ * g⁻¹ = b := by
    intro b hb
    rw [Group.conjugatesOfSet, Set.mem_iUnion₂] at hb
    obtain ⟨a, ha, hab⟩ := hb
    rw [Set.mem_singleton_iff] at ha
    subst ha
    exact isConj_iff.mp hab
  have hcomm : (Group.conjugatesOfSet ({φ} : Set Y)).Pairwise Commute := by
    intro b hb b' hb' _
    obtain ⟨g, rfl⟩ := hconj b hb
    obtain ⟨g', rfl⟩ := hconj b' hb'
    exact commute_conj_of_mem_center_isComponent hΛ hφ hc g g'
  have hNc : IsMulCommutative N := Subgroup.isMulCommutative_closure hcomm
  obtain ⟨k₀, hk₀⟩ := hp
  have hNp : IsPGroup p N := by
    rintro ⟨x, hx⟩
    suffices h : ∃ k : ℕ, x ^ p ^ k = 1 by
      obtain ⟨k, hk⟩ := h
      exact ⟨k, Subtype.ext (by simpa using hk)⟩
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hconj x hx
      exact ⟨k₀, by rw [conj_pow, hk₀, mul_one, mul_inv_cancel]⟩
    | one => exact ⟨0, one_pow _⟩
    | mul x y hx hy ihx ihy =>
      obtain ⟨a, ha⟩ := ihx
      obtain ⟨b, hb⟩ := ihy
      have hxy : Commute x y := congrArg Subtype.val (hNc.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
      refine ⟨a + b, ?_⟩
      rw [hxy.mul_pow, pow_add, pow_mul, ha, one_pow, one_mul, mul_comm, pow_mul, hb, one_pow]
    | inv x hx ihx =>
      obtain ⟨a, ha⟩ := ihx
      exact ⟨a, by rw [inv_pow, ha, inv_one]⟩
  have hNle : N ≤ CFSG.pCore p Y :=
    le_sSup (s := {K : Subgroup Y | K.Normal ∧ IsPGroup p K}) ⟨inferInstance, hNp⟩
  exact hNle (Subgroup.subset_normalClosure (Set.mem_singleton φ))

end Components

section Pair

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} {z : G}

omit [Finite G] in
theorem pCore_eq_barM_of_sup_eq {X : Subgroup G} (hXM : X ≤ M)
    (h : X ⊔ pCoreOf 2 M = pCorePreimage p M) :
    CFSG.pCore p (↥M ⧸ CFSG.pCore 2 ↥M) = barM M X := by
  have hQ : barM M (pCoreOf 2 M) = ⊥ := by
    rw [barM, Subgroup.map_eq_bot_iff]
    intro q hq
    exact (mk_eq_one_iff_coe_mem_pCoreOf q).mpr (Subgroup.mem_subgroupOf.mp hq)
  have h1 : barM M (pCorePreimage p M) = CFSG.pCore p (↥M ⧸ CFSG.pCore 2 ↥M) := by
    rw [barM, pCorePreimage_subgroupOf,
      Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]
  rw [← h1, ← h]
  unfold barM at hQ ⊢
  rw [Subgroup.subgroupOf_sup hXM (CFSG.PreuniquenessRankFour.Helpers.pCoreOf_le 2 M),
    Subgroup.map_sup, hQ, sup_bot_eq]

theorem pairData_pCorePreimage_facts (hFi : KFactSPLNotFi22) (hUP : KFactUPrimeSmall)
    (hSTO : KFactSmallThreeOrders) (hKU2 : KFactUnitarySylowStructure)
    (h84 : Asc81bEightFour) (hD2 : D1NoXBlock) (D : D1SPLPairData p P M H R Rbar K z) :
    D1PhaseThree p P M H R ∧
      (∀ a ∈ d1LiftX p H R K, ∀ b ∈ d1LiftX p H R K, a * b = b * a) ∧
      d1LiftX p H R K ≤ pCorePreimage p M ∧
      d1LiftX p H R K ⊔ pCoreOf 2 M = pCorePreimage p M := by
  obtain ⟨h3, -, -, -, hXab⟩ :=
    D.data.splPair_facts hFi hUP hSTO hKU2 h84 hD2 D.czElt D.family D.sp D.posK D.posC D.pair
  obtain ⟨hXY, hYeq⟩ := pair_pCorePreimage_facts hFi hUP hSTO hKU2 h84 hD2 D.data D.czElt
    D.family D.sp D.posK D.posC D.pair
  exact ⟨h3, hXab, hXY, hYeq⟩

theorem isElemAbelian_card_liftX (D : D1SPLPairData p P M H R Rbar K z)
    (hXab : ∀ a ∈ d1LiftX p H R K, ∀ b ∈ d1LiftX p H R K, a * b = b * a) :
    IsElemAbelian p (d1LiftX p H R K) ∧ Nat.card (d1LiftX p H R K) = p ^ 2 := by
  have hp := D.data.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨T₁, hT₁, -⟩ := D.data.exists_sylow
  obtain ⟨hTcard, hTexp⟩ := sylow_facts_of_pair D.family T₁
  obtain ⟨-, hXcard⟩ := D.data.d1LiftX_facts D.czElt
  set X := d1LiftX p H R K with hXdef
  set π := QuotientGroup.mk' (primeComplementCore (G := H) p) with hπ
  have hXH : X ≤ H := d1LiftX_le_H p H R K
  have hXp : IsPGroup p X := D.data.cfg.ext.isPGroup.to_le (d1LiftX_le p H R K)
  have hTK : Nat.card ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
      Subgroup _) = p ^ 2 := by
    rw [← hT₁, Subgroup.card_map_of_injective K.subtype_injective, hTcard]
  refine ⟨⟨⟨⟨fun a b => Subtype.ext (hXab _ a.2 _ b.2)⟩⟩, fun x hx => ?_⟩, hXcard.trans hTK⟩
  have hxH := hXH hx
  have hxT : π ⟨x, hxH⟩ ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K := by
    rw [← D.data.cfg.map_d1LiftX_eq_inf]
    exact ⟨⟨x, hxH⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  rw [← hT₁] at hxT
  obtain ⟨t, ht, hte⟩ := hxT
  have h1 : π (⟨x, hxH⟩ ^ p) = 1 := by
    rw [map_pow, ← hte, ← map_pow, hTexp t ht, map_one]
  have hXp' : IsPGroup p (X.subgroupOf H) := hXp.comap_subtype
  have h1' : π (⟨x, hxH⟩ ^ p) = π 1 := by rw [h1, map_one]
  have h2 := eq_of_mk_eq_of_isPGroup hp _ (primeComplementCore_coprime (G := H) p) hXp'
    ((X.subgroupOf H).pow_mem (Subgroup.mem_subgroupOf.mpr hx) p) (X.subgroupOf H).one_mem h1'
  simpa using congrArg Subtype.val h2

theorem isCatalogGroup_component_of_phaseThree (h3 : D1PhaseThree p P M H R)
    {Λ : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} (hΛ : CFSG.IsComponent Λ) :
    IsCatalogGroup (↥Λ ⧸ Subgroup.center ↥Λ) := by
  have hMtop : M ≠ ⊤ := fun hM => h3.not_le (hM ▸ le_top)
  exact ((catalogSimpleSections_of_isKProper h3.glob.kProper M hMtop).quotient
    (CFSG.pCore 2 ↥M)).isCatalogGroup_center_quotient ((CFSG.isComponent_iff_open Λ).mp hΛ)

end Pair

end CFSG.AGLEmbedding.SPLMSide
