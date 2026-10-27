module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneStageTransport
public import CFSG.LocalAnalysis.SeitzReduction.RankOneStageNextQuot

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.LocalAnalysis

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section RelImg

variable {G : Type*} [Group G]

@[expose] def relImg (N W : Subgroup G) [(W.subgroupOf N).Normal] (K : Subgroup G) :
    Subgroup (↥N ⧸ W.subgroupOf N) :=
  (K.subgroupOf N).map (QuotientGroup.mk' (W.subgroupOf N))

@[expose] def relPre (N W : Subgroup G) [(W.subgroupOf N).Normal]
    (H : Subgroup (↥N ⧸ W.subgroupOf N)) : Subgroup G :=
  (H.comap (QuotientGroup.mk' (W.subgroupOf N))).map N.subtype

variable {N W K L : Subgroup G} [(W.subgroupOf N).Normal]

theorem relMk_eq_one_iff (x : N) : QuotientGroup.mk' (W.subgroupOf N) x = 1 ↔ (x : G) ∈ W := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf]

theorem relMk_mem_relImg (x : N) (hx : (x : G) ∈ K) :
    QuotientGroup.mk' (W.subgroupOf N) x ∈ relImg N W K :=
  mem_map_of_mem _ (mem_subgroupOf.mpr hx)

theorem exists_of_mem_relImg {y : ↥N ⧸ W.subgroupOf N} (hy : y ∈ relImg N W K) :
    ∃ x : N, (x : G) ∈ K ∧ QuotientGroup.mk' (W.subgroupOf N) x = y := by
  obtain ⟨x, hx, rfl⟩ := mem_map.mp hy
  exact ⟨x, mem_subgroupOf.mp hx, rfl⟩

theorem comap_relImg (hWK : W ≤ K) :
    (relImg N W K).comap (QuotientGroup.mk' (W.subgroupOf N)) = K.subgroupOf N := by
  rw [relImg, comap_map_eq, QuotientGroup.ker_mk']
  exact sup_eq_left.mpr fun x hx => mem_subgroupOf.mpr (hWK (mem_subgroupOf.mp hx))

theorem relMk_mem_relImg_iff (hWK : W ≤ K) (x : N) :
    QuotientGroup.mk' (W.subgroupOf N) x ∈ relImg N W K ↔ (x : G) ∈ K := by
  rw [← mem_comap, comap_relImg hWK, mem_subgroupOf]

theorem relImg_mono (hKL : K ≤ L) : relImg N W K ≤ relImg N W L :=
  map_mono fun _ hx => hKL hx

theorem relImg_sup (hK : K ≤ N) (hL : L ≤ N) :
    relImg N W (K ⊔ L) = relImg N W K ⊔ relImg N W L := by
  rw [relImg, subgroupOf_sup hK hL, Subgroup.map_sup]
  rfl

theorem relImg_eq_bot_of_le (hKW : K ≤ W) : relImg N W K = ⊥ := by
  rw [relImg, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  exact fun x hx => mem_subgroupOf.mpr (hKW (mem_subgroupOf.mp hx))

theorem relImg_inf (hWK : W ≤ K) (hWL : W ≤ L) :
    relImg N W (K ⊓ L) = relImg N W K ⊓ relImg N W L := by
  refine le_antisymm (le_inf (relImg_mono inf_le_left) (relImg_mono inf_le_right))
    fun y hy => ?_
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ y
  obtain ⟨hK, hL⟩ := mem_inf.mp hy
  exact relMk_mem_relImg x (mem_inf.mpr ⟨(relMk_mem_relImg_iff hWK x).mp hK,
    (relMk_mem_relImg_iff hWL x).mp hL⟩)

theorem relImg_self_eq_top : relImg N W N = ⊤ := by
  rw [relImg, subgroupOf_self, ← MonoidHom.range_eq_map, QuotientGroup.range_mk']

theorem card_relImg (hK : K ≤ N) : Nat.card (relImg N W K) = W.relIndex K := by
  rw [← relIndex_bot_left, relImg, ← relIndex_comap, MonoidHom.comap_bot, QuotientGroup.ker_mk',
    relIndex_subgroupOf hK]

theorem card_relImg_mul (hWK : W ≤ K) (hK : K ≤ N) :
    Nat.card (relImg N W K) * Nat.card W = Nat.card K := by
  rw [card_relImg hK, ← relIndex_mul_card W K, inf_eq_left.mpr hWK]

theorem relIndex_relImg (hWK : W ≤ K) (hL : L ≤ N) :
    (relImg N W K).relIndex (relImg N W L) = K.relIndex L := by
  rw [show relImg N W L = (L.subgroupOf N).map (QuotientGroup.mk' (W.subgroupOf N)) from rfl,
    ← relIndex_comap, comap_relImg hWK, relIndex_subgroupOf hL]

theorem subgroupOf_relPre (H : Subgroup (↥N ⧸ W.subgroupOf N)) :
    (relPre N W H).subgroupOf N = H.comap (QuotientGroup.mk' (W.subgroupOf N)) :=
  comap_map_eq_self_of_injective N.subtype_injective _

theorem relImg_relPre (H : Subgroup (↥N ⧸ W.subgroupOf N)) : relImg N W (relPre N W H) = H := by
  rw [relImg, subgroupOf_relPre, map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]

theorem relPre_le (H : Subgroup (↥N ⧸ W.subgroupOf N)) : relPre N W H ≤ N :=
  map_subtype_le _

theorem mem_relPre_iff (H : Subgroup (↥N ⧸ W.subgroupOf N)) (x : N) :
    (x : G) ∈ relPre N W H ↔ QuotientGroup.mk' (W.subgroupOf N) x ∈ H := by
  rw [← mem_subgroupOf, subgroupOf_relPre, mem_comap]

theorem le_relPre (hWN : W ≤ N) (H : Subgroup (↥N ⧸ W.subgroupOf N)) : W ≤ relPre N W H :=
  fun x hx => (mem_relPre_iff H ⟨x, hWN hx⟩).mpr
    (by rw [(relMk_eq_one_iff ⟨x, hWN hx⟩).mpr hx]; exact one_mem H)

theorem relMk_mem_normalizer_iff (hWK : W ≤ K) (hKN : K ≤ N) (x : N) :
    QuotientGroup.mk' (W.subgroupOf N) x ∈
        normalizer ((relImg N W K : Subgroup (↥N ⧸ W.subgroupOf N)) : Set (↥N ⧸ W.subgroupOf N)) ↔
      (x : G) ∈ normalizer (K : Set G) := by
  rw [← mem_comap, comap_normalizer_eq_of_surjective _ (QuotientGroup.mk'_surjective _),
    comap_relImg hWK, ← subgroupOf_normalizer_eq hKN, mem_subgroupOf]

theorem normalizer_relImg (hWK : W ≤ K) (hKN : K ≤ N) :
    normalizer ((relImg N W K : Subgroup (↥N ⧸ W.subgroupOf N)) : Set (↥N ⧸ W.subgroupOf N)) =
      relImg N W (normalizer (K : Set G)) := by
  refine le_antisymm (fun y hy => ?_) fun y hy => ?_
  · obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ y
    exact relMk_mem_relImg x ((relMk_mem_normalizer_iff hWK hKN x).mp hy)
  · obtain ⟨x, hx, rfl⟩ := exists_of_mem_relImg hy
    exact (relMk_mem_normalizer_iff hWK hKN x).mpr hx

theorem isPGroup_of_relImg {p : ℕ} (hW : IsPGroup p W) (hWK : W ≤ K) (hKN : K ≤ N)
    (h : IsPGroup p (relImg N W K)) : IsPGroup p K := by
  have h1 : IsPGroup p (K.subgroupOf N) := by
    rw [← comap_relImg hWK]
    refine h.comap_of_ker_isPGroup _ ?_
    rw [QuotientGroup.ker_mk']
    exact hW.comap_subtype
  exact h1.of_equiv (subgroupOfEquivOfLe hKN)

theorem isSylowOf_of_relImg [Finite G] {p : ℕ} [Fact p.Prime] (hW : IsPGroup p W) (hWK : W ≤ K)
    (hKN : K ≤ N) (h : ∃ S : Sylow p (↥N ⧸ W.subgroupOf N), (S : Subgroup _) = relImg N W K) :
    ABGLocalTools.IsSylowOf p K N := by
  obtain ⟨S, hS⟩ := h
  rw [ABGLocalTools.isSylowOf_iff]
  refine ⟨hKN, isPGroup_of_relImg hW hWK hKN (hS ▸ S.isPGroup'), ?_⟩
  rw [← relIndex_relImg hWK le_rfl, relImg_self_eq_top, relIndex_top_right, ← hS]
  exact S.not_dvd_index

end RelImg

section ThirdIso

variable {G : Type*} [Group G]

instance normal_subgroupOf_inf_normalizer (N U : Subgroup G) :
    (U.subgroupOf (N ⊓ normalizer (U : Set G))).Normal :=
  ⟨fun x hx g => by
    rw [mem_subgroupOf] at hx ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact (mem_normalizer_iff.mp (mem_inf.mp g.2).2 x).mp hx⟩

variable {N W U : Subgroup G} [(W.subgroupOf N).Normal]

theorem nonempty_stageQuot_equiv (hWU : W ≤ U) (hUN : U ≤ N) :
    ∃ e : StageQuot (relImg N W U) ≃*
        (↥(N ⊓ normalizer (U : Set G)) ⧸ U.subgroupOf (N ⊓ normalizer (U : Set G))),
      ∀ K : Subgroup G, (stageImg (relImg N W U) (relImg N W K)).map e.toMonoidHom =
        relImg (N ⊓ normalizer (U : Set G)) U K := by
  have hπN : ∀ x : ↥(N ⊓ normalizer (U : Set G)),
      ((QuotientGroup.mk' (W.subgroupOf N)).comp (inclusion inf_le_left)) x ∈
        normalizer ((relImg N W U : Subgroup (↥N ⧸ W.subgroupOf N)) :
          Set (↥N ⧸ W.subgroupOf N)) := fun x =>
    (relMk_mem_normalizer_iff hWU hUN _).mpr (mem_inf.mp x.2).2
  let φ₀ := ((QuotientGroup.mk' (W.subgroupOf N)).comp
    (inclusion (inf_le_left : N ⊓ normalizer (U : Set G) ≤ N))).codRestrict _ hπN
  let φ := (stageMk (relImg N W U)).comp φ₀
  have hφ0 : ∀ x : ↥(N ⊓ normalizer (U : Set G)),
      ((φ₀ x : _) : ↥N ⧸ W.subgroupOf N) = QuotientGroup.mk' (W.subgroupOf N)
        ⟨(x : G), (mem_inf.mp x.2).1⟩ := fun x => rfl
  have hlift : ∀ z : ↥(normalizer ((relImg N W U : Subgroup (↥N ⧸ W.subgroupOf N)) :
      Set (↥N ⧸ W.subgroupOf N))), ∃ x : ↥(N ⊓ normalizer (U : Set G)), φ₀ x = z := by
    intro z
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (W.subgroupOf N) (z : _)
    have hxN : (x : G) ∈ normalizer (U : Set G) :=
      (relMk_mem_normalizer_iff hWU hUN x).mp (hx ▸ z.2)
    exact ⟨⟨x, mem_inf.mpr ⟨x.2, hxN⟩⟩, Subtype.ext hx⟩
  have hφ : Function.Surjective φ := by
    intro y
    obtain ⟨z, rfl⟩ := stageMk_surjective _ y
    obtain ⟨x, hx⟩ := hlift z
    exact ⟨x, by simp only [φ, MonoidHom.comp_apply, hx]⟩
  have hker : φ.ker = U.subgroupOf (N ⊓ normalizer (U : Set G)) := by
    ext x
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    change stageMk _ (φ₀ x) = 1 ↔ _
    rw [stageMk_eq_one_iff, hφ0, relMk_mem_relImg_iff hWU]
  let e₁ : (↥(N ⊓ normalizer (U : Set G)) ⧸ U.subgroupOf (N ⊓ normalizer (U : Set G))) ≃*
      StageQuot (relImg N W U) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφ)
  have he₁ : ∀ x : ↥(N ⊓ normalizer (U : Set G)), e₁ (QuotientGroup.mk x) = φ x := fun x => rfl
  refine ⟨e₁.symm, fun K => ?_⟩
  have h1 : stageImg (relImg N W U) (relImg N W K) =
      (relImg (N ⊓ normalizer (U : Set G)) U K).map e₁.toMonoidHom := by
    ext y
    constructor
    · intro hy
      obtain ⟨z, hz, rfl⟩ := exists_of_mem_stageImg hy
      obtain ⟨x, hxK, hx⟩ := exists_of_mem_relImg hz
      have hxN : (x : G) ∈ normalizer (U : Set G) :=
        (relMk_mem_normalizer_iff hWU hUN x).mp (hx ▸ z.2)
      refine ⟨QuotientGroup.mk ⟨x, mem_inf.mpr ⟨x.2, hxN⟩⟩, relMk_mem_relImg _ hxK, ?_⟩
      change e₁ (QuotientGroup.mk _) = _
      rw [he₁]
      change stageMk _ (φ₀ _) = stageMk _ z
      congr 1
      exact Subtype.ext hx
    · rintro ⟨_, hw, rfl⟩
      obtain ⟨x, hxK, rfl⟩ := exists_of_mem_relImg hw
      change e₁ (QuotientGroup.mk x) ∈ _
      rw [he₁]
      exact stageMk_mem_stageImg _ (by rw [hφ0]; exact relMk_mem_relImg _ hxK)
  rw [h1]
  ext y
  rw [mem_map_equiv, mem_map_equiv, MulEquiv.symm_symm, MulEquiv.symm_apply_apply]

end ThirdIso

section Rel

variable {G : Type*} [Group G]

@[expose] def RelSmallRootStage (N W R X U P : Subgroup G) (n : ℕ) : Prop :=
  (W.subgroupOf N).Normal ∧ W ≤ R ∧ W ≤ X ∧ W ≤ U ∧ W ≤ P ∧ R ≤ N ∧ X ≤ N ∧ U ≤ N ∧ P ≤ N ∧
    ∀ [(W.subgroupOf N).Normal],
      SmallRootStage (relImg N W R) (relImg N W X) (relImg N W U) (relImg N W P) n

theorem relSmallRootStage_of_stageQuot [Finite G] {N W : Subgroup G} [(W.subgroupOf N).Normal]
    {U R' X' U' P' N' : Subgroup G} {n : ℕ} (hWU : W ≤ U) (hUN : U ≤ N)
    (hN' : N' = N ⊓ normalizer (U : Set G))
    (hR : U ≤ R') (hX : U ≤ X') (hU : U ≤ U') (hP : U ≤ P')
    (hR' : R' ≤ N') (hX' : X' ≤ N') (hU' : U' ≤ N') (hP' : P' ≤ N')
    (h : SmallRootStage (stageImg (relImg N W U) (relImg N W R'))
      (stageImg (relImg N W U) (relImg N W X')) (stageImg (relImg N W U) (relImg N W U'))
      (stageImg (relImg N W U) (relImg N W P')) n) :
    RelSmallRootStage N' U R' X' U' P' n := by
  subst hN'
  refine ⟨inferInstance, hR, hX, hU, hP, hR', hX', hU', hP', ?_⟩
  intro _
  obtain ⟨e, he⟩ := nonempty_stageQuot_equiv hWU hUN
  have h1 := h.map_mulEquiv e
  rw [he, he, he, he] at h1
  exact h1

end Rel

end CFSG.SeitzReduction.RankOne
