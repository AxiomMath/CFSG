module

public import CFSG.CGT.Foote82.ChiefBridge
public import CFSG.CGT.Foote82.Thm66
import CFSG.CGT.Foote82.ClimbIrr
import CFSG.Quasithin.Background.G11Basic
import CFSG.CGT.Foote82.SetupLayer
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOMinusFacts
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockInputs

public section

namespace CFSG.CGT.Foote82

open CFSG.Open CFSG.Quasithin.G11 CFSG.QuasithinUnique CFSG.AGLEmbedding CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec19.SimsTheoremC
open scoped commutatorElement
open Matrix

variable {G : Type} [Group G] [Finite G]

theorem le_pCoreOf_of_normalizes {D R : Subgroup G} (hRD : R ≤ D)
    (hDR : D ≤ Subgroup.normalizer (R : Set G)) (hR : IsPGroup 2 R) : R ≤ pCoreOf 2 D := by
  haveI : (R.subgroupOf D).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hRD).mpr hDR
  have hS : IsPGroup 2 (R.subgroupOf D) := hR.of_equiv (Subgroup.subgroupOfEquivOfLe hRD).symm
  intro x hx
  exact ⟨⟨x, hRD hx⟩, le_pCore_of_normal (R.subgroupOf D) hS (Subgroup.mem_subgroupOf.mpr hx), rfl⟩

theorem map_conj_eq_self_of_mem_normalizer {C : Subgroup G} {g : G}
    (hC : g ∈ Subgroup.normalizer (C : Set G)) : C.map (MulAut.conj g).toMonoidHom = C := by
  ext x
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hC y).mp hy
  · intro hx
    refine ⟨g⁻¹ * x * g, ?_, by group⟩
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hC) x).mp hx
    simpa using this

theorem mem_normalizer_of_map_conj_eq {C : Subgroup G} {g : G}
    (h : C.map (MulAut.conj g).toMonoidHom = C) : g ∈ Subgroup.normalizer (C : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← h]
    exact ⟨x, hx, rfl⟩
  · intro hx
    rw [← h] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_left_inj, mul_right_inj] at hyx
    rwa [← hyx]

theorem mem_normalizer_pCoreOf {D : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (D : Set G)) :
    g ∈ Subgroup.normalizer (pCoreOf 2 D : Set G) := by
  have key : ∀ c ∈ Subgroup.normalizer (D : Set G),
      (pCoreOf 2 D).map (MulAut.conj c).toMonoidHom ≤ pCoreOf 2 D := by
    intro c hc
    refine le_pCoreOf_of_normalizes ?_ (fun d hd => ?_)
      ((CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 D).map _)
    · have := Subgroup.map_mono (f := (MulAut.conj c).toMonoidHom)
        (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 D)
      rwa [map_conj_eq_self_of_mem_normalizer hc] at this
    · apply mem_normalizer_of_map_conj_eq
      have hd' : c⁻¹ * d * c ∈ D := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hc) d).mp hd
        simpa using this
      have hN := CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 D hd'
      rw [Subgroup.map_map]
      have e : (MulAut.conj d).toMonoidHom.comp (MulAut.conj c).toMonoidHom =
          (MulAut.conj c).toMonoidHom.comp (MulAut.conj (c⁻¹ * d * c)).toMonoidHom := by
        ext x
        simp [MulAut.conj_apply, mul_assoc]
      rw [e, ← Subgroup.map_map, map_conj_eq_self_of_mem_normalizer hN]
  apply mem_normalizer_of_map_conj_eq
  refine le_antisymm (key g hg) fun x hx => ?_
  have := key g⁻¹ (Subgroup.inv_mem _ hg) ⟨x, hx, rfl⟩
  exact ⟨g⁻¹ * x * g⁻¹⁻¹, this, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem mem_normalizer_commutator {A B : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((⁅A, B⁆ : Subgroup G) : Set G) := by
  apply mem_normalizer_of_map_conj_eq
  rw [Subgroup.map_commutator, map_conj_eq_self_of_mem_normalizer hA,
    map_conj_eq_self_of_mem_normalizer hB]

namespace ChiefHyp

variable {N K Q : Subgroup G} (h : ChiefHyp N K Q)
include h

theorem mem_normalizer_kClosure {y : G} (hyX : y ∈ Subgroup.normalizer (footeX N K : Set G))
    (hyK : y ∈ Subgroup.normalizer (K : Set G)) :
    y ∈ Subgroup.normalizer (kClosure N K : Set G) := by
  have key : ∀ c, c ∈ Subgroup.normalizer (footeX N K : Set G) →
      c ∈ Subgroup.normalizer (K : Set G) → ∀ g ∈ kClosure N K, c * g * c⁻¹ ∈ kClosure N K := by
    intro c hcX hcK g hg
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      obtain ⟨x, hx, k, hk, rfl⟩ := hg
      refine Subgroup.subset_closure ⟨c * x * c⁻¹, (Subgroup.mem_normalizer_iff.mp hcX x).mp hx,
        c * k * c⁻¹, (Subgroup.mem_normalizer_iff.mp hcK k).mp hk, by group⟩
    | one => simp
    | mul a b _ _ ha hb =>
      have : c * (a * b) * c⁻¹ = (c * a * c⁻¹) * (c * b * c⁻¹) := by group
      rw [this]
      exact Subgroup.mul_mem _ ha hb
    | inv a _ ha =>
      have : c * a⁻¹ * c⁻¹ = (c * a * c⁻¹)⁻¹ := by group
      rw [this]
      exact Subgroup.inv_mem _ ha
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨key y hyX hyK g, fun hg => ?_⟩
  have := key y⁻¹ (Subgroup.inv_mem _ hyX) (Subgroup.inv_mem _ hyK) _ hg
  simpa [mul_assoc] using this

theorem Q_le_normalizer_kClosure : Q ≤ Subgroup.normalizer (kClosure N K : Set G) :=
  fun _ hq => h.mem_normalizer_kClosure (h.Q_le_normalizer_footeX hq) (h.normalizes hq)

theorem gam_le_normalizer_kClosure :
    footeX N K ⊔ Q ≤ Subgroup.normalizer (kClosure N K : Set G) :=
  sup_le h.footeX_le_normalizer_kClosure h.Q_le_normalizer_kClosure

theorem kClosure_le_gam : kClosure N K ≤ footeX N K ⊔ Q :=
  h.kClosure_le_footeX.trans le_sup_left

theorem kClosure_le : kClosure N K ≤ N := h.kClosure_le_footeX.trans (footeX_le N K)

theorem commutator_kClosure : ⁅kClosure N K, kClosure N K⁆ = kClosure N K := by
  refine le_antisymm ((Subgroup.commutator_le).mpr fun a ha b hb => ?_) ?_
  · rw [commutatorElement_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb)
      (Subgroup.inv_mem _ ha)) (Subgroup.inv_mem _ hb)
  · refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨x, hx, k, hk, rfl⟩
    have hKx : K.map (MulAut.conj x).toMonoidHom ≤ kClosure N K := by
      rintro _ ⟨k', hk', rfl⟩
      exact Subgroup.subset_closure ⟨x, hx, k', hk', rfl⟩
    have hk' : k ∈ ⁅K, K⁆ := by rw [IsFooteBlock.commutator_eq h.block]; exact hk
    have hmem : x * k * x⁻¹ ∈ ⁅K, K⁆.map (MulAut.conj x).toMonoidHom := ⟨k, hk', rfl⟩
    rw [Subgroup.map_commutator] at hmem
    exact Subgroup.commutator_mono hKx hKx hmem

theorem kClosure_eq_closure :
    kClosure N K = Subgroup.closure {g | ∃ ℓ ∈ kClosure N K, ∃ k ∈ K, g = ℓ * k * ℓ⁻¹} := by
  refine le_antisymm ((Subgroup.closure_le _).mpr ?_) ((Subgroup.closure_le _).mpr ?_)
  · rintro _ ⟨x, hx, k, hk, rfl⟩
    have hXH : kClosure N K ≤ Subgroup.normalizer (pCoreOf 2 N : Set G) :=
      h.kClosure_le.trans h.le_normalizer_core
    have hx' : x ∈ ((kClosure N K ⊔ pCoreOf 2 N : Subgroup G) : Set G) := by
      rw [← h.footeX_eq_sup]; exact hx
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hXH] at hx'
    obtain ⟨d, hd, c, hc, rfl⟩ := hx'
    have hck : c * k * c⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.mp (h.normalizes (h.core_le hc)) k).mp hk
    exact Subgroup.subset_closure ⟨d, hd, c * k * c⁻¹, hck, by group⟩
  · rintro _ ⟨ℓ, hℓ, k, hk, rfl⟩
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hℓ (h.K_le_kClosure hk)) (Subgroup.inv_mem _ hℓ)

theorem isSubnormal_kClosure : IsSubnormal (kClosure N K) N :=
  .step h.kClosure_le_footeX
    ((Subgroup.normal_subgroupOf_iff_le_normalizer h.kClosure_le_footeX).mpr
      h.footeX_le_normalizer_kClosure) h.isSubnormal_footeX

theorem pCoreOf_kClosure : pCoreOf 2 (kClosure N K) = kClosure N K ⊓ pCoreOf 2 N := by
  apply le_antisymm
  · refine le_inf (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 _) ?_
    refine h.le_core_of_isPGroup (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 _)
      ((CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 _).trans h.kClosure_le_footeX)
      fun x hx => mem_normalizer_pCoreOf (h.footeX_le_normalizer_kClosure hx)
  · refine le_pCoreOf_of_normalizes inf_le_left (fun d hd => ?_)
      (h.core_isPGroup.to_le inf_le_right)
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have h1 := Subgroup.mem_normalizer_iff.mp
      (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 N
        (h.kClosure_le hd)) x
    have h2 := Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hd) x
    exact ⟨fun hx => ⟨h2.mp hx.1, h1.mp hx.2⟩, fun hx => ⟨h2.mpr hx.1, h1.mpr hx.2⟩⟩

theorem blockU_le_pCoreOf_kClosure : blockU K ≤ pCoreOf 2 (kClosure N K) := by
  rw [h.pCoreOf_kClosure]
  exact le_inf ((blockU_le_self K).trans h.K_le_kClosure) h.blockU_le

theorem blockU_le_blockU_kClosure : blockU K ≤ blockU (kClosure N K) := by
  rw [← IsFooteBlock.commutator_blockU h.block]
  exact Subgroup.commutator_mono h.blockU_le_pCoreOf_kClosure h.K_le_kClosure

theorem blockU_kClosure_le_wOne : blockU (kClosure N K) ≤ wOne N K Q := by
  refine (Subgroup.commutator_le).mpr fun x hx d hd => ?_
  have hx' : x ∈ pCoreOf 2 (kClosure N K) := hx
  rw [h.pCoreOf_kClosure] at hx'
  have hxH : x ∈ pCoreOf 2 N := hx'.2
  have := h.kClosure_comm_mem_wOne (Q := Q) hd hxH
  have e : ⁅x, d⁆ = (d * x * d⁻¹ * x⁻¹)⁻¹ := by rw [commutatorElement_def]; group
  rw [e]
  exact Subgroup.inv_mem _ this

theorem gam_le_normalizer_blockU_kClosure :
    footeX N K ⊔ Q ≤ Subgroup.normalizer (blockU (kClosure N K) : Set G) := fun _ hγ =>
  mem_normalizer_commutator (mem_normalizer_pCoreOf (h.gam_le_normalizer_kClosure hγ))
    (h.gam_le_normalizer_kClosure hγ)

theorem commutator_pCoreOf_kClosure_K : ⁅pCoreOf 2 (kClosure N K), K⁆ = blockU K := by
  refine le_antisymm ?_ ?_
  · have h1 : pCoreOf 2 (kClosure N K) ≤ pCoreOf 2 N := h.pCoreOf_kClosure ▸ inf_le_right
    rw [Subgroup.commutator_comm]
    exact (Subgroup.commutator_mono le_rfl h1).trans h.commutator_core_le
  · conv_lhs => rw [← IsFooteBlock.commutator_blockU h.block]
    exact Subgroup.commutator_mono h.blockU_le_pCoreOf_kClosure le_rfl

end ChiefHyp

namespace ChiefHyp

variable {N K Q : Subgroup G} (h : ChiefHyp N K Q)
include h

theorem isComponentOf_barIn_kClosure :
    IsComponentOf (barIn (kClosure N K) K) (centralizerBarIn (kClosure N K) Q) := by
  have hKD := h.K_le_kClosure
  have hPQ : pCoreOf 2 (kClosure N K) ≤ Q := by
    rw [h.pCoreOf_kClosure]
    exact inf_le_right.trans h.core_le
  set C' : Subgroup G := Subgroup.closure {x : G | x ∈ kClosure N K ∧
    ∀ t ∈ Q, t * x * t⁻¹ * x⁻¹ ∈ pCoreOf 2 (kClosure N K)} with hC'
  have hKC' : K ≤ C' := fun k hk => Subgroup.subset_closure ⟨hKD hk, fun t ht => by
    have hc : ⁅t, k⁆ ∈ ⁅K, Q⁆ := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator ht hk
    rw [← commutatorElement_def]
    exact h.blockU_le_pCoreOf_kClosure (h.commutator_Q_le hc)⟩
  have hC'N : C' ≤ N ⊓ Subgroup.normalizer (Q : Set G) := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨hxD, hx⟩
    refine ⟨h.kClosure_le hxD, ?_⟩
    have hle : Q.map (MulAut.conj x).toMonoidHom ≤ Q := by
      rintro _ ⟨t, ht, rfl⟩
      have h1 := hPQ (hx t⁻¹ (Subgroup.inv_mem _ ht))
      have e : (MulAut.conj x).toMonoidHom t = t * (t⁻¹ * x * t⁻¹⁻¹ * x⁻¹) := by
        simp [MulAut.conj_apply, mul_assoc]
      rw [e]
      exact Subgroup.mul_mem _ ht h1
    refine mem_normalizer_of_map_conj_eq (Subgroup.eq_of_le_of_card_ge hle ?_)
    rw [Subgroup.card_map_of_injective (MulAut.conj x).injective]
  have hsub : IsSubnormal K C' := by
    have := CFSG.Open.IsSubnormal.inf_of_le h.subnormal hC'N
    rwa [inf_eq_left.mpr hKC'] at this
  refine ⟨Subgroup.map_mono fun y hy => hKC' hy, ?_, ?_⟩
  · exact CFSG.Open.IsSubnormal.map _
      (CFSG.Open.IsSubnormal.comap (kClosure N K).subtype hsub)
  · exact isQuasisimple_open_of_native (isQuasisimple_of_block h.block (hatMap hKD)
      (hatMap_surjective hKD) (ker_hatMap_le hKD) fun k hk =>
        (mem_ker_hatMap hKD k).mpr (h.blockU_le_pCoreOf_kClosure hk))

theorem footeArrow_kClosure : FooteArrow K (kClosure N K) :=
  ⟨h.K_le_kClosure, h.commutator_pCoreOf_kClosure_K.symm, Q, h.two, h.Q_le_normalizer_kClosure,
    h.isComponentOf_barIn_kClosure⟩

end ChiefHyp

namespace ChiefLin

variable {Γ W₀ W₁ : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
  (lin : ChiefLin Γ W₀ W₁ V)

@[expose] def imgVec (B : Subgroup G) : Submodule (ZMod 2) V where
  carrier := {v | ∃ w : ↥W₁, (w : G) ∈ B ∧ lin.vec w = v}
  add_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a * b, B.mul_mem ha hb, lin.vec_mul a b⟩
  zero_mem' := ⟨1, B.one_mem, lin.vec_one⟩
  smul_mem' := by
    rintro c _ ⟨a, ha, rfl⟩
    rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
    · exact ⟨1, B.one_mem, by rw [lin.vec_one, zero_smul]⟩
    · exact ⟨a, ha, by rw [one_smul]⟩

theorem invariant_imgVec {A B : Subgroup G} (hAB : A ≤ Subgroup.normalizer (B : Set G)) :
    Invariant (lin.img A) (lin.imgVec B) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨w, hw, rfl⟩
  have haA : (a : G) ∈ A := Subgroup.mem_subgroupOf.mp ha
  have hconj : (a : G) * w * (a : G)⁻¹ ∈ W₁ :=
    (Subgroup.mem_normalizer_iff.mp (lin.normalizes a.2) w).mp w.2
  exact ⟨⟨_, hconj⟩, (Subgroup.mem_normalizer_iff.mp (hAB haA) w).mp hw,
    (lin.ρ_vec a w ⟨_, hconj⟩ rfl).symm⟩

theorem kProper_img (hK : CFSG.Assembly.KProper CFSG.Assembly.InCatalog G) (A : Subgroup G) :
    CFSG.Assembly.KProper CFSG.Assembly.InCatalog ↥(lin.img A) :=
  CFSG.ComponentClassification.CatalogueKProper.of_surjective
    (CFSG.ComponentClassification.CatalogueKProper.subgroup
      (CFSG.ComponentClassification.CatalogueKProper.subgroup hK Γ) (A.subgroupOf Γ))
    (lin.ρ.subgroupMap (A.subgroupOf Γ)) (lin.ρ.subgroupMap_surjective (A.subgroupOf Γ))

theorem img_le_img_self (A : Subgroup G) : lin.img A ≤ lin.img Γ := by
  refine Subgroup.map_mono ?_
  rw [Subgroup.subgroupOf_self]
  exact le_top

end ChiefLin

theorem isPerfect_of_commutator_eq {D : Subgroup G} (hD : ⁅D, D⁆ = D) : Group.IsPerfect ↥D := by
  refine ⟨Subgroup.map_injective D.subtype_injective ?_⟩
  rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype, hD]

theorem isQuasisimple_of_isSimpleGroup_of_commutator_eq_top {S : Type*} [Group S]
    (hS : IsSimpleGroup S) (hp : commutator S = ⊤) : CFSG.Open.IsQuasisimple S := by
  haveI := hS
  refine ⟨hp, ?_⟩
  have hc : Subgroup.center S = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with hb | ht
    · exact hb
    · exfalso
      have hle : commutator S ≤ ⊥ := by
        rw [commutator_def, Subgroup.commutator_le]
        intro a _ b _
        have hab : a * b = b * a := Subgroup.mem_center_iff.mp (ht ▸ Subgroup.mem_top b) a
        rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
        exact hab
      rw [hp, le_bot_iff] at hle
      exact top_ne_bot hle
  exact ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot).isSimpleGroup

section Climb

variable {N K Q : Subgroup G} (h : ChiefHyp N K Q) {W₀ : Subgroup G}
  (hW₀ : Maximal (fun W : Subgroup G => W ≤ wOne N K Q ∧
    footeX N K ⊔ Q ≤ Subgroup.normalizer (W : Set G) ∧ ¬ blockU K ≤ W) W₀)
  {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  (lin : ChiefLin (footeX N K ⊔ Q) W₀ (wOne N K Q) V)
include h hW₀

omit hW₀ in
theorem ChiefHyp.img_kClosure_normal : ∀ γ ∈ lin.img (footeX N K ⊔ Q),
    ∀ b ∈ lin.img (kClosure N K), γ * b * γ⁻¹ ∈ lin.img (kClosure N K) := by
  rintro _ ⟨x, -, rfl⟩ _ ⟨d, hd, rfl⟩
  have hd' : (d : G) ∈ kClosure N K := Subgroup.mem_subgroupOf.mp hd
  refine ⟨x * d * x⁻¹, Subgroup.mem_subgroupOf.mpr ?_, by simp [map_mul, map_inv]⟩
  exact (Subgroup.mem_normalizer_iff.mp (h.gam_le_normalizer_kClosure x.2) d).mp hd'

omit hW₀ in
theorem ChiefHyp.img_K_le_img_kClosure : lin.img K ≤ lin.img (kClosure N K) := by
  rintro _ ⟨k, hk, rfl⟩
  exact ⟨k, Subgroup.mem_subgroupOf.mpr (h.K_le_kClosure (Subgroup.mem_subgroupOf.mp hk)), rfl⟩

omit hW₀ in
theorem ChiefHyp.img_kClosure_le_normalClosure :
    lin.img (kClosure N K) ≤ normalClosure (lin.img (kClosure N K)) (lin.img K) := by
  rintro _ ⟨d, hd, rfl⟩
  have hd' : (d : G) ∈ kClosure N K := Subgroup.mem_subgroupOf.mp hd
  suffices hP : kClosure N K ≤ ((normalClosure (lin.img (kClosure N K))
      (lin.img K)).comap lin.ρ).map (footeX N K ⊔ Q).subtype by
    obtain ⟨y, hy, hyd⟩ := hP hd'
    rw [← Subtype.ext hyd]
    exact hy
  refine h.kClosure_eq_closure.le.trans ((Subgroup.closure_le _).mpr ?_)
  rintro _ ⟨ℓ, hℓ, k, hk, rfl⟩
  have hℓΓ : ℓ ∈ footeX N K ⊔ Q := h.kClosure_le_gam hℓ
  have hkΓ : k ∈ footeX N K ⊔ Q := h.K_le_gam hk
  refine ⟨⟨ℓ, hℓΓ⟩ * ⟨k, hkΓ⟩ * ⟨ℓ, hℓΓ⟩⁻¹, ?_, rfl⟩
  show lin.ρ (⟨ℓ, hℓΓ⟩ * ⟨k, hkΓ⟩ * ⟨ℓ, hℓΓ⟩⁻¹) ∈ normalClosure _ _
  rw [map_mul, map_mul, map_inv]
  exact Subgroup.subset_closure ⟨lin.ρ ⟨ℓ, hℓΓ⟩, ⟨⟨ℓ, hℓΓ⟩, Subgroup.mem_subgroupOf.mpr hℓ, rfl⟩,
    lin.ρ ⟨k, hkΓ⟩, ⟨⟨k, hkΓ⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩, rfl⟩

theorem ChiefHyp.eq_bot_or_eq_top_img_kClosure {U : Submodule (ZMod 2) V}
    (hU : Invariant (lin.img (kClosure N K)) U) : U = ⊥ ∨ U = ⊤ := by
  have hS := h.setup6Irr_img hW₀ lin
  exact eq_bot_or_eq_top_of_le_normalClosure hS.irr (h.img_kClosure_normal lin)
    (h.img_K_le_img_kClosure lin) (h.img_kClosure_le_normalClosure lin)
    (commutator_eq_of_isPerfect ⟨hS.component.2.2.1⟩) hS.irrTilde hU

theorem ChiefHyp.fixedSpace_img_kClosure : fixedSpace (lin.img (kClosure N K)) = ⊥ := by
  have hS := h.setup6Irr_img hW₀ lin
  exact fixedSpace_eq_bot_of_le_normalClosure hS.irr (h.img_kClosure_normal lin)
    (h.img_K_le_img_kClosure lin) (h.img_kClosure_le_normalClosure lin)
    (commutator_eq_of_isPerfect ⟨hS.component.2.2.1⟩) hS.irrTilde

theorem ChiefHyp.imgVec_blockU_kClosure : lin.imgVec (blockU (kClosure N K)) = ⊤ := by
  have hinv : Invariant (lin.img (footeX N K ⊔ Q)) (lin.imgVec (blockU (kClosure N K))) :=
    lin.invariant_imgVec h.gam_le_normalizer_blockU_kClosure
  rcases IsIrr.eq_bot_or_eq (h.setup6Irr_img hW₀ lin).irr hinv le_top with hb | ht
  · exfalso
    obtain ⟨u, hu, hu0⟩ := SetLike.not_le_iff_exists.mp hW₀.1.2.2
    have huW : u ∈ wOne N K Q := h.blockU_le_wOne hu
    have hmem : lin.vec ⟨u, huW⟩ ∈ lin.imgVec (blockU (kClosure N K)) :=
      ⟨⟨u, huW⟩, h.blockU_le_blockU_kClosure hu, rfl⟩
    rw [hb, Submodule.mem_bot, lin.vec_eq_zero_iff] at hmem
    exact hu0 hmem
  · exact ht

include lin in
theorem ChiefHyp.blockU_inf_wZero_kClosure :
    blockU (kClosure N K) ⊓ W₀ = blockZ (kClosure N K) := by
  apply le_antisymm
  · rintro u ⟨hu, hu0⟩
    refine ⟨hu, Subgroup.mem_centralizer_iff.mpr fun d hd => ?_⟩
    exact (Subgroup.mem_centralizer_iff.mp (h.kClosure_le_centralizer_wZero hW₀ hd) u hu0).symm
  · rintro u ⟨hu, hc⟩
    refine ⟨hu, ?_⟩
    have huW : u ∈ wOne N K Q := h.blockU_kClosure_le_wOne hu
    have hfix : lin.vec ⟨u, huW⟩ ∈ fixedSpace (lin.img (kClosure N K)) := by
      rintro _ ⟨d, hd, rfl⟩
      have hd' : (d : G) ∈ kClosure N K := Subgroup.mem_subgroupOf.mp hd
      have hdu : ((⟨u, huW⟩ : ↥(wOne N K Q)) : G) = d * u * (d : G)⁻¹ := by
        rw [show (d : G) * u = u * d from Subgroup.mem_centralizer_iff.mp hc d hd',
          mul_inv_cancel_right]
      exact lin.ρ_vec d ⟨u, huW⟩ ⟨u, huW⟩ hdu
    rw [h.fixedSpace_img_kClosure hW₀ lin, Submodule.mem_bot, lin.vec_eq_zero_iff] at hfix
    exact hfix

include lin in
theorem ChiefHyp.chief_kClosure : blockZ (kClosure N K) < blockU (kClosure N K) ∧
    ∀ W : Subgroup G, blockZ (kClosure N K) ≤ W → W ≤ blockU (kClosure N K) →
      kClosure N K ≤ Subgroup.normalizer (W : Set G) →
        W = blockZ (kClosure N K) ∨ W = blockU (kClosure N K) := by
  have hZ := h.blockU_inf_wZero_kClosure hW₀ lin
  have hUW := h.blockU_kClosure_le_wOne
  haveI := lin.nontrivial (h.isChiefFactor hW₀).lt
  refine ⟨lt_of_le_of_ne inf_le_left fun heq => ?_, fun W hZW hWU hDW => ?_⟩
  · obtain ⟨v, hv⟩ := exists_ne (0 : V)
    have hv' : v ∈ lin.imgVec (blockU (kClosure N K)) := by
      rw [h.imgVec_blockU_kClosure hW₀ lin]; exact Submodule.mem_top
    obtain ⟨w, hw, rfl⟩ := hv'
    apply hv
    rw [lin.vec_eq_zero_iff]
    have hwZ : (w : G) ∈ blockZ (kClosure N K) := by rw [heq]; exact hw
    rw [← hZ] at hwZ
    exact hwZ.2
  · have hinv : Invariant (lin.img (kClosure N K)) (lin.imgVec W) := lin.invariant_imgVec hDW
    rcases h.eq_bot_or_eq_top_img_kClosure hW₀ lin hinv with hb | ht
    · left
      refine le_antisymm (fun w hw => ?_) hZW
      rw [← hZ]
      refine ⟨hWU hw, ?_⟩
      have hwW : w ∈ wOne N K Q := hUW (hWU hw)
      have hmem : lin.vec ⟨w, hwW⟩ ∈ lin.imgVec W := ⟨⟨w, hwW⟩, hw, rfl⟩
      rw [hb, Submodule.mem_bot, lin.vec_eq_zero_iff] at hmem
      exact hmem
    · right
      refine le_antisymm hWU fun u hu => ?_
      have huW : u ∈ wOne N K Q := hUW hu
      have hmem : lin.vec ⟨u, huW⟩ ∈ lin.imgVec W := by rw [ht]; exact Submodule.mem_top
      obtain ⟨w, hw, hwu⟩ := hmem
      have h1 : u * (w : G)⁻¹ ∈ W₀ := (lin.vec_eq_vec_iff ⟨u, huW⟩ w).mp hwu.symm
      have h2 : u * (w : G)⁻¹ ∈ blockU (kClosure N K) :=
        Subgroup.mul_mem _ hu (Subgroup.inv_mem _ (hWU hw))
      have h3 : u * (w : G)⁻¹ ∈ W := hZW (by rw [← hZ]; exact ⟨h2, h1⟩)
      have e : u = (u * (w : G)⁻¹) * w := by group
      rw [e]
      exact Subgroup.mul_mem _ h3 hw

theorem ChiefHyp.ker_restr_kClosure :
    (lin.restr h.kClosure_le_gam).ker = CFSG.pCore 2 ↥(kClosure N K) := by
  ext d
  rw [MonoidHom.mem_ker, mem_pCore_iff, h.pCoreOf_kClosure]
  have hdX : ((Subgroup.inclusion h.kClosure_le_gam d : ↥(footeX N K ⊔ Q)) : G) ∈ footeX N K :=
    h.kClosure_le_footeX d.2
  constructor
  · intro hd
    have h1 : lin.ρ (Subgroup.inclusion h.kClosure_le_gam d) = 1 := by
      have := congrArg Subtype.val hd
      rwa [lin.restr_apply] at this
    exact ⟨d.2, (h.ρ_eq_one_iff hW₀ lin _ hdX).mp h1⟩
  · rintro ⟨-, hdH⟩
    apply Subtype.ext
    rw [lin.restr_apply]
    exact (h.ρ_eq_one_iff hW₀ lin _ hdX).mpr hdH

theorem ChiefHyp.kClosure_eq_of_img_eq (h1 : lin.img K = lin.img (footeX N K ⊔ Q)) :
    kClosure N K = K := by
  refine le_antisymm ((Subgroup.closure_le _).mpr ?_) h.K_le_kClosure
  rintro _ ⟨x, hx, k, hk, rfl⟩
  have hxΓ : x ∈ footeX N K ⊔ Q := Subgroup.mem_sup_left hx
  have hmem : lin.ρ ⟨x, hxΓ⟩ ∈ lin.img K := by
    rw [h1]
    exact ⟨⟨x, hxΓ⟩, by rw [Subgroup.subgroupOf_self]; exact Subgroup.mem_top _, rfl⟩
  obtain ⟨k₀, hk₀, hρ⟩ := hmem
  have hk₀K : (k₀ : G) ∈ K := Subgroup.mem_subgroupOf.mp hk₀
  have hcX : (k₀ : G)⁻¹ * x ∈ footeX N K :=
    (footeX N K).mul_mem ((footeX N K).inv_mem (h.K_le_footeX hk₀K)) hx
  have hcρ : lin.ρ (k₀⁻¹ * ⟨x, hxΓ⟩) = 1 := by rw [map_mul, map_inv, hρ, inv_mul_cancel]
  have hcH : (k₀ : G)⁻¹ * x ∈ pCoreOf 2 N :=
    (h.ρ_eq_one_iff hW₀ lin (k₀⁻¹ * ⟨x, hxΓ⟩) hcX).mp hcρ
  have hck : ((k₀ : G)⁻¹ * x) * k * ((k₀ : G)⁻¹ * x)⁻¹ ∈ K :=
    (Subgroup.mem_normalizer_iff.mp (h.normalizes (h.core_le hcH)) k).mp hk
  have e : x * k * x⁻¹ =
      (k₀ : G) * (((k₀ : G)⁻¹ * x) * k * ((k₀ : G)⁻¹ * x)⁻¹) * (k₀ : G)⁻¹ := by group
  rw [e]
  exact K.mul_mem (K.mul_mem hk₀K hck) (K.inv_mem hk₀K)

theorem ChiefHyp.img_kClosure_le_layerIn :
    lin.img (kClosure N K) ≤ layerIn (lin.img (footeX N K ⊔ Q)) := by
  have hKE := (h.setup6Irr_img hW₀ lin).toSetup6.le_layerIn
  have : (CFSG.layer ↥(lin.img (footeX N K ⊔ Q))).Characteristic :=
    CFSG.LocalCores.layer_characteristic
  refine (h.img_kClosure_le_normalClosure lin).trans ((Subgroup.closure_le _).mpr ?_)
  rintro _ ⟨γ, hγ, l, hl, rfl⟩
  have hγΓ : γ ∈ lin.img (footeX N K ⊔ Q) := lin.img_le_img_self _ hγ
  obtain ⟨l₀, hl₀, rfl⟩ := hKE hl
  exact ⟨⟨γ, hγΓ⟩ * l₀ * ⟨γ, hγΓ⟩⁻¹, Subgroup.Normal.conj_mem inferInstance l₀ hl₀ ⟨γ, hγΓ⟩,
    by simp⟩

theorem ChiefHyp.img_kClosure_eq_layerIn
    (hE : IsSimpleGroup ↥(layerIn (lin.img (footeX N K ⊔ Q)))) :
    lin.img (kClosure N K) = layerIn (lin.img (footeX N K ⊔ Q)) := by
  set E := layerIn (lin.img (footeX N K ⊔ Q)) with hEdef
  have hDE := h.img_kClosure_le_layerIn hW₀ lin
  have hEΓ : E ≤ lin.img (footeX N K ⊔ Q) := Subgroup.map_subtype_le _
  have hn : ((lin.img (kClosure N K)).subgroupOf E).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact h.img_kClosure_normal lin g (hEΓ g.2) x hx
  haveI := hE
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((lin.img (kClosure N K)).subgroupOf E) with
    hb | ht
  · exfalso
    have hD : lin.img (kClosure N K) = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have hx' : (⟨x, hDE hx⟩ : ↥E) ∈ (lin.img (kClosure N K)).subgroupOf E := hx
      rw [hb, Subgroup.mem_bot] at hx'
      exact (Subgroup.mem_bot).mpr (congrArg Subtype.val hx')
    have hK : lin.img K = ⊥ := le_bot_iff.mp (hD ▸ h.img_K_le_img_kClosure lin)
    have hirr := (h.setup6Irr_img hW₀ lin).irrTilde.1
    have hc : commSpace (lin.img K) ⊤ = ⊥ := by
      rw [commSpace_eq_bot_iff]
      intro k hk u _
      rw [hK, Subgroup.mem_bot] at hk
      rw [hk]
      rfl
    rw [hc] at hirr
    exact not_lt_bot hirr
  · refine le_antisymm hDE fun x hx => ?_
    have hx' : (⟨x, hx⟩ : ↥E) ∈ (lin.img (kClosure N K)).subgroupOf E := by
      rw [ht]; exact Subgroup.mem_top _
    exact hx'

theorem ChiefHyp.isFooteBlock_kClosure
    (hE : IsSimpleGroup ↥(layerIn (lin.img (footeX N K ⊔ Q)))) :
    IsFooteBlock N (kClosure N K) := by
  have himg := h.img_kClosure_eq_layerIn hW₀ lin hE
  let e : (↥(kClosure N K) ⧸ CFSG.pCore 2 ↥(kClosure N K)) ≃*
      ↥(layerIn (lin.img (footeX N K ⊔ Q))) :=
    ((QuotientGroup.quotientMulEquivOfEq (h.ker_restr_kClosure hW₀ lin).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective _ (lin.restr_surjective h.kClosure_le_gam))).trans
      (MulEquiv.subgroupCongr himg)
  haveI hp : Group.IsPerfect ↥(kClosure N K) := isPerfect_of_commutator_eq h.commutator_kClosure
  refine ⟨h.kClosure_le, h.isSubnormal_kClosure, fun M _ h2 => ?_, ?_, h.chief_kClosure hW₀ lin⟩
  · haveI : Group.IsPerfect (↥(kClosure N K) ⧸ M) :=
      Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective M)
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    by_contra hne
    haveI : Nontrivial (↥(kClosure N K) ⧸ M) := QuotientGroup.nontrivial_iff.mpr hne
    exact (Group.IsPerfect.not_isNilpotent (G := ↥(kClosure N K) ⧸ M)) h2.isNilpotent
  · haveI := hE
    exact isQuasisimple_of_isSimpleGroup_of_commutator_eq_top e.isSimpleGroup
      (Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)).commutator_eq_top

theorem ChiefHyp.exists_typeWitness_kClosure
    (himg : lin.img (kClosure N K) = layerIn (lin.img (footeX N K ⊔ Q)))
    {T M : Type} [Group T] [AddGroup M] (φ : ↥(layerIn (lin.img (footeX N K ⊔ Q))) ≃* T)
    (ψ : V ≃+ M) (R : T → Multiplicative M → Multiplicative M → Prop)
    (hR : ∀ (e : ↥(layerIn (lin.img (footeX N K ⊔ Q)))) (v : V),
      R (φ e) (Multiplicative.ofAdd (ψ v)) (Multiplicative.ofAdd (ψ ((e : GLV V) v)))) :
    ∃ α : ↥(kClosure N K) →* T, Function.Surjective α ∧ α.ker = CFSG.pCore 2 ↥(kClosure N K) ∧
      ∃ β : ↥(blockU (kClosure N K)) →* Multiplicative M, Function.Surjective β ∧
        β.ker = (blockZ (kClosure N K)).subgroupOf (blockU (kClosure N K)) ∧
        ∀ (ℓ : ↥(kClosure N K)) (u v : ↥(blockU (kClosure N K))),
          (v : G) = ℓ * u * (ℓ : G)⁻¹ → R (α ℓ) (β u) (β v) := by
  have hUW := h.blockU_kClosure_le_wOne
  let ρD := lin.restr h.kClosure_le_gam
  let α : ↥(kClosure N K) →* T :=
    φ.toMonoidHom.comp ((MulEquiv.subgroupCongr himg).toMonoidHom.comp ρD)
  let β : ↥(blockU (kClosure N K)) →* Multiplicative M :=
    { toFun := fun u => Multiplicative.ofAdd (ψ (lin.vec (Subgroup.inclusion hUW u)))
      map_one' := by
        rw [map_one, lin.vec_one, map_zero, ofAdd_zero]
      map_mul' := fun u v => by
        rw [map_mul, lin.vec_mul, map_add, ofAdd_add] }
  refine ⟨α, φ.surjective.comp ((MulEquiv.subgroupCongr himg).surjective.comp
    (lin.restr_surjective _)), ?_, β, ?_, ?_, ?_⟩
  · ext d
    rw [MonoidHom.mem_ker, ← h.ker_restr_kClosure hW₀ lin, MonoidHom.mem_ker]
    simp only [α, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [MulEquiv.map_eq_one_iff, MulEquiv.map_eq_one_iff]
  · intro m
    have hv : ψ.symm (Multiplicative.toAdd m) ∈ lin.imgVec (blockU (kClosure N K)) := by
      rw [h.imgVec_blockU_kClosure hW₀ lin]
      exact Submodule.mem_top
    obtain ⟨w, hw, hwv⟩ := hv
    refine ⟨⟨w, hw⟩, ?_⟩
    show Multiplicative.ofAdd (ψ (lin.vec (Subgroup.inclusion hUW ⟨(w : G), hw⟩))) = m
    have e : Subgroup.inclusion hUW ⟨(w : G), hw⟩ = w := Subtype.ext rfl
    rw [e, hwv, ψ.apply_symm_apply, ofAdd_toAdd]
  · ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← h.blockU_inf_wZero_kClosure hW₀ lin]
    show Multiplicative.ofAdd (ψ (lin.vec (Subgroup.inclusion hUW u))) = 1 ↔ _
    rw [ofAdd_eq_one, EmbeddingLike.map_eq_zero_iff, lin.vec_eq_zero_iff]
    exact ⟨fun hu0 => ⟨u.2, hu0⟩, fun hu => hu.2⟩
  · intro ℓ u v huv
    have hv : lin.vec (Subgroup.inclusion hUW v) =
        lin.ρ (Subgroup.inclusion h.kClosure_le_gam ℓ) (lin.vec (Subgroup.inclusion hUW u)) :=
      (lin.ρ_vec _ _ _ huv).symm
    have key := hR ((MulEquiv.subgroupCongr himg) (ρD ℓ)) (lin.vec (Subgroup.inclusion hUW u))
    have hcoe : (((MulEquiv.subgroupCongr himg) (ρD ℓ) :
        ↥(layerIn (lin.img (footeX N K ⊔ Q)))) : GLV V) =
          lin.ρ (Subgroup.inclusion h.kClosure_le_gam ℓ) := rfl
    rw [hcoe, ← hv] at key
    exact key

theorem ChiefHyp.isAltNaturalType_kClosure
    (himg : lin.img (kClosure N K) = layerIn (lin.img (footeX N K ⊔ Q))) {n : ℕ}
    (hE : IsAltHeartFor (layerIn (lin.img (footeX N K ⊔ Q))) n) :
    IsAltNaturalType (kClosure N K) n := by
  obtain ⟨φ, ψ, hφψ⟩ := hE
  exact h.exists_typeWitness_kClosure hW₀ lin himg φ ψ
    (fun t a b => ∀ x : evenWeight n, Multiplicative.toAdd a = (x : altHeart n) →
      Multiplicative.toAdd b = (evenWeightPerm (t : Equiv.Perm (Fin n)) x : altHeart n))
    (fun e v x hx => hφψ e v x hx)

theorem ChiefHyp.isOmegaMinusType_kClosure
    (himg : lin.img (kClosure N K) = layerIn (lin.img (footeX N K ⊔ Q))) {m : ℕ}
    (hE : IsOmegaMinusFor (layerIn (lin.img (footeX N K ⊔ Q))) m) :
    IsOmegaMinusType (kClosure N K) m := by
  obtain ⟨φ, ψ, hφψ⟩ := hE
  exact h.exists_typeWitness_kClosure hW₀ lin himg φ ψ.toAddEquiv
    (fun t a b => Multiplicative.toAdd b =
      ((t : GL (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) :
        Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) *ᵥ
          Multiplicative.toAdd a)
    (fun e v => hφψ e v)

theorem ChiefHyp.isAltNaturalType_six_of_card (hKF : IsFPrimeType K)
    (h360 : Nat.card ↥(lin.img K) = 360) : IsAltNaturalType K 6 := by
  let g : ↥(lin.img K) →* ↥K ⧸ CFSG.pCore 2 ↥K :=
    (lin.restr h.K_le_gam).liftOfSurjective (lin.restr_surjective h.K_le_gam)
      ⟨QuotientGroup.mk' _, by rw [QuotientGroup.ker_mk']; exact h.ker_restr_le hW₀ lin⟩
  have hg : Function.Surjective g := by
    intro q
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨lin.restr h.K_le_gam k, MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ k⟩
  have hdvd : Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) ∣ 360 := h360 ▸ Subgroup.card_dvd_of_surjective hg
  rcases hKF with ⟨m, hm, hA⟩ | hA | hO | hO | hO | hA
  · rw [card_quot_of_isAltNaturalType hA, card_alternatingGroup_fin (by omega)] at hdvd
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    obtain rfl : m = 6 := by
      by_contra hne
      have h7 : Nat.factorial 7 ≤ m.factorial := Nat.factorial_le (by omega)
      have h5040 : Nat.factorial 7 = 5040 := by decide
      omega
    exact hA
  · rw [card_quot_of_isA7FourType hA] at hdvd
    exact absurd hdvd (by decide)
  · rw [card_quot_of_isOmegaPlusType hO] at hdvd
    obtain ⟨s, -, hs⟩ := exists_card_omegaPlusTwo (m := 3) le_rfl
    rw [hs] at hdvd
    exact absurd (dvd_trans (Dvd.intro s rfl) hdvd) (by decide)
  · rw [card_quot_of_isOmegaMinusType hO] at hdvd
    obtain ⟨s, -, hs⟩ := exists_card_omegaMinusTwo (m := 2) le_rfl
    rw [hs] at hdvd
    exact absurd (dvd_trans (Dvd.intro s rfl) hdvd) (by decide)
  · rw [card_quot_of_isOmegaMinusType hO] at hdvd
    obtain ⟨s, -, hs⟩ := exists_card_omegaMinusTwo (m := 3) (by norm_num)
    rw [hs] at hdvd
    exact absurd (dvd_trans (Dvd.intro s rfl) hdvd) (by decide)
  · rw [card_quot_of_isA6Z3Type hA] at hdvd
    exact absurd hdvd (by decide)

end Climb

theorem ChiefHyp.climb (hKP : CFSG.Assembly.KProper CFSG.Assembly.InCatalog G) (h66 : Thm66F)
    {N K Q : Subgroup G} (h : ChiefHyp N K Q) (hKF : IsFPrimeType K) :
    IsFooteBlock N (kClosure N K) ∧ K ≤ kClosure N K ∧
      Q ≤ Subgroup.normalizer (kClosure N K : Set G) ∧
      kClosure N K = Subgroup.closure {g | ∃ ℓ ∈ kClosure N K, ∃ k ∈ K, g = ℓ * k * ℓ⁻¹} ∧
      (kClosure N K = K ∨
        (kClosure N K ≠ K ∧ FooteArrow K (kClosure N K) ∧
          IsComponentOf (barIn (kClosure N K) K) (centralizerBarIn (kClosure N K) Q) ∧
          ((∃ n : ℕ, 8 ≤ n ∧ IsAltNaturalType (kClosure N K) n) ∨
            (IsOmegaMinusType (kClosure N K) 2 ∧ IsAltNaturalType K 6)))) := by
  obtain ⟨W₀, hW₀⟩ := h.exists_wZero
  have hc := h.isChiefFactor hW₀
  have hW₁Γ : wOne N K Q ≤ footeX N K ⊔ Q :=
    h.wOne_le_core.trans ((core_le_footeX N K).trans le_sup_left)
  obtain ⟨V, iV, iM, iF, ⟨lin⟩⟩ :=
    exists_chiefLin hc (h.core_isPGroup.to_le h.wOne_le_core) hW₁Γ
  have hS := h.setup6Irr_img hW₀ lin
  have hFM := h.isFPrimeModule_img hW₀ lin hKF
  rcases h66 V _ _ _ (lin.kProper_img hKP _) hS hFM with h1 | ⟨n, k, hn, hk, ⟨eK⟩, hE⟩ |
    ⟨⟨eK⟩, hE⟩
  ·
    have hDK := h.kClosure_eq_of_img_eq hW₀ lin h1
    have hblock : IsFooteBlock N (kClosure N K) := by
      have hsub := h.isSubnormal_kClosure
      rw [hDK] at hsub ⊢
      exact ⟨h.K_le, hsub, h.block.residual, h.block.quasisimple, h.block.chief⟩
    exact ⟨hblock, h.K_le_kClosure, h.Q_le_normalizer_kClosure, h.kClosure_eq_closure, Or.inl hDK⟩
  ·
    have hE' := hE
    obtain ⟨φ, -, -⟩ := hE'
    haveI : IsSimpleGroup (alternatingGroup (Fin (n + 2 * k))) :=
      alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)
    have hEs : IsSimpleGroup ↥(layerIn (lin.img (footeX N K ⊔ Q))) := φ.isSimpleGroup
    have himg := h.img_kClosure_eq_layerIn hW₀ lin hEs
    refine ⟨h.isFooteBlock_kClosure hW₀ lin hEs, h.K_le_kClosure, h.Q_le_normalizer_kClosure,
      h.kClosure_eq_closure, Or.inr ⟨fun hDK => ?_, h.footeArrow_kClosure,
        h.isComponentOf_barIn_kClosure,
        Or.inl ⟨n + 2 * k, by omega, h.isAltNaturalType_kClosure hW₀ lin himg hE⟩⟩⟩
    have hKE : lin.img K = layerIn (lin.img (footeX N K ⊔ Q)) := by rw [← himg, hDK]
    have h1 := Nat.card_congr eK.toEquiv
    have h2 := Nat.card_congr φ.toEquiv
    rw [hKE] at h1
    rw [h1, card_alternatingGroup_fin (by omega), card_alternatingGroup_fin (by omega)] at h2
    have hlt : n.factorial < (n + 2 * k).factorial := (Nat.factorial_lt (by omega)).mpr (by omega)
    have hd : 2 ∣ (n + 2 * k).factorial := Nat.dvd_factorial (by norm_num) (by omega)
    have := Nat.div_lt_div_of_lt_of_dvd hd hlt
    omega
  ·
    have hE' := hE
    obtain ⟨φ, -, -⟩ := hE'
    have hirr : ∀ s : ZMod 2, s ^ 2 + 1 * s + 1 ≠ 0 := by decide
    obtain ⟨hsimple, -, -⟩ :=
      CFSG.ComponentClassification.RankTwoClassical.isSimpleGroup_statedOmega_quadMinus_small
        (n := 3) (Or.inr rfl) hirr
    haveI : IsSimpleGroup ↥(omegaMinusTwo 2) := hsimple
    have hEs : IsSimpleGroup ↥(layerIn (lin.img (footeX N K ⊔ Q))) := φ.isSimpleGroup
    have himg := h.img_kClosure_eq_layerIn hW₀ lin hEs
    have h360 : Nat.card ↥(lin.img K) = 360 := by
      rw [Nat.card_congr eK.toEquiv, card_alternatingGroup_fin (by norm_num)]
      decide
    refine ⟨h.isFooteBlock_kClosure hW₀ lin hEs, h.K_le_kClosure, h.Q_le_normalizer_kClosure,
      h.kClosure_eq_closure, Or.inr ⟨fun hDK => ?_, h.footeArrow_kClosure,
        h.isComponentOf_barIn_kClosure,
        Or.inr ⟨h.isOmegaMinusType_kClosure hW₀ lin himg hE,
          h.isAltNaturalType_six_of_card hW₀ lin hKF h360⟩⟩⟩
    have hKE : lin.img K = layerIn (lin.img (footeX N K ⊔ Q)) := by rw [← himg, hDK]
    obtain ⟨s, -, hs⟩ := exists_card_omegaMinusTwo (m := 2) le_rfl
    have h2 := Nat.card_congr φ.toEquiv
    rw [← hKE, h360, hs] at h2
    norm_num at h2
    omega

end CFSG.CGT.Foote82
