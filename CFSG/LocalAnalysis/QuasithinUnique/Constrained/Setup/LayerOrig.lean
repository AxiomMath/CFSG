module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerBin
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerCP1
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerNonsolv3
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerSQTK
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.Reduced

public section

namespace CFSG.QuasithinUnique.Setup.Layer

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup CFSG.QuasithinUnique.Setup.Offender
  CFSG.Quasithin CFSG.Open CFSG.SectionRank CFSG.LocalCores
open scoped Multiplicative commutatorElement

universe u

section Model

variable {G : Type} [Group G] {P V : Subgroup G}

@[expose] def IsBinModel (hP : P ≤ Subgroup.normalizer (V : Set G)) {W : Type} [AddCommGroup W]
    [Module (ZMod 2) W] (θ : ↥V ≃* Multiplicative W) (ρ : ↥P →* (W ≃ₗ[ZMod 2] W)) : Prop :=
  ∀ (p : ↥P) (v : ↥V),
    θ (rho V P hP p v) = Multiplicative.ofAdd (ρ p (Multiplicative.toAdd (θ v)))

variable {hP : P ≤ Subgroup.normalizer (V : Set G)} {W : Type} [AddCommGroup W]
  [Module (ZMod 2) W] {θ : ↥V ≃* Multiplicative W} {ρ : ↥P →* (W ≃ₗ[ZMod 2] W)}

theorem IsBinModel.eq_comp (h : IsBinModel hP θ ρ) :
    ρ = (binPsi θ).toMonoidHom.comp (rho V P hP) := by
  apply MonoidHom.ext
  intro p
  apply LinearEquiv.ext
  intro w
  have h1 := h p (θ.symm (Multiplicative.ofAdd w))
  simp only [MulEquiv.apply_symm_apply, toAdd_ofAdd] at h1
  show ρ p w = binPsi θ (rho V P hP p) w
  rw [binPsi_apply]
  rw [h1]
  simp

theorem autOn_eq_map_rho {X : Subgroup G} (hXP : X ≤ P) :
    autOn X V = (X.subgroupOf P).map (rho V P hP) := by
  ext φ
  rw [mem_autOn_iff_rho hP hXP, Subgroup.mem_map]
  constructor
  · rintro ⟨p, hpX, rfl⟩
    exact ⟨p, hpX, rfl⟩
  · rintro ⟨p, hpX, rfl⟩
    exact ⟨p, hpX, rfl⟩

theorem IsBinModel.range_eq (h : IsBinModel hP θ ρ) :
    ρ.range = (autOn P V).map (binPsi θ).toMonoidHom := by
  rw [h.eq_comp, MonoidHom.range_comp, range_rho hP]

theorem IsBinModel.image_eq (h : IsBinModel hP θ ρ) {X : Subgroup G} (hXP : X ≤ P) :
    (X.subgroupOf P).map ρ = (autOn X V).map (binPsi θ).toMonoidHom := by
  rw [h.eq_comp, ← Subgroup.map_map, ← autOn_eq_map_rho hXP]

theorem IsBinModel.eq_one_iff (h : IsBinModel hP θ ρ) (p : ↥P) :
    ρ p = 1 ↔ (p : G) ∈ Subgroup.centralizer (V : Set G) := by
  rw [h.eq_comp, MonoidHom.comp_apply, ← rho_eq_one_iff hP]
  exact ⟨fun h1 => (binPsi θ).injective (by simpa using h1), fun h1 => by simp [h1]⟩

end Model

section Transport2

variable {A B : Type*} [Group A] [Group B]

theorem map_map_symm (e : A ≃* B) (X : Subgroup B) :
    (X.map e.symm.toMonoidHom).map e.toMonoidHom = X := by
  ext y
  constructor
  · rintro ⟨x, ⟨z, hz, rfl⟩, rfl⟩
    simpa using hz
  · intro hy
    exact ⟨e.symm y, ⟨y, hy, rfl⟩, by simp⟩

end Transport2

section Reduced

variable {G : Type} [Group G] {S P V : Subgroup G} {W : Type} [AddCommGroup W]
  [Module (ZMod 2) W]

structure OriginalReduced (S P : Subgroup G) (ρ : ↥P →* (W ≃ₗ[ZMod 2] W)) : Prop where
  o2 : ∀ N : Subgroup (W ≃ₗ[ZMod 2] W), N ≤ ρ.range → (N.subgroupOf ρ.range).Normal →
    IsPGroup 2 N → N = ⊥
  sylow : IsSylowTwoOf ((S.subgroupOf P).map ρ) ρ.range
  ne_bot : (S.subgroupOf P).map ρ ≠ ⊥
  not_normal : ¬ (((S.subgroupOf P).map ρ).subgroupOf ρ.range).Normal
  max : (S.subgroupOf P).map ρ ≤ ((uniqueMaxOver S P).subgroupOf P).map ρ ∧
    ((uniqueMaxOver S P).subgroupOf P).map ρ < ρ.range ∧
    ∀ X : Subgroup (W ≃ₗ[ZMod 2] W), (S.subgroupOf P).map ρ ≤ X → X < ρ.range →
      X ≤ ((uniqueMaxOver S P).subgroupOf P).map ρ
  offender : ∃ A : Subgroup G, IsMaxElemAbelian S A ∧ (A.subgroupOf P).map ρ ≠ ⊥ ∧
    Nat.card W ≤ weight (MonoidHom.id (W ≃ₗ[ZMod 2] W)) ((A.subgroupOf P).map ρ)

variable {θ : ↥V ≃* Multiplicative W} {ρ : ↥P →* (W ≃ₗ[ZMod 2] W)}

theorem IsBinModel.card_image {hP : P ≤ Subgroup.normalizer (V : Set G)}
    (h : IsBinModel hP θ ρ) {A : Subgroup G} (hAP : A ≤ P) :
    Nat.card ↥((A.subgroupOf P).map ρ) = (A ⊓ Subgroup.centralizer (V : Set G)).relIndex A := by
  rw [h.image_eq hAP, Subgroup.card_map_of_injective (binPsi θ).injective,
    card_autOn_eq_relIndex (hAP.trans hP)]

theorem IsBinModel.card_fix {hP : P ≤ Subgroup.normalizer (V : Set G)}
    (h : IsBinModel hP θ ρ) {A : Subgroup G} (hAP : A ≤ P) :
    Nat.card ↥(fixGL ((A.subgroupOf P).map ρ)) =
      Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) := by
  have hfix : ∀ w : W, w ∈ fixGL ((A.subgroupOf P).map ρ) ↔
      ∀ a : ↥P, (a : G) ∈ A → ρ a w = w := by
    intro w
    rw [mem_fixGL]
    constructor
    · intro hw a ha
      exact hw (ρ a) ⟨a, ha, rfl⟩
    · rintro hw _ ⟨a, ha, rfl⟩
      exact hw a ha
  have hconj : ∀ (a : ↥P) (v : ↥V), (rho V P hP a v : ↥V) = v ↔ ρ a (Multiplicative.toAdd (θ v)) =
      Multiplicative.toAdd (θ v) := by
    intro a v
    have h1 := h a v
    constructor
    · intro hv
      rw [hv] at h1
      have := congrArg Multiplicative.toAdd h1
      simpa using this.symm
    · intro hv
      apply θ.injective
      rw [h1, hv]
      simp
  have hcoe : ∀ (a : ↥P) (v : ↥V), (rho V P hP a v : ↥V) = v ↔
      (a : G) * (v : G) = (v : G) * (a : G) := by
    intro a v
    rw [Subtype.ext_iff, rho_apply_coe]
    constructor
    · intro h2
      calc (a : G) * v = (a * v * (a : G)⁻¹) * a := by group
        _ = v * a := by rw [h2]
    · intro h2
      rw [h2]
      group
  refine Nat.card_congr
    { toFun := fun w => ⟨(θ.symm (Multiplicative.ofAdd (w : W)) : G), ?_, ?_⟩
      invFun := fun v => ⟨Multiplicative.toAdd (θ ⟨(v : G), v.2.1⟩), ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · exact (θ.symm (Multiplicative.ofAdd (w : W))).2
  · refine Subgroup.mem_centralizer_iff.2 fun a ha => ?_
    have hw := (hfix w).1 w.2 ⟨a, hAP ha⟩ ha
    have h3 := (hconj ⟨a, hAP ha⟩ (θ.symm (Multiplicative.ofAdd (w : W)))).2 (by simpa using hw)
    exact (hcoe ⟨a, hAP ha⟩ _).1 h3
  · rw [hfix]
    intro a ha
    rw [← hconj a ⟨(v : G), v.2.1⟩]
    rw [hcoe]
    exact (Subgroup.mem_centralizer_iff.1 v.2.2) a ha
  · intro w
    apply Subtype.ext
    simp
  · intro v
    apply Subtype.ext
    simp

theorem OriginalReduced.of_reducedAction (hR : ReducedAction G S P V)
    (h : IsBinModel hR.le_normalizer θ ρ) : OriginalReduced S P ρ := by
  have hPN := hR.le_normalizer
  have hSP : S ≤ P := hR.sylow_le
  obtain ⟨hSI, hIP, hmaxI⟩ := uniqueMaxOver_spec hR.obstruction.minParabolic
  let ψ : MulAut ↥V ≃* (W ≃ₗ[ZMod 2] W) := binPsi θ
  have hΛ : ρ.range = (autOn P V).map ψ.toMonoidHom := h.range_eq
  have hRimg : (S.subgroupOf P).map ρ = (autOn S V).map ψ.toMonoidHom := h.image_eq hSP
  have hIimg : ((uniqueMaxOver S P).subgroupOf P).map ρ =
      (autOn (uniqueMaxOver S P) V).map ψ.toMonoidHom := h.image_eq hIP.le
  have hSΛ : autOn S V ≤ autOn P V := autOn_le_autOn V hSP
  have hnn : ¬ (((S.subgroupOf P).map ρ).subgroupOf ρ.range).Normal := by
    intro hn
    rw [hΛ, hRimg] at hn
    exact hR.image_not_normal ((normal_subgroupOf_map_iff ψ hSΛ).1 hn)
  refine ⟨?_, ?_, ?_, hnn, ?_, ?_⟩
  ·
    intro N hN hNn hNp
    rw [hΛ] at hN hNn
    have hNN₀ : (N.map ψ.symm.toMonoidHom).map ψ.toMonoidHom = N := map_map_symm ψ N
    have hN₀le : N.map ψ.symm.toMonoidHom ≤ autOn P V := by
      rw [← Subgroup.map_le_map_iff_of_injective ψ.injective (f := ψ.toMonoidHom), hNN₀]
      exact hN
    have hN₀n : ((N.map ψ.symm.toMonoidHom).subgroupOf (autOn P V)).Normal := by
      refine (normal_subgroupOf_map_iff ψ hN₀le).1 ?_
      rw [hNN₀]
      exact hNn
    have hN₀p : IsPGroup 2 ↥(N.map ψ.symm.toMonoidHom) := hNp.map ψ.symm.toMonoidHom
    have hle := CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2
      (N.map ψ.symm.toMonoidHom) (autOn P V) hN₀le hN₀n hN₀p
    rw [hR.image_pCore] at hle
    have h0 : N.map ψ.symm.toMonoidHom = ⊥ := le_bot_iff.1 hle
    rw [← hNN₀, h0, Subgroup.map_bot]
  ·
    rw [hΛ, hRimg]
    exact (isSylowTwoOf_map_mulEquiv ψ).2 hR.image_sylow
  ·
    intro hbot
    apply hnn
    rw [hbot, Subgroup.bot_subgroupOf]
    infer_instance
  ·
    rw [hΛ, hRimg, hIimg]
    obtain ⟨hSI', hIΛ, hmaxΛ⟩ := hR.image_max
    refine ⟨Subgroup.map_mono hSI', ?_, ?_⟩
    · exact (Subgroup.map_lt_map_iff_of_injective ψ.injective).2 hIΛ
    · intro X' hSX' hX'Λ
      have hXX' : (X'.map ψ.symm.toMonoidHom).map ψ.toMonoidHom = X' := map_map_symm ψ X'
      have h1 : autOn S V ≤ X'.map ψ.symm.toMonoidHom := by
        rw [← Subgroup.map_le_map_iff_of_injective ψ.injective (f := ψ.toMonoidHom), hXX']
        exact hSX'
      have h2 : X'.map ψ.symm.toMonoidHom < autOn P V := by
        rw [← Subgroup.map_lt_map_iff_of_injective ψ.injective (f := ψ.toMonoidHom), hXX']
        exact hX'Λ
      have h3 := hmaxΛ _ h1 h2
      rw [← hXX']
      exact Subgroup.map_mono h3
  ·
    obtain ⟨A, hA⟩ := hR.offender
    have hAS : A ≤ S := hA.1.1
    have hAP : A ≤ P := hAS.trans hSP
    have hAn : A ≤ Subgroup.normalizer (V : Set G) := hAP.trans hPN
    refine ⟨A, hA.1, ?_, ?_⟩
    · rw [h.image_eq hAP]
      intro hbot
      exact autOn_ne_bot_of_not_le_centralizer hAn hA.2.1
        ((Subgroup.map_eq_bot_iff_of_injective _ ψ.injective).1 hbot)
    · have hw : weight (MonoidHom.id (W ≃ₗ[ZMod 2] W)) ((A.subgroupOf P).map ρ) =
          Nat.card ↥((A.subgroupOf P).map ρ) * Nat.card ↥(fixGL ((A.subgroupOf P).map ρ)) := rfl
      rw [hw, h.card_image hAP, h.card_fix hAP]
      have hcard : Nat.card ↥V = Nat.card W :=
        Nat.card_congr (θ.toEquiv.trans Multiplicative.toAdd)
      rw [← hcard]
      exact hA.2.2.2

end Reduced

section Layer

variable {G : Type} [Group G] {S P V : Subgroup G} {W : Type} [AddCommGroup W]
  [Module (ZMod 2) W]

theorem layer_subgroupOf_eq_top {H : Type*} [Group H] {K : Subgroup H} (hK : K = CFSG.layer H) :
    CFSG.layer ↥K = ⊤ := by
  have hcomp : ∀ L : Subgroup H, CFSG.IsComponent L → L ≤ K := fun L hL =>
    (le_sSup hL : L ≤ CFSG.layer H).trans hK.ge
  have hKle : CFSG.layer H ≤ (CFSG.layer ↥K).map K.subtype := by
    refine sSup_le fun L hL => ?_
    have h1 : CFSG.IsComponent (L.subgroupOf K) := component_overgroup hL (hcomp L hL)
    have h2 : L.subgroupOf K ≤ CFSG.layer ↥K := le_sSup h1
    calc L = (L.subgroupOf K).map K.subtype := (Subgroup.map_subgroupOf_eq_of_le (hcomp L hL)).symm
      _ ≤ (CFSG.layer ↥K).map K.subtype := Subgroup.map_mono h2
  refine eq_top_iff.2 fun x _ => ?_
  obtain ⟨y, hy, hyx⟩ := (hK.le.trans hKle) x.2
  have : y = x := Subtype.ext hyx
  rwa [this] at hy

theorem exists_pow_mem_of_sup_eq_top {Q : Type*} [Group Q] {K T : Subgroup Q} [hK : K.Normal]
    (hT : IsPGroup 2 ↥T) (hKT : K ⊔ T = ⊤) (x : Q) : ∃ n : ℕ, x ^ 2 ^ n ∈ K := by
  have hx : x ∈ K ⊔ T := by
    rw [hKT]
    trivial
  have hTn : T ≤ Subgroup.normalizer (K : Set Q) := by
    have : Subgroup.normalizer (K : Set Q) = ⊤ := Subgroup.normalizer_eq_top_iff.2 hK
    rw [this]
    exact le_top
  obtain ⟨k, hk, t, ht, rfl⟩ := exists_mul_of_mem_sup hTn hx
  obtain ⟨n, hn⟩ := hT ⟨t, ht⟩
  refine ⟨n, ?_⟩
  have h1 : (t : Q) ^ 2 ^ n = 1 := congrArg Subtype.val hn
  have h2 : ((QuotientGroup.mk (k * t) : Q ⧸ K)) = QuotientGroup.mk t := by
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff k).2 hk, one_mul]
  refine (QuotientGroup.eq_one_iff _).1 ?_
  rw [QuotientGroup.mk_pow, h2, ← QuotientGroup.mk_pow, h1, QuotientGroup.mk_one]

theorem map_oddOrderSubgroup {A B : Type*} [Group A] [Group B] (e : A ≃* B) (Y : Subgroup A) :
    (oddOrderSubgroup Y).map e.toMonoidHom = oddOrderSubgroup (Y.map e.toMonoidHom) := by
  unfold oddOrderSubgroup
  rw [MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨x, ⟨hxY, hxo⟩, rfl⟩
    refine ⟨⟨x, hxY, rfl⟩, ?_⟩
    have := orderOf_injective e.toMonoidHom e.injective x
    rw [this]
    exact hxo
  · rintro ⟨⟨x, hxY, rfl⟩, hyo⟩
    refine ⟨x, ⟨hxY, ?_⟩, rfl⟩
    have := orderOf_injective e.toMonoidHom e.injective x
    rw [← this]
    exact hyo

theorem isElementaryAbelian_subgroupOf {A P : Subgroup G} (hA : IsElemAbelian 2 A) :
    CFSG.IsElementaryAbelian 2 ↥(A.subgroupOf P) := by
  refine { is_comm := ⟨fun a b => ?_⟩, exponent_dvd_p := ?_ }
  · apply Subtype.ext
    apply Subtype.ext
    have := congrArg Subtype.val
      (hA.1.is_comm.comm ⟨((a : ↥P) : G), a.2⟩ ⟨((b : ↥P) : G), b.2⟩)
    exact this
  · refine Monoid.exponent_dvd_of_forall_pow_eq_one fun g => ?_
    apply Subtype.ext
    apply Subtype.ext
    exact hA.2 _ g.2

end Layer

section Existence

variable {G : Type} [Group G] [Finite G]

theorem exists_binModel {P V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hP : P ≤ Subgroup.normalizer (V : Set G)) :
    ∃ (W : Type) (_ : AddCommGroup W) (_ : Module (ZMod 2) W) (_ : Finite W)
      (θ : ↥V ≃* Multiplicative W) (ρ : ↥P →* (W ≃ₗ[ZMod 2] W)), IsBinModel hP θ ρ := by
  let _ : CommGroup ↥V := CFSG.Quasithin.commGroupOfElemAbelian hV
  let _ : Module (ZMod 2) (Additive ↥V) := AddCommGroup.zmodModule (n := 2) fun x => by
    have h2 : (Additive.toMul x) ^ 2 = 1 := Subtype.ext (hV.2 _ (Additive.toMul x).2)
    have h3 : Additive.toMul (2 • x) = 1 := by
      rw [toMul_nsmul]
      exact h2
    exact toMul_eq_one.1 h3
  let θ : ↥V ≃* Multiplicative (Additive ↥V) := (MulEquiv.multiplicativeAdditive ↥V).symm
  refine ⟨Additive ↥V, inferInstance, inferInstance, inferInstance, θ,
    (binPsi θ).toMonoidHom.comp (rho V P hP), ?_⟩
  intro p v
  have := binPsi_apply θ (rho V P hP p) (Multiplicative.toAdd (θ v))
  show θ (rho V P hP p v) = Multiplicative.ofAdd (binPsi θ (rho V P hP p) (Multiplicative.toAdd (θ v)))
  rw [this]
  simp

end Existence

section Main

variable {G : Type} [Group G] [Finite G] {S P : Subgroup G} {W : Type} [AddCommGroup W]
  [Module (ZMod 2) W] [Finite W]

@[expose] def rhoOn (ρ : ↥P →* (W ≃ₗ[ZMod 2] W)) (N : Subgroup G) (hNP : N ≤ P) :
    ↥N →* (W ≃ₗ[ZMod 2] W) :=
  ρ.comp (Subgroup.inclusion hNP)

structure OriginalLayer (S P V : Subgroup G) (ρ : ↥P →* (W ≃ₗ[ZMod 2] W)) : Prop where
  layer : NonsolvableLayer ρ.range ((S.subgroupOf P).map ρ)
    (((uniqueMaxOver S P).subgroupOf P).map ρ)
  range_odd : ((oddOrderSubgroup P).subgroupOf P).map ρ = oddGen ρ.range
  layer_K : CFSG.layer ↥((oddGen ρ.range).subgroupOf ρ.range) = ⊤
  two_quotient : ∀ x : ↥ρ.range, ∃ n : ℕ, x ^ 2 ^ n ∈ (oddGen ρ.range).subgroupOf ρ.range
  sqtk : IsSQTKCat ↥ρ.range ∧ ∀ p : ℕ, p.Prime → p ≠ 2 →
    CFSG.Open.pRank p (⊤ : Subgroup ↥ρ.range) =
        CFSG.Open.pRank p (⊤ : Subgroup ↥((oddGen ρ.range).subgroupOf ρ.range)) ∧
      CFSG.Open.pRank p (⊤ : Subgroup ↥((oddGen ρ.range).subgroupOf ρ.range)) ≤ 2
  ker_eq : (rhoOn ρ (oddOrderSubgroup P) (oddOrderSubgroup_le P)).ker =
    (Subgroup.centralizer (V : Set G)).subgroupOf (oddOrderSubgroup P)
  iso : Nonempty (↥(oddOrderSubgroup P) ⧸
    (rhoOn ρ (oddOrderSubgroup P) (oddOrderSubgroup_le P)).ker ≃* ↥(oddGen ρ.range))

theorem original_nonsolvable_action (hQ : QuadBestOffendersNormalize (ZMod 2) W)
    (hcent : OddKernelCentralization) (hcat : CatalogStepHyp)
    (hobs : PushUpObstruction S P)
    {θ : ↥(conjClosure (omegaOneCenterOf S) P) ≃* Multiplicative W}
    {ρ : ↥P →* (W ≃ₗ[ZMod 2] W)}
    (h : IsBinModel (reducedAction_of_pushUpObstruction hobs).le_normalizer θ ρ) :
    OriginalReduced S P ρ ∧ (¬ Group.IsSolvable ↥ρ.range →
      OriginalLayer S P (conjClosure (omegaOneCenterOf S) P) ρ) := by
  classical
  have hR := reducedAction_of_pushUpObstruction hobs
  have hred := OriginalReduced.of_reducedAction hR h
  refine ⟨hred, fun hns => ?_⟩
  have hPN := hR.le_normalizer
  have hSP : S ≤ P := hR.sylow_le
  obtain ⟨A, hA, hAne, hAoff⟩ := hred.offender
  have hAP : A ≤ P := hA.1.trans hSP
  have hEΛ : (A.subgroupOf P).map ρ ≤ ρ.range := fun x hx => by
    obtain ⟨a, -, rfl⟩ := hx
    exact ⟨a, rfl⟩
  have hAel : CFSG.IsElementaryAbelian 2 ↥(A.subgroupOf P) :=
    isElementaryAbelian_subgroupOf hA.2.1
  have hEel : CFSG.IsElementaryAbelian 2 ↥((A.subgroupOf P).map ρ) :=
    isElementaryAbelian_map ρ (A.subgroupOf P)
  have hlayer := nonsolvable_layer hQ hns hred.o2 hred.sylow hred.not_normal hred.max.1
    hred.max.2.1 hred.max.2.2 hEΛ hAne hEel hAoff
  have hKn : ((oddGen ρ.range).subgroupOf ρ.range).Normal := by
    rw [hlayer.K_eq_layer]
    have := layer_characteristic (G := ↥ρ.range)
    infer_instance
  have hrange_odd : ((oddOrderSubgroup P).subgroupOf P).map ρ = oddGen ρ.range := by
    rw [h.image_eq (oddOrderSubgroup_le P), autOn_oddOrderSubgroup hPN, h.range_eq,
      map_oddOrderSubgroup (binPsi θ)]
    rfl
  have hKT : (oddGen ρ.range).subgroupOf ρ.range ⊔ ((S.subgroupOf P).map ρ).subgroupOf ρ.range =
      ⊤ := by
    have hKH : oddGen ρ.range ≤ ρ.range := (Subgroup.closure_le _).2 fun h hh => hh.1
    have h1 := hlayer.H_eq_KT
    have h2 : (oddGen ρ.range ⊔ (S.subgroupOf P).map ρ).subgroupOf ρ.range = ⊤ := by
      rw [h1, Subgroup.subgroupOf_self]
    rwa [Subgroup.subgroupOf_sup hKH hred.sylow.1] at h2
  have hRp : IsPGroup 2 ↥(((S.subgroupOf P).map ρ).subgroupOf ρ.range) :=
    hred.sylow.2.1.comap_subtype
  have hquot : ∀ x : ↥ρ.range, ∃ n : ℕ, x ^ 2 ^ n ∈ (oddGen ρ.range).subgroupOf ρ.range :=
    fun x => exists_pow_mem_of_sup_eq_top hRp hKT x
  have hLtop : CFSG.layer ↥((oddGen ρ.range).subgroupOf ρ.range) = ⊤ :=
    layer_subgroupOf_eq_top hlayer.K_eq_layer
  have h2grp : IsPGroup 2 (↥ρ.range ⧸ (oddGen ρ.range).subgroupOf ρ.range) := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨n, hn⟩ := hquot x
    exact ⟨n, by rw [← QuotientGroup.mk_pow]; exact (QuotientGroup.eq_one_iff _).2 hn⟩
  let π : ↥(⊤ : Subgroup ↥P) →* ↥ρ.range := ρ.rangeRestrict.comp Subgroup.topEquiv.toMonoidHom
  have hπ : Function.Surjective π := fun y => by
    obtain ⟨p, hp⟩ := ρ.rangeRestrict_surjective y
    exact ⟨Subgroup.topEquiv.symm p, by simpa [π] using hp⟩
  have hsqtk := sqtk_two_power_index hcent hcat hobs.sqtk ⊤ π hπ
    ((oddGen ρ.range).subgroupOf ρ.range) hLtop h2grp
  have hker : (rhoOn ρ (oddOrderSubgroup P) (oddOrderSubgroup_le P)).ker =
      (Subgroup.centralizer
        ((conjClosure (omegaOneCenterOf S) P : Subgroup G) : Set G)).subgroupOf
        (oddOrderSubgroup P) := by
    ext x
    rw [MonoidHom.mem_ker]
    exact h.eq_one_iff _
  have hrng : (rhoOn ρ (oddOrderSubgroup P) (oddOrderSubgroup_le P)).range = oddGen ρ.range := by
    unfold rhoOn
    rw [MonoidHom.range_comp, Subgroup.inclusion_range, hrange_odd]
  exact ⟨hlayer, hrange_odd, hLtop, hquot, hsqtk, hker,
    ⟨(QuotientGroup.quotientKerEquivRange _).trans (MulEquiv.subgroupCongr hrng)⟩⟩

end Main

end CFSG.QuasithinUnique.Setup.Layer
