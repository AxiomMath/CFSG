module

public import CFSG.ClassicalInvolution.Asc77.AscT8YC5

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
open scoped Pointwise

namespace T8YY

section Generic

variable {G : Type} [Group G] [Finite G]

theorem mem_zStarOf_iff (H : Subgroup G) {x : G} :
    x ∈ zStarOf H ↔ x ∈ H ∧ ∀ y ∈ H, x⁻¹ * y⁻¹ * x * y ∈ oddCoreOf H := by
  unfold zStarOf
  constructor
  · rintro ⟨h, hh, rfl⟩
    refine ⟨h.2, fun y hy => ?_⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_center_iff] at hh
    have h1 := hh (QuotientGroup.mk (⟨y, hy⟩ : ↥H))
    rw [← QuotientGroup.mk'_apply (classicalInvolutionOddCore ↥H) (⟨y, hy⟩ : ↥H), ← map_mul,
      ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h1
    exact Subgroup.mem_map.mpr ⟨_, h1, by simp [mul_assoc]⟩
  · rintro ⟨hx, hc⟩
    refine ⟨⟨x, hx⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_center_iff]
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    rw [← QuotientGroup.mk'_apply (classicalInvolutionOddCore ↥H) y, ← map_mul, ← map_mul,
      QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    obtain ⟨w, hw, hwv⟩ := Subgroup.mem_map.mp (hc (y : G) y.2)
    have hwv' : (w : G) = x⁻¹ * (y : G)⁻¹ * x * y := hwv
    have : (y * (⟨x, hx⟩ : ↥H))⁻¹ * ((⟨x, hx⟩ : ↥H) * y) = w := by
      apply Subtype.ext
      rw [hwv']
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, mul_assoc]
    rw [this]
    exact hw

theorem conj_mem_zStarOf {H : Subgroup G} {c : G} (hc : conjSub c H = H) {x : G}
    (hx : x ∈ zStarOf H) : c * x * c⁻¹ ∈ zStarOf H := by
  rw [mem_zStarOf_iff] at hx ⊢
  obtain ⟨hxH, hxc⟩ := hx
  have hcH : ∀ y ∈ H, c * y * c⁻¹ ∈ H := fun y hy => by
    have : c * y * c⁻¹ ∈ conjSub c H := mem_conjSub_iff.mpr (by simpa [mul_assoc] using hy)
    rwa [hc] at this
  have hcH' : ∀ y ∈ H, c⁻¹ * y * c ∈ H := fun y hy => by
    have : y ∈ conjSub c H := by rw [hc]; exact hy
    exact mem_conjSub_iff.mp this
  refine ⟨hcH x hxH, fun y hy => ?_⟩
  have h1 := hxc (c⁻¹ * y * c) (hcH' y hy)
  have h2 : conjSub c (oddCoreOf H) = oddCoreOf H := by
    rw [← Thompson.oddCoreOf_conjSub_eq, hc]
  have h3 : c * (x⁻¹ * (c⁻¹ * y * c)⁻¹ * x * (c⁻¹ * y * c)) * c⁻¹ ∈
      conjSub c (oddCoreOf H) :=
    mem_conjSub_iff.mpr (by simpa [mul_assoc] using h1)
  rw [h2] at h3
  have e : (c * x * c⁻¹)⁻¹ * y⁻¹ * (c * x * c⁻¹) * y =
      c * (x⁻¹ * (c⁻¹ * y * c)⁻¹ * x * (c⁻¹ * y * c)) * c⁻¹ := by group
  rw [e]
  exact h3

theorem card_le_of_le_sup_odd {V O A : Subgroup G} (hO : Odd (Nat.card O))
    (hVO : V ≤ Subgroup.normalizer (O : Set G)) (hAH : A ≤ V ⊔ O) (hA : IsPGroup 2 A) :
    Nat.card A ≤ Nat.card V := by
  classical
  set H : Subgroup G := V ⊔ O with hH
  have hVH : V ≤ H := le_sup_left
  have hNorm : (O.subgroupOf H).Normal := Subgroup.normal_subgroupOf_sup_of_le_normalizer hVO
  let φ : ↥V →* (↥H ⧸ O.subgroupOf H) :=
    (QuotientGroup.mk' (O.subgroupOf H)).comp (Subgroup.inclusion hVH)
  have hφ : Function.Surjective φ := by
    intro q
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective q
    have hmem : (h : G) ∈ (↑(V ⊔ O) : Set G) := h.2
    rw [Subgroup.coe_mul_of_left_le_normalizer_right V O hVO] at hmem
    obtain ⟨v, hv, o, ho, hvo⟩ := hmem
    refine ⟨⟨v, hv⟩, ?_⟩
    show (QuotientGroup.mk' (O.subgroupOf H)) (Subgroup.inclusion hVH ⟨v, hv⟩) =
      QuotientGroup.mk h
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa [← hvo] using ho
  have hψ : Function.Injective
      ((QuotientGroup.mk' (O.subgroupOf H)).comp (Subgroup.inclusion hAH)) := by
    rw [injective_iff_map_eq_one]
    intro a ha
    rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf] at ha
    have ha2 : IsPGroup 2 (Subgroup.zpowers (a : G)) := hA.to_le (Subgroup.zpowers_le.mpr a.2)
    have : (a : G) = 1 := eq_one_of_isPGroup_of_mem_odd hO ha ha2
    exact Subtype.ext this
  calc Nat.card A ≤ Nat.card (↥H ⧸ O.subgroupOf H) := Nat.card_le_card_of_injective _ hψ
    _ ≤ Nat.card V := Nat.card_le_card_of_surjective _ hφ

theorem exists_oddCore_conj_of_le_sup {V V' O : Subgroup G} (hO : Odd (Nat.card O))
    (hV : IsPGroup 2 V) (hV' : IsPGroup 2 V') (hVO : V ≤ Subgroup.normalizer (O : Set G))
    (hle : V' ≤ V ⊔ O) (hcard : Nat.card V' = Nat.card V) :
    ∃ o ∈ O, conjSub o V' = V := by
  classical
  set H : Subgroup G := V ⊔ O with hH
  have hVH : V ≤ H := le_sup_left
  have hsyl : ∀ A : Subgroup G, A ≤ H → IsPGroup 2 A → Nat.card A = Nat.card V →
      ∃ P : Sylow 2 ↥H, (P : Subgroup ↥H) = A.subgroupOf H := by
    intro A hAH hA hcardA
    refine ⟨{ toSubgroup := A.subgroupOf H, isPGroup' := ?_, is_maximal' := ?_ }, rfl⟩
    · exact hA.comap_subtype
    · intro Q hQ hAQ
      have hBH : Q.map H.subtype ≤ H := Subgroup.map_subtype_le Q
      have hB : IsPGroup 2 (Q.map H.subtype) := hQ.map H.subtype
      have hAB : A ≤ Q.map H.subtype := by
        intro x hx
        exact ⟨⟨x, hAH hx⟩, hAQ (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
      have hcardB : Nat.card (Q.map H.subtype) ≤ Nat.card V :=
        card_le_of_le_sup_odd hO hVO hBH hB
      have hAeq : A = Q.map H.subtype :=
        Subgroup.eq_of_le_of_card_ge hAB (by rw [hcardA]; exact hcardB)
      have : Q = (Q.map H.subtype).subgroupOf H :=
        (Subgroup.comap_map_eq_self_of_injective H.subtype_injective Q).symm
      rw [this, ← hAeq]
  obtain ⟨P, hP⟩ := hsyl V hVH hV rfl
  obtain ⟨P', hP'⟩ := hsyl V' hle hV' hcard
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq ↥H P P'
  have hmemP : ∀ y : ↥H, y ∈ P ↔ (y : G) ∈ V := fun y =>
    (Subgroup.ext_iff.mp hP y).trans Subgroup.mem_subgroupOf
  have hmemP' : ∀ y : ↥H, y ∈ P' ↔ (y : G) ∈ V' := fun y =>
    (Subgroup.ext_iff.mp hP' y).trans Subgroup.mem_subgroupOf
  have h1 := Sylow.coe_smul (g := h) (P := P)
  rw [hh] at h1
  have hconj : conjSub (h : G) V = V' := by
    ext x
    constructor
    · intro hx
      rw [mem_conjSub_iff] at hx
      have hyH : (h : G)⁻¹ * x * h ∈ H := hVH hx
      have hxH : x ∈ H := by
        have : x = (h : G) * ((h : G)⁻¹ * x * h) * (h : G)⁻¹ := by group
        rw [this]
        exact H.mul_mem (H.mul_mem h.2 hyH) (H.inv_mem h.2)
      have hy : (⟨(h : G)⁻¹ * x * h, hyH⟩ : ↥H) ∈ P := (hmemP _).mpr hx
      have hxP' : (⟨x, hxH⟩ : ↥H) ∈ (P' : Set ↥H) := by
        rw [h1]
        refine Set.mem_smul_set.mpr ⟨_, hy, ?_⟩
        apply Subtype.ext
        simp [MulAut.conj_apply, mul_assoc]
      exact (hmemP' _).mp hxP'
    · intro hx
      have hxH : x ∈ H := hle hx
      have hx' : (⟨x, hxH⟩ : ↥H) ∈ (P' : Set ↥H) := (hmemP' _).mpr hx
      rw [h1] at hx'
      obtain ⟨y, hy, hyx⟩ := Set.mem_smul_set.mp hx'
      rw [mem_conjSub_iff]
      have hyV := (hmemP y).mp hy
      have hval : (h : G) * (y : G) * (h : G)⁻¹ = x := by
        have := congrArg Subtype.val hyx
        simpa [MulAut.conj_apply] using this
      have : (h : G)⁻¹ * x * h = (y : G) := by
        rw [← hval]
        group
      rw [this]
      exact hyV
  have hmem : (h : G) ∈ (↑(O ⊔ V) : Set G) := by
    rw [sup_comm]
    exact h.2
  rw [Subgroup.coe_mul_of_right_le_normalizer_left O V hVO] at hmem
  obtain ⟨o', ho', v, hv, hov⟩ := hmem
  have hVv : conjSub v V = V := by
    ext x
    rw [mem_conjSub_iff]
    constructor
    · intro hx
      have : x = v * (v⁻¹ * x * v) * v⁻¹ := by group
      rw [this]
      exact V.mul_mem (V.mul_mem hv hx) (V.inv_mem hv)
    · intro hx
      exact V.mul_mem (V.mul_mem (V.inv_mem hv) hx) hv
  have hV' : conjSub o' V = V' := by
    rw [← hconj, ← hov, conjSub_mul, hVv]
  refine ⟨o'⁻¹, O.inv_mem ho', ?_⟩
  rw [← hV', ← conjSub_mul, inv_mul_cancel, conjSub_one]

end Generic

variable (p f : ℕ) [Fact p.Prime]

@[expose] def LayerCenterFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), Std8 p f Ω K J S R T W z t →
      ¬ DConnected Ω → MuIsoWylD4 Ω W → dComp Ω K ≠ dstarComp Ω K →
        ¬ DConnected (T8.layerFamQ Ω (z * t)) → ∀ F : FrameData Ω W K J z t,
          F.vGroup ≤ zStarOf (T8.layerJoin Ω (z * t)) ∧
            zStarOf (T8.layerJoin Ω (z * t)) ≤
              F.vGroup ⊔ oddCoreOf (T8.layerJoin Ω (z * t))

variable {p f}

theorem layerFrattiniFact_of_center (hC : LayerCenterFact p f) : LayerFrattiniFact p f := by
  intro G _ _ _ Ω K J S R T W z t hs hdisc hμ hne hnconn F c hc
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  obtain ⟨h1, h2⟩ := hC G Ω K J S R T W z t hs hdisc hμ hne hnconn F
  obtain ⟨hVab, -⟩ := alphaOf_vGroup_eq hs F
  set Y := T8.layerJoin Ω (z * t) with hY
  have hcz : c ∈ T8.cenZ (z * t) := by
    rw [T8.cenZ_eq_centralizer]
    exact hc
  have hcY : conjSub c Y = Y := T8.layerJoin_conjSub_eq hΩ hcz
  have hle : conjSub c F.vGroup ≤ F.vGroup ⊔ oddCoreOf Y := by
    intro x hx
    rw [mem_conjSub_iff] at hx
    have hxz : x ∈ zStarOf Y := by
      have := conj_mem_zStarOf hcY (h1 hx)
      simpa [mul_assoc] using this
    exact h2 hxz
  have hcardV : Nat.card F.vGroup = 2 ^ 2 := hVab.1
  have hV : IsPGroup 2 F.vGroup := IsPGroup.of_card hcardV
  have hcard : Nat.card (conjSub c F.vGroup) = Nat.card F.vGroup := by
    unfold conjSub
    exact Subgroup.card_map_of_injective (MulAut.conj c).injective
  have hV' : IsPGroup 2 (conjSub c F.vGroup) := IsPGroup.of_card (hcard.trans hcardV)
  have hVc : ∀ v ∈ F.vGroup, v ∈ Subgroup.centralizer ({z * t} : Set G) := by
    intro v hv
    have hzt : z * t ∈ F.vGroup := by
      have h01 : F.zz 0 * F.zz 1 ∈ F.vGroup := Subgroup.subset_closure (Set.mem_insert _ _)
      rwa [F.hz0, F.hz1] at h01
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hv2 : (v * (z * t)) * (v * (z * t)) = 1 := hVab.2 _ (F.vGroup.mul_mem hv hzt)
    have hvv : v * v = 1 := hVab.2 v hv
    have hzz : (z * t) * (z * t) = 1 := hVab.2 _ hzt
    calc v * (z * t) = (v * (z * t))⁻¹ := (inv_eq_of_mul_eq_one_right hv2).symm
      _ = (z * t)⁻¹ * v⁻¹ := mul_inv_rev _ _
      _ = (z * t) * v := by
        rw [inv_eq_of_mul_eq_one_right hzz, inv_eq_of_mul_eq_one_right hvv]
  have hVO : F.vGroup ≤ Subgroup.normalizer (oddCoreOf Y : Set G) := by
    intro v hv
    have hvz : v ∈ T8.cenZ (z * t) := by
      rw [T8.cenZ_eq_centralizer]
      exact hVc v hv
    have hvY : conjSub v Y = Y := T8.layerJoin_conjSub_eq hΩ hvz
    rw [mem_normalizer_iff_conjSub_eq, ← Thompson.oddCoreOf_conjSub_eq, hvY]
  obtain ⟨o, ho, hoV⟩ :=
    exists_oddCore_conj_of_le_sup (oddCoreOf_odd_natCard Y) hV hV' hVO hle hcard
  exact ⟨o, ho, by rw [conjSub_mul, hoV]⟩

theorem c26_13_sc_of_center_singleFrame (hC : LayerCenterFact p f) (hSF : SingleFrameFact p f) :
    C26_13_sc p f :=
  c26_13_sc_of_frattini_singleFrame (layerFrattiniFact_of_center hC) hSF

end T8YY

end CFSG.ClassicalInvolution.Asc77
