module

public import CFSG.ClassicalInvolution.SmallCases.A7T22Alpha
public import CFSG.ClassicalInvolution.Asc77.AscT7BConst

public section

namespace CFSG.ClassicalInvolution.A7T22

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K K' K₃ : Subgroup G}
  {z u₁ u₂ u₃ : G}

theorem exists_third_sylow (hΩ : HypOmegaGen Ω) {L L' L₃ R₁ R₂ : Subgroup G} {z : G}
    (hL : L ∈ Ω) (hL' : L' ∈ Ω) (hL₃ : L₃ ∈ Ω) (hz : IsUniqueInvolution L z)
    (hz' : IsUniqueInvolution L' z) (hz₃ : IsUniqueInvolution L₃ z) (hne₃ : L₃ ≠ L)
    (hne₃' : L₃ ≠ L') (hR₁ : IsSylow2In R₁ L) (hR₂ : IsSylow2In R₂ L') (hc : Commutes R₁ R₂) :
    ∃ R₃ : Subgroup G, IsSylow2In R₃ L₃ ∧ Commutes R₁ R₃ ∧ Commutes R₂ R₃ := by
  have hRn : R₁ ≤ Subgroup.normalizer (R₂ : Set G) := T7A.le_normalizer_of_commutes hc.symm
  have hP2 : IsPGroup 2 ↥(R₁ ⊔ R₂) := hR₁.2.1.to_sup_of_normal_right' hR₂.2.1 hRn
  have hPN : R₁ ⊔ R₂ ≤ Subgroup.normalizer (L₃ : Set G) :=
    sup_le (hR₁.1.trans (Sec6Gen.le_normalizer_of_twin hΩ hL hL₃ hne₃.symm hz hz₃))
      (hR₂.1.trans (Sec6Gen.le_normalizer_of_twin hΩ hL' hL₃ hne₃'.symm hz' hz₃))
  obtain ⟨R₃, hR₃, hfix⟩ := exists_sylow_normalized hP2 hPN
  have hPnR₃ : R₁ ⊔ R₂ ≤ Subgroup.normalizer (R₃ : Set G) := fun r hr =>
    mem_normalizer_iff_conjSub_eq.mpr (hfix r hr)
  have hQ2 : IsPGroup 2 ↥((R₁ ⊔ R₂) ⊔ R₃) := hP2.to_sup_of_normal_right' hR₃.2.1 hPnR₃
  exact ⟨R₃, hR₃,
    Sec6Gen.commutes_of_twin_of_isPGroup hΩ hL hL₃ hne₃.symm hz hz₃ hR₁.1 hR₃.1
      (hQ2.to_le (sup_le_sup_right le_sup_left _)),
    Sec6Gen.commutes_of_twin_of_isPGroup hΩ hL' hL₃ hne₃'.symm hz' hz₃ hR₂.1 hR₃.1
      (hQ2.to_le (sup_le_sup_right le_sup_right _))⟩

namespace Hyp22G

theorem exists_sylow_triple (h : Hyp22G Ω K K' K₃ z u₁ u₂ u₃) :
    ∃ R R' R₃ : Subgroup G, IsSylow2In R K ∧ IsSylow2In R' K' ∧ IsSylow2In R₃ K₃ ∧
      u₁ ∈ R ∧ u₂ ∈ R' ∧ u₃ ∈ R₃ ∧ Commutes R R' ∧ Commutes R R₃ ∧ Commutes R' R₃ := by
  have hΩ := h.hyp
  have hK : K ∈ Ω := h.mem
  have hK' : K' ∈ Ω := h.hK'.1
  have hK₃ : K₃ ∈ Ω := h.hK₃.1
  have hz := h.hz
  have hz' := h.hzK'
  have hz₃ := h.hzK₃
  have hne : K' ≠ K := h.hne
  have hne₃ : K₃ ≠ K := h.hK₃K
  have hne₃' : K₃ ≠ K' := h.hK₃K'
  set Z₁ := Subgroup.zpowers u₁ with hZ₁
  set Z₂ := Subgroup.zpowers u₂ with hZ₂
  set Z₃ := Subgroup.zpowers u₃ with hZ₃
  have p₁ : IsPGroup 2 ↥Z₁ := T7A.isPGroup_zpowers_of_orderOf_four h.hu₁.2
  have p₂ : IsPGroup 2 ↥Z₂ := T7A.isPGroup_zpowers_of_orderOf_four h.hu₂.2
  have p₃ : IsPGroup 2 ↥Z₃ := T7A.isPGroup_zpowers_of_orderOf_four h.hu₃.2
  have cm : ∀ {a b : G}, a * b = b * a → Commutes (Subgroup.zpowers a) (Subgroup.zpowers b) := by
    intro a b hab x hx y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_zpow (show Commute a b from hab) i j).eq
  have hP : IsPGroup 2 ↥((Z₁ ⊔ Z₂) ⊔ Z₃) :=
    T7B.isPGroup_sup_three p₁ p₂ p₃ (cm h.comm₁₂) (cm h.comm₁₃) (cm h.comm₂₃)
  set P := (Z₁ ⊔ Z₂) ⊔ Z₃ with hPdef
  have hz₁P : u₁ ∈ P := (le_sup_left.trans le_sup_left : Z₁ ≤ P) (Subgroup.mem_zpowers u₁)
  have hz₂P : u₂ ∈ P := (le_sup_right.trans le_sup_left : Z₂ ≤ P) (Subgroup.mem_zpowers u₂)
  have hz₃P : u₃ ∈ P := (le_sup_right : Z₃ ≤ P) (Subgroup.mem_zpowers u₃)
  have nT : ∀ {A B : Subgroup G}, A ∈ Ω → B ∈ Ω → A ≠ B → IsUniqueInvolution A z →
      IsUniqueInvolution B z → A ≤ Subgroup.normalizer (B : Set G) := fun hA hB hAB hzA hzB =>
    Sec6Gen.le_normalizer_of_twin hΩ hA hB hAB hzA hzB
  have hPK : P ≤ Subgroup.normalizer (K : Set G) :=
    sup_le (sup_le ((Subgroup.zpowers_le.mpr h.hu₁.1).trans Subgroup.le_normalizer)
      ((Subgroup.zpowers_le.mpr h.hu₂.1).trans (nT hK' hK hne hz' hz)))
      ((Subgroup.zpowers_le.mpr h.hu₃.1).trans (nT hK₃ hK hne₃ hz₃ hz))
  have hPK' : P ≤ Subgroup.normalizer (K' : Set G) :=
    sup_le (sup_le ((Subgroup.zpowers_le.mpr h.hu₁.1).trans (nT hK hK' hne.symm hz hz'))
      ((Subgroup.zpowers_le.mpr h.hu₂.1).trans Subgroup.le_normalizer))
      ((Subgroup.zpowers_le.mpr h.hu₃.1).trans (nT hK₃ hK' hne₃' hz₃ hz'))
  have hPK₃ : P ≤ Subgroup.normalizer (K₃ : Set G) :=
    sup_le (sup_le ((Subgroup.zpowers_le.mpr h.hu₁.1).trans (nT hK hK₃ hne₃.symm hz hz₃))
      ((Subgroup.zpowers_le.mpr h.hu₂.1).trans (nT hK' hK₃ hne₃'.symm hz' hz₃)))
      ((Subgroup.zpowers_le.mpr h.hu₃.1).trans Subgroup.le_normalizer)
  obtain ⟨R, hR, hRfix⟩ := exists_sylow_normalized hP hPK
  have hPR : P ≤ Subgroup.normalizer (R : Set G) := fun x hx =>
    mem_normalizer_iff_conjSub_eq.mpr (hRfix x hx)
  have hu₁R : u₁ ∈ R := T7B.mem_of_normalizes hR p₁ h.hu₁.1 (hRfix u₁ hz₁P)
  have hP₁ : IsPGroup 2 ↥(P ⊔ R) := hP.to_sup_of_normal_right' hR.2.1 hPR
  have hPR₁ : P ⊔ R ≤ Subgroup.normalizer (K' : Set G) :=
    sup_le hPK' (hR.1.trans (nT hK hK' hne.symm hz hz'))
  obtain ⟨R', hR', hR'fix⟩ := exists_sylow_normalized hP₁ hPR₁
  have hPR' : P ⊔ R ≤ Subgroup.normalizer (R' : Set G) := fun x hx =>
    mem_normalizer_iff_conjSub_eq.mpr (hR'fix x hx)
  have hPle₁ : P ≤ P ⊔ R := le_sup_left
  have hu₂R' : u₂ ∈ R' := T7B.mem_of_normalizes hR' p₂ h.hu₂.1 (hR'fix u₂ (hPle₁ hz₂P))
  have hP₂ : IsPGroup 2 ↥((P ⊔ R) ⊔ R') := hP₁.to_sup_of_normal_right' hR'.2.1 hPR'
  have hPR₂ : (P ⊔ R) ⊔ R' ≤ Subgroup.normalizer (K₃ : Set G) :=
    sup_le (sup_le hPK₃ (hR.1.trans (nT hK hK₃ hne₃.symm hz hz₃)))
      (hR'.1.trans (nT hK' hK₃ hne₃'.symm hz' hz₃))
  obtain ⟨R₃, hR₃, hR₃fix⟩ := exists_sylow_normalized hP₂ hPR₂
  have hPR₃ : (P ⊔ R) ⊔ R' ≤ Subgroup.normalizer (R₃ : Set G) := fun x hx =>
    mem_normalizer_iff_conjSub_eq.mpr (hR₃fix x hx)
  have hPle₂ : P ⊔ R ≤ (P ⊔ R) ⊔ R' := le_sup_left
  have hu₃R₃ : u₃ ∈ R₃ :=
    T7B.mem_of_normalizes hR₃ p₃ h.hu₃.1 (hR₃fix u₃ (hPle₂ (hPle₁ hz₃P)))
  have hQ : IsPGroup 2 ↥(((P ⊔ R) ⊔ R') ⊔ R₃) := hP₂.to_sup_of_normal_right' hR₃.2.1 hPR₃
  have hRQ : R ≤ ((P ⊔ R) ⊔ R') ⊔ R₃ := le_sup_right.trans (le_sup_left.trans le_sup_left)
  have hR'Q : R' ≤ ((P ⊔ R) ⊔ R') ⊔ R₃ := le_sup_right.trans le_sup_left
  have hR₃Q : R₃ ≤ ((P ⊔ R) ⊔ R') ⊔ R₃ := le_sup_right
  refine ⟨R, R', R₃, hR, hR', hR₃, hu₁R, hu₂R', hu₃R₃, ?_, ?_, ?_⟩
  · exact Sec6Gen.commutes_of_twin_of_isPGroup hΩ hK hK' hne.symm hz hz' hR.1 hR'.1
      (hQ.to_le (sup_le hRQ hR'Q))
  · exact Sec6Gen.commutes_of_twin_of_isPGroup hΩ hK hK₃ hne₃.symm hz hz₃ hR.1 hR₃.1
      (hQ.to_le (sup_le hRQ hR₃Q))
  · exact Sec6Gen.commutes_of_twin_of_isPGroup hΩ hK' hK₃ hne₃'.symm hz' hz₃ hR'.1 hR₃.1
      (hQ.to_le (sup_le hR'Q hR₃Q))

theorem of_sylows (h : Hyp22G Ω K K' K₃ z u₁ u₂ u₃) {L L' L₃ R₁ R₂ R₃ : Subgroup G} {x y w : G}
    (hL : L ∈ twinSet Ω K) (hL' : L' ∈ twinSet Ω K) (hL₃ : L₃ ∈ twinSet Ω K) (h12 : L' ≠ L)
    (h13 : L₃ ≠ L) (h23 : L₃ ≠ L') (hR₁ : IsSylow2In R₁ L) (hR₂ : IsSylow2In R₂ L')
    (hR₃ : IsSylow2In R₃ L₃) (c12 : Commutes R₁ R₂) (c13 : Commutes R₁ R₃)
    (c23 : Commutes R₂ R₃) (hx : x ∈ R₁) (hy : y ∈ R₂) (hw : w ∈ R₃) (ox : orderOf x = 4)
    (oy : orderOf y = 4) (ow : orderOf w = 4) : Hyp22G Ω L L' L₃ z x y w := by
  have hzL := isUniqueInvolution_of_mem_twinSet h.hz hL
  have hcore : Hyp22Core Ω L L' L₃ z x y w :=
    ⟨h.hyp, hL.1, hL'.1, hL₃.1, hzL, isUniqueInvolution_of_mem_twinSet h.hz hL',
      isUniqueInvolution_of_mem_twinSet h.hz hL₃, h12, h13, h23, ⟨hR₁.1 hx, ox⟩, ⟨hR₂.1 hy, oy⟩,
      ⟨hR₃.1 hw, ow⟩, c12 x hx y hy, c13 x hx w hw, c23 y hy w hw⟩
  refine Hyp22G.of_core hcore ?_
  rw [twinSet_eq_of_mem_twinSet h.hz hL]
  exact h.subn

theorem exists_replace_third (h : Hyp22G Ω K K' K₃ z u₁ u₂ u₃) {M : Subgroup G}
    (hM : M ∈ twinSet Ω K) (hMK : M ≠ K) (hMK' : M ≠ K') :
    ∃ w : G, Hyp22G Ω K K' M z u₁ u₂ w := by
  have hzM : IsUniqueInvolution M z := isUniqueInvolution_of_mem_twinSet h.hz hM
  obtain ⟨R, R', -, hR, hR', -, h₁, h₂, -, c₁₂, -, -⟩ := h.exists_sylow_triple
  obtain ⟨R_M, hRM, c₁, c₂⟩ := exists_third_sylow h.hyp h.mem h.hK'.1 hM.1 h.hz h.hzK' hzM
    hMK hMK' hR hR' c₁₂
  obtain ⟨w, hw, o₃⟩ := exists_orderOf_eq_four_of_isSylow2In h.hyp hM.1 hRM
  exact ⟨w, h.of_sylows (mem_twinSet_self h.mem h.hz) h.hK' hM h.hne hMK hMK' hR hR' hRM c₁₂ c₁
    c₂ h₁ h₂ hw h.hu₁.2 h.hu₂.2 o₃⟩

theorem twin_le_normalizer_alpha (hα : AlphaConst Ω z) (h : Hyp22G Ω K K' K₃ z u₁ u₂ u₃)
    {L : Subgroup G} (hL : L ∈ twinSet Ω K) :
    L ≤ Subgroup.normalizer (alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) : Set G) := by
  by_cases hLK : L = K
  · rw [hLK]
    exact (h.le_normalizer_alpha hα).1
  by_cases hLK' : L = K'
  · rw [hLK']
    exact (h.le_normalizer_alpha hα).2.1
  obtain ⟨w, hw⟩ := h.exists_replace_third hL hLK hLK'
  exact hw.third_le_normalizer_alpha hα

theorem const_on_family (hα : AlphaConst Ω z) (h : Hyp22G Ω K K' K₃ z u₁ u₂ u₃)
    {M₀ : Set (Subgroup G)} (hM₀ : M₀ ⊆ twinSet Ω K) (hKM : K ∈ M₀) (hK'M : K' ∈ M₀)
    (hK₃M : K₃ ∈ M₀) {Q : Subgroup G} (hQ : IsPGroup 2 ↥Q)
    (hSyl : ∀ M ∈ M₀, IsSylow2In (Q ⊓ M) M) :
    ∀ M₁ ∈ M₀, ∀ M₂ ∈ M₀, ∀ N₁ ∈ M₀, ∀ N₂ ∈ M₀, M₁ ≠ M₂ → N₁ ≠ N₂ →
      ∀ x ∈ Q ⊓ M₁, ∀ y ∈ Q ⊓ M₂, ∀ x' ∈ Q ⊓ N₁, ∀ y' ∈ Q ⊓ N₂,
        orderOf x = 4 → orderOf y = 4 → orderOf x' = 4 → orderOf y' = 4 →
        alphaOf (Subgroup.closure ({x * y, z} : Set G)) =
          alphaOf (Subgroup.closure ({x' * y', z} : Set G)) := by
  have hΩ := h.hyp
  have hzM : ∀ M ∈ M₀, IsUniqueInvolution M z := fun M hM =>
    isUniqueInvolution_of_mem_twinSet h.hz (hM₀ hM)
  have hcomm : ∀ M ∈ M₀, ∀ M' ∈ M₀, M ≠ M' → Commutes (Q ⊓ M) (Q ⊓ M') := by
    intro M hM M' hM' hne
    exact Sec6Gen.commutes_of_twin_of_isPGroup hΩ (hM₀ hM).1 (hM₀ hM').1 hne (hzM M hM)
      (hzM M' hM') inf_le_right inf_le_right (hQ.to_le (sup_le inf_le_left inf_le_left))
  let E : Type := Subgroup G × G
  let valid : E → Prop := fun a => a.1 ∈ M₀ ∧ a.2 ∈ Q ⊓ a.1 ∧ orderOf a.2 = 4
  let F : E → E → Subgroup G := fun a b => alphaOf (Subgroup.closure ({a.2 * b.2, z} : Set G))
  have key := T7B.const_of_triple (m := fun a : E => a.1) valid F
    (by
      intro a b ha hb hne
      show alphaOf _ = alphaOf _
      rw [hcomm a.1 ha.1 b.1 hb.1 hne a.2 ha.2.1 b.2 hb.2.1])
    (by
      intro a b c ha hb hc hab hbc hac
      have hd := h.of_sylows (hM₀ ha.1) (hM₀ hb.1) (hM₀ hc.1) (Ne.symm hab) (Ne.symm hac)
        (Ne.symm hbc) (hSyl a.1 ha.1) (hSyl b.1 hb.1) (hSyl c.1 hc.1)
        (hcomm a.1 ha.1 b.1 hb.1 hab) (hcomm a.1 ha.1 c.1 hc.1 hac)
        (hcomm b.1 hb.1 c.1 hc.1 hbc) ha.2.1 hb.2.1 hc.2.1 ha.2.2 hb.2.2 hc.2.2
      exact (hd.alpha_23 hα).symm)
    (by
      intro a b ha hb
      obtain ⟨M, hM, hMa, hMb⟩ : ∃ M ∈ M₀, M ≠ a.1 ∧ M ≠ b.1 := by
        rcases T7B.exists_ne_of_three (a := a.1) (b := b.1) h.hne h.hK₃K h.hK₃K' with
          hh | hh | hh
        · exact ⟨K, hKM, hh.1, hh.2⟩
        · exact ⟨K', hK'M, hh.1, hh.2⟩
        · exact ⟨K₃, hK₃M, hh.1, hh.2⟩
      obtain ⟨w, hw, o⟩ := exists_orderOf_eq_four_of_isSylow2In hΩ (hM₀ hM).1 (hSyl M hM)
      exact ⟨(M, w), ⟨hM, hw, o⟩, hMa, hMb⟩)
  intro M₁ hM₁ M₂ hM₂ N₁ hN₁ N₂ hN₂ hne hne' x hx y hy x' hx' y' hy' ox oy ox' oy'
  exact key (M₁, x) (M₂, y) (N₁, x') (N₂, y') ⟨hM₁, hx, ox⟩ ⟨hM₂, hy, oy⟩ ⟨hN₁, hx', ox'⟩
    ⟨hN₂, hy', oy'⟩ hne hne'

theorem alpha_eq_of_datum (hα : AlphaConst Ω z) {L L' L₃ : Subgroup G} {x₁ x₂ x₃ : G}
    (h : Hyp22G Ω K K' K₃ z u₁ u₂ u₃) (h' : Hyp22G Ω L L' L₃ z x₁ x₂ x₃) :
    alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) =
      alphaOf (Subgroup.closure ({x₁ * x₂, z} : Set G)) := by
  have hΩ := h.hyp
  have hz : IsUniqueInvolution K z := h.hz
  have hKV : K ∈ twinSet Ω K := mem_twinSet_self h.mem hz
  have hK'V : K' ∈ twinSet Ω K := h.hK'
  have hK₃V : K₃ ∈ twinSet Ω K := h.hK₃
  have hLV : L ∈ twinSet Ω K := ⟨h'.mem, z, hz, h'.hz⟩
  have hL'V : L' ∈ twinSet Ω K := ⟨h'.hK'.1, z, hz, h'.hzK'⟩
  have hL₃V : L₃ ∈ twinSet Ω K := ⟨h'.hK₃.1, z, hz, h'.hzK₃⟩
  have hVL : twinSet Ω L = twinSet Ω K := twinSet_eq_of_mem_twinSet hz hLV
  set X : Subgroup G := ⨆ M ∈ twinSet Ω K, M with hX
  have hXM : ∀ M ∈ twinSet Ω K, M ≤ X := fun M hM => le_iSup₂_of_le M hM le_rfl
  have hzV : ∀ M ∈ twinSet Ω K, IsUniqueInvolution M z := fun M hM =>
    isUniqueInvolution_of_mem_twinSet hz hM
  have hXz : X ≤ Subgroup.centralizer ({z} : Set G) := iSup₂_le fun M hM m hm =>
    Subgroup.mem_centralizer_singleton_iff.mpr (e189_commute_of_mem (hzV M hM) hm).symm
  have hXN : ∀ M ∈ twinSet Ω K, X ≤ Subgroup.normalizer (M : Set G) := by
    intro M hM
    refine iSup₂_le fun M' hM' => ?_
    by_cases hMM : M' = M
    · rw [hMM]
      exact Subgroup.le_normalizer
    · exact Sec6Gen.le_normalizer_of_twin hΩ hM'.1 hM.1 hMM (hzV M' hM') (hzV M hM)
  have hXα' : X ≤ Subgroup.normalizer
      (alphaOf (Subgroup.closure ({x₁ * x₂, z} : Set G)) : Set G) :=
    iSup₂_le fun M hM => h'.twin_le_normalizer_alpha hα (by rw [hVL]; exact hM)
  obtain ⟨R, R', R₃, hR, hR', hR₃, h₁, h₂, h₃, c12, c13, c23⟩ := h.exists_sylow_triple
  obtain ⟨S, S', S₃, hS, hS', hS₃, k₁, k₂, k₃, d12, d13, d23⟩ := h'.exists_sylow_triple
  have hT2 := T7B.isPGroup_sup_three hR.2.1 hR'.2.1 hR₃.2.1 c12 c13 c23
  have hT2' := T7B.isPGroup_sup_three hS.2.1 hS'.2.1 hS₃.2.1 d12 d13 d23
  obtain ⟨Q, hQ, hTQ⟩ := IsSylow2In.exists_ge hT2
    (sup_le (sup_le (hR.1.trans (hXM K hKV)) (hR'.1.trans (hXM K' hK'V)))
      (hR₃.1.trans (hXM K₃ hK₃V)))
  obtain ⟨Q', hQ', hTQ'⟩ := IsSylow2In.exists_ge hT2'
    (sup_le (sup_le (hS.1.trans (hXM L hLV)) (hS'.1.trans (hXM L' hL'V)))
      (hS₃.1.trans (hXM L₃ hL₃V)))
  obtain ⟨g, hgX, hgQ⟩ := exists_conjSub_eq_of_isSylow2In hQ' hQ
  have hgz : g * z * g⁻¹ = z := by
    have := Subgroup.mem_centralizer_singleton_iff.mp (hXz hgX)
    calc g * z * g⁻¹ = (z * g) * g⁻¹ := by rw [this]
      _ = z := by group
  have hgM : ∀ M ∈ twinSet Ω K, conjSub g M = M := fun M hM =>
    mem_normalizer_iff_conjSub_eq.mp (hXN M hM hgX)
  have hαg : alphaOf (Subgroup.closure ({(g * x₁ * g⁻¹) * (g * x₂ * g⁻¹), z} : Set G)) =
      alphaOf (Subgroup.closure ({x₁ * x₂, z} : Set G)) := by
    have e : (g * x₁ * g⁻¹) * (g * x₂ * g⁻¹) = g * (x₁ * x₂) * g⁻¹ := by group
    have e2 := T7A.conjSub_closure_pair g (x₁ * x₂) z
    rw [hgz] at e2
    rw [e, ← e2, alphaOf_conjSub]
    exact mem_normalizer_iff_conjSub_eq.mp (hXα' hgX)
  have hQ2 : IsPGroup 2 ↥Q := hQ.2.1
  have hSylK : ∀ {M R₀ : Subgroup G}, IsSylow2In R₀ M → R₀ ≤ Q → IsSylow2In (Q ⊓ M) M := by
    intro M R₀ hR₀ hRQ
    have : Q ⊓ M = R₀ := hR₀.eq_of_le (hQ2.to_le inf_le_left) inf_le_right (le_inf hRQ hR₀.1)
    rw [this]
    exact hR₀
  have hSylL : ∀ {M R₀ : Subgroup G}, M ∈ twinSet Ω K → IsSylow2In R₀ M → R₀ ≤ Q' →
      IsSylow2In (conjSub g R₀) M ∧ conjSub g R₀ ≤ Q ⊓ M := by
    intro M R₀ hM hR₀ hRQ
    have h1 : IsSylow2In (conjSub g R₀) M := by
      have := hR₀.conj g
      rwa [hgM M hM] at this
    refine ⟨h1, le_inf ?_ h1.1⟩
    rw [← hgQ]
    exact conjSub_mono hRQ
  have hQL : ∀ {M R₀ : Subgroup G}, M ∈ twinSet Ω K → IsSylow2In R₀ M → R₀ ≤ Q' →
      IsSylow2In (Q ⊓ M) M := by
    intro M R₀ hM hR₀ hRQ
    obtain ⟨h1, h2'⟩ := hSylL hM hR₀ hRQ
    have : Q ⊓ M = conjSub g R₀ :=
      h1.eq_of_le (hQ2.to_le inf_le_left) inf_le_right h2'
    rw [this]
    exact h1
  have hRK : R ≤ Q := (le_sup_left.trans le_sup_left).trans hTQ
  have hRK' : R' ≤ Q := (le_sup_right.trans le_sup_left).trans hTQ
  have hRK₃ : R₃ ≤ Q := le_sup_right.trans hTQ
  have hSL : S ≤ Q' := (le_sup_left.trans le_sup_left).trans hTQ'
  have hSL' : S' ≤ Q' := (le_sup_right.trans le_sup_left).trans hTQ'
  have hSL₃ : S₃ ≤ Q' := le_sup_right.trans hTQ'
  set M₀ : Set (Subgroup G) := {K, K', K₃, L, L', L₃} with hM₀
  have hM₀V : M₀ ⊆ twinSet Ω K := by
    intro M hM
    rcases hM with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hKV
    · exact hK'V
    · exact hK₃V
    · exact hLV
    · exact hL'V
    · exact hL₃V
  have hSyl : ∀ M ∈ M₀, IsSylow2In (Q ⊓ M) M := by
    intro M hM
    rcases hM with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hSylK hR hRK
    · exact hSylK hR' hRK'
    · exact hSylK hR₃ hRK₃
    · exact hQL hLV hS hSL
    · exact hQL hL'V hS' hSL'
    · exact hQL hL₃V hS₃ hSL₃
  have hconj₁ : g * x₁ * g⁻¹ ∈ Q ⊓ L := (hSylL hLV hS hSL).2 (conj_mem_conjSub k₁)
  have hconj₂ : g * x₂ * g⁻¹ ∈ Q ⊓ L' := (hSylL hL'V hS' hSL').2 (conj_mem_conjSub k₂)
  have hu₁ : u₁ ∈ Q ⊓ K := ⟨hRK h₁, hR.1 h₁⟩
  have hu₂ : u₂ ∈ Q ⊓ K' := ⟨hRK' h₂, hR'.1 h₂⟩
  have ho₁ : orderOf (g * x₁ * g⁻¹) = 4 := by rw [T7B.orderOf_conj']; exact h'.hu₁.2
  have ho₂ : orderOf (g * x₂ * g⁻¹) = 4 := by rw [T7B.orderOf_conj']; exact h'.hu₂.2
  have hmain := h.const_on_family hα hM₀V (by simp [hM₀]) (by simp [hM₀]) (by simp [hM₀]) hQ2
    hSyl K (by simp [hM₀]) K' (by simp [hM₀]) L (by simp [hM₀]) L' (by simp [hM₀]) h.hne.symm
    h'.hne.symm u₁ hu₁ u₂ hu₂ _ hconj₁ _ hconj₂ h.hu₁.2 h.hu₂.2 ho₁ ho₂
  rw [hmain, hαg]

theorem centralizer_le_normalizer_alpha (hα : AlphaConst Ω z)
    (h : Hyp22G Ω K K' K₃ z u₁ u₂ u₃) :
    Subgroup.centralizer ({z} : Set G) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) : Set G) := by
  intro c hc
  have hcz : c * z * c⁻¹ = z := by
    have := Subgroup.mem_centralizer_singleton_iff.mp hc
    calc c * z * c⁻¹ = (z * c) * c⁻¹ := by rw [this]
      _ = z := by group
  have hd := h.conj hcz
  have heq := alpha_eq_of_datum hα hd h
  have e : (c * u₁ * c⁻¹) * (c * u₂ * c⁻¹) = c * (u₁ * u₂) * c⁻¹ := by group
  have e2 := T7A.conjSub_closure_pair c (u₁ * u₂) z
  rw [hcz] at e2
  rw [e, ← e2, alphaOf_conjSub] at heq
  exact mem_normalizer_iff_conjSub_eq.mpr heq

end Hyp22G

end CFSG.ClassicalInvolution.A7T22
