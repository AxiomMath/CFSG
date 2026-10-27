module

public import CFSG.ClassicalInvolution.Asc77.AscT7BAlpha
public import CFSG.ClassicalInvolution.Asc77.AscT7BSetup

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

namespace T7B

variable {G : Type} [Group G]

theorem conjSub_closure_three (g a b c : G) :
    conjSub g (Subgroup.closure ({a, b, c} : Set G)) =
      Subgroup.closure ({g * a * g⁻¹, g * b * g⁻¹, g * c * g⁻¹} : Set G) := by
  unfold conjSub
  rw [MonoidHom.map_closure, Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton]
  rfl

theorem orderOf_conj' (g x : G) : orderOf (g * x * g⁻¹) = orderOf x := by
  simpa using MulEquiv.orderOf_eq (MulAut.conj g) x

variable [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

omit [Finite G] in
theorem mem_of_normalizes {K R : Subgroup G} {x : G} (hR : IsSylow2In R K)
    (hx2 : IsPGroup 2 ↥(Subgroup.zpowers x)) (hxK : x ∈ K) (hfix : conjSub x R = R) : x ∈ R := by
  have hn : Subgroup.zpowers x ≤ Subgroup.normalizer (R : Set G) :=
    Subgroup.zpowers_le.mpr (mem_normalizer_iff_conjSub_eq.mpr hfix)
  have h2 : IsPGroup 2 ↥(Subgroup.zpowers x ⊔ R) := hx2.to_sup_of_normal_right' hR.2.1 hn
  have heq := hR.eq_of_le h2 (sup_le (Subgroup.zpowers_le.mpr hxK) hR.1) le_sup_right
  have : Subgroup.zpowers x ≤ R := heq ▸ le_sup_left
  exact this (Subgroup.mem_zpowers x)

theorem exists_sylow_triple {K K' K₃ : Subgroup G} {z u₁ u₂ u₃ : G}
    (h : Hyp22 p f Ω K K' K₃ z u₁ u₂ u₃) :
    ∃ R R' R₃ : Subgroup G, IsSylow2In R K ∧ IsSylow2In R' K' ∧ IsSylow2In R₃ K₃ ∧
      u₁ ∈ R ∧ u₂ ∈ R' ∧ u₃ ∈ R₃ ∧ Commutes R R' ∧ Commutes R R₃ ∧ Commutes R' R₃ := by
  have hΩ : HypOmegaMod p f Ω := h.std.stand.hyp
  have hK : K ∈ Ω := h.std.stand.mem
  have hK' : K' ∈ Ω := h.std.hK'.1
  have hK₃ : K₃ ∈ Ω := h.hK₃.1
  have hz := h.std.hz
  have hz' := h.hzK'
  have hz₃ := h.hzK₃
  have hne : K' ≠ K := h.std.hne
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
  have c12 : Commutes Z₁ Z₂ := cm h.comm₁₂
  have c13 : Commutes Z₁ Z₃ := cm h.comm₁₃
  have c23 : Commutes Z₂ Z₃ := cm h.comm₂₃
  have hP12 : IsPGroup 2 ↥(Z₁ ⊔ Z₂) :=
    p₁.to_sup_of_normal_right' p₂ (T7A.le_normalizer_of_commutes c12.symm)
  have hP : IsPGroup 2 ↥((Z₁ ⊔ Z₂) ⊔ Z₃) :=
    hP12.to_sup_of_normal_right' p₃ (sup_le (T7A.le_normalizer_of_commutes c13.symm)
      (T7A.le_normalizer_of_commutes c23.symm))
  set P := (Z₁ ⊔ Z₂) ⊔ Z₃ with hPdef
  have hZ₁P : Z₁ ≤ P := le_sup_left.trans le_sup_left
  have hZ₂P : Z₂ ≤ P := le_sup_right.trans le_sup_left
  have hZ₃P : Z₃ ≤ P := le_sup_right
  have hz₁P : u₁ ∈ P := hZ₁P (Subgroup.mem_zpowers u₁)
  have hz₂P : u₂ ∈ P := hZ₂P (Subgroup.mem_zpowers u₂)
  have hz₃P : u₃ ∈ P := hZ₃P (Subgroup.mem_zpowers u₃)
  have nK₁ : K ≤ Subgroup.normalizer (K' : Set G) :=
    hΩ.le_normalizer_of_twin hK hK' hne.symm hz hz'
  have nK₂ : K ≤ Subgroup.normalizer (K₃ : Set G) :=
    hΩ.le_normalizer_of_twin hK hK₃ hne₃.symm hz hz₃
  have nK₃ : K' ≤ Subgroup.normalizer (K₃ : Set G) :=
    hΩ.le_normalizer_of_twin hK' hK₃ hne₃'.symm hz' hz₃
  have nK₄ : K' ≤ Subgroup.normalizer (K : Set G) := hΩ.le_normalizer_of_twin hK' hK hne hz' hz
  have nK₅ : K₃ ≤ Subgroup.normalizer (K : Set G) :=
    hΩ.le_normalizer_of_twin hK₃ hK hne₃ hz₃ hz
  have nK₆ : K₃ ≤ Subgroup.normalizer (K' : Set G) :=
    hΩ.le_normalizer_of_twin hK₃ hK' hne₃' hz₃ hz'
  have hPK : P ≤ Subgroup.normalizer (K : Set G) :=
    sup_le (sup_le ((Subgroup.zpowers_le.mpr h.hu₁.1).trans Subgroup.le_normalizer)
      ((Subgroup.zpowers_le.mpr h.hu₂.1).trans nK₄))
      ((Subgroup.zpowers_le.mpr h.hu₃.1).trans nK₅)
  have hPK' : P ≤ Subgroup.normalizer (K' : Set G) :=
    sup_le (sup_le ((Subgroup.zpowers_le.mpr h.hu₁.1).trans nK₁)
      ((Subgroup.zpowers_le.mpr h.hu₂.1).trans Subgroup.le_normalizer))
      ((Subgroup.zpowers_le.mpr h.hu₃.1).trans nK₆)
  have hPK₃ : P ≤ Subgroup.normalizer (K₃ : Set G) :=
    sup_le (sup_le ((Subgroup.zpowers_le.mpr h.hu₁.1).trans nK₂)
      ((Subgroup.zpowers_le.mpr h.hu₂.1).trans nK₃))
      ((Subgroup.zpowers_le.mpr h.hu₃.1).trans Subgroup.le_normalizer)
  obtain ⟨R, hR, hRfix⟩ := exists_sylow_normalized hP hPK
  have hPR : P ≤ Subgroup.normalizer (R : Set G) := fun x hx =>
    mem_normalizer_iff_conjSub_eq.mpr (hRfix x hx)
  have hu₁R : u₁ ∈ R := mem_of_normalizes hR p₁ h.hu₁.1 (hRfix u₁ hz₁P)
  have hP₁ : IsPGroup 2 ↥(P ⊔ R) := hP.to_sup_of_normal_right' hR.2.1 hPR
  have hPR₁ : P ⊔ R ≤ Subgroup.normalizer (K' : Set G) := sup_le hPK' (hR.1.trans nK₁)
  obtain ⟨R', hR', hR'fix⟩ := exists_sylow_normalized hP₁ hPR₁
  have hPR' : P ⊔ R ≤ Subgroup.normalizer (R' : Set G) := fun x hx =>
    mem_normalizer_iff_conjSub_eq.mpr (hR'fix x hx)
  have hPle₁ : P ≤ P ⊔ R := le_sup_left
  have hu₂R' : u₂ ∈ R' := mem_of_normalizes hR' p₂ h.hu₂.1 (hR'fix u₂ (hPle₁ hz₂P))
  have hP₂ : IsPGroup 2 ↥((P ⊔ R) ⊔ R') := hP₁.to_sup_of_normal_right' hR'.2.1 hPR'
  have hPR₂ : (P ⊔ R) ⊔ R' ≤ Subgroup.normalizer (K₃ : Set G) :=
    sup_le (sup_le hPK₃ (hR.1.trans nK₂)) (hR'.1.trans nK₃)
  obtain ⟨R₃, hR₃, hR₃fix⟩ := exists_sylow_normalized hP₂ hPR₂
  have hPR₃ : (P ⊔ R) ⊔ R' ≤ Subgroup.normalizer (R₃ : Set G) := fun x hx =>
    mem_normalizer_iff_conjSub_eq.mpr (hR₃fix x hx)
  have hPle₂ : P ⊔ R ≤ (P ⊔ R) ⊔ R' := le_sup_left
  have hu₃R₃ : u₃ ∈ R₃ :=
    mem_of_normalizes hR₃ p₃ h.hu₃.1 (hR₃fix u₃ (hPle₂ (hPle₁ hz₃P)))
  have hQ : IsPGroup 2 ↥(((P ⊔ R) ⊔ R') ⊔ R₃) := hP₂.to_sup_of_normal_right' hR₃.2.1 hPR₃
  have hRQ : R ≤ ((P ⊔ R) ⊔ R') ⊔ R₃ := le_sup_right.trans (le_sup_left.trans le_sup_left)
  have hR'Q : R' ≤ ((P ⊔ R) ⊔ R') ⊔ R₃ := le_sup_right.trans le_sup_left
  have hR₃Q : R₃ ≤ ((P ⊔ R) ⊔ R') ⊔ R₃ := le_sup_right
  refine ⟨R, R', R₃, hR, hR', hR₃, hu₁R, hu₂R', hu₃R₃, ?_, ?_, ?_⟩
  · exact hΩ.commutes_of_twin_of_isPGroup hK hK' hne.symm hz hz' hR.1 hR'.1
      (hQ.to_le (sup_le hRQ hR'Q))
  · exact hΩ.commutes_of_twin_of_isPGroup hK hK₃ hne₃.symm hz hz₃ hR.1 hR₃.1
      (hQ.to_le (sup_le hRQ hR₃Q))
  · exact hΩ.commutes_of_twin_of_isPGroup hK' hK₃ hne₃'.symm hz' hz₃ hR'.1 hR₃.1
      (hQ.to_le (sup_le hR'Q hR₃Q))

end T7B

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {K K' K₃ : Subgroup G} {z u₁ u₂ u₃ : G}

namespace Hyp22

theorem exists_replace_third (h : Hyp22 p f Ω K K' K₃ z u₁ u₂ u₃) {M : Subgroup G}
    (hM : M ∈ twinSet Ω K) (hMK : M ≠ K) (hMK' : M ≠ K') :
    ∃ w : G, Hyp22 p f Ω K K' M z u₁ u₂ w := by
  have hΩ : HypOmegaMod p f Ω := h.std.stand.hyp
  have hp : p ≠ 2 := h.std.stand.odd
  have hq : 5 ≤ p ^ f := h.std.stand.five
  have hzM : IsUniqueInvolution M z := isUniqueInvolution_of_mem_twinSet h.std.hz hM
  obtain ⟨R, R', -, hR, hR', -, h₁, h₂, -, c₁₂, -, -⟩ := T7B.exists_sylow_triple h
  obtain ⟨R_M, hRM, c₁, c₂⟩ := T7B.exists_third_sylow hp hq hΩ h.std.stand.mem h.std.hK'.1 hM.1
    h.std.hz h.hzK' hzM hMK hMK' hR hR' c₁₂
  obtain ⟨w, hw, o₃⟩ :=
    hΩ.exists_orderOf_eq_four_of_mem_RSet hp (mem_RSet_of_isSylow2In hM.1 hRM)
  exact ⟨w, T7B.hyp22_of_sylows h.std h.perp hM hMK hMK' hR hR' hRM c₁₂ c₁ c₂ h₁ h₂ hw
    h.hu₁.2 h.hu₂.2 o₃⟩

section Twins

variable [IsSimpleGroup G]

theorem twin_le_normalizer_alpha (h2 : C22_2 p f) (h : Hyp22 p f Ω K K' K₃ z u₁ u₂ u₃)
    {L : Subgroup G} (hL : L ∈ twinSet Ω K) :
    L ≤ Subgroup.normalizer (alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) : Set G) := by
  by_cases hLK : L = K
  · rw [hLK]
    exact (h.le_normalizer_alpha h2).1
  by_cases hLK' : L = K'
  · rw [hLK']
    exact (h.le_normalizer_alpha h2).2.1
  obtain ⟨w, hw⟩ := h.exists_replace_third hL hLK hLK'
  exact hw.third_le_normalizer_alpha h2

end Twins

theorem conj (h : Hyp22 p f Ω K K' K₃ z u₁ u₂ u₃) {g : G} (hg : g * z * g⁻¹ = z) :
    Hyp22 p f Ω (conjSub g K) (conjSub g K') (conjSub g K₃) z (g * u₁ * g⁻¹) (g * u₂ * g⁻¹)
      (g * u₃ * g⁻¹) := by
  have hΩ : HypOmegaMod p f Ω := h.std.stand.hyp
  have hp : p ≠ 2 := h.std.stand.odd
  have hq : 5 ≤ p ^ f := h.std.stand.five
  have hK : K ∈ Ω := h.std.stand.mem
  have hcK : conjSub g K ∈ Ω := hΩ.conjInvariant g K hK
  have hzc : IsUniqueInvolution (conjSub g K) z := by
    have := h.std.hz.conj g
    rwa [hg] at this
  have hmem : conjSub g K ∈ twinSet Ω K := ⟨hcK, z, h.std.hz, hzc⟩
  have hperp : KPerp Ω (conjSub g K) = KPerp Ω K :=
    ((l6_3 p f hp hq G Ω hΩ K hK _ hmem).1).symm
  have htw : twinSet Ω (conjSub g K) = twinSet Ω K := twinSet_eq_of_mem_twinSet h.std.hz hmem
  have hB : Subgroup.closure ({(g * u₁ * g⁻¹) * (g * u₂ * g⁻¹), z,
        (g * u₂ * g⁻¹) * (g * u₃ * g⁻¹)} : Set G) =
      conjSub g (Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G)) := by
    rw [T7B.conjSub_closure_three, hg]
    have e1 : (g * u₁ * g⁻¹) * (g * u₂ * g⁻¹) = g * (u₁ * u₂) * g⁻¹ := by group
    have e2 : (g * u₂ * g⁻¹) * (g * u₃ * g⁻¹) = g * (u₂ * u₃) * g⁻¹ := by group
    rw [e1, e2]
  refine
    { std := ⟨h.std.stand.of_mem hcK, h.std.disconnected, hzc,
        twinSet_conj hΩ.conjInvariant h.std.hK' g, fun e => h.std.hne (conjSub_injective g e),
        h.std.cex⟩
      perp := by rw [hperp, htw]; exact h.perp
      hK₃ := twinSet_conj hΩ.conjInvariant h.hK₃ g
      hK₃K := fun e => h.hK₃K (conjSub_injective g e)
      hK₃K' := fun e => h.hK₃K' (conjSub_injective g e)
      hu₁ := ⟨conj_mem_conjSub h.hu₁.1, by rw [T7B.orderOf_conj']; exact h.hu₁.2⟩
      hu₂ := ⟨conj_mem_conjSub h.hu₂.1, by rw [T7B.orderOf_conj']; exact h.hu₂.2⟩
      hu₃ := ⟨conj_mem_conjSub h.hu₃.1, by rw [T7B.orderOf_conj']; exact h.hu₃.2⟩
      hB := ?_ }
  rw [hB]
  refine ⟨by rw [natCard_conjSub]; exact h.hB.1, fun x hx => ?_⟩
  have hx' := mem_conjSub_iff.mp hx
  have := h.hB.2 _ hx'
  calc x * x = g * ((g⁻¹ * x * g) * (g⁻¹ * x * g)) * g⁻¹ := by group
    _ = 1 := by rw [this]; group

end Hyp22

end CFSG.ClassicalInvolution.Asc77
