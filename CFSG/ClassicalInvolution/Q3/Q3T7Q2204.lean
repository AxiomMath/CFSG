module

public import CFSG.ClassicalInvolution.Q3.Q3T7Q22M11
public import CFSG.ClassicalInvolution.Q3.Q3T7Q22Shape
public import CFSG.ClassicalInvolution.Q3.Q3T7Q2203

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
namespace T7B
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.T7B
variable {G : Type} [Group G]
variable [Finite G] {Ω : Set (Subgroup G)}

theorem exists_sylow_triple
    {K K' K₃ : Subgroup G} {z u₁ u₂ u₃ : G}
    (h : Q3T8.Asc77.Hyp22 Ω K K' K₃ z u₁ u₂ u₃) :
    ∃ R R' R₃ : Subgroup G, IsSylow2In R K ∧ IsSylow2In R' K' ∧ IsSylow2In R₃ K₃ ∧
      u₁ ∈ R ∧ u₂ ∈ R' ∧ u₃ ∈ R₃ ∧ Commutes R R' ∧ Commutes R R₃ ∧ Commutes R' R₃ := by
  have hΩ : Q3T8.Asc77.HypOmegaMod Ω := h.std.stand.hyp
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
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' K₃ : Subgroup G} {z u₁ u₂ u₃ : G}
namespace Hyp22
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.Hyp22

theorem exists_replace_third
    (h : Q3T8.Asc77.Hyp22 Ω K K' K₃ z u₁ u₂ u₃) {M : Subgroup G}
    (hM : M ∈ twinSet Ω K) (hMK : M ≠ K) (hMK' : M ≠ K') :
    ∃ w : G, Q3T8.Asc77.Hyp22 Ω K K' M z u₁ u₂ w := by
  have hΩ : Q3T7M.HM Ω := h.std.stand.modU
  have hzM : IsUniqueInvolution M z := isUniqueInvolution_of_mem_twinSet h.std.hz hM
  obtain ⟨R, R', -, hR, hR', -, h₁, h₂, -, c₁₂, -, -⟩ := Q3T8.Asc77.T7B.exists_sylow_triple h
  obtain ⟨R_M, hRM, c₁, c₂⟩ := Q3T8.Asc77.T7B.exists_third_sylow hΩ h.std.stand.mem h.std.hK'.1 hM.1
    h.std.hz h.hzK' hzM hMK hMK' hR hR' c₁₂
  obtain ⟨w, hw, o₃⟩ :=
    hΩ.exists_orderOf_eq_four_of_mem_RSet (mem_RSet_of_isSylow2In hM.1 hRM)
  exact ⟨w, Q3T8.Asc77.T7B.hyp22_of_sylows h.std h.perp hM hMK hMK' hR hR' hRM c₁₂ c₁ c₂ h₁ h₂ hw
    h.hu₁.2 h.hu₂.2 o₃⟩
section Twins
variable [IsSimpleGroup G]

theorem twin_le_normalizer_alpha
    (h2 : Q3T8.Asc77.C22_2) (h : Q3T8.Asc77.Hyp22 Ω K K' K₃ z u₁ u₂ u₃)
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

theorem conj
    (h : Q3T8.Asc77.Hyp22 Ω K K' K₃ z u₁ u₂ u₃) {g : G} (hg : g * z * g⁻¹ = z) :
    Q3T8.Asc77.Hyp22 Ω (conjSub g K) (conjSub g K') (conjSub g K₃) z (g * u₁ * g⁻¹) (g * u₂ * g⁻¹)
      (g * u₃ * g⁻¹) := by
  have hΩ : Q3T7M.HM Ω := h.std.stand.modU
  have hK : K ∈ Ω := h.std.stand.mem
  have hcK : conjSub g K ∈ Ω := hΩ.conjInvariant g K hK
  have hzc : IsUniqueInvolution (conjSub g K) z := by
    have := h.std.hz.conj g
    rwa [hg] at this
  have hmem : conjSub g K ∈ twinSet Ω K := ⟨hcK, z, h.std.hz, hzc⟩
  have hperp : KPerp Ω (conjSub g K) = KPerp Ω K :=
    ((CFSG.ClassicalInvolution.Q3.Q3T7M.l6_3 G Ω hΩ K hK _ hmem).1).symm
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
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
namespace T7B
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.T7B

theorem perp_of_twin
    {K K' L : Subgroup G} {z : G} (hs : Q3T8.Asc77.Std7 Ω K K' z)
    (hperp : KPerp Ω K = twinSet Ω K) (hL : L ∈ twinSet Ω K) : KPerp Ω L = twinSet Ω L := by
  have h1 := (CFSG.ClassicalInvolution.Q3.Q3T7M.l6_3 G Ω hs.stand.modU K hs.stand.mem L hL).1
  rw [← h1, twinSet_eq_of_mem_twinSet hs.hz hL]
  exact hperp
end T7B
namespace Hyp22
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.Hyp22
variable [IsSimpleGroup G]

theorem const_on_family
    (h2 : Q3T8.Asc77.C22_2) {K K' K₃ : Subgroup G} {z : G}
    (hs : Q3T8.Asc77.Std7 Ω K K' z) (hperp : KPerp Ω K = twinSet Ω K)
    (hK₃K : K₃ ≠ K) (hK₃K' : K₃ ≠ K')
    {M₀ : Set (Subgroup G)} (hM₀ : M₀ ⊆ twinSet Ω K) (hKM : K ∈ M₀) (hK'M : K' ∈ M₀)
    (hK₃M : K₃ ∈ M₀) {Q : Subgroup G} (hQ : IsPGroup 2 ↥Q)
    (hSyl : ∀ M ∈ M₀, IsSylow2In (Q ⊓ M) M) :
    ∀ M₁ ∈ M₀, ∀ M₂ ∈ M₀, ∀ N₁ ∈ M₀, ∀ N₂ ∈ M₀, M₁ ≠ M₂ → N₁ ≠ N₂ →
      ∀ x ∈ Q ⊓ M₁, ∀ y ∈ Q ⊓ M₂, ∀ x' ∈ Q ⊓ N₁, ∀ y' ∈ Q ⊓ N₂,
        orderOf x = 4 → orderOf y = 4 → orderOf x' = 4 → orderOf y' = 4 →
        alphaOf (Subgroup.closure ({x * y, z} : Set G)) =
          alphaOf (Subgroup.closure ({x' * y', z} : Set G)) := by
  have hΩ : Q3T7M.HM Ω := hs.stand.modU
  have hz : IsUniqueInvolution K z := hs.hz
  have hKe : K' ≠ K := hs.hne
  have hzM : ∀ M ∈ M₀, IsUniqueInvolution M z := fun M hM =>
    isUniqueInvolution_of_mem_twinSet hz (hM₀ hM)
  
  have hcomm : ∀ M ∈ M₀, ∀ M' ∈ M₀, M ≠ M' → Commutes (Q ⊓ M) (Q ⊓ M') := by
    intro M hM M' hM' hne
    exact hΩ.commutes_of_twin_of_isPGroup (hM₀ hM).1 (hM₀ hM').1 hne (hzM M hM) (hzM M' hM')
      inf_le_right inf_le_right
      (hQ.to_le (sup_le inf_le_left inf_le_left))
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
      have hLa : a.1 ∈ twinSet Ω K := hM₀ ha.1
      have hLb : b.1 ∈ twinSet Ω K := hM₀ hb.1
      have hLc : c.1 ∈ twinSet Ω K := hM₀ hc.1
      have hs' : Q3T8.Asc77.Std7 Ω a.1 b.1 z := Q3T8.Asc77.Std7.of_twin hs hLa hLb (Ne.symm hab)
      have hperp' : KPerp Ω a.1 = twinSet Ω a.1 := Q3T8.Asc77.T7B.perp_of_twin hs hperp hLa
      have hLc' : c.1 ∈ twinSet Ω a.1 := by
        rw [twinSet_eq_of_mem_twinSet hz hLa]; exact hLc
      have hd := Q3T8.Asc77.T7B.hyp22_of_sylows hs' hperp' hLc' (Ne.symm hac) (Ne.symm hbc)
        (hSyl a.1 ha.1) (hSyl b.1 hb.1) (hSyl c.1 hc.1)
        (hcomm a.1 ha.1 b.1 hb.1 hab) (hcomm a.1 ha.1 c.1 hc.1 hac)
        (hcomm b.1 hb.1 c.1 hc.1 hbc) ha.2.1 hb.2.1 hc.2.1 ha.2.2 hb.2.2 hc.2.2
      exact (hd.alpha_23 h2).symm)
    (by
      intro a b ha hb
      obtain ⟨M, hM, hMa, hMb⟩ : ∃ M ∈ M₀, M ≠ a.1 ∧ M ≠ b.1 := by
        rcases T7B.exists_ne_of_three (a := a.1) (b := b.1) hKe hK₃K hK₃K' with h | h | h
        · exact ⟨K, hKM, h.1, h.2⟩
        · exact ⟨K', hK'M, h.1, h.2⟩
        · exact ⟨K₃, hK₃M, h.1, h.2⟩
      obtain ⟨w, hw, o⟩ := hΩ.exists_orderOf_eq_four_of_mem_RSet
        (mem_RSet_of_isSylow2In (hM₀ hM).1 (hSyl M hM))
      exact ⟨(M, w), ⟨hM, hw, o⟩, hMa, hMb⟩)
  intro M₁ hM₁ M₂ hM₂ N₁ hN₁ N₂ hN₂ hne hne' x hx y hy x' hx' y' hy' ox oy ox' oy'
  exact key (M₁, x) (M₂, y) (N₁, x') (N₂, y') ⟨hM₁, hx, ox⟩ ⟨hM₂, hy, oy⟩ ⟨hN₁, hx', ox'⟩
    ⟨hN₂, hy', oy'⟩ hne hne'

theorem alpha_eq_of_datum
    (h2 : Q3T8.Asc77.C22_2) {K K' K₃ L L' L₃ : Subgroup G}
    {z u₁ u₂ u₃ x₁ x₂ x₃ : G} (h : Q3T8.Asc77.Hyp22 Ω K K' K₃ z u₁ u₂ u₃)
    (h' : Q3T8.Asc77.Hyp22 Ω L L' L₃ z x₁ x₂ x₃) :
    alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) =
      alphaOf (Subgroup.closure ({x₁ * x₂, z} : Set G)) := by
  have hΩ : Q3T7M.HM Ω := h.std.stand.modU
  have hz : IsUniqueInvolution K z := h.std.hz
  have hKV : K ∈ twinSet Ω K := mem_twinSet_self h.std.stand.mem hz
  have hK'V : K' ∈ twinSet Ω K := h.std.hK'
  have hK₃V : K₃ ∈ twinSet Ω K := h.hK₃
  have hLV : L ∈ twinSet Ω K := ⟨h'.std.stand.mem, z, hz, h'.std.hz⟩
  have hL'V : L' ∈ twinSet Ω K := ⟨h'.std.hK'.1, z, hz, h'.hzK'⟩
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
    · exact hΩ.le_normalizer_of_twin hM'.1 hM.1 hMM (hzV M' hM') (hzV M hM)
  have hXα : X ≤ Subgroup.normalizer
      (alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) : Set G) :=
    iSup₂_le fun M hM => h.twin_le_normalizer_alpha h2 hM
  have hXα' : X ≤ Subgroup.normalizer
      (alphaOf (Subgroup.closure ({x₁ * x₂, z} : Set G)) : Set G) :=
    iSup₂_le fun M hM => h'.twin_le_normalizer_alpha h2 (by rw [hVL]; exact hM)
  obtain ⟨R, R', R₃, hR, hR', hR₃, h₁, h₂, h₃, c12, c13, c23⟩ := Q3T8.Asc77.T7B.exists_sylow_triple
      h
  obtain ⟨S, S', S₃, hS, hS', hS₃, k₁, k₂, k₃, d12, d13, d23⟩ := Q3T8.Asc77.T7B.exists_sylow_triple
      h'
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
  have h'' := h'.conj hgz
  rw [hgM L hLV, hgM L' hL'V, hgM L₃ hL₃V] at h''
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
  have hRQ : ∀ {M₁ : Subgroup G}, M₁ ≤ (R ⊔ R') ⊔ R₃ → M₁ ≤ Q := fun hM => hM.trans hTQ
  have hSQ : ∀ {M₁ : Subgroup G}, M₁ ≤ (S ⊔ S') ⊔ S₃ → M₁ ≤ Q' := fun hM => hM.trans hTQ'
  have hRK : R ≤ Q := hRQ (le_sup_left.trans le_sup_left)
  have hRK' : R' ≤ Q := hRQ (le_sup_right.trans le_sup_left)
  have hRK₃ : R₃ ≤ Q := hRQ le_sup_right
  have hSL : S ≤ Q' := hSQ (le_sup_left.trans le_sup_left)
  have hSL' : S' ≤ Q' := hSQ (le_sup_right.trans le_sup_left)
  have hSL₃ : S₃ ≤ Q' := hSQ le_sup_right
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
  have hmain := Q3T8.Asc77.Hyp22.const_on_family h2 h.std h.perp h.hK₃K h.hK₃K' hM₀V
    (by simp [hM₀]) (by simp [hM₀]) (by simp [hM₀]) hQ2 hSyl K (by simp [hM₀]) K'
    (by simp [hM₀]) L (by simp [hM₀]) L' (by simp [hM₀]) h.std.hne.symm h'.std.hne.symm u₁ hu₁
    u₂ hu₂ _ hconj₁ _ hconj₂ h.hu₁.2 h.hu₂.2 ho₁ ho₂
  rw [hmain, hαg]

theorem centralizer_le_normalizer_alpha
    (h2 : Q3T8.Asc77.C22_2) {K K' K₃ : Subgroup G}
    {z u₁ u₂ u₃ : G} (h : Q3T8.Asc77.Hyp22 Ω K K' K₃ z u₁ u₂ u₃) :
    Subgroup.centralizer ({z} : Set G) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) : Set G) := by
  intro c hc
  have hcz : c * z * c⁻¹ = z := by
    have := Subgroup.mem_centralizer_singleton_iff.mp hc
    calc c * z * c⁻¹ = (z * c) * c⁻¹ := by rw [this]
      _ = z := by group
  have hd := h.conj hcz
  have heq := Q3T8.Asc77.Hyp22.alpha_eq_of_datum h2 hd h
  have e : (c * u₁ * c⁻¹) * (c * u₂ * c⁻¹) = c * (u₁ * u₂) * c⁻¹ := by group
  have e2 := T7A.conjSub_closure_pair c (u₁ * u₂) z
  rw [hcz] at e2
  rw [e, ← e2, alphaOf_conjSub] at heq
  exact mem_normalizer_iff_conjSub_eq.mpr heq
end Hyp22
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
    CFSG.ClassicalInvolution.Disconnected
namespace Hyp22Setting
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.Hyp22Setting
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' K₃ : Subgroup G} {z u₁ u₂ u₃ : G}

theorem hzK'
    (h : Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃) : IsUniqueInvolution K' z :=
  isUniqueInvolution_of_mem_twinSet h.hz h.hK'

theorem hzK₃
    (h : Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃) : IsUniqueInvolution K₃ z :=
  isUniqueInvolution_of_mem_twinSet h.hz h.hK₃

theorem sq₁
    (h : Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃) : u₁ * u₁ = z :=
  T7A.sq_eq_of_orderOf_four h.hz h.hu₁.1 h.hu₁.2

theorem sq₂
    (h : Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃) : u₂ * u₂ = z :=
  T7A.sq_eq_of_orderOf_four h.hzK' h.hu₂.1 h.hu₂.2

theorem sq₃
    (h : Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃) : u₃ * u₃ = z :=
  T7A.sq_eq_of_orderOf_four h.hzK₃ h.hu₃.1 h.hu₃.2

theorem comm_z₁
    (h : Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃) : z * u₁ = u₁ * z :=
  e189_commute_of_mem h.hz h.hu₁.1

theorem comm_z₂
    (h : Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃) : z * u₂ = u₂ * z :=
  e189_commute_of_mem h.hzK' h.hu₂.1

theorem comm_z₃
    (h : Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃) : z * u₃ = u₃ * z :=
  e189_commute_of_mem h.hzK₃ h.hu₃.1

theorem sq_12
    (h : Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃) : (u₁ * u₂) * (u₁ * u₂) = 1 :=
  h.hB.2 _ T7B.mem_closure_fst

theorem sq_23
    (h : Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃) : (u₂ * u₃) * (u₂ * u₃) = 1 :=
  h.hB.2 _ T7B.mem_closure_thd

theorem comm₁₂
    (h : Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃) : u₁ * u₂ = u₂ * u₁ :=
  T7B.comm_of_mul_self_eq_one h.sq₁ h.sq₂ h.hz.sq h.comm_z₁ h.sq_12

theorem comm₂₃
    (h : Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃) : u₂ * u₃ = u₃ * u₂ :=
  T7B.comm_of_mul_self_eq_one h.sq₂ h.sq₃ h.hz.sq h.comm_z₂ h.sq_23

theorem eq_13
    (h : Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃) :
    u₁ * u₃ = z * ((u₁ * u₂) * (u₂ * u₃)) := by
  have h1 : (u₁ * u₂) * (u₂ * u₃) = u₁ * z * u₃ := by
    calc (u₁ * u₂) * (u₂ * u₃) = u₁ * (u₂ * u₂) * u₃ := by group
      _ = u₁ * z * u₃ := by rw [h.sq₂]
  calc u₁ * u₃ = (z * z) * (u₁ * u₃) := by rw [h.hz.sq, one_mul]
    _ = z * (z * u₁) * u₃ := by group
    _ = z * (u₁ * z) * u₃ := by rw [h.comm_z₁]
    _ = z * ((u₁ * u₂) * (u₂ * u₃)) := by rw [h1]; group

theorem mem_B_13
    (h : Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃) :
    u₁ * u₃ ∈ Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G) := by
  rw [h.eq_13]
  exact Subgroup.mul_mem _ T7B.mem_closure_snd
    (Subgroup.mul_mem _ T7B.mem_closure_fst T7B.mem_closure_thd)

theorem isElemAbelian_B
    (h : Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃) :
    IsElemAbelian 2 (Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G)) := by
  have hsq : ∀ x ∈ Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G), x * x = 1 := h.hB.2
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · have hab : ((a : G) * b) * ((a : G) * b) = 1 := hsq _ (Subgroup.mul_mem _ a.2 b.2)
    have h1 : (a : G)⁻¹ = a := inv_eq_of_mul_eq_one_right (hsq a a.2)
    have h2 : (b : G)⁻¹ = b := inv_eq_of_mul_eq_one_right (hsq b b.2)
    have h3 : (a : G) * b = ((a : G) * b)⁻¹ := (inv_eq_of_mul_eq_one_right hab).symm
    rw [mul_inv_rev, h1, h2] at h3
    exact h3
  · rw [pow_two]
    exact hsq x hx
end Hyp22Setting
namespace T7S22
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.T7S22
open scoped commutatorElement
variable {G : Type} [Group G] [Finite G]

theorem mul_ne_one_of_twins
    {Ω : Set (Subgroup G)} (hΩ : Q3T8.Asc77.HypOmegaMod Ω) {K₁ K₂ :
    Subgroup G}
    {z a b : G} (hK₁ : K₁ ∈ Ω) (hK₂ : K₂ ∈ Ω) (hne : K₁ ≠ K₂) (hz : IsUniqueInvolution K₁ z)
    (haK : a ∈ K₁) (hbK : b ∈ K₂) (hb4 : orderOf b = 4) : a * b ≠ 1 ∧ a * b ≠ z := by
  have key : b ∈ K₁ → False := by
    intro hb
    have hle : Subgroup.zpowers b ≤ K₁ ⊓ K₂ :=
      Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨hb, hbK⟩)
    have hdvd : 4 ∣ Nat.card ↥(K₁ ⊓ K₂) := by
      have := Subgroup.card_dvd_of_le hle
      rwa [Nat.card_zpowers, hb4] at this
    have hpos : Nat.card ↥(K₁ ⊓ K₂) ≠ 0 := Nat.card_pos.ne'
    have h2 : 2 ≤ padicValNat 2 (Nat.card ↥(K₁ ⊓ K₂)) :=
      (padicValNat_dvd_iff_le (p := 2) hpos).mp (by simpa using hdvd)
    have h1 := (hΩ.omega4 K₁ hK₁ K₂ hK₂ hne).1
    omega
  refine ⟨fun h1 => key ?_, fun h1 => key ?_⟩
  · have : b = a⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [this]
    exact K₁.inv_mem haK
  · have : b = a⁻¹ * z := by
      rw [← h1]
      group
    rw [this]
    exact K₁.mul_mem (K₁.inv_mem haK) hz.mem
end T7S22

theorem hyp22Hyp51z
    [Fact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.Hyp22Hyp51z] :
    Q3T8.Asc77.Hyp22Hyp51z := Fact.out
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
namespace S16
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.S16
set_option linter.unusedSectionVars false
open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.LieType.Universal CFSG.ClassicalInvolution.Asc77.FrameVertex
    CFSG.ClassicalInvolution.Disconnected
section Connected
variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem hall_of_connected
    (hΦ : Q3T8.Asc77.HypOmegaMod Φ) (hconn : DConnected Φ)
    (hstar : ∀ B ∈ Φ, ∀ J ∈ Φ, J ∈ omegaStarNbr Φ B →
      ∃ w, IsUniqueInvolution B w ∧ IsUniqueInvolution J w)
    {A : Subgroup X} (hA : A ∈ Φ) {z : X} (hzA : IsUniqueInvolution A z) :
    ∀ B ∈ Φ, IsUniqueInvolution B z := by
  have hpath : ∀ N, Relation.ReflTransGen
      (fun M N : Subgroup X => N ∈ Φ ∧ dAdj Φ M N) A N → N ∈ Φ ∧ IsUniqueInvolution N z := by
    intro N hN
    induction hN with
    | refl => exact ⟨hA, hzA⟩
    | tail hpre hstep ih =>
      rename_i M N'
      obtain ⟨hN'Φ, hadj⟩ := hstep
      obtain ⟨hMΦ, hzM⟩ := ih
      refine ⟨hN'Φ, ?_⟩
      rcases hadj with h | h
      · obtain ⟨w, hw1, hw2⟩ :=
          hstar M hMΦ N' hN'Φ (Q3T8.Asc77.T3.omegaNbr_subset_omegaStarNbr hΦ M h)
        have := hzM.eq hw1
        subst this
        exact hw2
      · obtain ⟨w, hw1, hw2⟩ :=
          hstar N' hN'Φ M hMΦ (Q3T8.Asc77.T3.omegaNbr_subset_omegaStarNbr hΦ N' h)
        have := hzM.eq hw2
        subst this
        exact hw1
  intro B hB
  exact (hpath B (hconn A hA B hB)).2

theorem false_of_s3_shape
    (hΦ : Q3T8.Asc77.HypOmegaMod Φ)
    (hstar : ∀ B ∈ Φ, ∀ J ∈ Φ, J ∈ omegaStarNbr Φ B →
      ∃ w, IsUniqueInvolution B w ∧ IsUniqueInvolution J w)
    (hs3 : MuTab.ShapeS3 Φ) : False := by
  obtain ⟨hDE, B, hB, J, hJ⟩ := hs3
  obtain ⟨w, hw1, hw2⟩ := hstar B hB J hJ.1 hJ
  rcases CFSG.ClassicalInvolution.Q3.Q3T7M.mem_kPerp_of_twin hΦ hJ.1 hB hw2 hw1 with h | h
  · exact hJ.2.1 h
  · exact hDE B hB J hJ.1 (Or.inl h)

theorem false_of_t6_section [Fact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S16.M11NoInverted3] (hR1 :
    Q3T8.Asc77.S16.Z2NoD8) {n : ℕ}
    (hBelow : Q3T8.Generic.CITBelowU n) (hlt : Nat.card X < n) (hS : Q3T8.Asc77.TransSection Φ)
    (htop : (⊤ : Subgroup X) ∉ Φ) (hDE : DEdgeless Φ)
    (hstar : ∀ B ∈ Φ, ∀ J ∈ Φ, J ∈ omegaStarNbr Φ B →
      ∃ w, IsUniqueInvolution B w ∧ IsUniqueInvolution J w)
    {H : Type} [Group H] [Finite H] (ι : X →* H) (hι : Function.Injective ι) (a v : H)
    (ha : ∀ x : X, a * ι x * a⁻¹ ∈ ι.range ∧ a⁻¹ * ι x * a ∈ ι.range)
    (hv : ∀ x : X, v * ι x * v⁻¹ ∈ ι.range ∧ v⁻¹ * ι x * v ∈ ι.range)
    {A : Subgroup X} (hA : A ∈ Φ) {z : X} (hzA : IsUniqueInvolution A z)
    (haA : ∀ x ∈ A, ∃ n ∈ oddCoreOf A, a * ι x * a⁻¹ = ι (n * x))
    (hvA : ∀ x ∈ A, ∃ n ∈ oddCoreOf A, v * ι x * v⁻¹ = ι (n * x))
    (ha2 : a * a = ι z) (hv2 : v * v = 1) (hav : v * a * v⁻¹ = a⁻¹) : False := by
  classical
  have hΦ : Q3T7M.HM Φ := hS.hyp
  have h6 := Q3T8.Asc77.thm6SectBelow'_of_citBelow (ih8SmallEdge 3) hBelow X hlt Φ hS.toGen
    ⟨A, hA⟩ htop hDE
  have hmain : ∀ {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {k : ℕ}, HasLieType 3 1 Φ t k →
      ∀ (D : Q3T8.Asc77.OmegaLie Φ) (hcard : D.card = 1) (i : Fin D.card), D.tag i = t → D.rank i =
          k →
        (MuTab.muKind (piSign 3 1) t k = .s3 ∨
          ((t = .PSL ∧ k = 3 ∧ 3 % 4 = 3) ∨ (t = .PSU ∧ k = 3 ∧ 3 % 4 = 1))) →
        False := by
    intro t k hL D hcard i ht hk hkind
    rcases hkind with hk3 | hZ2
    · exact Q3T8.Asc77.S16.false_of_s3_shape hΦ hstar
        ⟨hDE, Q3T8.Asc77.MuTab.exists_starEdge_of_s3 hS ⟨A, hA⟩ hL hk3⟩
    · refine Q3T8.Asc77.S16.false_of_z2_section hR1 hS.toGen D hcard i ?_ ι hι a v ha hv hA hzA haA
        hvA
        ha2 hv2 hav
      rw [ht, hk]
      exact hZ2
  rcases h6 with hL | hL | hL | hL | hM
  · obtain ⟨D, hcard, i, ht, hk⟩ := hL
    by_cases hπ : piSign 3 1 = true
    · exact hmain ⟨D, hcard, i, ht, hk⟩ D hcard i ht hk
        (Or.inl (by simp [MuTab.muKind, hπ]))
    · have hπf : piSign 3 1 = false := by simpa using hπ
      exact hmain ⟨D, hcard, i, ht, hk⟩ D hcard i ht hk
        (Or.inr (Or.inl ⟨rfl, rfl, MuTab.pow_mod_four_of_piSign_false (by norm_num) hπf⟩))
  · obtain ⟨D, hcard, i, ht, hk⟩ := hL
    by_cases hπ : piSign 3 1 = true
    · exact hmain ⟨D, hcard, i, ht, hk⟩ D hcard i ht hk
        (Or.inr (Or.inr ⟨rfl, rfl, MuTab.piSign_true_iff.mp hπ⟩))
    · have hπf : piSign 3 1 = false := by simpa using hπ
      exact hmain ⟨D, hcard, i, ht, hk⟩ D hcard i ht hk
        (Or.inl (by simp [MuTab.muKind, hπf]))
  · obtain ⟨D, hcard, i, ht, hk⟩ := hL
    exact hmain ⟨D, hcard, i, ht, hk⟩ D hcard i ht hk (Or.inl (by simp [MuTab.muKind]))
  · obtain ⟨D, hcard, i, ht, hk⟩ := hL
    exact hmain ⟨D, hcard, i, ht, hk⟩ D hcard i ht hk (Or.inl (by simp [MuTab.muKind]))
  · exact Q3T8.Asc77.S16.false_of_m11_section hS htop hM ι hι a v ha hv hA hzA haA hvA ha2 hv2 hav

end Connected
end S16
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' K₃ : Subgroup G} {z u₁ u₂ u₃ : G}
namespace Hyp22
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.Hyp22

theorem stdCent_of_twin
    (h : Q3T8.Asc77.Hyp22 Ω K K' K₃ z u₁ u₂ u₃) {H : Subgroup G}
    (hz : Subgroup.centralizer ({z} : Set G) ≤ H)
    (htwin : ∀ L ∈ twinSet Ω K, ∀ L' ∈ twinSet Ω K, L' ≠ L → ∀ R₁ R₂ : Subgroup G,
      IsSylow2In R₁ L → IsSylow2In R₂ L' → Commutes R₁ R₂ → ∀ x ∈ R₁, ∀ y ∈ R₂,
        orderOf x = 4 → orderOf y = 4 → Subgroup.centralizer ({x * y} : Set G) ≤ H) :
    StdCent Ω K H z where
  z_le := hz
  nonTwin := by
    intro L hL J hJ z' hz' hzz
    exfalso
    have hJperp : J ∈ KPerp Ω L := Set.mem_insert_of_mem _ hJ
    have hJt : J ∈ twinSet Ω K := by
      have := Q3T8.Asc77.T7B.perp_of_twin h.std h.perp hL
      rw [this, twinSet_eq_of_mem_twinSet h.std.hz hL] at hJperp
      exact hJperp
    have hJz : IsUniqueInvolution J z := isUniqueInvolution_of_mem_twinSet h.std.hz hJt
    exact hzz (hz'.eq hJz)
  twin := htwin

theorem exists_datum_of_pair
    (h : Q3T8.Asc77.Hyp22 Ω K K' K₃ z u₁ u₂ u₃) {L L' : Subgroup G}
    (hL : L ∈ twinSet Ω K) (hL' : L' ∈ twinSet Ω K) (hne : L' ≠ L) {R₁ R₂ : Subgroup G}
    (hR₁ : IsSylow2In R₁ L) (hR₂ : IsSylow2In R₂ L') (hc : Commutes R₁ R₂) {x y : G}
    (hx : x ∈ R₁) (hy : y ∈ R₂) (ox : orderOf x = 4) (oy : orderOf y = 4) :
    ∃ (L₃ : Subgroup G) (w : G), Q3T8.Asc77.Hyp22 Ω L L' L₃ z x y w := by
  have hΩ : Q3T7M.HM Ω := h.std.stand.modU
  have hKV : K ∈ twinSet Ω K := mem_twinSet_self h.std.stand.mem h.std.hz
  obtain ⟨L₃, hL₃, hL₃L, hL₃L'⟩ : ∃ L₃ ∈ twinSet Ω K, L₃ ≠ L ∧ L₃ ≠ L' := by
    rcases T7B.exists_ne_of_three (a := L) (b := L') h.std.hne h.hK₃K h.hK₃K' with hh | hh | hh
    · exact ⟨K, hKV, hh.1, hh.2⟩
    · exact ⟨K', h.std.hK', hh.1, hh.2⟩
    · exact ⟨K₃, h.hK₃, hh.1, hh.2⟩
  have hzL : IsUniqueInvolution L z := isUniqueInvolution_of_mem_twinSet h.std.hz hL
  have hzL' : IsUniqueInvolution L' z := isUniqueInvolution_of_mem_twinSet h.std.hz hL'
  have hzL₃ : IsUniqueInvolution L₃ z := isUniqueInvolution_of_mem_twinSet h.std.hz hL₃
  obtain ⟨R₃, hR₃, c₁, c₂⟩ := Q3T8.Asc77.T7B.exists_third_sylow hΩ hL.1 hL'.1 hL₃.1 hzL hzL' hzL₃
    hL₃L hL₃L' hR₁ hR₂ hc
  obtain ⟨w, hw, ow⟩ :=
    hΩ.exists_orderOf_eq_four_of_mem_RSet (mem_RSet_of_isSylow2In hL₃.1 hR₃)
  have hs : Q3T8.Asc77.Std7 Ω L L' z := Q3T8.Asc77.Std7.of_twin h.std hL hL' hne
  have hperp : KPerp Ω L = twinSet Ω L := Q3T8.Asc77.T7B.perp_of_twin h.std h.perp hL
  have hL₃' : L₃ ∈ twinSet Ω L := by rw [twinSet_eq_of_mem_twinSet h.std.hz hL]; exact hL₃
  exact ⟨L₃, w, Q3T8.Asc77.T7B.hyp22_of_sylows hs hperp hL₃' hL₃L hL₃L' hR₁ hR₂ hR₃ hc c₁ c₂ hx hy
      hw
    ox oy ow⟩
end Hyp22
section C227

@[expose] def C22_7_trans
    : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' K₃ : Subgroup G) (z u₁ u₂ u₃ : G), Q3T8.Asc77.Hyp22 Ω K K' K₃ z u₁ u₂ u₃ →
      (∀ W ∈ WSet Ω, MuIsoWylD4 Ω W) → ∀ J ∈ dstarComp Ω K, ∃ x ∈ Subgroup.normalizer
        (alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) : Set G), conjSub x K = J

@[expose] def C22_7_cent
    : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' K₃ : Subgroup G) (z u₁ u₂ u₃ : G), Q3T8.Asc77.Hyp22 Ω K K' K₃ z u₁ u₂ u₃ →
      (∀ W ∈ WSet Ω, MuIsoWylD4 Ω W) → Subgroup.centralizer ({u₁ * u₂} : Set G) ≤
        Subgroup.normalizer (alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) : Set G)

theorem c22_7_of
    (hE : Q3T7E.ThmEWithSylow3) (h2 : Q3T8.Asc77.C22_2) (h4 : Q3T8.Asc77.C22_4)
    (htr : Q3T8.Asc77.C22_7_trans) (hc : Q3T8.Asc77.C22_7_cent) : Q3T8.Asc77.C22_7 := by
  intro G _ _ _ Ω K K' K₃ z u₁ u₂ u₃ h
  have hμ := h4 G Ω K K' K₃ z u₁ u₂ u₃ h
  have hstd : StdCent Ω K (Subgroup.normalizer
      (alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) : Set G)) z :=
    h.stdCent_of_twin (h.centralizer_le_normalizer_alpha h2) fun L hL L' hL' hne R₁ R₂ hR₁ hR₂ hcm
      x hx y hy ox oy => by
      obtain ⟨L₃, w, hd⟩ := h.exists_datum_of_pair hL hL' hne hR₁ hR₂ hcm hx hy ox oy
      have hc' := hc G Ω L L' L₃ z x y w hd (h4 G Ω L L' L₃ z x y w hd)
      have heq := Q3T8.Asc77.Hyp22.alpha_eq_of_datum h2 hd h
      rw [heq] at hc'
      exact hc'
  have htop := Q3T8.Asc77.thmE_apply hE h.std.stand h.std.hz h.std.hK' h.std.hne hstd
    (htr G Ω K K' K₃ z u₁ u₂ u₃ h hμ)
  exact T7B.eq_bot_of_normalizer_eq_top (h2 G Ω K K' K₃ z u₁ u₂ u₃ h).1 htop
    (T7B.two_dvd_natCard h.std.hz)
end C227
end Asc77

end

end CFSG.ClassicalInvolution.Q3.Q3T8
