module

public import CFSG.GroupTheory.Fitting.LayerTopBot
public import CFSG.LocalAnalysis.RankThreeUC.AGL81U4FFDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.General
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X5bGroup
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.U4FF.Defs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Monster.B.TwoA.Base.ElemAut
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.GroupTheory

open Subgroup
open CFSG.LocalAnalysis.RankThreeUC CFSG.HardMathSupport.U4FF

variable {W : Type} [CommGroup W]

theorem isIrrOn_mono {X Y : Subgroup (MulAut W)}
    (h : CFSG.LocalAnalysis.RankThreeUC.IsIrrOn X) (hXY : X ≤ Y) :
    CFSG.LocalAnalysis.RankThreeUC.IsIrrOn Y := by
  intro U hU
  exact h U fun x hx => hU x (hXY hx)

theorem generalizedFitting_eq_of_isComponent_of_centralizer_le {H : Type} [Group H] [Finite H]
    (Q : Subgroup H) (hQ : CFSG.IsComponent Q)
    (hC : Subgroup.centralizer (Q : Set H) ≤ Q) : CFSG.generalizedFitting H = Q := by
  have hothers : sSup {T : Subgroup H | CFSG.IsComponent T ∧ T ≠ Q} ≤ Q := by
    refine sSup_le ?_
    rintro T ⟨hT, hTQ⟩
    have hcomm : ⁅T, Q⁆ = ⊥ :=
      (CFSG.LocalCores.distinct_components_commute hT hQ).resolve_left hTQ
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm).trans hC
  have hlayer : CFSG.layer H = Q := by
    rw [(CFSG.WholeGroup.layer_eq_sup_others hQ).2, sup_eq_left.mpr hothers]
  have hfit : CFSG.fittingSubgroup H ≤ Q := by
    have hcomm : ⁅CFSG.fittingSubgroup H, CFSG.layer H⁆ = ⊥ :=
      CFSG.LocalCores.fitting_layer_commute (G := H)
    have hcent : CFSG.fittingSubgroup H ≤ Subgroup.centralizer (Q : Set H) := by
      refine (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm).trans ?_
      exact Subgroup.centralizer_le (by rw [hlayer])
    exact hcent.trans hC
  rw [CFSG.generalizedFitting, hlayer, sup_eq_right.mpr hfit]

theorem fstar_sup_zpowers_eq_of_quasisimple_normal [Finite W] [Nontrivial W]
    (hW : ∀ w : W, w * w = 1) {X G₁ : Subgroup (MulAut W)}
    (hXG₁ : X ≤ G₁) (hq : CFSG.IsQuasisimple X)
    (hirr : CFSG.LocalAnalysis.RankThreeUC.IsIrrOn X)
    (hXN : (X.subgroupOf G₁).Normal)
    {t : MulAut W} (htG : t ∈ G₁) (ht : t * t = 1) (ht1 : t ≠ 1) :
    CFSG.generalizedFitting ↥(X ⊔ Subgroup.zpowers t) =
      X.subgroupOf (X ⊔ Subgroup.zpowers t) := by
  classical
  have hCodd : Odd (Nat.card ↥(Subgroup.centralizer (X : Set (MulAut W)) ⊓ G₁)) :=
    (CFSG.QuasithinUnique.Setup.X5.centralizer_odd hW X hirr).of_dvd_nat
      (Subgroup.card_dvd_of_le inf_le_left)
  let G₂ : Subgroup (MulAut W) := X ⊔ Subgroup.zpowers t
  have ht2 : t ^ 2 = 1 := by simpa [pow_two] using ht
  have htord : orderOf t = 2 := orderOf_eq_prime ht2 ht1
  have hXG₂ : X ≤ G₂ := le_sup_left
  have htG₂ : t ∈ G₂ := Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have hG₂G₁ : G₂ ≤ G₁ := sup_le hXG₁ (Subgroup.zpowers_le.mpr htG)
  have hnormG₁ : G₁ ≤ Subgroup.normalizer (X : Set (MulAut W)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXG₁).mp hXN
  have hnormG₂ : G₂ ≤ Subgroup.normalizer (X : Set (MulAut W)) := hG₂G₁.trans hnormG₁
  have hXnormal : (X.subgroupOf G₂).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hnormG₂
  let N : Subgroup ↥G₂ := X.subgroupOf G₂
  let V : Subgroup ↥G₂ := (Subgroup.zpowers t).subgroupOf G₂
  have hNV : N ⊔ V = ⊤ := by
    rw [← Subgroup.subgroupOf_sup (A := X) (A' := Subgroup.zpowers t) (B := G₂)
      hXG₂ (Subgroup.zpowers_le.mpr htG₂)]
    exact Subgroup.subgroupOf_self G₂
  have hNnorm : N.Normal := hXnormal
  have hNq : CFSG.IsQuasisimple N := by
    change CFSG.IsQuasisimple (X.subgroupOf G₂)
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe (H := X) (K := G₂) hXG₂).symm hq
  have hNcomp : CFSG.IsComponent N := ⟨hNq, hNnorm.isSubnormal⟩
  have hC : Subgroup.centralizer (N : Set ↥G₂) ≤ N := by
    intro g hg
    rw [Subgroup.mem_subgroupOf]
    by_contra hgX
    have hmem : g ∈ N ⊔ V := by rw [hNV]; trivial
    obtain ⟨n, hn, v, hv, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hmem
    have hnX : (n : MulAut W) ∈ X := hn
    have hvz : (v : MulAut W) ∈ Subgroup.zpowers t := hv
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hvz
    have hv1 : (v : MulAut W) = 1 ∨ (v : MulAut W) = t := by
      rcases CFSG.EvenSporadicStandard.Solomon78.zpow_eq_one_or_self_of_orderOf_eq_two htord k
        with h | h
      · exact Or.inl (hk ▸ h)
      · exact Or.inr (hk ▸ h)
    have hgcent : ∀ a ∈ X, a * ((n * v : ↥G₂) : MulAut W) =
        ((n * v : ↥G₂) : MulAut W) * a := by
      intro a ha
      have h' := hg ⟨a, hXG₂ ha⟩ (Subgroup.mem_subgroupOf.mpr ha)
      exact congrArg Subtype.val h'
    rcases hv1 with hv1 | hv1
    ·
      apply hgX
      have hval : ((n * v : ↥G₂) : MulAut W) = (n : MulAut W) := by
        change (n : MulAut W) * (v : MulAut W) = (n : MulAut W)
        rw [hv1, mul_one]
      rw [hval]
      exact hnX
    ·
      set x : MulAut W := (n : MulAut W) with hxdef
      have hxX : x ∈ X := hnX
      have hgx : ((n * v : ↥G₂) : MulAut W) = x * t := by
        change (n : MulAut W) * (v : MulAut W) = x * t
        rw [hv1, hxdef]
      have hconj : ∀ a ∈ X, t * a * t⁻¹ = x⁻¹ * a * x := by
        intro a ha
        have hga := hgcent a ha
        rw [hgx] at hga
        have h1 : a * x * t = x * t * a := by simpa [mul_assoc] using hga
        calc t * a * t⁻¹ = x⁻¹ * (x * t * a) * t⁻¹ := by group
          _ = x⁻¹ * (a * x * t) * t⁻¹ := by rw [← h1]
          _ = x⁻¹ * a * x := by group
      have hx2inv : ∀ a ∈ X, x⁻¹ ^ 2 * a * x ^ 2 = a := by
        intro a ha
        have htinv : t⁻¹ * t⁻¹ = 1 := by
          rw [← mul_inv_rev, ht, inv_one]
        have h2 : t * (t * a * t⁻¹) * t⁻¹ = a := by
          calc t * (t * a * t⁻¹) * t⁻¹ = (t * t) * a * (t⁻¹ * t⁻¹) := by group
            _ = a := by rw [ht, htinv]; group
        rw [hconj a ha] at h2
        have hxa : x⁻¹ * a * x ∈ X := X.mul_mem (X.mul_mem (X.inv_mem hxX) ha) hxX
        rw [hconj (x⁻¹ * a * x) hxa] at h2
        calc x⁻¹ ^ 2 * a * x ^ 2 = x⁻¹ * (x⁻¹ * a * x) * x := by
              rw [pow_two, pow_two]
              group
          _ = a := h2
      have hx2c : ∀ a ∈ X, x ^ 2 * a = a * x ^ 2 := by
        intro a ha
        have hconj2 : x ^ 2 * a * (x ^ 2)⁻¹ = a := by
          calc x ^ 2 * a * (x ^ 2)⁻¹ = x ^ 2 * (x⁻¹ ^ 2 * a * x ^ 2) * (x ^ 2)⁻¹ := by
                rw [hx2inv a ha]
            _ = a := by group
        calc x ^ 2 * a = (x ^ 2 * a * (x ^ 2)⁻¹) * x ^ 2 := by group
          _ = a * x ^ 2 := by rw [hconj2]
      have hc0cent : (x⁻¹ * t) ∈ Subgroup.centralizer (X : Set (MulAut W)) := by
        rw [Subgroup.mem_centralizer_iff]
        intro a ha
        have hta : t * a * t⁻¹ = x⁻¹ * a * x := hconj a ha
        have hconj0 : (x⁻¹ * t) * a * (x⁻¹ * t)⁻¹ = a := by
          calc (x⁻¹ * t) * a * (x⁻¹ * t)⁻¹ = x⁻¹ * (t * a * t⁻¹) * x := by group
            _ = x⁻¹ * (x⁻¹ * a * x) * x := by rw [hta]
            _ = x⁻¹ ^ 2 * a * x ^ 2 := by simp only [pow_two]; group
            _ = a := hx2inv a ha
        calc a * (x⁻¹ * t) = ((x⁻¹ * t) * a * (x⁻¹ * t)⁻¹) * (x⁻¹ * t) := by
              rw [hconj0]
          _ = (x⁻¹ * t) * a := by group
      have hc0mem : x⁻¹ * t ∈ Subgroup.centralizer (X : Set (MulAut W)) ⊓ G₁ :=
        ⟨hc0cent, G₁.mul_mem (G₁.inv_mem (hXG₁ hxX)) htG⟩
      have hodd_c0 : Odd (orderOf (x⁻¹ * t)) :=
        Odd.of_dvd_nat hCodd
          ((Subgroup.centralizer (X : Set (MulAut W)) ⊓ G₁).orderOf_dvd_natCard hc0mem)
      have hc0G₂ : x⁻¹ * t ∈ G₂ := G₂.mul_mem (G₂.inv_mem (hXG₂ hxX)) htG₂
      let q : ↥G₂ →* ↥G₂ ⧸ N := QuotientGroup.mk' N
      have hxq : q ⟨x, hXG₂ hxX⟩ = 1 := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
        exact hxX
      have hq_x : q ⟨x⁻¹ * t, hc0G₂⟩ = q ⟨t, htG₂⟩ := by
        have h1 : (⟨x⁻¹ * t, hc0G₂⟩ : ↥G₂) =
            (⟨x, hXG₂ hxX⟩ : ↥G₂)⁻¹ * ⟨t, htG₂⟩ := by
          apply Subtype.ext
          rfl
        rw [h1, map_mul, map_inv, hxq, inv_one, one_mul]
      have hqt2 : q ⟨t, htG₂⟩ * q ⟨t, htG₂⟩ = 1 := by
        rw [← map_mul]
        have h : (⟨t, htG₂⟩ : ↥G₂) * ⟨t, htG₂⟩ = 1 := by
          apply Subtype.ext
          simpa [pow_two] using ht
        rw [h, map_one]
      have hqt1 : q ⟨t, htG₂⟩ ≠ 1 := by
        intro h
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h
        exact hgX (by rw [hgx]; exact X.mul_mem hxX h)
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have h2dvd : 2 ∣ orderOf (q ⟨t, htG₂⟩) := by
        have hqt2' : q ⟨t, htG₂⟩ ^ 2 = 1 := by
          rw [pow_two]
          exact hqt2
        rw [orderOf_eq_prime hqt2' hqt1]
      have hord_eq : orderOf (⟨x⁻¹ * t, hc0G₂⟩ : ↥G₂) = orderOf (x⁻¹ * t) :=
        (orderOf_injective (Subgroup.subtype G₂) Subtype.val_injective _).symm
      have hmapdvd : orderOf (q ⟨x⁻¹ * t, hc0G₂⟩) ∣ orderOf (x⁻¹ * t) := by
        rw [← hord_eq]
        exact orderOf_map_dvd q _
      rw [hq_x] at hmapdvd
      have hoddq : Odd (orderOf (q ⟨t, htG₂⟩)) := Odd.of_dvd_nat hodd_c0 hmapdvd
      exact (Nat.not_even_iff_odd.mpr hoddq) (even_iff_two_dvd.mpr h2dvd)
  exact generalizedFitting_eq_of_isComponent_of_centralizer_le N hNcomp hC

end CFSG.GroupTheory
