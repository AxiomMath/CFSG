module

public import CFSG.GroupTheory.Fitting.QuasisimpleNormalFstar

public section

namespace CFSG.GroupTheory

open Subgroup

variable {W : Type} [CommGroup W] [Finite W]

theorem generalizedFitting_sup_eq_of_isPGroup_two {X P G₁ : Subgroup (MulAut W)}
    (hq : CFSG.IsQuasisimple X) (hXG₁ : X ≤ G₁) (hPG₁ : P ≤ G₁)
    (hXN : (X.subgroupOf G₁).Normal) (hP : IsPGroup 2 ↥P)
    (hCodd : Odd (Nat.card ↥(Subgroup.centralizer (X : Set (MulAut W)) ⊓ G₁))) :
    CFSG.generalizedFitting ↥(X ⊔ P) = X.subgroupOf (X ⊔ P) := by
  classical
  let G₂ : Subgroup (MulAut W) := X ⊔ P
  have hXG₂ : X ≤ G₂ := le_sup_left
  have hPG₂ : P ≤ G₂ := le_sup_right
  have hG₂G₁ : G₂ ≤ G₁ := sup_le hXG₁ hPG₁
  have hnorm : G₂ ≤ Subgroup.normalizer (X : Set (MulAut W)) :=
    hG₂G₁.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hXG₁).mp hXN)
  have hXnormal : (X.subgroupOf G₂).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hnorm
  let N : Subgroup ↥G₂ := X.subgroupOf G₂
  have hNnormal : N.Normal := hXnormal
  have : N.Normal := hNnormal
  have hNq : CFSG.IsQuasisimple N := by
    change CFSG.IsQuasisimple (X.subgroupOf G₂)
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe (H := X) (K := G₂) hXG₂).symm hq
  have hNcomp : CFSG.IsComponent N := ⟨hNq, hNnormal.isSubnormal⟩
  have hC : Subgroup.centralizer (N : Set ↥G₂) ≤ N := by
    intro g hg
    rw [Subgroup.mem_subgroupOf]
    have hgX : ∀ a ∈ X, a * (g : MulAut W) = (g : MulAut W) * a := by
      intro a ha
      exact congrArg Subtype.val
        ((Subgroup.mem_centralizer_iff.mp hg) ⟨a, hXG₂ ha⟩ (Subgroup.mem_subgroupOf.mpr ha))
    have hgC : (g : MulAut W) ∈ Subgroup.centralizer (X : Set (MulAut W)) := by
      rw [Subgroup.mem_centralizer_iff]
      exact hgX
    have hodd : Odd (orderOf (g : MulAut W)) :=
      Odd.of_dvd_nat hCodd
        ((Subgroup.centralizer (X : Set (MulAut W)) ⊓ G₁).orderOf_dvd_natCard
          ⟨hgC, hG₂G₁ g.2⟩)
    have hsup : N ⊔ P.subgroupOf G₂ = ⊤ := by
      have h := Subgroup.subgroupOf_sup (A := X) (A' := P) (B := G₂) hXG₂ hPG₂
      rw [show X ⊔ P = G₂ from rfl, Subgroup.subgroupOf_self] at h
      rw [← h]
    have hmem : g ∈ N ⊔ P.subgroupOf G₂ := by
      rw [hsup]
      exact Subgroup.mem_top g
    obtain ⟨n, hn, p, hp, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hmem
    have hpP : (p : MulAut W) ∈ P := Subgroup.mem_subgroupOf.mp hp
    obtain ⟨m, hm⟩ := hP ⟨(p : MulAut W), hpP⟩
    have hmval : orderOf (p : MulAut W) ∣ 2 ^ m := by
      have h : orderOf (⟨(p : MulAut W), hpP⟩ : ↥P) ∣ 2 ^ m :=
        orderOf_dvd_iff_pow_eq_one.mpr hm
      rwa [show orderOf (⟨(p : MulAut W), hpP⟩ : ↥P) = orderOf (p : MulAut W) from
        (orderOf_injective (Subgroup.subtype P) Subtype.val_injective _).symm] at h
    let q : ↥G₂ →* ↥G₂ ⧸ N := QuotientGroup.mk' N
    have hnq : q n = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact hn
    have hqg : q (n * p) = q p := by rw [map_mul, hnq, one_mul]
    have hdvd2 : orderOf (q (n * p)) ∣ 2 ^ m := by
      have h : orderOf (q p) ∣ orderOf (p : MulAut W) := by
        have h1 := orderOf_map_dvd q p
        rwa [show orderOf (p : ↥G₂) = orderOf (p : MulAut W) from
          (orderOf_injective (Subgroup.subtype G₂) Subtype.val_injective p).symm] at h1
      rw [hqg]
      exact h.trans hmval
    have hdvdodd : orderOf (q (n * p)) ∣ orderOf ((n * p : ↥G₂) : MulAut W) := by
      have h := orderOf_map_dvd q (n * p)
      rwa [show orderOf (n * p : ↥G₂) = orderOf ((n * p : ↥G₂) : MulAut W) from
        (orderOf_injective (Subgroup.subtype G₂) Subtype.val_injective (n * p)).symm] at h
    have hone : orderOf (q (n * p)) = 1 :=
      Nat.eq_one_of_dvd_coprimes (hodd.coprime_two_left.pow_left m) hdvd2 hdvdodd
    have hq1 : q (n * p) = 1 := orderOf_eq_one_iff.mp hone
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hq1
    exact hq1
  exact generalizedFitting_eq_of_isComponent_of_centralizer_le N hNcomp hC

theorem generalizedFitting_sup_eq_of_isPGroup_two_of_isIrrOn [Nontrivial W]
    (hW : ∀ w : W, w * w = 1) {X P G₁ : Subgroup (MulAut W)}
    (hq : CFSG.IsQuasisimple X) (hXG₁ : X ≤ G₁) (hPG₁ : P ≤ G₁)
    (hirr : CFSG.LocalAnalysis.RankThreeUC.IsIrrOn X)
    (hXN : (X.subgroupOf G₁).Normal) (hP : IsPGroup 2 ↥P) :
    CFSG.generalizedFitting ↥(X ⊔ P) = X.subgroupOf (X ⊔ P) :=
  generalizedFitting_sup_eq_of_isPGroup_two hq hXG₁ hPG₁ hXN hP
    ((CFSG.QuasithinUnique.Setup.X5.centralizer_odd hW X hirr).of_dvd_nat
      (Subgroup.card_dvd_of_le inf_le_left))

end CFSG.GroupTheory
