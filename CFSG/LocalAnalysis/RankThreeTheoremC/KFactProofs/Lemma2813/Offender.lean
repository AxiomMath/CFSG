module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Lemma2813.TFacts
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.RankThree.PartOne.K1214.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Lemma2813

open CFSG.Open Subgroup CFSG.QuasithinUnique.Setup.Family
open scoped Pointwise

section B

variable {A : Type} [Group A] [Finite A] {X K R P : Subgroup A}

theorem off_isSimpleGroup_GL32 : IsSimpleGroup GL32 := by
  have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) :=
    (CFSG.LinearGroups.linear_projective_simple (K := ZMod 2) (n := 3) (by norm_num)
      (Or.inl le_rfl)).2.1
  exact L32Insp.pslEquiv.symm.isSimpleGroup

theorem off_normal_centralizer {G : Type*} [Group G] {Y W : Subgroup G}
    (hYW : Y ≤ normalizer (W : Set G)) :
    ((centralizer (W : Set G)).subgroupOf Y).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [mem_subgroupOf, mem_centralizer_iff] at hn ⊢
  intro w hw
  have hg : (g : G)⁻¹ * w * (g : G) ∈ W := by
    have := (mem_normalizer_iff.1 (hYW (inv_mem g.2)) w).1 hw
    simpa using this
  have h := hn _ hg
  show w * ((g : G) * (n : G) * (g : G)⁻¹) = (g : G) * (n : G) * (g : G)⁻¹ * w
  calc w * ((g : G) * (n : G) * (g : G)⁻¹)
      = (g : G) * (((g : G)⁻¹ * w * (g : G)) * (n : G)) * (g : G)⁻¹ := by group
    _ = (g : G) * ((n : G) * ((g : G)⁻¹ * w * (g : G))) * (g : G)⁻¹ := by rw [h]
    _ = (g : G) * (n : G) * (g : G)⁻¹ * w := by group

theorem Hyp2813.exists_offender (h : Hyp2813 X K R P) (hS : pCoreOf 2 P ≠ ⊥) :
    ∃ A₀ : Subgroup A, A₀ ∈ CFSG.thompsonAbelianSubgroups (pCoreOf 2 P) ∧
      ¬ A₀ ≤ pCoreOf 2 X := by
  by_contra hcon
  push Not at hcon
  have hN : normalizer (pCoreOf 2 X : Set A) ≤
      normalizer (CFSG.thompsonSubgroup (pCoreOf 2 P) : Set A) :=
    normalizer_le_normalizer_thompsonSubgroup h.pCore_X_le_pCore_P hcon
  have hXN : X ≤ normalizer (CFSG.thompsonSubgroup (pCoreOf 2 P) : Set A) :=
    (normalizer_pCoreOf X).trans hN
  exact h.nofact (CFSG.thompsonSubgroup (pCoreOf 2 P)) (thompsonSubgroup_le' _)
    (thompsonSubgroup_ne_bot hS) (thompsonSubgroup_characteristic _)
    (le_sup_of_le_right (le_inf le_rfl hXN))

theorem Hyp2813.exists_TT_not_T0 (h : Hyp2813 X K R P) (hS : pCoreOf 2 P ≠ ⊥) :
    ∃ t ∈ TT X, t ∉ T0 X := by
  by_contra hcon
  push Not at hcon
  have hXV : X ≤ centralizer ((omegaCenter (pCoreOf 2 P) : Subgroup A) : Set A) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hvT : v ∈ TT X := (h.mem_omegaCenter_S_iff.1 hv).1
    exact (((mem_T0_iff X).1 (hcon v hvT)).2 x hx).symm
  exact h.nofact (CFSG.thompsonSubgroup (pCoreOf 2 P)) (thompsonSubgroup_le' _)
    (thompsonSubgroup_ne_bot hS) (thompsonSubgroup_characteristic _)
    (le_sup_of_le_left (le_inf le_rfl hXV))

theorem Hyp2813.faithful (h : Hyp2813 X K R P) (hS : pCoreOf 2 P ≠ ⊥) :
    ∀ x ∈ X, (∀ t ∈ TT X, x * t = t * x) → x ∈ pCoreOf 2 X := by
  obtain ⟨ψ, hψs, hψk⟩ := h.exists_psi
  have hXT : X ≤ normalizer (TT X : Set A) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_TT X)
  have hCn : ((centralizer (TT X : Set A)).subgroupOf X).Normal := off_normal_centralizer hXT
  have hmapn : (((centralizer (TT X : Set A)).subgroupOf X).map ψ).Normal := hCn.map ψ hψs
  haveI : IsSimpleGroup GL32 := off_isSimpleGroup_GL32
  haveI := hmapn
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (((centralizer (TT X : Set A)).subgroupOf X).map ψ) with hbot | htop
  · intro x hx hxc
    have hxC : (⟨x, hx⟩ : ↥X) ∈ (centralizer (TT X : Set A)).subgroupOf X := by
      rw [mem_subgroupOf, mem_centralizer_iff]
      exact fun t ht => (hxc t ht).symm
    have hmem := Subgroup.mem_map_of_mem ψ hxC
    rw [hbot, Subgroup.mem_bot] at hmem
    have hker : (⟨x, hx⟩ : ↥X) ∈ ψ.ker := hmem
    rw [hψk, mem_subgroupOf] at hker
    exact hker
  · exfalso
    obtain ⟨t, htT, htT0⟩ := h.exists_TT_not_T0 hS
    refine htT0 ((mem_T0_iff X).2 ⟨htT, fun x hx => ?_⟩)
    have hmem : ψ ⟨x, hx⟩ ∈ ((centralizer (TT X : Set A)).subgroupOf X).map ψ := by
      rw [htop]
      exact Subgroup.mem_top _
    obtain ⟨c, hcC, hcψ⟩ := Subgroup.mem_map.1 hmem
    have hq : c⁻¹ * ⟨x, hx⟩ ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hcψ, inv_mul_cancel]
    rw [hψk, mem_subgroupOf] at hq
    have hcT : t * (c : A) = (c : A) * t :=
      mem_centralizer_iff.1 (mem_subgroupOf.1 hcC) t htT
    have hqT := pCoreOf_comm_TT X hq htT
    have hxeq : x = (c : A) * ((c⁻¹ * ⟨x, hx⟩ : ↥X) : A) := by simp
    calc x * t = (c : A) * ((c⁻¹ * ⟨x, hx⟩ : ↥X) : A) * t := by rw [← hxeq]
      _ = (c : A) * (((c⁻¹ * ⟨x, hx⟩ : ↥X) : A) * t) := by rw [mul_assoc]
      _ = (c : A) * (t * ((c⁻¹ * ⟨x, hx⟩ : ↥X) : A)) := by rw [hqT]
      _ = ((c : A) * t) * ((c⁻¹ * ⟨x, hx⟩ : ↥X) : A) := by rw [mul_assoc]
      _ = (t * (c : A)) * ((c⁻¹ * ⟨x, hx⟩ : ↥X) : A) := by rw [hcT]
      _ = t * ((c : A) * ((c⁻¹ * ⟨x, hx⟩ : ↥X) : A)) := by rw [mul_assoc]
      _ = t * x := by rw [← hxeq]

theorem Hyp2813.offender_ineq (h : Hyp2813 X K R P) (hS : pCoreOf 2 P ≠ ⊥) {A₀ : Subgroup A}
    (hA : A₀ ∈ CFSG.thompsonAbelianSubgroups (pCoreOf 2 P)) :
    Nat.card (TT X) * Nat.card ↥(A₀ ⊓ pCoreOf 2 X) ≤ Nat.card ↥(A₀ ⊓ TT X) * Nat.card A₀ := by
  obtain ⟨hAS, hAc, hAmax⟩ := hA
  have hTS : TT X ≤ pCoreOf 2 P := (TT_le_pCoreOf X).trans h.pCore_X_le_pCore_P
  have hTc : IsMulCommutative (TT X) :=
    IsMulCommutative.of_setLike_mul_comm fun _ ha _ hb => TT_comm X ha hb
  have hA₀X : A₀ ≤ X := hAS.trans ((pCoreOf_le_self P).trans h.P_le)
  have hCQ : A₀ ⊓ centralizer (TT X : Set A) = A₀ ⊓ pCoreOf 2 X := by
    apply le_antisymm
    · intro x hx
      obtain ⟨hxA, hxC⟩ := Subgroup.mem_inf.1 hx
      refine Subgroup.mem_inf.2 ⟨hxA, h.faithful hS x (hA₀X hxA) fun t ht => ?_⟩
      exact (Subgroup.mem_centralizer_iff.1 hxC t ht).symm
    · intro x hx
      obtain ⟨hxA, hxQ⟩ := Subgroup.mem_inf.1 hx
      exact Subgroup.mem_inf.2 ⟨hxA, Subgroup.mem_centralizer_iff.2 fun t ht =>
        (pCoreOf_comm_TT X hxQ ht).symm⟩
  have hCA : A₀ ⊓ centralizer (TT X : Set A) ≤ A₀ := inf_le_left
  have hCT : A₀ ⊓ centralizer (TT X : Set A) ≤ centralizer (TT X : Set A) := inf_le_right
  have hTC : TT X ≤ centralizer ((A₀ ⊓ centralizer (TT X : Set A) : Subgroup A) : Set A) :=
    fun t ht => Subgroup.mem_centralizer_iff.2 fun c hc =>
      (Subgroup.mem_centralizer_iff.1 (hCT hc) t ht).symm
  have hBc : IsMulCommutative ↥((A₀ ⊓ centralizer (TT X : Set A)) ⊔ TT X) := by
    have hCC : A₀ ⊓ centralizer (TT X : Set A) ≤
        centralizer ((A₀ ⊓ centralizer (TT X : Set A) : Subgroup A) : Set A) :=
      Subgroup.le_centralizer_iff_isMulCommutative.2 (isMulCommutative_anti hCA)
    have hTT : TT X ≤ centralizer (TT X : Set A) :=
      Subgroup.le_centralizer_iff_isMulCommutative.2 hTc
    refine Subgroup.le_centralizer_iff_isMulCommutative.1 (sup_le ?_ ?_)
    · exact Subgroup.le_centralizer_iff.2 (sup_le hCC hTC)
    · exact Subgroup.le_centralizer_iff.2 (sup_le hCT hTT)
  have hBA : Nat.card ↥((A₀ ⊓ centralizer (TT X : Set A)) ⊔ TT X) ≤ Nat.card ↥A₀ :=
    hAmax _ (sup_le (hCA.trans hAS) hTS) hBc
  have hprod := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer
    (A := A₀ ⊓ centralizer (TT X : Set A)) (B := TT X)
    (hTC.trans (Subgroup.centralizer_le_normalizer _))
  rw [hCQ] at hprod hBA
  have hCTT : (A₀ ⊓ pCoreOf 2 X) ⊓ TT X = A₀ ⊓ TT X := by
    rw [inf_assoc, inf_eq_right.2 (TT_le_pCoreOf X)]
  rw [hCTT] at hprod
  calc Nat.card (TT X) * Nat.card ↥(A₀ ⊓ pCoreOf 2 X)
      = Nat.card ↥(A₀ ⊓ pCoreOf 2 X) * Nat.card (TT X) := mul_comm _ _
    _ = Nat.card ↥((A₀ ⊓ pCoreOf 2 X) ⊔ TT X) * Nat.card ↥(A₀ ⊓ TT X) := hprod.symm
    _ ≤ Nat.card A₀ * Nat.card ↥(A₀ ⊓ TT X) := Nat.mul_le_mul_right _ hBA
    _ = Nat.card ↥(A₀ ⊓ TT X) * Nat.card A₀ := mul_comm _ _

end B

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Lemma2813
