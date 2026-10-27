module

public import CFSG.LargeExtraspecial.S8CorBStatement
public import CFSG.LargeExtraspecial.S3Eight
public import CFSG.SignalizerFunctorTheorem.Inheritance.Diagonal

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S8

open Subgroup CFSG.Blueprint

theorem CorBList.of_mulEquiv {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y')
    (h : CorBList Y) : CorBList Y' := by
  rcases h with ⟨f, h⟩ | ⟨f, h⟩ | ⟨f, h⟩ | ⟨f, h⟩ | ⟨f, h⟩ | h | ⟨f, h⟩ | h | h
  · exact Or.inl ⟨f, Blueprint.LieModel.of_mulEquiv e h⟩
  · exact Or.inr (Or.inl ⟨f, Blueprint.LieModel.of_mulEquiv e h⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨f, Blueprint.LieModel.of_mulEquiv e h⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨f, Blueprint.LieModel.of_mulEquiv e h⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨f, Blueprint.LieModel.of_mulEquiv e h⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (Blueprint.LieModel.of_mulEquiv e h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨f, Blueprint.LieModel.of_mulEquiv e h⟩))))))
  · obtain ⟨f⟩ := h
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e.symm.trans f⟩)))))))
  · obtain ⟨f⟩ := h
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨e.symm.trans f⟩)))))))

private theorem center_eq_bot_of_setting {G : Type} [Group G] [IsSimpleGroup G]
    (S : Setting G) : Subgroup.center G = ⊥ := by
  obtain ⟨a, -, b, -, hab⟩ := S.exists_not_commute
  exact CFSG.SignalizerFunctorTheorem.Diagonal.center_eq_bot ⟨a, b, hab⟩

theorem corBList_of_forall_conj_mem_QG (hCorB : TimmesfeldCorBInput) {G : Type} [Group G]
    [Finite G] [IsSimpleGroup G] (S : Setting G)
    (h : ∀ g : G, g * S.z * g⁻¹ ∈ S.M → g * S.z * g⁻¹ ∈ S.QG) : CorBList G := by
  have hGncomm : ¬ IsMulCommutative G := by
    obtain ⟨a, -, b, -, hab⟩ := S.exists_not_commute
    intro hcomm
    haveI : IsMulCommutative G := hcomm
    exact hab (mul_comm' a b)
  have hsub : conjCent S.z ⊆ (S.QG : Set G) := by
    rintro τ ⟨hcomm, hconj⟩
    obtain ⟨g, hg⟩ := isConj_iff.mp hconj
    rw [← hg]
    exact h g (by rw [hg]; exact S.mem_M_iff.mpr hcomm)
  set H : Subgroup G := closure (conjCent S.z) with hHdef
  have hHle : H ≤ S.QG := (Subgroup.closure_le (K := S.QG)).mpr hsub
  have hH2 : IsPGroup 2 H := S.isPGroup_QG.to_le hHle
  have hcomm_le : ⁅H, H⁆ ≤ Subgroup.zpowers S.z := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    change x * y * x⁻¹ * y⁻¹ ∈ Subgroup.zpowers S.z
    rcases S.commutator_eq_one_or_z (hHle hx) (hHle hy) with h1 | hz
    · rw [h1]
      exact Subgroup.one_mem _
    · rw [hz]
      exact Subgroup.mem_zpowers S.z
  have hzcent : S.z ∈ Subgroup.centralizer (S.QG : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact S.z_comm_QG hy
  have hzp_le : Subgroup.zpowers S.z ≤ Subgroup.centralizer (H : Set G) :=
    (Subgroup.zpowers_le.mpr hzcent).trans
      (Subgroup.centralizer_le (fun x hx => hHle hx))
  have htriple : ⁅⁅H, H⁆, H⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (hcomm_le.trans hzp_le)
  have hconjprop : ∀ τ : G, τ * S.z = S.z * τ → IsConj S.z τ → τ ≠ S.z →
      IsConj S.z (S.z * τ) := by
    intro τ hcomm hconj hτz
    obtain ⟨g, hg⟩ := isConj_iff.mp hconj
    have hτQ : τ ∈ S.QG := by
      rw [← hg]
      exact h g (by rw [hg]; exact S.mem_M_iff.mpr hcomm)
    have hτ1 : τ ≠ 1 := by
      rintro rfl
      exact S.z_ne_one (isConj_one_left.mp hconj)
    obtain ⟨u, huQ, hu⟩ := S.exists_conj_eq_mul_z hτQ hτ1 hτz
    have hconj2 : IsConj τ (τ * S.z) := by
      rw [isConj_iff]
      exact ⟨u, hu⟩
    have h := hconj.trans hconj2
    rwa [hcomm] at h
  have hres := hCorB G S.z S.orderOf_z hH2 htriple hconjprop
  have hNtop : Subgroup.normalClosure ({S.z} : Set G) = ⊤ := by
    apply Subgroup.normalClosure_normal.eq_bot_or_eq_top.resolve_left
    simp [S.z_ne_one]
  have hcenterG : Subgroup.center G = ⊥ := center_eq_bot_of_setting S
  rcases hres with ⟨K, hKle, hKN, hKodd, hKeq⟩ | hElem | hList
  ·
    have hKnormal : K.Normal := by
      have h := hKN
      rw [hNtop] at h
      have hnorm := (Subgroup.normal_subgroupOf_iff_le_normalizer (H := K) (K := ⊤)
        le_top).mp h
      exact Subgroup.normalizer_eq_top_iff.mp (le_antisymm le_top hnorm)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal K with hKbot | hKtop
    ·
      have htopz : (⊤ : Subgroup G) = Subgroup.zpowers S.z := by
        rw [← hNtop, hKeq, hKbot, bot_sup_eq]
      haveI : IsMulCommutative G := IsMulCommutative.of_comm fun a b =>
        congrArg Subtype.val (mul_comm'
          (⟨a, by rw [← htopz]; exact Subgroup.mem_top a⟩ : Subgroup.zpowers S.z)
          (⟨b, by rw [← htopz]; exact Subgroup.mem_top b⟩ : Subgroup.zpowers S.z))
      exact (hGncomm ‹IsMulCommutative G›).elim
    ·
      have hodd : Odd (Nat.card G) := by simpa [hKtop] using hKodd
      have h2 : 2 ∣ Nat.card G := by
        have := orderOf_dvd_natCard S.z
        rwa [S.orderOf_z] at this
      exact (Nat.not_even_iff_odd.mpr hodd (even_iff_two_dvd.mpr h2)).elim
  ·
    haveI : IsMulCommutative G := IsMulCommutative.of_comm fun a b =>
      (hElem a (by rw [hNtop]; exact Subgroup.mem_top a)
        b (by rw [hNtop]; exact Subgroup.mem_top b)).1
    exact (hGncomm ‹IsMulCommutative G›).elim
  ·
    let eNG : ↥(Subgroup.normalClosure ({S.z} : Set G)) ≃* G :=
      (MulEquiv.subgroupCongr hNtop).trans Subgroup.topEquiv
    let eQ := QuotientGroup.congr
      (Subgroup.center ↥(Subgroup.normalClosure ({S.z} : Set G)))
      (Subgroup.center G) eNG (Subgroup.map_center_eq eNG)
    let eG : (G ⧸ Subgroup.center G) ≃* G :=
      (QuotientGroup.quotientMulEquivOfEq hcenterG).trans QuotientGroup.quotientBot
    exact CorBList.of_mulEquiv (eQ.trans eG) hList

theorem false_of_forall_conj_mem_QG_of_section (hCorB : TimmesfeldCorBInput)
    (hFacts : CorBListFacts) {G : Type} [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G)
    (h : ∀ g : G, g * S.z * g⁻¹ ∈ S.M → g * S.z * g⁻¹ ∈ S.QG)
    (R N : Subgroup G) (hNR : N ≤ R) (hRM : R ≤ S.M) (hN : (N.subgroupOf R).Normal)
    (hsimple : IsSimpleGroup (↥R ⧸ N.subgroupOf R))
    (hnonab : ∀ P : Sylow 2 (↥R ⧸ N.subgroupOf R),
      ∃ x ∈ (P : Subgroup (↥R ⧸ N.subgroupOf R)), ∃ y ∈ (P : Subgroup (↥R ⧸ N.subgroupOf R)),
        x * y ≠ y * x) :
    False := by
  have hGlist : CorBList G := corBList_of_forall_conj_mem_QG hCorB S h
  have hcenterG : Subgroup.center G = ⊥ := center_eq_bot_of_setting S
  have hcenterTop : Subgroup.center (↥(⊤ : Subgroup G)) = ⊥ := by
    ext x
    constructor
    · intro hx
      have hmem : (x : G) ∈ Subgroup.center G := by
        rw [Subgroup.mem_center_iff]
        intro g
        have h := Subgroup.mem_center_iff.mp hx (⟨g, Subgroup.mem_top g⟩ : ↥(⊤ : Subgroup G))
        exact congrArg Subtype.val h
      rw [hcenterG] at hmem
      exact Subtype.ext (by simpa using hmem)
    · intro hx
      rw [hx]
      exact Subgroup.one_mem _
  have htopList : CorBList (↥(⊤ : Subgroup G) ⧸ Subgroup.center ↥(⊤ : Subgroup G)) :=
    CorBList.of_mulEquiv
      (((QuotientGroup.quotientMulEquivOfEq hcenterTop).trans
        QuotientGroup.quotientBot).trans Subgroup.topEquiv).symm hGlist
  obtain ⟨-, -, hsec⟩ := hFacts G (⊤ : Subgroup G) (by infer_instance) htopList
  have hnoncent : ∃ u : G, u * S.z ≠ S.z * u := by
    by_contra hc
    push Not at hc
    have hzcenter : S.z ∈ Subgroup.center G := Subgroup.mem_center_iff.mpr hc
    rw [hcenterG] at hzcenter
    exact S.z_ne_one (by simpa using hzcenter)
  obtain ⟨u, hu⟩ := hnoncent
  obtain ⟨P, hPab⟩ := hsec S.z (Subgroup.mem_top _) S.orderOf_z
    ⟨u, Subgroup.mem_top u, hu⟩ R N hNR (le_inf le_top hRM) hN hsimple
  obtain ⟨x, hxP, y, hyP, hxy⟩ := hnonab P
  exact hxy (hPab x hxP y hyP)

end CFSG.LargeExtraspecial.S8
