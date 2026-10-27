module

public import CFSG.GH74.KGroups.TwoM12Inner
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverExternalFixed
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverExternalConjugacy
public import CFSG.Assembly.ComponentTypeDefs

public section

namespace CFSG.GH74.KGroups.TwoM12

open Subgroup CFSG.Blueprint CFSG.ComponentClassification CFSG.ComponentClassification.M12Cover

variable {L : Type} [Group L] [Finite L] {t : L} {π : L →* NativeSporadic.M12}

abbrev Ext (σ : MulAut L) : Type := L ⋊[(zpowers σ).subtype] ↥(zpowers σ)

instance (σ : MulAut L) : Finite (Ext σ) :=
  Finite.of_equiv (L × ↥(zpowers σ)) (SemidirectProduct.equivProd (φ := (zpowers σ).subtype)).symm

theorem isQuasisimple_of_mulEquiv' {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (h : CFSG.Assembly.IsQuasisimple A) : CFSG.Assembly.IsQuasisimple B := by
  refine ⟨?_, ?_⟩
  · have := (map_commutator_eq A e.toMonoidHom)
    rw [h.1, MonoidHom.range_eq_top.mpr e.surjective, ← _root_.commutator_def] at this
    rw [← this, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr e.surjective]
  · exact (MulEquiv.isSimpleGroup_congr
      (QuotientGroup.congr (center A) (center B) e (map_center_eq e))).mp h.2

theorem card_le_sixty_of_outer
    (hc : IsCover t π) (hq : CFSG.Assembly.IsQuasisimple L)
    (σ : MulAut L) (hσ2 : σ * σ = 1) (hσ1 : σ ≠ 1) (hout : ¬ ∃ u : L, ∀ x : L, σ x = u * x * u⁻¹)
    {P : Subgroup L} (hP : ⁅P, P⁆ = P) (hPσ : ∀ x ∈ P, σ x = x) : Nat.card P ≤ 60 := by
  classical
  have hσ2' : σ ^ 2 = 1 := by rw [sq]; exact hσ2
  have hσord : orderOf σ = 2 := orderOf_eq_prime hσ2' hσ1
  let s : ↥(zpowers σ) := ⟨σ, mem_zpowers σ⟩
  have hs2 : s * s = 1 := Subtype.ext hσ2
  have hs1 : s ≠ 1 := fun h => hσ1 (congrArg Subtype.val h)
  let ι : L →* Ext σ := SemidirectProduct.inl
  let L' : Subgroup (Ext σ) := ι.range
  have hι : Function.Injective ι := SemidirectProduct.inl_injective
  let eL : L ≃* L' := MonoidHom.ofInjective hι
  have hL'ker : L' = SemidirectProduct.rightHom.ker := SemidirectProduct.range_inl_eq_ker_rightHom
  have hL'N : L'.Normal := by rw [hL'ker]; exact MonoidHom.normal_ker _
  let p : Ext σ := SemidirectProduct.inr s
  have hpact : ∀ x : L, p * ι x * p⁻¹ = ι (σ x) := fun x => by
    have := SemidirectProduct.inl_aut (φ := (zpowers σ).subtype) s x
    simpa using this.symm
  have hp2 : p * p = 1 := by
    have h := map_mul (SemidirectProduct.inr : ↥(zpowers σ) →* Ext σ) s s
    rw [hs2, map_one] at h
    exact h.symm
  have hpL : p ∉ L' := by
    intro hp
    rw [hL'ker, MonoidHom.mem_ker] at hp
    have h1 : SemidirectProduct.rightHom p = s := SemidirectProduct.rightHom_inr s
    exact hs1 (h1.symm.trans hp)
  have hporder : orderOf p = 2 := by
    refine orderOf_eq_prime (by rw [sq]; exact hp2) fun h => hpL (h ▸ L'.one_mem)
  let π' : L' →* NativeSporadic.M12 := π.comp eL.symm.toMonoidHom
  have hπ' : Function.Surjective π' := hc.surjective.comp eL.symm.surjective
  let t' : L' := eL t
  have ht' : orderOf t' = 2 := (MulEquiv.orderOf_eq eL t).trans hc.orderOf_t
  have hZ' : center L' = zpowers t' := by
    have h1 := Subgroup.map_center_eq eL
    rw [hc.center_eq, MonoidHom.map_zpowers] at h1
    exact h1.symm
  have hker' : π'.ker = zpowers t' := by
    ext x
    rw [MonoidHom.mem_ker]
    constructor
    · intro hx
      have h1 : eL.symm x ∈ π.ker := hx
      rw [hc.ker_eq] at h1
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h1
      refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
      apply eL.symm.injective
      rw [map_zpow, MulEquiv.symm_apply_apply]
      exact hk
    · intro hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      have h1 : eL.symm (t' ^ k) ∈ π.ker := by
        rw [hc.ker_eq, map_zpow, MulEquiv.symm_apply_apply]
        exact Subgroup.mem_zpowers_iff.2 ⟨k, rfl⟩
      exact h1
  have hkerZ' : π'.ker = center L' := hker'.trans hZ'.symm
  have hLq' : CFSG.Assembly.IsQuasisimple L' := isQuasisimple_of_mulEquiv' eL hq
  have htH : ((t' : L') : Ext σ) = ι t := rfl
  have hCL : centralizer (L' : Set (Ext σ)) = zpowers ((t' : L') : Ext σ) := by
    apply le_antisymm
    · intro x hx
      rw [Subgroup.mem_centralizer_iff] at hx
      have hcom : ∀ y : L, y * x.left = x.left * (x.right : MulAut L) y := fun y => by
        have h1 := congrArg SemidirectProduct.left (hx (ι y) ⟨y, rfl⟩)
        exact h1
      have hr : x.right = 1 ∨ x.right = s := by
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 x.right.2
        have h2 : (x.right : MulAut L) = σ ^ k := hk.symm
        have hmod : σ ^ k = σ ^ (k % 2) := by
          have := zpow_mod_orderOf σ k
          rw [hσord] at this
          simpa using this.symm
        rcases Int.emod_two_eq_zero_or_one k with h | h
        · left
          apply Subtype.ext
          show (x.right : MulAut L) = 1
          rw [h2, hmod, h, zpow_zero]
        · right
          apply Subtype.ext
          show (x.right : MulAut L) = σ
          rw [h2, hmod, h, zpow_one]
      rcases hr with hr | hr
      · have hxl : x = ι x.left := by
          have := SemidirectProduct.inl_left_mul_inr_right x
          rw [hr, map_one, mul_one] at this
          exact this.symm
        have hlc : x.left ∈ center L := by
          rw [Subgroup.mem_center_iff]
          intro y
          have := hcom y
          rw [hr] at this
          simpa using this
        rw [hc.center_eq] at hlc
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hlc
        refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
        rw [htH, ← map_zpow, hk]
        exact hxl.symm
      · exfalso
        apply hout
        refine ⟨x.left⁻¹, fun y => ?_⟩
        have h4 : y * x.left = x.left * σ y := by
          have := hcom y
          rw [hr] at this
          exact this
        calc σ y = x.left⁻¹ * (x.left * σ y) := by group
          _ = x.left⁻¹ * (y * x.left) := by rw [h4]
          _ = x.left⁻¹ * y * x.left⁻¹⁻¹ := by group
    · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
      rintro _ ⟨y, rfl⟩
      rw [htH, ← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hc.t_mem_center y]
  have hidx : L'.index = 2 := by
    rw [hL'ker, Subgroup.index_ker, MonoidHom.range_eq_top.2 SemidirectProduct.rightHom_surjective,
      Subgroup.card_top, Nat.card_zpowers, hσord]
  have hQ : Nonempty (L' ⧸ center L' ≃* NativeSporadic.M12) :=
    ⟨CentralCover.quotientEquivOfKerEqCenter π' hπ' hkerZ'⟩
  obtain ⟨hv, -, -⟩ :=
    ctss_m12_central_double_cover_external_involution_conjugacy_frontier hLq' ht' hZ' hQ hCL
  obtain ⟨v, -, hvp, -⟩ := hv p hpL hporder
  have hconj : IsConj p (((t' : L') : Ext σ) * p) := isConj_iff.2 ⟨(v : Ext σ), hvp⟩
  have hα := CentralCover.fullAction_apply π' hπ' hkerZ' p
  obtain ⟨-, -, -, -, -, -, hcard60, -, -⟩ :=
    ctss_m12_central_double_cover_external_fixed_section_frontier hLq' ht' hZ' π' hπ' hker' hCL
      hidx hpL hporder hconj _ hα
  let P' : Subgroup L' := P.map eL.toMonoidHom
  have hP'R : P' ≤ (centralizer ({p} : Set (Ext σ))).subgroupOf L' := by
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]
    have h1 := hpact x
    rw [hPσ x hx] at h1
    show ι x * p = p * ι x
    calc ι x * p = (p * ι x * p⁻¹) * p := by rw [h1]
      _ = p * ι x := by group
  have hP'perf : ⁅P', P'⁆ = P' := by rw [← Subgroup.map_commutator, hP]
  have hcardP' : Nat.card P' = Nat.card P := Subgroup.card_map_of_injective eL.injective
  calc Nat.card P = Nat.card P' := hcardP'.symm
    _ = Nat.card ↥⁅P', P'⁆ := by rw [hP'perf]
    _ ≤ Nat.card ↥⁅(centralizer ({p} : Set (Ext σ))).subgroupOf L',
          (centralizer ({p} : Set (Ext σ))).subgroupOf L'⁆ :=
        Subgroup.card_le_of_le (Subgroup.commutator_mono hP'R hP'R)
    _ = 60 := hcard60

end CFSG.GH74.KGroups.TwoM12
