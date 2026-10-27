module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Quot.Elem

public section

namespace CFSG.EvenSporadicStandard.Induction.Junction

open Subgroup CFSG.EvenSporadicStandard.Induction CFSG.EvenSporadicStandard.Solomon78
  CFSG.EvenSporadicStandard.Induction.Hyp
open scoped commutatorElement

variable {G : Type} [Group G] (M : Subgroup G) [M.Normal]

theorem cq_mem_centralizer_iff {L : Subgroup G} (hL : L ≤ M) (hLp : ⁅L, L⁆ = L) {x : G} :
    cq M x ∈ centralizer ((L.map (cq M) : Subgroup (CQ M)) : Set (CQ M)) ↔
      x ∈ centralizer (L : Set G) := by
  constructor
  · intro h
    have h1 : L.map (cq M) ≤ centralizer (((zpowers x).map (cq M) : Subgroup (CQ M)) :
        Set (CQ M)) := by
      rw [Subgroup.le_centralizer_iff, MonoidHom.map_zpowers, Subgroup.zpowers_le]
      exact h
    have h2 := le_centralizer_of_map_le M hL hLp h1
    exact (Subgroup.le_centralizer_iff.1 h2) (mem_zpowers x)
  · intro h
    refine mem_centralizer_iff.2 ?_
    rintro _ ⟨l, hl, rfl⟩
    rw [← map_mul, ← map_mul, mem_centralizer_iff.1 h l hl]

theorem jstdModulo_lf [Finite G] {Lp Li : Subgroup (CQ M)} (hLp : ⁅Lp, Lp⁆ = Lp)
    (hLi : ⁅Li, Li⁆ = Li) (hLpM : Lp ≤ M.map (cq M)) (hLiM : Li ≤ M.map (cq M))
    (hLpLi : Lp ≤ Li) (s : G)
    (h : StdModulo (Li ⊔ zpowers (cq M s)) (centralizer (Li : Set (CQ M))) Lp) :
    StdModulo (lf M Li ⊔ zpowers s) (centralizer ((lf M Li : Subgroup G) : Set G)) (lf M Lp) := by
  obtain ⟨hZq, hstd⟩ := h
  set L : Subgroup G := lf M Li with hL
  set P : Subgroup G := lf M Lp with hP
  set Y₁ : Subgroup G := L ⊔ zpowers s with hY₁
  set Yq : Subgroup (CQ M) := Li ⊔ zpowers (cq M s) with hYq
  set Zq : Subgroup (CQ M) := centralizer (Li : Set (CQ M)) with hZqdef
  have hLM : L ≤ M := lf_le M Li
  have hLp' : ⁅L, L⁆ = L := commutator_lf M hLi hLiM
  have hLmap : L.map (cq M) = Li := map_lf M hLi hLiM
  have hYmap : Y₁.map (cq M) = Yq := by rw [hY₁, map_sup_zpowers_cq, hLmap]
  let φ : ↥Y₁ →* ↥Yq := ((cq M).comp Y₁.subtype).codRestrict Yq (fun x => by
    rw [← hYmap]
    exact ⟨x, x.2, rfl⟩)
  have hφ : Function.Surjective φ := by
    rintro ⟨y, hy⟩
    rw [← hYmap] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨⟨x, hx⟩, rfl⟩
  have : (Zq.subgroupOf Yq).Normal := hZq
  let ψ : ↥Y₁ →* ↥Yq ⧸ Zq.subgroupOf Yq := (QuotientGroup.mk' (Zq.subgroupOf Yq)).comp φ
  have hψ : Function.Surjective ψ := (QuotientGroup.mk'_surjective _).comp hφ
  have hker : ψ.ker = (centralizer (L : Set G)).subgroupOf Y₁ := by
    ext x
    rw [MonoidHom.mem_ker]
    show (QuotientGroup.mk' (Zq.subgroupOf Yq)) (φ x) = 1 ↔ _
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    show cq M (x : G) ∈ Zq ↔ (x : G) ∈ centralizer (L : Set G)
    rw [hZqdef, ← hLmap]
    exact cq_mem_centralizer_iff M hLM hLp'
  have hZ : ((centralizer (L : Set G)).subgroupOf Y₁).Normal := by
    rw [← hker]
    exact ψ.normal_ker
  refine ⟨hZ, ?_⟩
  let θ : (↥Y₁ ⧸ (centralizer (L : Set G)).subgroupOf Y₁) ≃* ↥Yq ⧸ Zq.subgroupOf Yq :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)
  have hθ : ∀ x : ↥Y₁, θ (QuotientGroup.mk x) = ψ x := fun x => rfl
  have hPL : P ≤ L := le_of_map_le_cq M (lf_le M Lp) (lf_le M Li) (commutator_lf M hLp hLpM)
    hLp' (by rw [map_lf M hLp hLpM, hLmap]; exact hLpLi)
  have hPY : P ≤ Y₁ := hPL.trans le_sup_left
  have hPmap : P.map (cq M) = Lp := map_lf M hLp hLpM
  have E : ((P.subgroupOf Y₁).map (QuotientGroup.mk' ((centralizer (L : Set G)).subgroupOf Y₁))).map
      θ.toMonoidHom = (Lp.subgroupOf Yq).map (QuotientGroup.mk' (Zq.subgroupOf Yq)) := by
    ext y
    simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      refine ⟨φ x, ?_, rfl⟩
      show cq M (x : G) ∈ Lp
      rw [← hPmap]
      exact ⟨x, hx, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      have hw' : (w : CQ M) ∈ P.map (cq M) := by rw [hPmap]; exact hw
      obtain ⟨p, hp, hpw⟩ := hw'
      refine ⟨QuotientGroup.mk' _ ⟨p, hPY hp⟩, ⟨⟨p, hPY hp⟩, hp, rfl⟩, ?_⟩
      rw [QuotientGroup.mk'_apply, hθ]
      show (QuotientGroup.mk' (Zq.subgroupOf Yq)) (φ ⟨p, hPY hp⟩) = _
      congr 1
      exact Subtype.ext hpw
  have h2 := stdBare_map_mulEquiv θ.symm hstd
  have h3 : ((Lp.subgroupOf Yq).map (QuotientGroup.mk' (Zq.subgroupOf Yq))).map
      θ.symm.toMonoidHom = (P.subgroupOf Y₁).map
        (QuotientGroup.mk' ((centralizer (L : Set G)).subgroupOf Y₁)) := by
    rw [← E]
    exact CFSG.LocalCores.map_map_symm θ _
  rwa [h3] at h2

end CFSG.EvenSporadicStandard.Induction.Junction
