module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.P6bData

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P6b

open Subgroup CFSG.Sporadic.Schreier.Tits CFSG.LocalAnalysis.EvenBN.Tits CFSG.Open

section Gen

theorem nonempty_quotEquiv_comap {Γ Γ' : Type*} [Group Γ] [Group Γ'] (φ : Γ →* Γ')
    (hφ : Function.Surjective φ) (N' : Subgroup Γ') [N'.Normal] :
    Nonempty (Γ ⧸ N'.comap φ ≃* Γ' ⧸ N') := by
  have hs : Function.Surjective ((QuotientGroup.mk' N').comp φ) :=
    (QuotientGroup.mk'_surjective N').comp hφ
  have hker : ((QuotientGroup.mk' N').comp φ).ker = N'.comap φ := by
    ext g
    simp [MonoidHom.mem_ker, QuotientGroup.eq_one_iff]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ hs)⟩

end Gen


section JStar

variable {G : Type} [Group G] [Finite G] {d : Data G} {z₀ : G}


theorem Jg_le_Hg (d : Data G) : Jg d ≤ Hg d := Subgroup.map_subtype_le _

theorem Jg_conj_mem {h : G} (hh : h ∈ Hg d) {g : G} (hg : g ∈ Jg d) : h * g * h⁻¹ ∈ Jg d := by
  obtain ⟨g', hg', rfl⟩ := hg
  refine ⟨(⟨h, hh⟩ : ↥(Hg d)) * g' * (⟨h, hh⟩ : ↥(Hg d))⁻¹, ?_, rfl⟩
  exact Subgroup.Normal.conj_mem Subgroup.normalClosure_normal g' hg' _

theorem x5_mem_Jg (h49 : d.Thm49Statement) (hd : d.Hyp) : d.x₅ ∈ Jg d :=
  ⟨⟨d.x₅, x5_mem_H h49 hd⟩, Subgroup.subset_normalClosure
    (Subgroup.mem_subgroupOf.2 (mem_zpowers _)), rfl⟩


@[expose] noncomputable def starHom (d : Data G) : ↥(Hg d) →* ↥(Hs d) :=
  (conjActHom d.s56V).codRestrict (Hs d) (fun g => by
    have h1 : actFun d.s56V (g : G) ∈ imgIn d.s56V (Hg d) := actFun_mem_imgIn g.2 g.2
    rwa [actFun_of_mem d.s56V g.2] at h1)

theorem starHom_val (g : ↥(Hg d)) : ((starHom d g : ↥(Hs d)) : MulAut ↥d.s56V) = star d (g : G) := by
  show conjActHom d.s56V g = actFun d.s56V (g : G)
  rw [actFun_of_mem d.s56V g.2]
  rfl

theorem mem_Js_iff {σ : MulAut ↥d.s56V} : σ ∈ img d (Jg d) ↔ ∃ g ∈ Jg d, star d g = σ := by
  rw [img, mem_imgIn_iff]
  constructor
  · rintro ⟨g, hg, _, rfl⟩
    exact ⟨g, hg, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g, hg, Jg_le_Hg d hg, rfl⟩

@[expose] noncomputable def xB (h49 : d.Thm49Statement) (hd : d.Hyp) : ↥(Hs d) :=
  starB d d.x₅ (x5_mem_H h49 hd)

theorem Jb_map_eq (h49 : d.Thm49Statement) (hd : d.Hyp) :
    (normalClosure ({xB h49 hd} : Set ↥(Hs d))).map (Hs d).subtype = img d (Jg d) := by
  apply le_antisymm
  · rintro _ ⟨σ, hσ, rfl⟩
    have hnorm : ((img d (Jg d)).subgroupOf (Hs d)).Normal := by
      refine ⟨fun n hn g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      obtain ⟨j, hj, hjn⟩ := (mem_Js_iff).1 hn
      obtain ⟨h, hh, hhN, hhg⟩ := (mem_imgIn_iff d.s56V (Hg d)).1 g.2
      refine (mem_Js_iff).2 ⟨h * j * h⁻¹, Jg_conj_mem hh hj, ?_⟩
      have hjH := Jg_le_Hg d hj
      have e1 : star d (h * j * h⁻¹) = star d h * star d j * (star d h)⁻¹ :=
        actFun_conj d.s56V hh hjH
      have e2 : star d h = (g : MulAut ↥d.s56V) := hhg
      have e3 : (↑(g * n * g⁻¹ : ↥(Hs d)) : MulAut ↥d.s56V) =
          (g : MulAut ↥d.s56V) * (n : MulAut ↥d.s56V) * (g : MulAut ↥d.s56V)⁻¹ := rfl
      rw [e3, ← e2, ← hjn]
      exact e1
    haveI := hnorm
    have hx : xB h49 hd ∈ (img d (Jg d)).subgroupOf (Hs d) := by
      rw [Subgroup.mem_subgroupOf]
      exact (mem_Js_iff).2 ⟨d.x₅, x5_mem_Jg h49 hd, rfl⟩
    have hsub : ({xB h49 hd} : Set ↥(Hs d)) ⊆
        (((img d (Jg d)).subgroupOf (Hs d) : Subgroup ↥(Hs d)) : Set ↥(Hs d)) := by
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact hx
    have := Subgroup.normalClosure_le_normal hsub hσ
    exact Subgroup.mem_subgroupOf.1 this
  · intro τ hτ
    obtain ⟨g, hg, rfl⟩ := (mem_Js_iff).1 hτ
    obtain ⟨g', hg', rfl⟩ := hg
    refine ⟨starHom d g', ?_, starHom_val g'⟩
    have hle : (normalClosure (((Xg d).subgroupOf (Hg d) : Subgroup ↥(Hg d)) : Set ↥(Hg d))).map
        (starHom d) ≤ normalClosure ({xB h49 hd} : Set ↥(Hs d)) := by
      rw [Subgroup.map_le_iff_le_comap]
      refine Subgroup.normalClosure_le_normal (fun y hy => ?_)
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hy
      obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hy
      have hyk : y = (⟨d.x₅, x5_mem_H h49 hd⟩ : ↥(Hg d)) ^ k :=
        Subtype.ext (by rw [← hk]; simp)
      have hxB : starHom d ⟨d.x₅, x5_mem_H h49 hd⟩ = xB h49 hd :=
        Subtype.ext (by rw [starHom_val]; rfl)
      rw [SetLike.mem_coe, Subgroup.mem_comap, hyk, map_zpow, hxB]
      exact zpow_mem (Subgroup.subset_normalClosure (Set.mem_singleton _)) k
    exact hle (Subgroup.mem_map_of_mem (starHom d) hg')


theorem Wb_normal (hWnorm : ∀ h ∈ Hs d, ∀ w ∈ Ws d, h * w * h⁻¹ ∈ Ws d) :
    ((Ws d).subgroupOf (Hs d)).Normal :=
  ⟨fun n hn g => Subgroup.mem_subgroupOf.2 (by
    simpa using hWnorm (g : MulAut ↥d.s56V) g.2 n (Subgroup.mem_subgroupOf.1 hn))⟩

theorem Wb_le_Jb (h49 : d.Thm49Statement) (hd : d.Hyp) (hWJ : Ws d ≤ img d (Jg d)) :
    (Ws d).subgroupOf (Hs d) ≤ normalClosure ({xB h49 hd} : Set ↥(Hs d)) := by
  intro τ hτ
  have h1 : (τ : MulAut ↥d.s56V) ∈ img d (Jg d) := hWJ (Subgroup.mem_subgroupOf.1 hτ)
  rw [← Jb_map_eq h49 hd] at h1
  obtain ⟨σ, hσ, hστ⟩ := h1
  have : σ = τ := Subtype.ext hστ
  rwa [← this]

theorem jb_quot_equiv (h49 : d.Thm49Statement) (hd : d.Hyp)
    [hWb : ((Ws d).subgroupOf (Hs d)).Normal] (hWJ : Ws d ≤ img d (Jg d))
    [hN : ((Ws d).subgroupOf (img d (Jg d))).Normal] (A : Type*) [Group A]
    (e : ↥(img d (Jg d)) ⧸ (Ws d).subgroupOf (img d (Jg d)) ≃* A) :
    Nonempty (↥(normalClosure ({xB h49 hd} : Set ↥(Hs d))) ⧸
      ((Ws d).subgroupOf (Hs d)).subgroupOf (normalClosure ({xB h49 hd} : Set ↥(Hs d))) ≃* A) := by
  set Jb := normalClosure ({xB h49 hd} : Set ↥(Hs d)) with hJb
  let ψ : ↥Jb ≃* ↥(img d (Jg d)) :=
    (Subgroup.equivMapOfInjective Jb (Hs d).subtype (Hs d).subtype_injective).trans
      (MulEquiv.subgroupCongr (Jb_map_eq h49 hd))
  have hψ : ∀ k : ↥Jb, ((ψ k : ↥(img d (Jg d))) : MulAut ↥d.s56V) = ((k : ↥(Hs d)) : MulAut ↥d.s56V) :=
    fun k => rfl
  have hmap : (((Ws d).subgroupOf (Hs d)).subgroupOf Jb).map ψ.toMonoidHom =
      (Ws d).subgroupOf (img d (Jg d)) := by
    ext τ
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, MulEquiv.coe_toMonoidHom]
    constructor
    · rintro ⟨k, hk, rfl⟩
      rw [hψ]
      exact hk
    · intro hτ
      refine ⟨ψ.symm τ, ?_, ψ.apply_symm_apply τ⟩
      have := hψ (ψ.symm τ)
      rw [ψ.apply_symm_apply] at this
      rw [← this]
      exact hτ
  exact ⟨(QuotientGroup.congr _ _ ψ hmap).trans e⟩


@[expose] noncomputable def jpHom (d : Data G) : ↥(Jp d) →* ↥(img d (Jg d)) where
  toFun g := ⟨actFun d.s56V (g : G), ((mem_preIn_iff d.s56V _).1 g.2).2⟩
  map_one' := by
    refine Subtype.ext ?_
    exact actFun_one d.s56V
  map_mul' g h := by
    refine Subtype.ext ?_
    exact actFun_mul d.s56V ((mem_preIn_iff d.s56V _).1 g.2).1 ((mem_preIn_iff d.s56V _).1 h.2).1

theorem jpHom_surjective : Function.Surjective (jpHom d) := by
  rintro ⟨τ, hτ⟩
  obtain ⟨g, hg, rfl⟩ := (mem_Js_iff).1 hτ
  have hgJp : g ∈ Jp d := (mem_preIn_iff d.s56V _).2 ⟨Jg_le_Hg d hg, hτ⟩
  exact ⟨⟨g, hgJp⟩, rfl⟩

theorem jp_quot_equiv (hz : d.S56Z0 z₀) (hWimg : img d (Wg d z₀) = Ws d)
    [hN : ((Ws d).subgroupOf (img d (Jg d))).Normal] (A : Type*) [Group A]
    (e : ↥(img d (Jg d)) ⧸ (Ws d).subgroupOf (img d (Jg d)) ≃* A) :
    ∃ _ : ((Wg d z₀).subgroupOf (Jp d)).Normal,
      Nonempty (↥(Jp d) ⧸ (Wg d z₀).subgroupOf (Jp d) ≃* A) := by
  have hcomap : ((Ws d).subgroupOf (img d (Jg d))).comap (jpHom d) = (Wg d z₀).subgroupOf (Jp d) := by
    ext g
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Wg_eq_pre hz hWimg]
    constructor
    · intro h
      exact (mem_preIn_iff d.s56V _).2 ⟨((mem_preIn_iff d.s56V _).1 g.2).1, h⟩
    · intro h
      exact ((mem_preIn_iff d.s56V _).1 h).2
  haveI : ((Wg d z₀).subgroupOf (Jp d)).Normal := hcomap ▸ Subgroup.normal_comap _
  obtain ⟨e'⟩ := nonempty_quotEquiv_comap (jpHom d) jpHom_surjective ((Ws d).subgroupOf (img d (Jg d)))
  exact ⟨‹_›, ⟨(QuotientGroup.quotientMulEquivOfEq hcomap.symm).trans (e'.trans e)⟩⟩

end JStar

end CFSG.LocalAnalysis.EvenBN.Tits.N.P6b
