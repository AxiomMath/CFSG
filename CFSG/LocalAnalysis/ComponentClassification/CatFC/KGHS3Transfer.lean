module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.KGHS3Lift

public section

namespace CFSG.ComponentClassification.CatFC.KGHS3

open Subgroup

theorem exists_quasisimple_of_relation {G₁ G₂ : Type} [Group G₁] [Group G₂]
    (R : Subgroup (G₁ × G₂))
    (hK1 : ∀ h : G₂, (1, h) ∈ R → h ∈ Subgroup.center G₂)
    (hK2 : Group.IsSolvable ↥(R.comap (MonoidHom.inl G₁ G₂)))
    (Y : Subgroup G₁) (hY : CFSG.IsQuasisimple Y) (hYR : ∀ y ∈ Y, ∃ s, (y, s) ∈ R) :
    ∃ Y₂ : Subgroup G₂, (∀ s ∈ Y₂, ∃ g, (g, s) ∈ R) ∧ CFSG.IsQuasisimple Y₂ ∧
      Nonempty (↥Y₂ ⧸ center ↥Y₂ ≃* ↥Y ⧸ center ↥Y) := by
  classical
  set Γ : Subgroup (G₁ × G₂) := R ⊓ Y.comap (MonoidHom.fst G₁ G₂) with hΓ
  let f : ↥Γ →* G₁ := (MonoidHom.fst G₁ G₂).comp Γ.subtype
  have hf_apply : ∀ x : ↥Γ, f x = x.1.1 := fun x => rfl
  have hker : f.ker ≤ center ↥Γ := by
    intro x hx
    rw [MonoidHom.mem_ker, hf_apply] at hx
    have hxR : x.1 ∈ R := x.2.1
    have hs : x.1.2 ∈ center G₂ := by
      apply hK1
      have : x.1 = (1, x.1.2) := Prod.ext hx rfl
      rwa [this] at hxR
    rw [Subgroup.mem_center_iff]
    intro z
    apply Subtype.ext
    have hz := Subgroup.mem_center_iff.mp hs z.1.2
    refine Prod.ext ?_ ?_
    · show z.1.1 * x.1.1 = x.1.1 * z.1.1
      rw [hx]; simp
    · show z.1.2 * x.1.2 = x.1.2 * z.1.2
      exact hz
  have hKf : Y ≤ f.range := by
    intro y hy
    obtain ⟨s, hs⟩ := hYR y hy
    exact ⟨⟨(y, s), hs, hy⟩, rfl⟩
  obtain ⟨Yh, hYh, hmap, hcent, ⟨e₁⟩⟩ := exists_quasisimple_lift_of_hom f hker Y hY hKf
  let g : ↥Yh →* G₂ := (MonoidHom.snd G₁ G₂).comp (Γ.subtype.comp Yh.subtype)
  have hg_apply : ∀ x : ↥Yh, g x = x.1.1.2 := fun x => rfl
  have hfYh : ∀ x : ↥Yh, f x.1 ∈ Y := by
    intro x
    have : f x.1 ∈ Yh.map f := Subgroup.mem_map_of_mem f x.2
    rwa [hmap] at this
  let fY : ↥Yh →* ↥Y := MonoidHom.codRestrict (f.comp Yh.subtype) Y hfYh
  have hfY_apply : ∀ x : ↥Yh, (fY x : G₁) = f x.1 := fun x => rfl
  have hfY_surj : Function.Surjective fY := by
    intro y
    have : (y : G₁) ∈ Yh.map f := by rw [hmap]; exact y.2
    obtain ⟨x, hx, hxy⟩ := this
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  have hker_solv : Group.IsSolvable ↥g.ker := by
    let ψ : ↥g.ker →* ↥(R.comap (MonoidHom.inl G₁ G₂)) :=
      { toFun := fun n => ⟨f n.1.1, by
          have h1 : g n.1 = 1 := n.2
          rw [hg_apply] at h1
          have hR : n.1.1.1 ∈ R := n.1.1.2.1
          have : n.1.1.1 = (n.1.1.1.1, 1) := Prod.ext rfl h1
          rw [Subgroup.mem_comap]
          show (n.1.1.1.1, (1 : G₂)) ∈ R
          rwa [this] at hR⟩
        map_one' := by apply Subtype.ext; simp
        map_mul' := by intro a b; apply Subtype.ext; simp }
    have hψ : Function.Injective ψ := by
      intro a b hab
      have h1 : f a.1.1 = f b.1.1 := congrArg Subtype.val hab
      have ha : g a.1 = 1 := a.2
      have hb : g b.1 = 1 := b.2
      rw [hg_apply] at ha hb
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      refine Prod.ext ?_ ?_
      · exact h1
      · exact ha.trans hb.symm
    exact Group.isSolvable_of_isSolvable_injective hψ
  let N' : Subgroup ↥Y := g.ker.map fY
  haveI : N'.Normal := Subgroup.Normal.map inferInstance fY hfY_surj
  haveI : Group.IsSolvable ↥N' := Group.isSolvable_of_surjective (MonoidHom.subgroupMap_surjective fY g.ker)
  have hN'c : N' ≤ center ↥Y := le_center_of_normal_isSolvable hY N'
  have hgker : g.ker ≤ center ↥Yh := by
    intro n hn
    have h1 : fY n ∈ center ↥Y := hN'c (Subgroup.mem_map_of_mem fY hn)
    have h2 : ∀ k ∈ Y, k * f n.1 = f n.1 * k := by
      intro k hk
      have := Subgroup.mem_center_iff.mp h1 ⟨k, hk⟩
      exact congrArg Subtype.val this
    rw [Subgroup.mem_center_iff]
    intro z
    apply Subtype.ext
    exact hcent n.1 n.2 h2 z.1 z.2
  obtain ⟨hq2, ⟨e₂⟩⟩ := quasisimple_range_of_ker_le_center hYh g hgker
  refine ⟨g.range, ?_, hq2, ⟨e₂.trans e₁⟩⟩
  rintro s ⟨x, rfl⟩
  exact ⟨x.1.1.1, by rw [hg_apply]; exact x.1.2.1⟩

end CFSG.ComponentClassification.CatFC.KGHS3
