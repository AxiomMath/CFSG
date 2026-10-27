module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Fs79.Sylow
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Classification

public section

namespace CFSG.EvenSporadicStandard.Induction.Junction

open Subgroup CFSG.GorensteinWalter

theorem isCyclic_of_ker_le {A B C : Type} [Group A] [Group B] [Group C] (g : A →* B)
    (hg : Function.Surjective g) (h : A →* C) (hh : Function.Surjective h) [IsCyclic C]
    (hker : h.ker ≤ g.ker) : IsCyclic B := by
  obtain ⟨c, hc⟩ := (isCyclic_iff_exists_zpowers_eq_top.1 ‹IsCyclic C›)
  obtain ⟨ĉ, hĉ⟩ := hh c
  have hM : (Subgroup.zpowers ĉ).map h = ⊤ := by
    rw [MonoidHom.map_zpowers, hĉ, hc]
  have := map_eq_top_of_ker_le g hg h hM hker
  rw [MonoidHom.map_zpowers] at this
  exact isCyclic_iff_exists_zpowers_eq_top.2 ⟨g ĉ, this⟩

theorem sylow_image_cyclic_or_dihedral {G K Y : Type} [Group G] [Group K] [Group Y] [Finite G]
    [Finite K] [Finite Y] (hG : HasDihedralSylowTwo G) (ι : K →* G) (q : K →* Y)
    (hq : Function.Surjective q) (hker : ι.ker ≤ q.ker) (SY : Sylow 2 Y) :
    IsCyclic ↥SY ∨ ∃ j : ℕ, 1 ≤ j ∧ Nonempty (↥SY ≃* DihedralGroup (2 ^ j)) := by
  obtain ⟨SK, hSK⟩ := Sylow.mapSurjective_surjective (p := 2) (f := q) hq SY
  have hSKmap : (SK : Subgroup K).map q = (SY : Subgroup Y) := by
    rw [← Sylow.coe_mapSurjective hq SK, hSK]
  let gq : ↥(SK : Subgroup K) →* ↥(SY : Subgroup Y) :=
    (q.comp (SK : Subgroup K).subtype).codRestrict _ (fun x => hSKmap ▸ ⟨x, x.2, rfl⟩)
  have hgq : Function.Surjective gq := by
    rintro ⟨y, hy⟩
    rw [← hSKmap] at hy
    obtain ⟨p, hp, rfl⟩ := hy
    exact ⟨⟨p, hp⟩, rfl⟩
  set R : Subgroup G := (SK : Subgroup K).map ι with hR
  have hR2 : IsPGroup 2 ↥R := SK.isPGroup'.map ι
  obtain ⟨T, hRT⟩ := hR2.exists_le_sylow
  obtain ⟨m, hm, ⟨eT⟩⟩ := hG T
  let f0 : ↥(SK : Subgroup K) →* ↥(T : Subgroup G) :=
    (ι.comp (SK : Subgroup K).subtype).codRestrict _ (fun a => hRT ⟨a, a.2, rfl⟩)
  let H : Subgroup (DihedralGroup (2 ^ m)) :=
    (R.subgroupOf (T : Subgroup G)).map eT.toMonoidHom
  let hι : ↥(SK : Subgroup K) →* ↥H :=
    (eT.toMonoidHom.comp f0).codRestrict H (fun a => ⟨f0 a, ⟨a, a.2, rfl⟩, rfl⟩)
  have hhι : Function.Surjective hι := by
    rintro ⟨d, hd⟩
    obtain ⟨r, hr, rfl⟩ := hd
    obtain ⟨a, ha, har⟩ := (Subgroup.mem_subgroupOf.1 hr : (r : G) ∈ R)
    refine ⟨⟨a, ha⟩, Subtype.ext ?_⟩
    show eT (f0 ⟨a, ha⟩) = eT r
    congr 1
    exact Subtype.ext har
  have hkerι : hι.ker ≤ gq.ker := by
    intro a ha
    rw [MonoidHom.mem_ker] at ha ⊢
    have h1 : eT (f0 a) = 1 := congrArg Subtype.val ha
    have h2 : f0 a = 1 := by simpa using h1
    have h3 : ι (a : K) = 1 := congrArg Subtype.val h2
    have h4 : (a : K) ∈ q.ker := hker h3
    exact Subtype.ext h4
  rcases subgroups_dihedral_twoGroup_cyclic_or_dihedral hm H with hc | ⟨k, hk, ⟨eH⟩⟩
  · left
    exact isCyclic_of_ker_le gq hgq hι hhι hkerι
  · refine isCyclic_or_dihedral_of_dihedral_hom SY.isPGroup' gq hgq (eH.toMonoidHom.comp hι)
      (eH.surjective.comp hhι) ?_
    intro a ha
    rw [MonoidHom.mem_ker] at ha
    apply hkerι
    rw [MonoidHom.mem_ker]
    exact eH.injective (by simpa using ha)

end CFSG.EvenSporadicStandard.Induction.Junction
