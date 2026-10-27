module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.StarBasic

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P5

open Subgroup CFSG.Open CFSG.LocalAnalysis.EvenBN.Tits.N

theorem map_normalClosure_eq_map_subtype_of_range_eq {A B : Type*} [Group A] [Group B] (f : A →* B)
    {R : Subgroup B} (hR : f.range = R) (L : Subgroup A) :
    (normalClosure (L : Set A)).map f =
      (normalClosure (((L.map f).subgroupOf R : Subgroup ↥R) : Set ↥R)).map R.subtype := by
  have hmem : ∀ a, f a ∈ R := fun a => hR ▸ MonoidHom.mem_range.2 ⟨a, rfl⟩
  have hsurj : Function.Surjective (f.codRestrict R hmem) := by
    rintro ⟨b, hb⟩
    rw [← hR] at hb
    obtain ⟨a, rfl⟩ := hb
    exact ⟨a, rfl⟩
  have himg : f.codRestrict R hmem '' (L : Set A) = ((L.map f).subgroupOf R : Set ↥R) := by
    ext y
    simp only [Set.mem_image, SetLike.mem_coe, Subgroup.mem_subgroupOf, Subgroup.mem_map]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a, ha, rfl⟩
    · rintro ⟨a, ha, hay⟩
      exact ⟨a, ha, Subtype.ext hay⟩
  rw [← himg, ← Subgroup.map_normalClosure _ _ hsurj, Subgroup.map_map]
  rfl

theorem imgIn_map_subtype_eq_map {Γ : Type*} [Group Γ] (S : Subgroup Γ) {P : Subgroup Γ}
    (hP : P ≤ normalizer (S : Set Γ)) (M : Subgroup ↥P) :
    imgIn S (M.map P.subtype) = M.map ((conjActHom S).comp (inclusion hP)) := by
  ext x
  rw [mem_imgIn_iff, Subgroup.mem_map]
  constructor
  · rintro ⟨g, hg, hgN, rfl⟩
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.1 hg
    exact ⟨m, hm, (actFun_of_mem S hgN).symm⟩
  · rintro ⟨m, hm, rfl⟩
    exact ⟨m, Subgroup.mem_map.2 ⟨m, hm, rfl⟩, hP m.2, actFun_of_mem S (hP m.2)⟩

theorem imgIn_eq_map_normalClosure {G : Type*} [Group G] (V X J : Subgroup G)
    (hJ : J = (normalClosure (((X.subgroupOf (normalizer (V : Set G))) :
        Subgroup ↥(normalizer (V : Set G))) : Set ↥(normalizer (V : Set G)))).map
      (normalizer (V : Set G)).subtype) :
    imgIn V J = (normalClosure (((imgIn V X).subgroupOf (imgIn V (normalizer (V : Set G))) :
        Subgroup ↥(imgIn V (normalizer (V : Set G)))) : Set ↥(imgIn V (normalizer (V : Set G))))).map
      (imgIn V (normalizer (V : Set G))).subtype := by
  have h1 : J.subgroupOf (normalizer (V : Set G)) =
      normalClosure (((X.subgroupOf (normalizer (V : Set G))) :
        Subgroup ↥(normalizer (V : Set G))) : Set ↥(normalizer (V : Set G))) := by
    rw [hJ]
    exact Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) _
  change (J.subgroupOf (normalizer (V : Set G))).map (conjActHom V) = _
  rw [h1, map_normalClosure_eq_map_subtype_of_range_eq _ (imgIn_normalizer V).symm]
  rfl

theorem range_conjActHom_comp_inclusion {Γ : Type*} [Group Γ] (S : Subgroup Γ) {K : Subgroup Γ}
    (hK : K ≤ normalizer (S : Set Γ)) :
    ((conjActHom S).comp (inclusion hK)).range = imgIn S K := by
  rw [MonoidHom.range_comp, Subgroup.inclusion_range]
  rfl

theorem ker_conjActHom_comp_inclusion {Γ : Type*} [Group Γ] (S : Subgroup Γ) {K : Subgroup Γ}
    (hK : K ≤ normalizer (S : Set Γ)) :
    ((conjActHom S).comp (inclusion hK)).ker = (centralizer (S : Set Γ)).subgroupOf K := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← actFun_eq_one_iff S (hK x.2), actFun_of_mem S (hK x.2)]
  rfl

theorem exists_quotient_equiv_imgIn {Γ : Type*} [Group Γ] {K W : Subgroup Γ}
    (hK : K ≤ normalizer (W : Set Γ)) (hKC : K ⊓ centralizer (W : Set Γ) = W) :
    ∃ _ : (W.subgroupOf K).Normal, Nonempty (↥K ⧸ W.subgroupOf K ≃* ↥(imgIn W K)) := by
  have hker : ((conjActHom W).comp (inclusion hK)).ker = W.subgroupOf K := by
    rw [ker_conjActHom_comp_inclusion, ← inf_subgroupOf_left (centralizer _) K, hKC]
  have hn : (W.subgroupOf K).Normal := hker ▸ MonoidHom.normal_ker _
  exact ⟨hn, ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    ((QuotientGroup.quotientKerEquivRange _).trans
      (MulEquiv.subgroupCongr (range_conjActHom_comp_inclusion W hK)))⟩⟩

theorem quotient_equiv_Ja {G : Type*} [Group G] [Finite G] (V X J : Subgroup G)
    (hXN : X ≤ normalizer (V : Set G))
    (hJ : J = (normalClosure (((X.subgroupOf (normalizer (V : Set G))) :
        Subgroup ↥(normalizer (V : Set G))) : Set ↥(normalizer (V : Set G)))).map
      (normalizer (V : Set G)).subtype)
    {W : Subgroup (MulAut ↥V)}
    (hWn : ∀ h ∈ imgIn V (normalizer (V : Set G)), ∀ w ∈ W, h * w * h⁻¹ ∈ W)
    (hJC : imgIn V J ⊓ centralizer (W : Set (MulAut ↥V)) = W) :
    ∃ _ : (W.subgroupOf (imgIn V J)).Normal,
      Nonempty (↥(imgIn V J) ⧸ W.subgroupOf (imgIn V J) ≃*
        ↥((normalClosure ((((imgIn W (imgIn V X)).subgroupOf
          (imgIn W (normalizer (W : Set (MulAut ↥V)) ⊓ imgIn V (normalizer (V : Set G))))) :
            Subgroup ↥(imgIn W (normalizer (W : Set (MulAut ↥V)) ⊓
              imgIn V (normalizer (V : Set G))))) :
          Set ↥(imgIn W (normalizer (W : Set (MulAut ↥V)) ⊓
              imgIn V (normalizer (V : Set G)))))).map
          (imgIn W (normalizer (W : Set (MulAut ↥V)) ⊓ imgIn V (normalizer (V : Set G)))).subtype)) := by
  have hHsN : imgIn V (normalizer (V : Set G)) ≤ normalizer (W : Set (MulAut ↥V)) := by
    intro h hh
    rw [mem_normalizer_iff]
    intro w
    refine ⟨hWn h hh w, fun hw => ?_⟩
    have := hWn h⁻¹ (Subgroup.inv_mem _ hh) _ hw
    simpa [mul_assoc] using this
  obtain ⟨hn, ⟨e⟩⟩ := exists_quotient_equiv_imgIn ((imgIn_le_range V J).trans hHsN) hJC
  refine ⟨hn, ⟨e.trans (MulEquiv.subgroupCongr ?_)⟩⟩
  have hR : ((conjActHom W).comp (inclusion hHsN)).range =
      imgIn W (normalizer (W : Set (MulAut ↥V)) ⊓ imgIn V (normalizer (V : Set G))) := by
    rw [range_conjActHom_comp_inclusion, inf_eq_right.2 hHsN]
  have hY : ((imgIn V X).subgroupOf (imgIn V (normalizer (V : Set G)))).map
      ((conjActHom W).comp (inclusion hHsN)) = imgIn W (imgIn V X) := by
    rw [← imgIn_map_subtype_eq_map W hHsN, map_subgroupOf_eq_of_le (imgIn_mono V hXN)]
  rw [imgIn_eq_map_normalClosure V X J hJ, imgIn_map_subtype_eq_map W hHsN,
    map_normalClosure_eq_map_subtype_of_range_eq _ hR, hY]

end CFSG.LocalAnalysis.EvenBN.Tits.N.P5
