module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63PBase

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

@[expose] def l34gImg (E X : Subgroup G) : Subgroup (MulAut ↥E) :=
  (X.subgroupOf (normalizer (E : Set G))).map E.normalizerMonoidHom

theorem mem_l34gImg {E X : Subgroup G} {a : MulAut ↥E} :
    a ∈ l34gImg E X ↔ ∃ (g : G) (hg : g ∈ normalizer (E : Set G)), g ∈ X ∧
      E.normalizerMonoidHom ⟨g, hg⟩ = a := by
  constructor
  · intro ha
    have ha' : a ∈ (X.subgroupOf (normalizer (E : Set G))).map E.normalizerMonoidHom := ha
    rw [Subgroup.mem_map] at ha'
    obtain ⟨g, hgmem, hga⟩ := ha'
    refine ⟨(g : G), g.2, ?_, hga⟩
    rwa [Subgroup.mem_subgroupOf] at hgmem
  · rintro ⟨g, hg, hgX, rfl⟩
    have : E.normalizerMonoidHom ⟨g, hg⟩ ∈
        (X.subgroupOf (normalizer (E : Set G))).map E.normalizerMonoidHom := by
      rw [Subgroup.mem_map]
      exact ⟨⟨g, hg⟩, by rwa [Subgroup.mem_subgroupOf], rfl⟩
    exact this

theorem l34gAct_apply {E : Subgroup G} {g : G} (hg : g ∈ normalizer (E : Set G)) (e : ↥E) :
    ((E.normalizerMonoidHom ⟨g, hg⟩ e : ↥E) : G) = g * e * g⁻¹ :=
  Subgroup.normalizerMonoidHom_apply_apply_coe E ⟨g, hg⟩ e

theorem l34gAct_eq_one_iff {E : Subgroup G} {g : G} (hg : g ∈ normalizer (E : Set G)) :
    E.normalizerMonoidHom ⟨g, hg⟩ = 1 ↔ ∀ e ∈ E, g * e = e * g := by
  constructor
  · intro h e he
    have h2 : E.normalizerMonoidHom ⟨g, hg⟩ ⟨e, he⟩ = ⟨e, he⟩ := by
      rw [h]
      rfl
    have h3 : g * e * g⁻¹ = e := by
      have h4 := congrArg Subtype.val h2
      rw [l34gAct_apply hg] at h4
      exact h4
    calc g * e = (g * e * g⁻¹) * g := by group
      _ = e * g := by rw [h3]
  · intro h
    ext e
    rw [l34gAct_apply hg]
    change g * (e : G) * g⁻¹ = (e : G)
    rw [h e e.2]
    group

theorem l34gImg_mono {E X Y : Subgroup G} (h : X ≤ Y) : l34gImg E X ≤ l34gImg E Y := by
  exact Subgroup.map_mono (Subgroup.subgroupOf_mono (normalizer (E : Set G)) h)

theorem l34gImg_sup {E X Y : Subgroup G} (hX : X ≤ normalizer (E : Set G))
    (hY : Y ≤ normalizer (E : Set G)) : l34gImg E (X ⊔ Y) = l34gImg E X ⊔ l34gImg E Y := by
  change ((X ⊔ Y).subgroupOf (normalizer (E : Set G))).map E.normalizerMonoidHom =
    (X.subgroupOf (normalizer (E : Set G))).map E.normalizerMonoidHom ⊔
      (Y.subgroupOf (normalizer (E : Set G))).map E.normalizerMonoidHom
  rw [Subgroup.subgroupOf_sup hX hY, Subgroup.map_sup]

theorem l34gImg_sSup {E : Subgroup G} {𝒳 : Set (Subgroup G)}
    (h : ∀ X ∈ 𝒳, X ≤ normalizer (E : Set G)) :
    l34gImg E (sSup 𝒳) = sSup (l34gImg E '' 𝒳) := by
  let N := normalizer (E : Set G)
  let S := sSup (l34gImg E '' 𝒳)
  have hle : sSup 𝒳 ≤ N := sSup_le h
  have hsSup : sSup 𝒳 = closure (⋃ X : 𝒳, (X : Set G)) := by
    rw [sSup_eq_iSup']
    exact Subgroup.iSup_eq_closure _
  have claim : ∀ x ∈ sSup 𝒳, ∀ hx : x ∈ N, E.normalizerMonoidHom ⟨x, hx⟩ ∈ S := by
    intro x hx
    rw [hsSup] at hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      intro hyN
      rw [Set.mem_iUnion] at hy
      obtain ⟨X, hyX⟩ := hy
      have hmem : E.normalizerMonoidHom ⟨y, hyN⟩ ∈ l34gImg E (X : Subgroup G) := by
        rw [mem_l34gImg]
        exact ⟨y, hyN, hyX, rfl⟩
      exact le_sSup (Set.mem_image_of_mem (fun Z => l34gImg E Z) X.2) hmem
    | one =>
      intro h1N
      have h1 : (⟨1, h1N⟩ : N) = 1 := Subtype.ext rfl
      rw [h1, map_one]
      exact S.one_mem
    | mul x y hx hy ihx ihy =>
      intro hxyN
      have hxN : x ∈ N := hle (hsSup ▸ hx)
      have hyN : y ∈ N := hle (hsSup ▸ hy)
      have heq : E.normalizerMonoidHom ⟨x * y, hxyN⟩ =
          E.normalizerMonoidHom ⟨x, hxN⟩ * E.normalizerMonoidHom ⟨y, hyN⟩ := by
        rw [← map_mul]
        exact congrArg E.normalizerMonoidHom (Subtype.ext rfl)
      rw [heq]
      exact S.mul_mem (ihx hxN) (ihy hyN)
    | inv x hx ihx =>
      intro hxinvN
      have hxN : x ∈ N := hle (hsSup ▸ hx)
      have heq : E.normalizerMonoidHom ⟨x⁻¹, hxinvN⟩ =
          (E.normalizerMonoidHom ⟨x, hxN⟩)⁻¹ := by
        rw [← map_inv]
        exact congrArg E.normalizerMonoidHom (Subtype.ext rfl)
      rw [heq]
      exact S.inv_mem (ihx hxN)
  apply le_antisymm
  · intro a ha
    obtain ⟨g, hgN, hgX, rfl⟩ := (mem_l34gImg (E := E) (X := sSup 𝒳)).mp ha
    exact claim g hgX hgN
  · apply sSup_le
    rintro T ⟨X, hX, rfl⟩
    exact l34gImg_mono (le_sSup hX)

theorem l34gImg_conjugate {E X : Subgroup G} {g : G} (hg : g ∈ normalizer (E : Set G)) :
    CFSG.conjugate (l34gImg E X) (E.normalizerMonoidHom ⟨g, hg⟩) =
      l34gImg E (CFSG.conjugate X g) := by
  apply le_antisymm
  · intro b hb
    rw [sec63P_mem_conjugate_iff] at hb
    obtain ⟨x, hxN, hxX, hxa⟩ := (mem_l34gImg (E := E) (X := X)).mp hb
    have hgm : g⁻¹ * x * g ∈ normalizer (E : Set G) :=
      (normalizer (E : Set G)).mul_mem
        ((normalizer (E : Set G)).mul_mem ((normalizer (E : Set G)).inv_mem hg) hxN) hg
    have hmem : g⁻¹ * x * g ∈ CFSG.conjugate X g := by
      rw [sec63P_mem_conjugate_iff]
      have hx : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
      rw [hx]
      exact hxX
    refine (mem_l34gImg (E := E) (X := CFSG.conjugate X g)).mpr
      ⟨g⁻¹ * x * g, hgm, hmem, ?_⟩
    have hcong : E.normalizerMonoidHom ⟨g⁻¹ * x * g, hgm⟩ =
        (E.normalizerMonoidHom ⟨g, hg⟩)⁻¹ * E.normalizerMonoidHom ⟨x, hxN⟩ *
          E.normalizerMonoidHom ⟨g, hg⟩ := by
      have h1 : (⟨g⁻¹ * x * g, hgm⟩ : normalizer (E : Set G)) =
          (⟨g, hg⟩ : normalizer (E : Set G))⁻¹ * ⟨x, hxN⟩ *
            (⟨g, hg⟩ : normalizer (E : Set G)) := Subtype.ext rfl
      rw [h1]
      simp only [map_mul, map_inv]
    rw [hcong, hxa]
    group
  · intro b hb
    obtain ⟨y, hyN, hyX, hyb⟩ :=
      (mem_l34gImg (E := E) (X := CFSG.conjugate X g)).mp hb
    rw [sec63P_mem_conjugate_iff]
    rw [← hyb]
    have hzX : g * y * g⁻¹ ∈ X := sec63P_mem_conjugate_iff.mp hyX
    have hzN : g * y * g⁻¹ ∈ normalizer (E : Set G) :=
      (normalizer (E : Set G)).mul_mem
        ((normalizer (E : Set G)).mul_mem hg hyN) ((normalizer (E : Set G)).inv_mem hg)
    refine (mem_l34gImg (E := E) (X := X)).mpr ⟨g * y * g⁻¹, hzN, hzX, ?_⟩
    have hcong : E.normalizerMonoidHom ⟨g * y * g⁻¹, hzN⟩ =
        E.normalizerMonoidHom ⟨g, hg⟩ * E.normalizerMonoidHom ⟨y, hyN⟩ *
          (E.normalizerMonoidHom ⟨g, hg⟩)⁻¹ := by
      have h1 : (⟨g * y * g⁻¹, hzN⟩ : normalizer (E : Set G)) =
          (⟨g, hg⟩ : normalizer (E : Set G)) * ⟨y, hyN⟩ *
            (⟨g, hg⟩ : normalizer (E : Set G))⁻¹ := Subtype.ext rfl
      rw [h1]
      simp only [map_mul, map_inv]
    rw [hcong]

theorem l34gImg_self (E : Subgroup G) :
    l34gImg E E = (MulAut.conj : ↥E →* MulAut ↥E).range := by
  have hconj : ∀ (e : ↥E) (he : (e : G) ∈ normalizer (E : Set G)),
      E.normalizerMonoidHom ⟨(e : G), he⟩ = MulAut.conj e := by
    intro e he
    ext x
    rw [l34gAct_apply he]
    rfl
  apply le_antisymm
  · intro a ha
    obtain ⟨e, he, heE, rfl⟩ := (mem_l34gImg (E := E) (X := E)).mp ha
    exact MonoidHom.mem_range.mpr ⟨⟨e, heE⟩, (hconj ⟨e, heE⟩ he).symm⟩
  · intro a ha
    obtain ⟨e, rfl⟩ := MonoidHom.mem_range.mp ha
    exact (mem_l34gImg (E := E) (X := E)).mpr
      ⟨(e : G), Subgroup.le_normalizer e.2, e.2, hconj e (Subgroup.le_normalizer e.2)⟩

end CFSG.OddStandard.SmallF3.Omega
