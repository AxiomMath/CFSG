module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172XLayer
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172XType
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172XCent
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172Trans

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S172X

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.GLTheoremA.S10 (cs)

variable {Ω : Type} [Group Ω]

theorem map_csIn_subtype (S D : Subgroup Ω) : (csIn S D).map S.subtype = S ⊓ cs D :=
  Subgroup.map_subgroupOf_eq_of_le inf_le_left

theorem glaLayer_csIn_map (S D : Subgroup Ω) :
    (GLALayer (csIn S D)).map S.subtype = GLALayer (S ⊓ cs D) := by
  rw [← map_csIn_subtype S D, Y10F.glaLayer_map S.subtype_injective]

theorem isComponentOf_glaLayer_csIn_iff (S D : Subgroup Ω) :
    IsComponentOf (GLALayer (csIn S D)) (csIn S D) ↔
      IsComponentOf (GLALayer (S ⊓ cs D)) (S ⊓ cs D) := by
  have h := Y10F.isComponentOf_map_iff S.subtype_injective (L := GLALayer (csIn S D))
    (H := csIn S D)
  rw [glaLayer_csIn_map, map_csIn_subtype] at h
  exact h.symm

theorem catalogIs_pSimple_congr_eq {G : Type} [Group G] {p : ℕ} {X X' : Subgroup G}
    (h : X = X') {Q : TauCeti.CFSGIndex → Prop} :
    catalogIs (PSimple p X) Q ↔ catalogIs (PSimple p X') Q := by
  subst h
  exact Iff.rfl

namespace S172Model

variable {S B : Subgroup Ω} {G₀ : Type} [Group G₀] (M : S172Model S B G₀)

theorem glaLayer_centralizer_img {D : Subgroup Ω} (hDB : D ≤ B) :
    GLALayer (Subgroup.centralizer (M.img D : Set G₀)) = (GLALayer (csIn S D)).map M.π :=
  (glaLayer_eq_of_commutator_le (M.csImg_le_centralizer_img D) (M.csImg_normal hDB)
    (M.commutator_centralizer_img_le hDB)).symm.trans
    (glaLayer_map_eq M.π (fun _ hg => M.π_eq_one_mem_center hg) (csIn S D))

theorem isComponentOf_glaLayer_centralizer_img_iff {D : Subgroup Ω} (hDB : D ≤ B) :
    IsComponentOf (GLALayer (Subgroup.centralizer (M.img D : Set G₀)))
        (Subgroup.centralizer (M.img D : Set G₀)) ↔
      IsComponentOf (GLALayer (csIn S D)) (csIn S D) :=
  (isComponentOf_glaLayer_iff_of_commutator_le (M.csImg_le_centralizer_img D) (M.csImg_normal hDB)
    (M.commutator_centralizer_img_le hDB)).symm.trans
    (isComponentOf_glaLayer_map_iff M.π (fun _ hg => M.π_eq_one_mem_center hg) (csIn S D))

theorem layerIs_centralizer_img_iff [Finite Ω] {p : ℕ} (hp : p.Prime) {D : Subgroup Ω} (hDB : D ≤ B)
    {Q : TauCeti.CFSGIndex → Prop} :
    LayerIs p (Subgroup.centralizer (M.img D : Set G₀)) Q ↔ LayerIs p (S ⊓ cs D) Q := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcomp := M.isComponentOf_glaLayer_centralizer_img_iff hDB
  have hcomp' := isComponentOf_glaLayer_csIn_iff S D
  unfold LayerIs
  constructor
  · rintro ⟨h1, h2⟩
    have h1' := hcomp.1 h1
    haveI : Group.IsPerfect ↥(GLALayer (csIn S D)) := ⟨h1'.2.2.1⟩
    refine ⟨hcomp'.1 h1', ?_⟩
    obtain ⟨e⟩ := M.nonempty_pSimple_equiv_map p (K := GLALayer (csIn S D)) inferInstance
    have h3 := (catalogIs_pSimple_congr_eq (p := p) (M.glaLayer_centralizer_img hDB)).1 h2
    have h4 := (CFSG.LocalAnalysis.GLTheoremA.catalogIs_congr e).2 h3
    exact (catalogIs_pSimple_congr_eq (p := p) (glaLayer_csIn_map S D)).1
      ((S172.catalogIs_pSimple_map_iff (GLALayer (csIn S D)) Q).2 h4)
  · rintro ⟨h1, h2⟩
    have h1' := hcomp'.2 h1
    haveI : Group.IsPerfect ↥(GLALayer (csIn S D)) := ⟨h1'.2.2.1⟩
    refine ⟨hcomp.2 h1', ?_⟩
    obtain ⟨e⟩ := M.nonempty_pSimple_equiv_map p (K := GLALayer (csIn S D)) inferInstance
    have h3 := (S172.catalogIs_pSimple_map_iff (GLALayer (csIn S D)) Q).1
      ((catalogIs_pSimple_congr_eq (p := p) (glaLayer_csIn_map S D)).2 h2)
    have h4 := (CFSG.LocalAnalysis.GLTheoremA.catalogIs_congr e).1 h3
    exact (catalogIs_pSimple_congr_eq (p := p) (M.glaLayer_centralizer_img hDB)).2 h4

theorem img_cs_glaLayer [Finite Ω] {D : Subgroup Ω} (hDB : D ≤ B)
    (hc : IsComponentOf (GLALayer (S ⊓ cs D)) (S ⊓ cs D)) :
    M.img (cs (GLALayer (S ⊓ cs D))) =
      M.β.range ⊓
        Subgroup.centralizer (GLALayer (Subgroup.centralizer (M.img D : Set G₀)) : Set G₀) := by
  have hc' := (isComponentOf_glaLayer_csIn_iff S D).2 hc
  haveI : Group.IsPerfect ↥(GLALayer (csIn S D)) := ⟨hc'.2.2.1⟩
  rw [M.glaLayer_centralizer_img hDB, ← glaLayer_csIn_map S D]
  ext g
  rw [Subgroup.mem_inf, M.mem_img]
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact ⟨⟨b, rfl⟩, (M.mem_centralizer_map_iff inferInstance b).1 hb⟩
  · rintro ⟨⟨b, rfl⟩, hb⟩
    exact ⟨b, (M.mem_centralizer_map_iff inferInstance b).2 hb, rfl⟩

theorem img_inf_left (D : Subgroup Ω) : M.img (B ⊓ D) = M.img D := by
  ext g
  rw [M.mem_img, M.mem_img]
  simp only [Subgroup.mem_inf, SetLike.coe_mem, true_and]

theorem mem_of_β_mem_img {D : Subgroup Ω}
    (hxD : ∀ b ∈ B, b ∈ Subgroup.centralizer (S : Set Ω) → b ∈ D) {b : ↥B}
    (hb : M.β b ∈ M.img D) : (b : Ω) ∈ D := by
  obtain ⟨b', hb'D, hbb'⟩ := M.mem_img.1 hb
  have h1 : M.β (b'⁻¹ * b) = 1 := by rw [map_mul, map_inv, hbb', inv_mul_cancel]
  have h2 : ((b'⁻¹ * b : ↥B) : Ω) ∈ Subgroup.centralizer (S : Set Ω) := (M.β_eq_one_iff _).1 h1
  have h3 : ((b'⁻¹ * b : ↥B) : Ω) ∈ D := hxD _ (b'⁻¹ * b).2 h2
  have e : (b : Ω) = (b' : Ω) * ((b'⁻¹ * b : ↥B) : Ω) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [e]
  exact D.mul_mem hb'D h3

theorem eq_inf_of_img_eq {D D' : Subgroup Ω} (hDB : D ≤ B)
    (hxD : ∀ b ∈ B, b ∈ Subgroup.centralizer (S : Set Ω) → b ∈ D)
    (hxD' : ∀ b ∈ B, b ∈ Subgroup.centralizer (S : Set Ω) → b ∈ D') (h : M.img D = M.img D') :
    D = B ⊓ D' := by
  apply le_antisymm
  · intro d hd
    refine ⟨hDB hd, ?_⟩
    have h1 : M.β ⟨d, hDB hd⟩ ∈ M.img D' := h.le (M.mem_img.2 ⟨⟨d, hDB hd⟩, hd, rfl⟩)
    exact M.mem_of_β_mem_img hxD' h1
  · intro b hb
    have h1 : M.β ⟨b, hb.1⟩ ∈ M.img D := h.ge (M.mem_img.2 ⟨⟨b, hb.1⟩, hb.2, rfl⟩)
    exact M.mem_of_β_mem_img hxD h1

theorem card_img_mul_card_inf {D : Subgroup Ω} (hDB : D ≤ B) :
    Nat.card (M.img D) * Nat.card ↥(D ⊓ Subgroup.centralizer (S : Set Ω)) = Nat.card D := by
  let ρ : ↥D →* G₀ := M.β.comp (Subgroup.inclusion hDB)
  have hr : ρ.range = M.img D := by
    ext g
    rw [M.mem_img]
    constructor
    · rintro ⟨d, rfl⟩
      exact ⟨Subgroup.inclusion hDB d, d.2, rfl⟩
    · rintro ⟨b, hb, rfl⟩
      exact ⟨⟨b, hb⟩, rfl⟩
  have hk : ρ.ker.map D.subtype = D ⊓ Subgroup.centralizer (S : Set Ω) := by
    ext a
    constructor
    · rintro ⟨d, hd, rfl⟩
      exact ⟨d.2, (M.β_eq_one_iff (Subgroup.inclusion hDB d)).1 hd⟩
    · rintro ⟨haD, haC⟩
      exact ⟨⟨a, haD⟩, (M.β_eq_one_iff ⟨a, hDB haD⟩).2 haC, rfl⟩
  have h := Subgroup.card_ker_mul_card_range ρ
  rw [hr, ← Subgroup.card_map_of_injective D.subtype_injective (K := ρ.ker), hk] at h
  rw [mul_comm]
  exact h

@[expose] def preimg (Y : Subgroup G₀) : Subgroup Ω := (Y.comap M.β).map B.subtype

theorem mem_preimg {Y : Subgroup G₀} {a : Ω} :
    a ∈ M.preimg Y ↔ ∃ b : ↥B, (b : Ω) = a ∧ M.β b ∈ Y := by
  simp only [preimg, Subgroup.mem_map, Subgroup.mem_comap, Subgroup.subtype_apply]
  exact ⟨fun ⟨b, hb, h⟩ => ⟨b, h, hb⟩, fun ⟨b, h, hb⟩ => ⟨b, hb, h⟩⟩

theorem preimg_le (Y : Subgroup G₀) : M.preimg Y ≤ B := by
  intro a ha
  obtain ⟨b, rfl, -⟩ := M.mem_preimg.1 ha
  exact b.2

theorem centralizer_le_preimg (Y : Subgroup G₀) :
    ∀ b ∈ B, b ∈ Subgroup.centralizer (S : Set Ω) → b ∈ M.preimg Y := by
  intro b hb hbc
  exact M.mem_preimg.2 ⟨⟨b, hb⟩, rfl, by rw [(M.β_eq_one_iff ⟨b, hb⟩).2 hbc]; exact Y.one_mem⟩

theorem img_preimg {Y : Subgroup G₀} (hY : Y ≤ M.β.range) : M.img (M.preimg Y) = Y := by
  ext g
  rw [M.mem_img]
  constructor
  · rintro ⟨b, hb, rfl⟩
    obtain ⟨b', hb', hY'⟩ := M.mem_preimg.1 hb
    have : b' = b := Subtype.ext hb'
    rwa [this] at hY'
  · intro hg
    obtain ⟨b, rfl⟩ := hY hg
    exact ⟨b, M.mem_preimg.2 ⟨b, rfl, hg⟩, rfl⟩

end S172Model

theorem glaPLayer_eq_bot_of_isSolvable {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {X : Subgroup G} [Group.IsSolvable ↥X] : GLAPLayer p X = ⊥ := by
  have h := Y10F.glaPLayer_map hp X.subtype_injective (⊤ : Subgroup ↥X)
  rw [CFSG.LocalAnalysis.GLTheoremA.I142N.map_subtype_top,
    CFSG.LocalAnalysis.GLTheoremB.glaPLayer_top_eq_bot_of_isSolvable p, Subgroup.map_bot] at h
  exact h

namespace S172Model

variable {S B : Subgroup Ω} {G₀ : Type} [Group G₀] (M : S172Model S B G₀)

theorem glaPLayer_eq_bot_of_csImg_le [Finite Ω] {p : ℕ} (hp : p.Prime) {E : Subgroup Ω}
    {X : Subgroup G₀} [Group.IsSolvable ↥X] (hX : M.csImg E ≤ X) {K : Subgroup Ω} (hKS : K ≤ S) :
    GLAPLayer p (K ⊓ cs E) = ⊥ := by
  have h1 : Group.IsSolvable ↥(csIn S E) :=
    isSolvable_of_map_le M.π (fun _ hg => M.π_eq_one_mem_center hg) hX
  haveI : Group.IsSolvable ↥((csIn S E).map S.subtype) :=
    solvable_of_surjective (f := (Subgroup.equivMapOfInjective (csIn S E) S.subtype
      S.subtype_injective).toMonoidHom)
      (Subgroup.equivMapOfInjective (csIn S E) S.subtype S.subtype_injective).surjective
  have hle : K ⊓ cs E ≤ (csIn S E).map S.subtype := by
    rw [map_csIn_subtype]
    exact inf_le_inf_right _ hKS
  haveI : Group.IsSolvable ↥(K ⊓ cs E) :=
    solvable_of_solvable_injective (Subgroup.inclusion_injective hle)
  exact glaPLayer_eq_bot_of_isSolvable hp

end S172Model

end CFSG.LocalAnalysis.GLTheoremA.S172X

end
