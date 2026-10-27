module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFKindDefs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem ff_map_twoRes {A B : Type} [Group A] [Group B] (φ : A →* B)
    (hφ : Function.Injective φ) (H : Subgroup A) : (twoRes H).map φ = twoRes (H.map φ) := by
  unfold twoRes
  rw [MonoidHom.map_closure]
  congr 1
  ext b
  constructor
  · rintro ⟨a, ⟨ha, hodd⟩, rfl⟩
    exact ⟨Subgroup.mem_map_of_mem φ ha, by rwa [orderOf_injective φ hφ a]⟩
  · rintro ⟨hb, hodd⟩
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hb
    exact ⟨a, ⟨ha, by rwa [orderOf_injective φ hφ a] at hodd⟩, rfl⟩

theorem ff_map_twoPrimeRes {A B : Type} [Group A] [Group B] (φ : A →* B)
    (hφ : Function.Injective φ) (H : Subgroup A) :
    (twoPrimeRes H).map φ = twoPrimeRes (H.map φ) := by
  unfold twoPrimeRes
  rw [MonoidHom.map_closure]
  congr 1
  ext b
  constructor
  · rintro ⟨a, ⟨ha, k, hk⟩, rfl⟩
    exact ⟨Subgroup.mem_map_of_mem φ ha, k, by rwa [orderOf_injective φ hφ a]⟩
  · rintro ⟨hb, k, hk⟩
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hb
    exact ⟨a, ⟨ha, k, by rwa [orderOf_injective φ hφ a] at hk⟩, rfl⟩

theorem ff_map_ffX {A B : Type} [Group A] [Group B] (e : A ≃* B) :
    (ffX A).map e.toMonoidHom = ffX B := by
  unfold ffX
  rw [ff_map_twoPrimeRes _ e.injective, ff_map_twoRes _ e.injective,
    Subgroup.map_top_of_surjective _ e.surjective]

theorem ff_layer_map {A B : Type} [Group A] [Group B] (f : A ≃* B) :
    (CFSG.layer A).map f.toMonoidHom = CFSG.layer B := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun K hK => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_sSup (CFSG.LocalCores.isComponent_map_mulEquiv f hK)
  · refine sSup_le fun L hL => ?_
    have hL' : CFSG.IsComponent (L.map f.symm.toMonoidHom) :=
      CFSG.LocalCores.isComponent_map_mulEquiv f.symm hL
    have hle : L.map f.symm.toMonoidHom ≤ CFSG.layer A := le_sSup hL'
    have := Subgroup.map_mono (f := f.toMonoidHom) hle
    rwa [Subgroup.map_map, show f.toMonoidHom.comp f.symm.toMonoidHom = MonoidHom.id B from by
      ext; simp, Subgroup.map_id] at this

theorem ff_inSubgroup_map {A B : Type} [Group A] [Group B]
    (F : ∀ (K : Type) [Group K], Subgroup K)
    (hF : ∀ (K K' : Type) [Group K] [Group K'] (e : K ≃* K'), (F K).map e.toMonoidHom = F K')
    (φ : A →* B) (hφ : Function.Injective φ) (H : Subgroup A) :
    (CFSG.inSubgroup F H).map φ = CFSG.inSubgroup F (H.map φ) := by
  unfold CFSG.inSubgroup
  rw [Subgroup.map_map, ← hF _ _ (H.equivMapOfInjective φ hφ), Subgroup.map_map]
  congr 1

noncomputable def ff_mapEquiv {G B : Type} [Group G] [Group B] {C : Subgroup G} (f : ↥C ≃* B)
    (D : Subgroup ↥C) (D' : Subgroup B) (h : D.map f.toMonoidHom = D') :
    ↥(D.map C.subtype) ≃* ↥D' :=
  (D.equivMapOfInjective C.subtype C.subtype_injective).symm.trans
    ((f.subgroupMap D).trans (MulEquiv.subgroupCongr h))

noncomputable def ff_inSubgroupEquiv {G B : Type} [Group G] [Group B]
    (F : ∀ (K : Type) [Group K], Subgroup K)
    (hF : ∀ (K K' : Type) [Group K] [Group K'] (e : K ≃* K'), (F K).map e.toMonoidHom = F K')
    (C : Subgroup G) (f : ↥C ≃* B) : ↥(CFSG.inSubgroup F C) ≃* ↥(F B) :=
  ff_mapEquiv f (F ↥C) (F B) (hF _ _ f)

theorem ff_mem_inSubgroup_iff {G R : Type} [Group G] [Group R]
    (F : ∀ (K : Type) [Group K], Subgroup K)
    (hF : ∀ (K K' : Type) [Group K] [Group K'] (e : K ≃* K'), (F K).map e.toMonoidHom = F K')
    {L : Subgroup G} (Φ : ↥L ≃* R) {C : Subgroup G} (hCL : C ≤ L) {D : Subgroup R}
    (f : ↥C ≃* ↥D) (hf : ∀ c : ↥C, ((f c : ↥D) : R) = Φ ⟨(c : G), hCL c.2⟩) {u : G}
    (hu : u ∈ L) : u ∈ CFSG.inSubgroup F C ↔ Φ ⟨u, hu⟩ ∈ CFSG.inSubgroup F D := by
  let ι : ↥C →* ↥L := Subgroup.inclusion hCL
  have hD : CFSG.inSubgroup F D = ((F ↥C).map ι).map Φ.toMonoidHom := by
    unfold CFSG.inSubgroup
    rw [← hF _ _ f, Subgroup.map_map, Subgroup.map_map]
    congr 1
    exact MonoidHom.ext hf
  have hC : CFSG.inSubgroup F C = ((F ↥C).map ι).map L.subtype := by
    unfold CFSG.inSubgroup
    rw [Subgroup.map_map]
    rfl
  rw [hD, hC]
  constructor
  · rintro ⟨y, hy, hyu⟩
    have : y = ⟨u, hu⟩ := Subtype.ext hyu
    exact ⟨y, hy, by rw [this]; rfl⟩
  · rintro ⟨y, hy, hyu⟩
    have : y = ⟨u, hu⟩ := Φ.injective hyu
    exact ⟨y, hy, by rw [this]; rfl⟩

theorem ff_oddCore_map_le {A B : Type} [Group A] [Group B] (e : A ≃* B) :
    (CFSG.oddCore A).map e.toMonoidHom ≤ CFSG.oddCore B := by
  rw [Subgroup.map_le_iff_le_comap]
  refine sSup_le fun N hN => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  apply le_sSup
  refine ⟨hN.1.map e.toMonoidHom e.surjective, ?_⟩
  rw [Subgroup.card_map_of_injective e.injective]
  exact hN.2

theorem ff_oddCore_map_equiv {A B : Type} [Group A] [Group B] (e : A ≃* B) :
    (CFSG.oddCore A).map e.toMonoidHom = CFSG.oddCore B := by
  refine le_antisymm (ff_oddCore_map_le e) fun x hx => ?_
  rw [Subgroup.mem_map_equiv]
  exact ff_oddCore_map_le e.symm (Subgroup.mem_map_of_mem e.symm.toMonoidHom hx)

theorem ff_lieModel_quot_oddCore_iff {A B : Type} [Group A] [Group B] (e : A ≃* B)
    {t : CFSG.Open.StatedLieTag} {n p f : ℕ} :
    LieModel (A ⧸ oddCore A) t n p f ↔ LieModel (B ⧸ oddCore B) t n p f := by
  let e' : A ⧸ oddCore A ≃* B ⧸ oddCore B :=
    QuotientGroup.congr (oddCore A) (oddCore B) e (ff_oddCore_map_equiv e)
  exact ⟨LieModel.of_mulEquiv e', LieModel.of_mulEquiv e'.symm⟩

theorem ff_isOmega5_congr {G G' : Type} [Group G] [Group G'] {X : Subgroup G}
    {X' : Subgroup G'} (e : ↥X ≃* ↥X') : IsOmega5 X ↔ IsOmega5 X' :=
  ff_lieModel_quot_oddCore_iff e

theorem ff_isL29_congr {G G' : Type} [Group G] [Group G'] {X : Subgroup G}
    {X' : Subgroup G'} (e : ↥X ≃* ↥X') : IsL29 X ↔ IsL29 X' :=
  ff_lieModel_quot_oddCore_iff e

theorem ff_isL3Eps3_congr {G G' : Type} [Group G] [Group G'] {X : Subgroup G}
    {X' : Subgroup G'} (e : ↥X ≃* ↥X') : IsL3Eps3 X ↔ IsL3Eps3 X' :=
  or_congr (ff_lieModel_quot_oddCore_iff e) (ff_lieModel_quot_oddCore_iff e)

end CFSG.OddStandard.SmallF3.Omega
