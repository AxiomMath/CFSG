module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.GLTheoremA.S8.Defs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Timm.UnitaryPoint

open Subgroup CFSG.Open CFSG.LocalAnalysis.GLTheoremA.S8

theorem mem_map_equiv_iff {G H : Type} [Group G] [Group H] (e : G ≃* H) (S : Set G) (x : H) :
    x ∈ e '' S ↔ e.symm x ∈ S := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro h
    exact ⟨e.symm x, h, by simp⟩

theorem normalizer_image_equiv {G H : Type} [Group G] [Group H] (e : G ≃* H) (S : Set G) :
    Subgroup.normalizer (e '' S) = (Subgroup.normalizer S).map e.toMonoidHom := by
  ext h
  rw [Subgroup.mem_map]
  constructor
  · intro hh
    refine ⟨e.symm h, ?_, by simp⟩
    intro n
    have := hh (e n)
    rw [mem_map_equiv_iff, mem_map_equiv_iff] at this
    have hn : e.symm (e n) = n := by simp
    have hc : e.symm (h * e n * h⁻¹) = e.symm h * n * (e.symm h)⁻¹ := by simp
    rw [hn, hc] at this
    exact this
  · rintro ⟨g, hg, rfl⟩
    intro n
    rw [mem_map_equiv_iff, mem_map_equiv_iff]
    simp only [MulEquiv.coe_toMonoidHom, map_mul, map_inv, MulEquiv.symm_apply_apply]
    exact hg (e.symm n)

theorem isTwoLocal_map_of {K L : Type} [Group K] [Group L] (f : K ≃* L) (X : Subgroup K)
    (hX : IsTwoLocal X) : IsTwoLocal (X.map f.toMonoidHom) := by
  obtain ⟨P, hP, hpP, rfl⟩ := hX
  refine ⟨P.map f.toMonoidHom, ?_, hpP.map f.toMonoidHom, ?_⟩
  · intro h
    apply hP
    rw [eq_bot_iff]
    intro x hx
    have hm : f x ∈ P.map f.toMonoidHom := Subgroup.mem_map_of_mem _ hx
    rw [h, Subgroup.mem_bot] at hm
    rw [Subgroup.mem_bot]
    exact f.injective (by simpa using hm)
  · rw [← normalizer_image_equiv, Subgroup.coe_map]
    rfl

theorem isTwoLocal_map_iff {G H : Type} [Group G] [Group H] (e : G ≃* H) (M : Subgroup G) :
    IsTwoLocal (M.map e.toMonoidHom) ↔ IsTwoLocal M := by
  constructor
  · intro h
    have h' := isTwoLocal_map_of e.symm _ h
    rw [Subgroup.map_map] at h'
    have hid : (e.symm.toMonoidHom.comp e.toMonoidHom) = MonoidHom.id G := by
      ext x
      simp
    rw [hid, Subgroup.map_id] at h'
    exact h'
  · exact isTwoLocal_map_of e M

theorem isMaxTwoLocal_map_iff {G H : Type} [Group G] [Group H] (e : G ≃* H) (M : Subgroup G) :
    IsMaxTwoLocalSubgroup (M.map e.toMonoidHom) ↔ IsMaxTwoLocalSubgroup M := by
  unfold IsMaxTwoLocalSubgroup
  rw [isTwoLocal_map_iff]
  constructor
  · rintro ⟨hM, hmax⟩
    refine ⟨hM, fun H' hH' hle => ?_⟩
    have hle' : M.map e.toMonoidHom ≤ H'.map e.toMonoidHom := Subgroup.map_mono hle
    have := hmax (H'.map e.toMonoidHom) (isTwoLocal_map_of e H' hH') hle'
    exact Subgroup.map_injective e.injective this
  · rintro ⟨hM, hmax⟩
    refine ⟨hM, fun H'' hH'' hle => ?_⟩
    have hH3 : IsTwoLocal (H''.map e.symm.toMonoidHom) := isTwoLocal_map_of e.symm H'' hH''
    have hle' : M ≤ H''.map e.symm.toMonoidHom := by
      intro x hx
      have hx' : e x ∈ H'' := hle (Subgroup.mem_map_of_mem _ hx)
      exact Subgroup.mem_map.2 ⟨e x, hx', by simp⟩
    have heq := hmax _ hH3 hle'
    have h2 : (H''.map e.symm.toMonoidHom).map e.toMonoidHom = H'' := by
      rw [Subgroup.map_map]
      have hid : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id H := by
        ext x
        simp
      rw [hid, Subgroup.map_id]
    rw [← h2, heq]

theorem pCoreOf_map_equiv {G H : Type} [Group G] [Group H] (e : G ≃* H) (M : Subgroup G) :
    pCoreOf 2 (M.map e.toMonoidHom) = (pCoreOf 2 M).map e.toMonoidHom := by
  have hpc : Subgroup.map (MulEquiv.subgroupMap e M).toMonoidHom (pCore 2 ↥M) =
      pCore 2 ↥(M.map e.toMonoidHom) := CFSG.pCore_map_iso 2 _
  unfold pCoreOf
  erw [← hpc, Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem frattini_map_equiv {A B : Type} [Group A] [Group B] (θ : A ≃* B) :
    Subgroup.map θ.toMonoidHom (frattini A) = frattini B := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    exact frattini_le_comap_frattini_of_surjective (φ := θ.toMonoidHom) θ.surjective
  · have h2 : frattini B ≤ (frattini A).comap θ.symm.toMonoidHom :=
      frattini_le_comap_frattini_of_surjective (φ := θ.symm.toMonoidHom) θ.symm.surjective
    have h3 : Subgroup.map θ.symm.toMonoidHom (frattini B) ≤ frattini A :=
      Subgroup.map_le_iff_le_comap.2 h2
    have hid : θ.toMonoidHom.comp θ.symm.toMonoidHom = MonoidHom.id B := by
      ext x
      simp
    calc frattini B = Subgroup.map θ.toMonoidHom (Subgroup.map θ.symm.toMonoidHom (frattini B)) := by
          rw [Subgroup.map_map, hid, Subgroup.map_id]
      _ ≤ Subgroup.map θ.toMonoidHom (frattini A) := Subgroup.map_mono h3

theorem commutator_map_equiv {A B : Type} [Group A] [Group B] (θ : A ≃* B) :
    Subgroup.map θ.toMonoidHom (commutator A) = commutator B := by
  unfold _root_.commutator
  rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective _ θ.surjective]

theorem timmesfeldIsExtraspecial_of_equiv {A B : Type} [Group A] [Group B] (θ : A ≃* B)
    (h : CFSG.Open.timmesfeldIsExtraspecial A) : CFSG.Open.timmesfeldIsExtraspecial B := by
  unfold CFSG.Open.timmesfeldIsExtraspecial at h ⊢
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hfr := frattini_map_equiv θ
  have hcom := commutator_map_equiv θ
  have hcen : Subgroup.map θ.toMonoidHom (Subgroup.center A) = Subgroup.center B :=
    map_center_eq θ
  refine ⟨h1.of_equiv θ, ?_, ?_, ?_⟩
  · rw [← hcom, ← hfr, h2]
  · rw [← hfr, ← hcen, h3]
  · rw [← hcen, Subgroup.card_map_of_injective (f := θ.toMonoidHom) θ.injective]
    exact h4

end CFSG.LocalAnalysis.GLTheoremA.Timm.UnitaryPoint

end
