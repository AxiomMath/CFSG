module

public import CFSG.LocalAnalysis.EvenBN.LinearThree.ModelRadicals
import CFSG.LocalAnalysis.ComponentClassification.GS79bSec5.FieldStandardRowNormalizer
import CFSG.LocalAnalysis.ComponentClassification.GS79bSec5.FieldStandardCoverLevi
import CFSG.GroupTheory.Commutator.JoinNormalizer

public noncomputable section

open Matrix Subgroup
open scoped commutatorElement

namespace CFSG.ComponentClassification.GS79bSec5

universe u

theorem exists_row_torus_levi_factorization_of_mem_normalizer
    {G : Type u} [Group G]
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (A : Subgroup G)
    (e : (A ⧸ Subgroup.center A) ≃*
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F)
    (φ : Matrix.SpecialLinearGroup (Fin 3) F →* A)
    (hφsurj : Function.Surjective φ)
    (hφproj :
      (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center A))).comp φ =
        CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 3 F) :
    let ρ : Matrix.SpecialLinearGroup (Fin 3) F →* G := A.subtype.comp φ
    let E : Subgroup G :=
      (CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.unipOne F).map ρ
    let ι : (Fin 2 → F) → G := fun v =>
      ρ (CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.unipU F (-(v 1)) 0 (v 0))
    let tor : Fˣ →* G :=
      ρ.comp (CFSG.LocalAnalysis.EvenBN.LinearThree.torSLZero F)
    let lev : Matrix.SpecialLinearGroup (Fin 2) F →* G :=
      ρ.comp (CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.leviOne F)
    ∀ a : G, a ∈ A ⊓ Subgroup.normalizer (E : Set G) →
      ∃ (v : Fin 2 → F) (ell : Fˣ) (B : Matrix.SpecialLinearGroup (Fin 2) F),
        a = ι v * tor ell * lev B := by
  intro ρ E ι tor lev a ha
  have hρ : ρ.range = A := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hφsurj, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  obtain ⟨w, ell, B, h⟩ :=
    ((CFSG.LocalAnalysis.EvenBN.LinearThree.LeviData.ofCover ρ hρ
      (ker_subtype_comp_le_center e φ hφproj) 0).mem_normalizer_iff a ha.1).mp ha.2
  exact ⟨Multiplicative.toAdd w, ell, B, h⟩


private theorem levi_range_le_row_normalizer
    {G : Type u} [Group G] {F : Type} [Field F]
    (A : Subgroup G) (φ : Matrix.SpecialLinearGroup (Fin 3) F →* A) :
    let ρ : Matrix.SpecialLinearGroup (Fin 3) F →* G := A.subtype.comp φ
    let E : Subgroup G :=
      (CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.unipOne F).map ρ
    let L : Subgroup G :=
      (ρ.comp (CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.leviOne F)).range
    L ≤ A ⊓ Subgroup.normalizer (E : Set G) := by
  classical
  dsimp only
  set ρ : Matrix.SpecialLinearGroup (Fin 3) F →* G := A.subtype.comp φ with hρdef
  set E : Subgroup G :=
    (CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.unipOne F).map ρ with hEdef
  set L : Subgroup G :=
    (ρ.comp (CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.leviOne F)).range with hLdef
  intro x hx
  obtain ⟨B, rfl⟩ := hx
  refine ⟨(φ (CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.leviOne F B)).2, ?_⟩
  have hmap : ρ (CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.leviOne F B) ∈
      (Subgroup.normalizer
        (CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.unipOne F :
          Set (Matrix.SpecialLinearGroup (Fin 3) F))).map ρ :=
    Subgroup.mem_map_of_mem ρ (leviOne_mem_normalizer_unipOne B)
  exact Subgroup.le_normalizer_map
    (H := CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.unipOne F) ρ hmap

private theorem row_normalizer_le_row_sup_levi_sup_torus
    {G : Type u} [Group G]
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (A : Subgroup G)
    (e : (A ⧸ Subgroup.center A) ≃*
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F)
    (φ : Matrix.SpecialLinearGroup (Fin 3) F →* A)
    (hφsurj : Function.Surjective φ)
    (hφproj :
      (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center A))).comp φ =
        CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 3 F) :
    let ρ : Matrix.SpecialLinearGroup (Fin 3) F →* G := A.subtype.comp φ
    let E : Subgroup G :=
      (CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.unipOne F).map ρ
    let L : Subgroup G :=
      (ρ.comp (CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.leviOne F)).range
    let P : Subgroup G := A ⊓ Subgroup.normalizer (E : Set G)
    let T : Subgroup G :=
      (ρ.comp (CFSG.LocalAnalysis.EvenBN.LinearThree.torSLZero F)).range
    P ≤ (E ⊔ L) ⊔ T := by
  classical
  dsimp only
  set ρ : Matrix.SpecialLinearGroup (Fin 3) F →* G := A.subtype.comp φ with hρdef
  set E : Subgroup G :=
    (CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.unipOne F).map ρ with hEdef
  set L : Subgroup G :=
    (ρ.comp (CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.leviOne F)).range with hLdef
  set P : Subgroup G := A ⊓ Subgroup.normalizer (E : Set G) with hPdef
  set T : Subgroup G :=
    (ρ.comp (CFSG.LocalAnalysis.EvenBN.LinearThree.torSLZero F)).range with hTdef
  intro a ha
  obtain ⟨v, ell, B, rfl⟩ :=
    exists_row_torus_levi_factorization_of_mem_normalizer A e φ hφsurj hφproj a ha
  have hι : ρ (CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.unipU F
      (-(v 1)) 0 (v 0)) ∈ E :=
    Subgroup.mem_map.mpr ⟨_, ⟨-(v 1), v 0, rfl⟩, rfl⟩
  have htor : ρ (CFSG.LocalAnalysis.EvenBN.LinearThree.torSLZero F ell) ∈ T := ⟨ell, rfl⟩
  have hlev : ρ (CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.leviOne F B) ∈ L :=
    ⟨B, rfl⟩
  have hι1 : ρ (CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.unipU F
      (-(v 1)) 0 (v 0)) ∈ E ⊔ L := SetLike.le_def.mp le_sup_left hι
  have hlev1 : ρ (CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.leviOne F B) ∈
      E ⊔ L := SetLike.le_def.mp le_sup_right hlev
  have hι2 : ρ (CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.unipU F
      (-(v 1)) 0 (v 0)) ∈ (E ⊔ L) ⊔ T := SetLike.le_def.mp le_sup_left hι1
  have hlev2 : ρ (CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.leviOne F B) ∈
      (E ⊔ L) ⊔ T := SetLike.le_def.mp le_sup_left hlev1
  have htor2 : ρ (CFSG.LocalAnalysis.EvenBN.LinearThree.torSLZero F ell) ∈
      (E ⊔ L) ⊔ T := SetLike.le_def.mp le_sup_right htor
  exact ((E ⊔ L) ⊔ T).mul_mem (((E ⊔ L) ⊔ T).mul_mem hι2 htor2) hlev2

theorem commutator_row_normalizer_le_row_sup_levi
    {G : Type u} [Group G]
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (A : Subgroup G)
    (e : (A ⧸ Subgroup.center A) ≃*
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F)
    (φ : Matrix.SpecialLinearGroup (Fin 3) F →* A)
    (hφsurj : Function.Surjective φ)
    (hφproj :
      (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center A))).comp φ =
        CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 3 F) :
    let ρ : Matrix.SpecialLinearGroup (Fin 3) F →* G := A.subtype.comp φ
    let E : Subgroup G :=
      (CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.unipOne F).map ρ
    let L : Subgroup G :=
      (ρ.comp (CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.leviOne F)).range
    let P : Subgroup G := A ⊓ Subgroup.normalizer (E : Set G)
    ⁅P, P⁆ ≤ E ⊔ L := by
  classical
  dsimp only
  set ρ : Matrix.SpecialLinearGroup (Fin 3) F →* G := A.subtype.comp φ with hρdef
  set E : Subgroup G :=
    (CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.unipOne F).map ρ with hEdef
  set L : Subgroup G :=
    (ρ.comp (CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.leviOne F)).range with hLdef
  set P : Subgroup G := A ⊓ Subgroup.normalizer (E : Set G) with hPdef
  set T : Subgroup G :=
    (ρ.comp (CFSG.LocalAnalysis.EvenBN.LinearThree.torSLZero F)).range with hTdef
  have hL_leP : L ≤ P := levi_range_le_row_normalizer A φ
  have hL_NE : L ≤ Subgroup.normalizer (E : Set G) := hL_leP.trans inf_le_right
  have htorSL :
      CFSG.LocalAnalysis.EvenBN.LinearThree.torSLZero F =
        CFSG.LocalAnalysis.EvenBN.LinearThree.torSL F 0 := by
    apply MonoidHom.ext
    intro l
    simp [CFSG.LocalAnalysis.EvenBN.LinearThree.torSL]
  have tor_conj : ∀ (l : Fˣ), ∀ y ∈ E,
      ρ (CFSG.LocalAnalysis.EvenBN.LinearThree.torSLZero F l) * y *
          (ρ (CFSG.LocalAnalysis.EvenBN.LinearThree.torSLZero F l))⁻¹ ∈ E := by
    intro l y hy
    rw [hEdef] at hy ⊢
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hy
    obtain ⟨a, c, rfl⟩ := hu
    refine Subgroup.mem_map.mpr
      ⟨CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.unipU F
        ((l : F) ^ 3 * a) 0 ((l : F) ^ 3 * c), ⟨_, _, rfl⟩, ?_⟩
    have hconj :
        CFSG.LocalAnalysis.EvenBN.LinearThree.torSLZero F l *
            CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.unipU F a 0 c *
            (CFSG.LocalAnalysis.EvenBN.LinearThree.torSLZero F l)⁻¹ =
          CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.unipU F
            ((l : F) ^ 3 * a) 0 ((l : F) ^ 3 * c) := by
      rw [htorSL, CFSG.LocalAnalysis.EvenBN.LinearThree.torSL_zero_mul_unipU]
      group
    rw [← map_inv, ← map_mul, ← map_mul, ← hconj]
  have hT_NE : T ≤ Subgroup.normalizer (E : Set G) := by
    rintro x ⟨l, rfl⟩
    refine CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.mem_normalizer_of_conj_mem
      (tor_conj l) ?_
    intro y hy
    have h := tor_conj l⁻¹ y hy
    simpa [map_inv] using h
  have hT_comm : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x := by
    rintro _ ⟨l, rfl⟩ _ ⟨l', rfl⟩
    change (ρ.comp (CFSG.LocalAnalysis.EvenBN.LinearThree.torSLZero F)) l *
        (ρ.comp (CFSG.LocalAnalysis.EvenBN.LinearThree.torSLZero F)) l' =
      (ρ.comp (CFSG.LocalAnalysis.EvenBN.LinearThree.torSLZero F)) l' *
        (ρ.comp (CFSG.LocalAnalysis.EvenBN.LinearThree.torSLZero F)) l
    rw [← map_mul, ← map_mul, mul_comm]
  have hTT : ⁅T, T⁆ = ⊥ :=
    Subgroup.commutator_self_eq_bot_iff.mpr
      (IsMulCommutative.of_comm fun a b => Subtype.ext (hT_comm a.1 a.2 b.1 b.2))
  have hTL_cent : T ≤ Subgroup.centralizer (L : Set G) := by
    rintro _ ⟨l, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨B, rfl⟩ := hy
    show ρ (CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.leviOne F B) *
        ρ (CFSG.LocalAnalysis.EvenBN.LinearThree.torSLZero F l) =
      ρ (CFSG.LocalAnalysis.EvenBN.LinearThree.torSLZero F l) *
        ρ (CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.leviOne F B)
    rw [htorSL]
    simpa only [map_mul] using
      (congrArg ρ (CFSG.LocalAnalysis.EvenBN.LinearThree.torSL_zero_mul_leviOne l B)).symm
  have hT_NL : T ≤ Subgroup.normalizer (L : Set G) :=
    hTL_cent.trans (Subgroup.centralizer_le_normalizer (L : Set G))
  have hME : E ≤ E ⊔ L := le_sup_left
  have hML : L ≤ E ⊔ L := le_sup_right
  have hT_NM : T ≤ Subgroup.normalizer ((E ⊔ L : Subgroup G) : Set G) :=
    (le_inf hT_NE hT_NL).trans (Subgroup.inf_normalizer_le_normalizer_sup E L)
  have hM_NM : E ⊔ L ≤ Subgroup.normalizer ((E ⊔ L : Subgroup G) : Set G) :=
    Subgroup.le_normalizer
  have hTM : ⁅E ⊔ L, T⁆ ≤ E ⊔ L :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp hT_NM
  have hMT : ⁅T, E ⊔ L⁆ ≤ E ⊔ L :=
    Subgroup.le_normalizer_iff_commutator_le_right.mp hT_NM
  have hMM : ⁅E ⊔ L, E ⊔ L⁆ ≤ E ⊔ L := Subgroup.commutator_le_self (E ⊔ L)
  have hMTM : ⁅(E ⊔ L) ⊔ T, E ⊔ L⁆ ≤ E ⊔ L :=
    CFSG.GorensteinWalter.commutator_sup_le_of_commutator_le_and_normalize
      (E ⊔ L) T (E ⊔ L) (E ⊔ L) hMM hMT hM_NM hT_NM
  have hMTT : ⁅(E ⊔ L) ⊔ T, T⁆ ≤ E ⊔ L :=
    CFSG.GorensteinWalter.commutator_sup_le_of_commutator_le_and_normalize
      (E ⊔ L) T T (E ⊔ L) hTM (hTT.le.trans bot_le) hM_NM hT_NM
  have hMTMT : ⁅(E ⊔ L) ⊔ T, (E ⊔ L) ⊔ T⁆ ≤ E ⊔ L :=
    CFSG.GroupTheory.commutator_sup_right_le_of_le_normalizer
      hM_NM hT_NM hMTM hMTT
  have hP_le : P ≤ (E ⊔ L) ⊔ T := row_normalizer_le_row_sup_levi_sup_torus A e φ hφsurj hφproj
  calc ⁅P, P⁆ ≤ ⁅(E ⊔ L) ⊔ T, (E ⊔ L) ⊔ T⁆ := Subgroup.commutator_mono hP_le hP_le
    _ ≤ E ⊔ L := hMTMT


theorem map_levi_conj_le_row_sup_levi_of_mem_normalizers
    {G : Type u} [Group G]
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (A : Subgroup G)
    (e : (A ⧸ Subgroup.center A) ≃*
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F)
    (φ : Matrix.SpecialLinearGroup (Fin 3) F →* A)
    (hφsurj : Function.Surjective φ)
    (hφproj :
      (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center A))).comp φ =
        CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 3 F) :
    let ρ : Matrix.SpecialLinearGroup (Fin 3) F →* G := A.subtype.comp φ
    let E : Subgroup G :=
      (CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.unipOne F).map ρ
    let L : Subgroup G :=
      (ρ.comp (CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.leviOne F)).range
    ∀ c : G,
      c ∈ Subgroup.normalizer (A : Set G) →
      c ∈ Subgroup.normalizer (E : Set G) →
      L.map (MulAut.conj c).toMonoidHom ≤ E ⊔ L := by
  classical
  dsimp only
  set ρ : Matrix.SpecialLinearGroup (Fin 3) F →* G := A.subtype.comp φ with hρdef
  set E : Subgroup G :=
    (CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.unipOne F).map ρ with hEdef
  set L : Subgroup G :=
    (ρ.comp (CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.leviOne F)).range with hLdef
  set P : Subgroup G := A ⊓ Subgroup.normalizer (E : Set G) with hPdef
  set T : Subgroup G :=
    (ρ.comp (CFSG.LocalAnalysis.EvenBN.LinearThree.torSLZero F)).range with hTdef
  intro c hcA hcE
  have hL_leP : L ≤ P := levi_range_le_row_normalizer A φ
  have hLc_leP : L.map (MulAut.conj c).toMonoidHom ≤ P := by
    rintro x ⟨y, hy, rfl⟩
    change (MulAut.conj c) y ∈ A ⊓ Subgroup.normalizer (E : Set G)
    rw [MulAut.conj_apply]
    refine ⟨(Subgroup.mem_normalizer_iff.mp hcA y).mp (hL_leP hy).1, ?_⟩
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hcE (hL_leP hy).2) (Subgroup.inv_mem _ hcE)
  by_cases hq : 4 ≤ Nat.card F
  · have : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) F) :=
      CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card F hq
    have hLperf : Group.IsPerfect ↥L := by
      rw [hLdef]
      exact Group.IsPerfect.range
        (ρ.comp (CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.leviOne F))
    let f : ↥L →* G :=
      (MulAut.conj c).toMonoidHom.comp L.subtype
    have htop : Subgroup.map L.subtype (⊤ : Subgroup ↥L) = L := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have hrange : f.range = L.map (MulAut.conj c).toMonoidHom := by
      rw [MonoidHom.range_eq_map, ← Subgroup.map_map, htop]
    have hLcperf : Group.IsPerfect ↥(L.map (MulAut.conj c).toMonoidHom) := by
      have : Group.IsPerfect ↥f.range := Group.IsPerfect.range f
      exact hrange ▸ this
    have hcomm : ⁅L.map (MulAut.conj c).toMonoidHom,
        L.map (MulAut.conj c).toMonoidHom⁆ = L.map (MulAut.conj c).toMonoidHom :=
      Subgroup.commutator_eq_self
    calc L.map (MulAut.conj c).toMonoidHom
        = ⁅L.map (MulAut.conj c).toMonoidHom,
            L.map (MulAut.conj c).toMonoidHom⁆ := hcomm.symm
      _ ≤ ⁅P, P⁆ := Subgroup.commutator_mono hLc_leP hLc_leP
      _ ≤ E ⊔ L :=
        commutator_row_normalizer_le_row_sup_levi A e φ hφsurj hφproj
  ·
    have hq2 : Nat.card F = 2 := by
      let _ : Fintype F := Fintype.ofFinite F
      obtain ⟨n, -, hn⟩ := FiniteField.card F 2
      have hnpos : 0 < (n : ℕ) := by exact_mod_cast n.pos
      have hcardn : Nat.card F = 2 ^ (n : ℕ) := by
        rw [Nat.card_eq_fintype_card]
        exact hn
      have hlt : Nat.card F < 4 := by omega
      rcases Nat.lt_or_ge (n : ℕ) 2 with h | h
      · have hn1 : (n : ℕ) = 1 := by omega
        rw [hcardn, hn1]
        norm_num
      · have h4 : 4 ≤ 2 ^ (n : ℕ) := by
          calc 4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ (n : ℕ) := Nat.pow_le_pow_right (by norm_num) h
        omega
    have hcard_units : Nat.card Fˣ = 1 := by
      rw [Nat.card_units, hq2]
    have : Subsingleton Fˣ := (Nat.card_eq_one_iff_unique.mp hcard_units).1
    have hTbot : T = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨l, rfl⟩
      have hl : l = 1 := Subsingleton.elim l 1
      rw [hl, map_one]
      exact Subgroup.one_mem _
    have hTbot' : ((A.subtype.comp φ).comp
        (CFSG.LocalAnalysis.EvenBN.LinearThree.torSLZero F)).range = ⊥ := by
      simpa [hρdef, hTdef] using hTbot
    have hP_le : P ≤ E ⊔ L := by
      have h := row_normalizer_le_row_sup_levi_sup_torus A e φ hφsurj hφproj
      dsimp only at h
      rw [hTbot', sup_bot_eq] at h
      simpa [hPdef, hEdef, hLdef, hρdef] using h
    exact hLc_leP.trans hP_le

end CFSG.ComponentClassification.GS79bSec5
