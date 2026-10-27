module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFCoverSylow

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G H : Type} [Group G] [Group H] {L : Subgroup G}

theorem ff_cover_autIn_equiv {φ : ↥L →* H} (hφ : OddCentralCover φ) {B : Subgroup G}
    (hBL : B ≤ L) (hB : IsPGroup 2 B) :
    Nonempty (↥(autIn L B) ≃* ↥(autIn (⊤ : Subgroup H) (ffImg φ B))) := by
  let e : ↥B ≃* ↥(ffImg φ B) := ffImgEquiv hφ hBL hB
  have key : ∀ (g : G) (hgN : g ∈ Subgroup.normalizer (B : Set G)) (hgL : g ∈ L),
      (MulAut.congr e).toMonoidHom (B.normalizerMonoidHom ⟨g, hgN⟩) =
        (ffImg φ B).normalizerMonoidHom
          ⟨φ ⟨g, hgL⟩, (ff_cover_mem_normalizer_iff hφ hBL hB ⟨g, hgL⟩).mp hgN⟩ := by
    intro g hgN hgL
    ext y
    obtain ⟨b, rfl⟩ := e.surjective y
    simp only [e, MulEquiv.coe_toMonoidHom, MulAut.congr_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply, coe_ffImgEquiv,
      Subgroup.normalizerMonoidHom_apply_apply_coe]
    rw [← map_mul, ← map_inv, ← map_mul]
    congr 1
  have hset : (autIn L B).map (MulAut.congr e).toMonoidHom =
      autIn (⊤ : Subgroup H) (ffImg φ B) := by
    ext σ'
    constructor
    · intro hσ'
      obtain ⟨σ, hσ, rfl⟩ := Subgroup.mem_map.mp hσ'
      rw [autIn] at hσ
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hσ
      have hxL : (x : G) ∈ L := Subgroup.mem_subgroupOf.mp hx
      rw [autIn]
      refine Subgroup.mem_map.mpr ⟨⟨φ ⟨(x : G), hxL⟩,
        (ff_cover_mem_normalizer_iff hφ hBL hB ⟨(x : G), hxL⟩).mp x.2⟩, by simp, ?_⟩
      exact (key (x : G) x.2 hxL).symm
    · intro hσ'
      rw [autIn] at hσ'
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hσ'
      obtain ⟨l, hl⟩ := hφ.surjective (y : H)
      have hyN : φ l ∈ Subgroup.normalizer (ffImg φ B : Set H) := hl ▸ y.2
      have hlN : (l : G) ∈ Subgroup.normalizer (B : Set G) :=
        (ff_cover_mem_normalizer_iff hφ hBL hB l).mpr hyN
      refine Subgroup.mem_map.mpr ⟨B.normalizerMonoidHom ⟨(l : G), hlN⟩, ?_, ?_⟩
      · rw [autIn]
        exact Subgroup.mem_map_of_mem _
          (Subgroup.mem_subgroupOf.mpr (show (l : G) ∈ L from l.2))
      · rw [key (l : G) hlN l.2]
        exact congrArg (fun z : ↥(Subgroup.normalizer (ffImg φ B : Set H)) =>
          (ffImg φ B).normalizerMonoidHom z) (Subtype.ext hl)
  exact ⟨(Subgroup.equivMapOfInjective (autIn L B) (MulAut.congr e).toMonoidHom
    (MulAut.congr e).injective).trans (MulEquiv.subgroupCongr hset)⟩

theorem ff_cover_trans {φ : ↥L →* H} (hφ : OddCentralCover φ) {B : Subgroup G}
    (hBL : B ≤ L) (hB : IsPGroup 2 B)
    (h : ∀ b ∈ ffImg φ B, ∀ b' ∈ ffImg φ B, b ≠ 1 → b' ≠ 1 →
      ∃ n ∈ Subgroup.normalizer (ffImg φ B : Set H), n * b * n⁻¹ = b') :
    ∀ b ∈ B, b ≠ 1 → ∀ b' ∈ B, b' ≠ 1 →
      ∃ n ∈ L ⊓ Subgroup.normalizer (B : Set G), n * b * n⁻¹ = b' := by
  intro b hb hb1 b' hb' hb'1
  have hbL : b ∈ L := hBL hb
  have hb'L : b' ∈ L := hBL hb'
  have himg1 : φ ⟨b, hbL⟩ ≠ 1 := by
    intro hcon
    have h1 : (⟨b, hbL⟩ : ↥L) = 1 :=
      ff_cover_eq_of_pGroup hφ hB (l := ⟨b, hbL⟩) (l' := 1) hb (by simpa using B.one_mem)
        (by simpa using hcon)
    exact hb1 (by simpa using congrArg (fun x : ↥L => (x : G)) h1)
  have himg1' : φ ⟨b', hb'L⟩ ≠ 1 := by
    intro hcon
    have h1 : (⟨b', hb'L⟩ : ↥L) = 1 :=
      ff_cover_eq_of_pGroup hφ hB (l := ⟨b', hb'L⟩) (l' := 1) hb' (by simpa using B.one_mem)
        (by simpa using hcon)
    exact hb'1 (by simpa using congrArg (fun x : ↥L => (x : G)) h1)
  obtain ⟨n, hnN, hn⟩ := h (φ ⟨b, hbL⟩) (mem_ffImg_iff.mpr ⟨⟨b, hbL⟩, hb, rfl⟩)
    (φ ⟨b', hb'L⟩) (mem_ffImg_iff.mpr ⟨⟨b', hb'L⟩, hb', rfl⟩) himg1 himg1'
  obtain ⟨l, hl⟩ := hφ.surjective n
  have hlN : (l : G) ∈ Subgroup.normalizer (B : Set G) :=
    (ff_cover_mem_normalizer_iff hφ hBL hB l).mpr (hl ▸ hnN)
  have hmemB : ((l * ⟨b, hbL⟩ * l⁻¹ : ↥L) : G) ∈ B :=
    (Subgroup.mem_normalizer_iff.mp hlN b).mp hb
  have hconj : l * ⟨b, hbL⟩ * l⁻¹ = ⟨b', hb'L⟩ := by
    apply ff_cover_eq_of_pGroup hφ hB hmemB hb'
    rw [map_mul, map_mul, map_inv, hl, hn]
  exact ⟨(l : G), Subgroup.mem_inf.mpr ⟨l.2, hlN⟩,
    by simpa using congrArg (fun x : ↥L => (x : G)) hconj⟩

theorem ff_cover_centralizer_eq {φ : ↥L →* H} (hφ : OddCentralCover φ) {B : Subgroup G}
    (hBL : B ≤ L) (hab : CFSG.Open.IsElemAbelian 2 B)
    (hC : ∀ n : H, (∀ b ∈ ffImg φ B, n * b = b * n) → n ∈ ffImg φ B) :
    L ⊓ Subgroup.centralizer (B : Set G) = B ⊔ centerIn L := by
  have hsq : ∀ g : ↥B, g * g = 1 := fun g => Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_one]
    simpa [pow_two] using hab.2 (g : G) g.2)
  have hB : IsPGroup 2 B := fun g => ⟨1, by rw [pow_one]; simpa [pow_two] using hsq g⟩
  have hsup : B ⊔ centerIn L ≤ L ⊓ Subgroup.centralizer (B : Set G) := by
    refine sup_le (le_inf hBL ?_) (le_inf (Subgroup.map_subtype_le _) ?_)
    · haveI : IsMulCommutative ↥B := hab.1
      exact Subgroup.le_centralizer B
    · intro z hz
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hz
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hc ⟨x, hBL hx⟩)
  refine le_antisymm ?_ hsup
  intro g hg
  obtain ⟨hgL, hgC⟩ := Subgroup.mem_inf.mp hg
  let l : ↥L := ⟨g, hgL⟩
  have hcomm : ∀ b ∈ B, (l : G) * b = b * (l : G) := by
    intro b hb
    exact (Subgroup.mem_centralizer_iff.mp hgC b hb).symm
  have hcomm' : ∀ b' ∈ ffImg φ B, φ l * b' = b' * φ l :=
    (ff_cover_commute_iff hφ hBL hB l).mp hcomm
  obtain ⟨l', hl'B, hl'eq⟩ := mem_ffImg_iff.mp (hC (φ l) hcomm')
  have hker : l * l'⁻¹ ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hl'eq, mul_inv_cancel]
  have hcenter : l * l'⁻¹ ∈ Subgroup.center ↥L := hφ.ker_le_center hker
  have hz : ((l * l'⁻¹ : ↥L) : G) ∈ centerIn L :=
    Subgroup.mem_map.mpr ⟨l * l'⁻¹, hcenter, rfl⟩
  have hdecomp : ((l * l'⁻¹ : ↥L) : G) * (l' : G) = g := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [show (l : G) = g from rfl]
    group
  rw [← hdecomp, sup_comm]
  exact Subgroup.mul_mem_sup hz hl'B

end CFSG.OddStandard.SmallF3.Omega
