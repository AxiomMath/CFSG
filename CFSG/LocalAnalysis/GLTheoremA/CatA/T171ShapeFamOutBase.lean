module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeBoundBase
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Assembly CFSG.Yardstones.Md0ec50421ce4

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem inducesInnerMod_of_conj_eq {p : ℕ} {b : G} (l : ↥L)
    (hb : b ∈ Subgroup.normalizer (L : Set G))
    (h : ∀ y ∈ L, b⁻¹ * y * b = (l : G)⁻¹ * y * (l : G)) : InducesInnerMod p L b := by
  refine ⟨(l : G), l.2, fun y hy => ?_⟩
  rw [h y hy, inv_mul_cancel]
  exact Subgroup.one_mem (GLAPPrimeCoreOf p L)

theorem exists_conj_eq_of_marked_conj {R : Type} [Group R]
    {θ : ↥L ⧸ Subgroup.center ↥L ≃* R} {b : G} (hb : b ∈ Subgroup.normalizer (L : Set G))
    (hL : Group.IsPerfect ↥L) {r : R} (h : LargeEvenInduces θ (conjRel b) (MulAut.conj r)) :
    ∃ l : ↥L, ∀ y ∈ L, b⁻¹ * y * b = (l : G)⁻¹ * y * (l : G) := by
  classical
  obtain ⟨l, hlθ⟩ : ∃ l : ↥L, θ (QuotientGroup.mk l) = r := by
    obtain ⟨q, hq⟩ := θ.surjective r
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨l, hq⟩
  have key : ∀ y : ↥L, ∃ z ∈ Subgroup.center ↥L,
      b⁻¹ * (y : G) * b = ((l : G) * (y : G) * (l : G)⁻¹) * (z : G) := by
    intro y
    have hb' : b⁻¹ * (y : G) * b ∈ L := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hb) (y : G)).mp y.2
      simpa using this
    have hl' : (l : G) * (y : G) * (l : G)⁻¹ ∈ L :=
      L.mul_mem (L.mul_mem l.2 y.2) (L.inv_mem l.2)
    have h1 : MulAut.conj r (θ (QuotientGroup.mk y)) =
        θ (QuotientGroup.mk (⟨b⁻¹ * (y : G) * b, hb'⟩ : ↥L)) :=
      h y ⟨b⁻¹ * (y : G) * b, hb'⟩ rfl
    have h2 : MulAut.conj r (θ (QuotientGroup.mk y)) =
        θ (QuotientGroup.mk (⟨(l : G) * (y : G) * (l : G)⁻¹, hl'⟩ : ↥L)) := by
      rw [MulAut.conj_apply, ← hlθ, ← map_mul, ← map_inv, ← map_mul]
      rfl
    have heq : QuotientGroup.mk (⟨b⁻¹ * (y : G) * b, hb'⟩ : ↥L) =
        QuotientGroup.mk (⟨(l : G) * (y : G) * (l : G)⁻¹, hl'⟩ : ↥L) :=
      θ.injective (h1.symm.trans h2)
    have hmem : (⟨b⁻¹ * (y : G) * b, hb'⟩ : ↥L)⁻¹ *
        ⟨(l : G) * (y : G) * (l : G)⁻¹, hl'⟩ ∈ Subgroup.center ↥L :=
      QuotientGroup.eq.mp heq
    refine ⟨(⟨(l : G) * (y : G) * (l : G)⁻¹, hl'⟩ : ↥L)⁻¹ *
      ⟨b⁻¹ * (y : G) * b, hb'⟩, by simpa using Subgroup.inv_mem _ hmem, ?_⟩
    show b⁻¹ * (y : G) * b =
      ((l : G) * (y : G) * (l : G)⁻¹) *
        ((((l : G) * (y : G) * (l : G)⁻¹)⁻¹ * (b⁻¹ * (y : G) * b)) : G)
    group
  have ha : (b * (l : G)) ∈ Subgroup.normalizer (L : Set G) :=
    Subgroup.mul_mem _ hb (Subgroup.le_normalizer l.2)
  have hcent : b * (l : G) ∈ Subgroup.centralizer (L : Set G) := by
    refine centralizes_of_conjRel_center ha ?_ hL
    intro y
    obtain ⟨z, hz, hz'⟩ := key y
    refine ⟨z, hz, ?_⟩
    calc (b * (l : G))⁻¹ * (y : G) * (b * (l : G))
        = (l : G)⁻¹ * (b⁻¹ * (y : G) * b) * (l : G) := by group
      _ = (l : G)⁻¹ * (((l : G) * (y : G) * (l : G)⁻¹) * (z : G)) * (l : G) := by rw [hz']
      _ = (y : G) * (z : G) := by
          have hzc : (l : G) * (z : G) = (z : G) * (l : G) :=
            congrArg Subtype.val (Subgroup.mem_center_iff.mp hz l)
          have hzc' : (l : G)⁻¹ * (z : G) = (z : G) * (l : G)⁻¹ := by
            have h := congrArg (fun t : G => (l : G)⁻¹ * t * (l : G)⁻¹) hzc
            simpa [mul_assoc] using h.symm
          calc (l : G)⁻¹ * (((l : G) * (y : G) * (l : G)⁻¹) * (z : G)) * (l : G)
              = (y : G) * ((l : G)⁻¹ * (z : G)) * (l : G) := by group
            _ = (y : G) * ((z : G) * (l : G)⁻¹) * (l : G) := by rw [hzc']
            _ = (y : G) * (z : G) := by group
  refine ⟨l⁻¹, fun y hy => ?_⟩
  have hcomm : (b * (l : G))⁻¹ * y * (b * (l : G)) = y := by
    have h := Subgroup.mem_centralizer_iff.mp hcent y hy
    calc (b * (l : G))⁻¹ * y * (b * (l : G))
        = (b * (l : G))⁻¹ * (y * (b * (l : G))) := by group
      _ = (b * (l : G))⁻¹ * ((b * (l : G)) * y) := by rw [h]
      _ = y := by group
  calc b⁻¹ * y * b
      = (l : G) * ((b * (l : G))⁻¹ * y * (b * (l : G))) * (l : G)⁻¹ := by group
    _ = (l : G) * y * (l : G)⁻¹ := by rw [hcomm]
    _ = ((l⁻¹ : ↥L) : G)⁻¹ * y * ((l⁻¹ : ↥L) : G) := by simp

theorem inducesInnerMod_of_marked_conj {p : ℕ} {R : Type} [Group R]
    {θ : ↥L ⧸ Subgroup.center ↥L ≃* R} {b : G} (hb : b ∈ Subgroup.normalizer (L : Set G))
    (hL : Group.IsPerfect ↥L) {r : R} (h : LargeEvenInduces θ (conjRel b) (MulAut.conj r)) :
    InducesInnerMod p L b := by
  obtain ⟨l, hl⟩ := exists_conj_eq_of_marked_conj hb hL h
  exact inducesInnerMod_of_conj_eq l hb hl

theorem largeEvenInduces_pow_eq_one {p : ℕ} {R : Type} [Group R]
    {θ : ↥L ⧸ Subgroup.center ↥L ≃* R} {b : G} (hb : b ∈ Subgroup.normalizer (L : Set G))
    {φ : MulAut R} (hφ : LargeEvenInduces θ (conjRel b) φ) (hbpow : b ^ p = 1) :
    φ ^ p = 1 := by
  have h1 : LargeEvenInduces θ (conjRel (b ^ p)) (φ ^ p) := largeEvenInduces_pow hb hφ p
  rw [hbpow] at h1
  have h2 : LargeEvenInduces θ (conjRel (1 : G)) (1 : MulAut R) :=
    largeEvenInduces_one (rel := conjRel (1 : G)) fun l l' hl => by
      have hl' : (l' : G) = (l : G) := by simpa [conjRel] using hl
      exact Subtype.ext hl'.symm
  exact largeEvenInduces_unique h1 h2 (conjRel_total (Subgroup.one_mem _))

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
