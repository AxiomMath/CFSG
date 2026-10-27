module

public import CFSG.ClassicalInvolution.RouteD.GapsConj
public import CFSG.ClassicalInvolution.RouteD.GapsR2

public section

namespace CFSG.ClassicalInvolution.RouteD.Gaps

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

@[expose] noncomputable def layerAut {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) {t z : G}
    (ht : t * z * t⁻¹ = z) : ↥(locLayer Ω z) ≃* ↥(locLayer Ω z) :=
  (locLayerConj hΩ t z).trans (MulEquiv.subgroupCongr (congrArg (locLayer Ω) ht))

theorem coe_layerAut {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) {t z : G}
    (ht : t * z * t⁻¹ = z) (y : ↥(locLayer Ω z)) :
    ((layerAut hΩ ht y : ↥(locLayer Ω z)) : G) = t * y * t⁻¹ := rfl

@[expose] noncomputable def locAut {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) {t z : G}
    (ht : t * z * t⁻¹ = z) : locQuot Ω z ≃* locQuot Ω z :=
  QuotientGroup.congr _ _ (layerAut hΩ ht)
    (CFSG.ComponentClassification.OddCore.equiv_invariant (layerAut hΩ ht))

theorem locAut_mk {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) {t z : G} (ht : t * z * t⁻¹ = z)
    (y : ↥(locLayer Ω z)) :
    locAut hΩ ht (locMk Ω z y) = locMk Ω z (layerAut hΩ ht y) := rfl

theorem map_subgroupOf_layerAut {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) {t z : G}
    (ht : t * z * t⁻¹ = z) (L : Subgroup G) :
    (L.subgroupOf (locLayer Ω z)).map (layerAut hΩ ht).toMonoidHom =
      (conjSub t L).subgroupOf (locLayer Ω z) := by
  ext y'
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy2 : (y : G) ∈ L := hy
    show t * (y : G) * t⁻¹ ∈ conjSub t L
    rw [mem_conjSub_iff]
    simpa [mul_assoc] using hy2
  · intro hy'
    refine ⟨(layerAut hΩ ht).symm y', ?_, (layerAut hΩ ht).apply_symm_apply y'⟩
    have hy2 : t⁻¹ * (y' : G) * t ∈ L := mem_conjSub_iff.mp hy'
    have : ((layerAut hΩ ht).symm y' : G) = t⁻¹ * (y' : G) * t := by
      have h1 := coe_layerAut hΩ ht ((layerAut hΩ ht).symm y')
      rw [(layerAut hΩ ht).apply_symm_apply] at h1
      rw [h1]; group
    show ((layerAut hΩ ht).symm y' : G) ∈ L
    rw [this]
    exact hy2

theorem locAut_locImg {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) {t z : G}
    (ht : t * z * t⁻¹ = z) (L : Subgroup G) :
    (locImg Ω z L).map (locAut hΩ ht).toMonoidHom = locImg Ω z (conjSub t L) := by
  unfold locImg
  rw [← map_subgroupOf_layerAut hΩ ht L, Subgroup.map_map, Subgroup.map_map]
  rfl

theorem locAut_locAut {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) {t z : G}
    (ht : t * z * t⁻¹ = z) (h2 : t * t = 1) (a : locQuot Ω z) :
    locAut hΩ ht (locAut hΩ ht a) = a := by
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective a
  show locMk Ω z (layerAut hΩ ht (layerAut hΩ ht y)) = locMk Ω z y
  congr 1
  apply Subtype.ext
  show t * (t * (y : G) * t⁻¹) * t⁻¹ = y
  have h3 : t⁻¹ = t := inv_eq_of_mul_eq_one_right h2
  rw [h3, show t * (t * (y : G) * t) * t = (t * t) * y * (t * t) by group, h2]
  group

theorem fixed_of_perfect_of_central {Y : Type*} [Group Y] (σ : Y →* Y) {N : Subgroup Y}
    (hN : Group.IsPerfect ↥N) {Z : Subgroup Y} (hZ : Z ≤ Subgroup.center Y)
    (h : ∀ n ∈ N, n⁻¹ * σ n ∈ Z) : ∀ n ∈ N, σ n = n := by
  let φ : N →* Subgroup.center Y :=
    { toFun := fun n => ⟨(n : Y)⁻¹ * σ n, hZ (h n n.2)⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := fun a b => by
        apply Subtype.ext
        have ha := Subgroup.mem_center_iff.mp (hZ (h a a.2))
        simp only [Subgroup.coe_mul, mul_inv_rev, map_mul, Subgroup.coe_mul]
        calc (b : Y)⁻¹ * (a : Y)⁻¹ * (σ a * σ b)
            = (b : Y)⁻¹ * ((a : Y)⁻¹ * σ a) * σ b := by group
          _ = ((a : Y)⁻¹ * σ a) * (b : Y)⁻¹ * σ b := by rw [ha ((b : Y)⁻¹)]
          _ = ((a : Y)⁻¹ * σ a) * ((b : Y)⁻¹ * σ b) := by group }
  intro n hn
  have hker : commutator N ≤ φ.ker := Abelianization.commutator_subset_ker φ
  have hmem : (⟨n, hn⟩ : N) ∈ φ.ker := hker (by rw [hN.1]; exact Subgroup.mem_top _)
  have h1 : (n : Y)⁻¹ * σ n = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hmem)
  rw [inv_mul_eq_one] at h1
  exact h1.symm

theorem locAut_fixed_iff [Finite G] {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω) {t z : G}
    (hP1 : LocalOddCentral Ω {z}) (ht : t * z * t⁻¹ = z) {N : Subgroup G}
    (hN : N ∈ centralizingMembers Ω {z}) :
    N ≤ Subgroup.centralizer ({t} : Set G) ↔ ∀ a ∈ locImg Ω z N, locAut hΩ.conjInvariant ht a = a := by
  constructor
  · rintro h _ ⟨b, hb, rfl⟩
    show locMk Ω z (layerAut hΩ.conjInvariant ht b) = locMk Ω z b
    congr 1
    apply Subtype.ext
    show t * (b : G) * t⁻¹ = b
    have := Subgroup.mem_centralizer_singleton_iff.mp (h (Subgroup.mem_subgroupOf.mp hb))
    rw [mul_inv_eq_iff_eq_mul]
    exact this.symm
  · intro h n hn
    obtain ⟨z₀, hz₀⟩ := hΩ.classical N hN.1
    have hperf := (hz₀.subgroupOf p f (le_centralizingLayer hN)).perfect
    set Y := locLayer Ω z
    set O := classicalInvolutionOddCore ↥Y
    have hOc : ∀ b ∈ N.subgroupOf Y, b⁻¹ * layerAut hΩ.conjInvariant ht b ∈ O := by
      intro b hb
      have := h _ ⟨b, hb, rfl⟩
      have h2 : locMk Ω z (layerAut hΩ.conjInvariant ht b) = locMk Ω z b := this
      exact QuotientGroup.eq.mp h2.symm
    have key := fixed_of_perfect_of_central (layerAut hΩ.conjInvariant ht).toMonoidHom
      (N := N.subgroupOf Y) hperf hP1 hOc
    have := key ⟨n, le_centralizingLayer hN hn⟩ (Subgroup.mem_subgroupOf.mpr hn)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h4 := congrArg Subtype.val this
    have h5 : t * n * t⁻¹ = n := h4
    rw [mul_inv_eq_iff_eq_mul] at h5
    exact h5.symm

end CFSG.ClassicalInvolution.RouteD.Gaps
