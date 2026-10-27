module

public import CFSG.ClassicalInvolution.Q3.TL4E3S3OFr

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph

namespace E3S3O

section Gen

variable {H Y : Type} [Group H] [Finite H] [Group Y] [Finite Y]

omit [Finite H] [Finite Y] in
theorem isSylow2In_comap {ι : H →* Y} (hι : Function.Injective ι) {P M : Subgroup Y}
    (hM : M ≤ ι.range) (hP : IsSylow2In P M) : IsSylow2In (P.comap ι) (M.comap ι) := by
  refine ⟨Subgroup.comap_mono hP.1, hP.2.1.comap_of_injective ι hι, fun V hVM hV2 hPV => ?_⟩
  have hVmap : V.map ι = P := by
    refine hP.2.2 (V.map ι) ?_ (hV2.map ι) ?_
    · rw [Subgroup.map_le_iff_le_comap]
      exact hVM
    · have h1 := Subgroup.map_mono (f := ι) hPV
      rwa [Subgroup.map_comap_eq_self (hP.1.trans hM)] at h1
  rw [← hVmap, Subgroup.comap_map_eq_self_of_injective hι]

omit [Finite H] [Finite Y] in
theorem isUniqueInvolution_comap {ι : H →* Y} (hι : Function.Injective ι) {M : Subgroup Y}
    {z : Y} (hz : IsUniqueInvolution M z) {w : H} (hw : ι w = z) :
    IsUniqueInvolution (M.comap ι) w := by
  refine ⟨by rw [Subgroup.mem_comap, hw]; exact hz.mem, fun h => hz.ne_one (by rw [← hw, h,
    map_one]), hι (by rw [map_mul, hw, hz.sq, map_one]), fun y hy hy2 => ?_⟩
  rcases hz.unique (ι y) hy (by rw [← map_mul, hy2, map_one]) with h | h
  · exact Or.inl (hι (by rw [h, map_one]))
  · exact Or.inr (hι (by rw [h, hw]))

omit [Finite Y] in
theorem map_ne_of_isUniqueInvolution {N : Subgroup H} [N.Normal] (hN : Odd (Nat.card N))
    {A B : Subgroup H} {a b : H} (ha : IsUniqueInvolution A a) (hb : IsUniqueInvolution B b)
    (hab : a * b = b * a) (hne : a ≠ b) :
    A.map (QuotientGroup.mk' N) ≠ B.map (QuotientGroup.mk' N) := by
  intro heq
  have h1 := isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hN A) ha
  have h2 := isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hN B) hb
  rw [heq] at h1
  have hmem : a⁻¹ * b ∈ N := QuotientGroup.eq.mp (h1.eq h2)
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha.sq
  have hsq : a⁻¹ * b * (a⁻¹ * b) = 1 := by
    calc a⁻¹ * b * (a⁻¹ * b) = a * (b * a) * b := by rw [ha']; group
      _ = a * (a * b) * b := by rw [← hab]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [ha.sq, hb.sq, one_mul]
  exact hne (inv_mul_eq_one.mp (eq_one_of_isPGroup_of_mem_odd hN hmem
    (Balance.isPGroup_zpowers_of_mul_self_eq_one hsq)))

theorem mem_omegaNbr_quot {r : ℕ} {ι : H →* Y} (hι : Function.Injective ι) {N : Subgroup H}
    [N.Normal] (hN : Odd (Nat.card N)) {Ω : Set (Subgroup Y)} (hΩ : TypeRFam r Ω)
    {Φ : Set (Subgroup (H ⧸ N))} {M₁ M₂ : Subgroup Y} (hM₁ : M₁ ∈ Ω) (h₁ : M₁ ≤ ι.range)
    (h₂ : M₂ ≤ ι.range) (hΦ₂ : (M₂.comap ι).map (QuotientGroup.mk' N) ∈ Φ)
    (h : M₂ ∈ omegaNbr Ω M₁) :
    (M₂.comap ι).map (QuotientGroup.mk' N) ∈
      omegaNbr Φ ((M₁.comap ι).map (QuotientGroup.mk' N)) := by
  obtain ⟨hM₂, hne, P, hP, hPM, hPN⟩ := h
  obtain ⟨z₁, hz₁⟩ := Sec6Gen.exists_uniqueInvolution hΩ.hyp hM₁
  obtain ⟨z₂, hz₂⟩ := Sec6Gen.exists_uniqueInvolution hΩ.hyp hM₂
  have hPs : IsSylow2In P M₂ := Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ.hyp hM₂ hP hPM
  have h8 := Sec6Gen.eight_le_of_mem_RSet hΩ.hyp hP
  have hz₂P : z₂ ∈ P := T3.mem_of_isPGroup hz₂ hPM hPs.2.1 (by omega)
  have hc : z₂ * z₁ * z₂⁻¹ = z₁ := hz₁.conj_eq (mem_normalizer_iff_conjSub_eq.mp (hPN hz₂P))
  have hz12 : z₁ * z₂ = z₂ * z₁ := by
    calc z₁ * z₂ = (z₂ * z₁ * z₂⁻¹) * z₂ := by rw [hc]
      _ = z₂ * z₁ := by group
  have hzne : z₁ ≠ z₂ := fun e => hne (hΩ.noTwins M₁ hM₁ M₂ ⟨hM₂, z₁, hz₁, e ▸ hz₂⟩)
  obtain ⟨w₁, hw₁⟩ := h₁ hz₁.mem
  obtain ⟨w₂, hw₂⟩ := h₂ hz₂.mem
  have hw12 : w₁ * w₂ = w₂ * w₁ := hι (by rw [map_mul, map_mul, hw₁, hw₂, hz12])
  have hwne : w₁ ≠ w₂ := fun e => hzne (by rw [← hw₁, ← hw₂, e])
  refine ⟨hΦ₂, (map_ne_of_isUniqueInvolution hN (isUniqueInvolution_comap hι hz₁ hw₁)
    (isUniqueInvolution_comap hι hz₂ hw₂) hw12 hwne).symm, (P.comap ι).map (QuotientGroup.mk' N),
    mem_RSet_of_isSylow2In hΦ₂ (isSylow2In_map_mk hN (isSylow2In_comap hι h₂ hPs)),
    Subgroup.map_mono (Subgroup.comap_mono hPM), ?_⟩
  rintro _ ⟨p, hp, rfl⟩
  refine mk_mem_normalizer_map (N := N) ?_
  have hpN : ι p ∈ Subgroup.normalizer (M₁ : Set Y) := hPN hp
  rw [Subgroup.mem_normalizer_iff] at hpN ⊢
  intro y
  simp only [Subgroup.mem_comap, map_mul, map_inv]
  exact hpN (ι y)

end Gen

section Cit3


variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {J : Subgroup Y} {u : Y} {L Rd : Subgroup Y} {Sd : Sylow 2 Rd} {S' : Sylow 2 Y}
  {R' T W : Subgroup Y}

namespace Ctx

variable (h : Ctx n R S t J u L Rd Sd S' R' T W)
include h

theorem not_mem_omegaNbr_J {M₁ M₂ : Subgroup Y}
    (h₁ : M₁ ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) J)
    (h₂ : M₂ ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) J) :
    M₂ ∉ omegaNbr (CoreAssembly.conjClass (tightCore R)) M₁ := by
  intro h12
  set C := Subgroup.centralizer ({u} : Set Y) with hC
  set ι : ↥(secH R u) →* Y := C.subtype.comp (secH R u).subtype with hιdef
  have hι : Function.Injective ι := Subtype.val_injective.comp Subtype.val_injective
  have hJΩ := h.frame.maxAdj.1.2.1
  have hrange : ∀ M ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) J, M ≤ ι.range := by
    intro M hM y hy
    have hyC : y ∈ C := h.frame.nbr_le_centralizer hM hy
    have hyX : y ∈ nbrGen (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) J :=
      le_iSup₂ (f := fun N (_ : N ∈ {N | TC.nbrAdj (CoreAssembly.conjClass (tightCore R)) J N}) =>
        N) M ⟨hJΩ, hM⟩ hy
    exact ⟨⟨⟨y, hyC⟩, h.frame.nbrGen_le_secH h.orbit (Subgroup.mem_subgroupOf.mpr hyX)⟩, rfl⟩
  have hmem : ∀ M ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) J,
      (M.comap ι).map (QuotientGroup.mk' (classicalInvolutionOddCore ↥(secH R u))) ∈
        E3.secΩ R u := fun M hM => h.frame.map_mem_secΩ h.orbit hM
  have hedge := h.edge
  unfold TightEdgeless Disconnected.DEdgeless at hedge
  exact hedge _ (hmem M₁ h₁) _ (hmem M₂ h₂) (Or.inl (mem_omegaNbr_quot hι
    (CFSG.ComponentClassification.OddCore.odd_card ↥(secH R u))
    (TightLargeHypR.typeRFam h.frame.large) h₁.1 (hrange M₁ h₁) (hrange M₂ h₂) (hmem M₂ h₂) h12))

theorem not_mem_omegaNbr {M₁ M₂ : Subgroup Y}
    (h₁ : M₁ ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) L)
    (h₂ : M₂ ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) L) :
    M₂ ∉ omegaNbr (CoreAssembly.conjClass (tightCore R)) M₁ := by
  intro h12
  have hc := h.frame.large.datum.hypOmegaGen.conjInvariant
  obtain ⟨g, -, hgJ, -⟩ := h.exists_conj
  have e : ∀ M ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) L,
      conjSub g⁻¹ M ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) J := by
    intro M hM
    have h1 := omegaNbr_conj hc hM g⁻¹
    rwa [← hgJ, conjSub_inv_conjSub] at h1
  exact h.not_mem_omegaNbr_J (e M₁ h₁) (e M₂ h₂) (omegaNbr_conj hc h12 g⁻¹)

end Ctx

end Cit3

end E3S3O

end CFSG.ClassicalInvolution.Q3.TL4
