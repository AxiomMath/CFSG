module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherFactsL2Action
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2DeterminantSquare
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherFactsL2PGL

public section

namespace CFSG.ComponentClassification.Asc75T4KG

open Matrix CFSG.GorensteinWalter CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2
open scoped MatrixGroups

section Squares

variable {F : Type} [Field F] [Finite F]

theorem ringChar_ne_two (hF : IsOddPrimePower (Nat.card F)) : ringChar F ≠ 2 := by
  have : Fintype F := Fintype.ofFinite F
  intro h
  have h1 := (FiniteField.even_card_iff_char_two (F := F)).mp h
  have h2 := odd_card_of_isOddPrimePower hF
  rw [Nat.card_eq_fintype_card] at h2
  exact Nat.not_even_iff_odd.mpr h2 (Nat.even_iff.mpr h1)

theorem isSquare_map_mul_inv (hF : ringChar F ≠ 2) (σ : F ≃+* F) {x : F} (hx : x ≠ 0) :
    IsSquare (σ x * x⁻¹) := by
  have : Fintype F := Fintype.ofFinite F
  have hσx : σ x ≠ 0 := (map_ne_zero σ).mpr hx
  rw [FiniteField.isSquare_iff hF (mul_ne_zero hσx (inv_ne_zero hx)), mul_pow, inv_pow,
    ← map_pow]
  rcases FiniteField.pow_dichotomy hF hx with h | h <;> rw [h] <;> simp

theorem mul_pgl2FieldAut_mem_range_toPGL (hF : ringChar F ≠ 2) (σ : F ≃+* F) (g : PGL2 F) :
    g * pgl2FieldAut F σ g ∈
      (ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range := by
  obtain ⟨G, rfl⟩ := ProjGenLinGroup.mk_surjective g
  have hw : ProjGenLinGroup.mk G * pgl2FieldAut F σ (ProjGenLinGroup.mk G) =
      ProjGenLinGroup.mk (G * GeneralLinearGroup.map σ.toRingHom G) := by
    rw [show pgl2FieldAut F σ (ProjGenLinGroup.mk G) =
      ProjGenLinGroup.mk (GeneralLinearGroup.map σ.toRingHom G) from pgl2RingEquiv_mk σ G,
      map_mul]
  rw [hw]
  refine (pgl2_mk_mem_psl2_range_iff_det_isSquare _).2 ?_
  have hdet : ((GeneralLinearGroup.det (GeneralLinearGroup.map σ.toRingHom G) : Fˣ) : F) =
      σ ((GeneralLinearGroup.det G : Fˣ) : F) := by
    rw [GeneralLinearGroup.val_det_apply, GeneralLinearGroup.val_det_apply]
    change _ = σ.toRingHom _
    rw [RingHom.map_det]
    rfl
  have hG : ((GeneralLinearGroup.det G : Fˣ) : F) ≠ 0 := Units.ne_zero _
  have e : ((GeneralLinearGroup.det (G * GeneralLinearGroup.map σ.toRingHom G) : Fˣ) : F) =
      (((GeneralLinearGroup.det G : Fˣ) : F) * ((GeneralLinearGroup.det G : Fˣ) : F)) *
        (σ ((GeneralLinearGroup.det G : Fˣ) : F) * ((GeneralLinearGroup.det G : Fˣ) : F)⁻¹) := by
    rw [map_mul, Units.val_mul, hdet]
    field_simp
  change IsSquare ((GeneralLinearGroup.det _ : Fˣ) : F)
  rw [e]
  exact (IsSquare.mul_self _).mul (isSquare_map_mul_inv hF σ hG)

theorem sq_mem_pslRange_of_sq_mem_pglRange (hF : ringChar F ≠ 2) (x : PGammaL2 F)
    (hx : x ^ 2 ∈ pGammaL2PGLRange F) : x ^ 2 ∈ pGammaL2PSLRange F := by
  have hright : (x ^ 2).right = 1 := by
    rw [pGammaL2PGLRange, SemidirectProduct.range_inl_eq_ker_rightHom] at hx
    exact hx
  obtain ⟨y, hy⟩ := mul_pgl2FieldAut_mem_range_toPGL hF x.right x.left
  refine ⟨y, ?_⟩
  apply SemidirectProduct.ext
  · simp only [MonoidHom.comp_apply, SemidirectProduct.left_inl, hy, sq,
      SemidirectProduct.mul_left]
  · simp only [MonoidHom.comp_apply, SemidirectProduct.right_inl]
    exact hright.symm

end Squares

section Action

variable {R : Type} [Group R] (N : Subgroup R) [N.Normal] {K : Type} [Field K] [Finite K]
  (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K) (e : N ≃* PSL2 K)
  (hsurj : Function.Surjective (pGammaL2ToMulAutPSL2 K hK hcard))

theorem pGammaL2ToMulAutPSL2_surjective' :
    Function.Surjective (pGammaL2ToMulAutPSL2 K hK hcard) := by
  obtain ⟨p, n, hp, -, -, hn⟩ := hK
  have : Fact p.Prime := ⟨hp⟩
  exact pGammaL2ToMulAutPSL2_surjective K hn _ hcard

theorem psl2Action_eq_one_iff (r : R) :
    normalPSL2ToPGammaL2 N K hK hcard e hsurj r = 1 ↔ r ∈ Subgroup.centralizer (N : Set R) := by
  constructor
  · intro h
    rw [Subgroup.mem_centralizer_iff]
    intro n hn
    have h1 := (psl2Action_commute_iff N hK hcard e hsurj r ⟨n, hn⟩).mpr (by rw [h, one_mul,
      mul_one])
    exact h1.symm
  · intro h
    have h1 : MulAut.conjNormal (H := N) r = 1 := by
      ext n
      rw [MulAut.conjNormal_apply, MulAut.one_apply]
      have h2 := Subgroup.mem_centralizer_iff.mp h n n.2
      rw [← h2, mul_inv_cancel_right]
    have h2 : normalPSL2ConjAction N K e r = 1 := by
      simp only [normalPSL2ConjAction, MonoidHom.comp_apply, h1, map_one]
    simp only [normalPSL2ToPGammaL2, MonoidHom.comp_apply, h2, map_one]

theorem mem_sup_centralizer_iff (r : R) :
    r ∈ N ⊔ Subgroup.centralizer (N : Set R) ↔
      normalPSL2ToPGammaL2 N K hK hcard e hsurj r ∈ pGammaL2PSLRange K := by
  constructor
  · intro hr
    obtain ⟨n, hn, c, hc, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hr
    rw [map_mul, (psl2Action_eq_one_iff N hK hcard e hsurj c).mpr hc, mul_one]
    have h1 := psl2Action_apply N hK hcard e hsurj ⟨n, hn⟩
    rw [h1]
    exact ⟨e ⟨n, hn⟩, rfl⟩
  · intro hr
    obtain ⟨n, hn⟩ := psl2Action_mem_pslRange N hK hcard e hsurj r hr
    have hc : r * (n : R)⁻¹ ∈ Subgroup.centralizer (N : Set R) := by
      rw [Subgroup.mem_centralizer_iff]
      intro m hm
      exact (hn ⟨m, hm⟩).symm
    have e1 : r = (n : R) * ((n : R)⁻¹ * (r * (n : R)⁻¹) * n) := by group
    rw [e1]
    refine Subgroup.mul_mem_sup n.2 ?_
    have hCn : (Subgroup.centralizer (N : Set R)).Normal := Subgroup.normal_centralizer
    have h2 := hCn.conj_mem _ hc (n : R)⁻¹
    rwa [inv_inv] at h2

@[expose] noncomputable def pglPreimage : Subgroup R :=
  (pGammaL2PGLRange K).comap (normalPSL2ToPGammaL2 N K hK hcard e hsurj)

instance pglPreimage_normal : (pglPreimage N hK hcard e hsurj).Normal :=
  Subgroup.Normal.comap inferInstance _

theorem outerDiagonal_of_involution {a : R} (ha2 : a ^ 2 = 1)
    (haL : a ∉ N ⊔ Subgroup.centralizer (N : Set R))
    (hno : ∀ u w : N, u ^ 2 = 1 → w ^ 2 = 1 → u ≠ 1 → w ≠ 1 → u ≠ w → u * w = w * u →
      a * u = u * a → a * w = w * a → False) :
    normalPSL2ToPGammaL2 N K hK hcard e hsurj a ∈ pGammaL2PGLRange K ∧
      normalPSL2ToPGammaL2 N K hK hcard e hsurj a ∉ pGammaL2PSLRange K := by
  obtain ⟨g, hg⟩ := psl2Action_involution_linear N hK hcard e hsurj a ha2 hno
  exact ⟨⟨g, hg.symm⟩, fun h => haL ((mem_sup_centralizer_iff N hK hcard e hsurj a).mpr h)⟩

theorem sq_mul_inv_not_mem {a : R}
    (ha : normalPSL2ToPGammaL2 N K hK hcard e hsurj a ∈ pGammaL2PGLRange K)
    (ha' : normalPSL2ToPGammaL2 N K hK hcard e hsurj a ∉ pGammaL2PSLRange K) (b : R) :
    b ^ 2 * a⁻¹ ∉ N ⊔ Subgroup.centralizer (N : Set R) := by
  intro hb
  set ψ := normalPSL2ToPGammaL2 N K hK hcard e hsurj with hψ
  have hPSLle : pGammaL2PSLRange K ≤ pGammaL2PGLRange K := by
    rintro _ ⟨y, rfl⟩
    exact ⟨_, rfl⟩
  have h1 := (mem_sup_centralizer_iff N hK hcard e hsurj _).mp hb
  rw [map_mul, map_inv, map_pow] at h1
  have h2 : ψ b ^ 2 ∈ pGammaL2PGLRange K := by
    have h3 := mul_mem (hPSLle h1) ha
    rwa [inv_mul_cancel_right] at h3
  have h4 := sq_mem_pslRange_of_sq_mem_pglRange (ringChar_ne_two hK) (ψ b) h2
  apply ha'
  have h5 := mul_mem (inv_mem h1) h4
  rwa [_root_.mul_inv_rev, inv_inv, inv_mul_cancel_right] at h5

end Action

end CFSG.ComponentClassification.Asc75T4KG
