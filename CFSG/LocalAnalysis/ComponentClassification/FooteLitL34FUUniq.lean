module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76Thm12KStar
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Rank

public section

namespace CFSG.ComponentClassification.TBLit.L34FU

open CFSG Subgroup CFSG.ComponentClassification.FooteLit CFSG.ComponentClassification.Sol76
  CFSG.ComponentClassification.UnbalancedLayer

variable {X : Type} [Group X]

theorem orderOf_conj (b g : X) : orderOf (g⁻¹ * b * g) = orderOf b := by
  have h := MulEquiv.orderOf_eq (MulAut.conj g⁻¹) b
  rwa [MulAut.conj_apply, inv_inv] at h

theorem conjugate_centralizer (b g : X) :
    conjugate (centralizer ({b} : Set X)) g = centralizer ({g⁻¹ * b * g} : Set X) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff] at hy
    rw [mem_centralizer_singleton_iff]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    calc g⁻¹ * y * g * (g⁻¹ * b * g) = g⁻¹ * (y * b) * g := by group
      _ = g⁻¹ * (b * y) * g := by rw [hy]
      _ = g⁻¹ * b * g * (g⁻¹ * y * g) := by group
  · intro hx
    rw [mem_centralizer_singleton_iff] at hx
    refine ⟨g * x * g⁻¹, ?_, ?_⟩
    · rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
      calc g * x * g⁻¹ * b = g * (x * (g⁻¹ * b * g)) * g⁻¹ := by group
        _ = g * (g⁻¹ * b * g * x) * g⁻¹ := by rw [hx]
        _ = b * (g * x * g⁻¹) := by group
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      group

theorem mem_normalizer_of_conjugate_eq {K : Subgroup X} {h : X} (hK : conjugate K h = K) :
    h ∈ normalizer (K : Set X) := by
  have hinv : h⁻¹ ∈ normalizer (K : Set X) := by
    rw [mem_normalizer_iff]
    intro k
    constructor
    · intro hk
      rw [← hK]
      exact ⟨k, hk, by simp⟩
    · intro hk
      rw [← hK] at hk
      obtain ⟨k', hk', hkk⟩ := hk
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at hkk
      have : k' = k := by
        have := congrArg (fun z => h * z * h⁻¹) hkk
        simpa [mul_assoc] using this
      rwa [← this]
  simpa using inv_mem hinv

theorem isL34Type_conjugate {K : Subgroup X}
    (hKl : GrSLit.IsL34Type (↥K ⧸ Open.fusionZStar ↥K)) (g : X) :
    GrSLit.IsL34Type (↥(conjugate K g) ⧸ Open.fusionZStar ↥(conjugate K g)) := by
  obtain ⟨e⟩ := nonempty_quotient_fusionZStar_map (MulAut.conj g⁻¹) K
  exact LieType.CurtisTits.lieModel_of_mulEquiv e hKl

theorem mem_solomonKStar_of_l34 [Finite X] {K : Subgroup X}
    (hKmax : IsSolomonMaximal K) (hKl : GrSLit.IsL34Type (↥K ⧸ Open.fusionZStar ↥K)) :
    K ∈ solomonKStar X := by
  refine ⟨hKmax, hKmax.1, fun K' hK' => ?_⟩
  obtain ⟨e⟩ := nonempty_fusionZStar_equiv_of_reflTransGen hK'.2
  have h3 := GrSLit.GrS5.three_le_pRank_of_l34 (LieType.CurtisTits.lieModel_of_mulEquiv e hKl)
  omega

variable [Finite X]

theorem solomonKStarOf_eq (h13 : Sol76T13.SolomonThm13Simple) [IsSimpleGroup X]
    (hnab : ∃ a b : X, a * b ≠ b * a)
    (hKP : Assembly.KProper Blueprint.Catalog X) {t : X} (ht : orderOf t = 2) {J : Subgroup X}
    (hJ : IsTwoComponentIn J (centralizer ({t} : Set X))) (hJmax : IsSolomonMaximal J)
    (hJl : GrSLit.IsL34Type (↥J ⧸ Open.fusionZStar ↥J)) :
    solomonKStarOf (centralizer ({t} : Set X)) = J :=
  solomonKStarOf_centralizer_eq_of_simple h13 hnab hKP ht ⟨hJ, mem_solomonKStar_of_l34 hJmax hJl⟩
    (GrSLit.GrS5.three_le_pRank_of_l34 hJl)

theorem eq_of_isSolomonMaximal (h13 : Sol76T13.SolomonThm13Simple) [IsSimpleGroup X]
    (hnab : ∃ a b : X, a * b ≠ b * a)
    (hKP : Assembly.KProper Blueprint.Catalog X) {t : X} (ht : orderOf t = 2) {J M : Subgroup X}
    (hJ : IsTwoComponentIn J (centralizer ({t} : Set X))) (hJmax : IsSolomonMaximal J)
    (hJl : GrSLit.IsL34Type (↥J ⧸ Open.fusionZStar ↥J))
    (hM : IsTwoComponentIn M (centralizer ({t} : Set X))) (hMmax : IsSolomonMaximal M)
    (hMl : GrSLit.IsL34Type (↥M ⧸ Open.fusionZStar ↥M)) : M = J :=
  eq_of_mem_kStarComponents_of_simple h13 hnab hKP (mem_centralizer_singleton_iff.mpr rfl)
    (fun _ hn => mem_centralizer_singleton_iff.mp hn) ht ⟨hJ, mem_solomonKStar_of_l34 hJmax hJl⟩
    (GrSLit.GrS5.three_le_pRank_of_l34 hJl) ⟨hM, mem_solomonKStar_of_l34 hMmax hMl⟩

theorem centralizer_le_normalizer (h13 : Sol76T13.SolomonThm13Simple) [IsSimpleGroup X]
    (hnab : ∃ a b : X, a * b ≠ b * a)
    (hKP : Assembly.KProper Blueprint.Catalog X) {t : X}
    (ht : orderOf t = 2) {J : Subgroup X} (hJ : IsTwoComponentIn J (centralizer ({t} : Set X)))
    (hJmax : IsSolomonMaximal J) (hJl : GrSLit.IsL34Type (↥J ⧸ Open.fusionZStar ↥J)) :
    centralizer ({t} : Set X) ≤ normalizer (J : Set X) := by
  intro h hh
  have hC : conjugate (centralizer ({t} : Set X)) h = centralizer ({t} : Set X) := by
    rw [conjugate_centralizer]
    congr 2
    rw [mem_centralizer_singleton_iff] at hh
    rw [mul_assoc, ← hh, inv_mul_cancel_left]
  have hJh : IsTwoComponentIn (conjugate J h) (centralizer ({t} : Set X)) := by
    have := isTwoComponentIn_map (MulAut.conj h⁻¹) hJ
    rwa [show (centralizer ({t} : Set X)).map (MulAut.conj h⁻¹).toMonoidHom =
      conjugate (centralizer ({t} : Set X)) h from rfl, hC] at this
  exact mem_normalizer_of_conjugate_eq (eq_of_isSolomonMaximal h13 hnab hKP ht hJ hJmax hJl hJh
    (isSolomonMaximal_map (MulAut.conj h⁻¹) hJmax) (isL34Type_conjugate hJl h))

theorem twoLayerIn_le_conjugate (h13 : Sol76T13.SolomonThm13Simple) [IsSimpleGroup X]
    (hnab : ∃ a b : X, a * b ≠ b * a)
    (hKP : Assembly.KProper Blueprint.Catalog X) {b : X}
    (hb : orderOf b = 2) {K : Subgroup X} (hK : IsTwoComponentIn K (centralizer ({b} : Set X)))
    (hKmax : IsSolomonMaximal K) (hKl : GrSLit.IsL34Type (↥K ⧸ Open.fusionZStar ↥K)) (g : X)
    (hc : g⁻¹ * b * g ∈ coreActionKernel K) :
    twoLayerIn (K ⊓ centralizer ({g⁻¹ * b * g} : Set X)) ≤ conjugate K g := by
  set c := g⁻¹ * b * g with hcdef
  have hc2 : orderOf c = 2 := by rw [hcdef, orderOf_conj, hb]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set T := zpowers c with hT
  have hCT : centralizer ((T : Subgroup X) : Set X) = centralizer ({c} : Set X) := by
    rw [hT, zpowers_eq_closure, centralizer_closure]
  have hTne : T ≠ ⊥ := by
    intro h
    rw [hT, zpowers_eq_bot] at h
    rw [h, orderOf_one] at hc2
    norm_num at hc2
  have hT2 : IsPGroup 2 T := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hc2, pow_one])
  have hTK : T ≤ coreActionKernel K := by rw [hT, zpowers_le]; exact hc
  have h212 := lemma212Input X K T (mem_solomonKStar_of_l34 hKmax hKl) hTne hT2 hTK
  rw [hCT] at h212
  have hKg : IsTwoComponentIn (conjugate K g) (centralizer ({c} : Set X)) := by
    have := isTwoComponentIn_map (MulAut.conj g⁻¹) hK
    rwa [show (centralizer ({b} : Set X)).map (MulAut.conj g⁻¹).toMonoidHom =
      conjugate (centralizer ({b} : Set X)) g from rfl, conjugate_centralizer] at this
  have hKeq := solomonKStarOf_eq h13 hnab hKP hc2 hKg (isSolomonMaximal_map (MulAut.conj g⁻¹) hKmax)
    (isL34Type_conjugate hKl g)
  rwa [hKeq] at h212

end CFSG.ComponentClassification.TBLit.L34FU
