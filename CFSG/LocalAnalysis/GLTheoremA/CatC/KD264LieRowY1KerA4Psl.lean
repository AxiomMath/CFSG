module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerA4Block
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerA4Transport

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open Matrix CFSG.LocalAnalysis.GLTheoremA.KD264LieA4

variable {K : Type} [Field K]

theorem center_scalar {c : Matrix.SpecialLinearGroup (Fin 4) K}
    (hc : c ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 4) K)) :
    ∃ r : K, r ^ 4 = 1 ∧ (c : Matrix (Fin 4) (Fin 4) K) = Matrix.scalar (Fin 4) r := by
  obtain ⟨r, hr4, hrc⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hc
  refine ⟨r, ?_, ?_⟩
  · simpa using hr4
  · rw [← hrc]

theorem center_eq_one_of_pow_three {c : Matrix.SpecialLinearGroup (Fin 4) K}
    (hc : c ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 4) K)) (h3 : c ^ 3 = 1) :
    c = 1 := by
  obtain ⟨r, hr4, hrc⟩ := center_scalar hc
  have hpow : (c : Matrix (Fin 4) (Fin 4) K) ^ 3 = 1 := by
    have := congrArg Subtype.val h3
    rwa [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one] at this
  rw [hrc, ← map_pow] at hpow
  have hr3 : r ^ 3 = 1 := by
    have := congrFun (congrFun hpow 0) 0
    simpa [Matrix.scalar_apply] using this
  have hr : r = 1 := by
    have h4 : r ^ 4 = r := by rw [show r ^ 4 = r * r ^ 3 by ring, hr3, mul_one]
    rw [← h4, hr4]
  apply Subtype.ext
  rw [hrc, hr, map_one, Matrix.SpecialLinearGroup.coe_one]

theorem center_eq_one_of_entry {c : Matrix.SpecialLinearGroup (Fin 4) K}
    (hc : c ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 4) K))
    (h2 : (c : Matrix (Fin 4) (Fin 4) K) 2 2 = 1) : c = 1 := by
  obtain ⟨r, _, hrc⟩ := center_scalar hc
  have hr : r = 1 := by
    have := h2
    rw [hrc] at this
    simpa [Matrix.scalar_apply] using this
  apply Subtype.ext
  rw [hrc, hr, map_one, Matrix.SpecialLinearGroup.coe_one]

theorem pow_three_of_conj_aux {G : Type} [Group G] {f x w : G} (hf : f ^ 3 = 1)
    (h1 : f⁻¹ * x * f = x * w) (hc : ∀ g : G, g * w = w * g) : w ^ 3 = 1 := by
  have h3 : f * f * f = 1 := by rw [← pow_three']; exact hf
  have hinv3 : f⁻¹ * f⁻¹ * f⁻¹ = 1 := by
    calc f⁻¹ * f⁻¹ * f⁻¹ = (f⁻¹ * f⁻¹ * f⁻¹) * (f * f * f) := by rw [h3, mul_one]
      _ = 1 := by group
  have hw1 : f⁻¹ * w * f = w := by
    calc f⁻¹ * w * f = f⁻¹ * (w * f) := by rw [mul_assoc]
      _ = f⁻¹ * (f * w) := by rw [← hc f]
      _ = w := inv_mul_cancel_left f w
  have E1 : f⁻¹ * (x * w) * f = x * w * w := by
    calc f⁻¹ * (x * w) * f = (f⁻¹ * x * f) * (f⁻¹ * w * f) := by group
      _ = x * w * w := by rw [h1, hw1]
  have E2 : f⁻¹ * (x * w * w) * f = x * w * w * w := by
    calc f⁻¹ * (x * w * w) * f = (f⁻¹ * (x * w) * f) * (f⁻¹ * w * f) := by group
      _ = x * w * w * w := by rw [E1, hw1]
  have E3 : f⁻¹ * (f⁻¹ * (f⁻¹ * x * f) * f) * f = x := by
    calc f⁻¹ * (f⁻¹ * (f⁻¹ * x * f) * f) * f = (f⁻¹ * f⁻¹ * f⁻¹) * x * (f * f * f) := by group
      _ = x := by rw [hinv3, h3, one_mul, mul_one]
  have E4 : f⁻¹ * (f⁻¹ * (f⁻¹ * x * f) * f) * f = x * w * w * w := by
    rw [h1, E1, E2]
  have hx : x * w * w * w = x := E4.symm.trans E3
  apply mul_left_cancel (a := x)
  rw [pow_three', mul_one, ← mul_assoc, ← mul_assoc]
  exact hx

theorem pow_three_of_comm_mem_center {G : Type} [Group G] {f x : G} (hf : f ^ 3 = 1)
    (hw : (f * x)⁻¹ * (x * f) ∈ Subgroup.center G) : ((f * x)⁻¹ * (x * f)) ^ 3 = 1 :=
  pow_three_of_conj_aux (x := x) (w := (f * x)⁻¹ * (x * f)) hf (by group)
    (fun g => Subgroup.mem_center_iff.mp hw g)

@[expose] def piSL (K : Type) [Field K] :
    Matrix.SpecialLinearGroup (Fin 4) K →* Matrix.ProjectiveSpecialLinearGroup (Fin 4) K :=
  QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 4) K))

theorem comm_of_pi_comm {f x : Matrix.SpecialLinearGroup (Fin 4) K} (hf : f ^ 3 = 1)
    (h : piSL K x * piSL K f = piSL K f * piSL K x) : x * f = f * x := by
  have hq : piSL K (f * x) = piSL K (x * f) := by
    rw [map_mul, map_mul]
    exact h.symm
  have hmem : (f * x)⁻¹ * (x * f) ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 4) K) :=
    QuotientGroup.eq.mp hq
  have hw1 := center_eq_one_of_pow_three hmem (pow_three_of_comm_mem_center hf hmem)
  exact (inv_mul_eq_one.mp hw1).symm

@[expose] def psi (K : Type) [Field K] :
    Matrix.SpecialLinearGroup (Fin 2) K →* Matrix.ProjectiveSpecialLinearGroup (Fin 4) K :=
  (piSL K).comp emb

theorem psi_injective : Function.Injective (psi (K := K)) := by
  rw [injective_iff_map_eq_one]
  intro B hB
  have hc : emb B ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 4) K) :=
    (QuotientGroup.eq_one_iff (emb B)).mp hB
  have h22 : ((emb B : Matrix.SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 2 2 = 1 := by
    rw [emb_apply_coe]
    simp [embM]
  exact emb_injective (by rw [map_one]; exact center_eq_one_of_entry hc h22)

theorem F0_pow_three {f : Matrix.SpecialLinearGroup (Fin 4) K} (hf : f ∈ F0 K) : f ^ 3 = 1 := by
  obtain ⟨d, _, rfl⟩ := Subgroup.mem_map.mp hf
  exact diagHom_pow_three K d

theorem emb_comm_F0 (B : Matrix.SpecialLinearGroup (Fin 2) K) {f : Matrix.SpecialLinearGroup (Fin 4) K}
    (hf : f ∈ F0 K) : emb B * f = f * emb B := by
  obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.mp hf
  have hd01 : d.1 0 = d.1 1 := hd
  apply Subtype.ext
  show embM (B : Matrix (Fin 2) (Fin 2) K) * diagM K d.1 = diagM K d.1 * embM (B : Matrix (Fin 2) (Fin 2) K)
  unfold diagM
  exact embM_mul_diagonal _ _ (by simp only [hd01])

theorem isQuasisimple_SL2 {ζ : K} (hζ : IsPrimitiveRoot ζ 3) :
    CFSG.Open.IsQuasisimple (Matrix.SpecialLinearGroup (Fin 2) K) := by
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (by norm_num)
  have hζ2 : ζ ^ 2 ≠ 1 := hζ.pow_ne_one_of_pos_of_lt (l := 2) two_ne_zero (by norm_num)
  exact ⟨Matrix.SL2.commutator_eq_top hζ0 hζ2,
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple' ⟨ζ, hζ0, hζ2⟩⟩

theorem three_dvd_card_PSL2 {ζ : K} (hζ : IsPrimitiveRoot ζ 3) :
    3 ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 2) K ⧸
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)) := by
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (by norm_num)
  have hζ3 : ζ ^ 3 = 1 := hζ.pow_eq_one
  have hζ1 : ζ ≠ 1 := by
    simpa using hζ.pow_ne_one_of_pos_of_lt (l := 1) one_ne_zero (by norm_num)
  have hζζ : ζ ≠ ζ ^ 2 := by
    intro h
    apply hζ1
    have : ζ * ζ = ζ * 1 := by rw [mul_one, ← pow_two, ← h]
    exact mul_left_cancel₀ hζ0 this
  have hdet : (Matrix.diagonal ![ζ, ζ ^ 2] : Matrix (Fin 2) (Fin 2) K).det = 1 := by
    rw [Matrix.det_diagonal, Fin.prod_univ_two]
    simpa [pow_succ'] using hζ3
  let A0 : Matrix.SpecialLinearGroup (Fin 2) K := ⟨Matrix.diagonal ![ζ, ζ ^ 2], hdet⟩
  let T : Matrix.SpecialLinearGroup (Fin 2) K :=
    ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
  have hA3 : A0 ^ 3 = 1 := by
    apply Subtype.ext
    show (Matrix.diagonal ![ζ, ζ ^ 2]) ^ 3 = 1
    rw [Matrix.diagonal_pow, ← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i
    · simpa using hζ3
    · show (ζ ^ 2) ^ 3 = 1
      rw [show (ζ ^ 2) ^ 3 = (ζ ^ 3) ^ 2 by ring, hζ3, one_pow]
  have hA0c : A0 ∉ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) := by
    intro hc
    have hcomm := Subgroup.mem_center_iff.mp hc T
    have h01 := congrFun (congrFun (congrArg Subtype.val hcomm) 0) 1
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul] at h01
    simp [A0, T, Matrix.mul_apply, Fin.sum_univ_two] at h01
    first
      | exact hζζ h01
      | exact hζζ h01.symm
  let q : Matrix.SpecialLinearGroup (Fin 2) K ⧸
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) :=
    QuotientGroup.mk' _ A0
  have hq3 : q ^ 3 = 1 := by
    show QuotientGroup.mk' _ A0 ^ 3 = 1
    rw [← map_pow, hA3, map_one]
  have hq1 : q ≠ 1 := fun h => hA0c ((QuotientGroup.eq_one_iff A0).mp h)
  have hord : orderOf q = 3 := orderOf_eq_prime hq3 hq1
  rw [← hord]
  exact orderOf_dvd_natCard q

theorem kerConcl_diagonal [Finite K] {ζ : K} (hζ : IsPrimitiveRoot ζ 3) :
    KerConcl ((DiagSL K).map (piSL K)) := by
  unfold KerConcl
  let g : (F0 K) →* Matrix.ProjectiveSpecialLinearGroup (Fin 4) K :=
    (piSL K).comp (F0 K).subtype
  have hginj : Function.Injective g := by
    rw [injective_iff_map_eq_one]
    intro f hf
    have hf2 : QuotientGroup.mk ((f : Matrix.SpecialLinearGroup (Fin 4) K)) =
        (1 : Matrix.ProjectiveSpecialLinearGroup (Fin 4) K) := hf
    have hc := (QuotientGroup.eq_one_iff _).mp hf2
    have h1 := center_eq_one_of_pow_three hc (F0_pow_three f.2)
    exact Subtype.ext h1
  have hHC : (psi K).range ≤ Subgroup.centralizer (g.range : Set
      (Matrix.ProjectiveSpecialLinearGroup (Fin 4) K)) := by
    intro h hh
    obtain ⟨B, rfl⟩ := MonoidHom.mem_range.mp hh
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    obtain ⟨f, rfl⟩ := MonoidHom.mem_range.mp hs
    show piSL K ((f : Matrix.SpecialLinearGroup (Fin 4) K)) * piSL K (emb B) =
      piSL K (emb B) * piSL K ((f : Matrix.SpecialLinearGroup (Fin 4) K))
    rw [← map_mul, ← map_mul, emb_comm_F0 B f.2]
  refine ⟨g.range, ?_, ?_, (psi K).range, hHC, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨f, rfl⟩ := MonoidHom.mem_range.mp hx
    exact Subgroup.mem_map.mpr ⟨f, F0_le_DiagSL K f.2, rfl⟩
  · rw [Nat.card_congr (MonoidHom.ofInjective hginj).symm.toEquiv]
    exact card_F0 K hζ
  · refine CFSG.Open.IsSubnormal.step hHC ?_ (CFSG.Open.IsSubnormal.refl _)
    constructor
    intro n hn c
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨B, hB⟩ := MonoidHom.mem_range.mp hn
    obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (c : Matrix.ProjectiveSpecialLinearGroup (Fin 4) K)
    have hy' : piSL K y = (c : Matrix.ProjectiveSpecialLinearGroup (Fin 4) K) := hy
    have hc := Subgroup.mem_centralizer_iff.mp c.2 (piSL K (tElt K hζ))
      (MonoidHom.mem_range.mpr ⟨⟨tElt K hζ, tElt_mem K hζ⟩, rfl⟩)
    rw [← hy'] at hc
    have hyt : y * tElt K hζ = tElt K hζ * y :=
      comm_of_pi_comm (F0_pow_three (tElt_mem K hζ)) hc.symm
    obtain ⟨B', hB'⟩ := emb_conj_mem hζ y hyt B
    refine MonoidHom.mem_range.mpr ⟨B', ?_⟩
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ← hB, ← hy']
    show piSL K (emb B') = piSL K y * piSL K (emb B) * (piSL K y)⁻¹
    rw [hB', map_mul, map_mul, map_inv]
  · exact isQuasisimple_equiv (MonoidHom.ofInjective (psi_injective (K := K)))
      (isQuasisimple_SL2 hζ)
  · rw [← card_quotient_center_equiv (MonoidHom.ofInjective (psi_injective (K := K)))]
    exact three_dvd_card_PSL2 hζ

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
