module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4AltFrame

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace StabU

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  UnitaryOut UnitaryConj HBlocks ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank
  CFSG.LinearGroups
open scoped commutatorElement

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

include h in
theorem exists_lift_bd (hp2 : p ≠ 2) (P : GL (Fin 4) K)
    (hP : uStar h (P : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) = stdG)
    {l : K} (hl : l ^ 2 = -1) (hbl : h.bar l * l = -1)
    {J' : Subgroup (StatedProj (StatedSU 4 (p ^ f) K))}
    (hJX : J' ≤ Subgroup.centralizer {(QuotientGroup.mk (hypSU h P hP (X1 l) (unitary_X1 h hbl)
      (det_X1 hl)) : StatedProj (StatedSU 4 (p ^ f) K))})
    (hJp : ⁅J', J'⁆ = J') :
    ∀ z ∈ J', ∃ c : unitarySU p f K 4, (QuotientGroup.mk c : StatedProj (StatedSU 4 (p ^ f) K)) =
      z ∧ IsBD (cP P c) ∧ (ul (cP P c)).det = 1 ∧ (lr (cP P c)).det = 1 := by
  classical
  have : Finite K := h.finite
  have h2K : (2 : K) ≠ 0 := two_ne_zero_of_odd h hp2
  have hl0 : l ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num)] at hl
    exact one_ne_zero (by linear_combination hl : (1 : K) = 0)
  set X := hypSU h P hP (X1 l) (unitary_X1 h hbl) (det_X1 hl) with hX
  obtain ⟨C, hC⟩ : ∃ C : Subgroup (unitarySU p f K 4), C = Subgroup.centralizer {X} :=
    ⟨_, rfl⟩
  set θ : unitarySU p f K 4 →* StatedProj (StatedSU 4 (p ^ f) K) :=
    QuotientGroup.mk' (scal p f K) with hθdef
  have hscal : scal p f K ≤ Subgroup.center (unitarySU p f K 4) := fun z hz =>
    mem_center_of_mem_scal hz
  have hcen : ∀ Y : unitarySU p f K 4, θ Y ∈ Subgroup.centralizer {θ X} →
      Y * X * Y⁻¹ * X⁻¹ ∈ scal p f K := by
    intro Y hY
    rw [Subgroup.mem_centralizer_singleton_iff] at hY
    have h1 : θ (Y * X * Y⁻¹ * X⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hY]
      group
    rwa [hθdef, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  have hcomm_le : ⁅Subgroup.centralizer {θ X}, Subgroup.centralizer {θ X}⁆ ≤ C.map θ := by
    rw [Subgroup.commutator_le]
    intro u hu v hv
    obtain ⟨Y₁, rfl⟩ := QuotientGroup.mk'_surjective (scal p f K) u
    obtain ⟨Y₂, rfl⟩ := QuotientGroup.mk'_surjective (scal p f K) v
    refine ⟨⁅Y₁, Y₂⁆, ?_, by rw [map_commutatorElement]⟩
    rw [hC, SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    exact commutator_comm_of_comm_mod hscal (hcen Y₁ hu) (hcen Y₂ hv)
  have hJX' : J' ≤ Subgroup.centralizer {θ X} := hJX
  have hJC : J' ≤ (⁅C, C⁆).map θ := by
    have h1 : J' ≤ C.map θ := by
      rw [← hJp]
      exact (Subgroup.commutator_mono hJX' hJX').trans hcomm_le
    rw [Subgroup.map_commutator, ← hJp]
    exact Subgroup.commutator_mono h1 h1
  have hBD : ∀ g ∈ C, IsBD (cP P g) := by
    intro g hg
    rw [hC, Subgroup.mem_centralizer_singleton_iff] at hg
    have := congrArg (cP P) hg
    rw [cP_mul, cP_mul, hX, cP_hypSU] at this
    exact isBD_of_comm_X1 h2K hl0 this
  let β : C →* Matrix (Fin 2) (Fin 2) K :=
    { toFun := fun g => ul (cP P g.1)
      map_one' := by
        change ul (cP P (1 : unitarySU p f K 4)) = 1
        rw [cP_one, ul_one]
      map_mul' := fun g g' => by
        change ul (cP P (g.1 * g'.1)) = ul (cP P g.1) * ul (cP P g'.1)
        rw [cP_mul, ul_mul (hBD g.1 g.2) (hBD g'.1 g'.2)] }
  let δ : C →* Kˣ := (Matrix.detMonoidHom.comp β).toHomUnits
  have hSC : ⁅C, C⁆ ≤ C := Subgroup.commutator_le.2 fun a ha b hb =>
    mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  have hS : ⁅C, C⁆ ≤ δ.ker.map C.subtype := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    refine ⟨⁅(⟨a, ha⟩ : C), (⟨b, hb⟩ : C)⁆, ?_, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm _ _
  intro z hz
  obtain ⟨c, hc, rfl⟩ := hJC hz
  refine ⟨c, rfl, hBD c (hSC hc), ?_, ?_⟩
  · obtain ⟨y, hy, hyc⟩ := hS hc
    have hy' : y = ⟨c, hSC hc⟩ := Subtype.ext hyc
    have := congrArg Units.val (MonoidHom.mem_ker.mp hy)
    rw [hy'] at this
    simpa [δ, β] using this
  · obtain ⟨y, hy, hyc⟩ := hS hc
    have hy' : y = ⟨c, hSC hc⟩ := Subtype.ext hyc
    have h1 := congrArg Units.val (MonoidHom.mem_ker.mp hy)
    rw [hy'] at h1
    have hu : (ul (cP P c)).det = 1 := by simpa [δ, β] using h1
    have hd := det_cP h P c
    rw [det_of_isBD (hBD c (hSC hc)), hu, one_mul] at hd
    exact hd

include h in
theorem not_mem_normalizer_of (hp2 : p ≠ 2) (P : GL (Fin 4) K)
    (hP : uStar h (P : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) = stdG)
    {l : K} (hl : l ^ 2 = -1) (hbl : h.bar l * l = -1) {μ : K} (hμb : h.bar μ ≠ μ)
    {J' : Subgroup (StatedProj (StatedSU 4 (p ^ f) K))}
    (hJX : J' ≤ Subgroup.centralizer {(QuotientGroup.mk (hypSU h P hP (X1 l) (unitary_X1 h hbl)
      (det_X1 hl)) : StatedProj (StatedSU 4 (p ^ f) K))})
    (hU : HasUnipU h P hP μ J') {g : unitarySU p f K 4}
    (hg : ∀ x y : K, blk x 0 0 y * cP P g = cP P g * X1 l → False) :
    (QuotientGroup.mk g : StatedProj (StatedSU 4 (p ^ f) K)) ∉
      Subgroup.normalizer (J' : Set (StatedProj (StatedSU 4 (p ^ f) K))) := by
  intro hN
  set X := hypSU h P hP (X1 l) (unitary_X1 h hbl) (det_X1 hl) with hX
  set Y := g * X * g⁻¹ with hY
  have hcomm : ∀ u : unitarySU p f K 4,
      (QuotientGroup.mk u : StatedProj (StatedSU 4 (p ^ f) K)) ∈ J' → u ^ p = 1 →
        cP P u * cP P Y = cP P Y * cP P u := by
    intro u hu hup
    have h1 : (QuotientGroup.mk g : StatedProj (StatedSU 4 (p ^ f) K))⁻¹ *
        QuotientGroup.mk u * (QuotientGroup.mk g)⁻¹⁻¹ ∈ J' :=
      (Subgroup.mem_normalizer_iff.mp (inv_mem hN) _).mp hu
    have h2 := Subgroup.mem_centralizer_singleton_iff.mp (hJX h1)
    have h3 : (QuotientGroup.mk u : StatedProj (StatedSU 4 (p ^ f) K)) * QuotientGroup.mk Y =
        QuotientGroup.mk Y * QuotientGroup.mk u := by
      rw [hY, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      rw [inv_inv] at h2
      calc (QuotientGroup.mk u : StatedProj (StatedSU 4 (p ^ f) K)) *
            (QuotientGroup.mk g * QuotientGroup.mk X * (QuotientGroup.mk g)⁻¹) =
          QuotientGroup.mk g * (((QuotientGroup.mk g)⁻¹ * QuotientGroup.mk u *
            QuotientGroup.mk g) * QuotientGroup.mk X) * (QuotientGroup.mk g)⁻¹ := by group
        _ = QuotientGroup.mk g * (QuotientGroup.mk X * ((QuotientGroup.mk g)⁻¹ *
            QuotientGroup.mk u * QuotientGroup.mk g)) * (QuotientGroup.mk g)⁻¹ := by rw [h2]
        _ = _ := by group
    have h4 := comm_of_mk_comm' h hp2 hup h3
    rw [← cP_mul, ← cP_mul, h4]
  obtain ⟨hu1, hu2, hu3⟩ := hU
  have m1 := hcomm _ hu1 (uU_pow_char h P hP 1)
  have m2 := hcomm _ hu2 (uL_pow_char h P hP 1)
  have m3 := hcomm _ hu3 (uU_pow_char h P hP μ)
  rw [cP_uU] at m1 m3
  rw [cP_uL] at m2
  have hW := eq_blk_diag_of_comm h hμb m1.symm m2.symm m3.symm
  have hYg : cP P Y * cP P g = cP P g * cP P X := by
    rw [← cP_mul, ← cP_mul, hY, inv_mul_cancel_right]
  rw [hX, cP_hypSU, hW] at hYg
  exact hg _ _ hYg

theorem conj_bar_eq_of_transpose (A : GL (Fin 4) K) (u : unitarySU p f K 4)
    (hu : ((u : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)ᵀ * (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) *
      ((u : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K)) :
    (A : Matrix (Fin 4) (Fin 4) K) * ((u : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map h.bar *
      (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) = ((u : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
  have hU : uStar h ((u : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
      ((u : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = 1 := ((mem_unitarySU_iff h).1 u.2).2
  have h1 : ((u : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)ᵀ *
      ((u : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map h.bar = 1 := by
    have := congrArg Matrix.transpose hU
    rwa [uStar, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at this
  have h2 : ((u : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map h.bar *
      ((u : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)ᵀ = 1 := mul_eq_one_comm.1 h1
  have hAA : (A : Matrix (Fin 4) (Fin 4) K) * (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  calc (A : Matrix (Fin 4) (Fin 4) K) * ((u : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map h.bar *
        (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) =
      (A : Matrix (Fin 4) (Fin 4) K) * ((u : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map h.bar *
        (((u : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)ᵀ * (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) *
          ((u : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) := by rw [hu]
    _ = (A : Matrix (Fin 4) (Fin 4) K) *
        (((u : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map h.bar *
          ((u : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)ᵀ) * (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) *
          ((u : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by simp only [Matrix.mul_assoc]
    _ = ((u : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
        rw [h2, Matrix.mul_one, hAA, Matrix.one_mul]

include h in
theorem fix_of_cP {A : GL (Fin 4) K} (ψ : unitarySU p f K 4 →* unitarySU p f K 4)
    (hψv : ∀ g, ((ψ g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      (A : Matrix (Fin 4) (Fin 4) K) * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map h.bar *
        (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K))
    {α : MulAut (StatedProj (StatedSU 4 (p ^ f) K))}
    (hψ : ∀ g, (QuotientGroup.mk (ψ g) : StatedProj (StatedSU 4 (p ^ f) K)) =
      α (QuotientGroup.mk g))
    (P' : GL (Fin 4) K) (u : unitarySU p f K 4)
    (hD : (cP P' u)ᵀ * ((P' : Matrix (Fin 4) (Fin 4) K)ᵀ * (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) *
      (P' : Matrix (Fin 4) (Fin 4) K)) * cP P' u =
        (P' : Matrix (Fin 4) (Fin 4) K)ᵀ * (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) *
          (P' : Matrix (Fin 4) (Fin 4) K)) :
    α (QuotientGroup.mk u) = QuotientGroup.mk u := by
  have hPi : (↑P'⁻¹ : Matrix (Fin 4) (Fin 4) K) * (P' : Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hPiT : (P' : Matrix (Fin 4) (Fin 4) K)ᵀ * (↑P'⁻¹ : Matrix (Fin 4) (Fin 4) K)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, hPi, Matrix.transpose_one]
  have hut : ((u : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)ᵀ *
      (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) * ((u : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) := by
    rw [val_eq_cP P' u, Matrix.transpose_mul, Matrix.transpose_mul]
    calc (↑P'⁻¹ : Matrix (Fin 4) (Fin 4) K)ᵀ * ((cP P' u)ᵀ * (P' : Matrix (Fin 4) (Fin 4) K)ᵀ) *
          (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) *
          ((P' : Matrix (Fin 4) (Fin 4) K) * cP P' u * (↑P'⁻¹ : Matrix (Fin 4) (Fin 4) K)) =
        (↑P'⁻¹ : Matrix (Fin 4) (Fin 4) K)ᵀ * ((cP P' u)ᵀ *
          ((P' : Matrix (Fin 4) (Fin 4) K)ᵀ * (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) *
            (P' : Matrix (Fin 4) (Fin 4) K)) * cP P' u) *
          (↑P'⁻¹ : Matrix (Fin 4) (Fin 4) K) := by simp only [Matrix.mul_assoc]
      _ = (↑P'⁻¹ : Matrix (Fin 4) (Fin 4) K)ᵀ * (P' : Matrix (Fin 4) (Fin 4) K)ᵀ *
          (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) *
          ((P' : Matrix (Fin 4) (Fin 4) K) * (↑P'⁻¹ : Matrix (Fin 4) (Fin 4) K)) := by
          rw [hD]
          simp only [Matrix.mul_assoc]
      _ = (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) := by
          rw [← Matrix.transpose_mul, mul_eq_one_comm.1 hPi, Matrix.transpose_one,
            Matrix.one_mul, Matrix.mul_one]
  have hψu : ψ u = u := by
    apply ext_val
    rw [hψv]
    exact conj_bar_eq_of_transpose h A u hut
  rw [← hψ, hψu]

include h in
theorem exists_fixed_of_alt (hp2 : p ≠ 2) (hq : p ^ f % 4 = 1) (P : GL (Fin 4) K)
    (hP : uStar h (P : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) = stdG)
    {l : K} (hl : l ^ 2 = -1) (hbl : h.bar l * l = -1) {μ : Kˣ}
    (hμ : ∀ x : Kˣ, x ∈ Subgroup.zpowers μ) {J' : Subgroup (StatedProj (StatedSU 4 (p ^ f) K))}
    (hJX : J' ≤ Subgroup.centralizer {(QuotientGroup.mk (hypSU h P hP (X1 l) (unitary_X1 h hbl)
      (det_X1 hl)) : StatedProj (StatedSU 4 (p ^ f) K))})
    (hJp : ⁅J', J'⁆ = J') (hU : HasUnipU h P hP (μ : K) J') {A : GL (Fin 4) K}
    (hAu : uStar h (A : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K) = 1)
    (hAA : (A : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K).map h.bar = -1)
    (hAt : (A : Matrix (Fin 4) (Fin 4) K)ᵀ = -(A : Matrix (Fin 4) (Fin 4) K))
    (ψ : unitarySU p f K 4 →* unitarySU p f K 4)
    (hψv : ∀ g, ((ψ g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      (A : Matrix (Fin 4) (Fin 4) K) * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map h.bar *
        (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K))
    {α : MulAut (StatedProj (StatedSU 4 (p ^ f) K))}
    (hψ : ∀ g, (QuotientGroup.mk (ψ g) : StatedProj (StatedSU 4 (p ^ f) K)) =
      α (QuotientGroup.mk g)) :
    ∃ g₀ : unitarySU p f K 4, (∀ z ∈ J',
      α (QuotientGroup.mk g₀ * z * (QuotientGroup.mk g₀)⁻¹) =
        QuotientGroup.mk g₀ * z * (QuotientGroup.mk g₀)⁻¹) ∧
      ∃ m : unitarySU p f K 4, α (QuotientGroup.mk m) = QuotientGroup.mk m ∧
        (QuotientGroup.mk g₀ : StatedProj (StatedSU 4 (p ^ f) K))⁻¹ * QuotientGroup.mk m *
          QuotientGroup.mk g₀ ∉
            Subgroup.normalizer (J' : Set (StatedProj (StatedSU 4 (p ^ f) K))) := by
  classical
  have h2K : (2 : K) ≠ 0 := two_ne_zero_of_odd h hp2
  have hl0 : l ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num)] at hl
    exact one_ne_zero (by linear_combination hl : (1 : K) = 0)
  have hbl' : h.bar l = l := by
    have e : (h.bar l - l) * l = 0 := by linear_combination hbl - hl
    exact sub_eq_zero.1 ((mul_eq_zero.1 e).resolve_right hl0)
  obtain ⟨P', hP', y, hdet, hy0, hY⟩ := exists_alt_frame h hp2 hq hAu hAA hAt P hP
  have hg₀ : P' * P⁻¹ ∈ unitarySU p f K 4 := by
    rw [mem_unitarySU_iff h]
    constructor
    · rw [Units.val_mul, det_mul, hdet, ← det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        det_one]
    · change uStar h _ * _ = 1
      rw [Units.val_mul, uStar_mul]
      calc uStar h (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) * uStar h (P' : Matrix (Fin 4) (Fin 4) K) *
            ((P' : Matrix (Fin 4) (Fin 4) K) * (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K)) =
          uStar h (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) *
            (uStar h (P' : Matrix (Fin 4) (Fin 4) K) * (P' : Matrix (Fin 4) (Fin 4) K)) *
            (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hP']; exact uStar_inv_mul h P hP
  set g₀ : unitarySU p f K 4 := ⟨P' * P⁻¹, hg₀⟩ with hg₀def
  have hcPg : ∀ c : unitarySU p f K 4, cP P' (g₀ * c * g₀⁻¹) = cP P c := by
    intro c
    have e : P'⁻¹ * ((P' * P⁻¹) * (c : GL (Fin 4) K) * (P' * P⁻¹)⁻¹) * P' =
        P⁻¹ * (c : GL (Fin 4) K) * P := by group
    have e' := congrArg (fun X : GL (Fin 4) K => (X : Matrix (Fin 4) (Fin 4) K)) e
    simp only [Units.val_mul] at e'
    rw [cP, cP]
    exact e'
  refine ⟨g₀, fun z hz => ?_, ?_⟩
  · obtain ⟨c, hcz, hbd, hdu, hdl⟩ := exists_lift_bd h hp2 P hP hl hbl hJX hJp z hz
    have hfx := fix_of_cP h ψ hψv hψ P' (g₀ * c * g₀⁻¹)
      (by rw [hcPg, hY]; exact transpose_mul_bJ_mul' hbd hdu hdl _ _)
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hcz] at hfx
    exact hfx
  · set κ : K := (μ : K) - h.bar μ with hκdef
    have hμb := bar_ne_of_generator h hμ
    have hκ0 : κ ≠ 0 := sub_ne_zero.2 (Ne.symm hμb)
    have hκ : κ + h.bar κ = 0 := by
      rw [hκdef, map_sub, h.bar_bar]
      ring
    set m := hypSU h P' hP' (mk h κ l y) (unitary_mk h hκ hbl' hy0) (det_mk h κ l y) with hm
    refine ⟨m, fix_of_cP h ψ hψv hψ P' m (by rw [hm, cP_hypSU, hY]; exact transpose_mk h hy0), ?_⟩
    have hconj : (QuotientGroup.mk g₀ : StatedProj (StatedSU 4 (p ^ f) K))⁻¹ * QuotientGroup.mk m *
        QuotientGroup.mk g₀ = QuotientGroup.mk (g₀⁻¹ * m * g₀) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    have hcm : cP P (g₀⁻¹ * m * g₀) = mk h κ l y := by
      have := hcPg (g₀⁻¹ * m * g₀)
      rw [show g₀ * (g₀⁻¹ * m * g₀) * g₀⁻¹ = m by group, hm, cP_hypSU] at this
      exact this.symm
    rw [hconj]
    exact not_mem_normalizer_of h hp2 P hP hl hbl hμb hJX hU fun x w hxw =>
      hκ0 (eq_zero_of_blk_mul_mk h h2K hl0 (by rw [hcm] at hxw; exact hxw))

end StabU

end CFSG.ComponentClassification.CatFactsL4U4
