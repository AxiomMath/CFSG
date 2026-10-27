module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6EInputs
import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneCentralizer

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open Matrix

theorem k32b_trace_eq_zero_of_cube {k : Type} [Field k] {U : Matrix (Fin 3) (Fin 3) k}
    (hU3 : U ^ 3 = 1) (hdet : U.det = 1)
    (hns : ∀ a : k, U ≠ a • (1 : Matrix (Fin 3) (Fin 3) k)) : U.trace = 0 := by
  have hcp := Matrix.aeval_self_charpoly U
  have hmon := Matrix.charpoly_monic U
  have hdeg : U.charpoly.natDegree = 3 := by
    simp [Matrix.charpoly_natDegree_eq_dim U]
  have hc3 : U.charpoly.coeff 3 = 1 := by
    have := hmon.coeff_natDegree
    rwa [hdeg] at this
  have hc2 : U.charpoly.coeff 2 = - U.trace := by
    have := Matrix.trace_eq_neg_charpoly_coeff U
    simp at this
    rw [this]; ring
  have hc0 : U.charpoly.coeff 0 = -1 := by
    have := Matrix.det_eq_sign_charpoly_coeff U
    rw [hdet] at this
    simp at this
    linear_combination this
  rw [Polynomial.aeval_eq_sum_range, hdeg] at hcp
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, hc3, hc2, hc0, pow_zero,
    pow_one, hU3] at hcp
  have h1 : U.charpoly.coeff 1 • U = U.trace • U ^ 2 := by
    rw [← sub_eq_zero, ← hcp]
    module
  have h2 : U.charpoly.coeff 1 • U ^ 2 = U.trace • (1 : Matrix (Fin 3) (Fin 3) k) := by
    have := congrArg (U * ·) h1
    simp only [mul_smul_comm, ← pow_succ', hU3] at this
    simpa [pow_two] using this
  have h3 : U.charpoly.coeff 1 • (1 : Matrix (Fin 3) (Fin 3) k) = U.trace • U := by
    have := congrArg (U * ·) h2
    simp only [mul_smul_comm, ← pow_succ', hU3, mul_one] at this
    simpa using this
  by_contra ht
  apply hns (U.charpoly.coeff 1 / U.trace)
  calc U = U.trace⁻¹ • (U.trace • U) := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
    _ = U.trace⁻¹ • (U.charpoly.coeff 1 • (1 : Matrix (Fin 3) (Fin 3) k)) := by rw [h3]
    _ = _ := by rw [smul_smul, div_eq_inv_mul]

theorem k32b_span_eq_top {k : Type} [Field k] (h3 : (3 : k) ≠ 0) {ι : Type} [Fintype ι]
    (hι : Fintype.card ι = 9) (e : ι → GL (Fin 3) k)
    (htr : ∀ i j, i ≠ j →
      Matrix.trace ((e i : Matrix (Fin 3) (Fin 3) k) * (((e j)⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k)) = 0) :
    Submodule.span k (Set.range fun i => (e i : Matrix (Fin 3) (Fin 3) k)) = ⊤ := by
  have : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
  refine LinearIndependent.span_eq_top_of_card_eq_finrank ?_ ?_
  · rw [Fintype.linearIndependent_iff]
    intro g hg j
    have h := congrArg (fun M => Matrix.trace (M * (((e j)⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) : Matrix (Fin 3) (Fin 3) k)) hg
    simp only [Finset.sum_mul, Matrix.trace_sum, smul_mul_assoc, Matrix.trace_smul, zero_mul,
      Matrix.trace_zero] at h
    rw [Finset.sum_eq_single j] at h
    · have h1 : ((e j : Matrix (Fin 3) (Fin 3) k) * (((e j)⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k)) = 1 := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      rw [h1] at h
      simp at h
      exact h.resolve_right h3
    · intro i _ hij
      rw [htr i j hij, smul_zero]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  · rw [hι, Module.finrank_matrix]
    simp

theorem k32b_mem_scalar_range {k : Type} [Field k] {ι : Type}
    (e : ι → GL (Fin 3) k)
    (hspan : Submodule.span k (Set.range fun i => (e i : Matrix (Fin 3) (Fin 3) k)) = ⊤)
    (d : GL (Fin 3) k) (hd : ∀ i, d * e i = e i * d) :
    d ∈ (Matrix.GeneralLinearGroup.scalar (Fin 3) : kˣ →* GL (Fin 3) k).range := by
  rw [← Matrix.GeneralLinearGroup.center_eq_range_scalar, Subgroup.mem_center_iff]
  intro g
  have hle : Submodule.span k (Set.range fun i => (e i : Matrix (Fin 3) (Fin 3) k)) ≤
      (Subalgebra.centralizer k ({(d : Matrix (Fin 3) (Fin 3) k)} :
        Set (Matrix (Fin 3) (Fin 3) k))).toSubmodule := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, Subalgebra.mem_toSubmodule, Subalgebra.mem_centralizer_iff]
    intro m hm
    rw [Set.mem_singleton_iff] at hm
    rw [hm, ← Units.val_mul, ← Units.val_mul, hd i]
  have hg : (g : Matrix (Fin 3) (Fin 3) k) ∈
      (Subalgebra.centralizer k ({(d : Matrix (Fin 3) (Fin 3) k)} :
        Set (Matrix (Fin 3) (Fin 3) k))).toSubmodule := hle (by rw [hspan]; trivial)
  rw [Subalgebra.mem_toSubmodule, Subalgebra.mem_centralizer_iff] at hg
  exact Units.ext (hg _ (Set.mem_singleton _)).symm

theorem k32b_exists_generators {G : Type*} [Group G] (F : Subgroup G) (hF3 : ∀ x ∈ F, x ^ 3 = 1)
    (hcard : Nat.card F = 9) : ∃ x ∈ F, ∃ y ∈ F, F ≤ Subgroup.closure {x, y} := by
  have hfin : Finite F := Nat.finite_of_card_ne_zero (by omega)
  obtain ⟨x, hxF, hx1⟩ : ∃ x ∈ F, x ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : F = ⊥ := (Subgroup.eq_bot_iff_forall F).2 hcon
    rw [this, Subgroup.card_bot] at hcard
    omega
  have hord : orderOf x = 3 := orderOf_eq_prime (hF3 x hxF) hx1
  have hzc : Nat.card (Subgroup.zpowers x) = 3 := by rw [Nat.card_zpowers, hord]
  obtain ⟨y, hyF, hyx⟩ : ∃ y ∈ F, y ∉ Subgroup.zpowers x := by
    by_contra hcon
    push Not at hcon
    have : Finite (Subgroup.zpowers x) :=
      Nat.finite_of_card_ne_zero (by omega)
    have := Subgroup.card_le_of_le (H := F) (K := Subgroup.zpowers x) hcon
    omega
  refine ⟨x, hxF, y, hyF, ?_⟩
  have hHF : Subgroup.closure {x, y} ≤ F := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact hxF
    · exact hyF
  have : Finite (Subgroup.closure ({x, y} : Set G)) :=
    Finite.of_injective _ (Subgroup.inclusion_injective hHF)
  have hxH : Subgroup.zpowers x ≤ Subgroup.closure {x, y} := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.subset_closure (by simp)
  have hyH : y ∈ Subgroup.closure ({x, y} : Set G) := Subgroup.subset_closure (by simp)
  have hd1 : 3 ∣ Nat.card (Subgroup.closure ({x, y} : Set G)) := by
    rw [← hzc]; exact Subgroup.card_dvd_of_le hxH
  have hd2 : Nat.card (Subgroup.closure ({x, y} : Set G)) ∣ 9 := by
    rw [← hcard]; exact Subgroup.card_dvd_of_le hHF
  have hne : Nat.card (Subgroup.closure ({x, y} : Set G)) ≠ 3 := by
    intro h3
    have := Subgroup.eq_of_le_of_card_ge hxH (by rw [h3, hzc])
    exact hyx (this ▸ hyH)
  have h9 : Nat.card (Subgroup.closure ({x, y} : Set G)) = 9 := by
    obtain ⟨m, hm⟩ := hd1
    rw [hm] at hd2 hne ⊢
    have : m ∣ 3 := Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 3) (by simpa using hd2)
    have hm3 : m ≤ 3 := Nat.le_of_dvd (by norm_num) this
    interval_cases m <;> simp_all
  exact (Subgroup.eq_of_le_of_card_ge hHF (by rw [h9, hcard])).ge

section Proj

variable {k : Type} [Field k] (L : Subgroup (GL (Fin 3) k))

theorem k32b_mk_eq_mk_iff (a b : L) :
    (QuotientGroup.mk a : StatedProj L) = QuotientGroup.mk b ↔
      ∃ s : kˣ, Matrix.GeneralLinearGroup.scalar (Fin 3) s = (a : GL (Fin 3) k)⁻¹ * (b : GL (Fin 3) k) := by
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
  exact Iff.rfl

theorem k32b_mk_eq_one_iff (a : L) :
    (QuotientGroup.mk a : StatedProj L) = 1 ↔
      ∃ s : kˣ, Matrix.GeneralLinearGroup.scalar (Fin 3) s = (a : GL (Fin 3) k) := by
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  exact Iff.rfl


theorem k32b_trace_eq_zero_of_fused
    (hdet : ∀ A ∈ L, (A : Matrix (Fin 3) (Fin 3) k).det = 1)
    (F : Subgroup (StatedProj L)) (hF3 : ∀ x ∈ F, x ^ 3 = 1)
    (hfuse : ∀ x ∈ F, x ≠ 1 → ∀ y ∈ F, y ≠ 1 → ∃ g : StatedProj L, g * x * g⁻¹ = y)
    (u : L) (hu : (QuotientGroup.mk u : StatedProj L) ∈ F)
    (hu1 : (QuotientGroup.mk u : StatedProj L) ≠ 1) :
    ((u : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k).trace = 0 := by
  have hcube : ∃ s : kˣ, Matrix.GeneralLinearGroup.scalar (Fin 3) s = (u : GL (Fin 3) k) ^ 3 := by
    have h := hF3 _ hu
    rw [← QuotientGroup.mk_pow, k32b_mk_eq_one_iff] at h
    simpa using h
  obtain ⟨lam, hlam⟩ := hcube
  have hx2 : (QuotientGroup.mk u : StatedProj L) ^ 2 ∈ F := pow_mem hu 2
  have hx21 : (QuotientGroup.mk u : StatedProj L) ^ 2 ≠ 1 := by
    intro h
    apply hu1
    have h3 := hF3 _ hu
    calc (QuotientGroup.mk u : StatedProj L)
        = (QuotientGroup.mk u : StatedProj L) ^ 3 * ((QuotientGroup.mk u : StatedProj L) ^ 2)⁻¹ := by
          group
      _ = 1 := by rw [h3, h]; simp
  obtain ⟨g, hg⟩ := hfuse _ hu hu1 _ hx2 hx21
  obtain ⟨G, rfl⟩ := QuotientGroup.mk_surjective g
  have hmk : (QuotientGroup.mk (G * u * G⁻¹) : StatedProj L) = QuotientGroup.mk (u ^ 2) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_pow]
    exact hg
  obtain ⟨s, hs⟩ := (k32b_mk_eq_mk_iff L _ _).1 hmk
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow] at hs
  have hDU : GeneralLinearGroup.det (u : GL (Fin 3) k) = 1 := Units.ext (by
    rw [GeneralLinearGroup.val_det_apply]; exact hdet _ u.2)
  have hs3 : s ^ 3 = 1 := by
    have := congrArg GeneralLinearGroup.det hs
    simpa [map_mul, map_inv, map_pow, hDU, GeneralLinearGroup.det_scalar] using this
  set Gm : GL (Fin 3) k := (G : GL (Fin 3) k) with hGm
  set Um : GL (Fin 3) k := (u : GL (Fin 3) k) with hUm
  have hc : Commute (Matrix.GeneralLinearGroup.scalar (Fin 3) s) Um :=
    Matrix.GeneralLinearGroup.scalar_commute s Um
  have hconj : Gm * Um * Gm⁻¹ = Um ^ 2 * (Matrix.GeneralLinearGroup.scalar (Fin 3) s)⁻¹ := by
    rw [hs]; group
  have h6 : Gm * Um ^ 3 * Gm⁻¹ = Um ^ 6 := by
    rw [← conj_pow, hconj, Commute.mul_pow ((hc.inv_left.pow_right 2).symm), inv_pow,
      ← map_pow, hs3, map_one, inv_one, mul_one, ← pow_mul]
  have hU3 : Um ^ 3 = 1 := by
    have h1 : Gm * Um ^ 3 * Gm⁻¹ = Um ^ 3 := by
      rw [← hlam, ← Matrix.GeneralLinearGroup.scalar_commute, mul_assoc, mul_inv_cancel, mul_one]
    have h2 : Um ^ 3 = Um ^ 6 := h1.symm.trans h6
    have h7 : Um ^ 3 * 1 = Um ^ 3 * Um ^ 3 := by rw [mul_one, ← pow_add]; exact h2
    exact (mul_left_cancel h7).symm
  have hdetU : (Um : Matrix (Fin 3) (Fin 3) k).det = 1 := hdet _ u.2
  refine k32b_trace_eq_zero_of_cube ?_ hdetU ?_
  · have := congrArg (fun g : GL (Fin 3) k => (g : Matrix (Fin 3) (Fin 3) k)) hU3
    simpa [Units.val_pow_eq_pow_val] using this
  · intro a ha
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [zero_smul] at ha
      rw [ha] at hdetU
      simp at hdetU
    apply hu1
    rw [k32b_mk_eq_one_iff]
    refine ⟨Units.mk0 a ha0, Units.ext ?_⟩
    rw [Matrix.GeneralLinearGroup.coe_scalar, ha, Matrix.scalar_apply, smul_one_eq_diagonal]
    rfl


theorem k32b_card_centralizer_le [Finite k] (h3 : (3 : k) ≠ 0)
    (hdet : ∀ A ∈ L, (A : Matrix (Fin 3) (Fin 3) k).det = 1)
    (F : Subgroup (StatedProj L)) (hF3 : ∀ x ∈ F, x ^ 3 = 1) (hcard : Nat.card F = 9)
    (hfuse : ∀ x ∈ F, x ≠ 1 → ∀ y ∈ F, y ≠ 1 → ∃ g : StatedProj L, g * x * g⁻¹ = y) :
    Nat.card (Subgroup.centralizer (F : Set (StatedProj L))) ≤ 9 := by
  obtain ⟨x, hx, y, hy, hgen⟩ := k32b_exists_generators F hF3 hcard
  choose lift hlift using
    (QuotientGroup.mk_surjective : Function.Surjective (QuotientGroup.mk : L → StatedProj L))
  have hfinF : Finite F := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype F := Fintype.ofFinite F
  have hι : Fintype.card F = 9 := by rw [← Nat.card_eq_fintype_card]; exact hcard
  let E : F → GL (Fin 3) k := fun f => (lift f.1 : GL (Fin 3) k)
  have htr : ∀ f f' : F, f ≠ f' →
      Matrix.trace ((E f : Matrix (Fin 3) (Fin 3) k) *
        (((E f')⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k)) = 0 := by
    intro f f' hff
    have := k32b_trace_eq_zero_of_fused L hdet F hF3 hfuse (lift f.1 * (lift f'.1)⁻¹) (by
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hlift, hlift]
        exact F.mul_mem f.2 (F.inv_mem f'.2)) (by
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hlift, hlift]
        intro h
        exact hff (Subtype.ext (mul_inv_eq_one.1 h)))
    simpa [E] using this
  have hspan := k32b_span_eq_top h3 hι E htr
  have hchi : ∀ c : Subgroup.centralizer (F : Set (StatedProj L)), ∀ f : F, ∃ s : kˣ,
      (lift c.1 : GL (Fin 3) k) * E f * (lift c.1 : GL (Fin 3) k)⁻¹ =
        Matrix.GeneralLinearGroup.scalar (Fin 3) s * E f ∧ s ^ 3 = 1 := by
    intro c f
    have hcf : f.1 * c.1 = c.1 * f.1 := Subgroup.mem_centralizer_iff.1 c.2 f.1 f.2
    have hmk : (QuotientGroup.mk (lift f.1) : StatedProj L) =
        QuotientGroup.mk (lift c.1 * lift f.1 * (lift c.1)⁻¹) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hlift, hlift, ← hcf]
      group
    obtain ⟨t, ht⟩ := (k32b_mk_eq_mk_iff L _ _).1 hmk
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at ht
    refine ⟨t, ?_, ?_⟩
    · rw [Matrix.GeneralLinearGroup.scalar_commute, ht]
      simp [E]
    · have := congrArg Matrix.GeneralLinearGroup.det ht
      simp only [map_mul, map_inv, Matrix.GeneralLinearGroup.det_scalar] at this
      rw [Fintype.card_fin] at this
      rw [this]
      simp [mul_comm, mul_assoc]
  choose s hs using hchi
  let Ψ : Subgroup.centralizer (F : Set (StatedProj L)) →
      rootsOfUnity 3 k × rootsOfUnity 3 k := fun c =>
    (⟨s c ⟨x, hx⟩, (mem_rootsOfUnity 3 _).2 (hs c _).2⟩,
      ⟨s c ⟨y, hy⟩, (mem_rootsOfUnity 3 _).2 (hs c _).2⟩)
  have hinj : Function.Injective Ψ := by
    intro c c' hcc
    have hxs : s c ⟨x, hx⟩ = s c' ⟨x, hx⟩ := congrArg (fun p => ((p.1 : kˣ))) hcc
    have hys : s c ⟨y, hy⟩ = s c' ⟨y, hy⟩ := congrArg (fun p => ((p.2 : kˣ))) hcc
    have hcomm1 : ∀ f : F, s c f = s c' f →
        ((lift c.1)⁻¹ * lift c'.1 : L).1 * E f = E f * ((lift c.1)⁻¹ * lift c'.1 : L).1 := by
      intro f hsf
      have hA := (hs c f).1
      have hB := (hs c' f).1
      rw [← hsf] at hB
      have hdE : ((lift c.1 : GL (Fin 3) k))⁻¹ * (lift c'.1 : GL (Fin 3) k) * E f *
          (((lift c.1 : GL (Fin 3) k))⁻¹ * (lift c'.1 : GL (Fin 3) k))⁻¹ = E f := by
        calc _ = (lift c.1 : GL (Fin 3) k)⁻¹ * ((lift c'.1 : GL (Fin 3) k) * E f *
              (lift c'.1 : GL (Fin 3) k)⁻¹) * (lift c.1 : GL (Fin 3) k) := by group
          _ = (lift c.1 : GL (Fin 3) k)⁻¹ * ((lift c.1 : GL (Fin 3) k) * E f *
              (lift c.1 : GL (Fin 3) k)⁻¹) * (lift c.1 : GL (Fin 3) k) := by rw [hB, hA]
          _ = E f := by group
      simpa using mul_inv_eq_iff_eq_mul.1 hdE
    set d' : L := (lift c.1)⁻¹ * lift c'.1 with hd'
    let Sd : Subgroup (StatedProj L) :=
      (Subgroup.centralizer ({d'} : Set L)).map (QuotientGroup.mk' _)
    have hmem : ∀ g : StatedProj L, (d' : GL (Fin 3) k) * (lift g : GL (Fin 3) k) =
        (lift g : GL (Fin 3) k) * d' → g ∈ Sd := by
      intro g hg
      refine ⟨lift g, Subgroup.mem_centralizer_iff.2 ?_, hlift g⟩
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact Subtype.ext hg
    have hFS : F ≤ Sd := by
      refine hgen.trans ((Subgroup.closure_le Sd).2 ?_)
      rintro z (hz | hz)
      · rw [hz]; exact hmem _ (hcomm1 ⟨x, hx⟩ hxs)
      · rw [Set.mem_singleton_iff.1 hz]; exact hmem _ (hcomm1 ⟨y, hy⟩ hys)
    have hall : ∀ f : F, (d' : GL (Fin 3) k) * E f = E f * d' := by
      intro f
      obtain ⟨w, hw, hwf⟩ := hFS f.2
      have hw := Subgroup.mem_centralizer_iff.1 hw
      have hwc : (d' : GL (Fin 3) k) * w = w * d' := by
        have := hw d' (Set.mem_singleton _)
        exact congrArg Subtype.val this
      have hmk : (QuotientGroup.mk w : StatedProj L) = QuotientGroup.mk (lift f.1) := by
        rw [hlift]; exact hwf
      obtain ⟨t, ht⟩ := (k32b_mk_eq_mk_iff L _ _).1 hmk
      have hE : E f = (w : GL (Fin 3) k) * Matrix.GeneralLinearGroup.scalar (Fin 3) t := by
        rw [ht]; simp [E]
      have h1 := Matrix.GeneralLinearGroup.scalar_commute t (d' : GL (Fin 3) k)
      rw [hE]
      calc (d' : GL (Fin 3) k) * (w * Matrix.GeneralLinearGroup.scalar (Fin 3) t)
          = ((d' : GL (Fin 3) k) * w) * Matrix.GeneralLinearGroup.scalar (Fin 3) t := by group
        _ = w * (Matrix.GeneralLinearGroup.scalar (Fin 3) t * (d' : GL (Fin 3) k)) := by
          rw [hwc, mul_assoc, h1]
        _ = _ := by group
    obtain ⟨t, ht⟩ := k32b_mem_scalar_range E hspan (d' : GL (Fin 3) k) hall
    have h1 : (QuotientGroup.mk d' : StatedProj L) = 1 := (k32b_mk_eq_one_iff L d').2 ⟨t, ht⟩
    rw [hd', QuotientGroup.mk_mul, QuotientGroup.mk_inv, hlift, hlift, inv_mul_eq_one] at h1
    exact Subtype.ext h1
  calc Nat.card (Subgroup.centralizer (F : Set (StatedProj L)))
      ≤ Nat.card (rootsOfUnity 3 k × rootsOfUnity 3 k) := Nat.card_le_card_of_injective Ψ hinj
    _ = Nat.card (rootsOfUnity 3 k) * Nat.card (rootsOfUnity 3 k) := Nat.card_prod _ _
    _ ≤ 3 * 3 := Nat.mul_le_mul (card_rootsOfUnity k 3) (card_rootsOfUnity k 3)


theorem k32b_mem_of_commute_fused [Finite k] (h3 : (3 : k) ≠ 0)
    (hdet : ∀ A ∈ L, (A : Matrix (Fin 3) (Fin 3) k).det = 1)
    (F : Subgroup (StatedProj L)) (hFc : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a)
    (hF3 : ∀ x ∈ F, x ^ 3 = 1) (hcard : Nat.card F = 9)
    (hfuse : ∀ x ∈ F, x ≠ 1 → ∀ y ∈ F, y ≠ 1 → ∃ g : StatedProj L, g * x * g⁻¹ = y)
    (c : StatedProj L) (hc : ∀ f ∈ F, c * f = f * c) : c ∈ F := by
  have hle : F ≤ Subgroup.centralizer (F : Set (StatedProj L)) := fun a ha =>
    Subgroup.mem_centralizer_iff.2 fun b hb => hFc b hb a ha
  have hEq : F = Subgroup.centralizer (F : Set (StatedProj L)) :=
    Subgroup.eq_of_le_of_card_ge hle (by
      rw [hcard]; exact k32b_card_centralizer_le L h3 hdet F hF3 hcard hfuse)
  rw [hEq]
  exact Subgroup.mem_centralizer_iff.2 fun f hf => (hc f (hEq ▸ hf)).symm

end Proj

theorem k32b_sylow_of_proj {K : Type} [Group K] [Finite K] {Y : Type} [Group Y] (π : K →* Y)
    (hker : ∀ x : K, π x = 1 → x ∈ GLAPPrimeCore 3 K)
    (hcore : ∀ F : Subgroup Y, (∀ a ∈ F, ∀ b ∈ F, a * b = b * a) → (∀ x ∈ F, x ^ 3 = 1) →
      Nat.card F = 9 → (∀ x ∈ F, x ≠ 1 → ∀ y ∈ F, y ≠ 1 → ∃ g : Y, g * x * g⁻¹ = y) →
      ∀ c : Y, (∀ f ∈ F, c * f = f * c) → c ∈ F) :
    ∀ F : Subgroup K, IsElemAbelian 3 F → Nat.card F = 9 →
      (∀ x ∈ F, x ≠ 1 → ∀ y ∈ F, y ≠ 1 → ∃ g : K, g * x * g⁻¹ = y) →
      ∀ P : Subgroup K, IsPGroup 3 P → P ≤ Subgroup.centralizer (F : Set K) → F ≤ P → P ≤ F := by
  intro F hF hcard hfuse P hP hPc hFP
  have hinj : Set.InjOn π P := by
    intro a ha b hb hab
    have hz : a⁻¹ * b ∈ GLAPPrimeCore 3 K :=
      hker _ (by rw [map_mul, map_inv, hab, inv_mul_cancel])
    have hzP : a⁻¹ * b ∈ P := P.mul_mem (P.inv_mem ha) hb
    have h1 : orderOf (a⁻¹ * b) ∣ Nat.card (GLAPPrimeCore 3 K) :=
      Subgroup.orderOf_dvd_natCard _ hz
    have h2 : Nat.Coprime 3 (orderOf (a⁻¹ * b)) :=
      (CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane.coprime_card_GLAPPrimeCore
        Nat.prime_three K).coprime_dvd_right h1
    obtain ⟨m, hm⟩ := hP ⟨a⁻¹ * b, hzP⟩
    have hm' : (a⁻¹ * b) ^ (3 ^ m) = 1 := by
      have := congrArg Subtype.val hm
      simpa using this
    have h3 : orderOf (a⁻¹ * b) ∣ 3 ^ m := orderOf_dvd_of_pow_eq_one hm'
    have h4 : orderOf (a⁻¹ * b) = 1 := Nat.Coprime.eq_one_of_dvd (h2.symm.pow_right m) h3
    exact inv_mul_eq_one.1 (orderOf_eq_one_iff.1 h4)
  have hFinj : Set.InjOn π F := hinj.mono (fun x hx => hFP hx)
  have hFc : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hF.1.is_comm.comm (⟨a, ha⟩ : F) ⟨b, hb⟩)
  have hcard' : Nat.card (F.map π) = 9 := by
    rw [← hcard]
    calc Nat.card (F.map π) = Nat.card ((F.map π : Subgroup Y) : Set Y) := rfl
      _ = Nat.card (π '' (F : Set K)) := by rw [Subgroup.coe_map]
      _ = Nat.card (F : Set K) := Nat.card_image_of_injOn hFinj
      _ = Nat.card F := rfl
  intro p hp
  have hmem : π p ∈ F.map π := by
    refine hcore (F.map π) ?_ ?_ hcard' ?_ (π p) ?_
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [← map_mul, ← map_mul, hFc a ha b hb]
    · rintro _ ⟨a, ha, rfl⟩
      rw [← map_pow, hF.2 a ha, map_one]
    · rintro _ ⟨x, hx, rfl⟩ hx1 _ ⟨y, hy, rfl⟩ hy1
      have hx1' : x ≠ 1 := fun h => hx1 (by rw [h, map_one])
      have hy1' : y ≠ 1 := fun h => hy1 (by rw [h, map_one])
      obtain ⟨g, hg⟩ := hfuse x hx hx1' y hy hy1'
      exact ⟨π g, by rw [← map_mul, ← map_inv, ← map_mul, hg]⟩
    · rintro _ ⟨f, hf, rfl⟩
      have := Subgroup.mem_centralizer_iff.1 (hPc hp) f hf
      rw [← map_mul, ← map_mul, this]
  obtain ⟨f, hf, hfp⟩ := hmem
  rw [← hinj (hFP hf) hp hfp]
  exact hf

theorem k32b_three_ne_zero {k : Type} [Field k] [Finite k] (h : Nat.card k % 3 = 1) :
    (3 : k) ≠ 0 := by
  intro h0
  obtain ⟨p, hp⟩ := CharP.exists k
  have : Fintype k := Fintype.ofFinite k
  obtain ⟨n, hpp, hn0⟩ := FiniteField.card k p
  have hn : Nat.card k = p ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hn0
  have hdvd : p ∣ 3 := by
    have : ((3 : ℕ) : k) = 0 := by exact_mod_cast h0
    exact (CharP.cast_eq_zero_iff k p 3).1 this
  have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hpp Nat.prime_three).1 hdvd
  rw [hn, hp3] at h
  have : 3 ∣ 3 ^ (n : ℕ) := dvd_pow_self 3 n.ne_zero
  omega

theorem k32b_det_of_mem_closure {k : Type} [Field k] {S : Set (GL (Fin 3) k)}
    (hS : ∀ A ∈ S, (A : Matrix (Fin 3) (Fin 3) k).det = 1) {A : GL (Fin 3) k}
    (hA : A ∈ Subgroup.closure S) : (A : Matrix (Fin 3) (Fin 3) k).det = 1 := by
  have hle : Subgroup.closure S ≤ (Matrix.GeneralLinearGroup.det : GL (Fin 3) k →* kˣ).ker := by
    rw [Subgroup.closure_le]
    intro B hB
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    exact Units.ext (by rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]; exact hS B hB)
  have := hle hA
  rw [MonoidHom.mem_ker] at this
  have h2 := congrArg Units.val this
  rwa [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one] at h2

theorem sylow_of_fused_of_isLThreeEps (K : Type) [Group K] [Finite K]
    (h : IsLThreeEps (K ⧸ GLAPPrimeCore 3 K)) :
    ∀ F : Subgroup K, IsElemAbelian 3 F → Nat.card F = 9 →
      (∀ x ∈ F, x ≠ 1 → ∀ y ∈ F, y ≠ 1 → ∃ g : K, g * x * g⁻¹ = y) →
      ∀ P : Subgroup K, IsPGroup 3 P → P ≤ Subgroup.centralizer (F : Set K) → F ≤ P → P ≤ F := by
  have key : ∀ (k : Type) [Field k] [Finite k], Nat.card k % 3 = 1 →
      ∀ L : Subgroup (GL (Fin 3) k), (∀ A ∈ L, (A : Matrix (Fin 3) (Fin 3) k).det = 1) →
      (K ⧸ GLAPPrimeCore 3 K) ≃* StatedProj L →
      ∀ F : Subgroup K, IsElemAbelian 3 F → Nat.card F = 9 →
        (∀ x ∈ F, x ≠ 1 → ∀ y ∈ F, y ≠ 1 → ∃ g : K, g * x * g⁻¹ = y) →
        ∀ P : Subgroup K, IsPGroup 3 P → P ≤ Subgroup.centralizer (F : Set K) → F ≤ P →
          P ≤ F := by
    intro k _ _ hmod L hdet θ
    refine k32b_sylow_of_proj (θ.toMonoidHom.comp (QuotientGroup.mk' _)) ?_ ?_
    · intro x hx
      have : (QuotientGroup.mk' (GLAPPrimeCore 3 K)) x = 1 := θ.injective (by simpa using hx)
      simpa using this
    · intro F hFc hF3 hcard hfuse c hc
      exact k32b_mem_of_commute_fused L (k32b_three_ne_zero hmod) hdet F hFc hF3 hcard hfuse c hc
  rcases h with ⟨k, _, _, hmod, ⟨θ⟩⟩ | ⟨k, _, _, q, hcard, hq, ⟨θ⟩⟩
  · exact key k hmod (StatedSL 3 k)
      (fun A hA => k32b_det_of_mem_closure (fun B hB => hB) hA) θ
  · refine key k ?_ (StatedSU 3 q k)
      (fun A hA => k32b_det_of_mem_closure (fun B hB => hB.1) hA) θ
    rw [hcard, Nat.pow_mod, hq]

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
