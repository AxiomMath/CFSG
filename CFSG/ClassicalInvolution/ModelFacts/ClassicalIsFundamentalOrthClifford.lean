module

public import CFSG.LieType.Universal.SpinCenter
public import CFSG.LieType.Universal.Spin.RootElements
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalOrthEigen
public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement
public import TauCeti.LinearAlgebra.CliffordAlgebra.CentralSimple.Even

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CliffordAlgebra QuadraticMap CFSG.LieType.Universal.Spin

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

theorem commute_of_forall_commute_ι {x : CliffordAlgebra Q} (hx : ∀ v, Commute x (ι Q v))
    (y : CliffordAlgebra Q) : y * x = x * y := by
  induction y using CliffordAlgebra.induction with
  | algebraMap r => exact Algebra.commutes r x
  | ι v => exact (hx v).symm.eq
  | mul a b ha hb => rw [mul_assoc, hb, ← mul_assoc, ha, mul_assoc]
  | add a b ha hb => rw [add_mul, mul_add, ha, hb]

theorem prod_map_ι_mem_evenOdd (l : List V) :
    (l.map (ι Q)).prod ∈ evenOdd Q (l.length : ZMod 2) := by
  induction l with
  | nil => exact one_le_evenOdd_zero Q (by simp)
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, List.length_cons, Nat.cast_succ, add_comm]
    exact evenOdd_mul_le Q _ _ (Submodule.mul_mem_mul (ι_mem_evenOdd_one Q a) ih)

variable [FiniteDimensional F V] [Invertible (2 : F)]

theorem exists_eq_algebraMap_of_commute_of_mem_even (hQ : Q.Nondegenerate) {u : CliffordAlgebra Q}
    (hu : u ∈ evenOdd Q 0) (hc : ∀ v, Commute u (ι Q v)) :
    ∃ c : F, u = algebraMap F (CliffordAlgebra Q) c := by
  rcases Nat.even_or_odd (Module.finrank F V) with he | ho
  · have : Algebra.IsCentral F (CliffordAlgebra Q) :=
      CliffordAlgebra.isCentral_of_even_finrank hQ he
    exact exists_eq_algebraMap_of_commute hc
  · have : NeZero (2 : F) := ⟨(isUnit_of_invertible (2 : F)).ne_zero⟩
    have hcen := TauCeti.CliffordAlgebra.isCentral_even_of_odd_finrank hQ ho
    have hmem : (⟨u, (Subalgebra.mem_toSubmodule (even Q)).mp (by
        rw [even_toSubmodule]; exact hu)⟩ : even Q) ∈ Subalgebra.center F (even Q) := by
      rw [Subalgebra.mem_center_iff]
      intro y
      exact Subtype.ext (commute_of_forall_commute_ι hc y.1)
    rw [Algebra.IsCentral.center_eq_bot] at hmem
    obtain ⟨c, hc'⟩ := Algebra.mem_bot.mp hmem
    exact ⟨c, (congrArg Subtype.val hc').symm⟩

theorem exists_eq_smul_prod_map_ι (hQ : Q.Nondegenerate) {z : spinGroup Q} {i : V ≃ₗ[F] V}
    (hi : i ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hii : i * i = 1)
    (hzi : spinAction Q z = i) {l : List V} (hl : l.Pairwise Q.IsOrtho) (hlen : Even l.length)
    (hspan : Submodule.span F {x : V | x ∈ l} = minusSp i) (hQl : ∀ x ∈ l, Q x ≠ 0) :
    ∃ c : F, (z : CliffordAlgebra Q) = c • (l.map (ι Q)).prod := by
  have h2 : (2 : F) ≠ 0 := (isUnit_of_invertible (2 : F)).ne_zero
  set ω := (l.map (ι Q)).prod with hω
  have hzι : ∀ v, (z : CliffordAlgebra Q) * ι Q v = ι Q (i v) * z := fun v =>
    (spinAction_apply_eq_iff' Q z v (i v)).mp (by rw [hzi])
  have hmem : ∀ x ∈ l, x ∈ minusSp i := fun x hx => hspan ▸ Submodule.subset_span hx
  have hcomm : ∀ v, Commute ((z : CliffordAlgebra Q) * ω) (ι Q v) := by
    intro v
    obtain ⟨vp, hvp, vm, hvm, rfl⟩ := exists_add_eq h2 hii v
    rw [map_add]
    refine Commute.add_right ?_ ?_
    · have hortho : ∀ x ∈ l, Q.IsOrtho x vp := by
        intro x hx
        refine isOrtho_polarBilin.mp ?_
        rw [polarBilin_apply_apply, polar_comm]
        exact polar_plusSp_minusSp h2 hi hvp (hmem x hx)
      have h1 := prod_map_ι_mul_ι_of_forall_isOrtho (Q := Q) hortho
      rw [hlen.neg_one_pow, one_smul] at h1
      have h2' := hzι vp
      rw [mem_plusSp.mp hvp] at h2'
      show ((z : CliffordAlgebra Q) * ω) * ι Q vp = ι Q vp * ((z : CliffordAlgebra Q) * ω)
      rw [mul_assoc, h1, ← mul_assoc, h2', mul_assoc]
    · have h1 := prod_map_ι_mul_ι_of_even_length (Q := Q) hl hlen
        (hspan ▸ hvm : vm ∈ Submodule.span F {x : V | x ∈ l})
      have h2' := hzι vm
      rw [mem_minusSp.mp hvm, map_neg] at h2'
      show ((z : CliffordAlgebra Q) * ω) * ι Q vm = ι Q vm * ((z : CliffordAlgebra Q) * ω)
      rw [mul_assoc, h1, mul_neg, ← mul_assoc, h2']
      simp only [neg_mul, neg_neg, mul_assoc]
      rfl
  have hlen0 : (l.length : ZMod 2) = 0 := (ZMod.natCast_eq_zero_iff_even).mpr hlen
  have hωeven : ω ∈ evenOdd Q 0 := by
    have := prod_map_ι_mem_evenOdd (Q := Q) l
    rwa [hlen0] at this
  have hzeven : (z : CliffordAlgebra Q) ∈ evenOdd Q 0 := by
    have : (z : CliffordAlgebra Q) ∈ (even Q).toSubmodule := spinGroup.mem_even z.2
    rwa [even_toSubmodule] at this
  have hueven : (z : CliffordAlgebra Q) * ω ∈ evenOdd Q 0 := by
    have := evenOdd_mul_le Q 0 0 (Submodule.mul_mem_mul hzeven hωeven)
    rwa [add_zero] at this
  obtain ⟨c₀, hc₀⟩ := exists_eq_algebraMap_of_commute_of_mem_even hQ hueven hcomm
  have hωω := prod_map_ι_sq_scalar (Q := Q) hl
  rw [← hω] at hωω
  set s : F := ((-1 : F) ^ l.length.choose 2) * (l.map Q).prod with hs
  have hs0 : s ≠ 0 := by
    refine mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) ?_
    rw [Ne, List.prod_eq_zero_iff]
    intro h0
    obtain ⟨x, hx, hx0⟩ := List.mem_map.mp h0
    exact hQl x hx hx0
  have e : (z : CliffordAlgebra Q) * algebraMap F _ s = algebraMap F _ c₀ * ω := by
    rw [← hωω, ← mul_assoc, hc₀]
  refine ⟨s⁻¹ * c₀, ?_⟩
  have e2 : s • (z : CliffordAlgebra Q) = c₀ • ω := by
    rw [Algebra.smul_def, Algebra.smul_def, ← e, Algebra.commutes]
  calc (z : CliffordAlgebra Q) = s⁻¹ • (s • (z : CliffordAlgebra Q)) := by
        rw [smul_smul, inv_mul_cancel₀ hs0, one_smul]
    _ = (s⁻¹ * c₀) • ω := by rw [e2, smul_smul]

theorem spinLift_sq_and_norm (hQ : Q.Nondegenerate) {z : spinGroup Q} {i : V ≃ₗ[F] V}
    (hi : i ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hii : i * i = 1)
    (hzi : spinAction Q z = i) {l : List V} (hl : l.Pairwise Q.IsOrtho) (hlen : Even l.length)
    (hspan : Submodule.span F {x : V | x ∈ l} = minusSp i) (hQl : ∀ x ∈ l, Q x ≠ 0) :
    ∃ c : F, c * c * (l.map Q).prod = 1 ∧
      (z : CliffordAlgebra Q) * z =
        algebraMap F (CliffordAlgebra Q) ((-1) ^ l.length.choose 2) := by
  obtain ⟨c, hc⟩ := exists_eq_smul_prod_map_ι hQ hi hii hzi hl hlen hspan hQl
  have hωω := prod_map_ι_sq_scalar (Q := Q) hl
  have hrev := reverse_prod_map_ι_of_pairwise_isOrtho (Q := Q) hl
  set ω := (l.map (ι Q)).prod with hω
  set P : F := (l.map Q).prod with hP
  set ε : F := (-1 : F) ^ l.length.choose 2 with hε
  have hεε : ε * ε = 1 := by
    rw [hε, ← pow_add, ← two_mul, pow_mul]
    simp
  have hstar : star (z : CliffordAlgebra Q) = c • (ε • ω) := by
    rw [CliffordAlgebra.star_def, spinGroup.involute_eq z.2, hc, map_smul, hrev]
  have hnorm : star (z : CliffordAlgebra Q) * z = 1 := spinGroup.star_mul_self_of_mem z.2
  have hzz : (z : CliffordAlgebra Q) * z = algebraMap F _ (c * c * (ε * P)) := by
    rw [hc, smul_mul_smul_comm, hωω, Algebra.smul_def, ← map_mul]
  have hnn : star (z : CliffordAlgebra Q) * z = algebraMap F _ (c * (ε * c) * (ε * P)) := by
    rw [hstar, hc, smul_mul_smul_comm, smul_mul_assoc, hωω, Algebra.smul_def, Algebra.smul_def,
      ← map_mul, ← map_mul]
    congr 1
    ring
  have h1 : c * (ε * c) * (ε * P) = 1 := by
    apply algebraMap_injective' Q
    rw [← hnn, hnorm, map_one]
  have hcc : c * c * P = 1 := by
    have e : c * (ε * c) * (ε * P) = c * c * P * (ε * ε) := by ring
    rw [e, hεε, mul_one] at h1
    exact h1
  refine ⟨c, hcc, ?_⟩
  rw [hzz]
  congr 1
  calc c * c * (ε * P) = ε * (c * c * P) := by ring
    _ = ε := by rw [hcc, mul_one]

end CFSG.ClassicalInvolution.ModelFacts
