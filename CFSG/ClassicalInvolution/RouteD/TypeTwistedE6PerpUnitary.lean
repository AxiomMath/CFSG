module

public import CFSG.LinearAlgebra.LinearGroups.UnitaryVectorCount
public import CFSG.ClassicalInvolution.RouteD.TypeTwistedE6PerpOrthArith
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.ClassicalGroups.Unitary.Finite
public import CFSG.ClassicalInvolution.Phan.Geometry.Basic

public section

namespace CFSG.ClassicalInvolution.RouteD.NonClassical

open CFSG.ClassicalInvolution.Phan CFSG.ClassicalGroups.Unitary CFSG.LieType.BorelTits
  CFSG.LocalAnalysis.ComponentInitial CFSG.LinearGroups Module

section Bridge

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p] {m : ℕ}

@[expose] noncomputable def hermB (h : UnitaryFieldData p f K) (W : Submodule K (Fin m → K)) :
    W →ₛₗ[h.bar] W →ₗ[K] K :=
  LinearMap.mk₂'ₛₗ h.bar (RingHom.id K)
    (fun x y => ∑ i, h.bar ((x : Fin m → K) i) * (y : Fin m → K) i)
    (fun x x' y => by
      simp only [Submodule.coe_add, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib])
    (fun c x y => by
      simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum,
        mul_assoc])
    (fun x y y' => by
      simp only [Submodule.coe_add, Pi.add_apply, mul_add, Finset.sum_add_distrib])
    (fun c x y => by
      simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum,
        mul_left_comm])

omit [Finite K] [Fact p.Prime] [CharP K p] in
theorem hermB_apply (h : UnitaryFieldData p f K) (W : Submodule K (Fin m → K)) (x y : W) :
    hermB h W x y = ∑ i, h.bar ((x : Fin m → K) i) * (y : Fin m → K) i := rfl

theorem herm_unitary_eq (h : UnitaryFieldData p f K) (x y : Fin m → K) :
    herm (unitaryInvolution K p f) x y = ∑ i, h.bar (x i) * y i := by
  simp only [herm, unitaryInvolution_apply, h.bar_apply]

theorem hermB_eq_herm (h : UnitaryFieldData p f K) (W : Submodule K (Fin m → K)) (x y : W) :
    hermB h W x y = herm (unitaryInvolution K p f) (x : Fin m → K) y := by
  rw [hermB_apply, herm_unitary_eq h]

omit [Finite K] [Fact p.Prime] [CharP K p] in
theorem hermB_isSymm (h : UnitaryFieldData p f K) (W : Submodule K (Fin m → K)) :
    (hermB h W).IsSymm :=
  ⟨fun x y => by
    simp only [hermB_apply, map_sum, map_mul, h.bar_bar]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _⟩

theorem hermB_separatingLeft (h : UnitaryFieldData p f K) {W : Submodule K (Fin m → K)}
    (hW : Nondeg (unitaryInvolution K p f) W) : (hermB h W).SeparatingLeft := by
  intro x hx
  refine Subtype.ext (hW x x.2 fun t ht => ?_)
  have := hx ⟨t, ht⟩
  rwa [hermB_eq_herm] at this

end Bridge

section Aniso

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p] {m : ℕ}

abbrev Aniso (K : Type) [Field K] (p f : ℕ) [Fact p.Prime] [CharP K p] [Finite K] {m : ℕ}
    (W : Submodule K (Fin m → K)) : Type :=
  {v : W // herm (unitaryInvolution K p f) (v : Fin m → K) v ≠ 0}

theorem card_subtype_add_compl {α : Type*} [Finite α] (P : α → Prop) :
    Nat.card {x // P x} + Nat.card {x // ¬ P x} = Nat.card α := by
  classical
  rw [← Nat.card_sum, Nat.card_congr (Equiv.sumCompl P)]

theorem card_aniso_add (h : UnitaryFieldData p f K) {W : Submodule K (Fin m → K)}
    (hW : Nondeg (unitaryInvolution K p f) W) {n : ℕ} (hn : finrank K W = n) (hn1 : 1 ≤ n) :
    (Nat.card (Aniso K p f W) : ℤ) +
        (((p ^ f : ℕ) : ℤ) ^ (2 * n - 1) +
          (-1) ^ n * (((p ^ f : ℕ) : ℤ) - 1) * ((p ^ f : ℕ) : ℤ) ^ (n - 1)) =
      ((p ^ f : ℕ) : ℤ) ^ (2 * n) := by
  have hvc := (unitary_hermitian_vector_count h (hermB_isSymm h W) (hermB_separatingLeft h hW)
    hn hn1).1
  have hiso : Nat.card {v : W // hermB h W v v = 0} =
      Nat.card {v : W // herm (unitaryInvolution K p f) (v : Fin m → K) v = 0} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun v => by rw [hermB_eq_herm])
  have hW0 : Nat.card W = ((p ^ f : ℕ)) ^ (2 * n) := by
    rw [Module.natCard_eq_pow_finrank (K := K), hn, h.card, ← pow_mul, ← pow_mul]
    congr 1
    ring
  have hsplit := card_subtype_add_compl
    (fun v : W => herm (unitaryInvolution K p f) (v : Fin m → K) v = 0)
  rw [← hiso] at hsplit
  rw [hW0] at hsplit
  have hsplit' : (Nat.card (Aniso K p f W) : ℤ) + (Nat.card {v : W // hermB h W v v = 0} : ℤ) =
      (((p ^ f : ℕ) : ℤ)) ^ (2 * n) := by
    have := congrArg (fun k : ℕ => (k : ℤ)) hsplit
    push_cast at this
    rw [add_comm] at this
    simpa [Aniso] using this
  rw [hvc] at hsplit'
  exact hsplit'

end Aniso

section Pairs

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p] {m : ℕ}

@[expose] def anisoNum (q : ℤ) (n : ℕ) : ℤ :=
  q ^ (2 * n) - (q ^ (2 * n - 1) + (-1) ^ n * (q - 1) * q ^ (n - 1))

theorem card_aniso (h : UnitaryFieldData p f K) {W : Submodule K (Fin m → K)}
    (hW : Nondeg (unitaryInvolution K p f) W) {n : ℕ} (hn : finrank K W = n) (hn1 : 1 ≤ n) :
    (Nat.card (Aniso K p f W) : ℤ) = anisoNum ((p ^ f : ℕ) : ℤ) n := by
  have := card_aniso_add h hW hn hn1
  unfold anisoNum
  linarith

abbrev OrthPairs (K : Type) [Field K] (p f : ℕ) [Fact p.Prime] [CharP K p] [Finite K] {m : ℕ}
    (U : Submodule K (Fin m → K)) : Type :=
  {x : (Fin m → K) × (Fin m → K) // x.1 ∈ U ∧ x.2 ∈ U ∧
    herm (unitaryInvolution K p f) x.1 x.1 ≠ 0 ∧ herm (unitaryInvolution K p f) x.2 x.2 ≠ 0 ∧
    herm (unitaryInvolution K p f) x.1 x.2 = 0}

@[expose] def orthPairsEquiv (hσ : IsUnitaryInvolution (unitaryInvolution K p f))
    (U : Submodule K (Fin m → K)) :
    OrthPairs K p f U ≃ Σ v : Aniso K p f U,
      Aniso K p f (U ⊓ perp (unitaryInvolution K p f) (K ∙ (v.1 : Fin m → K))) where
  toFun x := ⟨⟨⟨x.1.1, x.2.1⟩, x.2.2.2.1⟩, ⟨⟨x.1.2, ⟨x.2.2.1,
    mem_perp_span_singleton.mpr ((herm_eq_zero_iff hσ _ _).mp x.2.2.2.2.2)⟩⟩, x.2.2.2.2.1⟩⟩
  invFun y := ⟨(y.1.1.1, y.2.1.1), y.1.1.2, y.2.1.2.1, y.1.2, y.2.2,
    (herm_eq_zero_iff hσ _ _).mp (mem_perp_span_singleton.mp y.2.1.2.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_orthPairs (h : UnitaryFieldData p f K) {U : Submodule K (Fin m → K)}
    (hU : Nondeg (unitaryInvolution K p f) U) {n : ℕ} (hn : finrank K U = n + 1) (hn1 : 1 ≤ n) :
    (Nat.card (OrthPairs K p f U) : ℤ) =
      anisoNum ((p ^ f : ℕ) : ℤ) (n + 1) * anisoNum ((p ^ f : ℕ) : ℤ) n := by
  classical
  have hσ := isUnitaryInvolution_unitaryInvolution h.card_eq_sq
  let _ : Fintype (Aniso K p f U) := Fintype.ofFinite _
  have hnd : ∀ v : Aniso K p f U, Nondeg (unitaryInvolution K p f)
      (U ⊓ perp (unitaryInvolution K p f) (K ∙ (v.1 : Fin m → K))) :=
    fun v => Nondeg.inf_perp_span_singleton hσ v.1.2 v.2 hU
  have hdim : ∀ v : Aniso K p f U, finrank K
      ↥(U ⊓ perp (unitaryInvolution K p f) (K ∙ (v.1 : Fin m → K))) = n := fun v => by
    have := finrank_eq_inf_perp_add_one hσ v.1.2 v.2
    omega
  rw [Nat.card_congr (orthPairsEquiv hσ U), Nat.card_sigma, Nat.cast_sum]
  rw [Finset.sum_congr rfl fun v _ => card_aniso h (hnd v) (hdim v) hn1, Finset.sum_const,
    Finset.card_univ, ← Nat.card_eq_fintype_card, nsmul_eq_mul,
    card_aniso h hU hn (by omega)]

end Pairs

section Planes

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p] {m : ℕ}

abbrev Planes (K : Type) [Field K] (p f : ℕ) [Fact p.Prime] [CharP K p] [Finite K] {m : ℕ}
    (U : Submodule K (Fin m → K)) : Type :=
  {P : Submodule K (Fin m → K) //
    Nondeg (unitaryInvolution K p f) P ∧ finrank K P = 2 ∧ P ≤ U}

omit [Finite K] [Fact p.Prime] [CharP K p] in
theorem finrank_span_pair {σ : K ≃+* K} (hσ : IsUnitaryInvolution σ) {a b : Fin m → K}
    (ha : herm σ a a ≠ 0) (hb : herm σ b b ≠ 0) (hab : herm σ a b = 0) :
    finrank K ↥(K ∙ a ⊔ K ∙ b) = 2 := by
  have ha0 : a ≠ 0 := fun h => ha (by rw [h]; simp)
  have hb0 : b ≠ 0 := fun h => hb (by rw [h]; simp)
  have hdisj : Disjoint (K ∙ a) (K ∙ b) :=
    (disjoint_span_perp ha).mono_right ((Submodule.span_singleton_le_iff_mem _ _).mpr
      (mem_perp_span_singleton.mpr ((herm_eq_zero_iff hσ _ _).mp hab)))
  rw [finrank_sup_of_disjoint hdisj, finrank_span_singleton ha0, finrank_span_singleton hb0]

@[expose] def spanPair (hσ : IsUnitaryInvolution (unitaryInvolution K p f))
    {U : Submodule K (Fin m → K)} (x : OrthPairs K p f U) : Planes K p f U :=
  ⟨K ∙ x.1.1 ⊔ K ∙ x.1.2, Nondeg.sup_of_orth hσ (nondeg_span_singleton x.2.2.2.1)
      (nondeg_span_singleton x.2.2.2.2.1) (orth_span_singleton_iff.mpr x.2.2.2.2.2),
    finrank_span_pair hσ x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2,
    sup_le ((Submodule.span_singleton_le_iff_mem _ _).mpr x.2.1)
      ((Submodule.span_singleton_le_iff_mem _ _).mpr x.2.2.1)⟩

@[expose] def pairsFiberEquiv (hσ : IsUnitaryInvolution (unitaryInvolution K p f))
    {U : Submodule K (Fin m → K)} (P : Planes K p f U) :
    {x : OrthPairs K p f U // spanPair hσ x = P} ≃ OrthPairs K p f P.1 where
  toFun x := ⟨x.1.1, by
      have hsp : K ∙ x.1.1.1 ⊔ K ∙ x.1.1.2 = P.1 := congrArg Subtype.val x.2
      exact ⟨by rw [← hsp]; exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self _),
        by rw [← hsp]; exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _),
        x.1.2.2.2.1, x.1.2.2.2.2.1, x.1.2.2.2.2.2⟩⟩
  invFun w := ⟨⟨w.1, P.2.2.2 w.2.1, P.2.2.2 w.2.2.1, w.2.2.2.1, w.2.2.2.2.1, w.2.2.2.2.2⟩,
    Subtype.ext (Submodule.eq_of_le_of_finrank_eq (S₁ := K ∙ w.1.1 ⊔ K ∙ w.1.2) (S₂ := P.1)
      (sup_le ((Submodule.span_singleton_le_iff_mem _ _).mpr w.2.1)
        ((Submodule.span_singleton_le_iff_mem _ _).mpr w.2.2.1))
      (by rw [finrank_span_pair hσ w.2.2.2.1 w.2.2.2.2.1 w.2.2.2.2.2, P.2.2.1]))⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_orthPairs_eq_planes (h : UnitaryFieldData p f K) (U : Submodule K (Fin m → K)) :
    (Nat.card (OrthPairs K p f U) : ℤ) =
      Nat.card (Planes K p f U) *
        (anisoNum ((p ^ f : ℕ) : ℤ) 2 * anisoNum ((p ^ f : ℕ) : ℤ) 1) := by
  classical
  have hσ := isUnitaryInvolution_unitaryInvolution h.card_eq_sq
  let _ : Fintype (Planes K p f U) := Fintype.ofFinite _
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv (spanPair hσ)), Nat.card_sigma, Nat.cast_sum]
  rw [Finset.sum_congr rfl fun P _ => by
      rw [Nat.card_congr (pairsFiberEquiv hσ P),
        card_orthPairs h P.2.1 (n := 1) P.2.2.1 le_rfl],
    Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, nsmul_eq_mul]

theorem card_planes_mul (h : UnitaryFieldData p f K) {U : Submodule K (Fin m → K)}
    (hU : Nondeg (unitaryInvolution K p f) U) (h4 : finrank K U = 4) :
    (Nat.card (Planes K p f U) : ℤ) *
        (anisoNum ((p ^ f : ℕ) : ℤ) 2 * anisoNum ((p ^ f : ℕ) : ℤ) 1) =
      anisoNum ((p ^ f : ℕ) : ℤ) 4 * anisoNum ((p ^ f : ℕ) : ℤ) 3 := by
  rw [← card_orthPairs_eq_planes h U]
  exact card_orthPairs h hU (n := 3) h4 (by norm_num)

theorem planes_arith {q N : ℤ} (hq : 2 ≤ q)
    (h : N * (anisoNum q 2 * anisoNum q 1) = anisoNum q 4 * anisoNum q 3) :
    N = q ^ 4 * (q ^ 2 + 1) * (q * (q - 1) + 1) := by
  have e1 : anisoNum q 1 = q ^ 2 - 1 := by
    norm_num [anisoNum]
  have e2 : anisoNum q 2 = q * (q - 1) ^ 2 * (q + 1) := by
    norm_num [anisoNum]
    ring
  have e3 : anisoNum q 3 = q ^ 2 * (q - 1) * (q ^ 3 + 1) := by
    norm_num [anisoNum]
    ring
  have e4 : anisoNum q 4 = q ^ 3 * (q - 1) * (q ^ 4 - 1) := by
    norm_num [anisoNum]
    ring
  rw [e1, e2, e3, e4] at h
  have hne : q * (q - 1) ^ 2 * (q + 1) * (q ^ 2 - 1) ≠ 0 := by
    have h1 : (0 : ℤ) < q := by linarith
    have h2 : (0 : ℤ) < q - 1 := by linarith
    have h3 : (0 : ℤ) < q + 1 := by linarith
    have h4 : (0 : ℤ) < q ^ 2 - 1 := by nlinarith
    positivity
  refine mul_right_cancel₀ hne ?_
  linear_combination h

theorem te6Core_cast {n : ℕ} (hn : 1 ≤ n) :
    ((te6Core n : ℕ) : ℤ) = (n : ℤ) ^ 4 * ((n : ℤ) ^ 2 + 1) * ((n : ℤ) * ((n : ℤ) - 1) + 1) := by
  unfold te6Core
  push_cast [Nat.cast_sub hn]
  ring

theorem card_planes (h : UnitaryFieldData p f K) {U : Submodule K (Fin m → K)}
    (hU : Nondeg (unitaryInvolution K p f) U) (h4 : finrank K U = 4) (hq : 2 ≤ p ^ f) :
    Nat.card (Planes K p f U) = te6Core (p ^ f) := by
  have hq' : (2 : ℤ) ≤ ((p ^ f : ℕ) : ℤ) := by exact_mod_cast hq
  have := planes_arith hq' (card_planes_mul h hU h4)
  rw [← te6Core_cast (by omega)] at this
  exact_mod_cast this

end Planes

end CFSG.ClassicalInvolution.RouteD.NonClassical
