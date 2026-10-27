module

public import CFSG.LieType.Chevalley.CLSOddG2F4E8AllInvolutionFourGroup
public import CFSG.LieType.AlgebraicGroups.RationalCentralizerCocycleComponents

public noncomputable section

namespace CFSG.LieType.Chevalley.OddE6AllInvolution

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups
open CFSG.LocalAnalysis.ComponentInitial.FixedFourGroup
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LieType.Chevalley.OddG2F4E8AllInvolution (exists_four_group_of_conj_fix
  exists_four_group_of_quadratic_field_coset)

theorem exists_fixed_four_group_of_baseChange
    {τ : Tag} {K Lk : Type} [Field K] [Field Lk]
    (ι : K →+* Lk) {C : Subgroup (ModGL τ K)} (β : MulAut C) (z : ModGL τ Lk)
    (hβz : ∀ u : C, baseChangeGL ι (β u : ModGL τ K) =
      z * baseChangeGL ι (u : ModGL τ K) * z⁻¹)
    {E : Subgroup (ModGL τ Lk)} (hE : E ≤ C.map (baseChangeGL ι) ⊓ Subgroup.centralizer {z})
    [hEab : CFSG.IsElementaryAbelian 2 E] (hEcard : Nat.card E = 4) :
    ∃ V : Subgroup C, V ≤ fixedSubgroup β ∧ CFSG.IsElementaryAbelian 2 V ∧ Nat.card V = 4 := by
  classical
  set φ : C →* ModGL τ Lk := (baseChangeGL ι).comp C.subtype with hφ
  have hφinj : Function.Injective φ := (baseChangeGL_injective ι).comp Subtype.val_injective
  have hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hEab.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hEs : ∀ x ∈ E, x ^ 2 = 1 := fun x hx => elemPow_eq_one_of_isElementaryAbelian x hx
  refine ⟨E.comap φ, fun u hu => ?_, ?_, ?_⟩
  · change β u = u
    refine hφinj ?_
    have hc : φ u * z = z * φ u := Subgroup.mem_centralizer_singleton_iff.1 (hE hu).2
    change baseChangeGL ι (β u : ModGL τ K) = φ u
    rw [hβz u]
    change z * φ u * z⁻¹ = φ u
    rw [← hc, mul_inv_cancel_right]
  · exact { is_comm := ⟨fun a b => Subtype.ext (hφinj (by
              simp only [Subgroup.coe_mul, map_mul]
              exact hEc _ a.2 _ b.2))⟩
            exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a =>
              Subtype.ext (hφinj (by
                simp only [Subgroup.coe_pow, Subgroup.coe_one, map_pow, map_one]
                exact hEs _ a.2)) }
  · have hrange : E ≤ φ.range := fun y hy => by
      obtain ⟨c, hc, rfl⟩ := (hE hy).1
      exact ⟨⟨c, hc⟩, rfl⟩
    rw [← Subgroup.card_map_of_injective hφinj, Subgroup.map_comap_eq_self hrange, hEcard]

theorem map_conj_inv_le_inf_centralizer {G : Type*} [Group G] {H : Subgroup G} {y z A : G}
    (hy : y ∈ Subgroup.normalizer (H : Set G)) (hyz : y * z * y⁻¹ = A) {E : Subgroup G}
    (hE : E ≤ H ⊓ Subgroup.centralizer {A}) :
    E.map (MulAut.conj y⁻¹).toMonoidHom ≤ H ⊓ Subgroup.centralizer {z} := by
  rintro _ ⟨e, he, rfl⟩
  obtain ⟨heH, heA⟩ := Subgroup.mem_inf.1 (hE he)
  rw [Subgroup.mem_centralizer_singleton_iff] at heA
  refine Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.1 (inv_mem hy) e).1 heH, ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  change y⁻¹ * e * y⁻¹⁻¹ * z = z * (y⁻¹ * e * y⁻¹⁻¹)
  have hz : z = y⁻¹ * A * y := by rw [← hyz]; group
  rw [hz]
  calc y⁻¹ * e * y⁻¹⁻¹ * (y⁻¹ * A * y) = y⁻¹ * (e * A) * y := by group
    _ = y⁻¹ * (A * e) * y := by rw [heA]
    _ = y⁻¹ * A * y * (y⁻¹ * e * y⁻¹⁻¹) := by group

theorem exists_four_group_inf_centralizer {G : Type*} [Group G] {H : Subgroup G} {y z A : G}
    (hy : y ∈ Subgroup.normalizer (H : Set G)) (hyz : y * z * y⁻¹ = A) {E : Subgroup G}
    (hE : E ≤ H ⊓ Subgroup.centralizer {A}) [CFSG.IsElementaryAbelian 2 E]
    (hEcard : Nat.card E = 4) :
    ∃ E' : Subgroup G, E' ≤ H ⊓ Subgroup.centralizer {z} ∧ CFSG.IsElementaryAbelian 2 E' ∧
      Nat.card E' = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨E.map (MulAut.conj y⁻¹).toMonoidHom, map_conj_inv_le_inf_centralizer hy hyz hE,
    CFSG.IsElementaryAbelian.map _, ?_⟩
  rw [Subgroup.card_map_of_injective (MulAut.conj y⁻¹).injective, hEcard]

theorem exists_sign_preimage {K Lk : Type} [Field K] [Field Lk] (ι : K →+* Lk) {n : ℕ}
    {a : Fin n → Lkˣ} (ha : ∀ i, a i = 1 ∨ a i = -1) :
    ∃ b : Fin n → Kˣ, (fun i => Units.map ι.toMonoidHom (b i)) = a := by
  classical
  refine ⟨fun i => if a i = 1 then 1 else -1, funext fun i => ?_⟩
  by_cases h : a i = 1
  · simp only [h, ↓reduceIte, map_one]
  · simp only [h, ↓reduceIte]
    rw [(ha i).resolve_left h]
    ext
    simp

theorem isAlgebraic_zmod_algebraicClosure (K : Type) [Field K] [Finite K] (p : ℕ) [Fact p.Prime]
    [CharP (AlgebraicClosure K) p] :
    letI := ZMod.algebra (AlgebraicClosure K) p
    Algebra.IsAlgebraic (ZMod p) (AlgebraicClosure K) := by
  let _ : Algebra (ZMod p) (AlgebraicClosure K) := ZMod.algebra (AlgebraicClosure K) p
  refine ⟨fun y => ?_⟩
  obtain ⟨E, hEf, hyE, -⟩ :=
    exists_finite_subfield_of_finset (K := K) ({y} : Finset (AlgebraicClosure K))
  have hy : y ∈ E := hyE (Finset.mem_coe.2 (Finset.mem_singleton_self y))
  have : Fintype E := Fintype.ofFinite E
  have hpow : y ^ Fintype.card E = y :=
    congrArg Subtype.val (FiniteField.pow_card (⟨y, hy⟩ : E))
  refine ⟨Polynomial.X ^ Fintype.card E - Polynomial.X,
    FiniteField.X_pow_card_sub_X_ne_zero (ZMod p) Fintype.one_lt_card, ?_⟩
  rw [map_sub, map_pow, Polynomial.aeval_X, hpow, sub_self]

end CFSG.LieType.Chevalley.OddE6AllInvolution
