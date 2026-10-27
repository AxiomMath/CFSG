module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2ConcreteSplitTorusCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralOddRotationCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4CycArith

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace L2Cyc

open CFSG GorensteinWalter Subgroup Matrix

variable {F : Type} [Field F] [Finite F]

noncomputable abbrev torus (F : Type) [Field F] : Subgroup (PGL2 F) :=
  (pGammaL2FullSplitTorus F).range

instance finite_pgl2 : Finite (PGL2 F) :=
  Finite.of_surjective ProjGenLinGroup.mk ProjGenLinGroup.mk_surjective

theorem factorization_eq {q : ℕ} (hq : q % 4 = 1) :
    (2 * (q - 1)).factorization 2 = (q * (q ^ 2 - 1)).factorization 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, rfl⟩ : ∃ t, q = 4 * t + 1 := ⟨q / 4, by omega⟩
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · simp
  have e1 : 4 * t + 1 - 1 = 4 * t := by omega
  have e2 : (4 * t + 1) ^ 2 - 1 = 4 * t * (2 * (2 * t + 1)) := by
    rw [show (4 * t + 1) ^ 2 = 4 * t * (2 * (2 * t + 1)) + 1 by ring, Nat.add_sub_cancel]
  have h1 : padicValNat 2 (2 * (4 * t)) = 1 + padicValNat 2 (4 * t) := by
    rw [padicValNat.mul (by norm_num) (by omega), padicValNat.self (by norm_num)]
  have h2 : padicValNat 2 (2 * (2 * t + 1)) = 1 := by
    rw [padicValNat.mul (by norm_num) (by omega), padicValNat.self (by norm_num),
      padicValNat.eq_zero_of_not_dvd (by omega : ¬ 2 ∣ 2 * t + 1)]
  have h3 : padicValNat 2 ((4 * t + 1) * (4 * t * (2 * (2 * t + 1)))) =
      padicValNat 2 (4 * t) + 1 := by
    rw [padicValNat.mul (by omega) (by positivity), padicValNat.mul (by omega) (by omega), h2,
      padicValNat.eq_zero_of_not_dvd (by omega : ¬ 2 ∣ 4 * t + 1)]
    ring
  rw [e1, e2, Nat.factorization_def _ Nat.prime_two, Nat.factorization_def _ Nat.prime_two, h1, h3]
  ring

theorem exists_conj_mem_sup (hF : IsOddPrimePower (Nat.card F)) (hF4 : Nat.card F % 4 = 1) :
    ∃ w : PGL2 F, IsCyclic (torus F) ∧ w ∉ torus F ∧ w * w = 1 ∧
      (∀ x ∈ torus F, w * x * w⁻¹ = x⁻¹) ∧
      Nat.card (torus F ⊔ zpowers w : Subgroup (PGL2 F)) = 2 * Nat.card (torus F) ∧
      ∀ P : Subgroup (PGL2 F), IsPGroup 2 P →
        ∃ n : PGL2 F, ∀ x ∈ P, n * x * n⁻¹ ∈ torus F ⊔ zpowers w := by
  classical
  obtain ⟨w, hUc, hUcard, -, -, hwU, hww, hinv, -, hMcard, -⟩ :=
    pgl2_fullSplitTorus_centralizer_data F hF
  refine ⟨w, hUc, hwU, hww, hinv, hMcard, fun P hP => ?_⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := torus F ⊔ zpowers w with hM
  have hfac : (Nat.card M).factorization 2 = (Nat.card (PGL2 F)).factorization 2 := by
    rw [hMcard, hUcard, pgl2_card_formula F]
    exact factorization_eq hF4
  obtain ⟨S'⟩ := (inferInstance : Nonempty (Sylow 2 M))
  have hS₀ : Nat.card ((S' : Subgroup M).map M.subtype) =
      2 ^ (Nat.card (PGL2 F)).factorization 2 := by
    rw [card_map_of_injective M.subtype_injective, Sylow.card_eq_multiplicity, hfac]
  let T₀ : Sylow 2 (PGL2 F) := Sylow.ofCard _ hS₀
  obtain ⟨T, hPT⟩ := hP.exists_le_sylow
  obtain ⟨n, hn⟩ := MulAction.exists_smul_eq (PGL2 F) T T₀
  refine ⟨n, fun x hx => ?_⟩
  have h1 : n * x * n⁻¹ ∈ ((n • T : Sylow 2 (PGL2 F)) : Subgroup (PGL2 F)) := by
    rw [Sylow.coe_subgroup_smul, mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def,
      ← map_inv, MulAut.conj_apply, inv_inv]
    convert hPT hx using 1
    group
  rw [hn] at h1
  obtain ⟨y, -, hy⟩ := h1
  rw [← hy]
  exact y.2

omit [Finite F] in
theorem mem_torus_of_mem_sup {w : PGL2 F} (hwU : w ∉ torus F) (hww : w * w = 1)
    (hinv : ∀ x ∈ torus F, w * x * w⁻¹ = x⁻¹) {x : PGL2 F} (hx : x ∈ torus F ⊔ zpowers w)
    (hx2 : x * x ≠ 1) : x ∈ torus F := by
  obtain ⟨u, hu, rfl | rfl⟩ := (mem_sup_zpowers_of_involution_inverts hwU hww hinv).mp hx
  · exact hu
  · exfalso
    apply hx2
    have hw' : w⁻¹ = w := inv_eq_of_mul_eq_one_right hww
    calc u * w * (u * w) = u * (w * u * w⁻¹) := by rw [hw']; group
      _ = 1 := by rw [hinv u hu, mul_inv_cancel]

theorem exists_conj_eq_torus (hF : IsOddPrimePower (Nat.card F)) (hF4 : Nat.card F % 4 = 1)
    {h : PGL2 F} {k : ℕ} (hk : 2 ≤ k) (hh : orderOf h = 2 ^ k) :
    ∃ (n : PGL2 F) (ζ : Fˣ), n * h * n⁻¹ = pGammaL2FullSplitTorus F ζ ∧ orderOf ζ = 2 ^ k := by
  obtain ⟨w, -, hwU, hww, hinv, -, hconj⟩ := exists_conj_mem_sup hF hF4
  have hP : IsPGroup 2 (zpowers h) := by
    apply IsPGroup.of_card (n := k)
    rw [Nat.card_zpowers, hh]
  obtain ⟨n, hn⟩ := hconj _ hP
  have hord : orderOf (n * h * n⁻¹) = 2 ^ k := by
    rw [← hh]
    exact (SemiconjBy.orderOf_eq n (x := h) (y := n * h * n⁻¹) (by
      change n * h = n * h * n⁻¹ * n
      group)).symm
  have hx2 : n * h * n⁻¹ * (n * h * n⁻¹) ≠ 1 := by
    intro h1
    have h2 : orderOf (n * h * n⁻¹) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact h1)
    rw [hord] at h2
    have h4 : 2 ^ 2 ∣ 2 ^ k := pow_dvd_pow 2 hk
    have := Nat.le_of_dvd (by norm_num) (h4.trans h2)
    norm_num at this
  obtain ⟨ζ, hζ⟩ := mem_torus_of_mem_sup hwU hww hinv (hn h (mem_zpowers h)) hx2
  refine ⟨n, ζ, hζ.symm, ?_⟩
  rw [← hord, ← hζ, orderOf_injective _ (pGammaL2FullSplitTorus_injective F)]

theorem card_le_four_of_le_sup {w : PGL2 F} (hU : IsCyclic (torus F)) (hwU : w ∉ torus F)
    (hww : w * w = 1) (hinv : ∀ x ∈ torus F, w * x * w⁻¹ = x⁻¹)
    (hMcard : Nat.card (torus F ⊔ zpowers w : Subgroup (PGL2 F)) = 2 * Nat.card (torus F))
    {A : Subgroup (PGL2 F)} (hAM : A ≤ torus F ⊔ zpowers w)
    (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hncyc : ¬ IsCyclic A) : Nat.card A ≤ 4 := by
  classical
  by_cases hAU : A ≤ torus F
  · exact absurd (Subgroup.isCyclic_of_le hAU) hncyc
  obtain ⟨x₀, hx₀A, hx₀U⟩ := Set.not_subset.mp hAU
  obtain ⟨u₀, hu₀, hx₀⟩ := (mem_sup_zpowers_of_involution_inverts hwU hww hinv).mp (hAM hx₀A)
  have hx₀w : x₀ = u₀ * w := hx₀.resolve_left (fun h => hx₀U (h ▸ hu₀))
  have hsq : ∀ u ∈ A ⊓ torus F, u ^ 2 = 1 := by
    rintro u ⟨huA, huU⟩
    have hc := hA u huA x₀ hx₀A
    rw [hx₀w] at hc
    have h1 : w * u = u⁻¹ * w := by
      have := hinv u huU
      calc w * u = w * u * w⁻¹ * w := by group
        _ = u⁻¹ * w := by rw [this]
    have hcomm : u₀ * u = u * u₀ := by
      have := hU
      exact congrArg Subtype.val ((IsCyclic.isMulCommutative (α := torus F)).is_comm.comm
        ⟨u₀, hu₀⟩ ⟨u, huU⟩)
    have h2 : u * (u₀ * w) = u⁻¹ * (u₀ * w) := by
      calc u * (u₀ * w) = u₀ * w * u := hc
        _ = u₀ * (w * u) := by group
        _ = u₀ * (u⁻¹ * w) := by rw [h1]
        _ = u⁻¹ * (u₀ * w) := by
          have : u₀ * u⁻¹ = u⁻¹ * u₀ := by
            calc u₀ * u⁻¹ = u⁻¹ * (u * u₀) * u⁻¹ := by group
              _ = u⁻¹ * (u₀ * u) * u⁻¹ := by rw [hcomm]
              _ = u⁻¹ * u₀ := by group
          calc u₀ * (u⁻¹ * w) = (u₀ * u⁻¹) * w := by group
            _ = (u⁻¹ * u₀) * w := by rw [this]
            _ = u⁻¹ * (u₀ * w) := by group
    have h3 : u = u⁻¹ := mul_right_cancel h2
    rw [sq]
    calc u * u = u * u⁻¹ := by rw [← h3]
      _ = 1 := mul_inv_cancel u
  have hAU2 : Nat.card ((A ⊓ torus F).subgroupOf (torus F)) ∣ 2 :=
    card_dvd_of_forall_pow_eq_one _ fun b hb => Subtype.ext (by
      rw [SubgroupClass.coe_pow]
      exact hsq b (mem_subgroupOf.mp hb))
  have hcardAU : Nat.card (A ⊓ torus F : Subgroup (PGL2 F)) ≤ 2 := by
    rw [← Nat.card_congr (subgroupOfEquivOfLe inf_le_right).toEquiv]
    exact Nat.le_of_dvd (by norm_num) hAU2
  have hrel : (torus F).relIndex A ≤ 2 := by
    have hrelM : (torus F).relIndex (torus F ⊔ zpowers w) = 2 := by
      have := relIndex_mul_card (torus F) (torus F ⊔ zpowers w)
      rw [inf_eq_left.mpr le_sup_left, hMcard] at this
      have hpos : 0 < Nat.card (torus F) := Nat.card_pos
      nlinarith
    calc (torus F).relIndex A ≤ (torus F).relIndex (torus F ⊔ zpowers w) :=
          relIndex_le_of_le_right hAM (by rw [hrelM]; norm_num)
      _ = 2 := hrelM
  have hmul := relIndex_mul_card (torus F) A
  rw [inf_comm] at hmul
  rw [← hmul]
  calc (torus F).relIndex A * Nat.card (A ⊓ torus F : Subgroup (PGL2 F)) ≤ 2 * 2 :=
        Nat.mul_le_mul hrel hcardAU
    _ = 4 := by norm_num

theorem card_le_four_of_not_isCyclic (hF : IsOddPrimePower (Nat.card F))
    (hF4 : Nat.card F % 4 = 1) {B : Subgroup (PGL2 F)} (hB2 : IsPGroup 2 B)
    (hB : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (hncyc : ¬ IsCyclic B) : Nat.card B ≤ 4 := by
  obtain ⟨w, hUc, hwU, hww, hinv, hMcard, hconj⟩ := exists_conj_mem_sup hF hF4
  obtain ⟨n, hn⟩ := hconj B hB2
  set e := MulAut.conj n with he
  have hAM : B.map e.toMonoidHom ≤ torus F ⊔ zpowers w := by
    rintro _ ⟨x, hx, rfl⟩
    exact hn x hx
  have hcard : Nat.card (B.map e.toMonoidHom) = Nat.card B :=
    card_map_of_injective e.injective
  have hA : ∀ a ∈ B.map e.toMonoidHom, ∀ b ∈ B.map e.toMonoidHom, a * b = b * a := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hB x hx y hy]
  have hncyc' : ¬ IsCyclic (B.map e.toMonoidHom) := by
    intro hc
    exact hncyc ((Subgroup.equivMapOfInjective B e.toMonoidHom e.injective).isCyclic.mpr hc)
  rw [← hcard]
  exact card_le_four_of_le_sup hUc hwU hww hinv hMcard hAM hA hncyc'

omit [Finite F] in
theorem eq_or_eq_inv_of_conj {g : PGL2 F} {α β : Fˣ}
    (h : g * pGammaL2FullSplitTorus F α * g⁻¹ = pGammaL2FullSplitTorus F β) :
    α = β ∨ α = β⁻¹ := by
  obtain ⟨G', rfl⟩ := ProjGenLinGroup.mk_surjective g
  change ProjGenLinGroup.mk G' * ProjGenLinGroup.mk (pGammaL2FullSplitTorusGL F α) *
      (ProjGenLinGroup.mk G')⁻¹ = ProjGenLinGroup.mk (pGammaL2FullSplitTorusGL F β) at h
  rw [← map_inv, ← map_mul, ← map_mul, ProjGenLinGroup.mk_eq_mk_iff] at h
  obtain ⟨u, hu⟩ := h
  have key := congrArg (fun A : GL (Fin 2) F => (A : Matrix (Fin 2) (Fin 2) F)) hu
  simp only [Units.val_mul, GeneralLinearGroup.coe_scalar] at key
  set A := (G' : Matrix (Fin 2) (Fin 2) F) with hA
  set Ai := ((G'⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) with hAi
  have hAAi : Ai * A = 1 := by rw [hA, hAi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hD : ∀ γ : Fˣ, ((pGammaL2FullSplitTorusGL F γ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      Matrix.diagonal ![(γ : F), 1] := fun γ => rfl
  rw [hD, hD, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul,
    Matrix.mul_one] at key
  have hdet := congrArg Matrix.det key
  have htr := congrArg Matrix.trace key
  rw [Matrix.det_smul, Matrix.det_mul, Matrix.det_mul, Fintype.card_fin, Matrix.det_diagonal,
    Matrix.det_diagonal, Fin.prod_univ_two, Fin.prod_univ_two] at hdet
  have hdA : A.det * Ai.det = 1 := by rw [← Matrix.det_mul, ← Matrix.det_one (n := Fin 2) (R := F),
    ← hAAi, Matrix.det_mul, Matrix.det_mul, mul_comm]
  rw [Matrix.trace_smul, Matrix.trace_mul_cycle, hAAi, Matrix.one_mul, Matrix.trace_diagonal,
    Matrix.trace_diagonal, Fin.sum_univ_two, Fin.sum_univ_two] at htr
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_one, smul_eq_mul] at hdet htr
  have hdet' : (u : F) ^ 2 * (α : F) = (β : F) := by
    rw [← hdet, mul_right_comm A.det, hdA, one_mul]
  have hfac : ((u : F) - 1) * ((u : F) * α - 1) = 0 := by
    linear_combination hdet' - htr
  rcases mul_eq_zero.mp hfac with h1 | h1
  · left
    apply Units.ext
    rw [← hdet', show (u : F) = 1 by linear_combination h1, one_pow, one_mul]
  · right
    apply Units.ext
    have hβ : (β : F) = u := by rw [← hdet']; linear_combination (u : F) * h1
    rw [Units.val_inv_eq_inv_val, hβ]
    exact eq_inv_of_mul_eq_one_left (by linear_combination h1)

end L2Cyc

end CFSG.ComponentClassification.CatFactsL4U4
