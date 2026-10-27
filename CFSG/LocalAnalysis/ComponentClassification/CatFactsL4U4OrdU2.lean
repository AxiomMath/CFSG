module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OrdU
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4HBlocks3
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4TypeU4

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace StabU

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  UnitaryOut UnitaryConj HBlocks ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

include h in
theorem det_cP (P : GL (Fin 4) K) (g : unitarySU p f K 4) : (cP P g).det = 1 := by
  have hg := ((mem_unitarySU_iff h).1 g.2).1
  rw [cP, det_mul, det_mul, hg, mul_one, ← det_mul, ← Units.val_mul, inv_mul_cancel,
    Units.val_one, det_one]

@[expose] noncomputable def negOne : unitarySU p f K 4 :=
  ⟨-1, neg_one_mem_statedSU_four h⟩

include h in
theorem negOne_mem_scal : negOne h ∈ scal p f K := by
  show ((negOne h : unitarySU p f K 4) : GL (Fin 4) K) ∈ StatedScalars (Fin 4) K
  exact ⟨-1, scalar_neg_one_eq 4⟩

theorem negOne_ne_one (h2 : (2 : K) ≠ 0) : negOne h ≠ 1 := by
  intro h1
  have := congrFun (congrFun (congrArg (fun g : unitarySU p f K 4 =>
    ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) h1) 0) 0
  simp only [negOne, Units.val_neg, Units.val_one, Matrix.neg_apply, Matrix.one_apply_eq,
    OneMemClass.coe_one] at this
  exact h2 (by linear_combination -this)

include h in
theorem card_scal_le (hq : p ^ f % 4 = 1) : Nat.card (scal p f K) ≤ 2 := by
  classical
  have hsub : ((scal p f K : Subgroup (unitarySU p f K 4)) : Set (unitarySU p f K 4)) ⊆
      {1, negOne h} := by
    intro z hz
    have hz' : (z : GL (Fin 4) K) ∈ StatedScalars (Fin 4) K := hz
    obtain ⟨c, hc⟩ := hz'
    have hcSU : GeneralLinearGroup.scalar (Fin 4) c ∈ StatedSU 4 (p ^ f) K := by
      rw [hc]
      exact z.2
    rcases scalar_eq_one_or_neg_one_U4 h hq hcSU with rfl | rfl
    · left
      apply Subtype.ext
      rw [← hc, map_one]
      rfl
    · right
      apply Subtype.ext
      rw [← hc, scalar_neg_one_eq]
      rfl
  calc Nat.card (scal p f K) = Nat.card ((scal p f K : Subgroup (unitarySU p f K 4)) :
        Set (unitarySU p f K 4)) := rfl
    _ ≤ Nat.card ({1, negOne h} : Set (unitarySU p f K 4)) :=
        Nat.card_mono (Set.toFinite _) hsub
    _ ≤ 2 := by
        rw [Nat.card_coe_set_eq]
        exact (Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton])

include h in
theorem card_centralizer_le_U4 (hp2 : p ≠ 2) (hq : p ^ f % 4 = 1) (P : GL (Fin 4) K)
    (hP : uStar h (P : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) = stdG)
    {l : K} (hl : l ^ 2 = -1) (hbl : h.bar l * l = -1) :
    Nat.card (Subgroup.centralizer {(QuotientGroup.mk (hypSU h P hP (X1 l) (unitary_X1 h hbl)
      (det_X1 hl)) : StatedProj (StatedSU 4 (p ^ f) K))}) ≤
      (p ^ f) ^ 2 * ((p ^ f) ^ 4 - 1) * (p ^ f - 1) := by
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
  obtain ⟨Z₀, hZ₀⟩ : ∃ Z₀ : Subgroup (StatedProj (StatedSU 4 (p ^ f) K)),
      Z₀ = Subgroup.centralizer {θ X} := ⟨_, rfl⟩
  show Nat.card (Subgroup.centralizer {θ X}) ≤ _
  rw [← hZ₀]
  obtain ⟨F₁, hF₁⟩ : ∃ F₁ : Subgroup (unitarySU p f K 4), F₁ = Z₀.comap θ := ⟨_, rfl⟩
  have hstep1 : 2 * Nat.card Z₀ ≤ Nat.card F₁ := by
    set ψ := θ.comp F₁.subtype with hψ
    have hrange : ψ.range = Z₀ := by
      rw [hψ, MonoidHom.range_comp, Subgroup.range_subtype, hF₁,
        Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]
    have hnegF : negOne h ∈ F₁ := by
      rw [hF₁, Subgroup.mem_comap, hθdef, QuotientGroup.mk'_apply,
        (QuotientGroup.eq_one_iff _).2 (negOne_mem_scal h)]
      exact one_mem _
    have hker : 2 ≤ Nat.card ψ.ker := by
      have : 1 < Nat.card ψ.ker := by
        rw [Subgroup.one_lt_card_iff_ne_bot]
        intro hbot
        have hmem : (⟨negOne h, hnegF⟩ : F₁) ∈ ψ.ker := by
          rw [MonoidHom.mem_ker, hψ, MonoidHom.comp_apply, Subgroup.coe_subtype, hθdef,
            QuotientGroup.mk'_apply]
          exact (QuotientGroup.eq_one_iff _).2 (negOne_mem_scal h)
        rw [hbot, Subgroup.mem_bot] at hmem
        exact negOne_ne_one h h2K (congrArg Subtype.val hmem)
      omega
    have hmul := Subgroup.card_ker_mul_card_range ψ
    rw [hrange] at hmul
    calc 2 * Nat.card Z₀ ≤ Nat.card ψ.ker * Nat.card Z₀ := Nat.mul_le_mul_right _ hker
      _ = Nat.card F₁ := hmul
  have hscen : ∀ g ∈ F₁, g * X * g⁻¹ * X⁻¹ ∈ scal p f K := by
    intro g hg
    rw [hF₁, Subgroup.mem_comap, hZ₀, Subgroup.mem_centralizer_singleton_iff] at hg
    have h1 : θ (g * X * g⁻¹ * X⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hg]
      group
    rwa [hθdef, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  let χ : F₁ →* unitarySU p f K 4 :=
    { toFun := fun g => g.1 * X * g.1⁻¹ * X⁻¹
      map_one' := by
        change (1 : unitarySU p f K 4) * X * 1⁻¹ * X⁻¹ = 1
        group
      map_mul' := fun g g' => by
        change g.1 * g'.1 * X * (g.1 * g'.1)⁻¹ * X⁻¹ =
          (g.1 * X * g.1⁻¹ * X⁻¹) * (g'.1 * X * g'.1⁻¹ * X⁻¹)
        have hc := mem_center_of_mem_scal (hscen g'.1 g'.2)
        have e : g'.1 * X * g'.1⁻¹ = (g'.1 * X * g'.1⁻¹ * X⁻¹) * X := by group
        calc g.1 * g'.1 * X * (g.1 * g'.1)⁻¹ * X⁻¹ =
            g.1 * (g'.1 * X * g'.1⁻¹) * g.1⁻¹ * X⁻¹ := by group
          _ = g.1 * ((g'.1 * X * g'.1⁻¹ * X⁻¹) * X) * g.1⁻¹ * X⁻¹ := by rw [← e]
          _ = (g'.1 * X * g'.1⁻¹ * X⁻¹) * (g.1 * X * g.1⁻¹ * X⁻¹) := by
              have hc' := Subgroup.mem_center_iff.mp hc g.1
              calc g.1 * ((g'.1 * X * g'.1⁻¹ * X⁻¹) * X) * g.1⁻¹ * X⁻¹ =
                  (g.1 * (g'.1 * X * g'.1⁻¹ * X⁻¹)) * X * g.1⁻¹ * X⁻¹ := by group
                _ = ((g'.1 * X * g'.1⁻¹ * X⁻¹) * g.1) * X * g.1⁻¹ * X⁻¹ := by rw [hc']
                _ = _ := by group
          _ = _ := (Subgroup.mem_center_iff.mp hc _).symm }
  have hstep2 : Nat.card F₁ ≤ 2 * Nat.card C := by
    have hmul := Subgroup.card_ker_mul_card_range χ
    have hrange : Nat.card χ.range ≤ 2 := by
      have hle : χ.range ≤ scal p f K := by
        rintro _ ⟨g, rfl⟩
        exact hscen g.1 g.2
      exact (Subgroup.card_le_of_le hle).trans (card_scal_le h hq)
    have hkerC : Nat.card χ.ker ≤ Nat.card C := by
      let ι : χ.ker → C := fun g => ⟨g.1.1, by
        have hg := g.2
        rw [MonoidHom.mem_ker] at hg
        change g.1.1 * X * g.1.1⁻¹ * X⁻¹ = 1 at hg
        rw [hC, Subgroup.mem_centralizer_singleton_iff]
        have : g.1.1 * X * g.1.1⁻¹ = X := by
          calc g.1.1 * X * g.1.1⁻¹ = g.1.1 * X * g.1.1⁻¹ * X⁻¹ * X := by group
            _ = X := by rw [hg, one_mul]
        calc g.1.1 * X = g.1.1 * X * g.1.1⁻¹ * g.1.1 := by group
          _ = X * g.1.1 := by rw [this]⟩
      refine Nat.card_le_card_of_injective ι fun a b hab => ?_
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : C => (z : unitarySU p f K 4)) hab
    calc Nat.card F₁ = Nat.card χ.ker * Nat.card χ.range := hmul.symm
      _ ≤ Nat.card C * 2 := Nat.mul_le_mul hkerC hrange
      _ = 2 * Nat.card C := by ring
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
  have hβ : ∀ g : C, β g = ul (cP P g.1) := fun g => rfl
  have hβinj : Function.Injective β := by
    intro g g' hgg
    have h1 : β (g⁻¹ * g') = 1 := by
      rw [map_mul, ← hgg, ← map_mul, inv_mul_cancel, map_one]
    rw [hβ] at h1
    have h2 := eq_one_of_ul_eq_one h (hBD _ (g⁻¹ * g').2) (unitary_cP h P hP _) h1
    have h3 : (g⁻¹ * g').1 = 1 := eq_of_cP_eq P (by rw [h2, cP_one])
    have h4 : g⁻¹ * g' = 1 := Subtype.ext h3
    rw [← inv_mul_eq_one, h4]
  let δ : C →* Kˣ := (Matrix.detMonoidHom.comp β).toHomUnits
  have hδ : ∀ g : C, ((δ g : Kˣ) : K) = (ul (cP P g.1)).det := fun g => rfl
  have hKcard : Nat.card K = (p ^ f) ^ 2 := by rw [h.card, ← pow_mul, mul_comm]
  have hq5 : 5 ≤ p ^ f := by
    have hp3 : 3 ≤ p := by have := h.prime.two_le; omega
    have : p ≤ p ^ f := Nat.le_self_pow (by have := h.one_le; omega) p
    omega
  have : NeZero (p ^ f - 1) := ⟨by omega⟩
  have hrangeδ : δ.range ≤ rootsOfUnity (p ^ f - 1) K := by
    rintro _ ⟨g, rfl⟩
    rw [mem_rootsOfUnity']
    have hfix := det_ul_fixed h (hBD g.1 g.2) (unitary_cP h P hP g.1) (det_cP h P g.1)
    rw [← hδ, UnitaryFieldData.bar_apply] at hfix
    have hu : ((δ g : Kˣ) : K) ≠ 0 := Units.ne_zero _
    have hq1 : 1 ≤ p ^ f := Nat.one_le_pow _ _ h.prime.pos
    have e : ((δ g : Kˣ) : K) ^ (p ^ f - 1) * (δ g : Kˣ) = 1 * (δ g : Kˣ) := by
      rw [← pow_succ, Nat.sub_add_cancel hq1, hfix, one_mul]
    exact mul_right_cancel₀ hu e
  have hkerδ : Nat.card δ.ker ≤ (p ^ f) ^ 2 * ((p ^ f) ^ 4 - 1) := by
    let F : δ.ker → SpecialLinearGroup (Fin 2) K := fun x =>
      ⟨β x.1, by
        have hx := x.2
        rw [MonoidHom.mem_ker] at hx
        have := congrArg Units.val hx
        simpa [δ] using this⟩
    have hF : Function.Injective F := by
      intro x y hxy
      have h1 : β x.1 = β y.1 := congrArg Subtype.val hxy
      exact Subtype.ext (hβinj h1)
    calc Nat.card δ.ker ≤ Nat.card (SpecialLinearGroup (Fin 2) K) :=
          Nat.card_le_card_of_injective F hF
      _ = Nat.card K * (Nat.card K ^ 2 - 1) := by
          let := Fintype.ofFinite K
          have hq : 1 < Fintype.card K := Fintype.one_lt_card
          rw [Matrix.card_SL_field, Fin.prod_univ_two, Fin.val_zero,
            Fin.val_one, pow_zero, pow_one, Nat.card_eq_fintype_card,
            show Fintype.card K ^ 2 - Fintype.card K =
              Fintype.card K * (Fintype.card K - 1) by rw [Nat.mul_sub_one, sq], ← mul_assoc,
            Nat.mul_div_cancel _ (by omega), mul_comm]
      _ = (p ^ f) ^ 2 * ((p ^ f) ^ 4 - 1) := by
          rw [hKcard, show ((p ^ f) ^ 2) ^ 2 = (p ^ f) ^ 4 by ring]
  have hstep3 : Nat.card C ≤ (p ^ f) ^ 2 * ((p ^ f) ^ 4 - 1) * (p ^ f - 1) := by
    have hmul := Subgroup.card_ker_mul_card_range δ
    have hr : Nat.card δ.range ≤ p ^ f - 1 :=
      (Subgroup.card_le_of_le hrangeδ).trans (card_rootsOfUnity _ _)
    calc Nat.card C = Nat.card δ.ker * Nat.card δ.range := hmul.symm
      _ ≤ _ := Nat.mul_le_mul hkerδ hr
  omega

end StabU

end CFSG.ComponentClassification.CatFactsL4U4
