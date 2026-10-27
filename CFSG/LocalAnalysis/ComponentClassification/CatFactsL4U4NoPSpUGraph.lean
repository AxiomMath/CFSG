module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4NoPSpUInner
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherConjDescent
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAntiunitaryTransport
public import CFSG.GroupTheory.WeirSylow.OrthogonalOrders

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace StabU

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  UnitaryOut UnitaryConj HBlocks ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank
  CFSG.LinearGroups

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

include h in
theorem card_eqLocus_le (hp2 : p ≠ 2) (hq : p ^ f % 4 = 1)
    (ψ : unitarySU p f K 4 →* unitarySU p f K 4) {α : MulAut (StatedProj (StatedSU 4 (p ^ f) K))}
    (hψ : ∀ g, (QuotientGroup.mk (ψ g) : StatedProj (StatedSU 4 (p ^ f) K)) =
      α (QuotientGroup.mk g)) :
    Nat.card ((α : StatedProj (StatedSU 4 (p ^ f) K) →* StatedProj (StatedSU 4 (p ^ f) K)).eqLocus
      (MonoidHom.id _)) ≤ Nat.card (ψ.eqLocus (MonoidHom.id _)) := by
  classical
  have : Finite K := h.finite
  have h2K : (2 : K) ≠ 0 := two_ne_zero_of_odd h hp2
  set θ : unitarySU p f K 4 →* StatedProj (StatedSU 4 (p ^ f) K) :=
    QuotientGroup.mk' (scal p f K) with hθdef
  obtain ⟨Fx, hFx⟩ : ∃ Fx : Subgroup (StatedProj (StatedSU 4 (p ^ f) K)),
      Fx = (α : StatedProj (StatedSU 4 (p ^ f) K) →* StatedProj (StatedSU 4 (p ^ f) K)).eqLocus
        (MonoidHom.id _) := ⟨_, rfl⟩
  rw [← hFx]
  obtain ⟨F₁, hF₁⟩ : ∃ F₁ : Subgroup (unitarySU p f K 4), F₁ = Fx.comap θ := ⟨_, rfl⟩
  have hmemF : ∀ g, g ∈ F₁ ↔ (QuotientGroup.mk (ψ g) : StatedProj (StatedSU 4 (p ^ f) K)) =
      QuotientGroup.mk g := by
    intro g
    rw [hF₁, Subgroup.mem_comap, hFx]
    change α (QuotientGroup.mk g) = QuotientGroup.mk g ↔ _
    rw [← hψ]
  have hstep1 : 2 * Nat.card Fx ≤ Nat.card F₁ := by
    set φ := θ.comp F₁.subtype with hφ
    have hrange : φ.range = Fx := by
      rw [hφ, MonoidHom.range_comp, Subgroup.range_subtype, hF₁,
        Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]
    have hnegF : negOne h ∈ F₁ := by
      rw [hF₁, Subgroup.mem_comap, hθdef, QuotientGroup.mk'_apply,
        (QuotientGroup.eq_one_iff _).2 (negOne_mem_scal h)]
      exact one_mem _
    have hker : 2 ≤ Nat.card φ.ker := by
      have : 1 < Nat.card φ.ker := by
        rw [Subgroup.one_lt_card_iff_ne_bot]
        intro hbot
        have hmem : (⟨negOne h, hnegF⟩ : F₁) ∈ φ.ker := by
          rw [MonoidHom.mem_ker, hφ, MonoidHom.comp_apply, Subgroup.coe_subtype, hθdef,
            QuotientGroup.mk'_apply]
          exact (QuotientGroup.eq_one_iff _).2 (negOne_mem_scal h)
        rw [hbot, Subgroup.mem_bot] at hmem
        exact negOne_ne_one h h2K (congrArg Subtype.val hmem)
      omega
    have hmul := Subgroup.card_ker_mul_card_range φ
    rw [hrange] at hmul
    calc 2 * Nat.card Fx ≤ Nat.card φ.ker * Nat.card Fx := Nat.mul_le_mul_right _ hker
      _ = Nat.card F₁ := hmul
  have hscal : ∀ g ∈ F₁, ψ g * g⁻¹ ∈ scal p f K := by
    intro g hg
    rw [hmemF] at hg
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, hg, QuotientGroup.mk_inv,
      mul_inv_cancel]
  let χ : F₁ →* unitarySU p f K 4 :=
    { toFun := fun g => ψ g.1 * g.1⁻¹
      map_one' := by
        change ψ 1 * 1⁻¹ = 1
        rw [map_one, inv_one, mul_one]
      map_mul' := fun g g' => by
        change ψ (g.1 * g'.1) * (g.1 * g'.1)⁻¹ = ψ g.1 * g.1⁻¹ * (ψ g'.1 * g'.1⁻¹)
        have hc := Subgroup.mem_center_iff.mp (mem_center_of_mem_scal (hscal g'.1 g'.2))
        calc ψ (g.1 * g'.1) * (g.1 * g'.1)⁻¹ = ψ g.1 * (ψ g'.1 * g'.1⁻¹) * g.1⁻¹ := by
              rw [map_mul]
              group
          _ = ψ g.1 * (g.1⁻¹ * (ψ g'.1 * g'.1⁻¹)) := by
              rw [mul_assoc, ← hc g.1⁻¹]
          _ = ψ g.1 * g.1⁻¹ * (ψ g'.1 * g'.1⁻¹) := by group }
  have hstep2 : Nat.card F₁ ≤ 2 * Nat.card (ψ.eqLocus (MonoidHom.id _)) := by
    have hmul := Subgroup.card_ker_mul_card_range χ
    have hrange : Nat.card χ.range ≤ 2 := by
      have hle : χ.range ≤ scal p f K := by
        rintro _ ⟨g, rfl⟩
        exact hscal g.1 g.2
      exact (Subgroup.card_le_of_le hle).trans (card_scal_le h hq)
    have hkerC : Nat.card χ.ker ≤ Nat.card (ψ.eqLocus (MonoidHom.id _)) := by
      let ι : χ.ker → ψ.eqLocus (MonoidHom.id _) := fun g => ⟨g.1.1, by
        have hg := g.2
        rw [MonoidHom.mem_ker] at hg
        change ψ g.1.1 * g.1.1⁻¹ = 1 at hg
        show ψ g.1.1 = g.1.1
        exact mul_inv_eq_one.1 hg⟩
      refine Nat.card_le_card_of_injective ι fun a b hab => ?_
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : ψ.eqLocus (MonoidHom.id _) => (z : unitarySU p f K 4)) hab
    calc Nat.card F₁ = Nat.card χ.ker * Nat.card χ.range := hmul.symm
      _ ≤ Nat.card (ψ.eqLocus (MonoidHom.id _)) * 2 := Nat.mul_le_mul hkerC hrange
      _ = 2 * Nat.card (ψ.eqLocus (MonoidHom.id _)) := by ring
  omega

theorem antiunitaryMap_bijective (A : GL (Fin 4) K) :
    Function.Bijective (antiunitaryMap h (A : Matrix (Fin 4) (Fin 4) K)) := by
  have hAi : (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hAi' : (A : Matrix (Fin 4) (Fin 4) K) * (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  constructor
  · intro v w hvw
    rw [antiunitaryMap_apply, antiunitaryMap_apply] at hvw
    have e := congrArg (fun x => (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) *ᵥ x) hvw
    simp only [Matrix.mulVec_mulVec, hAi, Matrix.one_mulVec] at e
    funext i
    exact (RingHom.injective h.bar) (congrFun e i)
  · intro w
    refine ⟨fun i => h.bar (((↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) *ᵥ w) i), ?_⟩
    rw [antiunitaryMap_apply]
    simp only [h.bar_bar]
    change (A : Matrix (Fin 4) (Fin 4) K) *ᵥ ((↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) *ᵥ w) = w
    rw [Matrix.mulVec_mulVec, hAi', Matrix.one_mulVec]

theorem stdHermForm_antiunitaryMap {A : GL (Fin 4) K}
    (hAu : uStar h (A : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K) = 1)
    (v w : Fin 4 → K) :
    stdHermForm h 4 (antiunitaryMap h (A : Matrix (Fin 4) (Fin 4) K) v)
      (antiunitaryMap h (A : Matrix (Fin 4) (Fin 4) K) w) = h.bar (stdHermForm h 4 v w) := by
  rw [antiunitaryMap_apply, antiunitaryMap_apply, stdHermForm_eq_gramForm, gramForm_mulVec,
    Matrix.mul_one]
  change gramForm h (uStar h (A : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K))
    _ _ = _
  rw [hAu, gramForm_apply, gramForm_apply]
  simp only [Matrix.one_mulVec, dotProduct, map_sum, map_mul, h.bar_bar]

theorem antiunitaryMap_sq (A : Matrix (Fin 4) (Fin 4) K) {c : K} (hc : A * A.map h.bar = c • 1)
    (v : Fin 4 → K) : antiunitaryMap h A (antiunitaryMap h A v) = c • v := by
  rw [antiunitaryMap_apply, antiunitaryMap_apply]
  have e : (fun i => h.bar ((A *ᵥ fun i => h.bar (v i)) i)) = A.map h.bar *ᵥ v := by
    funext i
    simp [Matrix.mulVec, dotProduct, map_sum, map_mul, h.bar_bar]
  rw [e, Matrix.mulVec_mulVec, hc, Matrix.smul_mulVec, Matrix.one_mulVec]

include h in
theorem symm_or_alt_of_graph (hp2 : p ≠ 2) (hq : p ^ f % 4 = 1) {A : GL (Fin 4) K}
    (hAu : uStar h (A : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K) = 1)
    (hcomm : ∀ g : unitarySU p f K 4,
      (A : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K).map h.bar *
        ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
        ((A : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K).map h.bar)) :
    ∃ ε : K, (ε = 1 ∨ ε = -1) ∧
      (A : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K).map h.bar = ε • 1 ∧
      (A : Matrix (Fin 4) (Fin 4) K)ᵀ = ε • (A : Matrix (Fin 4) (Fin 4) K) := by
  obtain ⟨c, hc⟩ := eq_smul_one_of_comm h hp2 hq hcomm
  have h1 : ((A : Matrix (Fin 4) (Fin 4) K).map h.bar)ᵀ * (A : Matrix (Fin 4) (Fin 4) K) = 1 := hAu
  have h2 : (A : Matrix (Fin 4) (Fin 4) K)ᵀ * (A : Matrix (Fin 4) (Fin 4) K).map h.bar = 1 := by
    have := congrArg Matrix.transpose h1
    rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at this
  have h3 : (A : Matrix (Fin 4) (Fin 4) K).map h.bar * (A : Matrix (Fin 4) (Fin 4) K)ᵀ = 1 :=
    mul_eq_one_comm.1 h2
  have hAc : (A : Matrix (Fin 4) (Fin 4) K) = c • (A : Matrix (Fin 4) (Fin 4) K)ᵀ := by
    calc (A : Matrix (Fin 4) (Fin 4) K) = (A : Matrix (Fin 4) (Fin 4) K) *
          ((A : Matrix (Fin 4) (Fin 4) K).map h.bar * (A : Matrix (Fin 4) (Fin 4) K)ᵀ) := by
          rw [h3, Matrix.mul_one]
      _ = c • (A : Matrix (Fin 4) (Fin 4) K)ᵀ := by
          rw [← Matrix.mul_assoc, hc, Matrix.smul_mul, Matrix.one_mul]
  have hAt : (A : Matrix (Fin 4) (Fin 4) K)ᵀ = c • (A : Matrix (Fin 4) (Fin 4) K) := by
    conv_lhs => rw [hAc]
    rw [Matrix.transpose_smul, Matrix.transpose_transpose]
  have hcc : c * c = 1 := by
    have e : (A : Matrix (Fin 4) (Fin 4) K) = (c * c) • (A : Matrix (Fin 4) (Fin 4) K) := by
      conv_lhs => rw [hAc, hAt]
      rw [smul_smul]
    have hdet : (A : Matrix (Fin 4) (Fin 4) K).det ≠ 0 := by
      rw [← GeneralLinearGroup.val_det_apply]
      exact Units.ne_zero _
    have hne : (A : Matrix (Fin 4) (Fin 4) K) ≠ 0 := fun h0 => hdet (by rw [h0, det_zero])
    obtain ⟨i, j, hij⟩ : ∃ i j, (A : Matrix (Fin 4) (Fin 4) K) i j ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hne (Matrix.ext hall)
    have e5 := congrFun (congrFun e i) j
    rw [Matrix.smul_apply, smul_eq_mul] at e5
    have e6 : (c * c - 1) * (A : Matrix (Fin 4) (Fin 4) K) i j = 0 := by linear_combination -e5
    exact sub_eq_zero.1 ((mul_eq_zero.1 e6).resolve_right hij)
  refine ⟨c, ?_, hc, hAt⟩
  rcases mul_self_eq_one_iff.1 hcc with h4 | h4
  · exact Or.inl h4
  · exact Or.inr h4

theorem bar_mulVec (M : Matrix (Fin 4) (Fin 4) K) (v : Fin 4 → K) :
    (fun i => h.bar ((M *ᵥ v) i)) = M.map h.bar *ᵥ fun i => h.bar (v i) := by
  funext i
  simp [Matrix.mulVec, dotProduct, map_sum, map_mul]

theorem card_eqLocus_le_commutingUnitary {A : GL (Fin 4) K}
    (ψ : unitarySU p f K 4 →* unitarySU p f K 4)
    (hψv : ∀ g, ((ψ g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      (A : Matrix (Fin 4) (Fin 4) K) * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map h.bar *
        (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K)) :
    Nat.card (ψ.eqLocus (MonoidHom.id _)) ≤
      Nat.card (commutingUnitary (stdHermForm h 4)
        (antiunitaryMap h (A : Matrix (Fin 4) (Fin 4) K))) := by
  classical
  have : Finite K := h.finite
  have : Finite (LinearMap.GeneralLinearGroup K (Fin 4 → K)) := finite_generalLinearGroup'
  have hAi : (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  let ι : ψ.eqLocus (MonoidHom.id _) →
      commutingUnitary (stdHermForm h 4) (antiunitaryMap h (A : Matrix (Fin 4) (Fin 4) K)) :=
    fun g => ⟨(toSesq h 4 g.1 : LinearMap.GeneralLinearGroup K (Fin 4 → K)), (toSesq h 4 g.1).2,
      fun v => by
        have hg : ψ g.1 = g.1 := g.2
        have hgA : ((g.1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * A =
            (A : Matrix (Fin 4) (Fin 4) K) *
              ((g.1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map h.bar := by
          have e := hψv g.1
          rw [hg] at e
          conv_lhs => rw [e]
          simp only [Matrix.mul_assoc]
          rw [hAi, Matrix.mul_one]
        change ((g.1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ
            antiunitaryMap h (A : Matrix (Fin 4) (Fin 4) K) v =
          antiunitaryMap h (A : Matrix (Fin 4) (Fin 4) K)
            (((g.1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ v)
        rw [antiunitaryMap_apply, antiunitaryMap_apply, bar_mulVec, Matrix.mulVec_mulVec, hgA,
          ← Matrix.mulVec_mulVec]⟩
  refine Nat.card_le_card_of_injective ι fun a b hab => ?_
  apply Subtype.ext
  apply toSesq_injective h 4
  apply Subtype.ext
  exact congrArg (fun z : commutingUnitary (stdHermForm h 4)
    (antiunitaryMap h (A : Matrix (Fin 4) (Fin 4) K)) =>
      (z : LinearMap.GeneralLinearGroup K (Fin 4 → K))) hab

theorem false_of_card_le_orth {q a o : ℕ} (hq5 : 5 ≤ q)
    (hcard : 2 * a = q ^ 4 * (q ^ 2 - 1) * (q ^ 4 - 1)) (hao : a ≤ o)
    (ho : (o : ℤ) ≤ 2 * (q : ℤ) ^ 2 * ((q : ℤ) ^ 2 + 1) * ((q : ℤ) ^ 2 - 1)) : False := by
  have h4 : 1 ≤ q ^ 4 := Nat.one_le_pow _ _ (by omega)
  have h2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  zify [h4, h2] at hcard
  have hao' : (a : ℤ) ≤ o := by exact_mod_cast hao
  have hq5' : (5 : ℤ) ≤ q := by exact_mod_cast hq5
  have hA : (0 : ℤ) < (q : ℤ) ^ 2 - 1 := by nlinarith
  have hB : (0 : ℤ) < (q : ℤ) ^ 2 + 1 := by positivity
  have hC : (0 : ℤ) < (q : ℤ) ^ 2 := by positivity
  have hD : (0 : ℤ) < (q : ℤ) ^ 2 * ((q : ℤ) ^ 2 - 1) - 4 := by nlinarith
  have hP := mul_pos (mul_pos (mul_pos hC hA) hB) hD
  have key : (q : ℤ) ^ 4 * ((q : ℤ) ^ 2 - 1) * ((q : ℤ) ^ 4 - 1) -
      2 * (2 * (q : ℤ) ^ 2 * ((q : ℤ) ^ 2 + 1) * ((q : ℤ) ^ 2 - 1)) =
      (q : ℤ) ^ 2 * ((q : ℤ) ^ 2 - 1) * ((q : ℤ) ^ 2 + 1) *
        ((q : ℤ) ^ 2 * ((q : ℤ) ^ 2 - 1) - 4) := by
    ring
  linarith

include h in
theorem false_of_graph_symm (hp2 : p ≠ 2) (hq : p ^ f % 4 = 1) {A : GL (Fin 4) K}
    (hAu : uStar h (A : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K) = 1)
    (hAA : (A : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K).map h.bar = 1)
    (ψ : unitarySU p f K 4 →* unitarySU p f K 4)
    (hψv : ∀ g, ((ψ g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      (A : Matrix (Fin 4) (Fin 4) K) * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map h.bar *
        (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K))
    {α : MulAut (StatedProj (StatedSU 4 (p ^ f) K))}
    (hψ : ∀ g, (QuotientGroup.mk (ψ g) : StatedProj (StatedSU 4 (p ^ f) K)) =
      α (QuotientGroup.mk g))
    {M : Subgroup (StatedProj (StatedSU 4 (p ^ f) K))} (hM : ∀ x ∈ M, α x = x)
    (hcard : 2 * Nat.card M = (p ^ f) ^ 4 * ((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 4 - 1)) : False := by
  classical
  have : Finite K := h.finite
  have h2K : (2 : K) ≠ 0 := two_ne_zero_of_odd h hp2
  set τ₀ := antiunitaryMap h (A : Matrix (Fin 4) (Fin 4) K) with hτ₀
  have hμ : ∀ v, τ₀ (τ₀ v) = ((1 : Kˣ) : K) • v := fun v => by
    rw [Units.val_one]
    exact antiunitaryMap_sq h _ (by rw [hAA, one_smul]) v
  obtain ⟨-, -, ⟨t, ht⟩, hmain⟩ := odd_unitary_conjugate_semilinear_involution_descent h
    (h.prime.odd_of_ne_two hp2) (by rw [Module.finrank_fin_fun]; norm_num)
    (stdHermForm_isSymm h 4) (stdHermForm_separatingLeft h 4) τ₀ (antiunitaryMap_bijective h A)
    (stdHermForm_antiunitaryMap h hAu) 1 hμ
  obtain ⟨-, hfinW, -, hsymm, -⟩ := hmain 1 t
    (by rw [UnitaryFieldData.norm, Units.val_one, map_one, mul_one, inv_one, Units.val_one]) ht
  obtain ⟨B, -, hBs, hBnd, Φ, -⟩ := hsymm rfl
  have : Module.Finite h.fixedField (conjFixed h (((1 : Kˣ) : K) • τ₀)) := finite_conjFixed
  set Q := LinearMap.BilinMap.toQuadraticMap B with hQ
  have hle : TauCeti.BilinForm.isometryGroup B ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
    intro e he
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro x
    rw [TauCeti.BilinForm.mem_isometryGroup_iff] at he
    rw [hQ, LinearMap.BilinMap.toQuadraticMap_apply, LinearMap.BilinMap.toQuadraticMap_apply, he]
  have hc1 := card_eqLocus_le h hp2 hq ψ hψ
  have hc2 := card_eqLocus_le_commutingUnitary h ψ hψv
  have hc3 : Nat.card (commutingUnitary (stdHermForm h 4) τ₀) =
      Nat.card (TauCeti.BilinForm.isometryGroup B) := Nat.card_congr Φ.toEquiv
  have : Finite (conjFixed h (((1 : Kˣ) : K) • τ₀)) := Module.finite_of_finite h.fixedField
  have : Finite (conjFixed h (((1 : Kˣ) : K) • τ₀) ≃ₗ[h.fixedField]
      conjFixed h (((1 : Kˣ) : K) • τ₀)) :=
    Finite.of_injective (fun e => (e : conjFixed h (((1 : Kˣ) : K) • τ₀) →
      conjFixed h (((1 : Kˣ) : K) • τ₀))) fun a b hab => LinearEquiv.ext (congrFun hab)
  have hc4 := Subgroup.card_le_of_le hle
  have hMle : M ≤ (α : StatedProj (StatedSU 4 (p ^ f) K) →*
      StatedProj (StatedSU 4 (p ^ f) K)).eqLocus (MonoidHom.id _) := fun x hx => hM x hx
  have hc0 := Subgroup.card_le_of_le hMle
  have hnd : (QuadraticMap.polarBilin Q).Nondegenerate := by
    have e : ∀ x y, QuadraticMap.polarBilin Q x y = 2 * B x y := by
      intro x y
      rw [hQ, LinearMap.BilinMap.polarBilin_toQuadraticMap, LinearMap.add_apply,
        LinearMap.add_apply, LinearMap.flip_apply, hBs.eq y x]
      ring
    have h2F : (2 : h.fixedField) ≠ 0 := by
      intro h0
      apply h2K
      have e1 : ((2 : h.fixedField) : K) = 2 := by
        rw [show (2 : h.fixedField) = 1 + 1 from one_add_one_eq_two.symm, Subfield.coe_add,
          Subfield.coe_one, one_add_one_eq_two]
      rw [← e1, h0]
      rfl
    refine ⟨fun x hx => hBnd.1 x fun y => ?_, fun y hy => hBnd.2 y fun x => ?_⟩
    · have := hx y
      rw [e] at this
      exact (mul_eq_zero.1 this).resolve_left h2F
    · have := hy x
      rw [e] at this
      exact (mul_eq_zero.1 this).resolve_left h2F
  have hdim : Module.finrank h.fixedField (conjFixed h (((1 : Kˣ) : K) • τ₀)) = 2 * (1 + 1) := by
    rw [hfinW, Module.finrank_fin_fun]
  have hFq : Nat.card h.fixedField = p ^ f := h.card_fixedField
  have hO : (Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) : ℤ) ≤
      2 * ((p ^ f : ℕ) : ℤ) ^ 2 * (((p ^ f : ℕ) : ℤ) ^ 2 + 1) * (((p ^ f : ℕ) : ℤ) ^ 2 - 1) := by
    have hq0 : (1 : ℤ) ≤ ((p ^ f : ℕ) : ℤ) ^ 2 := by
      have : 1 ≤ (p ^ f) ^ 2 := Nat.one_le_pow _ _ (pow_pos h.prime.pos f)
      exact_mod_cast this
    by_cases hp : CFSG.GroupTheory.WeirSylow.IsPlusType Q
    · rw [CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type hnd hdim (Or.inl ⟨rfl, hp⟩)]
      simp only [Finset.Icc_self, Finset.prod_singleton, hFq]
      norm_num
      push_cast at hq0
      have hx : (0 : ℤ) ≤ 4 * ((p : ℤ) ^ f) ^ 2 * (((p : ℤ) ^ f) ^ 2 - 1) :=
        mul_nonneg (by positivity) (by linarith)
      nlinarith [hx]
    · rw [CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type hnd hdim (Or.inr ⟨rfl, hp⟩)]
      simp only [Finset.Icc_self, Finset.prod_singleton, hFq, sub_neg_eq_add]
      norm_num
  have hq5 : 5 ≤ p ^ f := by
    have hp3 : 3 ≤ p := by have := h.prime.two_le; omega
    have : p ≤ p ^ f := Nat.le_self_pow (by have := h.one_le; omega) p
    omega
  have hchain := hc0.trans (hc1.trans (hc2.trans (hc3.le.trans hc4)))
  obtain ⟨a, ha⟩ : ∃ a, a = Nat.card M := ⟨_, rfl⟩
  obtain ⟨o, ho⟩ : ∃ o, o = Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) := ⟨_, rfl⟩
  rw [← ha, ← ho] at hchain
  rw [← ha] at hcard
  rw [← ho] at hO
  generalize p ^ f = q at hcard hO hq5
  exact false_of_card_le_orth hq5 hcard hchain hO

end StabU

end CFSG.ComponentClassification.CatFactsL4U4
