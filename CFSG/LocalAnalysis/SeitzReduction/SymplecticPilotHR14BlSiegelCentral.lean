module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14BlModelToral

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open CFSG.SeitzReduction.UnitaryPilot (modelToG mem_modelToG)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open scoped MatrixGroups

section Toral

variable {K : Type} [Field K] {n j : ℕ}

@[expose] def spAUpperSL2 : SL(2, K) :=
  ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩

theorem spAPartnerHom_upper (hjn : 2 * j ≤ n) :
    spAPartnerHom K n hjn spAUpperSL2 = spARep n j := by
  apply mat_injective
  rw [mat_spAPartnerHom, spARep, mat_upperUnipotentSp, spAPartnerMat]
  simp [spAUpperSL2]

@[expose] def spADiagSL2 (κ : Kˣ) : SL(2, K) :=
  ⟨!![(κ : K), 0; 0, ((κ⁻¹ : Kˣ) : K)], by simp [Matrix.det_fin_two]⟩

@[expose] def spAUpperSL2Of (c : K) : SL(2, K) :=
  ⟨!![1, c; 0, 1], by simp [Matrix.det_fin_two]⟩

theorem spAUpper_mul_diag (κ : Kˣ) :
    spAUpperSL2 * spADiagSL2 κ =
      spAUpperSL2Of (1 - (κ : K) * κ) * (spADiagSL2 κ * spAUpperSL2) := by
  apply Subtype.ext
  have hκ : (κ : K) * ((κ⁻¹ : Kˣ) : K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  change (!![1, 1; 0, 1] * !![(κ : K), 0; 0, ((κ⁻¹ : Kˣ) : K)] : Matrix (Fin 2) (Fin 2) K) =
    !![1, 1 - (κ : K) * κ; 0, 1] * (!![(κ : K), 0; 0, ((κ⁻¹ : Kˣ) : K)] * !![1, 1; 0, 1])
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two, Matrix.mul_fin_two]
  have hκ0 : (κ : K) ≠ 0 := κ.ne_zero
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Units.val_inv_eq_inv_val]
  field_simp
  ring

theorem spAUpper_commutator_diag (κ : Kˣ) :
    spAUpperSL2 * spADiagSL2 κ * spAUpperSL2⁻¹ * (spADiagSL2 κ)⁻¹ =
      spAUpperSL2Of (1 - (κ : K) * κ) := by
  calc spAUpperSL2 * spADiagSL2 κ * spAUpperSL2⁻¹ * (spADiagSL2 κ)⁻¹ =
      spAUpperSL2Of (1 - (κ : K) * κ) * (spADiagSL2 κ * spAUpperSL2) * spAUpperSL2⁻¹ *
        (spADiagSL2 κ)⁻¹ := by rw [← spAUpper_mul_diag]
    _ = spAUpperSL2Of (1 - (κ : K) * κ) := by group

theorem spAUpperSL2Of_mul_self [CharP K 2] (c : K) :
    spAUpperSL2Of c * spAUpperSL2Of c = 1 := by
  apply Subtype.ext
  change (!![1, c; 0, 1] * !![1, c; 0, 1] : Matrix (Fin 2) (Fin 2) K) = 1
  rw [Matrix.mul_fin_two]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [CharTwo.add_self_eq_zero]

theorem orderOf_spAPartnerHom_upperOf [CharP K 2] (hj : 1 ≤ j) (hjn : 2 * j ≤ n) {c : K}
    (hc : c ≠ 0) : orderOf (spAPartnerHom K n hjn (spAUpperSL2Of c)) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply orderOf_eq_prime
  · rw [_root_.sq, ← map_mul, spAUpperSL2Of_mul_self, map_one]
  · intro h1
    have h2 := congrArg (fun x => mat n K x (Sum.inl ⟨0, by omega⟩) (Sum.inr ⟨1, by omega⟩)) h1
    simp only [mat_spAPartnerHom, spAPartnerMat, fromBlocks_apply₁₂, Matrix.smul_apply,
      smul_eq_mul, map_one] at h2
    rw [spARepMat_apply hjn] at h2
    have hpar : (⟨0, by omega⟩ : Fin n) = spAPar ⟨1, by omega⟩ := by
      apply Fin.ext
      rw [spAPar_val hjn (show (1 : ℕ) < 2 * j by omega)]
      simp
    rw [ite_eq_left ⟨show (1 : ℕ) < 2 * j by omega, hpar⟩] at h2
    simp [spAUpperSL2Of] at h2
    exact hc h2

theorem exists_orderOf_commutator_eq_two_of_odd_spARep [Finite K] [CharP K 2]
    (hK : 4 ≤ Nat.card K) (hj : 1 ≤ j) (hjn : 2 * j ≤ n) {S : Subgroup (StatedSp n K)}
    (hS : S ≤ centralizer ({spARep n j} : Set (StatedSp n K))) (hodd : Odd (Nat.card S)) :
    ∃ p : StatedSp n K, p ∈ centralizer (S : Set (StatedSp n K)) ∧
      orderOf (spARep n j * p * (spARep n j)⁻¹ * p⁻¹) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcop : Nat.Coprime 2 (Nat.card S) := Nat.coprime_two_left.2 hodd
  obtain ⟨u, hu, hle⟩ := F4Pilot.exists_mem_map_conj_le_of_le_sup (isPGroup_spARadical hjn)
    (range_spALeviHom_le_normalizer hjn) (spARadical_inf_range_eq_bot hjn)
    (hS.trans (centralizer_spARep_le_sup hjn)) hcop
  have hua : u * spARep n j = spARep n j * u :=
    mem_centralizer_singleton_iff.1 (spARadical_le_centralizer hjn hu)
  obtain ⟨κ, hκ⟩ := exists_units_mul_self_ne_one_of_four_le hK
  set p₀ := spAPartnerHom K n hjn (spADiagSL2 κ) with hp₀
  refine ⟨u⁻¹ * p₀ * u, ?_, ?_⟩
  · rw [mem_centralizer_iff]
    intro s hs
    have hus : u * s * u⁻¹ ∈ (spALeviHom hjn).range := hle ⟨s, hs, rfl⟩
    have hc := mem_centralizer_iff.1 (range_spALeviHom_le_centralizer_partner hjn hus) p₀
      ⟨_, rfl⟩
    calc s * (u⁻¹ * p₀ * u) = u⁻¹ * ((u * s * u⁻¹) * p₀) * u := by group
      _ = u⁻¹ * (p₀ * (u * s * u⁻¹)) * u := by rw [hc]
      _ = u⁻¹ * p₀ * u * s := by group
  · have hcomm : spARep n j * p₀ * (spARep n j)⁻¹ * p₀⁻¹ =
        spAPartnerHom K n hjn (spAUpperSL2Of (1 - (κ : K) * κ)) := by
      rw [← spAPartnerHom_upper (K := K) hjn, hp₀, ← map_inv, ← map_inv, ← map_mul, ← map_mul,
        ← map_mul, spAUpper_commutator_diag]
    have ha' : spARep n j = u⁻¹ * spARep n j * u := by
      rw [mul_assoc, ← hua, inv_mul_cancel_left]
    have hconj : spARep n j * (u⁻¹ * p₀ * u) * (spARep n j)⁻¹ * (u⁻¹ * p₀ * u)⁻¹ =
        u⁻¹ * (spARep n j * p₀ * (spARep n j)⁻¹ * p₀⁻¹) * u := by
      conv_lhs => rw [ha']
      group
    have hc0 : (1 : K) - (κ : K) * κ ≠ 0 := by
      intro h
      apply hκ
      apply Units.ext
      rw [Units.val_mul, Units.val_one]
      linear_combination -h
    rw [hconj, hcomm]
    have h1 := MulEquiv.orderOf_eq (MulAut.conj u⁻¹)
      (spAPartnerHom K n hjn (spAUpperSL2Of (1 - (κ : K) * κ)))
    simp only [MulAut.conj_apply, inv_inv] at h1
    rw [h1]
    exact orderOf_spAPartnerHom_upperOf hj hjn hc0

end Toral

section Properties

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2]

theorem spOmegaBShape_properties_central (hperf : SpACentralizerPerfectInput)
    (htor : SpAToralInput) (hK : 4 ≤ Nat.card K) {n j : ℕ} (e : L ≃* StatedSp n K)
    {θ α : MulAut (spGlobal e)} (h : SpOmegaBShape e θ α j) :
    ∃ (x₀ : spGlobal e) (η : MulAut (spGlobal e)), α = MulAut.conj x₀ * η ∧ η x₀ = x₀ ∧
      x₀ * x₀ = 1 ∧ (∃ z : spGlobal e, η = MulAut.conj z * θ * (MulAut.conj z)⁻¹) ∧
      fixedSubgroup α ≤ centralizer ({x₀} : Set (spGlobal e)) ∧
      ⁅fixedSubgroup α, fixedSubgroup α⁆ = fixedSubgroup α ∧
      Nat.card (fixedSubgroup α) = Nat.card (centralizer ({spARep n j} : Set (StatedSp n K))) ∧
      (∀ T : Subgroup (spGlobal e), T ≤ fixedSubgroup α → Odd (Nat.card T) →
        ∃ P : Subgroup (spGlobal e), P ≤ centralizer (T : Set (spGlobal e)) ∧ ⁅P, P⁆ = P ∧
          ¬ P ≤ centralizer ({x₀} : Set (spGlobal e))) ∧
      ∀ T : Subgroup (spGlobal e), T ≤ fixedSubgroup α → Odd (Nat.card T) →
        ∃ p : spGlobal e, p ∈ centralizer (T : Set (spGlobal e)) ∧ η p = p ∧
          orderOf (x₀ * p * x₀⁻¹ * p⁻¹) = 2 := by
  obtain ⟨hj, hjn, ψ, η, hψ, hα, hη, hfix, hz, huniq⟩ := h
  set a : StatedSp n K := spARep n j with ha
  set C := centralizer ({a} : Set (StatedSp n K)) with hC
  have hCle : C.map ψ ≤ centralizer ({ψ a} : Set (spGlobal e)) := by
    rintro _ ⟨c, hc, rfl⟩
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul, mem_centralizer_singleton_iff.1 hc]
  have haa : ψ a * ψ a = 1 := by rw [← map_mul, ha, spARep_mul_self, map_one]
  have hηa : η (ψ a) = ψ a := by
    have h1 : ψ a ∈ fixedSubgroup η := by
      rw [hη]
      exact ⟨a, rfl⟩
    exact h1
  have hTor : ∀ T : Subgroup (spGlobal e), T ≤ fixedSubgroup α → Odd (Nat.card T) →
      T.comap ψ ≤ C ∧ Odd (Nat.card (T.comap ψ)) ∧ (T.comap ψ).map ψ = T := by
    intro T hT hTodd
    rw [hfix] at hT
    have hT'map : (T.comap ψ).map ψ = T := by
      refine le_antisymm (Subgroup.map_comap_le _ _) fun y hy => ?_
      obtain ⟨c, -, rfl⟩ := hT hy
      exact ⟨c, hy, rfl⟩
    refine ⟨fun c hc => ?_, ?_, hT'map⟩
    · obtain ⟨c', hc', hcc'⟩ := hT hc
      rw [← hψ hcc']
      exact hc'
    · rw [← Subgroup.card_map_of_injective hψ, hT'map]
      exact hTodd
  refine ⟨ψ a, η, hα, hηa, haa, hz, hfix ▸ hCle, ?_, ?_, ?_, ?_⟩
  · rw [hfix, ← Subgroup.map_commutator, hC, hperf n j K hK hj hjn]
  · rw [hfix, Subgroup.card_map_of_injective hψ]
  · intro T hT hTodd
    obtain ⟨hT'C, hT'odd, hT'map⟩ := hTor T hT hTodd
    obtain ⟨P, hPT, hPperf, hPa⟩ := htor n j K hK hj hjn _ hT'C hT'odd
    refine ⟨P.map ψ, ?_, by rw [← Subgroup.map_commutator, hPperf], fun h => hPa ?_⟩
    · rintro _ ⟨y, hy, rfl⟩
      rw [mem_centralizer_iff]
      intro τ hτ
      obtain ⟨τ', hτ', rfl⟩ : ∃ τ' ∈ T.comap ψ, ψ τ' = τ := by
        rw [← hT'map] at hτ
        exact hτ
      rw [← map_mul, ← map_mul, mem_centralizer_iff.1 (hPT hy) τ' hτ']
    · intro y hy
      have h1 := mem_centralizer_singleton_iff.1 (h ⟨y, hy, rfl⟩)
      rw [← map_mul, ← map_mul] at h1
      exact mem_centralizer_singleton_iff.2 (hψ h1)
  · intro T hT hTodd
    obtain ⟨hT'C, hT'odd, hT'map⟩ := hTor T hT hTodd
    obtain ⟨p, hpT, hpord⟩ :=
      exists_orderOf_commutator_eq_two_of_odd_spARep hK hj hjn hT'C hT'odd
    refine ⟨ψ p, ?_, ?_, ?_⟩
    · rw [mem_centralizer_iff]
      intro τ hτ
      obtain ⟨τ', hτ', rfl⟩ : ∃ τ' ∈ T.comap ψ, ψ τ' = τ := by
        rw [← hT'map] at hτ
        exact hτ
      rw [← map_mul, ← map_mul, mem_centralizer_iff.1 hpT τ' hτ']
    · have h1 : ψ p ∈ fixedSubgroup η := by
        rw [hη]
        exact ⟨p, rfl⟩
      exact h1
    · rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, orderOf_injective ψ hψ]
      exact hpord

end Properties


section Central

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K]

theorem false_of_conj_spARep_of_central {n : ℕ} (e : L ≃* StatedSp n K) {t g : G}
    (htC : t ∈ centralizer (L : Set G)) {G₀ : Subgroup G} (θs : MulAut G₀)
    (hact : ∀ y : G₀, ((θs y : G₀) : G) = (g⁻¹ * t * g) * y * (g⁻¹ * t * g)⁻¹)
    {x₀ : G₀} {η : MulAut G₀} (hα : θs = MulAut.conj x₀ * η)
    (hFel : ∀ T : Subgroup G₀, T ≤ fixedSubgroup θs → Odd (Nat.card T) →
      ∃ p : G₀, p ∈ centralizer (T : Set G₀) ∧ η p = p ∧ orderOf (x₀ * p * x₀⁻¹ * p⁻¹) = 2)
    (hΛ : L ⊓ centralizer ({g * x₀ * g⁻¹} : Set G) ≤
      (fixedSubgroup θs).map ((MulAut.conj g).toMonoidHom.comp G₀.subtype))
    {a : StatedSp n K} {A Z : Subgroup (StatedSp n K)} (hZA : Z ≤ A)
    (hA : A ≤ centralizer ({a} : Set (StatedSp n K))) (hAodd : Odd (Nat.card A)) {l : G}
    (hlL : l ∈ L) (hxl : g * x₀ * g⁻¹ = l * ((e.symm a : L) : G) * l⁻¹)
    (hcen : ∀ h ∈ centralizer (modelToG e Z : Set G), orderOf (t * h * t⁻¹ * h⁻¹) ≠ 2) :
    False := by
  set x : G := g * x₀ * g⁻¹ with hx
  set φ : G₀ →* G := (MulAut.conj g).toMonoidHom.comp G₀.subtype with hφ
  have hinj : Function.Injective φ := (MulAut.conj g).injective.comp G₀.subtype_injective
  set T₀ : Subgroup G := modelToG e A with hT₀
  set T : Subgroup G := T₀.map (MulAut.conj l).toMonoidHom with hT
  have hTΛ : T ≤ (fixedSubgroup θs).map φ := by
    refine le_trans ?_ hΛ
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨d, hd, rfl⟩ := (mem_modelToG e).1 hy
    have hdz := mem_centralizer_singleton_iff.1 (hA hd)
    have hmemL : l * ((e.symm d : L) : G) * l⁻¹ ∈ L :=
      L.mul_mem (L.mul_mem hlL (e.symm d).2) (L.inv_mem hlL)
    refine ⟨hmemL, ?_⟩
    show l * ((e.symm d : L) : G) * l⁻¹ ∈ centralizer ({x} : Set G)
    rw [mem_centralizer_singleton_iff, hxl]
    have h2 : ((e.symm d : L) : G) * ((e.symm a : L) : G) =
        ((e.symm a : L) : G) * ((e.symm d : L) : G) := by
      rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, hdz]
    calc l * ((e.symm d : L) : G) * l⁻¹ * (l * ((e.symm a : L) : G) * l⁻¹) =
        l * (((e.symm d : L) : G) * ((e.symm a : L) : G)) * l⁻¹ := by group
      _ = l * (((e.symm a : L) : G) * ((e.symm d : L) : G)) * l⁻¹ := by rw [h2]
      _ = l * ((e.symm a : L) : G) * l⁻¹ * (l * ((e.symm d : L) : G) * l⁻¹) := by group
  have hT₀odd : Odd (Nat.card T₀) := by
    rw [hT₀, UnitaryPilot.modelToG_def, Subgroup.card_map_of_injective L.subtype_injective,
      Subgroup.card_map_of_injective e.symm.injective]
    exact hAodd
  have hTodd : Odd (Nat.card T) := by
    rw [hT, Subgroup.card_map_of_injective (MulAut.conj l).injective]
    exact hT₀odd
  set Tu : Subgroup G₀ := T.comap φ with hTu
  have hTuF : Tu ≤ fixedSubgroup θs := by
    intro y hy
    obtain ⟨y', hy', hyy'⟩ := hTΛ hy
    have : y' = y := hinj hyy'
    rw [← this]
    exact hy'
  have hTuodd : Odd (Nat.card Tu) := by
    have h1 : Nat.card (Tu.map φ) = Nat.card Tu := Subgroup.card_map_of_injective hinj
    have h2 : Tu.map φ ≤ T := Subgroup.map_comap_le _ _
    rw [← h1]
    exact Odd.of_dvd_nat hTodd (Subgroup.card_dvd_of_le h2)
  obtain ⟨p, hpT, hηp, hpord⟩ := hFel Tu hTuF hTuodd
  set h : G := l⁻¹ * φ p * l with hh
  have hcentA : h ∈ centralizer (T₀ : Set G) := by
    rw [mem_centralizer_iff]
    intro τ hτ
    have hτT : l * τ * l⁻¹ ∈ T := ⟨τ, hτ, rfl⟩
    obtain ⟨τ', -, hττ'⟩ := hTΛ hτT
    have hτ'u : τ' ∈ Tu := by
      show φ τ' ∈ T
      rw [hττ']
      exact hτT
    have h1 : τ' * p = p * τ' := mem_centralizer_iff.1 hpT τ' hτ'u
    have h2 : (l * τ * l⁻¹) * φ p = φ p * (l * τ * l⁻¹) := by
      rw [← hττ', ← map_mul, ← map_mul, h1]
    calc τ * h = l⁻¹ * ((l * τ * l⁻¹) * φ p) * l := by rw [hh]; group
      _ = l⁻¹ * (φ p * (l * τ * l⁻¹)) * l := by rw [h2]
      _ = h * τ := by rw [hh]; group
  have hcentZ : h ∈ centralizer (modelToG e Z : Set G) := by
    rw [mem_centralizer_iff]
    intro τ hτ
    exact mem_centralizer_iff.1 hcentA τ (UnitaryPilot.modelToG_mono e hZA hτ)
  have hlt : l * t = t * l := mem_centralizer_iff.1 htC l hlL
  have htp : t * φ p * t⁻¹ = g * ((x₀ : G) * p * (x₀ : G)⁻¹) * g⁻¹ := by
    have h1 := hact p
    rw [hα, MulAut.mul_apply, hηp, MulAut.conj_apply] at h1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
    calc t * φ p * t⁻¹ = g * ((g⁻¹ * t * g) * (p : G) * (g⁻¹ * t * g)⁻¹) * g⁻¹ := by
          rw [hφ]
          simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
            MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
          group
      _ = g * ((x₀ : G) * p * (x₀ : G)⁻¹) * g⁻¹ := by rw [← h1]
  have hcomm : t * h * t⁻¹ * h⁻¹ =
      (l⁻¹ * g) * (((x₀ * p * x₀⁻¹ * p⁻¹ : G₀) : G)) * (l⁻¹ * g)⁻¹ := by
    have hlt' : l⁻¹ * t = t * l⁻¹ := by
      calc l⁻¹ * t = l⁻¹ * (t * l) * l⁻¹ := by group
        _ = l⁻¹ * (l * t) * l⁻¹ := by rw [hlt]
        _ = t * l⁻¹ := by group
    have e1 : t * h * t⁻¹ = l⁻¹ * (t * φ p * t⁻¹) * l := by
      rw [hh]
      calc t * (l⁻¹ * φ p * l) * t⁻¹ = (t * l⁻¹) * φ p * (l * t⁻¹) := by group
        _ = (l⁻¹ * t) * φ p * (t⁻¹ * l) := by
            rw [← hlt']
            congr 1
            calc l * t⁻¹ = t⁻¹ * (t * l) * t⁻¹ := by group
              _ = t⁻¹ * (l * t) * t⁻¹ := by rw [hlt]
              _ = t⁻¹ * l := by group
        _ = l⁻¹ * (t * φ p * t⁻¹) * l := by group
    rw [e1, htp, hh, hφ]
    simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  apply hcen h hcentZ
  rw [hcomm]
  have h1 := MulEquiv.orderOf_eq (MulAut.conj (l⁻¹ * g))
    (((x₀ * p * x₀⁻¹ * p⁻¹ : G₀) : G))
  rw [MulAut.conj_apply] at h1
  rw [h1, Subgroup.orderOf_coe]
  exact hpord

end Central

end CFSG.SeitzReduction.SymplecticPilot
