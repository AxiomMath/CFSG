module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.GroupTheory.SteinbergCDCyclicNormalHall
public import CFSG.RankThree.Lattice.SteinbergBIE6OrderThreeTools
public import CFSG.RankThree.LocalRank.SolvablePrimeComplementCore
public import CFSG.RankThree.PartOne.KE.E6TwThreeLayer
public import CFSG.RankThree.PartOne.KE.OrdinaryEPointwise

public noncomputable section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.TwE6Three

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.Chevalley CFSG.RankThree.GroupTheory
open CFSG.RankThree.PartOne.KE
open CFSG.RankThree.E6
open CFSG.RankThree.LocalRank CFSG.ComponentClassification.OuterAutomorphisms
open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Lattice
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.Classical2
open scoped Pointwise commutatorElement Matrix MatrixGroups

set_option linter.unusedSectionVars false


variable {ℓ f : ℕ} {K : Type} [Field K] {σ : K ≃+* K} {Ω : Type} [Field Ω] [Algebra K Ω]
  [IsAlgClosure K Ω] {Fr : Ω →+* Ω} {g : ModGL Tag.E6 Ω}


namespace A2A2Aux

theorem diag_mul_eq_scalar_of_centralizes_twoA2 {h z₁ z₂ : ModGL Tag.E6 Ω}
    (hh : h ∈ torusGroup Tag.E6 Ω) {s₁ t₁ s₂ t₂ : Ωˣ}
    (hs₁ : ∀ c : Ω, h * xUnit Tag.E6 Ω (e6Index 0) c * h⁻¹ = xUnit Tag.E6 Ω (e6Index 0) (s₁ * c))
    (ht₁ : ∀ c : Ω, h * xUnit Tag.E6 Ω (e6Index 2) c * h⁻¹ = xUnit Tag.E6 Ω (e6Index 2) (t₁ * c))
    (hs₂ : ∀ c : Ω, h * xUnit Tag.E6 Ω (e6Index 4) c * h⁻¹ = xUnit Tag.E6 Ω (e6Index 4) (s₂ * c))
    (ht₂ : ∀ c : Ω, h * xUnit Tag.E6 Ω (e6Index 5) c * h⁻¹ = xUnit Tag.E6 Ω (e6Index 5) (t₂ * c))
    (hz₁ : z₁ ∈ subsystemGroup Tag.E6 Ω support13)
    (hz₂ : z₂ ∈ subsystemGroup Tag.E6 Ω support56) (S : Set (SL(3, Ω) × SL(3, Ω)))
    (hS : ∀ s ∈ S, (h * z₁ * z₂) * twoA2Mul Ω s = twoA2Mul Ω s * (h * z₁ * z₂))
    (g₁ g₂ : SL(3, Ω))
    (hT₁ : ∀ (i j : Fin 3) (hij : i ≠ j),
      ∃ s ∈ S, s.1 = g₁ * Matrix.SpecialLinearGroup.transvection hij 1 * g₁⁻¹)
    (hT₂ : ∀ (i j : Fin 3) (hij : i ≠ j),
      ∃ s ∈ S, s.2 = g₂ * Matrix.SpecialLinearGroup.transvection hij 1 * g₂⁻¹) :
    (∃ c₁ : Ω, diagonal ![((s₁ * t₁ : Ωˣ) : Ω), (t₁ : Ω), 1] * a2Mat₁ z₁ = scalar (Fin 3) c₁) ∧
      ∃ c₂ : Ω, diagonal ![((s₂ * t₂ : Ωˣ) : Ω), (t₂ : Ω), 1] * a2Mat₂ z₂ = scalar (Fin 3) c₂ := by
  let D₁ : GL (Fin 3) Ω := ⟨_, _, (diagonal_inv_pair s₁ t₁).1, (diagonal_inv_pair s₁ t₁).2⟩
  let D₂ : GL (Fin 3) Ω := ⟨_, _, (diagonal_inv_pair s₂ t₂).1, (diagonal_inv_pair s₂ t₂).2⟩
  set ρz₁ := a2Rep₁ Ω ⟨z₁, hz₁⟩
  set ρz₂ := a2Rep₂ Ω ⟨z₂, hz₂⟩
  obtain ⟨M₁, hM₁⟩ : ∃ M : GL (Fin 3) Ω, M = D₁ * Matrix.SpecialLinearGroup.toGL ρz₁ :=
    ⟨_, rfl⟩
  obtain ⟨M₂, hM₂⟩ : ∃ M : GL (Fin 3) Ω, M = D₂ * Matrix.SpecialLinearGroup.toGL ρz₂ :=
    ⟨_, rfl⟩
  have hM₁v : (M₁ : Matrix (Fin 3) (Fin 3) Ω) =
      diagonal ![((s₁ * t₁ : Ωˣ) : Ω), (t₁ : Ω), 1] * a2Mat₁ z₁ := by
    rw [hM₁, Units.val_mul, Matrix.SpecialLinearGroup.coe_GL_coe_matrix, coe_a2Rep₁]
  have hM₂v : (M₂ : Matrix (Fin 3) (Fin 3) Ω) =
      diagonal ![((s₂ * t₂ : Ωˣ) : Ω), (t₂ : Ω), 1] * a2Mat₂ z₂ := by
    rw [hM₂, Units.val_mul, Matrix.SpecialLinearGroup.coe_GL_coe_matrix, coe_a2Rep₂]
  have hM₁i : (↑M₁⁻¹ : Matrix (Fin 3) (Fin 3) Ω) =
      a2Mat₁ z₁⁻¹ * diagonal ![(((s₁ * t₁)⁻¹ : Ωˣ) : Ω), ((t₁⁻¹ : Ωˣ) : Ω), 1] := by
    rw [hM₁, _root_.mul_inv_rev, Units.val_mul, ← map_inv,
      Matrix.SpecialLinearGroup.coe_GL_coe_matrix, ← map_inv, coe_a2Rep₁]
    rfl
  have hM₂i : (↑M₂⁻¹ : Matrix (Fin 3) (Fin 3) Ω) =
      a2Mat₂ z₂⁻¹ * diagonal ![(((s₂ * t₂)⁻¹ : Ωˣ) : Ω), ((t₂⁻¹ : Ωˣ) : Ω), 1] := by
    rw [hM₂, _root_.mul_inv_rev, Units.val_mul, ← map_inv,
      Matrix.SpecialLinearGroup.coe_GL_coe_matrix, ← map_inv, coe_a2Rep₂]
    rfl
  have hdisc : ∀ s ∈ S, ∃ c : Ω,
      (M₁ : Matrix (Fin 3) (Fin 3) Ω) * s.1 * (↑M₁⁻¹ : Matrix (Fin 3) (Fin 3) Ω) =
        c • (s.1 : Matrix (Fin 3) (Fin 3) Ω) ∧
      (M₂ : Matrix (Fin 3) (Fin 3) Ω) * s.2 * (↑M₂⁻¹ : Matrix (Fin 3) (Fin 3) Ω) =
        c • (s.2 : Matrix (Fin 3) (Fin 3) Ω) := by
    rintro ⟨X, Y⟩ hs
    set u := ((a2Equiv₁ Ω).symm X : ModGL Tag.E6 Ω)
    set v := ((a2Equiv₂ Ω).symm Y : ModGL Tag.E6 Ω)
    have hu : u ∈ subsystemGroup Tag.E6 Ω support13 := ((a2Equiv₁ Ω).symm X).2
    have hv : v ∈ subsystemGroup Tag.E6 Ω support56 := ((a2Equiv₂ Ω).symm Y).2
    have hau : a2Mat₁ u = X := by
      have := congrArg (fun A : SL(3, Ω) => (A : Matrix (Fin 3) (Fin 3) Ω))
        (MulEquiv.apply_symm_apply (a2Equiv₁ Ω) X)
      simpa only [a2Equiv₁_apply, coe_a2Rep₁] using this
    have hav : a2Mat₂ v = Y := by
      have := congrArg (fun A : SL(3, Ω) => (A : Matrix (Fin 3) (Fin 3) Ω))
        (MulEquiv.apply_symm_apply (a2Equiv₂ Ω) Y)
      simpa only [a2Equiv₂_apply, coe_a2Rep₂] using this
    obtain ⟨hu', hau'⟩ := a2Mat₁_conj_formula hh hs₁ ht₁ hz₁ hu
    obtain ⟨hv', hav'⟩ := a2Mat₂_conj_formula hh hs₂ ht₂ hz₂ hv
    set u' := h * (z₁ * u * z₁⁻¹) * h⁻¹
    set v' := h * (z₂ * v * z₂⁻¹) * h⁻¹
    have hcomm := hS (X, Y) hs
    rw [twoA2Mul_apply] at hcomm
    have c1 : z₂ * u = u * z₂ := (commute_Q₁_Q₂ hu hz₂).eq.symm
    have hzvz : z₂ * v * z₂⁻¹ ∈ subsystemGroup Tag.E6 Ω support56 :=
      mul_mem (mul_mem hz₂ hv) (inv_mem hz₂)
    have c2 : z₁⁻¹ * (z₂ * v * z₂⁻¹) = (z₂ * v * z₂⁻¹) * z₁⁻¹ :=
      (commute_Q₁_Q₂ (inv_mem hz₁) hzvz).eq
    have huv : u' * v' = u * v := by
      calc u' * v' = h * z₁ * u * (z₁⁻¹ * (z₂ * v * z₂⁻¹)) * h⁻¹ := by
            simp only [u', v']
            group
        _ = h * z₁ * u * ((z₂ * v * z₂⁻¹) * z₁⁻¹) * h⁻¹ := by rw [c2]
        _ = h * z₁ * (u * z₂) * v * z₂⁻¹ * z₁⁻¹ * h⁻¹ := by group
        _ = h * z₁ * (z₂ * u) * v * z₂⁻¹ * z₁⁻¹ * h⁻¹ := by rw [c1]
        _ = (h * z₁ * z₂) * (u * v) * (h * z₁ * z₂)⁻¹ := by group
        _ = u * v := by rw [hcomm, mul_inv_cancel_right]
    have h1 : u⁻¹ * u' ∈ subsystemGroup Tag.E6 Ω support13 := mul_mem (inv_mem hu) hu'
    have h2 : v' * v⁻¹ ∈ subsystemGroup Tag.E6 Ω support56 := mul_mem hv' (inv_mem hv)
    have hone : twoA2Mul Ω (a2Equiv₁ Ω ⟨_, h1⟩, a2Equiv₂ Ω ⟨_, h2⟩) = 1 := by
      rw [twoA2Mul_apply, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]
      change u⁻¹ * u' * (v' * v⁻¹) = 1
      calc u⁻¹ * u' * (v' * v⁻¹) = u⁻¹ * (u' * v') * v⁻¹ := by group
        _ = 1 := by rw [huv]; group
    obtain ⟨c, -, hc₁, hc₂⟩ := (twoA2Mul_eq_one_iff _ _).1 hone
    rw [a2Equiv₁_apply, coe_a2Rep₁] at hc₁
    rw [a2Equiv₂_apply, coe_a2Rep₂] at hc₂
    change a2Mat₁ (u⁻¹ * u') = scalar (Fin 3) c at hc₁
    change a2Mat₂ (v' * v⁻¹) = scalar (Fin 3) c at hc₂
    rw [a2Mat₁_mul (inv_mem hu) hu'] at hc₁
    rw [a2Mat₂_mul hv' (inv_mem hv)] at hc₂
    have hinvu : a2Mat₁ u * a2Mat₁ u⁻¹ = 1 := by
      rw [← a2Mat₁_mul hu (inv_mem hu), mul_inv_cancel, a2Mat₁_one]
    have hinvv : a2Mat₂ v⁻¹ * a2Mat₂ v = 1 := by
      rw [← a2Mat₂_mul (inv_mem hv) hv, inv_mul_cancel, a2Mat₂_one]
    refine ⟨c, ?_, ?_⟩
    ·
      change (M₁ : Matrix (Fin 3) (Fin 3) Ω) * X * (↑M₁⁻¹ : Matrix (Fin 3) (Fin 3) Ω) = _
      rw [hM₁v, hM₁i, ← hau, ← hau']
      calc a2Mat₁ u' = a2Mat₁ u * (a2Mat₁ u⁻¹ * a2Mat₁ u') := by
            rw [← Matrix.mul_assoc, hinvu, Matrix.one_mul]
        _ = c • a2Mat₁ u := by
            rw [hc₁, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul,
              Matrix.mul_one]
    · change (M₂ : Matrix (Fin 3) (Fin 3) Ω) * Y * (↑M₂⁻¹ : Matrix (Fin 3) (Fin 3) Ω) = _
      rw [hM₂v, hM₂i, ← hav, ← hav']
      calc a2Mat₂ v' = (a2Mat₂ v' * a2Mat₂ v⁻¹) * a2Mat₂ v := by
            rw [Matrix.mul_assoc, hinvv, Matrix.mul_one]
        _ = c • a2Mat₂ v := by
            rw [hc₂, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul,
              Matrix.one_mul]
  obtain ⟨c₁, hc₁⟩ := exists_eq_scalar_of_discrepancy M₁ g₁ (Prod.fst '' S)
    (fun X hX => by
      obtain ⟨s, hs, rfl⟩ := hX
      obtain ⟨c, hc, -⟩ := hdisc s hs
      exact ⟨c, hc⟩)
    (fun i j hij => by
      obtain ⟨s, hs, hs1⟩ := hT₁ i j hij
      exact ⟨s, hs, hs1⟩)
  obtain ⟨c₂, hc₂⟩ := exists_eq_scalar_of_discrepancy M₂ g₂ (Prod.snd '' S)
    (fun Y hY => by
      obtain ⟨s, hs, rfl⟩ := hY
      obtain ⟨c, -, hc⟩ := hdisc s hs
      exact ⟨c, hc⟩)
    (fun i j hij => by
      obtain ⟨s, hs, hs2⟩ := hT₂ i j hij
      exact ⟨s, hs, hs2⟩)
  rw [hM₁v] at hc₁
  rw [hM₂v] at hc₂
  exact ⟨⟨c₁, hc₁⟩, ⟨c₂, hc₂⟩⟩

theorem eq_one_of_diagonal_eq_scalar {s t : Ωˣ} {c : Ω}
    (h : diagonal ![((s * t : Ωˣ) : Ω), (t : Ω), 1] = scalar (Fin 3) c) : s = 1 ∧ t = 1 := by
  have h22 := congrFun (congrFun h 2) 2
  have h11 := congrFun (congrFun h 1) 1
  have h00 := congrFun (congrFun h 0) 0
  simp only [Matrix.scalar_apply, diagonal_apply_eq] at h22 h11 h00
  simp at h22 h11 h00
  subst h22
  have ht : t = 1 := Units.ext (by rw [h11, Units.val_one])
  refine ⟨Units.ext ?_, ht⟩
  rw [ht, Units.val_one, mul_one] at h00
  rw [h00, Units.val_one]

end A2A2Aux

theorem phi3_A2A2_commute_roots (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpq : p ∣ (ℓ ^ f) ^ 2 + ℓ ^ f + 1) (hg : g ∈ adjointGroup Tag.E6 Ω)
    (hgn : g⁻¹ * twistE6 Ω Fr g = canonicalRep (coxeterSystem Tag.E6) Ω phi3V)
    {x : ModGL Tag.E6 Ω} (hx : x ∈ phi3TStar K σ Ω Fr g) (hxp : orderOf x = p)
    (hA2A2 : ∃ w : WeylGroup Tag.E6,
      (w • ·) '' torusRootKernel x = parabolicRoots Tag.E6 supportA2A2)
    {h : ModGL Tag.E6 Ω} (hh : h ∈ torusGroup Tag.E6 Ω)
    (hc : ∀ u ∈ ⁅rootSpan Tag.E6 Ω (torusRootKernel x) ⊓ phi3FixedGroup Ω Fr,
      rootSpan Tag.E6 Ω (torusRootKernel x) ⊓ phi3FixedGroup Ω Fr⁆, h * u = u * h) :
    ∀ α ∈ torusRootKernel x, ∀ c : Ω, h * pinnedX Tag.E6 Ω α c = pinnedX Tag.E6 Ω α c * h := by
  classical
  obtain ⟨w, k₂, h₁, h₂, hw, -, hlayer⟩ := KETw3.phi3_A2A2_layer (σ := (σ : K →+* K)) hℓ hf hK
    (fun c => hσ c) hFr hp hp3 hpq hx.1 hxp hA2A2
  set n := canonicalRep (coxeterSystem Tag.E6) Ω w with hn
  have hnN := canonicalRep_mem_normalizer (R := Ω) w
  have hh' : n * h * n⁻¹ ∈ torusGroup Tag.E6 Ω := (Subgroup.mem_normalizer_iff.1 hnN h).1 hh
  set S : Set (SL(3, Ω) × SL(3, Ω)) := Set.range fun A : SL(3, k₂) =>
    (h₁ * Matrix.SpecialLinearGroup.map k₂.subtype A * h₁⁻¹,
      h₂ * invTransposeMapSL Fr 3 (Matrix.SpecialLinearGroup.map k₂.subtype A) * h₂⁻¹)
    with hSdef
  have hS : ∀ s ∈ S, (n * h * n⁻¹ * 1 * 1) * twoA2Mul Ω s =
      twoA2Mul Ω s * (n * h * n⁻¹ * 1 * 1) := by
    rintro _ ⟨A, rfl⟩
    have hc0 := hc _ (hlayer A)
    rw [mul_one, mul_one]
    set μ := twoA2Mul Ω (h₁ * Matrix.SpecialLinearGroup.map k₂.subtype A * h₁⁻¹,
      h₂ * invTransposeMapSL Fr 3 (Matrix.SpecialLinearGroup.map k₂.subtype A) * h₂⁻¹)
    calc n * h * n⁻¹ * μ = n * (h * (n⁻¹ * μ * n)) * n⁻¹ := by group
      _ = n * ((n⁻¹ * μ * n) * h) * n⁻¹ := by rw [hc0]
      _ = μ * (n * h * n⁻¹) := by group
  have hT₁ : ∀ (i j : Fin 3) (hij : i ≠ j),
      ∃ s ∈ S, s.1 = h₁ * Matrix.SpecialLinearGroup.transvection hij 1 * h₁⁻¹ :=
    fun i j hij => ⟨_, ⟨Matrix.SpecialLinearGroup.transvection hij 1, rfl⟩, by
      dsimp only
      rw [Matrix.SpecialLinearGroup.map_transvection, map_one]⟩
  have hT₂ : ∀ (i j : Fin 3) (hij : i ≠ j),
      ∃ s ∈ S, s.2 = h₂ * Matrix.SpecialLinearGroup.transvection hij 1 * h₂⁻¹ :=
    fun i j hij => ⟨_, ⟨Matrix.SpecialLinearGroup.transvection hij.symm (-1), rfl⟩, by
      dsimp only
      rw [Matrix.SpecialLinearGroup.map_transvection, map_neg, map_one,
        invTransposeMapSL_transvection_neg_one]⟩
  obtain ⟨χ, hχ, hχy⟩ := exists_simple_root_characters hh'
  obtain ⟨⟨c₁, hc₁⟩, ⟨c₂, hc₂⟩⟩ := A2A2Aux.diag_mul_eq_scalar_of_centralizes_twoA2 hh'
    (hχ (e6Index 0)) (hχ (e6Index 2)) (hχ (e6Index 4)) (hχ (e6Index 5)) (one_mem _) (one_mem _)
    S hS h₁ h₂ hT₁ hT₂
  rw [a2Mat₁_one, Matrix.mul_one] at hc₁
  rw [a2Mat₂_one, Matrix.mul_one] at hc₂
  obtain ⟨hs₁, ht₁⟩ := A2A2Aux.eq_one_of_diagonal_eq_scalar hc₁
  obtain ⟨hs₂, ht₂⟩ := A2A2Aux.eq_one_of_diagonal_eq_scalar hc₂
  have hχ1 : ∀ i ∈ supportA2A2, χ i = 1 := by
    intro i hi
    rcases (mem_supportA2A2 i).1 hi with rfl | rfl | rfl | rfl
    · exact hs₁
    · exact ht₁
    · exact hs₂
    · exact ht₂
  have hgen : ∀ i ∈ supportA2A2, ∀ c : Ω,
      xUnit Tag.E6 Ω i c ∈ Subgroup.centralizer {n * h * n⁻¹} ∧
        yUnit Tag.E6 Ω i c ∈ Subgroup.centralizer {n * h * n⁻¹} := by
    intro i hi c
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
    have hx' := hχ i c
    have hy' := hχy i c
    rw [hχ1 i hi, Units.val_one, one_mul] at hx'
    rw [hχ1 i hi, inv_one, Units.val_one, one_mul] at hy'
    exact ⟨(mul_inv_eq_iff_eq_mul.1 hx').symm, (mul_inv_eq_iff_eq_mul.1 hy').symm⟩
  have hsub : ∀ J : Set (Fin Tag.E6.rank), J ⊆ supportA2A2 →
      subsystemGroup Tag.E6 Ω J ≤ Subgroup.centralizer {n * h * n⁻¹} := by
    intro J hJ
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨i, hi, c, rfl | rfl⟩
    · exact (hgen i (hJ hi) c).1
    · exact (hgen i (hJ hi) c).2
  have hcent : subsystemGroup Tag.E6 Ω support13 ⊔ subsystemGroup Tag.E6 Ω support56 ≤
      Subgroup.centralizer {n * h * n⁻¹} := by
    refine sup_le (hsub _ fun i hi => ?_) (hsub _ fun i hi => ?_)
    · rcases (mem_support13 i).1 hi with rfl | rfl
      · exact (mem_supportA2A2 _).2 (Or.inl rfl)
      · exact (mem_supportA2A2 _).2 (Or.inr (Or.inl rfl))
    · rcases (mem_support56 i).1 hi with rfl | rfl
      · exact (mem_supportA2A2 _).2 (Or.inr (Or.inr (Or.inl rfl)))
      · exact (mem_supportA2A2 _).2 (Or.inr (Or.inr (Or.inr rfl)))
  have hmap : (rootSpan Tag.E6 Ω (torusRootKernel x)).map (MulAut.conj n).toMonoidHom =
      subsystemGroup Tag.E6 Ω support13 ⊔ subsystemGroup Tag.E6 Ω support56 := by
    rw [(canonical_weyl_root_transport Tag.E6 Ω).1 w _ fun α hα => hα.1, hw,
      rootSpan_supportA2A2]
  intro α hα c
  have hmem : pinnedX Tag.E6 Ω α c ∈ rootSpan Tag.E6 Ω (torusRootKernel x) :=
    Subgroup.mem_iSup_of_mem α (Subgroup.mem_iSup_of_mem hα (Subgroup.subset_closure ⟨c, rfl⟩))
  have h1 : n * pinnedX Tag.E6 Ω α c * n⁻¹ ∈
      subsystemGroup Tag.E6 Ω support13 ⊔ subsystemGroup Tag.E6 Ω support56 := by
    rw [← hmap]
    exact ⟨_, hmem, by simp [MulAut.conj_apply]⟩
  have h2 := Subgroup.mem_centralizer_singleton_iff.1 (hcent h1)
  have h3 : n * (h * pinnedX Tag.E6 Ω α c) * n⁻¹ = n * (pinnedX Tag.E6 Ω α c * h) * n⁻¹ := by
    calc n * (h * pinnedX Tag.E6 Ω α c) * n⁻¹ =
        n * h * n⁻¹ * (n * pinnedX Tag.E6 Ω α c * n⁻¹) := by group
      _ = n * pinnedX Tag.E6 Ω α c * n⁻¹ * (n * h * n⁻¹) := h2.symm
      _ = n * (pinnedX Tag.E6 Ω α c * h) * n⁻¹ := by group
  exact mul_left_cancel (mul_right_cancel h3)

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.TwE6Three
