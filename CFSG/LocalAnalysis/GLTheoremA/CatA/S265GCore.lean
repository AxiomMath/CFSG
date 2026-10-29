module

public import CFSG.LieType.Chevalley.EvenOddCentralizerRadicalLevels
public import CFSG.LieType.Chevalley.OddF4CosetDescent

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265G

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.EvenOddRadical

theorem two_pow_mod_three_of_odd {n : ℕ} (hn : Odd n) : 2 ^ n % 3 = 2 := by
  obtain ⟨k, rfl⟩ := hn
  rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
  norm_num

variable
  {τ : Tag} {K : Type} [Field K] [Finite K]

theorem entrywiseAdjointAut_apply_three {σ : K ≃+* K} (hσ : σ ^ 3 = 1) (x : adjointGroup τ K) :
    entrywiseAdjointAut τ σ (entrywiseAdjointAut τ σ (entrywiseAdjointAut τ σ x)) = x := by
  have h : entrywiseAdjointAut τ σ ^ 3 = 1 := by
    rw [← entrywiseAdjointAut_pow, hσ, entrywiseAdjointAut_one]
  have hx := congrArg (fun ψ : MulAut (adjointGroup τ K) => ψ x) h
  simpa only [pow_succ, pow_zero, one_mul, MulAut.mul_apply, MulAut.one_apply] using hx

theorem exists_fixed_of_odd_level {f : ℕ} (hf : Odd f) (hK : Nat.card K = 2 ^ f) {σ : K ≃+* K}
    (hσ : σ ^ 3 = 1) {J : Set (Fin τ.rank)} {d : ℤ} (hd : 1 ≤ d)
    (hodd : Odd (levelRoots τ J d).ncard) {A : Subgroup (adjointGroup τ K)}
    (hAσ : ∀ a ∈ A, entrywiseAdjointAut τ σ a = a) (g : adjointGroup τ K)
    (hy : ((g⁻¹ * entrywiseAdjointAut τ σ g : adjointGroup τ K) : ModGL τ K) ∈
      parabolicSubgroup τ K J)
    (hA : ∀ a ∈ A, ((g⁻¹ * a * g : adjointGroup τ K) : ModGL τ K) ∈ parabolicSubgroup τ K J) :
    ∃ U : Subgroup (adjointGroup τ K), U ≠ ⊥ ∧ IsPGroup 2 U ∧
      (∀ u ∈ U, entrywiseAdjointAut τ σ u = u) ∧
        A ≤ Subgroup.normalizer (U : Set (adjointGroup τ K)) := by
  classical
  set φ : MulAut (adjointGroup τ K) := entrywiseAdjointAut τ σ with hφdef
  have hcoe : ∀ x : adjointGroup τ K,
      ((φ x : adjointGroup τ K) : ModGL τ K) = Units.map (entrywiseHom σ.toRingHom) x :=
    fun _ => rfl
  have hφ3 : ∀ x, φ (φ (φ x)) = x := entrywiseAdjointAut_apply_three hσ
  have hBC : borelGroup τ K ≤ adjointGroup τ K :=
    ((triangular_borel_structure.{0, 0} τ K).2.2.2.2.2.2.2.2.2.2.2 K).1
  have hQC : levelRadical τ K J d ≤ adjointGroup τ K :=
    (levelRadical_le_posUnipotent J d).trans (le_sup_right.trans hBC)
  set QC : Subgroup (adjointGroup τ K) := (levelRadical τ K J d).subgroupOf (adjointGroup τ K)
    with hQCdef
  have hφQ : ∀ q ∈ QC, φ q ∈ QC := by
    intro q hq
    rw [hQCdef, Subgroup.mem_subgroupOf] at hq ⊢
    rw [hcoe]
    exact entrywise_mem_rootSpan hq
  have hPQ : ∀ p q : adjointGroup τ K, (p : ModGL τ K) ∈ parabolicSubgroup τ K J → q ∈ QC →
      p * q * p⁻¹ ∈ QC := by
    intro p q hp hq
    rw [hQCdef, Subgroup.mem_subgroupOf] at hq ⊢
    have h := (Subgroup.mem_normalizer_iff.mp
      (parabolicSubgroup_le_normalizer (J := J) hd hp) (q : ModGL τ K)).mp hq
    simpa using h
  set X : Subgroup (adjointGroup τ K) := QC.map (MulAut.conj g).toMonoidHom with hXdef
  have hmemX : ∀ x, x ∈ X ↔ g⁻¹ * x * g ∈ QC := by
    intro x
    constructor
    · rintro ⟨q, hq, rfl⟩
      simpa [MulAut.conj_apply, mul_assoc] using hq
    · intro hx
      refine ⟨g⁻¹ * x * g, hx, ?_⟩
      simp [MulAut.conj_apply, mul_assoc]
  have hφX : ∀ x ∈ X, φ x ∈ X := by
    intro x hx
    rw [hmemX] at hx ⊢
    have h : g⁻¹ * φ x * g = (g⁻¹ * φ g) * φ (g⁻¹ * x * g) * (g⁻¹ * φ g)⁻¹ := by
      simp only [map_mul, map_inv]
      group
    rw [h]
    exact hPQ _ _ hy (hφQ _ hx)
  have hAX : ∀ a ∈ A, ∀ x ∈ X, a * x * a⁻¹ ∈ X := by
    intro a ha x hx
    rw [hmemX] at hx ⊢
    have h : g⁻¹ * (a * x * a⁻¹) * g = (g⁻¹ * a * g) * (g⁻¹ * x * g) * (g⁻¹ * a * g)⁻¹ := by
      group
    rw [h]
    exact hPQ _ _ (hA a ha) hx
  have hcardX : Nat.card X = 2 ^ (f * (levelRoots τ J d).ncard) := by
    have h1 : Nat.card X = Nat.card QC :=
      Subgroup.card_map_of_injective (MulAut.conj g).injective
    have h2 : Nat.card QC = Nat.card (levelRadical τ K J d) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQC).toEquiv
    rw [h1, h2, card_levelRadical, hK, ← pow_mul]
  have hX2 : IsPGroup 2 X := IsPGroup.of_card hcardX
  obtain ⟨u, huX, hu1, hφu⟩ : ∃ u ∈ X, u ≠ 1 ∧ φ u = u := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    haveI : Fintype X := Fintype.ofFinite _
    let T : Function.End X := fun x => ⟨φ x, hφX x x.2⟩
    have hT : T ^ 3 ^ 1 = 1 := by
      funext x
      apply Subtype.ext
      exact hφ3 x
    have h := Equiv.Perm.card_fixedPoints_modEq (f := T) hT
    rw [← Nat.card_eq_fintype_card, hcardX] at h
    have hmod : Fintype.card (Function.fixedPoints T) % 3 = 2 := by
      have h' : 2 ^ (f * (levelRoots τ J d).ncard) % 3 =
          Fintype.card (Function.fixedPoints T) % 3 := h
      rw [← h', two_pow_mod_three_of_odd (hf.mul hodd)]
    by_contra hcon
    push Not at hcon
    have hsub : Function.fixedPoints T ⊆ {1} := by
      intro x hx
      have hx' : φ x = x := congrArg Subtype.val hx
      by_contra hx1
      exact hcon x x.2 (fun h => hx1 (Subtype.ext h)) hx'
    have hle : Fintype.card (Function.fixedPoints T) ≤ 1 := by
      calc Fintype.card (Function.fixedPoints T)
          ≤ Fintype.card ({1} : Set X) := Set.card_le_card hsub
        _ = 1 := by simp
    omega
  refine ⟨X ⊓ MonoidHom.eqLocus φ.toMonoidHom (MonoidHom.id _), ?_, hX2.to_le inf_le_left,
    fun v hv => hv.2, fun a ha => ?_⟩
  · intro hbot
    have h : u ∈ X ⊓ MonoidHom.eqLocus φ.toMonoidHom (MonoidHom.id _) := ⟨huX, hφu⟩
    rw [hbot, Subgroup.mem_bot] at h
    exact hu1 h
  · have hφa : φ a = a := hAσ a ha
    rw [Subgroup.mem_normalizer_iff]
    intro v
    constructor
    · rintro ⟨hvX, hvφ⟩
      refine ⟨hAX a ha v hvX, ?_⟩
      have hv : φ v = v := hvφ
      show φ (a * v * a⁻¹) = a * v * a⁻¹
      rw [map_mul, map_mul, map_inv, hφa, hv]
    · rintro ⟨hvX, hvφ⟩
      refine ⟨?_, ?_⟩
      · have h := hAX a⁻¹ (inv_mem ha) _ hvX
        simpa [mul_assoc] using h
      · have h : φ (a * v * a⁻¹) = a * v * a⁻¹ := hvφ
        rw [map_mul, map_mul, map_inv, hφa] at h
        show φ v = v
        have h' := congrArg (fun z => a⁻¹ * z * a) h
        simpa [mul_assoc] using h'

end CFSG.LocalAnalysis.GLTheoremA.S265G

end
