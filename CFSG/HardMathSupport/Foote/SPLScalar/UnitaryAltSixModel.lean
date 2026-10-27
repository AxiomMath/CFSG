module

public import CFSG.HardMathSupport.Foote.SPLScalar.UnitaryAltSixField
public import CFSG.HardMathSupport.Foote.SPLScalar.UnitaryAltSixAbstract
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Permutation.UnitaryThreeRecognition.ModelFinite

public section

namespace CFSG.HardMathSupport.Foote.SPLScalar

open CFSG.UnitaryThreeRecognition.Model CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External

section SqrtNegOne

theorem exists_sqrt_neg_one {K : Type} [Field K] [Finite K] [CharP K 3] (σ : K ≃+* K) {q : ℕ}
    (hfix : Nat.card {x : K // σ x = x} = q) (hq : q % 4 = 1) :
    ∃ ι : K, ι ^ 2 = -1 ∧ σ ι = ι := by
  let F : Subfield K := RingHom.eqLocusField (σ : K →+* K) (RingHom.id K)
  have : Fintype F := Fintype.ofFinite F
  have hcard : Fintype.card F = q := by
    rw [← Nat.card_eq_fintype_card, ← hfix]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun x => Iff.rfl)
  have hsq : IsSquare (-1 : F) :=
    FiniteField.isSquare_neg_one_iff.mpr (by rw [hcard]; omega)
  obtain ⟨r, hr⟩ := hsq
  refine ⟨(r : K), ?_, r.2⟩
  have := congrArg (fun x : F => (x : K)) hr
  simp only [Subfield.coe_neg, Subfield.coe_mul, Subfield.coe_one] at this
  rw [sq, ← this]

end SqrtNegOne

section Coords

variable {K : Type} [Field K] (J : HermitianForm 3 K)
  (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])

omit hJ in
theorem coord_conj_val (z₀ z : Coord J) :
    ((z₀ * z * z₀⁻¹ : Coord J) : K × K) = rConj J.conj z₀.1.1 ((z : Coord J) : K × K) := by
  have ht := z₀.2
  rw [coord_mul_val J (z₀ * z) z₀⁻¹, coord_mul_val J z₀ z, coord_inv_val]
  refine Prod.ext ?_ ?_
  · simp only [rConj]
    ring
  · simp only [rConj, map_neg]
    linear_combination ht

omit hJ in
theorem torusAction_val' (k : Kˣ) (z : Coord J) :
    ((hermitianTorusAction J k z : Coord J) : K × K) = tAct J.conj (k : K) ((z : Coord J) : K × K) :=
  rfl

theorem conj_root_val (z₀ z : Coord J) (k : Kˣ) :
    root J hJ z₀ * torus J hJ k * root J hJ z * (root J hJ z₀ * torus J hJ k)⁻¹ =
      root J hJ (z₀ * hermitianTorusAction J k z * z₀⁻¹) := by
  rw [map_mul, map_mul, map_inv]
  calc root J hJ z₀ * torus J hJ k * root J hJ z * (root J hJ z₀ * torus J hJ k)⁻¹
      = root J hJ z₀ * (torus J hJ k * root J hJ z * (torus J hJ k)⁻¹) * (root J hJ z₀)⁻¹ := by
        group
    _ = _ := by rw [torus_mul_root_mul_inv J hJ k z]

omit hJ in
theorem conj_root_coord (z₀ z : Coord J) (k : Kˣ) :
    ((z₀ * hermitianTorusAction J k z * z₀⁻¹ : Coord J) : K × K) =
      wAct J.conj (k : K) z₀.1.1 ((z : Coord J) : K × K) := by
  rw [coord_conj_val, torusAction_val']
  rfl

end Coords

section Main

variable {K : Type} [Field K] [Finite K] (J : HermitianForm 3 K)
  (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])

omit [Finite K] in
theorem root_smul_ne_self {z : Coord J} (hz : z ≠ 1) {x : IsoPoint J} (hx : x ≠ pinf J hJ) :
    root J hJ z • x ≠ x := by
  intro h
  obtain ⟨r, _, huniq⟩ := rootGroup_regular J hJ x x hx hx
  have h1 := huniq (rootCoord J hJ z) (by simpa using h)
  have h2 := huniq 1 (one_smul _ _)
  exact hz ((rootCoord J hJ).injective (h1.trans (h2.symm.trans (map_one _).symm)))

omit [Finite K] in
theorem smul_pinf_of_mem_normalizer {E : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)}
    (hER : E ≤ rootGroup J hJ) {z : Coord J} (hz : z ≠ 1) (hzE : root J hJ z ∈ E)
    {w : ProjectiveSpecialUnitaryMatrixGroup J}
    (hw : w ∈ Subgroup.normalizer (E : Set (ProjectiveSpecialUnitaryMatrixGroup J))) :
    w • pinf J hJ = pinf J hJ := by
  by_contra hne
  have hwinv : w⁻¹ ∈ Subgroup.normalizer (E : Set (ProjectiveSpecialUnitaryMatrixGroup J)) :=
    (Subgroup.normalizer _).inv_mem hw
  have h1 : w⁻¹ * root J hJ z * w⁻¹⁻¹ ∈ E :=
    (Subgroup.mem_normalizer_iff.mp hwinv _).mp hzE
  have h2 : (w⁻¹ * root J hJ z * w⁻¹⁻¹) • pinf J hJ = pinf J hJ :=
    rootGroup_le_stabilizer J hJ (hER h1)
  have h3 : root J hJ z • (w • pinf J hJ) = w • pinf J hJ := by
    have := congrArg (fun x => w • x) h2
    simpa [mul_smul] using this
  exact root_smul_ne_self J hJ hz hne h3

end Main

section Decomp

variable {K : Type} [Field K] [Finite K] (J : HermitianForm 3 K)
  (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) {q : ℕ}
  (hK : Nat.card K = q ^ 2) (hfix : Nat.card {x : K // J.conj x = x} = q)

include hK hfix

theorem exists_root_torus_of_smul_pinf {w : ProjectiveSpecialUnitaryMatrixGroup J}
    (hw : w • pinf J hJ = pinf J hJ) :
    ∃ (z₀ : Coord J) (k : Kˣ), w = root J hJ z₀ * torus J hJ k := by
  have hmem : w ∈ ((rootGroup J hJ ⊔ torusGroup J hJ :
      Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) : Set _) := by
    rw [rootGroup_sup_torusGroup J hJ q hK hfix]
    exact hw
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _
    (torusGroup_le_normalizer_rootGroup J hJ)] at hmem
  obtain ⟨r, hr, h, hh, rfl⟩ := hmem
  obtain ⟨z₀, rfl⟩ := (mem_rootGroup J hJ).1 hr
  obtain ⟨k, rfl⟩ := (mem_torusGroup J hJ).1 hh
  exact ⟨z₀, k, rfl⟩

end Decomp

section Final

variable {K : Type} [Field K] [Finite K] (J : HermitianForm 3 K)
  (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) {q : ℕ}
  (hK : Nat.card K = q ^ 2) (hfix : Nat.card {x : K // J.conj x = x} = q)

omit [Finite K] in
theorem coord_pow_fst (z : Coord J) (n : ℕ) : ((z ^ n : Coord J) : K × K).1 = n * z.1.1 := by
  induction n with
  | zero => simp [coord_one_val]
  | succ n ih =>
    rw [pow_succ, coord_mul_val, ih]
    simp only [Nat.cast_succ]
    ring

omit [Finite K] in
theorem root_mem_centralizer_of_fst_eq_zero {z : Coord J} (h0 : z.1.1 = 0) :
    root J hJ z ∈ Subgroup.centralizer
      (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) := by
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  obtain ⟨z', rfl⟩ := (mem_rootGroup J hJ).1 hg
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  rw [coord_mul_val, coord_mul_val, h0]
  refine Prod.ext ?_ ?_
  · simp
  · simp only [map_zero, mul_zero, zero_mul, sub_zero, add_comm]

include hK hfix

theorem singerConclusion_of_rootGroup [CharP K 3] (hq8 : q % 8 = 1)
    {E : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)} (hER : E ≤ rootGroup J hJ)
    (hE3 : ∀ a ∈ E, a ^ 3 = 1) (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hE9 : Nat.card E = 9)
    (hEZ : ¬ E ≤ Subgroup.centralizer
      (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)))
    {w : ProjectiveSpecialUnitaryMatrixGroup J}
    (hw : w ∈ Subgroup.normalizer (E : Set (ProjectiveSpecialUnitaryMatrixGroup J)))
    (hw2 : ∀ a ∈ E, w ^ 2 * a * (w ^ 2)⁻¹ = a⁻¹) : SingerConclusion E := by
  obtain ⟨ι, hι, hιF⟩ := exists_sqrt_neg_one J.conj hfix (by omega)
  obtain ⟨e, heE, hec⟩ : ∃ e ∈ E, e ∉ Subgroup.centralizer
      (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) := by
    by_contra h
    push Not at h
    exact hEZ fun e he => h e he
  obtain ⟨z₁, rfl⟩ := (mem_rootGroup J hJ).1 (hER heE)
  have ha₁ : z₁.1.1 ≠ 0 := fun h0 => hec (root_mem_centralizer_of_fst_eq_zero J hJ h0)
  have hz₁ : z₁ ≠ 1 := by
    intro h
    apply ha₁
    rw [h]
    rfl
  have hwpinf := smul_pinf_of_mem_normalizer J hJ hER hz₁ heE hw
  obtain ⟨z₀, k, rfl⟩ := exists_root_torus_of_smul_pinf J hJ hK hfix hwpinf
  set x := root J hJ z₁ with hx
  set z₂ : Coord J := z₀ * hermitianTorusAction J k z₁ * z₀⁻¹ with hz₂
  have hy : root J hJ z₀ * torus J hJ k * x * (root J hJ z₀ * torus J hJ k)⁻¹ = root J hJ z₂ :=
    conj_root_val J hJ z₀ z₁ k
  have hyE : root J hJ z₂ ∈ E := by
    rw [← hy]
    exact (Subgroup.mem_normalizer_iff.mp hw _).mp heE
  have hW : wAct J.conj (k : K) z₀.1.1 (wAct J.conj (k : K) z₀.1.1 ((z₁ : Coord J) : K × K)) =
      (-z₁.1.1, J.conj z₁.1.2) := by
    have h1 := hw2 x heE
    have h2 : (root J hJ z₀ * torus J hJ k) ^ 2 * x * ((root J hJ z₀ * torus J hJ k) ^ 2)⁻¹ =
        root J hJ (z₀ * hermitianTorusAction J k z₂ * z₀⁻¹) := by
      have : (root J hJ z₀ * torus J hJ k) ^ 2 * x * ((root J hJ z₀ * torus J hJ k) ^ 2)⁻¹ =
          (root J hJ z₀ * torus J hJ k) *
            (root J hJ z₀ * torus J hJ k * x * (root J hJ z₀ * torus J hJ k)⁻¹) *
            (root J hJ z₀ * torus J hJ k)⁻¹ := by
        simp only [pow_two, mul_inv_rev, mul_assoc]
      rw [this, hy]
      exact conj_root_val J hJ z₀ z₂ k
    rw [h2] at h1
    have h3 := root_injective J hJ (h1.trans (map_inv (root J hJ) z₁).symm)
    have h4 := congrArg (fun z : Coord J => (z : K × K)) h3
    simp only [conj_root_coord, coord_inv_val] at h4
    rw [hz₂, conj_root_coord] at h4
    exact h4
  have hy_val : ((z₂ : Coord J) : K × K) =
      wAct J.conj (k : K) z₀.1.1 ((z₁ : Coord J) : K × K) := conj_root_coord J z₀ z₁ k
  obtain ⟨hκ2, k₈, hk₈, s', hE1, hE2⟩ :=
    singer_field_core J.conj J.conj_involutive hι hιF k.ne_zero ha₁ z₁.2 hW
  have h2 : (2 : K) ≠ 0 := by
    rw [two_eq_neg_one]
    exact neg_ne_zero.mpr one_ne_zero
  have ht' : ∃ t' : K, t' + J.conj t' + s' * J.conj s' = 0 := by
    refine ⟨-(s' * J.conj s') / 2, ?_⟩
    rw [map_div₀, map_neg, map_mul, J.conj_involutive, map_ofNat]
    field_simp
    ring
  obtain ⟨t', ht'⟩ := ht'
  let z' : Coord J := ⟨(s', t'), ht'⟩
  let k₈u : Kˣ := Units.mk0 k₈ hk₈
  have hcx : root J hJ z' * torus J hJ k₈u * x * (root J hJ z' * torus J hJ k₈u)⁻¹ =
      x * (root J hJ z₂)⁻¹ := by
    rw [conj_root_val J hJ z' z₁ k₈u, ← map_inv, ← map_mul]
    congr 1
    apply Subtype.ext
    rw [conj_root_coord J z' z₁ k₈u, coord_mul_val J z₁ z₂⁻¹, coord_inv_val, hy_val]
    show wAct J.conj k₈ s' _ = _
    rw [hE1]
    refine Prod.ext ?_ ?_
    · simp only
      ring
    · simp only [map_neg]
      ring
  have hcy : root J hJ z' * torus J hJ k₈u * root J hJ z₂ * (root J hJ z' * torus J hJ k₈u)⁻¹ =
      x * root J hJ z₂ := by
    rw [conj_root_val J hJ z' z₂ k₈u, ← map_mul]
    congr 1
    apply Subtype.ext
    rw [conj_root_coord J z' z₂ k₈u, coord_mul_val J z₁ z₂, hy_val]
    show wAct J.conj k₈ s' _ = _
    rw [hE2]
  have hx1 : x ≠ 1 := by
    intro h
    apply hz₁
    exact root_injective J hJ (h.trans (map_one _).symm)
  have hyx : root J hJ z₂ ∉ Subgroup.zpowers x := by
    intro hmem
    have hfin : IsOfFinOrder x := isOfFinOrder_iff_pow_eq_one.mpr ⟨3, by norm_num, hE3 x heE⟩
    rw [← hfin.mem_powers_iff_mem_zpowers, Submonoid.mem_powers_iff] at hmem
    obtain ⟨m, hm⟩ := hmem
    have h1 : z₁ ^ m = z₂ := root_injective J hJ (by rw [map_pow]; exact hm)
    have h2' := congrArg (fun z : Coord J => (z : K × K).1) h1
    simp only [coord_pow_fst] at h2'
    have h3 : (z₂ : K × K).1 = z₁.1.1 * (k * (J.conj (k : K))⁻¹ ^ 2) := by
      rw [hy_val]
      simp only [wAct, rConj, tAct]
      ring
    rw [h3] at h2'
    have hκm : (k : K) * (J.conj (k : K))⁻¹ ^ 2 = (m : K) := by
      have : z₁.1.1 * ((k : K) * (J.conj (k : K))⁻¹ ^ 2 - m) = 0 := by
        linear_combination -h2'
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left ha₁)
    rw [hκm] at hκ2
    have hdvd : ((m ^ 2 + 1 : ℕ) : K) = 0 := by
      push_cast
      linear_combination hκ2
    rw [CharP.cast_eq_zero_iff K 3] at hdvd
    have : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega
    rcases this with h | h | h <;> simp [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.pow_mod, h] at hdvd
  exact singerConclusion_of_action E hE9 x (root J hJ z₂) _ heE hyE (hE3 x heE) (hE3 _ hyE)
    (hEc x heE _ hyE) hx1 hyx hcx hcy

end Final

end CFSG.HardMathSupport.Foote.SPLScalar
