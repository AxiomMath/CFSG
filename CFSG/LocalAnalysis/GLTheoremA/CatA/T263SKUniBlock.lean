module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263SKUniLift
import all CFSG.HardMathSupport.Solomon.Coordinator.LieComp.UnitaryInnerExport
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompAlgUnitaryBlock

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263.SK

open Polynomial Module Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne.KCPrimary CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp

section Abstract

variable {K : Type} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem inv_apply_of_scalar_on {W : Submodule K V} {g : LinearMap.GeneralLinearGroup K V} {l : Kˣ}
    (hg : ∀ v ∈ W, (g : Module.End K V) v = (l : K) • v) {v : V} (hv : v ∈ W) :
    ((g⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V) v = ((l⁻¹ : Kˣ) : K) • v := by
  have h1 : (g : Module.End K V) (((l⁻¹ : Kˣ) : K) • v) = v := by
    rw [hg _ (W.smul_mem ((l⁻¹ : Kˣ) : K) hv), smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      one_smul]
  calc ((g⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V) v
      = ((g⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V)
          ((g : Module.End K V) (((l⁻¹ : Kˣ) : K) • v)) := by rw [h1]
    _ = ((l⁻¹ : Kˣ) : K) • v := by
      rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel]
      rfl

theorem scalar_on_of_pow {W : Submodule K V} {B : LinearMap.GeneralLinearGroup K V} {p N : ℕ}
    (hpN : Nat.Coprime p N) {c₁ : Kˣ}
    (hBp : ∀ v, ((B ^ p : LinearMap.GeneralLinearGroup K V) : Module.End K V) v = (c₁ : K) • v)
    (hBN : ∀ v ∈ W, ((B ^ N : LinearMap.GeneralLinearGroup K V) : Module.End K V) v = v) :
    ∃ l : Kˣ, ∀ v ∈ W, (B : Module.End K V) v = (l : K) • v := by
  have hpow : ∀ m : ℕ, ∀ v, ((B ^ (p * m) : LinearMap.GeneralLinearGroup K V) : Module.End K V) v =
      ((c₁ ^ m : Kˣ) : K) • v := by
    intro m
    induction m with
    | zero => intro v; simp
    | succ m ih =>
      intro v
      rw [mul_add_one, pow_add, Units.val_mul, Module.End.mul_apply, hBp v, map_smul, ih v, smul_smul,
        pow_succ, Units.val_mul, mul_comm (c₁ : K)]
  have hNj : ∀ j : ℕ, ∀ v ∈ W, ((B ^ (N * j) : LinearMap.GeneralLinearGroup K V) : Module.End K V) v = v := by
    intro j
    induction j with
    | zero => intro v _; simp
    | succ j ih =>
      intro v hv
      rw [mul_add_one, pow_add, Units.val_mul, Module.End.mul_apply, hBN v hv, ih v hv]
  rcases Nat.lt_or_ge 1 N with hN | hN
  · obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hpN hN
    obtain ⟨j, hj⟩ : ∃ j, p * m = N * j + 1 :=
      ⟨p * m / N, by have := Nat.div_add_mod (p * m) N; omega⟩
    refine ⟨c₁ ^ m, fun v hv => ?_⟩
    have h1 := hpow m v
    rw [hj, pow_succ', Units.val_mul, Module.End.mul_apply, hNj j v hv] at h1
    exact h1
  · interval_cases N
    · have hp1 : p = 1 := by simpa using hpN
      subst hp1
      exact ⟨c₁, fun v _ => by simpa using hBp v⟩
    · exact ⟨1, fun v hv => by simpa using hBN v hv⟩

theorem units_eq_one_of_two_pow {E : Type*} [Field E] [CharP E 2] {u : Eˣ} {k : ℕ}
    (hu : u ^ (2 ^ k) = 1) : u = 1 := by
  have h1 : ((u : E) - 1) ^ (2 ^ k) = 0 := by
    rw [sub_pow_char_pow (p := 2), one_pow, ← Units.val_pow_eq_pow_val, hu, Units.val_one, sub_self]
  exact Units.ext (sub_eq_zero.1 ((pow_eq_zero_iff (pow_ne_zero k two_ne_zero)).1 h1))

variable [FiniteDimensional K V]

theorem pair_dual_closed {σ : K →+* K} {B : V →ₛₗ[σ] V →ₗ[K] K} {x : LinearMap.GeneralLinearGroup K V}
    (H : UnitaryPrimaryData σ B x) {a : K[X]} (ha : a ∈ primaryFactors (x : Module.End K V)) :
    ∀ b ∈ primaryFactors (x : Module.End K V), b ∈ ({a, dualPoly σ a} : Set K[X]) →
      dualPoly σ b ∈ ({a, dualPoly σ a} : Set K[X]) := by
  intro b _ hbO
  rcases hbO with rfl | hbO
  · exact Or.inr rfl
  · rw [Set.mem_singleton_iff] at hbO
    subst hbO
    exact Or.inl (dualPoly_dualPoly_of_mem H ha)

variable [Finite K]

theorem fix_of_scalar_on_block (h2 : (2 : K) = 0) {x : LinearMap.GeneralLinearGroup K V} {a : K[X]}
    (ha : a ∈ primaryFactors (x : Module.End K V)) {B g s zt : LinearMap.GeneralLinearGroup K V}
    (hgc : g ∈ gl_centralizer x) {l : Kˣ}
    (hB : ∀ v ∈ primaryComponent (x : Module.End K V) a, (B : Module.End K V) v = (l : K) • v)
    {μ : K} (hs : ∀ v, (s : Module.End K V) v = μ • v)
    (hzt : zt = B * g * B⁻¹ * g⁻¹ * s) {k : ℕ} (hzt2 : zt ^ (2 ^ k) = 1) :
    ∀ v ∈ primaryComponent (x : Module.End K V) a, (zt : Module.End K V) v = v := by
  have hact : ∀ v ∈ primaryComponent (x : Module.End K V) a, (zt : Module.End K V) v = μ • v := by
    intro v hv
    have hw : ((g⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V) v ∈
        primaryComponent (x : Module.End K V) a :=
      apply_mem_primaryComponent (mem_gl_centralizer.mp (inv_mem hgc)) hv
    have e1 := inv_apply_of_scalar_on hB hw
    have e2 : (g : Module.End K V) (((g⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V) v) = v := by
      rw [← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel]
      rfl
    have e3 : (B : Module.End K V) (((l⁻¹ : Kˣ) : K) • v) = v := by
      rw [map_smul, hB v hv, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
    rw [hzt]
    simp only [Units.val_mul, Module.End.mul_apply]
    rw [hs v, map_smul, map_smul, map_smul, map_smul, e1, map_smul, e2, e3]
  intro v hv
  exact SD.Lin.eq_of_smul_of_two_pow h2 ha hzt2 (c := algebraMap K (AdjoinRoot a) μ)
    (fun w => by rw [coe_algebraMap_smul_primaryComponent]; exact hact w w.2) ⟨v, hv⟩

theorem exists_good_block_uni (h2 : (2 : K) = 0) {ℓ f : ℕ} (hK : UnitaryFieldData ℓ f K)
    {x : LinearMap.GeneralLinearGroup K V} (hsq : Squarefree (minpoly K (x : Module.End K V)))
    {y : LinearMap.GeneralLinearGroup K V} (hyc : y ∈ gl_centralizer x) {k : ℕ}
    (hy : y ^ (2 ^ k) = 1) (hy1 : y ≠ 1)
    (hbad : ∀ b : primaryFactors (x : Module.End K V), ¬ IsGoodBlock hK x b →
      2 ≤ primaryMultiplicity (x : Module.End K V) (b : K[X]) →
      ∀ v ∈ primaryComponent (x : Module.End K V) (b : K[X]), (y : Module.End K V) v = v) :
    ∃ b : primaryFactors (x : Module.End K V), IsGoodBlock hK x b ∧
      ∃ v ∈ primaryComponent (x : Module.End K V) (b : K[X]), (y : Module.End K V) v ≠ v := by
  obtain ⟨b, hb, v, hv, hne⟩ := SD.Lin.exists_primary_ne_id hsq hy1
  refine ⟨⟨b, hb⟩, ?_, v, hv, hne⟩
  by_contra hng
  by_cases hm : primaryMultiplicity (x : Module.End K V) b ≤ 1
  · haveI : Fact (Irreducible b) := ⟨irreducible_of_mem_primaryFactors hb⟩
    obtain ⟨c, hc⟩ := SD.Lin.exists_smul_of_finrank_le_one hm
      (commutantRestrict b ⟨(y : Module.End K V), mem_commutant_of_mem_gl_centralizer hyc⟩)
    exact hne (SD.Lin.eq_of_smul_of_two_pow h2 hb hy (c := c) (fun w => congrArg Subtype.val (hc w))
      ⟨v, hv⟩)
  · exact hne (hbad ⟨b, hb⟩ hng (not_le.mp hm) v hv)

end Abstract

section BlockOrder

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem dvd_card_specialBlock_of_dvd {ℓ f : ℕ} {hK : UnitaryFieldData ℓ f K}
    {B : V →ₛₗ[hK.bar] V →ₗ[K] K} {x : LinearMap.GeneralLinearGroup K V}
    (H : UnitaryPrimaryData hK.bar B x) (a : primaryFactors (x : Module.End K V))
    (hm : 2 ≤ primaryMultiplicity (x : Module.End K V) (a : K[X])) {p : ℕ} (hp : p.Prime)
    (hpq : p ∣ Nat.card (AdjoinRoot (a : K[X])) - 1) :
    p ∣ Nat.card (specialBlock B x (a : K[X])) := by
  haveI : Finite (AdjoinRoot (a : K[X])) := Module.finite_of_finite K
  by_cases hself : dualPoly hK.bar (a : K[X]) = a
  · obtain ⟨hE, Hf, hHf, hHfl, ⟨e⟩⟩ :=
      nonempty_specialBlock_mulEquiv_sesqSU hself (selfDualPrimaryBlock H a hself)
    have hord := (CFSG.LinearGroups.unitary_full_group_order hE hHf hHfl
      (n := primaryMultiplicity (x : Module.End K V) (a : K[X])) rfl (by omega)).2.1
    have hcardE : Nat.card (AdjoinRoot (a : K[X])) = (ℓ ^ (f * (a : K[X]).natDegree)) ^ 2 := by
      rw [hE.card]
      exact pow_mul' _ _ _
    have hQ : 1 ≤ (ℓ ^ (f * (a : K[X]).natDegree)) ^ 2 :=
      Nat.one_le_pow _ _ (pow_pos hK.prime.pos _)
    have hpQ : (p : ℤ) ∣ (((ℓ ^ (f * (a : K[X]).natDegree) : ℕ) : ℤ) ^ 2 - (-1) ^ 2) := by
      rw [hcardE] at hpq
      have h1 := Int.natCast_dvd_natCast.2 hpq
      rw [Nat.cast_sub hQ, Nat.cast_pow, Nat.cast_one] at h1
      simpa using h1
    have hdvd : (((ℓ ^ (f * (a : K[X]).natDegree) : ℕ) : ℤ) ^ 2 - (-1) ^ 2) ∣
        ∏ i ∈ Finset.Icc 2 (primaryMultiplicity (x : Module.End K V) (a : K[X])),
          (((ℓ ^ (f * (a : K[X]).natDegree) : ℕ) : ℤ) ^ i - (-1) ^ i) :=
      Finset.dvd_prod_of_mem _ (Finset.mem_Icc.2 ⟨le_rfl, hm⟩)
    have h2 : (p : ℤ) ∣ (Nat.card (sesqSpecialUnitaryGroup Hf) : ℤ) := by
      rw [hord]
      exact Dvd.dvd.mul_left (hpQ.trans hdvd) _
    rw [Nat.card_congr e.toEquiv]
    exact Int.natCast_dvd_natCast.1 h2
  · obtain ⟨e⟩ := nonempty_specialBlock_mulEquiv_SL (pairedPrimaryBlock H a (Ne.symm hself))
    obtain ⟨g, hg⟩ := SD.Lin.exists_orderOf_eq_of_dvd_units hm hp hpq
    rw [Nat.card_congr e.toEquiv, ← hg]
    exact orderOf_dvd_natCard g

end BlockOrder

section Concrete

variable {n d : ℕ} {K : Type} [Field K] [Finite K] (h : UnitaryFieldData 2 n K)
  {A : primeFormUnitary h (idGram K d)}

local notation "𝒜" => Matrix.GeneralLinearGroup.toLin ((A : GL (Fin d) K))
local notation "𝒳" => ((Matrix.GeneralLinearGroup.toLin ((A : GL (Fin d) K)) :
  LinearMap.GeneralLinearGroup K (Fin d → K)) : Module.End K (Fin d → K))

theorem fix_of_scalar_conj {B : primeFormUnitary h (idGram K d)} {g zt : ↥(gramSU h (idGram K d))}
    (hgc : toLinSU h d g ∈ gl_centralizer 𝒜)
    (hs : (primeFormConjSU h (idGram K d) B g * g⁻¹)⁻¹ * zt ∈
      normOneScalars h (gramSU h (idGram K d)) d)
    {k : ℕ} (hzt2 : zt ^ (2 ^ k) = 1) {b : K[X]} (hb : b ∈ primaryFactors 𝒳) {l : Kˣ}
    (hl : ∀ v ∈ primaryComponent 𝒳 b,
      ((Matrix.GeneralLinearGroup.toLin (B : GL (Fin d) K) : LinearMap.GeneralLinearGroup K (Fin d → K)) :
        Module.End K (Fin d → K)) v = (l : K) • v) :
    ∀ v ∈ primaryComponent 𝒳 b, (toLinSU h d zt : Module.End K (Fin d → K)) v = v := by
  haveI : CharP K 2 := h.charP
  have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  obtain ⟨s, hsZ, rfl⟩ : ∃ s ∈ normOneScalars h (gramSU h (idGram K d)) d,
      zt = primeFormConjSU h (idGram K d) B g * g⁻¹ * s :=
    ⟨_, hs, (mul_inv_cancel_left _ _).symm⟩
  obtain ⟨c, -, -, hc⟩ := hsZ
  have hsact : ∀ v, (toLinSU h d s : Module.End K (Fin d → K)) v = (c : K) • v := by
    intro v
    change ((Matrix.GeneralLinearGroup.toLin ((s : ↥(gramSU h (idGram K d))) : GL (Fin d) K) :
      LinearMap.GeneralLinearGroup K (Fin d → K)) : Module.End K (Fin d → K)) v = _
    rw [hc]
    exact SD.Lin.glA_scalar_apply c v
  refine fix_of_scalar_on_block h2 hb hgc hl hsact ?_ (k := k) ?_
  · rw [map_mul, map_mul, map_inv, KD264Lie.toLinSU_primeFormConjSU h B g]
  · rw [← map_pow, hzt2, map_one]

theorem toLin_mem_unitaryCentralizer_of_comm {B : primeFormUnitary h (idGram K d)}
    (hBA : (B : GL (Fin d) K) * A = A * B) :
    Matrix.GeneralLinearGroup.toLin (B : GL (Fin d) K) ∈ unitaryCentralizer (idForm h d) 𝒜 := by
  refine mem_unitaryCentralizer.mpr ⟨(KCUnitaryModel.toLin_mem_sesqUnitaryGroup_iff _).mpr B.2, ?_⟩
  show ((Matrix.GeneralLinearGroup.toLin (B : GL (Fin d) K) : LinearMap.GeneralLinearGroup K (Fin d → K)) :
      Module.End K (Fin d → K)) * 𝒳 =
    𝒳 * ((Matrix.GeneralLinearGroup.toLin (B : GL (Fin d) K) : LinearMap.GeneralLinearGroup K (Fin d → K)) :
      Module.End K (Fin d → K))
  rw [← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul, hBA]

theorem bad_block_trivial_uni (hd : 3 ≤ d) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hK : p = 3 → 4 ≤ 2 ^ n)
    (H : UnitaryPrimaryData h.bar (idForm h d) 𝒜) (hAp : primeFormConjHom h (idGram K d) A ^ p = 1)
    {B : primeFormUnitary h (idGram K d)}
    (hBA : primeFormConjHom h (idGram K d) B * primeFormConjHom h (idGram K d) A =
      primeFormConjHom h (idGram K d) A * primeFormConjHom h (idGram K d) B)
    (hBp : primeFormConjHom h (idGram K d) B ^ p = 1) {g zt : ↥(gramSU h (idGram K d))}
    (hgc : toLinSU h d g ∈ gl_centralizer 𝒜)
    (hs : (primeFormConjSU h (idGram K d) B g * g⁻¹)⁻¹ * zt ∈
      normOneScalars h (gramSU h (idGram K d)) d)
    {k : ℕ} (hzt2 : zt ^ (2 ^ k) = 1) (b : primaryFactors 𝒳) (hng : ¬ IsGoodBlock h 𝒜 b)
    (hm2 : 2 ≤ primaryMultiplicity 𝒳 (b : K[X])) :
    ∀ v ∈ primaryComponent 𝒳 (b : K[X]), (toLinSU h d zt : Module.End K (Fin d → K)) v = v := by
  classical
  have hd0 : 0 < d := by omega
  have hbad : dualPoly h.bar (b : K[X]) = b ∧
      (primaryMultiplicity 𝒳 (b : K[X]), 2 ^ (n * (b : K[X]).natDegree)) ∈
        ({(2, 2), (2, 3), (3, 2)} : Set (ℕ × ℕ)) := by
    unfold IsGoodBlock at hng
    push Not at hng
    exact hng hm2
  have hQ : 2 ^ (n * (b : K[X]).natDegree) ≤ 3 := by
    have h3 := hbad.2
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at h3
    rcases h3 with ⟨-, h3⟩ | ⟨-, h3⟩ | ⟨-, h3⟩ <;> omega
  have hn1 : n = 1 := by
    have h1 := le_pow_natDegree h b
    have h2 := h.one_le
    by_contra hne
    have h4 : 4 ≤ 2 ^ n :=
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hcard : Nat.card K = 4 := by simp [h.card, hn1]
  have hp3 : 3 < p := by
    have hp3' : p ≠ 3 := fun h3 => by
      have := hK h3
      rw [hn1] at this
      norm_num at this
    have := hp.two_le
    omega
  obtain ⟨c, hAc⟩ := pow_scalar_of_conj_pow h hd A hAp
  obtain ⟨ζ, hζ⟩ := comm_scalar_of_conj_comm h hd hBA
  have hζ1 : ζ = 1 := SD.Lin.units_pow_eq_one_of_not_dvd (E := K) hp
    (by
      rw [hcard]
      intro hdvd
      have := Nat.le_of_dvd (by norm_num) hdvd
      omega)
    (SD.Lin.commutator_scalar_pow_eq_one hd0 hAc hζ)
  rw [hζ1, map_one] at hζ
  have hBA' : (B : GL (Fin d) K) * A = A * B := mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 hζ)
  have hβU := toLin_mem_unitaryCentralizer_of_comm h hBA'
  obtain ⟨c₁, hBc₁⟩ := pow_scalar_of_conj_pow h hd B hBp
  have hc₁3 : c₁ ^ 3 = 1 := by
    have h1 : Nat.card Kˣ = 3 := by rw [Nat.card_units, hcard]
    rw [← h1]
    exact pow_card_eq_one'
  have hβp : (Matrix.GeneralLinearGroup.toLin (B : GL (Fin d) K)) ^ p =
      Matrix.GeneralLinearGroup.toLin (Matrix.GeneralLinearGroup.scalar (Fin d) c₁) := by
    rw [← map_pow, hBc₁]
  have hβpv : ∀ v, (((Matrix.GeneralLinearGroup.toLin (B : GL (Fin d) K)) ^ p :
      LinearMap.GeneralLinearGroup K (Fin d → K)) : Module.End K (Fin d → K)) v = (c₁ : K) • v := by
    intro v
    rw [hβp]
    exact SD.Lin.glA_scalar_apply c₁ v
  have hβ3p : ((Matrix.GeneralLinearGroup.toLin (B : GL (Fin d) K)) ^ 3) ^ p = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hβp, ← map_pow, ← map_pow, hc₁3, map_one, map_one]
  have hfix3 : ∀ v ∈ primaryComponent 𝒳 (b : K[X]), (((Matrix.GeneralLinearGroup.toLin (B : GL (Fin d) K)) ^ 3 :
      LinearMap.GeneralLinearGroup K (Fin d → K)) : Module.End K (Fin d → K)) v = v :=
    fun v hv => apply_eq_of_exceptional H hp hp3 (pow_mem hβU 3) hβ3p b hbad.1 hbad.2 v hv
  have hcop : Nat.Coprime p 3 := (Nat.coprime_primes hp Nat.prime_three).2 (by omega)
  obtain ⟨l, hl⟩ := scalar_on_of_pow (W := primaryComponent 𝒳 (b : K[X])) hcop hβpv hfix3
  exact fix_of_scalar_conj h hgc hs hzt2 b.2 hl

theorem dvd_card_specialBlock_of_not_dvd (hd : 3 ≤ d) {p : ℕ} (hp : p.Prime)
    (H : UnitaryPrimaryData h.bar (idForm h d) 𝒜) (hAp : primeFormConjHom h (idGram K d) A ^ p = 1)
    {B : primeFormUnitary h (idGram K d)}
    (hBA : primeFormConjHom h (idGram K d) B * primeFormConjHom h (idGram K d) A =
      primeFormConjHom h (idGram K d) A * primeFormConjHom h (idGram K d) B)
    (hBp : primeFormConjHom h (idGram K d) B ^ p = 1) {g zt : ↥(gramSU h (idGram K d))}
    (hgc : toLinSU h d g ∈ gl_centralizer 𝒜)
    (hs : (primeFormConjSU h (idGram K d) B g * g⁻¹)⁻¹ * zt ∈
      normOneScalars h (gramSU h (idGram K d)) d)
    {k : ℕ} (hzt2 : zt ^ (2 ^ k) = 1) (a : primaryFactors 𝒳)
    (hpq : ¬ p ∣ Nat.card (AdjoinRoot (a : K[X])) - 1) {v : Fin d → K}
    (hv : v ∈ primaryComponent 𝒳 (a : K[X]))
    (hne : (toLinSU h d zt : Module.End K (Fin d → K)) v ≠ v) :
    p ∣ Nat.card (specialBlock (idForm h d) 𝒜 (a : K[X])) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (AdjoinRoot (a : K[X])) := Module.finite_of_finite K
  have hd0 : 0 < d := by omega
  obtain ⟨c, hAc⟩ := pow_scalar_of_conj_pow h hd A hAp
  obtain ⟨ζ, hζ⟩ := comm_scalar_of_conj_comm h hd hBA
  have hζ1 : ζ = 1 := SD.Lin.units_pow_eq_one_of_not_dvd (E := AdjoinRoot (a : K[X])) hp hpq
    (SD.Lin.commutator_scalar_pow_eq_one hd0 hAc hζ)
  rw [hζ1, map_one] at hζ
  have hBA' : (B : GL (Fin d) K) * A = A * B := mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 hζ)
  have hβU := toLin_mem_unitaryCentralizer_of_comm h hBA'
  have hβx := (mem_unitaryCentralizer.mp hβU).2
  obtain ⟨c₁, hBc₁⟩ := pow_scalar_of_conj_pow h hd B hBp
  have hβp : (Matrix.GeneralLinearGroup.toLin (B : GL (Fin d) K)) ^ p =
      Matrix.GeneralLinearGroup.toLin (Matrix.GeneralLinearGroup.scalar (Fin d) c₁) := by
    rw [← map_pow, hBc₁]
  have hβpv : ∀ w, (((Matrix.GeneralLinearGroup.toLin (B : GL (Fin d) K)) ^ p :
      LinearMap.GeneralLinearGroup K (Fin d → K)) : Module.End K (Fin d → K)) w = (c₁ : K) • w := by
    intro w
    rw [hβp]
    exact SD.Lin.glA_scalar_apply c₁ w
  obtain ⟨gB, hgB, hgBβ⟩ := exists_component H (pair_dual_closed H a.2) hβU
  have hgBc : gB ∈ gl_centralizer 𝒜 := supportedUnitary_le_gl_centralizer _ hgB
  have hpow : ∀ j : ℕ, ∀ b ∈ primaryFactors 𝒳,
      b ∈ ({(a : K[X]), dualPoly h.bar (a : K[X])} : Set K[X]) → ∀ w ∈ primaryComponent 𝒳 b,
        ((gB ^ j : LinearMap.GeneralLinearGroup K (Fin d → K)) : Module.End K (Fin d → K)) w =
          (((Matrix.GeneralLinearGroup.toLin (B : GL (Fin d) K)) ^ j :
            LinearMap.GeneralLinearGroup K (Fin d → K)) : Module.End K (Fin d → K)) w := by
    intro j
    induction j with
    | zero => intro b _ _ w _; rfl
    | succ j ih =>
      intro b hb hbO w hw
      rw [pow_succ, pow_succ, Units.val_mul, Units.val_mul, Module.End.mul_apply, Module.End.mul_apply,
        hgBβ b hb hbO w hw, ih b hb hbO _ (apply_mem_primaryComponent hβx hw)]
  have hc₁N : c₁ ^ Nat.card (AdjoinRoot (a : K[X]))ˣ = 1 := by
    apply Units.map_injective (f := (algebraMap K (AdjoinRoot (a : K[X])) : K →* AdjoinRoot (a : K[X])))
      (algebraMap K (AdjoinRoot (a : K[X]))).injective
    rw [map_pow, map_one]
    exact pow_card_eq_one'
  have hfS : gB ^ Nat.card (AdjoinRoot (a : K[X]))ˣ ∈ specialBlock (idForm h d) 𝒜 (a : K[X]) := by
    refine mem_specialBlock.mpr ⟨pow_mem hgB _, pow_mem hgBc _, ?_⟩
    have e : (⟨gB ^ Nat.card (AdjoinRoot (a : K[X]))ˣ, pow_mem hgBc _⟩ : gl_centralizer 𝒜) =
        ⟨gB, hgBc⟩ ^ Nat.card (AdjoinRoot (a : K[X]))ˣ := rfl
    rw [e, map_pow]
    exact pow_card_eq_one'
  have hfp : (gB ^ Nat.card (AdjoinRoot (a : K[X]))ˣ) ^ p = 1 := by
    refine eq_one_of_forall_apply_eq H.squarefree fun b hb w hw => ?_
    by_cases hbO : b ∈ ({(a : K[X]), dualPoly h.bar (a : K[X])} : Set K[X])
    · rw [← pow_mul, mul_comm, hpow _ b hb hbO w hw, pow_mul, hβp, ← map_pow, ← map_pow, hc₁N, map_one,
        map_one, Units.val_one, Module.End.one_apply]
    · exact (pow_mem (pow_mem hgB _) p).2 b hb hbO w hw
  have hf1 : gB ^ Nat.card (AdjoinRoot (a : K[X]))ˣ ≠ 1 := by
    intro h1
    have hβN : ∀ w ∈ primaryComponent 𝒳 (a : K[X]),
        (((Matrix.GeneralLinearGroup.toLin (B : GL (Fin d) K)) ^ Nat.card (AdjoinRoot (a : K[X]))ˣ :
          LinearMap.GeneralLinearGroup K (Fin d → K)) : Module.End K (Fin d → K)) w = w := by
      intro w hw
      rw [← hpow _ (a : K[X]) a.2 (Or.inl rfl) w hw, h1, Units.val_one, Module.End.one_apply]
    have hcop : Nat.Coprime p (Nat.card (AdjoinRoot (a : K[X]))ˣ) := by
      rw [Nat.card_units]
      exact (Nat.Prime.coprime_iff_not_dvd hp).2 hpq
    obtain ⟨l, hl⟩ := scalar_on_of_pow (W := primaryComponent 𝒳 (a : K[X])) hcop hβpv hβN
    exact hne (fix_of_scalar_conj h hgc hs hzt2 a.2 hl v hv)
  have hord : orderOf (⟨_, hfS⟩ : specialBlock (idForm h d) 𝒜 (a : K[X])) = p :=
    orderOf_eq_prime (Subtype.ext hfp) (fun h1 => hf1 (congrArg Subtype.val h1))
  rw [← hord]
  exact orderOf_dvd_natCard _

theorem exists_noncomm_uni (hd : 0 < d) (H : UnitaryPrimaryData h.bar (idForm h d) 𝒜) (hq : 2 ≤ 2 ^ n)
    (a : primaryFactors 𝒳) (ha : IsGoodBlock h 𝒜 a) {zt : ↥(gramSU h (idGram K d))}
    (hztc : toLinSU h d zt ∈ unitaryCentralizer (idForm h d) 𝒜) {k : ℕ} (hzt2 : zt ^ (2 ^ k) = 1)
    {v : Fin d → K} (hv : v ∈ primaryComponent 𝒳 (a : K[X]))
    (hne : (toLinSU h d zt : Module.End K (Fin d → K)) v ≠ v) :
    ∃ f ∈ KD264Lie.unitaryPreimageBlock h (x := 𝒜) (a : K[X]),
      (zt : primeFormP h (idGram K d)) * (f : primeFormP h (idGram K d)) ≠
        (f : primeFormP h (idGram K d)) * (zt : primeFormP h (idGram K d)) := by
  by_contra hcon
  push Not at hcon
  have hcomm : ∀ g' ∈ specialBlock (idForm h d) 𝒜 (a : K[X]), Commute (toLinSU h d zt) g' := by
    intro g' hg'
    obtain ⟨f, hf⟩ := mem_range_toLinSU (specialBlock_le_sesqSpecialUnitaryGroup_of_good H hq a ha hg')
    have hfF : f ∈ KD264Lie.unitaryPreimageBlock h (x := 𝒜) (a : K[X]) := by
      show toLinSU h d f ∈ specialBlock (idForm h d) 𝒜 (a : K[X])
      rw [hf]
      exact hg'
    have h1 := hcon f hfF
    have h2 : ((zt * f * zt⁻¹ : ↥(gramSU h (idGram K d))) : primeFormP h (idGram K d)) =
        (f : primeFormP h (idGram K d)) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, h1, mul_inv_cancel_right]
    have hz : f⁻¹ * (zt * f * zt⁻¹) ∈ normOneScalars h (gramSU h (idGram K d)) d :=
      QuotientGroup.eq.1 h2.symm
    have hconj : zt * f * zt⁻¹ = (f⁻¹ * (zt * f * zt⁻¹)) * f := by
      rw [(normOne_commute h hz f).eq, mul_inv_cancel_left]
    have hz1 := eq_one_of_conj_eq_mul h hd hzt2 hz hconj
    have h3 : zt * f = f * zt := by
      have : zt * f * zt⁻¹ = f := by rw [hconj, hz1, one_mul]
      exact mul_inv_eq_iff_eq_mul.1 this
    rw [← hf]
    show toLinSU h d zt * toLinSU h d f = toLinSU h d f * toLinSU h d zt
    rw [← map_mul, ← map_mul, h3]
  obtain ⟨c, hc⟩ := (commute_specialBlock_iff_scalar H hq a ha hztc).1 hcomm
  haveI : CharP K 2 := h.charP
  have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  have hzt2' : (toLinSU h d zt) ^ (2 ^ k) = 1 := by rw [← map_pow, hzt2, map_one]
  exact hne (SD.Lin.eq_of_smul_of_two_pow h2 a.2 hzt2' hc ⟨v, hv⟩)

theorem exists_decomp_uni (H : UnitaryPrimaryData h.bar (idForm h d) 𝒜) (hq : 2 ≤ 2 ^ n)
    (a : primaryFactors 𝒳) (ha : IsGoodBlock h 𝒜 a) {y : ↥(gramSU h (idGram K d))}
    (hyc : toLinSU h d y ∈ unitaryCentralizer (idForm h d) 𝒜) {k : ℕ} (hy : y ^ (2 ^ k) = 1) :
    ∃ w₁ ∈ KD264Lie.unitaryPreimageBlock h (x := 𝒜) (a : K[X]), ∃ w₂ : ↥(gramSU h (idGram K d)),
      toLinSU h d w₂ ∈ unitaryCentralizer (idForm h d) 𝒜 ∧
      (∀ f ∈ KD264Lie.unitaryPreimageBlock h (x := 𝒜) (a : K[X]), w₂ * f = f * w₂) ∧ y = w₂ * w₁ := by
  classical
  haveI : CharP K 2 := h.charP
  haveI : CharP (AdjoinRoot (a : K[X])) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AdjoinRoot (a : K[X]))).injective 2
  obtain ⟨w, hwO, hwy⟩ := exists_component H (pair_dual_closed H a.2) hyc
  have hwc : w ∈ gl_centralizer 𝒜 := supportedUnitary_le_gl_centralizer _ hwO
  have hyc' : toLinSU h d y ∈ gl_centralizer 𝒜 := hyc.2
  have hres : blockRestrict 𝒜 (a : K[X]) ⟨w, hwc⟩ = blockRestrict 𝒜 (a : K[X]) ⟨toLinSU h d y, hyc'⟩ :=
    blockGL_ext fun v hv => by
      rw [blockApply_blockRestrict, blockApply_blockRestrict]
      exact hwy (a : K[X]) a.2 (Or.inl rfl) v hv
  have hdet : blockDetHom 𝒜 (a : K[X]) ⟨w, hwc⟩ = 1 := by
    have h1 : (blockDetHom 𝒜 (a : K[X]) ⟨toLinSU h d y, hyc'⟩) ^ (2 ^ k) = 1 := by
      rw [← map_pow]
      have e : (⟨toLinSU h d y, hyc'⟩ : gl_centralizer 𝒜) ^ (2 ^ k) = 1 :=
        Subtype.ext (show (toLinSU h d y) ^ (2 ^ k) = 1 by rw [← map_pow, hy, map_one])
      rw [e, map_one]
    have h2 : blockDetHom 𝒜 (a : K[X]) ⟨w, hwc⟩ = blockDetHom 𝒜 (a : K[X]) ⟨toLinSU h d y, hyc'⟩ :=
      congrArg (blockGLDet 𝒳 (a : K[X])) hres
    rw [h2]
    exact units_eq_one_of_two_pow h1
  have hwS : w ∈ specialBlock (idForm h d) 𝒜 (a : K[X]) := mem_specialBlock.mpr ⟨hwO, hwc, hdet⟩
  obtain ⟨w₁, hw₁⟩ := mem_range_toLinSU (specialBlock_le_sesqSpecialUnitaryGroup_of_good H hq a ha hwS)
  have hw₁F : w₁ ∈ KD264Lie.unitaryPreimageBlock h (x := 𝒜) (a : K[X]) := by
    show toLinSU h d w₁ ∈ specialBlock (idForm h d) 𝒜 (a : K[X])
    rw [hw₁]
    exact hwS
  have hw₂U : toLinSU h d (y * w₁⁻¹) ∈ unitaryCentralizer (idForm h d) 𝒜 := by
    rw [map_mul, map_inv, hw₁]
    exact mul_mem hyc (inv_mem (specialBlock_le_unitaryCentralizer hwS))
  refine ⟨w₁, hw₁F, y * w₁⁻¹, hw₂U, ?_, (inv_mul_cancel_right y w₁).symm⟩
  have hw₂O : toLinSU h d (y * w₁⁻¹) ∈
      supportedUnitary (idForm h d) 𝒜 ({(a : K[X]), dualPoly h.bar (a : K[X])} : Set K[X])ᶜ := by
    refine ⟨hw₂U, fun b hb hbO v hv => ?_⟩
    have hbO' : b ∈ ({(a : K[X]), dualPoly h.bar (a : K[X])} : Set K[X]) := by
      by_contra hc
      exact hbO hc
    have hv' : ((w⁻¹ : LinearMap.GeneralLinearGroup K (Fin d → K)) : Module.End K (Fin d → K)) v ∈
        primaryComponent 𝒳 b :=
      apply_mem_primaryComponent (mem_gl_centralizer.mp (inv_mem hwc)) hv
    rw [map_mul, map_inv, hw₁, Units.val_mul, Module.End.mul_apply, ← hwy b hb hbO' _ hv',
      ← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel]
    rfl
  intro f hf
  have hfO : toLinSU h d f ∈
      supportedUnitary (idForm h d) 𝒜 ({(a : K[X]), dualPoly h.bar (a : K[X])} : Set K[X]) :=
    specialBlock_le_orbitFactor hf
  have hc := commute_of_disjoint H disjoint_compl_right hfO hw₂O
  apply toLinSU_injective
  rw [map_mul (toLinSU h d) (y * w₁⁻¹) f, map_mul (toLinSU h d) f (y * w₁⁻¹)]
  exact hc.eq.symm

end Concrete

end CFSG.LocalAnalysis.GLTheoremA.T263.SK

end
