module

public import CFSG.CGT.Foote82.Lemma62Extraspecial
import CFSG.Quasithin.Background.G11Basic
import TauCeti.RepresentationTheory.CharacterTable.Solvable

public section

open scoped commutatorElement

namespace CFSG.CGT.Foote82

open CFSG.Open CFSG.Quasithin.G11

namespace Endgame

section LinearAlgebra

private theorem matrix_aux {F : Type*} [Field F] {q : ℕ} (hq : (q : F) ≠ 0) (hqodd : Odd q)
    (M : Matrix (Fin 2) (Fin 2) F) (hdet : M.det = 1) (hMq : M ^ q = 1) (hM : M ≠ 1) :
    (∀ v : Fin 2 → F, M.mulVec v = v → v = 0) ∧
      ¬ ∃ c : F, M = c • (1 : Matrix (Fin 2) (Fin 2) F) := by
  constructor
  · intro v hv
    by_contra hv0
    obtain ⟨a, b, c, d, rfl⟩ : ∃ a b c d : F, M = !![a, b; c, d] :=
      ⟨M 0 0, M 0 1, M 1 0, M 1 1, Matrix.eta_fin_two M⟩
    rw [Matrix.det_fin_two_of] at hdet
    have h0 : a * v 0 + b * v 1 = v 0 := by
      have := congrFun hv 0
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
    have h1 : c * v 0 + d * v 1 = v 1 := by
      have := congrFun hv 1
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
    have htr : a + d = 2 := by
      have e0 : (2 - a - d) * v 0 = 0 := by
        linear_combination (d - 1) * h0 - b * h1 - v 0 * hdet
      have e1 : (2 - a - d) * v 1 = 0 := by
        linear_combination (a - 1) * h1 - c * h0 - v 1 * hdet
      have hne : v 0 ≠ 0 ∨ v 1 ≠ 0 := by
        by_contra hcon
        rw [not_or, not_not, not_not] at hcon
        exact hv0 (funext fun i => by fin_cases i <;> simp [hcon.1, hcon.2])
      rcases hne with h | h
      · have := (mul_eq_zero.1 e0).resolve_right h
        linear_combination -this
      · have := (mul_eq_zero.1 e1).resolve_right h
        linear_combination -this
    set N : Matrix (Fin 2) (Fin 2) F := !![a, b; c, d] - 1 with hN
    have hN2 : N * N = 0 := by
      have hd : d = 2 - a := by linear_combination htr
      subst hd
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [hN, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] <;>
        first | (linear_combination -hdet) | ring
    have hM' : !![a, b; c, d] = 1 + N := by rw [hN]; abel
    have hpow : ∀ n : ℕ, !![a, b; c, d] ^ n = 1 + (n : F) • N := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [pow_succ, ih, hM']
        have : (1 + (n : F) • N) * (1 + N) = 1 + ((n : F) + 1) • N + (n : F) • (N * N) := by
          simp only [mul_add, add_mul, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, add_smul,
            one_smul]
          abel
        rw [this, hN2]
        simp
    rw [hpow q] at hMq
    have hqN : (q : F) • N = 0 := by
      have := congrArg (fun X => X - 1) hMq
      simpa using this
    have hN0 : N = 0 := by
      rcases smul_eq_zero.1 hqN with h | h
      · exact absurd h hq
      · exact h
    apply hM
    rw [hM', hN0, add_zero]
  · rintro ⟨c, rfl⟩
    have hc2 : c ^ 2 = 1 := by
      have := hdet
      simpa [Matrix.det_smul] using this
    have hcq : c ^ q = 1 := by
      have := congrFun (congrFun hMq 0) 0
      simpa [smul_pow] using this
    obtain ⟨m, rfl⟩ := hqodd
    have : c ^ (2 * m + 1) = c := by
      rw [pow_succ, pow_mul, hc2, one_pow, one_mul]
    rw [this] at hcq
    exact hM (by rw [hcq, one_smul])

private theorem la_key {p q : ℕ} [Fact p.Prime] (hqodd : Odd q) (hqp : ¬ p ∣ q)
    {A : Type*} [AddCommGroup A] [Module (ZMod p) A] [Module.Finite (ZMod p) A]
    (hA : Module.finrank (ZMod p) A = 2)
    (T : A ≃ₗ[ZMod p] A) (hdet : LinearEquiv.det T = 1) (hTq : T ^ q = 1) (hT1 : T ≠ 1) :
    (∀ a, T a = a → a = 0) ∧ ∃ a, LinearIndependent (ZMod p) ![a, T a] := by
  have hq0 : (q : ZMod p) ≠ 0 := by
    rwa [Ne, ZMod.natCast_eq_zero_iff]
  let b := Module.finBasisOfFinrankEq (ZMod p) A hA
  let M := LinearMap.toMatrix b b (T : A →ₗ[ZMod p] A)
  have hMdet : M.det = 1 := by
    have h1 := LinearEquiv.coe_det T
    rw [hdet] at h1
    simpa [M, LinearMap.det_toMatrix] using h1.symm
  have hTq' : (T : A →ₗ[ZMod p] A) ^ q = 1 := by
    have := map_pow (LinearEquiv.automorphismGroup.toLinearMapMonoidHom (R := ZMod p) (M := A)) T q
    rw [hTq, map_one] at this
    exact this.symm
  have hMq : M ^ q = 1 := by
    change (LinearMap.toMatrix b b (T : A →ₗ[ZMod p] A)) ^ q = 1
    rw [LinearMap.toMatrix_pow, hTq', LinearMap.toMatrix_one]
  have hM1 : M ≠ 1 := by
    intro h
    apply hT1
    have : (T : A →ₗ[ZMod p] A) = 1 := by
      apply (LinearMap.toMatrix b b).injective
      simpa [M] using h
    ext a
    exact congrArg (fun f : A →ₗ[ZMod p] A => f a) this
  obtain ⟨h1, h2⟩ := matrix_aux hq0 hqodd M hMdet hMq hM1
  refine ⟨fun a ha => ?_, ?_⟩
  · have := h1 (b.repr a) (by rw [LinearMap.toMatrix_mulVec_repr]; simp [ha])
    exact b.repr.injective (by ext i; simpa using congrFun this i)
  · by_contra hcon
    have hcon' : ∀ a, ¬ LinearIndependent (ZMod p) ![a, (T : A →ₗ[ZMod p] A) a] := fun a h =>
      hcon ⟨a, h⟩
    obtain ⟨c, hc⟩ := LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent hcon'
    apply h2
    refine ⟨c, ?_⟩
    change (LinearMap.toMatrix b b (T : A →ₗ[ZMod p] A)) = c • 1
    rw [hc, map_smul, LinearMap.toMatrix_one]

end LinearAlgebra

section GroupTheory

variable {Γ : Type*} [Group Γ]

private abbrev AbK (K : Subgroup Γ) : Type _ := Additive (Abelianization ↥K)

private def ι (K : Subgroup Γ) (k : ↥K) : AbK K := Additive.ofMul (Abelianization.of k)

private theorem ι_mul (K : Subgroup Γ) (a b : ↥K) : ι K (a * b) = ι K a + ι K b := rfl

private theorem ι_one (K : Subgroup Γ) : ι K 1 = 0 := rfl

private theorem ι_inv (K : Subgroup Γ) (a : ↥K) : ι K a⁻¹ = - ι K a := rfl

private theorem ι_pow (K : Subgroup Γ) (a : ↥K) (n : ℕ) : ι K (a ^ n) = n • ι K a := rfl

private theorem ι_surjective (K : Subgroup Γ) : Function.Surjective (ι K) := fun a => by
  obtain ⟨k, hk⟩ := QuotientGroup.mk_surjective (s := commutator ↥K) (Additive.toMul a)
  exact ⟨k, (congrArg Additive.ofMul hk).trans (ofMul_toMul a)⟩

private theorem ι_eq_zero_iff (K : Subgroup Γ) (k : ↥K) : ι K k = 0 ↔ (k : Γ) ∈ ⁅K, K⁆ := by
  rw [← Subgroup.map_subtype_commutator K]
  have : (k : Γ) = K.subtype k := rfl
  rw [this, Subgroup.mem_map_iff_mem K.subtype_injective,
    ← QuotientGroup.eq_one_iff (N := commutator ↥K)]
  exact ofMul_eq_zero

private theorem card_AbK (K : Subgroup Γ) {p : ℕ} (hK : Nat.card K = p ^ 3)
    (hK' : Nat.card (⁅K, K⁆ : Subgroup Γ) = p) (hp : 0 < p) : Nat.card (AbK K) = p ^ 2 := by
  have h1 : Nat.card (commutator ↥K) = p := by
    rw [← hK', ← Subgroup.map_subtype_commutator K]
    exact (Subgroup.card_map_of_injective K.subtype_injective).symm
  have h2 : (commutator ↥K).index * Nat.card (commutator ↥K) = Nat.card ↥K :=
    Subgroup.index_mul_card _
  have h3 : Nat.card (AbK K) = (commutator ↥K).index := by
    rw [Nat.card_congr (Additive.toMul : AbK K ≃ Abelianization ↥K)]
    rfl
  rw [h3]
  rw [h1, hK] at h2
  have : (commutator ↥K).index * p = p ^ 2 * p := by rw [h2]; ring
  exact Nat.eq_of_mul_eq_mul_right hp this

private theorem exponent_AbK (K : Subgroup Γ) {p : ℕ} (hexp : ∀ k ∈ K, k ^ p = 1) (a : AbK K) :
    p • a = 0 := by
  obtain ⟨k, rfl⟩ := ι_surjective K a
  rw [← ι_pow, show k ^ p = 1 from Subtype.ext (hexp k k.2), ι_one]

private theorem finrank_AbK {p : ℕ} [Fact p.Prime] (K : Subgroup Γ) [Module (ZMod p) (AbK K)]
    [Finite (AbK K)] (hcard : Nat.card (AbK K) = p ^ 2) :
    Module.finrank (ZMod p) (AbK K) = 2 := by
  have : Fintype (AbK K) := Fintype.ofFinite _
  have h := Module.card_eq_pow_finrank (K := ZMod p) (V := AbK K)
  rw [ZMod.card, ← Nat.card_eq_fintype_card, hcard] at h
  exact (Nat.pow_right_injective (Fact.out : p.Prime).two_le h).symm

private noncomputable def actAdd (K : Subgroup Γ) (g : Subgroup.normalizer (K : Set Γ)) :
    AbK K ≃+ AbK K :=
  MulEquiv.toAdditive ((K.normalizerMonoidHom g).abelianizationCongr)

private theorem actAdd_ι (K : Subgroup Γ) (g : Subgroup.normalizer (K : Set Γ)) (k : ↥K) :
    actAdd K g (ι K k) = ι K (K.normalizerMonoidHom g k) := rfl

private theorem actAdd_one (K : Subgroup Γ) (a : AbK K) : actAdd K 1 a = a := by
  obtain ⟨k, rfl⟩ := ι_surjective K a
  rw [actAdd_ι, map_one]
  rfl

private theorem actAdd_mul (K : Subgroup Γ) (g h : Subgroup.normalizer (K : Set Γ)) (a : AbK K) :
    actAdd K (g * h) a = actAdd K g (actAdd K h a) := by
  obtain ⟨k, rfl⟩ := ι_surjective K a
  rw [actAdd_ι, actAdd_ι, actAdd_ι, map_mul]
  rfl

private noncomputable def actLin (K : Subgroup Γ) (p : ℕ) [Module (ZMod p) (AbK K)]
    (g : Subgroup.normalizer (K : Set Γ)) : AbK K ≃ₗ[ZMod p] AbK K :=
  { actAdd K g with map_smul' := fun c x => ZMod.map_smul (actAdd K g) c x }

private noncomputable def rhoLin (K : Subgroup Γ) (p : ℕ) [Module (ZMod p) (AbK K)] :
    Subgroup.normalizer (K : Set Γ) →* (AbK K ≃ₗ[ZMod p] AbK K) where
  toFun := actLin K p
  map_one' := LinearEquiv.ext fun a => actAdd_one K a
  map_mul' g h := LinearEquiv.ext fun a => actAdd_mul K g h a

private theorem exists_prime_dvd_card_of_not_solvable {R : Type*} [Group R] [Finite R] {p : ℕ}
    (hp : p.Prime) (hns : ¬ Group.IsSolvable R) :
    ∃ q : ℕ, q.Prime ∧ q ∣ Nat.card R ∧ q ≠ 2 ∧ q ≠ p := by
  by_contra hcon
  apply hns
  have hn0 : Nat.card R ≠ 0 := Nat.card_pos.ne'
  refine TauCeti.isSolvable_of_card_dvd_prime_pow_mul_prime_pow Nat.prime_two hp
    (a := Nat.card R) (b := Nat.card R) ?_
  have h2n : 2 ^ Nat.card R ≠ 0 := pow_ne_zero _ two_ne_zero
  have hpn : p ^ Nat.card R ≠ 0 := pow_ne_zero _ hp.ne_zero
  rw [← Nat.factorization_prime_le_iff_dvd hn0 (mul_ne_zero h2n hpn)]
  intro r hr
  by_cases hdvd : r ∣ Nat.card R
  · have hr' : r = 2 ∨ r = p := by
      by_contra h
      push Not at h
      exact hcon ⟨r, hr, hdvd, h.1, h.2⟩
    have hlt := Nat.factorization_lt r hn0
    rcases hr' with rfl | rfl
    · rw [Nat.factorization_mul h2n hpn]
      simp only [Finsupp.add_apply, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
        Nat.prime_two.factorization_self]
      omega
    · rw [Nat.factorization_mul h2n hpn]
      simp only [Finsupp.add_apply, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
        hr.factorization_self]
      omega
  · rw [Nat.factorization_eq_zero_of_not_dvd hdvd]
    exact Nat.zero_le _

private theorem commutator_le_self' (K : Subgroup Γ) : ⁅K, K⁆ ≤ K := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  rw [commutatorElement_def]
  exact K.mul_mem (K.mul_mem (K.mul_mem ha hb) (K.inv_mem ha)) (K.inv_mem hb)

private theorem conj_mem' {K : Subgroup Γ} {g : Γ} (hg : g ∈ Subgroup.normalizer (K : Set Γ))
    {k : Γ} (hk : k ∈ K) : g * k * g⁻¹ ∈ K :=
  (Subgroup.mem_set_normalizer_iff.1 hg k).1 hk

private theorem exists_pair_of_linearIndep (K : Subgroup Γ) {p : ℕ} [hp : Fact p.Prime]
    [Module (ZMod p) (AbK K)] [Finite (AbK K)] (hfr : Module.finrank (ZMod p) (AbK K) = 2)
    (hfrat : ∀ H : Subgroup Γ, H ≤ K → H ⊔ ⁅K, K⁆ = K → H = K)
    (x : Γ) (hx : x ∈ Subgroup.normalizer (K : Set Γ)) (hx' : x⁻¹ ∈ Subgroup.normalizer (K : Set Γ))
    (T : AbK K ≃ₗ[ZMod p] AbK K)
    (hT : ∀ (k : ↥K) (h : x * k * x⁻¹ ∈ K), T (ι K k) = ι K ⟨x * k * x⁻¹, h⟩)
    (hfix : ∀ a, T a = a → a = 0) (a₀ : AbK K) (ha₀ : LinearIndependent (ZMod p) ![a₀, T a₀]) :
    ∃ k₀ ∈ K, K ≤ Subgroup.closure {x, k₀ * x * k₀⁻¹} := by
  let f : AbK K →ₗ[ZMod p] AbK K := T.symm.toLinearMap - LinearMap.id
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro b hb
    have h1 : T.symm b = b := sub_eq_zero.1 (by simpa [f] using hb)
    refine hfix b ?_
    conv_lhs => rw [← h1]
    exact T.apply_symm_apply b
  obtain ⟨b, hb⟩ := LinearMap.injective_iff_surjective.1 hinj a₀
  obtain ⟨k₀, rfl⟩ := ι_surjective K b
  have hb' : T.symm (ι K k₀) - ι K k₀ = a₀ := by simpa [f] using hb
  have hxk : ∀ k : Γ, k ∈ K → x * k * x⁻¹ ∈ K := fun k hk => conj_mem' hx hk
  have hxk' : ∀ k : Γ, k ∈ K → x⁻¹ * k * x ∈ K := fun k hk => by
    simpa using conj_mem' hx' hk
  have hy : x⁻¹ * k₀ * x * k₀⁻¹ ∈ K := K.mul_mem (hxk' k₀ k₀.2) (K.inv_mem k₀.2)
  have hy' : x * (x⁻¹ * k₀ * x * k₀⁻¹) * x⁻¹ ∈ K := hxk _ hy
  let yK : ↥K := ⟨x⁻¹ * k₀ * x * k₀⁻¹, hy⟩
  let y'K : ↥K := ⟨x * (x⁻¹ * k₀ * x * k₀⁻¹) * x⁻¹, hy'⟩
  have hι_y : ι K yK = a₀ := by
    have e1 : yK = ⟨x⁻¹ * k₀ * x, hxk' k₀ k₀.2⟩ * k₀⁻¹ := rfl
    have e2 : T.symm (ι K k₀) = ι K ⟨x⁻¹ * k₀ * x, hxk' k₀ k₀.2⟩ := by
      rw [LinearEquiv.symm_apply_eq, hT _ (hxk _ (hxk' k₀ k₀.2))]
      congr 1
      exact Subtype.ext (by group)
    rw [e1, ι_mul, ι_inv, ← e2]
    exact (sub_eq_add_neg _ _).symm.trans hb'
  have hι_y' : ι K y'K = T a₀ := by
    rw [← hι_y]
    exact (hT yK hy').symm
  have hspan : Submodule.span (ZMod p) (Set.range ![a₀, T a₀]) = ⊤ :=
    ha₀.span_eq_top_of_card_eq_finrank (by simp [hfr])
  have hcover : K ≤ ⁅K, K⁆ ⊔ Subgroup.closure {(yK : Γ), (y'K : Γ)} := by
    intro k hk
    have hmem : ι K ⟨k, hk⟩ ∈ Submodule.span (ZMod p) (Set.range ![a₀, T a₀]) := by
      rw [hspan]; trivial
    rw [Submodule.mem_span_range_iff_exists_fun] at hmem
    obtain ⟨c, hc⟩ := hmem
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hc
    let z : ↥K := yK ^ (c 0).val * y'K ^ (c 1).val
    have hz : ι K z = ι K ⟨k, hk⟩ := by
      simp only [z, ι_mul, ι_pow, hι_y, hι_y']
      rw [← hc, ← Nat.cast_smul_eq_nsmul (ZMod p), ← Nat.cast_smul_eq_nsmul (ZMod p),
        ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    have h0 : ι K (⟨k, hk⟩ * z⁻¹) = 0 := by
      rw [ι_mul, ι_inv, hz]; abel
    have hk' := (ι_eq_zero_iff K _).1 h0
    have hzmem : (z : Γ) ∈ Subgroup.closure {(yK : Γ), (y'K : Γ)} := by
      refine Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
        (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
    have hkz : k = (k * (z : Γ)⁻¹) * (z : Γ) := by group
    rw [hkz]
    exact Subgroup.mul_mem_sup hk' hzmem
  have hcl : ⁅K, K⁆ ≤ K := commutator_le_self' K
  have hHle : Subgroup.closure {(yK : Γ), (y'K : Γ)} ≤ K := by
    rw [Subgroup.closure_le]
    intro z hz
    rcases hz with rfl | rfl
    exacts [yK.2, y'K.2]
  have hH : Subgroup.closure {(yK : Γ), (y'K : Γ)} = K :=
    hfrat _ hHle (le_antisymm (sup_le hHle hcl) (by rw [sup_comm]; exact hcover))
  refine ⟨k₀, k₀.2, ?_⟩
  refine le_trans (le_of_eq hH.symm) ((Subgroup.closure_le _).2 ?_)
  have hx1 : x ∈ Subgroup.closure {x, (k₀ : Γ) * x * (k₀ : Γ)⁻¹} :=
    Subgroup.subset_closure (by simp)
  have hx2 : (k₀ : Γ) * x * (k₀ : Γ)⁻¹ ∈ Subgroup.closure {x, (k₀ : Γ) * x * (k₀ : Γ)⁻¹} :=
    Subgroup.subset_closure (by simp)
  intro z hz
  rcases hz with rfl | rfl
  · have e : x⁻¹ * (k₀ : Γ) * x * (k₀ : Γ)⁻¹ = x⁻¹ * ((k₀ : Γ) * x * (k₀ : Γ)⁻¹) := by group
    show x⁻¹ * (k₀ : Γ) * x * (k₀ : Γ)⁻¹ ∈ _
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hx1) hx2
  · have e : x * (x⁻¹ * (k₀ : Γ) * x * (k₀ : Γ)⁻¹) * x⁻¹ = ((k₀ : Γ) * x * (k₀ : Γ)⁻¹) * x⁻¹ := by
      group
    show x * (x⁻¹ * (k₀ : Γ) * x * (k₀ : Γ)⁻¹) * x⁻¹ ∈ _
    rw [e]
    exact Subgroup.mul_mem _ hx2 (Subgroup.inv_mem _ hx1)

private instance finite_linearEquiv_AbK {p : ℕ} (K : Subgroup Γ) [Module (ZMod p) (AbK K)]
    [Finite (AbK K)] : Finite (AbK K ≃ₗ[ZMod p] AbK K) :=
  Finite.of_injective (fun f : AbK K ≃ₗ[ZMod p] AbK K => (f : AbK K → AbK K))
    DFunLike.coe_injective

private theorem exists_pair [Finite Γ] (K L : Subgroup Γ) {p : ℕ} [hp : Fact p.Prime]
    (hLN : L ≤ Subgroup.normalizer (K : Set Γ))
    (hperf : ⁅L, L⁆ = L) (hKL : ⁅K, L⁆ = K)
    (hexp : ∀ k ∈ K, k ^ p = 1) (hK : Nat.card K = p ^ 3)
    (hK' : Nat.card (⁅K, K⁆ : Subgroup Γ) = p)
    (hfrat : ∀ H : Subgroup Γ, H ≤ K → H ⊔ ⁅K, K⁆ = K → H = K) :
    ∃ x ∈ L, Odd (orderOf x) ∧ ∃ k₀ ∈ K, K ≤ Subgroup.closure {x, k₀ * x * k₀⁻¹} := by
  haveI : Module (ZMod p) (AbK K) := AddCommGroup.zmodModule (exponent_AbK K hexp)
  have hcard : Nat.card (AbK K) = p ^ 2 := card_AbK K hK hK' hp.out.pos
  haveI : Finite (AbK K) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hp.out.ne_zero)
  have hfr : Module.finrank (ZMod p) (AbK K) = 2 := finrank_AbK K hcard
  let ρL : ↥L →* (AbK K ≃ₗ[ZMod p] AbK K) := (rhoLin K p).comp (Subgroup.inclusion hLN)
  have hρL : ∀ (g : ↥L) (k : ↥K), ρL g (ι K k) = ι K (K.normalizerMonoidHom ⟨g, hLN g.2⟩ k) :=
    fun g k => rfl
  have hρnt : ∃ g : ↥L, ρL g ≠ 1 := by
    by_contra hcon
    have hall : ∀ g : ↥L, ρL g = 1 := fun g => not_not.1 (fun h => hcon ⟨g, h⟩)
    have hle : ⁅K, L⁆ ≤ ⁅K, K⁆ := by
      rw [Subgroup.commutator_le]
      intro k hk l hl
      let a : ↥K := ⟨k, hk⟩
      let σ := K.normalizerMonoidHom ⟨l, hLN hl⟩
      have hσ : (σ a : Γ) = l * k * l⁻¹ := rfl
      have key : ι K (a * (σ a)⁻¹) = 0 := by
        rw [ι_mul, ι_inv, ← hρL ⟨l, hl⟩ a, hall]
        simp
      have hcoe : ((a * (σ a)⁻¹ : ↥K) : Γ) = ⁅k, l⁆ := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, hσ, commutatorElement_def]
        change k * (l * k * l⁻¹)⁻¹ = _
        group
      rw [← hcoe]
      exact (ι_eq_zero_iff K _).1 key
    rw [hKL] at hle
    have hKK : K = ⁅K, K⁆ := le_antisymm hle (commutator_le_self' K)
    have h3 : p ^ 3 = p := by rw [← hK, ← hK', ← hKK]
    have h2 := hp.out.two_le
    nlinarith [pow_pos hp.out.pos 2]
  haveI : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.2 hperf
  haveI : Group.IsPerfect ↥(ρL.range) := Group.IsPerfect.range ρL
  haveI : Nontrivial ↥(ρL.range) := by
    obtain ⟨g, hg⟩ := hρnt
    exact ⟨⟨⟨ρL g, ⟨g, rfl⟩⟩, 1, fun h => hg (congrArg Subtype.val h)⟩⟩
  have hns : ¬ Group.IsSolvable ↥(ρL.range) := Group.IsPerfect.not_isSolvable _
  obtain ⟨q, hq, hqdvd, hq2, hqp⟩ := exists_prime_dvd_card_of_not_solvable hp.out hns
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' q hqdvd
  obtain ⟨ℓ, hℓ⟩ := y.2
  have hordy : orderOf (ρL ℓ) = q := by
    rw [hℓ]
    exact (Subgroup.orderOf_coe y).trans hy
  have hn0 : orderOf ℓ ≠ 0 := (orderOf_pos ℓ).ne'
  have hqn : q ∣ orderOf ℓ := hordy ▸ orderOf_map_dvd ρL ℓ
  obtain ⟨a, m, hqm, hnm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 q hq.ne_one
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hnm
    exact hn0 hnm
  have hmdvd : m ∣ orderOf ℓ := ⟨q ^ a, by rw [hnm, mul_comm]⟩
  have hord_x : orderOf (ℓ ^ m) = q ^ a := by
    rw [orderOf_pow_of_dvd hm0 hmdvd, hnm]
    exact Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm0)
  have hT : ρL (ℓ ^ m) = (ρL ℓ) ^ m := map_pow ρL ℓ m
  have hTq : (ρL (ℓ ^ m)) ^ q = 1 := by
    rw [hT, ← pow_mul, mul_comm, pow_mul, ← hordy, pow_orderOf_eq_one, one_pow]
  have hT1 : ρL (ℓ ^ m) ≠ 1 := by
    intro h
    rw [hT] at h
    have := orderOf_dvd_of_pow_eq_one h
    rw [hordy] at this
    exact hqm this
  have hdet : LinearEquiv.det (ρL (ℓ ^ m)) = 1 := by
    have hle := Abelianization.commutator_subset_ker
      ((LinearEquiv.det (R := ZMod p) (M := AbK K)).comp ρL)
    rw [Group.IsPerfect.commutator_eq_top] at hle
    exact MonoidHom.mem_ker.1 (hle (Subgroup.mem_top (ℓ ^ m)))
  obtain ⟨hfix, a₀, ha₀⟩ := la_key (hq.odd_of_ne_two hq2)
    (fun h => hqp ((Nat.prime_dvd_prime_iff_eq hp.out hq).1 h).symm) hfr (ρL (ℓ ^ m)) hdet hTq hT1
  have hxL : ((ℓ ^ m : ↥L) : Γ) ∈ L := (ℓ ^ m).2
  have hxN : ((ℓ ^ m : ↥L) : Γ) ∈ Subgroup.normalizer (K : Set Γ) := hLN hxL
  have hxN' : ((ℓ ^ m : ↥L) : Γ)⁻¹ ∈ Subgroup.normalizer (K : Set Γ) := hLN (L.inv_mem hxL)
  obtain ⟨k₀, hk₀, hcl⟩ := exists_pair_of_linearIndep K hfr hfrat ((ℓ ^ m : ↥L) : Γ) hxN hxN'
    (ρL (ℓ ^ m)) (fun k h => hρL (ℓ ^ m) k) hfix a₀ ha₀
  refine ⟨((ℓ ^ m : ↥L) : Γ), hxL, ?_, k₀, hk₀, hcl⟩
  rw [Subgroup.orderOf_coe, hord_x]
  exact (hq.odd_of_ne_two hq2).pow

private theorem exists_conj_eq_mul {K Φ : Subgroup Γ} {p : ℕ} (hp : p.Prime)
    (hΦc : ∀ d ∈ Φ, ∀ k ∈ K, k * d = d * k) (hΦcard : Nat.card Φ = p)
    (hcomm : ∀ a ∈ K, ∀ b ∈ K, a * b * a⁻¹ * b⁻¹ ∈ Φ) (hΦK : Φ ≤ K)
    {e : Γ} (he : e ∈ K) (hnc : ∃ k ∈ K, e * k ≠ k * e) :
    ∀ d ∈ Φ, ∃ k ∈ K, k⁻¹ * e * k = e * d := by
  have hc1 : ∀ d ∈ Φ, ∀ k ∈ K, k⁻¹ * d * k = d := fun d hd k hk => by
    have := hΦc d hd k⁻¹ (K.inv_mem hk)
    rw [this, mul_assoc, inv_mul_cancel, mul_one]
  have hc2 : ∀ d ∈ Φ, ∀ k ∈ K, k * d * k⁻¹ = d := fun d hd k hk => by
    have := hc1 d hd k⁻¹ (K.inv_mem hk)
    simpa using this
  let R : Subgroup Γ :=
    { carrier := {d | d ∈ Φ ∧ ∃ k ∈ K, k⁻¹ * e * k = e * d}
      mul_mem' := fun {d₁ d₂} h₁ h₂ => by
        obtain ⟨hd₁, k₁, hk₁, e₁⟩ := h₁
        obtain ⟨hd₂, k₂, hk₂, e₂⟩ := h₂
        refine ⟨Φ.mul_mem hd₁ hd₂, k₁ * k₂, K.mul_mem hk₁ hk₂, ?_⟩
        calc (k₁ * k₂)⁻¹ * e * (k₁ * k₂) = k₂⁻¹ * (k₁⁻¹ * e * k₁) * k₂ := by group
          _ = k₂⁻¹ * (e * d₁) * k₂ := by rw [e₁]
          _ = (k₂⁻¹ * e * k₂) * (k₂⁻¹ * d₁ * k₂) := by group
          _ = (e * d₂) * d₁ := by rw [e₂, hc1 d₁ hd₁ k₂ hk₂]
          _ = e * (d₁ * d₂) := by
            rw [mul_assoc, hΦc d₁ hd₁ d₂ (hΦK hd₂)]
      one_mem' := ⟨Φ.one_mem, 1, K.one_mem, by simp⟩
      inv_mem' := fun {d} h => by
        obtain ⟨hd, k, hk, e₁⟩ := h
        refine ⟨Φ.inv_mem hd, k⁻¹, K.inv_mem hk, ?_⟩
        have h3 : e = (k * e * k⁻¹) * d := by
          calc e = k * (e * d) * k⁻¹ := by rw [← e₁]; group
            _ = (k * e * k⁻¹) * (k * d * k⁻¹) := by group
            _ = (k * e * k⁻¹) * d := by rw [hc2 d hd k hk]
        have h2 : k * e * k⁻¹ = e * d⁻¹ := eq_mul_inv_of_mul_eq h3.symm
        rw [inv_inv]
        exact h2 }
  have hRΦ : R ≤ Φ := fun d hd => hd.1
  obtain ⟨k, hk, hek⟩ := hnc
  have hd0 : e⁻¹ * k⁻¹ * e * k ∈ R := by
    refine ⟨?_, k, hk, by group⟩
    have := hcomm e⁻¹ (K.inv_mem he) k⁻¹ (K.inv_mem hk)
    simpa using this
  have hd0ne : e⁻¹ * k⁻¹ * e * k ≠ 1 := by
    intro h
    apply hek
    have h1 : k⁻¹ * e * k = e := by
      calc k⁻¹ * e * k = e * (e⁻¹ * k⁻¹ * e * k) := by group
        _ = e := by rw [h, mul_one]
    calc e * k = k * (k⁻¹ * e * k) := by group
      _ = k * e := by rw [h1]
  have hRne : Nat.card R ≠ 1 := by
    intro h
    rw [Subgroup.card_eq_one] at h
    have : (e⁻¹ * k⁻¹ * e * k) ∈ (⊥ : Subgroup Γ) := h ▸ hd0
    exact hd0ne (Subgroup.mem_bot.1 this)
  have hRdvd : Nat.card R ∣ p := hΦcard ▸ Subgroup.card_dvd_of_le hRΦ
  haveI : Finite Φ := Nat.finite_of_card_ne_zero (by rw [hΦcard]; exact hp.ne_zero)
  have hReq : R = Φ := by
    have hRp : Nat.card R = p := ((Nat.dvd_prime hp).1 hRdvd).resolve_left hRne
    exact Subgroup.eq_of_le_of_card_ge hRΦ (by rw [hΦcard, hRp])
  intro d hd
  have : d ∈ R := hReq ▸ hd
  exact this.2

end GroupTheory

end Endgame

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
variable {G L K : Subgroup (GLV V)} {s : GLV V} {p : ℕ}

namespace Endgame

private theorem mem_fixedSpace_zpowers {g : GLV V} {v : V} :
    v ∈ fixedSpace (Subgroup.zpowers g) ↔ g v = v := by
  constructor
  · intro h
    exact h g (Subgroup.mem_zpowers g)
  · intro h t ht
    have hst : t ∈ MulAction.stabilizer (GLV V) v :=
      Subgroup.zpowers_le.2 (MulAction.mem_stabilizer_iff.2 h) ht
    exact MulAction.mem_stabilizer_iff.1 hst

private theorem fixedSpace_zpowers_conj (e k : GLV V) :
    fixedSpace (Subgroup.zpowers (k⁻¹ * e * k)) =
      conjSub k⁻¹ (fixedSpace (Subgroup.zpowers e)) := by
  ext v
  have hk : (k⁻¹ : GLV V).symm v = k v := rfl
  rw [mem_fixedSpace_zpowers, mem_conjSub, hk, mem_fixedSpace_zpowers]
  constructor
  · intro h
    have h' := congrArg k h
    simpa using h'
  · intro h
    show k⁻¹ (e (k v)) = v
    rw [h]
    simp

private theorem add_self_eq_zero' (v : V) : v + v = 0 := by
  have h2v : (2 : ZMod 2) • v = 0 := by
    have : (2 : ZMod 2) = 0 := rfl
    rw [this, zero_smul]
  rwa [two_smul] at h2v

private theorem odd_nsmul_eq (n : ℕ) (hn : Odd n) (v : V) : n • v = v := by
  obtain ⟨k, rfl⟩ := hn
  rw [add_nsmul, mul_nsmul, one_nsmul]
  have : (2 : ℕ) • v = 0 := by rw [two_nsmul]; exact add_self_eq_zero' v
  rw [this, nsmul_zero, zero_add]

private theorem le_commSpace_of_inf_fixedSpace_eq_bot {B : Subgroup (GLV V)} (hB : Odd (Nat.card B))
    {U : Submodule (ZMod 2) V} (hU : Invariant B U) (h : U ⊓ fixedSpace B = ⊥) :
    U ≤ commSpace B ⊤ := by
  classical
  haveI : Fintype B := Fintype.ofFinite B
  intro u hu
  have hcU : (∑ b : B, (b : GLV V) u) ∈ U :=
    Submodule.sum_mem _ (fun b _ => hU b b.2 u hu)
  have hcfix : (∑ b : B, (b : GLV V) u) ∈ fixedSpace B := by
    intro b' hb'
    rw [map_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft (⟨b', hb'⟩ : B)) _ _ (fun b => ?_)
    rfl
  have h0 : (∑ b : B, (b : GLV V) u) = 0 := by
    have : (∑ b : B, (b : GLV V) u) ∈ U ⊓ fixedSpace B := ⟨hcU, hcfix⟩
    rw [h] at this
    exact this
  have hsum : u = ∑ b : B, (u - (b : GLV V) u) := by
    rw [Finset.sum_sub_distrib, h0, sub_zero, Finset.sum_const, Finset.card_univ,
      ← Nat.card_eq_fintype_card, odd_nsmul_eq _ hB]
  rw [hsum]
  refine Submodule.sum_mem _ fun b _ => ?_
  have := (commSpace B ⊤).neg_mem
    (sub_mem_commSpace b.2 (Submodule.mem_top : u ∈ (⊤ : Submodule (ZMod 2) V)))
  rwa [neg_sub] at this

private theorem finrank_map_add_finrank_inf_ker (f : V →ₗ[ZMod 2] V) (W : Submodule (ZMod 2) V) :
    Module.finrank (ZMod 2) (W.map f) + Module.finrank (ZMod 2) ↥(W ⊓ LinearMap.ker f) =
      Module.finrank (ZMod 2) W := by
  have h := (f.domRestrict W).finrank_range_add_finrank_ker
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict] at h
  rw [← h]
  congr 1
  rw [← Submodule.finrank_map_subtype_eq W (Submodule.comap W.subtype (LinearMap.ker f)),
    Submodule.map_comap_subtype]

private theorem eq_one_or_eq_of_mem_zpowers {s t : GLV V} (hs : s ^ 2 = 1)
    (ht : t ∈ Subgroup.zpowers s) : t = 1 ∨ t = s := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 ht
  have h : s ^ n = s ^ (n % 2) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv n 2, zpow_add, zpow_mul]
    rw [show s ^ (2 : ℤ) = 1 by simpa using hs, one_zpow, mul_one]
  rw [h]
  have : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases this with h0 | h1
  · left; rw [h0]; simp
  · right; rw [h1]; simp

private def Nmap (s : GLV V) : V →ₗ[ZMod 2] V := (s : V →ₗ[ZMod 2] V) - LinearMap.id

private theorem Nmap_apply (s : GLV V) (v : V) : Nmap s v = s v - v := rfl

private theorem ker_Nmap (s : GLV V) :
    LinearMap.ker (Nmap s) = fixedSpace (Subgroup.zpowers s) := by
  ext v
  rw [LinearMap.mem_ker, Nmap_apply, sub_eq_zero, mem_fixedSpace_zpowers]

private theorem commSpace_zpowers_eq_map {s : GLV V} (hs : s ^ 2 = 1) (W : Submodule (ZMod 2) V) :
    commSpace (Subgroup.zpowers s) W = W.map (Nmap s) := by
  apply le_antisymm
  · refine commSpace_le_iff.2 fun t ht u hu => ?_
    rcases eq_one_or_eq_of_mem_zpowers hs ht with rfl | rfl
    · simp
    · exact ⟨u, hu, rfl⟩
  · rintro _ ⟨u, hu, rfl⟩
    exact sub_mem_commSpace (Subgroup.mem_zpowers s) hu

private theorem commSpace_zpowers_le_fixedSpace {s : GLV V} (hs : s ^ 2 = 1)
    (W : Submodule (ZMod 2) V) :
    commSpace (Subgroup.zpowers s) W ≤ fixedSpace (Subgroup.zpowers s) := by
  rw [commSpace_zpowers_eq_map hs]
  rintro _ ⟨u, hu, rfl⟩
  rw [mem_fixedSpace_zpowers, Nmap_apply, map_sub]
  have h2 : s (s u) = u := by
    have := congrArg (fun g : GLV V => g u) hs
    simpa [pow_two] using this
  rw [h2]
  have h3 : s u - u = -(s u - u) := eq_neg_of_add_eq_zero_left (add_self_eq_zero' (s u - u))
  rw [neg_sub] at h3
  exact h3.symm

end Endgame

private theorem Core62.eg_p_odd (hc : Core62 G L K s p) : Odd p := hc.prime.odd_of_ne_two hc.p_ne

private theorem Core62.eg_odd_zpowers (hc : Core62 G L K s p) {e : GLV V} (heK : e ∈ K) :
    Odd (Nat.card (Subgroup.zpowers e)) := by
  have hle : Subgroup.zpowers e ≤ K := Subgroup.zpowers_le.2 heK
  exact Odd.of_dvd_nat (hc.eg_p_odd.pow (n := 3)) (hc.card_eq ▸ Subgroup.card_dvd_of_le hle)

private theorem Core62.eg_frat_central (hc : Core62 G L K s p) :
    ∀ d ∈ frat K, ∀ k ∈ K, k * d = d * k := fun d hd k hk =>
  Subgroup.mem_centralizer_iff.1 (hc.frat_center hd) k hk

private theorem Core62.eg_exists_e (hc : Core62 G L K s p) :
    ∃ e ∈ K, e ∉ frat K ∧ s * e * s⁻¹ = e⁻¹ := by
  haveI := Fact.mk hc.prime
  obtain ⟨k₁, hk₁K, hk₁Φ⟩ : ∃ k ∈ K, k ∉ frat K := by
    by_contra hcon
    have hle : K ≤ frat K := fun k hk => by
      by_contra h
      exact hcon ⟨k, hk, h⟩
    have heq : K = frat K := le_antisymm hle (frat_le K)
    have h3 := hc.card_eq
    rw [heq, hc.card_frat] at h3
    have h2 := hc.prime.two_le
    nlinarith [pow_pos hc.prime.pos 2]
  obtain ⟨d₁, hd₁, hinv⟩ := hc.exists_inverted k₁ hk₁K
  refine ⟨k₁ * d₁, K.mul_mem hk₁K (frat_le K hd₁), fun h => hk₁Φ ?_, hinv⟩
  simpa using (frat K).mul_mem h ((frat K).inv_mem hd₁)

private theorem Core62.eg_conj_class (hc : Core62 G L K s p) {e : GLV V} (he : e ∈ K)
    (heΦ : e ∉ frat K) : ∀ d ∈ frat K, ∃ k ∈ K, k⁻¹ * e * k = e * d := by
  haveI := Fact.mk hc.prime
  refine Endgame.exists_conj_eq_mul hc.prime hc.eg_frat_central hc.card_frat ?_ (frat_le K) he ?_
  · intro a ha b hb
    rw [hc.frat_eq_commutator]
    exact Subgroup.commutator_mem_commutator ha hb
  · by_contra hcon
    apply heΦ
    rw [hc.frat_eq_center]
    refine ⟨he, Subgroup.mem_centralizer_iff.2 fun k hk => ?_⟩
    by_contra hne
    exact hcon ⟨k, hk, fun h => hne h.symm⟩

private theorem Core62.eg_exists_W (hc : Core62 G L K s p) :
    ∃ e ∈ K, e ∉ frat K ∧ s * e * s⁻¹ = e⁻¹ ∧
      Module.finrank (ZMod 2) V <
        2 * Module.finrank (ZMod 2) (commSpace (Subgroup.zpowers e) ⊤) := by
  haveI := Fact.mk hc.prime
  obtain ⟨e, heK, heΦ, hinv⟩ := hc.eg_exists_e
  refine ⟨e, heK, heΦ, hinv, ?_⟩
  have hBodd := hc.eg_odd_zpowers heK
  have hdec : IsCompl (fixedSpace (Subgroup.zpowers e)) (commSpace (Subgroup.zpowers e) ⊤) :=
    isCompl_fixedSpace_commSpace hBodd
  let Vd : GLV V → Submodule (ZMod 2) V := fun d => fixedSpace (Subgroup.zpowers (e * d))
  have hVd1 : Vd 1 = fixedSpace (Subgroup.zpowers e) := by simp [Vd]
  have hdim : ∀ d ∈ frat K, Module.finrank (ZMod 2) (Vd d) =
      Module.finrank (ZMod 2) (fixedSpace (Subgroup.zpowers e)) := by
    intro d hd
    obtain ⟨k, hkK, hk⟩ := hc.eg_conj_class heK heΦ d hd
    show Module.finrank (ZMod 2) (fixedSpace (Subgroup.zpowers (e * d))) = _
    rw [← hk, Endgame.fixedSpace_zpowers_conj, finrank_conjSub]
  have hdisj : ∀ d ∈ frat K, ∀ d' ∈ frat K, d ≠ d' → Vd d ⊓ Vd d' = ⊥ := by
    intro d hd d' hd' hne
    rw [eq_bot_iff]
    rintro v ⟨hv1, hv2⟩
    have h1 : e (d v) = v := Endgame.mem_fixedSpace_zpowers.1 hv1
    have h2 : e (d' v) = v := Endgame.mem_fixedSpace_zpowers.1 hv2
    have h3 : d v = d' v := e.injective (h1.trans h2.symm)
    have hdd : (d⁻¹ * d') v = v := by
      show d⁻¹ (d' v) = v
      rw [← h3]
      simp
    have hne1 : d⁻¹ * d' ≠ 1 := fun h => hne (inv_mul_eq_one.1 h)
    have hmem : d⁻¹ * d' ∈ frat K := (frat K).mul_mem ((frat K).inv_mem hd) hd'
    have hbot := hc.fixedSpace_eq_bot_of_mem_frat _ hmem hne1
    have : v ∈ fixedSpace (Subgroup.zpowers (d⁻¹ * d')) := Endgame.mem_fixedSpace_zpowers.2 hdd
    rw [hbot] at this
    exact this
  have hle : ∀ d ∈ frat K, d ≠ 1 → Vd d ≤ commSpace (Subgroup.zpowers e) ⊤ := by
    intro d hd hd1
    apply Endgame.le_commSpace_of_inf_fixedSpace_eq_bot hBodd
    · intro t ht v hv
      have hed : Commute e d := hc.eg_frat_central d hd e heK
      have hc1 : Commute e (e * d) := (Commute.refl e).mul_right hed
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 ht
      have hc2 : Commute (e ^ n) (e * d) := hc1.zpow_left n
      refine Endgame.mem_fixedSpace_zpowers.2 ?_
      have hv' : (e * d) v = v := Endgame.mem_fixedSpace_zpowers.1 hv
      have this' : (e ^ n) ((e * d) v) = (e * d) ((e ^ n) v) :=
        congrArg (fun g : GLV V => g v) hc2.eq
      show (e * d) ((e ^ n) v) = (e ^ n) v
      rw [← this', hv']
    · have := hdisj d hd 1 (frat K).one_mem hd1
      rwa [hVd1] at this
  obtain ⟨a, b, c, hab, hac, hbc⟩ : ∃ a b c : ↥(frat K), a ≠ b ∧ a ≠ c ∧ b ≠ c := by
    haveI : Finite (frat K) :=
      Nat.finite_of_card_ne_zero (by rw [hc.card_frat]; exact hc.prime.ne_zero)
    haveI : Fintype (frat K) := Fintype.ofFinite _
    have h3 : 2 < Fintype.card (frat K) := by
      rw [← Nat.card_eq_fintype_card, hc.card_frat]
      have := hc.prime.two_le
      have := hc.p_ne
      omega
    exact Fintype.two_lt_card_iff.1 h3
  have hd : (a : GLV V)⁻¹ * b ∈ frat K := (frat K).mul_mem ((frat K).inv_mem a.2) b.2
  have hd' : (a : GLV V)⁻¹ * c ∈ frat K := (frat K).mul_mem ((frat K).inv_mem a.2) c.2
  have hd1 : (a : GLV V)⁻¹ * b ≠ 1 := fun h => hab (Subtype.ext (inv_mul_eq_one.1 h))
  have hd1' : (a : GLV V)⁻¹ * c ≠ 1 := fun h => hac (Subtype.ext (inv_mul_eq_one.1 h))
  have hdd' : (a : GLV V)⁻¹ * b ≠ (a : GLV V)⁻¹ * c := fun h =>
    hbc (Subtype.ext (mul_left_cancel h))
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (Vd ((a : GLV V)⁻¹ * b))
    (Vd ((a : GLV V)⁻¹ * c))
  rw [hdisj _ hd _ hd' hdd', finrank_bot, add_zero, hdim _ hd, hdim _ hd'] at h1
  have h2 := Submodule.finrank_mono (sup_le (hle _ hd hd1) (hle _ hd' hd1'))
  have h3 := Submodule.finrank_add_eq_of_isCompl hdec
  have hnt : Nontrivial V := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    apply heΦ
    have : e = 1 := LinearEquiv.ext fun v => Subsingleton.elim _ _
    rw [this]
    exact (frat K).one_mem
  have hV : 0 < Module.finrank (ZMod 2) V := Module.finrank_pos
  omega

private theorem Core62.eg_two_mul_finrank_lt (hc : Core62 G L K s p) {x : GLV V} (hxL : x ∈ L)
    (hxodd : Odd (Nat.card (Subgroup.zpowers x))) :
    Module.finrank (ZMod 2) V <
      2 * Module.finrank (ZMod 2) (fixedSpace (Subgroup.zpowers x)) := by
  obtain ⟨e, heK, heΦ, hinv, hW⟩ := hc.eg_exists_W
  have hs2 : s ^ 2 = 1 := by
    have := pow_orderOf_eq_one s
    rwa [hc.s_ord] at this
  have hBodd := hc.eg_odd_zpowers heK
  have hdec : IsCompl (fixedSpace (Subgroup.zpowers e)) (commSpace (Subgroup.zpowers e) ⊤) :=
    isCompl_fixedSpace_commSpace hBodd
  have hV1s : ∀ v ∈ fixedSpace (Subgroup.zpowers e), s v = v :=
    hc.centralizes_fixedSpace heK heΦ hinv
  have hsB : ∀ b ∈ Subgroup.zpowers e, s * b * s⁻¹ = b⁻¹ := by
    intro b hb
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    have : s * e ^ n * s⁻¹ = (s * e * s⁻¹) ^ n := by
      have := map_zpow (MulAut.conj s) e n
      simpa [MulAut.conj_apply] using this
    rw [this, hinv, inv_zpow]
  have hab : ∀ a ∈ Subgroup.zpowers e, ∀ b ∈ Subgroup.zpowers e, a * b = b * a := by
    intro a ha b hb
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    exact (Commute.zpow_zpow_self e i j).eq
  have hWB : Invariant (Subgroup.zpowers e) (commSpace (Subgroup.zpowers e) ⊤) :=
    invariant_commSpace (fun k' hk' k hk =>
      (Subgroup.zpowers e).mul_mem ((Subgroup.zpowers e).mul_mem hk' hk)
        ((Subgroup.zpowers e).inv_mem hk')) (invariant_top _)
  have hWs' : Invariant (Subgroup.zpowers s) (commSpace (Subgroup.zpowers e) ⊤) := by
    refine invariant_commSpace (fun k' hk' k hk => ?_) (invariant_top _)
    rcases Endgame.eq_one_or_eq_of_mem_zpowers hs2 hk' with rfl | rfl
    · simpa using hk
    · rw [hsB k hk]
      exact (Subgroup.zpowers e).inv_mem hk
  have hWs : ∀ w ∈ commSpace (Subgroup.zpowers e) ⊤, s w ∈ commSpace (Subgroup.zpowers e) ⊤ :=
    fun w hw => hWs' s (Subgroup.mem_zpowers s) w hw
  have hV1Cs : fixedSpace (Subgroup.zpowers e) ≤ fixedSpace (Subgroup.zpowers s) :=
    fun v hv => Endgame.mem_fixedSpace_zpowers.2 (hV1s v hv)
  have hF3 : commSpace (Subgroup.zpowers s) ⊤ =
      commSpace (Subgroup.zpowers s) (commSpace (Subgroup.zpowers e) ⊤) := by
    apply le_antisymm
    · refine commSpace_le_iff.2 fun t ht v _ => ?_
      obtain ⟨v₁, hv₁, w, hw, rfl⟩ := Submodule.mem_sup.1
        (hdec.sup_eq_top ▸ Submodule.mem_top : v ∈ _ ⊔ _)
      have htv₁ : t v₁ = v₁ := hV1Cs hv₁ t ht
      rw [map_add, htv₁, add_sub_add_left_eq_sub]
      exact sub_mem_commSpace ht hw
    · exact commSpace_mono le_rfl le_top
  have hF4 : commSpace (Subgroup.zpowers e) ⊤ ⊓ fixedSpace (Subgroup.zpowers s) =
      commSpace (Subgroup.zpowers s) (commSpace (Subgroup.zpowers e) ⊤) := by
    apply le_antisymm
    · rintro w ⟨hw, hws⟩
      have hws' : s w = w := Endgame.mem_fixedSpace_zpowers.1 hws
      obtain ⟨u, hu, rfl⟩ := exists_eq_sub_of_inverts hBodd hab hs2 hsB hWB hWs
        hdec.inf_eq_bot w hw hws'
      exact sub_mem_commSpace (Subgroup.mem_zpowers s) hu
    · intro w hw
      exact ⟨commSpace_le_of_invariant hWs' hw, Endgame.commSpace_zpowers_le_fixedSpace hs2 _ hw⟩
  have hR2 : Module.finrank (ZMod 2) (commSpace (Subgroup.zpowers e) ⊤) =
      2 * Module.finrank (ZMod 2) (commSpace (Subgroup.zpowers s) ⊤) := by
    have h := Endgame.finrank_map_add_finrank_inf_ker (Endgame.Nmap s)
      (commSpace (Subgroup.zpowers e) ⊤)
    rw [← Endgame.commSpace_zpowers_eq_map hs2, Endgame.ker_Nmap, hF4, ← hF3] at h
    omega
  have hR3 : Module.finrank (ZMod 2) (commSpace (Subgroup.zpowers s) ⊤) +
      Module.finrank (ZMod 2) (fixedSpace (Subgroup.zpowers s)) = Module.finrank (ZMod 2) V := by
    have h := (Endgame.Nmap s).finrank_range_add_finrank_ker
    rw [Endgame.ker_Nmap, LinearMap.range_eq_map, ← Endgame.commSpace_zpowers_eq_map hs2] at h
    exact h
  obtain ⟨hl1, hl2⟩ := Setup6.lemma61 hc.conf.setup (Subgroup.mem_zpowers s)
  have hNsCx : commSpace (Subgroup.zpowers s) ⊤ ≤ fixedSpace (Subgroup.zpowers x) :=
    fun w hw => Endgame.mem_fixedSpace_zpowers.2 (hl1 x hxL w hw)
  have hNxCs : commSpace (Subgroup.zpowers x) ⊤ ≤ fixedSpace (Subgroup.zpowers s) :=
    (commSpace_mono (Subgroup.zpowers_le.2 hxL) le_rfl).trans hl2
  have hdecx : IsCompl (fixedSpace (Subgroup.zpowers x)) (commSpace (Subgroup.zpowers x) ⊤) :=
    isCompl_fixedSpace_commSpace hxodd
  have hinf : commSpace (Subgroup.zpowers x) ⊤ ⊓ commSpace (Subgroup.zpowers s) ⊤ = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    have : v ∈ fixedSpace (Subgroup.zpowers x) ⊓ commSpace (Subgroup.zpowers x) ⊤ :=
      ⟨hNsCx hv.2, hv.1⟩
    rw [hdecx.inf_eq_bot] at this
    exact this
  have hR4 : Module.finrank (ZMod 2) (commSpace (Subgroup.zpowers x) ⊤) +
      Module.finrank (ZMod 2) (commSpace (Subgroup.zpowers s) ⊤) ≤
      Module.finrank (ZMod 2) (fixedSpace (Subgroup.zpowers s)) := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq (commSpace (Subgroup.zpowers x) ⊤)
      (commSpace (Subgroup.zpowers s) ⊤)
    rw [hinf, finrank_bot, add_zero] at h1
    have h2 := Submodule.finrank_mono
      (sup_le hNxCs (Endgame.commSpace_zpowers_le_fixedSpace hs2 ⊤))
    omega
  have hR5 := Submodule.finrank_add_eq_of_isCompl hdecx
  omega

theorem Core62.false (hc : Core62 G L K s p) : False := by
  haveI := Fact.mk hc.prime
  have hperf : ⁅L, L⁆ = L :=
    Subgroup.isPerfect_iff.1 (Group.isPerfect_def.2 hc.conf.setup.component.2.2.1)
  have hK' : Nat.card (⁅K, K⁆ : Subgroup (GLV V)) = p := by
    rw [← hc.frat_eq_commutator]
    exact hc.card_frat
  have hfrat : ∀ H : Subgroup (GLV V), H ≤ K → H ⊔ ⁅K, K⁆ = K → H = K := fun H hH h =>
    eq_of_sup_frat hH (by rw [hc.frat_eq_commutator]; exact h)
  obtain ⟨x, hxL, hxodd, k₀, hk₀K, hKcl⟩ :=
    Endgame.exists_pair K L hc.conf.L_le hperf hc.KL hc.pow_eq_one hc.card_eq hK' hfrat
  have hlt := hc.eg_two_mul_finrank_lt hxL (by rwa [Nat.card_zpowers])
  have hC1 : fixedSpace (Subgroup.zpowers (k₀ * x * k₀⁻¹)) =
      conjSub k₀ (fixedSpace (Subgroup.zpowers x)) := by
    have := Endgame.fixedSpace_zpowers_conj x k₀⁻¹
    simpa using this
  have hdim1 : Module.finrank (ZMod 2) (fixedSpace (Subgroup.zpowers (k₀ * x * k₀⁻¹))) =
      Module.finrank (ZMod 2) (fixedSpace (Subgroup.zpowers x)) := by
    rw [hC1, finrank_conjSub]
  have hne : fixedSpace (Subgroup.zpowers x) ⊓
      fixedSpace (Subgroup.zpowers (k₀ * x * k₀⁻¹)) ≠ ⊥ := by
    intro hbot
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq (fixedSpace (Subgroup.zpowers x))
      (fixedSpace (Subgroup.zpowers (k₀ * x * k₀⁻¹)))
    rw [hbot, finrank_bot] at h1
    have h2 := Submodule.finrank_le
      (fixedSpace (Subgroup.zpowers x) ⊔ fixedSpace (Subgroup.zpowers (k₀ * x * k₀⁻¹)))
    omega
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hvK : v ∈ fixedSpace K := by
    intro k hk
    have hcl : Subgroup.closure {x, k₀ * x * k₀⁻¹} ≤ MulAction.stabilizer (GLV V) v := by
      rw [Subgroup.closure_le]
      intro t ht
      rcases ht with rfl | rfl
      · exact MulAction.mem_stabilizer_iff.2 (Endgame.mem_fixedSpace_zpowers.1 hv.1)
      · exact MulAction.mem_stabilizer_iff.2 (Endgame.mem_fixedSpace_zpowers.1 hv.2)
    exact MulAction.mem_stabilizer_iff.1 (hcl (hKcl hk))
  rw [hc.fix] at hvK
  exact hv0 hvK

end CFSG.CGT.Foote82
