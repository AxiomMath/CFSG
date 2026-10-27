module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSLOuter
public import CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupOddHigherLinear
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSLInner
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearDescentFixedBasis
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherScalarSquareSplit
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.PSL

open Matrix CFSG Subgroup CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.TBLit
open scoped MatrixGroups

variable {n : ℕ} {K : Type} [Field K]

abbrev fixField (σ : K ≃+* K) : Subfield K := RingHom.eqLocusField σ.toRingHom (RingHom.id K)

theorem mem_fixField {σ : K ≃+* K} {x : K} : x ∈ fixField σ ↔ σ x = x := Iff.rfl

theorem eq_one_of_fix_fixField {σ τ : K ≃+* K} (h2 : (2 : K) ≠ 0) (hσσ : ∀ x, σ (σ x) = x)
    (hσ : σ ≠ 1) (hτ : ∀ x, σ x = x → τ x = x) {k : ℕ} (hk : Odd k) (hτk : τ ^ k = 1) :
    τ = 1 := by
  obtain ⟨x, hx⟩ : ∃ x, σ x ≠ x := by
    by_contra h
    push Not at h
    exact hσ (RingEquiv.ext h)
  set θ := x - σ x with hθdef
  have hθ : θ ≠ 0 := sub_ne_zero.2 (Ne.symm hx)
  have hσθ : σ θ = -θ := by rw [hθdef, map_sub, hσσ]; ring
  have hθθ : τ θ * τ θ = θ * θ := by
    rw [← map_mul]
    exact hτ _ (by rw [map_mul, hσθ]; ring)
  have hτθ : τ θ = θ := by
    have h0 : (τ θ - θ) * (τ θ + θ) = 0 := by linear_combination hθθ
    rcases mul_eq_zero.1 h0 with h | h
    · exact sub_eq_zero.1 h
    · exfalso
      have hm : τ θ = -θ := eq_neg_of_add_eq_zero_left h
      have hpow : ∀ j : ℕ, (τ ^ j) θ = (-1) ^ j * θ := by
        intro j
        induction j with
        | zero => simp
        | succ j ih =>
          rw [pow_succ]
          change (τ ^ j) (τ θ) = _
          rw [hm, map_neg, ih, pow_succ]
          ring
      have := hpow k
      rw [hτk, hk.neg_one_pow] at this
      change θ = -1 * θ at this
      apply hθ
      have h2θ : (2 : K) * θ = 0 := by linear_combination this
      exact (mul_eq_zero.1 h2θ).resolve_left h2
  have hσ2 : σ (2 : K) = 2 := map_ofNat σ 2
  refine RingEquiv.ext fun z => ?_
  have hz : z = (z + σ z) / 2 + (z - σ z) / (2 * θ) * θ := by
    field_simp
    ring
  have ha : σ ((z + σ z) / 2) = (z + σ z) / 2 := by
    rw [map_div₀, map_add, hσσ, hσ2, add_comm]
  have hb : σ ((z - σ z) / (2 * θ)) = (z - σ z) / (2 * θ) := by
    rw [map_div₀, map_sub, map_mul, hσσ, hσ2, hσθ]
    field_simp
    ring
  calc τ z = τ ((z + σ z) / 2 + (z - σ z) / (2 * θ) * θ) := by rw [← hz]
    _ = (z + σ z) / 2 + (z - σ z) / (2 * θ) * θ := by
        rw [map_add, map_mul, hτ _ ha, hτ _ hb, hτθ]
    _ = z := hz.symm

variable (n) in
abbrev fieldFixedSL (σ : K ≃+* K) : Subgroup (SpecialLinearGroup (Fin n) K) :=
  MonoidHom.eqLocus (SpecialLinearGroup.map σ.toRingHom) (MonoidHom.id _)

theorem mem_fieldFixedSL {σ : K ≃+* K} {g : SpecialLinearGroup (Fin n) K} :
    g ∈ fieldFixedSL n σ ↔ ∀ i j, σ ((g : Matrix (Fin n) (Fin n) K) i j) = g i j := by
  constructor
  · intro hg i j
    have := congrArg (fun x : SpecialLinearGroup (Fin n) K => (x : Matrix (Fin n) (Fin n) K) i j)
      (show SpecialLinearGroup.map σ.toRingHom g = g from hg)
    simpa using this
  · intro hg
    change SpecialLinearGroup.map σ.toRingHom g = g
    apply Subtype.ext
    ext i j
    simpa using hg i j

theorem range_map_fixField (σ : K ≃+* K) :
    (SpecialLinearGroup.map (fixField σ).subtype).range = fieldFixedSL n σ := by
  ext g
  rw [mem_fieldFixedSL]
  constructor
  · rintro ⟨g₀, rfl⟩ i j
    exact ((g₀ : Matrix (Fin n) (Fin n) (fixField σ)) i j).2
  · intro hg
    set g₀ : Matrix (Fin n) (Fin n) (fixField σ) :=
      Matrix.of fun i j => ⟨(g : Matrix (Fin n) (Fin n) K) i j, hg i j⟩ with hg₀
    have hmap : (fixField σ).subtype.mapMatrix g₀ = (g : Matrix (Fin n) (Fin n) K) := by
      ext i j
      rfl
    have hdet : g₀.det = 1 := by
      apply (fixField σ).subtype_injective
      rw [RingHom.map_det, hmap, map_one, g.2]
    exact ⟨⟨g₀, hdet⟩, Subtype.ext hmap⟩

theorem map_fixField_injective (σ : K ≃+* K) :
    Function.Injective (SpecialLinearGroup.map (n := Fin n) (fixField σ).subtype) := by
  intro a b h
  apply Subtype.ext
  ext i j
  have := congrArg (fun x : SpecialLinearGroup (Fin n) K => (x : Matrix (Fin n) (Fin n) K) i j) h
  simpa using this

theorem transvection_mem_fieldFixedSL {σ : K ≃+* K} {i j : Fin n} (hij : i ≠ j) {c : K}
    (hc : σ c = c) : SpecialLinearGroup.transvection hij c ∈ fieldFixedSL n σ := by
  rw [mem_fieldFixedSL]
  intro k l
  simp only [SpecialLinearGroup.transvection_coe, Matrix.add_apply, one_apply, single_apply]
  split_ifs <;> simp_all

theorem isQuasisimple_fieldFixed [Finite K] (hn : 3 ≤ n) (σ : K ≃+* K)
    (hinj : Function.Injective (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K))) :
    IsQuasisimple ((fieldFixedSL n σ).map (conjProj n K)) := by
  have hE : IsQuasisimple (fieldFixedSL n σ) := by
    rw [← range_map_fixField]
    exact LocalCores.isQuasisimple_of_mulEquiv
      (MonoidHom.ofInjective (map_fixField_injective (n := n) σ))
      (CatalogueBGeneralLinear.specialLinear_quasisimple n (fixField σ) (by omega)
        (Or.inl (by omega)) (Or.inl (by omega)))
  refine LocalCores.isQuasisimple_map hE _ fun hle => ?_
  have h01 : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  have hmem := transvection_mem_fieldFixedSL (σ := σ) h01 (c := 1) (map_one σ)
  have hker : conjProj n K (SpecialLinearGroup.transvection h01 1) = 1 := hle hmem
  have hproj : proj n K (SpecialLinearGroup.transvection h01 1) = 1 :=
    hinj (by rw [map_one]; exact hker)
  obtain ⟨c, -, hc⟩ := proj_eq_one_iff.1 hproj
  have e := congrFun (congrFun hc ⟨0, by omega⟩) ⟨1, by omega⟩
  simp only [SpecialLinearGroup.transvection_coe, Matrix.add_apply, one_apply_ne h01,
    single_apply_same, zero_add, scalar_apply, diagonal_apply_ne _ h01] at e
  exact one_ne_zero e

theorem field_oddCoreIn_eq_bot [Finite K] (hK : ringChar K ≠ 2) (hn : 3 ≤ n)
    (hinj : Function.Injective (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)))
    {B : Subgroup (MulAut (projectiveSL n K))}
    (hB : (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range ≤ B)
    {σ : K ≃+* K} (hσσ : ∀ x, σ (σ x) = x) (hσ : σ ≠ 1) :
    oddCoreIn B (fieldAut n K σ) = ⊥ := by
  have : Fintype K := Fintype.ofFinite K
  set p := ringChar K with hp
  have : Fact p.Prime := ⟨CharP.char_is_prime K p⟩
  rw [eq_bot_iff]
  intro y hy
  rw [mem_bot]
  have hodd := odd_orderOf_of_mem_oddCoreIn hy
  obtain ⟨D, τ, rfl⟩ := exists_semilinear_of_odd hn hodd
  have hq := isQuasisimple_fieldFixed hn σ hinj
  have hfix : ∀ g ∈ fieldFixedSL n σ,
      (conjAut n K D * fieldAut n K τ) (proj n K g) = proj n K g :=
    fun g hg => commute_oddCoreIn_of_fixed hinj hB (SpecialLinearGroup.map σ.toRingHom)
      (fieldAut_proj σ) (fun _ h => h) (fun _ hh _ hg => conj_mem_eqLocus_of_scalar _ hh hg)
      hq hy hg
  have htr : ∀ {i j : Fin n} (hij : i ≠ j), (∀ c ∈ (fixField σ : Set K), τ c = c) ∧
      (D : Matrix (Fin n) (Fin n) K) * single i j 1 =
        single i j 1 * (D : Matrix (Fin n) (Fin n) K) :=
    fun hij => fix_transvections_on (p := p) hij (S := (fixField σ : Set K)) (one_mem _)
      fun c hc => hfix _ (transvection_mem_fieldFixedSL hij hc)
  have hD : conjAut n K D = 1 :=
    conjAut_eq_one_of_commute_single ⟨0, by omega⟩ fun i j hij => (htr hij).2
  have h01 : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  have hτK : ∀ x, σ x = x → τ x = x := fun x hx => (htr h01).1 x hx
  rw [hD, one_mul] at hodd ⊢
  have hτk : τ ^ orderOf (fieldAut n K τ) = 1 := by
    have h1 : conjAut n K 1 * fieldAut n K (τ ^ orderOf (fieldAut n K τ)) = 1 := by
      rw [map_one, one_mul, map_pow, pow_orderOf_eq_one]
    exact (eq_one_of_conjAut_mul_fieldAut_eq_one hn 1 _ h1).1
  rw [eq_one_of_fix_fixField (Ring.two_ne_zero hK) hσσ hσ hτK hodd hτk, map_one]

theorem field_eq_bot [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hKc : Nat.card K = p ^ f) (hn : 3 ≤ n)
    (hinj : Function.Injective (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)))
    {X : Type} [Group X] [Finite X] {ψ : X →* MulAut (projectiveSL n K)}
    (hψ : Function.Injective ψ)
    (hInn : (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range ≤ ψ.range)
    {t : X} (ht : orderOf t = 2) {A : GL (Fin n) K} {σ : K ≃+* K} (hσ : σ ≠ 1)
    (htA : ψ t = conjAut n K A * fieldAut n K σ) {Y : Subgroup X}
    (hYO : Y ≤ oddCentralizerCore t) : Y = ⊥ := by
  have : Fintype K := Fintype.ofFinite K
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
  have hK : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  have hα : (conjAut n K A * fieldAut n K σ) ^ 2 = 1 := by
    rw [← htA, ← map_pow, ← ht, pow_orderOf_eq_one, map_one]
  obtain ⟨H, hH⟩ := LocalAnalysis.ComponentInitial.OddHigherLinear.field_involution_conjugacy
    hp hp2 hf hKc hn A σ hσ hα
  obtain ⟨hinj', hInn'⟩ := conj_embedding hψ hInn (conjAut n K H)⁻¹
  set ψ' := (MulAut.conj (conjAut n K H)⁻¹).toMonoidHom.comp ψ with hψ'def
  have hψ't : ψ' t = fieldAut n K σ := by
    change (conjAut n K H)⁻¹ * ψ t * ((conjAut n K H)⁻¹)⁻¹ = _
    rw [htA, hH]
    group
  have hσσ : ∀ x, σ (σ x) = x := by
    have h1 : fieldAut n K σ ^ 2 = 1 := by
      rw [← hψ't, ← map_pow, ← ht, pow_orderOf_eq_one, map_one]
    have h2 : conjAut n K 1 * fieldAut n K (σ ^ 2) = 1 := by rw [map_one, one_mul, map_pow, h1]
    have h3 := (eq_one_of_conjAut_mul_fieldAut_eq_one hn 1 _ h2).1
    intro x
    have := congrArg (fun τ : K ≃+* K => τ x) h3
    simpa [pow_two] using this
  refine eq_bot_of_oddCoreIn hinj' ?_ hYO
  rw [hψ't]
  exact field_oddCoreIn_eq_bot hK hn hinj hInn' hσσ hσ

end CFSG.ComponentClassification.Burgoyne.PSL
