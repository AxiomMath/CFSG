module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseAMon
public import Mathlib.LinearAlgebra.Charpoly.Basic

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseB

open Matrix Subgroup Module Polynomial

variable {K : Type} [Field K] {p : ℕ}

@[expose] def GInv (G : Subgroup (GL (Fin p) K)) (W : Submodule K (Fin p → K)) : Prop :=
  ∀ g ∈ G, ∀ w ∈ W, (g : Matrix (Fin p) (Fin p) K) *ᵥ w ∈ W

theorem GInv.top (G : Subgroup (GL (Fin p) K)) : GInv G ⊤ := fun _ _ _ _ => Submodule.mem_top

theorem GInv.inf {G : Subgroup (GL (Fin p) K)} {W₁ W₂ : Submodule K (Fin p → K)}
    (h₁ : GInv G W₁) (h₂ : GInv G W₂) : GInv G (W₁ ⊓ W₂) := fun g hg w hw =>
  ⟨h₁ g hg w hw.1, h₂ g hg w hw.2⟩

theorem GInv.sup {G : Subgroup (GL (Fin p) K)} {W₁ W₂ : Submodule K (Fin p → K)}
    (h₁ : GInv G W₁) (h₂ : GInv G W₂) : GInv G (W₁ ⊔ W₂) := by
  intro g hg w hw
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hw
  rw [Matrix.mulVec_add]
  exact Submodule.add_mem_sup (h₁ g hg a ha) (h₂ g hg b hb)

theorem GInv.map {G : Subgroup (GL (Fin p) K)} {W : Submodule K (Fin p → K)} (hW : GInv G W)
    (h : GL (Fin p) K) (hh : ∀ g ∈ G, h⁻¹ * g * h ∈ G) :
    GInv G (W.map (Matrix.mulVecLin (h : Matrix (Fin p) (Fin p) K))) := by
  rintro g hg _ ⟨w, hw, rfl⟩
  have h1 := hW _ (hh g hg) w hw
  refine ⟨_, h1, ?_⟩
  have e : h * (h⁻¹ * g * h) = g * h := by group
  have e' : (h : Matrix (Fin p) (Fin p) K) * ((h⁻¹ * g * h : GL (Fin p) K) :
      Matrix (Fin p) (Fin p) K) =
        (g : Matrix (Fin p) (Fin p) K) * (h : Matrix (Fin p) (Fin p) K) := by
    rw [← Units.val_mul, e, Units.val_mul]
  simp only [Matrix.mulVecLin_apply]
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, e']

theorem eq_top_of_stable {ŷ : GL (Fin p) K} {ω : K} (hp : p.Prime)
    (hy : (ŷ : Matrix (Fin p) (Fin p) K) ^ p = Matrix.scalar (Fin p) ω)
    (hω : ∀ b : K, b ^ p ≠ ω) {U : Submodule K (Fin p → K)}
    (hU : ∀ u ∈ U, (ŷ : Matrix (Fin p) (Fin p) K) *ᵥ u ∈ U) (hne : U ≠ ⊥) : U = ⊤ := by
  classical
  haveI : Nontrivial U := Submodule.nontrivial_iff_ne_bot.2 hne
  set f₀ : Module.End K (Fin p → K) := Matrix.toLinAlgEquiv' (ŷ : Matrix (Fin p) (Fin p) K)
    with hf₀
  have hf₀p : f₀ ^ p = algebraMap K (Module.End K (Fin p → K)) ω := by
    rw [hf₀, ← map_pow, hy]
    have : (Matrix.scalar (Fin p) ω : Matrix (Fin p) (Fin p) K) =
        algebraMap K (Matrix (Fin p) (Fin p) K) ω := by
      simp [Matrix.algebraMap_eq_diagonal, Matrix.scalar_apply, Pi.algebraMap_def]
    rw [this, AlgEquiv.commutes]
  have hU' : ∀ x ∈ U, f₀ x ∈ U := hU
  set f : U →ₗ[K] U := f₀.restrict hU' with hf
  have hfp0 : f ^ p = algebraMap K (U →ₗ[K] U) ω := by
    rw [hf, Module.End.pow_restrict p hU']
    ext u
    simp [LinearMap.restrict_apply, hf₀p, Module.algebraMap_end_apply]
  have hfp : aeval f (X ^ p - C ω : K[X]) = 0 := by
    rw [map_sub, map_pow, aeval_X, aeval_C, hfp0, sub_self]
  have hirr : Irreducible (X ^ p - C ω : K[X]) := X_pow_sub_C_irreducible_of_prime hp hω
  have hdvd : minpoly K f ∣ (X ^ p - C ω : K[X]) := minpoly.dvd K f hfp
  have hmon : (minpoly K f).Monic := minpoly.monic (LinearMap.isIntegral f)
  have hnu : ¬ IsUnit (minpoly K f) := minpoly.not_isUnit K f
  obtain ⟨g, hg⟩ := hdvd
  have hgu : IsUnit g := (hirr.isUnit_or_isUnit hg).resolve_left hnu
  have hassoc : Associated (minpoly K f) (X ^ p - C ω) :=
    ⟨hgu.unit, by rw [hg, IsUnit.unit_spec]⟩
  have heq : minpoly K f = X ^ p - C ω :=
    eq_of_monic_of_associated hmon (monic_X_pow_sub_C ω hp.ne_zero) hassoc
  have hdeg : (minpoly K f).natDegree ≤ finrank K U := by
    have h1 := LinearMap.minpoly_dvd_charpoly f
    have := Polynomial.natDegree_le_of_dvd h1 (LinearMap.charpoly_monic f).ne_zero
    rwa [LinearMap.charpoly_natDegree] at this
  rw [heq, natDegree_X_pow_sub_C] at hdeg
  have hle : finrank K U ≤ p := by
    simpa using Submodule.finrank_le U
  exact Submodule.eq_top_of_finrank_eq (by simp; omega)


section Translates

variable {G : Subgroup (GL (Fin p) K)} {ŷ : GL (Fin p) K}

@[expose] def trans (ŷ : GL (Fin p) K) (W : Submodule K (Fin p → K)) (j : ℕ) :
    Submodule K (Fin p → K) :=
  W.map (Matrix.mulVecLin ((ŷ ^ j : GL (Fin p) K) : Matrix (Fin p) (Fin p) K))

theorem mem_trans {W : Submodule K (Fin p → K)} {j : ℕ} {u : Fin p → K} :
    u ∈ trans ŷ W j ↔ ∃ w ∈ W, ((ŷ ^ j : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) *ᵥ w = u := by
  simp [trans, Submodule.mem_map]

theorem finrank_trans (W : Submodule K (Fin p → K)) (j : ℕ) :
    finrank K (trans ŷ W j) = finrank K W := by
  have hinj : Function.Injective
      (Matrix.mulVecLin ((ŷ ^ j : GL (Fin p) K) : Matrix (Fin p) (Fin p) K)) := by
    have := Matrix.mulVec_injective_iff_isUnit.2 (Units.isUnit (ŷ ^ j))
    exact this
  exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj W)).symm

theorem ginv_trans {W : Submodule K (Fin p → K)} (hW : GInv G W)
    (hyN : ŷ ∈ normalizer (G : Set (GL (Fin p) K))) (j : ℕ) : GInv G (trans ŷ W j) := by
  refine GInv.map hW (ŷ ^ j) (fun g hg => ?_)
  have h1 : (ŷ ^ j) ∈ normalizer (G : Set (GL (Fin p) K)) := Subgroup.pow_mem _ hyN j
  have h2 := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ h1) g).1 hg
  simpa using h2

theorem mulVec_mem_trans_succ {W : Submodule K (Fin p → K)} {j : ℕ} {u : Fin p → K}
    (hu : u ∈ trans ŷ W j) : (ŷ : Matrix (Fin p) (Fin p) K) *ᵥ u ∈ trans ŷ W (j + 1) := by
  obtain ⟨w, hw, rfl⟩ := mem_trans.1 hu
  refine mem_trans.2 ⟨w, hw, ?_⟩
  rw [Matrix.mulVec_mulVec, pow_succ', Units.val_mul]

theorem trans_p_le {ω : K} (hy : (ŷ : Matrix (Fin p) (Fin p) K) ^ p = Matrix.scalar (Fin p) ω)
    (W : Submodule K (Fin p → K)) : trans ŷ W p ≤ W := by
  intro u hu
  obtain ⟨w, hw, rfl⟩ := mem_trans.1 hu
  rw [Units.val_pow_eq_pow_val, hy]
  have : (Matrix.scalar (Fin p) ω : Matrix (Fin p) (Fin p) K) *ᵥ w = ω • w := by
    ext i
    simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]
  rw [this]
  exact W.smul_mem ω hw

theorem trans_zero (W : Submodule K (Fin p → K)) : trans ŷ W 0 = W := by
  ext u
  rw [mem_trans]
  simp

@[expose] def psum (ŷ : GL (Fin p) K) (W : Submodule K (Fin p → K)) :
    ℕ → Submodule K (Fin p → K)
  | 0 => ⊥
  | j + 1 => psum ŷ W j ⊔ trans ŷ W j

theorem ginv_psum {W : Submodule K (Fin p → K)} (hW : GInv G W)
    (hyN : ŷ ∈ normalizer (G : Set (GL (Fin p) K))) (j : ℕ) : GInv G (psum ŷ W j) := by
  induction j with
  | zero =>
    have h0 : psum ŷ W 0 = ⊥ := rfl
    rw [h0]
    intro g hg w hw
    rw [Submodule.mem_bot] at hw
    simp [hw]
  | succ j ih => exact GInv.sup ih (ginv_trans hW hyN j)

theorem trans_le_psum {W : Submodule K (Fin p → K)} {i j : ℕ} (hij : i < j) :
    trans ŷ W i ≤ psum ŷ W j := by
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h | h
    · exact (ih h).trans le_sup_left
    · rw [h]; exact le_sup_right

theorem psum_mono {W : Submodule K (Fin p → K)} {i j : ℕ} (hij : i ≤ j) :
    psum ŷ W i ≤ psum ŷ W j := by
  induction j with
  | zero => rw [Nat.le_zero.1 hij]
  | succ j ih =>
    rcases Nat.le_succ_iff.1 hij with h | h
    · exact (ih h).trans le_sup_left
    · rw [h]

theorem mulVec_mem_psum_succ {W : Submodule K (Fin p → K)} {j : ℕ} {u : Fin p → K}
    (hu : u ∈ psum ŷ W j) : (ŷ : Matrix (Fin p) (Fin p) K) *ᵥ u ∈ psum ŷ W (j + 1) := by
  induction j generalizing u with
  | zero =>
    have h0 : psum ŷ W 0 = ⊥ := rfl
    rw [h0, Submodule.mem_bot] at hu
    simp [hu]
  | succ j ih =>
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hu
    rw [Matrix.mulVec_add]
    refine Submodule.add_mem _ ?_ ?_
    · exact psum_mono (Nat.le_succ _) (ih ha)
    · exact trans_le_psum (Nat.lt_succ_self _) (mulVec_mem_trans_succ hb)

end Translates


section Main

variable [Finite K] {G : Subgroup (GL (Fin p) K)} {ŷ : GL (Fin p) K}

theorem exists_central_involution (hG2 : IsPGroup 2 G) (hGne : G ≠ ⊥) :
    ∃ a ∈ G, a ≠ 1 ∧ a ^ 2 = 1 ∧ ∀ g ∈ G, g * a = a * g := by
  haveI : Nontrivial ↥G := (Subgroup.nontrivial_iff_ne_bot G).2 hGne
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Nontrivial ↥(Subgroup.center ↥G) := hG2.center_nontrivial
  have hZ2 : IsPGroup 2 ↥(Subgroup.center ↥G) :=
    hG2.of_injective (Subgroup.center ↥G).subtype (Subgroup.subtype_injective _)
  obtain ⟨n, hn⟩ := hZ2.exists_card_eq
  have hn1 : n ≠ 0 := by
    rintro rfl
    have h1 : 1 < Nat.card ↥(Subgroup.center ↥G) := Finite.one_lt_card
    rw [hn] at h1
    simp at h1
  have hdvd : 2 ∣ Nat.card ↥(Subgroup.center ↥G) := by
    rw [hn]
    exact dvd_pow_self 2 hn1
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  refine ⟨((z : ↥G) : GL (Fin p) K), (z : ↥G).2, ?_, ?_, ?_⟩
  · intro h
    have h1 : z = 1 := Subtype.ext (Subtype.ext h)
    rw [h1, orderOf_one] at hz
    omega
  · have h1 : z ^ 2 = 1 := by
      have := pow_orderOf_eq_one z
      rwa [hz] at this
    have h2 := congrArg (fun x : ↥(Subgroup.center ↥G) => ((x : ↥G) : GL (Fin p) K)) h1
    simpa using h2
  · intro g hg
    have := Subgroup.mem_center_iff.1 z.2 ⟨g, hg⟩
    exact congrArg Subtype.val this

theorem eq_one_of_isScalar (hp : p.Prime) (hp2 : p ≠ 2) (hG2 : IsPGroup 2 G)
    (hdet : ∀ g ∈ G, (g : Matrix (Fin p) (Fin p) K).det = 1) {g : GL (Fin p) K} (hg : g ∈ G)
    {c : K} (hs : (g : Matrix (Fin p) (Fin p) K) = Matrix.scalar (Fin p) c) : g = 1 := by
  have hcp : c ^ p = 1 := by
    have h1 := hdet g hg
    rw [hs, Matrix.scalar_apply, Matrix.det_diagonal] at h1
    simpa using h1
  have hgp : g ^ p = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hs, ← map_pow, hcp, map_one, Units.val_one]
  obtain ⟨k, hk⟩ := hG2 ⟨g, hg⟩
  have hk' : g ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  have h1 : orderOf g ∣ p := orderOf_dvd_of_pow_eq_one hgp
  have h2 : orderOf g ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  have hcop : Nat.Coprime (2 ^ k) p :=
    Nat.Coprime.pow_left k ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2))
  have h3 := Nat.dvd_gcd h2 h1
  rw [hcop.gcd_eq_one] at h3
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h3)

theorem eq_zero_of_mulVec_eq_zero {M : Matrix (Fin p) (Fin p) K} (h : ∀ u, M *ᵥ u = 0) :
    M = 0 := by
  apply Matrix.ext_of_mulVec_single
  intro j
  rw [h, Matrix.zero_mulVec]

theorem not_simple_of_central_involution (hp : p.Prime) (hp2 : p ≠ 2) (hG2 : IsPGroup 2 G)
    (hdet : ∀ g ∈ G, (g : Matrix (Fin p) (Fin p) K).det = 1) {a : GL (Fin p) K} (haG : a ∈ G)
    (ha1 : a ≠ 1) (ha2 : a ^ 2 = 1) (hac : ∀ g ∈ G, g * a = a * g)
    (hsimp : ∀ U : Submodule K (Fin p → K), GInv G U → U ≠ ⊥ → U = ⊤) : False := by
  set A : Matrix (Fin p) (Fin p) K := (a : Matrix (Fin p) (Fin p) K) with hA
  have hAA : A * A = 1 := by
    have := congrArg (fun x : GL (Fin p) K => (x : Matrix (Fin p) (Fin p) K)) ha2
    simpa [pow_two] using this
  have hAc : ∀ g ∈ G, (g : Matrix (Fin p) (Fin p) K) * A = A * (g : Matrix (Fin p) (Fin p) K) := by
    intro g hg
    have := congrArg (fun x : GL (Fin p) K => (x : Matrix (Fin p) (Fin p) K)) (hac g hg)
    simpa using this
  set Up : Submodule K (Fin p → K) := LinearMap.ker (Matrix.mulVecLin (A - 1)) with hUp
  have hmem : ∀ u, u ∈ Up ↔ (A - 1) *ᵥ u = 0 := by
    intro u
    simp [hUp, Matrix.sub_mulVec]
  have hUpinv : GInv G Up := by
    intro g hg u hu
    rw [hmem] at hu ⊢
    have : (A - 1) * (g : Matrix (Fin p) (Fin p) K) = (g : Matrix (Fin p) (Fin p) K) * (A - 1) := by
      rw [mul_sub, sub_mul, mul_one, one_mul, hAc g hg]
    rw [Matrix.mulVec_mulVec, this, ← Matrix.mulVec_mulVec, hu, Matrix.mulVec_zero]
  by_cases hUbot : Up = ⊥
  · have hA1 : A = -1 := by
      have h0 : A + 1 = 0 := by
        apply eq_zero_of_mulVec_eq_zero
        intro u
        have : (A + 1) *ᵥ u ∈ Up := by
          rw [hmem, Matrix.mulVec_mulVec]
          have : (A - 1) * (A + 1) = 0 := by
            rw [mul_add, sub_mul, sub_mul, mul_one, one_mul, one_mul, hAA]
            abel
          rw [this, Matrix.zero_mulVec]
        rw [hUbot, Submodule.mem_bot] at this
        exact this
      exact eq_neg_of_add_eq_zero_left h0
    have hd := hdet a haG
    rw [← hA, hA1, Matrix.det_neg, Matrix.det_one, Fintype.card_fin, mul_one,
      (hp.odd_of_ne_two hp2).neg_one_pow] at hd
    have hK : (-1 : K) = 1 := hd
    have h11 : (-1 : Matrix (Fin p) (Fin p) K) = 1 := by
      ext i j
      by_cases hij : i = j
      · subst hij
        simp [hK]
      · simp [Matrix.one_apply_ne hij]
    apply ha1
    apply Units.ext
    rw [Units.val_one, ← hA, hA1, h11]
  · have htop := hsimp Up hUpinv hUbot
    apply ha1
    apply Units.ext
    have h0 : A - 1 = 0 := by
      apply eq_zero_of_mulVec_eq_zero
      intro u
      have : u ∈ Up := by rw [htop]; exact Submodule.mem_top
      exact (hmem u).1 this
    rw [Units.val_one, ← hA]
    exact sub_eq_zero.1 h0


@[expose] def orbitVec (ŷ : GL (Fin p) K) (v₀ : Fin p → K) (j : Fin p) : Fin p → K :=
  ((ŷ ^ (j : ℕ) : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) *ᵥ v₀

theorem exists_common_eigenvector (hp : p.Prime) (hp2 : p ≠ 2) (hG2 : IsPGroup 2 G)
    (hGne : G ≠ ⊥) (hdet : ∀ g ∈ G, (g : Matrix (Fin p) (Fin p) K).det = 1) {ω : K}
    (hy : (ŷ : Matrix (Fin p) (Fin p) K) ^ p = Matrix.scalar (Fin p) ω) (hω : ∀ b : K, b ^ p ≠ ω)
    (hyN : ŷ ∈ normalizer (G : Set (GL (Fin p) K))) :
    ∃ v₀ : Fin p → K, v₀ ≠ 0 ∧
      (∀ g ∈ G, ∃ c : K, (g : Matrix (Fin p) (Fin p) K) *ᵥ v₀ = c • v₀) ∧
      Submodule.span K (Set.range (orbitVec ŷ v₀)) = ⊤ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨a, haG, ha1, ha2, hac⟩ := exists_central_involution hG2 hGne
  have hex : ∃ n, ∃ W : Submodule K (Fin p → K), GInv G W ∧ W ≠ ⊥ ∧ finrank K W = n :=
    ⟨_, ⊤, GInv.top G, top_ne_bot, rfl⟩
  obtain ⟨W, hWinv, hWne, hWd⟩ := Nat.find_spec hex
  set d := Nat.find hex with hd
  have hmin : ∀ U : Submodule K (Fin p → K), GInv G U → U ≠ ⊥ → d ≤ finrank K U :=
    fun U hU hne => Nat.find_min' hex ⟨U, hU, hne, rfl⟩
  have hsum : ∀ j, ∃ m, finrank K (psum ŷ W j) = m * d := by
    intro j
    induction j with
    | zero => exact ⟨0, by rw [show psum ŷ W 0 = ⊥ from rfl, finrank_bot, zero_mul]⟩
    | succ j ih =>
      obtain ⟨m, hm⟩ := ih
      have h1 := Submodule.finrank_sup_add_finrank_inf_eq (psum ŷ W j) (trans ŷ W j)
      have hinv : GInv G (psum ŷ W j ⊓ trans ŷ W j) :=
        (ginv_psum hWinv hyN j).inf (ginv_trans hWinv hyN j)
      have hle : psum ŷ W j ⊓ trans ŷ W j ≤ trans ŷ W j := inf_le_right
      have hdW : finrank K (trans ŷ W j) = d := (finrank_trans W j).trans hWd
      by_cases hbot : psum ŷ W j ⊓ trans ŷ W j = ⊥
      · refine ⟨m + 1, ?_⟩
        rw [hbot, finrank_bot] at h1
        show finrank K ↥(psum ŷ W j ⊔ trans ŷ W j) = (m + 1) * d
        rw [add_mul, one_mul]
        omega
      · have hge := hmin _ hinv hbot
        have hle' := Submodule.finrank_mono hle
        have hfin : finrank K ↥(psum ŷ W j ⊓ trans ŷ W j) = d := by omega
        refine ⟨m, ?_⟩
        show finrank K ↥(psum ŷ W j ⊔ trans ŷ W j) = m * d
        omega
  have hWle : W ≤ psum ŷ W p := by
    have := trans_le_psum (ŷ := ŷ) (W := W) hp.pos
    rwa [trans_zero] at this
  have hptop : psum ŷ W p = ⊤ := by
    refine eq_top_of_stable hp hy hω (fun u hu => ?_) ?_
    · have h1 := mulVec_mem_psum_succ hu
      obtain ⟨a', ha', b, hb, hab⟩ := Submodule.mem_sup.1 h1
      rw [← hab]
      exact Submodule.add_mem _ ha' (hWle (trans_p_le hy W hb))
    · intro hbot
      apply hWne
      exact eq_bot_iff.2 (hbot ▸ hWle)
  obtain ⟨m, hm⟩ := hsum p
  rw [hptop, finrank_top, Module.finrank_fin_fun] at hm
  have hdvd : d ∣ p := ⟨m, by rw [mul_comm]; exact hm⟩
  rcases (Nat.dvd_prime hp).1 hdvd with h1 | hdp
  ·
    have hW1 : finrank K W = 1 := hWd.trans h1
    obtain ⟨v, hv0, hv⟩ := finrank_eq_one_iff'.1 hW1
    have hline : ∀ w ∈ W, ∃ c : K, w = c • (v : Fin p → K) := by
      intro w hw
      obtain ⟨c, hc⟩ := hv ⟨w, hw⟩
      exact ⟨c, (congrArg Subtype.val hc).symm⟩
    have hv0' : (v : Fin p → K) ≠ 0 := fun h => hv0 (Subtype.ext h)
    refine ⟨v, hv0', fun g hg => ?_, ?_⟩
    · obtain ⟨c, hc⟩ := hline _ (hWinv g hg v v.2)
      exact ⟨c, hc⟩
    · rw [eq_top_iff, ← hptop]
      have hle : ∀ j, j ≤ p → psum ŷ W j ≤ Submodule.span K (Set.range (orbitVec ŷ v)) := by
        intro j
        induction j with
        | zero => intro _; exact bot_le
        | succ j ih =>
          intro hj
          refine sup_le (ih (by omega)) ?_
          intro u hu
          obtain ⟨w, hw, rfl⟩ := mem_trans.1 hu
          obtain ⟨c, rfl⟩ := hline w hw
          rw [Matrix.mulVec_smul]
          exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨j, by omega⟩, rfl⟩)
      exact hle p le_rfl
  ·
    exfalso
    refine not_simple_of_central_involution hp hp2 hG2 hdet haG ha1 ha2 hac (fun U hU hne => ?_)
    have h1 := hmin U hU hne
    have h2 : finrank K U ≤ p := by simpa using Submodule.finrank_le U
    exact Submodule.eq_top_of_finrank_eq (by simp; omega)

end Main

section Basis

open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseA

variable {G : Subgroup (GL (Fin p) K)} {ŷ : GL (Fin p) K} {v₀ : Fin p → K}

theorem mulVec_orbitVec (hp : p ≠ 0) {ω : K}
    (hy : (ŷ : Matrix (Fin p) (Fin p) K) ^ p = Matrix.scalar (Fin p) ω) (hω0 : ω ≠ 0)
    (v₀ : Fin p → K) (k : Fin p) :
    ∃ δ : Kˣ, (ŷ : Matrix (Fin p) (Fin p) K) *ᵥ orbitVec ŷ v₀ k =
      (δ : K) • orbitVec ŷ v₀ (finRotate p k) ∧ ((δ : K) = 1 ∨ (δ : K) = ω) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp
  by_cases hk : k = Fin.last n
  · subst hk
    refine ⟨Units.mk0 ω hω0, ?_, Or.inr rfl⟩
    rw [finRotate_last]
    have h0 : orbitVec ŷ v₀ 0 = v₀ := by simp [orbitVec]
    rw [h0]
    simp only [orbitVec, Matrix.mulVec_mulVec, Fin.val_last, Units.val_mk0]
    rw [← Units.val_mul, ← pow_succ', Units.val_pow_eq_pow_val, hy]
    ext i
    simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]
  · refine ⟨1, ?_, Or.inl rfl⟩
    simp only [orbitVec, Matrix.mulVec_mulVec, Units.val_one, one_smul]
    rw [← Units.val_mul, ← pow_succ', coe_finRotate_of_ne_last hk]

@[expose] def orbitMat (ŷ : GL (Fin p) K) (v₀ : Fin p → K) : Matrix (Fin p) (Fin p) K :=
  Matrix.of fun i j => orbitVec ŷ v₀ j i

theorem orbitMat_mulVec_single (j : Fin p) :
    orbitMat ŷ v₀ *ᵥ Pi.single j 1 = orbitVec ŷ v₀ j := by
  rw [Matrix.mulVec_single_one]
  rfl

theorem isUnit_orbitMat (hsp : Submodule.span K (Set.range (orbitVec ŷ v₀)) = ⊤) :
    IsUnit (orbitMat ŷ v₀) := by
  rw [← Matrix.linearIndependent_cols_iff_isUnit]
  have hcol : (orbitMat ŷ v₀).col = orbitVec ŷ v₀ := rfl
  rw [hcol]
  exact linearIndependent_of_top_le_span_of_card_eq_finrank hsp.ge (by simp)

theorem eigen_orbit (hv0 : v₀ ≠ 0)
    (hev : ∀ g ∈ G, ∃ c : K, (g : Matrix (Fin p) (Fin p) K) *ᵥ v₀ = c • v₀)
    (hyN : ŷ ∈ normalizer (G : Set (GL (Fin p) K))) {g : GL (Fin p) K} (hg : g ∈ G) (j : Fin p) :
    ∃ c : Kˣ, (g : Matrix (Fin p) (Fin p) K) *ᵥ orbitVec ŷ v₀ j =
      (c : K) • orbitVec ŷ v₀ j := by
  have h1 : (ŷ ^ (j : ℕ)) ∈ normalizer (G : Set (GL (Fin p) K)) := Subgroup.pow_mem _ hyN _
  have hg' : (ŷ ^ (j : ℕ))⁻¹ * g * ŷ ^ (j : ℕ) ∈ G := by
    have h2 := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ h1) g).1 hg
    simpa using h2
  obtain ⟨c, hc⟩ := hev _ hg'
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hc
    apply hv0
    have hinj := Matrix.mulVec_injective_iff_isUnit.2
      (Units.isUnit ((ŷ ^ (j : ℕ))⁻¹ * g * ŷ ^ (j : ℕ)))
    apply hinj
    rw [hc, Matrix.mulVec_zero]
  refine ⟨Units.mk0 c hc0, ?_⟩
  have e : g * ŷ ^ (j : ℕ) = ŷ ^ (j : ℕ) * ((ŷ ^ (j : ℕ))⁻¹ * g * ŷ ^ (j : ℕ)) := by group
  have e' : (g : Matrix (Fin p) (Fin p) K) * ((ŷ ^ (j : ℕ) : GL (Fin p) K) :
      Matrix (Fin p) (Fin p) K) = ((ŷ ^ (j : ℕ) : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) *
        (((ŷ ^ (j : ℕ))⁻¹ * g * ŷ ^ (j : ℕ) : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) := by
    rw [← Units.val_mul, ← Units.val_mul, e]
  simp only [orbitVec, Units.val_mk0]
  rw [Matrix.mulVec_mulVec, e', ← Matrix.mulVec_mulVec, hc, Matrix.mulVec_smul]


theorem rotGL_mulVec_single (j : Fin p) (c : K) :
    ((rotGL p K : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) *ᵥ Pi.single j c =
      Pi.single (finRotate p j) c := by
  rw [rotGL_val, Matrix.permMatrix_mulVec]
  ext i
  simp only [Function.comp_apply, Pi.single_apply, Equiv.Perm.inv_def, Equiv.symm_apply_eq]

theorem diagGL_mulVec_single (d : Fin p → Kˣ) (j : Fin p) (c : K) :
    ((diagGL p K d : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) *ᵥ Pi.single j c =
      Pi.single j ((d j : K) * c) := by
  rw [diagGL_val, Matrix.diagonal_mulVec_single]

theorem conj_orbit_diag (B : GL (Fin p) K)
    (hBe : ∀ j, (B : Matrix (Fin p) (Fin p) K) *ᵥ Pi.single j 1 = orbitVec ŷ v₀ j)
    {g : GL (Fin p) K} {d : Fin p → Kˣ}
    (hd : ∀ j, (g : Matrix (Fin p) (Fin p) K) *ᵥ orbitVec ŷ v₀ j =
      (d j : K) • orbitVec ŷ v₀ j) : B⁻¹ * g * B = diagGL p K d := by
  have hBinv : ∀ j, ((B⁻¹ : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) *ᵥ orbitVec ŷ v₀ j =
      Pi.single j 1 := by
    intro j
    rw [← hBe j, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec]
  apply Units.ext
  apply Matrix.ext_of_mulVec_single
  intro j
  rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hBe, hd j,
    Matrix.mulVec_smul, hBinv, diagGL_mulVec_single]
  ext i
  by_cases h : i = j <;> simp [Pi.single_apply, h]

theorem conj_orbit_rot (B : GL (Fin p) K)
    (hBe : ∀ j, (B : Matrix (Fin p) (Fin p) K) *ᵥ Pi.single j 1 = orbitVec ŷ v₀ j)
    {δ : Fin p → Kˣ}
    (hδ : ∀ k, (ŷ : Matrix (Fin p) (Fin p) K) *ᵥ orbitVec ŷ v₀ k =
      (δ k : K) • orbitVec ŷ v₀ (finRotate p k)) : B⁻¹ * ŷ * B = rotGL p K * diagGL p K δ := by
  have hBinv : ∀ j, ((B⁻¹ : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) *ᵥ orbitVec ŷ v₀ j =
      Pi.single j 1 := by
    intro j
    rw [← hBe j, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec]
  apply Units.ext
  apply Matrix.ext_of_mulVec_single
  intro j
  rw [Units.val_mul, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, hBe, hδ j, Matrix.mulVec_smul, hBinv, ← Matrix.mulVec_mulVec,
    diagGL_mulVec_single, rotGL_mulVec_single]
  ext i
  by_cases h : i = finRotate p j <;> simp [Pi.single_apply, h]

end Basis

section Characters

variable {G : Subgroup (GL (Fin p) K)} {ŷ : GL (Fin p) K} {v₀ : Fin p → K}

@[expose] def HasEv (ŷ : GL (Fin p) K) (v₀ : Fin p → K) (g : GL (Fin p) K) (k : Fin p) (c : K) :
    Prop :=
  (g : Matrix (Fin p) (Fin p) K) *ᵥ orbitVec ŷ v₀ k = c • orbitVec ŷ v₀ k

theorem orbitVec_ne_zero (hv0 : v₀ ≠ 0) (k : Fin p) : orbitVec ŷ v₀ k ≠ 0 := by
  intro h
  apply hv0
  have hinj := Matrix.mulVec_injective_iff_isUnit.2 (Units.isUnit (ŷ ^ (k : ℕ)))
  apply hinj
  rw [Matrix.mulVec_zero]
  exact h

theorem HasEv.unique (hv0 : v₀ ≠ 0) {g : GL (Fin p) K} {k : Fin p} {c c' : K}
    (h : HasEv ŷ v₀ g k c) (h' : HasEv ŷ v₀ g k c') : c = c' :=
  smul_left_injective K (orbitVec_ne_zero (ŷ := ŷ) hv0 k) (h.symm.trans h')

theorem HasEv.shift (hp : p ≠ 0) {ω : K}
    (hy : (ŷ : Matrix (Fin p) (Fin p) K) ^ p = Matrix.scalar (Fin p) ω) (hω0 : ω ≠ 0)
    {g : GL (Fin p) K} {k : Fin p} {c : K} (h : HasEv ŷ v₀ g k c) :
    HasEv ŷ v₀ (ŷ * g * ŷ⁻¹) (finRotate p k) c := by
  obtain ⟨δ, hδ, -⟩ := mulVec_orbitVec hp hy hω0 v₀ k
  have hδ' : orbitVec ŷ v₀ (finRotate p k) =
      ((δ⁻¹ : Kˣ) : K) • ((ŷ : Matrix (Fin p) (Fin p) K) *ᵥ orbitVec ŷ v₀ k) := by
    rw [hδ, smul_smul, Units.val_inv_eq_inv_val, inv_mul_cancel₀ δ.ne_zero, one_smul]
  unfold HasEv at h ⊢
  rw [hδ', Matrix.mulVec_smul, Matrix.mulVec_mulVec]
  have e : ŷ * g * ŷ⁻¹ * ŷ = ŷ * g := by group
  have e' : ((ŷ * g * ŷ⁻¹ : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) *
      (ŷ : Matrix (Fin p) (Fin p) K) = (ŷ : Matrix (Fin p) (Fin p) K) *
        (g : Matrix (Fin p) (Fin p) K) := by
    rw [← Units.val_mul, e, Units.val_mul]
  rw [e', ← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul, smul_comm]

theorem entry_eq_of_hasEv (B : GL (Fin p) K)
    (hBe : ∀ j, (B : Matrix (Fin p) (Fin p) K) *ᵥ Pi.single j 1 = orbitVec ŷ v₀ j)
    {g : GL (Fin p) K} {k : Fin p} {c : K} (h : HasEv ŷ v₀ g k c) :
    ((B⁻¹ * g * B : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) k k = c := by
  have hBinv : ((B⁻¹ : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) *ᵥ orbitVec ŷ v₀ k =
      Pi.single k 1 := by
    rw [← hBe k, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec]
  have h1 : ((B⁻¹ * g * B : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) *ᵥ Pi.single k 1 =
      c • Pi.single k 1 := by
    rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hBe, h,
      Matrix.mulVec_smul, hBinv]
  have h2 := congrFun h1 k
  rw [Matrix.mulVec_single_one] at h2
  simpa using h2

variable [Finite K]

theorem eq_bot_of_not_separated (hp : p.Prime) (hp2 : p ≠ 2) (hG2 : IsPGroup 2 G)
    (hdet : ∀ g ∈ G, (g : Matrix (Fin p) (Fin p) K).det = 1) {ω : K}
    (hy : (ŷ : Matrix (Fin p) (Fin p) K) ^ p = Matrix.scalar (Fin p) ω) (hω0 : ω ≠ 0)
    (hyN : ŷ ∈ normalizer (G : Set (GL (Fin p) K))) (hv0 : v₀ ≠ 0)
    (hev : ∀ g ∈ G, ∃ c : K, (g : Matrix (Fin p) (Fin p) K) *ᵥ v₀ = c • v₀)
    (hsp : Submodule.span K (Set.range (orbitVec ŷ v₀)) = ⊤) {i j : Fin p} (hij : i ≠ j)
    (H : ∀ g ∈ G, ∀ c c' : K, HasEv ŷ v₀ g i c → HasEv ŷ v₀ g j c' → c = c') : G = ⊥ := by
  classical
  set σ : Equiv.Perm (Fin p) := finRotate p with hσ
  have hp2' : 2 ≤ p := hp.two_le
  have hp0 : p ≠ 0 := hp.ne_zero
  have hcyc : σ.IsCycle := isCycle_finRotate_of_le hp2'
  have hord : orderOf σ = p := by
    rw [hcyc.orderOf, hσ, support_finRotate_of_le hp2', Finset.card_univ, Fintype.card_fin]
  have hmove : ∀ x, σ x ≠ x := fun x => by
    have : x ∈ σ.support := by
      rw [hσ, support_finRotate_of_le hp2']
      exact Finset.mem_univ x
    exact Equiv.Perm.mem_support.1 this
  have hex : ∀ g ∈ G, ∀ k, ∃ c, HasEv ŷ v₀ g k c := fun g hg k => by
    obtain ⟨c, hc⟩ := eigen_orbit hv0 hev hyN hg k
    exact ⟨c, hc⟩
  have hGconj : ∀ g ∈ G, ŷ⁻¹ * g * ŷ ∈ G := by
    intro g hg
    have h2 := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hyN) g).1 hg
    simpa using h2
  have hback : ∀ g ∈ G, ∀ k c, HasEv ŷ v₀ (ŷ * g * ŷ⁻¹) (σ k) c → HasEv ŷ v₀ g k c := by
    intro g hg k c h
    obtain ⟨c₀, hc₀⟩ := hex g hg k
    have h1 := HasEv.shift hp0 hy hω0 hc₀
    have h2 := HasEv.unique hv0 h1 h
    rw [← h2]
    exact hc₀
  have hcl : ∀ m : ℕ, ∀ g ∈ G, ∀ c c' : K, HasEv ŷ v₀ g ((σ ^ m) i) c →
      HasEv ŷ v₀ g ((σ ^ m) j) c' → c = c' := by
    intro m
    induction m with
    | zero =>
      intro g hg c c' h h'
      exact H g hg c c' (by simpa using h) (by simpa using h')
    | succ m ih =>
      intro g hg c c' h h'
      have hg' := hGconj g hg
      have e : ŷ * (ŷ⁻¹ * g * ŷ) * ŷ⁻¹ = g := by group
      have h1 : HasEv ŷ v₀ (ŷ * (ŷ⁻¹ * g * ŷ) * ŷ⁻¹) (σ ((σ ^ m) i)) c := by
        rw [e]
        simpa [pow_succ', Equiv.Perm.mul_apply] using h
      have h3 : HasEv ŷ v₀ (ŷ * (ŷ⁻¹ * g * ŷ) * ŷ⁻¹) (σ ((σ ^ m) j)) c' := by
        rw [e]
        simpa [pow_succ', Equiv.Perm.mul_apply] using h'
      exact ih _ hg' c c' (hback _ hg' _ c h1) (hback _ hg' _ c' h3)
  obtain ⟨s, hs⟩ := hcyc.exists_pow_eq (hmove i) (hmove j)
  have hσp : σ ^ p = 1 := by
    have := pow_orderOf_eq_one σ
    rwa [hord] at this
  have hps : ¬ p ∣ s := by
    rintro ⟨t, rfl⟩
    apply hij
    rw [← hs, pow_mul, hσp, one_pow]
    rfl
  have hcop : Nat.Coprime s p := ((Nat.Prime.coprime_iff_not_dvd hp).2 hps).symm
  obtain ⟨t, -, ht⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
  have hσt : σ ^ (s * t) = σ := by
    rw [← pow_mod_orderOf, hord, ht, pow_one]
  have hP1 : ∀ g ∈ G, ∀ u : Fin p, ∀ c c' : K, HasEv ŷ v₀ g u c →
      HasEv ŷ v₀ g ((σ ^ s) u) c' → c = c' := by
    intro g hg u c c' h h'
    obtain ⟨m, hm⟩ := hcyc.exists_pow_eq (hmove i) (hmove u)
    have hcomm : (σ ^ m) j = (σ ^ s) ((σ ^ m) i) := by
      rw [← hs, ← Equiv.Perm.mul_apply, ← Equiv.Perm.mul_apply, ← pow_add, ← pow_add, add_comm]
    refine hcl m g hg c c' (by rw [hm]; exact h) (by rw [hcomm, hm]; exact h')
  have hP2 : ∀ g ∈ G, ∀ n : ℕ, ∀ u : Fin p, ∀ c c' : K, HasEv ŷ v₀ g u c →
      HasEv ŷ v₀ g ((σ ^ (s * n)) u) c' → c = c' := by
    intro g hg n
    induction n with
    | zero =>
      intro u c c' h h'
      exact HasEv.unique hv0 h (by simpa using h')
    | succ n ih =>
      intro u c c' h h'
      have e : (σ ^ (s * (n + 1))) u = (σ ^ s) ((σ ^ (s * n)) u) := by
        rw [show s * (n + 1) = s + s * n by ring, pow_add, Equiv.Perm.mul_apply]
      rw [e] at h'
      obtain ⟨c₁, hc₁⟩ := hex g hg ((σ ^ (s * n)) u)
      exact (ih u c c₁ h hc₁).trans (hP1 g hg _ c₁ c' hc₁ h')
  have hP3 : ∀ g ∈ G, ∀ u : Fin p, ∀ c c' : K, HasEv ŷ v₀ g u c →
      HasEv ŷ v₀ g (σ u) c' → c = c' := by
    intro g hg u c c' h h'
    refine hP2 g hg t u c c' h ?_
    rw [hσt]
    exact h'
  have hP4 : ∀ g ∈ G, ∀ n : ℕ, ∀ u : Fin p, ∀ c c' : K, HasEv ŷ v₀ g u c →
      HasEv ŷ v₀ g ((σ ^ n) u) c' → c = c' := by
    intro g hg n
    induction n with
    | zero =>
      intro u c c' h h'
      exact HasEv.unique hv0 h (by simpa using h')
    | succ n ih =>
      intro u c c' h h'
      have e : (σ ^ (n + 1)) u = σ ((σ ^ n) u) := by
        rw [pow_succ', Equiv.Perm.mul_apply]
      rw [e] at h'
      obtain ⟨c₁, hc₁⟩ := hex g hg ((σ ^ n) u)
      exact (ih u c c₁ h hc₁).trans (hP3 g hg _ c₁ c' hc₁ h')
  have hP5 : ∀ g ∈ G, ∀ u u' : Fin p, ∀ c c' : K, HasEv ŷ v₀ g u c → HasEv ŷ v₀ g u' c' →
      c = c' := by
    intro g hg u u' c c' h h'
    obtain ⟨n, hn⟩ := hcyc.exists_pow_eq (hmove u) (hmove u')
    exact hP4 g hg n u c c' h (by rw [hn]; exact h')
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  obtain ⟨c₀, hc₀⟩ := hex g hg ⟨0, hp.pos⟩
  have hall : ∀ k, HasEv ŷ v₀ g k c₀ := by
    intro k
    obtain ⟨c, hc⟩ := hex g hg k
    rw [hP5 g hg ⟨0, hp.pos⟩ k c₀ c hc₀ hc]
    exact hc
  have hlin : Matrix.mulVecLin (g : Matrix (Fin p) (Fin p) K) = c₀ • LinearMap.id := by
    apply LinearMap.ext_on hsp
    rintro _ ⟨k, rfl⟩
    simpa [HasEv] using hall k
  have hs : (g : Matrix (Fin p) (Fin p) K) = Matrix.scalar (Fin p) c₀ := by
    apply Matrix.ext_of_mulVec_single
    intro j
    have := LinearMap.congr_fun hlin (Pi.single j 1)
    simp only [Matrix.mulVecLin_apply, LinearMap.smul_apply, LinearMap.id_apply] at this
    rw [this, Matrix.scalar_apply, Matrix.diagonal_mulVec_single]
    ext i
    by_cases h : i = j <;> simp [Pi.single_apply, h]
  exact eq_one_of_isScalar hp hp2 hG2 hdet hg hs

end Characters

section Final

open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseA

variable [Finite K] {G : Subgroup (GL (Fin p) K)} {ŷ : GL (Fin p) K}

theorem exists_diag_basis (hp : p.Prime) (hp2 : p ≠ 2) (hG2 : IsPGroup 2 G) (hGne : G ≠ ⊥)
    (hdet : ∀ g ∈ G, (g : Matrix (Fin p) (Fin p) K).det = 1) {ω : K}
    (hy : (ŷ : Matrix (Fin p) (Fin p) K) ^ p = Matrix.scalar (Fin p) ω) (hω : ∀ b : K, b ^ p ≠ ω)
    (hyN : ŷ ∈ normalizer (G : Set (GL (Fin p) K))) :
    ∃ B : GL (Fin p) K, ∃ δ : Fin p → Kˣ,
      B⁻¹ * ŷ * B = rotGL p K * diagGL p K δ ∧ (∀ j, (δ j : K) = 1 ∨ (δ j : K) = ω) ∧
      (∀ g ∈ G, ∃ d : Fin p → Kˣ, B⁻¹ * g * B = diagGL p K d) ∧
      (∀ i j : Fin p, i ≠ j → ∃ g ∈ G,
        ((B⁻¹ * g * B : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) i i ≠
          ((B⁻¹ * g * B : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) j j) := by
  classical
  have hp0 : p ≠ 0 := hp.ne_zero
  have hω0 : ω ≠ 0 := by
    intro h
    exact hω 0 (by rw [zero_pow hp0, h])
  obtain ⟨v₀, hv0, hev, hsp⟩ := exists_common_eigenvector hp hp2 hG2 hGne hdet hy hω hyN
  have hU := isUnit_orbitMat hsp
  set B : GL (Fin p) K := hU.unit with hB
  have hBcoe : (B : Matrix (Fin p) (Fin p) K) = orbitMat ŷ v₀ := rfl
  have hBe : ∀ j, (B : Matrix (Fin p) (Fin p) K) *ᵥ Pi.single j 1 = orbitVec ŷ v₀ j := fun j => by
    rw [hBcoe]
    exact orbitMat_mulVec_single j
  choose δ hδ using mulVec_orbitVec hp0 hy hω0 v₀
  refine ⟨B, δ, conj_orbit_rot B hBe (fun k => (hδ k).1), fun j => (hδ j).2, ?_, ?_⟩
  · intro g hg
    choose d hd using eigen_orbit hv0 hev hyN hg
    exact ⟨d, conj_orbit_diag B hBe hd⟩
  · intro i j hij
    by_contra hcon
    push Not at hcon
    refine hGne (eq_bot_of_not_separated hp hp2 hG2 hdet hy hω0 hyN hv0 hev hsp hij ?_)
    intro g hg c c' h h'
    rw [← entry_eq_of_hasEv B hBe h, ← entry_eq_of_hasEv B hBe h']
    exact hcon g hg

end Final




end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseB
