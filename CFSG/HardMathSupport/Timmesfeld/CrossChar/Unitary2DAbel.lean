module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Unitary2DGood
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Unitary2DLift
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Unitary2DCount
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Unitary45Main
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.OrthQ2SpFamily
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Unitary2DBase

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open Polynomial Module Matrix CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.RankThree.PartOne.KCUnitaryPlane CFSG.RankThree.PartOne.KCUnitaryExact
  CFSG.RankThree.PartOne.KCUnitaryOne CFSG.RankThree.PartOne.KCUnitaryFrame
  CFSG.RankThree.PartOne.KCUnitaryScalar CFSG.HardMathSupport.Timmesfeld.Balance

section Triple

variable {G : Type*} [Group G]

theorem pow_val_add_of_pow_three {a : G} (ha : a ^ 3 = 1) (x y : ZMod 3) :
    a ^ (x + y).val = a ^ x.val * a ^ y.val := by
  rw [ZMod.val_add, ← pow_add]
  conv_rhs => rw [← Nat.mod_add_div (x.val + y.val) 3, pow_add, pow_mul, ha, one_pow, mul_one]

@[expose] def homOfTriple (a : Fin 3 → G) (ha : ∀ k, a k ^ 3 = 1)
    (hc : ∀ k l, Commute (a k) (a l)) : Multiplicative Z3 →* G where
  toFun z := a 0 ^ (Multiplicative.toAdd z 0).val * a 1 ^ (Multiplicative.toAdd z 1).val *
    a 2 ^ (Multiplicative.toAdd z 2).val
  map_one' := by simp
  map_mul' z z' := by
    simp only [toAdd_mul, Pi.add_apply, pow_val_add_of_pow_three (ha _)]
    rw [((hc 0 1).pow_pow _ _).mul_mul_mul_comm,
      ((((hc 0 2).pow_pow _ _).mul_left ((hc 1 2).pow_pow _ _))).mul_mul_mul_comm]

theorem decomp_z3 (z : Z3) :
    z = (z 0).val • Pi.single 0 1 + (z 1).val • Pi.single 1 1 + (z 2).val • Pi.single 2 1 := by
  funext j
  simp only [Pi.add_apply, Pi.smul_apply]
  fin_cases j <;> simp [nsmul_eq_mul]

theorem comp_homOfTriple {G' : Type*} [Group G'] (ψ : G →* G') (a : Fin 3 → G)
    (ha : ∀ k, a k ^ 3 = 1) (hc : ∀ k l, Commute (a k) (a l)) (χ : Multiplicative Z3 →* G')
    (hχ : ∀ k, χ (Multiplicative.ofAdd (Pi.single k 1)) = ψ (a k)) (z : Multiplicative Z3) :
    ψ (homOfTriple a ha hc z) = χ z := by
  have hz : z = Multiplicative.ofAdd (Pi.single 0 1) ^ (Multiplicative.toAdd z 0).val *
      Multiplicative.ofAdd (Pi.single 1 1) ^ (Multiplicative.toAdd z 1).val *
      Multiplicative.ofAdd (Pi.single 2 1) ^ (Multiplicative.toAdd z 2).val := by
    apply Multiplicative.toAdd.injective
    simp only [toAdd_mul, toAdd_pow, toAdd_ofAdd]
    exact decomp_z3 _
  conv_rhs => rw [hz]
  simp only [homOfTriple, MonoidHom.coe_mk, OneHom.coe_mk, map_mul, map_pow, hχ]

end Triple

section Basis

variable {ℓ f n : ℕ} {K : Type} [Field K] {h : UnitaryFieldData ℓ f K}

theorem exists_orthonormal_eigenbasis_of_hom (hq : ℓ ^ f = 2) {G : Type*} [Group G] [Finite G]
    (φ : G →* primeFormUnitary h (idGram K n)) (hcomm : ∀ x y, Commute (φ x) (φ y))
    (hpow : ∀ x, φ x ^ 3 = 1) :
    ∃ b : Module.Basis (Fin n) K (Fin n → K), IsOrthonormalFamily h b ∧
      ∀ x i, ∃ c : K, ((φ x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ b i = c • b i := by
  have := h.finite
  have hpq : 3 ∣ ℓ ^ f + 1 := by rw [hq]
  obtain ⟨ζ, hζ⟩ := KCUnitaryPlane.exists_primitiveRoot_of_dvd h Nat.prime_three hpq
  set g : G → Module.End K (Fin n → K) := fun x =>
    ((toLinU h n (φ x) : LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K))
    with hg
  have hgc : ∀ x y, Commute (g x) (g y) := fun x y => by
    change (toLinU h n (φ x) : Module.End K (Fin n → K)) * toLinU h n (φ y) =
      (toLinU h n (φ y) : Module.End K (Fin n → K)) * toLinU h n (φ x)
    rw [← Units.val_mul, ← Units.val_mul, ← map_mul (toLinU h n), ← map_mul (toLinU h n),
      (hcomm x y).eq]
  have hgp : ∀ x, g x ^ 3 = 1 := fun x => by
    change (toLinU h n (φ x) : Module.End K (Fin n → K)) ^ 3 = 1
    rw [← Units.val_pow_eq_pow_val, ← map_pow, hpow x, map_one, Units.val_one]
  have hiso : ∀ x v w, idForm h n (g x v) (g x w) = idForm h n v w := fun x v w =>
    idForm_mulVec_of_mem (φ x) v w
  obtain ⟨b, μ, hbμ, hbo⟩ := exists_orthonormal_common_eigenbasis h hζ hpq
    (idForm_isSymm h n) (idForm_separatingLeft h n) g hgc hgp hiso
  refine ⟨b.reindex (finCongr (Module.finrank_fin_fun K)), fun i j => ?_, fun x i => ?_⟩
  · rw [Module.Basis.reindex_apply, Module.Basis.reindex_apply, hbo]
    simp
  · rw [Module.Basis.reindex_apply]
    exact ⟨μ x _, hbμ x _⟩

theorem exists_eigen_of_commute_of_unique {G : Type*} (b : Module.Basis (Fin n) K (Fin n → K))
    (X : G → Matrix (Fin n) (Fin n) K) (χ : G → Fin n → K) (hX : ∀ g k, X g *ᵥ b k = χ g k • b k)
    (S : Matrix (Fin n) (Fin n) K) (hSX : ∀ g, X g * S = S * X g) (l : Fin n)
    (hl : ∀ k, (∀ g, χ g k = χ g l) → k = l) : ∃ a : K, S *ᵥ b l = a • b l := by
  classical
  set v : Fin n → K := S *ᵥ b l with hv
  set α : Fin n → K := fun k => b.repr v k with hα
  have hvα : v = ∑ k, α k • b k := (b.sum_repr v).symm
  have hsupp : ∀ k, α k ≠ 0 → k = l := by
    intro k hk
    refine hl k fun g => ?_
    have e1 : X g *ᵥ v = χ g l • v := by
      rw [hv, Matrix.mulVec_mulVec, hSX g, ← Matrix.mulVec_mulVec, hX, Matrix.mulVec_smul]
    have e2 : X g *ᵥ v = ∑ k, (α k * χ g k) • b k := by
      conv_lhs => rw [hvα]
      simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, hX, smul_smul]
    have e3 : χ g l • v = ∑ k, (χ g l * α k) • b k := by
      conv_lhs => rw [hvα]
      simp only [Finset.smul_sum, smul_smul]
    have e4 := congrArg (fun w => b.repr w k) (e2.symm.trans (e1.trans e3))
    simp only [Module.Basis.repr_sum_self] at e4
    have e5 : α k * (χ g k - χ g l) = 0 := by linear_combination e4
    rcases mul_eq_zero.1 e5 with h1 | h1
    · exact absurd h1 hk
    · exact sub_eq_zero.1 h1
  refine ⟨α l, ?_⟩
  rw [hvα, Finset.sum_eq_single l (fun k _ hkl => ?_) (fun h' => absurd (Finset.mem_univ l) h')]
  by_contra hne
  exact hkl (hsupp k fun h0 => hne (by rw [h0, zero_smul]))

end Basis

section Main

variable {ℓ f n : ℕ} {K : Type} [Field K] {h : UnitaryFieldData ℓ f K}

theorem card_multiplicative_z3 : Nat.card (Multiplicative Z3) = 27 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, Fintype.card_fun, ZMod.card,
    Fintype.card_fin]
  norm_num

theorem localDeltaIn_eq_bot_of_abel (hn : 6 ≤ n) (hq : ℓ ^ f = 2)
    {D : Subgroup (MulAut (primeFormP h (idGram K n)))} (hD : IsElemAbelian 3 D)
    (hcard : Nat.card D = 27) (hDl : D ≤ primeFormD h (idGram K n))
    (hcube : ∀ Y : primeFormUnitary h (idGram K n), primeFormConjHom h (idGram K n) Y ∈ D →
      Y ^ 3 = 1)
    (hcomm : ∀ Y Y' : primeFormUnitary h (idGram K n), primeFormConjHom h (idGram K n) Y ∈ D →
      primeFormConjHom h (idGram K n) Y' ∈ D → Y * Y' = Y' * Y)
    {H : Subgroup (MulAut (primeFormP h (idGram K n)))}
    (hH : (MulAut.conj : primeFormP h (idGram K n) →*
      MulAut (primeFormP h (idGram K n))).range ≤ H) :
    localDeltaIn 3 H D = ⊥ := by
  classical
  have := h.finite
  have hp3 : Nat.Prime 3 := Nat.prime_three
  have hn3 : 3 ≤ n := by omega
  have hne : ¬(n = 3 ∧ ℓ ^ f = 2) := fun h' => by omega
  have : Finite (primeFormP h (idGram K n)) := finite_primeFormP
  let _ : CommGroup D := { (inferInstance : Group D) with
    mul_comm := fun a b => hD.1.is_comm.comm a b }
  obtain ⟨e⟩ := exists_mulEquiv_z3 (G := D) (fun g => Subtype.ext (hD.2 g g.2)) hcard
  have hlift : ∀ k : Fin 3, ∃ A : primeFormUnitary h (idGram K n),
      primeFormConjHom h (idGram K n) A = (e.symm (Multiplicative.ofAdd (Pi.single k 1)) : D) :=
    fun k => hDl (e.symm (Multiplicative.ofAdd (Pi.single k 1))).2
  choose a ha using hlift
  have haD : ∀ k, primeFormConjHom h (idGram K n) (a k) ∈ D := fun k => by
    rw [ha]; exact Subtype.prop _
  set φ := homOfTriple a (fun k => hcube _ (haD k)) (fun k l => hcomm _ _ (haD k) (haD l)) with hφ
  set χ : Multiplicative Z3 →* MulAut (primeFormP h (idGram K n)) :=
    D.subtype.comp e.symm.toMonoidHom with hχ
  have hρφ : ∀ z, primeFormConjHom h (idGram K n) (φ z) = χ z :=
    comp_homOfTriple _ a _ _ χ fun k => by rw [ha]; rfl
  have hφD : ∀ z, primeFormConjHom h (idGram K n) (φ z) ∈ D := fun z => by
    rw [hρφ]; exact Subtype.prop _
  have hφ1 : ∀ z, z ≠ 1 → primeFormConjHom h (idGram K n) (φ z) ≠ 1 := by
    intro z hz h1
    rw [hρφ] at h1
    apply hz
    have : (e.symm z : D) = 1 := Subtype.ext h1
    simpa using this
  have hφ3 : ∀ z, φ z ^ 3 = 1 := fun z => hcube _ (hφD z)
  have hφc : ∀ z z', Commute (φ z) (φ z') := fun z z' => hcomm _ _ (hφD z) (hφD z')
  obtain ⟨b, hbON, hbeig⟩ := exists_orthonormal_eigenbasis_of_hom hq φ hφc hφ3
  have hchar : ∀ i : Fin n, ∃ c : Multiplicative Z3 →* Kˣ, ∀ z,
      ((toLinU h n (φ z) : LinearMap.GeneralLinearGroup K (Fin n → K)) :
        Module.End K (Fin n → K)) (b i) = (c z : K) • b i := fun i =>
    exists_charHom ((toLinU h n).comp φ) (b.ne_zero i) (fun z => hbeig z i)
  choose c hc using hchar
  have hX : ∀ z k, ((φ z : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ b k = (c k z : K) • b k :=
    fun z k => hc k z
  have hc3 : ∀ k z, c k z ^ 3 = 1 := fun k z => by
    have hz : z ^ 3 = 1 := by
      apply Multiplicative.toAdd.injective
      funext j
      simp only [toAdd_pow, toAdd_one, Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul]
      have : ((3 : ℕ) : ZMod 3) = 0 := by decide
      rw [this, zero_mul]
    rw [← map_pow, hz, map_one]
  have hG : Nat.card (Multiplicative Z3) = 27 := card_multiplicative_z3
  have hdim_of : ∀ (z : Multiplicative Z3) (i : Fin n),
      4 ≤ (Finset.univ.filter fun k => c k z = c i z).card →
        4 ≤ Module.finrank K (primaryComponent ((toLinU h n (φ z) :
          LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K))
            (X - C (c i z : K))) := by
    intro z i h4
    set S := Finset.univ.filter fun k => c k z = c i z with hS
    have hli : LinearIndependent K (fun k : S => b (k : Fin n)) :=
      b.linearIndependent.comp _ Subtype.val_injective
    have hle : Submodule.span K (Set.range fun k : S => b (k : Fin n)) ≤
        primaryComponent ((toLinU h n (φ z) : LinearMap.GeneralLinearGroup K (Fin n → K)) :
          Module.End K (Fin n → K)) (X - C (c i z : K)) := by
      rw [Submodule.span_le]
      rintro _ ⟨⟨k, hk⟩, rfl⟩
      refine mem_primaryComponent_X_sub_C.2 ?_
      rw [hc k z, (Finset.mem_filter.1 hk).2]
    have := Submodule.finrank_mono hle
    rw [finrank_span_eq_card hli, Fintype.card_coe] at this
    omega
  have hgood : ∃ z : Multiplicative Z3, z ≠ 1 ∧ ∃ i : Fin n,
      4 ≤ (Finset.univ.filter fun k => c k z = c i z).card := by
    by_cases h7 : 7 ≤ n
    · obtain ⟨z, hz1, -, h4⟩ := exists_four_of_chars hG h7 c hc3 ⟨0, by omega⟩ ⟨1, by omega⟩
        (by simp [Fin.ext_iff])
      exact ⟨z, hz1, _, h4⟩
    · by_cases hinj : Function.Injective c
      · have h6 : n = 6 := by omega
        subst h6
        exact exists_four_of_six hG (card_units_eq_three h hq) hc3 hinj
      · obtain ⟨i, j, hij, hne'⟩ : ∃ i j : Fin n, c i = c j ∧ i ≠ j := by
          by_contra hcon
          push Not at hcon
          exact hinj fun i j hij => hcon i j hij
        obtain ⟨z, hz1, h4⟩ := exists_four_of_eq_chars hc3 hG hn hne' hij
        exact ⟨z, hz1, i, h4⟩
  refine eq_bot_iff.2 fun g hg => ?_
  rw [Subgroup.mem_bot]
  obtain ⟨⟨M, τ⟩, rfl⟩ := surjective_primeFormPsi_of_ne (h := h) hn3 hne g
  obtain ⟨z₀, hz₀1, i₀, h4₀⟩ := hgood
  have hτ : τ = RingEquiv.refl K := good_eigen_tau hn3 hne hq (hφ3 z₀) (hdim_of z₀ i₀ h4₀) hH hg
    (hφD z₀) (hφ1 z₀ hz₀1)
  subst hτ
  rw [psi_refl_eq] at hg ⊢
  have hcop : Nat.Coprime 3 (orderOf (primeFormConjHom h (idGram K n) M)) :=
    coprime_orderOf_of_mem_localDeltaIn hp3 hg (hφD z₀) (hφ1 z₀ hz₀1)
  have hMφ : ∀ z, M * φ z = φ z * M := fun z =>
    commute_of_commute_psi_coprime hn3 hne hq hcop (commute_of_mem_localDeltaIn hg (hφD z))
  have heig : ∀ l, ∃ a : K, a ^ 3 = 1 ∧ ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ b l =
      a • b l := by
    intro l
    obtain ⟨a, hal⟩ : ∃ a : K,
        ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ b l = a • b l := by
      by_cases hrep : ∃ j, j ≠ l ∧ c j = c l
      · obtain ⟨j, hjl, hcj⟩ := hrep
        obtain ⟨z, hz1, h4⟩ := exists_four_of_eq_chars hc3 hG hn (Ne.symm hjl) hcj.symm
        obtain ⟨a, hal⟩ := good_eigen_scalar hn3 hne hq (hφ3 z) (hdim_of z l h4) hH hg (hφD z)
          (hφ1 z hz1) (hMφ z)
        exact ⟨a, hal (b l) (hc l z)⟩
      · push Not at hrep
        refine exists_eigen_of_commute_of_unique b
          (fun z => ((φ z : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) (fun z k => (c k z : K))
          hX _ (fun z => ?_) l (fun k hk => ?_)
        · have := congrArg (fun y : primeFormUnitary h (idGram K n) =>
            ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) (hMφ z)
          simpa using this.symm
        · by_contra hkl
          exact hrep k hkl (MonoidHom.ext fun z => Units.ext (hk z))
    exact ⟨a, eigen_cube_eq_one hq M (by rw [hbON l l, ite_eq_left rfl]) hal, hal⟩
  have hM3 : (M : GL (Fin n) K) ^ 3 = 1 := pow_three_eq_one_of_eigen b _ heig
  have hM3' : M ^ 3 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow]
    exact hM3
  have h1 : orderOf (primeFormConjHom h (idGram K n) M) ∣ 3 :=
    orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hM3', map_one])
  exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd hcop.symm h1)

end Main

end CFSG.HardMathSupport.Timmesfeld.CrossChar
