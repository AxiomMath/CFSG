module

public import CFSG.HardMathSupport.Dickson.Bal207.FCBridgeHom
public import CFSG.HardMathSupport.Dickson.Bal207.UniLift
import CFSG.HardMathSupport.Dickson.Bal207.UniFrame

public section

namespace CFSG.HardMathSupport.Dickson.Bal207.FirstClaim

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.HardMathSupport.Dickson.I271 CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Dickson.Bal207.Uni

variable {ℓ f : ℕ} {E : Type} [Field E] {n : ℕ}

@[expose] def cubeDiag (E : Type) [Field E] (n : ℕ) : Subgroup (GL (Fin n) E) where
  carrier := {g | (g : Matrix (Fin n) (Fin n) E).IsDiag ∧ g ^ 3 = 1}
  mul_mem' {g g'} hg hg' := by
    refine ⟨?_, ?_⟩
    · rw [Units.val_mul, ← hg.1.diagonal_diag, ← hg'.1.diagonal_diag, diagonal_mul_diagonal]
      exact isDiag_diagonal _
    · have hc : Commute g g' := Units.ext (by
        rw [Units.val_mul, Units.val_mul]
        exact isDiag_commute hg.1 hg'.1)
      rw [hc.mul_pow, hg.2, hg'.2, one_mul]
  one_mem' := ⟨by rw [Units.val_one]; exact isDiag_one, one_pow 3⟩
  inv_mem' {g} hg := by
    have hinv : g⁻¹ = g ^ 2 := inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact hg.2)
    refine ⟨?_, ?_⟩
    · rw [hinv, Units.val_pow_eq_pow_val]
      exact isDiag_pow hg.1 2
    · rw [inv_pow, hg.2, inv_one]

theorem cubeDiag_apply_cube {d : GL (Fin n) E} (hd : d ∈ cubeDiag E n) (i : Fin n) :
    (d : Matrix (Fin n) (Fin n) E) i i ^ 3 = 1 := by
  have h1 := congrArg (fun g : GL (Fin n) E => (g : Matrix (Fin n) (Fin n) E) i i) hd.2
  simp only [Units.val_pow_eq_pow_val, Units.val_one, one_apply_eq] at h1
  rwa [pow_apply_diag hd.1] at h1

theorem isOmegaOneTorus_cubeDiag {ω : E} (hω : ω ^ 3 = 1) (hω1 : ω ≠ 1) :
    IsOmegaOneTorus (cubeDiag E n) where
  diag _ hd := hd.1
  cube _ hd := hd.2
  single u := by
    classical
    let v : Fin n → E := fun i => if i = u then ω else 1
    let w : Fin n → E := fun i => if i = u then ω ^ 2 else 1
    have hvw : ∀ i, v i * w i = 1 := fun i => by
      by_cases hi : i = u
      · simp only [v, w, hi, if_true]
        rw [← pow_succ', hω]
      · simp only [v, w, hi, if_false, mul_one]
    let d : GL (Fin n) E :=
      ⟨diagonal v, diagonal w, by rw [diagonal_mul_diagonal, funext hvw, diagonal_one],
        by rw [diagonal_mul_diagonal, funext fun i => (mul_comm _ _).trans (hvw i), diagonal_one]⟩
    have hv3 : ∀ i, v i ^ 3 = 1 := fun i => by
      by_cases hi : i = u
      · simp only [v, hi, if_true, hω]
      · simp only [v, hi, if_false, one_pow]
    refine ⟨d, ⟨isDiag_diagonal v, Units.ext ?_⟩, ?_, fun i hi => ?_⟩
    · change (diagonal v) ^ 3 = 1
      have hv : v ^ 3 = 1 := funext fun i => by rw [Pi.pow_apply, hv3 i, Pi.one_apply]
      rw [diagonal_pow, hv]
      exact diagonal_one
    · change diagonal v u u ≠ 1
      rw [diagonal_apply_eq]
      simp only [v, if_true]
      exact hω1
    · change diagonal v i i = 1
      rw [diagonal_apply_eq]
      simp only [v, hi, if_false]

theorem glAut_eq_of_mem_cubeDiag {φ : E ≃+* E} (hφ : ∀ c : E, c ^ 3 = 1 → φ c = c)
    {d : GL (Fin n) E} (hd : d ∈ cubeDiag E n) : glAut φ d = d := by
  apply Units.ext
  rw [coe_glAut]
  ext i j
  rw [Matrix.map_apply]
  by_cases hij : i = j
  · subst hij
    exact hφ _ (cubeDiag_apply_cube hd i)
  · rw [hd.1 hij, map_zero]

theorem mem_center_of_mulEquiv_apply {G H : Type*} [Group G] [Group H] (φ : G ≃* H) {z : G}
    (hz : φ z ∈ Subgroup.center H) : z ∈ Subgroup.center G := by
  rw [Subgroup.mem_center_iff] at hz ⊢
  intro g
  apply φ.injective
  rw [map_mul, map_mul, hz (φ g)]

abbrev blockGamma (h : UnitaryFieldData ℓ f E) (n : ℕ) : Type :=
  ↥(primeFormUnitary h (oneGram E n)) ⋊[primeFormFieldU h
    CFSG.HardMathSupport.Timmesfeld.LinearRank.isPrimeFormGram_one] (E ≃+* E)

section Block

variable {X : Type} [Group X] {K : Subgroup X} {S : Type} [Group S]
  (e : (↥K ⧸ Subgroup.center ↥K) ≃* S) (h : UnitaryFieldData ℓ f E)

abbrev blockSU (n : ℕ) : Subgroup ↥(primeFormUnitary h (oneGram E n)) :=
  (gramSU h (oneGram E n)).subgroupOf (primeFormUnitary h (oneGram E n))

theorem gramSU_le_primeFormUnitary :
    gramSU h (oneGram E n) ≤ primeFormUnitary h (oneGram E n) := fun _ hg => hg.1

variable {J : Subgroup X} (hJK : J ≤ K) {ι : ↥(primeFormUnitary h (oneGram E n)) →* S}
  (hι : Function.Injective ι) (hJι : (J.comap K.subtype).map (uniMap e) = (blockSU h n).map ι)

@[expose] noncomputable def blockEquiv :
    ↥((J.comap K.subtype).map (uniMap e)) ≃* ↥(gramSU h (oneGram E n)) :=
  ((MulEquiv.subgroupCongr hJι).trans (Subgroup.equivMapOfInjective (blockSU h n) ι hι).symm).trans
    (Subgroup.subgroupOfEquivOfLe (gramSU_le_primeFormUnitary h))

@[expose] noncomputable def blockPre : ↥J →* ↥(gramSU h (oneGram E n)) :=
  (blockEquiv e h hι hJι).toMonoidHom.comp (uniRestr e hJK)

theorem ι_blockPre (j : ↥J) :
    ι ⟨(blockPre e h hJK hι hJι j : GL (Fin n) E), (blockPre e h hJK hι hJι j).2.1⟩ =
      uniMap e (Subgroup.inclusion hJK j) := by
  have h1 := Subgroup.coe_equivMapOfInjective_apply (blockSU h n) ι hι
    ((Subgroup.equivMapOfInjective (blockSU h n) ι hι).symm
      (MulEquiv.subgroupCongr hJι (uniRestr e hJK j)))
  rw [MulEquiv.apply_symm_apply] at h1
  exact h1.symm

@[expose] noncomputable def blockHom (P : ↥(primeFormUnitary h (oneGram E n))) :
    ↥J →* primeFormP h (oneGram E n) :=
  (primeFormConjHom h _ P⁻¹).toMonoidHom.comp
    ((QuotientGroup.mk' (normOneScalars h (gramSU h (oneGram E n)) n)).comp
      (blockPre e h hJK hι hJι))

theorem blockHom_apply (P : ↥(primeFormUnitary h (oneGram E n))) (j : ↥J) :
    blockHom e h hJK hι hJι P j =
      primeFormConjHom h _ P⁻¹ (QuotientGroup.mk (blockPre e h hJK hι hJι j)) :=
  rfl

theorem blockHom_surjective (P : ↥(primeFormUnitary h (oneGram E n))) :
    Function.Surjective (blockHom e h hJK hι hJι P) := by
  intro z
  obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective
    (normOneScalars h (gramSU h (oneGram E n)) n) ((primeFormConjHom h _ P⁻¹).symm z)
  obtain ⟨r, rfl⟩ := (blockEquiv e h hι hJι).surjective g
  obtain ⟨j, rfl⟩ := uniRestr_surjective e hJK r
  refine ⟨j, ?_⟩
  rw [blockHom_apply]
  change primeFormConjHom h _ P⁻¹ (QuotientGroup.mk' _ (blockEquiv e h hι hJι
    (uniRestr e hJK j))) = z
  rw [hg, MulEquiv.apply_symm_apply]

theorem ker_blockHom_le_center (hJp : commutator ↥J = ⊤) (P : ↥(primeFormUnitary h (oneGram E n))) :
    (blockHom e h hJK hι hJι P).ker ≤ Subgroup.center ↥J := by
  intro j hj
  have h1 : (QuotientGroup.mk (blockPre e h hJK hι hJι j) : primeFormP h (oneGram E n)) = 1 :=
    (map_eq_one_iff _ (primeFormConjHom h _ P⁻¹).injective).1 hj
  have h2 : blockEquiv e h hι hJι (uniRestr e hJK j) ∈
      Subgroup.center ↥(gramSU h (oneGram E n)) :=
    normOneScalars_le_center h _ n ((QuotientGroup.eq_one_iff _).1 h1)
  exact uni_mem_center_of_map (Group.isPerfect_def.2 hJp) (uniRestr e hJK)
    (ker_uniRestr_le_center e hJK) (mem_center_of_mulEquiv_apply _ h2)

theorem blockHom_conj (P : ↥(primeFormUnitary h (oneGram E n))) {y : X} (hyK : y ∈ K)
    {Q : ↥(primeFormUnitary h (oneGram E n))} (hyQ : uniMap e ⟨y, hyK⟩ = ι Q)
    (hyJ : y ∈ Subgroup.normalizer (J : Set X)) (j : ↥J) :
    blockHom e h hJK hι hJι P (J.normalizerMonoidHom ⟨y, hyJ⟩ j) =
      primeFormConjHom h _ (P⁻¹ * Q * P) (blockHom e h hJK hι hJι P j) := by
  set j' := J.normalizerMonoidHom ⟨y, hyJ⟩ j with hj'
  set g := blockPre e h hJK hι hJι j with hg
  set g' := blockPre e h hJK hι hJι j' with hg'
  have hjK : (Subgroup.inclusion hJK j' : ↥K) =
      ⟨y, hyK⟩ * Subgroup.inclusion hJK j * ⟨y, hyK⟩⁻¹ := rfl
  have hι' : ι ⟨(g' : GL (Fin n) E), g'.2.1⟩ =
      ι (Q * ⟨(g : GL (Fin n) E), g.2.1⟩ * Q⁻¹) := by
    rw [hg', ι_blockPre, hjK, map_mul, map_mul, map_inv, hyQ, ← ι_blockPre e h hJK hι hJι j,
      map_mul, map_mul, map_inv]
  have hgg : (g' : GL (Fin n) E) = (Q : GL (Fin n) E) * g * (Q : GL (Fin n) E)⁻¹ :=
    congrArg Subtype.val (hι hι')
  rw [blockHom_apply, blockHom_apply, ← hg', ← hg, ← MulAut.mul_apply, ← map_mul,
    show P⁻¹ * Q * P * P⁻¹ = P⁻¹ * Q by group, map_mul, MulAut.mul_apply, primeFormConjHom_mk]
  congr 2
  rw [hgg]
  rfl

theorem conj_inl_eq_of_frame {P D A : ↥(primeFormUnitary h (oneGram E n))} {φ : E ≃+* E}
    (hD : ((D : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).IsDiag)
    (hφ : ∀ c : E, c ^ 3 = 1 → φ c = c) (hA : (A : GL (Fin n) E) ∈ cubeDiag E n)
    {x : blockGamma h n}
    (hPx : (SemidirectProduct.inl P)⁻¹ * x * SemidirectProduct.inl P =
      SemidirectProduct.inl D * SemidirectProduct.inr φ) :
    x * SemidirectProduct.inl (P * A * P⁻¹) * x⁻¹ = SemidirectProduct.inl (P * A * P⁻¹) := by
  have hxb : x = SemidirectProduct.inl P * (SemidirectProduct.inl D * SemidirectProduct.inr φ) *
      (SemidirectProduct.inl P)⁻¹ := by
    rw [← hPx]
    group
  have hφA : SemidirectProduct.inr φ * SemidirectProduct.inl A * (SemidirectProduct.inr φ)⁻¹ =
      (SemidirectProduct.inl A : blockGamma h n) := by
    rw [← map_inv, ← SemidirectProduct.inl_aut]
    congr 1
    exact Subtype.ext (glAut_eq_of_mem_cubeDiag hφ hA)
  have hDA : D * A = A * D := Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    exact Units.ext (by rw [Units.val_mul, Units.val_mul]; exact isDiag_commute hD hA.1))
  have hDA' : SemidirectProduct.inl D * SemidirectProduct.inl A * (SemidirectProduct.inl D)⁻¹ =
      (SemidirectProduct.inl A : blockGamma h n) := by
    rw [← map_mul, hDA, map_mul, mul_inv_cancel_right]
  rw [hxb, map_mul, map_mul, map_inv]
  calc _ = SemidirectProduct.inl P * (SemidirectProduct.inl D * (SemidirectProduct.inr φ *
        SemidirectProduct.inl A * (SemidirectProduct.inr φ)⁻¹) * (SemidirectProduct.inl D)⁻¹) *
          (SemidirectProduct.inl P)⁻¹ := by group
    _ = _ := by rw [hφA, hDA']

end Block

variable {X : Type} [Group X] {K : Subgroup X} {S : Type} [Group S]

theorem block_toral [Finite X] {B J : Subgroup X}
    (hB : IsSCp 3 ⊤ B) (hBK : B ≤ Subgroup.normalizer (K : Set X))
    (hZ : Nat.Coprime 3 (Nat.card (Subgroup.center ↥K))) (e : (↥K ⧸ Subgroup.center ↥K) ≃* S)
    (hJK : J ≤ K) (hBJ : B ≤ Subgroup.normalizer (J : Set X)) (h : UnitaryFieldData ℓ f E)
    {ι : ↥(primeFormUnitary h (oneGram E n)) →* S} (hι : Function.Injective ι)
    (hJι : (J.comap K.subtype).map (uniMap e) = (blockSU h n).map ι)
    (x : ↥B → blockGamma h n)
    (hx : ∀ (b : ↥B) (g : ↥(primeFormUnitary h (oneGram E n))),
      uniAut e ⟨b, hBK b.2⟩ (ι g) = ι ((x b * SemidirectProduct.inl g * (x b)⁻¹).left))
    (P : ↥(primeFormUnitary h (oneGram E n)))
    (hP : ∀ b : ↥B, ∃ D : ↥(primeFormUnitary h (oneGram E n)),
      ((D : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).IsDiag ∧ ∃ φ : E ≃+* E,
        (∀ c : E, c ^ 3 = 1 → φ c = c) ∧
          (SemidirectProduct.inl P)⁻¹ * x b * SemidirectProduct.inl P =
            SemidirectProduct.inl D * SemidirectProduct.inr φ)
    (A : primeFormUnitary h (oneGram E n)) (hA : (A : GL (Fin n) E) ∈ cubeDiag E n) :
    ∃ (y : X) (hy : y ∈ Subgroup.normalizer (J : Set X)), y ∈ B ∧
      ∀ j : ↥J, blockHom e h hJK hι hJι P (J.normalizerMonoidHom ⟨y, hy⟩ j) =
        primeFormConjHom h _ A (blockHom e h hJK hι hJι P j) := by
  have hA3 : A ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hA.2)
  have hfix : ∀ (b : X) (hb : b ∈ B),
      uniAut e ⟨b, hBK hb⟩ (ι (P * A * P⁻¹)) = ι (P * A * P⁻¹) := by
    intro b hb
    obtain ⟨D, hD, φ, hφ, hPx⟩ := hP ⟨b, hb⟩
    rw [hx ⟨b, hb⟩, conj_inl_eq_of_frame h hD hφ hA hPx, SemidirectProduct.left_inl]
  have hs3 : (ι (P * A * P⁻¹)) ^ 3 = 1 := by
    rw [← map_pow, conj_pow, hA3, mul_one, mul_inv_cancel, map_one]
  obtain ⟨y, hyB, hyK, hyψ⟩ := uni_exists_mem_of_fixed hB hBK hZ e hs3 hfix
  refine ⟨y, hBJ hyB, hyB, fun j => ?_⟩
  rw [blockHom_conj e h hJK hι hJι P hyK hyψ (hBJ hyB) j,
    show P⁻¹ * (P * A * P⁻¹) * P = A by group]

theorem isStronglyLocallyOneBalanced_of_block [Finite X] {B J : Subgroup X} {a : X}
    (hB : IsSCp 3 ⊤ B) (hBK : B ≤ Subgroup.normalizer (K : Set X))
    (hZ : Nat.Coprime 3 (Nat.card (Subgroup.center ↥K))) (e : (↥K ⧸ Subgroup.center ↥K) ≃* S)
    (hJ : CFSG.Open.IsQuasisimple ↥J) (hJK : J ≤ K) (hBJ : B ≤ Subgroup.normalizer (J : Set X))
    (h : UnitaryFieldData ℓ f E) (hℓ : ℓ = 2) (hf : f = 1 ∨ f = 3) (hn : 3 ≤ n)
    (hne : ¬(n = 3 ∧ ℓ ^ f = 2)) {ι : ↥(primeFormUnitary h (oneGram E n)) →* S}
    (hι : Function.Injective ι) (hJι : (J.comap K.subtype).map (uniMap e) = (blockSU h n).map ι)
    (x : ↥B → blockGamma h n)
    (hx : ∀ (b : ↥B) (g : ↥(primeFormUnitary h (oneGram E n))),
      uniAut e ⟨b, hBK b.2⟩ (ι g) = ι ((x b * SemidirectProduct.inl g * (x b)⁻¹).left))
    (P : ↥(primeFormUnitary h (oneGram E n)))
    (hP : ∀ b : ↥B, ∃ D : ↥(primeFormUnitary h (oneGram E n)),
      ((D : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).IsDiag ∧ ∃ φ : E ≃+* E,
        (∀ c : E, c ^ 3 = 1 → φ c = c) ∧
          (SemidirectProduct.inl P)⁻¹ * x b * SemidirectProduct.inl P =
            SemidirectProduct.inl D * SemidirectProduct.inr φ) :
    IsStronglyLocallyOneBalanced 3 B a J := by
  have h3 : 3 ∣ ℓ ^ f + 1 := by
    subst hℓ
    rcases hf with rfl | rfl <;> norm_num
  obtain ⟨ω, hω, hω1, -⟩ := exists_cube_root_bar h h3
  exact isStronglyLocallyOneBalanced_of_omegaOne_hom hJ h hℓ hf hn hne
    (blockHom e h hJK hι hJι P) (blockHom_surjective e h hJK hι hJι P)
    (ker_blockHom_le_center e h hJK hι hJι hJ.1 P) (isOmegaOneTorus_cubeDiag hω hω1)
    (block_toral hB hBK hZ e hJK hBJ h hι hJι x hx P hP)

end CFSG.HardMathSupport.Dickson.Bal207.FirstClaim

end
