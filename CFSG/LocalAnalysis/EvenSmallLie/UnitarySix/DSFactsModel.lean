module

public import CFSG.LocalAnalysis.ComponentInitial.UnitarySixFieldTwoRadicalPreimage
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixMaximalElementaryRadicals
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.NativeParabolic
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.Transfer
public import CFSG.LieType.Catalog.Realization
public import CFSG.LocalAnalysis.ComponentInitial.UnitarySixFieldTwoAutFixed
public import CFSG.LocalAnalysis.ComponentInitial.UnitarySixFieldTwoAutSimple

public section

namespace CFSG.EvenSmallLie.UnitarySix

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

section Reindex

variable {F : Type} [Field F]

@[expose] def hypSixEquiv : HypIndex 3 0 ≃ Fin 6 :=
  (Equiv.sumCongr (Equiv.refl _) (Equiv.emptySum (Fin 0) (Fin 3))).trans finSumFinEquiv

@[expose] noncomputable def hypSixGL : GL (HypIndex 3 0) F ≃* GL (Fin 6) F :=
  Units.mapEquiv (Matrix.reindexAlgEquiv F F hypSixEquiv).toMulEquiv

theorem coe_hypSixGL (g : GL (HypIndex 3 0) F) :
    (hypSixGL g : Matrix (Fin 6) (Fin 6) F) =
      Matrix.reindex hypSixEquiv hypSixEquiv (g : Matrix (HypIndex 3 0) (HypIndex 3 0) F) :=
  rfl

variable (h : UnitaryFieldData 2 1 F)

theorem reindex_hypGram_eq_sixJ :
    Matrix.reindex hypSixEquiv hypSixEquiv (hypGram 3 0 F) =
      (UnitarySixFieldTwoAut.sixJ h : Matrix (Fin 6) (Fin 6) F) := by
  rw [UnitarySixFieldTwoAut.sixJ_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hypGram_apply, hypSixEquiv, reindex_apply]

omit [Field F] in
theorem reindex_hypSix_injective :
    Function.Injective (Matrix.reindex hypSixEquiv hypSixEquiv :
      Matrix (HypIndex 3 0) (HypIndex 3 0) F → Matrix (Fin 6) (Fin 6) F) :=
  (Matrix.reindex hypSixEquiv hypSixEquiv).injective

theorem hypSixGL_mem_sixS_iff (g : GL (HypIndex 3 0) F) :
    hypSixGL g ∈ UnitarySixFieldTwoAut.sixS h ↔ g ∈ hypSU h 3 0 := by
  rw [mem_gramSU, mem_hypSU, coe_hypSixGL, ← reindex_hypGram_eq_sixJ h]
  simp only [reindex_apply, ← submatrix_map, transpose_submatrix, submatrix_mul_equiv,
    det_submatrix_equiv_self]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨reindex_hypSix_injective (by simpa only [reindex_apply] using h1), h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by rw [h1], h2⟩

@[expose] noncomputable def hypSixSU : hypSU h 3 0 ≃* UnitarySixFieldTwoAut.sixS h :=
  (hypSixGL.subgroupMap (hypSU h 3 0)).trans (MulEquiv.subgroupCongr (by
    ext x
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact (hypSixGL_mem_sixS_iff h g).mpr hg
    · intro hx
      refine ⟨hypSixGL.symm x, (hypSixGL_mem_sixS_iff h _).mp ?_, MulEquiv.apply_symm_apply _ _⟩
      rwa [MulEquiv.apply_symm_apply]))

theorem coe_hypSixSU (g : hypSU h 3 0) :
    ((hypSixSU h g : UnitarySixFieldTwoAut.sixS h) : GL (Fin 6) F) = hypSixGL g :=
  rfl

theorem hypSixGL_scalar (u : Fˣ) :
    hypSixGL (GeneralLinearGroup.scalar (HypIndex 3 0) u) =
      GeneralLinearGroup.scalar (Fin 6) u := by
  apply Units.ext
  rw [coe_hypSixGL, GeneralLinearGroup.coe_scalar, GeneralLinearGroup.coe_scalar, scalar_apply,
    scalar_apply, reindex_apply, submatrix_diagonal_equiv]
  rfl

theorem map_hypScalars_hypSixSU :
    (hypScalars h 3 0).map (hypSixSU h).toMonoidHom = UnitarySixFieldTwoAut.sixScalars h := by
  ext x
  constructor
  · rintro ⟨g, ⟨c, hc, hcn, hg⟩, rfl⟩
    refine ⟨c, hc, hcn, ?_⟩
    change hypSixGL (g : GL (HypIndex 3 0) F) = _
    rw [hg, hypSixGL_scalar]
  · rintro ⟨c, hc, hcn, hx⟩
    refine ⟨(hypSixSU h).symm x, ⟨c, hc, hcn, ?_⟩, MulEquiv.apply_symm_apply _ _⟩
    apply hypSixGL.injective
    rw [hypSixGL_scalar, ← hx, ← coe_hypSixSU, MulEquiv.apply_symm_apply]

@[expose] noncomputable def hypSixQ : hypPSU h 3 0 ≃* UnitarySixFieldTwoAut.sixQ h :=
  QuotientGroup.congr _ _ (hypSixSU h) (map_hypScalars_hypSixSU h)

end Reindex

theorem exists_hypPSU_mulEquiv {Q : Type} [Group Q]
    (hQ : CFSG.Blueprint.LieModel Q .PSU 6 2 1) :
    ∃ (F : Type) (_ : Field F) (h : UnitaryFieldData 2 1 F), Nonempty (hypPSU h 3 0 ≃* Q) := by
  rcases hQ with ⟨-, -, K, _, _, hcard, ⟨e⟩⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · have h : UnitaryFieldData 2 1 K := ⟨Nat.prime_two, le_rfl, by rw [hcard]; norm_num⟩
    obtain ⟨R, hR⟩ := exists_isHypTransport (r := 3) (ε := 0) h
    exact ⟨K, _, h, ⟨(hypPSUEquivStatedProj h hR (by norm_num)).trans e.symm⟩⟩
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)

open BinarySymplecticSix SymplecticFlag CFSG.Assembly.LowTwoRank in
theorem card_le_of_le_statedSp {C : Subgroup (StatedSp 3 (ZMod 2))}
    (hcomm : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x) (hsq : ∀ x ∈ C, x * x = 1) :
    Nat.card C ≤ 2 ^ 6 := by
  let inst : @Module (ZMod 2) (Fin 3 ⊕ Fin 3 → ZMod 2) _ AddCommGroup.toAddCommMonoid :=
    Pi.module _ _ _
  have hfd : FiniteDimensional (ZMod 2) (Fin 3 ⊕ Fin 3 → ZMod 2) := Module.Finite.pi
  have he : IsSymplecticBasis (pairedSympForm (ZMod 2) 3)
      (Pi.basisFun (ZMod 2) (Fin 3 ⊕ Fin 3)) :=
    toMatrix_pairedSympForm
  set ψ := (spCoord he).symm
  have h64 := (card_le_of_elementary pairedSympForm_isAlt
    SymplecticFlag.pairedSympForm_nondegenerate
    finrank_standard (E := C.map ψ.toMonoidHom) (by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul, hcomm x hx y hy]) (by
      rintro _ ⟨x, hx, rfl⟩
      rw [← map_mul, hsq x hx, map_one])).1
  rw [Subgroup.card_map_of_injective ψ.injective] at h64
  exact h64.trans (by norm_num)

open UnitarySixFieldTwoAut in
theorem card_le_of_le_map_binarySp {F : Type} [Field F] (h : UnitaryFieldData 2 1 F)
    {B : Subgroup (sixQ h)} (hB : B ≤ (binarySp h).map (sixProj h))
    (hsq : ∀ b ∈ B, b ^ 2 = 1) : Nat.card B ≤ 2 ^ 6 := by
  set j := (sixProj h).comp (binarySpEmbedding h)
  have hj : Function.Injective j := by
    intro A A' hAA'
    refine binarySpEmbedding_injective h (sixProj_injOn_binarySp h ?_ ?_ hAA')
    · rw [← range_binarySpEmbedding h]
      exact ⟨A, rfl⟩
    · rw [← range_binarySpEmbedding h]
      exact ⟨A', rfl⟩
  have hrange : j.range = (binarySp h).map (sixProj h) := by
    rw [MonoidHom.range_comp, range_binarySpEmbedding]
  have hBeq : (B.comap j).map j = B :=
    Subgroup.map_comap_eq_self (hrange ▸ hB)
  have hcard : Nat.card (B.comap j) = Nat.card B := by
    rw [← hBeq, Subgroup.card_map_of_injective hj, hBeq]
  rw [← hcard]
  refine card_le_of_le_statedSp (fun x hx y hy => hj ?_) (fun x hx => hj ?_)
  · rw [map_mul, map_mul]
    exact SolomonWong.mul_comm_of_sq_eq_one hsq hx hy
  · rw [map_mul, map_one, ← sq]
    exact hsq _ hx

theorem exists_omega {F : Type} [Field F] (h : UnitaryFieldData 2 1 F) :
    ∃ ω : F, ω ^ 2 + ω + 1 = 0 := by
  have := h.finite
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Nat.card Fˣ = 3 := by
    rw [Nat.card_units, UnitarySixFieldTwoAut.natCard_eq_four h]
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) 3 (by rw [hcard])
  refine ⟨u, ?_⟩
  have hu3 : (u : F) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← hu, pow_orderOf_eq_one, Units.val_one]
  have hu1 : (u : F) ≠ 1 := fun h1 => by
    rw [show u = 1 from Units.ext h1, orderOf_one] at hu
    exact absurd hu (by norm_num)
  have h0 : ((u : F) - 1) * ((u : F) ^ 2 + u + 1) = 0 := by linear_combination hu3
  rcases mul_eq_zero.1 h0 with h0 | h0
  · exact absurd (sub_eq_zero.1 h0) hu1
  · exact h0

theorem mulAut_mul_conj_mul_inv {X : Type*} [Group X] (β : MulAut X) (y : X) :
    β * MulAut.conj y * β⁻¹ = MulAut.conj (β y) := by
  ext x
  simp [MulAut.mul_apply, MulAut.inv_apply]

open UnitarySixFieldTwoAut in
theorem card_le_of_fixed_sixQ {F : Type} [Field F] (h : UnitaryFieldData 2 1 F)
    {α : MulAut (sixQ h)} (hα : α * α = 1) (hout : ∀ q, α ≠ MulAut.conj q)
    {B : Subgroup (sixQ h)} (hfix : ∀ b ∈ B, α b = b) (hsq : ∀ b ∈ B, b ^ 2 = 1) :
    Nat.card B ≤ 2 ^ 6 := by
  obtain ⟨ω, hω⟩ := exists_omega h
  have hα2 : orderOf α = 2 :=
    orderOf_eq_prime (by rw [sq, hα]) fun h1 => hout 1 (by rw [h1, map_one])
  obtain ⟨A, hA⟩ := exists_conj_eq_of_orderOf_eq_two h ω hω α hα2
  set c := UnitaryHigher.primeFormConjHom h _ A
  have hkey : ∀ γ : MulAut (sixQ h), c * α * c⁻¹ = γ →
      {x | γ x = x} ⊆ ((binarySp h).map (sixProj h) : Set (sixQ h)) → Nat.card B ≤ 2 ^ 6 := by
    intro γ hγ hfixγ
    have hle : B.map (c : MulAut (sixQ h)).toMonoidHom ≤ (binarySp h).map (sixProj h) := by
      rintro _ ⟨b, hb, rfl⟩
      apply hfixγ
      change γ (c b) = c b
      rw [← hγ, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self, hfix b hb]
    have h64 := card_le_of_le_map_binarySp h hle (by
      rintro _ ⟨b, hb, rfl⟩
      rw [← map_pow, hsq b hb, map_one])
    rwa [Subgroup.card_map_of_injective (f := (c : MulAut (sixQ h)).toMonoidHom)
      (MulEquiv.injective c)] at h64
  rcases hA with ⟨k, -, hk⟩ | hσ | hα1
  · refine absurd ?_ (hout (c⁻¹ (sixProj h (tElt h k))))
    rw [← mulAut_mul_conj_mul_inv, ← hk]
    group
  · exact hkey _ hσ (fixed_sigmaQ_eq h).subset
  · refine hkey _ hα1 ?_
    rw [fixed_alphaOne_eq h]
    exact Subgroup.map_mono inf_le_left

theorem card_le_of_fixed {Q : Type} [Group Q] (hQ : CFSG.Blueprint.LieModel Q .PSU 6 2 1)
    {α : MulAut Q} (hα : α * α = 1) (hout : ∀ q : Q, α ≠ MulAut.conj q) {B : Subgroup Q}
    (hfix : ∀ b ∈ B, α b = b) (hsq : ∀ b ∈ B, b ^ 2 = 1) : Nat.card B ≤ 2 ^ 6 := by
  obtain ⟨F, _, h, ⟨f⟩⟩ := exists_hypPSU_mulEquiv hQ
  set φ : Q ≃* UnitarySixFieldTwoAut.sixQ h := f.symm.trans (hypSixQ h)
  set α' : MulAut (UnitarySixFieldTwoAut.sixQ h) := (φ.symm.trans α).trans φ
  have hα'x : ∀ x, α' x = φ (α (φ.symm x)) := fun x => rfl
  have hαα : ∀ y, α (α y) = y := fun y => by rw [← MulAut.mul_apply, hα, MulAut.one_apply]
  have h64 := card_le_of_fixed_sixQ h (α := α') (B := B.map φ.toMonoidHom) (by
      ext x
      rw [MulAut.mul_apply, hα'x, hα'x, MulEquiv.symm_apply_apply, hαα,
        MulEquiv.apply_symm_apply, MulAut.one_apply])
    (fun q hq => hout (φ.symm q) (by
      ext x
      have := congrArg (fun β : MulAut _ => β (φ x)) hq
      simp only [hα'x, MulEquiv.symm_apply_apply, MulAut.conj_apply] at this
      rw [MulAut.conj_apply, ← φ.symm_apply_apply (α x), this, map_mul, map_mul, map_inv,
        MulEquiv.symm_apply_apply]))
    (by
      rintro _ ⟨b, hb, rfl⟩
      change φ (α (φ.symm (φ b))) = φ b
      rw [MulEquiv.symm_apply_apply, hfix b hb])
    (by
      rintro _ ⟨b, hb, rfl⟩
      rw [MulEquiv.coe_toMonoidHom, ← map_pow, hsq b hb, map_one])
  rwa [Subgroup.card_map_of_injective φ.injective] at h64

section Herm

variable {F : Type} [Field F] (h : UnitaryFieldData 2 1 F)

theorem card_bar_fixed : Nat.card {c : F // h.bar c = c} = 2 := by
  classical
  have hiff : ∀ c : F, h.bar c = c ↔ c = 0 ∨ c = 1 := fun c => by
    rw [h.bar_apply, pow_one, UnitarySixFieldTwoAut.sq_eq_self_iff]
  rw [Nat.card_congr ((Equiv.subtypeEquivRight hiff).trans (Equiv.Set.insert (a := (0 : F))
    (s := {1}) (by simp)))]
  simp

@[expose] noncomputable def hermEquiv :
    {B : Matrix (Fin 3) (Fin 3) F // (B.map h.bar)ᵀ = B} ≃
      (Fin 3 → {c : F // h.bar c = c}) × (Fin 3 → F) where
  toFun B := (fun i => ⟨B.1 i i, by simpa using congrFun (congrFun B.2 i) i⟩,
    ![B.1 0 1, B.1 0 2, B.1 1 2])
  invFun d := ⟨!![(d.1 0 : F), d.2 0, d.2 1; h.bar (d.2 0), d.1 1, d.2 2;
      h.bar (d.2 1), h.bar (d.2 2), d.1 2], by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h.bar_bar, (d.1 _).2]⟩
  left_inv B := by
    obtain ⟨B, hB⟩ := B
    have hB' : ∀ i j, h.bar (B j i) = B i j := fun i j => by
      simpa using congrFun (congrFun hB i) j
    refine Subtype.ext ?_
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hB']
  right_inv d := by
    obtain ⟨d, u⟩ := d
    refine Prod.ext (funext fun i => Subtype.ext ?_) (funext fun i => ?_) <;>
      fin_cases i <;> rfl

theorem card_hermMat : Nat.card {B : Matrix (Fin 3) (Fin 3) F // (B.map h.bar)ᵀ = B} = 2 ^ 9 := by
  have := h.finite
  rw [Nat.card_congr (hermEquiv h), Nat.card_prod, Nat.card_fun, Nat.card_fun, card_bar_fixed h,
    UnitarySixFieldTwoAut.natCard_eq_four h, Nat.card_fin]
  norm_num

open UnitarySixFieldTwo in
theorem nMat_apply_inl_inr_inr (B : Matrix (Fin 3) (Fin 3) F) (i j : Fin 3) :
    nMat B (.inl i) (.inr (.inr j)) = B i j := by
  simp [nMat, blk3]

open UnitarySixFieldTwo in
theorem card_hermRadical : Nat.card (hermRadical h) = 2 ^ 9 := by
  have := h.charP
  rw [← card_hermMat h]
  symm
  refine Nat.card_eq_of_bijective (fun B => ⟨nElt h (B := B.1) (by
    rw [← bar_transpose h]; exact B.2), B.1, B.2, rfl⟩) ⟨fun B B' hBB' => ?_, ?_⟩
  · have := congrArg (fun g : hermRadical h =>
      (((g : hypSU h 3 0) : GL (HypIndex 3 0) F) : Matrix (HypIndex 3 0) (HypIndex 3 0) F)) hBB'
    simp only [coe_nElt] at this
    refine Subtype.ext ?_
    ext i j
    rw [← nMat_apply_inl_inr_inr B.1, ← nMat_apply_inl_inr_inr B'.1, this]
  · rintro ⟨g, B, hB, hg⟩
    exact ⟨⟨B, hB⟩, Subtype.ext (Subtype.ext (Units.ext hg.symm))⟩

open UnitarySixFieldTwo in
theorem hermRadical_inf_sixScalars (g : hypSU h 3 0) (hg : g ∈ hermRadical h)
    (hgZ : g ∈ UnitarySixFieldTwo.sixScalars h) : g = 1 := by
  obtain ⟨B, -, hgB⟩ := hg
  obtain ⟨c, hc⟩ := hgZ
  have h1 := congrFun (congrFun hgB (.inl 0)) (.inl 0)
  rw [hc] at h1
  simp [nMat, blk3, GeneralLinearGroup.coe_scalar] at h1
  refine Subtype.ext ?_
  rw [hc, h1, map_one, Subgroup.coe_one]

theorem card_map_of_injOn {G G' : Type*} [Group G] [Group G'] (f : G →* G') {H : Subgroup G}
    (hinj : Set.InjOn f H) : Nat.card (H.map f) = Nat.card H := by
  rw [← SetLike.coe_sort_coe, Subgroup.coe_map]
  exact Nat.card_congr (Equiv.Set.imageOfInjOn f H hinj).symm

open UnitarySixFieldTwo in
theorem card_map_hermRadical :
    Nat.card ((hermRadical h).map (QuotientGroup.mk' (UnitarySixFieldTwo.sixScalars h))) =
      2 ^ 9 := by
  rw [card_map_of_injOn, card_hermRadical]
  intro x hx y hy hxy
  have hxy' := QuotientGroup.eq.1 hxy
  have := hermRadical_inf_sixScalars h _ ((hermRadical h).mul_mem
    ((hermRadical h).inv_mem hx) hy) hxy'
  rw [inv_mul_eq_one] at this
  exact this

end Herm

namespace ToddParabolic

open CFSG.Sporadic.Schreier

variable {Q : Type} [Group Q] (D : ToddParabolic Q)

theorem isPGroup_of_sq {X : Type*} [Group X] {B : Subgroup X} (hsq : ∀ x ∈ B, x ^ 2 = 1) :
    IsPGroup 2 B :=
  fun x => ⟨1, Subtype.ext (by simpa using hsq x x.2)⟩

include D in
theorem card_sylow (P : Sylow 2 Q) : Nat.card P = 2 ^ 15 := by
  have := D.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 D.S := IsPGroup.of_card D.card_S
  have hi : ¬ 2 ∣ D.S.index := by rw [D.index_of_card D.card_S]; norm_num
  rw [Sylow.card_eq_multiplicity, ← Sylow.card_eq_multiplicity (hP.toSylow hi)]
  exact D.card_S

theorem exists_conj_eq_A {X : Subgroup Q} (hsq : ∀ x ∈ X, x ^ 2 = 1) :
    Nat.card X ≤ 2 ^ 9 ∧
      (2 ^ 9 ≤ Nat.card X → ∃ g : Q, X.map (MulAut.conj g).toMonoidHom = D.A) := by
  have := D.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hXP⟩ := (isPGroup_of_sq hsq).exists_le_sylow
  obtain ⟨g, hg⟩ := D.exists_conj_le_S (S' := P) (D.card_sylow P)
  have hle : X.map (MulAut.conj g).toMonoidHom ≤ D.S := by
    rintro _ ⟨x, hx, rfl⟩
    exact hg x (hXP hx)
  have hc := D.abelian_S _ hle (by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, SolomonWong.mul_comm_of_sq_eq_one hsq hx hy])
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective] at hc
  exact ⟨hc.1, fun hX => ⟨g, hc.2 (le_antisymm hc.1 hX)⟩⟩

theorem S_le_normalizer : D.S ≤ Subgroup.normalizer (D.A : Set Q) := by
  intro s hs
  have hX : D.A.map (MulAut.conj s).toMonoidHom = D.A := by
    have hle : D.A.map (MulAut.conj s).toMonoidHom ≤ D.S := by
      rintro _ ⟨a, ha, rfl⟩
      exact D.S.mul_mem (D.S.mul_mem hs (D.A_le_S ha)) (D.S.inv_mem hs)
    refine (D.abelian_S _ hle ?_).2 ?_
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul, D.A_comm x hx y hy]
    · rw [Subgroup.card_map_of_injective (MulAut.conj s).injective, D.card_A]
  rw [Subgroup.mem_normalizer_iff]
  intro a
  constructor
  · intro ha
    rw [← hX]
    exact ⟨a, ha, rfl⟩
  · intro ha
    rw [← hX] at ha
    obtain ⟨a', ha', he⟩ := ha
    have : a' = a := by
      simpa [MulAut.conj_apply] using he
    rwa [← this]

theorem odd_index_normalizer : Odd (Subgroup.normalizer (D.A : Set Q)).index := by
  have h := Subgroup.index_dvd_of_le D.S_le_normalizer
  rw [D.index_of_card D.card_S] at h
  exact Odd.of_dvd_nat (by decide) h

theorem eq_A_of_le_normalizer {X : Subgroup Q} (hX : X ≤ Subgroup.normalizer (D.A : Set Q))
    (hsq : ∀ x ∈ X, x ^ 2 = 1) (hcard : Nat.card X = 2 ^ 9) : X = D.A := by
  have := D.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA2 : IsPGroup 2 D.A := isPGroup_of_sq D.A_sq
  obtain ⟨P, hP⟩ := (hA2.to_sup_of_normal_left' (isPGroup_of_sq hsq) hX).exists_le_sylow
  exact (D.abelian_of_sylow (D.card_sylow P) (le_sup_left.trans hP) (le_sup_right.trans hP)
    fun x hx y hy => SolomonWong.mul_comm_of_sq_eq_one hsq hx hy).2 hcard

theorem eq_one_of_forall_conj {a : Q} (ha : a ∈ D.A) (hfix : ∀ k ∈ D.K, k * a * k⁻¹ = a) :
    a = 1 := by
  by_contra ha1
  have key : ∀ b : Q, a ∈ conjClass D.K b → 21 ≤ (conjClass D.K b).ncard → False := by
    intro b hb h21
    obtain ⟨c, hc, rfl⟩ := hb
    have hsub : conjClass D.K b ⊆ {c * b * c⁻¹} := by
      rintro _ ⟨k, hk, rfl⟩
      have := hfix (k * c⁻¹) (D.K.mul_mem hk (D.K.inv_mem hc))
      rw [Set.mem_singleton_iff]
      calc k * b * k⁻¹ = (k * c⁻¹) * (c * b * c⁻¹) * (k * c⁻¹)⁻¹ := by group
        _ = c * b * c⁻¹ := this
    have := Set.ncard_le_ncard hsub (Set.finite_singleton _)
    rw [Set.ncard_singleton] at this
    omega
  obtain ⟨h1, h2, h3⟩ := D.orbit_card
  rcases D.orbits a ha ha1 with hb | hb | hb
  · exact key _ hb (by rw [h1])
  · exact key _ hb (by rw [h2]; norm_num)
  · exact key _ hb (by rw [h3]; norm_num)

theorem K_le_closure_odd :
    D.K ≤ Subgroup.closure {y | y ∈ D.K ∧ Odd (orderOf y)} := by
  have := D.finite
  set C := Subgroup.closure {y | y ∈ D.K ∧ Odd (orderOf y)}
  have hCK : C ≤ D.K := (Subgroup.closure_le _).2 fun y hy => hy.1
  have := (CFSG.LieType.Catalog.lieModel_finite_simple _ _ _ _ _ D.lieModel_K).2.2
  have hnormal : (C.subgroupOf D.K).Normal := by
    refine ⟨fun x hx k => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    have hmap : C.map (MulAut.conj (k : Q)).toMonoidHom ≤ C := by
      rw [MonoidHom.map_closure]
      refine Subgroup.closure_mono ?_
      rintro _ ⟨y, ⟨hyK, hyo⟩, rfl⟩
      refine ⟨D.K.mul_mem (D.K.mul_mem k.2 hyK) (D.K.inv_mem k.2), ?_⟩
      rwa [MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq]
    exact hmap ⟨_, hx, rfl⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (C.subgroupOf D.K) with hbot | htop
  · exfalso
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨k, hk⟩ := exists_prime_orderOf_dvd_card' (G := D.K) 3 (by rw [D.card_K]; norm_num)
    have hkC : (k : Q) ∈ C := Subgroup.subset_closure ⟨k.2, by
      rw [Subgroup.orderOf_coe, hk]; decide⟩
    have : k ∈ C.subgroupOf D.K := hkC
    rw [hbot, Subgroup.mem_bot] at this
    rw [this, orderOf_one] at hk
    exact absurd hk (by norm_num)
  · intro k hk
    have : (⟨k, hk⟩ : D.K) ∈ C.subgroupOf D.K := by rw [htop]; trivial
    exact this

include D in
theorem conj_injective : Function.Injective (MulAut.conj : Q →* MulAut Q) := by
  rw [injective_iff_map_eq_one]
  intro q hq
  have hc : ∀ x : Q, q * x * q⁻¹ = x := fun x => by
    have := congrArg (fun β : MulAut Q => β x) hq
    simpa [MulAut.conj_apply] using this
  have hqA : q ∈ D.A := by
    rw [← D.centralizer_A]
    refine Subgroup.mem_centralizer_iff.2 fun a _ => ?_
    have := hc a
    calc a * q = q * a * q⁻¹ * q := by rw [this]
      _ = q * a := by group
  refine D.eq_one_of_forall_conj hqA fun k _ => ?_
  have := hc k⁻¹
  calc k * q * k⁻¹ = k * (q * k⁻¹ * q⁻¹) * q := by group
    _ = q := by rw [this, mul_inv_cancel, one_mul]

end ToddParabolic

open UnitarySixFieldTwo in
theorem exists_elementary_preimage {L : Type} [Group L] [Finite L] [Group.IsPerfect L]
    (hZ : IsPGroup 2 (Subgroup.center L))
    (hQ : CFSG.Blueprint.LieModel (L ⧸ Subgroup.center L) .PSU 6 2 1) :
    ∃ M : Subgroup L, Subgroup.center L ≤ M ∧ (∀ x ∈ M, x ^ 2 = 1) ∧
      Nat.card (M.map (QuotientGroup.mk' (Subgroup.center L))) = 2 ^ 9 := by
  obtain ⟨F, _, h, ⟨f⟩⟩ := exists_hypPSU_mulEquiv hQ
  set e : hypSU h 3 0 ⧸ UnitarySixFieldTwo.sixScalars h ≃* L ⧸ Subgroup.center L :=
    (QuotientGroup.quotientMulEquivOfEq (sixScalars_eq h)).trans f
  set η : L →* hypSU h 3 0 ⧸ UnitarySixFieldTwo.sixScalars h :=
    e.symm.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))
  have hη : Function.Surjective η := e.symm.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : η.ker = Subgroup.center L := by
    ext z
    rw [MonoidHom.mem_ker]
    change e.symm (QuotientGroup.mk' _ z) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  obtain ⟨-, -, hMsq, hkerM⟩ :=
    unitary_six_field_two_full_cover_Hermitian_radical_preimage_elementary h η hη
      (hker ▸ le_rfl) (hker ▸ hZ)
  refine ⟨_, hker ▸ hkerM, hMsq, ?_⟩
  have hmap : (((hermRadical h).map (QuotientGroup.mk' (UnitarySixFieldTwo.sixScalars h))).comap
      η).map (QuotientGroup.mk' (Subgroup.center L)) =
        ((hermRadical h).map (QuotientGroup.mk' (UnitarySixFieldTwo.sixScalars h))).map
          e.toMonoidHom := by
    rw [show η = e.symm.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L)) from rfl,
      ← Subgroup.comap_comap, Subgroup.map_comap_eq_self_of_surjective
        (QuotientGroup.mk'_surjective _), ← Subgroup.map_equiv_eq_comap_symm']
  rw [hmap, Subgroup.card_map_of_injective e.injective, card_map_hermRadical]

end CFSG.EvenSmallLie.UnitarySix
