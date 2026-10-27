module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.A6.I1435Chev.Weir

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott

open Matrix Subgroup CFSG.RankThree.PartTwo.Sec4 CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.HardMathSupport.Dickson.Sec6.I1431 (NoE27)

section Cyclic

theorem card_le_three_of_isCyclic {W : Type*} [Group W] [Finite W] [IsCyclic W]
    (h3 : ∀ w : W, w ^ 3 = 1) : Nat.card W ≤ 3 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := W)
  rw [← orderOf_eq_card_of_forall_mem_zpowers hg]
  exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (h3 g))

theorem card_le_nine_of_pow_three {S : Type*} [Group S] [Finite S] [IsCyclic S]
    (E : Subgroup (S × S)) (hE : ∀ e ∈ E, e ^ 3 = 1) : Nat.card E ≤ 9 := by
  set E₁ := E.map (MonoidHom.fst S S)
  set E₂ := E.map (MonoidHom.snd S S)
  have h₁ : Nat.card E₁ ≤ 3 := by
    haveI : IsCyclic E₁ := Subgroup.isCyclic E₁
    refine card_le_three_of_isCyclic ?_
    rintro ⟨_, e, he, rfl⟩
    apply Subtype.ext
    have := congrArg Prod.fst (hE e he)
    simpa using this
  have h₂ : Nat.card E₂ ≤ 3 := by
    haveI : IsCyclic E₂ := Subgroup.isCyclic E₂
    refine card_le_three_of_isCyclic ?_
    rintro ⟨_, e, he, rfl⟩
    apply Subtype.ext
    have := congrArg Prod.snd (hE e he)
    simpa using this
  have hinj : Function.Injective (fun e : E =>
      ((⟨(e : S × S).1, ⟨e, e.2, rfl⟩⟩ : E₁), (⟨(e : S × S).2, ⟨e, e.2, rfl⟩⟩ : E₂))) := by
    intro a b h
    simp only [Prod.mk.injEq] at h
    exact Subtype.ext (Prod.ext (congrArg Subtype.val h.1) (congrArg Subtype.val h.2))
  have h := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_prod] at h
  calc Nat.card E ≤ Nat.card E₁ * Nat.card E₂ := h
    _ ≤ 3 * 3 := Nat.mul_le_mul h₁ h₂

theorem card_le_three_mul_of_cube_mem {T : Type*} [Group T] [Finite T] [IsCyclic T]
    (N : Subgroup T) (hN : ∀ t : T, t ^ 3 ∈ N) : Nat.card T ≤ 3 * Nat.card N := by
  letI : CommGroup T := IsCyclic.commGroup
  set χ : T →* T := powMonoidHom 3
  have hker : Nat.card χ.ker ≤ 3 := by
    haveI : IsCyclic χ.ker := Subgroup.isCyclic χ.ker
    refine card_le_three_of_isCyclic ?_
    intro w
    exact Subtype.ext (w.2 : χ w = 1)
  have hrange : Nat.card χ.range ≤ Nat.card N := by
    refine Subgroup.card_le_of_le ?_
    rintro _ ⟨t, rfl⟩
    exact hN t
  have hcard : Nat.card T = Nat.card χ.ker * Nat.card χ.range := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange χ).toEquiv,
      mul_comm, ← Subgroup.card_eq_card_quotient_mul_card_subgroup]
  rw [hcard]
  exact Nat.mul_le_mul hker hrange

end Cyclic

section GLTwo

variable {K : Type} [Field K]

theorem card_le_nine_of_elemAbelian_GL2 [Finite K] (hK3 : ¬ 3 ∣ Nat.card K)
    {E : Subgroup (GL (Fin 2) K)} (hE : CFSG.Open.IsElemAbelian 3 E) : Nat.card E ≤ 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fintype K := Fintype.ofFinite K
  have hK3' : ¬ 3 ∣ Fintype.card K := by rwa [← Nat.card_eq_fintype_card]
  have hno : NoE27 (GL (Fin 2) K) := by
    refine CFSG.LocalAnalysis.RankThreeTheoremC.A6.I1435Chev.Weir.noE27_of_sigma ?_ fun P =>
      CFSG.GroupTheory.WeirSylow.sylow_GL (by decide) K hK3' 2 P
    calc 2 / orderOf (Fintype.card K : ZMod 3) ≤ 2 := Nat.div_le_self 2 _
      _ < 3 := by norm_num
  have hp : IsPGroup 3 E := fun e => ⟨1, Subtype.ext (by simpa using hE.2 e e.2)⟩
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  by_contra hlt
  have hk3 : 3 ≤ k := by
    by_contra h
    have : k ≤ 2 := by omega
    have := Nat.pow_le_pow_right (by norm_num : 1 ≤ 3) this
    omega
  obtain ⟨F, hF⟩ := Sylow.exists_subgroup_card_pow_prime 3 (n := 3) (G := E) (by
    rw [hk]
    exact Nat.pow_dvd_pow 3 hk3)
  refine hno ⟨F.map E.subtype, ?_, ?_⟩
  · refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩
    · obtain ⟨_, ⟨x, -, rfl⟩⟩ := a
      obtain ⟨_, ⟨y, -, rfl⟩⟩ := b
      exact hE.comm x.2 y.2
    · rintro _ ⟨x, -, rfl⟩
      exact hE.2 _ x.2
  · rw [Subgroup.card_map_of_injective E.subtype_injective, hF]
    norm_num

@[expose] def lowerBlock (A : Matrix (Fin 3) (Fin 3) K) : Matrix (Fin 2) (Fin 2) K :=
  !![A 1 1, A 1 2; A 2 1, A 2 2]

@[expose] def IsBlock (A : Matrix (Fin 3) (Fin 3) K) : Prop :=
  A 0 1 = 0 ∧ A 0 2 = 0 ∧ A 1 0 = 0 ∧ A 2 0 = 0

theorem IsBlock.lowerBlock_mul {A B : Matrix (Fin 3) (Fin 3) K} (hA : IsBlock A)
    (hB : IsBlock B) : lowerBlock (A * B) = lowerBlock A * lowerBlock B := by
  obtain ⟨-, -, hA10, hA20⟩ := hA
  obtain ⟨hB01, hB02, -, -⟩ := hB
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lowerBlock, mul_apply, Fin.sum_univ_three, Fin.sum_univ_two, hA10, hA20, hB01, hB02]

theorem IsBlock.mul_zero_zero {A B : Matrix (Fin 3) (Fin 3) K} (hA : IsBlock A) :
    (A * B) 0 0 = A 0 0 * B 0 0 := by
  obtain ⟨hA01, hA02, -, -⟩ := hA
  simp [mul_apply, Fin.sum_univ_three, hA01, hA02]

theorem lowerBlock_one : lowerBlock (1 : Matrix (Fin 3) (Fin 3) K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lowerBlock]

theorem isBlock_of_mem_centralizer {e : Kˣ} (he : e ≠ 1) {m : GL (Fin 3) K}
    (hm : m ∈ centralizer ({diagE e} : Set (GL (Fin 3) K))) :
    IsBlock (m : Matrix (Fin 3) (Fin 3) K) := by
  rw [mem_centralizer_singleton_iff] at hm
  have h := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) hm
  simp only [Units.val_mul, coe_diagE] at h
  have he' : (e : K) ≠ 1 := fun h' => he (Units.ext h')
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact entry_eq_zero_of_commute_diagonal (d := ![(e : K), 1, 1]) h (by simpa using he')
  · exact entry_eq_zero_of_commute_diagonal (d := ![(e : K), 1, 1]) h (by simpa using he')
  · exact entry_eq_zero_of_commute_diagonal (d := ![(e : K), 1, 1]) h
      (by simpa using Ne.symm he')
  · exact entry_eq_zero_of_commute_diagonal (d := ![(e : K), 1, 1]) h
      (by simpa using Ne.symm he')

theorem mem_centralizer_of_isBlock (e : Kˣ) {m : GL (Fin 3) K}
    (hm : IsBlock (m : Matrix (Fin 3) (Fin 3) K)) :
    m ∈ centralizer ({diagE e} : Set (GL (Fin 3) K)) := by
  rw [mem_centralizer_singleton_iff]
  obtain ⟨h01, h02, h10, h20⟩ := hm
  apply Units.ext
  simp only [Units.val_mul, coe_diagE]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mul_apply, Fin.sum_univ_three, h01, h02, h10, h20, mul_comm]

theorem zero_zero_ne_zero_of_isBlock {m : GL (Fin 3) K}
    (hm : IsBlock (m : Matrix (Fin 3) (Fin 3) K)) :
    (m : Matrix (Fin 3) (Fin 3) K) 0 0 ≠ 0 := by
  intro h0
  have h := congrArg (fun A : Matrix (Fin 3) (Fin 3) K => A 0 0)
    (show ((m * m⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 by rw [mul_inv_cancel]; rfl)
  simp only [Units.val_mul, hm.mul_zero_zero, h0, zero_mul, Matrix.one_apply_eq] at h
  exact zero_ne_one h

@[expose] noncomputable def blockGL {e : Kˣ} (he : e ≠ 1) :
    ↥(centralizer ({diagE e} : Set (GL (Fin 3) K))) →* GL (Fin 2) K where
  toFun m :=
    { val := (((m : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0)⁻¹ •
        lowerBlock ((m : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
      inv := ((((m⁻¹ : ↥(centralizer ({diagE e} : Set (GL (Fin 3) K)))) : GL (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K) 0 0)⁻¹ •
        lowerBlock (((m⁻¹ : ↥(centralizer ({diagE e} : Set (GL (Fin 3) K)))) : GL (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K)
      val_inv := by
        have hm := isBlock_of_mem_centralizer he m.2
        have hm' := isBlock_of_mem_centralizer he (m⁻¹).2
        have h1 : ((m : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
            (((m⁻¹ : ↥(centralizer ({diagE e} : Set (GL (Fin 3) K)))) : GL (Fin 3) K) :
              Matrix (Fin 3) (Fin 3) K) = 1 := by
          rw [← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel]
          rfl
        rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← hm.lowerBlock_mul hm', h1,
          lowerBlock_one, ← mul_inv, ← hm.mul_zero_zero, h1, Matrix.one_apply_eq, inv_one,
          one_smul]
      inv_val := by
        have hm := isBlock_of_mem_centralizer he m.2
        have hm' := isBlock_of_mem_centralizer he (m⁻¹).2
        have h1 : (((m⁻¹ : ↥(centralizer ({diagE e} : Set (GL (Fin 3) K)))) : GL (Fin 3) K) :
              Matrix (Fin 3) (Fin 3) K) * ((m : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
          rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]
          rfl
        rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← hm'.lowerBlock_mul hm, h1,
          lowerBlock_one, ← mul_inv, ← hm'.mul_zero_zero, h1, Matrix.one_apply_eq, inv_one,
          one_smul] }
  map_one' := by
    apply Units.ext
    simp only [OneMemClass.coe_one, Units.val_one, Matrix.one_apply_eq, inv_one, one_smul]
    exact lowerBlock_one
  map_mul' m n := by
    apply Units.ext
    have hm := isBlock_of_mem_centralizer he m.2
    have hn := isBlock_of_mem_centralizer he n.2
    simp only [Subgroup.coe_mul, Units.val_mul]
    rw [hm.lowerBlock_mul hn, hm.mul_zero_zero, mul_inv, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul]

theorem coe_blockGL {e : Kˣ} (he : e ≠ 1)
    (m : ↥(centralizer ({diagE e} : Set (GL (Fin 3) K)))) :
    ((blockGL he m : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      (((m : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0)⁻¹ •
        lowerBlock ((m : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) :=
  rfl

theorem mem_statedScalars_of_blockGL_eq_one {e : Kˣ} (he : e ≠ 1)
    {m : ↥(centralizer ({diagE e} : Set (GL (Fin 3) K)))} (h : blockGL he m = 1) :
    (m : GL (Fin 3) K) ∈ StatedScalars (Fin 3) K := by
  have hm := isBlock_of_mem_centralizer he m.2
  have h0 := zero_zero_ne_zero_of_isBlock hm
  have h1 := congrArg (fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K)) h
  simp only [coe_blockGL, Units.val_one] at h1
  have h2 : lowerBlock ((m : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (((m : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0) • 1 := by
    rw [← h1, smul_smul, mul_inv_cancel₀ h0, one_smul]
  obtain ⟨h01, h02, h10, h20⟩ := hm
  have e11 := congrArg (fun A : Matrix (Fin 2) (Fin 2) K => A 0 0) h2
  have e12 := congrArg (fun A : Matrix (Fin 2) (Fin 2) K => A 0 1) h2
  have e21 := congrArg (fun A : Matrix (Fin 2) (Fin 2) K => A 1 0) h2
  have e22 := congrArg (fun A : Matrix (Fin 2) (Fin 2) K => A 1 1) h2
  simp [lowerBlock] at e11 e12 e21 e22
  refine mem_statedScalars_of_eq_smul (a := ((m : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0)
    ?_ h0
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h01, h02, h10, h20, e11, e12, e21, e22]

theorem blockGL_scalar {e : Kˣ} (he : e ≠ 1) (c : Kˣ)
    (hc : GeneralLinearGroup.scalar (Fin 3) c ∈ centralizer ({diagE e} : Set (GL (Fin 3) K))) :
    blockGL he ⟨_, hc⟩ = 1 := by
  apply Units.ext
  rw [coe_blockGL]
  simp only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lowerBlock, Matrix.diagonal_apply_eq,
    Matrix.diagonal_apply_ne]

end GLTwo

section PGL

variable {K : Type} [Field K] {π : Bool} {p f : ℕ}

theorem not_three_dvd_card (hK : PiField π p f K) (hq : ModThree π (p ^ f)) :
    ¬ 3 ∣ Nat.card K := by
  rw [hK.card]
  intro h
  have h3 : 3 ∣ p ^ f := by
    cases π
    · exact Nat.prime_three.dvd_of_dvd_pow (n := 2) (by simpa [piCard] using h)
    · simpa [piCard] using h
  cases π
  · change p ^ f % 3 = 2 at hq
    omega
  · change p ^ f % 3 = 1 at hq
    omega

theorem isCyclic_statedScalars [Finite K] : IsCyclic ↥(StatedScalars (Fin 3) K) :=
  isCyclic_of_surjective (scalarHom (K := K)) (MonoidHom.rangeRestrict_surjective _)

theorem commutator_mul_of_scalar {T : Subgroup (GL (Fin 3) K)}
    (hc : ∀ t ∈ T, ∀ u ∈ T, t * u * t⁻¹ * u⁻¹ ∈ StatedScalars (Fin 3) K) {w : GL (Fin 3) K}
    (hw : w ∈ T) {a b : GL (Fin 3) K} (ha : a ∈ T) (hb : b ∈ T) :
    a * b * w * (a * b)⁻¹ * w⁻¹ = (a * w * a⁻¹ * w⁻¹) * (b * w * b⁻¹ * w⁻¹) := by
  have hz := commute_of_mem_statedScalars (hc b hb w hw) a
  calc a * b * w * (a * b)⁻¹ * w⁻¹ = a * (b * w * b⁻¹ * w⁻¹) * (w * a⁻¹ * w⁻¹) := by
        simp only [mul_assoc, _root_.mul_inv_rev, inv_mul_cancel_left]
    _ = (b * w * b⁻¹ * w⁻¹) * a * (w * a⁻¹ * w⁻¹) := by rw [hz]
    _ = (b * w * b⁻¹ * w⁻¹) * (a * w * a⁻¹ * w⁻¹) := by simp only [mul_assoc]
    _ = (a * w * a⁻¹ * w⁻¹) * (b * w * b⁻¹ * w⁻¹) :=
        commute_of_mem_statedScalars (hc a ha w hw) (b * w * b⁻¹ * w⁻¹)

@[expose] noncomputable def commScalar {T : Subgroup (GL (Fin 3) K)}
    (hc : ∀ t ∈ T, ∀ u ∈ T, t * u * t⁻¹ * u⁻¹ ∈ StatedScalars (Fin 3) K) {w : GL (Fin 3) K}
    (hw : w ∈ T) : ↥T →* ↥(StatedScalars (Fin 3) K) :=
  MonoidHom.mk' (fun t => ⟨t * w * t⁻¹ * w⁻¹, hc t t.2 w hw⟩)
    (fun a b => Subtype.ext (commutator_mul_of_scalar hc hw a.2 b.2))

theorem card_le_nine_mul_of_heis (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {T : Subgroup (GL (Fin 3) K)} (h3 : ∀ t ∈ T, t ^ 3 ∈ StatedScalars (Fin 3) K)
    (hc : ∀ t ∈ T, ∀ u ∈ T, t * u * t⁻¹ * u⁻¹ ∈ StatedScalars (Fin 3) K)
    {u v : GL (Fin 3) K} (hu : u ∈ T) (hv : v ∈ T) (huv : u * v * u⁻¹ * v⁻¹ ≠ 1) :
    Nat.card T ≤ 9 * Nat.card ↥(T ⊓ StatedScalars (Fin 3) K) := by
  have := hK.finite
  haveI := isCyclic_statedScalars (K := K)
  set S := ↥(StatedScalars (Fin 3) K)
  have hcs : ∀ (z : GL (Fin 3) K), z ∈ StatedScalars (Fin 3) K → ∀ g : GL (Fin 3) K,
      g * z = z * g := fun z hz g => commute_of_mem_statedScalars hz g
  let φ : ↥T →* S × S := (commScalar hc hu).prod (commScalar hc hv)
  obtain ⟨ζ, hζ⟩ := hc u hu v hv
  have hζ' : u * v * u⁻¹ = GeneralLinearGroup.scalar (Fin 3) ζ * v := by
    rw [hζ, inv_mul_cancel_right]
  have hζ1 : ζ ≠ 1 := by
    rintro rfl
    rw [map_one] at hζ
    exact huv hζ.symm
  have hζ3 : ζ ^ 3 = 1 := pow_three_eq_one_of_conj_eq_scalar_mul hζ'
  have h3K := hK.three_ne_zero hq
  have hker : Nat.card φ.ker ≤ Nat.card ↥(T ⊓ StatedScalars (Fin 3) K) := by
    rw [← Subgroup.card_map_of_injective T.subtype_injective]
    refine Subgroup.card_le_of_le ?_
    rintro _ ⟨t, ht, rfl⟩
    have h1 : (t : GL (Fin 3) K) * u * (t : GL (Fin 3) K)⁻¹ * u⁻¹ = 1 :=
      congrArg (fun z : S × S => ((z.1 : S) : GL (Fin 3) K)) ht
    have h2 : (t : GL (Fin 3) K) * v * (t : GL (Fin 3) K)⁻¹ * v⁻¹ = 1 :=
      congrArg (fun z : S × S => ((z.2 : S) : GL (Fin 3) K)) ht
    refine ⟨t.2, mem_statedScalars_of_commute_heis h3K hζ1 hζ3 hζ' ?_ ?_⟩
    · exact mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 h1)
    · exact mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 h2)
  have hrange : Nat.card φ.range ≤ 9 := by
    refine card_le_nine_of_pow_three _ ?_
    rintro _ ⟨t, rfl⟩
    rw [← map_pow]
    have ht3 := h3 t t.2
    have hu' := hcs _ ht3 u
    have hv' := hcs _ ht3 v
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · show ((t ^ 3 : ↥T) : GL (Fin 3) K) * u * ((t ^ 3 : ↥T) : GL (Fin 3) K)⁻¹ * u⁻¹ = 1
      rw [SubgroupClass.coe_pow, ← hu', mul_inv_cancel_right, mul_inv_cancel]
    · show ((t ^ 3 : ↥T) : GL (Fin 3) K) * v * ((t ^ 3 : ↥T) : GL (Fin 3) K)⁻¹ * v⁻¹ = 1
      rw [SubgroupClass.coe_pow, ← hv', mul_inv_cancel_right, mul_inv_cancel]
  have hcard : Nat.card T = Nat.card φ.ker * Nat.card φ.range := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv,
      mul_comm, ← Subgroup.card_eq_card_quotient_mul_card_subgroup]
  rw [hcard, mul_comm 9]
  exact Nat.mul_le_mul hker hrange

theorem card_le_nine_mul_of_block (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {T : Subgroup (GL (Fin 3) K)} (h3 : ∀ t ∈ T, t ^ 3 ∈ StatedScalars (Fin 3) K)
    (hab : ∀ t ∈ T, ∀ u ∈ T, t * u = u * t) {a g z : GL (Fin 3) K} (ha : a ∈ T)
    (hz : z ∈ StatedScalars (Fin 3) K) {d : Fin 3 → K}
    (hD : ((g⁻¹ * (a * z) * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal d)
    (h01 : d 0 ≠ d 1) (h02 : d 0 ≠ d 2) :
    Nat.card T ≤ 9 * Nat.card ↥(T ⊓ StatedScalars (Fin 3) K) := by
  have := hK.finite
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  set e : Kˣ := Units.mk0 τ hτ0
  have he : e ≠ 1 := fun h => hτ1 (by
    rw [← Units.val_mk0 hτ0, show Units.mk0 τ hτ0 = e from rfl, h, Units.val_one])
  set C := centralizer ({diagE e} : Set (GL (Fin 3) K))
  have hmem : ∀ t ∈ T, g⁻¹ * t * g ∈ C := by
    intro t ht
    apply mem_centralizer_of_isBlock
    have h1 := hab t ht a ha
    have h2 := commute_of_mem_statedScalars hz t
    have htaz : t * (a * z) = (a * z) * t := by
      rw [← mul_assoc, h1, mul_assoc, h2, ← mul_assoc]
    have hc : (g⁻¹ * t * g) * (g⁻¹ * (a * z) * g) = (g⁻¹ * (a * z) * g) * (g⁻¹ * t * g) := by
      calc (g⁻¹ * t * g) * (g⁻¹ * (a * z) * g) = g⁻¹ * (t * (a * z)) * g := by group
        _ = g⁻¹ * ((a * z) * t) * g := by rw [htaz]
        _ = (g⁻¹ * (a * z) * g) * (g⁻¹ * t * g) := by group
    have hcm : ((g⁻¹ * t * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * diagonal d =
        diagonal d * ((g⁻¹ * t * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
      rw [← hD, ← Units.val_mul, ← Units.val_mul, hc]
    exact ⟨entry_eq_zero_of_commute_diagonal hcm h01,
      entry_eq_zero_of_commute_diagonal hcm h02,
      entry_eq_zero_of_commute_diagonal hcm (Ne.symm h01),
      entry_eq_zero_of_commute_diagonal hcm (Ne.symm h02)⟩
  let ρ : ↥T →* GL (Fin 2) K :=
    (blockGL he).comp
      { toFun := fun t => ⟨g⁻¹ * t * g, hmem t t.2⟩
        map_one' := Subtype.ext (by simp)
        map_mul' := fun s t => Subtype.ext (by
          show g⁻¹ * (s * t : GL (Fin 3) K) * g = g⁻¹ * s * g * (g⁻¹ * t * g)
          group) }
  have hρ : ∀ t : ↥T, ρ t = blockGL he ⟨g⁻¹ * t * g, hmem t t.2⟩ := fun t => rfl
  have hker : Nat.card ρ.ker ≤ Nat.card ↥(T ⊓ StatedScalars (Fin 3) K) := by
    rw [← Subgroup.card_map_of_injective T.subtype_injective]
    refine Subgroup.card_le_of_le ?_
    rintro _ ⟨t, ht, rfl⟩
    have h1 := mem_statedScalars_of_blockGL_eq_one he
      (show blockGL he ⟨_, hmem t t.2⟩ = 1 from ht)
    exact ⟨t.2, (inv_conj_mem_statedScalars_iff g t).1 h1⟩
  have hrange : Nat.card ρ.range ≤ 9 := by
    refine card_le_nine_of_elemAbelian_GL2 (not_three_dvd_card hK hq) ⟨⟨⟨?_⟩⟩, ?_⟩
    · rintro ⟨_, s, rfl⟩ ⟨_, t, rfl⟩
      apply Subtype.ext
      show ρ s * ρ t = ρ t * ρ s
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hab s s.2 t t.2)
    · rintro _ ⟨t, rfl⟩
      rw [← map_pow, hρ]
      obtain ⟨c, hc⟩ := h3 t t.2
      have hconj : g⁻¹ * ((t ^ 3 : ↥T) : GL (Fin 3) K) * g =
          GeneralLinearGroup.scalar (Fin 3) c := by
        rw [SubgroupClass.coe_pow, ← hc, mul_assoc, ← commute_of_mem_statedScalars ⟨c, rfl⟩ g,
          inv_mul_cancel_left]
      have hsc : GeneralLinearGroup.scalar (Fin 3) c ∈ C := by
        rw [← hconj]
        exact hmem _ (t ^ 3).2
      have : (⟨g⁻¹ * ((t ^ 3 : ↥T) : GL (Fin 3) K) * g, hmem _ (t ^ 3).2⟩ : C) = ⟨_, hsc⟩ :=
        Subtype.ext hconj
      rw [this, blockGL_scalar]
  have hcard : Nat.card T = Nat.card ρ.ker * Nat.card ρ.range := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv,
      mul_comm, ← Subgroup.card_eq_card_quotient_mul_card_subgroup]
  rw [hcard, mul_comm 9]
  exact Nat.mul_le_mul hker hrange

theorem card_le_nine_mul_of_commute_mod (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {T : Subgroup (GL (Fin 3) K)} (hTH : T ≤ glPi π 3 (p ^ f) K)
    (h3 : ∀ t ∈ T, t ^ 3 ∈ StatedScalars (Fin 3) K)
    (hc : ∀ t ∈ T, ∀ u ∈ T, t * u * t⁻¹ * u⁻¹ ∈ StatedScalars (Fin 3) K) :
    Nat.card T ≤ 9 * Nat.card ↥(T ⊓ StatedScalars (Fin 3) K) := by
  have := hK.finite
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  by_cases hH : ∃ u ∈ T, ∃ v ∈ T, u * v * u⁻¹ * v⁻¹ ≠ 1
  · obtain ⟨u, hu, v, hv, huv⟩ := hH
    exact card_le_nine_mul_of_heis hK hq h3 hc hu hv huv
  push Not at hH
  have hab : ∀ t ∈ T, ∀ u ∈ T, t * u = u * t := fun t ht u hu => by
    have := hH t ht u hu
    calc t * u = t * u * t⁻¹ * u⁻¹ * (u * t) := by group
      _ = u * t := by rw [this, one_mul]
  by_cases hTN : T ≤ StatedScalars (Fin 3) K
  · rw [inf_eq_left.2 hTN]
    exact Nat.le_mul_of_pos_left _ (by norm_num)
  obtain ⟨a, ha, haN⟩ := Set.not_subset.1 hTN
  have haH := hTH ha
  have haZ : a ∉ zPi π 3 (p ^ f) K := by
    rw [zPi_eq hπ hq' hτ hτ1]
    exact fun h => haN (Subgroup.mem_inf.1 h).2
  have ha3 : a ^ 3 ∈ zPi π 3 (p ^ f) K := by
    rw [zPi_eq hπ hq' hτ hτ1]
    exact Subgroup.mem_inf.2 ⟨pow_mem haH 3, h3 a ha⟩
  rcases type123_exhaust hK hq haH haZ ha3 with h1 | h2 | h3'
  · obtain ⟨τ', hτ', hτ'1, z, hz, g, -, hD⟩ := h1
    refine card_le_nine_mul_of_block hK hq h3 hab ha
      (mem_statedScalars_of_mem_zPi hK hq hτ hτ1 hz) (d := ![τ', τ' ^ 2, 1])
      (by rw [hD, coe_diagTau_eq_diagonal]) ?_ ?_
    · intro h
      apply hτ'1
      have hτ'0 : τ' ≠ 0 := by
        rintro rfl
        simp at hτ'
      have h' : τ' * τ' = τ' * 1 := by simpa [sq] using h.symm
      exact mul_left_cancel₀ hτ'0 h'
    · simpa using hτ'1
  · obtain ⟨e, he3, he1, z, hz, g, -, hD⟩ := h2
    refine card_le_nine_mul_of_block hK hq h3 hab ha
      (mem_statedScalars_of_mem_zPi hK hq hτ hτ1 hz) (d := ![(e : K), 1, 1])
      (by rw [hD, coe_diagE]) ?_ ?_
    · simpa using fun h => he1 (Units.ext h)
    · simpa using fun h => he1 (Units.ext h)
  ·
    obtain ⟨-, -, hirr⟩ := h3'
    obtain ⟨ℓ, -, hℓ⟩ := exists_scalar_of_mem_zPi hK hq hτ hτ1 ha3
    have hcube : ∀ μ : K, μ ^ 3 ≠ (ℓ : K) := by
      intro μ hμ
      have hμ0 : μ ≠ 0 := by
        rintro rfl
        rw [zero_pow (by norm_num)] at hμ
        exact ℓ.ne_zero hμ.symm
      have hμ' : a ^ 3 = GeneralLinearGroup.scalar (Fin 3) (Units.mk0 μ hμ0 ^ 3) := by
        rw [← hℓ]
        congr 1
        exact Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hμ])
      obtain ⟨y, ⟨z, hz, rfl⟩, g, -, hD⟩ := exists_diag_normal_form hK hq hτ hτ1 haH haN hμ'
      rcases hD with hD | ⟨e, -, hD⟩
      · exact not_irreducible_of_diag (g := g) (mem_statedScalars_of_mem_zPi hK hq hτ hτ1 hz)
          (d := ![τ, τ ^ 2, 1]) (by rw [hD, coe_diagTau_eq_diagonal]) hirr
      · exact not_irreducible_of_diag (g := g) (mem_statedScalars_of_mem_zPi hK hq hτ hτ1 hz)
          (d := ![(e : K), 1, 1]) (by rw [hD, coe_diagE]) hirr
    have hy : (a : Matrix (Fin 3) (Fin 3) K) ^ 3 = (ℓ : K) • 1 := by
      rw [← Units.val_pow_eq_pow_val, ← hℓ, coe_scalar_eq_smul]
    haveI hcyc := (centralizer_cyclic_card hcube hy).1
    have hTC : T ≤ centralizer ({a} : Set (GL (Fin 3) K)) := fun t ht =>
      mem_centralizer_singleton_iff.2 (hab t ht a ha)
    haveI : IsCyclic ↥T := by
      haveI : IsCyclic ↥(T.subgroupOf (centralizer ({a} : Set (GL (Fin 3) K)))) :=
        Subgroup.isCyclic _
      exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hTC).toMonoidHom
        (Subgroup.subgroupOfEquivOfLe hTC).surjective
    have h := card_le_three_mul_of_cube_mem ((T ⊓ StatedScalars (Fin 3) K).subgroupOf T)
      (fun t => Subgroup.mem_subgroupOf.2 ⟨(t ^ 3).2, by
        rw [SubgroupClass.coe_pow]; exact h3 t t.2⟩)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv] at h
    omega

end PGL

section SL

variable {K : Type} [Field K] {π : Bool} {p f : ℕ}

theorem not_elemAbelian_27_slPi (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {E : Subgroup (GL (Fin 3) K)} (hEL : E ≤ slPi π 3 (p ^ f) K)
    (hE : CFSG.Open.IsElemAbelian 3 E) : Nat.card E ≠ 27 := by
  have := hK.finite
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  intro h27
  have hsc : Nat.card ↥(E ⊓ StatedScalars (Fin 3) K) ≤ 3 := by
    haveI := isCyclic_statedScalars (K := K)
    have hle : E ⊓ StatedScalars (Fin 3) K ≤ StatedScalars (Fin 3) K := inf_le_right
    haveI : IsCyclic ↥((E ⊓ StatedScalars (Fin 3) K).subgroupOf (StatedScalars (Fin 3) K)) :=
      Subgroup.isCyclic _
    haveI : IsCyclic ↥(E ⊓ StatedScalars (Fin 3) K) :=
      isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hle).toMonoidHom
        (Subgroup.subgroupOfEquivOfLe hle).surjective
    refine card_le_three_of_isCyclic ?_
    intro w
    exact Subtype.ext (hE.2 _ w.2.1)
  have hnot : ¬ E ≤ StatedScalars (Fin 3) K := by
    intro h
    rw [inf_eq_left.2 h, h27] at hsc
    omega
  obtain ⟨s, hs, hsN⟩ := Set.not_subset.1 hnot
  have hsL := hEL hs
  have hsZ : s ∉ zPi π 3 (p ^ f) K := by
    rw [zPi_eq hπ hq' hτ hτ1]
    exact fun h => hsN (Subgroup.mem_inf.1 h).2
  have hs1 : s ≠ 1 := fun h => hsN (h ▸ one_mem _)
  have hso : orderOf s = 3 := orderOf_eq_prime (hE.2 s hs) hs1
  obtain ⟨g, hg, hD⟩ := rank3II_4_10_three hK hq hτ hτ1 hsL hsZ hso
  have hEC : E.map (MulAut.conj g⁻¹).toMonoidHom ≤
      slPi π 3 (p ^ f) K ⊓ centralizer ({diagTau hτ} : Set (GL (Fin 3) K)) := by
    rintro _ ⟨t, ht, rfl⟩
    refine Subgroup.mem_inf.2 ⟨?_, mem_centralizer_singleton_iff.2 ?_⟩
    · have := conj_mem_slPi hπ (inv_mem hg) (hEL ht)
      simpa using this
    · rw [← hD]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      have hc : t * s = s * t := hE.comm ht hs
      calc g⁻¹ * t * g * (g⁻¹ * s * g) = g⁻¹ * (t * s) * g := by group
        _ = g⁻¹ * (s * t) * g := by rw [hc]
        _ = g⁻¹ * s * g * (g⁻¹ * t * g) := by group
  obtain ⟨ψ⟩ := centralizer_diagTau_mulEquiv hK hq hτ hτ1
  have hNe : NeZero (qSubPi π (p ^ f)) := ⟨qSubPi_ne_zero hK hq⟩
  set F := (E.map (MulAut.conj g⁻¹).toMonoidHom).subgroupOf
    (slPi π 3 (p ^ f) K ⊓ centralizer ({diagTau hτ} : Set (GL (Fin 3) K)))
  have hF : Nat.card (F.map ψ.toMonoidHom) ≤ 9 := by
    refine card_le_nine_of_pow_three _ ?_
    rintro _ ⟨t, ht, rfl⟩
    rw [← map_pow]
    have : t ^ 3 = 1 := by
      obtain ⟨u, hu, hut⟩ := Subgroup.mem_subgroupOf.1 ht
      apply Subtype.ext
      rw [SubgroupClass.coe_pow, ← hut]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, OneMemClass.coe_one]
      rw [conj_pow, hE.2 u hu, mul_one, mul_inv_cancel]
    rw [this, map_one]
  rw [Subgroup.card_map_of_injective ψ.injective,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEC).toEquiv,
    Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, h27] at hF
  omega

end SL

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott
