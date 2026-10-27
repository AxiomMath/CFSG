module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.FRBasic
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FQLin
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FQSp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FQUni
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FQOmega

public section

namespace CFSG.LocalAnalysis.GLTheoremA

namespace FR

open CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.FP
open CFSG.LocalAnalysis.GLTheoremA.FQ CFSG.LocalAnalysis.GLTheoremA.YS09Field CFSG.Assembly
open scoped commutatorElement

section Mat

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

theorem scalar_iff [Nonempty ι] (k : Subfield K) (A : GL ι k) :
    A ∈ CFSG.Open.StatedScalars ι k ↔
      Matrix.GeneralLinearGroup.map k.subtype A ∈ CFSG.Open.StatedScalars ι K := by
  constructor
  · rintro ⟨c, rfl⟩
    refine ⟨Units.map k.subtype.toMonoidHom c, ?_⟩
    apply Units.ext
    ext i j
    by_cases h : i = j
    · subst h
      simp [Matrix.GeneralLinearGroup.coe_scalar, coe_glMap]
    · simp [Matrix.GeneralLinearGroup.coe_scalar, coe_glMap, Matrix.diagonal_apply, h]
  · rintro ⟨c, hc⟩
    obtain ⟨i⟩ := ‹Nonempty ι›
    have hent : ∀ a b : ι, ((A : Matrix ι ι k) a b : K) = if a = b then (c : K) else 0 := by
      intro a b
      have := congrArg (fun g : GL ι K => (g : Matrix ι ι K) a b) hc
      simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply,
        coe_glMap] using this.symm
    have hcm : (c : K) ∈ k := by
      have := hent i i
      rw [if_pos rfl] at this
      rw [← this]
      exact (A : Matrix ι ι k) i i |>.2
    have hc0 : (⟨(c : K), hcm⟩ : k) ≠ 0 := by
      intro h
      have : (c : K) = 0 := congrArg Subtype.val h
      exact c.ne_zero this
    refine ⟨Units.mk0 ⟨(c : K), hcm⟩ hc0, ?_⟩
    apply Units.ext
    ext a b
    have := hent a b
    by_cases h : a = b
    · subst h
      rw [if_pos rfl] at this
      simp [Matrix.GeneralLinearGroup.coe_scalar, this]
    · rw [if_neg h] at this
      simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.diagonal_apply, h, this]


noncomputable def fixHom (σ : K ≃+* K) (H : Subgroup (GL ι K))
    (hH : ∀ σ : K ≃+* K, ∀ h ∈ H, Matrix.GeneralLinearGroup.map σ.toRingHom h ∈ H)
    (Hk : Subgroup (GL ι (fixF σ)))
    (hiff : ∀ A : GL ι (fixF σ),
      Matrix.GeneralLinearGroup.map (fixF σ).subtype A ∈ H ↔ A ∈ Hk) :
    Hk →* ↥(FP.fixSub (matAct H hH σ)) where
  toFun A := ⟨⟨Matrix.GeneralLinearGroup.map (fixF σ).subtype A.1, (hiff A.1).2 A.2⟩,
    FP.mem_fixSub.2 (Subtype.ext (by rw [matAct_coe]; exact glMap_subtype_fixed σ A.1))⟩
  map_one' := Subtype.ext (Subtype.ext (map_one _))
  map_mul' A B := Subtype.ext (Subtype.ext (map_mul _ _ _))

theorem fixHom_bijective (σ : K ≃+* K) (H : Subgroup (GL ι K))
    (hH : ∀ σ : K ≃+* K, ∀ h ∈ H, Matrix.GeneralLinearGroup.map σ.toRingHom h ∈ H)
    (Hk : Subgroup (GL ι (fixF σ)))
    (hiff : ∀ A : GL ι (fixF σ),
      Matrix.GeneralLinearGroup.map (fixF σ).subtype A ∈ H ↔ A ∈ Hk) :
    Function.Bijective (fixHom σ H hH Hk hiff) := by
  constructor
  · intro A B hAB
    apply Subtype.ext
    exact glMap_subtype_injective σ (congrArg (fun h => ((h.1 : H) : GL ι K)) hAB)
  · rintro ⟨⟨h, hh⟩, hfix⟩
    have hf : Matrix.GeneralLinearGroup.map σ.toRingHom h = h :=
      congrArg Subtype.val (FP.mem_fixSub.1 hfix)
    obtain ⟨A, hA⟩ := exists_descend σ h hf
    have hAk : A ∈ Hk := (hiff A).1 (hA ▸ hh)
    exact ⟨⟨A, hAk⟩, Subtype.ext (Subtype.ext hA)⟩

noncomputable def fixEquiv (σ : K ≃+* K) (H : Subgroup (GL ι K))
    (hH : ∀ σ : K ≃+* K, ∀ h ∈ H, Matrix.GeneralLinearGroup.map σ.toRingHom h ∈ H)
    (Hk : Subgroup (GL ι (fixF σ)))
    (hiff : ∀ A : GL ι (fixF σ),
      Matrix.GeneralLinearGroup.map (fixF σ).subtype A ∈ H ↔ A ∈ Hk) :
    Hk ≃* ↥(FP.fixSub (matAct H hH σ)) :=
  MulEquiv.ofBijective (fixHom σ H hH Hk hiff) (fixHom_bijective σ H hH Hk hiff)

theorem subfield_of_matrix [Nonempty ι] [Finite K] {m : ℕ} (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ m)
    (H : Subgroup (GL ι K))
    (hH : ∀ σ : K ≃+* K, ∀ h ∈ H, Matrix.GeneralLinearGroup.map σ.toRingHom h ∈ H)
    (good : (K ≃+* K) → Prop) (hgood : ∀ σ, good σ → ∀ n : ℕ, good (σ ^ n))
    {u v : ℕ} (hu : 0 < u) (hv : 0 < v)
    (hordH : twoPart (Nat.card H) ^ v = 2 ^ (m * u))
    (hfix : ∀ σ, good σ → ∀ e : ℕ, Nat.card {x : K // σ x = x} = 2 ^ e →
      twoPart (Nat.card {h : H // Matrix.GeneralLinearGroup.map σ.toRingHom (h : GL ι K) = h}) ^ v =
        2 ^ (e * u))
    {p : ℕ} (hp : p.Prime) (hred : ∀ σ : K ≃+* K, ∃ n : ℕ, ¬ p ∣ n ∧ good (σ ^ n))
    (Hk : (σ : K ≃+* K) → Subgroup (GL ι (fixF σ)))
    (hiff : ∀ (σ : K ≃+* K), good σ → ∀ (A : GL ι (fixF σ)),
      Matrix.GeneralLinearGroup.map (fixF σ).subtype A ∈ H ↔ A ∈ Hk σ)
    (F : Set (MulAut (LargeEvenProj H))) (hF : F ⊆ LargeEvenMatFieldImage (LargeEvenProjMk H)) :
    ∀ f ∈ F, orderOf f = p → ∃ (σ₀ : K ≃+* K) (D : Subgroup (LargeEvenProj H)),
      orderOf σ₀ = p ∧ Nat.card (fixF σ₀) = 2 ^ (m / p) ∧ p ∣ m ∧
      D ≤ FP.fixSub f ∧ ⁅FP.fixSub f, FP.fixSub f⁆ ≤ D ∧ Odd (D.relIndex (FP.fixSub f)) ∧
      Nonempty (↥D ≃* LargeEvenProj (Hk σ₀)) := by
  intro f hf hord
  obtain ⟨σ, hσ⟩ := matField_spec H hH (hF hf)
  have hZc := scalars_subgroupOf_le_center H
  have hZo := scalars_subgroupOf_odd hm hK H
  obtain ⟨n, hn, hσ₀ord, hgn, hσn⟩ := sigma_order hm hK
    ((CFSG.Open.StatedScalars ι K).subgroupOf H) hZc hZo (matAct H hH) good hgood hu hv hordH
    (fun σ hσ e he => by rw [fixNum_matAct]; exact hfix σ hσ e he) hp hred f σ hσ hord
  obtain ⟨hDT, hcomm, hodd⟩ := subfield_core ((CFSG.Open.StatedScalars ι K).subgroupOf H) hZc hZo
    (matAct H hH (σ ^ n)) (f ^ n) hσn
  have hfeq := fixSub_pow_eq hp hord hn
  obtain ⟨hdvd, hcard⟩ := card_fixedPoints_field hm hK (σ ^ n)
  rw [hσ₀ord] at hdvd hcard
  refine ⟨σ ^ n, (FP.fixSub (matAct H hH (σ ^ n))).map
    (QuotientGroup.mk' ((CFSG.Open.StatedScalars ι K).subgroupOf H)), hσ₀ord,
    card_fixF.trans hcard, hdvd, hfeq ▸ hDT, hfeq ▸ hcomm, hfeq ▸ hodd, ?_⟩
  exact equiv_of_map_mk ((CFSG.Open.StatedScalars ι K).subgroupOf H)
    (FP.fixSub (matAct H hH (σ ^ n)))
    ((CFSG.Open.StatedScalars ι (fixF (σ ^ n))).subgroupOf (Hk (σ ^ n)))
    (fixEquiv (σ ^ n) H hH (Hk (σ ^ n)) (hiff (σ ^ n) hgn)) (fun x => by
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, scalar_iff]
      rfl)


end Mat

section Body

@[expose] def SubfieldGrp {R : Type} [Group R] (f : MulAut R) (D : Subgroup R) : Prop :=
  D ≤ FP.fixSub f ∧ ⁅FP.fixSub f, FP.fixSub f⁆ ≤ D ∧ Odd (D.relIndex (FP.fixSub f))

@[expose] def SubBody (p m : ℕ) (Rec : ℕ → LargeEvenRawCont → Prop) : LargeEvenRawCont :=
  fun R _ _ F => ∀ f ∈ F, orderOf f = p → p ∣ m ∧ ∃ D : Subgroup R, SubfieldGrp f D ∧
    Rec (m / p) (fun R' _ _ _ => Nonempty (↥D ≃* R'))

end Body

section Linear

open CFSG.Open

variable {K : Type} [Field K] [Finite K] {d : ℕ}

theorem subBody_linear (hd : 2 ≤ d) {m : ℕ} (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ m) {p : ℕ}
    (hp : p.Prime) (I : Set (MulAut (LargeEvenProj (LargeEvenSLGroup (Fin d) K)))) :
    SubBody p m (fun m' Q' => LargeEvenRecipeLinear d (2 ^ m') Q')
      (LargeEvenProj (LargeEvenSLGroup (Fin d) K)) I
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K))) := by
  intro f hf hord
  haveI : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  have hu : 0 < d * (d - 1) / 2 := by
    have : 2 ≤ d * (d - 1) := calc 2 = 2 * 1 := rfl
      _ ≤ d * (d - 1) := Nat.mul_le_mul hd (by omega)
    exact Nat.div_pos this (by norm_num)
  have hordH : twoPart (Nat.card (LargeEvenSLGroup (Fin d) K)) ^ 1 =
      2 ^ (m * (d * (d - 1) / 2)) := by
    rw [pow_one]
    exact twoPart_card_SL hd hm hK
  have hfix : ∀ σ : K ≃+* K, True → ∀ e : ℕ, Nat.card {x : K // σ x = x} = 2 ^ e →
      twoPart (Nat.card {h : LargeEvenSLGroup (Fin d) K //
        Matrix.GeneralLinearGroup.map σ.toRingHom (h : GL (Fin d) K) = h}) ^ 1 =
        2 ^ (e * (d * (d - 1) / 2)) := by
    intro σ _ e he
    have hk : Nat.card (fixF σ) = 2 ^ e := card_fixF.trans he
    rw [pow_one, card_fixed_eq_of_iff σ _ (LargeEvenSLGroup (Fin d) (fixF σ)) (sl_map_subtype_iff σ)]
    exact twoPart_card_SL hd (one_le_of_card_fixed he) hk
  obtain ⟨σ₀, D, ho, hc, hdvd, hD1, hD2, hD3, ⟨e⟩⟩ := subfield_of_matrix hm hK
    (LargeEvenSLGroup (Fin d) K) (fun σ h hh => sl_map_mem σ h hh) (fun _ => True)
    (fun _ _ _ => trivial) hu one_pos hordH hfix hp
    (fun σ => ⟨1, fun h => hp.one_lt.ne' (Nat.dvd_one.1 h), trivial⟩)
    (fun σ => LargeEvenSLGroup (Fin d) (fixF σ)) (fun σ _ A => sl_map_subtype_iff σ A) _ subset_rfl
    f hf hord
  exact ⟨hdvd, D, ⟨hD1, hD2, hD3⟩, fixF σ₀, inferInstance, inferInstance, hc, ⟨e⟩⟩

end Linear

section Symplectic

open CFSG.Open

variable {K : Type} [Field K] [Finite K] {m : ℕ}

theorem subBody_symplectic (hm : 1 ≤ m) {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n) {p : ℕ}
    (hp : p.Prime) (I : Set (MulAut (LargeEvenProj (LargeEvenSpGroup K m)))) :
    SubBody p n (fun n' Q' => LargeEvenRecipeSymplectic m (2 ^ n') false Q')
      (LargeEvenProj (LargeEvenSpGroup K m)) I
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSpGroup K m))) := by
  intro f hf hord
  haveI : Nonempty (Fin m ⊕ Fin m) := ⟨Sum.inl ⟨0, by omega⟩⟩
  have hu : 0 < m * m := Nat.mul_pos hm hm
  have hordH : twoPart (Nat.card (LargeEvenSpGroup K m)) ^ 1 = 2 ^ (n * (m * m)) := by
    rw [pow_one]
    exact twoPart_card_Sp hn hK
  have hfix : ∀ σ : K ≃+* K, True → ∀ e : ℕ, Nat.card {x : K // σ x = x} = 2 ^ e →
      twoPart (Nat.card {h : LargeEvenSpGroup K m //
        Matrix.GeneralLinearGroup.map σ.toRingHom (h : GL (Fin m ⊕ Fin m) K) = h}) ^ 1 =
        2 ^ (e * (m * m)) := by
    intro σ _ e he
    have hk : Nat.card (fixF σ) = 2 ^ e := card_fixF.trans he
    rw [pow_one, card_fixed_eq_of_iff σ _ (LargeEvenSpGroup (fixF σ) m) (sp_map_subtype_iff σ)]
    exact twoPart_card_Sp (one_le_of_card_fixed he) hk
  obtain ⟨σ₀, D, ho, hc, hdvd, hD1, hD2, hD3, ⟨e⟩⟩ := subfield_of_matrix hn hK
    (LargeEvenSpGroup K m) (fun σ h hh => sp_map_mem σ h hh) (fun _ => True)
    (fun _ _ _ => trivial) hu one_pos hordH hfix hp
    (fun σ => ⟨1, fun h => hp.one_lt.ne' (Nat.dvd_one.1 h), trivial⟩)
    (fun σ => LargeEvenSpGroup (fixF σ) m) (fun σ _ A => sp_map_subtype_iff σ A) _ subset_rfl
    f hf hord
  exact ⟨hdvd, D, ⟨hD1, hD2, hD3⟩, fixF σ₀, inferInstance, inferInstance, hc, ⟨e⟩⟩

end Symplectic

section OmegaPlus

open CFSG.Open

variable {K : Type} [Field K] [Finite K] {m : ℕ}

theorem subBody_omegaPlus (hm : 4 ≤ m) {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n) {p : ℕ}
    (hp : p.Prime) (I : Set (MulAut (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m))))) :
    SubBody p n (fun n' Q' => LargeEvenRecipeOmegaPlus m (2 ^ n') Q')
      (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m))) I
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus K m)))) := by
  intro f hf hord
  haveI : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hK
  haveI : Nonempty (Fin m ⊕ Fin m) := ⟨Sum.inl ⟨0, by omega⟩⟩
  have hu : 0 < m * (m - 1) := Nat.mul_pos (by omega) (by omega)
  have hordH : twoPart (Nat.card (LargeEvenOmega (LargeEvenQPlus K m))) ^ 1 =
      2 ^ (n * (m * (m - 1))) := by
    rw [pow_one]
    exact twoPart_card_omegaPlus hn hK hm
  have hfix : ∀ σ : K ≃+* K, True → ∀ e : ℕ, Nat.card {x : K // σ x = x} = 2 ^ e →
      twoPart (Nat.card {h : LargeEvenOmega (LargeEvenQPlus K m) //
        Matrix.GeneralLinearGroup.map σ.toRingHom (h : GL (Fin m ⊕ Fin m) K) = h}) ^ 1 =
        2 ^ (e * (m * (m - 1))) := by
    intro σ _ e he
    have hk : Nat.card (fixF σ) = 2 ^ e := card_fixF.trans he
    rw [pow_one, card_fixed_omegaPlus (by omega) σ]
    exact twoPart_card_omegaPlus (one_le_of_card_fixed he) hk hm
  obtain ⟨σ₀, D, ho, hc, hdvd, hD1, hD2, hD3, ⟨e⟩⟩ := subfield_of_matrix hn hK
    (LargeEvenOmega (LargeEvenQPlus K m)) (fun σ h hh => omegaPlus_map_mem σ h hh) (fun _ => True)
    (fun _ _ _ => trivial) hu one_pos hordH hfix hp
    (fun σ => ⟨1, fun h => hp.one_lt.ne' (Nat.dvd_one.1 h), trivial⟩)
    (fun σ => LargeEvenOmega (LargeEvenQPlus (fixF σ) m))
    (fun σ _ A => map_subtype_mem_omegaPlus_iff (by omega) (fixF σ) A) _ subset_rfl f hf hord
  exact ⟨hdvd, D, ⟨hD1, hD2, hD3⟩, fixF σ₀, inferInstance, inferInstance, hc, ⟨e⟩⟩

end OmegaPlus

section Unitary

open CFSG.Open

variable {K : Type} [Field K] [Finite K] {d : ℕ}

theorem su_hiff [CharP K 2] {j : ℕ} (hj : 1 ≤ j) (hK : Nat.card K = (2 ^ j) ^ 2)
    (σ : K ≃+* K) (hσ : Odd (orderOf σ)) (A : GL (Fin d) (fixF σ)) :
    Matrix.GeneralLinearGroup.map (fixF σ).subtype A ∈ LargeEvenSUGroup (Fin d) K (2 ^ j) ↔
      A ∈ LargeEvenSUGroup (Fin d) (fixF σ) (2 ^ (j / orderOf σ)) := by
  have hK' : Nat.card K = 2 ^ (2 * j) := by rw [hK, ← pow_mul, mul_comm]
  obtain ⟨hdvd, hcard⟩ := card_fixedPoints_field (m := 2 * j) (by omega) hK' σ
  have hcop : (orderOf σ).Coprime 2 := (Nat.coprime_two_left.2 hσ).symm
  obtain ⟨j', hjj'⟩ := (Nat.Coprime.dvd_of_dvd_mul_left hcop hdvd : orderOf σ ∣ j)
  have hr0 : 0 < orderOf σ := Nat.pos_of_dvd_of_pos hdvd (by omega)
  have hj'eq : j / orderOf σ = j' := by
    rw [hjj']; exact Nat.mul_div_cancel_left _ hr0
  have hee' : 2 * j / orderOf σ = 2 * j' := by
    rw [hjj', ← mul_assoc, mul_comm 2 (orderOf σ), mul_assoc, Nat.mul_div_cancel_left _ hr0]
  have hk : Nat.card (fixF σ) = (2 ^ j') ^ 2 := by
    rw [card_fixF, hcard, hee', pow_mul']
  haveI : CharP (fixF σ) 2 :=
    CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq (f := 2 * j')
      (by rw [hk, ← pow_mul, mul_comm])
  rw [hj'eq]
  exact su_map_subtype_iff (j := j) (j' := j') (r := orderOf σ) (by rw [hjj', mul_comm]) hσ σ hk A

theorem subBody_unitary [CharP K 2] (hd : 3 ≤ d) {j : ℕ} (hj : 1 ≤ j)
    (hK : Nat.card K = (2 ^ j) ^ 2) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (I : Set (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ j))))) :
    SubBody p j (fun j' Q' => LargeEvenRecipeUnitary d (2 ^ j') Q')
      (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ j))) I
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ j)))) := by
  intro f hf hord
  have hK' : Nat.card K = 2 ^ (2 * j) := by rw [hK, ← pow_mul, mul_comm]
  haveI : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  have hu : 0 < d * (d - 1) / 2 := by
    have : 2 ≤ d * (d - 1) := calc 2 = 2 * 1 := rfl
      _ ≤ d * (d - 1) := Nat.mul_le_mul (by omega) (by omega)
    exact Nat.div_pos this (by norm_num)
  have hordH : twoPart (Nat.card (LargeEvenSUGroup (Fin d) K (2 ^ j))) ^ 2 =
      2 ^ (2 * j * (d * (d - 1) / 2)) := by
    rw [twoPart_card_SU hd hj hK, ← pow_mul]
    exact congrArg (2 ^ ·) (by ring)
  have hfix : ∀ σ : K ≃+* K, Odd (orderOf σ) → ∀ e : ℕ, Nat.card {x : K // σ x = x} = 2 ^ e →
      twoPart (Nat.card {h : LargeEvenSUGroup (Fin d) K (2 ^ j) //
        Matrix.GeneralLinearGroup.map σ.toRingHom (h : GL (Fin d) K) = h}) ^ 2 =
        2 ^ (e * (d * (d - 1) / 2)) := by
    intro σ hσ e he
    obtain ⟨hdvd, hcard⟩ := card_fixedPoints_field (m := 2 * j) (by omega) hK' σ
    have hee : e = 2 * j / orderOf σ := Nat.pow_right_injective (le_refl 2) (he.symm.trans hcard)
    have hcop : (orderOf σ).Coprime 2 := (Nat.coprime_two_left.2 hσ).symm
    obtain ⟨j', hjj'⟩ := (Nat.Coprime.dvd_of_dvd_mul_left hcop hdvd : orderOf σ ∣ j)
    have hr0 : 0 < orderOf σ := Nat.pos_of_dvd_of_pos hdvd (by omega)
    have hee' : e = 2 * j' := by
      rw [hee, hjj', ← mul_assoc, mul_comm 2 (orderOf σ), mul_assoc, Nat.mul_div_cancel_left _ hr0]
    have hj' : 1 ≤ j' := by
      rcases Nat.eq_zero_or_pos j' with h0 | h0
      · rw [h0, mul_zero] at hjj'; omega
      · exact h0
    have hk : Nat.card (fixF σ) = (2 ^ j') ^ 2 := by
      rw [card_fixF.trans he, hee', pow_mul']
    haveI : CharP (fixF σ) 2 :=
      CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq (f := 2 * j')
        (by rw [hk, ← pow_mul, mul_comm])
    have hj'eq : j / orderOf σ = j' := by
      rw [hjj']; exact Nat.mul_div_cancel_left _ hr0
    rw [card_fixed_eq_of_iff σ _ (LargeEvenSUGroup (Fin d) (fixF σ) (2 ^ j'))
      (fun A => by simpa [hj'eq] using su_hiff hj hK σ hσ A),
      twoPart_card_SU hd hj' hk, ← pow_mul, hee']
    congr 1
    ring
  have hred : ∀ σ : K ≃+* K, ∃ n : ℕ, ¬ p ∣ n ∧ Odd (orderOf (σ ^ n)) := by
    intro σ
    obtain ⟨hdvd, -⟩ := card_fixedPoints_field (m := 2 * j) (by omega) hK' σ
    have hr0 : orderOf σ ≠ 0 := (Nat.pos_of_dvd_of_pos hdvd (by omega)).ne'
    obtain ⟨a, c, hc, hac⟩ := Nat.exists_eq_two_pow_mul_odd hr0
    refine ⟨2 ^ a, fun h => hp2 ?_, ?_⟩
    · exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h)
    · rw [orderOf_pow' _ (by positivity), hac, Nat.gcd_eq_right (Dvd.intro c rfl),
        Nat.mul_div_cancel_left c (by positivity)]
      exact hc
  obtain ⟨σ₀, D, ho, hc, hdvd, hD1, hD2, hD3, ⟨e⟩⟩ := subfield_of_matrix (m := 2 * j) (by omega) hK'
    (LargeEvenSUGroup (Fin d) K (2 ^ j)) (fun σ h hh => su_map_mem σ h hh)
    (fun σ => Odd (orderOf σ))
    (fun σ hσ n => Odd.of_dvd_nat hσ (orderOf_pow_dvd n)) hu two_pos hordH hfix hp hred
    (fun σ => LargeEvenSUGroup (Fin d) (fixF σ) (2 ^ (j / orderOf σ)))
    (fun σ hσ A => su_hiff hj hK σ hσ A) _ subset_rfl f hf hord
  have hpj : p ∣ j := by
    have hcop : p.Coprime 2 := (Nat.coprime_primes hp Nat.prime_two).2 hp2
    exact hcop.dvd_of_dvd_mul_left hdvd
  have hc' : Nat.card (fixF σ₀) = (2 ^ (j / p)) ^ 2 := by
    rw [hc, ← pow_mul]
    congr 1
    obtain ⟨c, hcc⟩ := hpj
    rw [hcc, Nat.mul_div_cancel_left _ hp.pos, show 2 * (p * c) = p * (2 * c) by ring,
      Nat.mul_div_cancel_left _ hp.pos]
    ring
  refine ⟨hpj, D, ⟨hD1, hD2, hD3⟩, fixF σ₀, inferInstance, inferInstance, hc', ?_⟩
  rw [ho] at e
  exact ⟨e⟩

end Unitary

end FR

end CFSG.LocalAnalysis.GLTheoremA
