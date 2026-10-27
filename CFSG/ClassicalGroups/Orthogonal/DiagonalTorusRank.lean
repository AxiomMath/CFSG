module

public import CFSG.ClassicalGroups.Orthogonal.OddOrder
public import CFSG.ClassicalGroups.Orthogonal.StatedOmegaElementary
public import CFSG.GroupTheory.CommutingMovingElemAbelian

public section

namespace CFSG.ClassicalGroups.Orthogonal

open CFSG.Open CFSG.LieType.Universal.Spin QuadraticMap
open Matrix

variable {m : ℕ} {F : Type} [Field F]

@[expose] def threeToFinOrth (hm : 4 ≤ m) : Fin 3 → Fin m := fun i => Fin.castLE (by omega) i

theorem threeToFinOrth_injective (hm : 4 ≤ m) :
    Function.Injective (threeToFinOrth (m := m) hm) :=
  Fin.castLE_injective (by omega)

@[expose] def pairedDiagHom (m : ℕ) (F : Type) [Field F] :
    (Fin m → Fˣ) →* (Fin m ⊕ Fin m → Fˣ) where
  toFun d := fun k =>
    match k with
    | Sum.inl i => d i
    | Sum.inr i => (d i)⁻¹
  map_one' := by
    funext k
    rcases k with i | i <;> simp
  map_mul' d e := by
    funext k
    rcases k with i | i <;> simp [mul_comm]

@[simp]
theorem pairedDiagHom_inl (d : Fin m → Fˣ) (i : Fin m) :
    pairedDiagHom m F d (Sum.inl i) = d i :=
  rfl

@[simp]
theorem pairedDiagHom_inr (d : Fin m → Fˣ) (i : Fin m) :
    pairedDiagHom m F d (Sum.inr i) = (d i)⁻¹ :=
  rfl

theorem pairedDiagHom_injective (m : ℕ) (F : Type) [Field F] :
    Function.Injective (pairedDiagHom m F) := by
  intro d e h
  funext i
  have := congrFun h (Sum.inl i)
  simpa using this

@[expose] noncomputable def diagGLPlusHom (m : ℕ) (F : Type) [Field F] :
    (Fin m → Fˣ) →* GL (Fin m ⊕ Fin m) F :=
  (TauCeti.diagGL (k := F) (ι := Fin m ⊕ Fin m)).comp (pairedDiagHom m F)

theorem diagGLPlusHom_injective (m : ℕ) (F : Type) [Field F] :
    Function.Injective (diagGLPlusHom m F) :=
  TauCeti.diagGL_injective.comp (pairedDiagHom_injective m F)

@[simp]
theorem coe_diagGLPlusHom (d : Fin m → Fˣ) :
    ((diagGLPlusHom m F d : GL (Fin m ⊕ Fin m) F) :
        Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F) =
      Matrix.diagonal (fun k => (pairedDiagHom m F d k : F)) :=
  TauCeti.diagGL_coe _

@[expose] noncomputable def diagTorusPlus (m : ℕ) (F : Type) [Field F] :
    Subgroup (GL (Fin m ⊕ Fin m) F) :=
  (diagGLPlusHom m F).range

theorem quadPlus_mulVec_diagGLPlus (d : Fin m → Fˣ) (v : Fin m ⊕ Fin m → F) :
    quadPlus m F
        (Matrix.mulVec ((diagGLPlusHom m F d : GL (Fin m ⊕ Fin m) F) :
          Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F) v) =
      quadPlus m F v := by
  rw [quadPlus_apply, quadPlus_apply, coe_diagGLPlusHom]
  simp only [Matrix.mulVec_diagonal]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pairedDiagHom_inl, pairedDiagHom_inr]
  have hd : (d i : F) * (((d i)⁻¹ : Fˣ) : F) = 1 := by simp
  calc
    ((d i : F) * v (Sum.inl i)) * ((((d i)⁻¹ : Fˣ) : F) * v (Sum.inr i))
        = ((d i : F) * (((d i)⁻¹ : Fˣ) : F)) *
            (v (Sum.inl i) * v (Sum.inr i)) := by ring
    _ = v (Sum.inl i) * v (Sum.inr i) := by rw [hd, one_mul]

theorem diagGen_mem_statedOmega (hm : 4 ≤ m) (h2 : (2 : F) = 0) (t : Fˣ) (i : Fin 3)
    {q : ℕ} (hodd : Odd q) (ht : orderOf t = q) :
    diagGLPlusHom m F (Pi.mulSingle (threeToFinOrth hm i) t) ∈
      StatedOmega (StatedQuadPlus m F) := by
  rw [mem_statedOmega_iff_mem_elementaryGroup (coe_quadPlus m F)
    (commutator_orthogonalGroup_quadPlus (K := F) (n := m) (by omega))]
  refine mem_elementaryGroup_quadPlus_of_odd_pow h2 (by omega) ?_ hodd ?_
  · rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro v
    rw [toLinEquiv_apply]
    exact quadPlus_mulVec_diagGLPlus _ v
  · rw [← map_pow (toLinEquiv (Fin m ⊕ Fin m) F), ← map_pow (diagGLPlusHom m F),
      ← Pi.mulSingle_pow, ← ht, pow_orderOf_eq_one, Pi.mulSingle_one]
    simp

@[expose] noncomputable def diagGenOmega (t : Fˣ) (hm : 4 ≤ m) (h2 : (2 : F) = 0) (i : Fin 3)
    {q : ℕ} (hodd : Odd q) (ht : orderOf t = q) :
    StatedOmega (StatedQuadPlus m F) :=
  ⟨diagGLPlusHom m F (Pi.mulSingle (threeToFinOrth hm i) t),
    diagGen_mem_statedOmega hm h2 t i hodd ht⟩

@[simp]
theorem coe_diagGenOmega (t : Fˣ) (hm : 4 ≤ m) (h2 : (2 : F) = 0) (i : Fin 3)
    {q : ℕ} (hodd : Odd q) (ht : orderOf t = q) :
    ((diagGenOmega t hm h2 i hodd ht : StatedOmega (StatedQuadPlus m F)) :
        GL (Fin m ⊕ Fin m) F) =
      diagGLPlusHom m F (Pi.mulSingle (threeToFinOrth hm i) t) :=
  rfl

theorem orderOf_diagGenOmega (t : Fˣ) (hm : 4 ≤ m) (h2 : (2 : F) = 0) (i : Fin 3)
    {q : ℕ} (hodd : Odd q) (ht : orderOf t = q) :
    orderOf (diagGenOmega t hm h2 i hodd ht) = q := by
  rw [← orderOf_injective (Subgroup.subtype (StatedOmega (StatedQuadPlus m F)))
    Subtype.coe_injective]
  change orderOf (diagGLPlusHom m F (Pi.mulSingle (threeToFinOrth hm i) t)) = q
  rw [orderOf_injective (diagGLPlusHom m F) (diagGLPlusHom_injective m F),
    orderOf_piMulSingle, ht]

theorem commute_diagGenOmega (t : Fˣ) (hm : 4 ≤ m) (h2 : (2 : F) = 0) (i j : Fin 3)
    {q : ℕ} (hodd : Odd q) (ht : orderOf t = q) :
    Commute (diagGenOmega t hm h2 i hodd ht) (diagGenOmega t hm h2 j hodd ht) := by
  rw [commute_iff_eq]
  apply Subtype.ext
  change diagGLPlusHom m F (Pi.mulSingle (threeToFinOrth hm i) t) *
      diagGLPlusHom m F (Pi.mulSingle (threeToFinOrth hm j) t) =
    diagGLPlusHom m F (Pi.mulSingle (threeToFinOrth hm j) t) *
      diagGLPlusHom m F (Pi.mulSingle (threeToFinOrth hm i) t)
  rw [← map_mul, ← map_mul]
  congr 1
  by_cases hij : i = j
  · subst hij
    rfl
  · have hne : threeToFinOrth hm i ≠ threeToFinOrth hm j := fun h =>
      hij (threeToFinOrth_injective hm h)
    exact (Pi.mulSingle_commute (f := fun _ : Fin m => Fˣ) hne t t).eq

@[expose] noncomputable def omegaActPlus (m : ℕ) (F : Type) [Field F] :
    StatedOmega (StatedQuadPlus m F) →*
      ((Fin m ⊕ Fin m → F) ≃ₗ[F] (Fin m ⊕ Fin m → F)) :=
  (toLinEquiv (Fin m ⊕ Fin m) F).toMonoidHom.comp
    (Subgroup.subtype (StatedOmega (StatedQuadPlus m F)))

theorem omegaActPlus_apply (A : StatedOmega (StatedQuadPlus m F))
    (v : Fin m ⊕ Fin m → F) :
    omegaActPlus m F A v =
      ((A : GL (Fin m ⊕ Fin m) F) :
        Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F) *ᵥ v :=
  rfl

theorem omegaAct_diagGen_zpow_single (t : Fˣ) (hm : 4 ≤ m) (h2 : (2 : F) = 0) (i : Fin 3)
    {q : ℕ} (hodd : Odd q) (ht : orderOf t = q) (a : ℤ) (k : Fin m ⊕ Fin m) :
    omegaActPlus m F ((diagGenOmega t hm h2 i hodd ht) ^ a) (Pi.single k 1) =
      Pi.single k
        (((pairedDiagHom m F (Pi.mulSingle (threeToFinOrth hm i) (t ^ a))) k : Fˣ) : F) := by
  rw [omegaActPlus_apply, Subgroup.coe_zpow, coe_diagGenOmega,
    ← map_zpow (diagGLPlusHom m F), ← Pi.mulSingle_zpow, coe_diagGLPlusHom]
  ext j
  rw [Matrix.mulVec_diagonal]
  by_cases hjk : j = k
  · subst hjk
    simp
  · simp [Pi.single_eq_of_ne hjk]

theorem omegaAct_diagGen_zpow_single_self (t : Fˣ) (hm : 4 ≤ m) (h2 : (2 : F) = 0)
    (i : Fin 3) {q : ℕ} (hodd : Odd q) (ht : orderOf t = q) (a : ℤ) :
    omegaActPlus m F ((diagGenOmega t hm h2 i hodd ht) ^ a)
        (Pi.single (Sum.inl (threeToFinOrth hm i)) 1) =
      Pi.single (Sum.inl (threeToFinOrth hm i)) (((t ^ a : Fˣ) : F)) := by
  rw [omegaAct_diagGen_zpow_single, pairedDiagHom_inl, Pi.mulSingle_eq_same]

theorem omegaAct_diagGen_single_of_ne (t : Fˣ) (hm : 4 ≤ m) (h2 : (2 : F) = 0)
    {i j : Fin 3} (hij : i ≠ j) {q : ℕ} (hodd : Odd q) (ht : orderOf t = q) :
    omegaActPlus m F (diagGenOmega t hm h2 i hodd ht)
        (Pi.single (Sum.inl (threeToFinOrth hm j)) 1) =
      Pi.single (Sum.inl (threeToFinOrth hm j)) 1 := by
  have hne : threeToFinOrth hm i ≠ threeToFinOrth hm j := fun h =>
    hij (threeToFinOrth_injective hm h)
  have h := omegaAct_diagGen_zpow_single (t := t) (hm := hm) (h2 := h2) (i := i)
    (hodd := hodd) (ht := ht) (a := 1) (k := Sum.inl (threeToFinOrth hm j))
  simpa [hne, Ne.symm hne] using h

theorem dvd_of_diagGen_zpow_fixes (t : Fˣ) (hm : 4 ≤ m) (h2 : (2 : F) = 0) (i : Fin 3)
    {q : ℕ} (hodd : Odd q) (ht : orderOf t = q) {a : ℤ}
    (h : omegaActPlus m F ((diagGenOmega t hm h2 i hodd ht) ^ a)
        (Pi.single (Sum.inl (threeToFinOrth hm i)) 1) =
      Pi.single (Sum.inl (threeToFinOrth hm i)) 1) :
    (q : ℤ) ∣ a := by
  rw [omegaAct_diagGen_zpow_single_self] at h
  have hval : ((t ^ a : Fˣ) : F) = 1 := by
    have := congrFun h (Sum.inl (threeToFinOrth hm i))
    simpa using this
  have hta : t ^ a = 1 := Units.ext hval
  rw [← ht, orderOf_dvd_iff_zpow_eq_one]
  exact hta

@[expose] noncomputable def diagTorusOrth (m : ℕ) (F : Type) [Field F] :
    Subgroup (StatedOmega (StatedQuadPlus m F)) :=
  (diagTorusPlus m F).subgroupOf (StatedOmega (StatedQuadPlus m F))

theorem diagGenOmega_mem_diagTorusOrth (t : Fˣ) (hm : 4 ≤ m) (h2 : (2 : F) = 0) (i : Fin 3)
    {q : ℕ} (hodd : Odd q) (ht : orderOf t = q) :
    diagGenOmega t hm h2 i hodd ht ∈ diagTorusOrth m F := by
  rw [diagTorusOrth, Subgroup.mem_subgroupOf]
  exact ⟨Pi.mulSingle (threeToFinOrth hm i) t, rfl⟩

theorem three_le_pRank_diagTorus_orthogonal {m : ℕ} (hm : 4 ≤ m) {F : Type} [Field F]
    [Finite F] [CharP F 2] {q : ℕ} (hq : q.Prime) (hdvd : q ∣ Nat.card F - 1) :
    3 ≤ CFSG.Open.pRank q (diagTorusOrth m F) := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hqne : q ≠ 2 := by
    rintro rfl
    letI : Fintype F := Fintype.ofFinite F
    have heven : Even (Nat.card F) := by
      rw [Nat.card_eq_fintype_card]
      exact Nat.even_iff.mpr
        (FiniteField.even_card_iff_char_two.mp (ringChar.eq F 2))
    have hodd : Odd (Nat.card F - 1) := by
      obtain ⟨k, hk⟩ := heven
      have hpos : 0 < Nat.card F := Nat.card_pos
      refine ⟨k - 1, ?_⟩
      omega
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)
  have hoddq : Odd q := hq.odd_of_ne_two hqne
  have hdvd' : q ∣ Nat.card Fˣ := by
    rw [Nat.card_units]
    exact hdvd
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' q hdvd'
  obtain ⟨T, hTle, -, -, hTrank⟩ :=
    CFSG.exists_elemAbelian_of_commuting_moving (F := F) (X := Fin m ⊕ Fin m → F)
      (G := StatedOmega (StatedQuadPlus m F)) (ι := Fin 3) (r := q) hq
      (fun i : Fin 3 => diagGenOmega t hm h2 i hoddq ht)
      (fun i : Fin 3 => Pi.single (Sum.inl (threeToFinOrth hm i)) 1)
      (omegaActPlus m F)
      (fun i => diagGenOmega_mem_diagTorusOrth t hm h2 i hoddq ht)
      (fun i => orderOf_diagGenOmega t hm h2 i hoddq ht)
      (fun i j => commute_diagGenOmega t hm h2 i j hoddq ht)
      (fun i a h => dvd_of_diagGen_zpow_fixes t hm h2 i hoddq ht h)
      (fun i j hij => omegaAct_diagGen_single_of_ne t hm h2 hij hoddq ht)
  have hcard : Nat.card (Fin 3) = 3 := by simp
  rw [hcard] at hTrank
  exact hTrank.trans (CFSG.SectionRank.pRank_mono hq.one_lt hTle)

end CFSG.ClassicalGroups.Orthogonal

end
