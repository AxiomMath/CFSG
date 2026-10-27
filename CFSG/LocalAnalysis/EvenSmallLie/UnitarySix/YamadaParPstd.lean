module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaEndL44
public import CFSG.Fischer.F4

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaPar

open Matrix Subgroup CFSG.EvenSmallLie.UnitarySix.YamadaEnd
open scoped MatrixGroups

variable {F : Type} [Field F]

@[expose] def lu (a b f c d e : F) : SL(4, F) :=
  SpecialLinearGroup.transvection (show (1 : Fin 4) ≠ 0 by decide) a *
    SpecialLinearGroup.transvection (show (2 : Fin 4) ≠ 0 by decide) b *
    SpecialLinearGroup.transvection (show (3 : Fin 4) ≠ 0 by decide) c *
    (SpecialLinearGroup.transvection (show (2 : Fin 4) ≠ 1 by decide) f *
      SpecialLinearGroup.transvection (show (3 : Fin 4) ≠ 1 by decide) d) *
    SpecialLinearGroup.transvection (show (3 : Fin 4) ≠ 2 by decide) e

theorem tv_apply {i j : Fin 4} (h : i ≠ j) (c : F) (a b : Fin 4) :
    (SpecialLinearGroup.transvection h c : SL(4, F)) a b =
      (if a = b then 1 else 0) + (if a = i ∧ b = j then c else 0) := by
  rw [SpecialLinearGroup.transvection_coe, Matrix.add_apply, one_apply, single_apply]
  congr 1
  by_cases h1 : a = i <;> by_cases h2 : b = j <;> simp [h1, h2, eq_comm] <;> intro h3 <;>
    exact absurd h3.symm ‹_›

theorem coe_lu (a b f c d e : F) : ((lu a b f c d e : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) =
    !![1, 0, 0, 0; a, 1, 0, 0; b, f, 1, 0; c, d, e, 1] := by
  ext i j
  simp only [lu]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four, tv_apply]

theorem lu_mem_pstd (a b f c d e : F) : lu a b f c d e ∈ pstd F := by
  have hg : ∀ (i j : Fin 4) (h : i ≠ j) (c : F), j < i →
      SpecialLinearGroup.transvection h c ∈ pstd F :=
    fun i j h c hji => subset_closure ⟨i, j, h, c, hji, rfl⟩
  exact mul_mem (mul_mem (mul_mem (mul_mem (hg 1 0 _ a (by decide)) (hg 2 0 _ b (by decide)))
    (hg 3 0 _ c (by decide))) (mul_mem (hg 2 1 _ f (by decide)) (hg 3 1 _ d (by decide))))
    (hg 3 2 _ e (by decide))

@[expose] def IsLowerUni (x : Matrix (Fin 4) (Fin 4) F) : Prop :=
  (∀ i j : Fin 4, i < j → x i j = 0) ∧ ∀ i : Fin 4, x i i = 1

theorem eq_lu_of_isLowerUni {y : SL(4, F)} (hy : IsLowerUni (y : Matrix (Fin 4) (Fin 4) F)) :
    y = lu (y 1 0) (y 2 0) (y 2 1) (y 3 0) (y 3 1) (y 3 2) := by
  apply Subtype.ext
  rw [coe_lu]
  obtain ⟨h1, h2⟩ := hy
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h2] <;> exact h1 _ _ (by decide)

theorem mem_pstd_iff {y : SL(4, F)} : y ∈ pstd F ↔ IsLowerUni (y : Matrix (Fin 4) (Fin 4) F) := by
  refine ⟨fun hy => lowerUni_of_mem_pstd F hy, fun hy => ?_⟩
  rw [eq_lu_of_isLowerUni hy]
  exact lu_mem_pstd _ _ _ _ _ _

theorem isLowerUni_lu (a b f c d e : F) :
    IsLowerUni ((lu a b f c d e : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) :=
  mem_pstd_iff.mp (lu_mem_pstd a b f c d e)

theorem lu_injective {a b f c d e a' b' f' c' d' e' : F}
    (h : lu a b f c d e = lu a' b' f' c' d' e') :
    a = a' ∧ b = b' ∧ f = f' ∧ c = c' ∧ d = d' ∧ e = e' := by
  have h' := congrArg (fun x : SL(4, F) => (x : Matrix (Fin 4) (Fin 4) F)) h
  simp only [coe_lu] at h'
  exact ⟨congrFun (congrFun h' 1) 0, congrFun (congrFun h' 2) 0, congrFun (congrFun h' 2) 1,
    congrFun (congrFun h' 3) 0, congrFun (congrFun h' 3) 1, congrFun (congrFun h' 3) 2⟩

theorem mem_conjR_pstd_iff {π : Equiv.Perm (Fin 4)} {g : SL(4, F)}
    (hg : (g : Matrix (Fin 4) (Fin 4) F) = π.permMatrix F) (x : SL(4, F)) :
    x ∈ conjR (pstd F) g ↔ (∀ i j : Fin 4, i < j → x (π i) (π j) = 0) ∧
      ∀ i : Fin 4, x (π i) (π i) = 1 := by
  rw [mem_conjR, mem_pstd_iff, IsLowerUni]
  simp only [conj_apply_of_coe_eq_permMatrix F hg]

theorem lu_apply_entries (a b f c d e : F) :
    (lu a b f c d e : SL(4, F)) 1 0 = a ∧ (lu a b f c d e : SL(4, F)) 2 0 = b ∧
      (lu a b f c d e : SL(4, F)) 2 1 = f ∧ (lu a b f c d e : SL(4, F)) 3 0 = c ∧
      (lu a b f c d e : SL(4, F)) 3 1 = d ∧ (lu a b f c d e : SL(4, F)) 3 2 = e := by
  simp [coe_lu]

section CharTwo

variable [CharP F 2]

theorem coe_sY_one : ((sY F 1 : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) =
    (Equiv.swap 1 2 : Equiv.Perm (Fin 4)).permMatrix F := coe_sY F 1

theorem lu_mem_conjR_u₀ (a b f c d e : F) :
    lu a b f c d e ∈ conjR (pstd F) (sY F 0 * sY F 2) ↔ a = 0 ∧ e = 0 := by
  rw [mem_conjR_pstd_iff (coe_sY_zero_mul_sY_two F)]
  constructor
  · rintro ⟨h1, -⟩
    have h01 := h1 0 1 (by decide)
    have h23 := h1 2 3 (by decide)
    simp [coe_lu, Equiv.Perm.mul_apply, Equiv.swap_apply_def] at h01 h23
    exact ⟨h01, h23⟩
  · rintro ⟨rfl, rfl⟩
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · fin_cases i <;> fin_cases j <;>
        simp [coe_lu, Equiv.Perm.mul_apply, Equiv.swap_apply_def] at hij ⊢
    · fin_cases i <;> simp [coe_lu, Equiv.Perm.mul_apply, Equiv.swap_apply_def]

theorem lu_mem_conjR_v₀ (a b f c d e : F) :
    lu a b f c d e ∈ conjR (pstd F) (sY F 1) ↔ f = 0 := by
  rw [mem_conjR_pstd_iff coe_sY_one]
  constructor
  · rintro ⟨h1, -⟩
    have h12 := h1 1 2 (by decide)
    simpa [coe_lu, Equiv.swap_apply_def] using h12
  · rintro rfl
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · fin_cases i <;> fin_cases j <;> simp [coe_lu, Equiv.swap_apply_def] at hij ⊢
    · fin_cases i <;> simp [coe_lu, Equiv.swap_apply_def]

@[expose] noncomputable def pstdU₀Equiv :
    ↥(pstd F ⊓ conjR (pstd F) (sY F 0 * sY F 2)) ≃ F × F × F × F where
  toFun y := ((y : SL(4, F)) 2 0, (y : SL(4, F)) 2 1, (y : SL(4, F)) 3 0, (y : SL(4, F)) 3 1)
  invFun p := ⟨lu 0 p.1 p.2.1 p.2.2.1 p.2.2.2 0,
    ⟨lu_mem_pstd _ _ _ _ _ _, (lu_mem_conjR_u₀ _ _ _ _ _ _).mpr ⟨rfl, rfl⟩⟩⟩
  left_inv y := by
    obtain ⟨hy₁, hy₂⟩ := Subgroup.mem_inf.mp y.2
    have hy := eq_lu_of_isLowerUni (mem_pstd_iff.mp hy₁)
    have h0 := hy₂
    rw [hy, lu_mem_conjR_u₀] at h0
    apply Subtype.ext
    change lu 0 _ _ _ _ 0 = (y : SL(4, F))
    conv_rhs => rw [hy, h0.1, h0.2]
  right_inv p := by
    obtain ⟨-, h2, h3, h4, h5, -⟩ := lu_apply_entries (0 : F) p.1 p.2.1 p.2.2.1 p.2.2.2 0
    simp only [h2, h3, h4, h5]

@[expose] noncomputable def pstdV₀Equiv :
    ↥(pstd F ⊓ conjR (pstd F) (sY F 1)) ≃ F × F × F × F × F where
  toFun y := ((y : SL(4, F)) 1 0, (y : SL(4, F)) 2 0, (y : SL(4, F)) 3 0, (y : SL(4, F)) 3 1,
    (y : SL(4, F)) 3 2)
  invFun p := ⟨lu p.1 p.2.1 0 p.2.2.1 p.2.2.2.1 p.2.2.2.2,
    ⟨lu_mem_pstd _ _ _ _ _ _, (lu_mem_conjR_v₀ _ _ _ _ _ _).mpr rfl⟩⟩
  left_inv y := by
    obtain ⟨hy₁, hy₂⟩ := Subgroup.mem_inf.mp y.2
    have hy := eq_lu_of_isLowerUni (mem_pstd_iff.mp hy₁)
    have h0 := hy₂
    rw [hy, lu_mem_conjR_v₀] at h0
    apply Subtype.ext
    change lu _ _ 0 _ _ _ = (y : SL(4, F))
    conv_rhs => rw [hy, h0]
  right_inv p := by
    obtain ⟨h1, h2, -, h4, h5, h6⟩ := lu_apply_entries p.1 p.2.1 (0 : F) p.2.2.1 p.2.2.2.1
      p.2.2.2.2
    simp only [h1, h2, h4, h5, h6]

theorem card_pstd_inf_u₀ [Finite F] :
    Nat.card ↥(pstd F ⊓ conjR (pstd F) (sY F 0 * sY F 2)) = Nat.card F ^ 4 := by
  rw [Nat.card_congr pstdU₀Equiv]
  simp only [Nat.card_prod]
  ring

theorem card_pstd_inf_v₀ [Finite F] :
    Nat.card ↥(pstd F ⊓ conjR (pstd F) (sY F 1)) = Nat.card F ^ 5 := by
  rw [Nat.card_congr pstdV₀Equiv]
  simp only [Nat.card_prod]
  ring

end CharTwo

@[expose] def SigFix {R : Type*} [CommRing R] (a b f c : R) : Prop :=
  (a ^ 2) ^ 2 = a ∧ (b ^ 2 + a ^ 2 * f ^ 2) ^ 2 + (a ^ 2) ^ 2 * f ^ 2 = b ∧ f ^ 2 = f ∧
    c ^ 2 + a ^ 2 * (b ^ 2 + a ^ 2 * f ^ 2) ^ 2 + (a ^ 2) ^ 2 * b ^ 2 +
      (a ^ 2) ^ 2 * a ^ 2 * f ^ 2 = c

theorem sigFix_map {R R' : Type*} [CommRing R] [CommRing R'] (e : R ≃+* R') (a b f c : R) :
    SigFix (e a) (e b) (e f) (e c) ↔ SigFix a b f c := by
  simp only [SigFix, ← map_pow, ← map_mul, ← map_add, e.injective.eq_iff]

section Sigma

variable [CharP F 2] [Finite F]

theorem sigmaSL_lu (a b f c d e : F) :
    sigmaSL F (lu a b f c d e) = lu (e ^ 2) (d ^ 2 + e ^ 2 * f ^ 2) (f ^ 2)
      (c ^ 2 + a ^ 2 * d ^ 2 + e ^ 2 * b ^ 2 + e ^ 2 * a ^ 2 * f ^ 2) (b ^ 2 + a ^ 2 * f ^ 2)
      (a ^ 2) := by
  apply Subtype.ext
  rw [coe_lu]
  simp only [lu, map_mul, sigmaSL_transvection]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four, tv_apply, Fin.rev] <;>
    ring

theorem lu_mem_msigma_iff (a b f c d e : F) :
    lu a b f c d e ∈ msigma F ↔ d = b ^ 2 + a ^ 2 * f ^ 2 ∧ e = a ^ 2 ∧ SigFix a b f c := by
  change sigmaSL F (lu a b f c d e) = lu a b f c d e ↔ _
  rw [sigmaSL_lu]
  constructor
  · intro h
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := lu_injective h
    subst h5 h6
    exact ⟨rfl, rfl, h1, h2, h3, h4⟩
  · rintro ⟨rfl, rfl, h1, h2, h3, h4⟩
    congr 1

@[expose] noncomputable def sigFixEquiv (X : Subgroup SL(4, F)) (R : F → F → F → F → Prop)
    (hX : ∀ a b f c, SigFix a b f c → (lu a b f c (b ^ 2 + a ^ 2 * f ^ 2) (a ^ 2) ∈ X ↔
      R a b f c)) :
    ↥(msigma F ⊓ pstd F ⊓ X) ≃
      {q : F × F × F × F // SigFix q.1 q.2.1 q.2.2.1 q.2.2.2 ∧ R q.1 q.2.1 q.2.2.1 q.2.2.2} where
  toFun y := ⟨((y : SL(4, F)) 1 0, (y : SL(4, F)) 2 0, (y : SL(4, F)) 2 1, (y : SL(4, F)) 3 0),
    by
      obtain ⟨hσP, hXy⟩ := Subgroup.mem_inf.mp y.2
      obtain ⟨hσ, hP⟩ := Subgroup.mem_inf.mp hσP
      have hy := eq_lu_of_isLowerUni (mem_pstd_iff.mp hP)
      rw [hy, lu_mem_msigma_iff] at hσ
      obtain ⟨hd, he, hS⟩ := hσ
      refine ⟨hS, (hX _ _ _ _ hS).mp ?_⟩
      rw [← hd, ← he, ← hy]
      exact hXy⟩
  invFun q := ⟨lu q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2
      (q.1.2.1 ^ 2 + q.1.1 ^ 2 * q.1.2.2.1 ^ 2) (q.1.1 ^ 2),
    ⟨⟨(lu_mem_msigma_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, q.2.1⟩, lu_mem_pstd _ _ _ _ _ _⟩,
      (hX _ _ _ _ q.2.1).mpr q.2.2⟩⟩
  left_inv y := by
    obtain ⟨hσP, -⟩ := Subgroup.mem_inf.mp y.2
    obtain ⟨hσ, hP⟩ := Subgroup.mem_inf.mp hσP
    have hy := eq_lu_of_isLowerUni (mem_pstd_iff.mp hP)
    have h0 := hσ
    rw [hy, lu_mem_msigma_iff] at h0
    apply Subtype.ext
    refine Eq.trans ?_ hy.symm
    dsimp only
    rw [h0.1, h0.2.1]
  right_inv q := by
    obtain ⟨h1, h2, h3, h4, -, -⟩ := lu_apply_entries q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2
      (q.1.2.1 ^ 2 + q.1.1 ^ 2 * q.1.2.2.1 ^ 2) (q.1.1 ^ 2)
    apply Subtype.ext
    simp only [h1, h2, h3, h4]

end Sigma

section Count

variable [CharP F 2] [Finite F]

theorem natCard_F4 : Nat.card CFSG.Fischer.F4 = 4 := by
  rw [Nat.card_eq_fintype_card]; rfl

theorem exists_ringEquiv_F4 (hF : Nat.card F = 4) : Nonempty (F ≃+* CFSG.Fischer.F4) := by
  have : Fintype F := Fintype.ofFinite F
  exact ⟨FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hF, natCard_F4])⟩

theorem card_sigFix_congr (hF : Nat.card F = 4) (R : F → F → F → F → Prop)
    (R' : CFSG.Fischer.F4 → CFSG.Fischer.F4 → CFSG.Fischer.F4 → CFSG.Fischer.F4 → Prop)
    (hR : ∀ e : F ≃+* CFSG.Fischer.F4, ∀ a b f c, R' (e a) (e b) (e f) (e c) ↔ R a b f c) :
    Nat.card {q : F × F × F × F // SigFix q.1 q.2.1 q.2.2.1 q.2.2.2 ∧ R q.1 q.2.1 q.2.2.1 q.2.2.2} =
      Nat.card {q : CFSG.Fischer.F4 × CFSG.Fischer.F4 × CFSG.Fischer.F4 × CFSG.Fischer.F4 //
        SigFix q.1 q.2.1 q.2.2.1 q.2.2.2 ∧ R' q.1 q.2.1 q.2.2.1 q.2.2.2} := by
  obtain ⟨e⟩ := exists_ringEquiv_F4 hF
  refine Nat.card_congr (Equiv.subtypeEquiv (e.toEquiv.prodCongr (e.toEquiv.prodCongr
    (e.toEquiv.prodCongr e.toEquiv))) fun q => ?_)
  simp only [Equiv.prodCongr_apply, Prod.map, RingEquiv.toEquiv_eq_coe, EquivLike.coe_coe]
  rw [sigFix_map, hR]

theorem f4_eq_iff (x y : CFSG.Fischer.F4) : x = y ↔ x.code = y.code :=
  ⟨fun h => h ▸ rfl, fun h => by cases x; cases y; cases h; rfl⟩

@[expose] def SigFixC (a b f c : CFSG.Fischer.F4) : Prop :=
  ((a ^ 2) ^ 2).code = a.code ∧
    ((b ^ 2 + a ^ 2 * f ^ 2) ^ 2 + (a ^ 2) ^ 2 * f ^ 2).code = b.code ∧
    (f ^ 2).code = f.code ∧
    (c ^ 2 + a ^ 2 * (b ^ 2 + a ^ 2 * f ^ 2) ^ 2 + (a ^ 2) ^ 2 * b ^ 2 +
      (a ^ 2) ^ 2 * a ^ 2 * f ^ 2).code = c.code

instance (a b f c : CFSG.Fischer.F4) : Decidable (SigFixC a b f c) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

theorem sigFix_iff_C (a b f c : CFSG.Fischer.F4) : SigFix a b f c ↔ SigFixC a b f c := by
  simp only [SigFix, SigFixC, f4_eq_iff]

theorem card_sigFix_F4 (R R' : CFSG.Fischer.F4 → CFSG.Fischer.F4 → CFSG.Fischer.F4 →
      CFSG.Fischer.F4 → Prop) [∀ a b f c, Decidable (R' a b f c)]
    (hR : ∀ a b f c, R a b f c ↔ R' a b f c) :
    Nat.card {q : CFSG.Fischer.F4 × CFSG.Fischer.F4 × CFSG.Fischer.F4 × CFSG.Fischer.F4 //
        SigFix q.1 q.2.1 q.2.2.1 q.2.2.2 ∧ R q.1 q.2.1 q.2.2.1 q.2.2.2} =
      Fintype.card {q : CFSG.Fischer.F4 × CFSG.Fischer.F4 × CFSG.Fischer.F4 × CFSG.Fischer.F4 //
        SigFixC q.1 q.2.1 q.2.2.1 q.2.2.2 ∧ R' q.1 q.2.1 q.2.2.1 q.2.2.2} := by
  rw [← Nat.card_eq_fintype_card]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun q => by rw [sigFix_iff_C, hR])

theorem card_msigma_inf_pstd (hF : Nat.card F = 4) : Nat.card ↥(msigma F ⊓ pstd F) = 2 ^ 6 := by
  have h := Nat.card_congr (sigFixEquiv (F := F) ⊤ (fun _ _ _ _ => True)
    (fun _ _ _ _ _ => iff_of_true (mem_top _) trivial))
  rw [inf_top_eq] at h
  rw [h]
  refine (card_sigFix_congr hF (fun _ _ _ _ => True) (fun _ _ _ _ => True)
    (fun _ _ _ _ _ => Iff.rfl)).trans ((card_sigFix_F4 _ (fun _ _ _ _ => True)
    (fun _ _ _ _ => Iff.rfl)).trans ?_)
  decide

theorem card_msigma_inf_u₀ (hF : Nat.card F = 4) :
    Nat.card ↥(msigma F ⊓ pstd F ⊓ conjR (pstd F) (sY F 0 * sY F 2)) = 2 ^ 4 := by
  rw [Nat.card_congr (sigFixEquiv (F := F) _ (fun a _ _ _ => a = 0) (fun a b f c _ => by
      rw [lu_mem_conjR_u₀]
      exact ⟨fun h => h.1, fun h => ⟨h, by rw [h]; ring⟩⟩))]
  refine (card_sigFix_congr hF (fun a _ _ _ => a = 0) (fun a _ _ _ => a = 0)
    (fun e a _ _ _ => by simp)).trans ((card_sigFix_F4 _
    (fun a _ _ _ => a.code = (0 : CFSG.Fischer.F4).code) (fun a _ _ _ => f4_eq_iff a 0)).trans ?_)
  decide

theorem card_msigma_inf_v₀ (hF : Nat.card F = 4) :
    Nat.card ↥(msigma F ⊓ pstd F ⊓ conjR (pstd F) (sY F 1)) = 2 ^ 5 := by
  rw [Nat.card_congr (sigFixEquiv (F := F) _ (fun _ _ f _ => f = 0) (fun a b f c _ =>
      lu_mem_conjR_v₀ _ _ _ _ _ _))]
  refine (card_sigFix_congr hF (fun _ _ f _ => f = 0) (fun _ _ f _ => f = 0)
    (fun e _ _ f _ => by simp)).trans ((card_sigFix_F4 _
    (fun _ _ f _ => f.code = (0 : CFSG.Fischer.F4).code) (fun _ _ f _ => f4_eq_iff f 0)).trans ?_)
  decide

end Count

end CFSG.EvenSmallLie.UnitarySix.YamadaPar
