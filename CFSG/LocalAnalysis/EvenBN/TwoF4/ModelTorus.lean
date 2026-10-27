module

public import CFSG.LocalAnalysis.EvenBN.TwoF4.Model

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.TwoF4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution
open CFSG.LieType.Ree.LargeReeCover (torusPair torusWeight torusWeight_apply torusExp0 torusExp1
  f4i twoRoot fourRoot isRoot_twoRoot isRoot_fourRoot torusPair_conj_pinnedX)
open CFSG.LieType.Chevalley.RootOps (orbitCertRoot)

@[expose] def SigmaCond (α β : Fin F4.tag.rank → ℤ) : Prop :=
  F4.cartanPair (f4i 0) β = F4.cartanPair (f4i 3) α ∧
    F4.cartanPair (f4i 3) β = 2 * F4.cartanPair (f4i 0) α ∧
    F4.cartanPair (f4i 1) β = F4.cartanPair (f4i 2) α ∧
    F4.cartanPair (f4i 2) β = 2 * F4.cartanPair (f4i 1) α

@[expose] def SqSigmaCond (α β : Fin F4.tag.rank → ℤ) : Prop :=
  F4.cartanPair (f4i 0) β = 2 * F4.cartanPair (f4i 0) α + F4.cartanPair (f4i 3) α ∧
    F4.cartanPair (f4i 3) β = 2 * F4.cartanPair (f4i 3) α + 2 * F4.cartanPair (f4i 0) α ∧
    F4.cartanPair (f4i 1) β = 2 * F4.cartanPair (f4i 1) α + F4.cartanPair (f4i 2) α ∧
    F4.cartanPair (f4i 2) β = 2 * F4.cartanPair (f4i 2) α + 2 * F4.cartanPair (f4i 1) α

instance (α β : Fin F4.tag.rank → ℤ) : Decidable (SigmaCond α β) := by
  unfold SigmaCond
  infer_instance

instance (α β : Fin F4.tag.rank → ℤ) : Decidable (SqSigmaCond α β) := by
  unfold SqSigmaCond
  infer_instance

theorem block_cartan_check :
    (∀ t : Fin 4, SigmaCond (twoRoot t 0) (twoRoot t 1)) ∧
      ∀ f : Fin 4, SigmaCond (fourRoot f 0) (fourRoot f 1) ∧
        SqSigmaCond (fourRoot f 0) (fourRoot f 3) ∧ SigmaCond (fourRoot f 2) (fourRoot f 3) ∧
          fourRoot f 2 = fourRoot f 0 + fourRoot f 1 := by
  decide +kernel

namespace Idx

@[expose] def leadRoot (i : Idx) : Fin F4.tag.rank → ℤ :=
  if i.isSz then fourRoot i.fourIdx 0
  else if i.isCenter then fourRoot i.fourIdx 2 else twoRoot i.twoIdx 0

theorem isRoot_leadRoot (i : Idx) :
    IsRoot F4.tag i.leadRoot := by
  unfold leadRoot
  split_ifs
  · exact isRoot_fourRoot _ _
  · exact isRoot_fourRoot _ _
  · exact isRoot_twoRoot _ _

end Idx

theorem torusExp_leadRoot (θ : ℤ) :
    (torusExp0 θ Idx.i1.leadRoot = -θ ∧ torusExp1 θ Idx.i1.leadRoot = 2 * θ - 1) ∧
    (torusExp0 θ Idx.i2.leadRoot = -θ - 1 ∧ torusExp1 θ Idx.i2.leadRoot = 1) ∧
    (torusExp0 θ Idx.i3.leadRoot = 2 * θ ∧ torusExp1 θ Idx.i3.leadRoot = -θ) ∧
    (torusExp0 θ Idx.i4.leadRoot = θ ∧ torusExp1 θ Idx.i4.leadRoot = θ - 1) ∧
    (torusExp0 θ Idx.i5.leadRoot = 1 - θ ∧ torusExp1 θ Idx.i5.leadRoot = 0) ∧
    (torusExp0 θ Idx.i6.leadRoot = θ - 1 ∧ torusExp1 θ Idx.i6.leadRoot = 1 - θ) ∧
    (torusExp0 θ Idx.i7.leadRoot = -1 ∧ torusExp1 θ Idx.i7.leadRoot = θ) ∧
    (torusExp0 θ Idx.i8.leadRoot = θ + 1 ∧ torusExp1 θ Idx.i8.leadRoot = -θ) ∧
    (torusExp0 θ Idx.i9.leadRoot = 1 ∧ torusExp1 θ Idx.i9.leadRoot = θ - 1) ∧
    (torusExp0 θ Idx.i10.leadRoot = 0 ∧ torusExp1 θ Idx.i10.leadRoot = 1 - θ) ∧
    (torusExp0 θ Idx.i11.leadRoot = -θ ∧ torusExp1 θ Idx.i11.leadRoot = θ) ∧
    (torusExp0 θ Idx.i12.leadRoot = θ ∧ torusExp1 θ Idx.i12.leadRoot = 0) := by
  have h : (F4.cartanPair (f4i 0) Idx.i1.leadRoot = 0 ∧ F4.cartanPair (f4i 3) Idx.i1.leadRoot = -1 ∧
      F4.cartanPair (f4i 1) Idx.i1.leadRoot = -1 ∧ F4.cartanPair (f4i 2) Idx.i1.leadRoot = 2) ∧
    (F4.cartanPair (f4i 0) Idx.i2.leadRoot = -1 ∧ F4.cartanPair (f4i 3) Idx.i2.leadRoot = -1 ∧
      F4.cartanPair (f4i 1) Idx.i2.leadRoot = 1 ∧ F4.cartanPair (f4i 2) Idx.i2.leadRoot = 0) ∧
    (F4.cartanPair (f4i 0) Idx.i3.leadRoot = 0 ∧ F4.cartanPair (f4i 3) Idx.i3.leadRoot = 2 ∧
      F4.cartanPair (f4i 1) Idx.i3.leadRoot = 0 ∧ F4.cartanPair (f4i 2) Idx.i3.leadRoot = -1) ∧
    (F4.cartanPair (f4i 0) Idx.i4.leadRoot = 0 ∧ F4.cartanPair (f4i 3) Idx.i4.leadRoot = 1 ∧
      F4.cartanPair (f4i 1) Idx.i4.leadRoot = -1 ∧ F4.cartanPair (f4i 2) Idx.i4.leadRoot = 1) ∧
    (F4.cartanPair (f4i 0) Idx.i5.leadRoot = 1 ∧ F4.cartanPair (f4i 3) Idx.i5.leadRoot = -1 ∧
      F4.cartanPair (f4i 1) Idx.i5.leadRoot = 0 ∧ F4.cartanPair (f4i 2) Idx.i5.leadRoot = 0) ∧
    (F4.cartanPair (f4i 0) Idx.i6.leadRoot = -1 ∧ F4.cartanPair (f4i 3) Idx.i6.leadRoot = 1 ∧
      F4.cartanPair (f4i 1) Idx.i6.leadRoot = 1 ∧ F4.cartanPair (f4i 2) Idx.i6.leadRoot = -1) ∧
    (F4.cartanPair (f4i 0) Idx.i7.leadRoot = -1 ∧ F4.cartanPair (f4i 3) Idx.i7.leadRoot = 0 ∧
      F4.cartanPair (f4i 1) Idx.i7.leadRoot = 0 ∧ F4.cartanPair (f4i 2) Idx.i7.leadRoot = 1) ∧
    (F4.cartanPair (f4i 0) Idx.i8.leadRoot = 1 ∧ F4.cartanPair (f4i 3) Idx.i8.leadRoot = 1 ∧
      F4.cartanPair (f4i 1) Idx.i8.leadRoot = 0 ∧ F4.cartanPair (f4i 2) Idx.i8.leadRoot = -1) ∧
    (F4.cartanPair (f4i 0) Idx.i9.leadRoot = 1 ∧ F4.cartanPair (f4i 3) Idx.i9.leadRoot = 0 ∧
      F4.cartanPair (f4i 1) Idx.i9.leadRoot = -1 ∧ F4.cartanPair (f4i 2) Idx.i9.leadRoot = 1) ∧
    (F4.cartanPair (f4i 0) Idx.i10.leadRoot = 0 ∧ F4.cartanPair (f4i 3) Idx.i10.leadRoot = 0 ∧
      F4.cartanPair (f4i 1) Idx.i10.leadRoot = 1 ∧ F4.cartanPair (f4i 2) Idx.i10.leadRoot = -1) ∧
    (F4.cartanPair (f4i 0) Idx.i11.leadRoot = 0 ∧ F4.cartanPair (f4i 3) Idx.i11.leadRoot = -1 ∧
      F4.cartanPair (f4i 1) Idx.i11.leadRoot = 0 ∧ F4.cartanPair (f4i 2) Idx.i11.leadRoot = 1) ∧
    (F4.cartanPair (f4i 0) Idx.i12.leadRoot = 0 ∧ F4.cartanPair (f4i 3) Idx.i12.leadRoot = 1 ∧
      F4.cartanPair (f4i 1) Idx.i12.leadRoot = 0 ∧ F4.cartanPair (f4i 2) Idx.i12.leadRoot = 0) := by
    decide +kernel
  simp only [torusExp0, torusExp1]
  obtain ⟨⟨a1, b1, c1, d1⟩, ⟨a2, b2, c2, d2⟩, ⟨a3, b3, c3, d3⟩, ⟨a4, b4, c4, d4⟩,
    ⟨a5, b5, c5, d5⟩, ⟨a6, b6, c6, d6⟩, ⟨a7, b7, c7, d7⟩, ⟨a8, b8, c8, d8⟩, ⟨a9, b9, c9, d9⟩,
    ⟨a10, b10, c10, d10⟩, ⟨a11, b11, c11, d11⟩, ⟨a12, b12, c12, d12⟩⟩ := h
  rw [a1, b1, c1, d1, a2, b2, c2, d2, a3, b3, c3, d3, a4, b4, c4, d4, a5, b5, c5, d5, a6, b6, c6,
    d6, a7, b7, c7, d7, a8, b8, c8, d8, a9, b9, c9, d9, a10, b10, c10, d10, a11, b11, c11, d11, a12,
    b12, c12, d12]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩,
    ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> ring

theorem torusWeight_add {K : Type} [Field K] {a : ℕ} (β γ : Fin F4.tag.rank → ℤ) (t : Kˣ × Kˣ) :
    torusWeight a (β + γ) t = torusWeight a β t * torusWeight a γ t := by
  obtain ⟨u, v⟩ := t
  have hl : ∀ k, F4.cartanPair k (β + γ) = F4.cartanPair k β + F4.cartanPair k γ := fun k => by
    simp only [ReeTag.cartanPair, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  have e0 : torusExp0 (2 ^ a) (β + γ) = torusExp0 (2 ^ a) β + torusExp0 (2 ^ a) γ := by
    simp only [torusExp0, hl]
    ring
  have e1 : torusExp1 (2 ^ a) (β + γ) = torusExp1 (2 ^ a) β + torusExp1 (2 ^ a) γ := by
    simp only [torusExp1, hl]
    ring
  rw [torusWeight_apply, torusWeight_apply, torusWeight_apply, e0, e1, zpow_add, zpow_add,
    mul_mul_mul_comm]

theorem isCoprime_torusExp_leadRoot {a : ℕ} (i : Idx) :
    IsCoprime (torusExp0 (2 ^ a) i.leadRoot) ((2 : ℤ) ^ (2 * a + 1) - 1) ∨
      IsCoprime (torusExp1 (2 ^ a) i.leadRoot) ((2 : ℤ) ^ (2 * a + 1) - 1) := by
  have hq : (2 : ℤ) ^ (2 * a + 1) - 1 = 2 * (2 ^ a) ^ 2 - 1 := by
    rw [pow_succ, pow_mul']
    ring
  have hpos : 0 < height i.leadRoot := by
    unfold Idx.leadRoot
    split_ifs
    · exact (LargeReeCover.height_check.2 _).1
    · exact (LargeReeCover.height_check.2 _).1.trans (LargeReeCover.height_check.2 _).2.2.1
    · exact (LargeReeCover.height_check.1 _).1
  rw [hq]
  exact LargeReeCover.f4_torusExp_isCoprime _ i.isRoot_leadRoot hpos

section Characters

variable (K : Type) [Field K] (a : ℕ)

@[expose] def rootChar (i : Idx) : Kˣ × Kˣ →* Kˣ :=
  torusWeight a i.leadRoot

variable {K a} [Finite K]

theorem torusWeight_eq_sigma (hK : Nat.card K = 2 ^ (2 * a + 1)) {α β : Fin F4.tag.rank → ℤ}
    (h : SigmaCond α β) (t : Kˣ × Kˣ) :
    (torusWeight a β t : K) = largeReeSigma a (torusWeight a α t : K) := by
  obtain ⟨u, v⟩ := t
  obtain ⟨h0, h3, h1, h2⟩ := h
  have hq : (2 : ℤ) ^ (2 * a + 1) = 2 * (2 ^ a) ^ 2 := by rw [pow_succ, pow_mul']; ring
  rw [largeReeSigma, ← Units.val_pow_eq_pow_val]
  congr 1
  rw [torusWeight_apply, torusWeight_apply, mul_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_mul,
    ← zpow_mul]
  congr 1
  · refine units_zpow_congr hK u (-F4.cartanPair (f4i 3) α) ?_
    simp only [torusExp0, h0, h3]
    push_cast
    rw [hq]
    ring
  · refine units_zpow_congr hK v (-F4.cartanPair (f4i 2) α) ?_
    simp only [torusExp1, h1, h2]
    push_cast
    rw [hq]
    ring

theorem torusWeight_eq_sq_mul_sigma (hK : Nat.card K = 2 ^ (2 * a + 1))
    {α β : Fin F4.tag.rank → ℤ} (h : SqSigmaCond α β) (t : Kˣ × Kˣ) :
    (torusWeight a β t : K) =
      (torusWeight a α t : K) ^ 2 * largeReeSigma a (torusWeight a α t : K) := by
  obtain ⟨u, v⟩ := t
  obtain ⟨h0, h3, h1, h2⟩ := h
  have hq : (2 : ℤ) ^ (2 * a + 1) = 2 * (2 ^ a) ^ 2 := by rw [pow_succ, pow_mul']; ring
  rw [largeReeSigma, ← pow_add, ← Units.val_pow_eq_pow_val]
  congr 1
  rw [torusWeight_apply, torusWeight_apply, mul_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_mul,
    ← zpow_mul]
  congr 1
  · refine units_zpow_congr hK u (-F4.cartanPair (f4i 3) α) ?_
    simp only [torusExp0, h0, h3]
    push_cast
    rw [hq]
    ring
  · refine units_zpow_congr hK v (-F4.cartanPair (f4i 2) α) ?_
    simp only [torusExp1, h1, h2]
    push_cast
    rw [hq]
    ring

theorem rootChar_center (hK : Nat.card K = 2 ^ (2 * a + 1)) {i : Idx} (hi : i.isSz = true)
    (t : Kˣ × Kˣ) : rootChar K a i.center t = rootChar K a i t ^ (1 + 2 * 2 ^ a) := by
  have hc : i.center.isSz = false ∧ i.center.isCenter = true ∧ i.center.fourIdx = i.fourIdx := by
    cases i <;> simp_all [Idx.isSz, Idx.isCenter, Idx.center, Idx.fourIdx]
  obtain ⟨h1, -, -, h4⟩ := block_cartan_check.2 i.fourIdx
  have hσ := torusWeight_eq_sigma (a := a) hK h1 t
  simp only [rootChar, Idx.leadRoot, hc.1, hc.2.1, hc.2.2, hi, ↓reduceIte, Bool.false_eq_true]
  rw [h4, torusWeight_add, pow_add, pow_one]
  congr 1
  exact Units.ext (by rw [hσ, largeReeSigma, Units.val_pow_eq_pow_val])

variable [CharP K F4.prime]

theorem torusPair_conj_twoCoordG (hK : Nat.card K = 2 ^ (2 * a + 1)) (s : Fin 4)
    (t : Kˣ × Kˣ) (c : K) :
    torusPair a t * twoCoordG a s c * (torusPair a t)⁻¹ =
      twoCoordG a s ((torusWeight a (twoRoot s 0) t : K) * c) := by
  rw [twoCoordG_eq, twoCoordG_eq, weyl_conj_mul, torusPair_conj_pinnedX a t (isRoot_twoRoot s 0),
    torusPair_conj_pinnedX a t (isRoot_twoRoot s 1),
    torusWeight_eq_sigma hK (block_cartan_check.1 s) t, largeReeSigma_mul]

theorem torusPair_conj_fourCoordG (hK : Nat.card K = 2 ^ (2 * a + 1)) (f : Fin 4)
    (t : Kˣ × Kˣ) (b c : K) :
    torusPair a t * fourCoordG a f b c * (torusPair a t)⁻¹ =
      fourCoordG a f ((torusWeight a (fourRoot f 0) t : K) * b)
        ((torusWeight a (fourRoot f 2) t : K) * c) := by
  obtain ⟨h1, h3, h3', -⟩ := block_cartan_check.2 f
  have e : ∀ n A B C D : ModGL F4.tag K, n * (A * B * C * D) * n⁻¹ =
      n * A * n⁻¹ * (n * B * n⁻¹) * (n * C * n⁻¹) * (n * D * n⁻¹) := fun _ _ _ _ _ => by group
  rw [fourCoordG_eq, fourCoordG_eq, e, torusPair_conj_pinnedX a t (isRoot_fourRoot f 0),
    torusPair_conj_pinnedX a t (isRoot_fourRoot f 1),
    torusPair_conj_pinnedX a t (isRoot_fourRoot f 2),
    torusPair_conj_pinnedX a t (isRoot_fourRoot f 3), torusWeight_eq_sigma hK h1 t,
    largeReeSigma_mul]
  have k1 : (torusWeight a (fourRoot f 3) t : K) * largeReeSigma a c =
      largeReeSigma a ((torusWeight a (fourRoot f 2) t : K) * c) := by
    rw [torusWeight_eq_sigma hK h3' t, largeReeSigma_mul]
  have k2 : (torusWeight a (fourRoot f 3) t : K) * (b ^ 2 * largeReeSigma a b) =
      ((torusWeight a (fourRoot f 0) t : K) * b) ^ 2 *
        largeReeSigma a ((torusWeight a (fourRoot f 0) t : K) * b) := by
    rw [torusWeight_eq_sq_mul_sigma hK h3 t, largeReeSigma_mul, mul_pow]
    ring
  rw [mul_add, k1, k2]
  simp only [largeReeSigma_mul]

theorem torusPair_conj_rootElt (hK : Nat.card K = 2 ^ (2 * a + 1)) (t : Kˣ × Kˣ) (i : Idx)
    (u : K) :
    torusPair a t * rootElt K a i u * (torusPair a t)⁻¹ =
      rootElt K a i ((rootChar K a i t : K) * u) := by
  rcases i.isSz_or_isLin_or_isCenter with hi | hi | hi
  · rw [(rootElt_eq_coord i _).1 hi, (rootElt_eq_coord i _).1 hi, torusPair_conj_fourCoordG hK,
      mul_zero]
    simp only [rootChar, Idx.leadRoot, hi, ↓reduceIte]
  · have h1 : i.isSz = false := by cases i <;> simp_all [Idx.isSz, Idx.isLin]
    have h2 : i.isCenter = false := by cases i <;> simp_all [Idx.isCenter, Idx.isLin]
    rw [(rootElt_eq_coord i _).2.2 hi, (rootElt_eq_coord i _).2.2 hi, torusPair_conj_twoCoordG hK,
      rootChar, Idx.leadRoot, h1, h2]
    rfl
  · have h1 : i.isSz = false := by cases i <;> simp_all [Idx.isSz, Idx.isCenter]
    rw [(rootElt_eq_coord i _).2.1 hi, (rootElt_eq_coord i _).2.1 hi, torusPair_conj_fourCoordG hK,
      mul_zero]
    simp only [rootChar, Idx.leadRoot, h1, hi, ↓reduceIte, Bool.false_eq_true]

end Characters

section Centralizers

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem torusH_le_normalizer_rootV (hK : Nat.card K = 2 ^ (2 * a + 1)) (i : Idx) :
    torusH K a ≤ Subgroup.normalizer (rootV K a i : Set (ModGL F4.tag K)) := by
  rintro _ ⟨t, rfl⟩
  refine mem_normalizer_of_map_eq ?_
  rw [rootV, MonoidHom.map_closure, ← Set.range_comp]
  congr 1
  ext g
  simp only [Set.mem_range, Function.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    torusPair_conj_rootElt hK]
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨_, rfl⟩
  · rintro ⟨u, rfl⟩
    refine ⟨((rootChar K a i t)⁻¹ : Kˣ) * u, ?_⟩
    rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]

theorem mem_torusHi_iff (hK : Nat.card K = 2 ^ (2 * a + 1)) (i : Idx) (t : Kˣ × Kˣ) :
    torusPair a t ∈ torusHi K a i ↔ rootChar K a i t = 1 := by
  constructor
  · intro h
    have hc := Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 h).2 _ (rootElt_mem_rootV i 1)
    have e : torusPair a t * rootElt K a i 1 * (torusPair a t)⁻¹ = rootElt K a i 1 := by
      rw [← hc]
      group
    rw [torusPair_conj_rootElt hK, mul_one] at e
    exact Units.ext (rootElt_injective hK i e)
  · intro h
    refine Subgroup.mem_inf.2 ⟨⟨t, rfl⟩, Subgroup.mem_centralizer_iff.2 fun g hg => ?_⟩
    have hle : rootV K a i ≤ Subgroup.centralizer {torusPair a t} := by
      rw [rootV, Subgroup.closure_le]
      rintro _ ⟨u, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      have e := torusPair_conj_rootElt hK t i u
      rw [h, Units.val_one, one_mul] at e
      calc rootElt K a i u * torusPair a t =
          torusPair a t * rootElt K a i u * (torusPair a t)⁻¹ * torusPair a t := by rw [e]
        _ = torusPair a t * rootElt K a i u := by group
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hg)

end Centralizers

section Table

variable (K : Type) [Field K] (a : ℕ)

@[expose] def torusHiParam (i : Idx) : Kˣ →* Kˣ × Kˣ :=
  (zpowGroupHom (torusExp1 (2 ^ a) i.leadRoot)).prod (zpowGroupHom (-torusExp0 (2 ^ a) i.leadRoot))

@[expose] def torusHiHom (i : Idx) :
    Kˣ →* ModGL F4.tag K :=
  (torusPair a).comp (torusHiParam K a i)

variable {K a}

theorem rootChar_torusHiParam (i j : Idx) (u : Kˣ) :
    rootChar K a j (torusHiParam K a i u) =
      u ^ (torusExp0 (2 ^ a) j.leadRoot * torusExp1 (2 ^ a) i.leadRoot -
        torusExp1 (2 ^ a) j.leadRoot * torusExp0 (2 ^ a) i.leadRoot) := by
  simp only [rootChar, torusHiParam, MonoidHom.prod_apply, zpowGroupHom_apply, torusWeight_apply,
    ← zpow_mul]
  rw [sub_eq_add_neg, zpow_add]
  congr 2 <;> ring

theorem rootChar_torusHiParam_self (i : Idx) (u : Kˣ) :
    rootChar K a i (torusHiParam K a i u) = 1 := by
  rw [rootChar_torusHiParam, mul_comm (torusExp0 _ _), sub_self, zpow_zero]

variable [Finite K] [CharP K F4.prime]

omit [CharP K F4.prime] in
theorem torusHiHom_injective (hK : Nat.card K = 2 ^ (2 * a + 1)) (i : Idx) :
    Function.Injective (torusHiHom K a i) := by
  refine (CFSG.RankThree.LargeReeOrder.torusPair_injective hK).comp ?_
  rw [injective_iff_map_eq_one]
  intro u hu
  have h1 : u ^ torusExp1 (2 ^ a) i.leadRoot = 1 := congrArg Prod.fst hu
  have h0 : u ^ (-torusExp0 (2 ^ a) i.leadRoot) = 1 := congrArg Prod.snd hu
  have hN : u ^ ((2 : ℤ) ^ (2 * a + 1) - 1) = 1 := by
    have := units_pow_card_sub_one hK u
    rw [← zpow_natCast, Nat.cast_sub Nat.one_le_two_pow] at this
    simpa using this
  rcases isCoprime_torusExp_leadRoot (a := a) i with ⟨x, y, hxy⟩ | ⟨x, y, hxy⟩
  · calc u = u ^ (x * torusExp0 (2 ^ a) i.leadRoot + y * ((2 : ℤ) ^ (2 * a + 1) - 1)) := by
          rw [hxy, zpow_one]
      _ = 1 := by
          rw [zpow_add, mul_comm x, zpow_mul, mul_comm y, zpow_mul, hN, one_zpow, mul_one,
            show torusExp0 (2 ^ a) i.leadRoot = -(-torusExp0 (2 ^ a) i.leadRoot) by ring,
            zpow_neg, h0, inv_one, one_zpow]
  · calc u = u ^ (x * torusExp1 (2 ^ a) i.leadRoot + y * ((2 : ℤ) ^ (2 * a + 1) - 1)) := by
          rw [hxy, zpow_one]
      _ = 1 := by
          rw [zpow_add, mul_comm x, zpow_mul, mul_comm y, zpow_mul, hN, one_zpow, mul_one, h1,
            one_zpow]

theorem range_torusHiHom (hK : Nat.card K = 2 ^ (2 * a + 1)) (i : Idx) :
    (torusHiHom K a i).range = torusHi K a i := by
  ext g
  constructor
  · rintro ⟨u, rfl⟩
    exact (mem_torusHi_iff hK i _).2 (rootChar_torusHiParam_self i u)
  · intro hg
    obtain ⟨⟨p, r⟩, rfl⟩ := (Subgroup.mem_inf.1 hg).1
    have hχ := (mem_torusHi_iff hK i _).1 hg
    simp only [rootChar, torusWeight_apply] at hχ
    set e₀ := torusExp0 (2 ^ a) i.leadRoot
    set e₁ := torusExp1 (2 ^ a) i.leadRoot
    have hN : ∀ w : Kˣ, w ^ ((2 : ℤ) ^ (2 * a + 1) - 1) = 1 := fun w => by
      have := units_pow_card_sub_one hK w
      rw [← zpow_natCast, Nat.cast_sub Nat.one_le_two_pow] at this
      simpa using this
    have hred : ∀ (w : Kˣ) (x y e : ℤ), x * e + y * ((2 : ℤ) ^ (2 * a + 1) - 1) = 1 →
        (w ^ x) ^ e = w := fun w x y e hxy => by
      have hw : w = w ^ (x * e + y * ((2 : ℤ) ^ (2 * a + 1) - 1)) := by rw [hxy, zpow_one]
      conv_rhs => rw [hw]
      rw [zpow_add, zpow_mul, mul_comm y, zpow_mul, hN, one_zpow, mul_one]
    have hr : r ^ e₁ = (p ^ e₀)⁻¹ := eq_inv_of_mul_eq_one_right hχ
    rcases isCoprime_torusExp_leadRoot (a := a) i with ⟨x, y, hxy⟩ | ⟨x, y, hxy⟩
    ·
      have h1 : (r ^ (-x)) ^ e₁ = p := by
        rw [← zpow_mul, mul_comm, zpow_mul, hr, ← zpow_neg, ← zpow_mul, neg_mul_neg, mul_comm,
          zpow_mul, hred p x y e₀ hxy]
      have h2 : (r ^ (-x)) ^ (-e₀) = r := by
        rw [← zpow_mul, neg_mul_neg, zpow_mul, hred r x y e₀ hxy]
      refine ⟨r ^ (-x), ?_⟩
      have hpar : torusHiParam K a i (r ^ (-x)) = (p, r) := Prod.ext h1 h2
      change torusPair a (torusHiParam K a i (r ^ (-x))) = torusPair a (p, r)
      rw [hpar]
    ·
      have h1 : (p ^ x) ^ e₁ = p := hred p x y e₁ hxy
      have h2 : (p ^ x) ^ (-e₀) = r := by
        rw [← zpow_mul, mul_comm, zpow_mul, zpow_neg, ← hr, ← zpow_mul, mul_comm, zpow_mul,
          hred r x y e₁ hxy]
      refine ⟨p ^ x, ?_⟩
      have hpar : torusHiParam K a i (p ^ x) = (p, r) := Prod.ext h1 h2
      change torusPair a (torusHiParam K a i (p ^ x)) = torusPair a (p, r)
      rw [hpar]

@[expose] def torusHiEquiv (hK : Nat.card K = 2 ^ (2 * a + 1)) (i : Idx) : Kˣ ≃* torusHi K a i :=
  (MonoidHom.ofInjective (torusHiHom_injective hK i)).trans
    (MulEquiv.subgroupCongr (range_torusHiHom hK i))

theorem card_torusHi (hK : Nat.card K = 2 ^ (2 * a + 1)) (i : Idx) :
    Nat.card (torusHi K a i) = 2 ^ (2 * a + 1) - 1 := by
  rw [← Nat.card_congr (torusHiEquiv hK i).toEquiv, Nat.card_units, hK]

end Table

theorem map_conj_centralizer {G : Type*} [Group G] (S : Subgroup G) (g : G) :
    (Subgroup.centralizer (S : Set G)).map (MulAut.conj g).toMonoidHom =
      Subgroup.centralizer ((S.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine Subgroup.mem_centralizer_iff.2 fun h hh => ?_
    obtain ⟨z, hz, rfl⟩ := hh
    have e := Subgroup.mem_centralizer_iff.1 hy z hz
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * z * g⁻¹ * (g * y * g⁻¹) = g * (z * y) * g⁻¹ := by group
      _ = g * (y * z) * g⁻¹ := by rw [e]
      _ = g * y * g⁻¹ * (g * z * g⁻¹) := by group
  · intro hx
    refine ⟨g⁻¹ * x * g, Subgroup.mem_centralizer_iff.2 fun z hz => ?_, ?_⟩
    · have e := Subgroup.mem_centralizer_iff.1 hx (g * z * g⁻¹) ⟨z, hz, rfl⟩
      calc z * (g⁻¹ * x * g) = g⁻¹ * ((g * z * g⁻¹) * x) * g := by group
        _ = g⁻¹ * (x * (g * z * g⁻¹)) * g := by rw [e]
        _ = g⁻¹ * x * g * z := by group
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group

section WeylTorus

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem map_conj_weylS_torusHi (hK : Nat.card K = 2 ^ (2 * a + 1)) {i : Idx} (hi : i ≠ .i3) :
    (torusHi K a i).map (MulAut.conj (weylS K)).toMonoidHom = torusHi K a i.sPerm := by
  rw [torusHi, torusHi, Subgroup.map_inf_eq _ _ _ (MulAut.conj _).injective,
    map_conj_eq_of_mem_normalizer (weylS_mem_normalizer_torusH hK), map_conj_centralizer,
    map_conj_weylS_rootV hi]

theorem map_conj_weylR_torusHi (hK : Nat.card K = 2 ^ (2 * a + 1)) {i : Idx} (hi1 : i ≠ .i1)
    (hi2 : i ≠ .i2) :
    (torusHi K a i).map (MulAut.conj (weylR K)).toMonoidHom = torusHi K a i.rPerm := by
  rw [torusHi, torusHi, Subgroup.map_inf_eq _ _ _ (MulAut.conj _).injective,
    map_conj_eq_of_mem_normalizer (weylR_mem_normalizer_torusH hK), map_conj_centralizer,
    map_conj_weylR_rootV hi1 hi2]

open CFSG.LieType.Ree.LargeReeCover (pairedTorusHom) in
theorem weylR_commute_torusHi_weylS_commute_torusHi (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    (∀ h ∈ torusHi K a .i1, weylR K * h = h * weylR K) ∧
      ∀ h ∈ torusHi K a .i3, weylS K * h = h * weylS K := by
  obtain ⟨⟨e10, e11⟩, -, ⟨e30, e31⟩, -⟩ := torusExp_leadRoot (2 ^ a)
  have hcomm : ∀ {g h : ModGL F4.tag K}, g * h * g⁻¹ = h → g * h = h * g := fun {g h} e => by
    calc g * h = g * h * g⁻¹ * g := by group
      _ = h * g := by rw [e]
  refine ⟨fun h hh => hcomm ?_, fun h hh => hcomm ?_⟩
  · rw [← range_torusHiHom hK] at hh
    obtain ⟨w, rfl⟩ := hh
    change weylR K * torusPair a (torusHiParam K a _ w) * (weylR K)⁻¹ =
      torusPair a (torusHiParam K a _ w)
    simp only [torusHiParam, MonoidHom.prod_apply, zpowGroupHom_apply, e10, e11, neg_neg]
    rw [rankOneTorusPair_eq_mul, weyl_conj_mul, weylR_conj_torusTwo hK, weylR,
      canonicalRep_conj_torusOne hK, mul_assoc, ← map_inv, ← map_mul]
    congr 2
    rw [← zpow_mul, ← zpow_neg, ← zpow_add]
    refine units_zpow_congr hK w 2 ?_
    push_cast
    rw [show (2 : ℤ) ^ (2 * a + 1) = 2 * (2 ^ a) ^ 2 by rw [pow_succ, pow_mul']; ring]
    ring
  · rw [← range_torusHiHom hK] at hh
    obtain ⟨w, rfl⟩ := hh
    change weylS K * torusPair a (torusHiParam K a _ w) * (weylS K)⁻¹ =
      torusPair a (torusHiParam K a _ w)
    simp only [torusHiParam, MonoidHom.prod_apply, zpowGroupHom_apply, e30, e31]
    rw [rankOneTorusPair_eq_mul, weyl_conj_mul, weylS_conj_torusOne hK,
      weylS, canonicalRep_conj_torusTwo hK,
      (rankOne_commute_pairedTorusHom (a := a) 1 2 0 3 _ _).eq, ← mul_assoc, ← map_inv,
      ← map_mul]
    congr 2
    rw [← zpow_neg, ← zpow_add]
    congr 1
    ring

end WeylTorus

end CFSG.LocalAnalysis.EvenBN.TwoF4
