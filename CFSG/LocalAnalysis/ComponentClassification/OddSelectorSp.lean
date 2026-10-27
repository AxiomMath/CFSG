module

public import CFSG.LieType.Steinberg.Classical.Symplectic.RankOne
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingIsometryNative
public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorQuaternion
public import CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices

public noncomputable section

namespace CFSG.ComponentClassification.OddSelector

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial

section Card

variable {H : Type*} {L : Type} [Group H] [Group L] [Finite H]

omit [Finite H] in
theorem not_small_source_of_cover_quaternion_card [Group.IsPerfect H] (σ : H →* L)
    (hσ : σ.ker ≤ center H) (q : QuaternionGroup 2 →* H)
    (hq : q (QuaternionGroup.a 2) ∉ center H) {l : ℕ} (hl : l.Prime) (hl2 : l ≠ 2)
    (hH : l ^ 3 ∣ Nat.card H) (hZ : Nat.Coprime l (Nat.card (center H))) :
    (∀ p f : ℕ, p ≠ 2 → ¬ StatedClassicalModel (L ⧸ center L) .PSL 2 p f) ∧
      IsEmpty (L ⧸ center L ≃* alternatingGroup (Fin 7)) ∧
      ¬ StatedClassicalModel (L ⧸ center L) .PSL 3 2 2 := by
  set τ : H →* L ⧸ center L := (QuotientGroup.mk' (center L)).comp σ with hτ
  have hker : τ.ker ≤ center H := by
    intro x hx
    refine mem_center_of_map_mem_center σ hσ ?_
    rw [MonoidHom.mem_ker, hτ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hx
    exact hx
  have hτq : Function.Injective (τ.comp q) := by
    refine injective_of_quaternion _ fun h => hq (hker ?_)
    exact h
  have hcard : Nat.card H = Nat.card τ.range * Nat.card τ.ker := by
    rw [(τ.ker).card_eq_card_quotient_mul_card_subgroup,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange τ).toEquiv]
  have hcop : Nat.Coprime (l ^ 3) (Nat.card τ.ker) :=
    Nat.Coprime.pow_left 3 (Nat.Coprime.coprime_dvd_right
      (Subgroup.card_dvd_of_le hker) hZ)
  have hU : l ^ 3 ∣ Nat.card (L ⧸ center L) := by
    have h1 : l ^ 3 ∣ Nat.card τ.range * Nat.card τ.ker := hcard ▸ hH
    exact (hcop.dvd_of_dvd_mul_right h1).trans (Subgroup.card_subgroup_dvd_card _)
  exact ⟨fun _ _ hp2 => not_psl_two_odd_of_quaternion _ hτq hp2,
    isEmpty_alternating_seven_of_dvd hl hl2 hU, not_psl_three_four_of_dvd hl hl2 hU⟩

end Card

section LongSL

variable {k : Type} [Field k] {r : ℕ}

theorem transvection_inl_inr (i : Fin r) (c : k) :
    transvection (Sum.inl i : Fin r ⊕ Fin r) (Sum.inr i) c =
      fromBlocks 1 (single i i c) 0 1 := by
  ext (a | a) (b | b) <;>
    simp [transvection, Matrix.one_apply, Matrix.single_apply, fromBlocks]

theorem transvection_inr_inl (i : Fin r) (c : k) :
    transvection (Sum.inr i : Fin r ⊕ Fin r) (Sum.inl i) c =
      fromBlocks 1 0 (single i i c) 1 := by
  ext (a | a) (b | b) <;>
    simp [transvection, Matrix.one_apply, Matrix.single_apply, fromBlocks]

theorem transvection_inl_inr_mem (i : Fin r) (c : k) :
    TauCeti.transvectionUnit (Sum.inl_ne_inr : (Sum.inl i : Fin r ⊕ Fin r) ≠ Sum.inr i) c ∈
      StatedSp r k := by
  refine Subgroup.subset_closure ?_
  rw [Set.mem_ofPred_eq, TauCeti.coe_transvectionUnit, transvection_inl_inr, fromBlocks_transpose,
    fromBlocks_multiply, fromBlocks_multiply]
  simp [Matrix.transpose_single]

theorem transvection_inr_inl_mem (i : Fin r) (c : k) :
    TauCeti.transvectionUnit (Sum.inr_ne_inl : (Sum.inr i : Fin r ⊕ Fin r) ≠ Sum.inl i) c ∈
      StatedSp r k := by
  refine Subgroup.subset_closure ?_
  rw [Set.mem_ofPred_eq, TauCeti.coe_transvectionUnit, transvection_inr_inl, fromBlocks_transpose,
    fromBlocks_multiply, fromBlocks_multiply]
  simp [Matrix.transpose_single]

theorem blockHom_mem_statedSp (i : Fin r) (A : SpecialLinearGroup (Fin 2) k) :
    LieType.Steinberg.Sp.blockHom k
      (Sum.inl_ne_inr : (Sum.inl i : Fin r ⊕ Fin r) ≠ Sum.inr i) A ∈ StatedSp r k := by
  set ψ := LieType.Steinberg.Sp.blockHom k
    (Sum.inl_ne_inr : (Sum.inl i : Fin r ⊕ Fin r) ≠ Sum.inr i)
  have hle : Subgroup.closure (Set.range (LieType.Steinberg.sl2Upper (k := k)) ∪
      Set.range LieType.Steinberg.sl2Lower) ≤
      (StatedSp r k).comap ψ := by
    rw [Subgroup.closure_le]
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · change ψ (LieType.Steinberg.sl2Upper c) ∈ StatedSp r k
      rw [LieType.Steinberg.Sp.blockHom_upper]
      exact transvection_inl_inr_mem i c
    · change ψ (LieType.Steinberg.sl2Lower c) ∈ StatedSp r k
      rw [LieType.Steinberg.Sp.blockHom_lower]
      exact transvection_inr_inl_mem i c
  exact hle (LieType.Steinberg.Sp.mem_closure_sl2 A)

@[expose] def longSL (i : Fin r) : SpecialLinearGroup (Fin 2) k →* StatedSp r k :=
  (LieType.Steinberg.Sp.blockHom k
    (Sum.inl_ne_inr : (Sum.inl i : Fin r ⊕ Fin r) ≠ Sum.inr i)).codRestrict (StatedSp r k)
    (blockHom_mem_statedSp i)

theorem coe_longSL (i : Fin r) (A : SpecialLinearGroup (Fin 2) k) :
    (((longSL i A : StatedSp r k) : GL (Fin r ⊕ Fin r) k) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) =
      LieType.Steinberg.Sp.blockMat (Sum.inl i) (Sum.inr i) (A : Matrix (Fin 2) (Fin 2) k) :=
  rfl

end LongSL

section Center

variable {k : Type} [Field k] {r : ℕ}

theorem exists_scalar_of_mem_center_statedSp {g : StatedSp r k}
    (hg : g ∈ center (StatedSp r k)) :
    ∃ c : kˣ, (g : GL (Fin r ⊕ Fin r) k) = GeneralLinearGroup.scalar _ c := by
  have heq := CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic (n := r) (K := k)
  have hg2 : (g : GL (Fin r ⊕ Fin r) k) ∈ TauCeti.GLSymplectic (Fin r) k := by
    rw [← heq]
    exact g.2
  set g' : TauCeti.GLSymplectic (Fin r) k := ⟨g, hg2⟩
  have hg' : g' ∈ center (TauCeti.GLSymplectic (Fin r) k) := by
    rw [mem_center_iff]
    intro h
    have hh : (h : GL (Fin r ⊕ Fin r) k) ∈ StatedSp r k := by
      rw [heq]
      exact h.2
    have := congrArg Subtype.val (mem_center_iff.mp hg ⟨h, hh⟩)
    exact Subtype.ext this
  rw [CFSG.ClassicalGroups.Symplectic.center_GLSymplectic_eq, mem_subgroupOf, StatedScalars,
    MonoidHom.mem_range] at hg'
  obtain ⟨c, hc⟩ := hg'
  exact ⟨c, hc.symm⟩

theorem scalar_mem_statedSp_iff' (hr : 1 ≤ r) (c : kˣ) :
    GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c ∈ StatedSp r k ↔ c ^ 2 = 1 :=
  CFSG.Open.StatedAPI.scalar_mem_statedSp_iff hr c

theorem coprime_card_center_statedSp [Finite k] (hr : 1 ≤ r) {l : ℕ} (hl : l.Prime)
    (hl2 : l ≠ 2) : Nat.Coprime l (Nat.card (center (StatedSp r k))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (StatedSp r k) := Subtype.finite
  have hP : IsPGroup 2 (center (StatedSp r k)) := by
    intro g
    refine ⟨1, ?_⟩
    obtain ⟨c, hc⟩ := exists_scalar_of_mem_center_statedSp g.2
    have hc2 : c ^ 2 = 1 := (scalar_mem_statedSp_iff' hr c).mp (hc ▸ (g : StatedSp r k).2)
    apply Subtype.ext
    apply Subtype.ext
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    rw [hc, ← map_pow, hc2, map_one]
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hP
  rw [hn]
  exact Nat.Coprime.pow_right n ((Nat.coprime_primes hl Nat.prime_two).mpr hl2)

end Center

theorem not_small_source_of_sp_cover {L : Type} [Group L] {r ℓ e : ℕ} (hr : 2 ≤ r)
    (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (he : 1 ≤ e) {k : Type} [Field k] [Finite k]
    (hk : Nat.card k = ℓ ^ e) (σ : StatedSp r k →* L) (hσ : σ.ker ≤ center (StatedSp r k)) :
    (∀ p f : ℕ, p ≠ 2 → ¬ StatedClassicalModel (L ⧸ center L) .PSL 2 p f) ∧
      IsEmpty (L ⧸ center L ≃* alternatingGroup (Fin 7)) ∧
      ¬ StatedClassicalModel (L ⧸ center L) .PSL 3 2 2 := by
  classical
  have : CharP k ℓ := finite_field_prime_power_characteristic hℓ he hk
  have hk2 : ringChar k ≠ 2 := by rw [ringChar.eq k ℓ]; exact hℓ2
  have h2 : (2 : k) ≠ 0 := Ring.two_ne_zero hk2
  have hodd : Odd (Nat.card k) := by rw [hk]; exact (hℓ.odd_of_ne_two hℓ2).pow
  have : Finite (StatedSp r k) := Subtype.finite
  have heq := CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic (n := r) (K := k)
  have hq := CatalogueBAlternatingIsometry.symplectic_quasisimple k r (by omega) hodd
    (Or.inl (by omega))
  have : Group.IsPerfect (TauCeti.GLSymplectic (Fin r) k) := hq.1
  have : Group.IsPerfect (StatedSp r k) :=
    Group.IsPerfect.ofSurjective (f := (MulEquiv.subgroupCongr heq.symm).toMonoidHom)
      (MulEquiv.subgroupCongr heq.symm).surjective
  obtain ⟨⟨a, b, hab⟩, -⟩ :=
    QuaternionMatrices.odd_field_two_dimensional_quaternion_matrices (K := k) hk2
  set i0 : Fin r := ⟨0, by omega⟩
  set i1 : Fin r := ⟨1, by omega⟩
  set q := (longSL (k := k) i0).comp (QuaternionMatrices.quatHom hab)
  have hq2 : q (QuaternionGroup.a 2) ∉ center (StatedSp r k) := by
    intro hmem
    obtain ⟨c, hc⟩ := exists_scalar_of_mem_center_statedSp hmem
    have hmat : (((q (QuaternionGroup.a 2) : StatedSp r k) : GL (Fin r ⊕ Fin r) k) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) =
          LieType.Steinberg.Sp.blockMat (Sum.inl i0) (Sum.inr i0) (-1) := by
      change LieType.Steinberg.Sp.blockMat (Sum.inl i0) (Sum.inr i0)
        ((QuaternionMatrices.quatHom hab (QuaternionGroup.a 2) :
          SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) = _
      rw [QuaternionMatrices.quatHom_a_two hab]
    rw [hc, GeneralLinearGroup.coe_scalar] at hmat
    have h00 := congrFun (congrFun hmat (Sum.inl i0)) (Sum.inl i0)
    have h11 := congrFun (congrFun hmat (Sum.inl i1)) (Sum.inl i1)
    have hi01 : i1 ≠ i0 := by simp [i0, i1, Fin.ext_iff]
    simp only [LieType.Steinberg.Sp.blockMat, Matrix.of_apply, scalar_apply,
      diagonal_apply_eq, ↓reduceIte, Matrix.neg_apply, Matrix.one_apply_eq] at h00
    simp only [LieType.Steinberg.Sp.blockMat, Matrix.of_apply, scalar_apply,
      diagonal_apply_eq, Sum.inl.injEq, hi01, ↓reduceIte, reduceCtorEq, Matrix.one_apply_eq] at h11
    apply h2
    linear_combination h00 - h11
  have hH : ℓ ^ 3 ∣ Nat.card (StatedSp r k) := by
    rw [SymplecticFlag.card_statedSp, hk, ← pow_mul]
    refine dvd_mul_of_dvd_left (pow_dvd_pow ℓ ?_) _
    have : 4 ≤ r ^ 2 := by nlinarith
    nlinarith
  exact not_small_source_of_cover_quaternion_card σ hσ q hq2 hℓ hℓ2 hH
    (coprime_card_center_statedSp (by omega) hℓ hℓ2)

end CFSG.ComponentClassification.OddSelector
