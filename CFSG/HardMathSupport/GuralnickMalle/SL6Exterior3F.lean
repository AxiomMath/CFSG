module

public import CFSG.HardMathSupport.GuralnickMalle.SL6Exterior3F.Compare
public import CFSG.HardMathSupport.GuralnickMalle.Prop310
public import CFSG.RankThree.GF2n.Smith81.S81VSchurFlag

public section

namespace CFSG.HardMathSupport.GuralnickMalle

open Module
open CFSG.Open

variable {K : Type} [Field K]

@[expose] noncomputable def natRank (a : GL (Fin 6) K) : ℕ :=
  Module.finrank K (LinearMap.range
    (Matrix.toLin' ((a : Matrix (Fin 6) (Fin 6) K)) - 1))

theorem natRank_eq_finrank_range_sub_one (a : GL (Fin 6) K) :
    natRank a = Module.finrank K (LinearMap.range
      (Matrix.toLin' ((a : Matrix (Fin 6) (Fin 6) K)) - 1)) := by
  rfl

theorem one_le_natRank {a : GL (Fin 6) K} (ha : a ≠ 1) : 1 ≤ natRank a := by
  show 1 ≤ Module.finrank K (LinearMap.range
    (Matrix.toLin' ((a : Matrix (Fin 6) (Fin 6) K)) - 1))
  have hx : (Matrix.toLin' ((a : Matrix (Fin 6) (Fin 6) K)) - 1 :
      Module.End K (Fin 6 → K)) ≠ 0 := by
    intro h0
    apply ha
    apply Units.ext
    apply Matrix.toLin'.injective
    rw [sub_eq_zero.mp h0]
    rw [show ((1 : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = 1 by simp]
    rw [Matrix.toLin'_one]
    rfl
  have hbot : LinearMap.range
      (Matrix.toLin' ((a : Matrix (Fin 6) (Fin 6) K)) - 1) ≠ ⊥ := by
    simpa [LinearMap.range_eq_bot] using hx
  exact Submodule.one_le_finrank_iff.mpr hbot

theorem natRank_le_three [Finite K] [CharP K 2] (a : GL (Fin 6) K) (ha : a * a = 1) : natRank a ≤ 3 := by
  have hT : (Matrix.toLin' ((a : Matrix (Fin 6) (Fin 6) K))) *
      (Matrix.toLin' ((a : Matrix (Fin 6) (Fin 6) K))) = 1 := by
    have h1 : (glNaturalRep 6 K) (a * a) = (glNaturalRep 6 K) 1 := by rw [ha]
    rw [map_mul, map_one] at h1
    rwa [glNaturalRep_eq_toLin] at h1
  have htwo : (2 : Module.End K (Fin 6 → K)) = 0 := by
    rw [← map_ofNat (algebraMap K ((Fin 6 → K) →ₗ[K] (Fin 6 → K))) 2, CharTwo.two_eq_zero,
      map_zero]
  have hone : (1 : Module.End K (Fin 6 → K)) + 1 = 0 := by
    rw [one_add_one_eq_two, htwo]
  have hX : (Matrix.toLin' ((a : Matrix (Fin 6) (Fin 6) K))) +
      (Matrix.toLin' ((a : Matrix (Fin 6) (Fin 6) K))) = 0 := by
    rw [← two_mul, htwo, zero_mul]
  have hsq : (Matrix.toLin' ((a : Matrix (Fin 6) (Fin 6) K)) - 1) *
      (Matrix.toLin' ((a : Matrix (Fin 6) (Fin 6) K)) - 1) = 0 := by
    calc (Matrix.toLin' ((a : Matrix (Fin 6) (Fin 6) K)) - 1) *
          (Matrix.toLin' ((a : Matrix (Fin 6) (Fin 6) K)) - 1)
        = Matrix.toLin' ((a : Matrix (Fin 6) (Fin 6) K)) *
            Matrix.toLin' ((a : Matrix (Fin 6) (Fin 6) K)) -
            Matrix.toLin' ((a : Matrix (Fin 6) (Fin 6) K)) -
            Matrix.toLin' ((a : Matrix (Fin 6) (Fin 6) K)) + 1 := by
          simp only [sub_mul, mul_sub, mul_one, one_mul]
          abel
      _ = 1 - Matrix.toLin' ((a : Matrix (Fin 6) (Fin 6) K)) -
            Matrix.toLin' ((a : Matrix (Fin 6) (Fin 6) K)) + 1 := by rw [hT]
      _ = (1 + 1) - (Matrix.toLin' ((a : Matrix (Fin 6) (Fin 6) K)) +
            Matrix.toLin' ((a : Matrix (Fin 6) (Fin 6) K))) := by abel
      _ = 0 := by rw [hone, hX, sub_zero]
  have hle : LinearMap.range (Matrix.toLin' ((a : Matrix (Fin 6) (Fin 6) K)) - 1) ≤
      LinearMap.ker (Matrix.toLin' ((a : Matrix (Fin 6) (Fin 6) K)) - 1) := by
    intro v hv
    rw [LinearMap.mem_ker]
    obtain ⟨u, rfl⟩ := hv
    have h2 := congrArg (fun f : Module.End K (Fin 6 → K) => f u) hsq
    simpa [Module.End.mul_eq_comp, LinearMap.comp_apply] using h2
  have hrn := LinearMap.finrank_range_add_finrank_ker
    (Matrix.toLin' ((a : Matrix (Fin 6) (Fin 6) K)) - 1)
  have hmono := Submodule.finrank_mono hle
  rw [Module.finrank_fin_fun] at hrn
  unfold natRank
  omega

theorem card_le_pow_nine [Finite K] [CharP K 2] (A : Subgroup (GL (Fin 6) K)) (hAel : IsElemAbelian 2 A) :
    Nat.card A ≤ Nat.card K ^ 9 := by
  have h := card_le_pow_half_sq (K := K) (n := 6) (p := 2) Nat.prime_two (A := A) hAel
  have h9 : 6 ^ 2 / 4 = 9 := by norm_num
  rwa [h9] at h

theorem card_fixSubGen_glExterior3 (A : Subgroup (GL (Fin 6) K)) :
    Nat.card (fixSubGen (glExterior3Rep K) A) =
      Nat.card K ^ Module.finrank K (fixSubGen (glExterior3Rep K) A) :=
  Module.natCard_eq_pow_finrank (K := K) (V := fixSubGen (glExterior3Rep K) A)

theorem exists_fixed_vector_natural [Finite K] [CharP K 2] (A : Subgroup (GL (Fin 6) K)) (_hA : A ≠ ⊥)
    (hAel : IsElemAbelian 2 A) :
    ∃ e : Fin 6 → K, e ≠ 0 ∧ ∀ a ∈ A,
      Matrix.toLin' ((a : Matrix (Fin 6) (Fin 6) K)) e = e := by
  have hne : commonKernel (unipotentAlgebra A) ≠ ⊥ :=
    commonKernel_ne_bot (unipotentAlgebra A)
      (fun f hf g hg => unipotentAlgebra_commute hAel.1 hf hg)
      (fun f hf => unipotentAlgebra_isNilpotent Nat.prime_two hAel hf)
      (inferInstance)
  rw [commonKernel_unipotentAlgebra] at hne
  obtain ⟨e, he, he0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  refine ⟨e, he0, fun a ha => ?_⟩
  have h := (mem_fixSubGen.mp he) a ha
  rwa [glNaturalRep_eq_toLin] at h

theorem exists_natCard_eq_two_pow [Finite K] [CharP K 2] :
    ∃ f : ℕ, Nat.card K = 2 ^ f := by
  let : Fintype K := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  exact ⟨n, by rw [Nat.card_eq_fintype_card]; exact hn⟩

theorem two_mul_pow_le_of_lt {f r : ℕ} (h : 2 ^ (8 * f) < 2 ^ r) :
    2 * 2 ^ (8 * f) ≤ 2 ^ r := by
  have hlt : 8 * f < r := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp h
  calc 2 * 2 ^ (8 * f) = 2 ^ (8 * f + 1) := by rw [pow_succ]; ring
    _ ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem unipotentEnd_eq_toLin_nilpOf (a : GL (Fin 6) K) :
    unipotentEnd a = Matrix.toLin' ((CFSG.RankThree.GF2n.Smith81.nilpOf a : Matrix (Fin 6) (Fin 6) K)) := by
  rw [unipotentEnd, CFSG.RankThree.GF2n.Smith81.nilpOf, map_sub, Matrix.toLin'_one,
    glNaturalRep_eq_toLin]
  rfl

theorem unipotentAlgebra_eq_map_nilpSpan (A : Subgroup (GL (Fin 6) K)) :
    unipotentAlgebra A = (CFSG.RankThree.GF2n.Smith81.nilpSpan A).map
      (Matrix.toLin' (n := Fin 6) (R := K)).toLinearMap := by
  rw [unipotentAlgebra, CFSG.RankThree.GF2n.Smith81.nilpSpan, Submodule.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨CFSG.RankThree.GF2n.Smith81.nilpOf a, ⟨⟨a, ha⟩, rfl⟩,
      (unipotentEnd_eq_toLin_nilpOf a).symm⟩
  · rintro ⟨y, ⟨⟨a, ha⟩, rfl⟩, rfl⟩
    exact ⟨a, ha, unipotentEnd_eq_toLin_nilpOf a⟩

theorem finrank_nilpSpan_eq_unipotentAlgebra [Finite K] [CharP K 2] (A : Subgroup (GL (Fin 6) K)) :
    Module.finrank K (CFSG.RankThree.GF2n.Smith81.nilpSpan A) = Module.finrank K (unipotentAlgebra A) := by
  rw [unipotentAlgebra_eq_map_nilpSpan]
  exact (LinearEquiv.finrank_map_eq
    (Matrix.toLinAlgEquiv' (R := K) (n := Fin 6)).toLinearEquiv (CFSG.RankThree.GF2n.Smith81.nilpSpan A)).symm

theorem nine_le_finrank_nilpSpan [Finite K] [CharP K 2] (A : Subgroup (GL (Fin 6) K))
    (hAel : IsElemAbelian 2 A) (h8 : Nat.card K ^ 8 < Nat.card A) :
    9 ≤ Module.finrank K (CFSG.RankThree.GF2n.Smith81.nilpSpan A) := by
  by_contra h
  have hfin : Module.finrank K (unipotentAlgebra A) ≤ 8 := by
    rw [← finrank_nilpSpan_eq_unipotentAlgebra]; omega
  have hcard := card_le_pow_finrank_unipotentAlgebra (K := K) (n := 6) (p := 2) hAel
  have hmono : Nat.card K ^ Module.finrank K (unipotentAlgebra A) ≤ Nat.card K ^ 8 :=
    Nat.pow_le_pow_right (Nat.card_pos) hfin
  have : Nat.card A ≤ Nat.card K ^ 8 := hcard.trans hmono
  omega

theorem exists_natCard_eq_two_pow_of_isPGroup {G : Type*} [Group G] [Finite G]
    (h : IsPGroup 2 G) :
    ∃ r : ℕ, Nat.card G = 2 ^ r := by
  obtain ⟨n, hn⟩ := isPGroup_iff_card_dvd_pow.mp h
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hn
  exact ⟨k, hk⟩

theorem toLin'_sub_one_apply (a : GL (Fin 6) K) (v : Fin 6 → K) :
    (Matrix.toLin' ((a : Matrix (Fin 6) (Fin 6) K)) - 1) v =
      ((a : Matrix (Fin 6) (Fin 6) K)).mulVec v - v := by
  rw [LinearMap.sub_apply, Module.End.one_apply, Matrix.toLin'_apply]

noncomputable def subOneOnCompl (a : GL (Fin 6) K) (W C : Submodule K (Fin 6 → K))
    (hsub : ∀ v, ((a : Matrix (Fin 6) (Fin 6) K)).mulVec v - v ∈ W) : C →ₗ[K] W :=
  LinearMap.codRestrict W
    (((a : Matrix (Fin 6) (Fin 6) K)).mulVecLin.comp C.subtype - C.subtype)
    (fun c => hsub (c : Fin 6 → K))

theorem range_toLin'_sub_one_eq_map_subOneOnCompl (a : GL (Fin 6) K)
    {W C : Submodule K (Fin 6 → K)} (hC : IsCompl W C)
    (hsub : ∀ v, ((a : Matrix (Fin 6) (Fin 6) K)).mulVec v - v ∈ W)
    (hkill : ∀ w ∈ W, ((a : Matrix (Fin 6) (Fin 6) K)).mulVec w = w) :
    (LinearMap.range (subOneOnCompl a W C hsub)).map W.subtype =
      LinearMap.range (Matrix.toLin' ((a : Matrix (Fin 6) (Fin 6) K)) - 1) := by
  apply le_antisymm
  · rintro x ⟨y, hy, rfl⟩
    obtain ⟨c, rfl⟩ := hy
    exact ⟨(c : Fin 6 → K), by
      rw [toLin'_sub_one_apply]
      show ((a : Matrix (Fin 6) (Fin 6) K)).mulVec (c : Fin 6 → K) - (c : Fin 6 → K) =
        ((a : Matrix (Fin 6) (Fin 6) K)).mulVec (c : Fin 6 → K) - (c : Fin 6 → K)
      rfl⟩
  · rintro x ⟨v, rfl⟩
    have hv : v ∈ W ⊔ C := by rw [hC.sup_eq_top]; trivial
    obtain ⟨w, hw, c, hc, rfl⟩ := Submodule.mem_sup.mp hv
    refine ⟨subOneOnCompl a W C hsub ⟨c, hc⟩, ⟨⟨c, hc⟩, rfl⟩, ?_⟩
    show ((a : Matrix (Fin 6) (Fin 6) K)).mulVec (c : Fin 6 → K) - (c : Fin 6 → K) =
      ((a : Matrix (Fin 6) (Fin 6) K)).mulVec ((w + (c : Fin 6 → K))) - (w + (c : Fin 6 → K))
    rw [Matrix.mulVec_add, hkill w hw]
    abel

theorem card_le_card_rank_lt_three [Finite K] [CharP K 2] (A : Subgroup (GL (Fin 6) K)) (hAel : IsElemAbelian 2 A)
    (h9 : 9 ≤ Module.finrank K (CFSG.RankThree.GF2n.Smith81.nilpSpan A))
    (h2 : ∀ a ∈ A, a ≠ 1 → natRank a ≤ 2) :
    Nat.card A ≤ Nat.card {f : (Fin 3 → K) →ₗ[K] (Fin 3 → K) //
      Module.finrank K (LinearMap.range f) < 3} := by
  classical
  obtain ⟨W, hW3, hsub, hkill, -⟩ :=
    CFSG.RankThree.GF2n.Smith81.S81V.exists_schur_space (F := K) (E := A) hAel h9
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl W
  have hdimC : Module.finrank K C = 3 := by
    have h := Submodule.finrank_add_eq_of_isCompl hC
    rw [hW3, Module.finrank_fin_fun] at h
    omega
  have hsubA : ∀ a : A, ∀ v : Fin 6 → K,
      (((a : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)).mulVec v - v ∈ W := fun a => hsub a a.2
  have hkillA : ∀ a : A, ∀ w ∈ W,
      (((a : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)).mulVec w = w := fun a => hkill a a.2
  let Φ : A → (C →ₗ[K] W) := fun a => subOneOnCompl (a : GL (Fin 6) K) W C (hsubA a)
  have hΦinj : Function.Injective Φ := by
    intro a b hab
    have hmem : ∀ v : Fin 6 → K,
        (((a : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)).mulVec v - v =
        (((b : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)).mulVec v - v := by
      intro v
      have hv : v ∈ W ⊔ C := by rw [hC.sup_eq_top]; trivial
      obtain ⟨w, hw, c, hc, rfl⟩ := Submodule.mem_sup.mp hv
      have hcc : (((a : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)).mulVec (c : Fin 6 → K) - (c : Fin 6 → K) =
          (((b : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)).mulVec (c : Fin 6 → K) - (c : Fin 6 → K) := by
        have h := congrArg (fun f : (C →ₗ[K] W) => (f ⟨c, hc⟩ : W)) hab
        exact congrArg (fun x : W => (x : Fin 6 → K)) h
      rw [Matrix.mulVec_add, Matrix.mulVec_add, hkillA a w hw, hkillA b w hw]
      calc w + (((a : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)).mulVec (c : Fin 6 → K) - (w + (c : Fin 6 → K))
          = (((a : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)).mulVec (c : Fin 6 → K) - (c : Fin 6 → K) := by abel
        _ = (((b : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)).mulVec (c : Fin 6 → K) - (c : Fin 6 → K) := hcc
        _ = w + (((b : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)).mulVec (c : Fin 6 → K) -
              (w + (c : Fin 6 → K)) := by abel
    apply Subtype.ext
    apply glNaturalRep_injective 6 K
    rw [glNaturalRep_eq_toLin, glNaturalRep_eq_toLin]
    refine LinearMap.ext fun v => ?_
    have hv := hmem v
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply]
    have := congrArg (fun z => z + v) hv
    simpa [sub_add_cancel] using this
  have hinj := hΦinj
  let bC : Basis (Fin 3) K C := (Module.finBasis K C).reindex (finCongr hdimC)
  let bW : Basis (Fin 3) K W := (Module.finBasis K W).reindex (finCongr hW3)
  let eC : C ≃ₗ[K] (Fin 3 → K) := bC.equivFun
  let eW : W ≃ₗ[K] (Fin 3 → K) := bW.equivFun
  let Ψ : A → ((Fin 3 → K) →ₗ[K] (Fin 3 → K)) := fun a =>
    (eW : W →ₗ[K] (Fin 3 → K)).comp ((Φ a).comp (eC.symm : (Fin 3 → K) →ₗ[K] C))
  have hΨinj : Function.Injective Ψ := by
    intro a b hab
    apply hinj
    have h := congrArg (fun f : (Fin 3 → K) →ₗ[K] (Fin 3 → K) =>
      (eW.symm : (Fin 3 → K) →ₗ[K] W).comp (f.comp (eC : C →ₗ[K] (Fin 3 → K)))) hab
    simpa [Ψ, LinearMap.comp_assoc] using h
  have hnat : ∀ a : A, natRank (a : GL (Fin 6) K) ≤ 2 := by
    intro a
    by_cases ha1 : (a : GL (Fin 6) K) = 1
    · rw [ha1, natRank, show ((1 : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = 1 by simp,
        Matrix.toLin'_one]
      have hz : (LinearMap.id - 1 : Module.End K (Fin 6 → K)) = 0 := by
        rw [show (1 : Module.End K (Fin 6 → K)) = LinearMap.id from rfl, sub_self]
      rw [hz, LinearMap.range_zero, finrank_bot]
      omega
    · exact h2 _ a.2 ha1
  have hΨrank : ∀ a : A, Module.finrank K (LinearMap.range (Ψ a)) < 3 := by
    intro a
    have hrange := range_toLin'_sub_one_eq_map_subOneOnCompl (a : GL (Fin 6) K) hC
      (hsubA a) (hkillA a)
    have hcard_le : Nat.card (LinearMap.range (Φ a)) ≤
        Nat.card ((LinearMap.range (Φ a)).map W.subtype) := by
      apply Nat.card_le_card_of_injective
        (fun x : (LinearMap.range (Φ a)) =>
          (⟨W.subtype (x : W), ⟨(x : W), x.2, rfl⟩⟩ :
            ((LinearMap.range (Φ a)).map W.subtype)))
      intro x y hxy
      have h2 : W.subtype (x : W) = W.subtype (y : W) :=
        congrArg (fun z : ((LinearMap.range (Φ a)).map W.subtype) => (z : Fin 6 → K)) hxy
      exact Subtype.ext (W.subtype_injective h2)
    rw [Module.natCard_eq_pow_finrank (K := K) (V := LinearMap.range (Φ a)),
      Module.natCard_eq_pow_finrank (K := K) (V := (LinearMap.range (Φ a)).map W.subtype)]
      at hcard_le
    let : Fintype K := Fintype.ofFinite K
    have hq : 1 < Nat.card K := by
      rw [Nat.card_eq_fintype_card]; exact Fintype.one_lt_card
    have hle : Module.finrank K (LinearMap.range (Φ a)) ≤ natRank (a : GL (Fin 6) K) := by
      rw [natRank, ← hrange]
      exact (Nat.pow_le_pow_iff_right hq).mp hcard_le
    have hΨrange : LinearMap.range (Ψ a) =
        (LinearMap.range (Φ a)).map (eW : W →ₗ[K] (Fin 3 → K)) := by
      show LinearMap.range ((eW : W →ₗ[K] (Fin 3 → K)).comp
        ((Φ a).comp (eC.symm : (Fin 3 → K) →ₗ[K] C))) = _
      rw [LinearMap.range_comp, LinearMap.range_comp,
        LinearMap.range_eq_top.mpr (LinearEquiv.surjective eC.symm), Submodule.map_top]
    rw [hΨrange, LinearEquiv.finrank_map_eq eW (LinearMap.range (Φ a))]
    have := hnat a
    omega
  have : Finite ((Fin 3 → K) →ₗ[K] (Fin 3 → K)) :=
    Finite.of_injective (fun f : (Fin 3 → K) →ₗ[K] (Fin 3 → K) => (f : (Fin 3 → K) → (Fin 3 → K)))
      (fun f g h => LinearMap.ext fun x => congrFun h x)
  exact Nat.card_le_card_of_injective
    (fun a : A => (⟨Ψ a, hΨrank a⟩ : {f : (Fin 3 → K) →ₗ[K] (Fin 3 → K) //
      Module.finrank K (LinearMap.range f) < 3})) (fun a b hab => hΨinj (congrArg Subtype.val hab))

end CFSG.HardMathSupport.GuralnickMalle
