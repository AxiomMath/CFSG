module

public import CFSG.RankThree.PartOne.AUTSL.SpTwoAut
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyPrimeSquare

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag

theorem card_statedSp_le {K : Type} [Field K] [Finite K] (r : ℕ) :
    Nat.card (StatedSp r K) ≤ Nat.card K ^ (2 * r ^ 2 + r) := by
  rw [card_statedSp]
  have h : ∀ m : ℕ, ∏ j ∈ Finset.Icc 1 m, (Nat.card K ^ (2 * j) - 1) ≤
      Nat.card K ^ (m * (m + 1)) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.prod_Icc_succ_top (by omega)]
      calc (∏ j ∈ Finset.Icc 1 m, (Nat.card K ^ (2 * j) - 1)) *
            (Nat.card K ^ (2 * (m + 1)) - 1)
          ≤ Nat.card K ^ (m * (m + 1)) * Nat.card K ^ (2 * (m + 1)) :=
            Nat.mul_le_mul ih (Nat.sub_le _ _)
        _ = Nat.card K ^ ((m + 1) * (m + 1 + 1)) := by
            rw [← pow_add]
            congr 1
            ring
  calc Nat.card K ^ (r ^ 2) * ∏ j ∈ Finset.Icc 1 r, (Nat.card K ^ (2 * j) - 1)
      ≤ Nat.card K ^ (r ^ 2) * Nat.card K ^ (r * (r + 1)) := Nat.mul_le_mul_left _ (h r)
    _ = Nat.card K ^ (2 * r ^ 2 + r) := by
      rw [← pow_add]
      congr 1
      ring

theorem scalar_mem_gsp {K : Type} [Field K] {r : ℕ} (c : Kˣ) :
    Matrix.GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c ∈ gsp r K := by
  refine ⟨c * c, ?_⟩
  have hs : ((Matrix.GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = (c : K) • (1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) := by
    ext i j
    simp [Matrix.GeneralLinearGroup.scalar, Matrix.scalar_apply, Matrix.diagonal_apply,
      Matrix.one_apply]
  rw [hs, Matrix.transpose_smul, Matrix.transpose_one, Matrix.smul_mul, Matrix.one_mul,
    Matrix.mul_smul, Matrix.mul_one, smul_smul, Units.val_mul]

theorem conjAut_scalar_sp {K : Type} [Field K] {r : ℕ} (c : Kˣ) :
    conjAut r K ⟨Matrix.GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c, scalar_mem_gsp c⟩ = 1 := by
  ext x
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  show conjAut r K _ (proj r K g) = proj r K g
  rw [conjAut_proj]
  congr 1
  apply Subtype.ext
  rw [coe_conjSp]
  have hc : Matrix.GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c ∈
      Subgroup.center (GL (Fin r ⊕ Fin r) K) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨c, rfl⟩
  rw [(Subgroup.mem_center_iff.mp hc (g : GL (Fin r ⊕ Fin r) K)).symm, mul_assoc, mul_inv_cancel,
    mul_one]

theorem card_range_conjAut_sp_le {K : Type} [Field K] [Finite K] {r : ℕ} [NeZero r] :
    Nat.card (conjAut r K).range ≤ Nat.card (StatedSp r K) := by
  have : Fintype K := Fintype.ofFinite K
  set φ := conjAut r K
  let ι : Kˣ →* gsp r K :=
    { toFun := fun c => ⟨Matrix.GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c, scalar_mem_gsp c⟩
      map_one' := by ext1; simp
      map_mul' := fun a b => by ext1; simp }
  have hι : Function.Injective ι := by
    intro a b h
    have h1 := congrArg (fun A : gsp r K =>
      ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)
        (Sum.inl ⟨0, Nat.pos_of_ne_zero (NeZero.ne r)⟩)
        (Sum.inl ⟨0, Nat.pos_of_ne_zero (NeZero.ne r)⟩)) h
    simp [ι, Matrix.GeneralLinearGroup.scalar] at h1
    exact Units.ext h1
  have hιker : ι.range ≤ φ.ker := by
    rintro _ ⟨c, rfl⟩
    exact conjAut_scalar_sp c
  have hcard_ι : Nat.card ι.range = Nat.card Kˣ :=
    (Nat.card_congr (MonoidHom.ofInjective hι).toEquiv).symm
  have hgsp : Nat.card (gsp r K) ≤ Nat.card (StatedSp r K) * Nat.card Kˣ := by
    have h1 := Subgroup.card_mul_index (multiplier r K).ker
    rw [Subgroup.index_ker, ker_multiplier] at h1
    have h2 : Nat.card ((StatedSp r K).subgroupOf (gsp r K)) = Nat.card (StatedSp r K) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe statedSp_le_gsp).toEquiv
    rw [← h1, h2]
    exact Nat.mul_le_mul_left _ (Subgroup.card_le_card_group _)
  have h3 := Subgroup.card_mul_index φ.ker
  rw [Subgroup.index_ker] at h3
  have h4 : Nat.card Kˣ ≤ Nat.card φ.ker := by
    rw [← hcard_ι]
    exact Subgroup.card_le_of_le hιker
  have hpos : 0 < Nat.card Kˣ := Nat.card_pos
  have h5 : Nat.card φ.range * Nat.card Kˣ ≤ Nat.card (StatedSp r K) * Nat.card Kˣ := by
    calc Nat.card φ.range * Nat.card Kˣ ≤ Nat.card φ.range * Nat.card φ.ker :=
          Nat.mul_le_mul_left _ h4
      _ = Nat.card (gsp r K) := by rw [mul_comm, h3]
      _ ≤ Nat.card (StatedSp r K) * Nat.card Kˣ := hgsp
  exact Nat.le_of_mul_le_mul_right h5 hpos

theorem card_mulAut_psp_le {K : Type} [Field K] [Finite K] {p e r : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hK : Nat.card K = p ^ e) (hr : 2 ≤ r) :
    Nat.card (MulAut (StatedProj (StatedSp r K))) ≤ p ^ (e * (2 * r ^ 2 + r)) * e := by
  have : NeZero r := ⟨by omega⟩
  have hgen : ∀ α : MulAut (StatedProj (StatedSp r K)), ∃ (A : gsp r K) (σ : K ≃+* K),
      α = conjAut r K A * fieldAut r K σ := by
    rcases (show r = 2 ∨ 3 ≤ r by omega) with rfl | h3
    · have h2K : (2 : K) ≠ 0 := by
        have : Fintype K := Fintype.ofFinite K
        have : CharP K p := charP_of_card_eq_prime_pow (by
          rw [← Nat.card_eq_fintype_card]; exact hK)
        intro h
        have h2 := (CharP.cast_eq_zero_iff K p 2).mp (by exact_mod_cast h)
        exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).mp h2)
      exact (CFSG.RankThree.PartOne.AUTSL.SpTwo.automorphism_generation_two h2K).2
    · exact (automorphism_generation h3).2
  let f : (conjAut r K).range × (K ≃+* K) → MulAut (StatedProj (StatedSp r K)) :=
    fun x => (x.1 : MulAut _) * fieldAut r K x.2
  have hf : Function.Surjective f := by
    intro α
    obtain ⟨A, σ, rfl⟩ := hgen α
    exact ⟨(⟨conjAut r K A, A, rfl⟩, σ), rfl⟩
  have hfin : Finite ((conjAut r K).range × (K ≃+* K)) := by
    have : Finite (K ≃+* K) :=
      Finite.of_injective (fun σ : K ≃+* K => (σ : K → K)) (fun a b h => RingEquiv.ext (congrFun h))
    infer_instance
  have h1 := Nat.card_le_card_of_surjective f hf
  rw [Nat.card_prod] at h1
  have hAut : Nat.card (K ≃+* K) = e := (card_ringAut_and_isCyclic (Fact.out : p.Prime) K hK).1
  calc Nat.card (MulAut (StatedProj (StatedSp r K)))
      ≤ Nat.card (conjAut r K).range * Nat.card (K ≃+* K) := h1
    _ ≤ Nat.card (StatedSp r K) * e := by
        rw [hAut]
        exact Nat.mul_le_mul_right _ card_range_conjAut_sp_le
    _ ≤ Nat.card K ^ (2 * r ^ 2 + r) * e := Nat.mul_le_mul_right _ (card_statedSp_le r)
    _ = p ^ (e * (2 * r ^ 2 + r)) * e := by rw [hK, ← pow_mul]

theorem card_sup_le_of_pspn {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w * w = 1)
    {K : Type} [Field K] [Finite K] {p e r : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ e) (hr : 2 ≤ r) {L E : Subgroup (MulAut W)}
    (hirr : CFSG.QuasithinUnique.Setup.X1.IsIrrOn L) (hcenter : Subgroup.center ↥L = ⊥)
    (θ : ↥L ≃* StatedProj (StatedSp r K))
    (hE : E ≤ Subgroup.normalizer (L : Set (MulAut W))) (hEel : CFSG.Quasithin.IsElemAbelian2 E) :
    Nat.card ↥(L ⊔ E) ≤ p ^ (e * (2 * r ^ 2 + r)) * e := by
  have hHn : L ⊔ E ≤ Subgroup.normalizer (L : Set (MulAut W)) :=
    sup_le Subgroup.le_normalizer hE
  have hNnormal : (L.subgroupOf (L ⊔ E)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2 hHn
  have hC := CFSG.QuasithinUnique.Setup.Family.centralizer_trivial hW hirr.2 hcenter hE hEel
  let ψ : ↥(L ⊔ E) →* MulAut ↥(L.subgroupOf (L ⊔ E)) := MulAut.conjNormal
  have hψ : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    apply hC z
    intro n hn
    have h1 := congrArg Subtype.val (DFunLike.congr_fun (MonoidHom.mem_ker.mp hz) ⟨n, hn⟩)
    simp only [MulAut.one_apply] at h1
    have h2 : z * n * z⁻¹ = n := by
      have := h1
      simpa [ψ, MulAut.conjNormal_apply] using this
    calc z * n = z * n * z⁻¹ * z := by group
      _ = n * z := by rw [h2]
  let θ' : ↥(L.subgroupOf (L ⊔ E)) ≃* StatedProj (StatedSp r K) :=
    (Subgroup.subgroupOfEquivOfLe (le_sup_left : L ≤ L ⊔ E)).trans θ
  have hfin : Finite (MulAut (StatedProj (StatedSp r K))) := by
    have : Finite ↥L := inferInstance
    have : Finite (StatedProj (StatedSp r K)) := Finite.of_equiv _ θ.toEquiv
    infer_instance
  calc Nat.card ↥(L ⊔ E) ≤ Nat.card (MulAut ↥(L.subgroupOf (L ⊔ E))) :=
        Nat.card_le_card_of_injective _ hψ
    _ = Nat.card (MulAut (StatedProj (StatedSp r K))) :=
        Nat.card_congr (MulAut.congr θ').toEquiv
    _ ≤ p ^ (e * (2 * r ^ 2 + r)) * e := card_mulAut_psp_le hp2 hK hr

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd
