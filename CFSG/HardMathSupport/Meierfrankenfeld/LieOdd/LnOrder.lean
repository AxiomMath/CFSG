module

public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.OuterBound
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration
public import CFSG.LocalAnalysis.ComponentInitial.DiagonalSemilinear

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem card_GL_le {K : Type} [Field K] [Finite K] {q : ℕ} (hK : Nat.card K = q) (n : ℕ)
    (hn : 1 ≤ n) :
    Nat.card (Matrix.GeneralLinearGroup (Fin n) K) ≤ q ^ (n ^ 2 - 1) * (q - 1) := by
  have : Fintype K := Fintype.ofFinite K
  have h := Matrix.card_GL_field (𝔽 := K) n
  rw [← Nat.card_eq_fintype_card, hK] at h
  rw [h]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Fin.prod_univ_castSucc]
  have h1 : ∏ i : Fin m, (q ^ (m + 1) - q ^ (Fin.castSucc i : ℕ)) ≤ (q ^ (m + 1)) ^ m := by
    calc ∏ i : Fin m, (q ^ (m + 1) - q ^ (Fin.castSucc i : ℕ))
        ≤ ∏ _i : Fin m, q ^ (m + 1) := Finset.prod_le_prod fun i _ => Nat.sub_le _ _
      _ = (q ^ (m + 1)) ^ m := by simp
  have h2 : q ^ (m + 1) - q ^ ((Fin.last m : Fin (m + 1)) : ℕ) = q ^ m * (q - 1) := by
    rw [Fin.val_last, pow_succ, Nat.mul_sub, mul_one, mul_comm]
  rw [h2]
  calc (∏ i : Fin m, (q ^ (m + 1) - q ^ (Fin.castSucc i : ℕ))) * (q ^ m * (q - 1))
      ≤ (q ^ (m + 1)) ^ m * (q ^ m * (q - 1)) := Nat.mul_le_mul_right _ h1
    _ = q ^ ((m + 1) ^ 2 - 1) * (q - 1) := by
      rw [← pow_mul, ← mul_assoc, ← pow_add]
      congr 2
      have h3 : (m + 1) ^ 2 = (m + 1) * m + m + 1 := by ring
      omega


theorem conjAut_scalar {K : Type} [Field K] {n : ℕ} (c : Kˣ) :
    conjAut n K (Matrix.GeneralLinearGroup.scalar (Fin n) c) = 1 := by
  ext x
  obtain ⟨g, rfl⟩ := proj_surjective n K x
  show conjAut n K _ (proj n K g) = proj n K g
  rw [conjAut_proj]
  congr 1
  apply Subtype.ext
  rw [coe_slConjugation]
  have hinv : (Matrix.GeneralLinearGroup.scalar (Fin n) c)⁻¹ =
      Matrix.GeneralLinearGroup.scalar (Fin n) c⁻¹ := (map_inv _ c).symm
  rw [hinv, Matrix.GeneralLinearGroup.coe_scalar, Matrix.GeneralLinearGroup.coe_scalar,
    (Matrix.scalar_commute (c : K) (fun _ => Commute.all _ _) (g : Matrix (Fin n) (Fin n) K)).eq,
    mul_assoc, ← map_mul]
  simp


theorem card_range_conjAut_le {K : Type} [Field K] [Finite K] {q : ℕ} (hK : Nat.card K = q)
    {n : ℕ} (hn : 1 ≤ n) : Nat.card (conjAut n K).range ≤ q ^ (n ^ 2 - 1) := by
  set ρ := conjAut n K with hρ
  have hq : 2 ≤ q := hK ▸ Nat.succ_le_of_lt (Finite.one_lt_card (α := K))
  have hinj : Function.Injective (Matrix.GeneralLinearGroup.scalar (Fin n) :
      Kˣ → Matrix.GeneralLinearGroup (Fin n) K) := by
    intro x y hxy
    apply Units.ext
    have h := congrArg (fun A : Matrix.GeneralLinearGroup (Fin n) K =>
      ((A : Matrix (Fin n) (Fin n) K) ⟨0, hn⟩ ⟨0, hn⟩)) hxy
    simpa [Matrix.GeneralLinearGroup.coe_scalar] using h
  have hker : q - 1 ≤ Nat.card ρ.ker := by
    have h1 : Nat.card Kˣ ≤ Nat.card ρ.ker :=
      Nat.card_le_card_of_injective (fun c : Kˣ =>
        (⟨Matrix.GeneralLinearGroup.scalar (Fin n) c, conjAut_scalar c⟩ : ρ.ker))
        (fun x y h => hinj (congrArg Subtype.val h))
    rwa [Nat.card_units, hK] at h1
  have hmul := Subgroup.card_ker_mul_card_range ρ
  have hGL := card_GL_le hK n hn
  have h2 : (q - 1) * Nat.card ρ.range ≤ q ^ (n ^ 2 - 1) * (q - 1) := by
    calc (q - 1) * Nat.card ρ.range ≤ Nat.card ρ.ker * Nat.card ρ.range :=
          Nat.mul_le_mul_right _ hker
      _ = Nat.card (Matrix.GeneralLinearGroup (Fin n) K) := hmul
      _ ≤ _ := hGL
  rw [mul_comm] at h2
  exact Nat.le_of_mul_le_mul_right h2 (by omega)


theorem card_mulAut_projectiveSL_le {K : Type} [Field K] [Finite K] {p e n : ℕ}
    [Fact p.Prime] (hK : Nat.card K = p ^ e) (hn : 3 ≤ n) :
    Nat.card (MulAut (projectiveSL n K)) ≤ p ^ (e * (n ^ 2 - 1)) * e * 2 := by
  have hrange := card_range_conjAut_le (K := K) hK (n := n) (by omega)
  have hRing := (card_ringAut_and_isCyclic (Fact.out : p.Prime) K hK).1
  have : Finite (K ≃+* K) :=
    Finite.of_injective (fun σ : K ≃+* K => (σ : K → K)) DFunLike.coe_injective
  let F : (conjAut n K).range × (K ≃+* K) × Fin 2 → MulAut (projectiveSL n K) :=
    fun x => (x.1 : MulAut (projectiveSL n K)) * fieldAut n K x.2.1 * dualAut n K ^ (x.2.2 : ℕ)
  have hF : Function.Surjective F := by
    intro α
    obtain ⟨A, σ, ε, hε, hα⟩ := (automorphism_generation (K := K) hn).2 α
    exact ⟨(⟨conjAut n K A, A, rfl⟩, σ, ⟨ε, by omega⟩), hα.symm⟩
  have := Nat.card_le_card_of_surjective F hF
  rw [Nat.card_prod, Nat.card_prod, hRing, Nat.card_eq_fintype_card (α := Fin 2),
    Fintype.card_fin] at this
  calc Nat.card (MulAut (projectiveSL n K))
      ≤ Nat.card (conjAut n K).range * (e * 2) := this
    _ ≤ (p ^ e) ^ (n ^ 2 - 1) * (e * 2) := Nat.mul_le_mul_right _ (hK ▸ hrange)
    _ = p ^ (e * (n ^ 2 - 1)) * e * 2 := by rw [← pow_mul, mul_assoc]


section Kernel

open CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit CFSG.QuasithinUnique.Setup
  CFSG.QuasithinUnique.Setup.Family

variable {W : Type} [CommGroup W] {L : Subgroup (MulAut W)} {S : Type} [Group S]

theorem comm_of_psiAut_eq_one (hperf : Group.IsPerfect ↥L) (e : CQ L ≃* S) {b : MulAut W}
    (hb : b ∈ Subgroup.normalizer (L : Set (MulAut W))) (h1 : psiAut L e hb = 1) :
    ∀ x ∈ L, x * b = b * x := by
  have hcentral : ∀ x : ↥L, x⁻¹ * X1.conjAut L hb x ∈ Subgroup.center ↥L := by
    intro x
    rw [← QuotientGroup.eq]
    have h := psiAut_mk e hb x
    rw [h1, MulAut.one_apply] at h
    exact e.injective h
  let f : ↥L →* ↥(Subgroup.center ↥L) :=
    MonoidHom.mk' (fun x => ⟨x⁻¹ * X1.conjAut L hb x, hcentral x⟩) (by
      intro x y
      apply Subtype.ext
      have hz := Subgroup.mem_center_iff.1 (hcentral x) y⁻¹
      show (x * y)⁻¹ * X1.conjAut L hb (x * y) = (x⁻¹ * X1.conjAut L hb x) * (y⁻¹ * X1.conjAut L hb y)
      calc (x * y)⁻¹ * X1.conjAut L hb (x * y)
          = y⁻¹ * (x⁻¹ * X1.conjAut L hb x) * X1.conjAut L hb y := by
            rw [map_mul]; group
        _ = (x⁻¹ * X1.conjAut L hb x) * y⁻¹ * X1.conjAut L hb y := by rw [hz]
        _ = (x⁻¹ * X1.conjAut L hb x) * (y⁻¹ * X1.conjAut L hb y) := by group)
  have hfker : (⊤ : Subgroup ↥L) ≤ f.ker := by
    rw [← hperf.commutator_eq_top, commutator_def]
    refine Subgroup.commutator_le.2 fun g₁ _ g₂ _ => ?_
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2
      (Subtype.ext (Subgroup.mem_center_iff.1 (f g₁).2 (f g₂)).symm)
  intro x hx
  have h1' := f.mem_ker.1 (hfker (Subgroup.mem_top ⟨x, hx⟩))
  have h2 := congrArg (fun z : ↥(Subgroup.center ↥L) => ((z : ↥L) : MulAut W)) h1'
  simp only [Subgroup.coe_one] at h2
  have h3 : (x : MulAut W)⁻¹ * (b * x * b⁻¹) = 1 := h2
  have h5 : b * x * b⁻¹ = x := (inv_mul_eq_one.1 h3).symm
  calc x * b = (b * x * b⁻¹) * b := by rw [h5]
    _ = b * x := by group

end Kernel


section Main

open CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit CFSG.QuasithinUnique.Setup
  CFSG.QuasithinUnique.Setup.Family CFSG.Quasithin

theorem card_sup_le_of_psln {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w * w = 1)
    {K : Type} [Field K] [Finite K] {p e n : ℕ} [Fact p.Prime] (hK : Nat.card K = p ^ e)
    (hn : 3 ≤ n) {L E : Subgroup (MulAut W)} (hperf : Group.IsPerfect ↥L)
    (hirr : X1.IsIrrOn L) (eL : CQ L ≃* projectiveSL n K)
    (hE : E ≤ Subgroup.normalizer (L : Set (MulAut W))) (hEel : IsElemAbelian2 E) :
    Nat.card ↥(L ⊔ E) ≤ Nat.card (Subgroup.center ↥L) * (p ^ (e * (n ^ 2 - 1)) * e * 2) := by
  have hfinW : Finite (MulAut W) := B42Disp.finite_mulAut
  have hfinS : Finite (MulAut (projectiveSL n K)) :=
    Finite.of_injective (fun f : MulAut (projectiveSL n K) => (f : projectiveSL n K → _))
      (fun f g h => MulEquiv.ext (congrFun h))
  have hHn : L ⊔ E ≤ Subgroup.normalizer (L : Set (MulAut W)) :=
    sup_le Subgroup.le_normalizer hE
  let ψ := psiHom L eL hHn
  have hker : Nat.card ψ.ker ≤ Nat.card (Subgroup.center ↥L) := by
    have hmem : ∀ h : ψ.ker, ((h : ↥(L ⊔ E)) : MulAut W) ∈ L := by
      intro h
      have h1 : psiAut L eL (hHn (h : ↥(L ⊔ E)).2) = 1 := h.2
      have hcomm := comm_of_psiAut_eq_one hperf eL (hHn (h : ↥(L ⊔ E)).2) h1
      have hC : ((h : ↥(L ⊔ E)) : MulAut W) ∈ Subgroup.centralizer (L : Set (MulAut W)) :=
        Subgroup.mem_centralizer_iff.2 fun x hx => hcomm x hx
      exact X1.centralizer_inf_le hW hirr hE hEel ⟨(h : ↥(L ⊔ E)).2, hC⟩
    refine Nat.card_le_card_of_injective (fun h : ψ.ker => (⟨⟨((h : ↥(L ⊔ E)) : MulAut W), hmem h⟩,
      ?_⟩ : ↥(Subgroup.center ↥L))) ?_
    · rw [Subgroup.mem_center_iff]
      intro g
      have h1 : psiAut L eL (hHn (h : ↥(L ⊔ E)).2) = 1 := h.2
      exact Subtype.ext (comm_of_psiAut_eq_one hperf eL (hHn (h : ↥(L ⊔ E)).2) h1 g g.2)
    · intro a b hab
      exact Subtype.ext (Subtype.ext (congrArg (fun z : ↥(Subgroup.center ↥L) =>
        ((z : ↥L) : MulAut W)) hab))
  have hrange : Nat.card ψ.range ≤ Nat.card (MulAut (projectiveSL n K)) :=
    Subgroup.card_le_card_group _
  have hAut := card_mulAut_projectiveSL_le hK hn
  calc Nat.card ↥(L ⊔ E) = Nat.card ψ.ker * Nat.card ψ.range :=
        (Subgroup.card_ker_mul_card_range ψ).symm
    _ ≤ Nat.card (Subgroup.center ↥L) * (p ^ (e * (n ^ 2 - 1)) * e * 2) :=
        Nat.mul_le_mul hker (hrange.trans hAut)

end Main

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd
