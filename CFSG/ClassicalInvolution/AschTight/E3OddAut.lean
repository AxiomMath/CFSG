module

public import CFSG.ClassicalInvolution.AschTight.CSM

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open scoped MatrixGroups

theorem mem_center_of_commutator_mem_center {L : Type} [Group L] [Group.IsPerfect L] {x : L}
    (h : ∀ y : L, y * x * y⁻¹ * x⁻¹ ∈ Subgroup.center L) : x ∈ Subgroup.center L := by
  let _ : CommGroup (Subgroup.center L) :=
    { (inferInstance : Group (Subgroup.center L)) with
      mul_comm := fun a b => Subtype.ext (Subgroup.mem_center_iff.mp b.2 a) }
  let φ : L →* Subgroup.center L :=
    { toFun := fun y => ⟨y * x * y⁻¹ * x⁻¹, h y⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun y y' => by
        apply Subtype.ext
        change y * y' * x * (y * y')⁻¹ * x⁻¹ = (y * x * y⁻¹ * x⁻¹) * (y' * x * y'⁻¹ * x⁻¹)
        rw [commutator_mul (Subgroup.mem_center_iff.mp (h y') y)]
        exact Subgroup.mem_center_iff.mp (h y) _ }
  rw [Subgroup.mem_center_iff]
  intro y
  have h1 : y * x * y⁻¹ * x⁻¹ = 1 := congrArg Subtype.val (eq_one_of_perfect φ y)
  calc y * x = y * x * y⁻¹ * x⁻¹ * (x * y) := by group
    _ = x * y := by rw [h1, one_mul]

theorem map_mem_center_of_mulEquiv {L M : Type*} [Group L] [Group M] (e : L ≃* M) {x : L}
    (hx : x ∈ Subgroup.center L) : e x ∈ Subgroup.center M := by
  rw [Subgroup.mem_center_iff] at hx ⊢
  intro y
  obtain ⟨y, rfl⟩ := e.surjective y
  rw [← map_mul, ← map_mul, hx y]

section PSL2

variable {L : Type} [Group L] {F : Type} [Field F]

@[expose] def psl2Quotient (e : L ⧸ classicalInvolutionOddCore L ≃* SL(2, F)) : L →* PSL(2, F) :=
  (QuotientGroup.mk' (Subgroup.center SL(2, F))).comp
    (e.toMonoidHom.comp (QuotientGroup.mk' (classicalInvolutionOddCore L)))

theorem psl2Quotient_surjective (e : L ⧸ classicalInvolutionOddCore L ≃* SL(2, F)) :
    Function.Surjective (psl2Quotient e) :=
  (QuotientGroup.mk'_surjective _).comp
    (e.surjective.comp (QuotientGroup.mk'_surjective _))

theorem ker_psl2Quotient_eq_center [Group.IsPerfect L]
    (e : L ⧸ classicalInvolutionOddCore L ≃* SL(2, F))
    (hP1 : classicalInvolutionOddCore L ≤ Subgroup.center L) :
    (psl2Quotient e).ker = Subgroup.center L := by
  apply le_antisymm
  · intro x hx
    have hx1 : e (QuotientGroup.mk x) ∈ Subgroup.center SL(2, F) :=
      (QuotientGroup.eq_one_iff _).mp hx
    have hx2 : (QuotientGroup.mk x : L ⧸ classicalInvolutionOddCore L) ∈
        Subgroup.center (L ⧸ classicalInvolutionOddCore L) := by
      have := map_mem_center_of_mulEquiv e.symm hx1
      simpa using this
    refine mem_center_of_commutator_mem_center fun y => hP1 ?_
    have h := Subgroup.mem_center_iff.mp hx2 (QuotientGroup.mk y⁻¹)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at h
    have hconj := (classicalInvolutionOddCore_normal L).conj_mem _ h x
    have e1 : x * ((y⁻¹ * x)⁻¹ * (x * y⁻¹)) * x⁻¹ = y * x * y⁻¹ * x⁻¹ := by group
    rwa [e1] at hconj
  · intro x hx
    rw [MonoidHom.mem_ker]
    apply (QuotientGroup.eq_one_iff _).mpr
    apply map_mem_center_of_mulEquiv e
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
    rw [QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
      Subgroup.mem_center_iff.mp hx y]

@[expose] noncomputable def centerQuotientEquivPSL2 [Group.IsPerfect L]
    (e : L ⧸ classicalInvolutionOddCore L ≃* SL(2, F))
    (hP1 : classicalInvolutionOddCore L ≤ Subgroup.center L) :
    L ⧸ Subgroup.center L ≃* PSL(2, F) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_psl2Quotient_eq_center e hP1).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (psl2Quotient_surjective e))

end PSL2

section Conj

variable {G : Type} [Group G]

@[expose] def normalizerConj (K : Subgroup G) : Subgroup.normalizer (K : Set G) →* MulAut K where
  toFun n :=
    { toFun := fun k => ⟨n * k * (n : G)⁻¹, (Subgroup.mem_normalizer_iff.mp n.2 k).mp k.2⟩
      invFun := fun k => ⟨(n : G)⁻¹ * k * n, by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ n.2) k).mp k.2
        simpa using this⟩
      left_inv := fun k => Subtype.ext (by simp [mul_assoc])
      right_inv := fun k => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun k k' => Subtype.ext (by simp [mul_assoc]) }
  map_one' := by
    ext k
    simp
  map_mul' n n' := by
    ext k
    simp [mul_assoc]

theorem normalizerConj_apply_coe (K : Subgroup G) (n : Subgroup.normalizer (K : Set G))
    (k : K) : ((normalizerConj K n k : K) : G) = n * k * (n : G)⁻¹ :=
  rfl

@[expose] def centerQuotientAut (L : Type) [Group L] :
    MulAut L →* MulAut (L ⧸ Subgroup.center L) where
  toFun α := QuotientGroup.congr (Subgroup.center L) (Subgroup.center L) α
    (Subgroup.characteristic_iff_map_eq.mp inferInstance α)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on
    rfl
  map_mul' α β := by
    ext x
    induction x using QuotientGroup.induction_on
    rfl

theorem centerQuotientAut_mk (L : Type) [Group L] (α : MulAut L) (x : L) :
    centerQuotientAut L α (QuotientGroup.mk x) = QuotientGroup.mk (α x) :=
  rfl

end Conj

section Action

variable {G : Type} [Group G] {K : Subgroup G} {F : Type} [Field F] [Finite F]

@[expose] noncomputable def normalizerToPGammaL2 [Group.IsPerfect K]
    (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, F))
    (hP1 : classicalInvolutionOddCore K ≤ Subgroup.center K) {p f : ℕ} [Fact p.Prime]
    (hFcard : Nat.card F = p ^ f) (hF : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card F))
    (h3 : 3 < Nat.card F) :
    Subgroup.normalizer (K : Set G) →* CFSG.GorensteinWalter.PGammaL2 F :=
  (MulEquiv.ofBijective (CFSG.GorensteinWalter.pGammaL2ToMulAutPSL2 F hF h3)
      ⟨CFSG.GorensteinWalter.pGammaL2ToMulAutPSL2_injective F hF h3,
        CFSG.GorensteinWalter.pGammaL2ToMulAutPSL2_surjective F hFcard hF h3⟩).symm.toMonoidHom.comp
    ((MulAut.congr (centerQuotientEquivPSL2 e hP1)).toMonoidHom.comp
      ((centerQuotientAut K).comp (normalizerConj K)))

theorem commute_of_normalizerToPGammaL2_eq_one [Group.IsPerfect K]
    (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, F))
    (hP1 : classicalInvolutionOddCore K ≤ Subgroup.center K) {p f : ℕ} [Fact p.Prime]
    (hFcard : Nat.card F = p ^ f) (hF : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card F))
    (h3 : 3 < Nat.card F) {n : Subgroup.normalizer (K : Set G)}
    (hn : normalizerToPGammaL2 e hP1 hFcard hF h3 n = 1) : ∀ k ∈ K, k * (n : G) = n * k := by
  have h1 : centerQuotientAut K (normalizerConj K n) = 1 := by
    have h2 := congrArg (MulEquiv.ofBijective (CFSG.GorensteinWalter.pGammaL2ToMulAutPSL2 F hF h3)
      ⟨CFSG.GorensteinWalter.pGammaL2ToMulAutPSL2_injective F hF h3,
        CFSG.GorensteinWalter.pGammaL2ToMulAutPSL2_surjective F hFcard hF h3⟩) hn
    simp only [normalizerToPGammaL2, MonoidHom.coe_comp, Function.comp_apply,
      MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply, map_one] at h2
    exact (MulAut.congr (centerQuotientEquivPSL2 e hP1)).injective (by rw [h2, map_one])
  have hc : ∀ k : K, (normalizerConj K n k)⁻¹ * k ∈ Subgroup.center K := by
    intro k
    have h3 := congrArg (fun α : MulAut (K ⧸ Subgroup.center K) => α (QuotientGroup.mk k)) h1
    simp only [centerQuotientAut_mk, MulAut.one_apply] at h3
    exact QuotientGroup.eq.mp h3
  have hK := commute_of_commutator_mem_center (inferInstance : Group.IsPerfect K) n.2
    (t := n) fun k hk => by
      have h4 := hc ⟨k, hk⟩⁻¹
      refine ⟨⟨k * n * k⁻¹ * (n : G)⁻¹, commutator_mem_of_mem_normalizer n.2 hk⟩, ?_, rfl⟩
      have e1 : (⟨k * n * k⁻¹ * (n : G)⁻¹, commutator_mem_of_mem_normalizer n.2 hk⟩ : K) =
          ((normalizerConj K n ⟨k, hk⟩⁻¹)⁻¹ * ⟨k, hk⟩⁻¹)⁻¹ := by
        apply Subtype.ext
        simp [normalizerConj_apply_coe, mul_assoc]
      rw [e1]
      exact Subgroup.inv_mem _ h4
  intro k hk
  exact hK k hk

end Action

end CFSG.ClassicalInvolution.Disconnected.AschTight
