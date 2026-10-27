module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LieType.Chevalley.OddF4G2AutomorphismNormalForm
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ClassicalInvolution.Q3.Q3T

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification

section Field

variable {K : Type} [Field K] [Finite K]

theorem ringEquiv_eq_refl_of_card_three (hK : Nat.card K = 3) (σ : K ≃+* K) :
    σ = RingEquiv.refl K := by
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : CharP K 3 := charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card, hK])
  have hbij : Function.Bijective (ZMod.castHom (dvd_refl 3) K) :=
    (ZMod.castHom (dvd_refl 3) K).injective.bijective_of_nat_card_le (by rw [hK, Nat.card_zmod])
  have hσ : σ.toRingHom.comp (ZMod.castHom (dvd_refl 3) K) = ZMod.castHom (dvd_refl 3) K :=
    RingHom.ext_zmod _ _
  ext x
  obtain ⟨y, rfl⟩ := hbij.2 x
  exact congrArg (fun φ : ZMod 3 →+* K => φ y) hσ

theorem units_mul_self_of_card_three (hK : Nat.card K = 3) (u : Kˣ) : (u : K) * u = 1 := by
  have : Fintype K := Fintype.ofFinite K
  have h := FiniteField.pow_card_sub_one_eq_one (u : K) u.ne_zero
  rw [← Nat.card_eq_fintype_card, hK] at h
  rw [← pow_two]
  simpa using h

end Field

section Out

theorem mem_inner_of_odd_of_pow_four {G : Type*} [Group G] {α ρ : MulAut G} (g : G)
    (hα : α = MulAut.conj g * ρ) (hρ : ρ ^ 4 = 1) (hodd : Odd (orderOf α)) :
    α ∈ OuterAutomorphisms.inner G := by
  have h1 : (α : MulAut G ⧸ OuterAutomorphisms.inner G) = (ρ : MulAut G ⧸ _) := by
    have hg : MulAut.conj g ∈ OuterAutomorphisms.inner G := MonoidHom.mem_range.mpr ⟨g, rfl⟩
    rw [hα, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).mpr hg, one_mul]
  have h2 : (α : MulAut G ⧸ OuterAutomorphisms.inner G) ^ 4 = 1 := by
    rw [h1, ← QuotientGroup.mk_pow, hρ, QuotientGroup.mk_one]
  have h3 : (α : MulAut G ⧸ OuterAutomorphisms.inner G) ^ orderOf α = 1 := by
    rw [← QuotientGroup.mk_pow, pow_orderOf_eq_one, QuotientGroup.mk_one]
  have hcop : Nat.Coprime (orderOf α) 4 := by
    have h2' : Nat.Coprime (orderOf α) 2 := Nat.coprime_two_right.mpr hodd
    simpa using Nat.Coprime.pow_right 2 h2'
  have h4 := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h3) (orderOf_dvd_of_pow_eq_one h2)
  rw [hcop.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at h4
  exact (QuotientGroup.eq_one_iff α).mp h4

theorem exists_eq_conj_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (h : ∀ β : MulAut H, Odd (orderOf β) → β ∈ OuterAutomorphisms.inner H) (α : MulAut G)
    (hodd : Odd (orderOf α)) : ∃ g : G, α = MulAut.conj g := by
  have hβ : Odd (orderOf (MulAut.congr e α)) := by
    rwa [MulEquiv.orderOf_eq]
  obtain ⟨c, hc⟩ := h _ hβ
  refine ⟨e.symm c, (MulAut.congr e).injective ?_⟩
  rw [OuterAutomorphisms.congr_conj, MulEquiv.apply_symm_apply, hc]

end Out

section Adjoint

theorem mem_inner_of_odd_adjoint_E {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (K : Type)
    [Field K] [Finite K] (hK : Nat.card K = 3) (α : MulAut (adjointGroup τ K))
    (hodd : Odd (orderOf α)) : α ∈ OuterAutomorphisms.inner (adjointGroup τ K) := by
  obtain ⟨-, -, hnf⟩ := ordinary_E_exact_automorphism_normal_form τ hτ K
  obtain ⟨g, a, σ, ε, hform⟩ := hnf α
  obtain rfl := ringEquiv_eq_refl_of_card_three hK σ
  have hα : α = MulAut.conj g * exactNormalAut τ K a (RingEquiv.refl K) ε := by
    refine MulEquiv.ext fun h => Subtype.ext ?_
    rw [hform h, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      coe_exactNormalAut, Subgroup.coe_inv]
    simp only [mul_assoc]
  have hπ : ∀ i, exactPerm τ ε (exactPerm τ ε i) = i := by
    rcases hτ with rfl | rfl | rfl
    · have hε : (ε : ℕ) = 0 ∨ (ε : ℕ) = 1 := by
        have := ε.2
        simp only [exactE] at this
        omega
      have hsq : TwistTag.E6.perm * TwistTag.E6.perm = 1 := by decide
      intro i
      rcases hε with h | h
      · simp only [exactPerm, h, pow_zero]
        rfl
      · simp only [exactPerm, h, pow_one]
        exact DFunLike.congr_fun hsq i
    · intro i
      rfl
    · intro i
      rfl
  have hu := units_mul_self_of_card_three hK
  refine mem_inner_of_odd_of_pow_four g hα ?_ hodd
  have hpow : ∀ x, (exactNormalAut τ K a (RingEquiv.refl K) ε ^ 4) x =
      exactNormalAut τ K a (RingEquiv.refl K) ε (exactNormalAut τ K a (RingEquiv.refl K) ε
        (exactNormalAut τ K a (RingEquiv.refl K) ε
          (exactNormalAut τ K a (RingEquiv.refl K) ε x))) := fun x => rfl
  apply mulAut_ext_adjX_adjY
  · intro i c
    rw [hpow, exactNormalAut_adjX, exactNormalAut_adjX, exactNormalAut_adjX, exactNormalAut_adjX,
      MulAut.one_apply]
    simp only [RingEquiv.refl_apply, hπ]
    congr 1
    calc (a i : K) * ((a (exactPerm τ ε i) : K) * ((a i : K) * ((a (exactPerm τ ε i) : K) * c)))
        = ((a i : K) * a i) * ((a (exactPerm τ ε i) : K) * a (exactPerm τ ε i)) * c := by ring
      _ = c := by rw [hu, hu, one_mul, one_mul]
  · intro i c
    rw [hpow, exactNormalAut_adjY, exactNormalAut_adjY, exactNormalAut_adjY, exactNormalAut_adjY,
      MulAut.one_apply]
    simp only [RingEquiv.refl_apply, hπ]
    congr 1
    calc (((a i)⁻¹ : Kˣ) : K) * ((((a (exactPerm τ ε i))⁻¹ : Kˣ) : K) *
          ((((a i)⁻¹ : Kˣ) : K) * ((((a (exactPerm τ ε i))⁻¹ : Kˣ) : K) * c)))
        = ((((a i)⁻¹ : Kˣ) : K) * (((a i)⁻¹ : Kˣ) : K)) *
          ((((a (exactPerm τ ε i))⁻¹ : Kˣ) : K) * (((a (exactPerm τ ε i))⁻¹ : Kˣ) : K)) * c := by
          ring
      _ = c := by rw [hu, hu, one_mul, one_mul]

theorem mem_inner_adjoint_F4 (K : Type) [Field K] [Finite K] (hK : Nat.card K = 3)
    (α : MulAut (adjointGroup .F4 K)) : α ∈ OuterAutomorphisms.inner (adjointGroup .F4 K) := by
  obtain ⟨-, Θ, -, -, hker, -⟩ := odd_F4_and_nonexceptional_G2_automorphism_normal_form
    Nat.prime_three (by norm_num) le_rfl K (by rw [hK]; norm_num) .F4 (Or.inl rfl)
  have hΘ : Θ α = 1 := ringEquiv_eq_refl_of_card_three hK _
  have hmem : α ∈ Θ.ker := hΘ
  rw [hker] at hmem
  exact hmem

end Adjoint

end CFSG.ClassicalInvolution.Q3.Q3T
