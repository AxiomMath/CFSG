module

public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
import CFSG.FeitThompson.Foundations.NormalCommuteModIntersection

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open CFSG.FeitThompson CFSG.FeitThompson Subgroup

universe u

variable {X : Type*} [Group X]

theorem isHallSubgroup_of_isHallPiSubgroup {π : Set ℕ} {H : Subgroup X}
    (h : IsHallPiSubgroup π H) : IsHallSubgroup π H :=
  ⟨isPiNumber_iff.2 (isPiSubgroup_iff.1 h.isPiSubgroup),
    isPiNumber_iff.2 fun q hq => h.notMem_of_mem_primeFactors_index q hq⟩

theorem natCard_subgroupOf {H K : Subgroup X} (h : H ≤ K) :
    Nat.card (H.subgroupOf K) = Nat.card H :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv

theorem natCard_mul_relIndex {H K : Subgroup X} (h : H ≤ K) :
    Nat.card H * H.relIndex K = Nat.card K := by
  rw [Subgroup.relIndex, ← natCard_subgroupOf h]
  exact Subgroup.card_mul_index _

theorem subgroupOf_inf_centralizer {H K : Subgroup X} (h : H ≤ K) :
    (K ⊓ centralizer (H : Set X)).subgroupOf K
      = centralizer ((H.subgroupOf K : Subgroup K) : Set K) := by
  ext x
  simp only [mem_subgroupOf, Subgroup.mem_inf, SetLike.mem_coe, mem_centralizer_iff,
    Subgroup.mem_subgroupOf]
  refine ⟨fun hx y hy => Subtype.ext (hx.2 (y : X) hy),
    fun hx => ⟨x.2, fun a ha => congrArg Subtype.val (hx (⟨a, h ha⟩ : K) ha)⟩⟩

theorem disjoint_tauTwoPrimes_tau3Primes (M : Subgroup X) :
    Disjoint (tauTwoPrimes M) (tau3Primes M) :=
  Set.disjoint_left.2 fun _ h h' => by
    have h2 := elementaryAbelianPRank_eq_two_of_mem_tauTwoPrimes h
    have h1 := elementaryAbelianPRank_eq_one_of_mem_tau3Primes h'
    omega

theorem relIndex_sup_eq_natCard_of_tauHall [Finite X] {M E E₁ E₂ E₃ : Subgroup X}
    (hE₂ : IsHallPiSubgroupOf (tauTwoPrimes M) E₂ E)
    (hE₃ : IsHallPiSubgroupOf (tau3Primes M) E₃ E)
    (hE : FreeCore.IsInternalSemidirectProduct E E₃ (E₂ ⊔ E₁))
    (hE₂₁ : FreeCore.IsInternalSemidirectProduct (E₂ ⊔ E₁) E₂ E₁) :
    (E₂ ⊔ E₃).relIndex E = Nat.card E₁ := by
  have hcop : (Nat.card ↥E₃).Coprime (Nat.card ↥E₂) := by
    refine ((isPiNumber_iff.2 (isPiSubgroup_iff.1 hE₃.isPiSubgroup)).coprime_of_compl
      (π := tau3Primes M) ?_ Nat.card_pos.ne' Nat.card_pos.ne')
    refine (isPiNumber_iff.2 (isPiSubgroup_iff.1 hE₂.isPiSubgroup)).mono ?_
    intro q hq hq'
    exact Set.disjoint_left.1 (disjoint_tauTwoPrimes_tau3Primes M) hq hq'
  have hsd : FreeCore.IsInternalSemidirectProduct (E₃ ⊔ E₂) E₃ E₂ :=
    ⟨rfl, le_trans (sup_le hE.left_le hE₂.1) hE.le_normalizer,
      Subgroup.disjoint_of_coprime_natCard hcop⟩
  have hcard32 : Nat.card ↥(E₂ ⊔ E₃) = Nat.card ↥E₃ * Nat.card ↥E₂ := by
    rw [sup_comm]; exact hsd.natCard_eq_mul
  have hcardE : Nat.card ↥E = Nat.card ↥E₃ * (Nat.card ↥E₂ * Nat.card ↥E₁) := by
    rw [hE.natCard_eq_mul, hE₂₁.natCard_eq_mul]
  have hkey := natCard_mul_relIndex (sup_le hE₂.1 hE₃.1 : E₂ ⊔ E₃ ≤ E)
  rw [hcard32, hcardE, mul_assoc] at hkey
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos
    (Nat.eq_of_mul_eq_mul_left Nat.card_pos hkey)

theorem sigma_complement_plane_action_support
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_tau_two_hall_abelian.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_complement_normalizer.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_sylow.{u})
    {G : Type u} [Group G] [Finite G] (hG : IsOddOrderMinimalSimple G)
    {M : Subgroup G} (hM : IsCoatom M) {p : ℕ} (hp : p.Prime) (hpσ : p ∉ sigmaPrimes M)
    {A : Subgroup G} (hAM : A ≤ M)
    (hplane : _root_.CFSG.FeitThompson.IsElementaryAbelianPlane p A)
    {E : Subgroup G} (hsemi : FreeCore.IsInternalSemidirectProduct M (sigmaCore M) E)
    (hAE : A ≤ E) {E₁ E₂ E₃ : Subgroup G}
    (hE₁ : IsHallPiSubgroupOf (tau1Primes M) E₁ E)
    (hE₂ : IsHallPiSubgroupOf (tauTwoPrimes M) E₂ E)
    (hE₃ : IsHallPiSubgroupOf (tau3Primes M) E₃ E)
    (hE : FreeCore.IsInternalSemidirectProduct E E₃ (E₂ ⊔ E₁))
    (hE₂₁ : FreeCore.IsInternalSemidirectProduct (E₂ ⊔ E₁) E₂ E₁) :
    (E₂ ⊔ E₃) ≤ E ⊓ centralizer (A : Set G) ∧
      ((E ⊓ centralizer (A : Set G) : Subgroup G).subgroupOf E).Normal ∧
      ∀ r ∈ ((E ⊓ centralizer (A : Set G) : Subgroup G).relIndex E).primeFactors,
        r ∈ tau1Primes M := by
  have hG' : _root_.CFSG.FeitThompson.IsOddSimpleMinimal G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hosp : _root_.CFSG.FeitThompson.IsOutsideSigmaPlane p M A := ⟨hM, hp, hpσ, hAM, hplane⟩
  have hsc : _root_.CFSG.FeitThompson.IsSigmaComplement M E := ⟨hM, hsemi⟩
  obtain ⟨hEnorm, -⟩ := h₂ G hG' p M A E hosp hsc hAE
  have hrank : elementaryAbelianPRank p ↥M = 2 := (h₃ G hG' p M A hosp).1
  have hpτ₂ : p ∈ tauTwoPrimes M := mem_tauTwoPrimes_iff.2 ⟨hp, hpσ, hrank⟩
  have hAcard : Nat.card ↥A = p ^ 2 :=
    _root_.CFSG.FeitThompson.IsElementaryAbelianPlane.natCard' hplane
  have hAnormal : (A.subgroupOf E).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hEnorm
  have hE₃normal : (E₃.subgroupOf E).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hE.le_normalizer
  have hπA : IsPiNumber (tauTwoPrimes M) (Nat.card ↥(A.subgroupOf E)) := by
    rw [natCard_subgroupOf hAE, hAcard]
    refine isPiNumber_iff.2 fun q hq => ?_
    rw [Nat.primeFactors_pow _ two_ne_zero, hp.primeFactors, Finset.mem_singleton] at hq
    exact hq ▸ hpτ₂
  have hAE₂ : A ≤ E₂ := by
    have := hAnormal
    have h := IsHallSubgroup.normal_le (π := tauTwoPrimes M)
      (N := A.subgroupOf E) (H := E₂.subgroupOf E) hπA
      (isHallSubgroup_of_isHallPiSubgroup hE₂.2)
    exact fun x hx => h (show (⟨x, hAE hx⟩ : ↥E) ∈ A.subgroupOf E from hx)
  have hE₂ab : IsMulCommutative ↥E₂ :=
    @h₁ G _ (Fintype.ofFinite G) hG M hM E hsemi E₂ hE₂
  have hE₂C : E₂ ≤ centralizer (A : Set G) := fun x hx =>
    mem_centralizer_iff.2 fun a ha =>
      congrArg Subtype.val (hE₂ab.is_comm.comm (⟨a, hAE₂ ha⟩ : ↥E₂) ⟨x, hx⟩)
  have hE₃C : E₃ ≤ centralizer (A : Set G) := by
    have hcop : (Nat.card ↥(A.subgroupOf E)).Coprime (Nat.card ↥(E₃.subgroupOf E)) := by
      refine hπA.coprime_of_compl ?_ Nat.card_pos.ne' Nat.card_pos.ne'
      rw [natCard_subgroupOf hE₃.1]
      refine (isPiNumber_iff.2 (isPiSubgroup_iff.1 hE₃.isPiSubgroup)).mono ?_
      intro q hq hq'
      exact Set.disjoint_left.1 (disjoint_tauTwoPrimes_tau3Primes M) hq' hq
    have := hAnormal
    have := hE₃normal
    intro x hx
    refine mem_centralizer_iff.2 fun a ha => ?_
    exact congrArg Subtype.val
      (mul_comm_of_normal_of_coprime_natCard (A.subgroupOf E) (E₃.subgroupOf E) hcop
        (a := (⟨a, hAE ha⟩ : ↥E)) (b := (⟨x, hE₃.1 hx⟩ : ↥E)) ha hx)
  have hsupC : E₂ ⊔ E₃ ≤ E ⊓ centralizer (A : Set G) :=
    sup_le (le_inf hE₂.1 hE₂C) (le_inf hE₃.1 hE₃C)
  refine ⟨hsupC, ?_, ?_⟩
  ·
    have := hAnormal
    rw [subgroupOf_inf_centralizer hAE]
    infer_instance
  ·
    intro r hr
    have hdvd : (E ⊓ centralizer (A : Set G) : Subgroup G).relIndex E ∣ Nat.card ↥E₁ := by
      rw [← relIndex_sup_eq_natCard_of_tauHall hE₂ hE₃ hE hE₂₁]
      exact Dvd.intro_left _
        (Subgroup.relIndex_mul_relIndex (E₂ ⊔ E₃) _ E hsupC inf_le_left)
    exact isPiSubgroup_iff.1 hE₁.isPiSubgroup r
      (Nat.primeFactors_mono hdvd Nat.card_pos.ne' hr)

theorem FBG_sigma_complement_plane_action_support
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_tau_two_hall_abelian.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_complement_normalizer.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_sylow.{u}) :
    _root_.CFSG.FeitThompson.Statements.FBG_sigma_complement_plane_action_support.{u} := by
  intro G _ _ hG M hM p hp hpσ A hAM hplane E hsemi hAE E₁ E₂ E₃ hE₁ hE₂ hE₃ hE hE₂₁
  exact sigma_complement_plane_action_support h₁ h₂ h₃ hG hM hp hpσ hAM hplane hsemi hAE
    hE₁ hE₂ hE₃ hE hE₂₁

end

end CFSG.FeitThompson.Proofs
