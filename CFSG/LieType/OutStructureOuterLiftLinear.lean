module

public import CFSG.LieType.OutStructure
public import CFSG.LieType.OutStructureActionMap
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphismsCongr
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenPClosed
public import CFSG.Monster.B.TwoA.Base.ElemAut

public section

namespace CFSG.LieType.OutStructure

open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.PerfectAutomorphisms (centerQuotientHom)
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  (higher_linear_outer_order_divides_field_gcd_bound)
open scoped Pointwise

theorem OuterPElementLifts.of_mulEquiv {A B : Type} [Group A] [Finite A] [Group B] [Finite B]
    (e : A ≃* B) {p : ℕ} (h : OuterPElementLifts B p) : OuterPElementLifts A p := by
  intro y hy
  obtain ⟨k, hk⟩ := hy
  obtain ⟨α, rfl⟩ := QuotientGroup.mk'_surjective (inner A) y
  have hmk : equivalence e (QuotientGroup.mk' (inner A) α) =
      QuotientGroup.mk' (inner B) (MulAut.congr e α) :=
    QuotientGroup.congr_mk' _ _ _ _ α
  obtain ⟨f, hf, hford⟩ := h (equivalence e (QuotientGroup.mk' (inner A) α))
    ⟨k, by rw [MulEquiv.orderOf_eq, hk]⟩
  rw [hmk] at hf hford
  refine ⟨(MulAut.congr e).symm f, ?_, ?_⟩
  · rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    rw [← congr_mem_inner_iff e, map_mul, map_inv, MulEquiv.apply_symm_apply]
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hf
    exact hf
  · rw [MulEquiv.orderOf_eq, hford, ← hmk]
    exact MulEquiv.orderOf_eq _ _

theorem exists_lift_orderOf_eq_of_sylow_map {Γ A B : Type*} [Group Γ] [Group A] [Group B]
    [Finite B] {p : ℕ} [Fact p.Prime] (π : A →* B) (hπ : Function.Surjective π) (φ : Γ →* A)
    (hφ : Function.Injective (π.comp φ)) (S : Subgroup Γ) (hS : IsPGroup p S)
    (hidx : ¬ p ∣ (S.map (π.comp φ)).index) {y : B} (hy : ∃ k : ℕ, orderOf y = p ^ k) :
    ∃ f : A, π f = y ∧ orderOf f = orderOf y := by
  classical
  obtain ⟨k, hk⟩ := hy
  let P : Sylow p B := (hS.map (π.comp φ)).toSylow hidx
  have hY : IsPGroup p (Subgroup.zpowers y) :=
    IsPGroup.of_card (by rw [Nat.card_zpowers, hk])
  obtain ⟨Q, hQ⟩ := hY.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq B P Q
  have hyQ : y ∈ MulAut.conj g • (P : Subgroup B) := by
    rw [← Sylow.coe_subgroup_smul, hg]
    exact hQ (Subgroup.mem_zpowers y)
  obtain ⟨s, hsP, hs⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).mp hyQ
  obtain ⟨σ, -, rfl⟩ := Subgroup.mem_map.mp ((IsPGroup.mem_toSylow _ _).mp hsP)
  obtain ⟨g', rfl⟩ := hπ g
  have hφ' : Function.Injective φ := Function.Injective.of_comp hφ
  refine ⟨g' * φ σ * g'⁻¹, ?_, ?_⟩
  · rw [← hs, map_mul, map_mul, map_inv, MulAut.smul_def, MulAut.conj_apply]
    rfl
  · have h1 : orderOf (g' * φ σ * g'⁻¹) = orderOf (φ σ) :=
      (MulAut.conj g').orderOf_eq (φ σ)
    have h2 : orderOf y = orderOf ((π.comp φ) σ) := by
      rw [← hs, MulAut.smul_def, MulEquiv.orderOf_eq]
    rw [h1, h2, orderOf_injective _ hφ σ, orderOf_injective _ hφ' σ]

theorem outerPElementLifts_projectiveSL_of_not_dvd (N : ℕ) (K : Type) [Field K] [Finite K]
    (hN : 3 ≤ N) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hdiv : ¬ p ∣ Nat.gcd N (Nat.card K - 1)) :
    OuterPElementLifts (projectiveSL N K) p := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨e, hq, hKcard⟩ := FiniteField.card K (ringChar K)
  have hKcard' : Nat.card K = ringChar K ^ (e : ℕ) := by
    rw [Nat.card_eq_fintype_card]
    exact hKcard
  obtain ⟨-, -, -, -, hfcard, -⟩ :=
    finite_field_automorphism_fixed_field_cardinality hq e.pos hKcard'
  have : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hfcard]; exact e.pos.ne')
  have hψ : Function.Injective
      ((QuotientGroup.mk' (inner (projectiveSL N K))).comp (fieldAut N K)) := by
    rw [injective_iff_map_eq_one]
    intro σ hσ
    have hI : fieldAut N K σ ∈ inner (projectiveSL N K) := (QuotientGroup.eq_one_iff _).mp hσ
    have hI' : fieldAut N K σ ∈ linearAutGroup N K :=
      (standard_outer_quotients (n := N) (K := K)).1 hI
    rw [linearAutGroup_eq_range] at hI'
    obtain ⟨A, hA⟩ := hI'
    have h1 : conjAut N K A * fieldAut N K σ⁻¹ = 1 := by
      rw [map_inv, ← hA, mul_inv_cancel]
    exact inv_eq_one.mp (eq_one_of_conjAut_mul_fieldAut_eq_one (n := N) hN A σ⁻¹ h1).1
  let S : Sylow p (K ≃+* K) := default
  have hidx : ¬ p ∣ ((S : Subgroup (K ≃+* K)).map
      ((QuotientGroup.mk' (inner (projectiveSL N K))).comp (fieldAut N K))).index := by
    intro hpd
    have hcard : Nat.card (Outer (projectiveSL N K)) =
        ((S : Subgroup (K ≃+* K)).map
          ((QuotientGroup.mk' (inner (projectiveSL N K))).comp (fieldAut N K))).index *
          p ^ (e : ℕ).factorization p := by
      rw [← Subgroup.index_mul_card, Subgroup.card_map_of_injective hψ,
        Sylow.card_eq_multiplicity S, hfcard]
    have hOut : Nat.card (Outer (projectiveSL N K)) ∣
        2 * (e : ℕ) * Nat.gcd N (ringChar K ^ (e : ℕ) - 1) :=
      higher_linear_outer_order_divides_field_gcd_bound hq e.pos hN hKcard'
    have h1 : p ^ ((e : ℕ).factorization p + 1) ∣
        (e : ℕ) * (2 * Nat.gcd N (ringChar K ^ (e : ℕ) - 1)) := by
      rw [mul_comm 2, mul_assoc] at hOut
      refine dvd_trans ?_ (hOut.trans (by rw [mul_comm]))
      rw [hcard, pow_succ, mul_comm (p ^ _) p]
      exact Nat.mul_dvd_mul_right hpd _
    have hnd : ¬ p ∣ 2 * Nat.gcd N (ringChar K ^ (e : ℕ) - 1) := by
      intro h
      rcases hp.dvd_mul.mp h with h2 | h2
      · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
      · rw [hKcard'] at hdiv
        exact hdiv h2
    have hcop : Nat.Coprime (p ^ ((e : ℕ).factorization p + 1))
        (2 * Nat.gcd N (ringChar K ^ (e : ℕ) - 1)) :=
      Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr hnd)
    exact Nat.pow_succ_factorization_not_dvd e.pos.ne' hp (hcop.dvd_of_dvd_mul_right h1)
  intro y hy
  exact exists_lift_orderOf_eq_of_sylow_map (QuotientGroup.mk' (inner (projectiveSL N K)))
    (QuotientGroup.mk'_surjective _) (fieldAut N K) hψ (S : Subgroup (K ≃+* K)) S.isPGroup'
    hidx hy

theorem exists_orderOf_eq_not_mem_of_outerPElementLifts {X : Type} [Group X] [Finite X]
    {L : Subgroup X} (hL : CFSG.IsComponent L) (hLn : L.Normal) {p : ℕ} (hp : p.Prime)
    (hlift : OuterPElementLifts (↥L ⧸ Subgroup.center ↥L) p)
    (hC : ¬ p ∣ Nat.card (Subgroup.centralizer (L : Set X)))
    (hnot : ¬ CFSG.LocalAnalysis.RankThreeUC.AGL81C.IsPClosedMod p
        (L ⊔ Subgroup.centralizer (L : Set X))) :
    ∃ x : X, orderOf x = p ∧ x ∉ L ⊔ Subgroup.centralizer (L : Set X) := by
  classical
  have : L.Normal := hLn
  have : Fact p.Prime := ⟨hp⟩
  have hdvd : p ∣ (L ⊔ Subgroup.centralizer (L : Set X)).index := by
    by_contra h
    exact hnot ⟨L ⊔ Subgroup.centralizer (L : Set X), inferInstance, le_rfl,
      ⟨0, by rw [Subgroup.relIndex_self, pow_zero]⟩, h⟩
  rw [Subgroup.index_eq_card] at hdvd
  obtain ⟨q, hq⟩ := exists_prime_orderOf_dvd_card'
    (G := X ⧸ (L ⊔ Subgroup.centralizer (L : Set X))) p hdvd
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (L ⊔ Subgroup.centralizer (L : Set X)) q
  have hyord : orderOf (conjOuterHom (L := L) y) = p := by
    rw [← conjQuotientHom_apply, orderOf_injective _ (conjHom_range_le_outer hL)]
    exact hq
  obtain ⟨f, hf, hford⟩ := hlift (conjOuterHom (L := L) y) ⟨1, by rw [hyord, pow_one]⟩
  have hfy : f⁻¹ * conjHom (L := L) y ∈ inner (↥L ⧸ Subgroup.center ↥L) := by
    have h := hf.trans (conjOuterHom_apply (L := L) y)
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h
    exact h
  have hconj : ∀ z : L, conjHom (L := L) (z : X) =
      MulAut.conj (QuotientGroup.mk' (Subgroup.center ↥L) z) := by
    intro z
    change centerQuotientHom ↥L (MulAut.conjNormal (H := L) (z : X)) = _
    rw [MulAut.conjNormal_val (H := L) (h := z)]
    exact centerQuotient_conj z
  obtain ⟨s, hs⟩ := hfy
  obtain ⟨z, hz⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥L) s⁻¹
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : X, conjHom (L := L) x₀ = f := by
    refine ⟨y * (z : X), ?_⟩
    rw [map_mul, hconj z, hz, map_inv, hs]
    group
  have hfp : orderOf f = p := by rw [hford, hyord]
  have hx₀p : x₀ ^ p ∈ Subgroup.centralizer (L : Set X) := by
    rw [← mem_ker_conjHom_iff hL, map_pow, hx₀, ← hfp, pow_orderOf_eq_one]
  have hpn : p ∣ orderOf x₀ := by
    have h := orderOf_map_dvd (conjHom (L := L)) x₀
    rwa [hx₀, hfp] at h
  have hn0 : orderOf x₀ ≠ 0 := (orderOf_pos x₀).ne'
  have hpm : ¬ p ∣ orderOf x₀ / p := by
    have hm : orderOf (x₀ ^ p) = orderOf x₀ / p := orderOf_pow_of_dvd hp.ne_zero hpn
    rw [← hm]
    exact fun h => hC (h.trans (Subgroup.orderOf_dvd_natCard _ hx₀p))
  refine ⟨x₀ ^ (orderOf x₀ / p), orderOf_pow_orderOf_div hn0 hpn, fun hmem => ?_⟩
  have h1 : conjOuterHom (L := L) (x₀ ^ (orderOf x₀ / p)) = 1 :=
    (mem_ker_conjOuterHom_iff hL).mpr hmem
  have h2 : conjOuterHom (L := L) x₀ = conjOuterHom (L := L) y := by
    rw [conjOuterHom_apply, hx₀, hf]
  rw [map_pow, h2, ← orderOf_dvd_iff_pow_eq_one, hyord] at h1
  exact hpm h1

theorem exists_orderOf_eq_not_mem_of_projectiveSL {X : Type} [Group X] [Finite X]
    {L : Subgroup X} [L.Normal] (hL : CFSG.IsComponent L) {K : Type} [Field K] [Finite K]
    {m : ℕ} (e : (↥L ⧸ Subgroup.center ↥L) ≃* projectiveSL m K) (hm : 3 ≤ m) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hdiv : ¬ p ∣ Nat.gcd m (Nat.card K - 1))
    (hnot : ¬ CFSG.LocalAnalysis.RankThreeUC.AGL81C.IsPClosedMod p
        (L ⊔ Subgroup.centralizer (L : Set X)))
    (hc : ¬ ∃ c : X, c ∈ Subgroup.centralizer (L : Set X) ∧ orderOf c = p) :
    ∃ x : X, orderOf x = p ∧ x ∉ L ⊔ Subgroup.centralizer (L : Set X) := by
  have : Fact p.Prime := ⟨hp⟩
  have hC : ¬ p ∣ Nat.card (Subgroup.centralizer (L : Set X)) := by
    intro hd
    obtain ⟨c, hcp⟩ := exists_prime_orderOf_dvd_card'
      (G := Subgroup.centralizer (L : Set X)) p hd
    exact hc ⟨c, c.2, by rw [Subgroup.orderOf_coe, hcp]⟩
  exact exists_orderOf_eq_not_mem_of_outerPElementLifts hL inferInstance hp
    (OuterPElementLifts.of_mulEquiv e
      (outerPElementLifts_projectiveSL_of_not_dvd m K hm hp hp2 hdiv)) hC hnot

end CFSG.LieType.OutStructure
