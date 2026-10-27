module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLiePOmegaOmega
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLiePOmegaFrameData
import CFSG.ClassicalInvolution.Orders.OrthogonalIndex
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLiePslNonab

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure

open CFSG.Open CFSG.ClassicalGroups.Orthogonal Module QuadraticMap

section Abstract

variable {p : ℕ} [Fact p.Prime]

theorem eq_one_of_sq_eq_one_of_pow_eq_one (hp2 : p ≠ 2) {G : Type*} [Group G] {x : G}
    (h2 : x ^ 2 = 1) {k : ℕ} (hk : x ^ p ^ k = 1) : x = 1 := by
  have hcop : Nat.Coprime 2 (p ^ k) :=
    Nat.Coprime.pow_right _ ((Nat.coprime_primes Nat.prime_two Fact.out).2 hp2.symm)
  have h3 : orderOf x ∣ Nat.gcd 2 (p ^ k) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one hk)
  rw [hcop.gcd_eq_one] at h3
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h3)

theorem factorization_card_commutator (hp2 : p ≠ 2) {O : Type*} [Group O] [Finite O]
    (hsq : ∀ g : O, g ^ 2 ∈ commutator O) :
    (Nat.card (commutator O)).factorization p = (Nat.card O).factorization p := by
  have hdvd : ¬ p ∣ (commutator O).index := by
    intro hd
    rw [Subgroup.index] at hd
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hd
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    have hx2 : (QuotientGroup.mk g : O ⧸ commutator O) ^ 2 = 1 := by
      rw [← QuotientGroup.mk_pow]
      exact (QuotientGroup.eq_one_iff _).2 (hsq g)
    have h2 : orderOf (QuotientGroup.mk g : O ⧸ commutator O) ∣ 2 := orderOf_dvd_of_pow_eq_one hx2
    rw [hx] at h2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 h2)
  have h := (commutator O).index_mul_card
  have hi : (commutator O).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hc : Nat.card (commutator O) ≠ 0 := Nat.card_pos.ne'
  rw [← h, Nat.factorization_mul hi hc, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hdvd, zero_add]

theorem factorization_card_of_surjective (hp2 : p ≠ 2) {G H : Type} [Group G] [Group H] [Finite G]
    (π : G →* H) (hπ : Function.Surjective π) (hker : ∀ x, π x = 1 → x ^ 2 = 1) :
    (Nat.card H).factorization p = (Nat.card G).factorization p := by
  haveI : Finite H := Finite.of_surjective π hπ
  have hcard : Nat.card G = Nat.card H * Nat.card π.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup π.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective π hπ).toEquiv]
  have hZ : ¬ p ∣ Nat.card π.ker := by
    intro hd
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hd
    have hx2 : x ^ 2 = 1 := Subtype.ext (hker x.1 x.2)
    have h2 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hx2
    rw [hx] at h2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 h2)
  have hH : Nat.card H ≠ 0 := Nat.card_pos.ne'
  have hK0 : Nat.card π.ker ≠ 0 := Nat.card_pos.ne'
  rw [hcard, Nat.factorization_mul hH hK0, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hZ, add_zero]

end Abstract

theorem wcOn_projOmega_of_sylowData {F : Type} [Field F] [Finite F] {ι : Type} [Fintype ι]
    [DecidableEq ι] {Q : QuadraticForm F (ι → F)} {Q₀ : (ι → F) → F} (hQ0 : ⇑Q = Q₀)
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule F (ι → F), finrank F T = 3 ∧ ∀ x ∈ T, Q x = 0) {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {a r : ℕ} {μ₀ : ℤ} (hμ₀ : r = 2 → ¬ (p : ℤ) ∣ μ₀ ^ 2 - 1)
    (hdata : OSylowData Q p a r μ₀) : WCOn p (StatedProj (StatedOmega Q₀)) := by
  classical
  have hp := (Fact.out : p.Prime)
  obtain ⟨-, -, -, -, -, hsq', -, -, -⟩ :=
    CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hQ hT
  have hsq : ∀ g : ↥(TauCeti.QuadraticMap.orthogonalGroup Q),
      g ^ 2 ∈ commutator ↥(TauCeti.QuadraticMap.orthogonalGroup Q) := fun g =>
    mem_commutator_of_coe_mem (by simpa using hsq' (g : (ι → F) ≃ₗ[F] (ι → F)) g.2)
  haveI : Nontrivial (ι → F) := by
    obtain ⟨T, hT3, -⟩ := hT
    refine Module.nontrivial_of_finrank_pos (R := F) ?_
    have := Submodule.finrank_le T
    omega
  haveI : Finite ↥(TauCeti.QuadraticMap.orthogonalGroup Q) := inferInstance
  set O := TauCeti.QuadraticMap.orthogonalGroup Q with hO
  let Θ₁ : ↥O →* GL ι F := (toLinEquiv ι F).symm.toMonoidHom.comp O.subtype
  have hΘ₁ : ∀ x : ↥O, toLinEquiv ι F (Θ₁ x) = (x : (ι → F) ≃ₗ[F] (ι → F)) := fun x =>
    MulEquiv.apply_symm_apply _ _
  have hmemΩ : ∀ A : GL ι F, A ∈ StatedOmega Q₀ ↔ toLinEquiv ι F A ∈ ⁅O, O⁆ := fun A => by
    rw [statedOmega_eq_comap hQ0, Subgroup.mem_comap]
    rfl
  have hΘ₁Ω : ∀ x ∈ commutator ↥O, Θ₁ x ∈ StatedOmega Q₀ := by
    intro x hx
    rw [hmemΩ, hΘ₁]
    have : (x : (ι → F) ≃ₗ[F] (ι → F)) ∈ (commutator ↥O).map O.subtype := ⟨x, hx, rfl⟩
    rwa [Subgroup.map_subtype_commutator] at this
  let Θ₂ : ↥(commutator ↥O) →* ↥(StatedOmega Q₀) :=
    (Θ₁.comp (commutator ↥O).subtype).codRestrict (StatedOmega Q₀) (fun x => hΘ₁Ω x x.2)
  let pj : ↥(commutator ↥O) →* StatedProj (StatedOmega Q₀) :=
    (QuotientGroup.mk' ((StatedScalars ι F).subgroupOf (StatedOmega Q₀))).comp Θ₂
  have hker : ∀ x : ↥(commutator ↥O), pj x = 1 → (x : ↥O) ^ 2 = 1 := by
    intro x hx
    have h1 : Θ₂ x ∈ (StatedScalars ι F).subgroupOf (StatedOmega Q₀) :=
      (QuotientGroup.eq_one_iff _).1 hx
    rw [Subgroup.mem_subgroupOf] at h1
    have h2 : ((x : ↥O) : (ι → F) ≃ₗ[F] (ι → F)) ∈ scalars F (ι → F) := by
      have := (mem_statedScalars_iff _).1 h1
      rwa [show ((Θ₂ x : ↥(StatedOmega Q₀)) : GL ι F) = Θ₁ (x : ↥O) from rfl, hΘ₁] at this
    obtain ⟨a₀, ha₀⟩ := CFSG.RankThree.OrthogonalInvolutions.exists_map_ne_zero hQ
    obtain ⟨c, hc, hcv⟩ :=
      CFSG.RankThree.Classical.exists_sq_eq_one_of_mem_scalars h2 (x : ↥O).2 ha₀
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    refine LinearEquiv.ext fun v => ?_
    rw [pow_two, LinearEquiv.mul_apply, hcv v, map_smul, hcv v, smul_smul, ← _root_.sq, hc,
      one_smul]
    rfl
  have hsurj : Function.Surjective pj := by
    intro y
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective y
    have hz : toLinEquiv ι F (z : GL ι F) ∈ ⁅O, O⁆ := (hmemΩ _).1 z.2
    rw [← Subgroup.map_subtype_commutator] at hz
    obtain ⟨x, hx, hxz⟩ := hz
    refine ⟨⟨x, hx⟩, ?_⟩
    have h1 : Θ₂ ⟨x, hx⟩ = z := Subtype.ext (by
      show Θ₁ x = (z : GL ι F)
      apply (toLinEquiv ι F).injective
      rw [hΘ₁]
      exact hxz)
    show QuotientGroup.mk' _ (Θ₂ ⟨x, hx⟩) = _
    rw [h1]
    rfl
  have hcardΩ : (Nat.card ↥(commutator ↥O)).factorization p = (Nat.card ↥O).factorization p :=
    factorization_card_commutator hp2 hsq
  have hker' : ∀ x : ↥(commutator ↥O), pj x = 1 → x ^ 2 = 1 := fun x hx => by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact hker x hx
  have hcardK : (Nat.card (StatedProj (StatedOmega Q₀))).factorization p =
      (Nat.card ↥(commutator ↥O)).factorization p :=
    factorization_card_of_surjective hp2 pj hsurj hker'
  have hcard : (Nat.card (StatedProj (StatedOmega Q₀))).factorization p =
      a * r + r.factorial.factorization p := hcardK.trans (hcardΩ.trans hdata.1)
  by_cases hr0 : r = 0
  · subst hr0
    refine WCOn.of_factorization_le_one ?_
    simp [hcard]
  by_cases hpr : p ≤ r
  ·
    obtain ⟨G, _, ψ, hψ, hGp, x, y, hxy⟩ := hdata.2.2 hpr
    have hmem : ∀ g : G, ψ g ∈ commutator ↥O := fun g => by
      obtain ⟨k, hk⟩ := hGp g
      exact mem_commutator_of_odd_pow_eq_one hsq ((hp.odd_of_ne_two hp2).pow : Odd (p ^ k))
        (by rw [← map_pow, hk, map_one])
    let ψ' : G →* ↥(commutator ↥O) := ψ.codRestrict _ hmem
    refine WCOn.of_hom_noncomm (pj.comp ψ') (Q := ⊤) ?_ ?_ (Subgroup.mem_top x)
      (Subgroup.mem_top y) hxy
    · exact hGp.of_injective (⊤ : Subgroup G).subtype Subtype.val_injective
    · intro g _ hg
      have h2 : (ψ' g : ↥O) ^ 2 = 1 := hker (ψ' g) hg
      obtain ⟨k, hk⟩ := hGp g
      have h3 : (ψ' g : ↥O) ^ p ^ k = 1 := by
        show ψ g ^ p ^ k = 1
        rw [← map_pow, hk, map_one]
      exact hψ (by rw [map_one]; exact eq_one_of_sq_eq_one_of_pow_eq_one hp2 h2 h3)
  ·
    have hrp : r < p := by omega
    have hr1 : 1 ≤ r := by omega
    obtain ⟨F, hFr, hsw⟩ := hdata.2.1 hr1 hrp
    obtain ⟨F'⟩ := nonempty_oFrame_of_blockFrame hp2 hsq F μ₀ hμ₀ hFr hsw
    have hinj : Function.Injective (pj.comp F'.T) := by
      rw [injective_iff_map_eq_one]
      intro c hc
      have h2 : ((F'.T c : ↥(commutator ↥O)) : ↥O) ^ 2 = 1 := hker (F'.T c) hc
      have h3 : ((F'.T c : ↥(commutator ↥O)) : ↥O) ^ p ^ a = 1 := by
        rw [← Subgroup.coe_pow, ← map_pow, pow_pPow_eq_one_pi, map_one]
        rfl
      have h4 := eq_one_of_sq_eq_one_of_pow_eq_one hp2 h2 h3
      exact F'.T_injective (by rw [map_one]; exact Subtype.ext h4)
    have hfac0 : r.factorial.factorization p = 0 :=
      Nat.factorization_eq_zero_of_not_dvd fun h => by
        have := (Nat.Prime.dvd_factorial hp).1 h
        omega
    exact (F'.map pj hinj).wcOn (by rw [hcard, hfac0, add_zero])

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure
