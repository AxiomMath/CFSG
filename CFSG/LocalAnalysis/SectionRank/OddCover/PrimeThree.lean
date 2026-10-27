module

public import CFSG.LocalAnalysis.SectionRank.OddCover.LiftedMonomial
public import CFSG.LocalAnalysis.SectionRank.OddCover.CyclicSylow
public import CFSG.LocalAnalysis.SectionRank.OddCover.ScalarCover
public import CFSG.LinearAlgebra.LinearGroups.Perfect
public import CFSG.LocalAnalysis.SectionRank.Framework.Semisimple

public section

namespace CFSG.SectionRank.OddCover

open scoped commutatorElement

section Sylow

variable {E J : Type*} [Group E] [Group J]

theorem sylow_eq_bot_of_not_dvd {G : Type*} [Group G] [Finite G] {r : ℕ} [Fact r.Prime]
    (P : Sylow r G) (h : ¬ r ∣ Nat.card G) : (P : Subgroup G) = ⊥ := by
  rw [← Subgroup.card_eq_one, Sylow.card_eq_multiplicity, Nat.factorization_eq_zero_of_not_dvd h,
    pow_zero]

theorem inf_ker_eq_bot_of_injective {π : E →* J} {N : Subgroup E}
    (h : Function.Injective (π.comp N.subtype)) : N ⊓ π.ker = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨hgN, hgk⟩
  have : (⟨g, hgN⟩ : N) = 1 := h (by simpa using hgk)
  exact Subgroup.mem_bot.2 (congrArg Subtype.val this)

theorem card_map_eq_of_injective {π : E →* J} {N : Subgroup E}
    (h : Function.Injective (π.comp N.subtype)) : Nat.card (N.map π) = Nat.card N := by
  have hmap : N.map π = (π.comp N.subtype).range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [hmap]
  exact Nat.card_congr (MonoidHom.ofInjective h).toEquiv.symm

theorem sylow_kernel_eq_bot_of_faithful [Finite E] [Group.IsPerfect E] {r : ℕ}
    [hr : Fact r.Prime] (π : E →* J) (hπ : Function.Surjective π)
    (hC : π.ker ≤ Subgroup.center E) {N : Subgroup E} (hN : N ⊓ π.ker = ⊥)
    (hv : (Nat.card J).factorization r ≤ (Nat.card N).factorization r) (Cr : Sylow r π.ker) :
    (Cr : Subgroup π.ker) = ⊥ := by
  have : Finite J := Finite.of_surjective π hπ
  obtain ⟨Q₀⟩ := (inferInstance : Nonempty (Sylow r N))
  set Q : Subgroup E := (Q₀ : Subgroup N).map N.subtype with hQdef
  have hQN : Q ≤ N := Subgroup.map_subtype_le _
  have hQcard : Nat.card Q = r ^ (Nat.card N).factorization r := by
    rw [hQdef, Subgroup.card_map_of_injective N.subtype_injective, Sylow.card_eq_multiplicity]
  have hQp : IsPGroup r Q := Q₀.isPGroup'.map _
  have hinjQ : Function.Injective (π.comp Q.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro q hq
    have hq1 : (q : E) ∈ N ⊓ π.ker := ⟨hQN q.2, hq⟩
    rw [hN] at hq1
    exact Subgroup.mem_bot.2 (Subtype.ext (Subgroup.mem_bot.1 hq1))
  have hQmap := card_map_eq_of_injective hinjQ
  obtain ⟨P, hQP⟩ := hQp.exists_le_sylow
  have hPQ : (P : Subgroup E).map π ≤ Q.map π := by
    have hle : Q.map π ≤ (P : Subgroup E).map π := Subgroup.map_mono hQP
    obtain ⟨S, hS⟩ := (P.isPGroup'.map π).exists_le_sylow
    have h1 : Nat.card ((P : Subgroup E).map π) ≤ Nat.card (S : Subgroup J) :=
      Subgroup.card_le_of_le hS
    have h2 := Sylow.card_eq_multiplicity S
    have h3 : r ^ (Nat.card J).factorization r ≤ r ^ (Nat.card N).factorization r :=
      Nat.pow_le_pow_right hr.out.pos hv
    have h4 : Nat.card ((P : Subgroup E).map π) ≤ Nat.card (Q.map π) := by
      rw [hQmap, hQcard]
      omega
    exact (Subgroup.eq_of_le_of_card_ge hle h4).ge
  have hdecomp : ∀ g ∈ (P : Subgroup E), ∃ q ∈ Q, q⁻¹ * g ∈ π.ker := by
    intro g hg
    obtain ⟨q, hq, hqg⟩ := hPQ ⟨g, hg, rfl⟩
    exact ⟨q, hq, by rw [MonoidHom.mem_ker, map_mul, map_inv, hqg, inv_mul_cancel]⟩
  have hcomm : ∀ g₁ ∈ (P : Subgroup E), ∀ g₂ ∈ (P : Subgroup E), ⁅g₁, g₂⁆ ∈ Q := by
    intro g₁ hg₁ g₂ hg₂
    obtain ⟨q₁, hq₁, hk₁⟩ := hdecomp g₁ hg₁
    obtain ⟨q₂, hq₂, hk₂⟩ := hdecomp g₂ hg₂
    rw [show g₁ = q₁ * (q₁⁻¹ * g₁) by group, show g₂ = q₂ * (q₂⁻¹ * g₂) by group,
      commutatorElement_mul_central_left (hC hk₁), commutatorElement_mul_central_right (hC hk₂),
      commutatorElement_def]
    exact Q.mul_mem (Q.mul_mem (Q.mul_mem hq₁ hq₂) (Q.inv_mem hq₁)) (Q.inv_mem hq₂)
  have hP'Q : (commutator (P : Subgroup E)).map (P : Subgroup E).subtype ≤ Q := by
    rw [Subgroup.map_le_iff_le_comap, commutator_def, Subgroup.commutator_le]
    intro g₁ _ g₂ _
    rw [Subgroup.mem_comap, map_commutatorElement]
    exact hcomm _ g₁.2 _ g₂.2
  set A : Subgroup E := (Cr : Subgroup π.ker).map π.ker.subtype with hAdef
  have hAc : A ≤ Subgroup.center E := (Subgroup.map_subtype_le _).trans hC
  have hAp : IsPGroup r A := Cr.isPGroup'.map _
  have hAQ : A ≤ Q :=
    (CFSG.ShultStronglyClosedTI.central_pSubgroup_le_sylow_derived P A hAc hAp).trans hP'Q
  rw [eq_bot_iff]
  intro c hc
  have h1 : (c : E) ∈ N ⊓ π.ker := ⟨hQN (hAQ ⟨c, hc, rfl⟩), c.2⟩
  rw [hN] at h1
  exact Subgroup.mem_bot.2 (Subtype.ext (Subgroup.mem_bot.1 h1))

theorem ker_eq_bot_of_sylow_conditions [Finite E] [Group.IsPerfect E] (π : E →* J)
    (hπ : Function.Surjective π) (hC : π.ker ≤ Subgroup.center E)
    (hodd : Odd (Nat.card π.ker)) {p e : ℕ} [Fact p.Prime]
    (hp : ∀ Cp : Sylow p π.ker, (Cp : Subgroup π.ker) = ⊥)
    (hcyc : ∀ (r : ℕ) [Fact r.Prime], r ≠ 2 → r ≠ p → ¬ r ∣ e →
      ∃ Q : Sylow r J, IsCyclic (Q : Subgroup J))
    (hmono : ∀ (r : ℕ) [Fact r.Prime], r ≠ 2 → r ≠ p → r ∣ e →
      ∃ N : Subgroup E, N ⊓ π.ker = ⊥ ∧
        (Nat.card J).factorization r ≤ (Nat.card N).factorization r) :
    π.ker = ⊥ := by
  apply eq_bot_of_forall_sylow_eq_bot
  intro r hr _ Cr
  by_cases hr2 : r = 2
  · subst hr2
    exact sylow_eq_bot_of_not_dvd Cr (fun h => Nat.not_even_iff_odd.2 hodd (even_iff_two_dvd.2 h))
  by_cases hrp : r = p
  · subst hrp
    exact hp Cr
  by_cases hre : r ∣ e
  · obtain ⟨N, hN, hv⟩ := hmono r hr2 hrp hre
    exact sylow_kernel_eq_bot_of_faithful π hπ hC hN hv Cr
  · obtain ⟨Q, hQ⟩ := hcyc r hr2 hrp hre
    exact CFSG.ShultStronglyClosedTI.central_cover_cyclic_sylow_kernel_eq_bot π hπ hC Cr Q hQ

end Sylow

section Perfect

open Matrix CFSG.Assembly.LowTwoRank

variable {K : Type} [Field K] [Finite K]

theorem card_statedSL_three_eq_mul {p : ℕ} (hK : Nat.card K = p) :
    Nat.card (StatedSL 3 K) = p ^ 3 * ((p - 1) * (p + 1)) * ((p - 1) * (p ^ 2 + p + 1)) := by
  have hp1 : 1 ≤ p := hK ▸ Nat.card_pos
  rw [card_statedSL_three, hK]
  zify [hp1, Nat.one_le_pow 2 p hp1, Nat.one_le_pow 3 p hp1]
  ring

theorem card_statedSU_three_eq_mul {p : ℕ} [Fact p.Prime] (hK : Nat.card K = p ^ 2) :
    Nat.card (StatedSU 3 p K) = p ^ 3 * ((p + 1) * (p - 1)) * ((p + 1) * (p ^ 2 - p + 1)) := by
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  have hpp : p ≤ p ^ 2 := Nat.le_self_pow (by norm_num) p
  have h := card_statedSU_three_prime hK
  zify [hp1, hpp]
  rw [h]
  ring

theorem not_dvd_add_one_of_dvd_sub_one {p r : ℕ} (hp : 1 ≤ p) (hr : r.Prime) (hr2 : r ≠ 2)
    (h : r ∣ p - 1) : ¬ r ∣ p + 1 := fun h' => by
  have h2 : r ∣ 2 := by
    have := Nat.dvd_sub h' h
    rwa [show p + 1 - (p - 1) = 2 by omega] at this
  exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 h2)

theorem prime_classical_three_perfect_odd_extension_trivial {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {ε : ℤ} {H : Subgroup (GL (Fin 3) K)}
    (hH : (ε = 1 ∧ Nat.card K = p ∧ H = StatedSL 3 K) ∨
      (ε = -1 ∧ Nat.card K = p ^ 2 ∧ H = StatedSU 3 p K))
    {E : Type*} [Group E] [Finite E] [Group.IsPerfect E] (π : E →* H)
    (hπ : Function.Surjective π) (hC : π.ker ≤ Subgroup.center E)
    (hodd : Odd (Nat.card π.ker)) : π.ker = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  have hp1 : 1 ≤ p := hp.one_lt.le
  have hcycH := (prime_classical_three_cyclic_odd_sylows hp hH).1
  have hcyc : ∀ e : ℕ, (e : ℤ) = p - ε → ∀ (r : ℕ) [Fact r.Prime], r ≠ 2 → r ≠ p → ¬ r ∣ e →
      ∃ Q : Sylow r H, IsCyclic (Q : Subgroup H) := by
    intro e he r _ hr2 hrp hre
    obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow r H))
    refine ⟨Q, hcycH r hr2 hrp (fun h => hre ?_) Q⟩
    rw [← he] at h
    exact Int.natCast_dvd_natCast.1 h
  have hrp : ∀ r : ℕ, r.Prime → r ≠ p → ¬ r ∣ p := fun r hr hrp h =>
    hrp ((Nat.prime_dvd_prime_iff_eq hr hp).1 h)
  rcases hH with ⟨rfl, hK, rfl⟩ | ⟨rfl, hK, rfl⟩
  · refine ker_eq_bot_of_sylow_conditions π hπ hC hodd (p := p) (e := p - 1)
      (statedSL_three_sylow_kernel_eq_bot hp2 hK π hπ hC)
      (hcyc (p - 1) (by push_cast [hp1]; ring)) ?_
    intro r hr hr2 hrp' hre
    obtain ⟨N, hNmap, hNinj, hNcard⟩ := prime_classical_three_lifted_monomial_subgroup hp
      (Or.inl ⟨rfl, hK, rfl, rfl⟩) π hπ hC hodd
    refine ⟨N, inf_ker_eq_bot_of_injective hNinj, ?_⟩
    have hN : Nat.card N = 6 * (p - 1) ^ 2 := by
      zify [hp1]
      rw [← card_map_eq_of_injective hNinj, hNmap]
      exact hNcard
    rw [card_statedSL_three_eq_mul hK, hN, factorization_order_eq hr.out hr2 hp.ne_zero
      (by have := hp.two_le; omega) (by omega) (by positivity) (hrp r hr.out hrp')
      (not_dvd_add_one_of_dvd_sub_one hp1 hr.out hr2 hre)
      (factorization_sq_add_add_one hr.out hp1 hre)]
  · refine ker_eq_bot_of_sylow_conditions π hπ hC hodd (p := p) (e := p + 1)
      (statedSU_three_sylow_kernel_eq_bot hp2 hK π hπ hC)
      (hcyc (p + 1) (by push_cast; ring)) ?_
    intro r hr hr2 hrp' hre
    obtain ⟨N, hNmap, hNinj, hNcard⟩ := prime_classical_three_lifted_monomial_subgroup hp
      (Or.inr ⟨rfl, hK, rfl, rfl⟩) π hπ hC hodd
    refine ⟨N, inf_ker_eq_bot_of_injective hNinj, ?_⟩
    have hN : Nat.card N = 6 * (p + 1) ^ 2 := by
      zify
      rw [← card_map_eq_of_injective hNinj, hNmap, hNcard]
      ring
    have hre' : ¬ r ∣ p - 1 := fun h => not_dvd_add_one_of_dvd_sub_one hp1 hr.out hr2 h hre
    rw [card_statedSU_three_eq_mul hK, hN, factorization_order_eq hr.out hr2 hp.ne_zero
      (by omega) (by have := hp.two_le; omega)
      (by have := Nat.le_self_pow (by norm_num : 2 ≠ 0) p; omega)
      (hrp r hr.out hrp') hre' (factorization_sq_sub_add_one hr.out hre)]

end Perfect

section Splitting

open Matrix CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary

variable {K : Type} [Field K] [Finite K]

theorem isPerfect_prime_three {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {ε : ℤ}
    {H : Subgroup (GL (Fin 3) K)}
    (hH : (ε = 1 ∧ Nat.card K = p ∧ H = StatedSL 3 K) ∨
      (ε = -1 ∧ Nat.card K = p ^ 2 ∧ H = StatedSU 3 p K)) :
    Group.IsPerfect H := by
  rcases hH with ⟨-, -, rfl⟩ | ⟨-, hK, rfl⟩
  · have := CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect (K := K) (n := 3)
      le_rfl
    exact Group.IsPerfect.ofSurjective (f := (specialLinearGroupEquivStatedSL 3 K).toMonoidHom)
      (specialLinearGroupEquivStatedSL 3 K).surjective
  · have : Fact p.Prime := ⟨hp⟩
    have hK1 : Nat.card K = (p ^ 1) ^ 2 := by rw [pow_one]; exact hK
    have : CharP K p := by
      have := Fintype.ofFinite K
      exact charP_of_card_eq_prime_pow (f := 2) (by rw [← Nat.card_eq_fintype_card, hK])
    have := CFSG.ClassicalGroups.Unitary.isPerfect_SUid
      (CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution hK1) (le_refl 3)
      (fun _ => CFSG.ClassicalGroups.Unitary.exists_norm_ne_one hK1 (by rw [pow_one]; exact hp2))
    have heq : SUid (unitaryInvolution K p 1) 3 = StatedSU 3 p K := by
      rw [SUid_eq_statedSU hK1 3, pow_one]
    exact Group.IsPerfect.ofSurjective (f := (MulEquiv.subgroupCongr heq).toMonoidHom)
      (MulEquiv.subgroupCongr heq).surjective

theorem prime_classical_three_central_odd_extension_splitting {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {ε : ℤ} {H : Subgroup (GL (Fin 3) K)}
    (hH : (ε = 1 ∧ Nat.card K = p ∧ H = StatedSL 3 K) ∨
      (ε = -1 ∧ Nat.card K = p ^ 2 ∧ H = StatedSU 3 p K))
    {E : Type*} [Group E] [Finite E] (π : E →* H) (hπ : Function.Surjective π)
    (hC : π.ker ≤ Subgroup.center E) (hodd : Odd (Nat.card π.ker)) :
    (∃! s : H →* E, π.comp s = MonoidHom.id H) ∧
      ∀ s : H →* E, π.comp s = MonoidHom.id H →
        π.ker ⊓ s.range = ⊥ ∧ π.ker ⊔ s.range = ⊤ ∧ ∀ c ∈ π.ker, ∀ g ∈ s.range, Commute c g := by
  have hHperf := isPerfect_prime_three hp hp2 hH
  obtain ⟨-, hE'perf, hE'surj⟩ :=
    CFSG.LocalCores.central_extension_derived_of_surjective π hπ hC hHperf
  set E' := commutator E with hE'def
  set π' : E' →* H := π.comp E'.subtype with hπ'def
  have hC' : π'.ker ≤ Subgroup.center E' := by
    intro g hg
    rw [Subgroup.mem_center_iff]
    intro g'
    exact Subtype.ext (Subgroup.mem_center_iff.1 (hC hg) g')
  have hodd' : Odd (Nat.card π'.ker) := by
    have hle : π'.ker.map E'.subtype ≤ π.ker := by
      rintro _ ⟨g, hg, rfl⟩
      exact hg
    have hdvd := Subgroup.card_dvd_of_le hle
    rw [Subgroup.card_map_of_injective E'.subtype_injective] at hdvd
    exact Odd.of_dvd_nat hodd hdvd
  have hker' : π'.ker = ⊥ :=
    prime_classical_three_perfect_odd_extension_trivial hp hp2 hH π' hE'surj hC' hodd'
  have hbij : Function.Bijective π' := ⟨(MonoidHom.ker_eq_bot_iff π').1 hker', hE'surj⟩
  set e' : E' ≃* H := MulEquiv.ofBijective π' hbij with he'def
  set s₀ : H →* E := E'.subtype.comp e'.symm.toMonoidHom with hs₀def
  have hs₀ : π.comp s₀ = MonoidHom.id H := by
    refine MonoidHom.ext fun h => ?_
    have := e'.apply_symm_apply h
    rw [he'def, MulEquiv.ofBijective_apply] at this
    exact this
  have hsec : ∀ s : H →* E, π.comp s = MonoidHom.id H → ∀ h : H, π (s h) = h :=
    fun s hs h => DFunLike.congr_fun hs h
  have huniq : ∀ s : H →* E, π.comp s = MonoidHom.id H → s = s₀ := by
    intro s hs
    have hdiff : ∀ h : H, (s₀ h)⁻¹ * s h ∈ π.ker := fun h => by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hsec s hs, hsec s₀ hs₀, inv_mul_cancel]
    refine MonoidHom.eq_of_eqOn_dense (s := commutatorSet H) ?_ ?_
    · rw [← commutator_eq_closure, hHperf.commutator_eq_top]
    · rintro _ ⟨x, y, rfl⟩
      rw [map_commutatorElement, map_commutatorElement,
        show s x = s₀ x * ((s₀ x)⁻¹ * s x) by group, show s y = s₀ y * ((s₀ y)⁻¹ * s y) by group,
        commutatorElement_mul_central_left (hC (hdiff x)),
        commutatorElement_mul_central_right (hC (hdiff y))]
  refine ⟨⟨s₀, hs₀, huniq⟩, fun s hs => ⟨?_, ?_, ?_⟩⟩
  · rw [eq_bot_iff]
    rintro c ⟨hck, ⟨h, rfl⟩⟩
    have h1 : h = 1 := by
      rw [← hsec s hs h]
      exact hck
    rw [h1, map_one]
    exact Subgroup.one_mem _
  · rw [eq_top_iff]
    intro g _
    rw [show g = (g * (s (π g))⁻¹) * s (π g) by group]
    refine Subgroup.mul_mem _ (Subgroup.mem_sup_left ?_) (Subgroup.mem_sup_right ⟨π g, rfl⟩)
    rw [MonoidHom.mem_ker, map_mul, map_inv, hsec s hs, mul_inv_cancel]
  · intro c hc g _
    exact (Subgroup.mem_center_iff.1 (hC hc) g).symm

end Splitting

section Catalog

open CFSG.Assembly.LowTwoRank

theorem prime_classical_three_odd_cover_catalog_step {L : Type} [Group L] [Finite L] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {t : StatedLieTag} (ht : t = .PSL ∨ t = .PSU)
    (hL : IsQuasisimple L) (hSQT : IsStronglyQuasithin L)
    (hodd : Odd (Nat.card (Subgroup.center L)))
    (h : StatedClassicalModel (L ⧸ Subgroup.center L) t 3 p 1) : CatalogStepConclusion L := by
  have : Fact p.Prime := ⟨hp⟩
  have hLperf : Group.IsPerfect L := hL.1
  obtain ⟨K, _, _, H, ε, hHK, hHK', ⟨θ⟩⟩ : ∃ (K : Type) (_ : Field K) (_ : Finite K)
      (H : Subgroup (GL (Fin 3) K)) (ε : ℤ),
      ((ε = 1 ∧ Nat.card K = p ∧ H = StatedSL 3 K) ∨
        (ε = -1 ∧ Nat.card K = p ^ 2 ∧ H = StatedSU 3 p K)) ∧
      ((Nat.card K = p ^ 1 ∧ H = StatedSL 3 K) ∨
        (Nat.card K = (p ^ 1) ^ 2 ∧ H = StatedSU 3 (p ^ 1) K)) ∧
      Nonempty (L ⧸ Subgroup.center L ≃* StatedProj H) := by
    rcases ht with rfl | rfl
    · obtain ⟨-, K, hF, hFin, hK, hθ⟩ := h
      exact ⟨K, hF, hFin, StatedSL 3 K, 1, Or.inl ⟨rfl, by rw [hK, pow_one], rfl⟩,
        Or.inl ⟨hK, rfl⟩, hθ⟩
    · obtain ⟨-, K, hF, hFin, hK, hθ⟩ := h
      exact ⟨K, hF, hFin, StatedSU 3 (p ^ 1) K, -1,
        Or.inr ⟨rfl, by rw [hK, pow_one], by rw [pow_one]⟩, Or.inr ⟨hK, rfl⟩, hθ⟩
  set D := (StatedScalars (Fin 3) K).subgroupOf H with hDdef
  set Z := Subgroup.center L with hZdef
  set F : Subgroup (H × L) := MonoidHom.eqLocus ((QuotientGroup.mk' D).comp (MonoidHom.fst H L))
    (θ.toMonoidHom.comp ((QuotientGroup.mk' Z).comp (MonoidHom.snd H L))) with hFdef
  have hmemF : ∀ x : H × L,
      x ∈ F ↔ QuotientGroup.mk' D x.1 = θ (QuotientGroup.mk' Z x.2) := fun x => Iff.rfl
  set π₁ : F →* H := (MonoidHom.fst H L).comp F.subtype with hπ₁def
  have hπ₁ : Function.Surjective π₁ := by
    intro h
    obtain ⟨l, hl⟩ := QuotientGroup.mk'_surjective Z (θ.symm (QuotientGroup.mk' D h))
    refine ⟨⟨(h, l), ?_⟩, rfl⟩
    rw [hmemF, hl, MulEquiv.apply_symm_apply]
  have hkerZ : ∀ x : F, x ∈ π₁.ker → (x : H × L).2 ∈ Z := by
    intro x hx
    have h1 := (hmemF x).1 x.2
    have hx1 : (x : H × L).1 = 1 := hx
    rw [hx1, map_one] at h1
    have h2 : QuotientGroup.mk' Z (x : H × L).2 = 1 := θ.injective (by rw [← h1, map_one])
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
  have hC₁ : π₁.ker ≤ Subgroup.center F := by
    intro x hx
    have hx1 : (x : H × L).1 = 1 := hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    apply Prod.ext
    · change (y : H × L).1 * (x : H × L).1 = (x : H × L).1 * (y : H × L).1
      rw [hx1, mul_one, one_mul]
    · exact Subgroup.mem_center_iff.1 (hkerZ x hx) (y : H × L).2
  have hodd₁ : Odd (Nat.card π₁.ker) := by
    have hZmem : ∀ z ∈ Z, ((1 : H), z) ∈ F := fun z hz => by
      rw [hmemF, map_one]
      have : QuotientGroup.mk' Z z = 1 := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact hz
      rw [this, map_one]
    have hcard : Nat.card π₁.ker = Nat.card Z := Nat.card_congr
      { toFun := fun x => ⟨((x : F) : H × L).2, hkerZ x x.2⟩
        invFun := fun z => ⟨⟨(1, z), hZmem z z.2⟩, rfl⟩
        left_inv := fun x => by
          apply Subtype.ext
          apply Subtype.ext
          apply Prod.ext
          · exact (x.2 : ((x : F) : H × L).1 = 1).symm
          · rfl
        right_inv := fun z => rfl }
    rw [hcard]
    exact hodd
  obtain ⟨⟨s, hs, -⟩, -⟩ :=
    prime_classical_three_central_odd_extension_splitting hp hp2 hHK π₁ hπ₁ hC₁ hodd₁
  set φ : H →* L := (MonoidHom.snd H L).comp (F.subtype.comp s) with hφdef
  have hsfst : ∀ h : H, ((s h : F) : H × L).1 = h := fun h => DFunLike.congr_fun hs h
  have hφ : ∀ h : H, QuotientGroup.mk' D h = θ (QuotientGroup.mk' Z (φ h)) := by
    intro h
    have h1 := (hmemF _).1 (s h).2
    rw [hsfst] at h1
    exact h1
  have hφsurj : Function.Surjective φ := by
    have hsup : φ.range ⊔ Z = ⊤ := by
      rw [eq_top_iff]
      intro l _
      obtain ⟨h, hh⟩ := QuotientGroup.mk'_surjective D (θ (QuotientGroup.mk' Z l))
      have h2 : QuotientGroup.mk' Z (φ h) = QuotientGroup.mk' Z l :=
        θ.injective (by rw [← hφ, hh])
      have hz : (φ h)⁻¹ * l ∈ Z := QuotientGroup.eq.1 h2
      rw [show l = φ h * ((φ h)⁻¹ * l) by group]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨h, rfl⟩) (Subgroup.mem_sup_right hz)
    exact MonoidHom.range_eq_top.1 ((perfect_central_supplement hLperf).1 φ.range hsup)
  have hkerφ : φ.ker ≤ D := by
    intro h hh
    have h1 := hφ h
    rw [(MonoidHom.mem_ker).1 hh, map_one, map_one, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at h1
    exact h1
  have hDZ : D.map φ = Z := by
    apply le_antisymm
    · rintro _ ⟨h, hh, rfl⟩
      have h1 := hφ h
      rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff _).2 hh] at h1
      have h2 : QuotientGroup.mk' Z (φ h) = 1 := θ.injective (by rw [← h1, map_one])
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
    · intro z hz
      obtain ⟨h, rfl⟩ := hφsurj z
      refine ⟨h, ?_, rfl⟩
      have h1 := hφ h
      rw [QuotientGroup.mk'_apply (Subgroup.center L), (QuotientGroup.eq_one_iff _).2 hz,
        map_one, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact h1
  exact classical_scalar_cover_step hp le_rfl (by norm_num) hHK' hSQT hodd φ hφsurj hkerφ hDZ

end Catalog

end CFSG.SectionRank.OddCover
