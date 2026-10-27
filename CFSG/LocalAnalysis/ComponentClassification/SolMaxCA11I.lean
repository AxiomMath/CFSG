module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxCA11B
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxCA11G
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxCA11H
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxHe9A
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxClaimA9P
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxClaimA9Q
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxTwoA

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv CFSG.Sporadic.HeldB

variable {X : Type} [Group X]

theorem false_of_le_normalizer_of_held_of_lt
    [Finite X]
    {M : Subgroup X} {m : ℕ} {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin m)}
    {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin m)} (hρ : IsPermAction θ ρ) (hm4 : 4 ≤ m)
    (hm : m < 17) {N : Subgroup X} (hNM : N ≤ normalizer (M : Set X))
    (hN : Nonempty (↥N ⧸ pPrimeCore 2 ↥N ≃* Blueprint.NativeSporadic.He)) {x : X} (hxN : x ∈ N)
    (hxM : x ∈ M) (hx2 : x * x = 1) (hx1 : x ≠ 1) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ψb⟩ := hN
  set O := pPrimeCore 2 ↥N with hOdef
  set φ : ↥N →* Perm (Fin m) := ρ.comp (inclusion hNM) with hφdef
  have hxo : orderOf x = 2 := orderOf_eq_prime (by rw [sq]; exact hx2) hx1
  have hφx : φ ⟨x, hxN⟩ ≠ 1 := by
    intro h
    have hxK : x ∈ UnbalancedLayer.coreActionKernel M := hρ.mem_coreActionKernel (hNM hxN) h
    obtain ⟨o, ho, rfl⟩ := mem_core_of_mem_coreActionKernel hρ hm4 hxM hxK
    have h1 : Odd (orderOf (⟨o, ho⟩ : ↥(pPrimeCore 2 ↥M))) :=
      (Nat.coprime_two_left.mp pPrimeCore_coprime_card).of_dvd_nat (orderOf_dvd_natCard _)
    rw [Subgroup.orderOf_mk, ← Subgroup.orderOf_coe] at h1
    change Odd (orderOf (M.subtype o)) at h1
    rw [hxo] at h1
    exact absurd h1 (by decide)
  have : IsSimpleGroup heP := heP_simple
  set Θ : ↥N ⧸ O ≃* heP := ψb.trans heEquivP with hΘdef
  set π : ↥N →* heP := Θ.toMonoidHom.comp (QuotientGroup.mk' O) with hπdef
  have hπs : Function.Surjective π := Θ.surjective.comp (QuotientGroup.mk'_surjective O)
  have hπ : ∀ n, π n = 1 ↔ n ∈ O := fun n => by
    rw [hπdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have : (φ.ker.map π).Normal := Normal.map φ.normal_ker π hπs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (φ.ker.map π) with h | h
  ·
    have hkO : φ.ker ≤ O := fun k hk => by
      have h1 : π k ∈ φ.ker.map π := mem_map_of_mem _ hk
      rw [h, mem_bot] at h1
      exact (hπ k).mp h1
    have h1 : Nat.card ↥N = Nat.card (↥N ⧸ O) * Nat.card O :=
      card_eq_card_quotient_mul_card_subgroup O
    have h2 : Nat.card ↥N = Nat.card φ.range * Nat.card φ.ker := by
      rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
      exact card_eq_card_quotient_mul_card_subgroup _
    obtain ⟨q, hq⟩ : Nat.card φ.ker ∣ Nat.card O := card_dvd_of_le hkO
    have hkpos : 0 < Nat.card φ.ker := Nat.card_pos
    have h3 : Nat.card φ.range = Nat.card (↥N ⧸ O) * q := by
      rw [hq, h2] at h1
      have h4 : Nat.card φ.range * Nat.card φ.ker = Nat.card (↥N ⧸ O) * q * Nat.card φ.ker := by
        rw [h1]
        ring
      exact Nat.eq_of_mul_eq_mul_right hkpos h4
    have h17 : 17 ∣ Nat.card φ.range := by
      rw [h3, Nat.card_congr Θ.toEquiv, card_heP]
      exact Dvd.dvd.mul_right (by norm_num) _
    have h5 : Nat.card φ.range ∣ Nat.card (Perm (Fin m)) := Subgroup.card_subgroup_dvd_card _
    rw [Nat.card_perm, Nat.card_fin] at h5
    have h6 := (Nat.Prime.dvd_factorial (by norm_num : Nat.Prime 17)).mp (h17.trans h5)
    omega
  ·
    obtain ⟨k, hk, hkx⟩ : π ⟨x, hxN⟩ ∈ φ.ker.map π := by
      rw [h]
      exact mem_top _
    have hko : k⁻¹ * ⟨x, hxN⟩ ∈ O := (hπ _).mp (by rw [map_mul, map_inv, hkx, inv_mul_cancel])
    have hφ : φ ⟨x, hxN⟩ = φ (k⁻¹ * ⟨x, hxN⟩) := by
      rw [map_mul, map_inv, MonoidHom.mem_ker.mp hk, inv_one, one_mul]
    have hodd : Odd (orderOf (φ ⟨x, hxN⟩)) := by
      rw [hφ]
      have h1 : Odd (orderOf (⟨_, hko⟩ : O)) :=
        (Nat.coprime_two_left.mp pPrimeCore_coprime_card).of_dvd_nat (orderOf_dvd_natCard _)
      rw [Subgroup.orderOf_mk] at h1
      exact h1.of_dvd_nat (orderOf_map_dvd φ _)
    have h2 : orderOf (φ ⟨x, hxN⟩) ∣ 2 := by
      refine orderOf_dvd_of_pow_eq_one ?_
      rw [← map_pow, sq, show (⟨x, hxN⟩ : ↥N) * ⟨x, hxN⟩ = 1 from Subtype.ext hx2, map_one]
    have h3 : orderOf (φ ⟨x, hxN⟩) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h4 | h4
      · exact h4
      · rw [h4] at hodd
        exact absurd hodd (by decide)
    exact hφx (orderOf_eq_one_iff.mp h3)

namespace Sig36

variable [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin 11)} {E : Subgroup X} {D : Finset (Fin 11)}
  (S : Sig36 X t J 11 e E D)
include S

theorem centralizer_le_of_four_of_oddCore
    (h33 : Sol78.BalanceLemmaInput)
    (h35 : SignalizerLemma35) (hT13 : Sol76T13.SolomonThm13Simple)
    (hML : Sol78.MaximalityLemmaInput) (hSch : SolAltLit.SchurAlternatingMultiplierInput)
    (hPump : Sol78.AlternatingPumpUpInput) (hN1 : TwoGroupAltCoverExclusion)
    {M : Subgroup X} (hMH : M ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hMpc : IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))))
    (hJM : J ≤ M)
    (hHN : normalizer (Sol78.signalizerCompletion E E : Set X) ≤ normalizer (M : Set X))
    (hsup : J ⊔ FooteLit.oddCoreIn M = M)
    {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin 11)}
    {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin 11)} (hρ : IsPermAction θ ρ) {c : X}
    (hcH : c ∈ normalizer (Sol78.signalizerCompletion E E : Set X)) (hc2 : c * c = 1)
    (hct : c ∈ centralizer ({t} : Set X)) (hc4 : (ρ ⟨c, hHN hcH⟩).support.card = 4)
    (hOC : (pPrimeCore 2 ↥(centralizer ({c} : Set X))).map (centralizer ({c} : Set X)).subtype ≤
      normalizer (Sol78.signalizerCompletion E E : Set X)) :
    centralizer ({c} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := normalizer (Sol78.signalizerCompletion E E : Set X) with hHdef
  have hCt : centralizer ({t} : Set X) ≤ H :=
    S.centralizer_le_normalizer_completion h33 h35 hT13 hML hSch
  have htH : t ∈ H := hCt (mem_centralizer_singleton_iff.mpr rfl)
  have ht2 : t * t = 1 := by rw [← sq, ← S.pair.1.1, pow_orderOf_eq_one]
  have hcJ : c ∈ normalizer (J : Set X) := S.centralizer_le_normalizer hT13 hML hSch hct
  have htc : t ∈ centralizer ({c} : Set X) :=
    mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp hct).symm
  have hc1 : c ≠ 1 := by
    rintro rfl
    have h1 : ρ ⟨1, hHN hcH⟩ = 1 := map_one ρ
    rw [h1, Perm.support_one, Finset.card_empty] at hc4
    omega
  have hco : orderOf c = 2 := orderOf_eq_prime (by rw [sq]; exact hc2) hc1
  obtain ⟨ρJ, hρJ⟩ := exists_isPermAction (M := J) (by norm_num) (by norm_num) e
  have hcJ4 : (ρJ ⟨c, hcJ⟩).support.card = 4 := by
    rw [← card_support_rho_eq_rhoJ (by norm_num) hJM hsup hρ hρJ hcJ (hHN hcH)]
    exact hc4
  obtain ⟨L₀, F, χ, DY, hL₀J, hL₀C, hL₀pc, hFL₀, hFJ, hF4, hFsq, hFD, hDY4, hFY⟩ :=
    S.exists_fixed_layer_seven_of_four hρJ hcJ hc2 hcJ4
  have hF2 : IsPGroup 2 F := IsPGroup.of_card (n := 2) (by rw [hF4]; norm_num)
  have hFH : normalizer (F : Set X) ≤ H := by
    obtain ⟨DF, hDF, hFs⟩ := hFD
    have hFW := S.completion_eq_of_four h33 h35 hFJ (klein_of_card_sq hF4 hFsq) hDF hFs
    have h1 := normalizer_le_normalizer_signalizerCompletion_self F
    rwa [hFW] at h1
  obtain ⟨N, hNC, hNpc, hL₀N, hbr⟩ := exists_pump_data_seven hPump hN1 S.nonab S.kProper
    S.unbal S.notU (by norm_num) S.pair.2.2.2.1 hco S.pair.1.1 htc hL₀C hL₀pc χ
  rcases hbr with ⟨r, hrodd, hr7, -, ⟨θN⟩, hfix, hpc⟩ | ⟨hfix, hpc, ⟨ψ⟩⟩ | ⟨hne, ⟨ψ⟩⟩
  ·
    have hr8 : r ≠ 8 := by
      rintro rfl
      exact (by decide : ¬ Odd 8) hrodd
    obtain ⟨ρN, τ', DN, P⟩ := S.exists_pumpG_of_data ht2 htc le_rfl hL₀C hL₀pc χ
      hFL₀ hFJ hF4 hFsq hFD hDY4 hFY hNC hNpc hL₀N hr7 (by omega) θN (Or.inr ⟨hfix, hpc⟩)
    exact S.centralizer_le_of_pumpG_of_four h33 h35 hT13 hML hSch hMH hMpc hJM hHN hsup hρ hcH
      hc2 hc4 hOC P hfix hr8
  ·
    exfalso
    have hL₀N' : L₀ ≤ N := by
      have h1 := hL₀N
      rwa [hfix, sup_idem] at h1
    have htN : t ∈ normalizer (N : Set X) := mem_normalizer_iff_map_conj_eq.2 hfix
    have hNperf : ⁅N, N⁆ = N := UnbalancedCorr.commutator_eq_of_isPComponent hNC hNpc
    have hOH : coreNOf N ≤ H := (pPrimeCore_le_of_isPComponent hNC hNpc).trans hOC
    have hL₀t : L₀ ≤ N ⊓ centralizer ({t} : Set X) := le_inf hL₀N' (hL₀C.trans inf_le_left)
    have hNH := He9.le_of_held_pump ht2 htN hNperf (inf_le_right.trans hCt) hOH hL₀t hpc χ
      hFL₀ hF4 hFsq hFH hDY4 hFY ψ
    obtain ⟨x, hxF, hx1⟩ : ∃ x ∈ F, x ≠ 1 := by
      rcases F.bot_or_exists_ne_one with h | h
      · rw [h, Subgroup.card_bot] at hF4
        exact absurd hF4 (by norm_num)
      · exact h
    have hNc : commutator ↥N = ⊤ := by
      apply map_injective N.subtype_injective
      rw [_root_.commutator_def, map_commutator, ← MonoidHom.range_eq_map, range_subtype]
      exact hNperf
    exact false_of_le_normalizer_of_held_of_lt hρ (by norm_num) (by norm_num) (hNH.trans hHN)
      (nonempty_coreQuot_held hNc ψ) (hL₀N' (hFL₀ hxF)) (hJM (hFJ hxF)) (hFsq x hxF) hx1
  ·
    exfalso
    have hNH : N ≤ H := le_of_diagonal ht2 htc (inf_le_left.trans hCt) hOC hL₀C
      hL₀pc χ hFL₀ hF2 hFH hDY4 hFY hNC hNpc hL₀N hne ψ
    have hNtH : N.map (MulAut.conj t).toMonoidHom ≤ H := by
      rintro _ ⟨z, hz, rfl⟩
      exact mul_mem (mul_mem htH (hNH hz)) (inv_mem htH)
    obtain ⟨hNtC, hNtpc⟩ := isPComponent_conj hNC hNpc htc
    let ψt : ↥(N.map (MulAut.conj t).toMonoidHom) ⧸
        Open.fusionZStar ↥(N.map (MulAut.conj t).toMonoidHom) ≃* alternatingGroup (Fin 7) :=
      (Sol78.fusionZStarQuotCongr (N.equivMapOfInjective (MulAut.conj t).toMonoidHom
        (MulAut.conj t).injective)).symm.trans ψ
    have htNM : t ∈ normalizer (M : Set X) := hHN htH
    have hFK := not_le_coreActionKernel_of_four hJM hρ hFJ hF4
    have hNK : ¬ N ≤ UnbalancedLayer.coreActionKernel M := by
      intro hNK
      have hNtK : N.map (MulAut.conj t).toMonoidHom ≤ UnbalancedLayer.coreActionKernel M := by
        rintro _ ⟨z, hz, rfl⟩
        exact hρ.conj_mem_coreActionKernel (by norm_num) htNM (hNK hz)
      exact hFK (hFL₀.trans (hL₀N.trans (sup_le hNK hNtK)))
    have hNtK : ¬ N.map (MulAut.conj t).toMonoidHom ≤ UnbalancedLayer.coreActionKernel M := by
      intro hNtK
      apply hNK
      intro z hz
      have h1 : t * z * t⁻¹ ∈ N.map (MulAut.conj t).toMonoidHom := ⟨z, hz, rfl⟩
      have h2 := hρ.conj_mem_coreActionKernel (by norm_num) (inv_mem htNM) (hNtK h1)
      have h3 : t⁻¹ * (t * z * t⁻¹) * t⁻¹⁻¹ = z := by group
      rwa [h3] at h2
    exact false_of_two_components_of_kerZ hρ hHN hcH hc2 hc4 hOC hNC hNpc hNtC hNtpc
      (Ne.symm hne) hNH hNtH hNK hNtK ψ ψt

end Sig36

end CFSG.ComponentClassification.SolMax
