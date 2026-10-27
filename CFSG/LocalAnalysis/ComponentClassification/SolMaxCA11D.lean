module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxCA11A
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxCA11B
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxCA11C
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxClaimA9P
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxClaimA9Q

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

namespace Sig36

variable [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin 11)} {E : Subgroup X} {D : Finset (Fin 11)}
  (S : Sig36 X t J 11 e E D)
include S

theorem centralizer_le_of_mem_E_eleven
    (h33 : Sol78.BalanceLemmaInput) (h35 : SignalizerLemma35)
    (hT13 : Sol76T13.SolomonThm13Simple) (hML : Sol78.MaximalityLemmaInput)
    (hSch : SolAltLit.SchurAlternatingMultiplierInput)
    (hPump : Sol78.AlternatingPumpUpInput) (hN1 : TwoGroupAltCoverExclusion)
    (hMult : TBLit.HeldTrivialMultiplier)
    {M : Subgroup X} (hMH : M ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hMpc : IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))))
    (hJM : J ≤ M)
    (hHN : normalizer (Sol78.signalizerCompletion E E : Set X) ≤ normalizer (M : Set X))
    (hsup : J ⊔ FooteLit.oddCoreIn M = M)
    {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin 11)}
    {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin 11)} (hρ : IsPermAction θ ρ) {e₀ : X}
    (he₀E : e₀ ∈ E) (he₀1 : e₀ ≠ 1) :
    centralizer ({e₀} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := normalizer (Sol78.signalizerCompletion E E : Set X) with hHdef
  have hJH : J ≤ H := S.le_normalizer_completion h33 h35
  have hCt : centralizer ({t} : Set X) ≤ H :=
    S.centralizer_le_normalizer_completion h33 h35 hT13 hML hSch
  have htH : t ∈ H := hCt (mem_centralizer_singleton_iff.mpr rfl)
  have ht2 : t * t = 1 := by rw [← sq, ← S.pair.1.1, pow_orderOf_eq_one]
  have he₀J : e₀ ∈ J := S.le he₀E
  have he₀H : e₀ ∈ H := hJH he₀J
  have he₀2 : e₀ * e₀ = 1 := by rw [← sq]; exact (card_sq_of_klein S.klein).2 e₀ he₀E
  have he₀o : orderOf e₀ = 2 := orderOf_eq_prime (by rw [sq]; exact he₀2) he₀1
  have he₀4 : (ρ ⟨e₀, hHN he₀H⟩).support.card = 4 := by
    have h1 := card_support_rho_eq_of_sup (by norm_num) e hJM hsup hρ he₀J
    rw [S.card_support_coreImage_E he₀E he₀1] at h1
    exact h1
  have hte₀ : t ∈ centralizer ({e₀} : Set X) :=
    mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp
      (S.pair.1.2.1 he₀J)).symm
  have hOC := S.oddCore_le_of_mem_E he₀E he₀1
  obtain ⟨L₀, F, χ, DY, hL₀J, hL₀C, hL₀pc, hFL₀, hFJ, hF4, hFsq, hFD, hDY4, hFY⟩ :=
    S.exists_fixed_layer_seven he₀E he₀1
  obtain ⟨N, hNC, hNpc, hL₀N, hbr⟩ := exists_pump_data_seven hPump hN1 S.nonab S.kProper
    S.unbal S.notU (by norm_num) S.pair.2.2.2.1 he₀o S.pair.1.1 hte₀ hL₀C hL₀pc χ
  rcases hbr with ⟨r, hrodd, hr7, -, ⟨θN⟩, hfix, hpc⟩ | ⟨hfix, hpc, ⟨ψ⟩⟩ | ⟨hne, ⟨ψ⟩⟩
  ·
    have hr8 : r ≠ 8 := by
      rintro rfl
      exact (by decide : ¬ Odd 8) hrodd
    obtain ⟨ρN, τ', DN, P⟩ := S.exists_pumpG_of_data ht2 hte₀ le_rfl hL₀C hL₀pc χ
      hFL₀ hFJ hF4 hFsq hFD hDY4 hFY hNC hNpc hL₀N hr7 (by omega) θN (Or.inr ⟨hfix, hpc⟩)
    exact S.centralizer_le_of_pumpG_sup h33 h35 hT13 hML hSch hMH hMpc hJM hHN hsup hρ he₀E he₀1
      P hfix hr8
  ·
    exfalso
    have hL₀N' : L₀ ≤ N := by
      have h1 := hL₀N
      rwa [hfix, sup_idem] at h1
    exact S.false_of_pump_held_seven hPump hN1 hT13 hML hSch hMult he₀E he₀1 hL₀J hL₀C hL₀pc χ
      hNC hNpc hfix hL₀N' hpc ψ
  ·
    exfalso
    have hF2 : IsPGroup 2 F := IsPGroup.of_card (n := 2) (by rw [hF4]; norm_num)
    obtain ⟨DF, hDF, hFs⟩ := hFD
    have hFH : normalizer (F : Set X) ≤ H := by
      have hFW := S.completion_eq_of_four h33 h35 hFJ (klein_of_card_sq hF4 hFsq) hDF hFs
      have h1 := normalizer_le_normalizer_signalizerCompletion_self F
      rwa [hFW] at h1
    have hNH : N ≤ H := le_of_diagonal ht2 hte₀ (inf_le_left.trans hCt) hOC hL₀C
      hL₀pc χ hFL₀ hF2 hFH hDY4 hFY hNC hNpc hL₀N hne ψ
    have hNtH : N.map (MulAut.conj t).toMonoidHom ≤ H := by
      rintro _ ⟨z, hz, rfl⟩
      exact mul_mem (mul_mem htH (hNH hz)) (inv_mem htH)
    obtain ⟨hNtC, hNtpc⟩ := isPComponent_conj hNC hNpc hte₀
    let ψt : ↥(N.map (MulAut.conj t).toMonoidHom) ⧸
        Open.fusionZStar ↥(N.map (MulAut.conj t).toMonoidHom) ≃* alternatingGroup (Fin 7) :=
      (Sol78.fusionZStarQuotCongr (N.equivMapOfInjective (MulAut.conj t).toMonoidHom
        (MulAut.conj t).injective)).symm.trans ψ
    have htN : t ∈ normalizer (M : Set X) := hHN htH
    have hFK := not_le_coreActionKernel_of_four hJM hρ hFJ hF4
    have hNK : ¬ N ≤ UnbalancedLayer.coreActionKernel M := by
      intro hNK
      have hNtK : N.map (MulAut.conj t).toMonoidHom ≤ UnbalancedLayer.coreActionKernel M := by
        rintro _ ⟨z, hz, rfl⟩
        exact hρ.conj_mem_coreActionKernel (by norm_num) htN (hNK hz)
      exact hFK (hFL₀.trans (hL₀N.trans (sup_le hNK hNtK)))
    have hNtK : ¬ N.map (MulAut.conj t).toMonoidHom ≤ UnbalancedLayer.coreActionKernel M := by
      intro hNtK
      apply hNK
      intro z hz
      have h1 : t * z * t⁻¹ ∈ N.map (MulAut.conj t).toMonoidHom := ⟨z, hz, rfl⟩
      have h2 := hρ.conj_mem_coreActionKernel (by norm_num) (inv_mem htN) (hNtK h1)
      have h3 : t⁻¹ * (t * z * t⁻¹) * t⁻¹⁻¹ = z := by group
      rwa [h3] at h2
    exact false_of_two_components_of_kerZ hρ hHN he₀H he₀2 he₀4 hOC hNC hNpc hNtC hNtpc
      (Ne.symm hne) hNH hNtH hNK hNtK ψ ψt

theorem claimA_M_eleven
    (h33 : Sol78.BalanceLemmaInput) (h35 : SignalizerLemma35)
    (hT13 : Sol76T13.SolomonThm13Simple) (hML : Sol78.MaximalityLemmaInput)
    (hSch : SolAltLit.SchurAlternatingMultiplierInput)
    (hPump : Sol78.AlternatingPumpUpInput) (hN1 : TwoGroupAltCoverExclusion)
    (hMult : TBLit.HeldTrivialMultiplier)
    {M : Subgroup X} (hMH : M ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hMpc : IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))))
    (hJM : J ≤ M)
    (hHN : normalizer (Sol78.signalizerCompletion E E : Set X) ≤ normalizer (M : Set X))
    (hsup : J ⊔ FooteLit.oddCoreIn M = M)
    {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin 11)}
    {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin 11)} (hρ : IsPermAction θ ρ) :
    ∀ (x : X) (hx : x ∈ M), x * x = 1 → (ρ ⟨x, le_normalizer hx⟩).support.card = 4 →
      centralizer ({x} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X) := by
  intro x hxM hx2 hx4
  obtain ⟨a₁, -, -, h₁, -, -, h₁₁, -⟩ := exists_three_of_klein S.klein
  have hC := S.centralizer_le_of_mem_E_eleven h33 h35 hT13 hML hSch hPump hN1 hMult hMH hMpc hJM
    hHN hsup hρ h₁ h₁₁
  have ha₁J : a₁ ∈ J := S.le h₁
  have ha₁M : a₁ ∈ M := hJM ha₁J
  have ha₁2 : a₁ * a₁ = 1 := by rw [← sq]; exact (card_sq_of_klein S.klein).2 a₁ h₁
  have ha₁4 : (ρ ⟨a₁, le_normalizer ha₁M⟩).support.card = 4 := by
    have h1 := card_support_rho_eq_of_sup (by norm_num) e hJM hsup hρ ha₁J
    rw [S.card_support_coreImage_E h₁ h₁₁] at h1
    exact h1
  have hkerM : ∀ g ∈ M, g ∈ UnbalancedLayer.coreActionKernel M → Odd (orderOf g) :=
    fun g hg hgK => odd_orderOf_of_mem_oddCoreIn (mem_core_of_mem_coreActionKernel hρ
      (by norm_num) hg hgK)
  obtain ⟨c, hcM, hc⟩ := hρ.exists_conj_of_four (by norm_num) le_rfl hkerM (le_normalizer ha₁M)
    (le_normalizer hxM) ha₁M hxM ha₁2 hx2 ha₁4 hx4
  intro y hy
  have hy' : c⁻¹ * y * c ∈ centralizer ({a₁} : Set X) := by
    rw [mem_centralizer_singleton_iff] at hy ⊢
    calc c⁻¹ * y * c * a₁ = c⁻¹ * (y * (c * a₁ * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * a₁ * c⁻¹) * y) * c := by rw [hc, hy]
      _ = a₁ * (c⁻¹ * y * c) := by group
  have hcH := hMH hcM
  have h1 := mul_mem (mul_mem hcH (hC hy')) (inv_mem hcH)
  have h2 : c * (c⁻¹ * y * c) * c⁻¹ = y := by group
  rwa [h2] at h1

end Sig36

end CFSG.ComponentClassification.SolMax
