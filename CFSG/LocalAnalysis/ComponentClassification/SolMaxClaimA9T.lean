module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxClaimA9Q
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxClaimA9P
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxClaimA9K
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxDiagD
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxClaimA11R
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxClaimA9C

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

namespace Sig36

variable [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin 9)} {E : Subgroup X} {D : Finset (Fin 9)}
  (S : Sig36 X t J 9 e E D)
include S

theorem centralizer_le_of_mem_E_nine_of_inputs
    (h33 : Sol78.BalanceLemmaInput) (h35 : SignalizerLemma35)
    (hPump : Sol78.AlternatingPumpUpInput) (hN1 : TwoGroupAltCoverExclusion)
    {M : Subgroup X} (hMH : M ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hMpc : IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))))
    (hJM : J ≤ M)
    (hHN : normalizer (Sol78.signalizerCompletion E E : Set X) ≤ normalizer (M : Set X))
    (hker : ∀ g ∈ normalizer (Sol78.signalizerCompletion E E : Set X),
      g ∈ UnbalancedLayer.coreActionKernel M → Odd (orderOf g))
    {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin 11)}
    {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin 11)} (hρ : IsPermAction θ ρ)
    (htM : t ∈ normalizer (M : Set X)) {e₀ e₁ : X} (he₀E : e₀ ∈ E) (he₁E : e₁ ∈ E)
    (he₀1 : e₀ ≠ 1) (he₁1 : e₁ ≠ 1) (h01 : e₀ ≠ e₁) :
    centralizer ({e₀} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := normalizer (Sol78.signalizerCompletion E E : Set X) with hHdef
  obtain ⟨L₀, F, χ, DY, hL₀M, hL₀C, hL₀pc, hFL₀, hFJ, hF4, hFsq, hFD, hDY4, hFY⟩ :=
    S.exists_fixed_layer_pair' hMH hMpc hJM hρ htM he₀E he₁E he₀1 he₁1 h01
  have he₀2 : e₀ * e₀ = 1 := by rw [← sq]; exact (card_sq_of_klein S.klein).2 e₀ he₀E
  have he₁2 : e₁ * e₁ = 1 := by rw [← sq]; exact (card_sq_of_klein S.klein).2 e₁ he₁E
  have he₀o : orderOf e₀ = 2 := orderOf_eq_prime (by rw [sq]; exact he₀2) he₀1
  have he₁o : orderOf e₁ = 2 := orderOf_eq_prime (by rw [sq]; exact he₁2) he₁1
  have he₁C : e₁ ∈ centralizer ({e₀} : Set X) := mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val ((isElementaryAbelian_of_klein S.klein).toIsMulCommutative.is_comm.comm
      ⟨e₁, he₁E⟩ ⟨e₀, he₀E⟩))
  have hCC := S.inf_centralizer_le he₀E he₁E he₀1 he₁1 h01
  have hOC := S.oddCore_le_of_mem_E he₀E he₀1
  have hFH : normalizer (F : Set X) ≤ H := by
    obtain ⟨DF, hDF, hFs⟩ := hFD
    have hFW := S.completion_eq_of_four h33 h35 hFJ (klein_of_card_sq hF4 hFsq) hDF hFs
    have h1 := normalizer_le_normalizer_signalizerCompletion_self F
    rwa [hFW] at h1
  obtain ⟨N, hNC, hNpc, hL₀N, hcase⟩ := exists_pump_data_seven hPump hN1 S.nonab S.kProper
    S.unbal S.notU (by norm_num) S.pair.2.2.2.1 he₀o he₁o he₁C hL₀C hL₀pc χ
  have hOH : coreNOf N ≤ H := (pPrimeCore_le_of_isPComponent hNC hNpc).trans hOC
  rcases hcase with ⟨r, hr, hr7, -, ⟨θN⟩, hfix, hpc⟩ | ⟨hfix, hpc, ⟨ψ⟩⟩ | ⟨hne, ⟨ψ⟩⟩
  ·
    have hr6 : r ≠ 6 := by
      obtain ⟨a, ha⟩ := hr
      omega
    have hr8 : r ≠ 8 := by
      obtain ⟨a, ha⟩ := hr
      omega
    obtain ⟨ρN, τ', DN, P⟩ := S.exists_pumpG_of_data he₁2 he₁C (by norm_num) hL₀C hL₀pc χ hFL₀
      hFJ hF4 hFsq hFD hDY4 hFY hNC hNpc hL₀N hr7 hr6 θN (Or.inr ⟨hfix, hpc⟩)
    exact S.centralizer_le_of_pumpG h33 h35 (by norm_num) le_rfl hJM hHN hker hρ htM he₀E he₁E
      he₀1 he₁1 h01 P (by norm_num) hr8 (by omega)
  ·
    exfalso
    have he₁N : e₁ ∈ normalizer (N : Set X) := mem_normalizer_iff_map_conj_eq.mpr hfix
    have hL₀N' : L₀ ≤ N := by
      have h1 := hL₀N
      rwa [hfix, sup_idem] at h1
    have hCH : N ⊓ centralizer ({e₁} : Set X) ≤ H := fun z hz =>
      hCC (mem_inf.mpr ⟨hNC (mem_inf.mp hz).1, (mem_inf.mp hz).2⟩)
    exact false_of_pump_held hρ le_rfl hHN hker he₁2 he₁N
      (UnbalancedCorr.commutator_eq_of_isPComponent hNC hNpc) hCH hOH
      (le_inf hL₀N' (hL₀C.trans inf_le_left)) hpc χ hFL₀ hF4 hFsq hFH hDY4 hFY ψ
  ·
    have hJH : J ≤ H := S.le_normalizer_completion h33 h35
    have he₀H : e₀ ∈ H := hJH (S.le he₀E)
    have he₀4 : (ρ ⟨e₀, hHN he₀H⟩).support.card = 4 :=
      S.card_support_of_mem_E htM hJM (by norm_num) (by norm_num) hρ he₀E he₀1
    have hF2 : IsPGroup 2 F := IsPGroup.of_card (n := 2) (by rw [hF4]; norm_num)
    have hCC' : centralizer ({e₁} : Set X) ⊓ centralizer ({e₀} : Set X) ≤ H :=
      fun z hz => hCC (mem_inf.mpr ⟨(mem_inf.mp hz).2, (mem_inf.mp hz).1⟩)
    obtain ⟨θN⟩ := nonempty_coreQuot_of_diagonal hρ hHN hker he₀H he₀2 he₀4 he₁2 he₁C hCC'
      hOC hL₀C hL₀pc χ hFL₀ hF2 hFH hDY4 hFY hNC hNpc hL₀N hne ψ
    obtain ⟨ρN, τ', DN, P⟩ := S.exists_pumpG_of_data he₁2 he₁C (by norm_num) hL₀C hL₀pc χ hFL₀
      hFJ hF4 hFsq hFD hDY4 hFY hNC hNpc hL₀N (by norm_num) (by norm_num) θN (Or.inl rfl)
    exact S.centralizer_le_of_pumpG h33 h35 (by norm_num) le_rfl hJM hHN hker hρ htM he₀E he₁E
      he₀1 he₁1 h01 P (by norm_num) (by norm_num) (by norm_num)

theorem claimA_nine_of_inputs
    (h33 : Sol78.BalanceLemmaInput) (h35 : SignalizerLemma35)
    (hPump : Sol78.AlternatingPumpUpInput) (hN1 : TwoGroupAltCoverExclusion)
    {M : Subgroup X} (hMH : M ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hMpc : IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))))
    (hJM : J ≤ M)
    (hHN : normalizer (Sol78.signalizerCompletion E E : Set X) ≤ normalizer (M : Set X))
    (hker : ∀ g ∈ normalizer (Sol78.signalizerCompletion E E : Set X),
      g ∈ UnbalancedLayer.coreActionKernel M → Odd (orderOf g))
    {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin 11)}
    {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin 11)} (hρ : IsPermAction θ ρ) :
    ∀ (x : X) (hx : x ∈ normalizer (Sol78.signalizerCompletion E E : Set X)), x * x = 1 →
      (ρ ⟨x, hHN hx⟩).support.card = 4 →
        centralizer ({x} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X) := by
  obtain ⟨a₁, a₂, -, h₁, h₂, -, h₁₁, h₂₁, -, h₁₂, -, -⟩ := exists_three_of_klein S.klein
  have hJH : J ≤ normalizer (Sol78.signalizerCompletion E E : Set X) :=
    S.le_normalizer_completion h33 h35
  have htM : t ∈ normalizer (M : Set X) := hHN S.t_mem_normalizer_completion
  have ha₁H := hJH (S.le h₁)
  have ha₁2 : a₁ * a₁ = 1 := by rw [← sq]; exact (card_sq_of_klein S.klein).2 a₁ h₁
  exact claimA_of_centralizer_le hρ (by norm_num) hMH hHN hker ha₁H ha₁2
    (S.card_support_of_mem_E htM hJM (by norm_num) (by norm_num) hρ h₁ h₁₁)
    (S.centralizer_le_of_mem_E_nine_of_inputs h33 h35 hPump hN1 hMH hMpc hJM hHN hker hρ htM
      h₁ h₂ h₁₁ h₂₁ h₁₂)

end Sig36

theorem signalizerClaimANineInput_of_inputs
    (h33 : Sol78.BalanceLemmaInput) (h35 : SignalizerLemma35)
    (hPump : Sol78.AlternatingPumpUpInput) (hN1 : TwoGroupAltCoverExclusion) :
    SignalizerClaimANineInput := by
  intro X _ _ _ t J e E D S _ M θ ρ hρ hMH hMpc hJM hHN hker x hx hx2 hx4
  exact S.claimA_nine_of_inputs h33 h35 hPump hN1 hMH hMpc hJM hHN hker hρ x hx hx2 hx4

end CFSG.ComponentClassification.SolMax
