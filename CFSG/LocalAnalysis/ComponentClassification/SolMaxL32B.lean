module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxL32Perm
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxFiveP

public section

namespace CFSG.ComponentClassification.SolMax.L32

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

theorem false_of_odd_part [Finite X] {t : X} {J : Subgroup X} {n : ℕ}
    {θ : ↥J ⧸ pPrimeCore 2 ↥J ≃* alternatingGroup (Fin n)}
    {ρJ : ↥(normalizer (J : Set X)) →* Perm (Fin n)} (hρJ : IsPermAction θ ρJ) (hn : 9 ≤ n)
    (hJC : J ≤ centralizer ({t} : Set X)) {c e₀ : X} (he₀ : e₀ ∈ J) (hc2 : c * c = 1)
    (hcN : c ∈ normalizer (J : Set X)) (hce : c * e₀⁻¹ ∈ UnbalancedLayer.coreActionKernel J)
    (hs4 : (coreImage θ he₀).support.card = 4) {Jc : Subgroup X}
    (hJcJ : Jc ≤ J ⊓ centralizer ({c} : Set X))
    (hJcpc : IsPComponent 2
      (Jc.subgroupOf (centralizer ({t} : Set X) ⊓ centralizer ({c} : Set X))))
    (hinv : ∀ (x : X) (hx : x ∈ J), x * c = c * x → (∃ k : ℕ, x ^ 2 ^ k = 1) →
      (coreImage θ hx).support ⊆ (coreImage θ he₀).supportᶜ → x ∈ Jc)
    (hsubP : ∀ x ∈ Jc, ∃ hx : x ∈ J, (coreImage θ hx).support ⊆ (coreImage θ he₀).supportᶜ)
    (χ : ↥Jc ⧸ pPrimeCore 2 ↥Jc ≃*
      alternatingGroup ↥((coreImage θ he₀).supportᶜ : Finset (Fin n)))
    (hχ : ∀ (x : ↥Jc) (hx : (x : X) ∈ J),
      Perm.ofSubtype ((χ (x : ↥Jc ⧸ pPrimeCore 2 ↥Jc) : alternatingGroup _) :
        Perm ↥((coreImage θ he₀).supportᶜ : Finset (Fin n))) = coreImage θ hx)
    {M : Subgroup X} (hMC : M ≤ centralizer ({c} : Set X))
    (hMpc : IsPComponent 2 (M.subgroupOf (centralizer ({c} : Set X)))) (hJcM : Jc ≤ M)
    (hE1 : ∀ w ∈ M, w * t = t * w → w ∈ UnbalancedLayer.coreActionKernel Jc → Odd (orderOf w))
    {h : X} (hhM : h ∈ M) (hht : h * t = t * h) (hhJ : h ∈ normalizer (J : Set X))
    {σD σF : Perm (Fin n)} (hsplit : ρJ ⟨h, hhJ⟩ = σD * σF)
    (hσD : ∀ v ∉ (coreImage θ he₀).support, σD v = v)
    (hσF : ∀ v ∈ (coreImage θ he₀).support, σF v = v) (hsD : Perm.sign σD ≠ 1) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJcJ' : Jc ≤ J := hJcJ.trans inf_le_left
  have hJcC : Jc ≤ centralizer ({t} : Set X) ⊓ centralizer ({c} : Set X) :=
    le_inf (hJcJ'.trans hJC) (hJcJ.trans inf_le_right)
  have hres := primeResidual_eq_top_of_isPComponent hJcC hJcpc
  have hJcperf : ⁅Jc, Jc⁆ = Jc := UnbalancedCorr.commutator_eq_of_isPComponent hJcC hJcpc
  have hcardF : Fintype.card ↥((coreImage θ he₀).supportᶜ : Finset (Fin n)) = n - 4 := by
    rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin, hs4]
  have hJcq : Nontrivial (↥Jc ⧸ pPrimeCore 2 ↥Jc) := by
    have : Nontrivial (alternatingGroup (Fin (n - 4))) :=
      alternatingGroup.nontrivial_of_three_le_card (by rw [Nat.card_fin]; omega)
    exact (χ.trans (Fintype.equivFinOfCardEq hcardF).altCongrHom).toEquiv.nontrivial
  have hρJc : ρJ ⟨c, hcN⟩ = coreImage θ he₀ :=
    hρJ.apply_eq_coreImage_of_acts (by omega) hcN he₀ hce
  have hσ2 : coreImage θ he₀ * coreImage θ he₀ = 1 := by
    rw [← hρJc, ← map_mul]
    convert map_one ρJ
    exact Subtype.ext hc2
  have hhc : h * c = c * h := mem_centralizer_singleton_iff.mp (hMC hhM)
  set π := ρJ ⟨h, hhJ⟩ with hπdef
  have hlift : ∀ b : alternatingGroup (Fin n),
      (b : Perm (Fin n)) * coreImage θ he₀ = coreImage θ he₀ * b →
      ∃ x : X, x ∈ J ∧ x * c = c * x ∧ ∃ hxJ : x ∈ normalizer (J : Set X),
        ρJ ⟨x, hxJ⟩ = b := by
    intro b hb
    obtain ⟨x, hxc, hxb⟩ := hρJ.exists_lift hcN hc2 (b := b) (by rw [hρJc]; exact hb)
    refine ⟨x, x.2, mem_centralizer_singleton_iff.mp hxc, le_normalizer x.2, ?_⟩
    rw [hρJ.apply_of_mem (by omega) x, hxb]
  have hnormM : ∀ (w : X) (hwN : w ∈ normalizer (J : Set X)), w * c = c * w →
      (ρJ ⟨w, hwN⟩).support ⊆ (coreImage θ he₀).support →
      w ∈ normalizer (M : Set X) ∧ w ∈ UnbalancedLayer.coreActionKernel Jc := by
    intro w hwN hwc hwD
    obtain ⟨hwJc, hwK⟩ :=
      mem_coreActionKernel_of_support_subset hρJ he₀ hJcJ hres hinv hsubP χ hχ hwN hwc hwD
    exact ⟨mem_normalizer_of_mem_normalizer_Jc hMC hMpc hJcM hJcperf hJcq
      (mem_centralizer_singleton_iff.mpr hwc) hwJc, hwK⟩
  obtain ⟨u, hu2, huD, hσu⟩ := exists_not_commute_of_sign hs4 hσD hsD
  set uP : Perm (Fin n) := (u : Perm (Fin n)) with huPdef
  have hu2' : uP * uP = 1 := congrArg Subtype.val hu2
  have huA : Perm.sign uP = 1 := Perm.mem_alternatingGroup.mp u.2
  have huD' : ∀ ω ∉ (coreImage θ he₀).support, uP ω = ω := huD
  have hσu' : σD * uP ≠ uP * σD := hσu
  have he₀A : Perm.sign (coreImage θ he₀) = 1 :=
    Perm.mem_alternatingGroup.mp (coreImage_mem θ he₀)
  have he₀D : ∀ ω ∉ (coreImage θ he₀).support, (coreImage θ he₀) ω = ω :=
    fun ω hω => Perm.notMem_support.mp hω
  have huc : uP * coreImage θ he₀ = coreImage θ he₀ * uP :=
    commute_of_four hs4 huA he₀A hu2' hσ2 huD' he₀D
  obtain ⟨s, hsJ, hsc, hsN, hρs⟩ := hlift u huc
  have hsD : (ρJ ⟨s, hsN⟩).support ⊆ (coreImage θ he₀).support := by
    rw [hρs]
    intro v hv
    by_contra hvD
    exact (Perm.mem_support.mp hv) (huD' v hvD)
  obtain ⟨hsM, -⟩ := hnormM s hsN hsc hsD
  have hst : s * t = t * s := mem_centralizer_singleton_iff.mp (hJC hsJ)
  set h' := h * s * h⁻¹ * s⁻¹ with hh'def
  have hh'M : h' ∈ M := by
    have h1 : s * h⁻¹ * s⁻¹ ∈ M := (mem_normalizer_iff.mp hsM h⁻¹).mp (inv_mem hhM)
    have h2 : h' = h * (s * h⁻¹ * s⁻¹) := by rw [hh'def]; group
    rw [h2]
    exact mul_mem hhM h1
  have hcomm : ∀ {g : X}, h * g = g * h → s * g = g * s → h' * g = g * h' := by
    intro g hgh hgs
    have c1 : Commute h g := hgh
    have c2 : Commute s g := hgs
    exact (((c1.mul_left c2).mul_left c1.inv_left).mul_left c2.inv_left).eq
  have hh't : h' * t = t * h' := hcomm hht hst
  have hh'c : h' * c = c * h' := hcomm hhc hsc
  have hh'J : h' ∈ normalizer (J : Set X) :=
    mul_mem (mul_mem (mul_mem hhJ hsN) (inv_mem hhJ)) (inv_mem hsN)
  have hσFu : σF * uP = uP * σF := by
    refine (Perm.Disjoint.commute fun v => ?_).eq
    by_cases hv : v ∈ (coreImage θ he₀).support
    · exact Or.inl (hσF v hv)
    · exact Or.inr (huD' v hv)
  have hu' : uP⁻¹ = uP := inv_eq_of_mul_eq_one_right hu2'
  have hρh' : ρJ ⟨h', hh'J⟩ = σD * uP * σD⁻¹ * uP := by
    have h1 : (⟨h', hh'J⟩ : ↥(normalizer (J : Set X))) =
        ⟨h, hhJ⟩ * ⟨s, hsN⟩ * ⟨h, hhJ⟩⁻¹ * ⟨s, hsN⟩⁻¹ := rfl
    rw [h1, map_mul, map_mul, map_mul, map_inv, map_inv, ← hπdef, hρs, ← huPdef, hu', hsplit,
      mul_inv_rev]
    calc σD * σF * uP * (σF⁻¹ * σD⁻¹) * uP = σD * (σF * uP) * σF⁻¹ * σD⁻¹ * uP := by group
      _ = σD * (uP * σF) * σF⁻¹ * σD⁻¹ * uP := by rw [hσFu]
      _ = σD * uP * σD⁻¹ * uP := by group
  have hvA : Perm.sign (σD * uP * σD⁻¹) = 1 := by
    rw [Perm.sign_mul, Perm.sign_mul, Perm.sign_inv, huA, mul_one, Int.units_mul_self]
  have hv2 : σD * uP * σD⁻¹ * (σD * uP * σD⁻¹) = 1 := by
    calc σD * uP * σD⁻¹ * (σD * uP * σD⁻¹) = σD * (uP * uP) * σD⁻¹ := by group
      _ = 1 := by rw [hu2', mul_one, mul_inv_cancel]
  have hσDinv : ∀ ω ∉ (coreImage θ he₀).support, σD⁻¹ ω = ω := fun ω hω => by
    rw [Perm.inv_eq_iff_eq]
    exact (hσD ω hω).symm
  have hvD : ∀ ω ∉ (coreImage θ he₀).support, (σD * uP * σD⁻¹) ω = ω := fun ω hω => by
    rw [Perm.mul_apply, Perm.mul_apply, hσDinv ω hω, huD' ω hω, hσD ω hω]
  have hvu := commute_of_four hs4 hvA huA hv2 hu2' hvD huD'
  have hsq : ρJ ⟨h', hh'J⟩ ^ 2 = 1 := by
    rw [sq, hρh']
    calc σD * uP * σD⁻¹ * uP * (σD * uP * σD⁻¹ * uP) =
        σD * uP * σD⁻¹ * (uP * (σD * uP * σD⁻¹)) * uP := by group
      _ = σD * uP * σD⁻¹ * (σD * uP * σD⁻¹ * uP) * uP := by rw [← hvu]
      _ = σD * uP * σD⁻¹ * (σD * uP * σD⁻¹) * (uP * uP) := by group
      _ = 1 := by rw [hv2, hu2', mul_one]
  have hne : ρJ ⟨h', hh'J⟩ ≠ 1 := by
    rw [hρh']
    intro h1
    apply hσu'
    have h2 : σD * uP * σD⁻¹ = uP⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [hu'] at h2
    calc σD * uP = σD * uP * σD⁻¹ * σD := by group
      _ = uP * σD := by rw [h2]
  have hh'D : (ρJ ⟨h', hh'J⟩).support ⊆ (coreImage θ he₀).support := by
    intro v hv
    by_contra hv'
    apply Perm.mem_support.mp hv
    rw [hρh', Perm.mul_apply, huD' v hv']
    exact hvD v hv'
  obtain ⟨-, hh'K⟩ := hnormM h' hh'J hh'c hh'D
  have hodd := hE1 h' hh'M hh't hh'K
  have h1 : orderOf (ρJ ⟨h', hh'J⟩) ∣ orderOf h' := by
    have h2 := orderOf_map_dvd ρJ (⟨h', hh'J⟩ : ↥(normalizer (J : Set X)))
    rwa [Subgroup.orderOf_mk] at h2
  have h2 : orderOf (ρJ ⟨h', hh'J⟩) ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
  rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h3 | h3
  · exact hne (orderOf_eq_one_iff.mp h3)
  · rw [h3] at h1
    exact (Nat.not_even_iff_odd.mpr (hodd.of_dvd_nat h1)) even_two

end CFSG.ComponentClassification.SolMax.L32
