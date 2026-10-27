module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxOutA
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig36ZA

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

theorem exists_layer_of_kernel [Finite X] {H M : Subgroup X} (hMH : M ≤ H)
    (hMpc : IsPComponent 2 (M.subgroupOf H)) {n : ℕ}
    (θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin n)) {a : X} (haH : a ∈ H)
    (haK : a ∈ UnbalancedLayer.coreActionKernel M) (ha2 : IsPGroup 2 (zpowers a))
    (hCa : centralizer ({a} : Set X) ≤ H) :
    ∃ L : Subgroup X, L ≤ M ∧ L ≤ centralizer ({a} : Set X) ∧
      IsPComponent 2 (L.subgroupOf (centralizer ({a} : Set X))) ∧ ⁅L, L⁆ = L ∧
      (∃ θL : ↥L ⧸ pPrimeCore 2 ↥L ≃* alternatingGroup (Fin n), ∀ (x : X) (hxL : x ∈ L)
        (hxM : x ∈ M), θL ((⟨x, hxL⟩ : ↥L) : ↥L ⧸ pPrimeCore 2 ↥L) =
          θ ((⟨x, hxM⟩ : ↥M) : ↥M ⧸ pPrimeCore 2 ↥M)) ∧
      ∀ g ∈ normalizer (M : Set X), g * a = a * g → g ∈ normalizer (L : Set X) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hMq : IsQuasisimple (↥M ⧸ pPrimeCore 2 ↥M) :=
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 M H hMH).mp hMpc).2.2
  have hMsub : (M.subgroupOf H).IsSubnormal := hMpc.choose_spec.2.1
  have hE : zpowers a ≤ UnbalancedLayer.coreActionKernel M := zpowers_le.mpr haK
  have hEX : zpowers a ≤ H := zpowers_le.mpr haH
  have hCE : centralizer ((zpowers a : Subgroup X) : Set X) = centralizer ({a} : Set X) :=
    centralizer_zpowers_eq' a
  have hpc := GSLit.fixedLayer_isPComponent hMH hMsub hEX hE ha2 hMq
  rw [hCE, inf_eq_right.mpr hCa] at hpc
  have hle := GSLit.fixedLayer_le_inf M (zpowers a)
  rw [hCE] at hle
  obtain ⟨hsup, -⟩ := GSLit.fixedLayer_sup_pPrimeCore hMq hE ha2
  have hLM : GSLit.fixedLayer M (zpowers a) ≤ M := hle.trans inf_le_left
  obtain ⟨θL, hθL⟩ := exists_coreQuot_of_sup hLM hsup θ
  exact ⟨GSLit.fixedLayer M (zpowers a), hLM, hle.trans inf_le_right, hpc,
    UnbalancedCorr.commutator_eq_of_isPComponent (hle.trans inf_le_right) hpc,
    ⟨θL, fun x hxL _ => hθL ⟨x, hxL⟩⟩, fun g hg hga => mem_normalizer_fixedLayer hMq hE ha2 hg hga⟩

namespace Sig36

variable [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X} {n : ℕ}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)} {E : Subgroup X} {D : Finset (Fin n)}

theorem mul_self_eq_one_of_conjugate (S : Sig36 X t J n e E D)
    (hD2 : SignalizerConjKernelExclusion) {M : Subgroup X}
    (hMH : M ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hMpc : IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))))
    (hHN : normalizer (Sol78.signalizerCompletion E E : Set X) ≤ normalizer (M : Set X))
    (hsup : J ⊔ FooteLit.oddCoreIn M = M)
    {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin n)}
    {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin n)} (hρ : IsPermAction θ ρ) {Q : Subgroup X}
    (hQK : Q ≤ normalizer (Sol78.signalizerCompletion E E : Set X) ⊓
      UnbalancedLayer.coreActionKernel M) (hQ2 : IsPGroup 2 Q)
    (hQcard : Nat.card Q = 2 ^ (Nat.card ↥(normalizer (Sol78.signalizerCompletion E E : Set X) ⊓
      UnbalancedLayer.coreActionKernel M)).factorization 2)
    (hA : ∀ (x : X) (hx : x ∈ M), x * x = 1 → (ρ ⟨x, le_normalizer hx⟩).support.card = 4 →
      centralizer ({x} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hNT : ∀ T : Subgroup X, T ≤ Q → T ≠ ⊥ →
      normalizer (T : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X)) {a g : X}
    (ha : a ∈ Q) (hs : g⁻¹ * a * g ∈ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hsNQ : g⁻¹ * a * g ∈ normalizer (Q : Set X))
    (hσ2 : ρ ⟨g⁻¹ * a * g, hHN hs⟩ * ρ ⟨g⁻¹ * a * g, hHN hs⟩ = 1)
    (hσ1 : ρ ⟨g⁻¹ * a * g, hHN hs⟩ ≠ 1) : g⁻¹ * a * g * (g⁻¹ * a * g) = 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := normalizer (Sol78.signalizerCompletion E E : Set X) with hHdef
  have hn9 := S.nine_le
  have haH : a ∈ H := (hQK ha).1
  have haK : a ∈ UnbalancedLayer.coreActionKernel M := (hQK ha).2
  have ha2 : IsPGroup 2 (zpowers a) := hQ2.to_le (zpowers_le.mpr ha)
  set s := g⁻¹ * a * g with hsdef
  have hsN : s ∈ normalizer (M : Set X) := hHN hs
  have hssH : s * s ∈ H := mul_mem hs hs
  have hssK : s * s ∈ UnbalancedLayer.coreActionKernel M := by
    refine hρ.mem_coreActionKernel (mul_mem hsN hsN) ?_
    have h1 : (⟨s * s, mul_mem hsN hsN⟩ : ↥(normalizer (M : Set X))) = ⟨s, hsN⟩ * ⟨s, hsN⟩ := rfl
    rw [h1, map_mul]
    exact hσ2
  obtain ⟨k, hk⟩ := ha2 ⟨a, mem_zpowers a⟩
  have hak : a ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hsk' : s ^ 2 ^ k = 1 := by
    rw [hsdef, show g⁻¹ * a * g = g⁻¹ * a * g⁻¹⁻¹ by rw [inv_inv], conj_pow, hak]
    group
  have hsk : (s * s) ^ 2 ^ k = 1 := by
    rw [← sq, ← pow_mul, mul_comm, pow_mul, hsk', one_pow]
  have hss2 : IsPGroup 2 (zpowers (s * s)) := isPGroup_zpowers_of_pow_eq_one hsk
  have hssQ : s * s ∈ Q := by
    have hP2 : IsPGroup 2 (zpowers (s * s) ⊔ Q : Subgroup X) :=
      hss2.to_sup_of_normal_right' hQ2 (zpowers_le.mpr (mul_mem hsNQ hsNQ))
    have hPK : (zpowers (s * s) ⊔ Q : Subgroup X) ≤ H ⊓ UnbalancedLayer.coreActionKernel M :=
      sup_le (zpowers_le.mpr ⟨hssH, hssK⟩) hQK
    obtain ⟨j, hj⟩ := hP2.exists_card_eq
    have h1 : Nat.card (zpowers (s * s) ⊔ Q : Subgroup X) ∣
        Nat.card ↥(H ⊓ UnbalancedLayer.coreActionKernel M) := Subgroup.card_dvd_of_le hPK
    rw [hj] at h1
    have h2 := (Nat.prime_two.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp h1
    have h3 : Nat.card (zpowers (s * s) ⊔ Q : Subgroup X) ≤ Nat.card Q := by
      rw [hj, hQcard]
      exact Nat.pow_le_pow_right (by norm_num) h2
    have h4 := Subgroup.eq_of_le_of_card_ge (le_sup_right : Q ≤ zpowers (s * s) ⊔ Q) h3
    rw [h4]
    exact mem_sup_left (mem_zpowers _)
  by_contra hss1
  have hT1 : zpowers (s * s) ≠ ⊥ := fun h => hss1 (zpowers_eq_bot.mp h)
  have hNss := hNT _ (zpowers_le.mpr hssQ) hT1
  have hCs : centralizer ({s} : Set X) ≤ H := by
    intro z hz
    apply hNss
    apply Subgroup.centralizer_le_normalizer
    rw [centralizer_zpowers_eq', mem_centralizer_singleton_iff]
    have h1 : z * s = s * z := mem_centralizer_singleton_iff.mp hz
    calc z * (s * s) = (z * s) * s := by group
      _ = (s * z) * s := by rw [h1]
      _ = s * (z * s) := by group
      _ = s * (s * z) := by rw [h1]
      _ = s * s * z := by group
  have ha1 : a ≠ 1 := by
    rintro rfl
    apply hσ1
    have h1 : (⟨s, hsN⟩ : ↥(normalizer (M : Set X))) = 1 :=
      Subtype.ext (show s = 1 by rw [hsdef]; group)
    rw [h1, map_one]
  have hCa : centralizer ({a} : Set X) ≤ H := by
    have hNa := hNT _ (zpowers_le.mpr ha) (fun h => ha1 (zpowers_eq_bot.mp h))
    intro z hz
    apply hNa
    apply Subgroup.centralizer_le_normalizer
    rw [centralizer_zpowers_eq']
    exact hz
  obtain ⟨La, hLaM, hLaC, -, hLaperf, ⟨θLa, hθLa⟩, -⟩ :=
    exists_layer_of_kernel hMH hMpc θ haH haK ha2 hCa
  set Ls := La.map (MulAut.conj g⁻¹).toMonoidHom with hLsdef
  have hLsC : Ls ≤ centralizer ({s} : Set X) := by
    have h1 := map_conj_centralizer_singleton g⁻¹ a
    rw [inv_inv] at h1
    rw [hsdef, ← h1]
    exact map_mono hLaC
  have hLsN : Ls ≤ normalizer (M : Set X) := hLsC.trans (hCs.trans hHN)
  have hLsperf : ⁅Ls, Ls⁆ = Ls := by rw [hLsdef, ← Subgroup.map_commutator, hLaperf]
  let θLs : ↥Ls ⧸ pPrimeCore 2 ↥Ls ≃* alternatingGroup (Fin n) :=
    (Sol78.coreQuotCongr (La.equivMapOfInjective (MulAut.conj g⁻¹).toMonoidHom
      (MulAut.conj g⁻¹).injective)).symm.trans θLa
  have hLsK := le_coreActionKernel_of_le_centralizer_of_ne_one hρ (by omega) hsN hσ1 hLsN hLsC θLs
    hLsperf
  obtain ⟨ρa, hρa⟩ := exists_isPermAction (M := La) (by omega) (by omega) θLa
  obtain ⟨δ, hδA, hδ2, hδ4, -, -⟩ := exists_four_of_fix (1 : Perm (Fin n)) (by simp; omega)
  have hδ1 : δ ≠ 1 := by
    rintro rfl
    rw [Perm.support_one, Finset.card_empty] at hδ4
    omega
  obtain ⟨f, hfLa, -, hf2, hρaf⟩ := hρa.exists_involution_lift (by omega) (one_mem _)
    (one_mul 1) hδA hδ2 hδ1 (by rw [show (⟨1, one_mem _⟩ : ↥(normalizer (La : Set X))) = 1 from
      rfl, map_one, mul_one, one_mul])
  have hfM : f ∈ M := hLaM hfLa
  have hρf : ρ ⟨f, le_normalizer hfM⟩ = δ := by
    rw [hρ.apply_of_mem (by omega) ⟨f, hfM⟩, ← hθLa f hfLa hfM, ← hρaf]
    exact (hρa.apply_of_mem (by omega) ⟨f, hfLa⟩).symm
  have hf4 : (ρ ⟨f, le_normalizer hfM⟩).support.card = 4 := by rw [hρf]; exact hδ4
  have hCf := hA f hfM hf2 hf4
  have hTg : (zpowers f).map (MulAut.conj g⁻¹).toMonoidHom ≤ Ls := map_mono (zpowers_le.mpr hfLa)
  exact hD2 X t J n e E D S M hMH hMpc hHN hsup θ ρ hρ f hfM (le_normalizer hfM) hf2 hf4 hCf g⁻¹
    (hTg.trans (hLsC.trans hCs)) (hTg.trans hLsK)

end Sig36

end CFSG.ComponentClassification.SolMax
