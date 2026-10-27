module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxFiveG
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSigSylow

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

@[expose] def SignalizerSwapMemberInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X] (t : X) (J : Subgroup X) (n : ℕ)
    (e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)) (E : Subgroup X) (D : Finset (Fin n)),
    Sig36 X t J n e E D →
    centralizer ({t} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X) →
    ∀ M : Subgroup X, M ≤ normalizer (Sol78.signalizerCompletion E E : Set X) →
      IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))) →
      M.map (MulAut.conj t).toMonoidHom ≠ M → J ≤ M ⊔ M.map (MulAut.conj t).toMonoidHom →
      Nonempty (↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin n)) →
      (∀ P : Subgroup X, P ≤ centralizer ({t} : Set X) ⊓ UnbalancedLayer.coreActionKernel J →
        IsPGroup 2 P → Nat.card P ≤ 2) →
      FooteLit.IsSolomonMember M

theorem IsPermAction.mem_alternatingGroup_of_perfect {M : Subgroup X} {r : ℕ}
    {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin r)} {L : Subgroup X}
    (hLN : L ≤ normalizer (M : Set X)) (hperf : ⁅L, L⁆ = L) {y : X} (hy : y ∈ L) :
    ρ ⟨y, hLN hy⟩ ∈ alternatingGroup (Fin r) := by
  have : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr hperf
  set φ : ↥L →* ℤˣ := Perm.sign.comp (ρ.comp (Subgroup.inclusion hLN)) with hφdef
  have h1 : (⟨y, hy⟩ : ↥L) ∈ φ.ker :=
    Abelianization.commutator_subset_ker φ Group.IsPerfect.mem_commutator
  rw [Perm.mem_alternatingGroup]
  exact (MonoidHom.mem_ker).mp h1

theorem le_normalizer_of_swap [Finite X] {H M J : Subgroup X} {t : X} (htH : t ∈ H) (hMH : M ≤ H)
    (hMpc : IsPComponent 2 (M.subgroupOf H)) (hne : M.map (MulAut.conj t).toMonoidHom ≠ M)
    (hJM : J ≤ M ⊔ M.map (MulAut.conj t).toMonoidHom) : J ≤ normalizer (M : Set X) := by
  obtain ⟨hMtH, hMtpc⟩ := isPComponent_conj hMH hMpc htH
  have hMtK := GSThmB.B5a.le_coreActionKernel_of_ne hMH hMtH hMpc hMtpc (Ne.symm hne)
  exact hJM.trans (sup_le le_normalizer fun x hx => (hMtK hx).1)

namespace Sig36

variable [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X} {n : ℕ}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)} {E : Subgroup X} {D : Finset (Fin n)}
  (S : Sig36 X t J n e E D)
include S

theorem not_le_coreActionKernel_of_swap {M : Subgroup X}
    (hCH : centralizer ({t} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hMH : M ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hMpc : IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))))
    (hne : M.map (MulAut.conj t).toMonoidHom ≠ M) (hJM : J ≤ M ⊔ M.map (MulAut.conj t).toMonoidHom)
    (θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin n)) :
    ¬ J ≤ UnbalancedLayer.coreActionKernel M := by
  classical
  have hn9 := S.nine_le
  have htH := hCH (mem_centralizer_singleton_iff.mpr rfl)
  have hJN := le_normalizer_of_swap (hCH (mem_centralizer_singleton_iff.mpr rfl)) hMH hMpc hne hJM
  obtain ⟨ρ, hρ⟩ := exists_isPermAction (M := M) (by omega) (by omega) θ
  have hperf : ⁅J, J⁆ = J :=
    UnbalancedCorr.commutator_eq_of_isPComponent S.pair.1.2.1 S.pair.1.2.2.1
  have hJq : Nontrivial (↥J ⧸ pPrimeCore 2 ↥J) := by
    have : Nontrivial (alternatingGroup (Fin n)) :=
      alternatingGroup.nontrivial_of_three_le_card (by rw [Nat.card_fin]; omega)
    exact e.toEquiv.nontrivial
  obtain ⟨z, hz⟩ := exists_ne_one_of_pump hMH hMpc htH hJM S.pair.1.2.1 hperf hJq
    (by omega : 4 ≤ n) hρ hJN
  intro hJK
  exact hz (hρ.eq_one_of_mem_coreActionKernel (by omega) (hJK z.2))

theorem map_conj_eq_or_of_swap {M : Subgroup X}
    (hCH : centralizer ({t} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hMH : M ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hMpc : IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))))
    (hne : M.map (MulAut.conj t).toMonoidHom ≠ M) (hJM : J ≤ M ⊔ M.map (MulAut.conj t).toMonoidHom)
    (θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin n)) {q : X}
    (hqt : q ∈ centralizer ({t} : Set X)) (hqK : q ∈ UnbalancedLayer.coreActionKernel J) :
    M.map (MulAut.conj q).toMonoidHom = M ∨
      M.map (MulAut.conj q).toMonoidHom = M.map (MulAut.conj t).toMonoidHom := by
  have htH := hCH (mem_centralizer_singleton_iff.mpr rfl)
  have hqH := hCH hqt
  have hJK := S.not_le_coreActionKernel_of_swap hCH hMH hMpc hne hJM θ
  by_contra hor
  push Not at hor
  obtain ⟨h1, h2⟩ := hor
  set K := M.map (MulAut.conj q).toMonoidHom with hKdef
  obtain ⟨hKH, hKpc⟩ := isPComponent_conj hMH hMpc hqH
  obtain ⟨hMtH, hMtpc⟩ := isPComponent_conj hMH hMpc htH
  have hMK := GSThmB.B5a.le_coreActionKernel_of_ne hKH hMH hKpc hMpc h1
  have hMtK := GSThmB.B5a.le_coreActionKernel_of_ne hKH hMtH hKpc hMtpc h2
  have hJKK : J ≤ UnbalancedLayer.coreActionKernel K := hJM.trans (sup_le hMK hMtK)
  apply hJK
  intro j hj
  have hj' : q * j * q⁻¹ ∈ J := (mem_normalizer_iff.mp hqK.1 j).mp hj
  have h3 := hJKK hj'
  rw [hKdef, ← Sol76.map_coreActionKernel (MulAut.conj q) M] at h3
  obtain ⟨k, hk, hkj⟩ := h3
  have hkj' : q * k * q⁻¹ = q * j * q⁻¹ := hkj
  rw [← mul_left_cancel (mul_right_cancel hkj')]
  exact hk

theorem mem_coreActionKernel_of_swap {M : Subgroup X}
    (hCH : centralizer ({t} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hMH : M ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hMpc : IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))))
    (hne : M.map (MulAut.conj t).toMonoidHom ≠ M) (hJM : J ≤ M ⊔ M.map (MulAut.conj t).toMonoidHom)
    (θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin n)) {z : X}
    (hzN : z ∈ normalizer (M : Set X)) (hzK : z ∈ UnbalancedLayer.coreActionKernel J) :
    z ∈ UnbalancedLayer.coreActionKernel M := by
  classical
  have hn9 := S.nine_le
  have hJN := le_normalizer_of_swap (hCH (mem_centralizer_singleton_iff.mpr rfl)) hMH hMpc hne hJM
  have hJK := S.not_le_coreActionKernel_of_swap hCH hMH hMpc hne hJM θ
  obtain ⟨ρ, hρ⟩ := exists_isPermAction (M := M) (by omega) (by omega) θ
  have hperf : ⁅J, J⁆ = J :=
    UnbalancedCorr.commutator_eq_of_isPComponent S.pair.1.2.1 S.pair.1.2.2.1
  have hQ : Nat.card (alternatingGroup (Fin n)) ≤ n.factorial / 2 := by
    have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
    rw [nat_card_alternatingGroup, Nat.card_fin]
  obtain ⟨hsurj, hO⟩ := hρ.image_eq_of_le hJN (by omega) e hperf hJK hQ
    (fun y hy => IsPermAction.mem_alternatingGroup_of_perfect hJN hperf hy)
  have hcomm : ∀ (y : X) (hy : y ∈ J),
      ρ ⟨z, hzN⟩ * ρ ⟨y, hJN hy⟩ = ρ ⟨y, hJN hy⟩ * ρ ⟨z, hzN⟩ := by
    intro y hy
    have hc : y⁻¹ * z⁻¹ * y * z ∈ coreNOf J := hzK.2 y hy
    have hcJ : y⁻¹ * z⁻¹ * y * z ∈ J := map_subtype_le _ hc
    have h1 := hO _ hcJ hc
    have h2 : (⟨y⁻¹ * z⁻¹ * y * z, hJN hcJ⟩ : ↥(normalizer (M : Set X))) =
        (⟨y, hJN hy⟩ : ↥(normalizer (M : Set X)))⁻¹ * (⟨z, hzN⟩)⁻¹ * ⟨y, hJN hy⟩ * ⟨z, hzN⟩ :=
      rfl
    rw [h2, map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    calc ρ ⟨z, hzN⟩ * ρ ⟨y, hJN hy⟩ = ρ ⟨y, hJN hy⟩ * ρ ⟨z, hzN⟩ *
        ((ρ ⟨y, hJN hy⟩)⁻¹ * (ρ ⟨z, hzN⟩)⁻¹ * ρ ⟨y, hJN hy⟩ * ρ ⟨z, hzN⟩)⁻¹ := by group
      _ = ρ ⟨y, hJN hy⟩ * ρ ⟨z, hzN⟩ := by rw [h1, inv_one, mul_one]
  have hz1 : ρ ⟨z, hzN⟩ = 1 := by
    apply Equiv.ext
    intro v
    have h4 : 4 ≤ n - (1 : Perm (Fin n)).support.card := by
      rw [Perm.support_one, Finset.card_empty]
      omega
    have h5 : v ∉ (1 : Perm (Fin n)).support := by
      rw [Perm.support_one]
      exact Finset.notMem_empty v
    refine apply_eq_of_commute_fixAlt h4 (fun b _ => ?_) h5
    obtain ⟨y, hy, hyb⟩ := hsurj b b.2
    rw [← hyb]
    exact hcomm y hy
  exact hρ.mem_coreActionKernel hzN hz1

theorem isSolomonMember_of_swap_of_two_lt (h33 : Sol78.BalanceLemmaInput)
    (h35 : SignalizerLemma35) (hT13 : Sol76T13.SolomonThm13Simple)
    (hML : Sol78.MaximalityLemmaInput) (hSch : SolAltLit.SchurAlternatingMultiplierInput)
    {M : Subgroup X} (hMH : M ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hMpc : IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))))
    (hne : M.map (MulAut.conj t).toMonoidHom ≠ M) (hJM : J ≤ M ⊔ M.map (MulAut.conj t).toMonoidHom)
    (θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin n)) {P : Subgroup X}
    (hPC : P ≤ centralizer ({t} : Set X) ⊓ UnbalancedLayer.coreActionKernel J)
    (hP2 : IsPGroup 2 P) (hP : 2 < Nat.card P) : FooteLit.IsSolomonMember M := by
  classical
  have hCH := S.centralizer_le_normalizer_completion h33 h35 hT13 hML hSch
  have hP0 : P ⊓ normalizer (M : Set X) ≠ ⊥ := by
    intro h0
    have hout : ∀ q ∈ P, q ≠ 1 →
        M.map (MulAut.conj q).toMonoidHom = M.map (MulAut.conj t).toMonoidHom := by
      intro q hq hq1
      rcases S.map_conj_eq_or_of_swap hCH hMH hMpc hne hJM θ (hPC hq).1 (hPC hq).2 with h | h
      · exfalso
        apply hq1
        have h1 : q ∈ P ⊓ normalizer (M : Set X) :=
          mem_inf.mpr ⟨hq, mem_normalizer_iff_map_conj_eq.mpr h⟩
        rwa [h0, mem_bot] at h1
      · exact h
    have key : ∀ q₁ ∈ P, ∀ q₂ ∈ P, q₁ ≠ 1 → q₂ ≠ 1 → q₁ = q₂ := by
      intro q₁ h₁ q₂ h₂ hq₁ hq₂
      have h3 : M.map (MulAut.conj (q₂⁻¹ * q₁)).toMonoidHom = M := by
        rw [map_conj_mul, hout q₁ h₁ hq₁, ← hout q₂ h₂ hq₂, ← map_conj_mul, inv_mul_cancel]
        exact mem_normalizer_iff_map_conj_eq.mp (one_mem _)
      have h1 : q₂⁻¹ * q₁ ∈ P ⊓ normalizer (M : Set X) :=
        mem_inf.mpr ⟨mul_mem (inv_mem h₂) h₁, mem_normalizer_iff_map_conj_eq.mpr h3⟩
      rw [h0, mem_bot] at h1
      exact (inv_mul_eq_one.mp h1).symm
    have hinj : Function.Injective (fun q : ↥P => decide ((q : X) = 1)) := by
      intro q₁ q₂ h
      by_cases h1 : (q₁ : X) = 1
      · have h2 : (q₂ : X) = 1 := by simpa [h1] using h
        exact Subtype.ext (h1.trans h2.symm)
      · have h2 : (q₂ : X) ≠ 1 := by simpa [h1] using h
        exact Subtype.ext (key _ q₁.2 _ q₂.2 h1 h2)
    have h3 := Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at h3
    omega
  obtain ⟨z, hz, hz2⟩ := exists_mem_orderOf_eq_two_of_ne_bot (hP2.to_le inf_le_left) hP0
  obtain ⟨hzP, hzN⟩ := mem_inf.mp hz
  obtain ⟨hzt, hzKJ⟩ := mem_inf.mp (hPC hzP)
  have hzM := S.mem_coreActionKernel_of_swap hCH hMH hMpc hne hJM θ hzN hzKJ
  have hCz := S.centralizer_le_of_kernel h33 h35 hT13 hML hSch hz2 hzt hzKJ
  have hz1 : zpowers z ≠ ⊥ := fun h => by
    rw [zpowers_eq_bot] at h
    rw [h, orderOf_one] at hz2
    omega
  refine Sol78H.isSolomonMember_of_centralizer_le ⟨hMH, hMpc⟩ hz1
    (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz2, pow_one])) (zpowers_le.mpr hzM)
    (zpowers_le.mpr (hCH hzt)) ?_
  rw [UnbalancedLayer.centralizer_zpowers_eq]
  exact hCz

theorem false_of_swap (h33 : Sol78.BalanceLemmaInput) (h35 : SignalizerLemma35)
    (hT13 : Sol76T13.SolomonThm13Simple) (hML : Sol78.MaximalityLemmaInput)
    (hSch : SolAltLit.SchurAlternatingMultiplierInput) (hR1 : SignalizerSwapMemberInput)
    {M : Subgroup X} (hMH : M ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hMpc : IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))))
    (hne : M.map (MulAut.conj t).toMonoidHom ≠ M) (hJM : J ≤ M ⊔ M.map (MulAut.conj t).toMonoidHom)
    (eM : Nonempty (↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin n))) : False := by
  obtain ⟨θ⟩ := eM
  have hCH := S.centralizer_le_normalizer_completion h33 h35 hT13 hML hSch
  have htH := hCH (mem_centralizer_singleton_iff.mpr rfl)
  have hmM : FooteLit.IsSolomonMember M := by
    by_cases hsmall : ∀ P : Subgroup X,
        P ≤ centralizer ({t} : Set X) ⊓ UnbalancedLayer.coreActionKernel J →
          IsPGroup 2 P → Nat.card P ≤ 2
    · exact hR1 X t J n e E D S hCH M hMH hMpc hne hJM ⟨θ⟩ hsmall
    · push Not at hsmall
      obtain ⟨P, hPC, hP2, hP⟩ := hsmall
      exact S.isSolomonMember_of_swap_of_two_lt h33 h35 hT13 hML hSch hMH hMpc hne hJM θ hPC hP2 hP
  have hmMt := Sol76.isSolomonMember_map (MulAut.conj t) hmM
  obtain ⟨hMtH, hMtpc⟩ := isPComponent_conj hMH hMpc htH
  have eMt : Nonempty ((M.map (MulAut.conj t).toMonoidHom) ⧸
      pPrimeCore 2 (M.map (MulAut.conj t).toMonoidHom) ≃* alternatingGroup (Fin n)) :=
    ⟨(Sol78.coreQuotCongr
      (M.equivMapOfInjective (MulAut.conj t).toMonoidHom (MulAut.conj t).injective)).symm.trans θ⟩
  exact hne (S.eq_of_isPComponent_alt_of_member hT13 hML hSch hMtH hMH hMtpc hMpc hmMt hmM eMt
    ⟨θ⟩)

end Sig36

theorem swapAltExclusion_of_member (h33 : Sol78.BalanceLemmaInput) (h35 : SignalizerLemma35)
    (hT13 : Sol76T13.SolomonThm13Simple) (hML : Sol78.MaximalityLemmaInput)
    (hSch : SolAltLit.SchurAlternatingMultiplierInput) (hR1 : SignalizerSwapMemberInput) :
    SignalizerSwapAltExclusion := by
  intro X _ _ _ t J n e E D S _ M hMH hMpc hne hJM eM
  exact S.false_of_swap h33 h35 hT13 hML hSch hR1 hMH hMpc hne hJM eM

end CFSG.ComponentClassification.SolMax
