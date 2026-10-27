module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSigSwapB
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSigExact

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup

variable {X : Type} [Group X]

theorem fusionZStar_le_coreActionKernel (M : Subgroup X) :
    (Open.fusionZStar ↥M).map M.subtype ≤ UnbalancedLayer.coreActionKernel M := by
  rintro _ ⟨u', hu'Z, rfl⟩
  refine ⟨le_normalizer u'.2, fun j hj => ?_⟩
  have hzc : QuotientGroup.mk' (pPrimeCore 2 ↥M) u' ∈ center (↥M ⧸ pPrimeCore 2 ↥M) := by
    have hu'Z' : u' ∈ Open.fusionZStar ↥M := hu'Z
    rw [Sol78.fusionZStar_eq_comap, mem_comap] at hu'Z'
    exact hu'Z'
  have hc := mem_center_iff.mp hzc (QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨j, hj⟩)
  have h1 : QuotientGroup.mk' (pPrimeCore 2 ↥M) ((⟨j, hj⟩ : ↥M)⁻¹ * u'⁻¹ * ⟨j, hj⟩ * u') = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, mul_assoc _ _ (QuotientGroup.mk' _ u'), hc]
    group
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact ⟨_, h1, by simp⟩

theorem two_dvd_card_fusionZStar [Finite X] {M : Subgroup X}
    (hne : Open.fusionZStar ↥M ≠ pPrimeCore 2 ↥M) : 2 ∣ Nat.card ↥(Open.fusionZStar ↥M) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hz, hzO⟩ : ∃ z ∈ Open.fusionZStar ↥M, z ∉ pPrimeCore 2 ↥M := by
    by_contra h
    push Not at h
    exact hne (le_antisymm h (Sol78.pPrimeCore_le_fusionZStar _))
  have hzc : QuotientGroup.mk' (pPrimeCore 2 ↥M) z ∈ center (↥M ⧸ pPrimeCore 2 ↥M) := by
    rw [Sol78.fusionZStar_eq_comap, mem_comap] at hz
    exact hz
  have hZ2 : IsPGroup 2 (center (↥M ⧸ pPrimeCore 2 ↥M)) :=
    Sol78.center_isPGroup_two (pPrimeCore_quotient_pPrimeCore_eq_bot 2)
  obtain ⟨k, hk⟩ := hZ2 ⟨_, hzc⟩
  have hne1 : QuotientGroup.mk' (pPrimeCore 2 ↥M) z ≠ 1 := by
    rwa [QuotientGroup.mk'_apply, Ne, QuotientGroup.eq_one_iff]
  have hk' : (QuotientGroup.mk' (pPrimeCore 2 ↥M) z) ^ 2 ^ k = 1 := congrArg Subtype.val hk
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk')
  have h2 : 2 ∣ orderOf (QuotientGroup.mk' (pPrimeCore 2 ↥M) z) := by
    rcases j with _ | j
    · rw [pow_zero, orderOf_eq_one_iff] at hj
      exact absurd hj hne1
    · rw [hj, pow_succ]
      exact dvd_mul_left 2 _
  have h3 := orderOf_map_dvd (QuotientGroup.mk' (pPrimeCore 2 ↥M)) z
  have h4 := orderOf_dvd_natCard (⟨z, hz⟩ : ↥(Open.fusionZStar ↥M))
  rw [Subgroup.orderOf_mk] at h4
  exact h2.trans (h3.trans h4)

theorem sup_mem_normalizer {A B : Subgroup X} {g : X} (hA : g ∈ normalizer (A : Set X))
    (hB : g ∈ normalizer (B : Set X)) : g ∈ normalizer ((A ⊔ B : Subgroup X) : Set X) := by
  rw [mem_normalizer_iff_map_conj_eq] at hA hB ⊢
  rw [Subgroup.map_sup, hA, hB]

theorem sup_le_normalizer_core_sup {M M' : Subgroup X} (hMM' : M ≤ normalizer (M' : Set X))
    (hM'M : M' ≤ normalizer (M : Set X)) :
    M ⊔ M' ≤ normalizer (((pPrimeCore 2 ↥M).map M.subtype ⊔
      (pPrimeCore 2 ↥M').map M'.subtype : Subgroup X) : Set X) := by
  refine sup_le (fun x hx => ?_) (fun x hx => ?_)
  · exact sup_mem_normalizer (le_normalizer_pPrimeCore (le_normalizer hx))
      (le_normalizer_pPrimeCore (hMM' hx))
  · exact sup_mem_normalizer (le_normalizer_pPrimeCore (hM'M hx))
      (le_normalizer_pPrimeCore (le_normalizer hx))

theorem commutator_mem_sup_core {M M' : Subgroup X} (hMM' : M ≤ normalizer (M' : Set X))
    (hM'M : M' ≤ normalizer (M : Set X)) {z : X} (hzM : z ∈ UnbalancedLayer.coreActionKernel M)
    (hzM' : z ∈ UnbalancedLayer.coreActionKernel M') {g : X} (hg : g ∈ M ⊔ M') :
    g⁻¹ * z⁻¹ * g * z ∈ (pPrimeCore 2 ↥M).map M.subtype ⊔ (pPrimeCore 2 ↥M').map M'.subtype := by
  set Q := (pPrimeCore 2 ↥M).map M.subtype ⊔ (pPrimeCore 2 ↥M').map M'.subtype with hQ
  have hQN : M ⊔ M' ≤ normalizer (Q : Set X) := sup_le_normalizer_core_sup hMM' hM'M
  let S' : Subgroup X :=
    { carrier := {g | g ∈ M ⊔ M' ∧ g⁻¹ * z⁻¹ * g * z ∈ Q}
      one_mem' := ⟨one_mem _, by simp⟩
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨mul_mem ha hb, ?_⟩
        have h1 : b⁻¹ * (a⁻¹ * z⁻¹ * a * z) * b ∈ Q := by
          have := (mem_normalizer_iff.mp (hQN (inv_mem hb)) _).mp ha'
          simpa [mul_assoc] using this
        have h2 : (a * b)⁻¹ * z⁻¹ * (a * b) * z =
            b⁻¹ * (a⁻¹ * z⁻¹ * a * z) * b * (b⁻¹ * z⁻¹ * b * z) := by group
        rw [h2]
        exact mul_mem h1 hb'
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨inv_mem ha, ?_⟩
        have h1 : a * (a⁻¹ * z⁻¹ * a * z)⁻¹ * a⁻¹ ∈ Q :=
          (mem_normalizer_iff.mp (hQN ha) _).mp (inv_mem ha')
        have h2 : a⁻¹⁻¹ * z⁻¹ * a⁻¹ * z = a * (a⁻¹ * z⁻¹ * a * z)⁻¹ * a⁻¹ := by group
        rw [h2]
        exact h1 }
  have hle : M ⊔ M' ≤ S' := by
    refine sup_le (fun x hx => ⟨mem_sup_left hx, mem_sup_left (hzM.2 x hx)⟩)
      (fun x hx => ⟨mem_sup_right hx, mem_sup_right (hzM'.2 x hx)⟩)
  exact (hle hg).2

namespace Sig36

variable [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X} {n : ℕ}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)} {E : Subgroup X} {D : Finset (Fin n)}
  (S : Sig36 X t J n e E D)
include S

theorem false_of_cover_swap (h33 : Sol78.BalanceLemmaInput) (h35 : SignalizerLemma35)
    (hT13 : Sol76T13.SolomonThm13Simple) (hML : Sol78.MaximalityLemmaInput)
    (hSch : SolAltLit.SchurAlternatingMultiplierInput) (hN1 : TwoGroupAltCoverExclusion)
    {M : Subgroup X}
    (hMH : M ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hMpc : IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))))
    (hne : M.map (MulAut.conj t).toMonoidHom ≠ M)
    (hJM : J ≤ M ⊔ M.map (MulAut.conj t).toMonoidHom)
    (eM : ↥M ⧸ Open.fusionZStar ↥M ≃* alternatingGroup (Fin n))
    (hZ : Open.fusionZStar ↥M ≠ pPrimeCore 2 ↥M) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn9 := S.nine_le
  have hCH := S.centralizer_le_normalizer_completion h33 h35 hT13 hML hSch
  set H := normalizer (Sol78.signalizerCompletion E E : Set X) with hHdef
  have htH : t ∈ H := hCH (mem_centralizer_singleton_iff.mpr rfl)
  have htt : t * t = 1 := by rw [← sq, ← S.pair.1.1, pow_orderOf_eq_one]
  set Mt := M.map (MulAut.conj t).toMonoidHom with hMtdef
  obtain ⟨hMtH, hMtpc⟩ := isPComponent_conj hMH hMpc htH
  have hMtK : Mt ≤ UnbalancedLayer.coreActionKernel M :=
    GSThmB.B5a.le_coreActionKernel_of_ne hMH hMtH hMpc hMtpc (Ne.symm hne)
  have hMK : M ≤ UnbalancedLayer.coreActionKernel Mt :=
    GSThmB.B5a.le_coreActionKernel_of_ne hMtH hMH hMtpc hMpc hne
  have hMMt : M ≤ normalizer (Mt : Set X) := fun x hx => (hMK hx).1
  have hMtM : Mt ≤ normalizer (M : Set X) := fun x hx => (hMtK hx).1
  set A := (Open.fusionZStar ↥M).map M.subtype with hAdef
  set At := A.map (MulAut.conj t).toMonoidHom with hAtdef
  have hAt : At = (Open.fusionZStar ↥Mt).map Mt.subtype := by
    let φ : ↥M ≃* ↥Mt :=
      M.equivMapOfInjective (MulAut.conj t).toMonoidHom (MulAut.conj t).injective
    have h1 := FooteLit.fusionZStar_map_mulEquiv φ
    rw [← h1, Subgroup.map_map, hAtdef, hAdef, Subgroup.map_map]
    rfl
  have hAtMt : At ≤ Mt := by rw [hAt]; exact map_subtype_le _
  set K₀ := A ⊔ At with hK₀def
  have hK₀M : K₀ ≤ UnbalancedLayer.coreActionKernel M :=
    sup_le (fusionZStar_le_coreActionKernel M) (hAtMt.trans hMtK)
  have hK₀Mt : K₀ ≤ UnbalancedLayer.coreActionKernel Mt := by
    refine sup_le ((map_subtype_le _).trans hMK) ?_
    rw [hAt]
    exact fusionZStar_le_coreActionKernel Mt
  have hK₀H : K₀ ≤ H := sup_le ((map_subtype_le _).trans hMH) (hAtMt.trans hMtH)
  have htK₀ : t ∈ normalizer (K₀ : Set X) := by
    have h1 : At.map (MulAut.conj t).toMonoidHom = A := by
      rw [hAtdef, ← map_conj_mul, htt]
      ext y
      simp
    rw [mem_normalizer_iff_map_conj_eq]
    change (A ⊔ At).map (MulAut.conj t).toMonoidHom = A ⊔ At
    rw [Subgroup.map_sup, h1, sup_comm]
  have hK₀even : Even (Nat.card K₀) := by
    have h1 : Nat.card A ∣ Nat.card K₀ := card_dvd_of_le le_sup_left
    have h2 : 2 ∣ Nat.card A := by
      rw [hAdef, card_map_of_injective M.subtype_injective]
      exact two_dvd_card_fusionZStar hZ
    exact even_iff_two_dvd.mpr (h2.trans h1)
  have ht2 : t ^ 2 ^ 1 = 1 := by rw [pow_one, ← S.pair.1.1, pow_orderOf_eq_one]
  obtain ⟨z, hzK₀, hz, hzt⟩ := exists_involution_commute_of_even ht2 htK₀ hK₀even
  have hzM := hK₀M hzK₀
  have hzMt := hK₀Mt hzK₀
  have hzH := hK₀H hzK₀
  have hztc : z ∈ centralizer ({t} : Set X) := mem_centralizer_singleton_iff.mpr hzt
  have hzJ : z ∈ UnbalancedLayer.coreActionKernel J := by
    have hJn := S.centralizer_le_normalizer hT13 hML hSch hztc
    refine ⟨hJn, fun j hj => ?_⟩
    have hw : j⁻¹ * z⁻¹ * j * z ∈ J := by
      have h1 : z⁻¹ * j * z ∈ J := by
        have := (mem_normalizer_iff.mp (inv_mem hJn) j).mp hj
        rwa [inv_inv] at this
      have h2 : j⁻¹ * z⁻¹ * j * z = j⁻¹ * (z⁻¹ * j * z) := by group
      rw [h2]
      exact mul_mem (inv_mem hj) h1
    have hwQ := commutator_mem_sup_core hMMt hMtM hzM hzMt (hJM hj)
    set Q := (pPrimeCore 2 ↥M).map M.subtype ⊔ (pPrimeCore 2 ↥Mt).map Mt.subtype with hQdef
    have hQodd : Odd (Nat.card Q) := by
      have hON : (pPrimeCore 2 ↥M).map M.subtype ≤
          normalizer (((pPrimeCore 2 ↥Mt).map Mt.subtype : Subgroup X) : Set X) :=
        fun x hx => le_normalizer_pPrimeCore (hMMt (map_subtype_le _ hx))
      have h1 := Sol78.card_sup_mul_card_inf' hON
      have hO1 : Odd (Nat.card ((pPrimeCore 2 ↥M).map M.subtype)) := by
        rw [card_map_of_injective M.subtype_injective]
        exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
      have hO2 : Odd (Nat.card ((pPrimeCore 2 ↥Mt).map Mt.subtype)) := by
        rw [card_map_of_injective Mt.subtype_injective]
        exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
      exact (hO1.mul hO2).of_dvd_nat ⟨_, h1.symm⟩
    have hle : J ⊓ Q ≤ (pPrimeCore 2 ↥J).map J.subtype := by
      refine le_pPrimeCore_map inf_le_left ?_ ?_
      · intro g hg
        exact inf_mem_normalizer' (le_normalizer hg)
          (sup_le_normalizer_core_sup hMMt hMtM (hJM hg))
      · exact Nat.Coprime.coprime_dvd_right (card_dvd_of_le inf_le_right)
          (Nat.coprime_two_left.mpr hQodd)
    exact hle ⟨hw, hwQ⟩
  have hCz := S.centralizer_le_of_kernel h33 h35 hT13 hML hSch hz hztc hzJ
  have hz2 : IsPGroup 2 (zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz, pow_one])
  have hMq : IsQuasisimple (↥M ⧸ pPrimeCore 2 ↥M) :=
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 M H hMH).mp hMpc).2.2
  have hMsub : (M.subgroupOf H).IsSubnormal := hMpc.choose_spec.2.1
  have hEM : zpowers z ≤ UnbalancedLayer.coreActionKernel M := zpowers_le.mpr hzM
  set Mz := GSLit.fixedLayer M (zpowers z) with hMzdef
  have hMzpc := GSLit.fixedLayer_isPComponent hMH hMsub (zpowers_le.mpr hzH) hEM hz2 hMq
  have hCzH : centralizer ((zpowers z : Subgroup X) : Set X) ≤ H := by
    rw [UnbalancedLayer.centralizer_zpowers_eq]
    exact hCz
  rw [inf_of_le_right hCzH] at hMzpc
  have hMzC : Mz ≤ centralizer ((zpowers z : Subgroup X) : Set X) :=
    (GSLit.fixedLayer_le_inf M (zpowers z)).trans inf_le_right
  obtain ⟨eMz⟩ := fixedLayer_coreQuot_equiv hMq hEM hz2
  have hZz : Open.fusionZStar ↥Mz ≠ pPrimeCore 2 ↥Mz := by
    intro h
    apply hZ
    rw [Sol78.fusionZStar_eq_iff] at h ⊢
    have h1 := map_center_eq eMz
    rw [h, Subgroup.map_bot] at h1
    exact h1.symm
  have hz1 : zpowers z ≠ ⊥ := by
    intro h
    rw [zpowers_eq_bot] at h
    rw [h, orderOf_one] at hz
    omega
  exact hZz (hN1 X S.nonab S.kProper S.unbal S.notU (zpowers z) n Mz hz1 hz2 S.pair.2.1 hn9
    hMzC hMzpc ⟨(Sol78.fusionZStarQuotOfCore eMz).trans eM⟩)

theorem exists_fixed_component (h33 : Sol78.BalanceLemmaInput) (h35 : SignalizerLemma35)
    (hT13 : Sol76T13.SolomonThm13Simple) (hML : Sol78.MaximalityLemmaInput)
    (hSch : SolAltLit.SchurAlternatingMultiplierInput) (hSwap : SignalizerSwapAltExclusion)
    (hN1 : TwoGroupAltCoverExclusion) :
    ∃ M : Subgroup X, M ≤ normalizer (Sol78.signalizerCompletion E E : Set X) ∧
      IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))) ∧
      t ∈ normalizer (M : Set X) ∧ J ≤ M := by
  obtain ⟨M, hMH, hMpc, h | ⟨hne, hJM, ⟨eM⟩, hZ⟩⟩ :=
    S.exists_fixed_or_cover_swap h33 h35 hT13 hML hSch hSwap
  · exact ⟨M, hMH, hMpc, h.1, h.2⟩
  · exact (S.false_of_cover_swap h33 h35 hT13 hML hSch hN1 hMH hMpc hne hJM eM hZ).elim

end Sig36

end CFSG.ComponentClassification.SolMax
