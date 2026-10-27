module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig33R
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSmallA

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

@[expose] def SignalizerFivePumpBalanceInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    Assembly.KProper Blueprint.Catalog X →
    (∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥) →
    ¬ OutcomeLocal.UOutcome X →
    ∀ (t : X) (J : Subgroup X), Sol78.IsSolomonPair t J 9 →
    ∀ (θ : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin 9)) (c e₀ : X) (he₀ : e₀ ∈ J),
      orderOf c = 2 → t * c = c * t → c ∈ normalizer (J : Set X) →
      c * e₀⁻¹ ∈ UnbalancedLayer.coreActionKernel J → (coreImage θ he₀).support.card = 4 →
    ∀ Jc : Subgroup X, Jc ≤ J ⊓ centralizer ({c} : Set X) →
      IsPComponent 2 (Jc.subgroupOf (centralizer ({t} : Set X) ⊓ centralizer ({c} : Set X))) →
      (∀ (x : X) (hx : x ∈ J), x * c = c * x → (∃ k : ℕ, x ^ 2 ^ k = 1) →
        (coreImage θ hx).support ⊆ (coreImage θ he₀).supportᶜ → x ∈ Jc) →
      (∀ x ∈ Jc, ∃ hx : x ∈ J, (coreImage θ hx).support ⊆ (coreImage θ he₀).supportᶜ) →
    ∀ χ : ↥Jc ⧸ pPrimeCore 2 ↥Jc ≃*
        alternatingGroup ↥((coreImage θ he₀).supportᶜ : Finset (Fin 9)),
      (∀ (x : ↥Jc) (hx : (x : X) ∈ J),
        Perm.ofSubtype ((χ (x : ↥Jc ⧸ pPrimeCore 2 ↥Jc) : alternatingGroup _) :
          Perm ↥((coreImage θ he₀).supportᶜ : Finset (Fin 9))) = coreImage θ hx) →
    ∀ M : Subgroup X, M ≤ centralizer ({c} : Set X) →
      IsPComponent 2 (M.subgroupOf (centralizer ({c} : Set X))) →
      Jc ≤ M ⊔ M.map (MulAut.conj t).toMonoidHom →
      IsPComponent 2 (Jc.subgroupOf ((M ⊔ M.map (MulAut.conj t).toMonoidHom) ⊓
        centralizer ({t} : Set X))) →
      ¬ Jc ≤ UnbalancedLayer.coreActionKernel M →
    ∀ a : X, orderOf a = 2 → a * c = c * a → a * t = t * a → a ∈ normalizer (J : Set X) →
      (∃ (j₀ : X) (hj₀ : j₀ ∈ J), a * j₀⁻¹ ∈ UnbalancedLayer.coreActionKernel J ∧
        (coreImage θ hj₀).support.card ≤ 4) →
      (∃ (j : X) (hjJ : j ∈ Jc), a * j⁻¹ ∈ UnbalancedLayer.coreActionKernel Jc ∧
        ((χ ((⟨j, hjJ⟩ : ↥Jc) : ↥Jc ⧸ pPrimeCore 2 ↥Jc) : alternatingGroup _) :
          Perm ↥((coreImage θ he₀).supportᶜ : Finset (Fin 9))).support.card ≤ 4) →
      ⁅M, (pPrimeCore 2 ↥(centralizer ({a} : Set X))).map
          (centralizer ({a} : Set X)).subtype ⊓ centralizer ({c} : Set X)⁆ ≤
        (pPrimeCore 2 ↥(centralizer ({c} : Set X))).map (centralizer ({c} : Set X)).subtype

variable {X : Type} [Group X]

theorem nontrivial_coreQuot_of_five {T : Subgroup X}
    (χ : ↥T ⧸ pPrimeCore 2 ↥T ≃* alternatingGroup (Fin 5)) :
    Nontrivial (↥T ⧸ pPrimeCore 2 ↥T) := by
  have : Nontrivial (Fin 5) := Fin.nontrivial_iff_two_le.mpr (by norm_num)
  have : Nontrivial (alternatingGroup (Fin 5)) :=
    alternatingGroup.nontrivial_of_three_le_card (by rw [Nat.card_fin]; norm_num)
  exact χ.toEquiv.nontrivial

theorem exists_pump_in [Finite X] {Y : Subgroup X} {x : X} (hxY : x ∈ Y) (hx : orderOf x = 2)
    {T : Subgroup X} (hTY : T ≤ Y ⊓ centralizer ({x} : Set X))
    (hTpc : IsPComponent 2 (T.subgroupOf (Y ⊓ centralizer ({x} : Set X)))) :
    ∃ M : Subgroup X, M ≤ Y ∧ IsPComponent 2 (M.subgroupOf Y) ∧
      T ≤ M ⊔ M.map (MulAut.conj x).toMonoidHom ∧
      IsPComponent 2 (T.subgroupOf ((M ⊔ M.map (MulAut.conj x).toMonoidHom) ⊓
        centralizer ({x} : Set X))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hx2 : x⁻¹ = x := by
    have h1 : x * x = 1 := by rw [← sq, ← hx, pow_orderOf_eq_one]
    exact inv_eq_of_mul_eq_one_right h1
  set x' : ↥Y := ⟨x, hxY⟩ with hx'def
  have hx' : orderOf x' = 2 := by rw [hx'def, Subgroup.orderOf_mk]; exact hx
  have hTYY : T ≤ Y := hTY.trans inf_le_left
  set T' := T.subgroupOf Y with hT'def
  have hcent : centralizer ({x'} : Set ↥Y) = (Y ⊓ centralizer ({x} : Set X)).subgroupOf Y := by
    rw [centralizer_mk_eq hxY, inf_comm]
  have hT'C : T' ≤ centralizer ({x'} : Set ↥Y) := by
    rw [hcent]
    intro y hy
    exact hTY hy
  have hT'pc : IsPComponent 2 (T'.subgroupOf (centralizer ({x'} : Set ↥Y))) := by
    rw [hcent, hT'def, UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff' inf_le_left 2
      Nat.prime_two]
    exact hTpc
  have hT'E : T' ≤ pLayer ↥Y 2 :=
    FooteLit.le_pLayer_of_isPComponent_centralizer_singleton hx' hT'C hT'pc
  obtain ⟨M₀, hM₀pc, hTM₀, hTM₀pc⟩ :=
    UnbalancedLayer.two_layer_fixed_component_orbit_location hx' hT'C hT'pc hT'E
  set M := M₀.map Y.subtype with hMdef
  have hMY : M ≤ Y := map_subtype_le _
  have hMsub : M.subgroupOf Y = M₀ := by
    change (M₀.map Y.subtype).comap Y.subtype = M₀
    exact comap_map_eq_self_of_injective Y.subtype_injective M₀
  have hconj := map_conjugate_subtype hxY hx2 M₀
  rw [← hx'def] at hconj
  set Mx := M.map (MulAut.conj x).toMonoidHom with hMxdef
  have hsup : (M₀ ⊔ conjugate M₀ x').map Y.subtype = M ⊔ Mx := by
    rw [Subgroup.map_sup, hconj]
  have hMxY : Mx ≤ Y := by
    rw [← hconj]
    exact map_subtype_le _
  refine ⟨M, hMY, by rw [hMsub]; exact hM₀pc, ?_, ?_⟩
  · rw [← hsup]
    intro y hy
    exact ⟨⟨y, hTYY hy⟩, hTM₀ hy, rfl⟩
  · have hle : (M ⊔ Mx) ⊓ centralizer ({x} : Set X) ≤ Y :=
      inf_le_left.trans (sup_le hMY hMxY)
    have heq : (M₀ ⊔ conjugate M₀ x') ⊓ centralizer ({x'} : Set ↥Y) =
        ((M ⊔ Mx) ⊓ centralizer ({x} : Set X)).subgroupOf Y := by
      rw [centralizer_mk_eq hxY, ← hsup]
      ext y
      simp only [mem_inf, mem_subgroupOf]
      constructor
      · rintro ⟨h1, h2, -⟩
        exact ⟨⟨y, h1, rfl⟩, h2⟩
      · rintro ⟨⟨z, hz, hzy⟩, h2⟩
        have hzy' : z = y := Subtype.ext hzy
        exact ⟨hzy' ▸ hz, h2, y.2⟩
    rw [heq] at hTM₀pc
    rw [← UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff' hle 2 Nat.prime_two]
    exact hTM₀pc

namespace Sol33

variable [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X} {n : ℕ}
  {θ : ↥J ⧸ pPrimeCore 2 ↥J ≃* alternatingGroup (Fin n)} {E : Subgroup X} {D : Finset (Fin n)}
  {y : X} (S : Sol33 X t J n θ E D y)
include S

theorem pumpOracle_of_nine (hbal : Sol78.BalanceTwoComponentInput)
    (hPump : Sol78.AlternatingPumpUpInput) (hN1 : TwoGroupAltCoverExclusion)
    (hFP : SignalizerFivePumpBalanceInput) (hn : n = 9) : S.PumpOracle := by
  intro c e₀ hcB htc hcN hc he₀ he₀2 hce hs4 hτc hdich
  by_cases h0 : (coreImage θ he₀).support.card = 0
  · exact S.exists_balanced_pump hbal hPump hN1 hcB htc hcN hc he₀ he₀2 hce (by omega) hτc hdich
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hne1 : coreImage θ he₀ ≠ 1 := fun h => h0 (by rw [h, Perm.support_one, Finset.card_empty])
  have hτ2 : coreImage θ he₀ * coreImage θ he₀ = 1 := by
    have h1 : (⟨e₀, he₀⟩ : ↥J) * ⟨e₀, he₀⟩ = 1 := Subtype.ext he₀2
    have h3 : θ ((⟨e₀, he₀⟩ : ↥J) : ↥J ⧸ pPrimeCore 2 ↥J) *
        θ ((⟨e₀, he₀⟩ : ↥J) : ↥J ⧸ pPrimeCore 2 ↥J) = 1 := by
      rw [← map_mul, ← QuotientGroup.mk_mul, h1, QuotientGroup.mk_one, map_one]
    exact congrArg Subtype.val h3
  have h4 := four_le_card_support_of_mem_alternatingGroup (coreImage_mem θ he₀) hτ2 hne1
  have hs4' : (coreImage θ he₀).support.card = 4 := by omega
  subst hn
  have hc2 : c * c = 1 := by rw [← sq, ← hc, pow_orderOf_eq_one]
  have htcC : t ∈ centralizer ({c} : Set X) := mem_centralizer_singleton_iff.mpr htc
  obtain ⟨Jc, hJcJ, hJcpc, hinv, hsubP, χ, hχ⟩ :=
    exists_fixed_component_of_acts S.pair.1.2.1 S.pair.1.2.2.1 θ hcN hc2 he₀ hce (by omega)
  have hβ : Fintype.card ↥((coreImage θ he₀).supportᶜ : Finset (Fin 9)) = 5 := by
    rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin]
    omega
  let eJc : ↥Jc ⧸ pPrimeCore 2 ↥Jc ≃* alternatingGroup (Fin 5) :=
    χ.trans (Fintype.equivFinOfCardEq hβ).altCongrHom
  have hJcCt : Jc ≤ centralizer ({t} : Set X) := (hJcJ.trans inf_le_left).trans S.pair.1.2.1
  have hJcCc : Jc ≤ centralizer ({c} : Set X) := hJcJ.trans inf_le_right
  have hJcC : Jc ≤ centralizer ({t} : Set X) ⊓ centralizer ({c} : Set X) := le_inf hJcCt hJcCc
  have hJcperf : ⁅Jc, Jc⁆ = Jc := UnbalancedCorr.commutator_eq_of_isPComponent hJcC hJcpc
  have hres := primeResidual_eq_top_of_isPComponent hJcC hJcpc
  have hJcq := nontrivial_coreQuot_of_five eJc
  have hTY : Jc ≤ centralizer ({c} : Set X) ⊓ centralizer ({t} : Set X) := by
    rw [inf_comm]
    exact hJcC
  have hTpc : IsPComponent 2
      (Jc.subgroupOf (centralizer ({c} : Set X) ⊓ centralizer ({t} : Set X))) := by
    rw [inf_comm]
    exact hJcpc
  obtain ⟨M, hMC, hMpc, hJcM, hJcMpc⟩ := exists_pump_in htcC S.pair.1.1 hTY hTpc
  set Mt := M.map (MulAut.conj t).toMonoidHom with hMtdef
  obtain ⟨hMtC, hMtpc⟩ := isPComponent_conj hMC hMpc htcC
  have hMtt : Mt.map (MulAut.conj t).toMonoidHom = M :=
    map_conj_map_conj_of_mul_self S.t_mul_self M
  have hJcMt : Jc ≤ Mt ⊔ Mt.map (MulAut.conj t).toMonoidHom := by
    rw [hMtt, sup_comm]
    exact hJcM
  have hJcMtpc : IsPComponent 2 (Jc.subgroupOf ((Mt ⊔ Mt.map (MulAut.conj t).toMonoidHom) ⊓
      centralizer ({t} : Set X))) := by
    rw [hMtt, sup_comm]
    exact hJcMpc
  have hJcK : ¬ Jc ≤ UnbalancedLayer.coreActionKernel M := by
    by_cases hfix : Mt = M
    · have hJcM' : Jc ≤ M := by
        have h1 := hJcM
        rwa [hfix, sup_idem] at h1
      exact not_le_coreActionKernel_of_le hJcM' hJcperf hJcq
    · exact not_le_coreActionKernel_of_pump hMC hMpc htcC hJcM hJcCt hJcperf hJcq hfix
  have hJcKt : ¬ Jc ≤ UnbalancedLayer.coreActionKernel Mt := by
    by_cases hfix : Mt = M
    · rw [hfix]
      exact hJcK
    · refine not_le_coreActionKernel_of_pump hMtC hMtpc htcC hJcMt hJcCt hJcperf hJcq ?_
      rw [hMtt]
      exact Ne.symm hfix
  refine ⟨Jc, M, hJcJ, hinv, hMC, hMpc, hJcM, hJcK, fun g hgN hgc hgs =>
    mem_normalizer_of_fixed_component θ hJcCc hres hinv hsubP hgN hgc hgs,
    fun a ha ha1 => ?_⟩
  have ha2 := S.mul_self_of_mem ha
  have hao : orderOf a = 2 := orderOf_eq_prime (by rw [sq]; exact ha2) ha1
  have hac : a * c = c * a := mem_centralizer_iff.mp hcB a ha
  have hat : a * t = t * a := (S.t_comm ha).symm
  have haJN := S.mem_normalizer ha
  have hj₀ : ∃ (j₀ : X) (hj₀ : j₀ ∈ J), a * j₀⁻¹ ∈ UnbalancedLayer.coreActionKernel J ∧
      (coreImage θ hj₀).support.card ≤ 4 := by
    obtain ⟨e₁, he₁, hae₁⟩ := S.exists_acts_like_E ha
    refine ⟨e₁, S.le he₁, hae₁, ?_⟩
    have h1 := Finset.card_le_card (S.supp e₁ (S.le he₁) he₁)
    rw [S.card] at h1
    exact h1
  have hj := S.exists_acts_like hcB he₀ hJcJ hinv hsubP hres hτc hdich χ hχ ha
  exact ⟨hFP X S.nonab S.kProper S.unbal S.notU t J S.pair θ c e₀ he₀ hc htc hcN hce hs4' Jc
      hJcJ hJcpc hinv hsubP χ hχ M hMC hMpc hJcM hJcMpc hJcK a hao hac hat haJN hj₀ hj,
    hFP X S.nonab S.kProper S.unbal S.notU t J S.pair θ c e₀ he₀ hc htc hcN hce hs4' Jc
      hJcJ hJcpc hinv hsubP χ hχ Mt hMtC hMtpc hJcMt hJcMtpc hJcKt a hao hac hat haJN hj₀ hj⟩

end Sol33

theorem balanceLemma_of_nine (hbal : Sol78.BalanceTwoComponentInput)
    (hPump : Sol78.AlternatingPumpUpInput) (hN1 : TwoGroupAltCoverExclusion)
    (hFP : SignalizerFivePumpBalanceInput) [Finite X] [IsSimpleGroup X]
    (hnab : ∃ a b : X, a * b ≠ b * a) (hKP : Assembly.KProper Blueprint.Catalog X)
    (hunb : ∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥)
    (hnU : ¬ OutcomeLocal.UOutcome X) {t : X} {J : Subgroup X}
    (hpair : Sol78.IsSolomonPair t J 9)
    (θ : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin 9)) {E : Subgroup X} (hEJ : E ≤ J)
    (hE : Nonempty (E ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)))
    {D : Finset (Fin 9)} (hD : D.card = 4)
    (hsupp : ∀ x : J, (x : X) ∈ E → ∀ ω ∉ D,
      ((θ (x : J ⧸ pPrimeCore 2 J) : alternatingGroup (Fin 9)) : Equiv.Perm (Fin 9)) ω = ω)
    {y : X} (hy : orderOf y = 2) (hyE : y ∈ centralizer (E : Set X))
    (hyK : y ∈ UnbalancedLayer.coreActionKernel J) (hyJ : y ∉ J) {a b : X}
    (ha : a ∈ E ⊔ zpowers y) (ha1 : a ≠ 1) (hb : b ∈ E ⊔ zpowers y) (hb1 : b ≠ 1) :
    SolAltLit.thetaFunctor E a ⊓ centralizer ({b} : Set X) ≤ SolAltLit.thetaFunctor E b := by
  have hy2 : y * y = 1 := by rw [← sq, ← hy, pow_orderOf_eq_one]
  obtain ⟨t', hpair', hty⟩ := exists_isSolomonPair_commute hpair hyK.1 hy2
  have S : Sol33 X t' J 9 θ E D y :=
    { nonab := hnab
      kProper := hKP
      unbal := hunb
      notU := hnU
      pair := hpair'
      le := hEJ
      klein := hE
      card := hD
      supp := fun x hx hxE => support_coreImage_subset θ hsupp hx hxE
      hy := hy
      hyE := hyE
      hyK := hyK
      hyJ := hyJ
      hty := hty }
  have hPO : S.PumpOracle := S.pumpOracle_of_nine hbal hPump hN1 hFP rfl
  have hdag : ∀ a' ∈ E ⊔ zpowers y, a' ≠ 1 → ∀ b' ∈ E ⊔ zpowers y, b' ≠ 1 →
      DaggerAt E a' b' := fun a' ha' ha'1 b' hb' hb'1 L hLC hLpc hLX =>
    S.dagger hbal hPO ha' ha'1 hb' hb'1 hLC hLpc hLX
  have hEC : ∀ c ∈ E ⊔ zpowers y, E ≤ centralizer ({c} : Set X) := fun c hc x hx =>
    mem_centralizer_singleton_iff.mpr (S.comm_of_mem (mem_sup_left hx) hc)
  exact thetaFunctor_inf_le_of_dagger hbal hE (S.mul_self_of_mem ha) ha1
    (S.mul_self_of_mem hb) hb1 (S.comm_of_mem ha hb) (hEC a ha) (hEC b hb)
    (hdag a ha ha1 b hb hb1) fun e he he1 => hdag a ha ha1 e (mem_sup_left he) he1

end CFSG.ComponentClassification.SolMax
