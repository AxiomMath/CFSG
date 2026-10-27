module

public import CFSG.GH74.GLS.TwoThin.PumpData
public import CFSG.LocalAnalysis.ComponentClassification.GS82DPrimeBasic

public section

namespace CFSG.ComponentClassification.GS82PumpInputs.DPrime

open CFSG Subgroup GH74.GLS GH74.GLS.TwoThin CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

variable {Y : Type} [Group Y] [Finite Y]

theorem map_eq_range_swapDiag {t : Y} (ht : orderOf t = 2) {Λ : Subgroup Y}
    (hΛC : Λ ≤ centralizer ({t} : Set Y))
    (hΛ : TwoComponents.IsTwoComponent (Λ.subgroupOf (centralizer ({t} : Set Y))))
    {L : Subgroup (barQ Y)} (hL : CFSG.IsComponent L) (hAB : ⁅L, conjSub (barMk Y t)⁻¹ L⁆ = ⊥)
    (hΛδ : Λ.map (barMk Y) ≤ (swapDiag hAB).range) :
    Λ.map (barMk Y) = (swapDiag hAB).range := by
  set Δ := (swapDiag hAB).range with hΔ
  have htinv : (barMk Y t)⁻¹ = barMk Y t := inv_eq_self_of_orderOf_eq_two (orderOf_barMk ht)
  have hP := isTwoComponent_map_barMk ht hΛC hΛ
  have hsub :
      ((Λ.map (barMk Y)).subgroupOf (centralizer ({barMk Y t} : Set (barQ Y)))).IsSubnormal :=
    Components.mathlib_subnormal_of_chain hP.1 Subgroup.IsSubnormal.top
  have hΔC : Δ ≤ centralizer ({barMk Y t} : Set (barQ Y)) := by
    rintro _ ⟨x, rfl⟩
    exact swapDiag_mem_centralizer hAB htinv x
  have hsubΔ : ((Λ.map (barMk Y)).subgroupOf Δ).IsSubnormal := isSubnormal_inf_subgroupOf hsub hΔC
  have hΔq : Open.IsQuasisimple ↥Δ :=
    isQuasisimple_range_swapDiag hAB (assembly_isQuasisimple_of_isComponent hL)
  have hperf : ⁅Λ, Λ⁆ = Λ := commutator_self_of_isTwoComponent hΛC hΛ
  have hperfb : ⁅Λ.map (barMk Y), Λ.map (barMk Y)⁆ = Λ.map (barMk Y) := by
    rw [← Subgroup.map_commutator, hperf]
  have : Group.IsPerfect ↥((Λ.map (barMk Y)).subgroupOf Δ) := by
    have : Group.IsPerfect ↥(Λ.map (barMk Y)) := Subgroup.isPerfect_iff.mpr hperfb
    exact Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hΛδ).symm.toMonoidHom)
      (subgroupOfEquivOfLe hΛδ).symm.surjective
  rcases Quasisimple.perfect_subnormal_eq_bot_or_eq_top hΔq _
      (Components.chain_of_mathlib_subnormal hsubΔ) with h | h
  · exfalso
    have hbot : Λ.map (barMk Y) = ⊥ :=
      (Subgroup.subgroupOf_eq_bot.mp h).eq_bot_of_le hΛδ
    exact map_barMk_ne_bot_of_perfect hperf (ne_bot_of_isTwoComponent hΛ) hbot
  · exact le_antisymm hΛδ (Subgroup.subgroupOf_eq_top.mp h)

theorem nonempty_fusionZStarQuot_equiv {t : Y} (ht : orderOf t = 2) {Λ : Subgroup Y}
    (hΛC : Λ ≤ centralizer ({t} : Set Y))
    (hΛ : TwoComponents.IsTwoComponent (Λ.subgroupOf (centralizer ({t} : Set Y))))
    {L : Subgroup (barQ Y)} (hL : CFSG.IsComponent L) (hAB : ⁅L, conjSub (barMk Y t)⁻¹ L⁆ = ⊥)
    (hΛδ : Λ.map (barMk Y) ≤ (swapDiag hAB).range)
    {M : Subgroup Y} (hM : TwoComponents.IsTwoComponent M) (hML : M.map (barMk Y) = L) :
    Nonempty (↥Λ ⧸ Open.fusionZStar ↥Λ ≃* ↥M ⧸ Open.fusionZStar ↥M) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have heq := map_eq_range_swapDiag ht hΛC hΛ hL hAB hΛδ
  set Λb := Λ.map (barMk Y) with hΛb
  let δ' : ↥L →* ↥Λb := (swapDiag hAB).codRestrict Λb fun l => by rw [heq]; exact ⟨l, rfl⟩
  have hδ' : Function.Surjective δ' := by
    rintro ⟨a, ha⟩
    rw [heq] at ha
    obtain ⟨l, rfl⟩ := ha
    exact ⟨l, rfl⟩
  let πΛ : ↥Λ →* ↥Λb := ((barMk Y).comp Λ.subtype).codRestrict Λb fun l => ⟨l, l.2, rfl⟩
  have hπΛ : Function.Surjective πΛ := by
    rintro ⟨_, l, hl, rfl⟩
    exact ⟨⟨l, hl⟩, rfl⟩
  have hπΛk : Odd (Nat.card πΛ.ker) := by
    have hk : πΛ.ker = ((barMk Y).domRestrict Λ).ker := MonoidHom.ker_codRestrict _ _ _
    rw [hk]
    exact OddKernel.odd_card_restriction_kernel (barMk Y) odd_card_ker_barMk Λ
  obtain ⟨eΛ⟩ := nonempty_coreQuotEquiv_of_surjective πΛ hπΛ hπΛk
  let ψ : ↥L →* ↥Λ ⧸ pPrimeCore 2 ↥Λ :=
    eΛ.symm.toMonoidHom.comp ((QuotientGroup.mk' (pPrimeCore 2 ↥Λb)).comp δ')
  have hψ : Function.Surjective ψ :=
    eΛ.symm.surjective.comp ((QuotientGroup.mk'_surjective _).comp hδ')
  have hΛpc : IsPComponent 2 (Λ.subgroupOf (centralizer ({t} : Set Y))) :=
    (CatalogueBAlternating.pComponent_two_iff _).mpr hΛ
  have hΛq : IsQuasisimple (↥Λ ⧸ pPrimeCore 2 ↥Λ) :=
    CatalogueBPrimeJoin.quasisimple_primeCore_quotient_of_equiv 2 (subgroupOfEquivOfLe hΛC)
      (CatalogueBHeldSmallCore.pComponent_coreQuotient_quasisimple 2 _ hΛpc)
  obtain ⟨e₁⟩ := nonempty_centerQuotEquiv_of_surjective hL.1 hΛq ψ hψ
  have hMsub : M.IsSubnormal := Components.mathlib_subnormal_of_chain hM.1 Subgroup.IsSubnormal.top
  obtain ⟨eM⟩ := hat_equiv_map hMsub
  let eM' : ↥M ⧸ pPrimeCore 2 ↥M ≃* ↥L := eM.trans (MulEquiv.subgroupCongr hML)
  exact ⟨(Sol78.coreQuotientCenterEquiv ↥Λ).symm.trans
    (e₁.symm.trans ((Sol78.centerQuotCongr eM').symm.trans (Sol78.coreQuotientCenterEquiv ↥M)))⟩

theorem exists_sl2_below {M : Subgroup Y} {L : Subgroup (barQ Y)} (hML : M.map (barMk Y) = L)
    {v : Y} (hvM : v ∈ M) (hvv : v * v = 1) (hvL : ∀ x ∈ L, barMk Y v * x = x * barMk Y v)
    {P : Subgroup (barQ Y)} (hPL : P ≤ L) (hPp : Group.IsPerfect ↥P) {q₀ : ℕ}
    (hPSL : HarrisLit.IsSLTwoOver q₀ (↥P ⧸ pPrimeCore 2 ↥P)) (hvP : barMk Y v ∈ P) :
    ∃ N : Subgroup Y, N ≤ M ∧ N ≤ centralizer ({v} : Set Y) ∧ ⁅N, N⁆ = N ∧
      HarrisLit.IsSLTwoOver q₀ (↥N ⧸ pPrimeCore 2 ↥N) ∧ v ∈ N := by
  set π := barMk Y with hπ
  set K := M ⊓ P.comap π with hK
  set O' := M ⊓ π.ker with hO'
  have hO'odd : Odd (Nat.card O') := odd_card_ker_barMk.of_dvd_nat (card_dvd_of_le inf_le_right)
  have hO'K : O' ≤ K := by
    intro o ho
    obtain ⟨hoM, hok⟩ := Subgroup.mem_inf.mp ho
    refine Subgroup.mem_inf.mpr ⟨hoM, mem_comap.mpr ?_⟩
    rw [(MonoidHom.mem_ker).mp hok]
    exact one_mem P
  have hvO : ∀ o ∈ O', v * o * v⁻¹ ∈ O' := by
    intro o ho
    obtain ⟨hoM, hok⟩ := Subgroup.mem_inf.mp ho
    exact Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem hvM hoM) (inv_mem hvM),
      (MonoidHom.normal_ker π).conj_mem o hok v⟩
  have hcomm : ∀ k ∈ K, ⁅k, v⁆ ∈ O' := by
    intro k hk
    obtain ⟨hkM, hkP⟩ := Subgroup.mem_inf.mp hk
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hkM hvM) (inv_mem hkM)) (inv_mem hvM)
    · rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact (hvL _ (hPL (mem_comap.mp hkP))).symm
  have hcov := exists_commute_mul_mem_of_odd hO'odd hO'K hvv hvO hcomm
  set Z := K ⊓ centralizer ({v} : Set Y) with hZ
  let πZ : ↥Z →* ↥P := (π.comp Z.subtype).codRestrict P fun z => mem_comap.mp (mem_inf.mp z.2).1.2
  have hπZ : Function.Surjective πZ := by
    rintro ⟨p, hp⟩
    have hp' : p ∈ M.map π := by rw [hML]; exact hPL hp
    obtain ⟨m, hm, rfl⟩ := hp'
    obtain ⟨c, hcK, hvc, o, ho, rfl⟩ := hcov m ⟨hm, hp⟩
    refine ⟨⟨c, hcK, mem_centralizer_singleton_iff.mpr hvc.symm⟩, Subtype.ext ?_⟩
    change π c = π (c * o)
    rw [map_mul, (MonoidHom.mem_ker).mp ho.2, mul_one]
  have hπZk : Odd (Nat.card πZ.ker) := by
    have hk : πZ.ker = (π.domRestrict Z).ker := MonoidHom.ker_codRestrict _ _ _
    rw [hk]
    exact OddKernel.odd_card_restriction_kernel π odd_card_ker_barMk Z
  set Nz := CFSG.perfectResidual ↥Z with hNz
  have hNzp : Group.IsPerfect ↥Nz := (perfect_residual_characterization (G := ↥Z)).2.2.1
  have : Nz.Characteristic := (perfect_residual_characterization (G := ↥Z)).2.1
  have hNzmap : Nz.map πZ = ⊤ := by
    have h1 := RankThreeCoreUniqueness.Helpers.finite_perfectResidual_map_eq πZ hπZ
    have htop : Group.IsPerfect ↥(⊤ : Subgroup ↥P) :=
      Group.IsPerfect.ofSurjective (f := (Subgroup.topEquiv (G := ↥P)).symm.toMonoidHom)
        (Subgroup.topEquiv (G := ↥P)).symm.surjective
    have h2 := RankThreeCoreUniqueness.Helpers.perfect_subgroup_le_perfectResidual ⊤ htop
    exact top_unique (h2.trans h1.symm.le)
  let πN : ↥Nz →* ↥P := πZ.domRestrict Nz
  have hπN : Function.Surjective πN := by
    intro p
    have hp : p ∈ Nz.map πZ := by rw [hNzmap]; exact mem_top p
    obtain ⟨n, hn, rfl⟩ := hp
    exact ⟨⟨n, hn⟩, rfl⟩
  obtain ⟨eN⟩ := nonempty_coreQuotEquiv_of_surjective πN hπN
    (OddKernel.odd_card_restriction_kernel πZ hπZk Nz)
  have hvZ : v ∈ Z := ⟨⟨hvM, hvP⟩, mem_centralizer_singleton_iff.mpr rfl⟩
  have hvNz : (⟨v, hvZ⟩ : ↥Z) ∈ Nz := by
    have hv2 : (⟨v, hvZ⟩ : ↥Z) ^ (2 ^ 1) = 1 := Subtype.ext (by simpa [pow_two] using hvv)
    refine le_of_isPGroup_of_map_le πZ hπZ hπZk (zpowers ⟨v, hvZ⟩) Nz
      (isPGroup_zpowers_of_pow_eq_one hv2)
      (Components.chain_of_mathlib_subnormal (Subgroup.Normal.isSubnormal inferInstance))
      (by rw [hNzmap]; exact le_top) (mem_zpowers _)
  let eNz : ↥Nz ≃* ↥(Nz.map Z.subtype) := Nz.equivMapOfInjective Z.subtype Z.subtype_injective
  refine ⟨Nz.map Z.subtype, (map_subtype_le Nz).trans (inf_le_left.trans inf_le_left),
    (map_subtype_le Nz).trans inf_le_right, ?_,
    isSLTwoOver_of_mulEquiv eNz (isSLTwoOver_of_coreEquiv eN.symm hPSL), ⟨_, hvNz, rfl⟩⟩
  rw [← Subgroup.map_commutator, Subgroup.isPerfect_iff.mp hNzp]

end CFSG.ComponentClassification.GS82PumpInputs.DPrime
