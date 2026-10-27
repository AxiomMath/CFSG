module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxL32Perm
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxL32Div
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxFiveU
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig33J
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig36P

public section

namespace CFSG.ComponentClassification.SolMax.L32

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

theorem card_coreQuot_eq_of_sup [Finite X] {M L : Subgroup X} (hLM : L ≤ M)
    (hsup : L ⊔ (pPrimeCore 2 ↥M).map M.subtype = M) :
    Nat.card (↥L ⧸ pPrimeCore 2 ↥L) = Nat.card (↥M ⧸ pPrimeCore 2 ↥M) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y := L.subgroupOf M with hYdef
  have hY : Function.Surjective ((QuotientGroup.mk' (pPrimeCore 2 ↥M)).comp Y.subtype) := by
    have h1 : Y ⊔ pPrimeCore 2 ↥M = ⊤ := by
      have h2 : (L ⊔ (pPrimeCore 2 ↥M).map M.subtype).subgroupOf M = ⊤ := by
        rw [hsup]
        exact subgroupOf_self M
      rwa [subgroupOf_sup hLM (map_subtype_le _), subgroupOf_map_subtype_self] at h2
    rw [← MonoidHom.range_eq_top, MonoidHom.range_comp, range_subtype]
    have h2 := congrArg (Subgroup.map (QuotientGroup.mk' (pPrimeCore 2 ↥M))) h1
    rwa [Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h2
  obtain ⟨φ, -⟩ := UnbalancedGS.FixedPrimeLayer.exists_quotient_mulEquiv Y hY
  rw [← Nat.card_congr φ.toEquiv]
  exact Nat.card_congr (Sol78.coreQuotCongr (subgroupOfEquivOfLe hLM).symm).toEquiv

theorem card_coreQuot_map_conj (H : Subgroup X) (g : X) :
    Nat.card (↥(H.map (MulAut.conj g).toMonoidHom) ⧸
      pPrimeCore 2 ↥(H.map (MulAut.conj g).toMonoidHom)) = Nat.card (↥H ⧸ pPrimeCore 2 ↥H) :=
  Nat.card_congr (Sol78.coreQuotCongr
    (H.equivMapOfInjective _ (MulAut.conj g).injective)).symm.toEquiv

theorem not_dvd_card_alt {p m : ℕ} (hp : p.Prime) (hm : 2 ≤ m) (hpm : m < p) :
    ¬ p ∣ Nat.card (alternatingGroup (Fin m)) := by
  intro h
  have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr hm
  rw [nat_card_alternatingGroup, Nat.card_fin] at h
  have h2 : p ∣ m.factorial := h.trans (Nat.div_dvd_of_dvd (Nat.dvd_factorial (by norm_num) hm))
  exact absurd ((Nat.Prime.dvd_factorial hp).mp h2) (by omega)

theorem false_of_trivial_pump (hPump : Sol78.AlternatingPumpUpInput)
    (hN1 : TwoGroupAltCoverExclusion) [Finite X] [IsSimpleGroup X]
    (hnab : ∃ a b : X, a * b ≠ b * a) (hKP : Assembly.KProper Blueprint.Catalog X)
    (hunb : ∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥)
    (hnU : ¬ OutcomeLocal.UOutcome X) {t : X} {J : Subgroup X} {n : ℕ}
    (hpair : Sol78.IsSolomonPair t J n) {θ : ↥J ⧸ pPrimeCore 2 ↥J ≃* alternatingGroup (Fin n)}
    {ρJ : ↥(normalizer (J : Set X)) →* Perm (Fin n)} (hρJ : IsPermAction θ ρJ) {c e₀ : X}
    (he₀ : e₀ ∈ J) (hc : orderOf c = 2) (hs4 : (coreImage θ he₀).support.card = 4)
    {Jc : Subgroup X} (hJcJ : Jc ≤ J ⊓ centralizer ({c} : Set X))
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
    {p : ℕ} (hp : p.Prime) (hpn : n < p) (hpM : p ∣ Nat.card (↥M ⧸ pPrimeCore 2 ↥M))
    (hpHe : n = 9 → ¬ p ∣ Nat.card Blueprint.NativeSporadic.He) {α : X} (hαo : orderOf α = 2)
    (hαc : α * c = c * α) (hαt : α * t = t * α) (hαJ : α ∈ normalizer (J : Set X))
    (hα2 : (ρJ ⟨α, hαJ⟩).support.card ≤ 2)
    (hαD : (ρJ ⟨α, hαJ⟩).support ⊆ (coreImage θ he₀).support)
    (hαM : α ∈ UnbalancedLayer.coreActionKernel M) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hα2' : α * α = 1 := by rw [← sq, ← hαo, pow_orderOf_eq_one]
  have hα1 : α ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hαo
    omega
  have hn9 : 9 ≤ n := hpair.2.2.1
  have hnodd : Odd n := hpair.2.1
  have hJC : J ≤ centralizer ({t} : Set X) := hpair.1.2.1
  have hJpc : IsPComponent 2 (J.subgroupOf (centralizer ({t} : Set X))) := hpair.1.2.2.1
  have hJcJ' : Jc ≤ J := hJcJ.trans inf_le_left
  have hJcCc : Jc ≤ centralizer ({c} : Set X) := hJcJ.trans inf_le_right
  have hJcC : Jc ≤ centralizer ({t} : Set X) ⊓ centralizer ({c} : Set X) :=
    le_inf (hJcJ'.trans hJC) hJcCc
  have hres := primeResidual_eq_top_of_isPComponent hJcC hJcpc
  have hp2 : p ≠ 2 := by omega
  have hρα2 : ρJ ⟨α, hαJ⟩ ^ 2 = 1 := by
    rw [sq, ← map_mul]
    convert map_one ρJ
    exact Subtype.ext hα2'
  have hdvd2 : 2 ∣ (ρJ ⟨α, hαJ⟩).support.card := Perm.two_dvd_card_support hρα2
  set k := n - (ρJ ⟨α, hαJ⟩).support.card with hkdef
  have hk7 : 7 ≤ k := by omega
  have hkodd : Odd k := Nat.Odd.sub_even (by omega) hnodd (even_iff_two_dvd.mpr hdvd2)
  obtain ⟨Jb, hJbJ, hJbpc, hinvb, -, χb, -⟩ :=
    exists_fixed_component_of_perm hJC hJpc hρJ hαJ hα2' (by omega)
  have hcardk : Fintype.card ↥((ρJ ⟨α, hαJ⟩).supportᶜ : Finset (Fin n)) = k := by
    rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin]
  let eJb : ↥Jb ⧸ pPrimeCore 2 ↥Jb ≃* alternatingGroup (Fin k) :=
    χb.trans (Fintype.equivFinOfCardEq hcardk).altCongrHom
  have hαCc : α ∈ centralizer ({c} : Set X) := mem_centralizer_singleton_iff.mpr hαc
  have hαCt : α ∈ centralizer ({t} : Set X) := mem_centralizer_singleton_iff.mpr hαt
  obtain ⟨-, hαKc⟩ := mem_coreActionKernel_of_support_subset hρJ he₀ hJcJ hres hinv hsubP χ hχ
    hαJ hαc hαD
  have hJcq : IsQuasisimple (↥Jc ⧸ pPrimeCore 2 ↥Jc) :=
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 Jc _ hJcC).mp hJcpc).2.2
  have hJcsub : (Jc.subgroupOf
      (centralizer ({t} : Set X) ⊓ centralizer ({c} : Set X))).IsSubnormal :=
    hJcpc.choose_spec.2.1
  have hE2 : IsPGroup 2 (zpowers α) := isPGroup_zpowers_of_mul_self hα2'
  have hEJc : zpowers α ≤ UnbalancedLayer.coreActionKernel Jc := zpowers_le.mpr hαKc
  have hEtc : zpowers α ≤ centralizer ({t} : Set X) ⊓ centralizer ({c} : Set X) :=
    zpowers_le.mpr (mem_inf.2 ⟨hαCt, hαCc⟩)
  have hCE : centralizer ((zpowers α : Subgroup X) : Set X) = centralizer ({α} : Set X) :=
    centralizer_zpowers_eq' α
  set K := GSLit.fixedLayer Jc (zpowers α) with hKdef
  have hKpc := GSLit.fixedLayer_isPComponent hJcC hJcsub hEtc hEJc hE2 hJcq
  rw [hCE] at hKpc
  have hKle := GSLit.fixedLayer_le_inf Jc (zpowers α)
  rw [hCE] at hKle
  have hKJc : K ≤ Jc := hKle.trans inf_le_left
  have hKY : K ≤ (centralizer ({t} : Set X) ⊓ centralizer ({c} : Set X)) ⊓
      centralizer ({α} : Set X) := fun z hz => mem_inf.2 ⟨hJcC (hKJc hz), (mem_inf.1 (hKle hz)).2⟩
  have hKperf : ⁅K, K⁆ = K := UnbalancedCorr.commutator_eq_of_isPComponent hKY hKpc
  obtain ⟨hKsup, -⟩ := GSLit.fixedLayer_sup_pPrimeCore hJcq hEJc hE2
  have hcardF : Fintype.card ↥((coreImage θ he₀).supportᶜ : Finset (Fin n)) = n - 4 := by
    rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin, hs4]
  let eJc : ↥Jc ⧸ pPrimeCore 2 ↥Jc ≃* alternatingGroup (Fin (n - 4)) :=
    χ.trans (Fintype.equivFinOfCardEq hcardF).altCongrHom
  obtain ⟨θK, -⟩ := exists_coreQuot_of_sup hKJc hKsup eJc
  have hKq : Nontrivial (↥K ⧸ pPrimeCore 2 ↥K) := by
    have : Nontrivial (alternatingGroup (Fin (n - 4))) :=
      alternatingGroup.nontrivial_of_three_le_card (by rw [Nat.card_fin]; omega)
    exact θK.toEquiv.nontrivial
  have hMq : IsQuasisimple (↥M ⧸ pPrimeCore 2 ↥M) :=
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 M _ hMC).mp hMpc).2.2
  have hMsub : (M.subgroupOf (centralizer ({c} : Set X))).IsSubnormal := hMpc.choose_spec.2.1
  have hE : zpowers α ≤ UnbalancedLayer.coreActionKernel M := zpowers_le.mpr hαM
  have hEX : zpowers α ≤ centralizer ({c} : Set X) := zpowers_le.mpr hαCc
  set L := GSLit.fixedLayer M (zpowers α) with hLdef
  have hLpc := GSLit.fixedLayer_isPComponent hMC hMsub hEX hE hE2 hMq
  rw [hCE, inf_comm] at hLpc
  have hle := GSLit.fixedLayer_le_inf M (zpowers α)
  rw [hCE] at hle
  have hLM : L ≤ M := hle.trans inf_le_left
  have hLY : L ≤ centralizer ({α} : Set X) ⊓ centralizer ({c} : Set X) := fun z hz =>
    mem_inf.2 ⟨(mem_inf.1 (hle hz)).2, hMC (hLM hz)⟩
  obtain ⟨hsup, -⟩ := GSLit.fixedLayer_sup_pPrimeCore hMq hE hE2
  have hcl := GSLit.fixedLayer_eq_closure hMq hE hE2
  have hKL : K ≤ L := by
    refine GSLit.fixedLayer_le_of_twoElements hJcq hEJc hE2 fun x hx hk => ?_
    rw [hLdef, hcl]
    exact subset_closure ⟨mem_inf.2 ⟨hJcM (mem_inf.1 hx).1, (mem_inf.1 hx).2⟩, hk⟩
  have hpL : p ∣ Nat.card (↥L ⧸ pPrimeCore 2 ↥L) := by
    rw [card_coreQuot_eq_of_sup hLM hsup]
    exact hpM
  have hKJb : K ≤ Jb := by
    refine GSLit.fixedLayer_le_of_twoElements hJcq hEJc hE2 fun x hx ⟨k', hk'⟩ => ?_
    have hxJc : x ∈ Jc := (mem_inf.1 hx).1
    have hxα : x * α = α * x :=
      ((mem_centralizer_iff.mp (mem_inf.1 hx).2) α (mem_zpowers α)).symm
    obtain ⟨hxJ, hxs⟩ := hsubP x hxJc
    refine hinvb x hxJ hxα ⟨k', by rw [← hk']; exact pow_orderOf_eq_one x⟩ ?_
    intro v hv
    have h1 := hxs hv
    rw [Finset.mem_compl] at h1 ⊢
    exact fun h2 => h1 (hαD h2)
  have hKα : SectionRank.IsKGroupCat ↥(centralizer ({α} : Set X)) :=
    UnbalancedCorr.isKGroupCat_of_ne_top hKP (centralizer_ne_top_of_ne_one hnab hα1)
  have htα : t ∈ centralizer ({α} : Set X) := mem_centralizer_singleton_iff.mpr hαt.symm
  have hcα : c ∈ centralizer ({α} : Set X) := mem_centralizer_singleton_iff.mpr hαc.symm
  have hJbJ' : Jb ≤ J := hJbJ.trans inf_le_left
  have hJbα : Jb ≤ centralizer ({α} : Set X) := hJbJ.trans inf_le_right
  have hJbY : Jb ≤ centralizer ({α} : Set X) ⊓ centralizer ({t} : Set X) := fun z hz =>
    mem_inf.2 ⟨hJbα hz, hJC (hJbJ' hz)⟩
  have hJbpc' : IsPComponent 2
      (Jb.subgroupOf (centralizer ({α} : Set X) ⊓ centralizer ({t} : Set X))) := by
    rw [inf_comm]
    exact hJbpc
  obtain ⟨K₁, hK₁Y, hK₁pc, hJbK₁, -, htype⟩ :=
    pump_type_in hPump hKα htα hpair.1.1 hJbY hJbpc' hkodd hk7 eJb
  obtain ⟨M', hM'Y, hM'pc, hLM'⟩ := exists_location_in hcα hc hLY hLpc
  obtain ⟨hK₁tY, hK₁tpc⟩ := isPComponent_conj hK₁Y hK₁pc htα
  obtain ⟨hM'cY, hM'cpc⟩ := isPComponent_conj hM'Y hM'pc hcα
  have hP0 := exists_eq_of_le_sup_sup hK₁Y hK₁pc hK₁tY hK₁tpc hM'Y hM'pc hM'cY hM'cpc hKperf hKq
    (hKJb.trans hJbK₁) (hKL.trans hLM')
  have hpK₁ : ¬ p ∣ Nat.card (↥K₁ ⧸ pPrimeCore 2 ↥K₁) := by
    apply not_dvd_card_quot_pPrimeCore hp hp2
    rcases htype with ⟨-, ⟨m', hm', hkm', ⟨eM⟩⟩ | ⟨h7, ⟨eM⟩⟩⟩ | ⟨-, ⟨eM⟩⟩
    · have hm'n : m' ≤ n := by
        by_cases hm9 : 9 ≤ m'
        · have hT : zpowers α ≠ ⊥ := fun h => hα1 (zpowers_eq_bot.mp h)
          have hK₁Y' : K₁ ≤ centralizer ((zpowers α : Subgroup X) : Set X) := by
            rw [hCE]
            exact hK₁Y
          have hK₁pc' : IsPComponent 2
              (K₁.subgroupOf (centralizer ((zpowers α : Subgroup X) : Set X))) := by
            rw [hCE]
            exact hK₁pc
          have hZ := hN1 X hnab hKP hunb hnU (zpowers α) m' K₁ hT hE2 hm' hm9 hK₁Y' hK₁pc' ⟨eM⟩
          have θ' : ↥K₁ ⧸ pPrimeCore 2 ↥K₁ ≃* alternatingGroup (Fin m') :=
            (QuotientGroup.quotientMulEquivOfEq hZ.symm).trans eM
          exact hpair.2.2.2.1 α K₁ m' ⟨hαo, hK₁Y, hK₁pc, ⟨θ'⟩⟩ hm'
        · omega
      rw [Nat.card_congr eM.toEquiv]
      exact not_dvd_card_alt hp (by omega) (by omega)
    · rw [Nat.card_congr eM.toEquiv]
      exact hpHe (by omega)
    · rw [Nat.card_congr eM.toEquiv]
      exact not_dvd_card_alt hp (by omega) (by omega)
  have hM'c := card_coreQuot_map_conj M' c
  have hK₁t := card_coreQuot_map_conj K₁ t
  have hpM' : ¬ p ∣ Nat.card (↥M' ⧸ pPrimeCore 2 ↥M') := by
    have hc2 : c * c = 1 := by rw [← sq, ← hc, pow_orderOf_eq_one]
    have hM'cc := map_conj_map_conj_of_mul_self hc2 M'
    rcases hP0 with h | h | h | h
    · rw [← h]
      exact hpK₁
    · have h1 := card_coreQuot_map_conj (M'.map (MulAut.conj c).toMonoidHom) c
      rw [hM'cc, ← h] at h1
      rw [h1]
      exact hpK₁
    · rw [← h, hK₁t]
      exact hpK₁
    · have h1 := card_coreQuot_map_conj (M'.map (MulAut.conj c).toMonoidHom) c
      rw [hM'cc, ← h, hK₁t] at h1
      rw [h1]
      exact hpK₁
  rcases dvd_or_dvd_of_le_sup hM'Y hM'pc hM'cY hM'cpc hLM' hp hpL with h | h
  · exact hpM' h
  · rw [hM'c] at h
    exact hpM' h

end CFSG.ComponentClassification.SolMax.L32
