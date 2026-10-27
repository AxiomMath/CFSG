module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxDgA
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxFiveO
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxFiveU

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

theorem card_support_eq_of_two_actions [Finite X] {M M' L : Subgroup X}
    {θM : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin 7)}
    {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin 7)} (hρ : IsPermAction θM ρ)
    {ρ' : ↥(normalizer (M' : Set X)) →* Perm (Fin 7)} (hLM : L ≤ M)
    (θL : ↥L ⧸ pPrimeCore 2 ↥L ≃* alternatingGroup (Fin 7))
    (hθL : ∀ (x : X) (hxL : x ∈ L) (hxM : x ∈ M), θL ((⟨x, hxL⟩ : ↥L) : ↥L ⧸ pPrimeCore 2 ↥L) =
      θM ((⟨x, hxM⟩ : ↥M) : ↥M ⧸ pPrimeCore 2 ↥M))
    (hLN : L ≤ normalizer (M' : Set X))
    (hsurj : ∀ g ∈ alternatingGroup (Fin 7), ∃ l : ↥L, ρ' (inclusion hLN l) = g)
    (hA : ∀ l : ↥L, ρ' (inclusion hLN l) ∈ alternatingGroup (Fin 7))
    (hO : ∀ l : ↥L, l ∈ pPrimeCore 2 ↥L → ρ' (inclusion hLN l) = 1) {x : X} (hxL : x ∈ L) :
    (ρ' ⟨x, hLN hxL⟩).support.card = (ρ ⟨x, le_normalizer (hLM hxL)⟩).support.card := by
  classical
  let f : ↥L →* alternatingGroup (Fin 7) := (ρ'.comp (inclusion hLN)).codRestrict _ hA
  have hf : ∀ l : ↥L, ((f l : alternatingGroup (Fin 7)) : Perm (Fin 7)) = ρ' (inclusion hLN l) :=
    fun _ => rfl
  have hfO : pPrimeCore 2 ↥L ≤ f.ker := fun l hl => Subtype.ext (hO l hl)
  let φ : ↥L ⧸ pPrimeCore 2 ↥L →* alternatingGroup (Fin 7) := QuotientGroup.lift _ f hfO
  have hφ : ∀ l : ↥L, φ (l : ↥L ⧸ pPrimeCore 2 ↥L) = f l := fun _ => rfl
  have hφs : Function.Surjective φ := by
    intro g
    obtain ⟨l, hl⟩ := hsurj g g.2
    exact ⟨l, Subtype.ext (by rw [hφ, hf, hl])⟩
  have hφb : Function.Bijective φ := hφs.bijective_of_nat_card_le
    (by rw [Nat.card_congr θL.toEquiv])
  let ψ₀ : alternatingGroup (Fin 7) ≃* alternatingGroup (Fin 7) :=
    θL.symm.trans (MulEquiv.ofBijective φ hφb)
  obtain ⟨ε, hε⟩ := exists_equiv_of_mulEquiv_alt (Fintype.card_fin 7) (Fintype.card_fin 7)
    le_rfl ψ₀
  have h1 : ρ' ⟨x, hLN hxL⟩ = ε.permCongr (ρ ⟨x, le_normalizer (hLM hxL)⟩) := by
    rw [hρ.apply_of_mem (by norm_num) ⟨x, hLM hxL⟩, ← hθL x hxL (hLM hxL), ← hε]
    have h2 : ψ₀ (θL ((⟨x, hxL⟩ : ↥L) : ↥L ⧸ pPrimeCore 2 ↥L)) =
        φ ((⟨x, hxL⟩ : ↥L) : ↥L ⧸ pPrimeCore 2 ↥L) := by
      change (MulEquiv.ofBijective φ hφb) (θL.symm (θL _)) = _
      rw [MulEquiv.symm_apply_apply]
      rfl
    rw [h2, hφ, hf]
    rfl
  rw [h1]
  have h3 : ε.permCongr (ρ ⟨x, le_normalizer (hLM hxL)⟩) =
      (ε : Perm (Fin 7)) * ρ ⟨x, le_normalizer (hLM hxL)⟩ * (ε : Perm (Fin 7))⁻¹ := by
    ext v
    simp [Perm.mul_apply]
  rw [h3, Perm.card_support_conj]

theorem diag_facts_of_beta (hPump : Sol78.AlternatingPumpUpInput)
    [Finite X] [IsSimpleGroup X] (hnab : ∃ a b : X, a * b ≠ b * a)
    (hKP : Assembly.KProper Blueprint.Catalog X) {t : X} {J : Subgroup X}
    (hpair : SolAltLit.IsAltTwoComponent t J 9)
    (hCtN : centralizer ({t} : Set X) ≤ normalizer (J : Set X))
    {θ : ↥J ⧸ pPrimeCore 2 ↥J ≃* alternatingGroup (Fin 9)}
    {ρJ : ↥(normalizer (J : Set X)) →* Perm (Fin 9)} (hρJ : IsPermAction θ ρJ)
    {c e₀ : X} (he₀ : e₀ ∈ J) (hc : orderOf c = 2) (htc : t * c = c * t)
    (hs4 : (coreImage θ he₀).support.card = 4) {Jc : Subgroup X}
    (hJcJ : Jc ≤ J ⊓ centralizer ({c} : Set X))
    (hJcpc : IsPComponent 2
      (Jc.subgroupOf (centralizer ({t} : Set X) ⊓ centralizer ({c} : Set X))))
    (hinv : ∀ (x : X) (hx : x ∈ J), x * c = c * x → (∃ k : ℕ, x ^ 2 ^ k = 1) →
      (coreImage θ hx).support ⊆ (coreImage θ he₀).supportᶜ → x ∈ Jc)
    (hsubP : ∀ x ∈ Jc, ∃ hx : x ∈ J, (coreImage θ hx).support ⊆ (coreImage θ he₀).supportᶜ)
    (χ : ↥Jc ⧸ pPrimeCore 2 ↥Jc ≃*
      alternatingGroup ↥((coreImage θ he₀).supportᶜ : Finset (Fin 9)))
    (hχ : ∀ (x : ↥Jc) (hx : (x : X) ∈ J),
      Perm.ofSubtype ((χ (x : ↥Jc ⧸ pPrimeCore 2 ↥Jc) : alternatingGroup _) :
        Perm ↥((coreImage θ he₀).supportᶜ : Finset (Fin 9))) = coreImage θ hx)
    {M : Subgroup X} (hMC : M ≤ centralizer ({c} : Set X))
    (hMpc : IsPComponent 2 (M.subgroupOf (centralizer ({c} : Set X)))) (hJcM : Jc ≤ M)
    (htM : t ∈ normalizer (M : Set X)) (θM : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin 7))
    {a : X}
    (hao : orderOf a = 2) (haJc : a ∈ Jc)
    {β : X} (hβo : orderOf β = 2) (hβc : β * c = c * β) (hβt : β * t = t * β)
    (hβJ : β ∈ normalizer (J : Set X)) (hβ2 : (ρJ ⟨β, hβJ⟩).support.card = 2)
    (hβD : (ρJ ⟨β, hβJ⟩).support ⊆ (coreImage θ he₀).support)
    (hβK : β ∈ UnbalancedLayer.coreActionKernel M) {M' : Subgroup X}
    (hM'Y : M' ≤ centralizer ({β} : Set X))
    (hM'pc : IsPComponent 2 (M'.subgroupOf (centralizer ({β} : Set X))))
    (hLM' : GSLit.fixedLayer M (zpowers β) ≤ M' ⊔ M'.map (MulAut.conj c).toMonoidHom)
    (htM' : M'.map (MulAut.conj t).toMonoidHom ≠ M') :
    M'.map (MulAut.conj t).toMonoidHom = M'.map (MulAut.conj c).toMonoidHom ∧
      ∀ (ψ : ↥M' ⧸ Open.fusionZStar ↥M' ≃* alternatingGroup (Fin 7))
        (ρ' : ↥(normalizer (M' : Set X)) →* Perm (Fin 7)), IsPermActionZ ψ ρ' →
        ∀ z : X, z ∈ (pPrimeCore 2 ↥(centralizer ({a} : Set X))).map
          (centralizer ({a} : Set X)).subtype → z * β = β * z → z * t = t * z →
          ∀ hzN : z ∈ normalizer (M' : Set X), ρ' ⟨z, hzN⟩ = 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht2 : t * t = 1 := by rw [← sq, ← hpair.1, pow_orderOf_eq_one]
  have hc2 : c * c = 1 := by rw [← sq, ← hc, pow_orderOf_eq_one]
  have hβ2' : β * β = 1 := by rw [← sq, ← hβo, pow_orderOf_eq_one]
  have hβ1 : β ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hβo
    omega
  have hJC : J ≤ centralizer ({t} : Set X) := hpair.2.1
  have hJpc : IsPComponent 2 (J.subgroupOf (centralizer ({t} : Set X))) := hpair.2.2.1
  have hJcJ' : Jc ≤ J := hJcJ.trans inf_le_left
  have hJcCc : Jc ≤ centralizer ({c} : Set X) := hJcJ.trans inf_le_right
  have hJcC : Jc ≤ centralizer ({t} : Set X) ⊓ centralizer ({c} : Set X) :=
    le_inf (hJcJ'.trans hJC) hJcCc
  have hres := primeResidual_eq_top_of_isPComponent hJcC hJcpc
  have hMq : IsQuasisimple (↥M ⧸ pPrimeCore 2 ↥M) :=
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 M _ hMC).mp hMpc).2.2
  have hMsub : (M.subgroupOf (centralizer ({c} : Set X))).IsSubnormal := hMpc.choose_spec.2.1
  have hE : zpowers β ≤ UnbalancedLayer.coreActionKernel M := zpowers_le.mpr hβK
  have hE2 : IsPGroup 2 (zpowers β) := isPGroup_zpowers_of_mul_self hβ2'
  have hβCc : β ∈ centralizer ({c} : Set X) := mem_centralizer_singleton_iff.mpr hβc
  have hβCt : β ∈ centralizer ({t} : Set X) := mem_centralizer_singleton_iff.mpr hβt
  have hEX : zpowers β ≤ centralizer ({c} : Set X) := zpowers_le.mpr hβCc
  have hCE : centralizer ((zpowers β : Subgroup X) : Set X) = centralizer ({β} : Set X) :=
    centralizer_zpowers_eq' β
  set L := GSLit.fixedLayer M (zpowers β) with hLdef
  have hLpc := GSLit.fixedLayer_isPComponent hMC hMsub hEX hE hE2 hMq
  rw [hCE, inf_comm] at hLpc
  have hle := GSLit.fixedLayer_le_inf M (zpowers β)
  rw [hCE] at hle
  have hLM : L ≤ M := hle.trans inf_le_left
  have hLY : L ≤ centralizer ({β} : Set X) ⊓ centralizer ({c} : Set X) := fun z hz =>
    mem_inf.2 ⟨(mem_inf.1 (hle hz)).2, hMC (hLM hz)⟩
  obtain ⟨hsup, -⟩ := GSLit.fixedLayer_sup_pPrimeCore hMq hE hE2
  obtain ⟨θL, -⟩ := exists_coreQuot_of_sup hLM hsup θM
  have hLperf : ⁅L, L⁆ = L := UnbalancedCorr.commutator_eq_of_isPComponent hLY hLpc
  have hLq : Nontrivial (↥L ⧸ pPrimeCore 2 ↥L) := nontrivial_coreQuot_of_seven θL
  have hcl := GSLit.fixedLayer_eq_closure hMq hE hE2
  obtain ⟨-, hβKc⟩ := mem_coreActionKernel_of_support_subset hρJ he₀ hJcJ hres hinv hsubP χ hχ
    hβJ hβc hβD
  have hJcq : IsQuasisimple (↥Jc ⧸ pPrimeCore 2 ↥Jc) :=
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 Jc _ hJcC).mp hJcpc).2.2
  have hJcsub : (Jc.subgroupOf
      (centralizer ({t} : Set X) ⊓ centralizer ({c} : Set X))).IsSubnormal :=
    hJcpc.choose_spec.2.1
  have hEJc : zpowers β ≤ UnbalancedLayer.coreActionKernel Jc := zpowers_le.mpr hβKc
  have hEtc : zpowers β ≤ centralizer ({t} : Set X) ⊓ centralizer ({c} : Set X) :=
    zpowers_le.mpr (mem_inf.2 ⟨hβCt, hβCc⟩)
  set K := GSLit.fixedLayer Jc (zpowers β) with hKdef
  have hKpc := GSLit.fixedLayer_isPComponent hJcC hJcsub hEtc hEJc hE2 hJcq
  rw [hCE] at hKpc
  have hKle := GSLit.fixedLayer_le_inf Jc (zpowers β)
  rw [hCE] at hKle
  have hKJc : K ≤ Jc := hKle.trans inf_le_left
  have hKY : K ≤ (centralizer ({t} : Set X) ⊓ centralizer ({c} : Set X)) ⊓
      centralizer ({β} : Set X) := fun z hz => mem_inf.2 ⟨hJcC (hKJc hz), (mem_inf.1 (hKle hz)).2⟩
  have hKperf : ⁅K, K⁆ = K := UnbalancedCorr.commutator_eq_of_isPComponent hKY hKpc
  obtain ⟨hKsup, -⟩ := GSLit.fixedLayer_sup_pPrimeCore hJcq hEJc hE2
  have hcard5 : Fintype.card ↥((coreImage θ he₀).supportᶜ : Finset (Fin 9)) = 5 := by
    rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin, hs4]
  let eJc : ↥Jc ⧸ pPrimeCore 2 ↥Jc ≃* alternatingGroup (Fin 5) :=
    χ.trans (Fintype.equivFinOfCardEq hcard5).altCongrHom
  obtain ⟨θK, -⟩ := exists_coreQuot_of_sup hKJc hKsup eJc
  have hKq : Nontrivial (↥K ⧸ pPrimeCore 2 ↥K) := by
    have : Nontrivial (alternatingGroup (Fin 5)) :=
      alternatingGroup.nontrivial_of_three_le_card (by rw [Nat.card_fin]; norm_num)
    exact θK.toEquiv.nontrivial
  have hKL : K ≤ L := by
    refine GSLit.fixedLayer_le_of_twoElements hJcq hEJc hE2 fun x hx hk => ?_
    rw [hLdef, hcl]
    exact subset_closure ⟨mem_inf.2 ⟨hJcM (mem_inf.1 hx).1, (mem_inf.1 hx).2⟩, hk⟩
  obtain ⟨Jb, hJbJ, hJbpc, hinvb, hsubPb, χb, hχb⟩ :=
    exists_fixed_component_of_perm hJC hJpc hρJ hβJ hβ2' (by omega)
  have hJbJ' : Jb ≤ J := hJbJ.trans inf_le_left
  have hJbβ : Jb ≤ centralizer ({β} : Set X) := hJbJ.trans inf_le_right
  have hKJb : K ≤ Jb := by
    refine GSLit.fixedLayer_le_of_twoElements hJcq hEJc hE2 fun x hx ⟨k, hk⟩ => ?_
    have hxJc : x ∈ Jc := (mem_inf.1 hx).1
    have hxβ : x * β = β * x :=
      ((mem_centralizer_iff.mp (mem_inf.1 hx).2) β (mem_zpowers β)).symm
    obtain ⟨hxJ, hxs⟩ := hsubP x hxJc
    refine hinvb x hxJ hxβ ⟨k, by rw [← hk]; exact pow_orderOf_eq_one x⟩ ?_
    intro v hv
    have h1 := hxs hv
    rw [Finset.mem_compl] at h1 ⊢
    exact fun h2 => h1 (hβD h2)
  have hcard7 : Fintype.card ↥((ρJ ⟨β, hβJ⟩).supportᶜ : Finset (Fin 9)) = 7 := by
    rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin, hβ2]
  let eJb : ↥Jb ⧸ pPrimeCore 2 ↥Jb ≃* alternatingGroup (Fin 7) :=
    χb.trans (Fintype.equivFinOfCardEq hcard7).altCongrHom
  have hK : SectionRank.IsKGroupCat ↥(centralizer ({β} : Set X)) :=
    UnbalancedCorr.isKGroupCat_of_ne_top hKP (centralizer_ne_top_of_ne_one hnab hβ1)
  have htβ : t ∈ centralizer ({β} : Set X) := mem_centralizer_singleton_iff.mpr hβt.symm
  have hcβ : c ∈ centralizer ({β} : Set X) := mem_centralizer_singleton_iff.mpr hβc.symm
  have hJbY : Jb ≤ centralizer ({β} : Set X) ⊓ centralizer ({t} : Set X) := fun z hz =>
    mem_inf.2 ⟨hJbβ hz, hJC (hJbJ' hz)⟩
  have hJbpc' : IsPComponent 2
      (Jb.subgroupOf (centralizer ({β} : Set X) ⊓ centralizer ({t} : Set X))) := by
    rw [inf_comm]
    exact hJbpc
  obtain ⟨K₁, hK₁Y, hK₁pc, hJbK₁, -, -⟩ :=
    pump_type_in hPump hK htβ hpair.1 hJbY hJbpc' (by decide) le_rfl eJb
  obtain ⟨hK₁tY, hK₁tpc⟩ := isPComponent_conj hK₁Y hK₁pc htβ
  obtain ⟨hM'cY, hM'cpc⟩ := isPComponent_conj hM'Y hM'pc hcβ
  have hP0 := exists_eq_of_le_sup_sup hK₁Y hK₁pc hK₁tY hK₁tpc hM'Y hM'pc hM'cY hM'cpc hKperf hKq
    (hKJb.trans hJbK₁) (hKL.trans hLM')
  have hback : ∀ H : Subgroup X, K₁.map (MulAut.conj t).toMonoidHom = H →
      K₁ = H.map (MulAut.conj t).toMonoidHom := fun H h => by
    have h1 := congrArg (fun H' : Subgroup X => H'.map (MulAut.conj t).toMonoidHom) h
    simp only [map_conj_map_conj_of_mul_self ht2] at h1
    exact h1
  have htL : t ∈ normalizer (L : Set X) := mem_normalizer_fixedLayer hMq hE hE2 htM hβt.symm
  have hLt : L.map (MulAut.conj t).toMonoidHom = L := mem_normalizer_iff_map_conj_eq.mp htL
  obtain ⟨hM'tY, hM'tpc⟩ := isPComponent_conj hM'Y hM'pc htβ
  obtain ⟨hM'tcY, hM'tcpc⟩ := isPComponent_conj hM'tY hM'tpc hcβ
  have hLle : L ≤ M'.map (MulAut.conj t).toMonoidHom ⊔
      (M'.map (MulAut.conj t).toMonoidHom).map (MulAut.conj c).toMonoidHom := by
    rw [← map_conj_comm htc.symm, ← Subgroup.map_sup, ← hLt]
    exact map_mono hLM'
  have hP1 := exists_eq_of_le_sup_sup hM'tY hM'tpc hM'tcY hM'tcpc hM'Y hM'pc hM'cY hM'cpc hLperf
    hLq hLle hLM'
  have hcinj : ∀ H K : Subgroup X, H.map (MulAut.conj c).toMonoidHom =
      K.map (MulAut.conj c).toMonoidHom → H = K := fun H K h =>
    Subgroup.map_injective (f := (MulAut.conj c).toMonoidHom)
      (fun u v huv => (MulAut.conj c).injective huv) h
  have hM'tc : M'.map (MulAut.conj t).toMonoidHom = M'.map (MulAut.conj c).toMonoidHom := by
    rcases hP1 with h | h | h | h
    · exact absurd h htM'
    · exact h
    · apply hcinj
      rw [h, map_conj_map_conj_of_mul_self hc2]
    · exfalso
      apply htM'
      apply hcinj
      exact h
  have hM'ct : (M'.map (MulAut.conj c).toMonoidHom).map (MulAut.conj t).toMonoidHom = M' := by
    rw [map_conj_comm htc.symm, hM'tc, map_conj_map_conj_of_mul_self hc2]
  have hJbD : Jb ≤ M' ⊔ M'.map (MulAut.conj c).toMonoidHom := by
    have h1 := hJbK₁
    rcases hP0 with h | h | h | h
    · rwa [h, hM'tc] at h1
    · rwa [h, hM'ct, sup_comm] at h1
    · rwa [h, hback _ h, hM'tc, sup_comm] at h1
    · rwa [h, hback _ h, hM'ct] at h1
  refine ⟨hM'tc, fun ψ ρ' hρ' z hzO hzβ hzt hzM' => ?_⟩
  have haJ : a ∈ J := hJcJ' haJc
  have ha2 : a * a = 1 := by rw [← sq, ← hao, pow_orderOf_eq_one]
  have hρJa : ρJ ⟨a, le_normalizer haJ⟩ = coreImage θ haJ :=
    hρJ.apply_of_mem (by norm_num) ⟨a, haJ⟩
  obtain ⟨haJ', haF⟩ := hsubP a haJc
  have haF' : (coreImage θ haJ).support ⊆ (coreImage θ he₀).supportᶜ := haF
  have ha5 : 5 ≤ 9 - (ρJ ⟨a, le_normalizer haJ⟩).support.card := by
    rw [hρJa]
    have h1 := Finset.card_le_card haF'
    rw [Finset.card_compl, Fintype.card_fin, hs4] at h1
    have hσ2 : coreImage θ haJ * coreImage θ haJ = 1 := by
      rw [← hρJa, ← map_mul]
      convert map_one ρJ
      exact Subtype.ext ha2
    obtain ⟨w, hw⟩ := four_dvd_card_support_of_mem_alternating hσ2 (coreImage_mem θ haJ)
    omega
  have hzJ : z ∈ normalizer (J : Set X) := hCtN (mem_centralizer_singleton_iff.mpr hzt)
  have hzK : z ∈ UnbalancedLayer.coreActionKernel J :=
    hρJ.le_coreActionKernel_of_fix (le_normalizer haJ) ha2 ha5 (zpowers_le.mpr hzJ)
      (zpowers_le.mpr hzO) (mem_zpowers z)
  have hJbC' : Jb ≤ centralizer ({t} : Set X) ⊓ centralizer ({β} : Set X) := fun w hw =>
    mem_inf.2 ⟨hJC (hJbJ' hw), hJbβ hw⟩
  have hresJb := primeResidual_eq_top_of_isPComponent hJbC' hJbpc
  have hzJb : z ∈ normalizer (Jb : Set X) := by
    refine mem_normalizer_of_fixed_component θ hJbβ hresJb hinvb hsubPb hzJ hzβ ?_
    intro w hw hws
    rw [coreImage_conj_of_cak θ hzK hw _]
    exact hws
  have hzKb : z ∈ UnbalancedLayer.coreActionKernel Jb :=
    SolMax.mem_coreActionKernel_of_le hJbJ' hzK hzJb
  obtain ⟨hDN, -, -, -⟩ := GSThmB.B5a.pComponent_sup_facts hM'Y hM'cY hM'pc hM'cpc
  have hJbN : Jb ≤ normalizer (M' : Set X) := hJbD.trans hDN
  have hJbperf : ⁅Jb, Jb⁆ = Jb := UnbalancedCorr.commutator_eq_of_isPComponent hJbC' hJbpc
  have hJbq : Nontrivial (↥Jb ⧸ pPrimeCore 2 ↥Jb) := nontrivial_coreQuot_of_seven eJb
  have hneJb := exists_ne_one_of_diag htβ hM'Y hM'pc hρ' (by rw [hM'tc]; exact hJbD)
    (hJbJ'.trans hJC) hJbperf hJbq hJbN
  obtain ⟨hsurjJb, -, hOJb⟩ := image_of_seven hJbN hJbperf hresJb eJb hneJb
  exact eq_one_of_mem_cak_of_image hJbN hsurjJb hOJb hzM' hzKb

end CFSG.ComponentClassification.SolMax
