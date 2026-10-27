module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxFiveU
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxFiveP

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

theorem false_of_seven_pump_of_normalizes (hPump : Sol78.AlternatingPumpUpInput)
    [Finite X] [IsSimpleGroup X] (hnab : ∃ a b : X, a * b ≠ b * a)
    (hKP : Assembly.KProper Blueprint.Catalog X) {t : X} {J : Subgroup X}
    (hpair : SolAltLit.IsAltTwoComponent t J 9)
    {θ : ↥J ⧸ pPrimeCore 2 ↥J ≃* alternatingGroup (Fin 9)}
    {ρJ : ↥(normalizer (J : Set X)) →* Perm (Fin 9)} (hρJ : IsPermAction θ ρJ)
    {c e₀ : X} (he₀ : e₀ ∈ J) (hc : orderOf c = 2) (htc : t * c = c * t)
    (hcN : c ∈ normalizer (J : Set X)) (hce : c * e₀⁻¹ ∈ UnbalancedLayer.coreActionKernel J)
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
    {β : X} (hβo : orderOf β = 2) (hβc : β * c = c * β) (hβt : β * t = t * β)
    (hβJ : β ∈ normalizer (J : Set X)) (hβ2 : (ρJ ⟨β, hβJ⟩).support.card = 2)
    (hβD : (ρJ ⟨β, hβJ⟩).support ⊆ (coreImage θ he₀).support)
    (hβK : β ∈ UnbalancedLayer.coreActionKernel M) {M' : Subgroup X}
    (hM'Y : M' ≤ centralizer ({β} : Set X))
    (hM'pc : IsPComponent 2 (M'.subgroupOf (centralizer ({β} : Set X))))
    (hLM' : GSLit.fixedLayer M (zpowers β) ≤ M' ⊔ M'.map (MulAut.conj c).toMonoidHom)
    (eM' : Nonempty (↥M' ⧸ Open.fusionZStar ↥M' ≃* alternatingGroup (Fin 7)))
    (hcase : M'.map (MulAut.conj c).toMonoidHom = M' ∨
      M'.map (MulAut.conj t).toMonoidHom = M') : False := by
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
  have hρJc : ρJ ⟨c, hcN⟩ = coreImage θ he₀ :=
    hρJ.apply_eq_coreImage_of_acts (by norm_num) hcN he₀ hce
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
  have hKc : K ≤ centralizer ({c} : Set X) := hKY.trans (inf_le_left.trans inf_le_right)
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
  by_cases hcM' : M'.map (MulAut.conj c).toMonoidHom = M'
  ·
    have hLM'' : L ≤ M' := by
      have h1 := hLM'
      rwa [hcM', sup_idem] at h1
    have htL : t ∈ normalizer (L : Set X) := mem_normalizer_fixedLayer hMq hE hE2 htM hβt.symm
    obtain ⟨hM'tY, hM'tpc⟩ := isPComponent_conj hM'Y hM'pc htβ
    have hLM't : L ≤ M'.map (MulAut.conj t).toMonoidHom := by
      intro z hz
      have h1 : t⁻¹ * z * t ∈ L := by
        have := (mem_normalizer_iff.mp (inv_mem htL) z).mp hz
        rwa [inv_inv] at this
      exact ⟨t⁻¹ * z * t, hLM'' h1, by simp [mul_assoc]⟩
    have hM'tt : M'.map (MulAut.conj t).toMonoidHom = M' :=
      eq_of_isPComponent_of_le_inf hM'tY hM'Y hM'tpc hM'pc hLM't hLM'' hLperf hLq
    have hK₁M' : K₁ = M' := by
      rcases hP0 with h | h | h | h
      · exact h
      · rwa [hcM'] at h
      · rw [hback _ h, hM'tt]
      · rw [hcM'] at h
        rw [hback _ h, hM'tt]
    have hJbM' : Jb ≤ M' := by
      have h1 := hJbK₁
      rwa [hK₁M', hM'tt, sup_idem] at h1
    obtain ⟨ψ⟩ := eM'
    obtain ⟨ρ', hρ'⟩ := exists_isPermActionZ (N := M') (by norm_num) (by norm_num) ψ
    have hM'perf : ⁅M', M'⁆ = M' := UnbalancedCorr.commutator_eq_of_isPComponent hM'Y hM'pc
    have hLN' : L ≤ normalizer (M' : Set X) := fun z hz => le_normalizer (hLM'' hz)
    have hne : ∃ l : ↥L, ρ' (inclusion hLN' l) ≠ 1 := by
      by_contra hall
      push Not at hall
      apply not_le_coreActionKernel_of_le hLM'' hLperf hLq
      intro l hl
      exact hρ'.mem_coreActionKernel hM'perf (hLN' hl) (hall ⟨l, hl⟩)
    have hresL := primeResidual_eq_top_of_isPComponent hLY hLpc
    obtain ⟨hsurjL, -, hOL⟩ := image_of_seven hLN' hLperf hresL θL hne
    have hcM'N : c ∈ normalizer (M' : Set X) := mem_normalizer_iff_map_conj_eq.mpr hcM'
    have hρ'c : ρ' ⟨c, hcM'N⟩ = 1 := eq_one_of_mem_cak_of_image hLN' hsurjL hOL hcM'N
      (mem_coreActionKernel_of_le_centralizer (hLM.trans hMC))
    have hcK' : c ∈ UnbalancedLayer.coreActionKernel M' :=
      hρ'.mem_coreActionKernel hM'perf hcM'N hρ'c
    have hδe₀ : coreImage θ he₀ * ρJ ⟨β, hβJ⟩ = ρJ ⟨β, hβJ⟩ * coreImage θ he₀ := by
      rw [← hρJc, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hβc.symm
    have hJbC' : Jb ≤ centralizer ({t} : Set X) ⊓ centralizer ({β} : Set X) := fun z hz =>
      mem_inf.2 ⟨hJC (hJbJ' hz), hJbβ hz⟩
    have hresJb := primeResidual_eq_top_of_isPComponent hJbC' hJbpc
    have hcJb : c ∈ normalizer (Jb : Set X) := by
      refine mem_normalizer_of_fixed_component θ hJbβ hresJb hinvb hsubPb hcN hβc.symm ?_
      intro x hx hxs
      rw [coreImage_conj_of_acts θ he₀ hce hx _, Perm.support_conj]
      intro v hv
      obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hv
      have hu' := hxs hu
      rw [Finset.mem_compl] at hu' ⊢
      intro h
      exact hu' ((apply_mem_support_iff_of_commute hδe₀ u).mp h)
    have hcKb : c ∈ UnbalancedLayer.coreActionKernel Jb :=
      mem_coreActionKernel_of_le hJbM' hcK' hcJb
    have hcomm : ∀ b ∈ fixAlt (ρJ ⟨β, hβJ⟩),
        coreImage θ he₀ * (b : Perm (Fin 9)) = (b : Perm (Fin 9)) * coreImage θ he₀ := by
      intro b hb
      obtain ⟨φ, hφ⟩ := exists_fixAlt_equiv (ρJ ⟨β, hβJ⟩)
      obtain ⟨q, hq⟩ := χb.surjective (φ.symm ⟨b, hb⟩)
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
      have hxJ : (x : X) ∈ J := hJbJ' x.2
      have hbx : (b : Perm (Fin 9)) = coreImage θ hxJ := by
        rw [← hχb x hxJ, hq]
        have h2 := hφ (φ.symm ⟨b, hb⟩)
        rw [MulEquiv.apply_symm_apply] at h2
        exact h2
      have hcx : c * (x : X) * c⁻¹ ∈ J := (mem_normalizer_iff.mp hcN x).mp hxJ
      have h1 := coreImage_conj_of_acts θ he₀ hce hxJ hcx
      have h2 : coreImage θ hcx = coreImage θ hxJ :=
        coreImage_conj_eq_of_cak hJbJ' χb hχb hcKb x.2 hcx
      rw [h2] at h1
      rw [hbx]
      calc coreImage θ he₀ * coreImage θ hxJ =
          coreImage θ he₀ * coreImage θ hxJ * (coreImage θ he₀)⁻¹ * coreImage θ he₀ := by group
        _ = coreImage θ hxJ * coreImage θ he₀ := by rw [← h1]
    obtain ⟨v, hvD, hvδ⟩ : ∃ v ∈ (coreImage θ he₀).support, v ∉ (ρJ ⟨β, hβJ⟩).support := by
      by_contra hall
      push Not at hall
      have h1 := Finset.card_le_card
        (show (coreImage θ he₀).support ⊆ (ρJ ⟨β, hβJ⟩).support from hall)
      rw [hs4, hβ2] at h1
      omega
    exact (Perm.mem_support.mp hvD) (apply_eq_of_commute_fixAlt (by omega) hcomm hvδ)
  rcases hcase with h | htM'
  · exact hcM' h
  have htM'c : (M'.map (MulAut.conj c).toMonoidHom).map (MulAut.conj t).toMonoidHom =
      M'.map (MulAut.conj c).toMonoidHom := by
    rw [map_conj_comm htc.symm, htM']
  have hK₁mem : K₁ = M' ∨ K₁ = M'.map (MulAut.conj c).toMonoidHom := by
    rcases hP0 with h | h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · left
      rw [hback _ h, htM']
    · right
      rw [hback _ h, htM'c]
  have hK₁t : K₁.map (MulAut.conj t).toMonoidHom = K₁ := by
    rcases hK₁mem with h | h <;> rw [h]
    · exact htM'
    · exact htM'c
  have hJbK₁' : Jb ≤ K₁ := by
    have h1 := hJbK₁
    rwa [hK₁t, sup_idem] at h1
  have hKK₁ : K ≤ K₁ := hKJb.trans hJbK₁'
  have hKK₁c : K ≤ K₁.map (MulAut.conj c).toMonoidHom := by
    intro z hz
    have hzc : z * c = c * z := mem_centralizer_singleton_iff.mp (hKc hz)
    refine ⟨z, hKK₁ hz, ?_⟩
    change c * z * c⁻¹ = z
    rw [← hzc]
    group
  obtain ⟨hK₁cY, hK₁cpc⟩ := isPComponent_conj hK₁Y hK₁pc hcβ
  have heq := eq_of_isPComponent_of_le_inf hK₁Y hK₁cY hK₁pc hK₁cpc hKK₁ hKK₁c hKperf hKq
  rcases hK₁mem with h | h
  · rw [h] at heq
    exact hcM' heq.symm
  · rw [h, map_conj_map_conj_of_mul_self hc2] at heq
    exact hcM' heq

end CFSG.ComponentClassification.SolMax
