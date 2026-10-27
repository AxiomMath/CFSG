module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.RankTwoDownLevel
public import CFSG.LocalAnalysis.GLTheoremA.PartI.KDClub.L3Lay
import CFSG.LocalAnalysis.GLTheoremA.S4.Lemma49i
public import CFSG.LocalAnalysis.GLTheoremA.PartI.I1412

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.KFacts CFSG.LocalAnalysis.ComponentInitial
  CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.UnitaryFlag
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns

section Dichot

variable {π : Bool} {p f : ℕ} {K : Type} [Field K] {Y : Type} [Group Y]

theorem rtd_dichot_proj (hK : PiField π p f K) (hq : ModThree π (p ^ f)) (hq2 : 2 < p ^ f)
    (e : Y ≃* (↥(slPi π 3 (p ^ f) K) ⧸ Subgroup.center ↥(slPi π 3 (p ^ f) K)))
    {β : MulAut Y} (hβ3 : β ^ 3 = 1) (hβ1 : β ≠ 1) :
    InnerAutAt π p f K β ∨ ∃ σ : K ≃+* K, orderOf σ = 3 ∧
      ∃ e2 : Y ≃* (↥(slPi π 3 (p ^ f) K) ⧸ Subgroup.center ↥(slPi π 3 (p ^ f) K)),
        MulAut.congr e2 β = centerDescend _ (frobSL hK σ) := by
  have := hK.finite
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  obtain ⟨pkg⟩ := exists_etaPkg hK hq2
  set ε : Y ≃* pkg.M := e.trans pkg.η with hε
  have hβ3' : MulAut.congr ε β ^ 3 = 1 := by rw [← map_pow, hβ3, map_one]
  rcases pkg.dich _ hβ3' with hin | ⟨σ, hσ, κ, hκ, hβ'⟩
  · left
    obtain ⟨x, hx, hxs⟩ := pkg.conj_of_inndiag _ hin
    have hxs' : ∀ s t : ↥(slPi π 3 (p ^ f) K), (t : GL (Fin 3) K) = x * s * x⁻¹ →
        β (e.symm (QuotientGroup.mk s)) = e.symm (QuotientGroup.mk t) := by
      intro s t ht
      have h1 := hxs s t ht
      rw [hε, congr_trans', congr_symm_congr, MulAut.congr_apply] at h1
      rw [← h1]
      simp
    let ν : ↥(slPi π 3 (p ^ f) K) →* Y :=
      e.symm.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥(slPi π 3 (p ^ f) K)))
    have hνker : ∀ s ∈ ν.ker, ((s : ↥(slPi π 3 (p ^ f) K)) : GL (Fin 3) K) ∈
        StatedScalars (Fin 3) K := by
      intro s hs
      have h1 : (QuotientGroup.mk s : ↥(slPi π 3 (p ^ f) K) ⧸
          Subgroup.center ↥(slPi π 3 (p ^ f) K)) = 1 :=
        e.symm.injective (by simpa [ν] using hs)
      have h2 : s ∈ Subgroup.center ↥(slPi π 3 (p ^ f) K) := (QuotientGroup.eq_one_iff s).1 h1
      rw [center_slPi_eq hK hq, Subgroup.mem_subgroupOf] at h2
      exact h2
    have hνsurj : Function.Surjective ν := by
      intro y
      obtain ⟨s, hs⟩ := QuotientGroup.mk_surjective (e y)
      exact ⟨s, by simp [ν, hs]⟩
    have hνβ : ∀ s t : ↥(slPi π 3 (p ^ f) K), (t : GL (Fin 3) K) = x * s * x⁻¹ →
        β (ν s) = ν t := fun s t ht => hxs' s t ht
    have hxZ : x ∉ zPi π 3 (p ^ f) K := by
      intro hz
      apply hβ1
      rw [zPi_eq hπ hq' (exists_tau hK hq).choose_spec.1 (exists_tau hK hq).choose_spec.2] at hz
      have hz' := (Subgroup.mem_inf.1 hz).2
      ext y
      obtain ⟨s, rfl⟩ := hνsurj y
      have := commute_of_mem_statedScalars hz' (s : GL (Fin 3) K)
      have h1 := hνβ s s (by
        calc (s : GL (Fin 3) K) = (s : GL (Fin 3) K) * x * x⁻¹ := (mul_inv_cancel_right _ _).symm
          _ = x * s * x⁻¹ := by rw [this])
      simpa using h1
    have hx3 : x ^ 3 ∈ zPi π 3 (p ^ f) K := by
      obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
      rw [zPi_eq hπ hq' hτ hτ1]
      refine Subgroup.mem_inf.2 ⟨pow_mem hx 3, ?_⟩
      refine mem_statedScalars_of_comm_mod hK hq hq2 fun s hs => ?_
      let s0 : ↥(slPi π 3 (p ^ f) K) := ⟨s, hs⟩
      let t1 : ↥(slPi π 3 (p ^ f) K) := ⟨x * s0 * x⁻¹, conj_mem_slPi hπ hx s0.2⟩
      let t2 : ↥(slPi π 3 (p ^ f) K) := ⟨x * t1 * x⁻¹, conj_mem_slPi hπ hx t1.2⟩
      let t3 : ↥(slPi π 3 (p ^ f) K) := ⟨x * t2 * x⁻¹, conj_mem_slPi hπ hx t2.2⟩
      have h1 : β (ν s0) = ν t1 := hνβ s0 t1 rfl
      have h2 : β (ν t1) = ν t2 := hνβ t1 t2 rfl
      have h3 : β (ν t2) = ν t3 := hνβ t2 t3 rfl
      have hβν : (β ^ 3) (ν s0) = ν s0 := by rw [hβ3]; rfl
      have h4 : ν s0 = ν t3 := by
        rw [← hβν]
        simp only [pow_succ, pow_zero, one_mul, MulAut.mul_apply]
        rw [h1, h2, h3]
      exact mem_centMod_of_nu_eq hνker t3 (by
        change x * (x * (x * (s0 : GL (Fin 3) K) * x⁻¹) * x⁻¹) * x⁻¹ = _
        rw [pow_three']
        group) h4
    exact ⟨ν, hνsurj, hνker, x, hx, hxZ, hx3, hνβ⟩
  · right
    refine ⟨σ, hσ, (ε.trans κ⁻¹).trans pkg.η.symm, ?_⟩
    have h1 : MulAut.congr ((ε.trans κ⁻¹).trans pkg.η.symm) β =
        MulAut.congr pkg.η.symm (MulAut.congr κ⁻¹ (MulAut.congr ε β)) := by
      rw [congr_trans', congr_trans']
    rw [h1, hβ', congr_self, inv_inv]
    have h2 : κ⁻¹ * (κ * MulAut.congr pkg.η (centerDescend _ (frobSL hK σ)) * κ⁻¹) * κ =
        MulAut.congr pkg.η (centerDescend _ (frobSL hK σ)) := by group
    rw [h2]
    ext x
    simp [MulAut.congr_apply]

end Dichot

section Frob

variable {π : Bool} {p f : ℕ} {K : Type} [Field K]

theorem rtd_frobProj_data (hK : PiField π p f K) (hq : ModThree π (p ^ f)) {σ : K ≃+* K}
    (d : FrobData hK σ) :
    ∃ S₀ : Subgroup (↥(slPi π 3 (p ^ f) K) ⧸ Subgroup.center ↥(slPi π 3 (p ^ f) K)),
      S₀ ≤ fixSub (centerDescend ↥(slPi π 3 (p ^ f) K) (frobSL hK σ)) ∧
      ⁅fixSub (centerDescend ↥(slPi π 3 (p ^ f) K) (frobSL hK σ)),
        fixSub (centerDescend ↥(slPi π 3 (p ^ f) K) (frobSL hK σ))⁆ ≤ S₀ ∧
      (∀ a ∈ fixSub (centerDescend ↥(slPi π 3 (p ^ f) K) (frobSL hK σ)),
        ∃ n : ℕ, a ^ 3 ^ n ∈ S₀) ∧
      Nonempty (↥(slPi π 3 (p ^ d.f₀) d.K₀) ⧸ Subgroup.center ↥(slPi π 3 (p ^ d.f₀) d.K₀) ≃*
        ↥S₀) := by
  set G := ↥(slPi π 3 (p ^ f) K) with hG
  let pm : G →* G ⧸ Subgroup.center G := QuotientGroup.mk' _
  have hsurj : Function.Surjective pm := QuotientGroup.mk'_surjective _
  have hker : ∀ c, pm c = 1 → c ∈ Subgroup.center G := fun c h => (QuotientGroup.eq_one_iff c).1 h
  have hc : ∀ x, pm (frobSL hK σ x) = centerDescend G (frobSL hK σ) (pm x) := fun x => rfl
  have h3 : ∀ c, pm c = 1 → ∃ n : ℕ, c ^ 3 ^ n = 1 := fun c h =>
    ⟨1, by simpa using pow_three_of_mem_center hK hq (hker c h)⟩
  set S := fixSub (frobSL hK σ) with hS
  let θ : ↥(slPi π 3 (p ^ d.f₀) d.K₀) →* G ⧸ Subgroup.center G := pm.comp d.incl
  have hrange : θ.range = S.map pm := by
    rw [MonoidHom.range_comp, ← d.fixSub_eq]
  have hker' : θ.ker = Subgroup.center ↥(slPi π 3 (p ^ d.f₀) d.K₀) := by
    ext s0
    rw [MonoidHom.mem_ker]
    constructor
    · intro h
      have h1 : d.incl s0 ∈ Subgroup.center G := hker _ h
      rw [← d.map_center_incl hq] at h1
      obtain ⟨z, hz, hzs⟩ := h1
      rwa [← d.incl_injective hzs]
    · intro h
      apply (QuotientGroup.eq_one_iff _).2
      rw [← d.map_center_incl hq]
      exact ⟨s0, h, rfl⟩
  let e1 : ↥(slPi π 3 (p ^ d.f₀) d.K₀) ⧸ Subgroup.center ↥(slPi π 3 (p ^ d.f₀) d.K₀) ≃*
      ↥(S.map pm) :=
    (QuotientGroup.quotientMulEquivOfEq hker'.symm).trans
      ((QuotientGroup.quotientKerEquivRange θ).trans (MulEquiv.subgroupCongr hrange))
  refine ⟨S.map pm, ?_, fixSub_commutator_le_map hsurj hker hc,
    fun a ha => exists_pow_mem_map_fixSub hsurj hker h3 hc ha, ⟨e1⟩⟩
  rintro _ ⟨x, hx, rfl⟩
  rw [mem_fixSub, ← hc, mem_fixSub.1 hx]

end Frob

section Model

variable {π : Bool} {p f : ℕ} {K : Type} [Field K]

theorem rtd_prime_pow_mod_two {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) :
    (p ^ f) % 2 = 0 ↔ p = 2 := by
  constructor
  · intro h
    have h2 : 2 ∣ p ^ f := Nat.dvd_of_mod_eq_zero h
    exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1
      (Nat.prime_two.dvd_of_dvd_pow h2)).symm
  · rintro rfl
    exact Nat.mod_eq_zero_of_dvd (dvd_pow_self 2 (by omega))

theorem rtd_kLevel_projModel_le (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (hq2 : 2 < p ^ f) :
    kLevel 3 (↥(slPi π 3 (p ^ f) K) ⧸ Subgroup.center ↥(slPi π 3 (p ^ f) K)) ≤
      if p = 2 then 2 else 3 := by
  have := hK.finite
  have e := QuotientGroup.quotientMulEquivOfEq (center_slPi_eq hK hq)
  rw [kLevel_congr 3 e]
  have hpar := rtd_prime_pow_mod_two hK.prime hK.one_le
  cases π
  · have hKq : Nat.card K = (p ^ f) ^ 2 := by rw [hK.card, piCard, Bool.cond_false]
    have h := rtd_kLevel_psu_three_le K (p ^ f) hKq hq (by omega)
    by_cases h2 : p = 2
    · rw [if_pos h2]
      rwa [if_pos (hpar.2 h2)] at h
    · rw [if_neg h2]
      rw [if_neg (fun h' => h2 (hpar.1 h'))] at h
      exact h
  · have hKq : Nat.card K = p ^ f := by rw [hK.card, piCard, Bool.cond_true]
    have h := rtd_kLevel_psl_three_le K (by rw [hKq]; exact hq)
    rw [hKq] at h
    by_cases h2 : p = 2
    · rw [if_pos h2]
      rwa [if_pos (hpar.2 h2)] at h
    · rw [if_neg h2]
      rw [if_neg (fun h' => h2 (hpar.1 h'))] at h
      exact h

theorem rtd_field_case (hK : PiField π p f K) (hq : ModThree π (p ^ f)) {σ : K ≃+* K}
    (hσ : orderOf σ = 3) {I : Subgroup (↥(slPi π 3 (p ^ f) K) ⧸ Subgroup.center ↥(slPi π 3 (p ^ f) K))}
    (hI : GLAPComponent 3 (fixSub (centerDescend ↥(slPi π 3 (p ^ f) K) (frobSL hK σ))) I) :
    kLevel 3 (PSimple 3 I) ≤ if p = 2 then 2 else 3 := by
  have := hK.finite
  obtain ⟨d⟩ := exists_frobData hK hσ
  have := d.hP.finite
  obtain ⟨S₀, hSF, hcomm, hpow, ⟨e1⟩⟩ := rtd_frobProj_data hK hq d
  have hq₀ := d.modThree hq
  have hp1 : 2 ≤ p ^ d.f₀ :=
    le_trans hK.prime.two_le (Nat.le_self_pow (by have := d.hP.one_le; omega) p)
  by_cases hπ2 : π = false ∧ p ^ d.f₀ = 2
  · exfalso
    obtain ⟨rfl, h2⟩ := hπ2
    have hsolv := (isSolvable_slPi_false_two d.hP h2).2
    haveI : Group.IsSolvable ↥S₀ :=
      Group.isSolvable_of_isSolvable_injective (f := e1.symm.toMonoidHom) e1.symm.injective
    exact rtd_false_of_component_of_solvable inferInstance hcomm hI
  · have hne : π = false → p ^ d.f₀ ≠ 2 := fun h h2 => hπ2 ⟨h, h2⟩
    have hq2₀ : 2 < p ^ d.f₀ := by
      cases π
      · have := hne rfl
        omega
      · change p ^ d.f₀ % 3 = 1 at hq₀
        omega
    have hS₀q : CFSG.Open.IsQuasisimple ↥(slPi π 3 (p ^ d.f₀) d.K₀) :=
      isQuasisimple_slPi d.hP hne
    have hS₀p : Group.IsPerfect ↥(slPi π 3 (p ^ d.f₀) d.K₀) := (Group.isPerfect_def).2 hS₀q.1
    have hqT := isQuasisimple_quotient_center hS₀q
    have hqS : CFSG.Open.IsQuasisimple ↥S₀ := isQuasisimple_open_of_mulEquiv e1.symm hqT
    have hcT : Subgroup.center (↥(slPi π 3 (p ^ d.f₀) d.K₀) ⧸
        Subgroup.center ↥(slPi π 3 (p ^ d.f₀) d.K₀)) = ⊥ :=
      Group.IsPerfect.center_quotient_center_eq_bot _
    have hcS : Subgroup.center ↥S₀ = ⊥ :=
      center_eq_bot_of_mulEquiv_of_center_eq_bot e1.symm hcT
    have hO : GLAPPrimeCore 3 ↥S₀ = ⊥ := by
      refine glaPPrimeCore_eq_bot_of_quasisimple hqS (fun z hz => ?_) ?_
      · rw [hcS, Subgroup.mem_bot] at hz
        rw [hz]
        exact one_pow 3
      · rw [Nat.card_congr e1.symm.toEquiv]
        exact three_dvd_card_slPi_quot d.hP hq₀
    obtain ⟨-, comp, -⟩ := layer_of_normal_quasisimple hSF hcomm hpow hqS hO
    have hIS : I = S₀ := (comp I).1 hI
    subst hIS
    obtain ⟨g⟩ := rtd_nonempty_pSimple_equiv_quasisimple hI e1 hqT
      (by rw [hcT, Subgroup.card_bot]; exact Nat.coprime_one_right 3)
    rw [kLevel_congr 3 (g.trans ((QuotientGroup.quotientMulEquivOfEq hcT).trans
      QuotientGroup.quotientBot))]
    exact rtd_kLevel_projModel_le d.hP hq₀ hq2₀

theorem rtd_downLe_projModel (hK : PiField π p f K) (hq : ModThree π (p ^ f)) (hq2 : 2 < p ^ f) :
    DownLe 3 (if p = 2 then 2 else 3)
      (↥(slPi π 3 (p ^ f) K) ⧸ Subgroup.center ↥(slPi π 3 (p ^ f) K)) := by
  have := hK.finite
  intro β hβ3 I hI
  by_cases hβ1 : β = 1
  · subst hβ1
    rw [rtd_fixSubgroup_one] at hI
    have hGq : CFSG.Open.IsQuasisimple ↥(slPi π 3 (p ^ f) K) :=
      isQuasisimple_slPi hK (fun _ h => by omega)
    haveI : IsSimpleGroup (↥(slPi π 3 (p ^ f) K) ⧸ Subgroup.center ↥(slPi π 3 (p ^ f) K)) :=
      hGq.2
    have hnc := CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hGq
    obtain ⟨g⟩ := rtd_nonempty_pSimple_equiv_top Nat.prime_three hnc hI
    rw [kLevel_congr 3 g]
    exact rtd_kLevel_projModel_le hK hq hq2
  · rcases rtd_dichot_proj hK hq hq2 (MulEquiv.refl _) hβ3 hβ1 with hin | ⟨σ, hσ, e2, hc⟩
    · rcases inner_lay_iso hK hq hq2 hin with hnone | ⟨Φ, hΦ, hall⟩
      · exact absurd hI (hnone I)
      · have hIΦ : I = Φ.range := hall I hI
        obtain ⟨F, _, _, hFc, ⟨eF⟩⟩ := exists_sl2_model hK
        let eJ : ↥(slPi π 2 (p ^ f) K) ≃* I :=
          (MonoidHom.ofInjective hΦ).trans (MulEquiv.subgroupCongr hIΦ.symm)
        have hGq : CFSG.Open.IsQuasisimple ↥(slPi π 2 (p ^ f) K) :=
          isQuasisimple_open (isQuasisimple_slPi_two hK hq hq2)
        have hZ : Nat.Coprime 3 (Nat.card (Subgroup.center ↥(slPi π 2 (p ^ f) K))) := by
          refine rtd_coprime_three_of_sq fun z hz => ?_
          have hz' : eF z ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
            rw [← Subgroup.map_center_eq eF]
            exact ⟨z, hz, rfl⟩
          apply eF.injective
          rw [map_pow, map_one]
          exact sl2_center_sq hz'
        obtain ⟨g⟩ := rtd_nonempty_pSimple_equiv_quasisimple hI eJ hGq hZ
        let g' : ↥(slPi π 2 (p ^ f) K) ⧸ Subgroup.center ↥(slPi π 2 (p ^ f) K) ≃*
            StatedProj (StatedSL 2 F) :=
          (QuotientGroup.congr _ _ eF (Subgroup.map_center_eq eF)).trans
            (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F)
        rw [kLevel_congr 3 (g.trans g')]
        have hmod : (p ^ f) % 3 ≠ 0 := by
          cases π
          · change p ^ f % 3 = 2 at hq
            omega
          · change p ^ f % 3 = 1 at hq
            omega
        refine (rtd_kLevel_psl_two_le F (by rw [hFc]; exact hmod) (by rw [hFc]; omega)).trans ?_
        split_ifs <;> omega
    · obtain ⟨hI', ⟨g⟩⟩ := rtd_exists_pSimple_equiv_map Nat.prime_three e2 β hI
      rw [hc] at hI'
      rw [kLevel_congr 3 g]
      exact rtd_field_case hK hq hσ hI'

end Model

end CFSG.LocalAnalysis.GLTheoremA
