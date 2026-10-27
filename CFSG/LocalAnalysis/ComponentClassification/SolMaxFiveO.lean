module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxFiveN
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxFiveH

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

theorem false_of_kernel_involution (hPump : Sol78.AlternatingPumpUpInput)
    (hN1 : TwoGroupAltCoverExclusion) (h13 : Sol76T13.SolomonThm13Simple)
    (hML : Sol78.MaximalityLemmaInput) (hSch : SolAltLit.SchurAlternatingMultiplierInput)
    [Finite X] [IsSimpleGroup X] (hnab : ∃ a b : X, a * b ≠ b * a)
    (hKP : Assembly.KProper Blueprint.Catalog X)
    (hunb : ∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥)
    (hnU : ¬ OutcomeLocal.UOutcome X) {t : X} {J : Subgroup X}
    (hpair : Sol78.IsSolomonPair t J 9) (θ : ↥J ⧸ pPrimeCore 2 ↥J ≃* alternatingGroup (Fin 9))
    {c e₀ : X} (he₀ : e₀ ∈ J) (hc2 : c * c = 1) (hcN : c ∈ normalizer (J : Set X))
    (hce : c * e₀⁻¹ ∈ UnbalancedLayer.coreActionKernel J)
    (hs4 : (coreImage θ he₀).support.card = 4) {M : Subgroup X}
    (hMC : M ≤ centralizer ({c} : Set X)) {r : ℕ}
    {θM : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin r)}
    {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin r)} (hρ : IsPermAction θM ρ) (hr7 : 7 ≤ r)
    {y : X} (hyo : orderOf y = 2) (hyt : y * t = t * y) (hyc : y * c = c * y)
    (hyK : y ∈ UnbalancedLayer.coreActionKernel J) (hyN : y ∈ normalizer (M : Set X))
    (hy7 : r - (ρ ⟨y, hyN⟩).support.card = 7) {j : X} (hjJ : j ∈ J) (hjM : j ∈ M)
    (hj2 : j * j = 1) (hjy : j * y = y * j) (hθj : coreImage θ hjJ ≠ 1)
    (hjfix : (ρ ⟨j, le_normalizer hjM⟩).support ⊆ (ρ ⟨y, hyN⟩).supportᶜ) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hy2 : y * y = 1 := by rw [← sq, ← hyo, pow_orderOf_eq_one]
  obtain ⟨M₁, θ₁, ρ₁, ε, hρ₁, hCyN, hconj⟩ :=
    exists_pump_of_kernel hPump hN1 h13 hML hSch hnab hKP hunb hnU hpair θ hyo hyt hyK
  have hcy : c ∈ centralizer ({y} : Set X) := mem_centralizer_singleton_iff.mpr hyc.symm
  have hjy' : j ∈ centralizer ({y} : Set X) := mem_centralizer_singleton_iff.mpr hjy
  have hρ₁c : ρ₁ ⟨c, hCyN hcy⟩ = ε * coreImage θ he₀ * ε⁻¹ := hconj hcy hcN he₀ hce
  have hρ₁j : ρ₁ ⟨j, hCyN hjy'⟩ = ε * coreImage θ hjJ * ε⁻¹ :=
    hconj hjy' (le_normalizer hjJ) hjJ (by rw [mul_inv_cancel]; exact one_mem _)
  have hc4 : (ρ₁ ⟨c, hCyN hcy⟩).support.card = 4 := by rw [hρ₁c, Perm.card_support_conj, hs4]
  have hj1 : ρ₁ ⟨j, hCyN hjy'⟩ ≠ 1 := by
    rw [hρ₁j]
    intro h
    apply hθj
    calc coreImage θ hjJ = ε⁻¹ * (ε * coreImage θ hjJ * ε⁻¹) * ε := by group
      _ = 1 := by rw [h]; group
  set σy := ρ ⟨y, hyN⟩ with hσydef
  let Hm : Subgroup ↥(normalizer (M : Set X)) :=
    (M ⊓ centralizer ({y} : Set X)).subgroupOf (normalizer (M : Set X)) ⊓
      ((fixAlt σy).map (alternatingGroup (Fin r)).subtype).comap ρ
  let H : Subgroup X := Hm.map (normalizer (M : Set X)).subtype
  have hHN : H ≤ normalizer (M : Set X) := map_subtype_le _
  have hmemH : ∀ (z : X) (hz : z ∈ H), z ∈ M ∧ z ∈ centralizer ({y} : Set X) ∧
      ρ ⟨z, hHN hz⟩ ∈ (fixAlt σy).map (alternatingGroup (Fin r)).subtype := by
    rintro _ ⟨w, ⟨⟨hwM, hwy⟩, hwρ⟩, rfl⟩
    exact ⟨hwM, hwy, hwρ⟩
  have hHmem : ∀ (z : X) (hzN : z ∈ normalizer (M : Set X)), z ∈ M →
      z ∈ centralizer ({y} : Set X) →
      ρ ⟨z, hzN⟩ ∈ (fixAlt σy).map (alternatingGroup (Fin r)).subtype → z ∈ H :=
    fun z hzN hzM hzy hzρ => ⟨⟨z, hzN⟩, ⟨⟨hzM, hzy⟩, hzρ⟩, rfl⟩
  have hHN₁ : H ≤ normalizer (M₁ : Set X) := fun z hz => hCyN (hmemH z hz).2.1
  have hjA : ρ ⟨j, le_normalizer hjM⟩ ∈ alternatingGroup (Fin r) := by
    rw [hρ.apply_of_mem (by omega) ⟨j, hjM⟩]
    exact (θM _).2
  have hjF : (⟨ρ ⟨j, le_normalizer hjM⟩, hjA⟩ : alternatingGroup (Fin r)) ∈ fixAlt σy :=
    mem_fixAlt.mpr hjfix
  have hjH : j ∈ H := hHmem j (le_normalizer hjM) hjM hjy' ⟨_, hjF, rfl⟩
  refine false_of_alt_seven_of_four (H := ↥H) (ρ.comp (inclusion hHN)) (ρ₁.comp (inclusion hHN₁))
    (by norm_num) (σ := ρ₁ ⟨c, hCyN hcy⟩) ?_ (by omega) ?_ hy7 ?_ ?_ ?_
    (j := ⟨j, hjH⟩) (Subtype.ext hj2) hj1
  · rw [← map_mul]
    convert map_one ρ₁
    exact Subtype.ext hc2
  · rintro ⟨z, hz⟩
    have hzc : z * c = c * z := mem_centralizer_singleton_iff.mp (hMC (hmemH z hz).1)
    change ρ₁ ⟨z, hHN₁ hz⟩ * ρ₁ ⟨c, hCyN hcy⟩ = ρ₁ ⟨c, hCyN hcy⟩ * ρ₁ ⟨z, hHN₁ hz⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hzc
  · rintro ⟨z, hz⟩
    exact (hmemH z hz).2.2
  · intro b hb
    have hbc : (b : Perm (Fin r)) * ρ ⟨y, hyN⟩ = ρ ⟨y, hyN⟩ * b := by
      have hd : (b : Perm (Fin r)).Disjoint σy := by
        rw [Perm.disjoint_iff_disjoint_support]
        exact Finset.disjoint_of_subset_left (mem_fixAlt.mp hb) disjoint_compl_left
      exact hd.commute.eq
    obtain ⟨x, hxy, hxb⟩ := hρ.exists_lift_of_two hyN (isPGroup_zpowers_of_mul_self hy2) hbc
    have hxρ : ρ ⟨x, le_normalizer x.2⟩ = (b : Perm (Fin r)) := by
      rw [hρ.apply_of_mem (by omega) x, hxb]
    have hxH : (x : X) ∈ H :=
      hHmem x (le_normalizer x.2) x.2 hxy (by rw [hxρ]; exact ⟨b, hb, rfl⟩)
    exact ⟨⟨x, hxH⟩, hxρ⟩
  · rintro ⟨z, hz⟩ hz1
    have hz1' : ρ ⟨z, le_normalizer (hmemH z hz).1⟩ = 1 := hz1
    have h1 : θM ((⟨z, (hmemH z hz).1⟩ : ↥M) : ↥M ⧸ pPrimeCore 2 ↥M) = 1 := by
      apply Subtype.ext
      rw [← hρ.apply_of_mem (by omega) ⟨z, (hmemH z hz).1⟩]
      exact hz1'
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff] at h1
    have h2 : orderOf (⟨⟨z, (hmemH z hz).1⟩, h1⟩ : ↥(pPrimeCore 2 ↥M)) ∣
        Nat.card (pPrimeCore 2 ↥M) := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk] at h2
    rw [Subgroup.orderOf_mk]
    exact (Nat.coprime_two_left.mp pPrimeCore_coprime_card).of_dvd_nat h2

theorem mem_coreActionKernel_of_support_subset [Finite X] {J Jc : Subgroup X}
    {ρJ : ↥(normalizer (J : Set X)) →* Perm (Fin 9)}
    {θ : ↥J ⧸ pPrimeCore 2 ↥J ≃* alternatingGroup (Fin 9)} (hρJ : IsPermAction θ ρJ)
    {c e₀ : X} (he₀ : e₀ ∈ J) (hJcJ : Jc ≤ J ⊓ centralizer ({c} : Set X))
    (hres : CatalogueBPrimeJoin.primeResidual 2 ↥Jc = ⊤)
    (hinv : ∀ (x : X) (hx : x ∈ J), x * c = c * x → (∃ k : ℕ, x ^ 2 ^ k = 1) →
      (coreImage θ hx).support ⊆ (coreImage θ he₀).supportᶜ → x ∈ Jc)
    (hsubP : ∀ x ∈ Jc, ∃ hx : x ∈ J, (coreImage θ hx).support ⊆ (coreImage θ he₀).supportᶜ)
    (χ : ↥Jc ⧸ pPrimeCore 2 ↥Jc ≃*
      alternatingGroup ↥((coreImage θ he₀).supportᶜ : Finset (Fin 9)))
    (hχ : ∀ (x : ↥Jc) (hx : (x : X) ∈ J),
      Perm.ofSubtype ((χ (x : ↥Jc ⧸ pPrimeCore 2 ↥Jc) : alternatingGroup _) :
        Perm ↥((coreImage θ he₀).supportᶜ : Finset (Fin 9))) = coreImage θ hx)
    {w : X} (hwN : w ∈ normalizer (J : Set X)) (hwc : w * c = c * w)
    (hwD : (ρJ ⟨w, hwN⟩).support ⊆ (coreImage θ he₀).support) :
    w ∈ normalizer (Jc : Set X) ∧ w ∈ UnbalancedLayer.coreActionKernel Jc := by
  classical
  have hJcJ' : Jc ≤ J := hJcJ.trans inf_le_left
  have hJcC : Jc ≤ centralizer ({c} : Set X) := hJcJ.trans inf_le_right
  have hconj : ∀ (x : X) (hx : x ∈ J), (coreImage θ hx).support ⊆ (coreImage θ he₀).supportᶜ →
      coreImage θ ((mem_normalizer_iff.mp hwN x).mp hx) = coreImage θ hx := by
    intro x hx hxs
    have h1 := hρJ ⟨w, hwN⟩ ⟨x, hx⟩
    have h2 : (J.normalizerMonoidHom ⟨w, hwN⟩ ⟨x, hx⟩ : ↥J) =
        ⟨w * x * w⁻¹, (mem_normalizer_iff.mp hwN x).mp hx⟩ := rfl
    rw [h2] at h1
    change coreImage θ _ = ρJ ⟨w, hwN⟩ * coreImage θ hx * (ρJ ⟨w, hwN⟩)⁻¹ at h1
    rw [h1]
    have hd : (ρJ ⟨w, hwN⟩).Disjoint (coreImage θ hx) := by
      rw [Perm.disjoint_iff_disjoint_support]
      exact Finset.disjoint_of_subset_left hwD
        (Finset.disjoint_of_subset_right hxs disjoint_compl_right)
    rw [hd.commute.eq]
    group
  have hwJc : w ∈ normalizer (Jc : Set X) :=
    mem_normalizer_of_fixed_component θ hJcC hres hinv hsubP hwN hwc fun x hx hxs => by
      rw [hconj x hx hxs]
      exact hxs
  refine ⟨hwJc, hwJc, fun l hl => ?_⟩
  have hlJ := hJcJ' hl
  obtain ⟨hlJ', hls'⟩ := hsubP l hl
  have hls : (coreImage θ hlJ).support ⊆ (coreImage θ he₀).supportᶜ := hls'
  have hwinv : w⁻¹ ∈ normalizer (J : Set X) := inv_mem hwN
  have hwl : w⁻¹ * l * w⁻¹⁻¹ ∈ J := (mem_normalizer_iff.mp hwinv l).mp hlJ
  have h1 := hρJ ⟨w⁻¹, hwinv⟩ ⟨l, hlJ⟩
  have h2 : (J.normalizerMonoidHom ⟨w⁻¹, hwinv⟩ ⟨l, hlJ⟩ : ↥J) = ⟨w⁻¹ * l * w⁻¹⁻¹, hwl⟩ := rfl
  rw [h2] at h1
  change coreImage θ hwl = ρJ ⟨w⁻¹, hwinv⟩ * coreImage θ hlJ * (ρJ ⟨w⁻¹, hwinv⟩)⁻¹ at h1
  have hd : (ρJ ⟨w⁻¹, hwinv⟩).Disjoint (coreImage θ hlJ) := by
    rw [Perm.disjoint_iff_disjoint_support]
    have h9 : ρJ ⟨w⁻¹, hwinv⟩ = (ρJ ⟨w, hwN⟩)⁻¹ := by
      rw [← map_inv]
      rfl
    rw [h9, Perm.support_inv]
    exact Finset.disjoint_of_subset_left hwD
      (Finset.disjoint_of_subset_right hls disjoint_compl_right)
  have h3 : coreImage θ hwl = coreImage θ hlJ := by
    rw [h1, hd.commute.eq, mul_inv_cancel_right]
  have hwlJc : w⁻¹ * l * w⁻¹⁻¹ ∈ Jc := by
    have := (mem_normalizer_iff.mp (inv_mem hwJc) l).mp hl
    exact this
  have hz : l⁻¹ * w⁻¹ * l * w ∈ Jc := by
    have h4 : l⁻¹ * w⁻¹ * l * w = l⁻¹ * (w⁻¹ * l * w⁻¹⁻¹) := by group
    rw [h4]
    exact mul_mem (inv_mem hl) hwlJc
  have h5 : coreImage θ (hJcJ' hz) = 1 := by
    have h6 : (⟨l⁻¹ * w⁻¹ * l * w, hJcJ' hz⟩ : ↥J) =
        (⟨l, hlJ⟩ : ↥J)⁻¹ * ⟨w⁻¹ * l * w⁻¹⁻¹, hwl⟩ :=
      Subtype.ext (by simp only [coe_mul, coe_inv]; group)
    have h7 : coreImage θ (hJcJ' hz) = (coreImage θ hlJ)⁻¹ * coreImage θ hwl := by
      unfold coreImage
      rw [h6, QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_inv]
      rfl
    rw [h7, h3, inv_mul_cancel]
  have h8 : ((χ ((⟨_, hz⟩ : ↥Jc) : ↥Jc ⧸ pPrimeCore 2 ↥Jc) :
      alternatingGroup ↥((coreImage θ he₀).supportᶜ : Finset (Fin 9))) :
        Perm ↥((coreImage θ he₀).supportᶜ : Finset (Fin 9))) = 1 := by
    apply Perm.ofSubtype_injective
    rw [hχ ⟨_, hz⟩ (hJcJ' hz), h5, map_one]
  have h9 : χ ((⟨_, hz⟩ : ↥Jc) : ↥Jc ⧸ pPrimeCore 2 ↥Jc) = 1 := Subtype.ext h8
  rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff] at h9
  exact ⟨⟨_, hz⟩, h9, rfl⟩

theorem mem_normalizer_of_mem_normalizer_Jc [Finite X] {c : X} {M Jc : Subgroup X}
    (hMC : M ≤ centralizer ({c} : Set X))
    (hMpc : IsPComponent 2 (M.subgroupOf (centralizer ({c} : Set X)))) (hJcM : Jc ≤ M)
    (hJcperf : ⁅Jc, Jc⁆ = Jc) (hJcq : Nontrivial (↥Jc ⧸ pPrimeCore 2 ↥Jc)) {w : X}
    (hwc : w ∈ centralizer ({c} : Set X)) (hwJc : w ∈ normalizer (Jc : Set X)) :
    w ∈ normalizer (M : Set X) := by
  obtain ⟨hMwC, hMwpc⟩ := isPComponent_conj hMC hMpc hwc
  have hJcMw : Jc ≤ M.map (MulAut.conj w).toMonoidHom := by
    intro z hz
    have h1 : w⁻¹ * z * w ∈ Jc := by
      have := (mem_normalizer_iff.mp (inv_mem hwJc) z).mp hz
      rwa [inv_inv] at this
    exact ⟨w⁻¹ * z * w, hJcM h1, by simp [mul_assoc]⟩
  have heq := eq_of_isPComponent_of_le_inf hMC hMwC hMpc hMwpc hJcM hJcMw hJcperf hJcq
  exact mem_normalizer_iff_map_conj_eq.mpr heq.symm

end CFSG.ComponentClassification.SolMax
