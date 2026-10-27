module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxFiveI
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxFiveH

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

theorem false_of_three_fix_of_not_mem (hPump : Sol78.AlternatingPumpUpInput)
    (hN1 : TwoGroupAltCoverExclusion) (h13 : Sol76T13.SolomonThm13Simple)
    (hML : Sol78.MaximalityLemmaInput) (hSch : SolAltLit.SchurAlternatingMultiplierInput)
    [Finite X] [IsSimpleGroup X] (hnab : ∃ a b : X, a * b ≠ b * a)
    (hKP : Assembly.KProper Blueprint.Catalog X)
    (hunb : ∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥)
    (hnU : ¬ OutcomeLocal.UOutcome X) {t : X} {J : Subgroup X}
    (hpair : Sol78.IsSolomonPair t J 9) (θ : ↥J ⧸ pPrimeCore 2 ↥J ≃* alternatingGroup (Fin 9))
    {c e₀ : X} (he₀ : e₀ ∈ J) (hc2 : c * c = 1) (hcN : c ∈ normalizer (J : Set X))
    (hce : c * e₀⁻¹ ∈ UnbalancedLayer.coreActionKernel J)
    (hs4 : (coreImage θ he₀).support.card = 4) {Jc : Subgroup X}
    (hJcJ : Jc ≤ J ⊓ centralizer ({c} : Set X))
    (χ : ↥Jc ⧸ pPrimeCore 2 ↥Jc ≃*
      alternatingGroup ↥((coreImage θ he₀).supportᶜ : Finset (Fin 9)))
    (hχ : ∀ (x : ↥Jc) (hx : (x : X) ∈ J),
      Perm.ofSubtype ((χ (x : ↥Jc ⧸ pPrimeCore 2 ↥Jc) : alternatingGroup _) :
        Perm ↥((coreImage θ he₀).supportᶜ : Finset (Fin 9))) = coreImage θ hx)
    {M : Subgroup X} (hMC : M ≤ centralizer ({c} : Set X)) (hJcM : Jc ≤ M) {r : ℕ}
    {θM : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin r)}
    {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin r)} (hρ : IsPermAction θM ρ) (hr7 : 7 ≤ r)
    {τ : Perm (Fin r)} (hτ5 : r - τ.support.card = 5)
    (hJcτ : ∀ (z : X) (hz : z ∈ Jc), ρ ⟨z, le_normalizer (hJcM hz)⟩ ∈
      (fixAlt τ).map (alternatingGroup (Fin r)).subtype)
    (hsurj : ∀ b ∈ fixAlt τ, ∃ (z : X) (hz : z ∈ Jc),
      ρ ⟨z, le_normalizer (hJcM hz)⟩ = (b : Perm (Fin r)))
    (hO : ∀ (z : X) (hz : z ∈ Jc), z ∈ coreNOf Jc → ρ ⟨z, le_normalizer (hJcM hz)⟩ = 1)
    {a : X} (ha2 : a * a = 1) (hac : a * c = c * a) (hat : a * t = t * a)
    (haM : a ∈ normalizer (M : Set X)) (h3 : (ρ ⟨a, haM⟩).supportᶜ.card = 3)
    {j₀ : X} (hj₀ : j₀ ∈ J) (haj₀ : a * j₀⁻¹ ∈ UnbalancedLayer.coreActionKernel J)
    (hj₀4 : (coreImage θ hj₀).support.card ≤ 4)
    {j' : X} (hj' : j' ∈ Jc) (haj' : a * j'⁻¹ ∈ UnbalancedLayer.coreActionKernel Jc)
    (haJc : a ∉ Jc) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hβ : Fintype.card ↥((coreImage θ he₀).supportᶜ : Finset (Fin 9)) = 5 := by
    rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin, hs4]
  let eJc : ↥Jc ⧸ pPrimeCore 2 ↥Jc ≃* alternatingGroup (Fin 5) :=
    χ.trans (Fintype.equivFinOfCardEq hβ).altCongrHom
  have hJcN : Jc ≤ normalizer (M : Set X) := fun z hz => le_normalizer (hJcM hz)
  have hJcJ' : Jc ≤ J := hJcJ.trans inf_le_left
  have hJcc : Jc ≤ centralizer ({c} : Set X) := hJcJ.trans inf_le_right
  have hJCt : J ≤ centralizer ({t} : Set X) := hpair.1.2.1
  obtain ⟨j, hjJc, hj2, haj, hajK⟩ := exists_involution_of_acts (by norm_num) eJc ha2 hj' haj'
  have hjJ : j ∈ J := hJcJ' hjJc
  have hjinv : j⁻¹ = j := inv_eq_of_mul_eq_one_right hj2
  have hyN : a * j⁻¹ ∈ normalizer (M : Set X) := mul_mem haM (inv_mem (hJcN hjJc))
  have hyfix : ∀ v, v ∉ τ.support → ρ ⟨a * j⁻¹, hyN⟩ v = v := fun v hv =>
    apply_eq_of_mem_cak_of_onto hJcN (by omega) hsurj hO hyN hajK hv
  have hsplit : ρ ⟨a, haM⟩ = ρ ⟨a * j⁻¹, hyN⟩ * ρ ⟨j, hJcN hjJc⟩ := by
    rw [← map_mul]
    congr 1
    apply Subtype.ext
    change a = a * j⁻¹ * j
    group
  obtain ⟨bj, hbj, hbje⟩ := hJcτ j hjJc
  have hjA : ρ ⟨j, hJcN hjJc⟩ ∈ alternatingGroup (Fin r) := by
    rw [← hbje]
    exact bj.2
  have hjsupp : (ρ ⟨j, hJcN hjJc⟩).support ⊆ τ.supportᶜ := by
    rw [← hbje]
    exact mem_fixAlt.mp hbj
  have hρj2 : ρ ⟨j, hJcN hjJc⟩ * ρ ⟨j, hJcN hjJc⟩ = 1 := by
    rw [← map_mul]
    convert map_one ρ
    exact Subtype.ext hj2
  have h3' : (ρ ⟨a * j⁻¹, hyN⟩ * ρ ⟨j, hJcN hjJc⟩).supportᶜ.card = 3 := by
    rw [← hsplit]
    exact h3
  obtain ⟨hj4, hy7⟩ := card_support_of_three_fix hyfix hjsupp hjA hρj2 hτ5 h3'
  have hθj : coreImage θ hjJ ≠ 1 := by
    intro h
    have h1 := hχ ⟨j, hjJc⟩ hjJ
    rw [h] at h1
    have h2 : ((χ ((⟨j, hjJc⟩ : ↥Jc) : ↥Jc ⧸ pPrimeCore 2 ↥Jc) :
        alternatingGroup ↥((coreImage θ he₀).supportᶜ : Finset (Fin 9))) :
          Perm ↥((coreImage θ he₀).supportᶜ : Finset (Fin 9))) = 1 := by
      apply Perm.ofSubtype_injective
      rw [h1, map_one]
    have h3 : χ ((⟨j, hjJc⟩ : ↥Jc) : ↥Jc ⧸ pPrimeCore 2 ↥Jc) = 1 := Subtype.ext h2
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff] at h3
    have h4 := hO j hjJc ⟨_, h3, rfl⟩
    have h5 : (ρ ⟨j, hJcN hjJc⟩).support.card = 0 := by
      rw [h4, Perm.support_one, Finset.card_empty]
    omega
  have hyK : a * j⁻¹ ∈ UnbalancedLayer.coreActionKernel J :=
    mul_inv_mem_cak_of_four θ he₀ hs4 hJcJ' χ hχ hjJc hj2 hθj hajK hj₀ haj₀ hj₀4
  have hjc : j * c = c * j := mem_centralizer_singleton_iff.mp (hJcc hjJc)
  have hjt : j * t = t * j := mem_centralizer_singleton_iff.mp (hJCt hjJ)
  have hyc : a * j⁻¹ * c = c * (a * j⁻¹) := by
    rw [hjinv]
    calc a * j * c = a * (j * c) := by group
      _ = a * (c * j) := by rw [hjc]
      _ = (a * c) * j := by group
      _ = (c * a) * j := by rw [hac]
      _ = c * (a * j) := by group
  have hyt : a * j⁻¹ * t = t * (a * j⁻¹) := by
    rw [hjinv]
    calc a * j * t = a * (j * t) := by group
      _ = a * (t * j) := by rw [hjt]
      _ = (a * t) * j := by group
      _ = (t * a) * j := by rw [hat]
      _ = t * (a * j) := by group
  have hy2 : a * j⁻¹ * (a * j⁻¹) = 1 := by
    rw [hjinv]
    calc a * j * (a * j) = a * (j * a) * j := by group
      _ = a * (a * j) * j := by rw [haj]
      _ = (a * a) * (j * j) := by group
      _ = 1 := by rw [ha2, hj2, one_mul]
  have hy1 : a * j⁻¹ ≠ 1 := by
    intro h
    apply haJc
    have h1 : a = j := by
      calc a = a * j⁻¹ * j := by group
        _ = j := by rw [h, one_mul]
    rw [h1]
    exact hjJc
  have hyo : orderOf (a * j⁻¹) = 2 := orderOf_eq_prime (by rw [sq]; exact hy2) hy1
  obtain ⟨M₁, θ₁, ρ₁, ε, hρ₁, hCyN, hconj⟩ :=
    exists_pump_of_kernel hPump hN1 h13 hML hSch hnab hKP hunb hnU hpair θ hyo hyt hyK
  have hcy : c ∈ centralizer ({a * j⁻¹} : Set X) := mem_centralizer_singleton_iff.mpr hyc.symm
  have hjy : j ∈ centralizer ({a * j⁻¹} : Set X) := by
    rw [mem_centralizer_singleton_iff, hjinv]
    calc j * (a * j) = (j * a) * j := by group
      _ = (a * j) * j := by rw [← haj]
  have hρ₁c : ρ₁ ⟨c, hCyN hcy⟩ = ε * coreImage θ he₀ * ε⁻¹ := hconj hcy hcN he₀ hce
  have hρ₁j : ρ₁ ⟨j, hCyN hjy⟩ = ε * coreImage θ hjJ * ε⁻¹ :=
    hconj hjy (le_normalizer hjJ) hjJ (by rw [mul_inv_cancel]; exact one_mem _)
  have hc4 : (ρ₁ ⟨c, hCyN hcy⟩).support.card = 4 := by rw [hρ₁c, Perm.card_support_conj, hs4]
  have hj1 : ρ₁ ⟨j, hCyN hjy⟩ ≠ 1 := by
    rw [hρ₁j]
    intro h
    apply hθj
    calc coreImage θ hjJ = ε⁻¹ * (ε * coreImage θ hjJ * ε⁻¹) * ε := by group
      _ = 1 := by rw [h]; group
  set σy := ρ ⟨a * j⁻¹, hyN⟩ with hσydef
  have hσy7 : r - σy.support.card = 7 := by omega
  let Hm : Subgroup ↥(normalizer (M : Set X)) :=
    (M ⊓ centralizer ({a * j⁻¹} : Set X)).subgroupOf (normalizer (M : Set X)) ⊓
      ((fixAlt σy).map (alternatingGroup (Fin r)).subtype).comap ρ
  let H : Subgroup X := Hm.map (normalizer (M : Set X)).subtype
  have hHN : H ≤ normalizer (M : Set X) := map_subtype_le _
  have hmemH : ∀ (z : X) (hz : z ∈ H), z ∈ M ∧ z ∈ centralizer ({a * j⁻¹} : Set X) ∧
      ρ ⟨z, hHN hz⟩ ∈ (fixAlt σy).map (alternatingGroup (Fin r)).subtype := by
    rintro _ ⟨w, ⟨⟨hwM, hwy⟩, hwρ⟩, rfl⟩
    exact ⟨hwM, hwy, hwρ⟩
  have hHmem : ∀ (z : X) (hzN : z ∈ normalizer (M : Set X)), z ∈ M →
      z ∈ centralizer ({a * j⁻¹} : Set X) →
      ρ ⟨z, hzN⟩ ∈ (fixAlt σy).map (alternatingGroup (Fin r)).subtype → z ∈ H :=
    fun z hzN hzM hzy hzρ => ⟨⟨z, hzN⟩, ⟨⟨hzM, hzy⟩, hzρ⟩, rfl⟩
  have hHN₁ : H ≤ normalizer (M₁ : Set X) := fun z hz => hCyN (hmemH z hz).2.1
  have hjF : (⟨ρ ⟨j, hJcN hjJc⟩, hjA⟩ : alternatingGroup (Fin r)) ∈ fixAlt σy := by
    rw [mem_fixAlt]
    intro v hv
    have hvτ := hjsupp hv
    rw [Finset.mem_compl] at hvτ ⊢
    intro hvy
    exact (Perm.mem_support.mp hvy) (hyfix v hvτ)
  have hjH : j ∈ H := hHmem j (hJcN hjJc) (hJcM hjJc) hjy ⟨_, hjF, rfl⟩
  refine false_of_alt_seven_of_four (H := ↥H) (ρ.comp (inclusion hHN)) (ρ₁.comp (inclusion hHN₁))
    (by norm_num) (σ := ρ₁ ⟨c, hCyN hcy⟩) ?_ (by omega) ?_ hσy7 ?_ ?_ ?_
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
    have hbc : (b : Perm (Fin r)) * ρ ⟨a * j⁻¹, hyN⟩ = ρ ⟨a * j⁻¹, hyN⟩ * b := by
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

end CFSG.ComponentClassification.SolMax
