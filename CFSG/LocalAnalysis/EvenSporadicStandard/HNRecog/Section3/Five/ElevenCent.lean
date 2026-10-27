module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Five.ElevenCard
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Five.OddOrbit
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Five.Generic.Burnside
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Five.Generic.Inversion
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Five.Generic.Cyclic

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem isShapeCentralizerEleven_of_mem_Gx (hI : TwoHSInterface) (hU : U35Facts) {G : Type}
    [Group G] [Finite G] {a z : G} (h : IsF5Type a z)
    (hcard : Nat.card G = 2 ^ 14 * 3 ^ 6 * 5 ^ 6 * 7 * 11 * 19) (hGam : GammaFacts a z)
    (hT7 : TableVIIFacts a z) (hFive : FiveFacts a z) {ω : G} (hωa : ω ∈ Gx a)
    (hω : orderOf ω = 11) : IsShapeCentralizerEleven ↥(Gx ω) := by
  classical
  have ha : a * a = 1 := by
    have h2 : a ^ 2 = 1 := (orderOf_dvd_iff_pow_eq_one (n := 2)).mp (by rw [h.orderOf_a])
    simpa [pow_two] using h2
  have ha1 : a ≠ 1 := by
    intro h1
    have hord := h.orderOf_a
    rw [h1, orderOf_one] at hord
    norm_num at hord
  have haK : a ∈ Gx ω := mem_Gx.mpr (mem_Gx.mp hωa).symm
  obtain ⟨N, hNK, hNn, hNodd, hNinf, hNsup⟩ :=
    exists_normal_two_complement_of_involution (K := Gx ω) haK ha ha1
      (padicValNat_card_Gx_eleven hI h hωa hω)
  have hprime : ∀ p, p.Prime → p ∣ Nat.card ↥N → p = 11 := by
    intro p hp hpN
    by_contra hp11
    have hp2 : p ≠ 2 := by
      intro hp2eq
      exact hNodd (hp2eq ▸ hpN)
    have hKcap : Gx ω ⊓ Subgroup.centralizer ({a} : Set G) = Gxy a ω := by
      rw [Gxy_eq_inf]
      exact inf_comm _ _
    have hCcard : Nat.card ↥(Gx ω ⊓ Subgroup.centralizer ({a} : Set G)) = 22 := by
      rw [hKcap, card_Gxy_eleven hI h hωa hω]
    have hC : ¬ p ∣ Nat.card ↥(Gx ω ⊓ Subgroup.centralizer ({a} : Set G)) := by
      rw [hCcard]
      intro hdiv
      have h22 : (22 : ℕ) = 2 * 11 := by norm_num
      rw [h22] at hdiv
      rcases hp.dvd_mul.mp hdiv with h2 | h11
      · exact hp2 ((Nat.dvd_prime Nat.prime_two).mp h2 |>.resolve_left hp.ne_one)
      · exact hp11 ((Nat.dvd_prime (by norm_num : Nat.Prime 11)).mp h11
          |>.resolve_left hp.ne_one)
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨σ, hσN, hσorder, hσinv⟩ :=
      exists_inverted_element (K := Gx ω) hNK hNn hNodd haK ha hpN hC
    let x : G := σ * a * σ⁻¹
    have hxconj : IsConj a x := isConj_iff.2 ⟨σ, rfl⟩
    have hax : a * x = σ⁻¹ * σ⁻¹ := by
      change a * (σ * a * σ⁻¹) = σ⁻¹ * σ⁻¹
      calc a * (σ * a * σ⁻¹) = (a * σ * a) * σ⁻¹ := by group
        _ = σ⁻¹ * σ⁻¹ := by rw [hσinv]
    have hodd_p : Odd p := hp.odd_of_ne_two hp2
    have hcop : (orderOf σ⁻¹).Coprime 2 := by
      rw [orderOf_inv, hσorder]
      exact Nat.coprime_two_right.mpr hodd_p
    have horder_ax : orderOf (a * x) = p := by
      rw [hax, ← pow_two, hcop.orderOf_pow, orderOf_inv, hσorder]
    have hodd : Odd (orderOf (a * x)) := by rw [horder_ax]; exact hodd_p
    have hx_ne_a : x ≠ a := by
      intro hxa
      have h1 : orderOf (a * x) = 1 := by rw [hxa, ha, orderOf_one]
      rw [horder_ax] at h1
      exact hp.ne_one h1
    have hωσ : Commute ω σ := mem_Gx.mp (hNK hσN)
    have hσω : Commute σ ω := hωσ.symm
    have haω : Commute a ω := mem_Gx.mp hωa
    have hxω : Commute x ω := by
      change Commute (σ * a * σ⁻¹) ω
      exact (hσω.mul_left haω).mul_left hσω.inv_left
    have hωmem : ω ∈ Gxy a x := mem_Gxy.mpr ⟨hωa, mem_Gx.mpr hxω.eq⟩
    have h11dvd : 11 ∣ Nat.card ↥(Gxy a x) := by
      have := Subgroup.orderOf_dvd_natCard (Gxy a x) hωmem
      simpa [hω] using this
    exact (not_dvd_card_Gxy_of_odd hU h hGam hT7 hFive hxconj hx_ne_a hodd) h11dvd
  let m := (Nat.card ↥N).primeFactorsList.length
  have hm : Nat.card ↥N = 11 ^ m :=
    Nat.eq_prime_pow_of_unique_prime_dvd (p := 11) (Nat.card_pos.ne')
      (fun {d} hd hdn => hprime d hd hdn)
  have hm_le : m ≤ 1 := by
    by_contra hm2
    have h2 : 2 ≤ m := by omega
    have hdvdN : 11 ^ 2 ∣ Nat.card ↥N := by
      rw [hm]
      exact pow_dvd_pow 11 h2
    have hdvdG : 11 ^ 2 ∣ Nat.card G := hdvdN.trans (Subgroup.card_subgroup_dvd_card N)
    rw [hcard] at hdvdG
    exact (by norm_num : ¬ 11 ^ 2 ∣ 2 ^ 14 * 3 ^ 6 * 5 ^ 6 * 7 * 11 * 19) hdvdG
  let N' : Subgroup ↥(Gx ω) := N.subgroupOf (Gx ω)
  haveI hN'normal : N'.Normal := hNn
  let T' : Subgroup ↥(Gx ω) := (Subgroup.zpowers a).subgroupOf (Gx ω)
  have hsup' : N' ⊔ T' = ⊤ := by
    have h := Subgroup.subgroupOf_sup (A := N) (A' := Subgroup.zpowers a) (B := Gx ω)
      hNK (Subgroup.zpowers_le.mpr haK)
    rw [hNsup, Subgroup.subgroupOf_self] at h
    exact h.symm
  have hT'map_top : T'.map (QuotientGroup.mk' N') = ⊤ := by
    apply top_le_iff.mp
    intro q hq
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N' q
    have hy : y ∈ N' ⊔ T' := by rw [hsup']; trivial
    rw [Subgroup.mem_sup_of_normal_left] at hy
    obtain ⟨n, hnN', t, htT', hnt⟩ := hy
    refine Subgroup.mem_map.mpr ⟨t, htT', ?_⟩
    have hπn : QuotientGroup.mk' N' n = 1 :=
      (QuotientGroup.eq_one_iff (N := N') n).mpr hnN'
    calc QuotientGroup.mk' N' t = 1 * QuotientGroup.mk' N' t := (one_mul _).symm
      _ = QuotientGroup.mk' N' n * QuotientGroup.mk' N' t := by rw [hπn]
      _ = QuotientGroup.mk' N' (n * t) := (map_mul _ n t).symm
      _ = QuotientGroup.mk' N' y := by rw [hnt]
  have hT'eq : T' = Subgroup.zpowers (⟨a, haK⟩ : ↥(Gx ω)) := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k, Subtype.ext (by simpa using hk)⟩
    · rintro ⟨k, hk⟩
      exact ⟨k, by simpa using congrArg (fun y : ↥(Gx ω) => (y : G)) hk⟩
  have htop_zpowers :
      Subgroup.zpowers (QuotientGroup.mk' N' (⟨a, haK⟩ : ↥(Gx ω))) = ⊤ := by
    rw [← MonoidHom.map_zpowers (QuotientGroup.mk' N') (⟨a, haK⟩ : ↥(Gx ω)), ← hT'eq]
    exact hT'map_top
  let ωk : ↥(Gx ω) := ⟨ω, self_mem_Gx ω⟩
  have hak_dvd2 : orderOf (QuotientGroup.mk' N' (⟨a, haK⟩ : ↥(Gx ω))) ∣ 2 := by
    have := orderOf_map_dvd (QuotientGroup.mk' N') (⟨a, haK⟩ : ↥(Gx ω))
    rwa [Subgroup.orderOf_mk a haK, h.orderOf_a] at this
  have hmem_zp : QuotientGroup.mk' N' ωk ∈
      Subgroup.zpowers (QuotientGroup.mk' N' (⟨a, haK⟩ : ↥(Gx ω))) := by
    rw [htop_zpowers]; trivial
  have hdvd2 : orderOf (QuotientGroup.mk' N' ωk) ∣ 2 :=
    (orderOf_dvd_of_mem_zpowers hmem_zp).trans hak_dvd2
  have hdvd11 : orderOf (QuotientGroup.mk' N' ωk) ∣ 11 := by
    have := orderOf_map_dvd (QuotientGroup.mk' N') ωk
    rwa [Subgroup.orderOf_mk ω (self_mem_Gx ω), hω] at this
  have hgcd : orderOf (QuotientGroup.mk' N' ωk) ∣ 1 := by
    simpa using Nat.dvd_gcd hdvd2 hdvd11
  have horder1 : orderOf (QuotientGroup.mk' N' ωk) = 1 := Nat.dvd_one.mp hgcd
  have hπω1 : QuotientGroup.mk' N' ωk = 1 := orderOf_eq_one_iff.mp horder1
  have hωN' : ωk ∈ N' := (QuotientGroup.eq_one_iff (N := N') ωk).mp hπω1
  have hωN : ω ∈ N := by
    have := (Subgroup.mem_subgroupOf (H := N) (K := Gx ω)).mp hωN'
    simpa [ωk] using this
  have h11dvdN : 11 ∣ Nat.card ↥N := by
    have := Subgroup.orderOf_dvd_natCard N hωN
    simpa [hω] using this
  have hm_ge : 1 ≤ m := by
    by_contra h
    have hm0 : m = 0 := by omega
    rw [hm, hm0, pow_zero] at h11dvdN
    norm_num at h11dvdN
  have hm1 : m = 1 := le_antisymm hm_le hm_ge
  have hNcard : Nat.card ↥N = 11 := by rw [hm, hm1, pow_one]
  have hNeq : N = Subgroup.zpowers ω := by
    have hle : Subgroup.zpowers ω ≤ N := Subgroup.zpowers_le.mpr hωN
    have hcard : Nat.card ↥N ≤ Nat.card ↥(Subgroup.zpowers ω) := by
      rw [hNcard, Nat.card_zpowers, hω]
    exact (Subgroup.eq_of_le_of_card_ge hle hcard).symm
  have hclosure : Subgroup.zpowers ω ⊔ Subgroup.zpowers a =
      Subgroup.closure ({ω, a} : Set G) := by
    apply le_antisymm
    · apply sup_le
      · exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
      · exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
    · exact (Subgroup.closure_le (k := ({ω, a} : Set G))
        (K := Subgroup.zpowers ω ⊔ Subgroup.zpowers a)).2 (by
          intro y hy
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
          rcases hy with h | h
          · rw [h]; exact Subgroup.mem_sup_left (Subgroup.mem_zpowers ω)
          · rw [h]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers a))
  have hK' : Subgroup.closure ({ω, a} : Set G) = Gx ω := by
    rw [← hclosure, ← hNeq, hNsup]
  obtain ⟨e⟩ := nonempty_mulEquiv_zmod_prod_of_commute (x := ω) (y := a) (m := 11) (n := 2)
    (by norm_num) (by norm_num) hω h.orderOf_a (by norm_num) (mem_Gx.mp hωa).symm
  exact ⟨(MulEquiv.subgroupCongr hK').symm.trans e⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3
