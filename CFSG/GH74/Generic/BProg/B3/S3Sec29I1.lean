module

public import CFSG.GH74.Generic.BProg.B3.S3Sec29I
public import CFSG.GH74.Generic.BProg.B3.S3Ctx29Defs

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.GLS.C3.Layer1 CFSG.ABGLocalTools Subgroup
  Equiv Equiv.Perm
open scoped commutatorElement

namespace S3Sec29I1

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def rho7 (J : Subgroup G) (e : kBar J ≃* alternatingGroup (Fin 7)) :
    ↥J →* Perm (Fin 7) :=
  (alternatingGroup (Fin 7)).subtype.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pPrimeCore 2 ↥J)))

theorem rho7_eq_one_iff (J : Subgroup G) (e : kBar J ≃* alternatingGroup (Fin 7)) (g : ↥J) :
    rho7 J e g = 1 ↔ g ∈ pPrimeCore 2 ↥J := by
  constructor
  · intro h
    have h1 : e (QuotientGroup.mk' (pPrimeCore 2 ↥J) g) = 1 := by
      apply Subtype.ext
      simpa [rho7] using h
    have h2 : QuotientGroup.mk' (pPrimeCore 2 ↥J) g = 1 := by
      simpa using h1
    exact (QuotientGroup.eq_one_iff g).1 h2
  · intro h
    have h2 : QuotientGroup.mk' (pPrimeCore 2 ↥J) g = 1 := (QuotientGroup.eq_one_iff g).2 h
    show ((e (QuotientGroup.mk' (pPrimeCore 2 ↥J) g) : alternatingGroup (Fin 7)) : Perm (Fin 7)) = 1
    rw [h2, map_one]
    rfl

theorem eq_one_of_mem_pPrimeCore {X : Type} [Group X] [Finite X] {g : X}
    (hg : g ∈ pPrimeCore 2 X) (h2 : ∃ n : ℕ, orderOf g = 2 ^ n) : g = 1 := by
  obtain ⟨n, hn⟩ := h2
  have hdvd : orderOf g ∣ Nat.card (pPrimeCore 2 X) := Subgroup.orderOf_dvd_natCard _ hg
  have hcop : Nat.Coprime 2 (Nat.card (pPrimeCore 2 X)) := CFSG.pPrimeCore_coprime_card
  have h1 : orderOf g = 1 := by
    rw [hn] at hdvd ⊢
    have := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_left n hcop) hdvd
    exact this
  exact orderOf_eq_one_iff.1 h1

theorem rho7_eq_one_of_two_elt (J : Subgroup G) (e : kBar J ≃* alternatingGroup (Fin 7)) {g : ↥J}
    (h2 : ∃ n : ℕ, orderOf g = 2 ^ n) (hg : rho7 J e g = 1) : g = 1 :=
  eq_one_of_mem_pPrimeCore ((rho7_eq_one_iff J e g).1 hg) h2

theorem rho7_injective_on {J T : Subgroup G} (e : kBar J ≃* alternatingGroup (Fin 7)) (hTJ : T ≤ J)
    (hT : IsPGroup 2 ↥T) : Function.Injective ((rho7 J e).comp (Subgroup.inclusion hTJ)) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro a ha
  rw [MonoidHom.mem_ker] at ha
  obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.1 hT) a
  have hord : orderOf (Subgroup.inclusion hTJ a) = 2 ^ n := by
    rw [← hn]
    exact orderOf_injective _ (Subgroup.inclusion_injective hTJ) a
  have := rho7_eq_one_of_two_elt J e ⟨n, hord⟩ ha
  have h1 : a = 1 := Subgroup.inclusion_injective hTJ (by simpa using this)
  rw [h1]
  exact Subgroup.one_mem _

theorem two_invol_of_A7 {J H T : Subgroup G} (hJ : IsA7Bar J) (hHJ : H ≤ J) (hperf : ⁅H, H⁆ = H)
    (hne : H ≠ ⊥) (hT : IsSylowOf 2 T H) :
    ∃ s ∈ T, ∃ t ∈ T, s ≠ 1 ∧ t ≠ 1 ∧ s ≠ t ∧ s * s = 1 ∧ t * t = 1 := by
  classical
  obtain ⟨e⟩ := hJ
  have hTH : T ≤ H := hT.le
  have hTJ : T ≤ J := hTH.trans hHJ
  have hperfH : Group.IsPerfect ↥H := Subgroup.isPerfect_iff.mpr hperf
  have : Nontrivial ↥H := (Subgroup.nontrivial_iff_ne_bot H).mpr hne
  have heven : 2 ∣ Nat.card ↥H := S3Sec29I.even_card_of_perfect hperfH
  have hnc : ¬ IsCyclic ↥T := by
    obtain ⟨Q, hQ⟩ := hT.exists_sylow_eq_subgroupOf
    intro hcyc
    have hQc : IsCyclic ↥(Q : Subgroup ↥H) := by
      rw [hQ]
      exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hTH).symm.toMonoidHom
        (Subgroup.subgroupOfEquivOfLe hTH).symm.surjective
    exact S3Sec29I.perfect_sylow_two_not_cyclic hperfH heven Q hQc
  set ρT : ↥T →* Perm (Fin 7) := (rho7 J e).comp (Subgroup.inclusion hTJ) with hρT
  have hinj : Function.Injective ρT := rho7_injective_on e hTJ hT.isPGroup
  let eT : ↥T ≃* ↥ρT.range := MonoidHom.ofInjective hinj
  have hp : IsPGroup 2 ↥ρT.range := hT.isPGroup.of_equiv eT
  have hncr : ¬ IsCyclic ↥ρT.range := fun hc => hnc (isCyclic_of_surjective eT.symm.toMonoidHom
    eT.symm.surjective)
  obtain ⟨s', hs', t', ht', hs1, ht1, hst, hs2, ht2⟩ := S3Sec29I.factQ _ hp hncr
  obtain ⟨s, rfl⟩ := hs'
  obtain ⟨t, rfl⟩ := ht'
  refine ⟨(s : G), s.2, (t : G), t.2, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    apply hs1
    have : s = 1 := Subtype.ext h
    rw [this, map_one]
  · intro h
    apply ht1
    have : t = 1 := Subtype.ext h
    rw [this, map_one]
  · intro h
    apply hst
    have : s = t := Subtype.ext h
    rw [this]
  · have : s * s = 1 := hinj (by rw [map_mul, map_one]; exact hs2)
    simpa using congrArg Subtype.val this
  · have : t * t = 1 := hinj (by rw [map_mul, map_one]; exact ht2)
    simpa using congrArg Subtype.val this

theorem no_perfect_centralizing_invol {J H : Subgroup G} (hJ : IsA7Bar J) (hHJ : H ≤ J)
    (hperf : ⁅H, H⁆ = H) {v : G} (hvH : v ∈ H) (hv2 : v * v = 1) (hv1 : v ≠ 1)
    (hc : ∀ h ∈ H, h * v = v * h) : False := by
  classical
  obtain ⟨e⟩ := hJ
  set ρ := rho7 J e with hρ
  have hvJ : v ∈ J := hHJ hvH
  set v' : ↥J := ⟨v, hvJ⟩ with hv'
  have hv'2 : v' * v' = 1 := Subtype.ext hv2
  have hv'1 : v' ≠ 1 := fun h => hv1 (congrArg Subtype.val h)
  have hord : orderOf v' = 2 := orderOf_eq_prime (by rw [pow_two]; exact hv'2) hv'1
  have hρv1 : ρ v' ≠ 1 := by
    intro h
    exact hv'1 (rho7_eq_one_of_two_elt J e ⟨1, by rw [hord, pow_one]⟩ h)
  have hρv2 : ρ v' * ρ v' = 1 := by rw [← map_mul, hv'2, map_one]
  have hρvA : ρ v' ∈ alternatingGroup (Fin 7) := (e _).2
  have hsq : ρ v' ^ 2 = 1 := by rw [pow_two]; exact hρv2
  have hcard : (ρ v').support.card = 4 := by
    rcases CFSG.GH74.GLS.IVK.A7.involution_cycleType (ρ v') hsq hρv1 with h | h | h
    · exfalso
      have hs := Equiv.Perm.sign_of_cycleType (ρ v')
      rw [h] at hs
      have h6 : ((-1 : ℤˣ)) ^ (Multiset.sum ({2} : Multiset ℕ) + Multiset.card ({2} : Multiset ℕ)) = -1 :=
        Odd.neg_one_pow (by decide)
      rw [h6] at hs
      have h7 := Equiv.Perm.mem_alternatingGroup.1 hρvA
      rw [hs] at h7
      exact absurd h7 (by decide)
    · have h1 := Equiv.Perm.sum_cycleType (ρ v')
      rw [h] at h1
      have h2 : Multiset.sum ({2, 2} : Multiset ℕ) = 4 := by decide
      omega
    · exfalso
      have hs := Equiv.Perm.sign_of_cycleType (ρ v')
      rw [h] at hs
      have h6 : ((-1 : ℤˣ)) ^ (Multiset.sum ({2, 2, 2} : Multiset ℕ) +
          Multiset.card ({2, 2, 2} : Multiset ℕ)) = -1 := Odd.neg_one_pow (by decide)
      rw [h6] at hs
      have h7 := Equiv.Perm.mem_alternatingGroup.1 hρvA
      rw [hs] at h7
      exact absurd h7 (by decide)
  set Hρ : Subgroup (Perm (Fin 7)) := (H.subgroupOf J).map ρ with hHρ
  have hperfρ : ⁅Hρ, Hρ⁆ = Hρ := by
    have h1 : ⁅H.subgroupOf J, H.subgroupOf J⁆ = H.subgroupOf J := by
      apply Subgroup.map_injective J.subtype_injective
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hHJ, hperf]
    rw [hHρ, ← Subgroup.map_commutator, h1]
  have hcentρ : Hρ ≤ centralizer {ρ v'} := by
    rintro _ ⟨h, hh, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hhH : (h : G) ∈ H := hh
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hc _ hhH)
  have hbot : Hρ = ⊥ := S3Sec29I.perfect_le_centralizer_even_invol Hρ hperfρ (ρ v') hcard hcentρ
  have hker : ∀ h : ↥J, (h : G) ∈ H → h ∈ pPrimeCore 2 ↥J := by
    intro h hh
    rw [← rho7_eq_one_iff J e]
    have : ρ h ∈ Hρ := ⟨h, hh, rfl⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact this
  have hvO : v' ∈ pPrimeCore 2 ↥J := hker v' hvH
  exact hv'1 (eq_one_of_mem_pPrimeCore hvO ⟨1, by rw [hord, pow_one]⟩)

end S3Sec29I1

end CFSG.GH74.Generic.BProg.B3
