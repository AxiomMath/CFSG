module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSigUniq

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup
open scoped commutatorElement

variable {X : Type} [Group X]

theorem two_dvd_card_of_isPComponent_in [Finite X] {Y K : Subgroup X} (hKY : K ≤ Y)
    (hKpc : IsPComponent 2 (K.subgroupOf Y)) : 2 ∣ Nat.card K := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKq := ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 K Y hKY).mp hKpc).2.2
  by_contra h2
  have hcop : Nat.Coprime 2 (Nat.card K) := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h2
  have hKO : K ≤ (pPrimeCore 2 ↥K).map K.subtype := le_pPrimeCore_map le_rfl le_normalizer hcop
  have htriv : ∀ q : ↥K ⧸ pPrimeCore 2 ↥K, q = 1 := by
    intro q
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨k', hk', hkk'⟩ := hKO k.2
    rw [QuotientGroup.eq_one_iff]
    have : k' = k := Subtype.ext hkk'
    rwa [← this]
  obtain ⟨a, b, hab⟩ := hKq.2.2
  obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
  rw [htriv a', htriv b'] at hab
  exact hab rfl

namespace Sig36

variable [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X} {n : ℕ}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)} {E : Subgroup X} {D : Finset (Fin n)}
  (S : Sig36 X t J n e E D)
include S

theorem mem_coreActionKernel_of_centralizer_swap
    (hCH : centralizer ({t} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    {M : Subgroup X} (hMH : M ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hMpc : IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))))
    (hJM : J ≤ M ⊔ M.map (MulAut.conj t).toMonoidHom) {u : X}
    (hut : u ∈ centralizer ({t} : Set X)) (huK : u ∈ UnbalancedLayer.coreActionKernel M)
    (huKt : u ∈ UnbalancedLayer.coreActionKernel (M.map (MulAut.conj t).toMonoidHom)) :
    u ∈ UnbalancedLayer.coreActionKernel J := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := normalizer (Sol78.signalizerCompletion E E : Set X) with hHdef
  set Mt := M.map (MulAut.conj t).toMonoidHom with hMtdef
  have htH : t ∈ H := hCH (mem_centralizer_singleton_iff.mpr rfl)
  obtain ⟨hMtH, hMtpc⟩ := isPComponent_conj hMH hMpc htH
  set OH := (pPrimeCore 2 ↥H).map H.subtype with hOHdef
  have hOHodd : Nat.Coprime 2 (Nat.card OH) := by
    rw [hOHdef, card_map_of_injective H.subtype_injective]
    exact pPrimeCore_coprime_card
  have hMO : (pPrimeCore 2 ↥M).map M.subtype ≤ OH := pPrimeCore_le_of_isPComponent hMH hMpc
  have hMtO : (pPrimeCore 2 ↥Mt).map Mt.subtype ≤ OH := pPrimeCore_le_of_isPComponent hMtH hMtpc
  have hJH : J ≤ H := hJM.trans (sup_le hMH hMtH)
  have key : ∀ v ∈ H, v ∈ UnbalancedLayer.coreActionKernel M →
      v ∈ UnbalancedLayer.coreActionKernel Mt → ∀ j ∈ J, j⁻¹ * v⁻¹ * j * v ∈ OH := by
    intro v hvH hvK hvKt
    set π := QuotientGroup.mk' (pPrimeCore 2 ↥H) with hπdef
    set Cv := (centralizer ({π ⟨v, hvH⟩} : Set (↥H ⧸ pPrimeCore 2 ↥H))).comap π with hCvdef
    have hmem : ∀ m (hm : m ∈ H), m⁻¹ * v⁻¹ * m * v ∈ OH → (⟨m, hm⟩ : ↥H) ∈ Cv := by
      intro m hm hc
      rw [hCvdef, mem_comap, mem_centralizer_singleton_iff]
      obtain ⟨o, ho, hoeq⟩ := hc
      have h1 : π (⟨m, hm⟩⁻¹ * ⟨v, hvH⟩⁻¹ * ⟨m, hm⟩ * ⟨v, hvH⟩) = 1 := by
        rw [hπdef, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        have : (⟨m, hm⟩⁻¹ * ⟨v, hvH⟩⁻¹ * ⟨m, hm⟩ * ⟨v, hvH⟩ : ↥H) = o := Subtype.ext hoeq.symm
        rw [this]
        exact ho
      rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
      calc π ⟨m, hm⟩ * π ⟨v, hvH⟩ = π ⟨v, hvH⟩ * π ⟨m, hm⟩ *
          ((π ⟨m, hm⟩)⁻¹ * (π ⟨v, hvH⟩)⁻¹ * π ⟨m, hm⟩ * π ⟨v, hvH⟩) := by group
        _ = π ⟨v, hvH⟩ * π ⟨m, hm⟩ := by rw [h1, mul_one]
    have hMC : M.subgroupOf H ≤ Cv := fun m hm =>
      hmem m m.2 (hMO (UnbalancedLayer.mem_coreActionKernel.mp hvK |>.2 m hm))
    have hMtC : Mt.subgroupOf H ≤ Cv := fun m hm =>
      hmem m m.2 (hMtO (UnbalancedLayer.mem_coreActionKernel.mp hvKt |>.2 m hm))
    have hJC : J.subgroupOf H ≤ Cv := by
      have h1 : J.subgroupOf H ≤ (M ⊔ Mt).subgroupOf H := fun x hx => hJM hx
      refine h1.trans ?_
      rw [subgroupOf_sup hMH hMtH]
      exact sup_le hMC hMtC
    intro j hj
    have hjC := hJC (show (⟨j, hJH hj⟩ : ↥H) ∈ J.subgroupOf H from hj)
    rw [hCvdef, mem_comap, mem_centralizer_singleton_iff] at hjC
    have h2 : π (⟨j, hJH hj⟩⁻¹ * ⟨v, hvH⟩⁻¹ * ⟨j, hJH hj⟩ * ⟨v, hvH⟩) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv]
      calc (π ⟨j, hJH hj⟩)⁻¹ * (π ⟨v, hvH⟩)⁻¹ * π ⟨j, hJH hj⟩ * π ⟨v, hvH⟩ =
          (π ⟨j, hJH hj⟩)⁻¹ * (π ⟨v, hvH⟩)⁻¹ * (π ⟨j, hJH hj⟩ * π ⟨v, hvH⟩) := by group
        _ = 1 := by rw [hjC]; group
    rw [hπdef, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
    exact ⟨_, h2, rfl⟩
  have huH : u ∈ H := hCH hut
  have hkey := key u huH huK huKt
  have hkey' := key u⁻¹ (inv_mem huH) (inv_mem huK) (inv_mem huKt)
  set OC := (pPrimeCore 2 ↥(centralizer ({t} : Set X))).map (centralizer ({t} : Set X)).subtype
    with hOCdef
  have hOHC : OH ⊓ centralizer ({t} : Set X) ≤ OC := by
    refine le_pPrimeCore_map inf_le_right (fun c hc => inf_normalizer_le_normalizer_inf
      ⟨le_normalizer_pPrimeCore (le_normalizer (hCH hc)), le_normalizer hc⟩) ?_
    exact Nat.Coprime.coprime_dvd_right (card_dvd_of_le inf_le_left) hOHodd
  have hJO : (pPrimeCore 2 ↥J).map J.subtype ≤ OC :=
    pPrimeCore_le_of_isPComponent S.pair.1.2.1 S.pair.1.2.2.1
  have hJN : J.map (MulAut.conj u).toMonoidHom = J := by
    by_contra hJu
    set Jt := J.map (MulAut.conj u).toMonoidHom with hJtdef
    obtain ⟨hJtC, hJtpc⟩ := isPComponent_conj S.pair.1.2.1 S.pair.1.2.2.1 hut
    have hJtK : Jt ≤ UnbalancedLayer.coreActionKernel J :=
      GSThmB.B5a.le_coreActionKernel_of_ne S.pair.1.2.1 hJtC S.pair.1.2.2.1 hJtpc (Ne.symm hJu)
    have hOCn : ∀ z ∈ centralizer ({t} : Set X), ∀ w ∈ OC, z * w * z⁻¹ ∈ OC :=
      fun z hz w hw => (mem_normalizer_iff.mp (le_normalizer_pPrimeCore (le_normalizer hz)) w).mp hw
    have hcomm : ∀ x ∈ Jt, ∀ x' ∈ Jt, ⁅x, x'⁆ ∈ OC := by
      intro x hx x' hx'
      obtain ⟨j, hj, rfl⟩ := hx'
      have hxt : x ∈ centralizer ({t} : Set X) := hJtC hx
      have hjt : j ∈ centralizer ({t} : Set X) := S.pair.1.2.1 hj
      have hcO : j⁻¹ * u * j * u⁻¹ ∈ OC := by
        refine hOHC (mem_inf.mpr ⟨?_, ?_⟩)
        · have := hkey' j hj
          rwa [inv_inv] at this
        · exact mul_mem (mul_mem (mul_mem (inv_mem hjt) hut) hjt) (inv_mem hut)
      have hjx : j⁻¹ * x⁻¹ * j * x ∈ OC :=
        hJO ((UnbalancedLayer.mem_coreActionKernel.mp (hJtK hx)).2 j hj)
      have hid : ⁅x, (MulAut.conj u).toMonoidHom j⁆ =
          (x * j) * (j⁻¹ * x⁻¹ * j * x)⁻¹ * (x * j)⁻¹ *
            (j * (x * (j⁻¹ * u * j * u⁻¹) * x⁻¹ * (j⁻¹ * u * j * u⁻¹)⁻¹) * j⁻¹) := by
        change x * (u * j * u⁻¹) * x⁻¹ * (u * j * u⁻¹)⁻¹ = _
        group
      rw [hid]
      exact mul_mem (hOCn _ (mul_mem hxt hjt) _ (inv_mem hjx))
        (hOCn _ hjt _ (mul_mem (hOCn _ hxt _ hcO) (inv_mem hcO)))
    have hJtperf : ⁅Jt, Jt⁆ = Jt := by
      rw [hJtdef, ← map_commutator, UnbalancedCorr.commutator_eq_of_isPComponent
        S.pair.1.2.1 S.pair.1.2.2.1]
    have hJtO : Jt ≤ OC := by
      rw [← hJtperf, commutator_le]
      exact hcomm
    have h1 : Nat.card Jt ∣ Nat.card OC := card_dvd_of_le hJtO
    have h2 : Nat.card Jt = Nat.card J := card_map_of_injective (MulAut.conj u).injective
    have h3 := two_dvd_card_of_isPComponent_in S.pair.1.2.1 S.pair.1.2.2.1
    have h4 : Nat.Coprime 2 (Nat.card OC) := by
      rw [hOCdef, card_map_of_injective (centralizer ({t} : Set X)).subtype_injective]
      exact pPrimeCore_coprime_card
    rw [h2] at h1
    exact absurd (Nat.Coprime.coprime_dvd_right h1 h4) (by
      rw [Nat.coprime_two_left]
      exact Nat.not_odd_iff_even.mpr (even_iff_two_dvd.mpr h3))
  have huJ : u ∈ normalizer (J : Set X) := mem_normalizer_iff_map_conj_eq.mpr hJN
  refine ⟨huJ, fun j hj => ?_⟩
  have hjJ : j⁻¹ * u⁻¹ * j * u ∈ J := by
    have h1 : u⁻¹ * j * u⁻¹⁻¹ ∈ J := (mem_normalizer_iff.mp (inv_mem huJ) j).mp hj
    rw [inv_inv] at h1
    have h2 := mul_mem (inv_mem hj) h1
    rwa [show j⁻¹ * (u⁻¹ * j * u) = j⁻¹ * u⁻¹ * j * u by group] at h2
  refine le_pPrimeCore_map inf_le_right (fun y hy => inf_normalizer_le_normalizer_inf
    ⟨le_normalizer_pPrimeCore (le_normalizer (hJH hy)), le_normalizer hy⟩) ?_ ⟨hkey j hj, hjJ⟩
  exact Nat.Coprime.coprime_dvd_right (card_dvd_of_le inf_le_left) hOHodd

end Sig36

end CFSG.ComponentClassification.SolMax
