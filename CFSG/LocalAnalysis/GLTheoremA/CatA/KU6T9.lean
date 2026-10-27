module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.KU6Facts
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsAlpha
public import CFSG.LocalAnalysis.GLTheoremA.S3.ChevTools

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.HardMathSupport.Solomon.Coordinator

namespace KU6T9

theorem catalogIs_of_mulEquiv {S T : Type} [Group S] [Group T] {Q : TauCeti.CFSGIndex → Prop}
    (h : catalogIs T Q) (e : S ≃* T) : catalogIs S Q := by
  obtain ⟨i, hi, ⟨f⟩⟩ := h
  exact ⟨i, hi, ⟨e.trans f⟩⟩

variable {G : Type} [Group G] [Finite G]

theorem chevTransfer_ne_bot {K T : Subgroup G} (hTK : T ≤ K) (hT : IsPGroup 2 T)
    (hnot : ¬ T ≤ GLAPPrimeCoreOf 3 K) : chevTransfer 3 K T ≠ ⊥ := by
  intro hbot
  apply hnot
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hTK' : IsPGroup 2 (T.subgroupOf K) := hT.of_equiv (Subgroup.subgroupOfEquivOfLe hTK).symm
  have hYc : (T.subgroupOf K).map (pQuotHom 3 K) ≤ Subgroup.center (PQuot 3 K) := by
    rintro _ ⟨t, ht, rfl⟩
    have h1 : chevQuotHom 3 K t ∈ (⊥ : Subgroup (PSimple 3 K)) := by
      rw [← hbot]
      exact Subgroup.mem_map_of_mem _ ht
    rw [Subgroup.mem_bot] at h1
    exact (QuotientGroup.eq_one_iff _).1 h1
  have hYn : ((T.subgroupOf K).map (pQuotHom 3 K)).Normal := ⟨fun n hn g => by
    have hz := Subgroup.mem_center_iff.1 (hYc hn) g
    have key : g * n * g⁻¹ = n := by rw [hz, mul_assoc, mul_inv_cancel, mul_one]
    rw [key]
    exact hn⟩
  have hYp : IsPGroup 2 ((T.subgroupOf K).map (pQuotHom 3 K)) := hTK'.map _
  have hYcop : Nat.Coprime 3 (Nat.card ↥((T.subgroupOf K).map (pQuotHom 3 K))) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hYp
    rw [hn]
    exact Nat.Coprime.pow_right _ (by norm_num)
  have hYle : (T.subgroupOf K).map (pQuotHom 3 K) ≤ CFSG.pPrimeCore 3 (PQuot 3 K) :=
    le_sSup (show (T.subgroupOf K).map (pQuotHom 3 K) ∈
      {N : Subgroup (PQuot 3 K) | N.Normal ∧ Nat.Coprime 3 (Nat.card N)} from ⟨hYn, hYcop⟩)
  have hker : ¬ 3 ∣ Nat.card (pQuotHom 3 K).ker := by
    rw [ker_pQuotHom]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 CFSG.pPrimeCore_coprime_card
  have hcomap := (CFSG.prime_complement_kernel_core_preimage (pQuotHom 3 K)
    (pQuotHom_surjective 3 K) hker).1
  intro t ht
  have htK : t ∈ K := hTK ht
  have hmem : (⟨t, htK⟩ : ↥K) ∈ (CFSG.pPrimeCore 3 (PQuot 3 K)).comap (pQuotHom 3 K) :=
    hYle (Subgroup.mem_map_of_mem _ (show (⟨t, htK⟩ : ↥K) ∈ T.subgroupOf K from ht))
  rw [hcomap] at hmem
  exact (chev_mem_glaPPrimeCoreOf_iff htK).2 hmem

end KU6T9

open KU6T9 in
theorem u62t9_of_facts (hF : KU6FixCompFact) (G : Type) [Group G] [Finite G] : U62Type9At G := by
  intro X K A T hX hK hA hA3 hAN hfaith _hInn hTK hTp hTnot hAT a ha ha1 M hM
  have hp : Nat.Prime 3 := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  let AN : Subgroup ↥(Subgroup.normalizer (K : Set G)) :=
    A.subgroupOf (Subgroup.normalizer (K : Set G))
  let ψA : ↥AN →* MulAut (PSimple 3 K) := (chevAut 3 K).comp AN.subtype
  have hinj : Function.Injective ψA := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : chevAut 3 K ((x : ↥(Subgroup.normalizer (K : Set G)))) = 1 := hx
    have hxA : ((x : ↥(Subgroup.normalizer (K : Set G))) : G) ∈ A := x.2
    by_contra hne
    have hx1 : ((x : ↥(Subgroup.normalizer (K : Set G))) : G) ≠ 1 := by
      intro h
      apply hne
      apply Subtype.ext
      exact Subtype.ext h
    exact hfaith _ hxA hx1 ((chevAut_eq_one_iff hp hX _).1 h1)
  let A' : Subgroup (MulAut (PSimple 3 K)) := ψA.range
  have hcomm : ∀ x y : ↥AN, x * y = y * x := by
    intro x y
    apply Subtype.ext
    apply Subtype.ext
    have hc := hA.1.is_comm.comm (⟨((x : ↥(Subgroup.normalizer (K : Set G))) : G), x.2⟩ : ↥A)
      ⟨((y : ↥(Subgroup.normalizer (K : Set G))) : G), y.2⟩
    have h2 := congrArg Subtype.val hc
    simpa using h2
  have hA'el : IsElemAbelian 3 A' := by
    refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨a', ha'⟩ := ψA.mem_range.1 x.2
      obtain ⟨b', hb'⟩ := ψA.mem_range.1 y.2
      apply Subtype.ext
      show (x : MulAut (PSimple 3 K)) * (y : MulAut (PSimple 3 K)) =
        (y : MulAut (PSimple 3 K)) * (x : MulAut (PSimple 3 K))
      rw [← ha', ← hb', ← map_mul, ← map_mul, hcomm a' b']
    · obtain ⟨a', ha'⟩ := ψA.mem_range.1 hx
      have h3 : ((a' : ↥(Subgroup.normalizer (K : Set G))) : G) ^ 3 = 1 := hA.2 _ a'.2
      have h4 : a' ^ 3 = 1 := by
        apply Subtype.ext
        apply Subtype.ext
        simpa using h3
      rw [← ha', ← map_pow, h4, map_one]
  have hA'card : Nat.card A' = Nat.card A := by
    rw [Nat.card_congr (MonoidHom.ofInjective hinj).symm.toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAN).toEquiv
  have hTK' : IsPGroup 2 ↥(T.subgroupOf K) := hTp.of_equiv (Subgroup.subgroupOfEquivOfLe hTK).symm
  have hTbp : IsPGroup 2 (chevTransfer 3 K T) := IsPGroup.map hTK' (chevQuotHom 3 K)
  have hTbne : chevTransfer 3 K T ≠ ⊥ := chevTransfer_ne_bot hTK hTp hTnot
  have hTbnorm : ∀ α ∈ A', ∀ x ∈ chevTransfer 3 K T, α x ∈ chevTransfer 3 K T := by
    intro α hα x hx
    obtain ⟨y, rfl⟩ := ψA.mem_range.1 hα
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 hx
    have hyN : ((y : ↥(Subgroup.normalizer (K : Set G))) : G) ∈ Subgroup.normalizer (T : Set G) :=
      hAT y.2
    have htT : ((K.normalizerMonoidHom y t : ↥K) : G) ∈ T := by
      rw [chev_coe_normalizerMonoidHom]
      have := (Subgroup.mem_normalizer_iff.1 hyN ((t : K) : G)).1 ht
      exact this
    show chevAut 3 K ((y : ↥(Subgroup.normalizer (K : Set G)))) (chevQuotHom 3 K t) ∈
      chevTransfer 3 K T
    rw [chevAut_chevQuotHom]
    exact Subgroup.mem_map_of_mem _ (show K.normalizerMonoidHom y t ∈ T.subgroupOf K from htT)
  have hap : IsPGroup 3 (Subgroup.zpowers a) := by
    have h3 : a ^ 3 = 1 := hA.2 a ha
    have hd : orderOf a ∣ 3 ^ 1 := by simpa using orderOf_dvd_of_pow_eq_one h3
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hd
    exact IsPGroup.iff_card.2 ⟨k, by rw [Nat.card_zpowers, hk]⟩
  have haN : a ∈ Subgroup.normalizer (K : Set G) := hAN ha
  have hN3 := glaPComponent_chevTransfer hp haN hap hM
  have hα_mem : chevAut 3 K ⟨a, haN⟩ ∈ A' := ⟨⟨⟨a, haN⟩, ha⟩, rfl⟩
  have hα_ne : chevAut 3 K ⟨a, haN⟩ ≠ 1 := by
    intro h
    exact hfaith a ha ha1 ((chevAut_eq_one_iff hp hX haN).1 h)
  have hF' := hF (PSimple 3 K) hK A' (chevTransfer 3 K T) hA'el (by rw [hA'card]; exact hA3)
    hTbp hTbne hTbnorm _ hα_mem hα_ne (chevTransfer 3 K M) hN3
  obtain ⟨e⟩ := nonempty_pSimple_equiv_chevTransfer hp haN hap hM
  exact catalogIs_of_mulEquiv hF' e

end CFSG.LocalAnalysis.GLTheoremA
