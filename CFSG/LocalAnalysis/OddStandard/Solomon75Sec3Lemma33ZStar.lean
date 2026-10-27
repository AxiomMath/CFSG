module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec3Frattini
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec3Lemma51Cover
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec3Pick

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS CFSG.ComponentClassification.CatalogueBPrimeJoin

open scoped commutatorElement

variable {X : Type} [Group X] [Finite X]

theorem aux_pPrimeCoreOf_eq_inf_of_covers_le {F K : Subgroup X} (hFK : F ≤ K)
    (hcov : F ⊔ pPrimeCoreOf 2 K = K) : pPrimeCoreOf 2 F ≤ pPrimeCoreOf 2 K := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcov' : F.subgroupOf K ⊔ pPrimeCore 2 ↥K = ⊤ := (covers_subgroupOf_iff hFK).2 hcov
  let φ : ↥F →* ↥K ⧸ pPrimeCore 2 ↥K :=
    (QuotientGroup.mk' (pPrimeCore 2 ↥K)).comp (Subgroup.inclusion hFK)
  have hφ : Function.Surjective φ := by
    intro x
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    have hx : x ∈ F.subgroupOf K ⊔ pPrimeCore 2 ↥K := hcov' ▸ Subgroup.mem_top x
    obtain ⟨f, hf, o, ho, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hx
    refine ⟨⟨(f : X), hf⟩, ?_⟩
    have h1 : (QuotientGroup.mk (f * o) : ↥K ⧸ pPrimeCore 2 ↥K) = QuotientGroup.mk f := by
      rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff o).2 ho, mul_one]
    rw [h1]
    rfl
  have hker : pPrimeCore 2 ↥F ≤ φ.ker := by
    have hN : ((pPrimeCore 2 ↥F).map φ).Normal := Subgroup.Normal.map inferInstance φ hφ
    have hcard : Nat.card ((pPrimeCore 2 ↥F).map φ) ∣ Nat.card (pPrimeCore 2 ↥F) :=
      Subgroup.card_map_dvd _ _
    have hle : (pPrimeCore 2 ↥F).map φ ≤ pPrimeCore 2 (↥K ⧸ pPrimeCore 2 ↥K) :=
      le_sSup ⟨hN, Nat.Coprime.coprime_dvd_right hcard pPrimeCore_coprime_card⟩
    rw [pPrimeCore_quotient_pPrimeCore_eq_bot] at hle
    intro a ha
    have h1 : φ a ∈ (pPrimeCore 2 ↥F).map φ := ⟨a, ha, rfl⟩
    have h2 := hle h1
    rwa [Subgroup.mem_bot, ← MonoidHom.mem_ker] at h2
  rintro x ⟨a, ha, rfl⟩
  have h1 : φ a = 1 := MonoidHom.mem_ker.1 (hker ha)
  have h2 : Subgroup.inclusion hFK a ∈ pPrimeCore 2 ↥K := (QuotientGroup.eq_one_iff _).1 h1
  exact ⟨Subgroup.inclusion hFK a, h2, rfl⟩

theorem aux_pPrimeCoreOf_eq_inf_of_covers_ge {F K : Subgroup X} (hFK : F ≤ K) :
    F ⊓ pPrimeCoreOf 2 K ≤ pPrimeCoreOf 2 F := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M : Subgroup ↥F := (F ⊓ pPrimeCoreOf 2 K).subgroupOf F with hM
  have hMnormal : M.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [hM, Subgroup.mem_subgroupOf] at hn ⊢
    refine ⟨F.mul_mem (F.mul_mem g.2 hn.1) (F.inv_mem g.2), ?_⟩
    exact (Subgroup.mem_normalizer_iff.1 (mem_normalizer_pPrimeCoreOf_of_mem (hFK g.2))
      (n : X)).1 hn.2
  have hMcard : Nat.Coprime 2 (Nat.card M) := by
    have h1 : Nat.card M = Nat.card ↥(F ⊓ pPrimeCoreOf 2 K) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
    have h2 : Nat.card ↥(F ⊓ pPrimeCoreOf 2 K) ∣ Nat.card ↥(pPrimeCoreOf 2 K) :=
      Subgroup.card_dvd_of_le inf_le_right
    have h3 : Nat.card ↥(pPrimeCoreOf 2 K) = Nat.card (pPrimeCore 2 ↥K) :=
      Subgroup.card_map_of_injective K.subtype_injective
    rw [h1]
    exact Nat.Coprime.coprime_dvd_right (h3 ▸ h2) pPrimeCore_coprime_card
  have hMle : M ≤ pPrimeCore 2 ↥F := le_sSup ⟨hMnormal, hMcard⟩
  intro x hx
  have hxM : (⟨x, hx.1⟩ : ↥F) ∈ M := hx
  exact ⟨⟨x, hx.1⟩, hMle hxM, rfl⟩

omit [Finite X] in
theorem aux_pPrimeCoreOf_eq_inf_of_covers_decomp {F K : Subgroup X} (hFK : F ≤ K) {k : X}
    (hk : k ∈ F ⊔ pPrimeCoreOf 2 K) : ∃ f ∈ F, ∃ o ∈ pPrimeCoreOf 2 K, f * o = k := by
  have hle : F ≤ normalizer (pPrimeCoreOf 2 K : Set X) := fun f hf =>
    mem_normalizer_pPrimeCoreOf_of_mem (hFK hf)
  have hmem : k ∈ ((F ⊔ pPrimeCoreOf 2 K : Subgroup X) : Set X) := hk
  rw [Subgroup.coe_mul_of_left_le_normalizer_right F (pPrimeCoreOf 2 K) hle] at hmem
  exact hmem

theorem pPrimeCoreOf_eq_inf_of_covers {F K : Subgroup X} (hFK : F ≤ K)
    (hcov : F ⊔ pPrimeCoreOf 2 K = K) : pPrimeCoreOf 2 F = F ⊓ pPrimeCoreOf 2 K :=
  le_antisymm (le_inf (Subgroup.map_subtype_le _) (aux_pPrimeCoreOf_eq_inf_of_covers_le hFK hcov))
    (aux_pPrimeCoreOf_eq_inf_of_covers_ge hFK)

theorem zStar_le_zStar_of_covers {F K : Subgroup X} (hFK : F ≤ K)
    (hcov : F ⊔ pPrimeCoreOf 2 K = K) : zStar F ≤ zStar K := by
  intro w hw
  obtain ⟨hwF, -, -, hwc⟩ := hw
  have hwK : w ∈ K := hFK hwF
  refine ⟨hwK, Subgroup.le_normalizer hwK, mem_normalizer_pPrimeCoreOf_of_mem hwK,
    fun k hk => ?_⟩
  have hk' : k ∈ F ⊔ pPrimeCoreOf 2 K := hcov.ge hk
  obtain ⟨f, hf, o, ho, rfl⟩ := aux_pPrimeCoreOf_eq_inf_of_covers_decomp hFK hk'
  have hOw : ⁅o, w⁆ ∈ pPrimeCoreOf 2 K := by
    have h1 : w * o⁻¹ * w⁻¹ ∈ pPrimeCoreOf 2 K :=
      (Subgroup.mem_normalizer_iff.1 (mem_normalizer_pPrimeCoreOf_of_mem hwK) _).1
        ((pPrimeCoreOf 2 K).inv_mem ho)
    have h2 : ⁅o, w⁆ = o * (w * o⁻¹ * w⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [h2]
    exact (pPrimeCoreOf 2 K).mul_mem ho h1
  have hfN : f ∈ normalizer (pPrimeCoreOf 2 K : Set X) :=
    mem_normalizer_pPrimeCoreOf_of_mem (hFK hf)
  have hFw : ⁅f, w⁆ ∈ pPrimeCoreOf 2 K :=
    (pPrimeCoreOf_eq_inf_of_covers hFK hcov ▸ hwc f hf : ⁅f, w⁆ ∈ F ⊓ pPrimeCoreOf 2 K).2
  have hid : ⁅f * o, w⁆ = f * ⁅o, w⁆ * f⁻¹ * ⁅f, w⁆ := by
    simp only [commutatorElement_def]
    group
  rw [hid]
  exact (pPrimeCoreOf 2 K).mul_mem ((Subgroup.mem_normalizer_iff.1 hfN _).1 hOw) hFw

theorem zStar_le_sup_of_covers {F K : Subgroup X} (hFK : F ≤ K)
    (hcov : F ⊔ pPrimeCoreOf 2 K = K) : zStar K ≤ pPrimeCoreOf 2 K ⊔ zStar F := by
  intro w hw
  obtain ⟨hwK, -, hwO, hwc⟩ := hw
  have hw' : w ∈ F ⊔ pPrimeCoreOf 2 K := hcov.ge hwK
  obtain ⟨f, hf, o, ho, hfo⟩ := aux_pPrimeCoreOf_eq_inf_of_covers_decomp hFK hw'
  have hfw : f = w * o⁻¹ := eq_mul_inv_iff_mul_eq.2 hfo
  have hfz : f ∈ zStar F := by
    refine ⟨hf, Subgroup.le_normalizer hf, mem_normalizer_pPrimeCoreOf_of_mem hf,
      fun x hx => ?_⟩
    rw [pPrimeCoreOf_eq_inf_of_covers hFK hcov]
    refine ⟨F.mul_mem (F.mul_mem (F.mul_mem hx hf) (F.inv_mem hx)) (F.inv_mem hf), ?_⟩
    have hxK : x ∈ K := hFK hx
    have hxw : ⁅x, w⁆ ∈ pPrimeCoreOf 2 K := hwc x hxK
    have hxo : ⁅x, o⁻¹⁆ ∈ pPrimeCoreOf 2 K := by
      have h1 : x * o⁻¹ * x⁻¹ ∈ pPrimeCoreOf 2 K :=
        (Subgroup.mem_normalizer_iff.1 (mem_normalizer_pPrimeCoreOf_of_mem hxK) _).1
          ((pPrimeCoreOf 2 K).inv_mem ho)
      have h2 : ⁅x, o⁻¹⁆ = (x * o⁻¹ * x⁻¹) * o := by
        simp only [commutatorElement_def]
        group
      rw [h2]
      exact (pPrimeCoreOf 2 K).mul_mem h1 ho
    have hconj : w * ⁅x, o⁻¹⁆ * w⁻¹ ∈ pPrimeCoreOf 2 K :=
      (Subgroup.mem_normalizer_iff.1 hwO _).1 hxo
    have hid : ⁅x, f⁆ = ⁅x, w⁆ * (w * ⁅x, o⁻¹⁆ * w⁻¹) := by
      rw [hfw]
      simp only [commutatorElement_def]
      group
    rw [hid]
    exact (pPrimeCoreOf 2 K).mul_mem hxw hconj
  rw [← hfo]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hfz) (Subgroup.mem_sup_left ho)

omit [Finite X] in
theorem aux_relIndex_zStar_eq_of_covers_pPrimeCoreOf_le_zStar (K : Subgroup X) :
    pPrimeCoreOf 2 K ≤ zStar K := by
  intro o ho
  have hoK : o ∈ K := by
    obtain ⟨w, -, rfl⟩ := ho
    exact w.2
  refine ⟨hoK, Subgroup.le_normalizer hoK, mem_normalizer_pPrimeCoreOf_of_mem hoK,
    fun k hk => ?_⟩
  have h1 : k * o * k⁻¹ ∈ pPrimeCoreOf 2 K :=
    (Subgroup.mem_normalizer_iff.1 (mem_normalizer_pPrimeCoreOf_of_mem hk) o).1 ho
  rw [commutatorElement_def]
  exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ ho)

theorem relIndex_zStar_eq_of_covers {F K : Subgroup X} (hFK : F ≤ K)
    (hcov : F ⊔ pPrimeCoreOf 2 K = K) :
    (pPrimeCoreOf 2 K).relIndex (zStar K) = (pPrimeCoreOf 2 F).relIndex (zStar F) := by
  have hBA : zStar F ≤ zStar K := zStar_le_zStar_of_covers hFK hcov
  have hOA : pPrimeCoreOf 2 K ≤ zStar K :=
    aux_relIndex_zStar_eq_of_covers_pPrimeCoreOf_le_zStar K
  have hOFB : pPrimeCoreOf 2 F ≤ zStar F :=
    aux_relIndex_zStar_eq_of_covers_pPrimeCoreOf_le_zStar F
  have hAcov : zStar K ≤ pPrimeCoreOf 2 K ⊔ zStar F := zStar_le_sup_of_covers hFK hcov
  have hOF : pPrimeCoreOf 2 F = F ⊓ pPrimeCoreOf 2 K := pPrimeCoreOf_eq_inf_of_covers hFK hcov
  have hBF : zStar F ≤ F := inf_le_left
  have hAK : zStar K ≤ K := inf_le_left
  have hinf : pPrimeCoreOf 2 K ⊓ zStar F = pPrimeCoreOf 2 F := by
    refine le_antisymm ?_ (le_inf (hOF ▸ inf_le_right) hOFB)
    rw [hOF]
    exact le_inf (inf_le_right.trans hBF) inf_le_left
  have hnorm : ((pPrimeCoreOf 2 K).subgroupOf (zStar K)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hOA).2
      (fun a ha => mem_normalizer_pPrimeCoreOf_of_mem (hAK ha))
  have h1 := Subgroup.relIndex_sup_right ((zStar F).subgroupOf (zStar K))
    ((pPrimeCoreOf 2 K).subgroupOf (zStar K))
  have htop : (zStar F).subgroupOf (zStar K) ⊔ (pPrimeCoreOf 2 K).subgroupOf (zStar K) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hBA hOA, Subgroup.subgroupOf_eq_top, sup_comm]
    exact hAcov
  rw [htop, Subgroup.relIndex_top_right, Subgroup.relIndex_subgroupOf hBA] at h1
  calc (pPrimeCoreOf 2 K).relIndex (zStar K) = (pPrimeCoreOf 2 K).relIndex (zStar F) := h1
    _ = (pPrimeCoreOf 2 K ⊓ zStar F).relIndex (zStar F) := (Subgroup.inf_relIndex_right _ _).symm
    _ = (pPrimeCoreOf 2 F).relIndex (zStar F) := by rw [hinf]

omit [Finite X] in
theorem pPrimeCoreOf_le_zStar (K : Subgroup X) : pPrimeCoreOf 2 K ≤ zStar K := by
  intro o ho
  have hoK : o ∈ K := by
    obtain ⟨w, -, rfl⟩ := ho
    exact w.2
  refine ⟨hoK, Subgroup.le_normalizer hoK, mem_normalizer_pPrimeCoreOf_of_mem hoK,
    fun k hk => ?_⟩
  have h1 : k * o * k⁻¹ ∈ pPrimeCoreOf 2 K :=
    (Subgroup.mem_normalizer_iff.1 (mem_normalizer_pPrimeCoreOf_of_mem hk) o).1 ho
  rw [commutatorElement_def]
  exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ ho)

theorem aux_card_eq_relIndex_of_isSylowTwoIn_odd (K : Subgroup X) :
    Odd (Nat.card (pPrimeCoreOf 2 K)) := by
  have h1 : Nat.card (pPrimeCoreOf 2 K) = Nat.card (pPrimeCore 2 ↥K) :=
    Subgroup.card_map_of_injective K.subtype_injective
  rw [h1]
  exact Nat.coprime_two_left.1 pPrimeCore_coprime_card

omit [Finite X] in
theorem aux_card_eq_relIndex_of_isSylowTwoIn_mul {H A : Subgroup X} (h : H ≤ A) :
    H.relIndex A * Nat.card H = Nat.card A := by
  have := Subgroup.relIndex_mul_card H A
  rwa [inf_eq_left.2 h] at this

theorem aux_card_eq_relIndex_of_isSylowTwoIn_pow_eq {m m' a e : ℕ} (hm : Odd m) (hm' : Odd m')
    (h : m * 2 ^ e = 2 ^ a * m') : a = e := by
  have h1 : 2 ^ e ∣ 2 ^ a * m' := ⟨m, by rw [← h]; ring⟩
  have h2 : 2 ^ a ∣ m * 2 ^ e := ⟨m', h⟩
  have hc1 : Nat.Coprime (2 ^ e) m' := Nat.Coprime.pow_left e (Nat.coprime_two_left.2 hm')
  have hc2 : Nat.Coprime (2 ^ a) m := Nat.Coprime.pow_left a (Nat.coprime_two_left.2 hm)
  have h3 : 2 ^ e ∣ 2 ^ a := hc1.dvd_of_dvd_mul_right h1
  have h4 : 2 ^ a ∣ 2 ^ e := hc2.dvd_of_dvd_mul_left h2
  exact le_antisymm ((Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 h4)
    ((Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 h3)

theorem card_eq_relIndex_of_isSylowTwoIn {K Z : Subgroup X} (hZ : IsSylowTwoIn (zStar K) Z) :
    Nat.card Z = (pPrimeCoreOf 2 K).relIndex (zStar K) := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hZA, hZp, hZidx⟩ := hZ
  have hOA : pPrimeCoreOf 2 K ≤ zStar K := pPrimeCoreOf_le_zStar K
  have hA1 := aux_card_eq_relIndex_of_isSylowTwoIn_mul hOA
  have hA2 := aux_card_eq_relIndex_of_isSylowTwoIn_mul hZA
  have hOodd : Odd (Nat.card (pPrimeCoreOf 2 K)) := aux_card_eq_relIndex_of_isSylowTwoIn_odd K
  have hZodd : Odd (Z.relIndex (zStar K)) := Nat.odd_iff.2 (by omega)
  obtain ⟨e, he⟩ := exists_relIndex_zStar_eq_two_pow K
  obtain ⟨a, ha⟩ := hZp.exists_card_eq
  rw [he, mul_comm] at hA1
  rw [ha, mul_comm] at hA2
  have hae : a = e :=
    aux_card_eq_relIndex_of_isSylowTwoIn_pow_eq hOodd hZodd (hA1.trans hA2.symm)
  rw [ha, he, hae]

theorem aux_isSylowTwoIn_zStar_of_card_eq_odd (K : Subgroup X) :
    Odd (Nat.card (pPrimeCoreOf 2 K)) := by
  have h1 : Nat.card (pPrimeCoreOf 2 K) = Nat.card (pPrimeCore 2 ↥K) :=
    Subgroup.card_map_of_injective K.subtype_injective
  rw [h1]
  exact Nat.coprime_two_left.1 pPrimeCore_coprime_card

omit [Finite X] in
theorem aux_isSylowTwoIn_zStar_of_card_eq_mul {H A : Subgroup X} (h : H ≤ A) :
    H.relIndex A * Nat.card H = Nat.card A := by
  have := Subgroup.relIndex_mul_card H A
  rwa [inf_eq_left.2 h] at this

theorem isSylowTwoIn_zStar_of_card_eq {K Z : Subgroup X} (hZK : Z ≤ zStar K)
    (hZ : IsPGroup 2 ↥Z) (hcard : Nat.card Z = (pPrimeCoreOf 2 K).relIndex (zStar K)) :
    IsSylowTwoIn (zStar K) Z := by
  refine ⟨hZK, hZ, ?_⟩
  have hOA : pPrimeCoreOf 2 K ≤ zStar K := pPrimeCoreOf_le_zStar K
  have hA1 := aux_isSylowTwoIn_zStar_of_card_eq_mul hOA
  have hA2 := aux_isSylowTwoIn_zStar_of_card_eq_mul hZK
  have hOodd : Odd (Nat.card (pPrimeCoreOf 2 K)) := aux_isSylowTwoIn_zStar_of_card_eq_odd K
  have hpos : 0 < Nat.card Z := Nat.card_pos
  rw [← hcard] at hA1
  have heq : Z.relIndex (zStar K) = Nat.card (pPrimeCoreOf 2 K) :=
    Nat.eq_of_mul_eq_mul_right hpos (hA2.trans (hA1.symm.trans (mul_comm _ _)))
  rw [heq]
  have := Nat.odd_iff.1 hOodd
  omega

end CFSG.OddStandard.Solomon75
