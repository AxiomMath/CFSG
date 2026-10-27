module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.MultA1
public import CFSG.LocalAnalysis.GLTheoremA.CatB.MultA2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FRField

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.MultA3

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.MI
open CFSG.LocalAnalysis.GLTheoremA.CatB.MultA1 CFSG.LocalAnalysis.GLTheoremA.CatB.MultA2

@[expose] def MultAG2Residual (G : Type) [Group G] [Finite G] : Prop :=
  (∀ (X L : Subgroup G) (b : G) (n : ℕ), GLAPComponent 3 X L → CFSG.Open.IsQuasisimple ↥L → b ^ 3 = 1 →
      IsTD4 3 L → NonInner 3 b L → GLAPComponent 3 (L ⊓ cx b) (Ipart 3 L b) →
      catalogIs (PSimple 3 (Ipart 3 L b)) (S10.isG2n n) → IsChevSimple 2 (PSimple 3 L)) ∧
  (∀ (X L : Subgroup G) (b : G) (n : ℕ), GLAPComponent 3 X L → CFSG.Open.IsQuasisimple ↥L → b ^ 3 = 1 →
      R2Prop 3 b L → GLAPComponent 3 (L ⊓ cx b) (Ipart 3 L b) →
      catalogIs (PSimple 3 (Ipart 3 L b)) (S10.isG2n n) → n = 2 → Ipart 3 L b ⊓ GLAPPrimeCoreOf 3 L = ⊥)

section Holds


variable {G : Type} [Group G] [Finite G]



theorem image_simple_of_core {L : Subgroup G} {b : G} (hb : b ∈ Subgroup.normalizer (L : Set G))
    (hbp : b ^ 3 = 1) (hI : Ipart 3 L b ≠ ⊥)
    (hcore : FR.CoreSub (FP.fixSub (indAut 3 L b hb))) :
    ∃ E : Subgroup (PSimple 3 L), IsSimpleGroup ↥E ∧ chevTransfer 3 L (Ipart 3 L b) = E := by
  rw [FR.fixSub_indAut hb] at hcore
  obtain ⟨E, hEC, hE, -, hperf, -, -⟩ := hcore
  obtain ⟨J₀, -, hIeq, hTE⟩ := FR.ipart_single Nat.prime_three hb hbp hE hEC hperf hI
  exact ⟨E, hE, by rw [hIeq]; exact hTE⟩

theorem image_simple_fieldOn {L : Subgroup G} {b : G} (hSmall : FR.SmallDatum) (hTwF4 : FR.TwF4Core 3)
    (hF : FieldOn 3 b L) (hbp : b ^ 3 = 1) (hI : Ipart 3 L b ≠ ⊥) :
    ∃ E : Subgroup (PSimple 3 L), IsSimpleGroup ↥E ∧ chevTransfer 3 L (Ipart 3 L b) = E :=
  image_simple_of_core hF.1 hbp hI
    (FR.coreSub_of_fieldOn Nat.prime_three (by norm_num) hSmall hTwF4 hF
      (FR.exists_perfect_of_ipart Nat.prime_three hF.1 hbp hI))

theorem image_simple_td4 (hTD4 : FR.TD4Core) {X L : Subgroup G} {b : G} (hX : GLAPComponent 3 X L)
    (hchev : IsChevSimple 2 (PSimple 3 L)) (hT : IsTD4 3 L) (hNI : NonInner 3 b L) (hbp : b ^ 3 = 1)
    (hI : Ipart 3 L b ≠ ⊥) :
    ∃ E : Subgroup (PSimple 3 L), IsSimpleGroup ↥E ∧ chevTransfer 3 L (Ipart 3 L b) = E :=
  image_simple_of_core hNI.1 hbp hI
    (hTD4 X L b hNI.1 hX hchev hbp hT hNI
      (FR.exists_perfect_of_ipart Nat.prime_three hNI.1 hbp hI))

theorem coprime_orderOf_of_core {H : Type} [Group H] [Finite H] {r : H} (hr : r ∈ GLAPPrimeCore 3 H) :
    Nat.Coprime 3 (orderOf r) := by
  have hcop : Nat.Coprime 3 (Nat.card (GLAPPrimeCore 3 H)) :=
    CFSG.pPrimeCore_coprime_card (p := 3) (G := H)
  have hd : orderOf (⟨r, hr⟩ : GLAPPrimeCore 3 H) ∣ Nat.card (GLAPPrimeCore 3 H) :=
    orderOf_dvd_natCard _
  rw [← Subgroup.orderOf_mk r hr]
  exact Nat.Coprime.coprime_dvd_right hd hcop

theorem layer_wrapper (hGA : CFSG.Open.GriessAllModelsStatement) {X L I C : Subgroup G} {n : ℕ}
    (hL : GLAPComponent 3 X L) (hLq : CFSG.Open.IsQuasisimple ↥L) (hCL : C ≤ L)
    (hI : GLAPComponent 3 C I)
    (hcat : catalogIs (PSimple 3 I) (S10.isG2n n))
    (hE : ∃ E : Subgroup (PSimple 3 L), IsSimpleGroup ↥E ∧ chevTransfer 3 L I = E) :
    GLAPPrimeCoreOf 3 I ≤ I ⊓ GLAPPrimeCoreOf 3 L ∧ (n ≠ 2 → GLAPPrimeCoreOf 3 I = ⊥) := by
  classical
  haveI hp3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hIL : I ≤ L := hI.1.trans hCL
  obtain ⟨E, hEs, hEq⟩ := hE
  have hZI : Subgroup.center (PQuot 3 I) = ⊥ := center_pQuot_eq_bot_G2 hGA hI hcat
  obtain ⟨q, hv, hq2, hqn, ⟨eI⟩⟩ := lieIndex_isG2n hcat
  haveI hsimpG : IsSimpleGroup (TauCeti.ValidLieTypeIndex.Group ⟨.G2 q, hv⟩) :=
    (CFSG.Assembly.lie_finite_simple ⟨.G2 q, hv⟩).2
  have hPSs : IsSimpleGroup (PSimple 3 I) := eI.isSimpleGroup
  have eQ : PQuot 3 I ≃* PSimple 3 I :=
    (QuotientGroup.quotientBot (G := PQuot 3 I)).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hZI.symm)
  have hPQs : IsSimpleGroup (PQuot 3 I) := (eQ.isSimpleGroup_congr).2 hPSs
  let R : Subgroup ↥I := GLAPPrimeCore 3 ↥I
  let O : Subgroup ↥L := GLAPPrimeCore 3 ↥L
  let ι : ↥I →* ↥L := Subgroup.inclusion hIL
  let ψ : ↥I →* PSimple 3 L := (chevQuotHom 3 L).comp ι
  have hrange_eq : ψ.range = E := by
    rw [← hEq]
    ext x
    rw [MonoidHom.mem_range, chevTransfer, Subgroup.mem_map]
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨ι k, Subgroup.mem_subgroupOf.2 k.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, Subgroup.mem_subgroupOf.1 hy⟩, rfl⟩
  have hrange : IsSimpleGroup ↥ψ.range := by rw [hrange_eq]; exact hEs
  have hOn : O.Normal := GLAPPrimeCore.normal 3 ↥L
  have hLq' : CFSG.Open.IsQuasisimple (PQuot 3 L) := isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hL
  have hOne : O ≠ ⊤ := by
    intro h
    have hsub : Subsingleton (PQuot 3 L) := QuotientGroup.subsingleton_iff.2 h
    have htop : Subgroup.center (PQuot 3 L) = ⊤ :=
      eq_top_iff.2 fun x _ => by rw [Subsingleton.elim x 1]; exact Subgroup.one_mem _
    have hsub2 : Subsingleton (PQuot 3 L ⧸ Subgroup.center (PQuot 3 L)) :=
      QuotientGroup.subsingleton_iff.2 htop
    exact (not_nontrivial_iff_subsingleton.2 hsub2) hLq'.2.toNontrivial
  have hOc : O ≤ Subgroup.center ↥L := le_center_of_normal_of_isQuasisimple hLq hOn hOne
  have hkey : ∀ k : ↥I, ψ k = 1 → ∃ a : ℕ, (ι k) ^ (3 ^ a) ∈ O := by
    intro k hk
    have hk' : (QuotientGroup.mk (ι k) : PQuot 3 L) ∈ Subgroup.center (PQuot 3 L) := by
      have h1 : (QuotientGroup.mk' (Subgroup.center (PQuot 3 L))) (QuotientGroup.mk (ι k) : PQuot 3 L) = 1 := hk
      exact (QuotientGroup.eq_one_iff _).1 h1
    obtain ⟨a, ha⟩ := I2611.isPGroup_center_pQuot' Nat.prime_three L ⟨_, hk'⟩
    refine ⟨a, ?_⟩
    have h2 : (QuotientGroup.mk (ι k) : PQuot 3 L) ^ (3 ^ a) = 1 := by
      have := congrArg Subtype.val ha
      simpa using this
    rw [← QuotientGroup.mk_pow] at h2
    exact (QuotientGroup.eq_one_iff _).1 h2
  let NJ : Subgroup ↥I := O.comap ι
  have hNJcop : Nat.Coprime 3 (Nat.card NJ) := by
    have hle : NJ.map ι ≤ O := by
      rintro _ ⟨x, hx, rfl⟩
      exact hx
    have hcard : Nat.card (NJ.map ι) = Nat.card NJ :=
      Subgroup.card_map_of_injective (Subgroup.inclusion_injective hIL)
    have hdvd : Nat.card (NJ.map ι) ∣ Nat.card O := Subgroup.card_dvd_of_le hle
    have hOcop : Nat.Coprime 3 (Nat.card O) := CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥L)
    rw [← hcard]
    exact Nat.Coprime.coprime_dvd_right hdvd hOcop
  have hNJR : NJ ≤ R := le_sSup ⟨inferInstance, hNJcop⟩
  have hN : ∀ k : ↥I, ψ k = 1 → ∃ a : ℕ, k ^ (3 ^ a) ∈ R := by
    intro k hk
    obtain ⟨a, ha⟩ := hkey k hk
    refine ⟨a, hNJR ?_⟩
    show ι (k ^ (3 ^ a)) ∈ O
    rw [map_pow]
    exact ha
  have hZ : ∀ k : ↥I, ψ k = 1 → ∃ a : ℕ, k ^ (3 ^ a) ∈ Subgroup.center ↥I := by
    intro k hk
    obtain ⟨a, ha⟩ := hkey k hk
    refine ⟨a, ?_⟩
    have hz : ι (k ^ (3 ^ a)) ∈ Subgroup.center ↥L := hOc (by rw [map_pow]; exact ha)
    rw [Subgroup.mem_center_iff]
    intro j
    apply Subtype.ext
    have hc := congrArg Subtype.val (Subgroup.mem_center_iff.1 hz (ι j))
    exact hc
  have hR3 : Nat.Coprime 3 (Nat.card R) := CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥I)
  obtain ⟨hker, hcen⟩ := key_center ψ R hR3 hPQs hZI hrange hN hZ
  have hperf : ⁅I, I⁆ = I := CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect hI
  have htop : (⊤ : Subgroup ↥I).map I.subtype = I := by
    ext x
    constructor
    · rintro ⟨y, -, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, Subgroup.mem_top _, rfl⟩
  have hcomm : commutator ↥I = ⊤ := by
    apply Subgroup.map_injective (f := I.subtype) (Subgroup.subtype_injective I)
    rw [commutator_def, Subgroup.map_commutator, htop, hperf]
  have hJq : CFSG.Open.IsQuasisimple ↥I := by
    refine ⟨hcomm, ?_⟩
    exact (MulEquiv.isSimpleGroup_congr (QuotientGroup.quotientMulEquivOfEq hcen)).2 hPQs
  have eJ : ↥I ⧸ Subgroup.center ↥I ≃* TauCeti.ValidLieTypeIndex.Group ⟨.G2 q, hv⟩ :=
    (QuotientGroup.quotientMulEquivOfEq hcen).trans (eQ.trans eI)
  obtain ⟨-, hdn⟩ := card_center_dvd_G2 hGA hJq hq2 hqn eJ
  rw [hcen] at hdn
  refine ⟨?_, fun hn2 => ?_⟩
  · intro x hx
    change x ∈ R.map I.subtype at hx
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.1 hx
    have hψr : ψ r = 1 := MonoidHom.mem_ker.1 (by rw [hker]; exact hr)
    obtain ⟨a, ha⟩ := hkey r hψr
    have hcop : Nat.Coprime (3 ^ a) (orderOf (ι r)) := by
      rw [orderOf_injective ι (Subgroup.inclusion_injective hIL) r]
      exact Nat.Coprime.pow_left a (coprime_orderOf_of_core hr)
    have hιr : ι r ∈ O := mem_of_pow_mem hcop ha
    refine Subgroup.mem_inf.2 ⟨r.2, ?_⟩
    change (r : G) ∈ O.map L.subtype
    exact Subgroup.mem_map.2 ⟨ι r, hιr, rfl⟩
  · have hd1 : Nat.card R = 1 := Nat.dvd_one.1 (hdn hn2)
    have hbot : R = ⊥ := Subgroup.eq_bot_of_card_eq R hd1
    change R.map I.subtype = ⊥
    rw [hbot, Subgroup.map_bot]

end Holds

end CFSG.LocalAnalysis.GLTheoremA.CatB.MultA3

end
