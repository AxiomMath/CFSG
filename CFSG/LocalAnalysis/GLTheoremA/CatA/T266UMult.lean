module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.KMultA1

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T266

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.GLTheoremA.CatB.MultA1 CFSG.LocalAnalysis.GLTheoremA.CatB.MultA2
open CFSG.LocalAnalysis.GLTheoremA.CatB.MultA3
open scoped commutatorElement

section Abstract

theorem core_le_ker {J S : Type} [Group J] [Finite J] [Group S] (ψ : J →* S) (R : Subgroup J) [hRn : R.Normal]
    [Group.IsPerfect J] [Nontrivial (J ⧸ R)] (hrange : IsSimpleGroup ↥ψ.range)
    (hN : ∀ k : J, ψ k = 1 → ∃ a : ℕ, k ^ (3 ^ a) ∈ R) : R ≤ ψ.ker := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let Tr : Subgroup ↥ψ.range := (R.map ψ).subgroupOf ψ.range
  have hTr : Tr.Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨j, hj⟩ := MonoidHom.mem_range.1 g.2
    obtain ⟨r, hr, hrn⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hn)
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
    refine ⟨j * r * j⁻¹, hRn.conj_mem r hr j, ?_⟩
    simp [map_mul, map_inv, hj, hrn]
  rcases hrange.eq_bot_or_eq_top_of_normal Tr with h | h
  · intro r hr
    have hmem : (⟨ψ r, MonoidHom.mem_range.2 ⟨r, rfl⟩⟩ : ↥ψ.range) ∈ Tr := by
      rw [Subgroup.mem_subgroupOf]
      exact Subgroup.mem_map_of_mem ψ hr
    rw [h, Subgroup.mem_bot] at hmem
    exact MonoidHom.mem_ker.2 (congrArg Subtype.val hmem)
  · exfalso
    have hPG : IsPGroup 3 (J ⧸ R) := by
      intro y
      obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective y
      have hmem : (⟨ψ j, MonoidHom.mem_range.2 ⟨j, rfl⟩⟩ : ↥ψ.range) ∈ Tr := by
        rw [h]; exact Subgroup.mem_top _
      obtain ⟨r, hr, hrj⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hmem)
      have hrj' : ψ r = ψ j := hrj
      have hk : r⁻¹ * j ∈ ψ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hrj', inv_mul_cancel]
      obtain ⟨a, ha⟩ := hN _ (MonoidHom.mem_ker.1 hk)
      refine ⟨a, ?_⟩
      have hj : (QuotientGroup.mk j : J ⧸ R) = QuotientGroup.mk (r⁻¹ * j) := by
        rw [QuotientGroup.eq]
        have h1 := hRn.conj_mem r⁻¹ (R.inv_mem hr) j⁻¹
        rwa [inv_inv, mul_assoc] at h1
      show (QuotientGroup.mk j : J ⧸ R) ^ (3 ^ a) = 1
      rw [hj, ← QuotientGroup.mk_pow]
      exact (QuotientGroup.eq_one_iff _).2 ha
    haveI : Group.IsNilpotent (J ⧸ R) := hPG.isNilpotent
    exact (Group.IsPerfect.not_isNilpotent (J ⧸ R)) inferInstance

end Abstract

theorem lieIndex_isU6n {S : Type} [Group S] {n : ℕ} (h : catalogIs S (S10.isU6n n)) :
    ∃ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.twistedA 5 q).Valid), q.p = 2 ∧ q.exponent = n ∧
      Nonempty (S ≃* TauCeti.ValidLieTypeIndex.Group ⟨.twistedA 5 q, hv⟩) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic _ _ => exact hi.elim
  | alternating _ _ => exact hi.elim
  | sporadic _ => exact hi.elim
  | lie j =>
    obtain ⟨d, hv⟩ := j
    cases d with
    | twistedA r q =>
      by_cases hr : r = 5
      · subst hr
        exact ⟨q, hv, hi.1, hi.2, ⟨e⟩⟩
      · exfalso
        simp only [S10.isU6n, onLie] at hi
        split at hi
        · next _ q' heq => exact hr (by injection heq)
        · exact hi
    | _ => exact hi.elim

open CFSG.LocalAnalysis.GLTheoremA.CatB.MultA1 CFSG.Blueprint.Multiplier in
theorem card_center_dvd_U6 (hGA : CFSG.Open.GriessAllModelsStatement) {Q : Type} [Group Q] [Finite Q]
    (hQ : CFSG.Open.IsQuasisimple Q) {n : ℕ} {q : TauCeti.PrimePower}
    {hv : (TauCeti.LieTypeIndex.twistedA 5 q).Valid} (hq2 : q.p = 2) (hqn : q.exponent = n) (hn1 : 1 < n)
    (e : Q ⧸ Subgroup.center Q ≃* TauCeti.ValidLieTypeIndex.Group ⟨.twistedA 5 q, hv⟩) :
    Nat.card (Subgroup.center Q) ∣ 3 := by
  have hm : CFSG.Models.LieModel (Q ⧸ Subgroup.center Q) .PSU 6 2 n := by
    have h := CFSG.Models.lieModel_twistedA 5 q hv e
    have hc : TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA 5 q, hv⟩ = q.p :=
      TauCeti.LieTypeIndex.characteristic_twistedA 5 q
    have hf : TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA 5 q, hv⟩ = q.exponent :=
      TauCeti.LieTypeIndex.fieldExponent_twistedA 5 q
    rw [hc, hf, hq2, hqn] at h
    exact h
  have hg : genericOrders .PSU 6 2 n = (Nat.gcd 6 (2 ^ n + 1), 1) := rfl
  have he : exceptionalOrders .PSU 6 2 n = (1, 1) := by
    unfold exceptionalOrders
    split <;> simp_all
  have hodd : ¬ 2 ∣ 2 ^ n + 1 := by
    have : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
    omega
  have hgpos : 0 < Nat.gcd 6 (2 ^ n + 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  have hne : Nat.gcd 6 (2 ^ n + 1) * 1 * (1 * 1) ≠ 0 := by simpa using hgpos.ne'
  have hd := card_center_dvd_of_table hGA hQ hm hg he hne
  have hgd : Nat.gcd 6 (2 ^ n + 1) ∣ 3 := by
    have h1 : Nat.gcd 6 (2 ^ n + 1) ∣ 3 * 2 := Nat.gcd_dvd_left 6 _
    have h2 : Nat.Coprime (Nat.gcd 6 (2 ^ n + 1)) 2 :=
      Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2
        fun h => hodd (h.trans (Nat.gcd_dvd_right 6 _)))
    exact h2.dvd_of_dvd_mul_right h1
  simpa using hd.trans (by simpa using hgd)


section Center

variable {G : Type} [Group G] [Finite G]

theorem ker_chevQuotHom_eq_center_of_core (I : Subgroup G) (hcomm : commutator ↥I = ⊤)
    (hRZ : GLAPPrimeCore 3 ↥I ≤ Subgroup.center ↥I) :
    (chevQuotHom 3 I).ker = Subgroup.center ↥I := by
  refine le_antisymm ?_ (CFSG.LocalAnalysis.GLTheoremA.CatB.KMultA1.center_le_ker_chevQuotHom I)
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  have hxc : (QuotientGroup.mk x : PQuot 3 I) ∈ Subgroup.center (PQuot 3 I) :=
    (QuotientGroup.eq_one_iff _).1 hx
  have hxR : ∀ y : ↥I, x⁻¹ * y⁻¹ * x * y ∈ GLAPPrimeCore 3 ↥I := by
    intro y
    have h1 := Subgroup.mem_center_iff.1 hxc (QuotientGroup.mk y)
    have h2 : (QuotientGroup.mk (y * x) : PQuot 3 I) = QuotientGroup.mk (x * y) := h1
    have h3 := QuotientGroup.eq.1 h2
    simpa [mul_assoc] using h3
  let δ : ↥I →* Subgroup.center ↥I :=
    { toFun := fun y => ⟨x⁻¹ * y⁻¹ * x * y, hRZ (hxR y)⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := by
        intro y y'
        apply Subtype.ext
        have hc := Subgroup.mem_center_iff.1 (hRZ (hxR y)) y'
        have hc' := Subgroup.mem_center_iff.1 (hRZ (hxR y)) (x⁻¹ * y'⁻¹ * x * y')
        show x⁻¹ * (y * y')⁻¹ * x * (y * y') = (x⁻¹ * y⁻¹ * x * y) * (x⁻¹ * y'⁻¹ * x * y')
        calc x⁻¹ * (y * y')⁻¹ * x * (y * y')
            = x⁻¹ * y'⁻¹ * x * ((x⁻¹ * y⁻¹ * x * y) * y') := by group
          _ = x⁻¹ * y'⁻¹ * x * (y' * (x⁻¹ * y⁻¹ * x * y)) := by rw [hc.symm]
          _ = (x⁻¹ * y'⁻¹ * x * y') * (x⁻¹ * y⁻¹ * x * y) := by group
          _ = (x⁻¹ * y⁻¹ * x * y) * (x⁻¹ * y'⁻¹ * x * y') := hc' }
  have hδ : δ.ker = ⊤ := by
    refine eq_top_iff.2 ?_
    rw [← hcomm]
    exact Abelianization.commutator_subset_ker δ
  rw [Subgroup.mem_center_iff]
  intro y
  have hy : y ∈ δ.ker := by rw [hδ]; exact Subgroup.mem_top y
  have hy' : x⁻¹ * y⁻¹ * x * y = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hy)
  have hcm : Commute x⁻¹ y⁻¹ := by
    rw [← commutatorElement_eq_one_iff_commute]
    simpa [commutatorElement_def] using hy'
  exact (Commute.inv_inv_iff.1 hcm).symm.eq

end Center

section Layer

variable {G : Type} [Group G] [Finite G]

theorem coprime_orderOf_of_core' {H : Type} [Group H] [Finite H] {r : H} (hr : r ∈ GLAPPrimeCore 3 H) :
    Nat.Coprime 3 (orderOf r) := by
  have hcop : Nat.Coprime 3 (Nat.card (GLAPPrimeCore 3 H)) :=
    CFSG.pPrimeCore_coprime_card (p := 3) (G := H)
  have hd : orderOf (⟨r, hr⟩ : GLAPPrimeCore 3 H) ∣ Nat.card (GLAPPrimeCore 3 H) :=
    orderOf_dvd_natCard _
  rw [← Subgroup.orderOf_mk r hr]
  exact Nat.Coprime.coprime_dvd_right hd hcop

theorem layer_core_eq_bot_u6 (hGA : CFSG.Open.GriessAllModelsStatement) {X L I C : Subgroup G} {n : ℕ}
    (hn1 : 1 < n) (hL : GLAPComponent 3 X L) (hLq : CFSG.Open.IsQuasisimple ↥L) (hCL : C ≤ L)
    (hI : GLAPComponent 3 C I) (hcat : catalogIs (PSimple 3 I) (S10.isU6n n))
    (hE : ∃ E : Subgroup (PSimple 3 L), IsSimpleGroup ↥E ∧ chevTransfer 3 L I = E) :
    GLAPPrimeCoreOf 3 I = ⊥ := by
  classical
  haveI hp3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hIL : I ≤ L := hI.1.trans hCL
  obtain ⟨E, hEs, hEq⟩ := hE
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
  haveI : Group.IsPerfect ↥I := ⟨hcomm⟩
  have hPQ : CFSG.Open.IsQuasisimple (PQuot 3 I) := isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hI
  haveI hnt : Nontrivial (↥I ⧸ R) := by
    haveI := hPQ.2.toNontrivial
    exact (QuotientGroup.mk'_surjective (Subgroup.center (PQuot 3 I))).nontrivial
  have hRK : R ≤ ψ.ker := core_le_ker ψ R hrange hN
  have hRZ : R ≤ Subgroup.center ↥I := by
    intro r hr
    have hψr : ψ r = 1 := MonoidHom.mem_ker.1 (hRK hr)
    obtain ⟨a, ha⟩ := hkey r hψr
    have hcop : Nat.Coprime (3 ^ a) (orderOf (ι r)) := by
      rw [orderOf_injective ι (Subgroup.inclusion_injective hIL) r]
      exact Nat.Coprime.pow_left a (coprime_orderOf_of_core' hr)
    have hιr : ι r ∈ O := mem_of_pow_mem hcop ha
    have hz : ι r ∈ Subgroup.center ↥L := hOc hιr
    rw [Subgroup.mem_center_iff]
    intro j
    apply Subtype.ext
    have hc := congrArg Subtype.val (Subgroup.mem_center_iff.1 hz (ι j))
    exact hc
  have hker : (chevQuotHom 3 I).ker = Subgroup.center ↥I := ker_chevQuotHom_eq_center_of_core I hcomm hRZ
  let eJ : ↥I ⧸ Subgroup.center ↥I ≃* PSimple 3 I :=
    centralIso (chevQuotHom 3 I) (chevQuotHom_surjective 3 I) hker
  have hJq : CFSG.Open.IsQuasisimple ↥I := ⟨hcomm, (eJ.isSimpleGroup_congr).2 hPQ.2⟩
  obtain ⟨q, hv, hq2, hqn, ⟨eU⟩⟩ := lieIndex_isU6n hcat
  have hdvd : Nat.card (Subgroup.center ↥I) ∣ 3 := card_center_dvd_U6 hGA hJq hq2 hqn hn1 (eJ.trans eU)
  have hRcard : Nat.card R ∣ 3 := (Subgroup.card_dvd_of_le hRZ).trans hdvd
  have hR3 : Nat.Coprime 3 (Nat.card R) := CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥I)
  have hR1 : Nat.card R = 1 := Nat.Coprime.eq_one_of_dvd hR3.symm hRcard
  have hbot : R = ⊥ := Subgroup.eq_bot_of_card_eq R hR1
  change R.map I.subtype = ⊥
  rw [hbot, Subgroup.map_bot]

end Layer

end CFSG.LocalAnalysis.GLTheoremA.T266

end
