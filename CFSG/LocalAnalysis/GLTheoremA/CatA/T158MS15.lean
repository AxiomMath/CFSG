module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MTriv
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158Inn

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T158

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.GLTheoremA.T156 CFSG.LocalAnalysis.GLTheoremA.S267
open scoped commutatorElement

section Basic

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Group Ω] [Finite Ω]

private theorem t158s15_eq_one {p : ℕ} (hp : p.Prime) {H : Type} [Group H] {π : H →* Ω}
    (hN : ¬ p ∣ Nat.card π.ker) {u : H} (hu : u ^ p = 1) (hπ : π u = 1) : u = 1 := by
  have hker : u ∈ π.ker := hπ
  by_contra hne
  have hord : orderOf u = p := by
    rcases (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one hu) with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hne
    · exact h
  exact hN (by rw [← hord]; exact Subgroup.orderOf_dvd_natCard π.ker hker)

private theorem t158s15_dvd_of_zpow_eq_one {M : Type*} [Group M] {p : ℕ} (hp : p.Prime) {a : M}
    (hap : a ^ p = 1) (hne : a ≠ 1) {i : ℤ} (hi : a ^ i = 1) : (p : ℤ) ∣ i := by
  haveI := Fact.mk hp
  rw [← orderOf_eq_prime hap hne]
  exact orderOf_dvd_iff_zpow_eq_one.2 hi

private theorem t158s15_zpow_eq_one {M : Type*} [Group M] {p : ℕ} {a : M} (hap : a ^ p = 1) {i : ℤ}
    (hi : (p : ℤ) ∣ i) : a ^ i = 1 := by
  obtain ⟨k, rfl⟩ := hi
  rw [zpow_mul, zpow_natCast, hap, one_zpow]

private theorem t158s15_chevAut_centralizes {p : ℕ} (hp : p.Prime) {X₀ L : Subgroup G}
    (hL : GLAPComponent p X₀ L) {g : G} (hg : ∀ l ∈ L, l * g = g * l)
    (hgN : g ∈ Subgroup.normalizer (L : Set G)) : chevAut p L ⟨g, hgN⟩ = 1 := by
  refine (chevAut_eq_one_iff hp hL hgN).2 (centMod_iff.2 (mem_centModSubgroup.2 ⟨hgN, fun l hl => ?_⟩))
  rw [commutatorElement_eq_one_iff_mul_comm.2 (hg l hl)]
  exact Subgroup.one_mem _

private theorem t158s15_chevAut_one {p : ℕ} (hp : p.Prime) {H L : Subgroup G} (hLH : L ≤ H)
    {π : ↥H →* Ω} (hN : ¬ p ∣ Nat.card π.ker) {a : G} (haH : a ∈ H)
    (haL : a ∈ Subgroup.normalizer (L : Set G))
    (hcent : ∀ s ∈ (L.subgroupOf H).map π, s * π ⟨a, haH⟩ = π ⟨a, haH⟩ * s) :
    chevAut p L ⟨a, haL⟩ = 1 := by
  have hz := mem_normalizer_subgroupOf' haH haL
  have hmap : (L.subgroupOf H).map H.subtype = L := Subgroup.map_subgroupOf_eq_of_le hLH
  have key : ∀ q q' : PQuot p L, indRel p L a q q' → q' = q := by
    intro q q' hr
    obtain ⟨l, l', hl, hl', hll'⟩ := (compIso_rel hp hmap π hN hz q q').1 hr
    have h1 : (l' : Ω) = l := by
      rw [hll']
      have := hcent l l.2
      rw [mul_assoc, this, ← mul_assoc, inv_mul_cancel, one_mul]
    have h2 : l' = l := Subtype.ext h1
    apply (compIso hp hmap π hN).injective
    rw [← hl, ← hl', h2]
  have hind : MI.indAut p L a haL = 1 := by
    ext r
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective r
    obtain ⟨q', hq'⟩ := MI.indRel_total haL y
    rw [MI.indAut_apply_mk haL hq', key y q' hq']
    rfl
  have hinv : MI.indAut p L a haL = (chevAut p L ⟨a, haL⟩)⁻¹ := by
    rw [MI.indAut, ← map_inv]
    rfl
  rw [hinv] at hind
  exact inv_eq_one.1 hind

private theorem t158s15_innDiagOn_forth {p : ℕ} (hp : p.Prime) {H L A : Subgroup G} (hLH : L ≤ H)
    {π : ↥H →* Ω} (hN : ¬ p ∣ Nat.card π.ker) (h : InnDiagOn p A L) :
    InnDiagOn p ((A.subgroupOf H).map π) ((L.subgroupOf H).map π) := by
  have hAY : ∀ z ∈ A.subgroupOf H,
      z ∈ Subgroup.normalizer ((L.subgroupOf H : Subgroup ↥H) : Set ↥H) := fun z hz =>
    mem_normalizer_subgroupOf' z.2 (h.1 (Subgroup.mem_subgroupOf.1 hz))
  refine innDiagOn_to_Omega (compIso hp (Subgroup.map_subgroupOf_eq_of_le hLH) π hN) ?_ ?_ h
  · rintro _ ⟨z, hz, rfl⟩
    exact map_normalizer_mem π (hAY z hz)
  · rintro _ ⟨z, hz, rfl⟩
    exact ⟨(z : G), Subgroup.mem_subgroupOf.1 hz, fun q q' =>
      compIso_rel hp (Subgroup.map_subgroupOf_eq_of_le hLH) π hN (hAY z hz) q q'⟩

end Basic

section Faithful


variable {X : Type} [Group X] [Finite X] {p : ℕ} {K B : Subgroup X} {x₁ x₂ : X} {L₁ L₂ : Subgroup X}

private theorem t158s15_chevAut_ne_one {X₀ L : Subgroup X} {y : X} (hp : p.Prime)
    (hL : GLAPComponent p X₀ L) (hchev : IsChevSimple 2 (PSimple p L)) (hFG : FGOn p y L) :
    chevAut p L ⟨y, t158m_fgOn_normalizer hFG⟩ ≠ 1 := by
  intro h1
  have hyN := t158m_fgOn_normalizer hFG
  have hin : InducesInnerMod p L y := by
    refine (chevAut_mem_inner_iff hp hL hyN).1 ?_
    rw [h1]
    exact Subgroup.one_mem _
  have hInn : InnDiagOn p (Subgroup.zpowers y) L := MI.inner_innDiag_any hL hchev hyN hin
  rcases hFG with hF | ⟨hNI, -, -⟩
  · exact (MI.field_nonInnDiag_any hL hF).2 hInn
  · exact hNI.2 hInn

private theorem t158s15_split (hh : T158Hyp p K B x₁ x₂ L₁ L₂) {a : X} {i j : ℤ}
    (hdec : a = x₁ ^ i * x₂ ^ j)
    (h1 : ∀ ha : a ∈ Subgroup.normalizer (L₁ : Set X), chevAut p L₁ ⟨a, ha⟩ = 1)
    (h2 : ∀ ha : a ∈ Subgroup.normalizer (L₂ : Set X), chevAut p L₂ ⟨a, ha⟩ = 1) :
    x₁ ^ i = 1 ∧ x₂ ^ j = 1 := by
  subst hdec
  obtain ⟨-, -, -, -, -, -, hL1, hc1, hL2, hc2, hn12, hn21⟩ := t158m_unpack hh
  obtain ⟨hx1p, hx2p⟩ := t158m_pow hh
  have hp := hh.prime
  have hx1L1 : ∀ l ∈ L₁, l * x₁ = x₁ * l := fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 (hL1.1 hl)).2
  have hx2L2 : ∀ l ∈ L₂, l * x₂ = x₂ * l := fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 (hL2.1 hl)).2
  have hx1N1 : x₁ ∈ Subgroup.normalizer (L₁ : Set X) := by
    apply Subgroup.centralizer_le_normalizer
    exact Subgroup.mem_centralizer_iff.2 hx1L1
  have hx2N2 : x₂ ∈ Subgroup.normalizer (L₂ : Set X) := by
    apply Subgroup.centralizer_le_normalizer
    exact Subgroup.mem_centralizer_iff.2 hx2L2
  have hx1N2 : x₁ ∈ Subgroup.normalizer (L₂ : Set X) := t158m_fgOn_normalizer hn12
  have hx2N1 : x₂ ∈ Subgroup.normalizer (L₁ : Set X) := t158m_fgOn_normalizer hn21
  have hn1 : x₁ ^ i * x₂ ^ j ∈ Subgroup.normalizer (L₁ : Set X) :=
    Subgroup.mul_mem _ (Subgroup.zpow_mem _ hx1N1 i) (Subgroup.zpow_mem _ hx2N1 j)
  have hn2 : x₁ ^ i * x₂ ^ j ∈ Subgroup.normalizer (L₂ : Set X) :=
    Subgroup.mul_mem _ (Subgroup.zpow_mem _ hx1N2 i) (Subgroup.zpow_mem _ hx2N2 j)
  have e1 : chevAut p L₁ ⟨x₁ ^ i * x₂ ^ j, hn1⟩ =
      chevAut p L₁ ⟨x₁, hx1N1⟩ ^ i * chevAut p L₁ ⟨x₂, hx2N1⟩ ^ j := by
    rw [← map_zpow, ← map_zpow, ← map_mul]
    congr 1
  have e2 : chevAut p L₂ ⟨x₁ ^ i * x₂ ^ j, hn2⟩ =
      chevAut p L₂ ⟨x₁, hx1N2⟩ ^ i * chevAut p L₂ ⟨x₂, hx2N2⟩ ^ j := by
    rw [← map_zpow, ← map_zpow, ← map_mul]
    congr 1
  have z1 : chevAut p L₁ ⟨x₁, hx1N1⟩ = 1 := t158s15_chevAut_centralizes hp hL1 hx1L1 hx1N1
  have z2 : chevAut p L₂ ⟨x₂, hx2N2⟩ = 1 := t158s15_chevAut_centralizes hp hL2 hx2L2 hx2N2
  have ne1 : chevAut p L₁ ⟨x₂, hx2N1⟩ ≠ 1 := t158s15_chevAut_ne_one hp hL1 hc1 hn21
  have ne2 : chevAut p L₂ ⟨x₁, hx1N2⟩ ≠ 1 := t158s15_chevAut_ne_one hp hL2 hc2 hn12
  have hb1 : chevAut p L₁ ⟨x₂, hx2N1⟩ ^ j = 1 := by
    have := h1 hn1
    rwa [e1, z1, one_zpow, one_mul] at this
  have hb2 : chevAut p L₂ ⟨x₁, hx1N2⟩ ^ i = 1 := by
    have := h2 hn2
    rwa [e2, z2, one_zpow, mul_one] at this
  exact ⟨t158s15_zpow_eq_one hx1p
      (t158s15_dvd_of_zpow_eq_one hp (chevAut_pow_eq_one p L₂ hx1N2 hx1p) ne2 hb2),
    t158s15_zpow_eq_one hx2p
      (t158s15_dvd_of_zpow_eq_one hp (chevAut_pow_eq_one p L₁ hx2N1 hx2p) ne1 hb1)⟩

theorem t158Shape15_of_fact15 (h15 : I171.I171ShapeFact15) : T158Shape15 := by
  intro X _ _ p K B x₁ x₂ L₁ L₂ hQ hh hE
  have hp : p.Prime := hh.prime
  have hp2 : p ≠ 2 := hh.odd
  obtain ⟨hK, hBel, hx1B, hx2B, hx1, hx2, hL1, hc1, hL2, hc2, hn12, hn21⟩ := t158m_unpack hh
  have hKc : IsChevSimple 2 (PSimple p K) := Or.inl hQ
  obtain ⟨hN1, hN2⟩ := t158m_normalizer hh
  obtain ⟨hx1p, hx2p⟩ := t158m_pow hh
  have hcommAll : ∀ u ∈ Subgroup.zpowers x₁, ∀ v ∈ Subgroup.zpowers x₂, u * v = v * u := fun u hu v hv =>
    isElemAbelian_commute hBel (Subgroup.zpowers_le.2 hx1B hu) (Subgroup.zpowers_le.2 hx2B hv)
  have hnorm12 : Subgroup.zpowers x₁ ≤ Subgroup.normalizer (Subgroup.zpowers x₂ : Set X) := by
    intro u hu
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact (hcommAll u hu v hv).symm
  have hnorm21 : Subgroup.zpowers x₂ ≤ Subgroup.normalizer (Subgroup.zpowers x₁ : Set X) := by
    intro v hv
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact hcommAll u hu v hv
  set A : Subgroup X := Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ with hAdef
  have hAB : A ≤ B := sup_le (Subgroup.zpowers_le.2 hx1B) (Subgroup.zpowers_le.2 hx2B)
  have hAel : IsElemAbelian p A := isElemAbelian_mono hBel hAB
  have hx1A : x₁ ∈ A := Subgroup.mem_sup_left (Subgroup.mem_zpowers x₁)
  have hx2A : x₂ ∈ A := Subgroup.mem_sup_right (Subgroup.mem_zpowers x₂)
  have hAN : A ≤ Subgroup.normalizer (K : Set X) :=
    sup_le (Subgroup.zpowers_le.2 hN1) (Subgroup.zpowers_le.2 hN2)
  have hdecomp : ∀ a ∈ A, ∃ i j : ℤ, a = x₁ ^ i * x₂ ^ j := by
    intro a ha
    rw [← SetLike.mem_coe, hAdef, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hnorm12] at ha
    obtain ⟨u, hu, v, hv, rfl⟩ := Set.mem_mul.1 ha
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hv
    exact ⟨i, j, rfl⟩
  have htriv : ∀ (L : Subgroup X), ∀ ha : (1 : X) ∈ Subgroup.normalizer (L : Set X), chevAut p L ⟨1, ha⟩ = 1 :=
    fun L ha => by
      rw [show (⟨1, ha⟩ : ↥(Subgroup.normalizer (L : Set X))) = 1 from rfl, map_one]
  have hind12 : x₂ ∉ Subgroup.zpowers x₁ := by
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    have h1 : (1 : X) = x₁ ^ (-k) * x₂ ^ (1 : ℤ) := by
      rw [← hk, zpow_one, zpow_neg, inv_mul_cancel]
    have := (t158s15_split hh h1 (htriv L₁) (htriv L₂)).2
    rw [zpow_one] at this
    exact hx2 this
  have hind21 : x₁ ∉ Subgroup.zpowers x₂ := by
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    have h1 : (1 : X) = x₁ ^ (1 : ℤ) * x₂ ^ (-k) := by
      rw [← hk, zpow_one, zpow_neg, mul_inv_cancel]
    have := (t158s15_split hh h1 (htriv L₁) (htriv L₂)).1
    rw [zpow_one] at this
    exact hx1 this
  haveI : Fact p.Prime := ⟨hp⟩
  have hz1 : Nat.card (Subgroup.zpowers x₁) = p := by
    rw [Nat.card_zpowers]; exact orderOf_eq_prime hx1p hx1
  have hz2 : Nat.card (Subgroup.zpowers x₂) = p := by
    rw [Nat.card_zpowers]; exact orderOf_eq_prime hx2p hx2
  have hinfbot : Subgroup.zpowers x₁ ⊓ Subgroup.zpowers x₂ = ⊥ := by
    have hdvd : Nat.card ↥(Subgroup.zpowers x₁ ⊓ Subgroup.zpowers x₂) ∣ p := by
      rw [← hz1]
      exact Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime hp).1 hdvd with h | h
    · exact Subgroup.card_eq_one.1 h
    · exfalso
      have heq : Subgroup.zpowers x₁ ⊓ Subgroup.zpowers x₂ = Subgroup.zpowers x₁ :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h, hz1])
      apply hind21
      have : Subgroup.zpowers x₁ ≤ Subgroup.zpowers x₂ := by
        rw [← heq]; exact inf_le_right
      exact this (Subgroup.mem_zpowers x₁)
  have hcardA : Nat.card A = p ^ 2 := by
    have := card_sup_mul_card_inf_of_le_normalizer hnorm21
    rw [hinfbot, Subgroup.card_bot, hz1, hz2, mul_one] at this
    rw [hAdef, this]; ring
  set H : Subgroup X := K ⊔ A with hHdef
  have hKH : K ≤ H := le_sup_left
  have hAH : A ≤ H := le_sup_right
  have hx1H : x₁ ∈ H := hAH hx1A
  have hx2H : x₂ ∈ H := hAH hx2A
  have hHN : H ≤ Subgroup.normalizer (K : Set X) := sup_le Subgroup.le_normalizer hAN
  set M : Subgroup ↥H := K.subgroupOf H with hMdef
  have hMn : M.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).2 hHN
  have hN0n : (GLAPPrimeCoreOf p M).Normal := by
    have h := normalizer_le_normalizer_glaPPrimeCoreOf p M
    rw [Subgroup.normalizer_eq_top_iff.2 hMn, top_le_iff] at h
    exact Subgroup.normalizer_eq_top_iff.1 h
  haveI := hN0n
  set N0 : Subgroup ↥H := GLAPPrimeCoreOf p M with hN0def
  set π : ↥H →* ↥H ⧸ N0 := QuotientGroup.mk' N0 with hπdef
  have hN : ¬ p ∣ Nat.card π.ker := by
    rw [hπdef, QuotientGroup.ker_mk']
    exact not_dvd_card_glaPPrimeCoreOf hp _
  have hMK : M.map H.subtype = K := Subgroup.map_subgroupOf_eq_of_le hKH
  set S : Subgroup (↥H ⧸ N0) := M.map π with hSdef
  have hSn : S.Normal := hMn.map π (QuotientGroup.mk'_surjective N0)
  set eK : PQuot p K ≃* PQuot p S := compIso hp hMK π hN with heKdef
  have hqPS : CFSG.Open.IsQuasisimple (PQuot p S) :=
    (isQuasisimple_pQuot_of_glaPComponent hp hK).of_mulEquiv eK.symm
  have hSp : GLAPPrimeCore p ↥S = ⊥ := by
    have h1 : (GLAPPrimeCoreOf p M).map π = GLAPPrimeCoreOf p S := map_glaPPrimeCoreOf hp π hN M
    have h2 : (GLAPPrimeCoreOf p M).map π = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, hπdef, QuotientGroup.ker_mk']
    have h3 : GLAPPrimeCoreOf p S = ⊥ := by rw [← h1, h2]
    exact (Subgroup.map_eq_bot_iff_of_injective _ S.subtype_injective).1 h3
  have eS : PQuot p S ≃* ↥S :=
    (QuotientGroup.quotientMulEquivOfEq hSp).trans QuotientGroup.quotientBot
  have hqS : CFSG.Open.IsQuasisimple ↥S := hqPS.of_mulEquiv eS.symm
  have hcS : IsChevSimple 2 (PSimple p S) := isChevSimple_congr (psimpleIso eK) hKc
  have hqS' : CFSG.IsQuasisimple ↥S :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mp
      ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open _).mpr hqS)
  have hL1K : L₁ ≤ K := hL1.1.trans inf_le_left
  have hL2K : L₂ ≤ K := hL2.1.trans inf_le_left
  have hL1H : L₁ ≤ H := hL1K.trans hKH
  have hL2H : L₂ ≤ H := hL2K.trans hKH
  have hJ := glaPComponent_forth hp hKH hx1H hN1 hx1p hN hL1
  have hFG := fgOn_forth hp hL1H hN hx2H (t158m_fgOn_normalizer hn21) hn21
  have hLS1 : (L₁.subgroupOf H).map π ≤ S :=
    Subgroup.map_mono fun u hu => Subgroup.mem_subgroupOf.2 (hL1K (Subgroup.mem_subgroupOf.1 hu))
  have hLS2 : (L₂.subgroupOf H).map π ≤ S :=
    Subgroup.map_mono fun u hu => Subgroup.mem_subgroupOf.2 (hL2K (Subgroup.mem_subgroupOf.1 hu))
  set E : Subgroup (↥H ⧸ N0) := (A.subgroupOf H).map π with hEdef
  have hEel : IsElemAbelian p E := (hAel.subgroupOf H).map π
  have hEN : E ≤ Subgroup.normalizer (S : Set (↥H ⧸ N0)) := by
    rw [Subgroup.normalizer_eq_top_iff.2 hSn]
    exact le_top
  have hEinn : InnDiagOn p E S := t158s15_innDiagOn_forth hp hKH hN hE
  have hEcard : Nat.card E = p ^ 2 := by
    have hinj : Function.Injective (π.domRestrict (A.subgroupOf H)) := by
      rw [injective_iff_map_eq_one]
      intro u hu
      have hmem : ((u : ↥H) : X) ∈ A := Subgroup.mem_subgroupOf.1 u.2
      have hu' : (u : ↥H) ^ p = 1 := Subtype.ext (by simpa using hAel.2 _ hmem)
      exact Subtype.ext (t158s15_eq_one hp hN hu' hu)
    rw [hEdef, ← MonoidHom.restrict_range, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAH).toEquiv, hcardA]
  have hdE : π ⟨x₁, hx1H⟩ ∈ E := Subgroup.mem_map.2 ⟨⟨x₁, hx1H⟩, Subgroup.mem_subgroupOf.2 hx1A, rfl⟩
  have hbE : π ⟨x₂, hx2H⟩ ∈ E := Subgroup.mem_map.2 ⟨⟨x₂, hx2H⟩, Subgroup.mem_subgroupOf.2 hx2A, rfl⟩
  have hd1 : π ⟨x₁, hx1H⟩ ≠ 1 := fun h =>
    hx1 (congrArg Subtype.val (t158s15_eq_one hp hN (Subtype.ext hx1p) h))
  have hAN1 : A ≤ Subgroup.normalizer (L₁ : Set X) := by
    refine sup_le (Subgroup.zpowers_le.2 ?_) (Subgroup.zpowers_le.2 (t158m_fgOn_normalizer hn21))
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 (hL1.1 hl)).2
  have hAN2 : A ≤ Subgroup.normalizer (L₂ : Set X) := by
    refine sup_le (Subgroup.zpowers_le.2 (t158m_fgOn_normalizer hn12)) (Subgroup.zpowers_le.2 ?_)
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 (hL2.1 hl)).2
  have hEC : E ⊓ Subgroup.centralizer (S : Set (↥H ⧸ N0)) = ⊥ := by
    rw [eq_bot_iff]
    intro e he
    obtain ⟨heE, heC⟩ := Subgroup.mem_inf.1 he
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 heE
    have haA : (z : X) ∈ A := Subgroup.mem_subgroupOf.1 hz
    obtain ⟨i, j, hij⟩ := hdecomp _ haA
    have hcz := Subgroup.mem_centralizer_iff.1 heC
    have g1 := t158s15_chevAut_one hp hL1H hN z.2 (hAN1 haA) (fun s hs => hcz s (hLS1 hs))
    have g2 := t158s15_chevAut_one hp hL2H hN z.2 (hAN2 haA) (fun s hs => hcz s (hLS2 hs))
    obtain ⟨e1, e2⟩ := t158s15_split hh hij (fun _ => g1) (fun _ => g2)
    have hz1 : (z : X) = 1 := by rw [hij, e1, e2, mul_one]
    have hz1' : z = 1 := Subtype.ext hz1
    rw [hz1', map_one]
    exact Subgroup.one_mem _
  rcases h15 (↥H ⧸ N0) p S ((L₁.subgroupOf H).map π) E (π ⟨x₁, hx1H⟩) hp hp2 hqS' hcS hEel hEcard hEN
      hEinn hEC hdE hd1 hJ (π ⟨x₂, hx2H⟩) hbE with ⟨-, hbinn⟩ | hshape
  · exfalso
    rcases hFG with hF | hG
    · exact (MI.field_nonInnDiag_any hJ hF).2 hbinn
    · exact hG.1.2 hbinn
  · exact (catalogIs_congr (psimpleIso eK)).2 hshape

end Faithful

end CFSG.LocalAnalysis.GLTheoremA.T158

end
