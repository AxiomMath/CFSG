module

public import CFSG.GH74.GLS.C3.Layer1.St1Iv251
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.GH74.GLS.C3.Layer1.Iv251

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.TwoThin
  CFSG.GH74.GLS.C3.Layer1.PumpCalc CFSG.GH74.GLS.Stage1.Thm2.Recip CFSG.ComponentClassification
open scoped commutatorElement

section Triv

variable {G : Type} [Group G] [Finite G]

structure TrivData (x z : G) (K K' Λ : Subgroup G) : Prop where
  lam : IsLam x z K Λ
  le : Λ ≤ K'
  cover : ∀ k ∈ K', ∃ l ∈ Λ, ∃ o ∈ pPrimeCoreOf 2 K', k = l * o
  cent : ∀ q ∈ CxK x K, z * q = q * z → q ∈ CxK z K'
  x_mem : x ∈ CxK z K'
  twoElt : ∀ g ∈ K' ⊓ centralizer ({x} : Set G), (∃ n : ℕ, g ^ (2 ^ n) = 1) → g ∈ Λ

theorem exists_trivData {x z : G} {K K' : Subgroup G}
    (hlt : PumpUpLT 2 x K z K')
    (htr : x ∈ normalizer (K' : Set G) ∧ Nonempty (kBar K' ≃* kBar K)) :
    ∃ Λ : Subgroup G, TrivData x z K K' Λ := by
  obtain ⟨hxK', ⟨e⟩⟩ := htr
  have hx2 : orderOf x = 2 := hlt.1.1
  have hz2 : orderOf z = 2 := hlt.2.1.1
  have hKc : IsPCompIn 2 (centralizer ({x} : Set G)) K := hlt.1.2.2
  have hK'c : IsPCompIn 2 (centralizer ({z} : Set G)) K' := hlt.2.1.2.2
  have hzC : z ∈ centralizer ({x} : Set G) := hlt.2.2.1
  have hzs : z ∈ centralizerSection K (pPrimeCoreOf 2 K) := hlt.2.2.2.1
  obtain ⟨Λ, hΛ⟩ := exists_isLam hz2 hKc hzs
  have hxY : x ∈ centralizer ({z} : Set G) := mem_centralizer_symm hzC
  have hΛK : Λ ≤ K := hΛ.le.trans inf_le_left
  have hΛY : Λ ≤ centralizer ({z} : Set G) := hΛ.le.trans inf_le_right
  have hle := bar_le_of_stable hlt hΛ hxK'
  obtain ⟨φ, hφs, -, -⟩ := TwoThin.exists_phi hΛK hΛY hΛ.cover
  obtain ⟨e2⟩ := kBar_equiv_bar hK'c
  have hcard : Nat.card ↥(bar z K') ≤ Nat.card ↥(bar z Λ) := by
    have h1 : Nat.card (kBar K) ≤ Nat.card ↥(bar z Λ) := Nat.card_le_card_of_surjective φ hφs
    have h2 : Nat.card ↥(bar z K') = Nat.card (kBar K) :=
      (Nat.card_congr e2.symm.toEquiv).trans (Nat.card_congr e.toEquiv)
    omega
  have hEq : bar z Λ = bar z K' := Subgroup.eq_of_le_of_card_ge hle hcard
  have hΛK' : Λ ≤ K' := by
    have hperf : Group.IsPerfect ↥(Λ.subgroupOf (centralizer ({z} : Set G))) :=
      Subgroup.isPerfect_iff.mpr (lam_perfect_Y hΛ)
    have hM2 : TwoComponents.IsTwoComponent (K'.subgroupOf (centralizer ({z} : Set G))) :=
      (isPCompIn_two_iff.mp hK'c).2
    have hmap : (Λ.subgroupOf (centralizer ({z} : Set G))).map
        (barMk ↥(centralizer ({z} : Set G))) ≤
        (K'.subgroupOf (centralizer ({z} : Set G))).map (barMk ↥(centralizer ({z} : Set G))) :=
      hEq.le
    intro a ha
    have haY : a ∈ centralizer ({z} : Set G) := hΛY ha
    have := PumpRigid.le_of_perfect_map_le hperf hM2 hmap
      (Subgroup.mem_subgroupOf.mpr ha : (⟨a, haY⟩ : ↥(centralizer ({z} : Set G))) ∈ _)
    exact Subgroup.mem_subgroupOf.mp this
  have hcover : ∀ k ∈ K', ∃ l ∈ Λ, ∃ o ∈ pPrimeCoreOf 2 K', k = l * o := by
    intro k hk
    have hkY : k ∈ centralizer ({z} : Set G) := hK'c.1 hk
    have hmem : barMk ↥(centralizer ({z} : Set G)) ⟨k, hkY⟩ ∈ bar z Λ := by
      rw [hEq]
      exact ⟨⟨k, hkY⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩
    obtain ⟨m, hm, hmk⟩ := hmem
    have hmΛ : (m : G) ∈ Λ := Subgroup.mem_subgroupOf.mp hm
    refine ⟨m, hmΛ, (m : G)⁻¹ * k, ?_, by group⟩
    have hmK' : (m : G) ∈ K' := hΛK' hmΛ
    have h1 : (m : G)⁻¹ * k ∈ K' := mul_mem (inv_mem hmK') hk
    refine PumpRigid.mem_pPrimeCoreOf_of_barMk_eq_one' hK'c.1 h1 (hK'c.1 h1) ?_
    have : (⟨(m : G)⁻¹ * k, hK'c.1 h1⟩ : ↥(centralizer ({z} : Set G))) = m⁻¹ * ⟨k, hkY⟩ := rfl
    rw [this, map_mul, map_inv, hmk, inv_mul_cancel]
  have hleHat : hatCard K' ≤ hatCard K := (Nat.card_congr e.toEquiv).le
  obtain ⟨Λ₀, -, hK'c, -, -, hcent₀, hcases₀⟩ :=
    PumpRigid.rigid_step hlt hxY hleHat
  have hbar₀ : bar z Λ₀ = bar z K' :=
    (hcases₀.resolve_right (fun hh => hh.1 hxK')).2
  have hR3 : ∀ q ∈ CxK x K, z * q = q * z → q ∈ CxK z K' := by
    intro q hqC hqz
    have hqY : q ∈ centralizer ({z} : Set G) :=
      mem_centralizer_singleton_iff.mpr hqz.symm
    refine PumpRigid.mem_CxK_of_centralizes hK'c hqY ?_
    intro w hw
    rw [← hbar₀] at hw
    exact hcent₀ q hqY hqC w hw
  have hxC : x ∈ CxK z K' :=
    hR3 x (PumpRigid.x_mem_CxK hKc.1)
      (mem_centralizer_singleton_iff.mp hlt.2.2.1)
  obtain ⟨Λ', hΛ'⟩ := exists_isLam (z := z) hx2 hK'c (Subgroup.mem_inf.mp hxC).2
  have hΛΛ' : Λ = Λ' := by
    refine hΛ'.uniq Λ ?_
    exact isPCompIn_of_le hΛ.pcW (le_inf hΛK' (hΛ.pcW.1.trans inf_le_left))
      (le_inf inf_le_right (inf_le_left.trans hK'c.1))
  refine ⟨Λ, hΛ, hΛK', hcover, hR3, hxC, fun g hg h2 => ?_⟩
  rw [hΛΛ']
  exact hΛ'.twoElt g hg h2


end Triv

section KQ

variable {G : Type} [Group G]

@[expose] def kQ (K Q : Subgroup G) : Subgroup G :=
  oPrimeResidualOf 2 (K ⊓ centralizer (Q : Set G))

@[expose] def bigC (K Q : Subgroup G) : Subgroup G :=
  normalizer (Q : Set G) ⊓ centralizerSection (kQ K Q) (pPrimeCoreOf 2 (kQ K Q))

theorem kQ_le (K Q : Subgroup G) : kQ K Q ≤ K ⊓ centralizer (Q : Set G) :=
  oPrimeResidualOf_le_self 2 _

theorem le_bigC [Finite G] {K Q : Subgroup G} : Q ≤ bigC K Q := by
  intro q hq
  have hcomm : ∀ k ∈ kQ K Q, q * k = k * q := fun k hk =>
    Subgroup.mem_centralizer_iff.mp (kQ_le K Q hk).2 q hq
  have hcent : q ∈ centralizer (kQ K Q : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun k hk => (hcomm k hk).symm
  have hN : q ∈ normalizer (kQ K Q : Set G) :=
    Subgroup.centralizer_le_normalizer (kQ K Q : Set G) hcent
  refine ⟨Subgroup.le_normalizer hq, hN, mem_normalizer_pPrimeCoreOf hN, fun k hk => ?_⟩
  have : ⁅k, q⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr (hcomm k hk).symm
  rw [this]
  exact one_mem _

end KQ

section Pumpup

variable {G : Type} [Group G] [Finite G] {x z : G} {K K' Q Λ : Subgroup G}

omit [Finite G] in
theorem kQ_eq (T : TrivData x z K K' Λ) (hxQ : x ∈ Q) (hzQ : z ∈ Q) :
    kQ K Q = oPrimeResidualOf 2 (K' ⊓ centralizer (Q : Set G)) := by
  refine le_antisymm (oPrimeResidualOf_mono_of_two_elt fun g hg k hk => ?_)
    (oPrimeResidualOf_mono_of_two_elt fun g hg k hk => ?_)
  · have hgz : g ∈ centralizer ({z} : Set G) :=
      mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hg.2 z hzQ).symm
    have hgΛ : g ∈ Λ := T.lam.twoElt g ⟨hg.1, hgz⟩ ⟨k, hk⟩
    exact ⟨T.le hgΛ, hg.2⟩
  · have hgx : g ∈ centralizer ({x} : Set G) :=
      mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hg.2 x hxQ).symm
    have hgΛ : g ∈ Λ := T.twoElt g ⟨hg.1, hgx⟩ ⟨k, hk⟩
    exact ⟨(T.lam.le hgΛ).1, hg.2⟩

omit [Finite G] in
theorem kQ_le_of_trivData (T : TrivData x z K K' Λ) (hxQ : x ∈ Q) (hzQ : z ∈ Q) :
    kQ K Q ≤ K' := by
  rw [kQ_eq T hxQ hzQ]
  exact (oPrimeResidualOf_le_self 2 _).trans inf_le_left

theorem kQ_cover (T : TrivData x z K K' Λ) (hK'c : IsPCompIn 2 (centralizer ({z} : Set G)) K')
    (hQC : Q ≤ CxK x K) (hQ2 : IsPGroup 2 Q) (hxQ : x ∈ Q) (hzQ : z ∈ Q)
    (hzc : ∀ q ∈ Q, z * q = q * z) :
    ∀ k ∈ K', ∃ p ∈ kQ K Q, ∃ o ∈ pPrimeCoreOf 2 K', k = p * o := by
  set O := pPrimeCoreOf 2 K' with hO
  set N₀ : Subgroup G := Λ ⊓ O with hN₀
  have hQcent : ∀ q ∈ Q, q ∈ CxK z K' := fun q hq => T.cent q (hQC hq) (hzc q hq)
  have hQΛ : ∀ q ∈ Q, q ∈ normalizer (Λ : Set G) := fun q hq =>
    PumpRigid.mem_normalizer_lam T.lam (mem_centralizer_singleton_iff.mpr (hzc q hq).symm)
      (hQC hq).2.1
  have hodd : Odd (Nat.card N₀) :=
    Odd.of_dvd_nat (TwoThin.card_pPrimeCoreOf_odd K') (Subgroup.card_dvd_of_le inf_le_right)
  have hPN : ∀ p ∈ Q, ∀ n ∈ N₀, p * n * p⁻¹ ∈ N₀ := fun p hp n hn =>
    ⟨(Subgroup.mem_normalizer_iff.mp (hQΛ p hp) n).mp hn.1,
      (Subgroup.mem_normalizer_iff.mp (mem_normalizer_pPrimeCoreOf (hQcent p hp).2.1) n).mp hn.2⟩
  have hD : ∀ k ∈ K', ∃ d ∈ Λ ⊓ centralizer (Q : Set G), ∃ o ∈ O, k = d * o := by
    intro k hk
    obtain ⟨l, hl, o, ho, rfl⟩ := T.cover k hk
    have hcomm : ∀ p ∈ Q, l⁻¹ * (p * l * p⁻¹) ∈ N₀ := by
      intro p hp
      have h1 : p * l * p⁻¹ ∈ Λ := (Subgroup.mem_normalizer_iff.mp (hQΛ p hp) l).mp hl
      have h3 : l⁻¹ ∈ Λ := inv_mem hl
      refine ⟨mul_mem h3 h1, ?_⟩
      have h2 := (hQcent p hp).2.2.2 l⁻¹ (T.le (inv_mem hl))
      have e : ⁅l⁻¹, p⁆ = l⁻¹ * (p * l * p⁻¹) := by
        simp only [commutatorElement_def]; group
      rwa [e] at h2
    obtain ⟨n, hn, hnc⟩ := exists_mul_mem_centralizer_of_odd hQ2 hodd hPN hcomm
    refine ⟨l * n, ⟨mul_mem hl hn.1, Subgroup.mem_centralizer_iff.mpr fun p hp => hnc p hp⟩,
      n⁻¹ * o, mul_mem (inv_mem hn.2) ho, by group⟩
  have hDK : Λ ⊓ centralizer (Q : Set G) ≤ K' := inf_le_left.trans T.le
  have hle : K' ≤ kQ K Q ⊔ O := by
    refine PumpRigid.le_of_forall_two_elt hK'c fun t ht ⟨a, hta⟩ => ?_
    obtain ⟨d, hd, o', ho', htd⟩ := hD t ht
    obtain ⟨e, he, hea, o, ho, hto⟩ := exists_two_elt_mul hDK ht hd ho' htd hta
    have heK : e ∈ kQ K Q := by
      rw [kQ_eq T hxQ hzQ]
      exact mem_oPrimeResidualOf ⟨hDK he, he.2⟩ hea
    rw [hto]
    exact mul_mem (Subgroup.mem_sup_left heK) (Subgroup.mem_sup_right ho)
  intro k hk
  have hkQ : kQ K Q ≤ normalizer (O : Set G) := fun p hp =>
    mem_normalizer_pPrimeCoreOf (Subgroup.le_normalizer (kQ_le_of_trivData T hxQ hzQ hp))
  have := hle hk
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hkQ] at this
  obtain ⟨p, hp, o, ho, hpo⟩ := this
  exact ⟨p, hp, o, ho, hpo.symm⟩

theorem mem_CxK_of_mem_bigC (T : TrivData x z K K' Λ)
    (hK'c : IsPCompIn 2 (centralizer ({z} : Set G)) K') (hQC : Q ≤ CxK x K) (hQ2 : IsPGroup 2 Q)
    (hxQ : x ∈ Q) (hzQ : z ∈ Q) (hzc : ∀ q ∈ Q, z * q = q * z) {s : G} (hs : s ∈ bigC K Q)
    (hsz : s ∈ centralizer ({z} : Set G)) : s ∈ CxK z K' := by
  have hcov := kQ_cover T hK'c hQC hQ2 hxQ hzQ hzc
  have hkK' : kQ K Q ≤ K' := kQ_le_of_trivData T hxQ hzQ
  have hsQ : s ∈ normalizer (kQ K Q : Set G) := hs.2.1
  have hsinv : ∀ p ∈ kQ K Q, s⁻¹ * p * s ∈ kQ K Q := fun p hp => by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hsQ) p).mp hp
    simpa using this
  have hK''c := isPCompIn_conj_of_mem_normalizer hK'c (Subgroup.le_normalizer hsz)
  have hkK'' : kQ K Q ≤ K'.map (MulAut.conj s).toMonoidHom := fun p hp =>
    ⟨s⁻¹ * p * s, hkK' (hsinv p hp), by simp [MulAut.conj_apply]; group⟩
  have hEq : K' = K'.map (MulAut.conj s).toMonoidHom :=
    eq_of_isPCompIn_of_cover hK'c hK''c hkK' hkK'' hcov
  have hsK' : s ∈ normalizer (K' : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hEq.symm
  have hsO : s ∈ normalizer (pPrimeCoreOf 2 K' : Set G) := mem_normalizer_pPrimeCoreOf hsK'
  refine ⟨hsz, hsK', hsO, fun k hk => ?_⟩
  obtain ⟨p, hp, o, ho, rfl⟩ := hcov k hk
  have hpK' : p ∈ K' := hkK' hp
  have h1 : ⁅p, s⁆ ∈ pPrimeCoreOf 2 K' :=
    pPrimeCoreOf_le_of_cover hkK' hcov (hs.2.2.2 p hp)
  have h2 : ⁅o, s⁆ ∈ pPrimeCoreOf 2 K' := by
    have e : ⁅o, s⁆ = o * (s * o⁻¹ * s⁻¹) := by simp only [commutatorElement_def]; group
    rw [e]
    exact mul_mem ho ((Subgroup.mem_normalizer_iff.mp hsO _).mp (inv_mem ho))
  have e2 : ⁅p * o, s⁆ = p * ⁅o, s⁆ * p⁻¹ * ⁅p, s⁆ := by
    simp only [commutatorElement_def]; group
  rw [e2]
  exact mul_mem (TwoThin.pPrimeCoreOf_normalized K' hpK' h2) h1

theorem mem_bigC_of_mem_CxK (T : TrivData x z K K' Λ) (hxQ : x ∈ Q) (hzQ : z ∈ Q) {s : G}
    (hs : s ∈ CxK z K') (hsN : s ∈ normalizer (Q : Set G)) : s ∈ bigC K Q := by
  have hkK' : kQ K Q ≤ K' := kQ_le_of_trivData T hxQ hzQ
  have hsK' : s ∈ normalizer (K' : Set G) := hs.2.1
  have hsX : s ∈ normalizer ((K' ⊓ centralizer (Q : Set G) : Subgroup G) : Set G) :=
    TwoThin.mem_normalizer_inf hsK' (mem_normalizer_centralizer hsN)
  have hsQ : s ∈ normalizer (kQ K Q : Set G) := by
    rw [kQ_eq T hxQ hzQ]
    exact le_normalizer_oPrimeResidualOf (H := Subgroup.zpowers s)
      (Subgroup.zpowers_le.mpr hsX) (Subgroup.mem_zpowers s)
  refine ⟨hsN, hsQ, mem_normalizer_pPrimeCoreOf hsQ, fun k hk => ?_⟩
  have h1 : ⁅k, s⁆ ∈ pPrimeCoreOf 2 K' := hs.2.2.2 k (hkK' hk)
  have h2 : ⁅k, s⁆ ∈ kQ K Q := by
    have e : ⁅k, s⁆ = k * (s * k⁻¹ * s⁻¹) := by simp only [commutatorElement_def]; group
    rw [e]
    exact mul_mem hk ((Subgroup.mem_normalizer_iff.mp hsQ _).mp (inv_mem hk))
  exact inf_pPrimeCoreOf_le hkK' ⟨h2, h1⟩

end Pumpup

section Normalizer

variable {G : Type} [Group G] {K Q : Subgroup G}

theorem le_normalizer_bigC {V : Subgroup G} (hVK : V ≤ normalizer (K : Set G))
    (hVQ : V ≤ normalizer (Q : Set G)) : V ≤ normalizer ((bigC K Q : Subgroup G) : Set G) := by
  intro v hv
  have hvX : v ∈ normalizer ((K ⊓ centralizer (Q : Set G) : Subgroup G) : Set G) :=
    TwoThin.mem_normalizer_inf (hVK hv) (mem_normalizer_centralizer (hVQ hv))
  have hvkQ : v ∈ normalizer (kQ K Q : Set G) :=
    le_normalizer_oPrimeResidualOf (H := Subgroup.zpowers v)
      (Subgroup.zpowers_le.mpr hvX) (Subgroup.mem_zpowers v)
  have hvN : v ∈ normalizer ((normalizer (Q : Set G) : Subgroup G) : Set G) :=
    Subgroup.le_normalizer (hVQ hv)
  have hvS : v ∈ normalizer ((centralizerSection (kQ K Q) (pPrimeCoreOf 2 (kQ K Q)) :
      Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro c
    constructor
    · intro hc
      exact conj_mem_cSec hvkQ hc
    · intro hc
      have := conj_mem_cSec (inv_mem hvkQ) hc
      simpa [mul_assoc] using this
  exact TwoThin.mem_normalizer_inf hvN hvS

end Normalizer




end CFSG.GH74.GLS.C3.Layer1.Iv251
