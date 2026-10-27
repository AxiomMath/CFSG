module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.BorelLocal

import CFSG.RankThree.PartOne.S12.Sec1511SPEFStar
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SignalizerTrivialSporadicBase
import CFSG.GroupTheory.SteinbergBSFixedPointFree
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.NormalizerLeNormalizerCentralizer
import CFSG.Quasithin.Vol2.Ch3E213MKer
import CFSG.Quasithin.EmptyFaithfulMultiple.L3213Basic

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KFTwo

open CFSG.Open
open scoped commutatorElement

variable {X : Type*} [Group X] [Finite X] {p : ℕ}

theorem relIndex_sup_zpowers_eq [Fact p.Prime] {R Z : Subgroup X}
    (hZleR : Z ≤ R) (hZC : Z ≤ Subgroup.centralizer (R : Set X))
    (hexp : ∀ r ∈ R, r ^ p = 1) (hcardR : Nat.card R = p ^ 2 * Nat.card Z)
    {r : X} (hrR : r ∈ R) (hrZ : r ∉ Z) :
    (Subgroup.zpowers r ⊔ Z).relIndex R = p := by
  have hp : p.Prime := Fact.out
  have hcard := CFSG.RankThree.PartOne.Planes.card_sup_zpowers (G := X) hp Z
    (hexp r hrR) hrZ (fun e he => (Subgroup.mem_centralizer_iff.mp (hZC he) r hrR).symm)
  rw [sup_comm, Nat.mul_comm] at hcard
  have hWR : Subgroup.zpowers r ⊔ Z ≤ R := sup_le (Subgroup.zpowers_le.mpr hrR) hZleR
  have hinf : (Subgroup.zpowers r ⊔ Z) ⊓ R = Subgroup.zpowers r ⊔ Z :=
    le_antisymm inf_le_left (le_inf le_rfl hWR)
  have hmul := Subgroup.relIndex_mul_card (Subgroup.zpowers r ⊔ Z) R
  rw [hinf, hcard, hcardR] at hmul
  have h1 : (Subgroup.zpowers r ⊔ Z).relIndex R * (p * Nat.card Z) = p * (p * Nat.card Z) := by
    rw [hmul]; ring
  exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hp.pos Nat.card_pos) h1

theorem exists_normal_subgroup_relIndex_eq_of_three_element [Fact p.Prime]
    {R Z : Subgroup X} (hZleR : Z ≤ R) (hZC : Z ≤ Subgroup.centralizer (R : Set X))
    (hcomm : ⁅R, R⁆ ≤ Z) (hexp : ∀ r ∈ R, r ^ p = 1)
    (hcardR : Nat.card R = p ^ 2 * Nat.card Z)
    {e r : X} (hrR : r ∈ R) (hrZ : r ∉ Z) (hre : r * e = e * r)
    (hZe : Z ≤ Subgroup.centralizer ({e} : Set X)) :
    ∃ W : Subgroup X, W ≤ R ∧ R ≤ Subgroup.normalizer (W : Set X) ∧
      W ≤ Subgroup.centralizer ({e} : Set X) ∧ W.relIndex R = p := by
  have hWleR : Subgroup.zpowers r ⊔ Z ≤ R := sup_le (Subgroup.zpowers_le.mpr hrR) hZleR
  have hWn : R ≤ Subgroup.normalizer ((Subgroup.zpowers r ⊔ Z : Subgroup X) : Set X) := by
    rw [Subgroup.le_normalizer_iff_commutator_le_right]
    exact (Subgroup.commutator_mono le_rfl hWleR).trans (hcomm.trans le_sup_right)
  have hWe : Subgroup.zpowers r ⊔ Z ≤ Subgroup.centralizer ({e} : Set X) :=
    sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hre)) hZe
  exact ⟨_, hWleR, hWn, hWe, relIndex_sup_zpowers_eq hZleR hZC hexp hcardR hrR hrZ⟩

theorem quotient_congr_eq_one_of_relIndex_eq_prime [Fact p.Prime] (hp : ¬ 3 ∣ p - 1)
    {R W : Subgroup X} [(W.subgroupOf R).Normal] (hrel : W.relIndex R = p)
    (φ : MulAut ↥R) (hφW : (W.subgroupOf R).map (φ : ↥R →* ↥R) = W.subgroupOf R)
    (hφ3 : φ ^ 3 = 1) :
    QuotientGroup.congr (W.subgroupOf R) (W.subgroupOf R) φ hφW = 1 := by
  classical
  have hquotcard : Nat.card (↥R ⧸ W.subgroupOf R) = p := by
    rw [← Subgroup.index_eq_card]
    exact hrel
  let ψ : MulAut (↥R ⧸ W.subgroupOf R) :=
    QuotientGroup.congr (W.subgroupOf R) (W.subgroupOf R) φ hφW
  have hψ3 : ψ ^ 3 = 1 := by
    apply MulEquiv.ext
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    have h := CFSG.GroupTheory.SteinbergBS.quotientCongr_pow_mk φ (W.subgroupOf R) hφW 3 x
    simpa [ψ, hφ3] using h
  have hψdvd3 : orderOf ψ ∣ 3 := orderOf_dvd_of_pow_eq_one hψ3
  have hψcard : Nat.card (MulAut (↥R ⧸ W.subgroupOf R)) = p - 1 := by
    haveI : IsCyclic (↥R ⧸ W.subgroupOf R) := isCyclic_of_prime_card hquotcard
    rw [IsCyclic.card_mulAut, hquotcard, Nat.totient_prime (Fact.out : p.Prime)]
  have hψdvd : orderOf ψ ∣ p - 1 := by
    have := orderOf_dvd_natCard ψ
    rwa [hψcard] at this
  have hψ1 : ψ = 1 := by
    rw [← orderOf_eq_one_iff]
    exact Nat.eq_one_of_dvd_coprimes ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr hp)
      hψdvd3 hψdvd
  simpa [ψ] using hψ1

theorem eq_one_of_fixed_inf_of_relIndex_eq_prime [Fact p.Prime] (hp3 : p ≠ 3)
    (hp : ¬ 3 ∣ p - 1) {R W : Subgroup X} (hR : IsPGroup p R) (hWR : W ≤ R)
    (hWn : R ≤ Subgroup.normalizer (W : Set X)) (hrel : W.relIndex R = p)
    (φ : MulAut ↥R) (hφ3 : φ ^ 3 = 1)
    (hfix : ∀ w ∈ W.subgroupOf R, φ w = w) : φ = 1 := by
  classical
  have hφW : (W.subgroupOf R).map (φ : ↥R →* ↥R) = W.subgroupOf R := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · intro y hy
      obtain ⟨w, hw, rfl⟩ := hy
      show φ w ∈ W.subgroupOf R
      rw [hfix w hw]
      exact hw
    · exact le_of_eq (Subgroup.card_map_of_injective φ.injective).symm
  haveI : (W.subgroupOf R).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hWn
  have hψ1 := quotient_congr_eq_one_of_relIndex_eq_prime hp hrel φ hφW hφ3
  have hdisp : ∀ x : ↥R, x⁻¹ * φ x ∈ W.subgroupOf R := by
    intro x
    have hq : (QuotientGroup.congr (W.subgroupOf R) (W.subgroupOf R) φ hφW)
        (QuotientGroup.mk x) = QuotientGroup.mk x := by
      rw [hψ1]
      rfl
    rw [QuotientGroup.congr_mk] at hq
    exact (QuotientGroup.eq (s := W.subgroupOf R)).mp hq.symm
  have hcop : Nat.Coprime 3 (Nat.card (W.subgroupOf R)) := by
    have hcard : Nat.card (W.subgroupOf R) = Nat.card W :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWR).toEquiv
    rw [hcard]
    obtain ⟨n, hn⟩ := (hR.to_le hWR).exists_card_eq
    rw [hn]
    have hpc : Nat.Coprime p 3 :=
      (Nat.coprime_primes (Fact.out : p.Prime) (by norm_num)).mpr hp3
    exact hpc.symm.pow_right n
  exact CFSG.ComponentClassification.CoprimeAutomorphisms.eq_one_of_fixed_displacement
    (W.subgroupOf R) φ 3 hφ3 hcop hfix hdisp

theorem centralizes_of_relIndex_eq_prime [Fact p.Prime] (hp3 : p ≠ 3) (hp : ¬ 3 ∣ p - 1)
    {R W : Subgroup X} {e : X} (hR : IsPGroup p R) (hWR : W ≤ R)
    (hWn : R ≤ Subgroup.normalizer (W : Set X)) (hrel : W.relIndex R = p)
    (hWe : W ≤ Subgroup.centralizer ({e} : Set X))
    (he : e ∈ Subgroup.normalizer (R : Set X)) (he3 : e ^ 3 = 1) :
    e ∈ Subgroup.centralizer (R : Set X) := by
  classical
  let φ : MulAut ↥R := (Subgroup.normalizerMonoidHom R) ⟨e, he⟩
  have hpow : (⟨e, he⟩ : ↥(Subgroup.normalizer (R : Set X))) ^ 3 = 1 := by
    apply Subtype.ext
    simpa using he3
  have hφ3 : φ ^ 3 = 1 := by
    rw [← map_pow]
    simpa using congrArg (Subgroup.normalizerMonoidHom R) hpow
  have hfix : ∀ w ∈ W.subgroupOf R, φ w = w := by
    intro w hw
    have hwW : (w : X) ∈ W := Subgroup.mem_subgroupOf.mp hw
    have hcommw : (w : X) * e = e * (w : X) :=
      Subgroup.mem_centralizer_singleton_iff.mp (hWe hwW)
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    calc e * (w : X) * e⁻¹ = (w : X) * e * e⁻¹ := by rw [hcommw]
      _ = (w : X) := by group
  have hφ1 : φ = 1 :=
    eq_one_of_fixed_inf_of_relIndex_eq_prime hp3 hp hR hWR hWn hrel φ hφ3 hfix
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hφx : ((φ ⟨x, hx⟩ : ↥R) : X) = e * x * e⁻¹ := by
    simp only [φ, MulEquiv.coe_toMonoidHom, Subgroup.normalizerMonoidHom_apply_apply_coe]
  have hxfix : ((φ ⟨x, hx⟩ : ↥R) : X) = x := by
    rw [hφ1]
    rfl
  rw [hφx] at hxfix
  calc x * e = (e * x * e⁻¹) * e := by rw [hxfix]
    _ = e * x := by group

theorem inf_centralizer_singleton_eq_of_three_element [Fact p.Prime] (hp3 : p ≠ 3)
    (hp : ¬ 3 ∣ p - 1) {R Z : Subgroup X} (hR : IsPGroup p R)
    (hC : Subgroup.centralizer (R : Set X) ≤ R)
    (hZleR : Z ≤ R) (hZC : Z ≤ Subgroup.centralizer (R : Set X))
    (hZcard : Nat.card Z = 1 ∨ Nat.card Z = p)
    (hcomm : ⁅R, R⁆ ≤ Z) (hexp : ∀ r ∈ R, r ^ p = 1)
    (hcardR : Nat.card R = p ^ 2 * Nat.card Z)
    {e : X} (he : e ∈ Subgroup.normalizer (R : Set X)) (he3 : e ^ 3 = 1) (he1 : e ≠ 1)
    (hZe : Z ≤ Subgroup.centralizer ({e} : Set X)) :
    R ⊓ Subgroup.centralizer ({e} : Set X) = Z := by
  refine le_antisymm ?_ (le_inf hZleR hZe)
  rintro r ⟨hrR, hre⟩
  by_contra hrZ
  have hre' : r * e = e * r := Subgroup.mem_centralizer_singleton_iff.mp hre
  obtain ⟨W, hWR, hWn, hWe, hrel⟩ :=
    exists_normal_subgroup_relIndex_eq_of_three_element hZleR hZC hcomm hexp hcardR
      hrR hrZ hre' hZe
  have hcent := centralizes_of_relIndex_eq_prime hp3 hp hR hWR hWn hrel hWe he he3
  have heR : e ∈ R := hC hcent
  have hpc : p.Coprime 3 :=
    (Nat.coprime_primes (Fact.out : p.Prime) (by norm_num)).mpr hp3
  have hcope : (orderOf (⟨e, heR⟩ : ↥R)).Coprime 3 := hR.orderOf_coprime hpc _
  rw [← Subgroup.orderOf_coe] at hcope
  rw [orderOf_eq_prime he3 he1] at hcope
  exact absurd hcope (by norm_num : ¬ Nat.Coprime 3 3)

theorem le_centralizer_of_three_element [Fact p.Prime] (hp : ¬ 3 ∣ p - 1)
    {Z E : Subgroup X} (hZcard : Nat.card Z = 1 ∨ Nat.card Z = p)
    (hEZ : E ≤ Subgroup.normalizer (Z : Set X))
    (hEab : CFSG.Open.IsElemAbelian 3 E) :
    Z ≤ Subgroup.centralizer (E : Set X) := by
  have hcop3 : Nat.Coprime 3 (p - 1) :=
    (Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr hp
  rcases hZcard with hZ1 | hZp
  · rw [Subgroup.card_eq_one.mp hZ1]
    exact bot_le
  · intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    have h3 : orderOf e ∣ 3 := orderOf_dvd_of_pow_eq_one (hEab.2 e he)
    have hcop : Nat.Coprime (orderOf e) (p - 1) := Nat.Coprime.of_dvd_left h3 hcop3
    exact CFSG.Quasithin.EmptyFaithfulMultiple.L3213.commute_of_normalizes_of_coprime
      hZp hcop (hEZ he) z hz

theorem inf_centralizer_singleton_eq_of_isElemAbelian [Fact p.Prime] (hp3 : p ≠ 3)
    (hp : ¬ 3 ∣ p - 1) {R Z E : Subgroup X} (hR : IsPGroup p R)
    (hC : Subgroup.centralizer (R : Set X) ≤ R)
    (hZleR : Z ≤ R) (hZC : Z ≤ Subgroup.centralizer (R : Set X))
    (hZcard : Nat.card Z = 1 ∨ Nat.card Z = p)
    (hcomm : ⁅R, R⁆ ≤ Z) (hexp : ∀ r ∈ R, r ^ p = 1)
    (hcardR : Nat.card R = p ^ 2 * Nat.card Z)
    (hZcentE : Z ≤ Subgroup.centralizer (E : Set X))
    (hE : E ≤ Subgroup.normalizer (R : Set X))
    (hEab : CFSG.Open.IsElemAbelian 3 E) {e : ↥E} (he1 : e ≠ 1) :
    R ⊓ Subgroup.centralizer ({(e : X)} : Set X) = Z := by
  have hZe : Z ≤ Subgroup.centralizer ({(e : X)} : Set X) := by
    intro z hz
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp (hZcentE hz) (e : X) e.2).symm
  exact inf_centralizer_singleton_eq_of_three_element hp3 hp hR hC hZleR hZC hZcard hcomm hexp
    hcardR (hE e.2) (hEab.2 (e : X) e.2) (by intro h; exact he1 (Subtype.ext h)) hZe

theorem card_dvd_sub_of_free_action {R Z E : Subgroup X}
    (hZleR : Z ≤ R) (hE : E ≤ Subgroup.normalizer (R : Set X))
    (hZcentE : Z ≤ Subgroup.centralizer (E : Set X))
    (hcent : ∀ e : ↥E, e ≠ 1 → R ⊓ Subgroup.centralizer ({(e : X)} : Set X) = Z) :
    Nat.card E ∣ Nat.card R - Nat.card Z := by
  classical
  letI : E.Normalizes R := ⟨hE⟩
  letI : MulDistribMulAction ↥E ↥R := Subgroup.conjMulDistribMulActionOfLeNormalizer E R hE
  have hC : ∀ e : ↥E, ∀ x ∈ ({r : ↥R | (r : X) ∈ Z} : Set ↥R),
      e • x ∈ ({r : ↥R | (r : X) ∈ Z} : Set ↥R) := by
    intro e x hx
    have hcomm : (e : X) * (x : X) = (x : X) * (e : X) :=
      Subgroup.mem_centralizer_iff.mp (hZcentE hx) (e : X) e.2
    show ((e • x : ↥R) : X) ∈ Z
    rw [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, hcomm]
    simpa using hx
  have hfix : ∀ e : ↥E, e ≠ 1 → ∀ x : ↥R, e • x = x →
      x ∈ ({r : ↥R | (r : X) ∈ Z} : Set ↥R) := by
    intro e he1 x hx
    have hcoe : (e : X) * (x : X) * (e : X)⁻¹ = (x : X) := by
      have h := congrArg (fun z : ↥R => (z : X)) hx
      simpa [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] using h
    have hmem : (x : X) ∈ R ⊓ Subgroup.centralizer ({(e : X)} : Set X) := by
      refine Subgroup.mem_inf.mpr ⟨x.2, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc (x : X) * e = ((e : X) * (x : X) * (e : X)⁻¹) * e := by rw [hcoe]
        _ = e * (x : X) := by group
    obtain ⟨h1, h2⟩ := Subgroup.mem_inf.mp hmem
    rw [← hcent e he1]
    exact ⟨h1, h2⟩
  have hdvd := CFSG.Quasithin.Ch3E213M.card_dvd_card_sub_of_fixed_subset
    (K := ↥E) (β := ↥R) (C := {r : ↥R | (r : X) ∈ Z}) hC hfix
  rwa [show Nat.card {r : ↥R | (r : X) ∈ Z} = Nat.card Z from
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZleR).toEquiv] at hdvd

theorem pRank_three_normalizer_le_one [Fact p.Prime] (hp : p = 5 ∨ p = 11)
    {R Z E : Subgroup X} (hR : IsPGroup p R)
    (hC : Subgroup.centralizer (R : Set X) ≤ R)
    (hZleR : Z ≤ R) (hZC : Z ≤ Subgroup.centralizer (R : Set X))
    (hZcard : Nat.card Z = 1 ∨ Nat.card Z = p)
    (hcomm : ⁅R, R⁆ ≤ Z) (hexp : ∀ r ∈ R, r ^ p = 1)
    (hcardR : Nat.card R = p ^ 2 * Nat.card Z)
    (hE : E ≤ Subgroup.normalizer (R : Set X))
    (hEZ : E ≤ Subgroup.normalizer (Z : Set X))
    (hEab : CFSG.Open.IsElemAbelian 3 E) : Nat.card E ≤ 3 := by
  classical
  have hp3 : p ≠ 3 := by
    rcases hp with rfl | rfl <;> norm_num
  have hp31 : ¬ 3 ∣ p - 1 := by
    rcases hp with rfl | rfl <;> norm_num
  have hZcentE := le_centralizer_of_three_element hp31 hZcard hEZ hEab
  have hcent : ∀ e : ↥E, e ≠ 1 → R ⊓ Subgroup.centralizer ({(e : X)} : Set X) = Z :=
    fun e he1 => inf_centralizer_singleton_eq_of_isElemAbelian hp3 hp31 hR hC hZleR hZC hZcard
      hcomm hexp hcardR hZcentE hE hEab he1
  have hdvd := card_dvd_sub_of_free_action hZleR hE hZcentE hcent
  have hEp : IsPGroup 3 ↥E := by
    intro e
    exact ⟨1, by
      apply Subtype.ext
      simpa using hEab.2 (e : X) e.2⟩
  by_contra hle
  have hEcard : 3 < Nat.card E := by omega
  obtain ⟨k, hk⟩ := hEp.exists_card_eq
  have hk2 : 2 ≤ k := by
    by_contra h
    have hk1 : k ≤ 1 := by omega
    interval_cases k <;> norm_num [hk] at hEcard
  have h9 : 9 ∣ Nat.card E := by
    rw [show Nat.card E = Nat.card ↥E from rfl, hk]
    refine ⟨3 ^ (k - 2), ?_⟩
    rw [show (9 : ℕ) = 3 ^ 2 by norm_num, ← pow_add, Nat.add_sub_cancel' hk2]
  have h9dvd : 9 ∣ Nat.card R - Nat.card Z := h9.trans hdvd
  rcases hZcard with hZ1 | hZp
  · rcases hp with rfl | rfl
    · rw [hcardR, hZ1, Nat.mul_one] at h9dvd
      norm_num at h9dvd
    · rw [hcardR, hZ1, Nat.mul_one] at h9dvd
      norm_num at h9dvd
  · rcases hp with rfl | rfl
    · rw [hcardR, hZp] at h9dvd
      norm_num at h9dvd
    · rw [hcardR, hZp] at h9dvd
      norm_num at h9dvd

theorem eq_normalizer_and_isSolvable_of_maximal [Fact p.Prime] {N : Subgroup X}
    (hN : CFSG.RankThree.PartOne.IsStronglyPEmbedded p N) {R : Sylow p X}
    (hRN : (R : Subgroup X) ≤ N) (hRne : (R : Subgroup X) ≠ ⊥)
    (hmax : ∀ Y : Subgroup X, Subgroup.normalizer ((R : Subgroup X) : Set X) ≤ Y →
      Y = Subgroup.normalizer ((R : Subgroup X) : Set X) ∨ Y = ⊤)
    (hsolv : Group.IsSolvable (Subgroup.normalizer ((R : Subgroup X) : Set X))) :
    N = Subgroup.normalizer ((R : Subgroup X) : Set X) ∧ Group.IsSolvable ↥N := by
  have hMleN : Subgroup.normalizer ((R : Subgroup X) : Set X) ≤ N :=
    hN.normalizer_le hRne R.isPGroup' hRN
  rcases hmax N hMleN with h | h
  · exact ⟨h, h ▸ hsolv⟩
  · exact absurd h hN.1

theorem isSolvable_and_pRank_three_self_le_one_of_d2HeisLocalAt {i : TauCeti.CFSGIndex} {p : ℕ}
    [Fact p.Prime] (hp : p = 5 ∨ p = 11)
    (H : CFSG.AGLEmbeddingD2.D2HeisLocalAt i fun q => q = p)
    {X : Type} [Group X] [Finite X] (hO : CFSG.pPrimeCore p X = ⊥) {N : Subgroup X}
    (hN : CFSG.RankThree.PartOne.IsStronglyPEmbedded p N)
    (e : ↥(CFSG.generalizedFitting X) ≃* i.Group) :
    Group.IsSolvable ↥N ∧ CFSG.Open.pRank 3 N ≤ 1 := by
  classical
  set K : Subgroup X := CFSG.generalizedFitting X with hKdef
  obtain ⟨hKs, hKnab, hKn, hKC⟩ :=
    CFSG.RankThree.PartOne.Sec1511.spe_fstar (p := p) Fact.out hO hN
  haveI : K.Normal := hKn
  obtain ⟨P, hPsyl, hPN⟩ := hN.exists_isSylowOf_le
  let R : Sylow p X := hPsyl.2.1.toSylow (by simpa [Subgroup.relIndex_top_right] using hPsyl.2.2)
  have hRcoe : (R : Subgroup X) = P :=
    IsPGroup.toSylow_coe hPsyl.2.1 (by simpa [Subgroup.relIndex_top_right] using hPsyl.2.2)
  have hRN : (R : Subgroup X) ≤ N := hRcoe ▸ hPN
  obtain ⟨hout, hcard, hmax, hC, hZ, hcomm, hexp, hsolv, hlines⟩ :=
    H X K hKn hKC ⟨e⟩ p rfl R
  have hRne : (R : Subgroup X) ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card (R : Subgroup X) = 1 := by rw [hbot]; exact Subgroup.card_bot
    rw [hcard] at h1
    have h8 : 8 ≤ p ^ 3 :=
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ p ^ 3 := Nat.pow_le_pow_left (Fact.out : p.Prime).two_le 3
    omega
  obtain ⟨hNM, hNsolv⟩ := eq_normalizer_and_isSolvable_of_maximal hN hRN hRne hmax hsolv
  refine ⟨hNsolv, ?_⟩
  have hrank : CFSG.Open.pRank 3 N ≤ 1 := by
    rw [hNM]
    refine CFSG.SectionRank.pRank_le (by norm_num) ?_
    intro E hE hEab
    have hEZ : E ≤ Subgroup.normalizer
        ((R : Subgroup X) ⊓ Subgroup.centralizer ((R : Subgroup X) : Set X) : Subgroup X) := by
      have h2 : E ≤ Subgroup.normalizer
          (Subgroup.centralizer ((R : Subgroup X) : Set X) : Set X) :=
        hE.trans (CFSG.GorensteinWalter.normalizer_le_normalizer_centralizer_subgroup
          (R : Subgroup X))
      exact (le_inf hE h2).trans Subgroup.inf_normalizer_le_normalizer_inf
    have hcardE := pRank_three_normalizer_le_one (Z := (R : Subgroup X) ⊓
        Subgroup.centralizer ((R : Subgroup X) : Set X)) (E := E) hp R.isPGroup' hC
      inf_le_left inf_le_right (Or.inr hZ) (le_of_eq hcomm) hexp ?_ hE hEZ hEab
    · simpa using hcardE
    · rw [hcard, hZ]; ring
  exact hrank

theorem isSolvable_and_pRank_three_le_one_of_d2HeisLocalAt {i : TauCeti.CFSGIndex} {p : ℕ}
    [Fact p.Prime] (hp : p = 5 ∨ p = 11)
    (H : CFSG.AGLEmbeddingD2.D2HeisLocalAt i fun q => q = p)
    {X : Type} [Group X] [Finite X] (hO : CFSG.pPrimeCore p X = ⊥) {N : Subgroup X}
    (hN : CFSG.RankThree.PartOne.IsStronglyPEmbedded p N)
    (e : ↥(CFSG.generalizedFitting X) ≃* i.Group) :
    Group.IsSolvable ↥N ∧ CFSG.Open.pRank 3 ⁅N, N⁆ ≤ 1 := by
  have h := isSolvable_and_pRank_three_self_le_one_of_d2HeisLocalAt hp H hO hN e
  exact ⟨h.1, (CFSG.SectionRank.pRank_mono (by norm_num)
    (Subgroup.commutator_le_self N)).trans h.2⟩

theorem isSolvable_and_pRank_three_self_le_one_of_d2TorusLocalAt {i : TauCeti.CFSGIndex}
    (H : CFSG.AGLEmbeddingD2.D2TorusLocalAt i fun q => q = 5)
    {X : Type} [Group X] [Finite X] (hO : CFSG.pPrimeCore 5 X = ⊥) {N : Subgroup X}
    (hN : CFSG.RankThree.PartOne.IsStronglyPEmbedded 5 N)
    (e : ↥(CFSG.generalizedFitting X) ≃* i.Group) :
    Group.IsSolvable ↥N ∧ CFSG.Open.pRank 3 N ≤ 1 := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set K : Subgroup X := CFSG.generalizedFitting X with hKdef
  obtain ⟨hKs, hKnab, hKn, hKC⟩ :=
    CFSG.RankThree.PartOne.Sec1511.spe_fstar (p := 5) (by norm_num) hO hN
  haveI : K.Normal := hKn
  obtain ⟨P, hPsyl, hPN⟩ := hN.exists_isSylowOf_le
  let R : Sylow 5 X := hPsyl.2.1.toSylow (by simpa [Subgroup.relIndex_top_right] using hPsyl.2.2)
  have hRcoe : (R : Subgroup X) = P :=
    IsPGroup.toSylow_coe hPsyl.2.1 (by simpa [Subgroup.relIndex_top_right] using hPsyl.2.2)
  have hRN : (R : Subgroup X) ≤ N := hRcoe ▸ hPN
  obtain ⟨hout, hcard, hmax, hC, hsolv, htorus⟩ := H X K hKn hKC ⟨e⟩ 5 rfl R
  obtain ⟨t, htN, m, lam, ee, hm, hlam, he, hpow, hinv, hline⟩ := htorus
  have hTpow : ∀ x ∈ (R : Subgroup X), x ^ 5 = 1 :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SignalizerTrivial.pow_eq_one_of_torus
      (by norm_num) hcard htN (fun Y₀ hY₀ hY₀c => by
        simpa using hline 1 one_pos (by omega) Y₀ hY₀ hY₀c)
  have hRne : (R : Subgroup X) ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hcard
    norm_num at hcard
  obtain ⟨hNM, hNsolv⟩ := eq_normalizer_and_isSolvable_of_maximal hN hRN hRne hmax hsolv
  refine ⟨hNsolv, ?_⟩
  have hcomm0 : ⁅(R : Subgroup X), (R : Subgroup X)⁆ ≤ (⊥ : Subgroup X) := by
    rw [le_bot_iff, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact congrArg Subtype.val
      (IsPGroup.commutative_of_card_eq_prime_sq hcard ⟨b, hb⟩ ⟨a, ha⟩)
  have hrank : CFSG.Open.pRank 3 N ≤ 1 := by
    rw [hNM]
    refine CFSG.SectionRank.pRank_le (by norm_num) ?_
    intro E hE hEab
    have hcardE := pRank_three_normalizer_le_one (Z := ⊥) (E := E) (Or.inl rfl)
      R.isPGroup' hC bot_le bot_le (Or.inl (by simp)) hcomm0 hTpow ?_ hE
      (fun x hx => by
        rw [Subgroup.mem_normalizer_iff]
        intro y
        simp) hEab
    · simpa using hcardE
    · rw [hcard, Subgroup.card_bot, mul_one]
  exact hrank

theorem isSolvable_and_pRank_three_le_one_of_d2TorusLocalAt {i : TauCeti.CFSGIndex}
    (H : CFSG.AGLEmbeddingD2.D2TorusLocalAt i fun q => q = 5)
    {X : Type} [Group X] [Finite X] (hO : CFSG.pPrimeCore 5 X = ⊥) {N : Subgroup X}
    (hN : CFSG.RankThree.PartOne.IsStronglyPEmbedded 5 N)
    (e : ↥(CFSG.generalizedFitting X) ≃* i.Group) :
    Group.IsSolvable ↥N ∧ CFSG.Open.pRank 3 ⁅N, N⁆ ≤ 1 := by
  have h := isSolvable_and_pRank_three_self_le_one_of_d2TorusLocalAt H hO hN e
  exact ⟨h.1, (CFSG.SectionRank.pRank_mono (by norm_num)
    (Subgroup.commutator_le_self N)).trans h.2⟩

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KFTwo
