module

public import CFSG.RankThree.PartOne.SPOR.Co1FiveFixed
public import CFSG.RankThree.PartOne.SPOR.Co1SylowGenSound
public import Certificates.Certificate1322150
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo1FiveA
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo1FiveB
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo1FiveC
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo1Census
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1Thirteen
public import Certificates.Certificate13670

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3.SporBig

open CFSG.Blueprint.NativeSporadic
open CFSG.RankThree.PartOne.SPOR
open CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Block
open CFSG.HardMathSupport.Dickson.I271 CFSG.HardMathSupport.Dickson.I271.TabCo1
open CFSG.HardMathSupport.Dickson.I271.TabCo1FiveA
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1F
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1Thirteen

private theorem card_center_mulEquiv {G H : Type} [Group G] [Group H] (e : G ≃* H) :
    Nat.card (Subgroup.center G) = Nat.card (Subgroup.center H) := by
  let c : Subgroup.center G ≃* Subgroup.center H := Subgroup.centerCongr e
  let ee : ↥(Subgroup.center G) ≃ ↥(Subgroup.center H) := c.toEquiv
  exact Nat.card_congr ee

private theorem center_card_eq_five {G : Type} [Group G] [Finite G] {P : Subgroup G} {x : G}
    (hP : Nat.card ↥P = 625) (hx5 : x ^ 5 = 1)
    (hZ : ∀ z ∈ P, (∀ y ∈ P, z * y = y * z) → z ∈ Subgroup.zpowers x) :
    Nat.card (Subgroup.center ↥P) = 5 := by
  have hnt : Nontrivial ↥P := by
    rw [← Finite.one_lt_card_iff_nontrivial, hP]; norm_num
  have hP5 : IsPGroup 5 ↥P := IsPGroup.of_card (n := 4) (by rw [hP]; norm_num)
  have : Nontrivial ↥P := hnt
  have hZnt : Nontrivial (Subgroup.center ↥P) := IsPGroup.center_nontrivial hP5
  have hmemZ : ∀ z : ↥(Subgroup.center ↥P), (z.1 : G) ∈ Subgroup.zpowers x := by
    intro z
    exact hZ _ z.1.2 fun y hy => by
      have h := Subgroup.mem_center_iff.1 z.2 (⟨y, hy⟩ : ↥P)
      exact (Subtype.ext_iff.1 h).symm
  have hle : Nat.card ↥(Subgroup.center ↥P) ≤ Nat.card ↥(Subgroup.zpowers x) := by
    refine Nat.card_le_card_of_injective
      (fun z : ↥(Subgroup.center ↥P) => (⟨(z.1 : G), hmemZ z⟩ : ↥(Subgroup.zpowers x))) ?_
    intro a b hab
    exact Subtype.ext (Subtype.ext (congrArg (fun z : ↥(Subgroup.zpowers x) => (z : G)) hab))
  have hx1 : x ≠ 1 := by
    rintro rfl
    obtain ⟨z, hz⟩ := exists_ne (1 : ↥(Subgroup.center ↥P))
    have h1 : (z.1 : G) = 1 := by simpa using hmemZ z
    exact hz (Subtype.ext (Subtype.ext h1))
  have h5 : Nat.card ↥(Subgroup.center ↥P) ≤ 5 := by
    calc Nat.card ↥(Subgroup.center ↥P) ≤ Nat.card ↥(Subgroup.zpowers x) := hle
      _ = 5 := by rw [Nat.card_zpowers, orderOf_eq_prime hx5 hx1]
  have hgt : 1 < Nat.card ↥(Subgroup.center ↥P) :=
    Finite.one_lt_card_iff_nontrivial.mpr hZnt
  have hdvd : Nat.card ↥(Subgroup.center ↥P) ∣ 5 ^ 4 := by
    have h := Subgroup.card_dvd_of_le (le_top : Subgroup.center ↥P ≤ ⊤)
    rw [Subgroup.card_top, hP] at h
    rwa [show (625 : ℕ) = 5 ^ 4 by norm_num] at h
  obtain ⟨k, hk4, hk⟩ := (Nat.dvd_prime_pow Nat.prime_five).1 hdvd
  have hk1 : k = 1 := by
    have hgt' : 1 < 5 ^ k := hk ▸ hgt
    have h5' : 5 ^ k ≤ 5 := hk ▸ h5
    have hle' : k ≤ 1 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 5)).1 h5'
    have hpos : 0 < k := by
      rcases Nat.eq_zero_or_pos k with hk0 | h
      · rw [hk0] at hgt'; norm_num at hgt'
      · exact h
    omega
  rw [hk, hk1]; norm_num

private theorem fiveA_card_cent_dvd
    (x : ↥GA)
    (hx : MRep repD0 (x : GL24)) :
    604800 ∣ Nat.card ↥(Subgroup.centralizer ({x} : Set ↥GA)) := by
  obtain ⟨hk, -, -, hku, hkv, hu1, hw1, hw2, hw3, -⟩ := fiveA_data
  obtain ⟨h1, h2, h3⟩ := relators_of_wordG hw1 hw2 hw3
  have hLcard : Nat.card ↥(Subgroup.closure ({kG ext 89, kG ext 90} : Set GL24)) = 604800 := by
    obtain ⟨e⟩ := nonempty_mulEquiv_J2_of_relators (kG ext 89) (kG ext 90)
      (Subgroup.closure ({kG ext 89, kG ext 90} : Set GL24)) rfl h1 h2 _ rfl h3 hu1
    rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.J2.card_J2]
  have hxeq : (x : GL24) = kG ext 88 := hx.eq hk
  have hsub : Subgroup.closure ({kG ext 89, kG ext 90} : Set GL24) ≤
      Subgroup.centralizer ({(x : GL24)} : Set GL24) ⊓ GA := by
    refine (Subgroup.closure_le _).2 ?_
    intro y hy
    rcases hy with rfl | rfl
    · exact Subgroup.mem_inf.2
        ⟨Subgroup.mem_centralizer_singleton_iff.2 (by rw [hxeq]; exact hku.symm), kG_mem ext 89⟩
    · exact Subgroup.mem_inf.2
        ⟨Subgroup.mem_centralizer_singleton_iff.2 (by rw [hxeq]; exact hkv.symm), kG_mem ext 90⟩
  have hdvd : 604800 ∣ Nat.card ↥(Subgroup.centralizer ({(x : GL24)} : Set GL24) ⊓ GA) :=
    hLcard ▸ Subgroup.card_dvd_of_le hsub
  rw [← map_centralizer_subtype' GA x,
    Subgroup.card_map_of_injective (f := GA.subtype) GA.subtype_injective] at hdvd
  exact hdvd

private theorem fiveB_card_cent_dvd
    (x : ↥GA) (hx : MRep repD1 (x : GL24)) :
    36000 ∣ Nat.card ↥(Subgroup.centralizer ({x} : Set ↥GA)) := by
  obtain ⟨k, x₁, y₁, τ, hk, hkGA, hx₁, hy₁, hτ, -, -, hkx, hky, hkt, -, -, -, -, -, -, -,
    -, hE, -, -⟩ := fiveB_data
  have hxeq : (x : GL24) = k := hx.eq hk
  have hsub : Subgroup.closure ({k, x₁, y₁, τ} : Set GL24) ≤
      Subgroup.centralizer ({(x : GL24)} : Set GL24) ⊓ GA := by
    refine (Subgroup.closure_le _).2 ?_
    intro y hy
    rcases hy with rfl | rfl | rfl | rfl
    · exact Subgroup.mem_inf.2
        ⟨Subgroup.mem_centralizer_singleton_iff.2 (by rw [hxeq]), hkGA⟩
    · exact Subgroup.mem_inf.2
        ⟨Subgroup.mem_centralizer_singleton_iff.2 (by rw [hxeq]; exact hkx.symm), hx₁⟩
    · exact Subgroup.mem_inf.2
        ⟨Subgroup.mem_centralizer_singleton_iff.2 (by rw [hxeq]; exact hky.symm), hy₁⟩
    · exact Subgroup.mem_inf.2
        ⟨Subgroup.mem_centralizer_singleton_iff.2 (by rw [hxeq]; exact hkt.symm), hτ⟩
  have hdvd : 36000 ∣ Nat.card ↥(Subgroup.centralizer ({(x : GL24)} : Set GL24) ⊓ GA) :=
    hE ▸ Subgroup.card_dvd_of_le hsub
  rw [← map_centralizer_subtype' GA x,
    Subgroup.card_map_of_injective (f := GA.subtype) GA.subtype_injective] at hdvd
  exact hdvd

private theorem fiveC_card_cent_eq
    (x : ↥GA) (hx : MRep repZ (x : GL24)) :
    Nat.card ↥(Subgroup.centralizer ({x} : Set ↥GA)) = 15000 := by
  obtain ⟨z, t₁, t₂, s₁, s₂, hz, -, -, -, hs₁, hs₂, -, -, hzs₁, hzs₂, -, -, hbd, hC, -⟩ :=
    fiveC_data
  have hxeq : (x : GL24) = z := hx.eq hz
  have hC' : Nat.card ↥(Subgroup.centralizer ({(x : GL24)} : Set GL24) ⊓ GA) = 15000 := by
    refine le_antisymm ?_ ?_
    · rw [hxeq]; exact hbd
    · refine hC.trans (Subgroup.card_le_of_le ?_)
      refine (Subgroup.closure_le _).2 ?_
      intro y hy
      rcases hy with rfl | rfl
      · exact Subgroup.mem_inf.2
          ⟨Subgroup.mem_centralizer_singleton_iff.2 (by rw [hxeq]; exact hzs₁), hs₁⟩
      · exact Subgroup.mem_inf.2
          ⟨Subgroup.mem_centralizer_singleton_iff.2 (by rw [hxeq]; exact hzs₂), hs₂⟩
  rw [← Subgroup.card_map_of_injective (f := GA.subtype) GA.subtype_injective,
    map_centralizer_subtype' GA x]
  exact hC'

theorem card_center_sylow_Co1
    {L : Type} [Group L] [Finite L]
    (e : L ≃* Carrier .Co1) :
    ∀ Q : Sylow 5 L, Nat.card (Subgroup.center ↥(Q : Subgroup L)) = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hfin : Finite (Carrier .Co1) := CFSG.Sporadic.Co1.fam_co1_simplicity.1
  obtain ⟨P, x, hPcard, hx5, hZ⟩ := co1_sylow_centre
  have hfac : (Nat.card (Carrier .Co1)).factorization 5 = 4 := by
    change (Nat.card CFSG.Blueprint.NativeSporadic.Co1).factorization 5 = 4
    have hco1 : Nat.card CFSG.Blueprint.NativeSporadic.Co1 = 4157776806543360000 :=
      CFSG.Sporadic.Co1.card_Co1
    rw [hco1]
    have hnum : (4157776806543360000 : ℕ) = 5 ^ 4 * 6652442890469376 := by norm_num
    rw [hnum, Nat.factorization_mul (by positivity) (by positivity), Finsupp.add_apply,
      Nat.Prime.factorization_pow (by norm_num), Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]
  let S : Sylow 5 (Carrier .Co1) := Sylow.ofCard P (by rw [hPcard, hfac]; norm_num)
  have hScenter : Nat.card (Subgroup.center ↥(S : Subgroup (Carrier .Co1))) = 5 :=
    center_card_eq_five hPcard hx5 hZ
  intro Q
  let Qe : Sylow 5 (Carrier .Co1) := Q.mapSurjective (f := e.toMonoidHom) e.surjective
  have h1 : Nat.card (Subgroup.center ↥(Q : Subgroup L)) =
      Nat.card (Subgroup.center ↥((Q : Subgroup L).map e.toMonoidHom)) :=
    card_center_mulEquiv (MulEquiv.subgroupMap e (Q : Subgroup L))
  have h2 : Nat.card (Subgroup.center ↥((Q : Subgroup L).map e.toMonoidHom)) =
      Nat.card (Subgroup.center ↥(S : Subgroup (Carrier .Co1))) :=
    card_center_mulEquiv (Sylow.equiv Qe S)
  rw [h1, h2, hScenter]

theorem exists_sylow_generators_Co1
    {L : Type} [Group L] [Finite L]
    (e : L ≃* Carrier .Co1) :
    ∃ g₁ g₂ : L, g₁ ^ 5 = 1 ∧ g₂ ^ 5 = 1 ∧
      Nat.card (Subgroup.closure ({g₁, g₂} : Set L)) = 5 ^ 4 := by
  obtain ⟨a₁, a₂, h1, h2, h3⟩ := co1SylowGen_sound co1Iota co1Iota_injective
    co1_base_rep co1_base_mem co1_sylow_check Certificates.certificate1322150
  set b₁ : Carrier .Co1 := a₁ with hb₁
  set b₂ : Carrier .Co1 := a₂ with hb₂
  have h1' : b₁ ^ 5 = 1 := h1
  have h2' : b₂ ^ 5 = 1 := h2
  have h3' : Nat.card (Subgroup.closure ({b₁, b₂} : Set (Carrier .Co1))) = 625 := h3
  refine ⟨e.symm b₁, e.symm b₂, ?_, ?_, ?_⟩
  · rw [← map_pow, h1', map_one]
  · rw [← map_pow, h2', map_one]
  · have hmap : Subgroup.map e.symm.toMonoidHom
        (Subgroup.closure ({b₁, b₂} : Set (Carrier .Co1))) =
        Subgroup.closure ({e.symm b₁, e.symm b₂} : Set L) := by
      rw [MonoidHom.map_closure, Set.image_pair]
      simp only [MulEquiv.coe_toMonoidHom]
    rw [← hmap,
      Subgroup.card_map_of_injective (f := e.symm.toMonoidHom) e.symm.injective, h3']
    norm_num

theorem card_centralizer_Co1_of_five_central
    {L : Type} [Group L] [Finite L]
    (e : L ≃* Carrier .Co1) {z : L} (hz : orderOf z = 5)
    (h54 : 5 ^ 4 ∣ Nat.card (Subgroup.centralizer ({z} : Set L))) :
    Nat.card (Subgroup.centralizer ({z} : Set L)) = 15000 := by
  have hG : GOK := Certificates.certificate13670
  have hcard : Nat.card (Subgroup.centralizer ({z} : Set L)) =
      Nat.card (Subgroup.centralizer ({co1MatEquiv (e z)} : Set ↥GA)) :=
    (card_centralizer_mulEquiv e z).symm.trans (card_centralizer_co1 (e z))
  have hs5 : orderOf (co1MatEquiv (e z)) = 5 :=
    (orderOf_co1MatEquiv (e z)).trans ((MulEquiv.orderOf_eq e z).trans hz)
  have h54s : 5 ^ 4 ∣ Nat.card (Subgroup.centralizer ({co1MatEquiv (e z)} : Set ↥GA)) :=
    hcard ▸ h54
  obtain ⟨c, hc | hc | hc⟩ := tabCo1_census hG (co1MatEquiv (e z)) hs5
  · exfalso
    have hdvd : 604800 ∣
        Nat.card (Subgroup.centralizer ({co1MatEquiv (e z)} : Set ↥GA)) :=
      (card_centralizer_conj c (co1MatEquiv (e z))) ▸ fiveA_card_cent_dvd _ hc
    have hlcm : 15120000 ∣
        Nat.card (Subgroup.centralizer ({co1MatEquiv (e z)} : Set ↥GA)) := by
      have h := Nat.lcm_dvd hdvd h54s
      have hnum : Nat.lcm 604800 (5 ^ 4) = 15120000 := by norm_num
      rwa [hnum] at h
    have hupper : Nat.card (Subgroup.centralizer ({co1MatEquiv (e z)} : Set ↥GA)) ≤ 3024000 :=
      (card_centralizer_conj c (co1MatEquiv (e z))).symm.le.trans (card_cent_fiveA_le _ hc)
    have := Nat.le_of_dvd (by norm_num) hlcm
    omega
  · exfalso
    have hdvd : 36000 ∣
        Nat.card (Subgroup.centralizer ({co1MatEquiv (e z)} : Set ↥GA)) :=
      (card_centralizer_conj c (co1MatEquiv (e z))) ▸ fiveB_card_cent_dvd _ hc
    have hlcm : 180000 ∣
        Nat.card (Subgroup.centralizer ({co1MatEquiv (e z)} : Set ↥GA)) := by
      have h := Nat.lcm_dvd hdvd h54s
      have hnum : Nat.lcm 36000 (5 ^ 4) = 180000 := by norm_num
      rwa [hnum] at h
    have hupper : Nat.card (Subgroup.centralizer ({co1MatEquiv (e z)} : Set ↥GA)) ≤ 36000 :=
      (card_centralizer_conj c (co1MatEquiv (e z))).symm.le.trans (card_cent_fiveB_le _ hc)
    have := Nat.le_of_dvd (by norm_num) hlcm
    omega
  · have heq : Nat.card (Subgroup.centralizer ({co1MatEquiv (e z)} : Set ↥GA)) = 15000 :=
      (card_centralizer_conj c (co1MatEquiv (e z))).symm.trans (fiveC_card_cent_eq _ hc)
    rw [hcard, heq]

theorem card_centralizer_Co1_thirteen
    {L : Type} [Group L] [Finite L]
    (e : L ≃* Carrier .Co1) {x : L} (hx : orderOf x = 13) :
    Nat.card (Subgroup.centralizer ({x} : Set L)) = 156 := by
  have hx13 : orderOf (e x) = 13 := by rw [MulEquiv.orderOf_eq]; exact hx
  have h := (co1_thirteen_facts (e x) hx13).1
  exact (card_centralizer_mulEquiv e x).symm.trans h

end CFSG.LocalAnalysis.AGL81I.Section3.SporBig
