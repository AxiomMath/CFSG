module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93CovArith
public import CFSG.GH74.GLS.Stage2.Local.P34Bar
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.GH74.Generic.S3.V1InnerUni
public import CFSG.GH74.KGroups.L33
public import CFSG.GH74.KGroups.U33

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.ComponentClassification
open CFSG.GH74.KGroups.L3Eps (InvData tInv tInv_mul_self tInv_ne_one blockSub blockEmb_injective
  isQuasisimple_blockSub blockSub_le_centralizer conj_mem_blockSub commutator_mem_blockSub
  subgroupOfEquiv mem_subgroupOfEquiv exists_projectiveSL_equiv)
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL)
open scoped MatrixGroups commutatorElement

namespace Ivk93Cov

variable {J : Type} [Group J] [Finite J] {x : J} {n : ℕ} {B : Subgroup J}

theorem eq_of_normal_quasisimple (h : Ivk93Cov x n B) {S : Subgroup J} (hSq : CFSG.IsQuasisimple ↥S)
    (hle : S ≤ centralizer ({x} : Set J))
    (hconj : ∀ y ∈ centralizer ({x} : Set J), ∀ s ∈ S, y * s * y⁻¹ ∈ S)
    (hcomm : ∀ a ∈ centralizer ({x} : Set J), ∀ b ∈ centralizer ({x} : Set J), ⁅a, b⁆ ∈ S) :
    B = S := by
  have hBS : B ≤ S := by
    have hp : ⁅B, B⁆ = B := Subgroup.isPerfect_iff.mp h.perfect
    rw [← hp]
    exact Subgroup.commutator_le.mpr fun a ha b hb => hcomm a (h.le ha) b (h.le hb)
  set C : Subgroup J := centralizer ({x} : Set J) with hC
  have hSN : (S.subgroupOf C).Normal := by
    refine ⟨fun s hs y => ?_⟩
    have := hconj (y : J) y.2 (s : J) hs
    exact this
  have hSq' : CFSG.IsQuasisimple ↥(S.subgroupOf C) :=
    LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hle).symm hSq
  have hI : CFSG.IsComponent (S.subgroupOf C) := ⟨hSq', hSN.isSubnormal⟩
  have hAsub : (B.subgroupOf C).IsSubnormal := h.comp.2.choose_spec.2.1
  have hperfA : Group.IsPerfect ↥(B.subgroupOf C) := CatalogueBAlternating.pComponent_perfect h.comp.2
  have hntA : Nontrivial ↥(B.subgroupOf C) := CatalogueBAlternating.pComponent_nontrivial h.comp.2
  have hle' : B.subgroupOf C ≤ S.subgroupOf C := fun y hy => hBS hy
  rcases CFSG.LocalCores.component_subnormal_subgroup hI hAsub with h1 | h1
  · exact le_antisymm hBS (fun y hy => h1 (show (⟨y, hle hy⟩ : ↥C) ∈ S.subgroupOf C from hy))
  · exfalso
    have hcomm' : ∀ u v : ↥(B.subgroupOf C), u * v = v * u := by
      intro u v
      have h3 : ⁅(v : ↥C), (u : ↥C)⁆ ∈ ⁅S.subgroupOf C, B.subgroupOf C⁆ :=
        Subgroup.commutator_mem_commutator (hle' v.2) u.2
      rw [h1, Subgroup.mem_bot] at h3
      exact Subtype.ext ((commutatorElement_eq_one_iff_mul_comm.1 h3).symm)
    exact Group.IsPerfect.not_isSolvable ↥(B.subgroupOf C) (Group.isSolvable_of_comm hcomm')

end Ivk93Cov

theorem ivk93cov_l3_data {J : Type} [Group J] {F : Type} [Field F] [Finite F] (h2 : (2 : F) ≠ 0)
    (h4 : 4 ≤ Nat.card F) (e : J ≃* projectiveSL 3 F) {t : J} (ht : e t = tInv) :
    ∃ S : Subgroup J, CFSG.IsQuasisimple ↥S ∧ Nonempty (SL(2, F) ≃* ↥S) ∧
      S ≤ centralizer ({t} : Set J) ∧
      (∀ y ∈ centralizer ({t} : Set J), ∀ s ∈ S, y * s * y⁻¹ ∈ S) ∧
      (∀ a ∈ centralizer ({t} : Set J), ∀ b ∈ centralizer ({t} : Set J), ⁅a, b⁆ ∈ S) := by
  have hcen : ∀ y : J, y ∈ centralizer ({t} : Set J) ↔
      e y ∈ centralizer ({tInv} : Set (projectiveSL 3 F)) := by
    intro y
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff, ← ht,
      ← map_mul, ← map_mul]
    exact ⟨fun h => by rw [h], fun h => e.injective h⟩
  have hmem : ∀ y : J, y ∈ blockSub.map (e.symm : projectiveSL 3 F →* J) ↔ e y ∈ blockSub := by
    intro y
    exact Subgroup.mem_map_equiv (f := e.symm) (K := blockSub) (x := y)
  refine ⟨blockSub.map (e.symm : projectiveSL 3 F →* J), ?_, ?_, ?_, ?_, ?_⟩
  · exact LocalCores.isQuasisimple_of_mulEquiv (MulEquiv.subgroupMap e.symm blockSub)
      (isQuasisimple_blockSub h4)
  · exact ⟨(MonoidHom.ofInjective (blockEmb_injective (F := F))).trans
      (MulEquiv.subgroupMap e.symm blockSub)⟩
  · intro s hs
    rw [hmem] at hs
    rw [hcen]
    exact blockSub_le_centralizer hs
  · intro y hy s hs
    rw [hcen] at hy
    rw [hmem] at hs ⊢
    rw [map_mul, map_mul, map_inv]
    exact conj_mem_blockSub h2 hy hs
  · intro a ha b hb
    rw [hcen] at ha hb
    rw [hmem, map_commutatorElement]
    exact commutator_mem_blockSub h2 ha hb

theorem ivk93cov_eq_three {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (h : p ^ f = 3) : p = 3 ∧ f = 1 := by
  have hp3 : p = 3 := by
    have : p ∣ 3 := h ▸ dvd_pow_self p (by omega : f ≠ 0)
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 this
  subst hp3
  exact ⟨rfl, Nat.pow_right_injective (by norm_num : 2 ≤ 3) (show 3 ^ f = 3 ^ 1 by simpa using h)⟩

theorem ivk93cov_five_le_pow {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (h3 : p ^ f ≠ 3) :
    5 ≤ p ^ f := by
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have h1 : 3 ≤ p ^ f := hp3.trans (Nat.le_self_pow (by omega) p)
  have h2 : p ^ f % 2 = 1 := Nat.odd_iff.mp ((hp.odd_of_ne_two hp2).pow)
  omega

theorem ivk93cov_l3 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f →
    Ivk93CovEmpty (fun X _ => LieModel X .PSL 3 p f) := by
  intro p f hp hp2 hf
  refine ivk93cov_empty_of_cfg fun J _ _ hJ x _ n B hc => ?_
  by_cases hq3 : p ^ f = 3
  · obtain ⟨rfl, rfl⟩ := ivk93cov_eq_three hp hf hq3
    obtain ⟨e⟩ := KGroups.L33.equiv_of_lieModel hJ
    have hcard : Nat.card J = 5616 := by
      rw [Nat.card_congr e.toEquiv, KGroups.card_group KGroups.L33.QP KGroups.L33.QP_ok,
        KGroups.L33.QP_valid.2]
    exact hc.false_of_card_group_lt (by rw [hcard]; norm_num)
  · have h5 := ivk93cov_five_le_pow hp hp2 hf hq3
    have hst := CFSG.GH74.Generic.stated_of_lieModel_PSL hJ
    obtain ⟨F, _, _, hF, ⟨e⟩⟩ := exists_projectiveSL_equiv hst
    have hodd : Odd (Nat.card F) := by
      rw [hF]
      exact (hp.odd_of_ne_two hp2).pow
    have h2 : (2 : F) ≠ 0 := CFSG.ABGLocalTools.two_ne_zero_of_odd_card hodd
    have h5' : 5 ≤ Nat.card F := by
      rw [hF]
      exact h5
    have hex2 : e x * e x = 1 := by rw [← map_mul, hc.mul_self_eq_one, map_one]
    have hex1 : e x ≠ 1 := fun h1 => hc.ne_one (e.injective (h1.trans (map_one e).symm))
    obtain ⟨g, hg⟩ := Generic.S3.singleInv_projectiveSL h2 (e x) tInv hex2 hex1 tInv_mul_self
      (tInv_ne_one h2)
    let e' : J ≃* projectiveSL 3 F := e.trans (MulAut.conj g)
    have he' : e' x = tInv := by
      show MulAut.conj g (e x) = tInv
      rw [MulAut.conj_apply]
      exact hg
    obtain ⟨S, hSq, ⟨eS⟩, hSle, hconj, hcomm⟩ := ivk93cov_l3_data h2 (by omega) e' he'
    have hBS := hc.eq_of_normal_quasisimple hSq hSle hconj hcomm
    exact hc.false_of_equiv_sl2 hodd h5' (eS.trans (MulEquiv.subgroupCongr hBS.symm))

theorem ivk93cov_u3 :
    ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f →
    Ivk93CovEmpty (fun X _ => LieModel X .PSU 3 p f) := by
  intro p f hp hp2 hf
  refine ivk93cov_empty_of_cfg fun J _ _ hJ x _ n B hc => ?_
  by_cases hq3 : p ^ f = 3
  · obtain ⟨rfl, rfl⟩ := ivk93cov_eq_three hp hf hq3
    obtain ⟨e⟩ := KGroups.U33.equiv_of_lieModel hJ
    have hcard : Nat.card J = 6048 := by
      rw [Nat.card_congr e.toEquiv, KGroups.card_group KGroups.U33.QP KGroups.U33.QP_ok,
        KGroups.U33.QP_valid.2]
    exact hc.false_of_card_group_lt (by rw [hcard]; norm_num)
  · have h5 := ivk93cov_five_le_pow hp hp2 hf hq3
    have hst := CFSG.GH74.Generic.stated_of_lieModel_PSU hJ
    obtain ⟨S, hInv⟩ := ((Generic.S3.libData_uni hp hp2 h5) J hst).1 x hc.mul_self_eq_one hc.ne_one
    have hBS := hc.eq_of_normal_quasisimple hInv.quasisimple hInv.le_centralizer hInv.conj_mem
      hInv.commutator_mem
    subst hBS
    have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
    have hev : 2 ∣ Nat.card ↥B := by
      rw [hInv.card]
      exact Dvd.dvd.mul_left (even_iff_two_dvd.mp (Nat.Odd.sub_odd hodd.pow odd_one)) _
    have hN : (pPrimeCore 2 ↥B).Normal := inferInstance
    have hcop : Nat.Coprime 2 (Nat.card ↥(pPrimeCore 2 ↥B)) :=
      CFSG.pPrimeCore_coprime_card (p := 2) (G := ↥B)
    have hO : pPrimeCore 2 ↥B = ⊥ := by
      rcases LocalCores.quasisimple_normal_subgroups hInv.quasisimple hN with h0 | h0
      · exfalso
        have h1 : Nat.card ↥(pPrimeCore 2 ↥B) = Nat.card ↥B := by
          rw [h0]
          exact Subgroup.card_top
        rw [h1] at hcop
        exact absurd (Nat.Coprime.eq_one_of_dvd hcop hev) (by
          have := hc.card_ge_big
          omega)
      · rw [eq_bot_iff]
        intro o ho
        rw [Subgroup.mem_bot]
        have hoc : o ∈ center ↥B := h0 ho
        have hodd' : Odd (orderOf o) :=
          CFSG.GH74.GLS.Stage2.Local.P34.odd_orderOf_of_mem_pPrimeCore ho
        have hmem : (o : J) = 1 ∨ (o : J) = x := hInv.center o hoc
        rcases hmem with h1 | h1
        · exact Subtype.ext h1
        · exfalso
          have h2 : orderOf o = 2 := by
            rw [← Subgroup.orderOf_coe, h1]
            exact hc.ord
          rw [h2] at hodd'
          exact absurd hodd' (by decide)
    exact hc.false_of_card_sl2 hO hInv.card

end CFSG.GH74.GLS.IVK.Proofs2
