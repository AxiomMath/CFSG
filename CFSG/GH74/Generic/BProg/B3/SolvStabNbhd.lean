module

public import CFSG.GH74.Generic.BProg.B3.SolvLift
public import CFSG.GH74.GLS.Balance.SL23Ext

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.GH74.Generic.BProg.B1
  Subgroup
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G]

namespace SolvStabNbhd

theorem exists_sl23_anticomm : ∃ s t m : SL(2, ZMod 3), s ^ 4 = 1 ∧ t ^ 4 = 1 ∧ s * t = t * s * m ∧
    m ≠ 1 ∧ m ^ 2 = 1 := by
  obtain ⟨s, t, m, hs, ht, hst, hm0, hm2⟩ : ∃ s t m : SL(2, ZMod 3), s ^ 4 = 1 ∧ t ^ 4 = 1 ∧
      s * t = t * s * m ∧ (m : Matrix (Fin 2) (Fin 2) (ZMod 3)) 0 0 = 2 ∧ m ^ 2 = 1 :=
    ⟨⟨!![0, 1; 2, 0], by decide⟩, ⟨!![1, 1; 1, 2], by decide⟩, ⟨!![2, 0; 0, 2], by decide⟩,
      by decide, by decide, by decide, by decide, by decide⟩
  refine ⟨s, t, m, hs, ht, hst, ?_, hm2⟩
  rintro rfl
  simp at hm0
  exact absurd hm0 (by decide)

theorem exists_twoElts_not_mem_odd [Finite G] {I1 : Subgroup G} (π : ↥I1 →* SL(2, ZMod 3))
    (hπ : Function.Surjective π) :
    ∃ a ∈ I1, ∃ b ∈ I1, (∃ k : ℕ, a ^ (2 ^ k) = 1) ∧ (∃ k : ℕ, b ^ (2 ^ k) = 1) ∧
      ∀ O : Subgroup G, Odd (Nat.card ↥O) → (b * a)⁻¹ * (a * b) ∉ O := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨s, t, m, hs, ht, hst, hm1, hm2⟩ := exists_sl23_anticomm
  obtain ⟨s', hs'⟩ := hπ s
  obtain ⟨t', ht'⟩ := hπ t
  obtain ⟨n, e, hne, hn⟩ := exists_pow_two_power_lift π s' (k := 2) (by rw [hs']; simpa using hs)
  obtain ⟨n', e', hne', hn'⟩ := exists_pow_two_power_lift π t' (k := 2) (by rw [ht']; simpa using ht)
  set a' : ↥I1 := s' ^ n with ha'
  set b' : ↥I1 := t' ^ n' with hb'
  refine ⟨(a' : G), a'.2, (b' : G), b'.2, ⟨e, ?_⟩, ⟨e', ?_⟩, ?_⟩
  · have := congrArg Subtype.val hne
    simpa using this
  · have := congrArg Subtype.val hne'
    simpa using this
  · intro O hO hmem
    set c : ↥I1 := (b' * a')⁻¹ * (a' * b') with hc
    have hcG : ((c : ↥I1) : G) = ((b' : G) * a')⁻¹ * ((a' : G) * b') := by
      simp [hc]
    have hπc : π c = m := by
      rw [hc, map_mul, map_inv, map_mul, map_mul, hn, hn', hs', ht', hst, mul_inv_rev,
        ← mul_assoc, ← mul_assoc]
      group
    have hodd : Odd (orderOf (c : G)) :=
      Odd.of_dvd_nat hO (Subgroup.orderOf_dvd_natCard O (hcG ▸ hmem))
    rw [Subgroup.orderOf_coe] at hodd
    have hm : orderOf m = 2 := orderOf_eq_prime hm2 hm1
    have h2 : orderOf (π c) ∣ orderOf c := orderOf_map_dvd π c
    rw [hπc, hm] at h2
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h2)

theorem centralizer_closure_le {x y d : G} (hd : d ∈ closure ({x, y} : Set G)) :
    centralizer ((closure ({x, y} : Set G) : Subgroup G) : Set G) ≤ centralizer ({d} : Set G) :=
  Subgroup.centralizer_le (Set.singleton_subset_iff.2 hd)

theorem conj_mem_centralizer_pPrimeCoreOf {d k z : G} (hk : k ∈ centralizer ({d} : Set G))
    (hz : z ∈ centralizer ((pPrimeCoreOf 2 (centralizer ({d} : Set G)) : Subgroup G) : Set G)) :
    k * z * k⁻¹ ∈ centralizer ((pPrimeCoreOf 2 (centralizer ({d} : Set G)) : Subgroup G) : Set G) := by
  set W : Subgroup G := pPrimeCoreOf 2 (centralizer ({d} : Set G)) with hW
  have hkd : k⁻¹ ∈ centralizer ({d} : Set G) := Subgroup.inv_mem _ hk
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  have hw' : k⁻¹ * w * k⁻¹⁻¹ ∈ W := CFSG.GH74.GLS.TwoThin.pPrimeCoreOf_normalized _ hkd hw
  have hzw : k⁻¹ * w * k⁻¹⁻¹ * z = z * (k⁻¹ * w * k⁻¹⁻¹) := Subgroup.mem_centralizer_iff.1 hz _ hw'
  calc w * (k * z * k⁻¹) = k * (k⁻¹ * w * k⁻¹⁻¹ * z) * k⁻¹ := by group
    _ = k * (z * (k⁻¹ * w * k⁻¹⁻¹)) * k⁻¹ := by rw [hzw]
    _ = (k * z * k⁻¹) * w := by group

end SolvStabNbhd

open SolvStabNbhd in
theorem nbhdSemisimple_of_centralizes [Finite G] {x y : G} {K E : Subgroup G}
    {Lb Ib : Subgroup (CentralizerBar x)} {I0 I1 : Subgroup G} (hx : orderOf x = 2)
    (hK : IsPCompIn 2 (centralizer ({x} : Set G)) K) (h : SolvAdm x y K E Lb Ib)
    (hI : SolvLift x y E Lb I0 I1)
    (hc : ∀ d ∈ closure ({x, y} : Set G), d ≠ 1 → ⁅I0, pPrimeCoreOf 2 (centralizer ({d} : Set G))⁆ = ⊥) :
    NbhdSemisimple x y Lb := by
  have _hx := hx
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro d hd hd1
  set W : Subgroup G := pPrimeCoreOf 2 (centralizer ({d} : Set G)) with hW
  set D : Subgroup G := closure ({x, y} : Set G) with hD
  set C : Subgroup G := centralizer (D : Set G) with hC
  have hy : orderOf y = 2 := h.setup.y_ord
  have hxy : x * y = y * x := (Subgroup.mem_centralizer_singleton_iff.1 h.setup.y_mem).symm
  have hCd : C ≤ centralizer ({d} : Set G) := centralizer_closure_le hd
  have hI0W : I0 ≤ centralizer (W : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.1 (hc d hd hd1)
  have hI1C : I1 ≤ C := hI.le_cent.trans (Subgroup.centralizer_le (by
    intro g hg
    exact (le_sup_left : D ≤ D ⊔ E) hg))
  have hI0I1 : I0 ≤ I1 := by
    rw [← hI.res_I1]
    exact Balance.oPrimeResidualOf_le_self I1
  refine Subgroup.commutator_eq_bot_iff_le_centralizer.2 ?_
  rcases h.quasiL with hLb | hLb
  ·
    obtain ⟨hLA, -⟩ := isPCompIn_liftAt hxy hy hK hLb
    have hLC : liftAt x y Lb ≤ C := hLA.1
    obtain ⟨π, hπs, -⟩ := hI.sl23
    obtain ⟨a, haI, b, hbI, ha2, hb2, hab⟩ := exists_twoElts_not_mem_odd π hπs
    have haI0 : a ∈ I0 := hI.res_I1 ▸ Balance.mem_oPrimeResidualOf_of_two_element haI ha2
    have hbI0 : b ∈ I0 := hI.res_I1 ▸ Balance.mem_oPrimeResidualOf_of_two_element hbI hb2
    have haC : a ∈ C := hI1C haI
    have hbC : b ∈ C := hI1C hbI
    have hZ : ∀ k ∈ (liftAt x y Lb).subgroupOf C, ∀ z ∈ (centralizer (W : Set G)).subgroupOf C,
        k * z * k⁻¹ ∈ (centralizer (W : Set G)).subgroupOf C := by
      intro k hk z hz
      rw [Subgroup.mem_subgroupOf] at hk hz ⊢
      exact conj_mem_centralizer_pPrimeCoreOf (hCd (hLC hk)) hz
    have hnc : QuotientGroup.mk' (pPrimeCore 2 ↥C) (⟨a, haC⟩ : ↥C) *
        QuotientGroup.mk' (pPrimeCore 2 ↥C) (⟨b, hbC⟩ : ↥C) ≠
        QuotientGroup.mk' (pPrimeCore 2 ↥C) (⟨b, hbC⟩ : ↥C) *
          QuotientGroup.mk' (pPrimeCore 2 ↥C) (⟨a, haC⟩ : ↥C) := by
      intro heq
      rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq] at heq
      have hinv := Subgroup.inv_mem _ heq
      have hmemG : (b * a)⁻¹ * (a * b) ∈ pPrimeCoreOf 2 C := by
        refine ⟨_, hinv, ?_⟩
        simp
      exact hab (pPrimeCoreOf 2 C) (CFSG.GH74.GLS.TwoThin.card_pPrimeCoreOf_odd C) hmemG
    have hLle : (liftAt x y Lb).subgroupOf C ≤ (centralizer (W : Set G)).subgroupOf C :=
      component_le_of_noncomm hLA.2 hZ (l₁ := ⟨a, haC⟩) (l₂ := ⟨b, hbC⟩)
        (Subgroup.mem_subgroupOf.2 (hI.le_lift haI0)) (Subgroup.mem_subgroupOf.2 (hI.le_lift hbI0))
        (Subgroup.mem_subgroupOf.2 (hI0W haI0)) hnc
    intro l hl
    exact Subgroup.mem_subgroupOf.1
      (hLle (Subgroup.mem_subgroupOf.2 hl : (⟨l, hLC hl⟩ : ↥C) ∈ (liftAt x y Lb).subgroupOf C))
  ·
    have hYx : C ≤ centralizer ({x} : Set G) := centralizer_closure_pair_le_left x y
    set φ := projRes hYx with hφdef
    have hφ : ¬ 2 ∣ Nat.card φ.ker := not_two_dvd_card_ker_projRes hYx
    have hLbY : Lb ≤ φ.range := by
      rw [range_projRes, imgBar_centralizer_closure_pair hxy hy]
      exact (SolvLiftBasic.isSolv2CompIn_le hLb).trans inf_le_left
    set P : Subgroup G := (Lb.comap φ).map C.subtype with hP
    have hlift : liftAt x y Lb = oPrimeResidualOf 2 P := by
      unfold liftAt
      rw [liftAt_pre_eq Lb]
    have hPC : P ≤ C := Subgroup.map_subtype_le _
    obtain ⟨πP, hπPs, hπPo⟩ := SolvLiftBasic.exists_sl23_preimage φ hφ hLbY rfl
      (SolvLiftBasic.exists_sl23_of_isSolv2CompIn hLb)
    let EP : Balance.SL23.Ext ↥P := ⟨πP, hπPs, hπPo⟩
    obtain ⟨π1, hπ1s, hπ1o⟩ := hI.sl23
    let E1 : Balance.SL23.Ext ↥I1 := ⟨π1, hπ1s, hπ1o⟩
    obtain ⟨S1⟩ := (inferInstance : Nonempty (Sylow 2 ↥I1))
    have hS1 : Nat.card ↥(S1 : Subgroup ↥I1) = 8 := E1.card_sylow S1
    set S : Subgroup G := (S1 : Subgroup ↥I1).map I1.subtype with hS
    have hSI0 : S ≤ I0 := by
      rintro _ ⟨s, hs, rfl⟩
      obtain ⟨k, hk⟩ := (S1.isPGroup' ⟨s, hs⟩)
      have hk' : (s : G) ^ (2 ^ k) = 1 := by
        have := congrArg (fun z : ↥(S1 : Subgroup ↥I1) => ((z : ↥I1) : G)) hk
        simpa using this
      exact hI.res_I1 ▸ Balance.mem_oPrimeResidualOf_of_two_element s.2 ⟨k, hk'⟩
    have hSP : S ≤ P := hSI0.trans (hI.le_lift.trans (hlift ▸ Balance.oPrimeResidualOf_le_self P))
    have hScard : Nat.card ↥S = 8 := by
      show Nat.card ↥((S1 : Subgroup ↥I1).map I1.subtype) = 8
      rw [Subgroup.card_map_of_injective I1.subtype_injective, hS1]
    set SP : Subgroup ↥P := S.subgroupOf P with hSPdef
    have hSPcard : Nat.card ↥SP = 8 := by
      rw [hSPdef, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSP).toEquiv]
      exact hScard
    obtain ⟨Q0⟩ := (inferInstance : Nonempty (Sylow 2 ↥P))
    let SS : Sylow 2 ↥P := Sylow.ofCard SP (by rw [hSPcard, ← Sylow.card_eq_multiplicity Q0, EP.card_sylow Q0])
    rw [hlift]
    refine Balance.oPrimeResidualOf_le_of_two_elements fun g hgP hg2 => ?_
    obtain ⟨k, hk⟩ := hg2
    have hgp : IsPGroup 2 ↥(zpowers (⟨g, hgP⟩ : ↥P)) :=
      isPGroup_zpowers_of_pow_two_pow_eq_one (a := (⟨g, hgP⟩ : ↥P)) (k := k)
        (Subtype.ext (by simpa using hk))
    obtain ⟨Q, hQ⟩ := hgp.exists_le_sylow
    obtain ⟨p, hpQ⟩ := MulAction.exists_smul_eq ↥P SS Q
    have hgQ : (⟨g, hgP⟩ : ↥P) ∈ (Q : Subgroup ↥P) := hQ (Subgroup.mem_zpowers _)
    rw [← hpQ] at hgQ
    have hgQ' : (⟨g, hgP⟩ : ↥P) ∈ (SS : Subgroup ↥P).map (MulAut.conj p).toMonoidHom := hgQ
    obtain ⟨q, hq, hqg⟩ := hgQ'
    have hqS : ((q : ↥P) : G) ∈ S := hq
    have hgeq : g = (p : G) * (q : G) * (p : G)⁻¹ := by
      have := congrArg (fun z : ↥P => (z : G)) hqg
      simpa [MulAut.conj_apply] using this.symm
    rw [hgeq]
    exact conj_mem_centralizer_pPrimeCoreOf (hCd (hPC p.2)) (hI0W (hSI0 hqS))

end CFSG.GH74.Generic.BProg.B3
