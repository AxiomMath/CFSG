module

public import CFSG.HardMathSupport.Solomon.Coordinator.I22_7UDefs
import CFSG.Goldschmidt.Steps.Sec82PGroup
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection5.theorem_5_3

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open

theorem i227ug_isElemAbelian_of_comm_pow {K : Type*} [Group K] {p : ℕ} {E : Subgroup K}
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hpow : ∀ x ∈ E, x ^ p = 1) :
    IsElemAbelian p E :=
  ⟨⟨⟨fun a b => Subtype.ext (hcomm a a.2 b b.2)⟩⟩, hpow⟩

theorem i227ug_isElementaryAbelian_subgroupOf {K : Type*} [Group K] {p : ℕ} {E : Subgroup K}
    (U : Subgroup K) (hE : IsElemAbelian p E) : IsElementaryAbelian p (E.subgroupOf U) where
  is_comm := ⟨fun x y => Subtype.ext (Subtype.ext (by
    have h := congrArg Subtype.val (hE.1.is_comm.comm ⟨((x : U) : K), x.2⟩ ⟨((y : U) : K), y.2⟩)
    exact h))⟩
  exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
    Subtype.ext (Subtype.ext (by simpa using hE.2 _ x.2))

theorem i227ug_not_isCyclic {K : Type*} [Group K] [Finite K] {p : ℕ} (hp : p.Prime)
    {U E : Subgroup K} (hEU : E ≤ U) (hE : IsElemAbelian p E) (hcard : p < Nat.card E) :
    ¬ IsCyclic U := by
  intro hU
  have : IsCyclic E := Subgroup.isCyclic_of_le hEU
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := E)
  have hgp : g ^ p = 1 := Subtype.ext (by simpa using hE.2 g g.2)
  have hdvd : Nat.card E ∣ p := hg ▸ orderOf_dvd_of_pow_eq_one hgp
  exact absurd (Nat.le_of_dvd hp.pos hdvd) (not_le.mpr hcard)

theorem i227u_uq_holds : I22_7UQ := by
  intro K _ _ P U hP hUP hUn h3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp1 : 1 < 3 := by norm_num
  have hPU : P ≤ Subgroup.normalizer (U : Set K) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUP).mp hUn
  obtain ⟨E₀, hE₀U, hE₀, hE₀c⟩ := CFSG.SectionRank.exists_pRank hp1 U
  have hE₀27 : 3 ^ 3 ≤ Nat.card E₀ := hE₀c ▸ Nat.pow_le_pow_right (by norm_num) h3
  have hUc : ¬ IsCyclic U :=
    i227ug_not_isCyclic Nat.prime_three hE₀U hE₀ (by omega)
  obtain ⟨V, hVU, hPV, hVc, hVpow, hVcomm⟩ :=
    CFSG.Goldschmidt.Sec82.exists_normal_plane_le_of_le Nat.prime_three (by norm_num) hP hUP hPU
      hUc
  have hVel : IsElemAbelian 3 V := i227ug_isElemAbelian_of_comm_pow hVcomm hVpow
  have hVn : (V.subgroupOf P).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (hVU.trans hUP)).mpr hPV
  have hV2 : 2 ≤ CFSG.Open.pRank 3 V :=
    CFSG.SectionRank.le_pRank hp1 le_rfl hVel hVc
  obtain ⟨K₀, hK₀⟩ := Sylow.exists_subgroup_card_pow_prime (G := E₀) 3 (n := 3)
    (by
      obtain ⟨k, hk⟩ := (hP.to_le (hE₀U.trans hUP)).exists_card_eq
      rw [hk] at hE₀27 ⊢
      exact Nat.pow_dvd_pow 3 ((Nat.pow_le_pow_iff_right hp1).mp hE₀27))
  set E₃ : Subgroup K := K₀.map E₀.subtype with hE₃
  have hE₃U : E₃ ≤ U := (Subgroup.map_subtype_le _).trans hE₀U
  have hE₃c : Nat.card E₃ = 3 ^ 3 := by
    rw [hE₃, Subgroup.card_map_of_injective E₀.subtype_injective, hK₀]
  have hE₃el : IsElemAbelian 3 E₃ := by
    refine i227ug_isElemAbelian_of_comm_pow (fun x hx y hy => ?_) (fun x hx => ?_)
    · obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨b, hb, rfl⟩ := hy
      exact congrArg Subtype.val (hE₀.1.is_comm.comm a b)
    · obtain ⟨a, ha, rfl⟩ := hx
      exact hE₀.2 a a.2
  have : IsElementaryAbelian 3 (E₃.subgroupOf U) :=
    i227ug_isElementaryAbelian_subgroupOf U hE₃el
  have hrank : 3 ≤ CFSG.groupRank U :=
    CFSG.groupRank_at_least_three_of_elementaryAbelian_subgroup_card_p3' (p := 3)
      (B := E₃.subgroupOf U)
      (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE₃U).toEquiv, hE₃c])
  have hVnU : (V.subgroupOf U).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hVU).mpr (hUP.trans hPV)
  have : IsElementaryAbelian 3 (V.subgroupOf U) := i227ug_isElementaryAbelian_subgroupOf U hVel
  obtain ⟨B, hBn, hBel, hBc, hVB⟩ :=
    CFSG.exists_normal_elementaryAbelian_card_p3_containing_rank_two_normal (p := 3)
      (by norm_num) (hP.to_le hUP) hrank (E := V.subgroupOf U)
      ⟨by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVU).toEquiv, hVc], inferInstance⟩
  have hBcard : Nat.card (B.map U.subtype) = 3 ^ 3 := by
    rw [Subgroup.card_map_of_injective U.subtype_injective, hBc]
  have hBel' : IsElemAbelian 3 (B.map U.subtype) :=
    i227ug_isElemAbelian_of_comm_pow
      (fun x hx y hy => by
        obtain ⟨a, ha, rfl⟩ := hx
        obtain ⟨b, hb, rfl⟩ := hy
        exact congrArg Subtype.val (congrArg Subtype.val (hBel.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)))
      (fun x hx => by
        obtain ⟨a, ha, rfl⟩ := hx
        exact congrArg Subtype.val (elemPow_eq_one_of_isElementaryAbelian (A := B) a ha))
  refine ⟨V, hVU, hVn, hV2, B.map U.subtype, Subgroup.map_subtype_le B, hBel', ?_,
    CFSG.SectionRank.le_pRank hp1 le_rfl hBel' hBcard⟩
  intro v hv
  exact ⟨⟨v, hVU hv⟩, hVB (Subgroup.mem_subgroupOf.mpr hv), rfl⟩

end CFSG.HardMathSupport.Solomon.Coordinator
