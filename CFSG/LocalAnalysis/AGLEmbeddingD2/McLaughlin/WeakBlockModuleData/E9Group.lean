module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.E9Abs1
public import CFSG.RankThree.PartOne.K1214.Basic

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

open scoped commutatorElement Pointwise

section Three

variable {Y : Type} [Group Y] [Finite Y]

theorem le_normalizer_of_commute' {A B : Subgroup Y} (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    B ≤ Subgroup.normalizer (A : Set Y) := fun b hb =>
  Subgroup.mem_normalizer_fintype fun a ha => by
    rw [← h a ha b hb, mul_inv_cancel_right]
    exact ha

theorem inf_zpowers_eq_bot_of_inverts {A : Subgroup Y} {c z : Y} (hc3 : c ^ 3 = 1)
    (hz : z * c * z⁻¹ = c⁻¹) (hA : ∀ a ∈ A, z * a = a * z) :
    A ⊓ Subgroup.zpowers c = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro w hw
  obtain ⟨hwA, hwc⟩ := Subgroup.mem_inf.1 hw
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hwc
  have h1 : z * c ^ m * z⁻¹ = c ^ m := by rw [hA _ hwA, mul_inv_cancel_right]
  have h2 : z * c ^ m * z⁻¹ = (c ^ m)⁻¹ := by
    have := map_zpow (MulAut.conj z) c m
    simp only [MulAut.conj_apply] at this
    rw [this, hz, inv_zpow]
  have hw : c ^ m = (c ^ m)⁻¹ := h1.symm.trans h2
  have h3 : c ^ m * c ^ m = 1 := by
    calc c ^ m * c ^ m = c ^ m * (c ^ m)⁻¹ := by rw [← hw]
      _ = 1 := mul_inv_cancel _
  exact eq_one_of_mul_self_of_pow_three h3 (zpow_cube_eq_one hc3 m)

theorem card_zpowers_of_pow_three {a : Y} (ha3 : a ^ 3 = 1) (ha1 : a ≠ 1) :
    Nat.card (Subgroup.zpowers a) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [Nat.card_zpowers]; exact orderOf_eq_prime ha3 ha1

theorem exists_pGroup_card_27 {a b c zb zc : Y} (hab : a * b = b * a) (hac : a * c = c * a)
    (hbc : b * c = c * b) (ha3 : a ^ 3 = 1) (hb3 : b ^ 3 = 1) (hc3 : c ^ 3 = 1) (ha1 : a ≠ 1)
    (hb1 : b ≠ 1) (hc1 : c ≠ 1) (hzb : zb * b * zb⁻¹ = b⁻¹) (hzba : zb * a = a * zb)
    (hzc : zc * c * zc⁻¹ = c⁻¹) (hzca : zc * a = a * zc) (hzcb : zc * b = b * zc) :
    ∃ V : Subgroup Y, IsPGroup 3 V ∧ Nat.card V = 27 ∧
      V = (Subgroup.zpowers a ⊔ Subgroup.zpowers b) ⊔ Subgroup.zpowers c := by
  set Za : Subgroup Y := Subgroup.zpowers a with hZa
  set Zb : Subgroup Y := Subgroup.zpowers b with hZb
  set Zc : Subgroup Y := Subgroup.zpowers c with hZc
  have hcommzp : ∀ {u v : Y}, u * v = v * u → ∀ m n : ℤ, u ^ m * v ^ n = v ^ n * u ^ m :=
    fun {u v} h m n => (Commute.zpow_zpow (show Commute u v from h) m n).eq
  have hZbN : Zb ≤ Subgroup.normalizer (Za : Set Y) :=
    le_normalizer_of_commute' fun x hx y hy => by
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      exact hcommzp hab m n
  have hbot₁ : Za ⊓ Zb = ⊥ := inf_zpowers_eq_bot_of_inverts hb3 hzb (fun w hw => by
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
    exact ((show Commute zb a from hzba).zpow_right m).eq)
  have hcard₁ : Nat.card (Za ⊔ Zb : Subgroup Y) = 9 := by
    have h := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hZbN
    rw [hbot₁, Subgroup.card_bot, card_zpowers_of_pow_three ha3 ha1,
      card_zpowers_of_pow_three hb3 hb1, mul_one] at h
    omega
  have hAc : Za ⊔ Zb ≤ Subgroup.centralizer ({c} : Set Y) := by
    refine sup_le (fun w hw => ?_) (fun w hw => ?_)
    · obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact ((show Commute c a from hac.symm).zpow_right m).eq
    · obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact ((show Commute c b from hbc.symm).zpow_right m).eq
  have hZcN : Zc ≤ Subgroup.normalizer ((Za ⊔ Zb : Subgroup Y) : Set Y) :=
    le_normalizer_of_commute' fun x hx y hy => by
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      have := Subgroup.mem_centralizer_iff.mp (hAc hx) c (Set.mem_singleton c)
      exact ((show Commute c x from this).zpow_left n).eq.symm
  have hzA : ∀ w ∈ Za ⊔ Zb, zc * w = w * zc := by
    have hle : Za ⊔ Zb ≤ Subgroup.centralizer ({zc} : Set Y) := by
      refine sup_le (fun w hw => ?_) (fun w hw => ?_)
      · obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        rw [hh]
        exact ((show Commute zc a from hzca).zpow_right m).eq
      · obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        rw [hh]
        exact ((show Commute zc b from hzcb).zpow_right m).eq
    intro w hw
    exact Subgroup.mem_centralizer_iff.mp (hle hw) zc (Set.mem_singleton zc)
  have hbot₂ : (Za ⊔ Zb) ⊓ Zc = ⊥ := inf_zpowers_eq_bot_of_inverts hc3 hzc hzA
  have hcard₂ : Nat.card ((Za ⊔ Zb) ⊔ Zc : Subgroup Y) = 27 := by
    have h := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hZcN
    rw [hbot₂, Subgroup.card_bot, hcard₁, card_zpowers_of_pow_three hc3 hc1, mul_one] at h
    omega
  exact ⟨(Za ⊔ Zb) ⊔ Zc, IsPGroup.of_card (n := 3) (by rw [hcard₂]; norm_num), hcard₂, rfl⟩

theorem exists_conj_into {J E V : Subgroup Y} (hE : E ≤ J) (hE9 : Nat.card E = 9)
    (hsyl : ¬ 3 ∣ (E.subgroupOf J).index) (hV : V ≤ J) (hV3 : IsPGroup 3 V) :
    ∃ g ∈ J, ∀ v ∈ V, g⁻¹ * v * g ∈ E := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let E' : Subgroup J := E.subgroupOf J
  have hE'c : Nat.card E' = 9 := by
    rw [← hE9]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE).toEquiv
  have hE'3 : IsPGroup 3 E' := IsPGroup.of_card (n := 2) (by rw [hE'c]; norm_num)
  let sE : Sylow 3 J := hE'3.toSylow hsyl
  let V' : Subgroup J := V.subgroupOf J
  have hV'3 : IsPGroup 3 V' := hV3.of_equiv (Subgroup.subgroupOfEquivOfLe hV).symm
  obtain ⟨sV, hsV⟩ := hV'3.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq J sE sV
  have hsub : ((g • sE : Sylow 3 J) : Subgroup J) = (sV : Subgroup J) := by rw [hg]
  rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at hsub
  refine ⟨(g : Y), g.2, fun v hv => ?_⟩
  have hvs : (⟨v, hV hv⟩ : J) ∈ (sV : Subgroup J) := hsV (Subgroup.mem_subgroupOf.2 hv)
  rw [← hsub] at hvs
  obtain ⟨c, hc, hcx⟩ := hvs
  have hx0 : (g : Y) * (c : Y) * (g : Y)⁻¹ = v := by
    have := congrArg Subtype.val hcx
    simpa [MulAut.conj_apply] using this
  have hcE : (c : Y) ∈ E := Subgroup.mem_subgroupOf.mp (show c ∈ E' from hc)
  have : (c : Y) = (g : Y)⁻¹ * v * (g : Y) := by rw [← hx0]; group
  rw [← this]; exact hcE

theorem exists_pGroup_card_9 {a b zb : Y} (hab : a * b = b * a) (ha3 : a ^ 3 = 1) (hb3 : b ^ 3 = 1)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hzb : zb * b * zb⁻¹ = b⁻¹) (hzba : zb * a = a * zb) :
    ∃ V : Subgroup Y, IsPGroup 3 V ∧ V = Subgroup.zpowers a ⊔ Subgroup.zpowers b := by
  set Za : Subgroup Y := Subgroup.zpowers a with hZa
  set Zb : Subgroup Y := Subgroup.zpowers b with hZb
  have hZbN : Zb ≤ Subgroup.normalizer (Za : Set Y) :=
    le_normalizer_of_commute' fun x hx y hy => by
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      exact (Commute.zpow_zpow (show Commute a b from hab) m n).eq
  have hbot : Za ⊓ Zb = ⊥ := inf_zpowers_eq_bot_of_inverts hb3 hzb (fun w hw => by
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
    exact ((show Commute zb a from hzba).zpow_right m).eq)
  have hcard : Nat.card (Za ⊔ Zb : Subgroup Y) = 9 := by
    have h := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hZbN
    rw [hbot, Subgroup.card_bot, card_zpowers_of_pow_three ha3 ha1,
      card_zpowers_of_pow_three hb3 hb1, mul_one] at h
    omega
  exact ⟨Za ⊔ Zb, IsPGroup.of_card (n := 2) (by rw [hcard]; norm_num), rfl⟩

theorem card_le_of_conj_into {V E : Subgroup Y} {g : Y} (h : ∀ v ∈ V, g⁻¹ * v * g ∈ E) :
    Nat.card V ≤ Nat.card E := by
  refine Nat.card_le_card_of_injective (fun v : V => (⟨g⁻¹ * v * g, h v v.2⟩ : E)) ?_
  intro u v huv
  have := congrArg Subtype.val huv
  simp only at this
  exact Subtype.ext (by simpa using this)

end Three

section Transfer

variable {Y : Type} [Group Y]

theorem top_le_subgroupOf_sup {J A B C : Subgroup Y} (hJ : J ≤ A ⊔ (B ⊔ C)) (hA : A ≤ J)
    (hB : B ≤ J) (hC : C ≤ J) :
    (⊤ : Subgroup J) ≤ A.subgroupOf J ⊔ (B.subgroupOf J ⊔ C.subgroupOf J) := by
  rw [← Subgroup.map_le_map_iff_of_injective J.subtype_injective, Subgroup.map_sup,
    Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hA, Subgroup.map_subgroupOf_eq_of_le hB,
    Subgroup.map_subgroupOf_eq_of_le hC, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  exact hJ

theorem subgroupOf_closure_pair {J : Subgroup Y} {x y : Y} (hx : x ∈ J) (hy : y ∈ J) :
    Subgroup.closure ({(⟨x, hx⟩ : J), (⟨y, hy⟩ : J)} : Set J) =
      (Subgroup.closure ({x, y} : Set Y)).subgroupOf J := by
  have hcl : Subgroup.closure ({x, y} : Set Y) ≤ J := (Subgroup.closure_le _).2 (by
    intro z hz
    rcases hz with rfl | hz
    · exact hx
    · rw [Set.mem_singleton_iff] at hz; rw [hz]; exact hy)
  apply Subgroup.map_injective J.subtype_injective
  rw [MonoidHom.map_closure, Subgroup.map_subgroupOf_eq_of_le hcl]
  congr 1
  ext z
  simp [Set.mem_image]

theorem subgroupOf_le_pCore {J R : Subgroup Y} (hRJ : R ≤ J) (hJR : J ≤ Subgroup.normalizer (R : Set Y))
    (hR2 : IsPGroup 2 R) : R.subgroupOf J ≤ CFSG.pCore 2 ↥J := by
  haveI : (R.subgroupOf J).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hRJ).2 hJR
  exact le_sSup ⟨inferInstance, hR2.of_equiv (Subgroup.subgroupOfEquivOfLe hRJ).symm⟩

end Transfer


end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
