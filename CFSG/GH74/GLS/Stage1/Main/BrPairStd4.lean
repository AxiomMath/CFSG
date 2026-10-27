module

public import CFSG.GH74.GLS.Stage1.Main.BrPairAbs
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx65
public import CFSG.GH74.GLS.IVK.Lifted.FStarC
public import CFSG.GH74.GLS.Stage1.Main.Out
public import CFSG.GH74.GLS.Stage1.Thm6.Prod.Transport

public section

namespace CFSG.GH74.GLS.Stage1.Main

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage1.Thm3.Sec4
  CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6 CFSG.GH74.GLS.Stage1.Thm3.Sec7
  CFSG.GH74.GLS.Stage1.Thm3.Sec8 CFSG.GH74.GLS.Stage1.Thm2.Recip CFSG.GH74.GLS.Stage1.Thm6.Prod
open scoped commutatorElement

section Std4Bar

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ : Subgroup G}

theorem imgBar_comm4 (hII : II4_4_4_center) (hs : Std4 G z S K₁ K₂) :
    ∀ a ∈ imgBar z K₁, ∀ b ∈ imgBar z K₂, a * b = b * a := by
  have hM := m4_of_std hII hs
  have hK₁C : K₁ ≤ Cz z := hM.K₁_le
  have hK₂C : K₂ ≤ Cz z := hM.K₂_le
  intro a ha b hb
  obtain ⟨k₁, hk₁, rfl⟩ := (mem_imgBar hK₁C).1 ha
  obtain ⟨k₂, hk₂, rfl⟩ := (mem_imgBar hK₂C).1 hb
  have h1 : ⁅k₁, k₂⁆ ∈ pPrimeCoreOf 2 K₁ := (hM.cs₁ hk₂).2.2 k₁ hk₁
  have hOz : ⁅k₁, k₂⁆ ∈ Oz z := pPrimeCoreOf_le_Oz (hs.comp_isPCompIn (Or.inl rfl)) h1
  have hcx : ⁅k₁, k₂⁆ ∈ Cz z := by
    simp only [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem (hK₁C hk₁) (hK₂C hk₂)) (inv_mem (hK₁C hk₁)))
      (inv_mem (hK₂C hk₂))
  have hcomm1 : piC z ⟨⁅k₁, k₂⁆, hcx⟩ = 1 :=
    (hatMk_eq_one_iff (Cz z) ⟨⁅k₁, k₂⁆, hcx⟩).2 hOz
  have e : (⟨⁅k₁, k₂⁆, hcx⟩ : ↥(Cz z)) =
      ⁅(⟨k₁, hK₁C hk₁⟩ : ↥(Cz z)), (⟨k₂, hK₂C hk₂⟩ : ↥(Cz z))⁆ := rfl
  rw [e, map_commutatorElement] at hcomm1
  exact commutatorElement_eq_one_iff_mul_comm.1 hcomm1

theorem zbar_facts4 (hII : II4_4_4_center) (hs : Std4 G z S K₁ K₂) :
    piC z ⟨z, mem_centralizer_singleton_iff.2 rfl⟩ ∈ imgBar z K₁ ⊓ imgBar z K₂ ∧
      piC z ⟨z, mem_centralizer_singleton_iff.2 rfl⟩ ≠ 1 := by
  have hM := m4_of_std hII hs
  have hK₁C : K₁ ≤ Cz z := hM.K₁_le
  have hK₂C : K₂ ≤ Cz z := hM.K₂_le
  refine ⟨⟨piC_mem_imgBar hK₁C (hM.z_mem_comp (Or.inl rfl)),
    piC_mem_imgBar hK₂C (hM.z_mem_comp (Or.inr rfl))⟩, fun h => ?_⟩
  have hz : z ∈ Oz z := (hatMk_eq_one_iff (Cz z) ⟨z, mem_centralizer_singleton_iff.2 rfl⟩).1 h
  have hdvd := Subgroup.orderOf_dvd_natCard (Oz z) hz
  rw [hs.orderOf_z] at hdvd
  exact (Nat.not_even_iff_odd.2 card_Oz_odd) (even_iff_two_dvd.2 hdvd)

theorem imgBar_inf_card4 (hII : II4_4_4_center) (h44 : II4_44) (hs : Std4 G z S K₁ K₂) :
    Nat.card ↥(imgBar z K₁ ⊓ imgBar z K₂) = 2 := by
  have hc1 := hs.comp_isPCompIn (Or.inl rfl : K₁ = K₁ ∨ K₁ = K₂)
  have hsl := h44 G hs.simple z hs.orderOf_z K₁ hc1 (hs.comp_pRank (Or.inl rfl))
  obtain ⟨e⟩ := imgBar_equiv hc1
  have hcen : Nat.card ↥(Subgroup.center ↥(imgBar z K₁)) = 2 := by
    have := Nat.card_congr (Subgroup.centerCongr e).toEquiv
    rw [hsl.2] at this
    exact this.symm
  have hD : (imgBar z K₁ ⊓ imgBar z K₂).subgroupOf (imgBar z K₁) ≤
      Subgroup.center ↥(imgBar z K₁) := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    rw [Subgroup.mem_center_iff]
    intro a
    exact Subtype.ext (imgBar_comm4 hII hs a a.2 x hx.2)
  have hle : Nat.card ↥(imgBar z K₁ ⊓ imgBar z K₂) ≤ 2 := by
    have h1 := Subgroup.card_le_of_le hD
    rw [hcen, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_left : imgBar z K₁ ⊓ imgBar z K₂ ≤ imgBar z K₁)).toEquiv] at h1
    exact h1
  have hge : 2 ≤ Nat.card ↥(imgBar z K₁ ⊓ imgBar z K₂) := by
    obtain ⟨hz1, hz2⟩ := zbar_facts4 hII hs
    have hne : imgBar z K₁ ⊓ imgBar z K₂ ≠ ⊥ := by
      intro hbot
      rw [hbot, Subgroup.mem_bot] at hz1
      exact hz2 hz1
    have := (Subgroup.one_lt_card_iff_ne_bot _).2 hne
    omega
  omega

theorem map_K12 (hII : II4_4_4_center) (hs : Std4 G z S K₁ K₂) :
    ((K₁ ⊔ K₂).subgroupOf (Cz z)).map (piC z) = imgBar z K₁ ⊔ imgBar z K₂ := by
  have hM := m4_of_std hII hs
  unfold imgBar
  rw [Subgroup.subgroupOf_sup hM.K₁_le hM.K₂_le, Subgroup.map_sup]

theorem imgBar_sup_normal4 (hII : II4_4_4_center) (hs : Std4 G z S K₁ K₂) :
    (imgBar z K₁ ⊔ imgBar z K₂).Normal := by
  have hM := m4_of_std hII hs
  rw [← map_K12 hII hs]
  have hn : ((K₁ ⊔ K₂).subgroupOf (Cz z)).Normal := by
    constructor
    intro n hn g
    exact hM.C_norm_K g.2 hn
  exact hn.map (piC z) (QuotientGroup.mk'_surjective _)

theorem imgBar_quasi (hs : Std4 G z S K₁ K₂) {K : Subgroup G} (hK : K = K₁ ∨ K = K₂) :
    IsQuasisimple ↥(imgBar z K) := by
  have hc := hs.comp_isPCompIn hK
  obtain ⟨e⟩ := imgBar_equiv hc
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e (TwoThin.isQuasisimple_hat hc)

theorem imgBar_sl2 (hs : Std4 G z S K₁ K₂) {K : Subgroup G} (hK : K = K₁ ∨ K = K₂) {q : ℕ}
    (h : HatSL2 K q) : HasSL2Model ↥(imgBar z K) (fun r => r = q) := by
  obtain ⟨F, iF, fF, hq, ⟨e⟩⟩ := h
  obtain ⟨ι⟩ := imgBar_equiv (hs.comp_isPCompIn hK)
  exact ⟨F, iF, fF, hq, ⟨ι.symm.trans e⟩⟩

theorem centralizer_le_K12_of_hQ (hII : II4_4_4_center) (hs : Std4 G z S K₁ K₂)
    (hQ : Qz S z = zpowers z) :
    ∀ γ : CentralizerBar z, (∀ a ∈ imgBar z K₁ ⊔ imgBar z K₂, a * γ = γ * a) →
      γ ∈ imgBar z K₁ ⊔ imgBar z K₂ := by
  have hM := m4_of_std hII hs
  have hK₁C : K₁ ≤ Cz z := hM.K₁_le
  have hK₂C : K₂ ≤ Cz z := hM.K₂_le
  have hzC : z ∈ Cz z := mem_centralizer_singleton_iff.2 rfl
  intro γ hγ
  obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective γ
  have hcomm : ∀ k ∈ K₁ ⊔ K₂, ⁅k, (c : G)⁆ ∈ Oz z := by
    intro k hk
    have hkC : k ∈ Cz z := sup_le hK₁C hK₂C hk
    have hkb : piC z ⟨k, hkC⟩ ∈ imgBar z K₁ ⊔ imgBar z K₂ := by
      rw [← map_K12 hII hs]; exact ⟨⟨k, hkC⟩, hk, rfl⟩
    have h1 := hγ _ hkb
    have hcx : ⁅k, (c : G)⁆ ∈ Cz z := by
      simp only [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hkC c.2) (inv_mem hkC)) (inv_mem c.2)
    refine (hatMk_eq_one_iff (Cz z) ⟨⁅k, (c : G)⁆, hcx⟩).1 ?_
    have e : (⟨⁅k, (c : G)⁆, hcx⟩ : ↥(Cz z)) = ⁅(⟨k, hkC⟩ : ↥(Cz z)), c⁆ := rfl
    rw [e, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 h1
  have hF := IVK.Lifted.fStar_C_of_II4 hII G z S K₁ K₂ hs hQ (c : G) c.2 hcomm
  have hle : (zpowers z ⊔ Oz z).subgroupOf (Cz z) ≤
      (imgBar z K₁ ⊔ imgBar z K₂).comap (piC z) := by
    rw [show Oz z = pPrimeCoreOf 2 (Cz z) from rfl,
      Subgroup.subgroupOf_sup (zpowers_le.2 hzC) (TwoThin.pPrimeCoreOf_le (Cz z))]
    refine sup_le ?_ ?_
    · intro x hx
      obtain ⟨n, hn⟩ := (show (x : G) ∈ zpowers z from hx)
      have hxe : x = (⟨z, hzC⟩ : ↥(Cz z)) ^ n := Subtype.ext (by simpa using hn.symm)
      have hz1 : piC z ⟨z, hzC⟩ ∈ imgBar z K₁ ⊔ imgBar z K₂ :=
        Subgroup.mem_sup_left (piC_mem_imgBar hK₁C (hM.z_mem_comp (Or.inl rfl)))
      show piC z x ∈ imgBar z K₁ ⊔ imgBar z K₂
      rw [hxe, map_zpow]
      exact zpow_mem hz1 n
    · intro x hx
      have : piC z x = 1 := (hatMk_eq_one_iff (Cz z) x).2 hx
      show piC z x ∈ imgBar z K₁ ⊔ imgBar z K₂
      rw [this]; exact one_mem _
  exact hle (show c ∈ (zpowers z ⊔ Oz z).subgroupOf (Cz z) from hF)

theorem centralizer_le_K12 (hII : II4_4_4_center) (h41 : Prop4_1) (hs : Std4 G z S K₁ K₂) :
    ∀ γ : CentralizerBar z, (∀ a ∈ imgBar z K₁ ⊔ imgBar z K₂, a * γ = γ * a) →
      γ ∈ imgBar z K₁ ⊔ imgBar z K₂ :=
  centralizer_le_K12_of_hQ hII hs (h41 G z S K₁ K₂ hs).1

theorem isPGroup_barS (hII : II4_4_4_center) (hs : Std4 G z S K₁ K₂) :
    IsPGroup 2 ↥((S.subgroupOf (Cz z)).map (piC z)) := by
  have hM := m4_of_std hII hs
  have hSC : S ≤ Cz z := hs.sylow.le
  have h1 : IsPGroup 2 ↥(S.subgroupOf (Cz z)) :=
    hM.S_pgroup.of_equiv (Subgroup.subgroupOfEquivOfLe hSC).symm
  exact h1.of_surjective _ (MonoidHom.subgroupMap_surjective (piC z) _)

theorem comps_of_std4_of_hQ (hII : II4_4_4_center) (hs : Std4 G z S K₁ K₂) (hQ : Qz S z = zpowers z) :
    {K : Subgroup (CentralizerBar z) | IsComponent K} = {imgBar z K₁, imgBar z K₂} :=
  comps_of_pair (imgBar_quasi hs (Or.inl rfl)) (imgBar_quasi hs (Or.inr rfl)) (imgBar_comm4 hII hs)
    (imgBar_sup_normal4 hII hs) (centralizer_le_K12_of_hQ hII hs hQ)

theorem layer_eq_imgBar_of_hQ (hII : II4_4_4_center) (hs : Std4 G z S K₁ K₂) (hQ : Qz S z = zpowers z) :
    layer (CentralizerBar z) = imgBar z K₁ ⊔ imgBar z K₂ := by
  show sSup {K : Subgroup (CentralizerBar z) | IsComponent K} = _
  rw [comps_of_std4_of_hQ hII hs hQ, sSup_pair]

theorem comps_of_std4 (hII : II4_4_4_center) (h41 : Prop4_1) (hs : Std4 G z S K₁ K₂) :
    {K : Subgroup (CentralizerBar z) | IsComponent K} = {imgBar z K₁, imgBar z K₂} :=
  comps_of_std4_of_hQ hII hs (h41 G z S K₁ K₂ hs).1

theorem LBar_eq_pair_of_std4 (hII : II4_4_4_center) (h41 : Prop4_1) (hs : Std4 G z S K₁ K₂) :
    LBar z = imgBar z K₁ ⊔ imgBar z K₂ := by
  have hQ₁ := imgBar_quasi hs (Or.inl rfl)
  have hQ₂ := imgBar_quasi hs (Or.inr rfl)
  have hcomm := imgBar_comm4 hII hs
  have hC := centralizer_le_K12 hII h41 hs
  have hcomps := comps_of_std4 hII h41 hs
  have hlayer : layer (CentralizerBar z) = imgBar z K₁ ⊔ imgBar z K₂ := by
    show sSup {K : Subgroup (CentralizerBar z) | IsComponent K} = _
    rw [hcomps, sSup_pair]
  have hI : InnerE z = imgBar z K₁ ⊔ imgBar z K₂ := by
    unfold InnerE
    rw [hlayer]
    exact sup_eq_left.2 hC
  rw [LBar_eq z, hI]
  exact inf_eq_right.2 (sup_le (perfect_le_oPrimePResidual' hQ₁.1) (perfect_le_oPrimePResidual' hQ₂.1))

theorem stage1Pair_of_std4 (hII : II4_4_4_center) (h44 : II4_44) (h41 : Prop4_1)
    {q : ℕ} (hs : Std4 G z S K₁ K₂) (hodd : Odd q) (h5 : 5 ≤ q) (hK₁ : HatSL2 K₁ q)
    (hK₂ : HatSL2 K₂ q) (hbase : Stage1Base G z S)
    (hsw : ∃ s ∈ S, Swaps z s (imgBar z K₁) (imgBar z K₂)) :
    Stage1Pair G z S q (imgBar z K₁) (imgBar z K₂) := by
  have hcomm := imgBar_comm4 hII hs
  have hcard := imgBar_inf_card4 hII h44 hs
  have hC := centralizer_le_K12 hII h41 hs
  have hcomps := comps_of_std4 hII h41 hs
  have hLB : LBar z = imgBar z K₁ ⊔ imgBar z K₂ := LBar_eq_pair_of_std4 hII h41 hs
  refine ⟨hbase, hodd, by omega, ?_, ⟨hLB.symm, hcomm, hcard⟩, imgBar_sl2 hs (Or.inl rfl) hK₁,
    imgBar_sl2 hs (Or.inr rfl) hK₂, hcomps, ?_, hsw⟩
  · intro hEq
    rw [← hEq, inf_idem] at hcard
    obtain ⟨F, iF, fF, hq, ⟨e⟩⟩ := imgBar_sl2 hs (Or.inl rfl) hK₁
    have h1 := Nat.card_congr e.toEquiv
    rw [hcard, card_statedSL_two', hq] at h1
    have h25 : 25 ≤ q ^ 2 := by nlinarith
    have h24 : 24 ≤ q ^ 2 - 1 := by omega
    have : 5 * 24 ≤ q * (q ^ 2 - 1) := Nat.mul_le_mul h5 h24
    omega
  · rw [hLB]
    show fittingSubgroup (CentralizerBar z) ⊔ layer (CentralizerBar z) = _
    have hlayer : layer (CentralizerBar z) = imgBar z K₁ ⊔ imgBar z K₂ := by
      show sSup {K : Subgroup (CentralizerBar z) | IsComponent K} = _
      rw [hcomps, sSup_pair]
    have hF : fittingSubgroup (CentralizerBar z) ≤ imgBar z K₁ ⊔ imgBar z K₂ := by
      intro f hf
      apply hC f
      intro a ha
      have hal : a ∈ layer (CentralizerBar z) := by rw [hlayer]; exact ha
      have hm : ⁅f, a⁆ ∈ ⁅fittingSubgroup (CentralizerBar z), layer (CentralizerBar z)⁆ :=
        Subgroup.commutator_mem_commutator hf hal
      rw [CFSG.LocalCores.fitting_layer_commute] at hm
      have h1 : ⁅f, a⁆ = 1 := by simpa using hm
      exact (commutatorElement_eq_one_iff_mul_comm.1 h1).symm
    rw [hlayer]
    exact sup_eq_right.2 hF

theorem isComponent_map_barOf (hII : II4_4_4_center) (hs : Std4 G z S K₁ K₂)
    {H : Subgroup ↥(barOf z (K₁ ⊔ K₂ ⊔ S))} (hH : IsComponent H) :
    IsComponent (H.map (barOf z (K₁ ⊔ K₂ ⊔ S)).subtype) := by
  have hM := m4_of_std hII hs
  have hSC : S ≤ Cz z := hs.sylow.le
  have hX : barOf z (K₁ ⊔ K₂ ⊔ S) =
      imgBar z K₁ ⊔ imgBar z K₂ ⊔ (S.subgroupOf (Cz z)).map (piC z) := by
    show ((K₁ ⊔ K₂ ⊔ S).subgroupOf (Cz z)).map (piC z) = _
    rw [Subgroup.subgroupOf_sup (sup_le hM.K₁_le hM.K₂_le) hSC, Subgroup.map_sup, map_K12 hII hs]
  have hN := imgBar_sup_normal4 hII hs
  have hNW : imgBar z K₁ ⊔ imgBar z K₂ ≤ barOf z (K₁ ⊔ K₂ ⊔ S) := by
    rw [hX]; exact le_sup_left
  have hperf : Group.IsPerfect ↥(H.map (barOf z (K₁ ⊔ K₂ ⊔ S)).subtype) :=
    (CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (H.equivMapOfInjective _ (Subgroup.subtype_injective _)) hH.1).1
  have hle : H.map (barOf z (K₁ ⊔ K₂ ⊔ S)).subtype ≤
      imgBar z K₁ ⊔ imgBar z K₂ ⊔ (S.subgroupOf (Cz z)).map (piC z) := by
    rw [← hX]; exact Subgroup.map_subtype_le H
  exact isComponent_map_subtype_of_le_normal hN hNW hH
    (perfect_le_of_le_sup_pgroup hN (isPGroup_barS hII hs) hperf hle)

end Std4Bar

end CFSG.GH74.GLS.Stage1.Main
