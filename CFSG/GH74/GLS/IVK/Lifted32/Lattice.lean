module

public import CFSG.GH74.GLS.IVK.Lifted32.Pull
public import CFSG.GH74.GLS.IVK.Lifted.TwoA7
public import CFSG.GH74.GLS.Stage1.Thm4.L97b
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Basic
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Core
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Stages

public section

namespace CFSG.GH74.GLS.IVK.Lifted32

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage1.Thm3.Sec4
  CFSG.GH74.GLS.Stage1.Thm3.Sec5
open scoped commutatorElement

namespace Lat

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ : Subgroup G}

theorem mem_normalizer_iff_bar {K : Subgroup G} (hK : IsPCompIn 2 (Cen z) K) {s : G}
    (hsC : s ∈ Cen z) :
    s ∈ normalizer (K : Set G) ↔
      toBar z ⟨s, hsC⟩ ∈ normalizer (barOf z K : Set (CentralizerBar z)) := by
  have h2 : (⟨s, hsC⟩ : ↥(Cen z)) ∈ normalizer ((K.subgroupOf (Cen z) : Subgroup ↥(Cen z)) : Set ↥(Cen z)) ↔
      s ∈ normalizer (K : Set G) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hK.1]
    rfl
  rw [← h2]
  constructor
  · intro h
    exact Subgroup.le_normalizer_map (toBar z) (Subgroup.mem_map.2 ⟨_, h, rfl⟩)
  · intro h
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact CFSG.ComponentClassification.UnbalancedLayer.mem_normalizer_of_map hK.2 h


theorem pull_T1 (hK : IsPCompIn 2 (Cen z) K₁) (hS : CFSG.ABGLocalTools.IsSylowOf 2 S (Cen z)) :
    pull z S (IVK.Prod3.T1 (barOf z S) (barOf z K₁)) = S1 S K₁ := by
  ext s
  rw [Pull.mem_pull]
  constructor
  · rintro ⟨hsS, hsC, h⟩
    exact ⟨hsS, (mem_normalizer_iff_bar hK hsC).2 h.2⟩
  · rintro ⟨hsS, hs⟩
    have hsC := hS.le hsS
    exact ⟨hsS, hsC, Pull.mem_barOf hsS hsC, (mem_normalizer_iff_bar hK hsC).1 hs⟩

theorem mem_pull_sup_iff (hII : II4_4_4_center) (h : Std4 G z S K₁ K₂) {s : G} (hsS : s ∈ S) :
    s ∈ pull z S (barOf z K₁ ⊔ barOf z K₂) ↔ s ∈ K₁ ⊔ K₂ := by
  have hM := m4_of_std hII h
  have hK₁C : K₁ ≤ Cen z := hM.K₁_le
  have hK₂C : K₂ ≤ Cen z := hM.K₂_le
  have hsC : s ∈ Cen z := hM.S_syl.1 hsS
  constructor
  · intro hs
    have hb := Pull.toBar_mem_of_mem_pull hs hsC
    rw [← Pull.barOf_sup hK₁C hK₂C] at hb
    obtain ⟨k, hk, hkC, hks⟩ := Pull.exists_of_mem_barOf hb
    have hker : (⟨k, hkC⟩ : ↥(Cen z))⁻¹ * ⟨s, hsC⟩ ∈ (toBar z).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hks, inv_mul_cancel]
    rw [ker_toBar] at hker
    have hO : k⁻¹ * s ∈ Oz z := Subgroup.mem_map.2 ⟨_, hker, rfl⟩
    have hmem : s ∈ (K₁ ⊔ K₂) ⊔ Oz z := by
      have e : s = k * (k⁻¹ * s) := by group
      rw [e]
      exact mul_mem (mem_sup_left hk) (mem_sup_right hO)
    have hSyl := isSylowOf_of_syl2In hM.P_syl
    have hcard := hSyl.card_eq
    have hinf := inf_sup_le_of_odd hM.S_pgroup hcard card_Oz_odd
      (le_normalizer_Oz (sup_le hK₁C hK₂C))
    exact hinf ⟨hsS, hmem⟩
  · intro hs
    have hb : toBar z ⟨s, hsC⟩ ∈ barOf z (K₁ ⊔ K₂) := Pull.mem_barOf hs hsC
    rw [Pull.barOf_sup hK₁C hK₂C] at hb
    exact Pull.mem_pull_of hsS hsC hb

theorem pull_P (hII : II4_4_4_center) (h : Std4 G z S K₁ K₂) :
    pull z S (IVK.Prod3.P (barOf z S) (barOf z K₁) (barOf z K₂)) = Pz S z := by
  have hSC : S ≤ Cen z := h.sylow.le
  have hrp : rigidProduct z = K₁ ⊔ K₂ := h.rigidProduct_eq
  unfold IVK.Prod3.P Pz
  rw [Pull.pull_inf, Pull.pull_barOf_S hSC, hrp]
  ext s
  rw [Subgroup.mem_inf, Subgroup.mem_inf]
  constructor
  · rintro ⟨hsS, hs⟩
    exact ⟨hsS, (mem_pull_sup_iff hII h hsS).1 hs⟩
  · rintro ⟨hsS, hs⟩
    exact ⟨hsS, (mem_pull_sup_iff hII h hsS).2 hs⟩


theorem hasSL2Model_hat (h : Std4 G z S K₁ K₂) {K : Subgroup G} (hK : K = K₁ ∨ K = K₂)
    {P : ℕ → Prop} (hm : HasSL2Model ↥(barOf z K) P) : HasSL2Model (HatT K) P := by
  obtain ⟨F, iF, fF, hP, ⟨e⟩⟩ := hm
  exact ⟨F, iF, fF, hP,
    ⟨(Stage1.Thm4.L97.hatBar (Lh := HatT K) ⟨(h.comp_rigid hK).1, ⟨MulEquiv.refl _⟩⟩).trans e⟩⟩

end Lat

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ : Subgroup G} {a x : G}

theorem l53Lat_of_absData (hII : II4_4_4_center) (_h2A7 : IVK.Lifted.II4_2A7)
    (hctr : Ctr5 G z S K₁ K₂ a x) (_h52 : L52 S K₁ K₂) (haC : a ∈ Cen z)
    (hnotK : toBar z ⟨a, haC⟩ ∉ barOf z K₁ ⊔ barOf z K₂)
    {Y A : Subgroup (CentralizerBar z)} {r : ℕ} (hD : AbsData z S K₁ K₂ a haC Y A r) :
    L53Lat z S K₁ K₂ a (pull z S Y) (pull z S A) := by
  have hstd : Std4 G z S K₁ K₂ := hctr.cfg.std
  have hS : CFSG.ABGLocalTools.IsSylowOf 2 S (Cen z) := hstd.sylow
  have hSC : S ≤ Cen z := hS.le
  have hK₁ : IsPCompIn 2 (Cen z) K₁ := hstd.comp_isPCompIn (Or.inl rfl)
  have hK₂ : IsPCompIn 2 (Cen z) K₂ := hstd.comp_isPCompIn (Or.inr rfl)
  have hYT : Y ≤ barOf z S := hD.Y_le.trans inf_le_left
  have hAT : A ≤ barOf z S := hD.A_le.trans inf_le_left
  have hPT : IVK.Prod3.P (barOf z S) (barOf z K₁) (barOf z K₂) ≤ barOf z S := inf_le_left
  have hP := Lat.pull_P hII hstd
  have hT1 := Lat.pull_T1 hK₁ hS
  refine
    { Y_le := ?_, A_le := ?_, prod := ?_, inter := ?_, Y_normal := ?_, Y_index := ?_, a_mem := ?_,
      A_cyclic := ?_, A_order := ?_, YA_comm := ?_, S_nonab := ?_, field := ?_, swap := ?_,
      a_not_K := ?_ }
  · rw [← hT1]
    exact Pull.pull_mono hD.Y_le
  · rw [← hT1]
    exact Pull.pull_mono hD.A_le
  · rw [← Pull.pull_sup hSC hYT hAT, hD.prod, hT1]
  · rw [← Pull.pull_inf, ← hD.inter, hP]
  · exact Pull.pull_normal hSC hD.Cc.1
  · rw [← hP, Pull.relIndex_pull hSC hYT]
    exact hD.Cc.2.1
  · exact Pull.mem_pull_of hctr.elt.mem haC hD.Cd.1
  · obtain ⟨c, hc, hAc⟩ := hD.Cd.2.1
    obtain ⟨s, hsS, hsC, rfl⟩ := Pull.exists_of_mem_barOf (hAT hc)
    refine ⟨s, Pull.mem_pull_of hsS hsC hc, ?_⟩
    calc pull z S A = pull z S (IVK.Prod3.P (barOf z S) (barOf z K₁) (barOf z K₂) ⊔
          zpowers (toBar z ⟨s, hsC⟩)) := by rw [← hAc]
      _ = pull z S (IVK.Prod3.P (barOf z S) (barOf z K₁) (barOf z K₂)) ⊔
          pull z S (zpowers (toBar z ⟨s, hsC⟩)) :=
        Pull.pull_sup hSC hPT (zpowers_le.2 (hAT hc))
      _ = Pz S z ⊔ zpowers s := by rw [hP, Pull.pull_zpowers hS hsS hsC]
  · rw [← hP, Pull.relIndex_pull hSC hAT]
    exact hD.Cd.2.2
  · intro y hy b hb
    obtain ⟨hyS, hyC, hyY⟩ := Pull.mem_pull.1 hy
    obtain ⟨hbS, hbC, hbA⟩ := Pull.mem_pull.1 hb
    rw [← hP]
    exact (Pull.comm_mem_pull hSC hyS hbS).2 (hD.Ce.1 _ hyY _ hbA)
  · obtain ⟨t, ht, t', ht', hnot⟩ := hD.Cf
    obtain ⟨s, hsS, hsC, rfl⟩ := Pull.exists_of_mem_barOf ht
    obtain ⟨s', hs'S, hs'C, rfl⟩ := Pull.exists_of_mem_barOf ht'
    exact ⟨s, hsS, s', hs'S, fun hmem => hnot ((Pull.comm_mem_pull hSC hsS hs'S).1 hmem)⟩
  · obtain ⟨hr, hodd, hs1, hs2⟩ := hD.Cb
    exact ⟨r, hr, hodd, Lat.hasSL2Model_hat hstd (Or.inl rfl) hs1,
      Lat.hasSL2Model_hat hstd (Or.inr rfl) hs2⟩
  · have hne : ¬ barOf z S ≤ IVK.Prod3.T1 (barOf z S) (barOf z K₁) := not_le_of_gt hD.Ca.1
    obtain ⟨t, htS, htT⟩ := IsConcreteLE.not_le_iff_exists.1 hne
    obtain ⟨s, hsS, hsC, rfl⟩ := Pull.exists_of_mem_barOf htS
    exact ⟨s, hsS, fun hs => htT ⟨htS, (Lat.mem_normalizer_iff_bar hK₁ hsC).1 hs⟩⟩
  · intro ha
    apply hnotK
    rw [← Pull.barOf_sup hK₁.1 hK₂.1]
    exact Pull.mem_barOf ha haC

end CFSG.GH74.GLS.IVK.Lifted32
