module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphRowRange
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphParamFinal
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphParamSpinCover

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule
open CFSG.Quasithin (perfectCore)
open CFSG.LieType.Universal.Spin (cartanD isFiniteType_cartanD quadPlus)
open CFSG.LieType.RootSystem (roots)
open CFSG.LieType.Steinberg.TwistedE6 (sigma rhoPerm)
open scoped commutatorElement

local instance f4PilotGraphRowParamNeZeroRankE6 : NeZero Tag.E6.rank := ⟨by decide⟩

local instance f4PilotGraphRowParamNeZeroRankF4 : NeZero Tag.F4.rank := ⟨by decide⟩

section RankOne

variable {K : Type} [Field K]

theorem e6ScLevi_D4_eq_sup : e6ScLevi K e6D4Nodes = e6ScLevi K e6A3Nodes ⊔ e6ScLevi K {1} := by
  have h : e6D4Nodes = e6A3Nodes ∪ ({1} : Finset (Fin (Tag.rank .E6))) := by decide
  dsimp only [e6ScLevi]
  rw [h, CFSG.LieType.CurtisTits.levi, CFSG.LieType.CurtisTits.levi,
    CFSG.LieType.CurtisTits.levi, Finset.iSup_union]

theorem sigma_eq_self_of_mem_e6ScLevi_one {x : e6Data_valid.minGroup K}
    (hx : x ∈ e6ScLevi K {1}) : sigma K (RingHom.id K) x = x := by
  have hle : e6ScLevi K {1} ≤ (sigma K (RingHom.id K)).eqLocus (MonoidHom.id _) := by
    dsimp only [e6ScLevi]
    rw [CFSG.LieType.CurtisTits.levi_singleton, CFSG.LieType.CurtisTits.rankOne]
    refine sup_le ?_ ?_
    · intro z hz
      obtain ⟨c, rfl⟩ := (e6Data_valid.mem_rootGroup K).1 hz
      change sigma K (RingHom.id K) _ = _
      rw [CFSG.LieType.Steinberg.TwistedE6.sigma_xm_single, e6RhoPerm_one, RingHom.id_apply]
      rfl
    · intro z hz
      obtain ⟨c, rfl⟩ := (e6Data_valid.mem_rootGroup K).1 hz
      change sigma K (RingHom.id K) _ = _
      rw [CFSG.LieType.Steinberg.TwistedE6.sigma_xm_neg_single, e6RhoPerm_one, RingHom.id_apply]
      rfl
  exact hle hx

theorem hm_mem_e6ScLevi_one (t : Kˣ) : e6Data_valid.hm K 1 t ∈ e6ScLevi K {1} := by
  dsimp only [e6ScLevi]
  rw [CFSG.LieType.CurtisTits.levi_singleton]
  exact mul_mem (e6Data_valid.nt_mem_rankOne K 1 t) (inv_mem (e6Data_valid.nt_mem_rankOne K 1 1))

theorem commutator_e6ScLevi_one {t : Kˣ} (ht : t ^ 2 ≠ 1) :
    ⁅e6ScLevi K {1}, e6ScLevi K {1}⁆ = e6ScLevi K {1} := by
  refine le_antisymm (commutator_le_self _) ?_
  have hmem := hm_mem_e6ScLevi_one (K := K) t
  have key : ∀ (γ : Fin (Tag.rank .E6) → ℤ), (γ = Pi.single 1 1 ∨ γ = -Pi.single 1 1) →
      ∀ c : K, e6Data_valid.xm K γ c ∈ ⁅e6ScLevi K {1}, e6ScLevi K {1}⁆ := by
    intro γ hγ c
    have hroot : IsRoot .E6 γ := by
      rcases hγ with rfl | rfl
      exacts [isRoot_single _ 1, isRoot_neg_single _ 1]
    have hw : ((t ^ MinData.toWeight (τ := Tag.E6) γ 1 : Kˣ) : K) ≠ 1 := by
      rcases hγ with rfl | rfl
      · have h2 : MinData.toWeight (τ := Tag.E6) (Pi.single (1 : Fin (Tag.rank .E6)) 1) 1 = 2 := by
          decide
        rw [h2]
        intro h
        apply ht
        exact Units.ext (by simpa using h)
      · have h2 : MinData.toWeight (τ := Tag.E6) (-Pi.single (1 : Fin (Tag.rank .E6)) 1) 1 =
            -2 := by
          decide
        rw [h2]
        intro h
        apply ht
        have h' : ((t ^ (2 : ℤ))⁻¹ : Kˣ) = 1 := by
          rw [← zpow_neg]
          exact Units.ext (by simpa using h)
        rw [inv_eq_one] at h'
        simpa using h'
    set w : K := ((t ^ MinData.toWeight (τ := Tag.E6) γ 1 : Kˣ) : K)
    have hw1 : w - 1 ≠ 0 := sub_ne_zero.2 hw
    set d : K := c / (w - 1)
    have hxmem : e6Data_valid.xm K γ d ∈ e6ScLevi K {1} := by
      rcases hγ with rfl | rfl
      · exact xm_single_mem_scLevi 1 d
      · exact xm_neg_single_mem_scLevi 1 d
    have hc : ⁅e6Data_valid.hm K 1 t, e6Data_valid.xm K γ d⁆ = e6Data_valid.xm K γ c := by
      rw [commutatorElement_def, e6Data_valid.hm_conj_xm K hroot, e6Data_valid.xm_neg,
        ← e6Data_valid.xm_add]
      congr 1
      change w * d + -d = c
      rw [show w * d + -d = (w - 1) * d by ring, mul_div_cancel₀ c hw1]
    rw [← hc]
    exact commutator_mem_commutator hmem hxmem
  dsimp only [e6ScLevi]
  rw [CFSG.LieType.CurtisTits.levi_singleton, CFSG.LieType.CurtisTits.rankOne]
  refine sup_le ?_ ?_
  · intro z hz
    obtain ⟨c, rfl⟩ := (e6Data_valid.mem_rootGroup K).1 hz
    have := key _ (Or.inl rfl) c
    dsimp only [e6ScLevi] at this
    rwa [CFSG.LieType.CurtisTits.levi_singleton, CFSG.LieType.CurtisTits.rankOne] at this
  · intro z hz
    obtain ⟨c, rfl⟩ := (e6Data_valid.mem_rootGroup K).1 hz
    have := key _ (Or.inr rfl) c
    dsimp only [e6ScLevi] at this
    rwa [CFSG.LieType.CurtisTits.levi_singleton, CFSG.LieType.CurtisTits.rankOne] at this

theorem exists_sq_ne_one_of_four_le [Finite K] [CharP K 2] (hq : 4 ≤ Nat.card K) :
    ∃ t : Kˣ, t ^ 2 ≠ 1 := by
  have hcard : 1 < Nat.card Kˣ := by
    have := Nat.card_units K
    omega
  have : Nontrivial Kˣ := Finite.one_lt_card_iff_nontrivial.1 hcard
  obtain ⟨t, ht⟩ := exists_ne (1 : Kˣ)
  refine ⟨t, fun h => ht ?_⟩
  have h' : ((t : K)) ^ 2 = 1 ^ 2 := by
    rw [one_pow, ← Units.val_pow_eq_pow_val, h, Units.val_one]
  exact Units.ext (CharTwo.sq_injective h')

end RankOne

section A3

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem exists_chainNode_A3 : ∀ j ∈ e6A3Nodes, ∃ k : Fin 5, (k = 1 ∨ k = 2 ∨ k = 3) ∧
    E6Pilot.chainNode k = j := by
  decide

theorem graphSwapPerm_mem_sl6BlockAIdx : ∀ k : Fin 5, (k = 1 ∨ k = 2 ∨ k = 3) →
    graphSwapPerm k.castSucc ∈ sl6BlockAIdx ∧ graphSwapPerm k.succ ∈ sl6BlockAIdx := by
  decide

theorem e6ScLevi_A3_le_map_sl6BlockA :
    e6ScLevi K e6A3Nodes ≤ (sl6BlockA K).map (graphParamHom K (RingEquiv.refl K)) := by
  dsimp only [e6ScLevi]
  rw [CFSG.LieType.CurtisTits.levi]
  refine iSup₂_le fun j hj => ?_
  obtain ⟨k, hk, rfl⟩ := exists_chainNode_A3 j hj
  obtain ⟨h1, h2⟩ := graphSwapPerm_mem_sl6BlockAIdx k hk
  have hne : graphSwapPerm k.castSucc ≠ graphSwapPerm k.succ :=
    graphSwapPerm.injective.ne (Fin.castSucc_lt_succ (i := k)).ne
  rw [CFSG.LieType.CurtisTits.rankOne]
  refine sup_le ?_ ?_
  · intro z hz
    obtain ⟨c, rfl⟩ := (e6Data_valid.mem_rootGroup K).1 hz
    refine ⟨Matrix.SpecialLinearGroup.transvection hne c,
      transvection_mem_sl6BlockA hne h1 h2 c, ?_⟩
    rw [graphParamHom_transvection, Equiv.symm_apply_apply, Equiv.symm_apply_apply,
      E6Pilot.a5Root_castSucc_succ]
    rfl
  · intro z hz
    obtain ⟨c, rfl⟩ := (e6Data_valid.mem_rootGroup K).1 hz
    refine ⟨Matrix.SpecialLinearGroup.transvection hne.symm c,
      transvection_mem_sl6BlockA hne.symm h2 h1 c, ?_⟩
    rw [graphParamHom_transvection, Equiv.symm_apply_apply, Equiv.symm_apply_apply,
      E6Pilot.a5Root_succ_castSucc]
    rfl

end A3

section D4

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

omit
  [Finite G] [CharP K 2] in
theorem neighbourFrame_eq {e e₁ : L ≃* adjointGroup .F4 K} {N : AmalgamNeighbour}
    (he₁ : IsNeighbourFrame e e₁ N) :
    neighbourCore e N = neighbourCore e₁ .X ∧ pieceSpan e₁ = pieceSpan e := by
  cases N with
  | X =>
    have h : e₁ = e := he₁
    subst h
    exact ⟨rfl, rfl⟩
  | Y =>
    obtain ⟨hc, h⟩ := he₁
    subst h
    exact ⟨neighbourCore_Y_eq_X e, pieceSpan_trans_graphAutF4_symm e⟩
  | X' => exact he₁.elim

omit
  [Finite K] [CharP K 2] in
theorem perfectCore_neighbourCore_inf_centralizer_le {t : G} {f : ℕ} (hw : F4Work L K t f)
    (hf : 2 ≤ f) (e : L ≃* adjointGroup .F4 K) {N : AmalgamNeighbour} (hN : N ≠ .X') :
    perfectCore (neighbourCore e N ⊓ centralizer ({t} : Set G)) ≤ L := by
  cases N with
  | X => rw [perfectCore_neighbourCore_inf_centralizer_X hw hf e]; exact modelToG_le e _
  | Y => rw [perfectCore_neighbourCore_inf_centralizer_Y hw hf e]; exact modelToG_le e _
  | X' => exact absurd rfl hN

theorem neighbourCore_le_pieceSpan_of_D4 {t : G} {f : ℕ} (hw : F4Work L K t f) (hf : 2 ≤ f)
    (e : L ≃* adjointGroup .F4 K) {N₁ N₂ : AmalgamNeighbour}
    (hN : (N₁ = .X ∧ N₂ = .Y) ∨ (N₁ = .Y ∧ N₂ = .X)) {e₁ : L ≃* adjointGroup .F4 K}
    (he₁ : IsNeighbourFrame e e₁ N₁) {ΦA : e6ScLevi K e6A5Nodes →* G}
    (hrA : ΦA.range = neighbourCore e N₁) (hnA : IsLeviNormalizedA e₁ ΦA)
    {ΦD : e6ScLevi K e6D4Nodes →* G} (hrD : ΦD.range = neighbourCore e N₂)
    (htw : (∀ x : e6ScLevi K e6A3Nodes, scLeviRestrict ΦA e6A3Nodes_subset_e6A5Nodes x =
        scLeviRestrict ΦD e6A3Nodes_subset_e6D4Nodes x) ∨
      (∀ x y : e6ScLevi K e6A3Nodes, (y : e6Data_valid.minGroup K) = sigma K (RingHom.id K) x →
        scLeviRestrict ΦA e6A3Nodes_subset_e6A5Nodes x =
          scLeviRestrict ΦD e6A3Nodes_subset_e6D4Nodes y))
    (hcD : ∀ x y : e6ScLevi K e6D4Nodes,
      (y : e6Data_valid.minGroup K) = sigma K (RingHom.id K) x → t * ΦD x * t⁻¹ = ΦD y) :
    neighbourCore e N₂ ≤ pieceSpan e := by
  have hq : 4 ≤ Nat.card K := by
    rw [hw.card_eq]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨hframe, hspan⟩ := neighbourFrame_eq he₁
  have hN₂ : N₂ ≠ .X' := by
    rcases hN with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> decide
  have hB := (neighbourCore_X_le_pieceSpan_of_isLeviNormalizedA hq e₁ (hrA.trans hframe) hnA).2
  have hM : pieceCore e₁ {1, 2} ≤ pieceSpan e := by
    rw [← hspan]
    exact le_iSup (fun J : {J : Finset (Fin (Tag.rank .F4)) // J.card ≤ 2} => pieceCore e₁ J.1)
      ⟨{1, 2}, by decide⟩
  have hA3 : ∀ x : e6ScLevi K e6A3Nodes,
      scLeviRestrict ΦA e6A3Nodes_subset_e6A5Nodes x ∈ pieceSpan e := by
    intro x
    obtain ⟨b, hb, hbx⟩ := e6ScLevi_A3_le_map_sl6BlockA x.2
    have hx : (⟨(x : e6Data_valid.minGroup K),
        CFSG.LieType.CurtisTits.levi_mono _ e6A3Nodes_subset_e6A5Nodes x.2⟩ :
          e6ScLevi K e6A5Nodes) = graphParamEquiv K (RingEquiv.refl K) b :=
      Subtype.ext hbx.symm
    rw [scLeviRestrict_apply, hx]
    exact hM (hB ⟨b, hb, rfl⟩)
  have hD3 : ∀ y : e6ScLevi K e6A3Nodes,
      scLeviRestrict ΦD e6A3Nodes_subset_e6D4Nodes y ∈ pieceSpan e := by
    intro y
    rcases htw with h | h
    · rw [← h y]
      exact hA3 y
    · have hσy : sigma K (RingHom.id K) (y : e6Data_valid.minGroup K) ∈ e6ScLevi K e6A3Nodes :=
        sigma_mem_e6ScLevi (fun i hi => by revert i; decide) y.2
      have hyy : (y : e6Data_valid.minGroup K) =
          sigma K (RingHom.id K) (sigma K (RingHom.id K) (y : e6Data_valid.minGroup K)) :=
        (CFSG.LieType.Steinberg.TwistedE6.sigma_sigma (RingHom.id K) (fun _ => rfl) _).symm
      rw [← h ⟨_, hσy⟩ y hyy]
      exact hA3 _
  have hD1 : (scLeviRestrict ΦD one_subset_e6D4Nodes).range ≤ L := by
    obtain ⟨s, hs⟩ := exists_sq_ne_one_of_four_le hq
    have hperf : Group.IsPerfect (e6ScLevi K {1}) :=
      Subgroup.isPerfect_iff.2 (commutator_e6ScLevi_one hs)
    have hperf' : ⁅(scLeviRestrict ΦD one_subset_e6D4Nodes).range,
        (scLeviRestrict ΦD one_subset_e6D4Nodes).range⁆ =
        (scLeviRestrict ΦD one_subset_e6D4Nodes).range :=
      Subgroup.isPerfect_iff.1 (Group.IsPerfect.range _)
    refine (CFSG.Quasithin.le_perfectCore_of_perfect ?_ hperf').trans
      (perfectCore_neighbourCore_inf_centralizer_le hw hf e hN₂)
    rintro _ ⟨y, rfl⟩
    refine mem_inf.2 ⟨?_, ?_⟩
    · rw [← hrD, scLeviRestrict_apply]
      exact ⟨_, rfl⟩
    · rw [mem_centralizer_iff]
      rintro _ rfl
      have h := hcD ⟨(y : e6Data_valid.minGroup K),
          CFSG.LieType.CurtisTits.levi_mono _ one_subset_e6D4Nodes y.2⟩
        ⟨(y : e6Data_valid.minGroup K),
          CFSG.LieType.CurtisTits.levi_mono _ one_subset_e6D4Nodes y.2⟩
        (sigma_eq_self_of_mem_e6ScLevi_one y.2).symm
      rw [scLeviRestrict_apply]
      rw [mul_inv_eq_iff_eq_mul] at h
      exact h
  set S : Subgroup (e6Data_valid.minGroup K) :=
    ((pieceSpan e).comap ΦD).map (e6ScLevi K e6D4Nodes).subtype with hS
  have hDS : e6ScLevi K e6D4Nodes ≤ S := by
    rw [e6ScLevi_D4_eq_sup]
    refine sup_le ?_ ?_
    · intro y hy
      exact ⟨⟨y, CFSG.LieType.CurtisTits.levi_mono _ e6A3Nodes_subset_e6D4Nodes hy⟩,
        hD3 ⟨y, hy⟩, rfl⟩
    · intro y hy
      refine ⟨⟨y, CFSG.LieType.CurtisTits.levi_mono _ one_subset_e6D4Nodes hy⟩, ?_, rfl⟩
      exact le_pieceSpan hq e (hD1 ⟨⟨y, hy⟩, rfl⟩)
  rw [← hrD]
  rintro _ ⟨y, rfl⟩
  obtain ⟨y', hy', hyy'⟩ := hDS y.2
  rw [show y = y' from Subtype.ext hyy'.symm]
  exact hy'

theorem range_sup_eq_pieceSpan_of_spinNorm {t : G} {f : ℕ} (hw : F4Work L K t f) (hf : 2 ≤ f)
    (e : L ≃* adjointGroup .F4 K) {N₁ N₂ : AmalgamNeighbour}
    (hN : (N₁ = .X ∧ N₂ = .Y) ∨ (N₁ = .Y ∧ N₂ = .X)) {e₁ : L ≃* adjointGroup .F4 K}
    (he₁ : IsNeighbourFrame e e₁ N₁) {ΦA : e6ScLevi K e6A5Nodes →* G}
    (hrA : ΦA.range = neighbourCore e N₁) (hnA : IsLeviNormalizedA e₁ ΦA)
    {ΦD : e6ScLevi K e6D4Nodes →* G} (hrD : ΦD.range = neighbourCore e N₂)
    (htw : (∀ x : e6ScLevi K e6A3Nodes, scLeviRestrict ΦA e6A3Nodes_subset_e6A5Nodes x =
        scLeviRestrict ΦD e6A3Nodes_subset_e6D4Nodes x) ∨
      (∀ x y : e6ScLevi K e6A3Nodes, (y : e6Data_valid.minGroup K) = sigma K (RingHom.id K) x →
        scLeviRestrict ΦA e6A3Nodes_subset_e6A5Nodes x =
          scLeviRestrict ΦD e6A3Nodes_subset_e6D4Nodes y))
    (hcD : ∀ x y : e6ScLevi K e6D4Nodes,
      (y : e6Data_valid.minGroup K) = sigma K (RingHom.id K) x → t * ΦD x * t⁻¹ = ΦD y) :
    ΦA.range ⊔ ΦD.range = pieceSpan e := by
  have hq : 4 ≤ Nat.card K := by
    rw [hw.card_eq]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨hframe, hspan⟩ := neighbourFrame_eq he₁
  have h₁ : neighbourCore e N₁ ≤ pieceSpan e := by
    rw [hframe, ← hspan]
    exact (neighbourCore_X_le_pieceSpan_of_isLeviNormalizedA hq e₁ (hrA.trans hframe) hnA).1
  have h₂ := neighbourCore_le_pieceSpan_of_D4 hw hf e hN he₁ hrA hnA hrD htw hcD
  refine le_antisymm (sup_le (hrA ▸ h₁) (hrD ▸ h₂)) ?_
  rw [hrA, hrD]
  refine (pieceSpan_le_sup_neighbourCore hq e).trans ?_
  rcases hN with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact le_rfl
  · exact (sup_comm _ _).le

omit
  [Finite G] in
theorem range_comp_alpha_spinEquivD4_symm {ΦY : spinGroup (quadPlus 4 K) →* G}
    (α : MulAut (spinGroup (quadPlus 4 K))) {E : Subgroup G} (hrY : ΦY.range = E) :
    ((ΦY.comp α.toMonoidHom).comp (spinEquivD4 K).symm.toMonoidHom).range = E := by
  rw [range_comp_spinEquivD4_symm, MonoidHom.range_comp, MonoidHom.range_eq_top.2 α.surjective,
    ← MonoidHom.range_eq_map, hrY]

theorem e6GraphRowParamInput_of_spinNorm (h : E6GraphRowSpinNormInput) : E6GraphRowParamInput := by
  intro G _ _ L K _ _ _ e t f hw hf hk
  rcases hk with ⟨h6, h8⟩ | ⟨h8, h6⟩
  · obtain ⟨ΦA, hrA, hkA, hcA, hnA⟩ := exists_graphParamA_normalized_X hw hf e h6
    obtain ⟨ΦY, hrY, hiY⟩ := exists_spin8_cover_neighbourCore hw hf e (N := .Y) (by decide) h8
    obtain ⟨α, hc, htw, hcomm⟩ :=
      h G L K e t f hw hf .X .Y (Or.inl ⟨rfl, rfl⟩) h6 h8 e rfl ΦA hrA hkA hcA hnA ΦY hrY hiY
    have hrD : ((ΦY.comp α.toMonoidHom).comp (spinEquivD4 K).symm.toMonoidHom).range =
        neighbourCore e .Y := range_comp_alpha_spinEquivD4_symm α hrY
    have hcD := conj_comp_spinEquivD4_symm (ΦY := ΦY.comp α.toMonoidHom) hc
    exact ⟨ΦA, (ΦY.comp α.toMonoidHom).comp (spinEquivD4 K).symm.toMonoidHom,
      { agree_or_twist := htw
        conjA := hcA
        conjD := hcD
        comm := hcomm
        range_sup := range_sup_eq_pieceSpan_of_spinNorm hw hf e (Or.inl ⟨rfl, rfl⟩)
          (e₁ := e) rfl hrA hnA hrD htw hcD }⟩
  · have hc2 : CharP K CFSG.LieType.Ree.ReeTag.F4.prime := ‹CharP K 2›
    obtain ⟨ΦA, hrA, hkA, hcA, hnA⟩ := exists_graphParamA_normalized_Y hw hf e h6
    obtain ⟨ΦY, hrY, hiY⟩ := exists_spin8_cover_neighbourCore hw hf e (N := .X) (by decide) h8
    obtain ⟨α, hc, htw, hcomm⟩ :=
      h G L K e t f hw hf .Y .X (Or.inr ⟨rfl, rfl⟩) h6 h8 (e.trans (graphAutF4 K).symm)
        ⟨hc2, rfl⟩ ΦA hrA hkA hcA hnA ΦY hrY hiY
    have hrD : ((ΦY.comp α.toMonoidHom).comp (spinEquivD4 K).symm.toMonoidHom).range =
        neighbourCore e .X := range_comp_alpha_spinEquivD4_symm α hrY
    have hcD := conj_comp_spinEquivD4_symm (ΦY := ΦY.comp α.toMonoidHom) hc
    exact ⟨ΦA, (ΦY.comp α.toMonoidHom).comp (spinEquivD4 K).symm.toMonoidHom,
      { agree_or_twist := htw
        conjA := hcA
        conjD := hcD
        comm := hcomm
        range_sup := range_sup_eq_pieceSpan_of_spinNorm hw hf e (Or.inr ⟨rfl, rfl⟩)
          (e₁ := e.trans (graphAutF4 K).symm) ⟨hc2, rfl⟩ hrA hnA hrD htw hcD }⟩

end D4

section Reduction

theorem e6RowCTQuotInput_of_spinNorm (h : E6GraphRowSpinNormInput) : E6RowCTQuotInput :=
  e6RowCTQuotInput_of_paramInput (e6GraphRowParamInput_of_spinNorm h)

end Reduction

end CFSG.SeitzReduction.F4Pilot
