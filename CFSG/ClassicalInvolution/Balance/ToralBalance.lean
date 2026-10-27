module

public import CFSG.ClassicalInvolution.Balance.Layer
public import CFSG.ClassicalInvolution.Balance.LocalBalance.Faithful
public import CFSG.ClassicalInvolution.Balance.LocalBalance.Fixed
public import CFSG.ClassicalInvolution.Balance.LocalBalance.Normalizes

public section

namespace CFSG.ClassicalInvolution.Balance

open CFSG CFSG.Open CFSG.LocalCores CFSG.ComponentClassification CFSG.Assembly.Dichotomy
open CFSG.ClassicalInvolution.Balance.LocalBalance
open scoped commutatorElement

section Layers

variable {X : Type*} [Group X] [Finite X]

@[expose] noncomputable def centralizerLayer (f : X) : Subgroup X :=
  (Layer.subgroup ↥(Subgroup.centralizer ({f} : Set X))).map
    (Subgroup.centralizer ({f} : Set X)).subtype

theorem commute_of_mem_involutionOddCore_of_mem_centralizerLayer {f d x : X}
    (hd : d ∈ involutionOddCore f) (hx : x ∈ centralizerLayer f) : d * x = x * d := by
  set C : Subgroup X := Subgroup.centralizer ({f} : Set X) with hC
  obtain ⟨d', hd', rfl⟩ := hd
  obtain ⟨x', hx', rfl⟩ := hx
  have hsolv : Group.IsSolvable (componentClassificationOddCore ↥C) :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard _ (OddCore.odd_card ↥C)
  have hsub : IsSubnormal (componentClassificationOddCore ↥C) ⊤ :=
    isSubnormal_of_normal_subgroupOf le_top Subgroup.normal_subgroupOf
  have h := Layer.commutes_with_solvable_subnormal _ hsub
  have hmem : ⁅x', d'⁆ ∈ ⁅Layer.subgroup ↥C, componentClassificationOddCore ↥C⁆ :=
    Subgroup.commutator_mem_commutator hx' hd'
  rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
  exact congrArg Subtype.val hmem.symm

theorem deltaCore_le_centralizer_iSup_centralizerLayer (F : Subgroup X) :
    deltaCore F ≤ Subgroup.centralizer
      ((⨆ f ∈ F, ⨆ (_ : f ≠ 1), centralizerLayer f : Subgroup X) : Set X) := by
  rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm,
    Subgroup.commutator_eq_bot_iff_le_centralizer]
  refine iSup₂_le fun f hf => iSup_le fun hf1 => fun x hx => ?_
  rw [Subgroup.mem_centralizer_iff]
  intro d hd
  exact commute_of_mem_involutionOddCore_of_mem_centralizerLayer
    (deltaCore_le_involutionOddCore hf hf1 hd) hx

omit [Finite X] in
theorem layer_map_le_of_isSubnormal {W Y : Subgroup X} (hWY : W ≤ Y) (hsub : IsSubnormal W Y) :
    (Layer.subgroup ↥W).map W.subtype ≤ (Layer.subgroup ↥Y).map Y.subtype := by
  have hsub' : IsSubnormal (W.subgroupOf Y) ⊤ :=
    (CFSG.ComponentClassification.LBalance.subnormal_subgroupOf_iff hWY).mpr hsub
  let e : ↥W ≃* ↥(W.subgroupOf Y) := (Subgroup.subgroupOfEquivOfLe hWY).symm
  refine Subgroup.map_le_iff_le_comap.mpr (sSup_le fun M hM => ?_)
  refine Subgroup.map_le_iff_le_comap.mp ?_
  have h1 : IsComponentOf (M.map e.toMonoidHom) ⊤ :=
    (LocalComponents.equiv_iff e M).mpr hM
  have h2 := LocalComponents.of_subnormal_subgroup (W.subgroupOf Y) hsub' _ h1
  have h3 := Subgroup.map_mono (f := Y.subtype) (Layer.component_le h2)
  refine le_trans (le_of_eq ?_) h3
  rw [Subgroup.map_map, Subgroup.map_map]
  rfl

theorem deltaCore_eq_bot_of_faithful_centralized (hO : CFSG.pPrimeCore 2 X = ⊥) {F : Subgroup X}
    (hF4 : Nat.card F = 4) (hF2 : ∀ f ∈ F, f * f = 1)
    (hfaith : ∀ L : Subgroup X, IsComponent L → F ≤ Subgroup.normalizer (L : Set X) →
      (∀ f ∈ F, f ≠ 1 → ¬ ∀ x ∈ L, f * x = x * f) →
      ∀ d ∈ deltaCore F, conjSub d L = L → ∀ x ∈ L, d * x = x * d) :
    deltaCore F = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨f₀, hf₀F, hf₀1⟩ : ∃ f ∈ F, f ≠ 1 := by
    have : Nontrivial F := Finite.one_lt_card_iff_nontrivial.mp (by rw [hF4]; norm_num)
    obtain ⟨⟨f, hf⟩, hne⟩ := exists_ne (1 : F)
    exact ⟨f, hf, fun h => hne (Subtype.ext h)⟩
  have hDodd : Odd (Nat.card (deltaCore F)) := odd_card_deltaCore hf₀F hf₀1
  have hDF : ∀ f ∈ F, f ≠ 1 → deltaCore F ≤ involutionOddCore f :=
    fun f hf hf1 => deltaCore_le_involutionOddCore hf hf1
  have hord : ∀ f ∈ F, f ≠ 1 → orderOf f = 2 := fun f hf hf1 =>
    orderOf_eq_prime (by rw [sq]; exact hF2 f hf) hf1
  have hQ : deltaCore F ≤ Subgroup.centralizer (CFSG.pCore 2 X : Set X) := by
    intro d hd
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have := commute_pCore_of_mem_involutionOddCore (hord f₀ hf₀F hf₀1)
      (deltaCore_le_involutionOddCore hf₀F hf₀1 hd) q hq
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this.symm
  have hL : ∀ L : Subgroup X, IsComponent L → deltaCore F ≤ Subgroup.centralizer (L : Set X) := by
    intro L hL
    have key : ∀ d ∈ deltaCore F, ∀ x ∈ L, d * x = x * d := by
      by_cases hcen : ∃ f ∈ F, f ≠ 1 ∧ ∀ x ∈ L, f * x = x * f
      · obtain ⟨f, hfF, hf1, hfL⟩ := hcen
        have hLC : L ≤ Subgroup.centralizer ({f} : Set X) := fun x hx =>
          Subgroup.mem_centralizer_singleton_iff.mpr (hfL x hx).symm
        intro d hd
        exact commute_of_isComponent_centralizer (hDF f hfF hf1 hd) hLC
          (component_overgroup hL hLC)
      · by_cases hmov : ∃ f ∈ F, conjSub f L ≠ L
        · obtain ⟨f, hfF, hfne⟩ := hmov
          have hf1 : f ≠ 1 := fun h => hfne (by rw [h, conjSub_one])
          intro d hd
          exact commute_of_moved hL (hF2 f hfF) hfne (hDF f hfF hf1 hd)
        · push Not at hcen hmov
          have hDn : ∀ d ∈ deltaCore F, conjSub d L = L := fun d hd =>
            conjSub_eq_of_mem_involutionOddCore hL (hF2 f₀ hf₀F) (hmov f₀ hf₀F)
              (hDF f₀ hf₀F hf₀1 hd)
          have hfaith' : ∀ f ∈ F, f ≠ 1 → ¬ ∀ x ∈ L, f * x = x * f := by
            intro f hf hf1 h
            obtain ⟨x, hx, hxne⟩ := hcen f hf hf1
            exact hxne (h x hx)
          have hFn : F ≤ Subgroup.normalizer (L : Set X) := fun f hf =>
            mem_normalizer_of_conjSub_eq (hmov f hf)
          intro d hd x hx
          exact hfaith L hL hFn hfaith' d hd (hDn d hd) x hx
    intro d hd x hx
    exact (key d hd x hx).symm
  exact eq_bot_of_centralizes_pCore_of_centralizes_components hO hDodd hQ hL

theorem deltaCore_eq_bot_of_le_centralizerLayers (hO : CFSG.pPrimeCore 2 X = ⊥) {F : Subgroup X}
    (hF4 : Nat.card F = 4) (hF2 : ∀ f ∈ F, f * f = 1)
    (hgen : ∀ L : Subgroup X, IsComponent L → F ≤ Subgroup.normalizer (L : Set X) →
      (∀ f ∈ F, f ≠ 1 → ¬ ∀ x ∈ L, f * x = x * f) →
      L ≤ ⨆ f ∈ F, ⨆ (_ : f ≠ 1), centralizerLayer f) :
    deltaCore F = ⊥ :=
  deltaCore_eq_bot_of_faithful_centralized hO hF4 hF2 fun L hL hFn hfaith _ hd _ x hx =>
    (Subgroup.mem_centralizer_iff.mp (deltaCore_le_centralizer_iSup_centralizerLayer F hd) x
      (hgen L hL hFn hfaith hx)).symm

theorem deltaCore_eq_bot_of_normal_generated {N F : Subgroup X} [N.Normal]
    (hN : Subgroup.centralizer (N : Set X) = ⊥)
    (hgen : N ≤ ⨆ f ∈ F, ⨆ (_ : f ≠ 1),
      (Layer.subgroup ↥(N ⊓ Subgroup.centralizer ({f} : Set X))).map
        (N ⊓ Subgroup.centralizer ({f} : Set X)).subtype) :
    deltaCore F = ⊥ := by
  refine le_bot_iff.mp ?_
  rw [← hN]
  refine (deltaCore_le_centralizer_iSup_centralizerLayer F).trans (Subgroup.centralizer_le ?_)
  refine hgen.trans (iSup₂_le fun f hf => iSup_le fun hf1 => ?_)
  refine le_iSup₂_of_le f hf (le_iSup_of_le hf1 ?_)
  have hWC : N ⊓ Subgroup.centralizer ({f} : Set X) ≤ Subgroup.centralizer ({f} : Set X) :=
    inf_le_right
  refine layer_map_le_of_isSubnormal hWC ?_
  refine isSubnormal_of_normal_subgroupOf hWC ?_
  rw [Subgroup.inf_subgroupOf_right]
  exact Subgroup.normal_subgroupOf

end Layers

section Placement

variable {Y : Type} [Group Y] [Finite Y]

theorem le_layer_of_l2PrimeBalance_of_isTwoComponent_quasisimple (hLB : L2PrimeBalance)
    {W : Type} [Group W] [Finite W] {A K : Subgroup W} (hA : IsPGroup 2 A)
    (hKA : K ≤ Subgroup.centralizer (A : Set W))
    (hKsub : IsSubnormal K (Subgroup.centralizer (A : Set W))) (hKperf : commutator K = ⊤)
    (hKq : CFSG.Open.IsQuasisimple (K ⧸ componentClassificationOddCore K))
    (hB : ∀ M : Subgroup W, TwoComponents.IsTwoComponent M → CFSG.Open.IsQuasisimple M) :
    K ≤ Layer.subgroup W := by
  have h1 : K ≤ TwoLayer.subgroup W := le_twoLayer_of_l2PrimeBalance hLB hA hKA hKsub hKperf hKq
  have hbad : TwoComponents.badSubgroup W = ⊥ :=
    le_antisymm (sSup_le fun M hM => (hM.2 (hB M hM.1)).elim) bot_le
  have h2 : TwoLayer.subgroup W = TwoLayer.goodSubgroup W := by
    rw [← TwoLayer.good_sup_bad, hbad, sup_bot_eq]
  exact h1.trans (h2 ▸ TwoLayer.good_le_layer _)

theorem le_centralizerLayer_of_l2PrimeBalance (hLB : L2PrimeBalance) {L K A : Subgroup Y} {f : Y}
    (hL : IsSubnormal L ⊤) (hKL : K ≤ L) (hKf : K ≤ Subgroup.centralizer ({f} : Set Y))
    (hAK : A ≤ K) (hA : IsPGroup 2 A) (hKA : K ≤ Subgroup.centralizer (A : Set Y))
    (hKsub : IsSubnormal K (Subgroup.centralizer (A : Set Y))) (hKperf : commutator K = ⊤)
    (hKq : CFSG.Open.IsQuasisimple (K ⧸ componentClassificationOddCore K))
    (hB : ∀ M : Subgroup ↥(L ⊓ Subgroup.centralizer ({f} : Set Y)),
      TwoComponents.IsTwoComponent M → CFSG.Open.IsQuasisimple M) :
    K ≤ centralizerLayer f := by
  set C : Subgroup Y := Subgroup.centralizer ({f} : Set Y) with hC
  set W : Subgroup Y := L ⊓ C with hW
  have hKW : K ≤ W := le_inf hKL hKf
  have hWC : W ≤ C := inf_le_right
  have hAW : A ≤ W := hAK.trans hKW
  let A' : Subgroup ↥W := A.subgroupOf W
  let K' : Subgroup ↥W := K.subgroupOf W
  let e : K' ≃* K := Subgroup.subgroupOfEquivOfLe hKW
  have hA' : IsPGroup 2 A' := hA.of_equiv (Subgroup.subgroupOfEquivOfLe hAW).symm
  have hKA' : K' ≤ Subgroup.centralizer (A' : Set ↥W) := by
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hKA hk) (a : Y) ha)
  have hcent : (Subgroup.centralizer (A : Set Y)).subgroupOf W =
      Subgroup.centralizer (A' : Set ↥W) := by
    ext y
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
    constructor
    · intro hy a ha
      exact Subtype.ext (hy (a : Y) ha)
    · intro hy h hh
      exact congrArg Subtype.val (hy ⟨h, hAW hh⟩ hh)
  have hKsub' : IsSubnormal K' (Subgroup.centralizer (A' : Set ↥W)) := by
    have h := CFSG.ComponentClassification.LBalance.subnormal_subgroupOf hKsub W
    rwa [hcent] at h
  have hKperf' : commutator K' = ⊤ := by
    have : Group.IsPerfect K := ⟨hKperf⟩
    have : Group.IsPerfect K' :=
      Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
    exact Group.IsPerfect.commutator_eq_top
  have hKq' : CFSG.Open.IsQuasisimple (↥K' ⧸ componentClassificationOddCore K') :=
    Components.quasisimple_of_equiv
      (QuotientGroup.congr (componentClassificationOddCore K') (componentClassificationOddCore K)
        e (OddCore.equiv_invariant e)) hKq
  have h1 : K' ≤ Layer.subgroup ↥W :=
    le_layer_of_l2PrimeBalance_of_isTwoComponent_quasisimple hLB hA' hKA' hKsub' hKperf' hKq' hB
  have hWsub : IsSubnormal W C := by
    refine (CFSG.ComponentClassification.LBalance.subnormal_subgroupOf_iff hWC).mp ?_
    have h := CFSG.ComponentClassification.LBalance.subnormal_subgroupOf hL C
    rwa [Subgroup.top_subgroupOf, ← Subgroup.inf_subgroupOf_right L C] at h
  have h2 := layer_map_le_of_isSubnormal hWC hWsub
  have h3 : K ≤ (Layer.subgroup ↥W).map W.subtype := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hKW]
    exact Subgroup.map_mono h1
  exact h3.trans h2

end Placement

section Members

structure IsInvolutionMember {X : Type*} [Group X] (K : Subgroup X) : Prop where
  perfect : commutator K = ⊤
  quasisimple : CFSG.Open.IsQuasisimple (K ⧸ componentClassificationOddCore K)
  exists_involution : ∃ z ∈ K, z * z = 1 ∧ (∀ k ∈ K, z * k = k * z) ∧
    IsSubnormal K (Subgroup.centralizer ({z} : Set X))

@[expose] def InvolutionCentralizerB {X : Type*} [Group X] (L : Subgroup X) : Prop :=
  ∀ f : X, f ≠ 1 → f * f = 1 → f ∈ Subgroup.normalizer (L : Set X) →
    ∀ M : Subgroup ↥(L ⊓ Subgroup.centralizer ({f} : Set X)),
      TwoComponents.IsTwoComponent M → CFSG.Open.IsQuasisimple M

theorem IsInvolutionMember.le_centralizerLayer (hLB : L2PrimeBalance) {Y : Type} [Group Y]
    [Finite Y] {L K : Subgroup Y} {f : Y} (hK : IsInvolutionMember K) (hL : IsSubnormal L ⊤)
    (hKL : K ≤ L) (hKf : K ≤ Subgroup.centralizer ({f} : Set Y))
    (hB : ∀ M : Subgroup ↥(L ⊓ Subgroup.centralizer ({f} : Set Y)),
      TwoComponents.IsTwoComponent M → CFSG.Open.IsQuasisimple M) :
    K ≤ centralizerLayer f := by
  obtain ⟨z, hzK, hz2, hzc, hzsub⟩ := hK.exists_involution
  have hcentz : Subgroup.centralizer ((Subgroup.zpowers z : Subgroup Y) : Set Y) =
      Subgroup.centralizer ({z} : Set Y) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hA : IsPGroup 2 (Subgroup.zpowers z) := isPGroup_zpowers_of_mul_self_eq_one hz2
  have hzK' : Subgroup.zpowers z ≤ K := Subgroup.zpowers_le.mpr hzK
  have hKA : K ≤ Subgroup.centralizer ((Subgroup.zpowers z : Subgroup Y) : Set Y) := by
    rw [hcentz]
    exact fun k hk => Subgroup.mem_centralizer_singleton_iff.mpr (hzc k hk).symm
  have hsub : IsSubnormal K
      (Subgroup.centralizer ((Subgroup.zpowers z : Subgroup Y) : Set Y)) := by
    rw [hcentz]
    exact hzsub
  exact le_centralizerLayer_of_l2PrimeBalance hLB hL hKL hKf hzK' hA hKA hsub hK.perfect
    hK.quasisimple hB

@[expose] def OddCentralizerFree {Y : Type*} [Group Y] (F L : Subgroup Y) : Prop :=
  ∀ d : Y, Odd (orderOf d) → conjSub d L = L →
    (∀ x ∈ L ⊓ ⨆ f ∈ F, ⨆ (_ : f ≠ 1), centralizerLayer f, d * x = x * d) →
    ∀ x ∈ L, d * x = x * d

@[expose] def OddCentralizerFreeMembers {Y : Type*} [Group Y] (F L : Subgroup Y) : Prop :=
  ∀ d : Y, Odd (orderOf d) → conjSub d L = L →
    (∀ K : Subgroup Y, K ≤ L → IsInvolutionMember K →
      (∃ f ∈ F, f ≠ 1 ∧ K ≤ Subgroup.centralizer ({f} : Set Y)) → ∀ k ∈ K, d * k = k * d) →
    ∀ x ∈ L, d * x = x * d

theorem OddCentralizerFree.of_le_layers {Y : Type*} [Group Y] {F L : Subgroup Y}
    (h : L ≤ ⨆ f ∈ F, ⨆ (_ : f ≠ 1), centralizerLayer f) : OddCentralizerFree F L :=
  fun _ _ _ hd x hx => hd x ⟨hx, h hx⟩

theorem OddCentralizerFree.of_members (hLB : L2PrimeBalance) {Y : Type} [Group Y] [Finite Y]
    {F L : Subgroup Y} (hL : IsComponent L)
    (hB : ∀ f ∈ F, f ≠ 1 → ∀ M : Subgroup ↥(L ⊓ Subgroup.centralizer ({f} : Set Y)),
      TwoComponents.IsTwoComponent M → CFSG.Open.IsQuasisimple M)
    (hmem : OddCentralizerFreeMembers F L) : OddCentralizerFree F L := by
  have hLsub : IsSubnormal L ⊤ := ((CFSG.isComponent_iff_open L).mp hL).2.1
  intro d hdodd hdL hdlayers
  refine hmem d hdodd hdL (fun K hKL hK ⟨f, hfF, hf1, hKf⟩ k hk => ?_)
  have hlayer := hK.le_centralizerLayer hLB hLsub hKL hKf (hB f hfF hf1)
  have hle : K ≤ ⨆ f ∈ F, ⨆ (_ : f ≠ 1), centralizerLayer f :=
    le_iSup₂_of_le f hfF (le_iSup_of_le hf1 hlayer)
  exact hdlayers k ⟨hKL hk, hle hk⟩

theorem OddCentralizerFreeMembers.of_le_iSup {Y : Type*} [Group Y] {F L : Subgroup Y}
    {𝒦 : Set (Subgroup Y)} (hle : L ≤ ⨆ K ∈ 𝒦, K)
    (h𝒦 : ∀ K ∈ 𝒦, K ≤ L ∧ IsInvolutionMember K ∧
      ∃ f ∈ F, f ≠ 1 ∧ K ≤ Subgroup.centralizer ({f} : Set Y)) : OddCentralizerFreeMembers F L := by
  intro d _ _ hd x hx
  have hcomm : (⨆ K ∈ 𝒦, K) ≤ Subgroup.centralizer ({d} : Set Y) := by
    refine iSup₂_le fun K hK k hk => ?_
    obtain ⟨hKL, hmem, hf⟩ := h𝒦 K hK
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hd K hKL hmem hf k hk).symm
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hcomm (hle hx))).symm

theorem deltaCore_eq_bot_of_oddCentralizerFree {Y : Type*} [Group Y] [Finite Y]
    (hO : CFSG.pPrimeCore 2 Y = ⊥) {F : Subgroup Y} (hF4 : Nat.card F = 4)
    (hF2 : ∀ f ∈ F, f * f = 1)
    (hL : ∀ L : Subgroup Y, IsComponent L → F ≤ Subgroup.normalizer (L : Set Y) →
      (∀ f ∈ F, f ≠ 1 → ¬ ∀ x ∈ L, f * x = x * f) → OddCentralizerFree F L) :
    deltaCore F = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨f₀, hf₀F, hf₀1⟩ : ∃ f ∈ F, f ≠ 1 := by
    have : Nontrivial F := Finite.one_lt_card_iff_nontrivial.mp (by rw [hF4]; norm_num)
    obtain ⟨⟨f, hf⟩, hne⟩ := exists_ne (1 : F)
    exact ⟨f, hf, fun h => hne (Subtype.ext h)⟩
  have hDodd : Odd (Nat.card (deltaCore F)) := odd_card_deltaCore hf₀F hf₀1
  refine deltaCore_eq_bot_of_faithful_centralized hO hF4 hF2
    fun L hL' hFn hfaith d hd hdL x hx => ?_
  have hdodd : Odd (orderOf d) := by
    have h1 : orderOf (⟨d, hd⟩ : deltaCore F) ∣ Nat.card (deltaCore F) :=
      orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1
    exact hDodd.of_dvd_nat h1
  refine hL L hL' hFn hfaith d hdodd hdL (fun y hy => ?_) x hx
  exact (Subgroup.mem_centralizer_iff.mp (deltaCore_le_centralizer_iSup_centralizerLayer F hd) y
    (Subgroup.mem_inf.mp hy).2).symm

theorem deltaCore_eq_bot_of_generated_by_members (hLB : L2PrimeBalance) {Y : Type} [Group Y]
    [Finite Y] (hO : CFSG.pPrimeCore 2 Y = ⊥) {F : Subgroup Y} (hF4 : Nat.card F = 4)
    (hF2 : ∀ f ∈ F, f * f = 1)
    (hmem : ∀ L : Subgroup Y, IsComponent L → F ≤ Subgroup.normalizer (L : Set Y) →
      (∀ f ∈ F, f ≠ 1 → ¬ ∀ x ∈ L, f * x = x * f) →
      ∃ 𝒦 : Set (Subgroup Y), L ≤ ⨆ K ∈ 𝒦, K ∧ ∀ K ∈ 𝒦, K ≤ L ∧
        (∃ f ∈ F, f ≠ 1 ∧ K ≤ Subgroup.centralizer ({f} : Set Y)) ∧ IsInvolutionMember K)
    (hB : ∀ L : Subgroup Y, IsComponent L → F ≤ Subgroup.normalizer (L : Set Y) →
      (∀ f ∈ F, f ≠ 1 → ¬ ∀ x ∈ L, f * x = x * f) → ∀ f ∈ F, f ≠ 1 →
      ∀ M : Subgroup ↥(L ⊓ Subgroup.centralizer ({f} : Set Y)),
        TwoComponents.IsTwoComponent M → CFSG.Open.IsQuasisimple M) :
    deltaCore F = ⊥ := by
  refine deltaCore_eq_bot_of_oddCentralizerFree hO hF4 hF2 fun L hL hFn hfaith => ?_
  obtain ⟨𝒦, hle, hK⟩ := hmem L hL hFn hfaith
  exact OddCentralizerFree.of_members hLB hL (hB L hL hFn hfaith)
    (OddCentralizerFreeMembers.of_le_iSup hle fun K hK' =>
      ⟨(hK K hK').1, (hK K hK').2.2, (hK K hK').2.1⟩)

end Members

end CFSG.ClassicalInvolution.Balance
