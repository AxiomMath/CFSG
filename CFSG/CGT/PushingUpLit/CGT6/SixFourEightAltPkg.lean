module

public import CFSG.CGT.PushingUpLit.CGT6.SixFourEightBasic
public import CFSG.CGT.PushingUpLit.CGT6.SixTwoConj
public import CFSG.CGT.PushingUpLit.CGT6.TwoFiveAut

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.CGT.PushingUpLit
open CFSG.CGT.PushingUpLit.SixThree
open CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6 CFSG.Quasithin CFSG.Quasithin.G6
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem conjAct_mem_normalizer_autOn {Y : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (Y : Set G)) :
    conjAct (blockU Y) ⟨g, normalizer_le_normalizer_blockU Y hg⟩ ∈
      Subgroup.normalizer ((autOn Y (blockU Y) : Subgroup (MulAut ↥(blockU Y))) :
        Set (MulAut ↥(blockU Y))) :=
  CFSG.Quasithin.AutOn.conjAct_mem_normalizer_autOn _ hg


omit [Finite G] in
theorem not_commutator_le_of_not_le {Y A : Subgroup G} (hAN : A ≤ Subgroup.normalizer (Y : Set G))
    (hnot : ¬ A ≤ centralizerModCore Y) : ¬ ⁅A, Y⁆ ≤ oTwoIn Y := by
  intro hle
  apply hnot
  intro g hg
  exact ⟨hAN hg, fun x hx => hle (Subgroup.commutator_mem_commutator hg hx)⟩

omit [Finite G] in
theorem card_fixU_eq {Y : Subgroup G} {n : ℕ}
    (β : ↥(blockU Y) ≃* ↥(coreMod n))
    (Φ : ↥(Subgroup.normalizer (Y : Set G)) →* Equiv.Perm (Fin n))
    (hequiv : ∀ (g : ↥(Subgroup.normalizer (Y : Set G))) (w : ↥(blockU Y))
      (hw : (g : G) * w * (g : G)⁻¹ ∈ blockU Y),
      β ⟨(g : G) * w * (g : G)⁻¹, hw⟩ = coreAct n (Φ g) (β w))
    (g : ↥(Subgroup.normalizer (Y : Set G))) :
    Nat.card ↥(blockU Y ⊓ Subgroup.centralizer ({(g : G)} : Set G)) =
      Nat.card ↥(fixSub (coreAct n (Φ g))) := by
  have hmap : ((blockU Y ⊓ Subgroup.centralizer ({(g : G)} : Set G)).subgroupOf (blockU Y)).map
      β.toMonoidHom = fixSub (coreAct n (Φ g)) := by
    ext v
    obtain ⟨w, rfl⟩ := β.surjective v
    rw [Subgroup.mem_map_equiv, mem_fixSub]
    have hw : (g : G) * w * (g : G)⁻¹ ∈ blockU Y := conj_mem_blockU g.2 w.2
    have h1 := hequiv g w hw
    constructor
    · intro hmem
      rw [MulEquiv.symm_apply_apply] at hmem
      rw [← h1]
      congr 1
      apply Subtype.ext
      have := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_subgroupOf.mp hmem).2 g
        (Set.mem_singleton _)
      show (g : G) * w * (g : G)⁻¹ = w
      calc (g : G) * w * (g : G)⁻¹ = (w * (g : G)) * (g : G)⁻¹ := by rw [this]
        _ = w := by group
    · intro hfix
      rw [MulEquiv.symm_apply_apply]
      refine Subgroup.mem_subgroupOf.mpr ⟨w.2, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
      rw [Set.mem_singleton_iff.mp hy]
      have h2 : (⟨(g : G) * w * (g : G)⁻¹, hw⟩ : ↥(blockU Y)) = w := by
        apply β.injective
        rw [h1]
        exact hfix
      have h3 : (g : G) * w * (g : G)⁻¹ = w := congrArg Subtype.val h2
      calc (g : G) * w = ((g : G) * w * (g : G)⁻¹) * g := by group
        _ = w * g := by rw [h3]
  rw [← hmap, Subgroup.card_map_of_injective β.injective]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv.symm

omit [Finite G] in
theorem mem_centralizer_blockU_of_eq_one {Y : Subgroup G} {n : ℕ}
    (β : ↥(blockU Y) ≃* ↥(coreMod n))
    (Φ : ↥(Subgroup.normalizer (Y : Set G)) →* Equiv.Perm (Fin n))
    (hequiv : ∀ (g : ↥(Subgroup.normalizer (Y : Set G))) (w : ↥(blockU Y))
      (hw : (g : G) * w * (g : G)⁻¹ ∈ blockU Y),
      β ⟨(g : G) * w * (g : G)⁻¹, hw⟩ = coreAct n (Φ g) (β w))
    {g : ↥(Subgroup.normalizer (Y : Set G))} (hg : Φ g = 1) :
    (g : G) ∈ Subgroup.centralizer (blockU Y : Set G) := by
  refine Subgroup.mem_centralizer_iff.mpr fun u hu => ?_
  have hw : (g : G) * u * (g : G)⁻¹ ∈ blockU Y := conj_mem_blockU g.2 hu
  have := hequiv g ⟨u, hu⟩ hw
  rw [hg, map_one] at this
  have h2 : (⟨(g : G) * u * (g : G)⁻¹, hw⟩ : ↥(blockU Y)) = ⟨u, hu⟩ := β.injective this
  have h3' : (g : G) * u * (g : G)⁻¹ = u := congrArg Subtype.val h2
  calc u * (g : G) = ((g : G) * u * (g : G)⁻¹) * g := by rw [h3']
    _ = g * u := by group

omit [Finite G] in
theorem eq_one_of_mem_centralizer_blockU {Y : Subgroup G} {n : ℕ} (h3 : 3 ≤ n)
    (β : ↥(blockU Y) ≃* ↥(coreMod n))
    (Φ : ↥(Subgroup.normalizer (Y : Set G)) →* Equiv.Perm (Fin n))
    (hequiv : ∀ (g : ↥(Subgroup.normalizer (Y : Set G))) (w : ↥(blockU Y))
      (hw : (g : G) * w * (g : G)⁻¹ ∈ blockU Y),
      β ⟨(g : G) * w * (g : G)⁻¹, hw⟩ = coreAct n (Φ g) (β w))
    {g : ↥(Subgroup.normalizer (Y : Set G))}
    (hg : (g : G) ∈ Subgroup.centralizer (blockU Y : Set G)) : Φ g = 1 := by
  have hcoe : coreAct n (Φ g) = 1 := by
    refine MulEquiv.ext fun v => ?_
    obtain ⟨w, rfl⟩ := β.surjective v
    have hw : (g : G) * w * (g : G)⁻¹ ∈ blockU Y := conj_mem_blockU g.2 w.2
    have h1 := hequiv g w hw
    have h2 : (⟨(g : G) * w * (g : G)⁻¹, hw⟩ : ↥(blockU Y)) = w := by
      apply Subtype.ext
      have := Subgroup.mem_centralizer_iff.mp hg w w.2
      show (g : G) * w * (g : G)⁻¹ = w
      calc (g : G) * w * (g : G)⁻¹ = (w * (g : G)) * (g : G)⁻¹ := by rw [this]
        _ = w := by group
    rw [h2] at h1
    exact h1.symm
  exact coreAct_injective h3 (hcoe.trans (map_one (coreAct n)).symm)

theorem EightCtx.inf_centralizer_blockU_eq_inf {Y R : Subgroup G} {T : Sylow 2 G}
    (h : EightCtx Y T R) {A : Subgroup G} (hA : IsMaxElemAbelian (T : Subgroup G) A)
    (hC : Y ⊓ Subgroup.centralizer (blockU Y : Set G) = oTwoIn Y) :
    A ⊓ Subgroup.centralizer (blockU Y : Set G) = A ⊓ R := by
  have hAN : A ≤ Subgroup.normalizer (Y : Set G) := h.le_normalizer_of_isMax hA
  have hCUV : Subgroup.centralizer (omegaOneCenterIn R : Set G) ≤
      Subgroup.centralizer ((blockU Y) : Set G) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr h.blockU_le_V)
  apply le_antisymm
  · have hA2 : IsPGroup 2 A := isPGroup_two_of_isElemAbelian hA.2.1
    have hP2 : IsPGroup 2 ↥(A ⊓ Subgroup.centralizer (blockU Y : Set G)) :=
      hA2.to_le inf_le_left
    have hPC : A ⊓ Subgroup.centralizer (blockU Y : Set G) ≤ centralizerModCore Y :=
      fun g hg => EightCtx.mem_centralizerModCore_of_centralizer_blockU hC (hAN hg.1) hg.2
    exact le_inf inf_le_left (h.le_R_of_le_centralizerModCore hP2 hPC)
  · refine inf_le_inf_left A ?_
    rw [← h.hC]
    exact hCUV

theorem eight_vpart {Y R : Subgroup G} {T : Sylow 2 G} (h : EightCtx Y T R) {A : Subgroup G}
    (hOff : IsOffG (omegaOneCenterIn R) A)
    (hUcard : Nat.card ↥(blockU Y) = (A ⊓ R).relIndex A *
      Nat.card ↥(blockU Y ⊓ Subgroup.centralizer (A : Set G))) :
    blockU Y ⊔ (omegaOneCenterIn R ⊓ Subgroup.centralizer (A : Set G)) = omegaOneCenterIn R ∧
      Nat.card ↥(omegaOneCenterIn R) = wtG (omegaOneCenterIn R) A := by
  classical
  have hV := isElemAbelian_omegaOneCenterIn R
  have hUV : blockU Y ≤ omegaOneCenterIn R := h.blockU_le_V
  set nA : ℕ := (A ⊓ R).relIndex A with hnA
  have hwtV : wtG (omegaOneCenterIn R) A =
      nA * Nat.card ↥(omegaOneCenterIn R ⊓ Subgroup.centralizer (A : Set G)) := by
    unfold wtG
    rw [h.hC]
  have hVle : Nat.card ↥(omegaOneCenterIn R) ≤ wtG (omegaOneCenterIn R) A := by
    have h1 := hOff.2.2.2.2 ⊥ bot_le
    have hbot : wtG (omegaOneCenterIn R) (⊥ : Subgroup G) = Nat.card ↥(omegaOneCenterIn R) := by
      have e : omegaOneCenterIn R ⊓ Subgroup.centralizer ((⊥ : Subgroup G) : Set G) =
          omegaOneCenterIn R :=
        inf_eq_left.mpr fun x _ => Subgroup.mem_centralizer_iff.mpr fun y hy => by
          have : y = 1 := hy
          simp [this]
      unfold wtG
      rw [e]
      simp
    rwa [hbot] at h1
  set CVA : Subgroup G := omegaOneCenterIn R ⊓ Subgroup.centralizer (A : Set G) with hCVA
  have hcommUC : ∀ x ∈ blockU Y, ∀ y ∈ CVA, x * y = y * x := fun x hx y hy =>
    isElemAbelian_comm' hV (hUV hx) hy.1
  have hcard1 := card_sup_mul_card_inf' hcommUC
  have hUCVA : blockU Y ⊓ CVA = blockU Y ⊓ Subgroup.centralizer (A : Set G) := by
    ext x
    simp only [Subgroup.mem_inf, hCVA]
    exact ⟨fun ⟨a, _, c⟩ => ⟨a, c⟩, fun ⟨a, c⟩ => ⟨a, hUV a, c⟩⟩
  rw [hUCVA] at hcard1
  have hpos : 0 < Nat.card ↥(blockU Y ⊓ Subgroup.centralizer (A : Set G)) := Nat.card_pos
  have hsupcard : Nat.card ↥(blockU Y ⊔ CVA) = nA * Nat.card ↥CVA := by
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [hcard1, hUcard]
    ring
  have hsupV : blockU Y ⊔ CVA = omegaOneCenterIn R := by
    refine Subgroup.eq_of_le_of_card_ge (sup_le hUV inf_le_left) ?_
    rw [hsupcard]
    calc _ ≤ wtG (omegaOneCenterIn R) A := hVle
      _ = nA * Nat.card ↥CVA := hwtV
  refine ⟨hsupV, ?_⟩
  refine le_antisymm hVle ?_
  calc wtG (omegaOneCenterIn R) A = Nat.card ↥(blockU Y ⊔ CVA) := by rw [hsupcard, hwtV]
    _ ≤ Nat.card ↥(omegaOneCenterIn R) := Subgroup.card_le_of_le (sup_le hUV inf_le_left)

theorem exists_altPkg {Y R : Subgroup G} {T : Sylow 2 G} (h : EightCtx Y T R) {a : ℕ} (ha : 2 ≤ a)
    {φ : (↥Y ⧸ pCore 2 ↥Y) ≃* alternatingGroup (Fin (2 * a + 1))}
    (hnat : IsNaturalAltModuleWith ↥Y a φ) {A : Subgroup G}
    (hA : IsMaxElemAbelian (T : Subgroup G) A) (hnot : ¬ A ≤ centralizerModCore Y) :
    ∃ (β : ↥(blockU Y) ≃* ↥(coreMod (2 * a + 1)))
      (Φ : ↥(Subgroup.normalizer (Y : Set G)) →* Equiv.Perm (Fin (2 * a + 1))),
      (∀ (g : ↥(Subgroup.normalizer (Y : Set G))) (w : ↥(blockU Y))
          (hw : (g : G) * w * (g : G)⁻¹ ∈ blockU Y),
          β ⟨(g : G) * w * (g : G)⁻¹, hw⟩ = coreAct (2 * a + 1) (Φ g) (β w)) ∧
      (∀ π ∈ alternatingGroup (Fin (2 * a + 1)), ∃ y : ↥Y,
        Φ ⟨y, Subgroup.le_normalizer y.2⟩ = (π : Equiv.Perm (Fin (2 * a + 1)))) ∧
      (∃ (t : G) (ht : t ∈ A) (i j : Fin (2 * a + 1)), i ≠ j ∧
        Φ ⟨t, h.le_normalizer_of_isMax hA ht⟩ = Equiv.swap i j) ∧
      (blockU Y ⊔ (omegaOneCenterIn R ⊓ Subgroup.centralizer (A : Set G)) = omegaOneCenterIn R) ∧
      Nat.card (omegaOneCenterIn R) = wtG (omegaOneCenterIn R) A := by
  classical
  have hY := h.hY.1
  have h3 : 3 ≤ 2 * a + 1 := by omega
  have h5 : 5 ≤ 2 * a + 1 := by omega
  have hodd : Odd (2 * a + 1) := ⟨a, rfl⟩
  have hperf : ⁅Y, Y⁆ = Y := by
    rcases hY.quotient_type with hq | hp
    · exact inClassX_commutator_eq_self h.hY hq
    · exfalso
      have : Fact (Nat.Prime (Nat.card (↥Y ⧸ pCore 2 ↥Y))) := ⟨hp⟩
      have hcyc : IsCyclic (↥Y ⧸ pCore 2 ↥Y) := isCyclic_of_prime_card rfl
      have hcomm : IsMulCommutative (alternatingGroup (Fin (2 * a + 1))) := by
        have : IsCyclic (alternatingGroup (Fin (2 * a + 1))) :=
          isCyclic_of_surjective φ.toMonoidHom φ.surjective
        infer_instance
      rw [alternatingGroup.isMulCommutative_iff_card_le_three] at hcomm
      simp at hcomm
      omega
  have hAN : A ≤ Subgroup.normalizer (Y : Set G) := h.le_normalizer_of_isMax hA
  have hV := isElemAbelian_omegaOneCenterIn R
  have hUV : blockU Y ≤ omegaOneCenterIn R := h.blockU_le_V
  have hU2 : CFSG.Open.IsElemAbelian 2 (blockU Y) := h.blockU_isElemAbelian
  have hXU : Y ≤ Subgroup.normalizer (blockU Y : Set G) := le_normalizer_blockU Y
  have hAU : A ≤ Subgroup.normalizer (blockU Y : Set G) := fun g hg =>
    normalizer_le_normalizer_blockU Y (hAN hg)
  have hC : Y ⊓ Subgroup.centralizer (blockU Y : Set G) = oTwoIn Y :=
    inf_centralizer_blockU_eq hY h3 hnat
  have hOff : IsOffG (omegaOneCenterIn R) A := h.isOffG hA hnot
  obtain ⟨D, hD⟩ := exists_altNatData hY hperf h3 hnat hU2
  let _ : CommGroup ↥(blockU Y) := commGroupOfElemAbelian hU2
  have hW : ∀ w : ↥(blockU Y), w ^ 2 = 1 := fun w => Subtype.ext (by simpa using hU2.2 w w.2)
  have hnot' := not_commutator_le_of_not_le hAN hnot
  have hAnorm : (autOn A (blockU Y)) ≤
      Subgroup.normalizer ((autOn Y (blockU Y)) : Set (MulAut ↥(blockU Y))) := by
    intro g hg
    obtain ⟨a₁, ha₁, rfl⟩ := mem_autOn_iff.mp hg
    exact conjAct_mem_normalizer_autOn (hAN ha₁)
  have hCUV : Subgroup.centralizer (omegaOneCenterIn R : Set G) ≤
      Subgroup.centralizer ((blockU Y) : Set G) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hUV)
  have hAel : @IsElemAbelian2 ↥(blockU Y) (commGroupOfElemAbelian hU2) (autOn A (blockU Y)) := by
    refine ⟨fun g hg g' hg' => ?_, fun g hg => ?_⟩
    · obtain ⟨a₁, ha₁, rfl⟩ := mem_autOn_iff.mp hg
      obtain ⟨a₂, ha₂, rfl⟩ := mem_autOn_iff.mp hg'
      exact (conjAct_comm_eq_one_iff (blockU Y) a₁ a₂).mpr (hCUV (hOff.2.2.1 _ ha₁ _ ha₂))
    · obtain ⟨a₁, ha₁, rfl⟩ := mem_autOn_iff.mp hg
      rw [← map_pow, conjAct_eq_one_iff]
      exact hCUV (hOff.2.2.2.1 _ ha₁)
  have hAw : Nat.card ↥(blockU Y) ≤ Nat.card ↥(autOn A (blockU Y)) *
      Nat.card ↥(@fixV ↥(blockU Y) (commGroupOfElemAbelian hU2) (autOn A (blockU Y))) := by
    rw [card_autOn_eq_relIndex hAU, card_fixV_autOn_eq hU2 hAU]
    exact card_le_relIndex_mul_card_of_isOffG hV hOff hUV
  have hEA : ⁅(autOn Y (blockU Y)), (autOn A (blockU Y))⁆ ≠ ⊥ := by
    intro hbot
    apply hnot'
    rw [← hC]
    refine Subgroup.commutator_le.mpr fun a ha x hx => ?_
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [commutatorElement_def]
      exact Y.mul_mem ((Subgroup.mem_normalizer_iff.mp (hAN ha) x).mp hx) (Y.inv_mem hx)
    · have h1 : conjAct (blockU Y) ⟨a, hAU ha⟩ ∈ (autOn A (blockU Y)) :=
        mem_autOn_iff.mpr ⟨⟨a, hAU ha⟩, ha, rfl⟩
      have h2 : conjAct (blockU Y) ⟨x, hXU hx⟩ ∈ (autOn Y (blockU Y)) :=
        mem_autOn_iff.mpr ⟨⟨x, hXU hx⟩, hx, rfl⟩
      have h3' := Subgroup.commutator_mem_commutator h2 h1
      rw [hbot, Subgroup.mem_bot, ← map_commutatorElement] at h3'
      have h4 := (conjAct_eq_one_iff (blockU Y) _).mp h3'
      have h5' : ⁅a, x⁆ = ⁅x, a⁆⁻¹ := (commutatorElement_inv x a).symm
      rw [h5']
      exact (Subgroup.centralizer ((blockU Y) : Set G)).inv_mem h4
  obtain ⟨hfix, θX, hθXE, hequi, ⟨T', hTne, hTsw, hTc, hTeq⟩, hquad, hcardU⟩ :=
    alt_core hW hodd h5 D hAnorm hAel hAw hEA
  have hβinj : Function.Injective D.β := by
    rw [injective_iff_map_eq_one]
    intro w hw
    have h1 := D.ker_fix w hw
    rw [hfix] at h1
    exact Subgroup.mem_bot.mp h1
  let β : ↥(blockU Y) ≃* ↥(coreMod (2 * a + 1)) := MulEquiv.ofBijective D.β ⟨hβinj, D.surj⟩
  have hβ : ∀ w, β w = D.β w := fun w => rfl
  let Ψ : ↥(Subgroup.normalizer (Y : Set G)) →*
      ↥(Subgroup.normalizer ((autOn Y (blockU Y) : Subgroup (MulAut ↥(blockU Y))) :
        Set (MulAut ↥(blockU Y)))) :=
    ((conjAct (blockU Y)).comp (Subgroup.inclusion (normalizer_le_normalizer_blockU Y))).codRestrict
      _ (fun g => conjAct_mem_normalizer_autOn g.2)
  let Φ : ↥(Subgroup.normalizer (Y : Set G)) →* Equiv.Perm (Fin (2 * a + 1)) :=
    (D.psi hodd h5).comp Ψ
  have hequiv : ∀ (g : ↥(Subgroup.normalizer (Y : Set G))) (w : ↥(blockU Y))
      (hw : (g : G) * w * (g : G)⁻¹ ∈ blockU Y),
      β ⟨(g : G) * w * (g : G)⁻¹, hw⟩ = coreAct (2 * a + 1) (Φ g) (β w) := by
    intro g w hw
    have h1 := D.psi_spec hodd h5 (Ψ g) w
    have h2 : (((Ψ g : ↥(Subgroup.normalizer ((autOn Y (blockU Y) : Subgroup (MulAut ↥(blockU Y))) :
        Set (MulAut ↥(blockU Y))))) : MulAut ↥(blockU Y)) w) = ⟨(g : G) * w * (g : G)⁻¹, hw⟩ :=
      Subtype.ext (conjAct_apply' (blockU Y) _ w)
    rw [h2] at h1
    exact h1
  have hAU_R : A ⊓ Subgroup.centralizer (blockU Y : Set G) = A ⊓ R :=
    h.inf_centralizer_blockU_eq_inf hA hC
  set nA : ℕ := (A ⊓ R).relIndex A with hnA
  have hUcard : Nat.card ↥(blockU Y) =
      nA * Nat.card ↥(blockU Y ⊓ Subgroup.centralizer (A : Set G)) := by
    have := hcardU
    rw [card_autOn_eq_relIndex hAU, card_fixV_autOn_eq hU2 hAU, hAU_R] at this
    exact this
  obtain ⟨hsupV, hwtEq⟩ := eight_vpart h hOff hUcard
  refine ⟨β, Φ, hequiv, ?_, ?_, hsupV, hwtEq⟩
  · intro π hπ
    obtain ⟨q, hq⟩ := φ.surjective ⟨π, hπ⟩
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    refine ⟨y, ?_⟩
    let e : ↥(autOn Y (blockU Y)) := actOnRange (blockU Y) Y hXU y
    have h1 : Ψ ⟨y, Subgroup.le_normalizer y.2⟩ =
        ⟨(e : MulAut ↥(blockU Y)), Subgroup.le_normalizer e.2⟩ := rfl
    have h2 : Φ ⟨y, Subgroup.le_normalizer y.2⟩ =
        D.psi hodd h5 (Ψ ⟨y, Subgroup.le_normalizer y.2⟩) := rfl
    rw [h2, h1, D.psi_of_mem hodd h5 e]
    have h3' := congrArg (fun z : alternatingGroup (Fin (2 * a + 1)) =>
      (z : Equiv.Perm (Fin (2 * a + 1)))) (hD y)
    rw [h3', hq]
  · obtain ⟨t₀, ht₀⟩ := hTne
    have ht₀' : t₀ ∈ Subgroup.closure T' := Subgroup.subset_closure ht₀
    rw [← hTeq] at ht₀'
    obtain ⟨u, hu, hut⟩ := ht₀'
    obtain ⟨g, hg, hgu⟩ := mem_autOn_iff.mp (Subgroup.mem_subgroupOf.mp hu)
    obtain ⟨i, j, hij, rfl⟩ := hTsw t₀ ht₀
    refine ⟨(g : G), hg, i, j, hij, ?_⟩
    have hgN : (g : G) ∈ Subgroup.normalizer (Y : Set G) := hAN hg
    have hΦ : Φ ⟨(g : G), hgN⟩ = θX u := by
      apply D.perm_unique (by omega)
      intro w
      have e1 := D.psi_spec hodd h5 (Ψ ⟨(g : G), hgN⟩) w
      have e2 := hequi u w
      have hu' : ((Ψ ⟨(g : G), hgN⟩ : ↥(Subgroup.normalizer ((autOn Y (blockU Y) :
          Subgroup (MulAut ↥(blockU Y))) : Set (MulAut ↥(blockU Y))))) : MulAut ↥(blockU Y)) =
          (u : MulAut ↥(blockU Y)) := hgu
      rw [hu'] at e1
      exact e1.symm.trans e2
    rw [hΦ]
    exact hut

end CFSG.CGT.PushingUpLit.CGT6
