module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6S

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6jB

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Q3.Q3CH CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf12
open CFSG.ClassicalInvolution.Asc77.Thompson CFSG.ClassicalInvolution.Uniform
open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE

theorem isUniqueInvolution_conjSub {X : Type*} [Group X] {J : Subgroup X} {a : X}
    (h : IsUniqueInvolution J a) (c : X) : IsUniqueInvolution (conjSub c J) (c * a * c⁻¹) where
  mem := conj_mem_conjSub h.mem
  ne_one := by
    intro h1
    apply h.ne_one
    calc a = c⁻¹ * (c * a * c⁻¹) * c := by group
      _ = 1 := by rw [h1]; group
  sq := by
    calc c * a * c⁻¹ * (c * a * c⁻¹) = c * (a * a) * c⁻¹ := by group
      _ = 1 := by rw [h.sq]; group
  unique := by
    intro y hy hyy
    rw [mem_conjSub_iff] at hy
    have h2 : (c⁻¹ * y * c) * (c⁻¹ * y * c) = 1 := by
      calc (c⁻¹ * y * c) * (c⁻¹ * y * c) = c⁻¹ * (y * y) * c := by group
        _ = 1 := by rw [hyy]; group
    rcases h.unique _ hy h2 with h1 | h1
    · left
      calc y = c * (c⁻¹ * y * c) * c⁻¹ := by group
        _ = 1 := by rw [h1]; group
    · right
      calc y = c * (c⁻¹ * y * c) * c⁻¹ := by group
        _ = c * a * c⁻¹ := by rw [h1]

theorem map_conjSub {X X' : Type*} [Group X] [Group X'] (e : X ≃* X') (c : X) (J : Subgroup X) :
    (conjSub c J).map e.toMonoidHom = conjSub (e c) (J.map e.toMonoidHom) := by
  ext x
  rw [Subgroup.mem_map_equiv, mem_conjSub_iff, mem_conjSub_iff, Subgroup.mem_map_equiv]
  simp [map_mul, map_inv]

theorem smallQ8_map {X X' : Type} [Group X] [Group X'] [Finite X] (e : X ≃* X') {a : X}
    {J : Subgroup X} (h : AE6SmallQ8 a J) : AE6SmallQ8 (e a) (J.map e.toMonoidHom) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨q⟩, hu, hO, hcard⟩ := h
  have hcent : ∀ c : X', c ∈ Subgroup.centralizer ({e a} : Set X') →
      e.symm c ∈ Subgroup.centralizer ({a} : Set X) := by
    intro c hc
    rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
    apply e.injective
    simp only [map_mul, MulEquiv.apply_symm_apply]
    exact hc
  refine ⟨⟨(Subgroup.equivMapOfInjective J e.toMonoidHom e.injective).symm.trans q⟩, ?_, ?_, ?_⟩
  · refine ⟨⟨a, hu.mem, rfl⟩, fun h1 => hu.ne_one (e.injective (by simpa using h1)), ?_, ?_⟩
    · rw [← map_mul, hu.sq, map_one]
    · rintro _ ⟨x, hx, rfl⟩ hyy
      have hxx : x * x = 1 := e.injective (by simpa [map_mul] using hyy)
      rcases hu.unique x hx hxx with h1 | h1
      · left; simp [h1]
      · right; simp [h1]
  · have hP2 : IsPGroup 2 ↥((pCoreOf 2 (Subgroup.centralizer ({a} : Set X))).map e.toMonoidHom) :=
      (LieType.BorelTits.pCoreOf_isPGroup 2 _).map _
    have hPC : (pCoreOf 2 (Subgroup.centralizer ({a} : Set X))).map e.toMonoidHom ≤
        Subgroup.centralizer ({e a} : Set X') := by
      rintro _ ⟨x, hx, rfl⟩
      have hxC := LieType.BorelTits.pCoreOf_le 2 _ hx
      rw [Subgroup.mem_centralizer_singleton_iff] at hxC ⊢
      simp only [MulEquiv.coe_toMonoidHom]
      rw [← map_mul, ← map_mul, hxC]
    have hCN : Subgroup.centralizer ({e a} : Set X') ≤
        Subgroup.normalizer
          (((pCoreOf 2 (Subgroup.centralizer ({a} : Set X))).map e.toMonoidHom : Subgroup X') :
            Set X') := by
      intro c hc
      have hnorm := LieType.BorelTits.le_normalizer_pCoreOf 2 _ (hcent c hc)
      rw [Subgroup.mem_normalizer_iff] at hnorm ⊢
      intro y
      rw [Subgroup.mem_map_equiv, Subgroup.mem_map_equiv, hnorm (e.symm y)]
      simp [map_mul, map_inv]
    exact (Subgroup.map_mono hO).trans
      (LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hPC hCN hP2)
  · have himg : {J' | ∃ c ∈ Subgroup.centralizer ({e a} : Set X'),
        conjSub c (J.map e.toMonoidHom) = J'} =
        (fun L : Subgroup X => L.map e.toMonoidHom) ''
          {J' | ∃ c ∈ Subgroup.centralizer ({a} : Set X), conjSub c J = J'} := by
      ext L
      constructor
      · rintro ⟨c, hc, rfl⟩
        refine ⟨conjSub (e.symm c) J, ⟨e.symm c, hcent c hc, rfl⟩, ?_⟩
        show (conjSub (e.symm c) J).map e.toMonoidHom = _
        rw [map_conjSub, MulEquiv.apply_symm_apply]
      · rintro ⟨_, ⟨c, hc, rfl⟩, rfl⟩
        refine ⟨e c, ?_, (map_conjSub e c J).symm⟩
        rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
        rw [← map_mul, ← map_mul, hc]
    rw [himg, Set.ncard_image_of_injective _ (Subgroup.map_injective e.injective)]
    exact hcard

theorem smallQ8_subgroupOf {Y : Type} [Group Y] [Finite Y] {H J : Subgroup Y} {a : Y}
    {T : Set (Subgroup Y)} (hJH : J ≤ H) (hq : Nonempty (↥J ≃* QuaternionGroup 2))
    (hu : IsUniqueInvolution J a) (hO : J ≤ pCoreOf 2 (Subgroup.centralizer ({a} : Set Y)))
    (hT : ∀ c ∈ Subgroup.centralizer ({a} : Set Y), conjSub c J ∈ T) (hTc : T.ncard ≤ 4) :
    AE6SmallQ8 (⟨a, hJH hu.mem⟩ : ↥H) (J.subgroupOf H) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨q⟩ := hq
  set a' : ↥H := ⟨a, hJH hu.mem⟩ with ha'
  have hcent : ∀ c : ↥H, c ∈ Subgroup.centralizer ({a'} : Set ↥H) →
      (c : Y) ∈ Subgroup.centralizer ({a} : Set Y) := by
    intro c hc
    rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
    exact congrArg Subtype.val hc
  refine ⟨⟨(Subgroup.subgroupOfEquivOfLe hJH).trans q⟩, ?_, ?_, ?_⟩
  · refine ⟨Subgroup.mem_subgroupOf.mpr hu.mem, fun h1 => hu.ne_one (congrArg Subtype.val h1),
      Subtype.ext hu.sq, ?_⟩
    intro y hy hyy
    rcases hu.unique (y : Y) (Subgroup.mem_subgroupOf.mp hy) (congrArg Subtype.val hyy) with h1 | h1
    · left; exact Subtype.ext h1
    · right; exact Subtype.ext h1
  · have hP2 : IsPGroup 2 ↥((pCoreOf 2 (Subgroup.centralizer ({a} : Set Y))).subgroupOf H) :=
      (LieType.BorelTits.pCoreOf_isPGroup 2 _).comap_of_injective H.subtype H.subtype_injective
    have hPC : (pCoreOf 2 (Subgroup.centralizer ({a} : Set Y))).subgroupOf H ≤
        Subgroup.centralizer ({a'} : Set ↥H) := by
      intro x hx
      have hxC := LieType.BorelTits.pCoreOf_le 2 _ (Subgroup.mem_subgroupOf.mp hx)
      rw [Subgroup.mem_centralizer_singleton_iff] at hxC ⊢
      exact Subtype.ext hxC
    have hCN : Subgroup.centralizer ({a'} : Set ↥H) ≤
        Subgroup.normalizer
          (((pCoreOf 2 (Subgroup.centralizer ({a} : Set Y))).subgroupOf H : Subgroup ↥H) : Set ↥H) := by
      intro c hc
      have hnorm := LieType.BorelTits.le_normalizer_pCoreOf 2 _ (hcent c hc)
      rw [Subgroup.mem_normalizer_iff] at hnorm ⊢
      intro y
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, hnorm (y : Y)]
      simp
    have hJP : J.subgroupOf H ≤ (pCoreOf 2 (Subgroup.centralizer ({a} : Set Y))).subgroupOf H :=
      fun x hx =>
      Subgroup.mem_subgroupOf.mpr (hO (Subgroup.mem_subgroupOf.mp hx))
    exact hJP.trans (LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hPC hCN hP2)
  · have hconj : ∀ c : ↥H, (conjSub c (J.subgroupOf H)).map H.subtype = conjSub (c : Y) J := by
      intro c
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        have hy' : y ∈ conjSub c (J.subgroupOf H) := hy
        rw [mem_conjSub_iff, Subgroup.mem_subgroupOf] at hy'
        rw [mem_conjSub_iff]
        simpa using hy'
      · intro hx
        have hxH : x ∈ H := by
          rw [mem_conjSub_iff] at hx
          have := H.mul_mem (H.mul_mem c.2 (hJH hx)) (H.inv_mem c.2)
          simpa [mul_assoc] using this
        refine ⟨⟨x, hxH⟩, ?_, rfl⟩
        show (⟨x, hxH⟩ : ↥H) ∈ conjSub c (J.subgroupOf H)
        rw [mem_conjSub_iff, Subgroup.mem_subgroupOf]
        rw [mem_conjSub_iff] at hx
        simpa using hx
    have hfin : T.Finite := Set.toFinite T
    calc Set.ncard {J' | ∃ c ∈ Subgroup.centralizer ({a'} : Set ↥H), conjSub c (J.subgroupOf H) = J'}
        = Set.ncard ((fun L : Subgroup ↥H => L.map H.subtype) ''
            {J' | ∃ c ∈ Subgroup.centralizer ({a'} : Set ↥H), conjSub c (J.subgroupOf H) = J'}) :=
          (Set.ncard_image_of_injective _ (Subgroup.map_injective H.subtype_injective)).symm
      _ ≤ T.ncard := by
          refine Set.ncard_le_ncard ?_ hfin
          rintro _ ⟨_, ⟨c, hc, rfl⟩, rfl⟩
          show (conjSub c (J.subgroupOf H)).map H.subtype ∈ T
          rw [hconj c]
          exact hT _ (hcent c hc)
      _ ≤ 4 := hTc

variable {n : ℕ}


local notation "Ω[" R "]" => CoreAssembly.conjClass (tightCore R)

theorem exists_M_conj_of_twin {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
    {K K' K₃ : Subgroup Y} {u₁ u₂ u₃ : Y} {K₄ W : Subgroup Y}
    (H : AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W) {J₀ : Subgroup Y} (hJ₀ : J₀ ∈ twinSet Ω[R] K) :
    ∃ m ∈ MGrp Ω[R] W, conjSub m K = J₀ := by
  have hStd := H.ex.1
  have hd := hStd.datum
  have hP := (CoreData.of_S hStd.perp.core).partIHypG
  have h2g : ∀ J ∈ Ω[R], IsPGroup 2 ↥J := H.ex.2.2.2.1
  have htW : t ∈ W := hd.sq₁ ▸ W.mul_mem H.hu₁ H.hu₁
  have hK : K ∈ Ω[R] := hd.mem
  have c : Q3CL.Thompson.Ctx Ω[R] W := Q3CL.T8.ctxOf hP H.hW
  have hKsyl : IsSylow2In K K := ⟨le_rfl, h2g K hK, fun V' hV'K _ hKV' => le_antisymm hV'K hKV'⟩
  obtain ⟨ρ, hρK⟩ : ∃ ρ : Asc77.Thompson.Rep Ω[R] W, ρ.K = K :=
    ⟨Q3CL.T8.mkRep hP H.hW hK H.hK hKsyl, rfl⟩
  have hJ₀Ω : J₀ ∈ Ω[R] := hJ₀.1
  have hzJ₀ : IsUniqueInvolution J₀ t := Asc77.isUniqueInvolution_of_mem_twinSet hd.hz hJ₀
  have hJ₀D : J₀ ∈ DSet Ω[R] W := twin_mem_DSet hP h2g H.hW htW hJ₀Ω hzJ₀
  have hJ₀syl : IsSylow2In J₀ J₀ :=
    ⟨le_rfl, h2g J₀ hJ₀Ω, fun V' hV'K _ hKV' => le_antisymm hV'K hKV'⟩
  obtain ⟨σ, hσK⟩ : ∃ σ : Asc77.Thompson.Rep Ω[R] W, σ.K = J₀ :=
    ⟨Q3CL.T8.mkRep hP H.hW hJ₀Ω hJ₀D hJ₀syl, rfl⟩
  have hnc : ¬ DbarConnected Ω[R] W :=
    not_dbarConnected_of_wyl' hP hd (kPerp_datum hStd.perp hd.mem hd.hz) H.hW ρ hρK (hStd.wyl W H.hW)
  obtain ⟨m, hm, hmK⟩ := c.exists_conj_of_rep hP.cls hnc ρ σ
  exact ⟨m, hm, by rw [← hσK, ← hmK, hρK]⟩

theorem twinSet_ncard_le {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
    {K K' K₃ : Subgroup Y} {u₁ u₂ u₃ : Y} {K₄ W : Subgroup Y}
    (H : AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W) {J : Subgroup Y} (hJ : J ∈ Ω[R]) :
    (twinSet Ω[R] J).ncard ≤ 4 := by
  have hStd := H.ex.1
  have hd := hStd.datum
  have hinv := conjInvariant_conjClass (tightCore R)
  obtain ⟨g₁, hg₁⟩ := hJ
  obtain ⟨g₂, hg₂⟩ := hd.mem
  have hg₁' : conjSub g₁ (tightCore R) = J := hg₁
  have hg₂' : conjSub g₂ (tightCore R) = K := hg₂
  obtain ⟨g, rfl⟩ : ∃ g, conjSub g K = J :=
    ⟨g₁ * g₂⁻¹, by rw [← hg₂', ← conjSub_mul, inv_mul_cancel_right, hg₁']⟩
  have hsub : twinSet Ω[R] (conjSub g K) ⊆ conjSub g '' ({K, K', K₃, K₄} : Set (Subgroup Y)) := by
    rintro X ⟨hXΩ, z, hzJ, hzX⟩
    refine ⟨conjSub g⁻¹ X, ?_, conjSub_conjSub_inv g X⟩
    have h1 := isUniqueInvolution_conjSub hzJ g⁻¹
    rw [conjSub_inv_conjSub] at h1
    have h2 := isUniqueInvolution_conjSub hzX g⁻¹
    have hmem : conjSub g⁻¹ X ∈ twinSet Ω[R] K := ⟨hinv g⁻¹ X hXΩ, _, h1, h2⟩
    rcases twinSet_four hStd H.ex.2.1 _ hmem with h | h | h | h <;> simp [h]
  calc (twinSet Ω[R] (conjSub g K)).ncard
      ≤ (conjSub g '' ({K, K', K₃, K₄} : Set (Subgroup Y))).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ ({K, K', K₃, K₄} : Set (Subgroup Y)).ncard := Set.ncard_image_le (Set.toFinite _)
    _ ≤ 4 := by
        refine (Set.ncard_insert_le _ _).trans ?_
        refine (Nat.add_le_add_right (Set.ncard_insert_le _ _) 1).trans ?_
        refine (Nat.add_le_add_right (Nat.add_le_add_right (Set.ncard_insert_le _ _) 1) 1).trans ?_
        rw [Set.ncard_singleton]

theorem smallQ8_of_member {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
    {K K' K₃ : Subgroup Y} {u₁ u₂ u₃ : Y} {K₄ W : Subgroup Y}
    (H : AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W) {Hε J : Subgroup Y} {a : Y} (hJ : J ∈ Ω[R])
    (ha : IsUniqueInvolution J a) (hJH : J ≤ Hε) :
    AE6SmallQ8 (⟨a, hJH ha.mem⟩ : ↥Hε) (J.subgroupOf Hε) := by
  have hStd := H.ex.1
  have hC := CoreData.of_S hStd.perp.core
  have hΩ : HypOmegaGen Ω[R] := hC.hyp
  have h2g : ∀ J ∈ Ω[R], IsPGroup 2 ↥J := H.ex.2.2.2.1
  have hinv := conjInvariant_conjClass (tightCore R)
  refine smallQ8_subgroupOf hJH (members_q8_of_isPGroup hStd.perp h2g J hJ) ha
    (TC.Thin.le_pCoreOf_centralizer hΩ h2g hJ ha) (T := twinSet Ω[R] J) ?_ (twinSet_ncard_le H hJ)
  intro c hc
  have hca : c * a * c⁻¹ = a := by
    rw [Subgroup.mem_centralizer_singleton_iff] at hc
    rw [hc, mul_inv_cancel_right]
  have h1 := isUniqueInvolution_conjSub ha c
  rw [hca] at h1
  exact ⟨hinv c J hJ, a, ha, h1⟩

theorem v3AE6OmegaHB_of (hQ8 : AE6ModelQ8) : V3AE6OmegaHB n := by
  intro Y _ _ R S t K K' K₃ u₁ u₂ u₃ K₄ W a₁ a₂ a₃ a₄ y h H fr hx ε hrel hI hL J hJ hJH
  have hStd := H.ex.1
  have hd := hStd.datum
  have hC := CoreData.of_S hStd.perp.core
  have hΩ : HypOmegaGen Ω[R] := hC.hyp
  have hinv := conjInvariant_conjClass (tightCore R)
  set Hε := Subgroup.closure (Set.range ε) with hHε
  have hMH : MGrp Ω[R] W ≤ Hε := le_trans le_sup_left hI
  have hKM : K ≤ MGrp Ω[R] W := by
    unfold MGrp
    exact le_iSup₂_of_le K H.hK le_rfl
  have hKH : K ≤ Hε := hKM.trans hMH
  let ε' : Fin 8 → ↥Hε := fun i => ⟨ε i, Subgroup.subset_closure ⟨i, rfl⟩⟩
  have hrel' : ∀ r ∈ A6.curtisRels, A6.curtisEval (List.ofFn ε') r = 1 := by
    intro r hr
    apply Hε.subtype_injective
    rw [← curtisEval_map, List.map_ofFn, map_one]
    exact hrel r hr
  have hgen' : Subgroup.closure (Set.range ε') = ⊤ := by
    have hrange : Set.range ε' = ((↑) : ↥Hε → Y) ⁻¹' Set.range ε := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨i, rfl⟩
      · rintro ⟨i, hi⟩
        exact ⟨i, Subtype.ext hi⟩
    rw [hrange]
    exact Subgroup.closure_closure_coe_preimage
  haveI : Nontrivial ↥Hε :=
    ⟨⟨⟨t, hKH hd.hz.mem⟩, 1, fun h1 => hd.hz.ne_one (congrArg Subtype.val h1)⟩⟩
  obtain ⟨e⟩ := A6.curtisD42_recognition ε' hrel' hgen'
  obtain ⟨a, ha⟩ := Sec6Gen.exists_uniqueInvolution hΩ hJ
  have hsK := smallQ8_map e (smallQ8_of_member H hd.mem hd.hz hKH)
  have hsJ := smallQ8_map e (smallQ8_of_member H hJ ha hJH)
  obtain ⟨g, hg⟩ := hQ8 _ _ _ _ hsK hsJ
  set h₀ : ↥Hε := e.symm g with hh₀
  have hh₀a : (h₀ : Y) * t * (h₀ : Y)⁻¹ = a := by
    have := congrArg e.symm hg
    simp only [map_mul, map_inv, MulEquiv.symm_apply_apply] at this
    exact congrArg Subtype.val this
  have hJ₀ : conjSub (h₀ : Y)⁻¹ J ∈ twinSet Ω[R] K := by
    have h1 := isUniqueInvolution_conjSub ha (h₀ : Y)⁻¹
    have ht : (h₀ : Y)⁻¹ * a * (h₀ : Y)⁻¹⁻¹ = t := by
      rw [← hh₀a]; group
    rw [ht] at h1
    exact ⟨hinv _ J hJ, t, hd.hz, h1⟩
  obtain ⟨m, hm, hmK⟩ := exists_M_conj_of_twin H hJ₀
  refine ⟨(h₀ : Y) * m, Hε.mul_mem h₀.2 (hMH hm), ?_⟩
  rw [conjSub_mul, hmK, conjSub_conjSub_inv]

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6jB
