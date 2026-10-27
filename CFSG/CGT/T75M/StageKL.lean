module

public import CFSG.CGT.T75M.StageA2
public import CFSG.CGT.T75M.JHyp
public import CFSG.CGT.T75M.KLFamily
public import CFSG.CGT.Timmesfeld75.JLemma

public section

namespace CFSG.CGT.T75M

open CFSG.CGT.Timmesfeld75 CFSG.Open

variable {G : Type} [Group G] [Finite G] {T T₁ : Subgroup G} {a : ℕ}

section Aux

omit [Finite G] in
theorem mem_normalizer_subgroupOf {Y U : Subgroup G} {z : G} (hz : z ∈ Y)
    (hzU : z ∈ Subgroup.normalizer (U : Set G)) :
    (⟨z, hz⟩ : ↥Y) ∈ Subgroup.normalizer ((U.subgroupOf Y : Subgroup ↥Y) : Set ↥Y) := by
  rw [Subgroup.mem_normalizer_iff]
  intro s
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  have := Subgroup.mem_normalizer_iff.1 hzU (s : G)
  simpa using this

omit [Finite G] in
theorem mem_pCore_of_le_pCoreOf {Y N : Subgroup G} (hN : N ≤ pCoreOf 2 Y) {x : G} (hx : x ∈ N)
    (hxY : x ∈ Y) : (⟨x, hxY⟩ : ↥Y) ∈ CFSG.pCore 2 ↥Y := by
  obtain ⟨r, hr, hrx⟩ := hN hx
  have : r = ⟨x, hxY⟩ := Subtype.ext hrx
  rw [this] at hr
  have h2 := hr
  rwa [SetLike.mem_coe] at h2

end Aux

section Main

open scoped commutatorElement

theorem szTriangle_main (h214 : Lemma214)
    (hInv : InvolutionClassInput) (h215 : Lemma215Stmt) (h26 : Lemma26Input)
    (hD : SzData T T₁ a) {c : G} (hc : c ∈ Subgroup.normalizer (T : Set G))
    (hel : IsElemAbelian 2 (normIn T T₁ ⊔ normIn T₁ T ⊔ conjSubgroup c (normIn T₁ T)))
    (hnorm : ∀ y ∈ T ⊔ T₁ ⊔ conjSubgroup c T₁,
      ∀ n ∈ normIn T T₁ ⊔ normIn T₁ T ⊔ conjSubgroup c (normIn T₁ T),
        y * n * y⁻¹ ∈ normIn T T₁ ⊔ normIn T₁ T ⊔ conjSubgroup c (normIn T₁ T)) :
    conjSubgroup c T₁ ≤ T ⊔ T₁ := by
  classical
  have hS := hD.sec3
  have hcfg := hS.cfg
  have hT : IsWC T := hcfg.wc
  have ha : 1 ≤ a := hD.ha
  have hD₂ : SzData T (conjSubgroup c T₁) a := szData_conj_normalizer hD hc
  set T₂ : Subgroup G := conjSubgroup c T₁ with hT₂
  set N : Subgroup G := normIn T T₁ ⊔ normIn T₁ T ⊔ conjSubgroup c (normIn T₁ T) with hN
  set Y : Subgroup G := T ⊔ T₁ ⊔ T₂ with hY
  have hTY : T ≤ Y := le_trans le_sup_left le_sup_left
  have hT₁Y : T₁ ≤ Y := le_trans le_sup_right le_sup_left
  have hT₂Y : T₂ ≤ Y := le_sup_right
  have hXY : T ⊔ T₁ ≤ Y := le_sup_left
  have hL₁₂ : conjSubgroup c (normIn T₁ T) ≤ T₂ := Subgroup.map_mono (normIn_le T₁ T)
  have hNY : N ≤ Y := sup_le (sup_le (le_trans (normIn_le T T₁) hTY)
    (le_trans (normIn_le T₁ T) hT₁Y)) (le_trans hL₁₂ hT₂Y)
  have hMN : cfgM T T₁ ≤ N := le_sup_left
  have hYN : ∀ y ∈ Y, conjSubgroup y N = N := fun y hy =>
    conjSubgroup_eq_of_le fun z hz => by
      have h1 : y⁻¹ * z * y ∈ N := mem_conjSubgroup.1 hz
      have h2 := hnorm y hy _ h1
      have e : y * (y⁻¹ * z * y) * y⁻¹ = z := by group
      rwa [e] at h2
  have hN2 : IsPGroup 2 N := isPGroup_two_of_isElemAbelian hel
  have hNle : N ≤ pCoreOf 2 Y := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hNY
    (fun y hy => mem_normalizer_of_conjSubgroup_eq (hYN y hy)) hN2
  obtain ⟨x₀, hx₀X, hx₀⟩ := hS.conj
  obtain ⟨x₂, hx₂X, hx₂⟩ := hD₂.sec3.conj
  have hx₀Y : x₀ ∈ Y := hXY hx₀X
  have hx₂Y : x₂ ∈ Y := (sup_le (le_trans le_sup_left hXY) hT₂Y) hx₂X
  have hLpos : 0 < Nat.card (normIn T T₁) := Nat.card_pos
  have hTcard : Nat.card T = Nat.card (normIn T T₁) * 2 ^ (2 * a + 1) := hD.card_eq_mul
  have hq8 : 8 ≤ 2 ^ (2 * a + 1) := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  set TR : Subgroup ↥Y := T.subgroupOf Y with hTR
  have hWC : IsWC TR := isWC_subgroupOf hT Y hTY
  have hgen : Y ≤ ⨆ g : ↥Y, conjSubgroup (g : G) T := by
    refine sup_le (sup_le ?_ ?_) ?_
    · exact le_iSup_of_le (⟨1, Y.one_mem⟩ : ↥Y) (by rw [conjSubgroup_one])
    · rw [hx₀]
      exact le_iSup (fun g : ↥Y => conjSubgroup (g : G) T) ⟨x₀, hx₀Y⟩
    · rw [hx₂]
      exact le_iSup (fun g : ↥Y => conjSubgroup (g : G) T) ⟨x₂, hx₂Y⟩
  have hcl : Subgroup.normalClosure (TR : Set ↥Y) = ⊤ :=
    normalClosure_subgroupOf_eq_top_of_le hTY hgen
  have hglob : Sec3Global T := Sec3Global.of_inputs h214 hInv hT
  have hQT : ⁅N, T⁆ ≠ ⊥ := by
    obtain ⟨t₀, ht₀T, ht₀M⟩ := IsConcreteLE.not_le_iff_exists.1 hS.not_le_cfgM
    obtain ⟨⟨x, hx⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hcfg.ne₁
    have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
    have hxt : x * t₀ ≠ t₀ * x := by
      intro h
      have hxL : x ∈ normIn T T₁ := by
        rw [← hcfg.cfgM_inf_centralizer ht₀T ht₀M]
        exact Subgroup.mem_inf.2 ⟨Cfg.normIn_le_cfgM_right T T₁ hx,
          Subgroup.mem_centralizer_singleton_iff.2 h⟩
      have h2 : x ∈ T ⊓ T₁ := Subgroup.mem_inf.2 ⟨normIn_le _ _ hxL, normIn_le _ _ hx⟩
      rw [hcfg.inf, Subgroup.mem_bot] at h2
      exact hx1' h2
    intro hbot
    have hmem : ⁅x, t₀⁆ ∈ ⁅N, T⁆ :=
      Subgroup.commutator_mem_commutator (hMN (Cfg.normIn_le_cfgM_right T T₁ hx)) ht₀T
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hxt (commutatorElement_eq_one_iff_mul_comm.1 hmem)
  have hroot : CFSG.Timmesfeld.IsRootInvolutionSet (classD TR) :=
    isRootInvolutionSet_classD_subgroupOf
      (isRootInvolutionSet_classDIn_of_not_commute_of_global hglob hT hTY fun h =>
        hQT (le_bot_iff.1 ((Subgroup.commutator_mono hNle le_rfl).trans h.le)))
  have h4 : 4 ≤ Nat.card (TR.map (QuotientGroup.mk' (CFSG.pCore 2 ↥Y))) := by
    refine four_le_card_map_pCore hT hTY hx₀Y ?_
    rw [← hx₀, hTcard]
    nlinarith
  have htrans : ∀ t ∈ TR, t ∉ CFSG.pCore 2 ↥Y → ∀ t' ∈ TR, t' ∉ CFSG.pCore 2 ↥Y →
      ∃ z ∈ Subgroup.normalizer (TR : Set ↥Y), z * t * z⁻¹ = t' := by
    intro t ht htO t' ht' ht'O
    have htT : (t : G) ∈ T := Subgroup.mem_subgroupOf.1 ht
    have ht'T : (t' : G) ∈ T := Subgroup.mem_subgroupOf.1 ht'
    have htM : (t : G) ∉ cfgM T T₁ := fun hM => htO (mem_pCore_of_le_pCoreOf hNle (hMN hM) t.2)
    have ht'M : (t' : G) ∉ cfgM T T₁ := fun hM =>
      ht'O (mem_pCore_of_le_pCoreOf hNle (hMN hM) t'.2)
    obtain ⟨z, hzX, hzN, hz⟩ := hS.exists_mem_normalizer_conj htT htM ht'T ht'M
    refine ⟨⟨z, hXY hzX⟩, mem_normalizer_subgroupOf (hXY hzX) hzN, Subtype.ext ?_⟩
    simpa using hz
  obtain ⟨hsimple, hnabK, hHyp⟩ := lemma26Hyp_jQuot h215 hWC hcl hroot h4 htrans
  have hConcl := h26.apply hHyp
  obtain ⟨hNormX, ⟨e⟩⟩ := hD.iso
  have := hNormX
  set π : ↥Y →* jQuot ↥Y := jMap ↥Y with hπ
  have hker : (cfgM T T₁).subgroupOf (T ⊔ T₁) ≤
      (π.comp (Subgroup.inclusion hXY)).ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    have hxM : (x : G) ∈ cfgM T T₁ := Subgroup.mem_subgroupOf.1 hx
    have h1 := pCore_le_ker_jMap (mem_pCore_of_le_pCoreOf hNle (hMN hxM) (hXY x.2))
    exact MonoidHom.mem_ker.1 h1
  let φ : (↥(T ⊔ T₁) ⧸ (cfgM T T₁).subgroupOf (T ⊔ T₁)) →* jQuot ↥Y :=
    QuotientGroup.lift _ (π.comp (Subgroup.inclusion hXY)) hker
  have hφmk : ∀ x : ↥(T ⊔ T₁), φ (QuotientGroup.mk x) = π ⟨x, hXY x.2⟩ := fun x => rfl
  have hsimpleXQ : IsSimpleGroup (↥(T ⊔ T₁) ⧸ (cfgM T T₁).subgroupOf (T ⊔ T₁)) :=
    CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.isSimpleGroup
      (CFSG.CGT.Timmesfeld75.isBenderGroup_of_mulEquiv_sz ha e)
  have hHyp4 := hHyp.2.1
  have hφinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases (inferInstance : φ.ker.Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      have hbot : TR.map π = ⊥ := by
        rw [Subgroup.map_eq_bot_iff]
        intro t ht
        have htT : (t : G) ∈ T := Subgroup.mem_subgroupOf.1 ht
        have h1 : φ (QuotientGroup.mk (⟨(t : G), Subgroup.mem_sup_left htT⟩ : ↥(T ⊔ T₁))) = 1 :=
          MonoidHom.mem_ker.1 (h ▸ Subgroup.mem_top _)
        rw [hφmk] at h1
        exact h1
      rw [hbot, Subgroup.card_bot] at hHyp4
      omega
  have hTQ : Nat.card ((T.subgroupOf (T ⊔ T₁)).map
      (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)))) = 2 ^ (2 * a + 1) :=
    card_map_sz hS ha e
  have hTmap : TR.map π = ((T.subgroupOf (T ⊔ T₁)).map
      (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)))).map φ := by
    ext z
    constructor
    · rintro ⟨s, hs, rfl⟩
      have hsT : (s : G) ∈ T := Subgroup.mem_subgroupOf.1 hs
      exact ⟨QuotientGroup.mk' _ ⟨(s : G), Subgroup.mem_sup_left hsT⟩,
        ⟨⟨(s : G), Subgroup.mem_sup_left hsT⟩, Subgroup.mem_subgroupOf.2 hsT, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨⟨(x : G), hXY x.2⟩, Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.1 hx), rfl⟩
  have hTq : Nat.card (TR.map π) = 2 ^ (2 * a + 1) := by
    rw [hTmap, Subgroup.card_map_of_injective hφinj, hTQ]
  have hXcard : Nat.card φ.range = Nat.card (Sz a) := by
    rw [Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv.symm, Nat.card_congr e.toEquiv]
  have hrange : φ.range = ⊤ :=
    eq_top_of_card_sz hnabK hHyp.1 (by rw [hTq]; omega) hConcl hTq hXcard
  have hπx₂ : π ⟨x₂, hx₂Y⟩ ∈ φ.range := hrange ▸ Subgroup.mem_top _
  obtain ⟨q', hq'⟩ := hπx₂
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q'
  rw [hφmk] at hq'
  set xY : ↥Y := ⟨(x : G), hXY x.2⟩ with hxY
  have hw : xY⁻¹ * ⟨x₂, hx₂Y⟩ ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hq', inv_mul_cancel]
  have hTw := conjSubgroup_coe_eq_of_mem_ker_jMap hTY hT hw (g := 1) Y.one_mem
  rw [conjSubgroup_one] at hTw
  have hT₂x : T₂ = conjSubgroup (x : G) T := by
    rw [hx₂]
    have e1 : x₂ = (x : G) * ((xY⁻¹ * ⟨x₂, hx₂Y⟩ : ↥Y) : G) := by
      show x₂ = (x : G) * ((x : G)⁻¹ * x₂)
      group
    rw [e1, ← conjSubgroup_conjSubgroup, hTw]
  rw [hT₂x]
  intro y hy
  have h1 : (x : G)⁻¹ * y * x ∈ T := mem_conjSubgroup.1 hy
  have h2 : (x : G) * ((x : G)⁻¹ * y * x) * (x : G)⁻¹ ∈ T ⊔ T₁ :=
    (T ⊔ T₁).mul_mem ((T ⊔ T₁).mul_mem x.2 (Subgroup.mem_sup_left h1)) ((T ⊔ T₁).inv_mem x.2)
  rwa [show (x : G) * ((x : G)⁻¹ * y * x) * (x : G)⁻¹ = y by group] at h2

theorem szTriangleInput_of_lemma26 (h214 : Lemma214)
    (hInv : InvolutionClassInput) (h215 : Lemma215Stmt) (h26 : Lemma26Input) :
    SzTriangleInput := by
  unfold SzTriangleInput
  intro G _ _ _ _ T T₁ a hD c hc _ hel hnorm
  exact szTriangle_main h214 hInv h215 h26 hD hc hel hnorm

end Main

end CFSG.CGT.T75M
