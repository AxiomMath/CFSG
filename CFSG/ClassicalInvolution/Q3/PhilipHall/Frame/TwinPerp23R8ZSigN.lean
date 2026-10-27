module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ZSigCtx
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ZSigAux
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8AAE7

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.ZSig

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Q3.AE
  CFSG.ClassicalInvolution.Q3.AE.Wr CFSG.ClassicalInvolution.Sp62Rec
  CFSG.ClassicalInvolution.Solomon73 CFSG.ClassicalInvolution.Solomon73.Yamaki
  CFSG.ClassicalInvolution.Balance


section NSetup

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g x : Y}

namespace ZCtx

variable (H : ZCtx n Y R S t K' W u e g x)
include H

theorem hΩ : HypOmegaGen (Om R) := (CoreData.of_S H.cfg.std.perp.core).hyp

theorem hz : IsUniqueInvolution (tightCore R) t :=
  Inner.isUniqueInvolution_core (CoreData.of_S H.cfg.std.perp.core).datum

theorem isPGroup_zpowers_e : IsPGroup 2 (Subgroup.zpowers e) :=
  ExactLayer.isPGroup_zpowers_of_sq_eq_one H.cfg.data.he2

theorem K_le_Ce : tightCore R ≤ Subgroup.centralizer ({e} : Set Y) := by
  obtain ⟨R₁, -, -, -, hR₁, -, hRD, -⟩ := e_decomp H.cfg
  have heq : tightCore R = R₁ :=
    hR₁.2.2 (tightCore R) le_rfl (H.two _ (CoreAssembly.mem_conjClass_self _)) hR₁.1
  rw [heq]
  exact hRD.2.trans (normalizer_le_centralizer_e H.cfg.data)

theorem K'_le_Ce : K' ≤ Subgroup.centralizer ({e} : Set Y) := by
  obtain ⟨-, R₁', -, -, -, hR₁', -, hR'D, -⟩ := e_decomp H.cfg
  have heq : K' = R₁' := hR₁'.2.2 K' le_rfl (H.two _ H.cfg.std.hK'.1) hR₁'.1
  rw [heq]
  exact hR'D.2.trans (normalizer_le_centralizer_e H.cfg.data)

theorem le_E_of_le_Ce {J : Subgroup Y} (hJ : J ∈ Om R)
    (hJc : J ≤ Subgroup.centralizer ({e} : Set Y)) : J ≤ rLayer (Om R) e :=
  C22G.le_rLayer_of_le_centralizer (TC.mem_RSet_of_isPGroup hJ (H.two J hJ)) hJc

theorem K_le_E : tightCore R ≤ rLayer (Om R) e :=
  H.le_E_of_le_Ce (CoreAssembly.mem_conjClass_self _) H.K_le_Ce

theorem K'_le_E : K' ≤ rLayer (Om R) e := H.le_E_of_le_Ce H.cfg.std.hK'.1 H.K'_le_Ce

theorem K_le_N : tightCore R ≤ p23XE R e x := H.K_le_E.trans le_sup_left

theorem K'_le_N : K' ≤ p23XE R e x := H.K'_le_E.trans le_sup_left

theorem t_mem_N : t ∈ p23XE R e x := H.K_le_N H.hz.mem

theorem e_mem_N : e ∈ p23XE R e x :=
  (le_sup_left : rLayer (Om R) e ≤ p23XE R e x) H.hat.e_mem

theorem exists_conj_of_le_Ce {J : Subgroup Y} (hJ : J ∈ Om R)
    (hJc : J ≤ Subgroup.centralizer ({e} : Set Y)) :
    ∃ y ∈ rLayer (Om R) e, conjSub y (tightCore R) = J := by
  have hS := p23_q8Section H.cfg.std.perp H.cfg.data.he2
  obtain ⟨I₆⟩ := H.ae6
  have htr := TwinDisc.AE5.trans_of_aeIdent (by norm_num : 5 ≤ 6) hS I₆
  have hKtq : tightCore R ∈ tqMembers3 (Om R) e :=
    mem_tqMembers3_of_le_centralizer (CoreAssembly.mem_conjClass_self _) H.K_le_Ce
  have hJtq : J ∈ tqMembers3 (Om R) e := mem_tqMembers3_of_le_centralizer hJ hJc
  obtain ⟨gb, hgb⟩ :=
    htr _ (TwinDisc.secImg_mem_secFam hKtq) _ (TwinDisc.secImg_mem_secFam hJtq)
  obtain ⟨y, hy⟩ := TwinPerpV3.A6d.exists_conj_hull_of_secImg H.hΩ H.isPGroup_zpowers_e hKtq
    hJtq ⟨gb, hgb⟩
  exact ⟨((y : ↥(Subgroup.centralizer ({e} : Set Y))) : Y),
    TwinDisc.coreHull_map_le_rLayer H.hΩ H.isPGroup_zpowers_e ⟨_, y.2, rfl⟩, hy.symm⟩

theorem twin_N : ∃ K ∈ twinSet {L | ∃ y : p23XE R e x, conjSub (y : Y) (tightCore R) = L}
    (tightCore R), K ≠ tightCore R := by
  obtain ⟨y, hy, hyK⟩ := H.exists_conj_of_le_Ce H.cfg.std.hK'.1 H.K'_le_Ce
  refine ⟨K', ⟨⟨⟨y, (le_sup_left : rLayer (Om R) e ≤ p23XE R e x) hy⟩, hyK⟩, t, H.hz, ?_⟩,
    H.cfg.std.hne⟩
  exact isUniqueInvolution_of_mem_twinSet H.hz H.cfg.std.hK'

theorem exists_four_group_E (hA : MFA) : ∃ A : Subgroup Y, A ≤ rLayer (Om R) e ∧ IsElemAbelian 2 A ∧
    2 ^ 2 ≤ Nat.card A ∧ ∀ a ∈ A, a ≠ 1 → ∃ y ∈ rLayer (Om R) e, a = y * t * y⁻¹ := by
  obtain ⟨f, hfinj, hfrange, hlab, -⟩ := H.hat.labels
  have hKE : tightCore R ≤ rLayer (Om R) e := H.K_le_E
  have htE : t ∈ rLayer (Om R) e := hKE H.hz.mem
  obtain ⟨α, hα, b, hb⟩ := hlab.label (tightCore R) (CoreAssembly.mem_conjClass_self _) hKE
  set v : Wr 6 := f ⟨t, htE⟩ with hv
  have hvmem : v ∈ memAt α hα b := by
    rw [← hb]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr H.hz.mem)
  have hv1 : v ≠ 1 := by
    intro h
    have : (⟨t, htE⟩ : ↥(rLayer (Om R) e)) = 1 := hfinj (by rw [← hv, h, map_one])
    exact H.hz.ne_one (congrArg Subtype.val this)
  have hv2 : v * v = 1 := by
    rw [hv, ← map_mul]
    have : (⟨t, htE⟩ * ⟨t, htE⟩ : ↥(rLayer (Om R) e)) = 1 := Subtype.ext H.hz.sq
    rw [this, map_one]
  obtain ⟨AW, hAW, hAab, hA4, hAcl⟩ := hA α hα b v hvmem hv1 hv2
  have hcommW : ∀ a ∈ AW, ∀ b ∈ AW, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hAab.1.is_comm.comm (⟨a, ha⟩ : ↥AW) ⟨b, hb⟩)
  refine ⟨(AW.comap f).map (rLayer (Om R) e).subtype, Subgroup.map_subtype_le _, ?_, ?_, ?_⟩
  · refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨_, ⟨a₀, ha₀, rfl⟩⟩ := a
      obtain ⟨_, ⟨b₀, hb₀, rfl⟩⟩ := b
      refine Subtype.ext ?_
      show (a₀ : Y) * b₀ = b₀ * a₀
      have h1 : f (a₀ * b₀) = f (b₀ * a₀) := by
        rw [map_mul, map_mul]
        exact hcommW _ ha₀ _ hb₀
      exact congrArg Subtype.val (hfinj h1)
    · rintro _ ⟨a₀, ha₀, rfl⟩
      show ((a₀ : Y)) ^ 2 = 1
      have h1 : f (a₀ ^ 2) = f 1 := by
        rw [map_pow, map_one]
        exact hAab.2 _ ha₀
      have := congrArg Subtype.val (hfinj h1)
      simpa using this
  · rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
    have h1 : (AW.comap f).map f = AW := by
      rw [Subgroup.map_comap_eq, inf_eq_right]
      rw [hfrange]
      exact hAW
    rw [← Subgroup.card_map_of_injective hfinj, h1]
    exact hA4
  · rintro _ ⟨a₀, ha₀, rfl⟩ hne
    have ha₀1 : f a₀ ≠ 1 := by
      intro h
      apply hne
      have : a₀ = 1 := hfinj (by rw [h, map_one])
      simp [this]
    obtain ⟨y', hy'AE, hy'⟩ := hAcl (f a₀) ha₀ ha₀1
    have hy'r : y' ∈ f.range := hfrange ▸ hy'AE
    obtain ⟨z, rfl⟩ := hy'r
    refine ⟨(z : Y), z.2, ?_⟩
    have h1 : f a₀ = f (z * ⟨t, htE⟩ * z⁻¹) := by rw [map_mul, map_mul, map_inv]; exact hy'
    have := congrArg Subtype.val (hfinj h1)
    simpa using this

theorem oc (hA : MFA) :
    classicalInvolutionOddCore ↥(p23XE R e x) ≤ Subgroup.center ↥(p23XE R e x) := by
  set N := p23XE R e x with hN
  set E := rLayer (Om R) e with hE
  set P := oddCoreOf N with hP
  have hPN : P ≤ N := oddCoreOf_le_self N
  have hPnorm : ∀ n ∈ N, ∀ p ∈ P, n * p * n⁻¹ ∈ P := fun n hn p hp =>
    T7R.conj_mem_oddCoreOf hn hp
  have hPodd : Odd (Nat.card P) := oddCoreOf_odd_natCard N
  have hEN : E ≤ N := le_sup_left
  have hE'N : conjSub x E ≤ N := le_sup_right
  have heN : e ∈ N := H.e_mem_N
  set C := Subgroup.centralizer ({t} : Set Y) with hC
  set Q := pCoreOf 2 C with hQ
  have hQ2 : IsPGroup 2 Q := (CFSG.pCore_isPGroup (p := 2) (G := ↥C)).map _
  have hQnorm : ∀ c ∈ C, ∀ q ∈ Q, c * q * c⁻¹ ∈ Q := by
    rintro c hc _ ⟨q₀, hq₀, rfl⟩
    have := (CFSG.pCore_normal (p := 2) (G := ↥C)).conj_mem q₀ hq₀ ⟨c, hc⟩
    exact ⟨_, this, rfl⟩
  have heQ : e ∈ Q := H.eO2
  obtain ⟨A, hAE, hAab, hA4, hAcl⟩ := H.exists_four_group_E hA
  have hEe : ∀ y ∈ E, e * y = y * e := fun y hy =>
    (Subgroup.mem_centralizer_singleton_iff.mp (AAE7.rLayer_le_centralizer' (Om R) e hy)).symm
  have hEnorm : ∀ g ∈ Subgroup.centralizer ({e} : Set Y), ∀ y ∈ E, g * y * g⁻¹ ∈ E := by
    intro g hg y hy
    have := conj_mem_conjSub (n := g) hy
    rwa [H.hat.normal g hg] at this
  have hPE : P ⊓ E = ⊥ := by
    have h1 := T3CII.oddCoreOf_inf_le hEN
    rw [H.hat.odd] at h1
    exact le_bot_iff.mp h1
  have hCP : ∀ o ∈ P, o * t = t * o → o * e = e * o := fun o ho hot =>
    comm_of_mem_two_normalized hPnorm hPodd hQ2 heN heQ hQnorm ho hot
  have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hAab.1.is_comm.comm (⟨a, ha⟩ : ↥A) ⟨b, hb⟩)
  have hAsq : ∀ a ∈ A, a ^ 2 = 1 := hAab.2
  have hEe' : ∀ y ∈ conjSub x E, (x * e * x⁻¹) * y = y * (x * e * x⁻¹) := by
    intro y hy
    have h1 := hEe _ (mem_conjSub_iff.mp hy)
    calc (x * e * x⁻¹) * y = x * (e * (x⁻¹ * y * x)) * x⁻¹ := by group
      _ = x * ((x⁻¹ * y * x) * e) * x⁻¹ := by rw [h1]
      _ = y * (x * e * x⁻¹) := by group
  have hEnorm' : ∀ g ∈ Subgroup.centralizer ({x * e * x⁻¹} : Set Y), ∀ y ∈ conjSub x E,
      g * y * g⁻¹ ∈ conjSub x E := by
    intro g hg y hy
    have hg0 : x⁻¹ * g * x ∈ Subgroup.centralizer ({e} : Set Y) := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hg ⊢
      calc x⁻¹ * g * x * e = x⁻¹ * (g * (x * e * x⁻¹)) * x := by group
        _ = x⁻¹ * ((x * e * x⁻¹) * g) * x := by rw [hg]
        _ = e * (x⁻¹ * g * x) := by group
    have h1 := hEnorm _ hg0 _ (mem_conjSub_iff.mp hy)
    rw [mem_conjSub_iff]
    have h2 : x⁻¹ * (g * y * g⁻¹) * x = (x⁻¹ * g * x) * (x⁻¹ * y * x) * (x⁻¹ * g * x)⁻¹ := by group
    rw [h2]
    exact h1
  have hPE' : P ⊓ conjSub x E = ⊥ := by
    have h1 := T3CII.oddCoreOf_inf_le hE'N
    have h2 : oddCoreOf (conjSub x E) = ⊥ := by
      have := ExactLayer.oddCoreOf_map_equiv (MulAut.conj x) E
      rw [H.hat.odd, Subgroup.map_bot] at this
      exact this
    rw [h2] at h1
    exact le_bot_iff.mp h1
  have hAE' : conjSub x A ≤ conjSub x E := Subgroup.map_mono hAE
  have hA' : IsElemAbelian 2 (conjSub x A) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨a', ha⟩ := a
      obtain ⟨b', hb⟩ := b
      refine Subtype.ext ?_
      show a' * b' = b' * a'
      have h1 := hAcomm _ (mem_conjSub_iff.mp ha) _ (mem_conjSub_iff.mp hb)
      calc a' * b' = x * ((x⁻¹ * a' * x) * (x⁻¹ * b' * x)) * x⁻¹ := by group
        _ = x * ((x⁻¹ * b' * x) * (x⁻¹ * a' * x)) * x⁻¹ := by rw [h1]
        _ = b' * a' := by group
    · intro a ha
      have h1 := hAsq _ (mem_conjSub_iff.mp ha)
      calc a ^ 2 = x * ((x⁻¹ * a * x) ^ 2) * x⁻¹ := by
            rw [show a = x * (x⁻¹ * a * x) * x⁻¹ by group, conj_pow]; group
        _ = 1 := by rw [h1]; group
  have hA4' : 2 ^ 2 ≤ Nat.card (conjSub x A) := by
    show 2 ^ 2 ≤ Nat.card (A.map (MulAut.conj x).toMonoidHom)
    rw [Subgroup.card_map_of_injective (MulAut.conj x).injective]
    exact hA4
  have hAcl' : ∀ a ∈ conjSub x A, a ≠ 1 → ∃ y ∈ conjSub x E, a = y * (x * t * x⁻¹) * y⁻¹ := by
    intro a ha hne
    have ha0 : x⁻¹ * a * x ∈ A := mem_conjSub_iff.mp ha
    have hne0 : x⁻¹ * a * x ≠ 1 := by
      intro h
      apply hne
      have : a = x * (x⁻¹ * a * x) * x⁻¹ := by group
      rw [this, h]; group
    obtain ⟨y, hy, hy'⟩ := hAcl _ ha0 hne0
    refine ⟨x * y * x⁻¹, conj_mem_conjSub hy, ?_⟩
    calc a = x * (x⁻¹ * a * x) * x⁻¹ := by group
      _ = x * (y * t * y⁻¹) * x⁻¹ := by rw [← hy']
      _ = (x * y * x⁻¹) * (x * t * x⁻¹) * (x * y * x⁻¹)⁻¹ := by group
  have hQ' : IsPGroup 2 (conjSub x Q) := isPGroup_conjSub x hQ2
  have hQnorm' : ∀ c ∈ Subgroup.centralizer ({x * t * x⁻¹} : Set Y), ∀ q ∈ conjSub x Q,
      c * q * c⁻¹ ∈ conjSub x Q := by
    intro c hc q hq
    have hc0 : x⁻¹ * c * x ∈ C := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hc
      show x⁻¹ * c * x ∈ Subgroup.centralizer ({t} : Set Y)
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc x⁻¹ * c * x * t = x⁻¹ * (c * (x * t * x⁻¹)) * x := by group
        _ = x⁻¹ * ((x * t * x⁻¹) * c) * x := by rw [hc]
        _ = t * (x⁻¹ * c * x) := by group
    have h1 := hQnorm _ hc0 _ (mem_conjSub_iff.mp hq)
    rw [mem_conjSub_iff]
    have h2 : x⁻¹ * (c * q * c⁻¹) * x = (x⁻¹ * c * x) * (x⁻¹ * q * x) * (x⁻¹ * c * x)⁻¹ := by group
    rw [h2]
    exact h1
  have he'N : x * e * x⁻¹ ∈ N := hE'N (conj_mem_conjSub H.hat.e_mem)
  have hCP' : ∀ o ∈ P, o * (x * t * x⁻¹) = (x * t * x⁻¹) * o → o * (x * e * x⁻¹) = (x * e * x⁻¹) * o :=
    fun o ho hot => comm_of_mem_two_normalized hPnorm hPodd hQ' he'N
      (conj_mem_conjSub heQ) hQnorm' ho hot
  have hmain := le_center_of_two_layers hPN hPnorm hPodd rfl hEe hEnorm hPE hAE hAab hA4
    hAcl hCP hEe' hEnorm' hPE' hAE' hA' hA4' hAcl' hCP'
  intro p hp
  rw [Subgroup.mem_center_iff]
  intro g
  exact Subtype.ext (hmain (p : Y) ⟨p, hp, rfl⟩ (g : Y) g.2).symm

theorem q8_of_mem {J : Subgroup Y} (hJ : J ∈ Om R) : Nonempty (↥J ≃* QuaternionGroup 2) :=
  members_sylow_q8 H.cfg.std.perp J hJ J ⟨le_rfl, H.two J hJ, fun _ hV' _ hle => le_antisymm hV' hle⟩

theorem eq_of_secImage_eq (hoc : classicalInvolutionOddCore ↥(p23XE R e x) ≤
      Subgroup.center ↥(p23XE R e x))
    {J J' : Subgroup Y} (hJ : J ∈ Om R) (hJ' : J' ∈ Om R) (hJN : J ≤ p23XE R e x)
    (hJ'N : J' ≤ p23XE R e x) (h : secImage (p23XE R e x) J = secImage (p23XE R e x) J') : J = J' := by
  have h1 := AAE7.eq_of_map_eq_central hoc (CFSG.ComponentClassification.OddCore.odd_card _)
    (H.two J hJ).comap_subtype (H.two J' hJ').comap_subtype h
  have h2 := Subgroup.subgroupOf_inj.mp h1
  rwa [inf_eq_left.mpr hJN, inf_eq_left.mpr hJ'N] at h2

theorem comm_of_secImage_comm (hoc : classicalInvolutionOddCore ↥(p23XE R e x) ≤
      Subgroup.center ↥(p23XE R e x))
    {J J' : Subgroup Y} (hJ' : J' ∈ Om R) (hJN : J ≤ p23XE R e x) (hJ'N : J' ≤ p23XE R e x)
    (hc : ∀ a ∈ secImage (p23XE R e x) J, ∀ b ∈ secImage (p23XE R e x) J', a * b = b * a) :
    ∀ a ∈ J, ∀ b ∈ J', a * b = b * a := by
  intro a ha b hb
  have hmx : QuotientGroup.mk' (classicalInvolutionOddCore ↥(p23XE R e x)) ⟨a, hJN ha⟩ ∈
      secImage (p23XE R e x) J := ⟨⟨a, hJN ha⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
  have hmy : QuotientGroup.mk' (classicalInvolutionOddCore ↥(p23XE R e x)) ⟨b, hJ'N hb⟩ ∈
      secImage (p23XE R e x) J' := ⟨⟨b, hJ'N hb⟩, Subgroup.mem_subgroupOf.mpr hb, rfl⟩
  obtain ⟨k, hk⟩ := OddQuot.two_elt (H.two J' hJ') hb
  have hya : (⟨b, hJ'N hb⟩ : ↥(p23XE R e x)) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk)
  exact congrArg Subtype.val (AAE7.comm_of_mk_comm hoc
    (CFSG.ComponentClassification.OddCore.odd_card _) hya (hc _ hmx _ hmy))

theorem eq_K'_of_comm {J : Subgroup Y} (hJ : J ∈ Om R) (hne : J ≠ tightCore R)
    (hc : ∀ a ∈ tightCore R, ∀ b ∈ J, a * b = b * a) : J = K' := by
  have hperp : KPerp (Om R) (tightCore R) = {tightCore R, K'} :=
    H.cfg.std.perp.perp.trans (twinSet_eq_pair H.cfg.std.two H.cfg.std.hK' H.cfg.std.hne)
  have hJN : J ≤ Subgroup.normalizer (tightCore R : Set Y) :=
    TC.Thin.le_normalizer_of_comm fun a ha b hb => (hc b hb a ha).symm
  have hJn : J ∈ omegaNbr (Om R) (tightCore R) :=
    (TC.mem_omegaNbr_iff H.hΩ H.two).mpr ⟨hJ, hne, hJN⟩
  have hJp : J ∈ KPerp (Om R) (tightCore R) := Set.mem_insert_of_mem _ hJn
  rw [hperp] at hJp
  rcases hJp with h | h
  · exact absurd h hne
  · exact h

theorem trans_N (hT : Thm4RTwinBelow 3 n) (hoc : classicalInvolutionOddCore ↥(p23XE R e x) ≤
      Subgroup.center ↥(p23XE R e x))
    {J : Subgroup Y} (hJ : J ∈ Om R) (hJN : J ≤ p23XE R e x) :
    ∃ y : p23XE R e x, conjSub (y : Y) (tightCore R) = J := by
  by_contra hcon
  have hmem : tightCore R ∈ Om R := CoreAssembly.mem_conjClass_self _
  have hNodd := CFSG.ComponentClassification.OddCore.odd_card ↥(p23XE R e x)
  have hΩX : HypOmegaGen (restrictFamily (Om R) (p23XE R e x)) :=
    hypOmegaGen_restrict H.hΩ (p23XE R e x)
  have h2X : ∀ L ∈ restrictFamily (Om R) (p23XE R e x), IsPGroup 2 L := by
    rintro _ ⟨L, hL, -, rfl⟩
    exact (H.two L hL).comap_subtype
  have hAX : ∀ L ∈ restrictFamily (Om R) (p23XE R e x),
      AEmpty (restrictFamily (Om R) (p23XE R e x)) L := by
    rintro _ ⟨L, hL, hLX, rfl⟩
    exact aEmpty_restrictFamily H.hΩ H.two subset_rfl hLX
      ((CoreData.of_S H.cfg.std.perp.core).aEmpty_all L hL)
  have hΔ1 := OddQuot.hypOmegaGen_quotFamily hΩX h2X hNodd
  have hΔA := OddQuot.aEmpty_quotFamily hΩX h2X hNodd hAX
  have hmemΔ : ∀ {L : Subgroup Y}, L ∈ Om R → L ≤ p23XE R e x → secImage (p23XE R e x) L ∈
      quotFamily (restrictFamily (Om R) (p23XE R e x))
        (classicalInvolutionOddCore ↥(p23XE R e x)) :=
    fun hL hLX => ⟨_, ⟨_, hL, hLX, rfl⟩, rfl⟩
  have hΔ2' : ∀ M ∈ quotFamily (restrictFamily (Om R) (p23XE R e x))
      (classicalInvolutionOddCore ↥(p23XE R e x)), IsPGroup 2 M := by
    rintro _ ⟨_, ⟨L, hL, -, rfl⟩, rfl⟩
    exact (H.two L hL).comap_subtype.map _
  have hΔ2 : ∀ M ∈ quotFamily (restrictFamily (Om R) (p23XE R e x))
      (classicalInvolutionOddCore ↥(p23XE R e x)),
      IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M) := fun M hM =>
    (hΔ2' M hM).to_quotient (classicalInvolutionOddCore ↥M)
  have hΔq : ∀ M ∈ quotFamily (restrictFamily (Om R) (p23XE R e x))
      (classicalInvolutionOddCore ↥(p23XE R e x)), ∀ P : Subgroup (SecQuot (p23XE R e x)),
      IsSylow2In P M → Nonempty (↥P ≃* QuaternionGroup (2 ^ (3 - 2))) := by
    rintro _ ⟨_, ⟨L, hL, hLX, rfl⟩, rfl⟩ P hP
    have hM2 : IsPGroup 2 (secImage (p23XE R e x) L) :=
      SectionThmD.isPGroup_secImage (H.two L hL)
    have hPM : P = secImage (p23XE R e x) L := (hP.2.2 _ le_rfl hM2 hP.1).symm
    obtain ⟨e8⟩ := H.q8_of_mem hL
    exact ⟨(MulEquiv.subgroupCongr hPM).trans
      ((SectionThmD.secImageEquiv hLX (H.two L hL)).trans e8)⟩
  have hodd : classicalInvolutionOddCore (SecQuot (p23XE R e x)) = ⊥ :=
    CFSG.ComponentClassification.OddCore.quotient_corefree ↥(p23XE R e x)
  have hcard : Nat.card (SecQuot (p23XE R e x)) < n :=
    lt_of_le_of_lt (Nat.le_of_dvd Nat.card_pos (Subgroup.index_dvd_card _)) H.card_lt
  have hnc : ¬ ∃ g : SecQuot (p23XE R e x),
      conjSub g (secImage (p23XE R e x) (tightCore R)) = secImage (p23XE R e x) J := by
    rintro ⟨g, hg⟩
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective
      (classicalInvolutionOddCore ↥(p23XE R e x)) g
    have hg' : secImage (p23XE R e x) (conjSub (y : Y) (tightCore R)) =
        secImage (p23XE R e x) J := by
      rw [SectionThmD.secImage_conjSub]
      exact hg
    have hyK : conjSub (y : Y) (tightCore R) ≤ p23XE R e x := by
      have := conjSub_mono (n := (y : Y)) H.K_le_N
      rwa [conjSub_eq_self_of_mem y.2] at this
    exact hcon ⟨y, H.eq_of_secImage_eq hoc (H.hΩ.conjInvariant _ _ hmem) hJ hyK hJN hg'⟩
  have hcomm := hT (SecQuot (p23XE R e x)) hcard _ hΔ1 hΔ2 hΔq hΔA hodd _
    (hmemΔ hmem H.K_le_N) _ (hmemΔ hJ hJN) hnc
  have hcY := H.comm_of_secImage_comm hoc hJ H.K_le_N hJN hcomm
  have hJne : J ≠ tightCore R := fun h => hcon ⟨1, by rw [h]; simp⟩
  have hJK' := H.eq_K'_of_comm hJ hJne hcY
  obtain ⟨y, hy, hyK⟩ := H.exists_conj_of_le_Ce H.cfg.std.hK'.1 H.K'_le_Ce
  exact hcon ⟨⟨y, (le_sup_left : rLayer (Om R) e ≤ p23XE R e x) hy⟩, by rw [hJK']; exact hyK⟩

theorem gen_N (hT : Thm4RTwinBelow 3 n) (hoc : classicalInvolutionOddCore ↥(p23XE R e x) ≤
      Subgroup.center ↥(p23XE R e x)) :
    (⨆ y : p23XE R e x, conjSub (y : Y) (tightCore R)) = p23XE R e x := by
  refine le_antisymm (iSup_le fun y => ?_) (sup_le ?_ ?_)
  · have := conjSub_mono (n := (y : Y)) H.K_le_N
    rwa [conjSub_eq_self_of_mem y.2] at this
  · unfold rLayer
    refine iSup₂_le fun Q hQ => iSup_le fun hQC => ?_
    rw [rSet_eq_of_isPGroup H.two] at hQ
    obtain ⟨y, hy, rfl⟩ := H.exists_conj_of_le_Ce hQ hQC
    exact le_iSup_of_le ⟨y, (le_sup_left : rLayer (Om R) e ≤ p23XE R e x) hy⟩ le_rfl
  · rw [← rLayer_conj (R := R) x e]
    unfold rLayer
    refine iSup₂_le fun Q hQ => iSup_le fun hQC => ?_
    rw [rSet_eq_of_isPGroup H.two] at hQ
    have hQE : Q ≤ conjSub x (rLayer (Om R) e) := by
      rw [← rLayer_conj (R := R) x e]
      exact C22G.le_rLayer_of_le_centralizer (TC.mem_RSet_of_isPGroup hQ (H.two Q hQ)) hQC
    obtain ⟨y, rfl⟩ := H.trans_N hT hoc hQ
      (hQE.trans (le_sup_right : conjSub x (rLayer (Om R) e) ≤ p23XE R e x))
    exact le_iSup_of_le y le_rfl

theorem outcome (hT : Thm4RTwinBelow 3 n) (hA : MFA) (hP : TL4.TightBelowRPlus 3 n) :
    TightInO2 (secInv (p23XE R e x) ⟨t, H.t_mem_N⟩) ∨ TwinE4 (SecQuot (p23XE R e x)) ∨
      LongFundSet3 (secImage (p23XE R e x) (tightCore R)) (secInv (p23XE R e x) ⟨t, H.t_mem_N⟩) := by
  have hC := CoreData.of_S H.cfg.std.perp.core
  have hq8 : Nonempty (↥(tightCore R) ≃* QuaternionGroup 2) :=
    H.q8_of_mem (CoreAssembly.mem_conjClass_self _)
  have hAe : AEmpty (Om R) (tightCore R) := hC.aEmpty
  exact sectionOutcomeS_twin (hP.twin rfl).toSet (tightBelowR_three_iff.mp hP.tbelow) H.hΩ H.two
    (CoreAssembly.mem_conjClass_self _) hq8 hAe H.K_le_N H.card_lt (H.gen_N hT (H.oc hA)) H.hz
    H.twin_N

end ZCtx

end NSetup

section Helpers

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g x : Y}

theorem isPGroup_three_zpowers {z : Y} {m : ℕ} (h : z ^ 3 ^ m = 1) :
    IsPGroup 3 (Subgroup.zpowers z) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  apply IsPGroup.of_card_dvd_pow (n := m)
  rw [Nat.card_zpowers]
  exact orderOf_dvd_of_pow_eq_one h

namespace ZCtx

variable (H : ZCtx n Y R S t K' W u e g x)
include H

theorem card_K : Nat.card (tightCore R) = 8 := by
  obtain ⟨e8⟩ := H.q8_of_mem (CoreAssembly.mem_conjClass_self (tightCore R))
  rw [Nat.card_congr e8.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]

end ZCtx

end Helpers

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.ZSig
