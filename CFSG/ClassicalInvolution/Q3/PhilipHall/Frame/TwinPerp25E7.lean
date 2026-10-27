module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25E4
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25E6

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q8P.Asc77.P25R.EndL

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
open CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap
open CFSG.ClassicalInvolution.Asc77.C5O
open CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.C5O (Om5Data Om5Centerless Om5InvFixFour Om5Interchange Om5ZSwap
  Om5USwapNotZ Om5ExcClass ModelFacts TwinShare M8GFacts Om5TwinComm Om5TwinCommSwap HasBigFix)
open CFSG.ClassicalInvolution.Balance
open CFSG.ClassicalInvolution.Asc77.ExactLayer (isPGroup_zpowers_of_sq_eq_one)
open scoped commutatorElement

section Gen

variable {X X' : Type} [Group X] [Group X']

theorem map_symm_map_eq (e : X ≃* X') (S : Subgroup X) :
    (S.map e.toMonoidHom).map e.symm.toMonoidHom = S := by
  rw [Subgroup.map_map]
  have : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id X := by
    ext x
    simp
  rw [this, Subgroup.map_id]

end Gen

section LiftMap

variable {X X' : Type} [Group X] [Group X'] [Finite X]

theorem liftFam_map' {Φ : Set (Subgroup X)} {Φ' : Set (Subgroup X')} (σ : X ≃* X')
    (hσ : ∀ K ∈ Φ, K.map σ.toMonoidHom ∈ Φ') {M : Subgroup X} (hM : M ∈ liftFam Φ) :
    M.map σ.toMonoidHom ∈ liftFam Φ' := by
  obtain ⟨J, hJ, L, u, hL, rfl⟩ := hM
  refine ⟨J.map σ.toMonoidHom, hσ J hJ, L.map σ.toMonoidHom, σ u,
    TwinExitPf10.isLiftOf_map σ hL, ?_⟩
  rw [TwinExitPf10.satU_map]

end LiftMap

section Fam

variable {G : Type} [Group G] [Finite G] [CoreLike G] {Ω : Set (Subgroup G)}
  {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z t u₁ u₂ a : G}

@[expose] def famBar (Ω : Set (Subgroup G)) (c : G) : Set (Subgroup (layerBar Ω c)) :=
  {T | ∃ J ∈ tqMembers3 Ω c, T = imgK Ω c J}

theorem conjSub_mem_tqMembers3_gen (hΩ : ConjInvariant Ω) {g c c' : G} (hg : g * c * g⁻¹ = c')
    {J : Subgroup G} (hJ : J ∈ tqMembers3 Ω c) : conjSub g J ∈ tqMembers3 Ω c' := by
  refine ⟨hΩ g J hJ.1, ?_⟩
  have h := trivialOnQuot_conjSub hJ.2 g
  rwa [hg] at h

namespace Ctx

theorem fam_eq (C : Ctx Ω K K' W S R R' z t u₁ u₂ a) : C.fam = liftFam (famBar Ω a) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨M₀, hM₀, rfl⟩
    refine liftFam_map' C.lbe.symm ?_ hM₀
    intro J₀ hJ₀
    obtain ⟨J, hJ, rfl⟩ := exists_of_mem_secFam hJ₀
    refine ⟨J, hJ, ?_⟩
    rw [← C.map_lbe_imgK hJ, map_symm_map_eq]
  · intro M hM
    have h1 : M.map C.lbe.toMonoidHom ∈ liftFam (TwinDisc.secFam Ω a) := by
      refine liftFam_map' C.lbe ?_ hM
      rintro _ ⟨J, hJ, rfl⟩
      rw [C.map_lbe_imgK hJ]
      exact secImg_mem_secFam hJ
    exact ⟨_, h1, map_symm_map_eq C.lbe M⟩

theorem map_fam_layerAut (C : Ctx Ω K K' W S R R' z t u₁ u₂ a) {b : G}
    (hbC : b ∈ Subgroup.centralizer ({a} : Set G)) (hb : conjSub b (layerX Ω a) = layerX Ω a)
    {M : Subgroup (layerBar Ω a)} (hM : M ∈ C.fam) :
    M.map (C25Y.layerAut (layerX Ω a) hb).toMonoidHom ∈ C.fam := by
  rw [C.fam_eq] at hM ⊢
  refine liftFam_map' (C25Y.layerAut (layerX Ω a) hb) ?_ hM
  rintro _ ⟨J, hJ, rfl⟩
  exact ⟨conjSub b J, conjSub_mem_tqMembers3 C.hΩ.conjInvariant hbC hJ,
    imgK_map_layerAut hbC hb J⟩

theorem A_map_layerAut (C : Ctx Ω K K' W S R R' z t u₁ u₂ a) {A : Subgroup (layerBar Ω a)}
    (hA : A ∈ C.fam) {J : Subgroup G} (hJA : imgK Ω a J ≤ A)
    (huniq : ∀ M ∈ C.fam, imgK Ω a J ≤ M → M = A) {b : G}
    (hbC : b ∈ Subgroup.centralizer ({a} : Set G)) (hb : conjSub b (layerX Ω a) = layerX Ω a)
    (hbJ : conjSub b J = J) :
    A.map (C25Y.layerAut (layerX Ω a) hb).toMonoidHom = A := by
  apply huniq _ (C.map_fam_layerAut hbC hb hA)
  have h := imgK_map_layerAut hbC hb J
  rw [hbJ] at h
  calc imgK Ω a J = (imgK Ω a J).map (C25Y.layerAut (layerX Ω a) hb).toMonoidHom := h.symm
    _ ≤ A.map (C25Y.layerAut (layerX Ω a) hb).toMonoidHom := Subgroup.map_mono hJA

theorem map_fam_layerIso (C : Ctx Ω K K' W S R R' z t u₁ u₂ a)
    {a' : G} (C' : Ctx Ω K K' W S R R' z t u₁ u₂ a') {g : G} (hg : g * a * g⁻¹ = a')
    {M : Subgroup (layerBar Ω a)} (hM : M ∈ C.fam) :
    M.map (layerIso C.hΩ hg).toMonoidHom ∈ C'.fam := by
  rw [C.fam_eq] at hM
  rw [C'.fam_eq]
  refine liftFam_map' (layerIso C.hΩ hg) ?_ hM
  rintro _ ⟨J, hJ, rfl⟩
  exact ⟨conjSub g J, conjSub_mem_tqMembers3_gen C.hΩ.conjInvariant hg hJ,
    map_imgK_layerIso C.hΩ hg J⟩

theorem card_imgK (C : Ctx Ω K K' W S R R' z t u₁ u₂ a) {J : Subgroup G}
    (hJ : J ∈ tqMembers3 Ω a) : Nat.card (imgK Ω a J) = 8 := by
  classical
  obtain ⟨hno, -⟩ := C.h5
  have hS := layer_q8Section C.hyp C.ha2
  have hcenter : a ∉ Subgroup.center G := by
    have hZ := CoreLike.center_eq_bot (G := G)
    rw [hZ]
    exact fun h => C.ha1 (Subgroup.mem_bot.mp h)
  have hlt := card_secQuot_lt (Ω := Ω) hcenter
  have hih : TwinThmE.EIH (Nat.card G) := C.hyp.std.1.ih
  obtain ⟨h2', -, -⟩ := lifts_of_noExit hih.2 hlt hS hno
  have hJ0 : secImg Ω a J ∈ TwinDisc.secFam Ω a := secImg_mem_secFam hJ
  have hP : IsSylow2In (secImg Ω a J) (secImg Ω a J) :=
    ⟨le_rfl, h2' _ hJ0, fun V' hV'J _ hPV' => le_antisymm hV'J hPV'⟩
  obtain ⟨e⟩ := hS.q8 _ hJ0 _ hP
  have h8 : Nat.card (secImg Ω a J) = 8 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  rw [← h8, ← C.map_lbe_imgK hJ]
  exact (Subgroup.card_map_of_injective C.lbe.injective).symm

end Ctx

end Fam

section Twin

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def twinM (a : G) (K K' : Subgroup G) : Subgroup G :=
  TwinADescent.coreAt a K ⊔ TwinADescent.coreAt a K'

@[expose] noncomputable def twinπ (Ω : Set (Subgroup G)) (c : G) {M : Subgroup G}
    (h : M ≤ layerX Ω c) : ↥M →* layerBar Ω c :=
  (QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerX Ω c))).comp (Subgroup.inclusion h)

theorem twinπ_apply (Ω : Set (Subgroup G)) (c : G) {M : Subgroup G} (h : M ≤ layerX Ω c)
    (m : ↥M) : twinπ Ω c h m = QuotientGroup.mk ⟨(m : G), h m.2⟩ := rfl

theorem map_twinπ (Ω : Set (Subgroup G)) (c : G) {M B : Subgroup G} (h : M ≤ layerX Ω c)
    (hB : B ≤ M) : (B.subgroupOf M).map (twinπ Ω c h) =
      (B.subgroupOf (layerX Ω c)).map
        (QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerX Ω c))) := by
  ext e
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact ⟨⟨m, h m.2⟩, hm, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, hB hy⟩, hy, rfl⟩

theorem odd_card_ker_twinπ (Ω : Set (Subgroup G)) (c : G) {M : Subgroup G}
    (h : M ≤ layerX Ω c) : Odd (Nat.card (twinπ Ω c h).ker) := by
  have h1 : Nat.card ((twinπ Ω c h).ker.map M.subtype) = Nat.card (twinπ Ω c h).ker :=
    Subgroup.card_map_of_injective M.subtype_injective
  have h2 : (twinπ Ω c h).ker.map M.subtype ≤ oddCoreIn (layerX Ω c) := by
    rintro _ ⟨m, hm, rfl⟩
    exact (mk_eq_one_iff (layerX Ω c) ⟨m, h m.2⟩).mp hm
  rw [← h1]
  exact Odd.of_dvd_nat (odd_card_oddCoreIn _) (Subgroup.card_dvd_of_le h2)

end Twin

section Share

variable {G : Type} [Group G] [Finite G] [CoreLike G] {Ω : Set (Subgroup G)}
  {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z t u₁ u₂ a : G}

namespace Ctx

theorem K_le_cent (C : Ctx Ω K K' W S R R' z t u₁ u₂ a) :
    K ≤ Subgroup.centralizer ({z} : Set G) ∧ K' ≤ Subgroup.centralizer ({z} : Set G) := by
  obtain ⟨-, -, hz, hz', -, -⟩ := layer_twins_tq C.hyp C.haA
  exact ⟨fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr (hz.commute_of_mem hy).symm,
    fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr (hz'.commute_of_mem hy).symm⟩

theorem coreAt_az (C : Ctx Ω K K' W S R R' z t u₁ u₂ a) :
    TwinADescent.coreAt (a * z) K = TwinADescent.coreAt a K ∧
      TwinADescent.coreAt (a * z) K' = TwinADescent.coreAt a K' :=
  ⟨coreAt_mul_eq C.K_le_cent.1 a, coreAt_mul_eq C.K_le_cent.2 a⟩

theorem twinM_le (C : Ctx Ω K K' W S R R' z t u₁ u₂ a) :
    twinM a K K' ≤ layerX Ω a ∧ twinM a K K' ≤ layerX Ω (a * z) := by
  obtain ⟨hKtq, hK'tq, -, -, -, -⟩ := layer_twins_tq C.hyp C.haA
  obtain ⟨hKtq', hK'tq', -, -, -, -⟩ := layer_twins_tq C.hyp C.swap.haA
  refine ⟨sup_le (C.coreAt_le_layerX hKtq) (C.coreAt_le_layerX hK'tq), sup_le ?_ ?_⟩
  · rw [← C.coreAt_az.1]
    exact C.swap.coreAt_le_layerX hKtq'
  · rw [← C.coreAt_az.2]
    exact C.swap.coreAt_le_layerX hK'tq'

theorem exists_twinShareQ (C : Ctx Ω K K' W S R R' z t u₁ u₂ a)
    (hMa : twinM a K K' ≤ layerX Ω a) (hMaz : twinM a K K' ≤ layerX Ω (a * z)) :
    ∃ (A₁ A₁' : Subgroup (layerBar Ω a)) (A₂ A₂' : Subgroup (layerBar Ω (a * z))),
      (∃ z₁ a₁ b₁ z₂ a₂ b₂,
        Q8.TwinShareQ C.fam A₁ A₁' z₁ a₁ b₁ C.swap.fam A₂ A₂' z₂ a₂ b₂ (twinπ Ω a hMa)
          (twinπ Ω (a * z) hMaz) ((TwinADescent.coreAt a K).subgroupOf (twinM a K K'))
          ((TwinADescent.coreAt a K').subgroupOf (twinM a K K'))) ∧
      (∀ {b : G} (hbC : b ∈ Subgroup.centralizer ({a} : Set G))
        (hb : conjSub b (layerX Ω a) = layerX Ω a), conjSub b K = K →
          A₁.map (C25Y.layerAut (layerX Ω a) hb).toMonoidHom = A₁) ∧
      (∀ {b : G} (hbC : b ∈ Subgroup.centralizer ({a * z} : Set G))
        (hb : conjSub b (layerX Ω (a * z)) = layerX Ω (a * z)), conjSub b K = K →
          A₂.map (C25Y.layerAut (layerX Ω (a * z)) hb).toMonoidHom = A₂) ∧
      (∀ {g : G} (hg : g * a * g⁻¹ = a * z), conjSub g K = K →
          A₁.map (layerIso C.hΩ hg).toMonoidHom = A₂) ∧
      (∀ {g : G} (hg : g * (a * z) * g⁻¹ = a), conjSub g K = K →
          A₂.map (layerIso C.hΩ hg).toMonoidHom = A₁) := by
  classical
  obtain ⟨hzX, hu₁X, hu₂X, hKtq, hK'tq, A₁, A₁', hD₁, hA₁, hA₁', hU₁, hU₁'⟩ := C.om5''
  obtain ⟨hzX', hu₁X', hu₂X', hKtq', hK'tq', A₂, A₂', hD₂, hA₂, hA₂', hU₂, hU₂'⟩ := C.swap.om5''
  have hL₁ : ((TwinADescent.coreAt a K).subgroupOf (twinM a K K')).map (twinπ Ω a hMa) =
      imgK Ω a K := map_twinπ Ω a hMa le_sup_left
  have hL₁' : ((TwinADescent.coreAt a K').subgroupOf (twinM a K K')).map (twinπ Ω a hMa) =
      imgK Ω a K' := map_twinπ Ω a hMa le_sup_right
  have hL₂ : ((TwinADescent.coreAt a K).subgroupOf (twinM a K K')).map (twinπ Ω (a * z) hMaz) =
      imgK Ω (a * z) K := by
    rw [map_twinπ Ω (a * z) hMaz le_sup_left]
    unfold imgK
    rw [C.coreAt_az.1]
  have hL₂' : ((TwinADescent.coreAt a K').subgroupOf (twinM a K K')).map (twinπ Ω (a * z) hMaz) =
      imgK Ω (a * z) K' := by
    rw [map_twinπ Ω (a * z) hMaz le_sup_right]
    unfold imgK
    rw [C.coreAt_az.2]
  refine ⟨A₁, A₁', A₂, A₂', ⟨toBar Ω a z hzX, toBar Ω a u₁ hu₁X, toBar Ω a u₂ hu₂X,
    toBar Ω (a * z) z hzX', toBar Ω (a * z) u₁ hu₁X', toBar Ω (a * z) u₂ hu₂X', ?_⟩,
    ?_, ?_, ?_, ?_⟩
  · refine ⟨hD₁, hD₂, ?_, odd_card_ker_twinπ Ω a hMa, odd_card_ker_twinπ Ω (a * z) hMaz,
      ⟨hL₁ ▸ hA₁, hL₁' ▸ hA₁'⟩, ⟨hL₂ ▸ hA₂, hL₂' ▸ hA₂'⟩,
      ⟨hL₁ ▸ C.card_imgK hKtq, hL₁' ▸ C.card_imgK hK'tq⟩,
      ⟨hL₂ ▸ C.swap.card_imgK hKtq', hL₂' ▸ C.swap.card_imgK hK'tq'⟩⟩
    have h := Subgroup.subgroupOf_sup (B := twinM a K K')
      (le_sup_left : TwinADescent.coreAt a K ≤ twinM a K K')
      (le_sup_right : TwinADescent.coreAt a K' ≤ twinM a K K')
    rw [← h]
    exact Subgroup.subgroupOf_self (twinM a K K')
  · intro b hbC hb hbK
    exact C.A_map_layerAut hD₁.twin.hA hA₁ hU₁ hbC hb hbK
  · intro b hbC hb hbK
    exact C.swap.A_map_layerAut hD₂.twin.hA hA₂ hU₂ hbC hb hbK
  · intro g hg hgK
    apply hU₂ _ (C.map_fam_layerIso C.swap hg hD₁.twin.hA)
    have h := map_imgK_layerIso C.hΩ hg K
    rw [hgK] at h
    calc imgK Ω (a * z) K = (imgK Ω a K).map (layerIso C.hΩ hg).toMonoidHom := h.symm
      _ ≤ A₁.map (layerIso C.hΩ hg).toMonoidHom := Subgroup.map_mono hA₁
  · intro g hg hgK
    apply hU₁ _ (C.swap.map_fam_layerIso C hg hD₂.twin.hA)
    have h := map_imgK_layerIso C.hΩ hg K
    rw [hgK] at h
    calc imgK Ω a K = (imgK Ω (a * z) K).map (layerIso C.hΩ hg).toMonoidHom := h.symm
      _ ≤ A₂.map (layerIso C.hΩ hg).toMonoidHom := Subgroup.map_mono hA₂

end Ctx

end Share

section Iter

variable {G : Type} [Group G]

theorem layerAut_one' (Y : Subgroup G) {b : G} (hb : conjSub b Y = Y) (h1 : b = 1)
    (e : ↥Y ⧸ classicalInvolutionOddCore ↥Y) : C25Y.layerAut Y hb e = e := by
  subst h1
  induction e using QuotientGroup.induction_on with
  | H w =>
    rw [C25Y.layerAut_mk]
    congr 1
    apply Subtype.ext
    rw [C25Y.coe_conjOnSub]
    group

theorem layerAut_mul_apply' (Y : Subgroup G) {x y b : G} (hx : conjSub x Y = Y)
    (hy : conjSub y Y = Y) (hb : conjSub b Y = Y) (hbe : b = x * y)
    (e : ↥Y ⧸ classicalInvolutionOddCore ↥Y) :
    C25Y.layerAut Y hb e = C25Y.layerAut Y hx (C25Y.layerAut Y hy e) := by
  subst hbe
  exact layerAut_mul_apply Y hx hy hb e

theorem layerAut_iterate_eq_id [Finite G] (Y : Subgroup G) {c : G} (hc : conjSub c Y = Y) {k : ℕ}
    (hk : c ^ k = 1) (e : ↥Y ⧸ classicalInvolutionOddCore ↥Y) :
    (⇑(C25Y.layerAut Y hc))^[k] e = e := by
  have key : ∀ j : ℕ, ∃ hcj : conjSub (c ^ j) Y = Y,
      (⇑(C25Y.layerAut Y hc))^[j] e = C25Y.layerAut Y hcj e := by
    intro j
    induction j with
    | zero =>
      refine ⟨by rw [pow_zero, conjSub_one], ?_⟩
      rw [Function.iterate_zero, id_eq]
      exact (layerAut_one' Y _ (pow_zero c) e).symm
    | succ j ih =>
      obtain ⟨hcj, hj⟩ := ih
      have hxy : conjSub (c ^ (j + 1)) Y = Y := by rw [pow_succ', conjSub_mul, hcj, hc]
      refine ⟨hxy, ?_⟩
      rw [Function.iterate_succ_apply', hj]
      exact (layerAut_mul_apply' Y hc hcj hxy (pow_succ' c j) e).symm
  obtain ⟨hck, hj⟩ := key k
  rw [hj]
  exact layerAut_one' Y hck hk e

end Iter

end CFSG.ClassicalInvolution.Q8P.Asc77.P25R.EndL
