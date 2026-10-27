module

public import CFSG.LocalAnalysis.GLTheoremB.Prop95Parts
public import CFSG.LocalAnalysis.GLTheoremB.Lemma99Setup
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.FiveThreeBridge
public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.FF531.ChevFrontier
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.FinalSmall
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.J3
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co1Final
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co2Model
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co3
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Fi22Three
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Fi24Prime
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.McL
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Suz
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.ON
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.HN
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Ly
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Th
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.B
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.M

public section

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Parts

open CFSG CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs
open CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542
open CFSG.HardMathSupport.Meierfrankenfeld.AGL81.FF531
open CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open CFSG.HardMathSupport.Cooperstein.Coordinator
open CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

namespace Lemma96Proof

theorem chevConclusion_of_offender (hFF : FFChevModuleTheorem) (X : Type) [Group X] [Finite X]
    (W : Type) [AddCommGroup W] [Module (ZMod 2) W] [Finite W] (ρ : Representation (ZMod 2) X W)
    (hρ : Function.Injective ρ) (hX : CFSG.Open.IsKGroup X)
    (A : Subgroup X) (hAel : CFSG.IsElementaryAbelian 2 A)
    (hAbest : CFSG.RankThree.FFModules.IsBestOffender ρ A) (K : Subgroup X)
    (hKq : CFSG.IsQuasisimple ↥K) (hAK : A ≤ Subgroup.normalizer (K : Set X)) (hKA : ⁅K, A⁆ = K) :
    FFChevConclusion (↥K ⧸ Subgroup.center ↥K) := by
  classical
  have hfaith : ∀ x : X, (∀ w, ρ x w = w) → x = 1 := fun x hx =>
    hρ (by ext w; simp [hx w])
  have hKbot : K ≠ ⊥ := by
    intro h
    have := CFSG.LocalCores.isQuasisimple_nontrivial hKq
    rw [h] at this
    exact not_nontrivial_iff_subsingleton.mpr inferInstance this
  have hKnt : ¬ K ≤ cenOn ρ K ⊤ := fun h => hKbot (eq_bot_iff.mpr fun k hk =>
    (Subgroup.mem_bot).mpr (hfaith k fun w => (h hk).2 w Submodule.mem_top))
  have hb : IsBestOffenderOn ρ A ⊤ :=
    (isBestOffender_iff_on ρ A (fun a _ ha => hfaith a ha)).mp ⟨hAel, hAbest⟩
  obtain ⟨V, _, _, L, E, hV, hirr, hLq, hE0, hEel, -, hEN, hoff, ψ, hψ⟩ :=
    exists_irrSection ρ K A hKq hAel hAK hKA hKnt hb
  let f : ↥K →* MulAut V := L.subtype.comp ψ
  have hrange : f.range = L := by
    show (L.subtype.comp ψ).range = L
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hψ, Subgroup.map_top,
      Subgroup.range_subtype]
  have hf0 : f.range ≠ ⊥ := by
    rw [hrange]
    have := CFSG.LocalCores.isQuasisimple_nontrivial hLq
    exact (Subgroup.nontrivial_iff_ne_bot L).mp inferInstance
  obtain ⟨hLq', ⟨e⟩⟩ :=
    CFSG.QuasithinUnique.Setup.X5.quasisimple_range_centerQuotientEquiv hKq f hf0
  rw [hrange] at hLq' e
  set H : Subgroup (MulAut V) := L ⊔ E
  have hLH : L ≤ H := le_sup_left
  have hEH : E ≤ H := le_sup_right
  have hHN : H ≤ Subgroup.normalizer (L : Set (MulAut V)) := sup_le Subgroup.le_normalizer hEN
  have hV2 : ∀ v : V, v ^ 2 = 1 := fun v => by rw [pow_two]; exact hV v
  have hVnt : Nontrivial V := hirr.1
  have hP : ∀ P : Subgroup (MulAut V), IsPGroup 2 ↥P →
      (∀ h ∈ H, ∀ p ∈ P, h * p * h⁻¹ ∈ P) → P = ⊥ := by
    intro P hP2 hPn
    have hinv : ∀ g ∈ L, ∀ v ∈ fixV P, g v ∈ fixV P := by
      intro g hg v hv p hp
      have h1 : g⁻¹ * p * g⁻¹⁻¹ ∈ P := hPn _ (H.inv_mem (hLH hg)) p hp
      have h2 := hv _ h1
      rw [inv_inv] at h2
      calc p (g v) = g ((g⁻¹ * p * g) v) := by simp [MulAut.mul_apply]
        _ = g v := by rw [h2]
    have hfix : fixV P = ⊤ := by
      rcases hirr.2 (fixV P) hinv with h | h
      · exact absurd h (fixV_ne_bot_of_isPGroup' hV2 hP2)
      · exact h
    rw [eq_bot_iff]
    intro p hp
    rw [Subgroup.mem_bot]
    ext v
    have hv : v ∈ fixV P := by rw [hfix]; exact Subgroup.mem_top v
    exact hv p hp
  have hNorm2 : ∀ N : Subgroup ↥H, N.Normal → IsPGroup 2 ↥N → N = ⊥ := by
    intro N hNn hN2
    have h1 := hP (N.map H.subtype) (hN2.map H.subtype) (fun h hh p hp => by
      obtain ⟨q, hq, rfl⟩ := hp
      exact ⟨⟨h, hh⟩ * q * ⟨h, hh⟩⁻¹, hNn.conj_mem q hq ⟨h, hh⟩, rfl⟩)
    rwa [Subgroup.map_eq_bot_iff_of_injective _ H.subtype_injective] at h1
  have hpCore : CFSG.pCore 2 ↥H = ⊥ := by
    unfold CFSG.pCore
    rw [sSup_eq_bot]
    rintro K ⟨hKn, hK2⟩
    exact hNorm2 K hKn hK2
  have hpCoreOf : CFSG.Open.pCoreOf 2 H = ⊥ := by
    unfold CFSG.Open.pCoreOf
    rw [CFSG.pCore_eq_iSup]
    rw [Subgroup.map_eq_bot_iff_of_injective _ H.subtype_injective]
    simp only [iSup_eq_bot]
    intro N hNn hN2
    exact hNorm2 N hNn hN2
  have hF : CFSG.Open.quasithinGenFitting H = L := by
    refine C124.quasithinGenFitting_eq_of_two_group_quot hLH (fun y hy l hl =>
      (Subgroup.mem_normalizer_iff.mp (hHN hy) l).mp hl) (.inl (B1Red.isQuasisimple_to_open hLq'))
      (fun y hy => ?_) hpCoreOf
    have hmem : y ∈ ((L ⊔ E : Subgroup (MulAut V)) : Set (MulAut V)) := hy
    rw [Subgroup.coe_mul_of_right_le_normalizer_left L E hEN] at hmem
    obtain ⟨l, hl, a, ha, rfl⟩ := hmem
    refine ⟨1, ?_⟩
    have h1 : a * l * a⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hEN ha) l).mp hl
    have h2 : a * a = 1 := hEel.2 a ha
    have e1 : (l * a) ^ 2 ^ 1 = l * (a * l * a⁻¹) * (a * a) := by rw [pow_one, pow_two]; group
    rw [e1, h2, mul_one]
    exact L.mul_mem hl h1
  have hHyp : FFHyp H L := by
    refine ⟨hF.symm, hLq', hpCore, ?_⟩
    obtain ⟨i, ⟨e'⟩⟩ := isCatalogGroup_centerQuotient' hX hKq
    exact ⟨i, ⟨e.trans e'⟩⟩
  exact ffChevConclusion_of_mulEquiv e (hFF V hV2 H L hHyp ⟨E, hEH, hE0, hEel, hoff⟩)

section Core

variable {X : Type} [Group X] [Finite X]

theorem omegaOneCenterOf_le_centralizer' (T : Subgroup X) :
    omegaOneCenterOf T ≤ Subgroup.centralizer (T : Set X) := by
  unfold omegaOneCenterOf omegaOneOf
  refine (Subgroup.closure_le _).2 fun x hx => ?_
  have hx1 : x ∈ T ⊓ Subgroup.centralizer (T : Set X) := hx.1
  exact hx1.2

theorem pCore_le_gnC {T : Subgroup X} (hQT : CFSG.pCore 2 X ≤ T) :
    CFSG.pCore 2 X ≤ gnC T := by
  have hn : (Subgroup.centralizer (CFSG.pCore 2 X : Set X)).Normal := Subgroup.normal_centralizer
  have h1 : gnV T ≤ Subgroup.centralizer (CFSG.pCore 2 X : Set X) := by
    refine Subgroup.normalClosure_le_normal (fun z hz => ?_)
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro o ho
    exact Subgroup.mem_centralizer_iff.mp (omegaOneCenterOf_le_centralizer' T hz) o (hQT ho)
  intro o ho
  rw [gnC, Subgroup.mem_centralizer_iff]
  intro v hv
  exact (Subgroup.mem_centralizer_iff.mp (h1 hv) o ho).symm

theorem mem_normalizer_thompsonJ_of_forall {T : Subgroup X} {x : X}
    (h : ∀ A : Subgroup X, IsMaxElemAbelian T A → ∀ a ∈ A, x * a * x⁻¹ ∈ T) :
    x ∈ Subgroup.normalizer (thompsonJ T : Set X) := by
  have hle : (thompsonJ T).map (MulAut.conj x).toMonoidHom ≤ thompsonJ T := by
    unfold thompsonJ
    rw [Subgroup.map_iSup]
    refine iSup_le fun A => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hA => ?_
    have hAT : A.map (MulAut.conj x).toMonoidHom ≤ T := by
      rintro _ ⟨a, ha, rfl⟩
      simpa using h A hA a ha
    refine le_iSup₂_of_le (A.map (MulAut.conj x).toMonoidHom) ⟨hAT, ?_, ?_⟩ le_rfl
    · exact CFSG.Open.IsElemAbelian.map hA.2.1 _
    · intro B hBT hBe
      have hc : Nat.card (A.map (MulAut.conj x).toMonoidHom) = Nat.card A :=
        Subgroup.card_map_of_injective (MulAut.conj x).injective
      rw [hc]
      exact hA.2.2 B hBT hBe
  have heq : (thompsonJ T).map (MulAut.conj x).toMonoidHom = thompsonJ T := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Subgroup.card_map_of_injective (MulAut.conj x).injective]
  exact Subgroup.mem_normalizer_iff_map_conj_eq.2 heq

theorem exists_isMaxElemAbelian_comm_ne_bot {T : Subgroup X} (hQT : CFSG.pCore 2 X ≤ T)
    {K : Subgroup (X ⧸ CFSG.pCore 2 X)}
    (hJ : ¬ K ≤ (Subgroup.normalizer (thompsonJ T : Set X)).map
      (QuotientGroup.mk' (CFSG.pCore 2 X))) :
    ∃ A : Subgroup X, IsMaxElemAbelian T A ∧
      ⁅K, A.map (QuotientGroup.mk' (CFSG.pCore 2 X))⁆ ≠ ⊥ := by
  by_contra hno
  push_neg at hno
  apply hJ
  intro k hk
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective k
  refine ⟨x, mem_normalizer_thompsonJ_of_forall (fun A hA a ha => ?_), rfl⟩
  have h1 : ⁅(QuotientGroup.mk' (CFSG.pCore 2 X)) x, (QuotientGroup.mk' (CFSG.pCore 2 X)) a⁆ ∈
      ⁅K, A.map (QuotientGroup.mk' (CFSG.pCore 2 X))⁆ :=
    Subgroup.commutator_mem_commutator hk (Subgroup.mem_map_of_mem _ ha)
  rw [hno A hA, Subgroup.mem_bot, ← map_commutatorElement] at h1
  have h2 : ⁅x, a⁆ ∈ CFSG.pCore 2 X := (QuotientGroup.eq_one_iff _).1 h1
  have h3 : x * a * x⁻¹ = ⁅x, a⁆ * a := by simp [commutatorElement_def]
  rw [h3]
  exact T.mul_mem (hQT h2) (hA.1 ha)

theorem thompsonJ_le_self' {Y : Type} [Group Y] (T : Subgroup Y) : thompsonJ T ≤ T :=
  iSup₂_le fun _ hA => hA.1

theorem pCoreOf_top_eq_pCore' (Y : Type) [Group Y] :
    pCoreOf 2 (⊤ : Subgroup Y) = CFSG.pCore 2 Y := by
  unfold CFSG.Open.pCoreOf
  rw [← CFSG.pCore_map_iso 2 (Subgroup.topEquiv (G := Y)).symm, Subgroup.map_map]
  have : (Subgroup.subtype ⊤).comp (Subgroup.topEquiv (G := Y)).symm.toMonoidHom =
      MonoidHom.id Y := by
    ext x
    rfl
  rw [this, Subgroup.map_id]

theorem core_ii (hFF : FFChevModuleTheorem) (hXK : CFSG.Open.IsKGroup X)
    (hC : CharTwo (⊤ : Subgroup X)) {T : Subgroup X} (hQT : pCoreOf 2 (⊤ : Subgroup X) ≤ T)
    {K : Subgroup (X ⧸ CFSG.pCore 2 X)} (hKq : CFSG.IsQuasisimple ↥K)
    (hTK : T.map (QuotientGroup.mk' (CFSG.pCore 2 X)) ≤ Subgroup.normalizer (K : Set _))
    (hJ : ¬ K ≤ (Subgroup.normalizer (thompsonJ T : Set X)).map
      (QuotientGroup.mk' (CFSG.pCore 2 X)))
    (hZ : ¬ K ≤ (Subgroup.normalizer (omegaOneCenterOf T : Set X)).map
      (QuotientGroup.mk' (CFSG.pCore 2 X))) :
    FFChevConclusion (↥K ⧸ Subgroup.center ↥K) := by
  classical
  have hOT : CFSG.pCore 2 X ≤ T := by
    rw [← pCoreOf_top_eq_pCore']
    exact hQT
  have hVT : gnV T ≤ T := gnV_le_of_le hC hQT
  have hV : IsElemAbelian 2 (gnV T) := isElemAbelian_gnV_of_le hC hQT
  letI : Module (ZMod 2) (Additive (IntMod (gnV T) hV)) :=
    binModule (fun v : IntMod (gnV T) hV => IntMod.sq_eq_one v)
  let π : X →* X ⧸ CFSG.pCore 2 X := QuotientGroup.mk' _
  let θ : X ⧸ CFSG.pCore 2 X →* X ⧸ gnC T :=
    QuotientGroup.map _ _ (MonoidHom.id X) (pCore_le_gnC hOT)
  have hKθ : ¬ K ≤ θ.ker := by
    intro h
    apply hZ
    intro k hk
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective k
    refine ⟨x, ?_, rfl⟩
    have h1 : θ (π x) = 1 := h hk
    have h2 : x ∈ gnC T := (QuotientGroup.eq_one_iff _).1 h1
    have h3 : x ∈ Subgroup.centralizer (omegaOneCenterOf T : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact Subgroup.mem_centralizer_iff.mp h2 z (Subgroup.subset_normalClosure hz)
    exact Subgroup.centralizer_le_normalizer (omegaOneCenterOf T : Set X) h3
  let Kst : Subgroup (X ⧸ gnC T) := (θ.comp K.subtype).range
  have hKr : Kst = K.map θ := by
    show (θ.comp K.subtype).range = K.map θ
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hθK : Kst ≠ ⊥ := by
    intro h
    apply hKθ
    intro k hk
    have : (θ.comp K.subtype) ⟨k, hk⟩ ∈ Kst := ⟨⟨k, hk⟩, rfl⟩
    rw [h, Subgroup.mem_bot] at this
    exact this
  obtain ⟨hKq', ⟨e⟩⟩ :=
    CFSG.QuasithinUnique.Setup.X5.quasisimple_range_centerQuotientEquiv hKq (θ.comp K.subtype) hθK
  obtain ⟨A, hA, hAK⟩ := exists_isMaxElemAbelian_comm_ne_bot hOT hJ
  have hAN : A.map π ≤ Subgroup.normalizer (K : Set _) := (Subgroup.map_mono hA.1).trans hTK
  have hKA : ⁅K, A.map π⁆ = K := commutator_eq_of_ne_bot hKq hAN hAK
  have hAst : (A.map π).map θ = A.map (QuotientGroup.mk' (gnC T)) := by
    rw [Subgroup.map_map]
    rfl
  have hAstN : A.map (QuotientGroup.mk' (gnC T)) ≤ Subgroup.normalizer (Kst : Set _) := by
    rw [← hAst, hKr]
    exact ((Subgroup.map_mono hAN).trans (Subgroup.le_normalizer_map θ))
  have hAstK : ⁅Kst, A.map (QuotientGroup.mk' (gnC T))⁆ = Kst := by
    rw [← hAst, hKr, ← Subgroup.map_commutator, hKA]
  have hX' : CFSG.Open.IsKGroup (X ⧸ gnC T) := hXK.quotient (gnC T)
  have hres := chevConclusion_of_offender hFF (X ⧸ gnC T) (Additive (IntMod (gnV T) hV))
    (gnRep hV) (gnRep_injective hV) hX' (A.map (QuotientGroup.mk' (gnC T)))
    (isElementaryAbelian_map_mk hA) (isBestOffender_gnRep_of_le hV hVT hA) Kst hKq' hAstN hAstK
  exact ffChevConclusion_of_mulEquiv e hres

end Core

section Cover

variable {X : Type} [Group X] [Finite X]

theorem not_isPGroup_two_of_isQuasisimple {Y : Type} [Group Y] [Finite Y]
    (hY : CFSG.IsQuasisimple Y) : ¬ IsPGroup 2 Y := by
  intro h
  haveI : Nontrivial Y := CFSG.LocalCores.isQuasisimple_nontrivial hY
  haveI : Group.IsPerfect Y := hY.1
  exact Group.IsPerfect.not_isNilpotent Y h.isNilpotent

theorem not_covers {T : Subgroup X} {K : Subgroup (X ⧸ CFSG.pCore 2 X)}
    (hKq : CFSG.IsQuasisimple ↥K)
    (hΓK : ⁅T.map (QuotientGroup.mk' (CFSG.pCore 2 X)), K⁆ = K)
    {N R : Subgroup X} (hRN : R ≤ N) (hR2 : IsPGroup 2 ↥R) (hRn : (R.subgroupOf N).Normal)
    (hTR : T ≤ R) (hKN : K ≤ N.map (QuotientGroup.mk' (CFSG.pCore 2 X))) : False := by
  have hRK : ⁅T.map (QuotientGroup.mk' (CFSG.pCore 2 X)), K⁆ ≤
      R.map (QuotientGroup.mk' (CFSG.pCore 2 X)) := by
    rw [Subgroup.commutator_le]
    intro g hg k hk
    have hgR : g ∈ R.map (QuotientGroup.mk' (CFSG.pCore 2 X)) := Subgroup.map_mono hTR hg
    obtain ⟨n, hn, rfl⟩ := hKN hk
    obtain ⟨r, hr, rfl⟩ := hgR
    refine ⟨r * (n * r⁻¹ * n⁻¹), R.mul_mem hr ?_, by simp [commutatorElement_def, mul_assoc]⟩
    have := hRn.conj_mem ⟨r⁻¹, hRN (R.inv_mem hr)⟩
      (by simpa [Subgroup.mem_subgroupOf] using R.inv_mem hr) ⟨n, hn⟩
    simpa [Subgroup.mem_subgroupOf] using this
  rw [hΓK] at hRK
  have hK2 : IsPGroup 2 ↥K := (hR2.map (QuotientGroup.mk' (CFSG.pCore 2 X))).to_le hRK
  exact not_isPGroup_two_of_isQuasisimple hKq hK2

end Cover

section Transfer

variable {G : Type} [Group G]

theorem subgroupOf_normalizer_map_subtype (M : Subgroup G) (S : Subgroup ↥M) :
    (Subgroup.normalizer ((S.map M.subtype : Subgroup G) : Set G)).subgroupOf M =
      Subgroup.normalizer (S : Set ↥M) := by
  ext x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  have key : ∀ s : ↥M, (s : G) ∈ (S.map M.subtype : Subgroup G) ↔ s ∈ S := fun s =>
    ⟨fun ⟨t, ht, hts⟩ => by rwa [← Subtype.ext hts], fun hs => ⟨s, hs, rfl⟩⟩
  constructor
  · intro h s
    rw [← key, h (s : G), ← key]
    rfl
  · intro h y
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨x * t * x⁻¹, (h t).1 ht, rfl⟩
    · rintro ⟨t, ht, hty⟩
      have hyM : y = ((x⁻¹ * t * x : ↥M) : G) := by
        have : (t : G) = (x : G) * y * (x : G)⁻¹ := hty
        simp [this, mul_assoc]
      refine ⟨x⁻¹ * t * x, (h _).2 ?_, hyM.symm⟩
      simpa [mul_assoc] using ht

theorem isCharIn_map_subtype {M Γ : Subgroup G} (hΓM : Γ ≤ M) {S : Subgroup ↥M}
    (hST : S ≤ Γ.subgroupOf M) (hch : (S.subgroupOf (Γ.subgroupOf M)).Characteristic) :
    IsCharIn (S.map M.subtype) Γ := by
  refine ⟨?_, fun ψ x hx => ?_⟩
  · rintro _ ⟨s, hs, rfl⟩
    exact Subgroup.mem_subgroupOf.mp (hST hs)
  · let e : ↥(Γ.subgroupOf M) ≃* ↥Γ := Subgroup.subgroupOfEquivOfLe hΓM
    let φ : ↥(Γ.subgroupOf M) ≃* ↥(Γ.subgroupOf M) := e.trans (ψ.trans e.symm)
    obtain ⟨s, hs, hsx⟩ := hx
    have hfix := hch.fixed φ
    have ht : e.symm x ∈ S.subgroupOf (Γ.subgroupOf M) := by
      rw [Subgroup.mem_subgroupOf]
      have : ((e.symm x : ↥(Γ.subgroupOf M)) : ↥M) = s := by
        apply Subtype.ext
        exact (show (((e.symm x : ↥(Γ.subgroupOf M)) : ↥M) : G) = (x : G) from rfl).trans hsx.symm
      rw [this]
      exact hs
    have h2 : φ (e.symm x) ∈ S.subgroupOf (Γ.subgroupOf M) := by
      rw [← hfix] at ht
      exact ht
    refine ⟨((φ (e.symm x) : ↥(Γ.subgroupOf M)) : ↥M), Subgroup.mem_subgroupOf.mp h2, ?_⟩
    simp [φ, e]

end Transfer

end Lemma96Proof

open Lemma96Proof

theorem lemma96_of_ffChev (hFF : FFChevModuleTheorem) : Lemma96 := by
  intro G _ _ m p hS M D hD K hKc hΓK
  classical
  have hKq : CFSG.IsQuasisimple ↥K := ((CFSG.isComponent_iff_open K).mpr hKc).1
  have hM2 : IsTwoLocal M := hD.twoLocal
  have hMtop : M ≠ ⊤ := isTwoLocal_ne_top hS hM2
  have hXK : CFSG.Open.IsKGroup ↥M := CFSG.Open.IsKProper.isKGroup hS.kProper M hMtop
  have hΓM : gammaD D ≤ M := by
    refine (gammaD_le_sigmaStar D).trans ?_
    unfold sigmaStar
    exact iSup_le fun d => iSup_le fun hd => iSup_le fun hd1 => hD.clause_a d hd hd1
  have hi : ∀ T₀ : Subgroup G, T₀ ≠ ⊥ → (IsCharIn T₀ (gammaD D) ∨ IsCharIn T₀ (sigmaOf D)) →
      ¬ K ≤ tl M (Subgroup.normalizer (T₀ : Set G)) := by
    intro T₀ h0 hchar hKN
    have hΓ : gammaD D ≤ pCoreOf 2 (Subgroup.normalizer (T₀ : Set G)) := by
      rcases hchar with h | h
      · exact gammaD_le_pCoreOf_normalizer_of_isCharIn_gammaD h0 h
      · exact gammaD_le_pCoreOf_normalizer_of_isCharIn_sigmaOf h0 h
    have hP2 : IsPGroup 2 ↥(pCoreOf 2 (Subgroup.normalizer (T₀ : Set G))) := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
    refine not_covers (T := (gammaD D).subgroupOf M) (K := K) hKq hΓK
      (N := (Subgroup.normalizer (T₀ : Set G)).subgroupOf M)
      (R := (pCoreOf 2 (Subgroup.normalizer (T₀ : Set G))).subgroupOf M) ?_ ?_ ?_ ?_ hKN
    · intro x hx
      exact Subgroup.mem_subgroupOf.mpr (CFSG.LieType.BorelTits.pCoreOf_le 2 _
        (Subgroup.mem_subgroupOf.mp hx))
    · refine hP2.of_injective
        ((M.subtype.comp (Subgroup.subtype _)).codRestrict
          (pCoreOf 2 (Subgroup.normalizer (T₀ : Set G))) (fun r => r.2)) ?_
      intro a b hab
      have h2 : (((a : ↥M)) : G) = (((b : ↥M)) : G) :=
        congrArg (fun z : ↥(pCoreOf 2 (Subgroup.normalizer (T₀ : Set G))) => (z : G)) hab
      exact Subtype.ext (Subtype.ext h2)
    · refine ⟨fun n hn g => ?_⟩
      have hg : ((g : ↥M) : G) ∈ Subgroup.normalizer (T₀ : Set G) := g.2
      have hn' : ((n : ↥M) : G) ∈ pCoreOf 2 (Subgroup.normalizer (T₀ : Set G)) :=
        Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hn)
      have := (Subgroup.mem_normalizer_iff.mp
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ hg) _).1 hn'
      exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr this)
    · intro x hx
      exact hΓ (Subgroup.mem_subgroupOf.mp hx)
  refine ⟨hi, ?_⟩
  set T : Subgroup ↥M := (gammaD D).subgroupOf M with hT
  have hΓ2 : IsPGroup 2 ↥(gammaD D) := isPGroup_gammaD D
  have hT2 : IsPGroup 2 ↥T := hΓ2.of_equiv (Subgroup.subgroupOfEquivOfLe hΓM).symm
  have hΓne : gammaD D ≠ ⊥ := by
    obtain ⟨P, hP, -, hPle⟩ := exists_ne_bot_le_pCoreOf hM2
    intro h
    exact hP (le_bot_iff.mp (h ▸ hPle.trans hD.clause_c))
  have hTne : T ≠ ⊥ := by
    intro h
    apply hΓne
    have h' : (gammaD D).subgroupOf M = ⊥ := h
    rw [← Subgroup.map_subgroupOf_eq_of_le hΓM, h', Subgroup.map_bot]
  have hC : CharTwo (⊤ : Subgroup ↥M) := by
    intro x hx
    rw [pCoreOf_top_eq_pCore'] at hx ⊢
    obtain ⟨-, hxc⟩ := hx
    have hmem : (x : G) ∈ M ⊓ Subgroup.centralizer (pCoreOf 2 M : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨x.2, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨w, hw, rfl⟩
      have := Subgroup.mem_centralizer_iff.mp hxc w hw
      exact congrArg Subtype.val this
    obtain ⟨w, hw, hwx⟩ := hS.charTwo M hM2 hmem
    have : w = x := Subtype.ext hwx
    rwa [← this]
  have hQT : pCoreOf 2 (⊤ : Subgroup ↥M) ≤ T := by
    rw [pCoreOf_top_eq_pCore']
    intro w hw
    exact Subgroup.mem_subgroupOf.mpr (hD.clause_c ⟨w, hw, rfl⟩)
  have hΓK' : ⁅T.map (QuotientGroup.mk' (CFSG.pCore 2 ↥M)), K⁆ = K := hΓK
  have hTK : T.map (QuotientGroup.mk' (CFSG.pCore 2 ↥M)) ≤ Subgroup.normalizer (K : Set _) := by
    have := Subgroup.normalizer_commutator_ge_left
      (T.map (QuotientGroup.mk' (CFSG.pCore 2 ↥M))) K
    rwa [hΓK'] at this
  have key : ∀ S : Subgroup ↥M, S ≠ ⊥ → S ≤ T → (S.subgroupOf T).Characteristic →
      ¬ K ≤ (Subgroup.normalizer (S : Set ↥M)).map (QuotientGroup.mk' (CFSG.pCore 2 ↥M)) := by
    intro S hS0 hST hch hKS
    refine hi (S.map M.subtype) ?_ (Or.inl (isCharIn_map_subtype hΓM hST hch)) ?_
    · intro h
      exact hS0 ((Subgroup.map_eq_bot_iff_of_injective _ M.subtype_injective).mp h)
    · show K ≤ ((Subgroup.normalizer ((S.map M.subtype : Subgroup G) : Set G)).subgroupOf M).map _
      rw [subgroupOf_normalizer_map_subtype]
      exact hKS
  exact core_ii hFF hXK hC hQT hKq hTK
    (key _ (CFSG.QuasithinUnique.Setup.thompsonJ_ne_bot hT2 hTne) (thompsonJ_le_self' T)
      (CFSG.QuasithinUnique.Setup.characteristic_thompsonJ T))
    (key _ (CFSG.QuasithinUnique.Setup.omegaOneCenterOf_ne_bot hT2 hTne)
      (CFSG.QuasithinUnique.Setup.omegaOneCenterOf_le T)
      (CFSG.QuasithinUnique.Setup.characteristic_omegaOneCenterOf T))

set_option linter.unusedSectionVars false


theorem lemma96_holds : Lemma96 := lemma96_of_ffChev (ffChevModuleTheorem_of
    (FFSporadic.gf2NoFFSporadic_of_each FFSporadic.gf2NoFFSporadicFor_J3
        FFSporadic.gf2NoFFSporadicFor_Co1 FFSporadic.gf2NoFFSporadicFor_Co2
        FFSporadic.gf2NoFFSporadicFor_Co3 FFSporadic.gf2NoFFSporadicFor_Fi22
        FFSporadic.gf2NoFFSporadicFor_Fi23 FFSporadic.gf2NoFFSporadicFor_Fi24Prime
        FFSporadic.gf2NoFFSporadicFor_McL FFSporadic.gf2NoFFSporadicFor_Suz
        FFSporadic.gf2NoFFSporadicFor_ONan FFSporadic.gf2NoFFSporadicFor_HN
        FFSporadic.gf2NoFFSporadicFor_Ly FFSporadic.gf2NoFFSporadicFor_Th
        FFSporadic.gf2NoFFSporadicFor_B FFSporadic.gf2NoFFSporadicFor_M)
    (HardMathSupport.Meierfrankenfeld.LieOdd.gf2NoFFLieOdd_of_nodes
        HardMathSupport.Meierfrankenfeld.LieOdd.gf2NoFFLieOddExceptional
        HardMathSupport.Meierfrankenfeld.LieOdd.gf2NoFFLieOddSmall))

end CFSG.LocalAnalysis.GLTheoremB.Prop95Parts
