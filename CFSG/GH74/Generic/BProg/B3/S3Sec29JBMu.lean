module

public import CFSG.GH74.Generic.BProg.B3.S3Sec29JBL1
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.GH74.Generic.BProg.B3.S3Sec29C2
public import CFSG.GH74.Generic.BProg.B3.S3Sec29C6
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsTransfer

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.S3 CFSG.GH74.Generic.S45
  CFSG.GH74.Generic.BProg CFSG.GH74.Generic.BProg.B3 CFSG.Blueprint CFSG.ABGLocalTools
  CFSG.Assembly.LowTwoRank CFSG.LocalCores CFSG.ClassicalInvolution.Balance Subgroup
  CFSG.GH74.GLS.C3.Layer1 CFSG.ComponentClassification
open scoped commutatorElement

@[expose] def MuPkgL {G : Type} [Group G] [Finite G] (K A Q : Subgroup G) (y : G)
    (L : Subgroup G) : Prop :=
  ∀ u ∈ Q, orderOf u = 2 → ∃ M : Subgroup G, IsPCompIn 2 (centralizer ({u} : Set G)) M ∧
    QShape3 (↥M ⧸ pPrimeCore 2 ↥M) ∧ y ∈ M ∧ A ⊓ K ≤ M ∧
    (∀ g ∈ centralizer ({u} : Set G) ⊓ centralizer ({y} : Set G), g ∈ normalizer (M : Set G)) ∧
    S3Sec29C.FixesLayer u M y
      (centralizer ({u} : Set G) ⊓ centralizer ({y} : Set G) ⊓ cSec L)

namespace S3Sec29JB

variable {G : Type} [Group G] [Finite G] {x y : G} {K A B Q D J : Subgroup G}

theorem centralizes_of_cover {u : G} {M Θ L₁ : Subgroup G}
    (hMc : IsPCompIn 2 (centralizer ({u} : Set G)) M) (h3 : QShape3 (↥M ⧸ pPrimeCore 2 ↥M))
    (hy : orderOf y = 2) (hM : M ≤ centralizer ({u} : Set G)) (hyM : y ∈ M) {F : Type}
    [Field F] [Finite F] {S : Subgroup ↥(S3.imgBar u M)} (hS : S3L3Lift.LayerHyp u hM hyM S F)
    (hΘL : Θ ≤ L₁) (hΘC : Θ ≤ centralizer ({u} : Set G))
    (hSθ : ∀ s' ∈ S, ∃ θ ∈ Θ, (s' : CentralizerBar u) = piC u θ) {t : G}
    (htu : t ∈ centralizer ({u} : Set G)) (hty : t ∈ centralizer ({y} : Set G))
    (htL : t ∈ cSec L₁) {s : ↥(S3.imgBar u M)} (hs : s ∈ S) :
    (s : CentralizerBar u) * piC u t = piC u t * (s : CentralizerBar u) := by
  have htN : t ∈ normalizer (M : Set G) := S3Sec29C.mem_normalizer_of_comm hMc
    (B1.PilotS3.center_trivial_of_shape3 hMc h3) hyM hy htu
    (Subgroup.mem_centralizer_singleton_iff.1 hty)
  obtain ⟨hcenM, hmodelM⟩ := S3Ctx29K26.model_centerless_of_ctx hMc h3
  obtain ⟨F₂, hF₂, hFin₂, S₀, hS₀, hcomm₀, -⟩ :=
    S3Sec29C.exists_layerHyp_comm hMc hyM hy hcenM hmodelM
  have hS₀S : S₀ = S := hS.uniq S₀ hS₀.comp
  set C' : Subgroup ↥(S3.imgBar u M) :=
    centralizer ({S3L3Lift.yK u hM hyM} : Set ↥(S3.imgBar u M)) with hC'
  have hcomm : ∀ a ∈ C', ∀ b ∈ C', ⁅a, b⁆ ∈ S := fun a ha b hb => by
    rw [← hS₀S]
    exact hcomm₀ a ha b hb
  let σ : MulAut ↥(S3.imgBar u M) := TwoThin.conjAut (S3Sec29C.piC_mem_normalizer htu htN)
  have hσ : ∀ c : ↥(S3.imgBar u M), ((σ c : ↥(S3.imgBar u M)) : CentralizerBar u) =
      piC u t * (c : CentralizerBar u) * (piC u t)⁻¹ := fun c => rfl
  have hyC : y ∈ centralizer ({u} : Set G) := hM hyM
  have hσy : σ (S3L3Lift.yK u hM hyM) = S3L3Lift.yK u hM hyM := by
    apply Subtype.ext
    rw [hσ, S3L3Lift.yK_coe]
    have hty' : t * y * t⁻¹ = y := by
      rw [Subgroup.mem_centralizer_singleton_iff.1 hty]; group
    rw [← piC_inv u htu, ← piC_mul u htu hyC, ← piC_mul u (mul_mem htu hyC) (inv_mem htu), hty']
  have hσC : ∀ a ∈ C', σ a ∈ C' := by
    intro a ha
    rw [hC', Subgroup.mem_centralizer_singleton_iff] at ha ⊢
    rw [← hσy, ← map_mul, ← map_mul, ha]
  have hσS : ∀ s' ∈ S, σ s' ∈ S := by
    intro s' hs'
    have hSC : S ≤ C' := hS.comp.1
    have hperf : ⁅S.subgroupOf C', S.subgroupOf C'⁆ = S.subgroupOf C' :=
      Subgroup.isPerfect_iff.1 (CatalogueBAlternating.pComponent_perfect hS.comp.2)
    have hSS : ⁅S, S⁆ = S := by
      have := congrArg (Subgroup.map C'.subtype) hperf
      rwa [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hSC] at this
    have h1 : s' ∈ ⁅C', C'⁆ := by
      have : s' ∈ ⁅S, S⁆ := by rw [hSS]; exact hs'
      exact Subgroup.commutator_mono hSC hSC this
    have h2 : σ s' ∈ (⁅C', C'⁆).map σ.toMonoidHom := ⟨s', h1, rfl⟩
    rw [Subgroup.map_commutator] at h2
    have hCm : C'.map σ.toMonoidHom ≤ C' := by
      rintro _ ⟨a, ha, rfl⟩
      exact hσC a ha
    exact (Subgroup.commutator_le.2 hcomm) (Subgroup.commutator_mono hCm hCm h2)
  set N₀ := pPrimeCoreOf 2 L₁ ⊓ centralizer ({u} : Set G) with hN₀
  set Nb := S3.imgBar u N₀ with hNb
  have hNodd : Nat.Coprime 2 (Nat.card ↥Nb) := by
    have h1 : Nat.card ↥Nb ∣ Nat.card ↥(N₀.subgroupOf (centralizer ({u} : Set G))) :=
      Subgroup.card_map_dvd (H := N₀.subgroupOf (centralizer ({u} : Set G))) (proj u)
    have h2 : Nat.card ↥(N₀.subgroupOf (centralizer ({u} : Set G))) = Nat.card ↥N₀ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
    have h3' : Nat.card ↥N₀ ∣ Nat.card ↥(pPrimeCoreOf 2 L₁) := Subgroup.card_dvd_of_le inf_le_left
    rw [h2] at h1
    exact Nat.Coprime.coprime_dvd_right (h1.trans h3') (coprime_card_pPrimeCoreOf L₁)
  have hNbn : ∀ θ ∈ Θ, ∀ n ∈ Nb, piC u θ * n * (piC u θ)⁻¹ ∈ Nb := by
    intro θ hθ n hn
    obtain ⟨n', hn'N, hn'e⟩ := S3.mem_imgBar.1 hn
    have hθC : θ ∈ centralizer ({u} : Set G) := hΘC hθ
    have hθO : θ ∈ normalizer (pPrimeCoreOf 2 L₁ : Set G) :=
      TwoThin.mem_normalizer_pPrimeCoreOf (Subgroup.le_normalizer (hΘL hθ))
    have hn'C : (n' : G) ∈ centralizer ({u} : Set G) := n'.2
    have hmem : θ * (n' : G) * θ⁻¹ ∈ N₀ := Subgroup.mem_inf.2
      ⟨(Subgroup.mem_normalizer_iff.1 hθO _).1 (Subgroup.mem_inf.1 hn'N).1,
        mul_mem (mul_mem hθC hn'C) (inv_mem hθC)⟩
    refine S3.mem_imgBar.2 ⟨⟨θ, hθC⟩ * n' * ⟨θ, hθC⟩⁻¹, hmem, ?_⟩
    rw [map_mul, map_mul, map_inv, hn'e, piC_of_mem u hθC]
  obtain ⟨θ, hθ, hsθ⟩ := hSθ s hs
  set w : ↥(S3.imgBar u M) := s * σ s⁻¹ with hw
  have hwS : w ∈ S := mul_mem hs (hσS _ (inv_mem hs))
  have hwc : (w : CentralizerBar u) = ⁅(s : CentralizerBar u), piC u t⁆ := by
    rw [hw, Subgroup.coe_mul, hσ, Subgroup.coe_inv, commutatorElement_def]
    group
  have hθC : θ ∈ centralizer ({u} : Set G) := hΘC hθ
  have hcC : ⁅θ, t⁆ ∈ centralizer ({u} : Set G) := by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hθC htu) (inv_mem hθC)) (inv_mem htu)
  have hwNb : (w : CentralizerBar u) ∈ Nb := by
    rw [hwc, hsθ, ← S3L3Facts.piC_commutator u hθC htu, piC_of_mem u hcC]
    exact S3.mem_imgBar.2 ⟨⟨⁅θ, t⁆, hcC⟩, Subgroup.mem_inf.2 ⟨htL.2.2 θ (hΘL hθ), hcC⟩, rfl⟩
  let f : ↥S →* CentralizerBar u := (S3.imgBar u M).subtype.comp S.subtype
  have hf : Function.Injective f :=
    (S3.imgBar u M).subtype_injective.comp S.subtype_injective
  set W : Subgroup ↥S := Nb.comap f with hW
  have hWn : W.Normal := by
    refine ⟨fun a ha g => ?_⟩
    rw [hW, Subgroup.mem_comap] at ha ⊢
    obtain ⟨θ', hθ', hgθ⟩ := hSθ g g.2
    have hfe : f (g * a * g⁻¹) = piC u θ' * f a * (piC u θ')⁻¹ := by
      rw [map_mul, map_mul, map_inv]
      exact congrArg (fun c => c * f a * c⁻¹) hgθ
    rw [hfe]
    exact hNbn θ' hθ' _ ha
  have hWc : Nat.Coprime 2 (Nat.card ↥W) := by
    rw [← Subgroup.card_map_of_injective hf]
    exact Nat.Coprime.coprime_dvd_right
      (Subgroup.card_dvd_of_le (Subgroup.map_comap_le _ _)) hNodd
  obtain ⟨eS⟩ := hS.equiv
  have hW1 : W = ⊥ := by
    have hle : W ≤ pPrimeCore 2 ↥S := le_sSup ⟨hWn, hWc⟩
    rw [S3L3Lift.pPrimeCore_eq_bot_of_sl2 hS.odd hS.big eS] at hle
    exact le_bot_iff.1 hle
  have hwW : (⟨w, hwS⟩ : ↥S) ∈ W := by
    rw [hW, Subgroup.mem_comap]
    exact hwNb
  rw [hW1, Subgroup.mem_bot] at hwW
  have hw1 : (w : CentralizerBar u) = 1 := by
    have := congrArg (fun a : ↥S => ((a : ↥(S3.imgBar u M)) : CentralizerBar u)) hwW
    simpa using this
  rw [hwc] at hw1
  exact commutatorElement_eq_one_iff_mul_comm.1 hw1

theorem fixesLayer_Mu_L1 (h : Ctx29w G x K A B Q y y D J) {u : G} (hu : u ∈ Q)
    (hu2 : orderOf u = 2) {M Λ : Subgroup G} (hMc : IsPCompIn 2 (centralizer ({u} : Set G)) M)
    (hlam : PumpCalc.IsLam x u K Λ) (hbar : PumpCalc.bar u Λ = PumpCalc.bar u M)
    (e : kBar M ≃* kBar K) (hyΛ : y ∈ Λ) :
    S3Sec29C.FixesLayer u M y
      (centralizer ({u} : Set G) ⊓ centralizer ({y} : Set G) ⊓ cSec (L1 K y)) := by
  intro hM hyM F _ _ S hS t ht s hs
  have hK : IsPCompIn 2 (centralizer ({x} : Set G)) K := h.circ.1.1.1.2.2
  have hyK : y ∈ K := (Subgroup.mem_inf.1 h.y_mem).2
  obtain ⟨hcenK, hmodelK⟩ := S3Ctx29K26.model_centerless_of_ctx hK h.shape.qShape3
  obtain ⟨F₁, hF₁, hFin₁, SK, hSK, hcommK, -⟩ :=
    S3Sec29C.exists_layerHyp_comm hK hyK h.y_ord hcenK hmodelK
  obtain ⟨L₀, hL₀, -⟩ := hSK.exists_comp h.y_ord
  have hLy : Ly29 K y = L₀ := hSK.pLayerOf_eq h.y_ord hL₀
  obtain ⟨ψ, hψs, hψk, hψc⟩ := hSK.psi_data h.y_ord hL₀
  have huL : u ∈ cSec L₀ := hLy ▸ S3Sec29Cw.Q_le_cSec_Ly h hu
  have hL₀K : L₀ ≤ K := hL₀.1.trans inf_le_left
  obtain ⟨Θ, hΘX, hΘpc, hΘuniq, -, -, hΘcov⟩ := TwoThin.cover_data (K := L₀)
    (X := L₀ ⊓ centralizer ({u} : Set G)) inf_le_left
    (TwoThin.exists_centralizer_mul_pPrimeCore huL hu2) (TwoThin.isQuasisimple_hat hL₀)
  have hΘL : Θ ≤ L₀ := hΘX.trans inf_le_left
  have hΘC : Θ ≤ centralizer ({u} : Set G) := hΘX.trans inf_le_right
  have hΘΛ : Θ ≤ Λ := PumpRigid.le_of_forall_two_elt hΘpc fun z hz h2 =>
    hlam.twoElt z (Subgroup.mem_inf.2 ⟨hL₀K (hΘL hz), hΘC hz⟩) h2
  have ho1 : ∀ o ∈ pPrimeCoreOf 2 L₀, piC x o = 1 := by
    rintro o ⟨z, hz, rfl⟩
    have hzk : z ∈ ψ.ker := hψk ▸ hz
    have h2 := hψc (z : G) z.2
    have h3 : ψ ⟨(z : G), z.2⟩ = 1 := hzk
    rw [h3] at h2
    exact h2.symm
  obtain ⟨Ξ, hΞ⟩ := S3Sec29C.exists_Xi hK hlam hMc hbar e
  have hxC : ∀ k ∈ K, k ∈ centralizer ({x} : Set G) := fun k hk => hK.1 hk
  have hSθ : ∀ s' ∈ S, ∃ θ ∈ Θ, (s' : CentralizerBar u) = piC u θ := by
    intro s' hs'
    set C' : Subgroup ↥(S3.imgBar u M) :=
      centralizer ({S3L3Lift.yK u hM hyM} : Set ↥(S3.imgBar u M)) with hC'
    set CK : Subgroup ↥(S3.imgBar x K) :=
      centralizer ({S3L3Lift.yK x hK.1 hyK} : Set ↥(S3.imgBar x K)) with hCK
    have hSC : S ≤ C' := hS.comp.1
    have hperf : ⁅S.subgroupOf C', S.subgroupOf C'⁆ = S.subgroupOf C' :=
      Subgroup.isPerfect_iff.1 (CatalogueBAlternating.pComponent_perfect hS.comp.2)
    have hSS : ⁅S, S⁆ = S := by
      have := congrArg (Subgroup.map C'.subtype) hperf
      rwa [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hSC] at this
    have hs'' : s' ∈ ⁅S, S⁆ := by
      rw [hSS]
      exact hs'
    have h1 : s' ∈ ⁅C', C'⁆ := Subgroup.commutator_mono hSC hSC hs''
    have hΞy : Ξ (S3L3Lift.yK x hK.1 hyK) = S3L3Lift.yK u hM hyM :=
      Subtype.ext (hΞ _ y hyΛ rfl)
    have hC'le : C' ≤ CK.map Ξ.toMonoidHom := by
      intro c' hc'
      have hmemCK : Ξ.symm c' ∈ CK := by
        rw [hCK, Subgroup.mem_centralizer_singleton_iff]
        apply Ξ.injective
        rw [map_mul, map_mul, hΞy, MulEquiv.apply_symm_apply]
        exact Subgroup.mem_centralizer_singleton_iff.1 hc'
      exact ⟨Ξ.symm c', hmemCK, Ξ.apply_symm_apply c'⟩
    have h2 : s' ∈ (⁅CK, CK⁆).map Ξ.toMonoidHom := by
      rw [Subgroup.map_commutator]
      exact Subgroup.commutator_mono hC'le hC'le h1
    have h3 : (⁅CK, CK⁆).map Ξ.toMonoidHom ≤ SK.map Ξ.toMonoidHom :=
      Subgroup.map_mono (Subgroup.commutator_le.2 hcommK)
    obtain ⟨sK, hsK, hsKs⟩ := h3 h2
    obtain ⟨⟨l, hl⟩, hls⟩ := hψs ⟨sK, hsK⟩
    obtain ⟨θ, hθ, o, ho, hlθ⟩ := hΘcov l hl
    have hθC : θ ∈ centralizer ({x} : Set G) := hxC θ (hL₀K (hΘL hθ))
    have hoC : o ∈ centralizer ({x} : Set G) := hxC o (hL₀K (TwoThin.pPrimeCoreOf_le L₀ ho))
    have hsKθ : (sK : CentralizerBar x) = piC x θ := by
      have h4 : (sK : CentralizerBar x) = piC x l := by rw [← hψc l hl, hls]
      rw [h4, hlθ, piC_mul x hθC hoC, ho1 o ho, mul_one]
    refine ⟨θ, hθ, ?_⟩
    rw [← hsKs]
    exact hΞ sK θ (hΘΛ hθ) hsKθ
  have hL₀L1 : L₀ ≤ L1 K y := by
    rw [← hLy]
    exact le_sup_left
  have h3M : QShape3 (↥M ⧸ pPrimeCore 2 ↥M) := S3Sec29C.qShape3_of_equiv e.symm h.shape.qShape3
  obtain ⟨⟨htu, hty⟩, htL⟩ := Subgroup.mem_inf.1 ht |>.imp_left Subgroup.mem_inf.1
  exact centralizes_of_cover hMc h3M h.y_ord hM hyM hS (hΘL.trans hL₀L1) hΘC hSθ htu hty htL hs

open C3.Layer1 in
theorem muPkgL1_of_ctx29w (h : Ctx29w G x K A B Q y y D J) : MuPkgL K A Q y (L1 K y) := by
  intro u hu hu2
  obtain ⟨M, Λ, hlt, hlam, -, ⟨e⟩, hbar, hyΛ, hyM⟩ := S3Sec29Cw.exists_Mu h hu hu2
  have hMc : IsPCompIn 2 (centralizer ({u} : Set G)) M := hlt.2.1.2.2
  have h3 : QShape3 (↥M ⧸ pPrimeCore 2 ↥M) := S3Sec29C.qShape3_of_equiv e.symm h.shape.qShape3
  refine ⟨M, hMc, h3, hyM, ?_, fun g hg => ?_, fixesLayer_Mu_L1 h hu hu2 hMc hlam hbar e hyΛ⟩
  · intro a ha
    obtain ⟨haA, haK⟩ := Subgroup.mem_inf.1 ha
    have hau : a ∈ centralizer ({u} : Set G) := Subgroup.mem_centralizer_singleton_iff.2
      ((Subgroup.mem_centralizer_iff.1 (h.Q_cent hu)) a haA)
    have haa : a ^ (2 ^ 1) = 1 := by
      obtain ⟨hAB, -, -, hBel, -⟩ := h.ext
      obtain ⟨-, hsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hBel
      rw [pow_one, pow_two]
      exact hsq a (hAB haA)
    have haΛ : a ∈ Λ := hlam.twoElt a (Subgroup.mem_inf.2 ⟨haK, hau⟩) ⟨1, haa⟩
    have hmem : TwoThin.barMk ↥(centralizer ({u} : Set G)) ⟨a, hau⟩ ∈
        (M.subgroupOf (centralizer ({u} : Set G))).map
          (TwoThin.barMk ↥(centralizer ({u} : Set G))) := by
      have h1 : TwoThin.barMk ↥(centralizer ({u} : Set G)) ⟨a, hau⟩ ∈ PumpCalc.bar u Λ :=
        ⟨⟨a, hau⟩, Subgroup.mem_subgroupOf.2 haΛ, rfl⟩
      rw [hbar] at h1
      exact h1
    have ha2 : (⟨a, hau⟩ : ↥(centralizer ({u} : Set G))) ^ (2 ^ 1) = 1 :=
      Subtype.ext (by simpa using haa)
    exact Subgroup.mem_subgroupOf.1 (mem_of_two_pow_eq_one_of_map_mem hMc.2 ha2 hmem)
  · exact S3Sec29C.mem_normalizer_of_comm hMc (B1.PilotS3.center_trivial_of_shape3 hMc h3) hyM
      h.y_ord (Subgroup.mem_inf.1 hg).1
      (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hg).2)

end S3Sec29JB

end CFSG.GH74.Generic.BProg.B3
