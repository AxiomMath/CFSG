module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6S
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7TwoWTr
public import CFSG.ClassicalInvolution.Q3.TL4WylA
public import CFSG.ClassicalInvolution.Q3.Sec13L711Mu
public import CFSG.YGroups.Y443.Native.Hom

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6Gen

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


theorem exists_weaklyClosed_conj_of_nonab {Y : Type} [Group Y] [Finite Y] {Ω : Set (Subgroup Y)}
    (hP : Q3CL.PartIHypG Ω) (htr : ∀ K₁ ∈ Ω, ∀ J ∈ Ω, ∃ g : Y, conjSub g K₁ = J)
    {W : Subgroup Y} (hW : W ∈ WSet Ω) (hnab : ¬ ∀ x y : ↥(muGroup Ω W), x * y = y * x) :
    ∃ S₀ : Sylow 2 Y, W ≤ (S₀ : Subgroup Y) ∧ Sec7.WeaklyClosedIn W (S₀ : Subgroup Y) ∧
      ∀ W₁ ∈ WSet Ω, ∃ x : Y, conjSub x W = W₁ := by
  have hW' := hW
  obtain ⟨η, hηG, hWη⟩ := hW
  obtain ⟨S₀, hηS₀, hinv⟩ := id hηG
  have hUS₀ : ∀ U ∈ η, U ≤ (S₀ : Subgroup Y) := fun U hU => (hηS₀.1 hU).2
  have hWS₀ : W ≤ (S₀ : Subgroup Y) := by
    rw [hWη]; exact iSup₂_le fun U hU => hUS₀ U hU
  have h612 := CFSG.ClassicalInvolution.Q3.Q3T8.Disconnected.AschTight.Sec7.l6_12_mod Y Ω hP htr S₀
  dsimp only at h612
  rcases h612 with ⟨η₀, -, -, huniq, hwc⟩ | h2
  swap
  · exact (TwinPerpV3.false_of_alt2_of_nonabelian hP hW' hWS₀ h2 hnab).elim
  have hMS₀ : (⨆ U ∈ {U : Subgroup Y | (∃ η ∈ etaG Ω, U ∈ η) ∧ U ≤ (S₀ : Subgroup Y)}, U) ≤
      (S₀ : Subgroup Y) := iSup₂_le fun U hU => hU.2
  have hηeq : η = η₀ := huniq η hηG fun m hm U hU => hinv m (hMS₀ hm) U hU
  subst hηeq
  refine ⟨S₀, hWS₀, ?_, ?_⟩
  · intro x hx
    rw [hWη] at hx ⊢
    refine Sec7.conjSub_iSup_eq_of_forall_mem (hwc x fun U hU => ?_)
    exact le_trans (conjSub_mono (le_iSup₂ (f := fun V (_ : V ∈ η) => V) U hU)) hx
  · intro W₁ hW₁
    obtain ⟨η₁, ⟨S₁, hS₁, hinv₁⟩, rfl⟩ := hW₁
    obtain ⟨x, hx⟩ := exists_conjSub_eq_of_sylow S₁ S₀
    have hinv₁' : ∀ s ∈ (S₀ : Subgroup Y), ∀ U ∈ conjSub x '' η₁,
        conjSub s U ∈ conjSub x '' η₁ := by
      intro s hs U hU
      obtain ⟨U₀, hU₀, rfl⟩ := hU
      have hs' : x⁻¹ * s * x ∈ (S₁ : Subgroup Y) := by
        rw [← hx, mem_conjSub_iff] at hs
        exact hs
      refine ⟨conjSub (x⁻¹ * s * x) U₀, hinv₁ _ hs' U₀ hU₀, ?_⟩
      rw [← conjSub_mul, ← conjSub_mul]
      congr 1
      group
    have hη₁' : conjSub x '' η₁ ∈ etaG Ω := by
      refine ⟨S₀, ?_, hinv₁'⟩
      have := conjSub_image_mem_etaSet hP.hyp.conjInvariant hS₁ x
      rwa [hx] at this
    have hη₁eq : conjSub x '' η₁ = η :=
      huniq _ hη₁' fun m hm U hU => hinv₁' m (hMS₀ hm) U hU
    refine ⟨x⁻¹, ?_⟩
    have e : conjSub x (⨆ U ∈ η₁, U) = W := by
      have e1 : conjSub x (⨆ U ∈ η₁, U) = ⨆ U ∈ conjSub x '' η₁, U := by
        rw [conjSub_iSup₂, iSup_image]
      rw [e1, hη₁eq, hWη]
    rw [← e, conjSub_inv_conjSub]

theorem exists_centralizer_conj_of_nonab {Y : Type} [Group Y] [Finite Y] {Ω : Set (Subgroup Y)}
    (hP : Q3CL.PartIHypG Ω) (htr : ∀ K₁ ∈ Ω, ∀ J ∈ Ω, ∃ g : Y, conjSub g K₁ = J)
    {W : Subgroup Y} (hW : W ∈ WSet Ω) (hnab : ¬ ∀ x y : ↥(muGroup Ω W), x * y = y * x)
    {z : Y} (hzW : z ∈ W) {W₁ : Subgroup Y} (hW₁ : W₁ ∈ WSet Ω) (hzW₁ : z ∈ W₁) :
    ∃ c ∈ Subgroup.centralizer ({z} : Set Y), conjSub c W = W₁ := by
  obtain ⟨S₀, hWS₀, hWC, hconj⟩ := exists_weaklyClosed_conj_of_nonab hP htr hW hnab
  obtain ⟨x, rfl⟩ := hconj W₁ hW₁
  rw [mem_conjSub_iff] at hzW₁
  have hWab : ∀ {v : Y}, v ∈ W → v ∈ Subgroup.centralizer (W : Set Y) := fun hv =>
    Subgroup.mem_centralizer_iff.mpr fun w hw =>
      Q3CL.Thompson.commutes_of_mem_WSet hP.hyp hW w hw _ hv
  obtain ⟨m, hmN, hm⟩ := Sec7.control_centralizer_of_weaklyClosed
    (S₀.isPGroup'.to_le hWS₀) hWC (hWab hzW) (g := x⁻¹) (by rw [inv_inv]; exact hWab hzW₁)
  refine ⟨x * m, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    calc x * m * z = x * (m * z * m⁻¹) * m := by group
      _ = x * (x⁻¹ * z * x⁻¹⁻¹) * m := by rw [hm]
      _ = z * (x * m) := by group
  · rw [conjSub_mul, mem_normalizer_iff_conjSub_eq.mp hmN]

variable {n : ℕ}

local notation "Ω[" R "]" => CoreAssembly.conjClass (tightCore R)

theorem q8Omega_of_hyp {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
    {K K' K₃ : Subgroup Y} {u₁ u₂ u₃ : Y} {K₄ W : Subgroup Y}
    (H : AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W) : Sec13.Q8Omega Ω[R] := by
  have hStd := H.ex.1
  have hC := CoreData.of_S hStd.perp.core
  have h2g : ∀ J ∈ Ω[R], IsPGroup 2 ↥J := H.ex.2.2.2.1
  have hcard8 : ∀ L ∈ Ω[R], Nat.card ↥L = 8 := by
    intro L hL
    obtain ⟨e⟩ := members_q8_of_isPGroup hStd.perp h2g L hL
    rw [Nat.card_congr e.toEquiv]
    simp [Nat.card_eq_fintype_card, QuaternionGroup.card]
  exact ⟨hC.hyp, h2g, hcard8, hC.aEmpty_all⟩

theorem exists_cent_conj_W {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
    {K K' K₃ : Subgroup Y} {u₁ u₂ u₃ : Y} {K₄ W : Subgroup Y}
    (H : AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W) {W₁ : Subgroup Y} (hW₁ : W₁ ∈ WSet Ω[R])
    (htW₁ : t ∈ W₁) : ∃ c ∈ Subgroup.centralizer ({t} : Set Y), conjSub c W = W₁ := by
  have hStd := H.ex.1
  have hd := hStd.datum
  have hP := (CoreData.of_S hStd.perp.core).partIHypG
  have htr : ∀ K₁ ∈ Ω[R], ∀ J ∈ Ω[R], ∃ x : Y, conjSub x K₁ = J := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    exact ⟨b * a⁻¹, by rw [conjSub_mul, conjSub_inv_conjSub]⟩
  have htW : t ∈ W := hd.sq₁ ▸ W.mul_mem H.hu₁ H.hu₁
  have hnab : ¬ ∀ x y : ↥(muGroup Ω[R] W), x * y = y * x := fun hc =>
    TL4.not_comm_of_muIsoWylD4_gen (hStd.wyl W H.hW) fun x hx y hy =>
      congrArg Subtype.val (hc ⟨x, hx⟩ ⟨y, hy⟩)
  exact exists_centralizer_conj_of_nonab hP htr H.hW hnab htW hW₁ htW₁

theorem exists_conj_of_dstarAdj {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
    {K K' K₃ : Subgroup Y} {u₁ u₂ u₃ : Y} {K₄ W : Subgroup Y}
    (H : AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W) {J' : Subgroup Y} (hadj : dstarAdj Ω[R] K J') :
    ∃ g ∈ MGrp Ω[R] W ⊔ Subgroup.centralizer ({t} : Set Y), conjSub g K = J' := by
  have hStd := H.ex.1
  have hd := hStd.datum
  have hC := CoreData.of_S hStd.perp.core
  have hΩ : HypOmegaGen Ω[R] := hC.hyp
  have hP := hC.partIHypG
  have hQ8 := q8Omega_of_hyp H
  have h2g : ∀ J ∈ Ω[R], IsPGroup 2 ↥J := H.ex.2.2.2.1
  have hK : K ∈ Ω[R] := hd.mem
  have hz : IsUniqueInvolution K t := hd.hz
  have key : ∀ W₁ : Subgroup Y, W₁ ∈ WSet Ω[R] → t ∈ W₁ →
      ∀ J : Subgroup Y, J ∈ Ω[R] → (∃ T ∈ DSet Ω[R] W₁, IsSylow2In T J) →
      ∃ g ∈ MGrp Ω[R] W ⊔ Subgroup.centralizer ({t} : Set Y), conjSub g K = J := by
    intro W₁ hW₁ htW₁ J hJΩ ⟨T, hTD, hTJ⟩
    obtain ⟨c, hc, rfl⟩ := exists_cent_conj_W H hW₁ htW₁
    have hJ0Ω : conjSub c⁻¹ J ∈ Ω[R] := hΩ.conjInvariant c⁻¹ J hJΩ
    have hT0D : conjSub c⁻¹ T ∈ DSet Ω[R] W := by
      have := hQ8.conjSub_mem_DSet hTD c⁻¹
      rwa [conjSub_inv_conjSub] at this
    have hT0J : IsSylow2In (conjSub c⁻¹ T) (conjSub c⁻¹ J) := by
      have hTJ' : T = J := (hTJ.2.2 J le_rfl (h2g J hJΩ) hTJ.1).symm
      rw [hTJ']
      exact ⟨le_rfl, h2g _ hJ0Ω, fun V' hV'K _ hKV' => le_antisymm hV'K hKV'⟩
    have c0 : Q3CL.Thompson.Ctx Ω[R] W := Q3CL.T8.ctxOf hP H.hW
    have hKsyl : IsSylow2In K K := ⟨le_rfl, h2g K hK, fun V' hV'K _ hKV' => le_antisymm hV'K hKV'⟩
    obtain ⟨ρ, hρK⟩ : ∃ ρ : Asc77.Thompson.Rep Ω[R] W, ρ.K = K :=
      ⟨Q3CL.T8.mkRep hP H.hW hK H.hK hKsyl, rfl⟩
    obtain ⟨σ, hσK⟩ : ∃ σ : Asc77.Thompson.Rep Ω[R] W, σ.K = conjSub c⁻¹ J :=
      ⟨Q3CL.T8.mkRep hP H.hW hJ0Ω hT0D hT0J, rfl⟩
    have hnc : ¬ DbarConnected Ω[R] W :=
      not_dbarConnected_of_wyl' hP hd (kPerp_datum hStd.perp hd.mem hd.hz) H.hW ρ hρK
        (hStd.wyl W H.hW)
    obtain ⟨m, hm, hmK⟩ := c0.exists_conj_of_rep hP.cls hnc ρ σ
    refine ⟨c * m, Subgroup.mul_mem _ (Subgroup.mem_sup_right hc) (Subgroup.mem_sup_left hm), ?_⟩
    rw [conjSub_mul, ← hρK, hmK, hσK, conjSub_conjSub_inv]
  obtain ⟨hJ'Ω, h' | h'⟩ := hadj
  · obtain ⟨W₁, hW₁, R₁, hR₁, T, hT, hR₁K, hTJ'⟩ :=
      CFSG.ClassicalInvolution.Q8P.Asc77.Thompson.exists_W_of_mem_omegaStarNbr hΩ hK h'
    have hzW₁ : t ∈ W₁ := (Q3CL.Thompson.uniqueInvolution_mem_W hΩ hW₁ hK hR₁ hR₁K hz).2
    exact key W₁ hW₁ hzW₁ J' hJ'Ω ⟨T, hT, hTJ'⟩
  · obtain ⟨W₁, hW₁, R₁, hR₁, T, hT, hR₁J', hTK⟩ :=
      CFSG.ClassicalInvolution.Q8P.Asc77.Thompson.exists_W_of_mem_omegaStarNbr hΩ hJ'Ω h'
    have hzW₁ : t ∈ W₁ := (Q3CL.Thompson.uniqueInvolution_mem_W hΩ hW₁ hK hT hTK hz).2
    exact key W₁ hW₁ hzW₁ J' hJ'Ω ⟨R₁, hR₁, hR₁J'⟩

theorem ae6I_sup_centralizer_eq_top (hEW : TwinThmEW.ThmEQ8) (hcit : CIT3Below n)
    (hP : TL4.TightBelowRPlus 3 n) (h4 : Thm4RTwinBelow 3 n) (h5 : V3Fourth n) (h7 : V3Alpha13 n)
    (hOpen : V3SecOpenW n) {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
    {K K' K₃ : Subgroup Y} {u₁ u₂ u₃ : Y} {K₄ W : Subgroup Y}
    (H : AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W) :
    MGrp Ω[R] W ⊔ Subgroup.centralizer ({t} : Set Y) = ⊤ := by
  have hStd := H.ex.1
  have hd := hStd.datum
  have hC := CoreData.of_S hStd.perp.core
  have hΩ : HypOmegaGen Ω[R] := hC.hyp
  set X := MGrp Ω[R] W ⊔ Subgroup.centralizer ({t} : Set Y) with hX
  have hKX : K ≤ X := by
    refine le_trans ?_ le_sup_left
    unfold MGrp
    exact le_iSup₂_of_le K H.hK le_rfl
  have hconn := A6.dstarConn_of_ae6 hEW hcit hP h4 h5 h7 hOpen H.no H.ex H.hW H.hK H.hK' H.hK₃
    H.hu₁ H.hu₂ H.ae6
  have key : ∀ J, Relation.ReflTransGen (dstarAdj Ω[R]) K J → ∃ g ∈ X, conjSub g K = J := by
    intro J hc
    induction hc with
    | refl => exact ⟨1, X.one_mem, conjSub_one K⟩
    | @tail J₁ J₂ _ hadj ih =>
      obtain ⟨h₁, hh₁, hJ₁⟩ := ih
      have hadj' : dstarAdj Ω[R] K (conjSub h₁⁻¹ J₂) := by
        obtain ⟨hJ₂, h' | h'⟩ := hadj
        · refine ⟨hΩ.conjInvariant h₁⁻¹ J₂ hJ₂, Or.inl ?_⟩
          have := omegaStarNbr_conj hΩ.conjInvariant h' h₁⁻¹
          rwa [← hJ₁, conjSub_inv_conjSub] at this
        · refine ⟨hΩ.conjInvariant h₁⁻¹ J₂ hJ₂, Or.inr ?_⟩
          have := omegaStarNbr_conj hΩ.conjInvariant h' h₁⁻¹
          rwa [← hJ₁, conjSub_inv_conjSub] at this
      obtain ⟨h₂, hh₂, hJ₂⟩ := exists_conj_of_dstarAdj H hadj'
      refine ⟨h₁ * h₂, X.mul_mem hh₁ hh₂, ?_⟩
      rw [conjSub_mul, hJ₂, conjSub_conjSub_inv]
  rw [eq_top_iff, ← hC.gen]
  refine iSup_le fun g => ?_
  obtain ⟨h, hh, hJ⟩ := key _ (hconn _ ⟨g, rfl⟩)
  have hJ' : conjSub h K = conjSub g (tightCore R) := hJ
  rw [← hJ']
  calc conjSub h K ≤ conjSub h X := conjSub_mono hKX
    _ = X := conjSub_eq_self_of_mem hh

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6Gen
