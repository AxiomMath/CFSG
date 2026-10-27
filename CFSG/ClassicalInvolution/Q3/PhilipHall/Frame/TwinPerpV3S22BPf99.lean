module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf64Adapt
public import CFSG.ClassicalInvolution.Q3.Q3PsuSup3
public import CFSG.ClassicalInvolution.Q3.Q3T7Q22PsuPair
public import CFSG.ClassicalInvolution.Q3.Q3T7Q22Psu
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDimTool
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf9Layer
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDimToolE2
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf25Bridge

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Balance.Bootstrap (trivialOnQuot)
open scoped commutatorElement

section LeafB



variable {n : ℕ}

theorem psuLayerApi3_of_cert : Q3T8.Asc77.C22G.PsuLayerApi3 where
  pair := Q3T8.Asc77.C22G.psuLayer_pair3
  sup := by
    intro X _ Φ P K J J' RK RJ RJ' hRJ' hKR hJR hJ'R h1 h2 hc
    exact Q3PsuSup.psuLayer_sup3 P hRJ' hKR hJR hJ'R h1 h2 hc

theorem gen_lift_top {H : Type} [Group H] [Finite H] {N : Subgroup H} [N.Normal]
    (hN : Odd (Nat.card N)) {a b : H} (ha : a * a = 1) (hb : b * b = 1)
    (h : ∀ g : H ⧸ N, g ∈ Subgroup.centralizer ({QuotientGroup.mk' N a} : Set (H ⧸ N)) ⊔
      Subgroup.centralizer ({QuotientGroup.mk' N b} : Set (H ⧸ N))) :
    ∀ g : H, g ∈ (Subgroup.centralizer ({a} : Set H) ⊔ Subgroup.centralizer ({b} : Set H)) ⊔ N := by
  intro g
  have h1 := (CFSG.ClassicalInvolution.Asc77.centralizer_map_le (N := N) hN ha).trans
    (Subgroup.map_mono (le_sup_left : Subgroup.centralizer ({a} : Set H) ≤
      Subgroup.centralizer ({a} : Set H) ⊔ Subgroup.centralizer ({b} : Set H)))
  have h2 := (CFSG.ClassicalInvolution.Asc77.centralizer_map_le (N := N) hN hb).trans
    (Subgroup.map_mono (le_sup_right : Subgroup.centralizer ({b} : Set H) ≤
      Subgroup.centralizer ({a} : Set H) ⊔ Subgroup.centralizer ({b} : Set H)))
  have h3 : QuotientGroup.mk' N g ∈
      (Subgroup.centralizer ({a} : Set H) ⊔ Subgroup.centralizer ({b} : Set H)).map
        (QuotientGroup.mk' N) := sup_le h1 h2 (h _)
  obtain ⟨s, hs, hsg⟩ := h3
  have hn : s⁻¹ * g ∈ N := QuotientGroup.eq.mp hsg
  have e : g = s * (s⁻¹ * g) := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hs) (Subgroup.mem_sup_right hn)

theorem layer_le_of_sec_gen {Y : Type} [Group Y] [Finite Y] {c : Y}
    {H : Subgroup ↥(Subgroup.centralizer ({c} : Set Y))} {L : Subgroup Y}
    (hmap : H.map (Subgroup.centralizer ({c} : Set Y)).subtype = L) {t t' : Y} (z τ : ↥H)
    (hz : ((z : ↥(Subgroup.centralizer ({c} : Set Y))) : Y) = t)
    (hτ : ((τ : ↥(Subgroup.centralizer ({c} : Set Y))) : Y) = t')
    (hz2 : t * t = 1) (hτ2 : t' * t' = 1)
    (hgen : ∀ g : ↥H ⧸ classicalInvolutionOddCore ↥H,
      g ∈ Subgroup.centralizer ({QuotientGroup.mk' (classicalInvolutionOddCore ↥H) z} :
          Set (↥H ⧸ classicalInvolutionOddCore ↥H)) ⊔
        Subgroup.centralizer ({QuotientGroup.mk' (classicalInvolutionOddCore ↥H) τ} :
          Set (↥H ⧸ classicalInvolutionOddCore ↥H))) :
    L ≤ ((L ⊓ Subgroup.centralizer ({t} : Set Y)) ⊔ (L ⊓ Subgroup.centralizer ({t'} : Set Y))) ⊔
      oddCoreOf L := by
  have hza : z * z = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    show (((z : ↥(Subgroup.centralizer ({c} : Set Y))) : Y)) *
      (((z : ↥(Subgroup.centralizer ({c} : Set Y))) : Y)) = 1
    rw [hz]; exact hz2
  have hτb : τ * τ = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    show (((τ : ↥(Subgroup.centralizer ({c} : Set Y))) : Y)) *
      (((τ : ↥(Subgroup.centralizer ({c} : Set Y))) : Y)) = 1
    rw [hτ]; exact hτ2
  have hlift := gen_lift_top (N := classicalInvolutionOddCore ↥H)
    (CFSG.ComponentClassification.OddCore.odd_card ↥H) hza hτb hgen
  let e : ↥H ≃* ↥L :=
    (Subgroup.equivMapOfInjective _ _ (Subgroup.subtype_injective _)).trans
      (MulEquiv.subgroupCongr hmap)
  have he : ∀ h : ↥H, ((e h : ↥L) : Y) = (((h : ↥(Subgroup.centralizer ({c} : Set Y)))) : Y) :=
    fun h => rfl
  let φ : ↥H →* Y := (Subgroup.centralizer ({c} : Set Y)).subtype.comp H.subtype
  have hφ : ∀ h : ↥H, φ h = (((h : ↥(Subgroup.centralizer ({c} : Set Y)))) : Y) := fun h => rfl
  have hmem : ∀ h : ↥H, φ h ∈ L := by
    intro h
    rw [← hmap]
    exact ⟨(h : ↥(Subgroup.centralizer ({c} : Set Y))), h.2, rfl⟩
  have h1 : (Subgroup.centralizer ({z} : Set ↥H)).map φ ≤ L ⊓ Subgroup.centralizer ({t} : Set Y) := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨hmem x, ?_⟩
    have hx' : x * z = z * x := Subgroup.mem_centralizer_singleton_iff.mp hx
    have := congrArg φ hx'
    rw [map_mul, map_mul, hφ z, hz] at this
    exact Subgroup.mem_centralizer_singleton_iff.mpr this
  have h2 : (Subgroup.centralizer ({τ} : Set ↥H)).map φ ≤ L ⊓ Subgroup.centralizer ({t'} : Set Y) := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨hmem x, ?_⟩
    have hx' : x * τ = τ * x := Subgroup.mem_centralizer_singleton_iff.mp hx
    have := congrArg φ hx'
    rw [map_mul, map_mul, hφ τ, hτ] at this
    exact Subgroup.mem_centralizer_singleton_iff.mpr this
  have h3 : (classicalInvolutionOddCore ↥H).map φ ≤ oddCoreOf L := by
    rintro _ ⟨m, hm, rfl⟩
    have hm' : e m ∈ classicalInvolutionOddCore ↥L := by
      rw [← classicalInvolutionOddCore_map_equiv e]
      exact ⟨m, hm, rfl⟩
    exact ⟨e m, hm', he m⟩
  intro x hx
  rw [← hmap] at hx
  obtain ⟨g', hg', rfl⟩ := hx
  have hg := hlift ⟨g', hg'⟩
  have hgφ := Subgroup.mem_map_of_mem φ hg
  rw [Subgroup.map_sup, Subgroup.map_sup] at hgφ
  exact sup_le_sup (sup_le_sup h1 h2) h3 hgφ

@[expose] def V3LayerSecGen (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y)
    (K K' K₃ : Subgroup Y) (u₁ u₂ u₃ : Y), V3Std n Y R S t K K' K₃ u₁ u₂ u₃ →
      ∀ (K₄ : Subgroup Y) (a₃ a₄ y : Y), V3Frame R t K K' K₃ u₁ u₂ K₄ a₃ a₄ y →
        SecNoExitAt (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) →
          ∃ z τ : ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)),
            ((z : ↥(Subgroup.centralizer ({u₁ * u₂} : Set Y))) : Y) = t ∧
            ((τ : ↥(Subgroup.centralizer ({u₁ * u₂} : Set Y))) : Y) = y * t * y⁻¹ ∧
            ∀ g : ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)) ⧸
                classicalInvolutionOddCore
                  ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)),
              g ∈ Subgroup.centralizer ({QuotientGroup.mk' (classicalInvolutionOddCore
                  ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂))) z} : Set _) ⊔
                Subgroup.centralizer ({QuotientGroup.mk' (classicalInvolutionOddCore
                  ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂))) τ} : Set _)

theorem v3LayerGenFr_of_secGen (h : V3LayerSecGen n) : V3LayerGenFr n := by
  intro Y _ _ R S t K K' K₃ u₁ u₂ u₃ hStd K₄ a₃ a₄ y fr hno
  obtain ⟨z, τ, hz, hτ, hgen⟩ := h Y R S t K K' K₃ u₁ u₂ u₃ hStd K₄ a₃ a₄ y fr hno
  have hd := hStd.datum
  have hΩ := hd.hyp
  have hCd := CoreData.of_S hStd.perp.core
  have hc2 : IsPGroup 2 (Subgroup.zpowers (u₁ * u₂)) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hd.sq_12
  have h2 : ∀ M ∈ CoreAssembly.conjClass (tightCore R),
      IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M) :=
    TwinADescent3.isPGroup_two_quotient_conjClass
      (TwinEdge.isPGroup_two_quotient_of_le (tightCore_le R) hCd.datum.twoGroup)
  have hmap := coreHull_map_eq_rLayer hΩ hc2 h2
  have hτ2 : (y * t * y⁻¹) * (y * t * y⁻¹) = 1 := by
    calc y * t * y⁻¹ * (y * t * y⁻¹) = y * (t * t) * y⁻¹ := by group
      _ = 1 := by rw [hd.hz.sq]; group
  exact layer_le_of_sec_gen hmap z τ hz hτ hd.hz.sq hτ2 hgen


theorem commutes_of_twins_bot' {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)} (hΦ : Q3T7M.HM Φ)
    {M₁ M₂ : Subgroup X} {z : X} (hM₁ : M₁ ∈ Φ) (hM₂ : M₂ ∈ Φ) (hne : M₁ ≠ M₂)
    (hz₁ : IsUniqueInvolution M₁ z) (hz₂ : IsUniqueInvolution M₂ z) (hO : oddCoreOf M₁ = ⊥) :
    Commutes M₁ M₂ := by
  have h := hΦ.comm_le_oddCore_of_twin hM₁ hM₂ hne hz₁ hz₂
  rw [hO, bot_inf_eq, le_bot_iff] at h
  intro x hx y hy
  have : ⁅x, y⁆ ∈ ⁅M₁, M₂⁆ := Subgroup.commutator_mem_commutator hx hy
  rw [h, Subgroup.mem_bot] at this
  exact commutatorElement_eq_one_iff_mul_comm.mp this

theorem secLayer_gen3 {X : Type} [Group X] [Finite X] {Λ : Set (Subgroup X)}
    (hΛ : Q3T7M.HM Λ) (hgen : omegaGen Λ = ⊤) (D : OmegaLieU 3 1 Λ) (hc : D.card = 1) (i : Fin D.card)
    {tag : CFSG.Assembly.LowTwoRank.StatedLieTag} {k d : ℕ} {ε : Bool}
    (hort : IsOrthTag d ε tag k) (hcis : CompIs 3 1 (D.kind i) tag k)
    (hdisc : ¬ DConnected Λ) {A A' B B' : Subgroup X} {z a b τ ε₀ : X}
    (hfr : TwinFrame Λ A A' B z a b τ ε₀) (hτz : τ ≠ z)
    (hB' : B' ∈ Λ) (hτB' : IsUniqueInvolution B' τ) (hBB' : B' ≠ B)
    (hnb : ∀ M ∈ Λ, M ∈ omegaNbr Λ A → M = A') :
    ∀ g : X, g ∈ Subgroup.centralizer ({z} : Set X) ⊔ Subgroup.centralizer ({τ} : Set X) := by
  classical
  obtain ⟨hd6, hε⟩ := TwinDimTool.dimOfTwinFrame hΛ hgen D hc i hort hcis hdisc hfr
  subst hd6 hε
  obtain ⟨htag, hk⟩ := (MuTab.isOrth_six_false tag k).mp hort
  subst htag hk
  obtain ⟨e, ⟨M⟩⟩ := TwinDimTool.exists_model hΛ hgen D hc i hcis
  have hee : e = 1 := by
    rcases M.exp_eq with h | ⟨h, -⟩
    · exact h
    · exact absurd h (by decide)
  subst hee
  have hrange : M.ψ.range = omegaGen Λ := by
    rw [hgen]; exact MonoidHom.range_eq_top.mpr M.surj
  let P : C22G.PSULayer 3 1 Λ :=
    { ψ := M.ψ
      ker_le := M.ker_le_center
      range_eq := hrange
      fund := fun L hL => by
        obtain ⟨R, hR, hLR⟩ := (M.mem_iff L).mp hL
        exact ⟨R, M.cls_sub hR, hLR⟩ }
  obtain ⟨hA, hA', hB, hne, hzA, hzA', h₁, h₂, o₁, o₂, htB, he, he2, he1, hrel⟩ := hfr
  obtain ⟨RK, hRK, hKR⟩ := P.fund A hA
  obtain ⟨RK', hRK', hKR'⟩ := P.fund A' hA'
  obtain ⟨RL, hRL, hLR⟩ := P.fund B hB
  obtain ⟨RL', hRL', hL'R⟩ := P.fund B' hB'
  have hOA : oddCoreOf A = ⊥ := Q3T8.Asc77.C22G.PSULayer.oddCoreOf_fund3 P hRK hKR
  have hOB : oddCoreOf B = ⊥ := Q3T8.Asc77.C22G.PSULayer.oddCoreOf_fund3 P hRL hLR
  have hcomm : Commutes A A' := commutes_of_twins_bot' hΛ hA hA' hne hzA hzA' hOA
  have hcomm' : Commutes B B' :=
    commutes_of_twins_bot' hΛ hB hB' (fun h => hBB' h.symm) htB hτB' hOB
  have hBA : B ≠ A := by
    intro h
    rw [h] at htB
    exact hτz (htB.eq hzA)
  have hB'A : B' ≠ A := by
    intro h
    rw [h] at hτB'
    exact hτz (hτB'.eq hzA)
  have hnc : ¬ Commutes A B := fun h => by
    have hn := MuTab.mem_omegaNbr_of_commutes hB hBA h
    have := hnb B hB hn
    rw [this] at htB
    exact hτz (htB.eq hzA')
  have hnc' : ¬ Commutes A B' := fun h => by
    have hn := MuTab.mem_omegaNbr_of_commutes hB' hB'A h
    have := hnb B' hB' hn
    rw [this] at hτB'
    exact hτz (hτB'.eq hzA')
  have hec : ∀ y ∈ omegaGen Λ, ε₀ * y = y * ε₀ := fun y _ => (Subgroup.mem_center_iff.mp he y).symm
  have hsup := Q3T8.Asc77.C22G.PSULayer.sup_eq_of_chain3 (psuLayerApi3_of_cert) P hRK hRL hRL' hKR hKR'
    hLR hL'R hzA htB hτB' h₁ h₂ o₁ hcomm hcomm' (by rw [hgen]; trivial) hec hrel hBA.symm hnc
    hB'A.symm hnc'
  intro g
  have hg : g ∈ B' ⊔ A ⊔ B := by rw [hsup, hgen]; exact Subgroup.mem_top g
  have hAz : A ≤ Subgroup.centralizer ({z} : Set X) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hzA.commute_of_mem hx).symm
  have hBτ : B ≤ Subgroup.centralizer ({τ} : Set X) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (htB.commute_of_mem hx).symm
  have hB'τ : B' ≤ Subgroup.centralizer ({τ} : Set X) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hτB'.commute_of_mem hx).symm
  exact (sup_le (sup_le (hB'τ.trans le_sup_right) (hAz.trans le_sup_left))
    (hBτ.trans le_sup_right)) hg


theorem v3_tq_members_fr {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R}
    {t : Y} {K K' K₃ : Subgroup Y} {u₁ u₂ u₃ : Y} (hStd : V3Std n Y R S t K K' K₃ u₁ u₂ u₃)
    {K₄ : Subgroup Y} {a₃ a₄ y : Y} (fr : V3Frame R t K K' K₃ u₁ u₂ K₄ a₃ a₄ y) :
    K₃ ∈ tqMembers3 (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) ∧
      K₄ ∈ tqMembers3 (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) := by
  have hd := hStd.datum
  have hΩ := hd.hyp
  have hz4 : IsUniqueInvolution K₄ t := isUniqueInvolution_of_mem_twinSet hd.hz fr.hK₄
  refine ⟨⟨hd.hK₃.1, ?_⟩, ⟨fr.hK₄.1, ?_⟩⟩
  · have t13 : u₁ ∈ trivialOnQuot K₃ :=
      A7T22.le_trivialOnQuot_of_twin hΩ hd.mem hd.hK₃.1 hd.hK₃K.symm hd.hz hd.hzK₃ hd.hu₁.1
    have t23 : u₂ ∈ trivialOnQuot K₃ :=
      A7T22.le_trivialOnQuot_of_twin hΩ hd.hK'.1 hd.hK₃.1 hd.hK₃K'.symm hd.hzK' hd.hzK₃ hd.hu₂.1
    exact (trivialOnQuot K₃).mul_mem t13 t23
  · have t14 : u₁ ∈ trivialOnQuot K₄ :=
      A7T22.le_trivialOnQuot_of_twin hΩ hd.mem fr.hK₄.1 fr.h41.symm hd.hz hz4 hd.hu₁.1
    have t24 : u₂ ∈ trivialOnQuot K₄ :=
      A7T22.le_trivialOnQuot_of_twin hΩ hd.hK'.1 fr.hK₄.1 fr.h42.symm hd.hzK' hz4 hd.hu₂.1
    exact (trivialOnQuot K₄).mul_mem t14 t24

theorem v3_secFrame {n : ℕ} (hP : TL4.TightBelowRPlus 3 n) (h4 : Thm4RTwinBelow 3 n)
    {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
    {K K' K₃ : Subgroup Y} {u₁ u₂ u₃ : Y} (hStd : V3Std n Y R S t K K' K₃ u₁ u₂ u₃)
    {K₄ : Subgroup Y} {a₃ a₄ y : Y} (fr : V3Frame R t K K' K₃ u₁ u₂ K₄ a₃ a₄ y)
    (hno : SecNoExitAt (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)) :
    ∃ (z τ : ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)))
      (A A' B B' : Subgroup (↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)) ⧸
          classicalInvolutionOddCore ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂))))
      (a b ε₀ : ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)) ⧸
          classicalInvolutionOddCore ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂))),
      ((z : ↥(Subgroup.centralizer ({u₁ * u₂} : Set Y))) : Y) = t ∧
      ((τ : ↥(Subgroup.centralizer ({u₁ * u₂} : Set Y))) : Y) = y * t * y⁻¹ ∧
      TwinFrame (liftFam (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)))
        A A' B (QuotientGroup.mk' (classicalInvolutionOddCore
          ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂))) z) a b
        (QuotientGroup.mk' (classicalInvolutionOddCore
          ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂))) τ) ε₀ ∧
      QuotientGroup.mk' (classicalInvolutionOddCore
          ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂))) τ ≠
        QuotientGroup.mk' (classicalInvolutionOddCore
          ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂))) z ∧
      B' ∈ liftFam (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)) ∧
      IsUniqueInvolution B' (QuotientGroup.mk' (classicalInvolutionOddCore
          ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂))) τ) ∧ B' ≠ B ∧
      (∀ M ∈ liftFam (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)),
        M ∈ omegaNbr (liftFam (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂))) A →
          M = A') ∧
      ¬ DConnected (liftFam (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂))) ∧
      (∀ K ∈ TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂),
        ∀ L ∈ TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂),
          ∃ x : ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)) ⧸
              classicalInvolutionOddCore
                ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)),
            conjSub x K = L) := by
  classical
  have hd := hStd.datum
  have hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R)) := hd.hyp
  have hCd := CoreData.of_S hStd.perp.core
  have hc2 : IsPGroup 2 (Subgroup.zpowers (u₁ * u₂)) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hd.sq_12
  have h2 : ∀ M ∈ CoreAssembly.conjClass (tightCore R),
      IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M) :=
    TwinADescent3.isPGroup_two_quotient_conjClass
      (TwinEdge.isPGroup_two_quotient_of_le (tightCore_le R) hCd.datum.twoGroup)
  have hz₃ : IsUniqueInvolution K₃ t := hd.hzK₃
  have hz₄ : IsUniqueInvolution K₄ t := isUniqueInvolution_of_mem_twinSet hd.hz fr.hK₄
  have hz₃y : IsUniqueInvolution (conjSub y K₃) (y * t * y⁻¹) := hz₃.conj y
  have hz₄y : IsUniqueInvolution (conjSub y K₄) (y * t * y⁻¹) := hz₄.conj y
  obtain ⟨hK₃tq, hK₄tq⟩ := v3_tq_members_fr hStd fr
  have hK₃ytq : conjSub y K₃ ∈ tqMembers3 (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) :=
    conjSub_mem_tqMembers3 hΩ.conjInvariant fr.hyc hK₃tq
  have hK₄ytq : conjSub y K₄ ∈ tqMembers3 (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) :=
    conjSub_mem_tqMembers3 hΩ.conjInvariant fr.hyc hK₄tq
  have hcu3 : Commute (u₁ * u₂) a₃ :=
    (show Commute u₁ a₃ from fr.c13).mul_left (show Commute u₂ a₃ from fr.c23)
  have hcu4 : Commute (u₁ * u₂) a₄ :=
    (show Commute u₁ a₄ from fr.c14).mul_left (show Commute u₂ a₄ from fr.c24)
  have cut : (u₁ * u₂) * t = t * (u₁ * u₂) := by
    have h1 : Commute t u₁ := hd.comm_z₁
    have h2 : Commute t u₂ := hd.comm_z₂
    exact ((h1.symm).mul_left (h2.symm)).eq
  have hτ' : y * t * y⁻¹ = a₃ * a₄ * (u₁ * u₂) := by
    rw [fr.hy]
    calc u₁ * u₂ * a₃ * a₄ = a₃ * (u₁ * u₂) * a₄ := by rw [hcu3.eq]
      _ = a₃ * ((u₁ * u₂) * a₄) := by group
      _ = a₃ * (a₄ * (u₁ * u₂)) := by rw [hcu4.eq]
      _ = a₃ * a₄ * (u₁ * u₂) := by group
  have hcτ : Commute (u₁ * u₂) (y * t * y⁻¹) := by
    rw [fr.hy]
    exact ((Commute.refl (u₁ * u₂)).mul_right hcu3).mul_right hcu4
  have htC : t ∈ Subgroup.centralizer ({u₁ * u₂} : Set Y) :=
    Subgroup.mem_centralizer_singleton_iff.mpr cut.symm
  have ha₃C : a₃ ∈ Subgroup.centralizer ({u₁ * u₂} : Set Y) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hcu3.eq.symm
  have ha₄C : a₄ ∈ Subgroup.centralizer ({u₁ * u₂} : Set Y) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hcu4.eq.symm
  have hτC : y * t * y⁻¹ ∈ Subgroup.centralizer ({u₁ * u₂} : Set Y) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hcτ.eq.symm
  have hτ2 : (y * t * y⁻¹) * (y * t * y⁻¹) = 1 := by
    calc y * t * y⁻¹ * (y * t * y⁻¹) = y * (t * t) * y⁻¹ := by group
      _ = 1 := by rw [hd.hz.sq]; group
  have hS := layer_q8Section hStd.perp hd.sq_12
  have hlt := card_layer_lt hStd.perp hd.mul_ne_one
  obtain ⟨h2X, hl, hex⟩ := lifts_of_noExit hP hlt hS hno
  have hp3 : IsPGroup 2 (Subgroup.zpowers a₃) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, fr.o3]; norm_num)
  have hp4 : IsPGroup 2 (Subgroup.zpowers a₄) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, fr.o4]; norm_num)
  have hcoreT : t ∈ TwinADescent.coreAt (u₁ * u₂) K₃ :=
    le_tightCore_of_isPGroup (V := Subgroup.zpowers t)
      (le_inf (Subgroup.zpowers_le.mpr hz₃.mem) (Subgroup.zpowers_le.mpr htC))
      (CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hd.hz.sq)
      (Subgroup.mem_zpowers t)
  have hcoreA₃ : a₃ ∈ TwinADescent.coreAt (u₁ * u₂) K₃ :=
    le_tightCore_of_isPGroup (V := Subgroup.zpowers a₃)
      (le_inf (Subgroup.zpowers_le.mpr fr.h3) (Subgroup.zpowers_le.mpr ha₃C)) hp3
      (Subgroup.mem_zpowers a₃)
  have hcoreA₄ : a₄ ∈ TwinADescent.coreAt (u₁ * u₂) K₄ :=
    le_tightCore_of_isPGroup (V := Subgroup.zpowers a₄)
      (le_inf (Subgroup.zpowers_le.mpr fr.h4) (Subgroup.zpowers_le.mpr ha₄C)) hp4
      (Subgroup.mem_zpowers a₄)
  have hcoreτ : y * t * y⁻¹ ∈ TwinADescent.coreAt (u₁ * u₂) (conjSub y K₃) :=
    le_tightCore_of_isPGroup (V := Subgroup.zpowers (y * t * y⁻¹))
      (le_inf (Subgroup.zpowers_le.mpr hz₃y.mem) (Subgroup.zpowers_le.mpr hτC))
      (CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hτ2)
      (Subgroup.mem_zpowers _)
  obtain ⟨wH, hwHv, hwHm⟩ := TwinPerp23.exists_hull_elt hK₃tq hcoreT
  obtain ⟨a₃H, ha₃Hv, ha₃Hm⟩ := TwinPerp23.exists_hull_elt hK₃tq hcoreA₃
  obtain ⟨a₄H, ha₄Hv, ha₄Hm⟩ := TwinPerp23.exists_hull_elt hK₄tq hcoreA₄
  obtain ⟨τH, hτHv, hτHm⟩ := TwinPerp23.exists_hull_elt hK₃ytq hcoreτ
  set N := classicalInvolutionOddCore
    ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)) with hN
  have hv : ∀ x y' : ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)),
      (((x * y' : ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂))) :
        ↥(Subgroup.centralizer ({u₁ * u₂} : Set Y))) : Y) =
        ((x : ↥(Subgroup.centralizer ({u₁ * u₂} : Set Y))) : Y) *
          ((y' : ↥(Subgroup.centralizer ({u₁ * u₂} : Set Y))) : Y) := fun _ _ => rfl
  have hext : ∀ x y' : ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)),
      ((x : ↥(Subgroup.centralizer ({u₁ * u₂} : Set Y))) : Y) =
        ((y' : ↥(Subgroup.centralizer ({u₁ * u₂} : Set Y))) : Y) → x = y' :=
    fun x y' h => Subtype.ext (Subtype.ext h)
  obtain ⟨eH, heH⟩ : ∃ eH : ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)),
      eH = (a₃H * a₄H)⁻¹ * τH := ⟨_, rfl⟩
  have heHv : ((eH : ↥(Subgroup.centralizer ({u₁ * u₂} : Set Y))) : Y) = u₁ * u₂ := by
    have h1 : (((a₃H * a₄H : ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂))) :
        ↥(Subgroup.centralizer ({u₁ * u₂} : Set Y))) : Y) = a₃ * a₄ := by
      rw [hv, ha₃Hv, ha₄Hv]
    have h2 : ((((a₃H * a₄H)⁻¹ : ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂))) :
        ↥(Subgroup.centralizer ({u₁ * u₂} : Set Y))) : Y) = (a₃ * a₄)⁻¹ := by
      rw [← h1]; rfl
    rw [heH]
    show ((((a₃H * a₄H)⁻¹ : ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂))) :
        ↥(Subgroup.centralizer ({u₁ * u₂} : Set Y))) : Y) *
      ((τH : ↥(Subgroup.centralizer ({u₁ * u₂} : Set Y))) : Y) = u₁ * u₂
    rw [h2, hτHv, hτ']
    group
  have hrelH : τH = a₃H * a₄H * eH := by rw [heH]; group
  have hecen : QuotientGroup.mk' N eH ∈ Subgroup.center (↥(coreHull (CoreAssembly.conjClass
      (tightCore R)) (u₁ * u₂)) ⧸ N) := by
    rw [Subgroup.mem_center_iff]
    intro x
    obtain ⟨y', rfl⟩ := QuotientGroup.mk'_surjective N x
    rw [← map_mul, ← map_mul]
    congr 1
    apply hext
    rw [hv, hv, heHv]
    exact Subgroup.mem_centralizer_singleton_iff.mp y'.1.2
  have he2' : eH * eH = 1 := by
    apply hext
    rw [hv, heHv]
    exact hd.sq_12
  have he1' : QuotientGroup.mk' N eH ≠ 1 := by
    intro h1
    have hmem : eH ∈ N := (QuotientGroup.eq_one_iff _).mp h1
    have := CFSG.ClassicalInvolution.Asc77.T7H.eq_one_of_mem_odd_of_sq
      (CFSG.ComponentClassification.OddCore.odd_card _) hmem he2'
    apply hd.mul_ne_one
    have := congrArg (fun x : ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)) =>
      ((x : ↥(Subgroup.centralizer ({u₁ * u₂} : Set Y))) : Y)) this
    simpa [heHv] using this
  obtain ⟨htC₁, htY₁, hzA⟩ := isUniqueInvolution_secImg hΩ hc2 hK₃tq hz₃
  obtain ⟨htC₂, htY₂, hzA'⟩ := isUniqueInvolution_secImg hΩ hc2 hK₄tq hz₄
  obtain ⟨hτC₃, hτY₃, hτA⟩ := isUniqueInvolution_secImg hΩ hc2 hK₃ytq hz₃y
  obtain ⟨hτC₄, hτY₄, hτA'⟩ := isUniqueInvolution_secImg hΩ hc2 hK₄ytq hz₄y
  have hwHeq : wH = ⟨⟨t, htC₁⟩, htY₁⟩ := hext _ _ hwHv
  have hτHeq : τH = ⟨⟨y * t * y⁻¹, hτC₃⟩, hτY₃⟩ := hext _ _ hτHv
  have hzA₁ : IsUniqueInvolution (secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₃)
      (QuotientGroup.mk' N wH) := by rw [hwHeq]; exact hzA
  have hzA₂ : IsUniqueInvolution (secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₄)
      (QuotientGroup.mk' N wH) := by rw [hwHeq]; exact hzA'
  have hτA₃ : IsUniqueInvolution
      (secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) (conjSub y K₃))
      (QuotientGroup.mk' N τH) := by rw [hτHeq]; exact hτA
  have hτA₄ : IsUniqueInvolution
      (secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) (conjSub y K₄))
      (QuotientGroup.mk' N τH) := by rw [hτHeq]; exact hτA'
  have hta₃ : Commute t a₃ := hz₃.commute_of_mem fr.h3
  have hta₄ : Commute t a₄ := hz₄.commute_of_mem fr.h4
  have htτ : t * (y * t * y⁻¹) = (y * t * y⁻¹) * t := by
    rw [fr.hy]
    exact ((((show Commute t (u₁ * u₂) from cut.symm).mul_right hta₃).mul_right hta₄)).eq
  have hτne : QuotientGroup.mk' N τH ≠ QuotientGroup.mk' N wH := by
    intro h
    have := TwinPerp23.eq_of_mk_eq_of_involutions (x := τH) (y := wH)
      (hext _ _ (by rw [hv, hτHv]; exact hτ2)) (hext _ _ (by rw [hv, hwHv]; exact hz₃.sq))
      (hext _ _ (by rw [hv, hv, hτHv, hwHv]; exact htτ.symm)) h
    have hval := congrArg
      (fun x : ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)) =>
        ((x : ↥(Subgroup.centralizer ({u₁ * u₂} : Set Y))) : Y)) this
    simp only [hτHv, hwHv] at hval
    exact fr.hne hval
  have hperp3 := kPerp_datum hStd.perp hd.hK₃.1 hd.hzK₃
  have hK₄ := fr.hK₄
  have h41 := fr.h41
  have h42 := fr.h42
  have h43 := fr.h43
  have hp3' := v3_perp_tq hStd hd.hK₃ hK₄ (Ne.symm h43) hd.hK₃K hd.hK₃K' h41 h42
  have hp4' := v3_perp_tq hStd hK₄ hd.hK₃ h43 h41 h42 hd.hK₃K hd.hK₃K'
  have hnb : ∀ M ∈ TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂),
      M ∈ omegaNbr (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂))
        (secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₃) →
      M = secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₄ := by
    intro M hM hn
    obtain ⟨J, hJq, rfl⟩ := exists_of_mem_secFam hM
    exact TwinLayerGen.secNbr_eq_of_perp hΩ hc2 hK₃tq hJq (K' := K₄)
      (fun J₀ hJ₀ hJ₀p => hp3' J₀ hJ₀ (by rw [hperp3] at *; exact hJ₀p)) hn
  have hnb' : ∀ M ∈ TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂),
      M ∈ omegaNbr (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂))
        (secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₄) →
      M = secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₃ := by
    intro M hM hn
    obtain ⟨J, hJq, rfl⟩ := exists_of_mem_secFam hM
    exact TwinLayerGen.secNbr_eq_of_perp hΩ hc2 hK₄tq hJq (K' := K₃)
      (fun J₀ hJ₀ hJ₀p => hp4' J₀ hJ₀ hJ₀p) hn
  have hBA : secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) (conjSub y K₃) ≠
      secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₃ := by
    intro h
    rw [h] at hτA₃
    exact hτne (hτA₃.eq hzA₁)
  have hBA' : secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) (conjSub y K₃) ≠
      secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₄ := by
    intro h
    rw [h] at hτA₃
    exact hτne (hτA₃.eq hzA₂)
  have hne_img : secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₃ ≠
      secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₄ :=
    TwinPerp23.secImg_ne_of_twins hΩ hc2 hK₃tq hK₄tq h43 hz₃ hz₄
  have hne_img' : secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) (conjSub y K₃) ≠
      secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) (conjSub y K₄) :=
    TwinPerp23.secImg_ne_of_twins hΩ hc2 hK₃ytq hK₄ytq (fun h => h43 (by
      have := congrArg (conjSub y⁻¹) h
      rwa [conjSub_inv_conjSub, conjSub_inv_conjSub] at this)) hz₃y hz₄y
  obtain ⟨LA, uA, hLA⟩ := hl _ (secImg_mem_secFam hK₃tq)
  obtain ⟨LA', uA', hLA'⟩ := hl _ (secImg_mem_secFam hK₄tq)
  obtain ⟨LB, uB, hLB⟩ := hl _ (secImg_mem_secFam hK₃ytq)
  obtain ⟨LB', uB', hLB'⟩ := hl _ (secImg_mem_secFam hK₄ytq)
  have hMA := satU_mem_liftFam (secImg_mem_secFam hK₃tq) hLA
  have hMA' := satU_mem_liftFam (secImg_mem_secFam hK₄tq) hLA'
  have hMB := satU_mem_liftFam (secImg_mem_secFam hK₃ytq) hLB
  have hMB' := satU_mem_liftFam (secImg_mem_secFam hK₄ytq) hLB'
  have hnbΛ : ∀ M ∈ liftFam (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)),
      M ∈ omegaNbr (liftFam (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)))
        (satU (.sl2 3 1) LA uA) → M = satU (.sl2 3 1) LA' uA' := by
    intro M hMΛ hnbr
    obtain ⟨J, hJΦ, hJN⟩ := exists_core_of_mem_liftFam hMΛ
    have hJ := (hex.mem_omegaNbr_liftFam_iff hS.hyp h2X hl hMA (secImg_mem_secFam hK₃tq)
      hLA.le_sat hMΛ hJΦ hJN).mp hnbr
    have hJeq := hnb J hJΦ hJ
    subst hJeq
    exact liftFam_eq_of_le hS.hyp hMΛ hMA' (secImg_mem_secFam hK₄tq) hJN hLA'.le_sat
  have hBB' : satU (.sl2 3 1) LB' uB' ≠ satU (.sl2 3 1) LB uB := by
    intro h
    exact hne_img' (hex.core_unique hS.hyp h2X hMB (secImg_mem_secFam hK₃ytq)
      (secImg_mem_secFam hK₄ytq) hLB.le_sat (by rw [← h]; exact hLB'.le_sat))
  have htr := TwinLayerGen.transitive_of_twin_nbr h4 hlt hS hno (secImg_mem_secFam hK₃tq)
    (secImg_mem_secFam hK₄tq) hzA₁ hzA₂ hnb hnb'
  have sq₃ : a₃ * a₃ = t := T7A.sq_eq_of_orderOf_four hd.hzK₃ fr.h3 fr.o3
  have sq₄ : a₄ * a₄ = t := T7A.sq_eq_of_orderOf_four hz₄ fr.h4 fr.o4
  refine ⟨wH, τH, satU (.sl2 3 1) LA uA, satU (.sl2 3 1) LA' uA', satU (.sl2 3 1) LB uB,
    satU (.sl2 3 1) LB' uB', QuotientGroup.mk' N a₃H, QuotientGroup.mk' N a₄H,
    QuotientGroup.mk' N eH, hwHv, hτHv, ⟨hMA, hMA', hMB, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hecen,
      ?_, he1', ?_⟩, hτne, hMB', isUniqueInvolution_liftFam_of_le hMB' hτA₄ hLB'.le_sat, hBB',
    hnbΛ, TwinDimTool.not_dConnected_liftFam hS.hyp h2X hl hex (secImg_mem_secFam hK₃tq)
      (secImg_mem_secFam hK₄tq) (secImg_mem_secFam hK₃ytq) hnb hnb' hBA hBA', htr⟩
  · intro h
    exact hne_img (hex.core_unique hS.hyp h2X hMA (secImg_mem_secFam hK₃tq)
      (secImg_mem_secFam hK₄tq) hLA.le_sat (by rw [h]; exact hLA'.le_sat))
  · exact isUniqueInvolution_liftFam_of_le hMA hzA₁ hLA.le_sat
  · exact isUniqueInvolution_liftFam_of_le hMA' hzA₂ hLA'.le_sat
  · exact hLA.le_sat ha₃Hm
  · exact hLA'.le_sat ha₄Hm
  · rw [← map_mul]
    congr 1
    apply hext
    rw [hv, ha₃Hv, hwHv]
    exact sq₃
  · rw [← map_mul]
    congr 1
    apply hext
    rw [hv, ha₄Hv, hwHv]
    exact sq₄
  · exact isUniqueInvolution_liftFam_of_le hMB hτA₃ hLB.le_sat
  · rw [← map_mul, he2', map_one]
  · rw [← map_mul, ← map_mul, ← hrelH]

theorem v3_layer_sec_gen {n : ℕ} (hcit : CIT3Below n) (hP : TL4.TightBelowRPlus 3 n)
    (h4 : Thm4RTwinBelow 3 n)
    {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
    {K K' K₃ : Subgroup Y} {u₁ u₂ u₃ : Y} (hStd : V3Std n Y R S t K K' K₃ u₁ u₂ u₃)
    {K₄ : Subgroup Y} {a₃ a₄ y : Y} (fr : V3Frame R t K K' K₃ u₁ u₂ K₄ a₃ a₄ y)
    (hno : SecNoExitAt (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)) :
    ∃ z τ : ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)),
      ((z : ↥(Subgroup.centralizer ({u₁ * u₂} : Set Y))) : Y) = t ∧
      ((τ : ↥(Subgroup.centralizer ({u₁ * u₂} : Set Y))) : Y) = y * t * y⁻¹ ∧
      ∀ g : ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)) ⧸
          classicalInvolutionOddCore
            ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)),
        g ∈ Subgroup.centralizer ({QuotientGroup.mk' (classicalInvolutionOddCore
            ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂))) z} : Set _) ⊔
          Subgroup.centralizer ({QuotientGroup.mk' (classicalInvolutionOddCore
            ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂))) τ} : Set _) := by
  classical
  obtain ⟨z, τ, A, A', B, B', a, b, ε₀, hz, hτ, hfr, hτz, hB', hτB', hBB', hnb, hdisc, htr⟩ :=
    v3_secFrame hP h4 hStd fr hno
  refine ⟨z, τ, hz, hτ, ?_⟩
  have hd := hStd.datum
  have hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R)) := hd.hyp
  have hc2 : IsPGroup 2 (Subgroup.zpowers (u₁ * u₂)) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hd.sq_12
  have hz₄ : IsUniqueInvolution K₄ t := isUniqueInvolution_of_mem_twinSet hd.hz fr.hK₄
  obtain ⟨hK₃tq, hK₄tq⟩ := v3_tq_members_fr hStd fr
  have hS := layer_q8Section hStd.perp hd.sq_12
  have hlt := card_layer_lt hStd.perp hd.mul_ne_one
  have hne : (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)).Nonempty :=
    ⟨_, secImg_mem_secFam hK₃tq⟩
  obtain ⟨h2', hl', hex', ⟨D⟩⟩ := lieDecomp_of_noExit hcit hP hlt hS hne hno
  have hΛ : HypOmegaModU (.sl2 3 1)
      (liftFam (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂))) :=
    hypOmegaModU_liftFam hS.hyp.conjInvariant
  have hgen : omegaGen
      (liftFam (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂))) = ⊤ := by
    refine eq_top_iff.mpr ?_
    rw [← hS.gen]
    refine iSup₂_le fun J hJ => ?_
    obtain ⟨L, u', hL⟩ := hl' J hJ
    exact hL.le_sat.trans (le_omegaGen (satU_mem_liftFam hJ hL))
  have hcard := TwinPerp23.secDecomp_card_one hcit hP hStd.perp hd.sq_12 hd.mul_ne_one hne hno htr D
  obtain ⟨T₃, hT₃, hT₃c⟩ := TwinADescent.exists_sylow_centralizer_of_tq hc2 hK₃tq.2
  obtain ⟨T₄, hT₄, hT₄c⟩ := TwinADescent.exists_sylow_centralizer_of_tq hc2 hK₄tq.2
  obtain ⟨tag, k, d, ε, -, hort, hcis⟩ := TwinPerp23.layer_orthTag hP hStd.perp hd.sq_12
    hd.mul_ne_one hno hne htr hd.hK₃.1 fr.hK₄.1 fr.h43 hd.hzK₃ hz₄ hT₃ hT₄ hT₃c hT₄c
    (TwinPerp23.involution_mem_sylow hΩ hd.hK₃.1 hd.hzK₃ hT₃)
    (TwinPerp23.involution_mem_sylow hΩ fr.hK₄.1 hz₄ hT₄) D hcard
  exact secLayer_gen3 hΛ hgen D hcard ⟨0, by omega⟩ hort hcis hdisc hfr hτz hB' hτB' hBB' hnb

theorem v3LayerSecGen_proved {n : ℕ} (hcit : CIT3Below n) (hP : TL4.TightBelowRPlus 3 n)
    (h4 : Thm4RTwinBelow 3 n) : V3LayerSecGen n := by
  intro Y _ _ R S t K K' K₃ u₁ u₂ u₃ hStd K₄ a₃ a₄ y fr hno
  exact v3_layer_sec_gen hcit hP h4 hStd fr hno

theorem v3LayerGenFr_proved {n : ℕ} (hcit : CIT3Below n) (hP : TL4.TightBelowRPlus 3 n)
    (h4 : Thm4RTwinBelow 3 n) : V3LayerGenFr n :=
  v3LayerGenFr_of_secGen (v3LayerSecGen_proved hcit hP h4)

end LeafB

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
