module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.BlockExclusion
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.FStarSubnormal
import CFSG.Quasithin.Background.E1Amb
import CFSG.Adapters.GeneralizedFittingTop

public section

namespace CFSG.AGLEmbeddingD2.Tits.GN516

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbeddingD2.GN
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

section Components

variable {Y : Type*} [Group Y]

private theorem le_normalizer_of_conj_mem' {S M : Subgroup Y}
    (h : ∀ g ∈ S, ∀ x ∈ M, g * x * g⁻¹ ∈ M) : S ≤ Subgroup.normalizer (M : Set Y) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨h g hg y, fun hy => ?_⟩
  have := h g⁻¹ (S.inv_mem hg) _ hy
  simpa [mul_assoc] using this

private theorem isComponentOf_conjSub {L : Subgroup Y} (hL : Open.IsComponentOf L ⊤) (t : Y) :
    Open.IsComponentOf (B6.conjSub t L) ⊤ :=
  (CFSG.Adapters.isComponentOf_top_iff _).2
    (CFSG.GorensteinWalter.fstar_isComponentOf_conjugateSubgroup_of_mem
      ((CFSG.Adapters.isComponentOf_top_iff L).1 hL) t (Subgroup.mem_top t))

variable [Finite Y]

private theorem conjSub_le_centralizer_of_notMem_normalizer {L : Subgroup Y}
    (hL : Open.IsComponentOf L ⊤) {t : Y} (ht : t ∉ Subgroup.normalizer (L : Set Y)) :
    B6.conjSub t L ≤ Subgroup.centralizer (L : Set Y) := by
  have hne : B6.conjSub t L ≠ L := fun h =>
    ht (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h)
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    (CFSG.GorensteinWalter.component_commute_of_ne
      ((CFSG.Adapters.isComponentOf_top_iff _).1 (isComponentOf_conjSub hL t))
      ((CFSG.Adapters.isComponentOf_top_iff L).1 hL) hne)

private theorem commute_of_conjSub_ne {L : Subgroup Y} (hL : Open.IsComponentOf L ⊤) {s t : Y}
    (h : B6.conjSub s L ≠ B6.conjSub t L) {x y : Y} (hx : x ∈ B6.conjSub s L)
    (hy : y ∈ B6.conjSub t L) : x * y = y * x :=
  (Subgroup.mem_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    (CFSG.GorensteinWalter.component_commute_of_ne
      ((CFSG.Adapters.isComponentOf_top_iff _).1 (isComponentOf_conjSub hL s))
      ((CFSG.Adapters.isComponentOf_top_iff _).1 (isComponentOf_conjSub hL t)) h) hx) y hy).symm

private theorem conjSub_le_normalizer_conjClosure {L W S : Subgroup Y}
    (hL : Open.IsComponentOf L ⊤) (hWL : W ≤ L) (hLW : L ≤ Subgroup.normalizer (W : Set Y))
    (g : Y) : B6.conjSub g L ≤ Subgroup.normalizer (conjClosure W S : Set Y) := by
  refine le_normalizer_of_conj_mem' fun x hx y hy => ?_
  have key : conjClosure W S ≤ (conjClosure W S).comap (MulAut.conj x).toMonoidHom := by
    refine conjClosure_le fun s hs w hw => ?_
    rw [Subgroup.mem_comap]
    show x * (s * w * s⁻¹) * x⁻¹ ∈ conjClosure W S
    by_cases h : B6.conjSub g L = B6.conjSub s L
    · have hx' : s⁻¹ * x * s ∈ L := B6.mem_conjSub.1 (h ▸ hx)
      have e : x * (s * w * s⁻¹) * x⁻¹ =
          s * ((s⁻¹ * x * s) * w * (s⁻¹ * x * s)⁻¹) * s⁻¹ := by group
      rw [e]
      exact mem_conjClosure hs ((Subgroup.mem_normalizer_iff.mp (hLW hx') w).mp hw)
    · have hws : s * w * s⁻¹ ∈ B6.conjSub s L := by
        rw [B6.mem_conjSub]
        simpa [mul_assoc] using hWL hw
      have e : x * (s * w * s⁻¹) * x⁻¹ = s * w * s⁻¹ := by
        rw [commute_of_conjSub_ne hL h hx hws, mul_inv_cancel_right]
      rw [e]
      exact mem_conjClosure hs hw
  exact Subgroup.mem_comap.1 (key hy)

theorem isSubnormal_conjClosure_of_component {L W S : Subgroup Y} (hL : Open.IsComponentOf L ⊤)
    (hWL : W ≤ L) (hLW : L ≤ Subgroup.normalizer (W : Set Y)) :
    IsSubnormal (conjClosure W S) ⊤ := by
  have hDN : conjClosure W S ≤ Subgroup.normalClosure (L : Set Y) :=
    conjClosure_le fun s _ w hw =>
      Subgroup.normalClosure_normal.conj_mem w (Subgroup.subset_normalClosure (hWL hw)) s
  have hND : Subgroup.normalClosure (L : Set Y) ≤
      Subgroup.normalizer (conjClosure W S : Set Y) := by
    refine (Subgroup.closure_le _).2 fun x hx => ?_
    obtain ⟨a, ha, hax⟩ := Group.mem_conjugatesOfSet_iff.1 hx
    obtain ⟨c, rfl⟩ := isConj_iff.1 hax
    exact conjSub_le_normalizer_conjClosure hL hWL hLW c
      (B6.mem_conjSub.2 (by simpa [mul_assoc] using ha))
  exact IsSubnormal.step hDN ((Subgroup.normal_subgroupOf_iff_le_normalizer hDN).2 hND)
    (IsSubnormal.step le_top Subgroup.normal_subgroupOf (IsSubnormal.refl _))

theorem conjClosure_le_normalizer_of_component {L W S N : Subgroup Y}
    (hL : Open.IsComponentOf L ⊤) (hWL : W ≤ L)
    (hRW : S ⊓ Subgroup.normalizer (L : Set Y) ≤ Subgroup.normalizer (W : Set Y))
    (hNL : N ≤ L) (hWN : W ≤ Subgroup.normalizer (N : Set Y)) :
    conjClosure W S ≤ Subgroup.normalizer (N : Set Y) := by
  refine conjClosure_le fun t ht w hw => ?_
  by_cases htL : t ∈ Subgroup.normalizer (L : Set Y)
  · exact hWN ((Subgroup.mem_normalizer_iff.mp (hRW ⟨ht, htL⟩) w).mp hw)
  · have hmem : t * w * t⁻¹ ∈ B6.conjSub t L := by
      rw [B6.mem_conjSub]
      simpa [mul_assoc] using hWL hw
    exact Subgroup.centralizer_le_normalizer _ (Subgroup.centralizer_le hNL
      (conjSub_le_centralizer_of_notMem_normalizer hL htL hmem))

end Components

section Subnormal

variable {G : Type*} [Group G]

private theorem isSubnormal_map {G' : Type*} [Group G'] (f : G →* G') {A B : Subgroup G}
    (h : IsSubnormal A B) : IsSubnormal (A.map f) (B.map f) :=
  h.map f

private theorem isSubnormal_inf {A B C : Subgroup G} (h : IsSubnormal A B) (hCB : C ≤ B) :
    IsSubnormal (A ⊓ C) C :=
  h.inf_of_le hCB

private theorem isSubnormal_of_le_of_le {A B C : Subgroup G} (h : IsSubnormal A B) (hAC : A ≤ C)
    (hCB : C ≤ B) : IsSubnormal A C := by
  simpa [inf_eq_left.2 hAC] using isSubnormal_inf h hCB

private theorem isSubnormal_trans_of {A B C : Subgroup G} (h : IsSubnormal A B)
    (h' : IsSubnormal B C) : IsSubnormal A C :=
  h.trans h'

private theorem isSubnormal_of_mathlib {H K : Subgroup G} (hKH : K ≤ H)
    (h : (K.subgroupOf H).IsSubnormal) : IsSubnormal K H :=
  (CFSG.Open.IsSubnormal.iff_subgroupOf hKH).2 h

end Subnormal

section BlockCase

variable {X : Type} [Group X] [Finite X] {T : Subgroup X}

theorem twoResidual_eq_bot_of_blocks_subnormal (hX : GNSetting X T) {W R : Subgroup (X ⧸ gnC T)}
    (hWsub : IsSubnormal W ⊤) (hR2 : IsPGroup 2 R)
    (hRW : R ≤ Subgroup.normalizer (W : Set (X ⧸ gnC T)))
    {H₁ : Subgroup X} (hQH : pCoreOf 2 (⊤ : Subgroup X) ≤ H₁) (hmap : gnImg T H₁ = W ⊔ R)
    {r : ℕ} {K : Fin r → Subgroup X} (hK : ∀ i, IsChiBlockGN H₁ (K i))
    (hres : twoResidual H₁ = ⨆ i, K i) : twoResidual W = ⊥ := by
  have hYW : twoResidual (W ⊔ R) ≤ W := twoResidual_sup_le_of_pGroup hR2 hRW
  have hYimg : gnImg T (twoResidual H₁) = twoResidual (W ⊔ R) := by
    rw [gnImg, E1.map_twoResidual]
    exact congrArg twoResidual hmap
  have hKsub : ∀ i, IsSubnormal (gnImg T (K i)) ⊤ := by
    intro i
    have hKH : K i ≤ H₁ := (hK i).1.2.1
    have hKW : gnImg T (K i) ≤ W :=
      calc gnImg T (K i) ≤ gnImg T (twoResidual H₁) :=
            Subgroup.map_mono ((le_iSup K i).trans hres.ge)
        _ = twoResidual (W ⊔ R) := hYimg
        _ ≤ W := hYW
    have h1 : IsSubnormal (gnImg T (K i)) (gnImg T H₁) :=
      isSubnormal_map _ (isSubnormal_of_mathlib hKH (hK i).1.2.2)
    rw [hmap] at h1
    exact isSubnormal_trans_of (isSubnormal_of_le_of_le h1 hKW le_sup_left) hWsub
  have hbot : twoResidual (W ⊔ R) = ⊥ := by
    have := twoResidual_gnImg_eq_bot_q hX hQH hK hres hKsub
    rwa [hmap] at this
  exact le_bot_iff.1 ((E1.twoResidual_mono le_sup_left).trans hbot.le)

theorem not_le_normalizer_of_twoResidual_eq_bot {L W : Subgroup (X ⧸ gnC T)}
    (hS : IsSylowTwoOf (gnImg T T ⊓ L) W) (hW0 : twoResidual W = ⊥)
    (hnn : ¬ L ≤ Subgroup.normalizer ((gnImg T T ⊓ L : Subgroup (X ⧸ gnC T)) : Set _)) :
    ¬ L ≤ Subgroup.normalizer (W : Set (X ⧸ gnC T)) := by
  intro hLW
  have hW2 : IsPGroup 2 W := by
    intro g
    obtain ⟨k, hk⟩ := twoResidual_isTwoQuotient W (g : X ⧸ gnC T) g.2
    rw [hW0, Subgroup.mem_bot] at hk
    exact ⟨k, Subtype.ext hk⟩
  have hWS : W ≤ gnImg T T ⊓ L := by
    obtain ⟨n, hn⟩ := B6.exists_relIndex_eq_two_pow_of_isPGroup hW2 (gnImg T T ⊓ L)
    have hn0 : n = 0 := by
      by_contra hne
      have h2 : 2 ∣ (gnImg T T ⊓ L).relIndex W := hn ▸ dvd_pow_self 2 hne
      exact hS.2.2 h2
    rw [hn0, pow_zero] at hn
    exact Subgroup.relIndex_eq_one.1 hn
  apply hnn
  rw [← le_antisymm hWS hS.1]
  exact hLW

theorem false_of_blocks_of_normal_S (hX : GNSetting X T) {L W S' : Subgroup (X ⧸ gnC T)}
    (hL : Open.IsComponentOf L ⊤) (hWL : W ≤ L)
    (hLW : L ≤ Subgroup.normalizer (W : Set (X ⧸ gnC T)))
    (hS : IsSylowTwoOf (gnImg T T ⊓ L) W)
    (hnn : ¬ L ≤ Subgroup.normalizer ((gnImg T T ⊓ L : Subgroup (X ⧸ gnC T)) : Set _))
    (hS2 : IsPGroup 2 S') {H₁ : Subgroup X} (hQH : pCoreOf 2 (⊤ : Subgroup X) ≤ H₁)
    (hmap : gnImg T H₁ = conjClosure W S' ⊔ S')
    {r : ℕ} {K : Fin r → Subgroup X} (hK : ∀ i, IsChiBlockGN H₁ (K i))
    (hres : twoResidual H₁ = ⨆ i, K i) : False := by
  have h0 := twoResidual_eq_bot_of_blocks_subnormal hX
    (isSubnormal_conjClosure_of_component hL hWL hLW) hS2
    (le_normalizer_conjClosure W S') hQH hmap hK hres
  have hW0 : twoResidual W = ⊥ :=
    le_bot_iff.1 ((E1.twoResidual_mono (le_conjClosure W S')).trans h0.le)
  exact not_le_normalizer_of_twoResidual_eq_bot hS hW0 hnn hLW

theorem false_of_blocks_of_ne_S (hX : GNSetting X T) {L W S' : Subgroup (X ⧸ gnC T)}
    (hL : Open.IsComponentOf L ⊤) (hWL : W ≤ L)
    (hRW : S' ⊓ Subgroup.normalizer (L : Set (X ⧸ gnC T)) ≤
      Subgroup.normalizer (W : Set (X ⧸ gnC T)))
    (hS2 : IsPGroup 2 S')
    (hbad : ⁅pCoreOf 2 (twoResidual W), twoResidual W⁆ ≠ ⊥)
    {H₁ : Subgroup X} (hQH : pCoreOf 2 (⊤ : Subgroup X) ≤ H₁)
    (hmap : gnImg T H₁ = conjClosure W S' ⊔ S')
    {r : ℕ} {K : Fin r → Subgroup X} (hK : ∀ i, IsChiBlockGN H₁ (K i))
    (hKK : ∀ i j, i ≠ j → ⁅K i, K j⁆ = ⊥) (hres : twoResidual H₁ = ⨆ i, K i) : False := by
  set N₀ : Subgroup (X ⧸ gnC T) := pCoreOf 2 (twoResidual W) with hN₀
  have hYD : twoResidual (conjClosure W S' ⊔ S') ≤ conjClosure W S' :=
    twoResidual_sup_le_of_pGroup hS2 (le_normalizer_conjClosure W S')
  have hYimg : gnImg T (twoResidual H₁) = twoResidual (conjClosure W S' ⊔ S') := by
    rw [gnImg, E1.map_twoResidual]
    exact congrArg twoResidual hmap
  have hWD : W ≤ conjClosure W S' ⊔ S' := (le_conjClosure W S').trans le_sup_left
  have hWY : twoResidual W ≤ gnImg T (twoResidual H₁) := by
    rw [hYimg]
    exact E1.twoResidual_mono hWD
  have hN₀W : N₀ ≤ twoResidual W := CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hN₀L : N₀ ≤ L := hN₀W.trans ((twoResidual_le W).trans hWL)
  have hWN : W ≤ Subgroup.normalizer (N₀ : Set (X ⧸ gnC T)) :=
    (le_normalizer_twoResidual W).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)
  have hDN : conjClosure W S' ≤ Subgroup.normalizer (N₀ : Set (X ⧸ gnC T)) :=
    conjClosure_le_normalizer_of_component hL hWL hRW hN₀L hWN
  have hYN : gnImg T (twoResidual H₁) ≤ Subgroup.normalizer (N₀ : Set (X ⧸ gnC T)) := by
    rw [hYimg]
    exact hYD.trans hDN
  have hcomm := commutator_eq_bot_of_pGroup_q hX hQH hK hKK hres (N := N₀) (hN₀W.trans hWY)
    hYN (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
  exact hbad (le_bot_iff.1 ((Subgroup.commutator_mono le_rfl hWY).trans hcomm.le))

end BlockCase

end CFSG.AGLEmbeddingD2.Tits.GN516
