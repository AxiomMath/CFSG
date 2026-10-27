module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.BlockLiftQ
import CFSG.Quasithin.Background.E1Amb
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.AGLEmbeddingD2.Tits.GN516

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbeddingD2.GN
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

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

section Residual

theorem twoResidual_sup_le_of_pGroup {Y : Type*} [Group Y] [Finite Y] {W R : Subgroup Y}
    (hR : IsPGroup 2 R) (hRW : R ≤ Subgroup.normalizer (W : Set Y)) :
    twoResidual (W ⊔ R) ≤ W := by
  have hn : W ⊔ R ≤ Subgroup.normalizer (W : Set Y) := sup_le Subgroup.le_normalizer hRW
  exact twoResidual_le_of_isTwoQuotient le_sup_left hn
    (B6.isTwoQuotient_of_sup_eq hR hn (sup_comm R W))

variable {X : Type} [Group X] [Finite X] {T : Subgroup X}

theorem twoResidual_gnImg_eq_bot_q (hX : GNSetting X T) {H : Subgroup X}
    (hQH : pCoreOf 2 (⊤ : Subgroup X) ≤ H) {r : ℕ} {K : Fin r → Subgroup X}
    (hK : ∀ i, IsChiBlockGN H (K i)) (hres : twoResidual H = ⨆ i, K i)
    (hsub : ∀ i, IsSubnormal (gnImg T (K i)) ⊤) : twoResidual (gnImg T H) = ⊥ := by
  have hle : ∀ i, K i ≤ gnC T := fun i => by
    by_contra hKC
    exact false_of_block_subnormal_q hX hQH (hK i) hKC (hsub i)
  rw [gnImg, ← E1.map_twoResidual, hres, Subgroup.map_iSup]
  refine iSup_eq_bot.2 fun i => ?_
  rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  exact hle i

end Residual

section BlockCase

variable {X : Type} [Group X] [Finite X] {T : Subgroup X}

theorem false_of_blocks_of_normal_q (hX : GNSetting X T) {L W R : Subgroup (X ⧸ gnC T)}
    (hL : IsComponentOf L ⊤) (hWL : W ≤ L)
    (hLW : L ≤ Subgroup.normalizer (W : Set (X ⧸ gnC T)))
    (hS : IsSylowTwoOf (gnImg T T ⊓ L) W)
    (hnn : ¬ L ≤ Subgroup.normalizer ((gnImg T T ⊓ L : Subgroup (X ⧸ gnC T)) : Set _))
    (hR2 : IsPGroup 2 R) (hRW : R ≤ Subgroup.normalizer (W : Set (X ⧸ gnC T)))
    {H₁ : Subgroup X} (hQH : pCoreOf 2 (⊤ : Subgroup X) ≤ H₁) (hmap : gnImg T H₁ = W ⊔ R)
    {r : ℕ} {K : Fin r → Subgroup X} (hK : ∀ i, IsChiBlockGN H₁ (K i))
    (hres : twoResidual H₁ = ⨆ i, K i) : False := by
  set T' : Subgroup (X ⧸ gnC T) := gnImg T T with hT'
  have hYW : twoResidual (W ⊔ R) ≤ W := twoResidual_sup_le_of_pGroup hR2 hRW
  have hWsub : IsSubnormal W ⊤ :=
    IsSubnormal.step hWL ((Subgroup.normal_subgroupOf_iff_le_normalizer hWL).2 hLW) hL.2.1
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
  have hW0 : twoResidual W = ⊥ :=
    le_bot_iff.1 ((E1.twoResidual_mono le_sup_left).trans hbot.le)
  have hW2 : IsPGroup 2 W := by
    intro g
    obtain ⟨k, hk⟩ := twoResidual_isTwoQuotient W (g : X ⧸ gnC T) g.2
    rw [hW0, Subgroup.mem_bot] at hk
    exact ⟨k, Subtype.ext hk⟩
  have hWS : W ≤ T' ⊓ L := by
    obtain ⟨n, hn⟩ := B6.exists_relIndex_eq_two_pow_of_isPGroup hW2 (T' ⊓ L)
    have hn0 : n = 0 := by
      by_contra hne
      have h2 : 2 ∣ (T' ⊓ L).relIndex W := hn ▸ dvd_pow_self 2 hne
      exact hS.2.2 h2
    rw [hn0, pow_zero] at hn
    exact Subgroup.relIndex_eq_one.1 hn
  apply hnn
  rw [← le_antisymm hWS hS.1]
  exact hLW

theorem false_of_blocks_of_ne_q (hX : GNSetting X T) {W R : Subgroup (X ⧸ gnC T)}
    (hR2 : IsPGroup 2 R) (hRW : R ≤ Subgroup.normalizer (W : Set (X ⧸ gnC T)))
    (hbad : ⁅pCoreOf 2 (twoResidual W), twoResidual W⁆ ≠ ⊥)
    {H₁ : Subgroup X} (hQH : pCoreOf 2 (⊤ : Subgroup X) ≤ H₁) (hmap : gnImg T H₁ = W ⊔ R)
    {r : ℕ} {K : Fin r → Subgroup X} (hK : ∀ i, IsChiBlockGN H₁ (K i))
    (hKK : ∀ i j, i ≠ j → ⁅K i, K j⁆ = ⊥) (hres : twoResidual H₁ = ⨆ i, K i) : False := by
  set N₀ : Subgroup (X ⧸ gnC T) := pCoreOf 2 (twoResidual W) with hN₀
  have hYW : twoResidual (W ⊔ R) ≤ W := twoResidual_sup_le_of_pGroup hR2 hRW
  have hYimg : gnImg T (twoResidual H₁) = twoResidual (W ⊔ R) := by
    rw [gnImg, E1.map_twoResidual]
    exact congrArg twoResidual hmap
  have hWY : twoResidual W ≤ gnImg T (twoResidual H₁) := by
    rw [hYimg]
    exact E1.twoResidual_mono le_sup_left
  have hN₀W : N₀ ≤ twoResidual W := CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hWN : W ≤ Subgroup.normalizer (N₀ : Set (X ⧸ gnC T)) :=
    (le_normalizer_twoResidual W).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)
  have hYN : gnImg T (twoResidual H₁) ≤ Subgroup.normalizer (N₀ : Set (X ⧸ gnC T)) := by
    rw [hYimg]
    exact hYW.trans hWN
  have hcomm := commutator_eq_bot_of_pGroup_q hX hQH hK hKK hres (N := N₀) (hN₀W.trans hWY)
    hYN (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
  exact hbad (le_bot_iff.1 ((Subgroup.commutator_mono le_rfl hWY).trans hcomm.le))

end BlockCase

end CFSG.AGLEmbeddingD2.Tits.GN516
