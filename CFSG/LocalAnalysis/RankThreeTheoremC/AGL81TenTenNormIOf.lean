module

import CFSG.LocalAnalysis.RankThreeTheoremC.ZLayer3Comp
import CFSG.Quasithin.Background.C41PfE
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneThreeWCGammaTools
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81CfgData
import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.RankThreeCoreUniqueness.Helpers
open Subgroup

variable (G : Type) [Group G] [Finite G]

@[expose] def AGL81TenEightCfg : Prop :=
  Setting G → ∀ (p : ℕ) (P : Sylow p G) (M H Q : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)),
    AGL81CfgData p P M H Q K → ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
    ∀ m ∈ M, ∀ Q₀ : Subgroup G, IsAGLQ p M Q₀ → ∀ N : Subgroup G, GLBIsMaxTwoLocal N →
        L.map (MulAut.conj m).toMonoidHom ≤ N → Q₀ ≤ N → N = M

@[expose] def AGL81TenTenClaimCfg : Prop :=
  Setting G → ∀ (p : ℕ) (P : Sylow p G) (M H Q : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)),
    AGL81CfgData p P M H Q K → ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
    ¬ (L.subgroupOf M).Normal → ∀ I₀ ∈ cZero (H ⊓ L),
      ∃ Q₀ : Subgroup G, IsAGLQ p M Q₀ ∧
        Q₀ ≤ normalizer (CFSG.ComponentClassification.AS76b.oUpperTwo I₀ : Set G)

variable {G}

namespace TenTenNormI

theorem le_normalizer_of_chain {K Q : Subgroup G} (hKQ : K ≤ normalizer (Q : Set G))
    (hQ : IsPGroup 2 Q) (hK : ⁅K, K⁆ = K) :
    ∀ {A H : Subgroup G}, IsSubnormal A H → H ≤ K ⊔ Q → K ≤ A →
      A ≤ normalizer (K : Set G) → H ≤ normalizer (K : Set G) := by
  intro A H hA
  induction hA with
  | refl => exact fun _ _ h => h
  | @step A B C hAB hAn hBC ih =>
    intro hCK hKA hAN
    refine ih hCK (hKA.trans hAB) ?_
    intro b hb
    have hBA : B ≤ normalizer (A : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hAB).mp hAn
    have hKb : K.map (MulAut.conj b).toMonoidHom ≤ A := by
      rintro _ ⟨k, hk, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp (hBA hb) k).mp (hKA hk)
    have hperf : ⁅K.map (MulAut.conj b).toMonoidHom, K.map (MulAut.conj b).toMonoidHom⁆ =
        K.map (MulAut.conj b).toMonoidHom := by
      rw [← Subgroup.map_commutator, hK]
    have hsup : K.map (MulAut.conj b).toMonoidHom ≤ K ⊔ (A ⊓ Q) := by
      intro x hx
      have hxA := hKb hx
      have hxKQ : x ∈ ((K ⊔ Q : Subgroup G) : Set G) := hCK (hBC.le (hAB hxA))
      rw [Subgroup.coe_mul_of_left_le_normalizer_right K Q hKQ] at hxKQ
      obtain ⟨k, hk, q, hq, rfl⟩ := hxKQ
      have hqA : q ∈ A := by
        have := A.mul_mem (A.inv_mem (hKA hk)) hxA
        simpa using this
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hk) (Subgroup.mem_sup_right ⟨hqA, hq⟩)
    have hle := CFSG.Quasithin.C41Pf.le_of_perfect_of_le_sup
      (inf_le_left.trans hAN) (hQ.to_le inf_le_right) hperf hsup
    exact TenNineOneThree.mem_normalizer_of_conj_mem fun k hk => hle ⟨k, hk, rfl⟩

theorem pCoreOf_le_normalizer {M L : Subgroup G} (hLM : L ≤ M) (hsub : IsSubnormal L M)
    (hperf : ⁅L, L⁆ = L) : pCoreOf 2 M ≤ normalizer (L : Set G) := by
  have hLV : L ≤ normalizer (pCoreOf 2 M : Set G) :=
    hLM.trans (localGroup_le_normalizer_pCoreOf 2 M)
  have hsup : L ⊔ pCoreOf 2 M ≤ M := sup_le hLM (CFSG.LieType.BorelTits.pCoreOf_le 2 M)
  have hsub' : IsSubnormal L (L ⊔ pCoreOf 2 M) := by
    have h := hsub.inf_of_le hsup
    rwa [inf_eq_left.mpr le_sup_left] at h
  have := le_normalizer_of_chain hLV (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M) hperf hsub'
    le_rfl le_rfl Subgroup.le_normalizer
  exact le_sup_right.trans this

theorem commutator_mem_of_ne {M L : Subgroup G} (hL : IsTwoPrimeComponent M L) {m : G}
    (hm : m ∈ M) (hne : L.map (MulAut.conj m).toMonoidHom ≠ L) :
    ∀ a ∈ L, ∀ b ∈ L.map (MulAut.conj m).toMonoidHom, a * b * a⁻¹ * b⁻¹ ∈ pCoreOf 2 M := by
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hπ
  set B := barM M L with hB
  set mb : ↥M ⧸ CFSG.pCore 2 ↥M := π ⟨m, hm⟩ with hmb
  set B' := B.map (MulAut.conj mb).toMonoidHom with hB'
  have hBc : IsComponentOf B ⊤ := hL.component
  have hB'c : IsComponentOf B' ⊤ := isComponentOf_map_conj hBc mb
  have hBB : B ≠ B' := by
    intro heq
    apply hne
    have hle : L.map (MulAut.conj m).toMonoidHom ≤ L ⊔ pCoreOf 2 M := by
      rintro _ ⟨b, hb, rfl⟩
      have hbM : b ∈ M := hL.le hb
      have hmem : π ⟨m * b * m⁻¹, M.mul_mem (M.mul_mem hm hbM) (M.inv_mem hm)⟩ ∈ B := by
        rw [heq]
        refine ⟨π ⟨b, hbM⟩, ⟨⟨b, hbM⟩, hb, rfl⟩, ?_⟩
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hmb]
        rw [← map_mul, ← map_inv, ← map_mul]
        rfl
      obtain ⟨a, ha, hab⟩ := hmem
      have hv : a⁻¹ * ⟨m * b * m⁻¹, M.mul_mem (M.mul_mem hm hbM) (M.inv_mem hm)⟩ ∈
          CFSG.pCore 2 ↥M := by
        rw [← QuotientGroup.eq_one_iff]
        show π _ = 1
        rw [map_mul, map_inv, hab, inv_mul_cancel]
      have e : m * b * m⁻¹ = (a : G) *
          ((a⁻¹ * ⟨m * b * m⁻¹, M.mul_mem (M.mul_mem hm hbM) (M.inv_mem hm)⟩ : ↥M) : G) := by
        simp
      show (MulAut.conj m) b ∈ L ⊔ pCoreOf 2 M
      rw [MulAut.conj_apply, e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp ha))
        (Subgroup.mem_sup_right ⟨_, hv, rfl⟩)
    have hperf' : ⁅L.map (MulAut.conj m).toMonoidHom, L.map (MulAut.conj m).toMonoidHom⁆ =
        L.map (MulAut.conj m).toMonoidHom := by
      rw [← Subgroup.map_commutator, hL.perfect]
    have hle' := CFSG.Quasithin.C41Pf.le_of_perfect_of_le_sup
      (pCoreOf_le_normalizer hL.le hL.subnormal hL.perfect)
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M) hperf' hle
    refine Subgroup.eq_of_le_of_card_ge hle' ?_
    rw [Subgroup.card_map_of_injective (MulAut.conj m).injective]
  have hcomm := commute_of_isComponentOf_ne hBc hB'c hBB
  intro a ha b hb
  obtain ⟨b₀, hb₀, rfl⟩ := hb
  have haM : a ∈ M := hL.le ha
  have hb₀M : b₀ ∈ M := hL.le hb₀
  have hbM : (MulAut.conj m).toMonoidHom b₀ ∈ M := by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact M.mul_mem (M.mul_mem hm hb₀M) (M.inv_mem hm)
  have h1 : π ⟨a, haM⟩ ∈ B := ⟨⟨a, haM⟩, ha, rfl⟩
  have h2 : π ⟨_, hbM⟩ ∈ B' := by
    refine ⟨π ⟨b₀, hb₀M⟩, ⟨⟨b₀, hb₀M⟩, hb₀, rfl⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hmb]
    rw [← map_mul, ← map_inv, ← map_mul]
    rfl
  have hc := hcomm _ h1 _ h2
  have hv : (⟨a, haM⟩ : ↥M) * ⟨_, hbM⟩ * (⟨a, haM⟩ : ↥M)⁻¹ * (⟨_, hbM⟩ : ↥M)⁻¹ ∈
      CFSG.pCore 2 ↥M := by
    rw [← QuotientGroup.eq_one_iff]
    show π _ = 1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hc]
    group
  exact ⟨_, hv, rfl⟩

end TenTenNormI

open TenTenNormI

end CFSG.LocalAnalysis.RankThreeTheoremC
