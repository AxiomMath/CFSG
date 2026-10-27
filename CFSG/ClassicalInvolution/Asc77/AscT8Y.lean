module

public import CFSG.ClassicalInvolution.Asc77.AscT8Eight

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

variable (p f : ℕ) [Fact p.Prime]

@[expose] def C27_Y : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), Std8 p f Ω K J S R T W z t →
      ¬ DConnected Ω → rLayer Ω (z * t) ≤ sigmaNorm Ω K

variable {p f}

theorem c27_Y_of_c27_6_c27_7 (h6 : C27_6 p f) (h7 : C27_7 p f) : C27_Y p f :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ hs hdisc => rLayer_le_sigmaNorm_of_c27_6_c27_7 h6 h7 hs hdisc

theorem c27_8_of_c27_Y (hY : C27_Y p f) : C27_8 p f := by
  intro G _ _ _ Ω K J S R T W z t hs hdisc c hc
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM
  have ha2 : z * t * (z * t) = 1 := T8.mul_self_zt hp hΩ hs.hz hs.hJ hs.ht
  have hKx : T8.XMem Ω (z * t) K := T8.xMem_zt hs
  have hcz : c ∈ T8.cenZ (z * t) := by
    rw [T8.cenZ_eq_centralizer]
    exact hc
  have hKc : T8.XMem Ω (z * t) (conjSub c K) := hKx.conj hΩ hcz
  have hn : CITBelowU p f (Nat.card G) := hs.stand.below f hq
  have hlt := T8.card_layerQuot_lt (Ω := Ω) (T8.zt_not_central hs)
  have hY' : T8.layerJoin Ω (z * t) ≤ sigmaNorm Ω K :=
    (T8.layerJoin_le_rLayer hp hq hΩ ha2).trans (hY G Ω K J S R T W z t hs hdisc)
  show c ∈ sigmaNorm Ω K
  rw [T8.mem_sigmaNorm_iff hΩ.conjInvariant hK]
  rcases T8.layer_dichotomy hp hq hΩ hnt ha2 hn hlt hKx hKc with ⟨y, hy, hyc⟩ | ⟨m, hm, hmc⟩
  · rw [hyc]
    exact (T8.mem_sigmaNorm_iff hΩ.conjInvariant hK).1 (hY' hy)
  · have hmK := (T8.mem_sigmaNorm_iff hΩ.conjInvariant hK).1 (hY' hm)
    exact hmK.trans (Relation.ReflTransGen.single ⟨hKc.1, Or.inl hmc⟩)

end CFSG.ClassicalInvolution.Asc77
