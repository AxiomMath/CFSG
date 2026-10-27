module

public import CFSG.ClassicalInvolution.Asc77.AscT8LayerDich
public import CFSG.ClassicalInvolution.Asc77.AscT8Layer

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

namespace T8

section Eight

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

omit [Finite G] in
theorem ne_of_mem_omegaNbr {K J : Subgroup G} {z t : G} (hnt : ∀ K' ∈ twinSet Ω K, K' = K)
    (hJ : J ∈ omegaNbr Ω K) (hz : IsUniqueInvolution K z) (ht : IsUniqueInvolution J t) :
    z ≠ t := by
  intro h
  exact hJ.2.1 (hnt J ⟨hJ.1, z, hz, h ▸ ht⟩)

theorem xMem_zt {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}
    (hs : Std8 p f Ω K J S R T W z t) : XMem Ω (z * t) K := by
  have hp : p ≠ 2 := hs.stand.odd
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  refine ⟨hK, ?_, R, T3.isSylow2In_of_mem_RSet_of_le hp hΩ hK hs.hR.1 hs.hR.2.1, fun r hr => ?_⟩
  · have hc := mul_comm_of_mem_omegaNbr hp hΩ hs.hz hs.hJ hs.ht
    have haz : z * t ∈ Subgroup.centralizer ({z} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc z * t * z = z * (t * z) := by group
        _ = z * (z * t) := by rw [← hc]
    exact centralizer_le_normalizer_of_noTwins hΩ.conjInvariant hK hs.noTwins hs.hz haz
  · exact Subgroup.mem_centralizer_singleton_iff.mp (le_centralizer_mul hs hr)

omit [Finite G] in
theorem zt_ne_one {K J : Subgroup G} {z t : G} (hnt : ∀ K' ∈ twinSet Ω K, K' = K)
    (hJ : J ∈ omegaNbr Ω K) (hz : IsUniqueInvolution K z) (ht : IsUniqueInvolution J t) :
    z * t ≠ 1 := mul_ne_one_of_ne hz.sq (ne_of_mem_omegaNbr hnt hJ hz ht)

theorem zt_not_central [IsSimpleGroup G] {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G}
    {z t : G} (hs : Std8 p f Ω K J S R T W z t) : ¬ ({z * t} : Set G) ⊆ Subgroup.center G := by
  intro hc
  have hz : z * t ∈ Subgroup.center G := hc rfl
  have hKs := CFSG.StronglyEmbedded.UniqueCoset.not_isSolvable_of_mem hs.stand.hyp hs.stand.mem
    hs.hz
  rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center G) with h | h
  · exact zt_ne_one hs.noTwins hs.hJ hs.hz hs.ht (by rw [h] at hz; simpa using hz)
  · have hcomm : ∀ a b : G, a * b = b * a := fun a b => by
      have hb : b ∈ Subgroup.center G := by rw [h]; exact Subgroup.mem_top b
      exact (Subgroup.mem_center_iff.1 hb a)
    have : Group.IsSolvable G := IsSimpleGroup.comm_iff_isSolvable.mp hcomm
    exact hKs inferInstance

theorem card_layerQuot_lt {x : G} (hx : ¬ ({x} : Set G) ⊆ Subgroup.center G) :
    Nat.card (LayerQuot Ω x) < Nat.card G := by
  have h1 : Nat.card (LayerQuot Ω x) ≤ Nat.card ↥(layerJoin Ω x) :=
    Nat.card_le_card_of_surjective _ (QuotientGroup.mk_surjective)
  have h2 : Nat.card ↥(layerJoin Ω x) ≤ Nat.card ↥(Subgroup.centralizer ({x} : Set G)) := by
    refine Subgroup.card_le_of_le ?_
    rw [← cenZ_eq_centralizer]
    exact layerJoin_le_cenZ x
  have hne : Subgroup.centralizer ({x} : Set G) ≠ ⊤ := fun h =>
    hx (Subgroup.centralizer_eq_top_iff_subset.mp h)
  have h3 := Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr hne)
  rw [Subgroup.card_top] at h3
  omega

theorem layerJoin_le_rLayer (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω) {x : G}
    (hx : x * x = 1) : layerJoin Ω x ≤ rLayer Ω x :=
  iSup₂_le fun L hL => by
    obtain ⟨K, hK, rfl⟩ := hL
    exact hK.layerRes_le_rLayer hp hq hΩ hx

end Eight

end T8

variable {p f : ℕ} [Fact p.Prime]

theorem c27_8_of_c27_6_c27_7 (h6 : C27_6 p f) (h7 : C27_7 p f) : C27_8 p f := by
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
  have hY : T8.layerJoin Ω (z * t) ≤ sigmaNorm Ω K :=
    (T8.layerJoin_le_rLayer hp hq hΩ ha2).trans
      (rLayer_le_sigmaNorm_of_c27_6_c27_7 h6 h7 hs hdisc)
  show c ∈ sigmaNorm Ω K
  rw [T8.mem_sigmaNorm_iff hΩ.conjInvariant hK]
  rcases T8.layer_dichotomy hp hq hΩ hnt ha2 hn hlt hKx hKc with ⟨y, hy, hyc⟩ | ⟨m, hm, hmc⟩
  · rw [hyc]
    exact (T8.mem_sigmaNorm_iff hΩ.conjInvariant hK).1 (hY hy)
  · have hmK := (T8.mem_sigmaNorm_iff hΩ.conjInvariant hK).1 (hY hm)
    exact hmK.trans (Relation.ReflTransGen.single ⟨hKc.1, Or.inl hmc⟩)

end CFSG.ClassicalInvolution.Asc77
