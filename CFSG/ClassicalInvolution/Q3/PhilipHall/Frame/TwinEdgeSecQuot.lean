module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.SectionIH

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open scoped commutatorElement

namespace Quot

variable {H : Type} [Group H] [Finite H] {Λ : Set (Subgroup H)} {N : Subgroup H} [N.Normal]

theorem exists_lift_isPGroup (hN : Odd (Nat.card N)) {K : Subgroup H} {W : Subgroup (H ⧸ N)}
    (hW : IsPGroup 2 W) (hWK : W ≤ K.map (QuotientGroup.mk' N)) :
    ∃ V : Subgroup H, V ≤ K ∧ IsPGroup 2 V ∧ V.map (QuotientGroup.mk' N) = W := by
  set π := QuotientGroup.mk' N with hπ
  set B : Subgroup H := K ⊓ W.comap π with hB
  have hBmap : B.map π = W := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact hx.2
    · intro w hw
      obtain ⟨k, hk, hkw⟩ := hWK hw
      exact ⟨k, ⟨hk, show π k ∈ W by rw [hkw]; exact hw⟩, hkw⟩
  obtain ⟨V, hV, -⟩ := IsSylow2In.exists_ge (T := ⊥) (P := B) IsPGroup.of_bot bot_le
  have hmap := isSylow2In_map_mk hN hV
  rw [hBmap] at hmap
  exact ⟨V, hV.1.trans inf_le_left, hV.2.1, (hmap.2.2 W le_rfl hW (by
    rw [← hBmap]; exact Subgroup.map_mono hV.1)).symm⟩

theorem exists_conj_lift (hN : Odd (Nat.card N)) {K J : Subgroup H} {W : Subgroup (H ⧸ N)}
    (hW : IsPGroup 2 W) (hWK : W ≤ K.map (QuotientGroup.mk' N))
    (hWJ : W ≤ J.map (QuotientGroup.mk' N)) :
    ∃ n ∈ N, ∃ V : Subgroup H, V ≤ conjSub n K ⊓ J ∧ IsPGroup 2 V ∧
      V.map (QuotientGroup.mk' N) = W := by
  set π := QuotientGroup.mk' N with hπ
  obtain ⟨VK, hVKK, hVK2, hVKW⟩ := exists_lift_isPGroup hN hW hWK
  obtain ⟨VJ, hVJJ, hVJ2, hVJW⟩ := exists_lift_isPGroup hN hW hWJ
  have hKN : VK ⊓ N = ⊥ :=
    AscQuot.inf_eq_bot_of_isPGroup_of_odd N hVK2 (le_refl VK) (odd_natCard_inf hN VK)
  have hJN : VJ ⊓ N = ⊥ :=
    AscQuot.inf_eq_bot_of_isPGroup_of_odd N hVJ2 (le_refl VJ) (odd_natCard_inf hN VJ)
  have hcard : Nat.card VJ = Nat.card VK := by
    have h1 : Nat.card ↥(VJ.map π) = Nat.card VJ :=
      (Nat.card_congr (AscQuot.quotRestrictEquiv hJN).toEquiv).symm
    have h2 : Nat.card ↥(VK.map π) = Nat.card VK :=
      (Nat.card_congr (AscQuot.quotRestrictEquiv hKN).toEquiv).symm
    rw [← h1, ← h2, hVJW, hVKW]
  have hle : VJ ≤ N ⊔ VK := by
    intro x hx
    have hx' : π x ∈ VK.map π := hVKW ▸ hVJW ▸ Subgroup.mem_map_of_mem _ hx
    obtain ⟨k, hk, hkx⟩ := hx'
    have hnx : k⁻¹ * x ∈ N := OddQuot.inv_mul_mem_of_mk_eq hkx
    have : x = k * (k⁻¹ * x) := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hk) (Subgroup.mem_sup_left hnx)
  have hnorm : VK ≤ Subgroup.normalizer (N : Set H) := by
    rw [Subgroup.normalizer_eq_top]; exact le_top
  obtain ⟨n, hn, hnV⟩ := Q3T7M.CentQ.exists_conjSub_of_le_sup_odd hnorm hN hKN hVK2 hVJ2 hcard hle
  refine ⟨n, hn, VJ, ?_, hVJ2, hVJW⟩
  refine le_inf ?_ hVJJ
  rw [← hnV]
  exact conjSub_mono hVKK

theorem omega4_quot_odd (hΛ : HypOmegaGen Λ) (hN : Odd (Nat.card N)) {K J : Subgroup H}
    (hK : K ∈ Λ) (hJ : J ∈ Λ)
    (hne : K.map (QuotientGroup.mk' N) ≠ J.map (QuotientGroup.mk' N)) :
    padicValNat 2 (Nat.card ↥(K.map (QuotientGroup.mk' N) ⊓ J.map (QuotientGroup.mk' N))) ≤ 1 ∧
      (padicValNat 2 (Nat.card ↥(K.map (QuotientGroup.mk' N) ⊓
          J.map (QuotientGroup.mk' N))) = 1 →
        ⁅K.map (QuotientGroup.mk' N), J.map (QuotientGroup.mk' N)⁆ ≤
          oddCoreOf (K.map (QuotientGroup.mk' N)) ⊓ oddCoreOf (J.map (QuotientGroup.mk' N))) := by
  set π := QuotientGroup.mk' N with hπ
  set A : Subgroup (H ⧸ N) := K.map π ⊓ J.map π with hA
  obtain ⟨W, hW, -⟩ := IsSylow2In.exists_ge (T := ⊥) (P := A) IsPGroup.of_bot bot_le
  obtain ⟨n, hn, V, hVle, hV2, hVW⟩ := exists_conj_lift hN hW.2.1 (hW.1.trans inf_le_left)
    (hW.1.trans inf_le_right)
  have himg := OddQuot.map_conjSub_of_mem hn K
  have hK' : conjSub n K ∈ Λ := hΛ.conjInvariant n K hK
  have hne' : conjSub n K ≠ J := fun h => hne (by rw [← himg, h])
  have h4 := hΛ.omega4 _ hK' _ hJ hne'
  have hVN : V ⊓ N = ⊥ :=
    AscQuot.inf_eq_bot_of_isPGroup_of_odd N hV2 (le_refl V) (odd_natCard_inf hN V)
  have hWcard : Nat.card W = 2 ^ padicValNat 2 (Nat.card A) := by
    rw [natCard_eq_pow_of_isSylow2In hW, Nat.factorization_def _ Nat.prime_two]
  have hVcard : Nat.card V = Nat.card W := by
    rw [← hVW]
    exact Nat.card_congr (AscQuot.quotRestrictEquiv hVN).toEquiv
  have hdvd : 2 ^ padicValNat 2 (Nat.card A) ∣ Nat.card ↥(conjSub n K ⊓ J) := by
    rw [← hWcard, ← hVcard]
    exact Subgroup.card_dvd_of_le hVle
  have hv : padicValNat 2 (Nat.card A) ≤ padicValNat 2 (Nat.card ↥(conjSub n K ⊓ J)) :=
    (padicValNat_dvd_iff_le Nat.card_pos.ne').mp hdvd
  refine ⟨hv.trans h4.1, fun h1 => ?_⟩
  have h1' : padicValNat 2 (Nat.card ↥(conjSub n K ⊓ J)) = 1 := le_antisymm h4.1 (h1 ▸ hv)
  have hc := h4.2 h1'
  rw [← himg, ← Subgroup.map_commutator]
  calc Subgroup.map π ⁅conjSub n K, J⁆
      ≤ Subgroup.map π (oddCoreOf (conjSub n K) ⊓ oddCoreOf J) := Subgroup.map_mono hc
    _ ≤ Subgroup.map π (oddCoreOf (conjSub n K)) ⊓ Subgroup.map π (oddCoreOf J) :=
        Subgroup.map_inf_le _ _ _
    _ = oddCoreOf ((conjSub n K).map π) ⊓ oddCoreOf (J.map π) := by
        rw [oddCoreOf_map_mk_of_odd (odd_natCard_inf hN (conjSub n K)),
          oddCoreOf_map_mk_of_odd (odd_natCard_inf hN J)]

theorem omega5_quot_odd (hΛ : HypOmegaGen Λ) (hN : Odd (Nat.card N)) :
    ∀ L ∈ quotFamily Λ N, ∀ L' ∈ quotFamily Λ N, L ≠ L' →
      ∀ z : H ⧸ N, IsUniqueInvolution L z → ∀ v ∈ L',
        (¬ ∀ w ∈ L', v * w = w * v) → IsPGroup 2 (Subgroup.zpowers v) → v * z = z * v →
          v ∈ Subgroup.normalizer (L : Set (H ⧸ N)) := by
  have hXK : ∀ K ∈ Λ, Odd (Nat.card ↥(N ⊓ K)) := fun K _ => odd_natCard_inf hN K
  rintro _ ⟨K, hK, rfl⟩ _ ⟨J, hJ, rfl⟩ hne zb hzb v hvJ hvnc hv2 hcomm
  beta_reduce at hne hzb hvJ hvnc ⊢
  obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution hΛ hK
  have hzb' : zb = QuotientGroup.mk' N z :=
    hzb.eq (isUniqueInvolution_map_mk_of_odd (hXK K hK) hz)
  obtain ⟨v₀, hv₀J, hv₀mk, hv₀2⟩ := exists_isPGroup_lift_of_mem_map hvJ hv2
  have hvnc' : ¬ ∀ w ∈ J, v₀ * w = w * v₀ := fun h => hvnc (by
    rintro _ ⟨w, hw, rfl⟩
    rw [← hv₀mk, ← map_mul, ← map_mul, h w hw])
  obtain ⟨n, hn, hncomm⟩ := OddQuot.exists_conj_commuting hN hz.sq
    (OddQuot.two_elt hv₀2 (Subgroup.mem_zpowers v₀))
    (by rw [hv₀mk, ← hzb']; exact hcomm)
  have himg := OddQuot.map_conjSub_of_mem hn K
  have hne' : conjSub n K ≠ J := fun h => hne (by rw [← himg, h])
  have hnorm := hΛ.omega5 (conjSub n K) (hΛ.conjInvariant n K hK) J hJ hne' _ (hz.conj n) v₀ hv₀J
    hvnc' hv₀2 hncomm.symm
  have := mk_mem_normalizer_map (N := N) hnorm
  rwa [himg, hv₀mk] at this

end Quot

theorem hypOmegaGen_quotFamily_odd {H : Type} [Group H] [Finite H] {Λ : Set (Subgroup H)}
    (hΛ : HypOmegaGen Λ) {N : Subgroup H} [N.Normal] (hN : Odd (Nat.card N)) :
    HypOmegaGen (Asc77.quotFamily Λ N) := by
  have hXK : ∀ K ∈ Λ, Odd (Nat.card ↥(N ⊓ K)) := fun K _ => odd_natCard_inf hN K
  refine
    { conjInvariant := AscQuot.conjInvariant_quot hΛ.conjInvariant N
      omega1 := ?_
      omega2 := ?_
      omega3 := ?_
      omega4 := ?_
      omega5 := Quot.omega5_quot_odd hΛ hN }
  · rintro _ ⟨K, hK, rfl⟩
    exact CentQ.omega1_quot_gen hΛ N hXK hK
  · rintro _ ⟨K, hK, rfl⟩
    exact CentQ.omega2_quot_gen hΛ N hXK hK
  · rintro _ ⟨K, hK, rfl⟩ _ ⟨J, hJ, rfl⟩ P Q hP hQ
    exact CentQ.omega3_quot_gen hΛ N hXK hK hJ hP hQ
  · rintro _ ⟨K, hK, rfl⟩ _ ⟨J, hJ, rfl⟩ hne
    exact Quot.omega4_quot_odd hΛ hN hK hJ hne

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge
