module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62xIrred
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureReduction
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.OutThreeCore
public import CFSG.LocalAnalysis.GL83PartI.I_6_10
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62xDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank

open CFSG.Open Subgroup
open scoped commutatorElement

theorem map_conj_eq_of_normalizer_le {K : Type} [Group K] [Finite K] {p : ℕ} [Fact p.Prime]
    (S : Sylow p K) [IsMulCommutative (S : Subgroup K)] {L : Subgroup K}
    (hL : L ≤ (S : Subgroup K)) {g : K}
    (hgL : L.map (MulAut.conj g).toMonoidHom ≤ (S : Subgroup K))
    (hle : normalizer ((S : Subgroup K) : Set K) ≤ normalizer (L : Set K)) :
    L.map (MulAut.conj g).toMonoidHom = L := by
  have hsub : L.map (MulAut.conj g).toMonoidHom ≤ L := by
    rintro _ ⟨x, hx, rfl⟩
    have hxS : x ∈ (S : Subgroup K) := hL hx
    have hyS : g * x * g⁻¹ ∈ (S : Subgroup K) := hgL ⟨x, hx, rfl⟩
    obtain ⟨n, hnN, hn⟩ := Sylow.conj_eq_normalizer_conj_of_mem S x g⁻¹ hxS (by rw [inv_inv]; exact hyS)
    have hn' : n⁻¹ ∈ normalizer (L : Set K) := hle (inv_mem hnN)
    have h1 : (MulAut.conj g).toMonoidHom x = n⁻¹ * x * n⁻¹⁻¹ := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      simpa using hn
    rw [h1]
    exact (mem_set_normalizer_iff.mp hn' x).mp hx
  refine Subgroup.eq_of_le_of_card_ge hsub ?_
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]

theorem kFactSylowNormalizerIrreducible_of_weakClosureInner
    (hWC : Stroth.WeakClosure.KFactWeakClosureInner) : KFactSylowNormalizerIrreducible := by
  intro K _ _ hK hs hnab P hPe hP9 hPidx L hLP hL3 hle
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hPpg : IsPGroup 3 P := IsPGroup.of_card (n := 2) (by rw [hP9]; norm_num)
  let S : Sylow 3 K := hPpg.toSylow hPidx
  have hS : (S : Subgroup K) = P := IsPGroup.toSylow_coe hPpg hPidx
  haveI hcomm : IsMulCommutative (S : Subgroup K) := by rw [hS]; exact hPe.1
  have hrank : 2 ≤ CFSG.Open.pRank 3 (S : Subgroup K) :=
    CFSG.SectionRank.le_pRank (k := 2) (by norm_num) hS.ge (hS ▸ hPe) (by rw [hP9]; norm_num)
  rw [← hS] at hLP hle
  obtain ⟨g, hgL, hgne⟩ := hWC 3 Nat.prime_three (by norm_num) K hs hnab
    (isCatalogGroup_of_isKGroup_simple hK) S hcomm hrank L hLP hL3
  exact hgne (map_conj_eq_of_normalizer_le S hLP hgL hle)

theorem eq_one_of_mem_center_of_pow_eq_one {K : Type} [Group K] [Finite K] {f : ℕ} (hf : f.Prime)
    (hZ : ¬ f ∣ Nat.card (Subgroup.center K)) {z : K} (hz : z ∈ Subgroup.center K) {m : ℕ}
    (hzm : z ^ (f ^ m) = 1) : z = 1 := by
  have hord : orderOf z ∣ f ^ m := orderOf_dvd_of_pow_eq_one hzm
  obtain ⟨i, -, hiord⟩ := (Nat.dvd_prime_pow hf).mp hord
  have hzord : orderOf z ∣ Nat.card (Subgroup.center K) :=
    Subgroup.orderOf_dvd_natCard (Subgroup.center K) hz
  by_cases hi0 : i = 0
  · have h1 : orderOf z = 1 := by rw [hiord, hi0, pow_zero]
    exact orderOf_eq_one_iff.mp h1
  · exfalso
    apply hZ
    have : f ∣ orderOf z := by rw [hiord]; exact dvd_pow_self f hi0
    exact this.trans hzord

theorem mem_of_map_mem_of_pow_eq_one {K : Type} [Group K] [Finite K] {f : ℕ} (hf : f.Prime)
    (hZ : ¬ f ∣ Nat.card (Subgroup.center K)) {P : Subgroup K} (hP : IsPGroup f P)
    {x : K} {k : ℕ} (hx : x ^ (f ^ k) = 1)
    (hmem : (QuotientGroup.mk' (Subgroup.center K)) x ∈
      P.map (QuotientGroup.mk' (Subgroup.center K))) : x ∈ P := by
  obtain ⟨p, hpP, hpx⟩ := hmem
  have hz : p⁻¹ * x ∈ Subgroup.center K := QuotientGroup.eq.mp hpx
  obtain ⟨z, hzc, rfl⟩ : ∃ z ∈ Subgroup.center K, x = p * z := ⟨p⁻¹ * x, hz, by simp⟩
  obtain ⟨j, hj⟩ := hP ⟨p, hpP⟩
  have hpj : p ^ (f ^ j) = 1 := congrArg Subtype.val hj
  have hcomm : Commute p z := Subgroup.mem_center_iff.mp hzc p
  have hpm : p ^ (f ^ (max j k)) = 1 := by
    obtain ⟨c, hc⟩ := pow_dvd_pow f (le_max_left j k)
    rw [hc, pow_mul, hpj, one_pow]
  have hxm : (p * z) ^ (f ^ (max j k)) = 1 := by
    obtain ⟨c, hc⟩ := pow_dvd_pow f (le_max_right j k)
    rw [hc, pow_mul, hx, one_pow]
  have hzm : z ^ (f ^ (max j k)) = 1 := by
    rw [hcomm.mul_pow, hpm, one_mul] at hxm
    exact hxm
  have hz1 : z = 1 := eq_one_of_mem_center_of_pow_eq_one hf hZ hzc hzm
  subst hz1
  simpa using hpP

@[expose] def KFactAbelianSylowLineMoving : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.IsKGroup K → CFSG.Open.IsQuasisimple K →
    ∀ (f : ℕ), f.Prime → f ≠ 2 → ∀ P A : Subgroup K, IsPGroup f P → ¬ f ∣ P.index →
      IsMulCommutative P → A ≤ P → Nat.card A = f ^ 3 → (∀ y ∈ A, y ^ f = 1) →
      (∀ y ∈ P, y ^ f = 1 → y ∈ A) →
        ∀ L : Subgroup K, L ≤ A → Nat.card L = f →
          ¬ normalizer (P : Set K) ≤ normalizer (L : Set K)

theorem lineMoving_of_weakClosureInner
    (hWC : Stroth.WeakClosure.KFactWeakClosureInner) : KFactAbelianSylowLineMoving := by
  intro K _ _ hK hq f hf hf2 P A hP hPi hPc hAP hA3 hA1 hA2 L hLA hL3 hle
  haveI : Fact f.Prime := ⟨hf⟩
  let S : Sylow f K := hP.toSylow hPi
  have hS : (S : Subgroup K) = P := IsPGroup.toSylow_coe hP hPi
  haveI hSc : IsMulCommutative (S : Subgroup K) := by rw [hS]; exact hPc
  have hZ : ¬ f ∣ Nat.card (Subgroup.center K) := fun hd =>
    GL83.not_isMulCommutative_sylow_of_perfect hq.1 hd S hSc
  let π : K →* K ⧸ Subgroup.center K := QuotientGroup.mk' (Subgroup.center K)
  haveI hsimple : IsSimpleGroup (K ⧸ Subgroup.center K) := hq.2
  have hKbar : CFSG.IsKGroup (K ⧸ Subgroup.center K) := hK.quotient _
  have hnab : ∃ a b : K ⧸ Subgroup.center K, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    have h1 : commutator K ≤ Subgroup.center K := by
      refine Subgroup.commutator_le.mpr fun x _ y _ => ?_
      rw [← QuotientGroup.eq_one_iff]
      have h0 : (QuotientGroup.mk' (Subgroup.center K)) ⁅x, y⁆ = 1 := by
        rw [map_commutatorElement]
        exact commutatorElement_eq_one_iff_commute.mpr (hcon _ _)
      exact h0
    have h2 : Subgroup.center K = ⊤ := top_unique (hq.1 ▸ h1)
    obtain ⟨a, ha⟩ := exists_ne (1 : K ⧸ Subgroup.center K)
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    exact ha ((QuotientGroup.eq_one_iff x).mpr (h2 ▸ Subgroup.mem_top x))
  let S' : Sylow f (K ⧸ Subgroup.center K) := S.mapSurjective (QuotientGroup.mk'_surjective _)
  have hS' : (S' : Subgroup (K ⧸ Subgroup.center K)) = P.map π := by
    rw [← hS]; rfl
  have hinj : Set.InjOn π (P : Set K) := by
    intro a ha b hb hab
    have h1 : a⁻¹ * b ∈ Subgroup.center K := QuotientGroup.eq.mp hab
    have h2 : a⁻¹ * b ∈ P := mul_mem (inv_mem ha) hb
    obtain ⟨j, hj⟩ := hP ⟨a⁻¹ * b, h2⟩
    have h3 : a⁻¹ * b = 1 :=
      eq_one_of_mem_center_of_pow_eq_one hf hZ h1 (congrArg Subtype.val hj)
    exact inv_mul_eq_one.mp h3
  have hcardmap : ∀ X : Subgroup K, X ≤ P → Nat.card (X.map π) = Nat.card X := by
    intro X hX
    have h1 := Nat.card_image_of_injOn (hinj.mono (fun x hx => hX hx))
    have e : Nat.card ↥(X.map π) = Nat.card ↥(π '' (X : Set K)) :=
      Nat.card_congr (Equiv.subtypeEquivRight (fun x => by
        rw [← SetLike.mem_coe, Subgroup.coe_map]))
    rw [e, h1]
    rfl
  haveI hS'c : IsMulCommutative (S' : Subgroup (K ⧸ Subgroup.center K)) := by
    rw [hS']
    haveI : IsMulCommutative P := hPc
    infer_instance
  have hrank : 2 ≤ CFSG.Open.pRank f (S' : Subgroup (K ⧸ Subgroup.center K)) := by
    have hAc : IsMulCommutative A := ⟨⟨fun a b => Subtype.ext (by
      have := hPc.is_comm.comm ⟨a, hAP a.2⟩ ⟨b, hAP b.2⟩
      exact congrArg (Subtype.val : P → K) this)⟩⟩
    have hAbar : IsElemAbelian f (A.map π) := by
      refine ⟨inferInstance, ?_⟩
      rintro _ ⟨a, ha, rfl⟩
      rw [← map_pow, hA1 a ha, map_one]
    have hle3 : 3 ≤ CFSG.Open.pRank f (S' : Subgroup (K ⧸ Subgroup.center K)) :=
      CFSG.SectionRank.le_pRank (k := 3) hf.one_lt (by rw [hS']; exact Subgroup.map_mono hAP)
        hAbar (by rw [hcardmap A hAP, hA3])
    omega
  have hLS' : L.map π ≤ (S' : Subgroup (K ⧸ Subgroup.center K)) := by
    rw [hS']
    exact Subgroup.map_mono (hLA.trans hAP)
  obtain ⟨gb, hgL, hgne⟩ := hWC f hf hf2 (K ⧸ Subgroup.center K) hsimple hnab
    (isCatalogGroup_of_isKGroup_simple hKbar) S' hS'c hrank (L.map π) hLS'
    (by rw [hcardmap L (hLA.trans hAP), hL3])
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center K) gb
  have hconj : ∀ X : Subgroup K,
      (X.map (MulAut.conj g).toMonoidHom).map π =
        (X.map π).map (MulAut.conj (π g)).toMonoidHom := by
    intro X
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
  have hgP : L.map (MulAut.conj g).toMonoidHom ≤ P := by
    rintro _ ⟨x, hx, rfl⟩
    have hxA : x ∈ A := hLA hx
    have hxf : x ^ f = 1 := hA1 x hxA
    have himg : π ((MulAut.conj g).toMonoidHom x) ∈ P.map π := by
      rw [← hS']
      apply hgL
      rw [← hconj] at *
      exact ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine mem_of_map_mem_of_pow_eq_one hf hZ hP (k := 1) ?_ himg
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, pow_one]
    rw [conj_pow, hxf]
    simp
  have hdone : L.map (MulAut.conj g).toMonoidHom = L :=
    map_conj_eq_of_normalizer_le S (hS ▸ hLA.trans hAP) (hS ▸ hgP) (hS ▸ hle)
  apply hgne
  rw [← hconj, hdone]

theorem kFactAbelianSylowRankThree_of_lineMoving (h : KFactAbelianSylowLineMoving) :
    KFactAbelianSylowRankThree := by
  intro K _ _ hK hq f hf hf2 P A hP hPi hPc hAP hA3 hA1 hA2
  by_contra hcon
  push Not at hcon
  have key : ∀ g ∈ normalizer (P : Set K), ∀ y ∈ A, g * y * g⁻¹ ∈ A := by
    intro g hg y hy
    refine hA2 _ ((Subgroup.mem_normalizer_iff.1 hg y).1 (hAP hy)) ?_
    rw [conj_pow, hA1 y hy, mul_one, mul_inv_cancel]
  have hnormA : ∀ g ∈ normalizer (P : Set K), ∀ y, y ∈ A ↔ g * y * g⁻¹ ∈ A := by
    intro g hg y
    refine ⟨key g hg y, fun hy => ?_⟩
    have := key g⁻¹ (inv_mem hg) _ hy
    simpa [mul_assoc] using this
  obtain ⟨L, hLA, hLcard, hLfix⟩ := irred62x_exists_fixed_line hf hf2 hA3 hA1
    (Γ := normalizer (P : Set K)) hnormA hcon
  exact h K hK hq f hf hf2 P A hP hPi hPc hAP hA3 hA1 hA2 L hLA hLcard fun g hg => hLfix g hg

theorem kFactAbelianSylowRankThree_of_weakClosureInner
    (hWC : Stroth.WeakClosure.KFactWeakClosureInner) : KFactAbelianSylowRankThree :=
  kFactAbelianSylowRankThree_of_lineMoving (lineMoving_of_weakClosureInner hWC)

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank
