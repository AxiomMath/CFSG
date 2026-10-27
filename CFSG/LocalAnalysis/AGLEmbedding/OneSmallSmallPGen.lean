module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBOneChar
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBZeroFusion
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSmallPKFacts
public import CFSG.LocalAnalysis.SectionRank.ClassicalEven.Basic

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {X : Type} [Group X] [Finite X]

theorem exists_central_order_three_of_le_normalizer {R N : Subgroup X} (hR : IsPGroup 3 R)
    (hNR : N ≤ R) (hRN : R ≤ Subgroup.normalizer (N : Set X)) (hN : N ≠ ⊥) :
    ∃ c ∈ N, (∀ r ∈ R, r * c = c * r) ∧ orderOf c = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Group.IsNilpotent R := hR.isNilpotent
  set N' : Subgroup R := N.subgroupOf R with hN'
  have hN'n : N'.Normal := ⟨fun n hn g => by
    rw [hN', Subgroup.mem_subgroupOf] at hn ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact (Subgroup.mem_normalizer_iff.mp (hRN g.2) n).mp hn⟩
  have hN'1 : N' ≠ ⊥ := by
    intro h
    apply hN
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hNR hx⟩ : R) ∈ N' := hx
    rw [h, Subgroup.mem_bot] at this
    exact (Subgroup.mem_bot).mpr (congrArg Subtype.val this)
  have hne := Group.IsNilpotent.inf_center_ne_bot_of_normal hN'1
  set D : Subgroup R := N' ⊓ Subgroup.center R with hD
  have hDp : IsPGroup 3 D := hR.to_subgroup D
  obtain ⟨n, hn⟩ := hDp.exists_card_eq
  have h1 : 1 < Nat.card D := (Subgroup.one_lt_card_iff_ne_bot D).mpr hne
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [hn, pow_zero] at h1
    exact lt_irrefl 1 h1
  have hdvd : 3 ∣ Nat.card D := by
    rw [hn]
    exact dvd_pow_self 3 hn0
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 3 hdvd
  refine ⟨((g : R) : X), g.2.1, fun r hr => ?_, ?_⟩
  · have hc := Subgroup.mem_center_iff.mp g.2.2 ⟨r, hr⟩
    exact congrArg Subtype.val hc
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hg]

theorem ReducedNongeneration.false_of_outer_three (hGen : KFactL34OuterGen)
    {R : Sylow 3 X} {X₀ : Subgroup X} (h : ReducedNongeneration 3 X R X₀) {K : Subgroup X}
    (hK : IsComponentOf K ⊤) (hL : IsLinThreeFour K)
    (hnc : ¬ IsCyclic ((R : Subgroup X) ⊓ K : Subgroup X))
    {z : X} (hzR : z ∈ (R : Subgroup X)) (hzK : z ∉ K) (hzp : orderOf z = 3)
    (hzc : z ∈ Subgroup.centralizer (K : Set X))
    {f : X} (hfR : f ∈ (R : Subgroup X)) (hf3 : f ^ 3 = 1) (hfz : f * z = z * f)
    (hfK : f ∉ K ⊔ Subgroup.centralizer (K : Set X)) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hRN := h.sylow_le_normalizer_component hK
  obtain ⟨hNU, hKX₀⟩ := h.rankOne_principle hK hnc hzR hzK hzp hzc
  apply hKX₀
  obtain ⟨T₀, hT₀⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal R
    (ComponentClassification.Components.mathlib_subnormal_of_chain hK.2.1
      Subgroup.IsSubnormal.top)
  have hRKne : (R : Subgroup X) ⊓ K ≠ ⊥ := fun h0 => hnc (h0 ▸ inferInstance)
  have hRRK : (R : Subgroup X) ≤ Subgroup.normalizer (((R : Subgroup X) ⊓ K : Subgroup X) :
      Set X) := by
    intro r hr
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have h1 := Subgroup.mem_normalizer_iff.mp (hRN hr) y
    constructor
    · rintro ⟨hyR, hyK⟩
      exact ⟨(R : Subgroup X).mul_mem ((R : Subgroup X).mul_mem hr hyR)
        ((R : Subgroup X).inv_mem hr), h1.mp hyK⟩
    · rintro ⟨hyR, hyK⟩
      refine ⟨?_, h1.mpr hyK⟩
      have : y = r⁻¹ * (r * y * r⁻¹) * r := by group
      rw [this]
      exact (R : Subgroup X).mul_mem ((R : Subgroup X).mul_mem ((R : Subgroup X).inv_mem hr) hyR)
        hr
  obtain ⟨d, ⟨hdR, hdK⟩, hdc, hdp⟩ :=
    exists_central_order_three_of_le_normalizer R.isPGroup' inf_le_left hRRK hRKne
  have hfN : f ∈ Subgroup.normalizer (K : Set X) := hRN hfR
  set φ : MulAut K := K.normalizerMonoidHom ⟨f, hfN⟩ with hφdef
  have hφ : ∀ k : K, ((φ k : K) : X) = f * k * f⁻¹ := fun k => rfl
  have hφ3 : φ ^ 3 = 1 := by
    have h1 : (⟨f, hfN⟩ : Subgroup.normalizer (K : Set X)) ^ 3 = 1 :=
      Subtype.ext (by simpa using hf3)
    rw [hφdef, ← map_pow, h1, map_one]
  have hφout : φ ∉ (MulAut.conj : K →* MulAut K).range := by
    rintro ⟨κ, hκ⟩
    apply hfK
    have hcen : (κ : X)⁻¹ * f ∈ Subgroup.centralizer (K : Set X) := by
      refine Subgroup.mem_centralizer_iff.mpr fun k hk => ?_
      have h1 := congrArg (fun g : MulAut K => ((g ⟨k, hk⟩ : K) : X)) hκ
      simp only [MulAut.conj_apply] at h1
      have h2 : (κ : X) * k * (κ : X)⁻¹ = f * k * f⁻¹ := by
        rw [← hφ ⟨k, hk⟩]
        simpa using h1
      calc k * ((κ : X)⁻¹ * f) = (κ : X)⁻¹ * ((κ : X) * k * (κ : X)⁻¹) * f := by group
        _ = (κ : X)⁻¹ * (f * k * f⁻¹) * f := by rw [h2]
        _ = (κ : X)⁻¹ * f * k := by group
    have : f = (κ : X) * ((κ : X)⁻¹ * f) := by group
    rw [this]
    exact Subgroup.mul_mem_sup κ.2 hcen
  have hT₀mem : ∀ t : K, t ∈ (T₀ : Subgroup K) ↔ (t : X) ∈ (R : Subgroup X) ⊓ K := by
    intro t
    constructor
    · intro ht
      rw [← hT₀]
      exact ⟨t, ht, rfl⟩
    · intro ht
      rw [← hT₀] at ht
      obtain ⟨t', ht', htt⟩ := ht
      rw [← Subtype.ext htt]
      exact ht'
  have hφT : ∀ t ∈ (T₀ : Subgroup K), φ t ∈ (T₀ : Subgroup K) := by
    intro t ht
    rw [hT₀mem] at ht ⊢
    rw [hφ]
    exact (Subgroup.mem_normalizer_iff.mp (hRRK hfR) t).mp ht
  have hz3 : z ^ 3 = 1 := by rw [← hzp]; exact pow_orderOf_eq_one z
  have hcz : Commute z f := hfz.symm
  set Q := commPlane (by norm_num : 0 < 3) hcz hz3 hf3 with hQ
  have hQR : Q ≤ (R : Subgroup X) := by
    rintro _ ⟨i, j, rfl⟩
    exact (R : Subgroup X).mul_mem ((R : Subgroup X).pow_mem hzR i)
      ((R : Subgroup X).pow_mem hfR j)
  have hf1 : f ≠ 1 := fun h1 => hfK (h1 ▸ (K ⊔ Subgroup.centralizer (K : Set X)).one_mem)
  have hfp : orderOf f = 3 := orderOf_eq_prime hf3 hf1
  have hinf : Subgroup.zpowers z ⊓ Subgroup.zpowers f = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).mpr fun w hw => ?_
    by_contra hw1
    apply hfK
    have h1 := mem_zpowers_of_mem_zpowers_of_prime Nat.prime_three hfp hw.2 hw1
    have hwC : w ∈ Subgroup.centralizer (K : Set X) := (Subgroup.zpowers_le.mpr hzc) hw.1
    exact Subgroup.mem_sup_right ((Subgroup.zpowers_le.mpr hwC) h1)
  have hQcard : Nat.card Q = 3 ^ 2 := by
    refine le_antisymm (card_commPlane_le _ _ _ _) ?_
    have h1 := mul_card_le_of_inf_eq_bot (Subgroup.zpowers_le.mpr ⟨1, 0, by simp⟩ :
      Subgroup.zpowers z ≤ Q) (Subgroup.zpowers_le.mpr ⟨0, 1, by simp⟩ :
        Subgroup.zpowers f ≤ Q) hinf
    rw [Nat.card_zpowers, Nat.card_zpowers, hzp, hfp] at h1
    simpa [sq] using h1
  have hQ2 : 2 ≤ Open.pRank 3 Q :=
    le_csSup (pRank_bddAbove 3 Nat.prime_three Q)
      ⟨Q, le_rfl, isElemAbelian_commPlane _ _ _ _, hQcard⟩
  have hdQ : d ∈ (R : Subgroup X) ⊓ Subgroup.centralizer (Q : Set X) :=
    ⟨hdR, Subgroup.mem_centralizer_iff.mpr fun q hq => hdc q (hQR hq)⟩
  set S := Q ⊔ ((R : Subgroup X) ⊓ Subgroup.centralizer (Q : Set X)) with hS
  have hzS : z ∈ S := Subgroup.mem_sup_left ⟨1, 0, by simp⟩
  have hfS : f ∈ S := Subgroup.mem_sup_left ⟨0, 1, by simp⟩
  have hdS : d ∈ S := Subgroup.mem_sup_right hdQ
  have hd3 : d ^ 3 = 1 := by rw [← hdp]; exact pow_orderOf_eq_one d
  have hz1 : z ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hzp; norm_num at hzp
  have h3top : 3 ≤ Open.pRank 3 (⊤ : Subgroup S) := by
    refine CFSG.SectionRank.ClassicalEven.three_le_pRank_of_gens (x := ⟨z, hzS⟩)
      (y := ⟨d, hdS⟩) (z := ⟨f, hfS⟩) (Subtype.ext (by simpa using hz3))
      (Subtype.ext (by simpa using hd3)) (Subtype.ext (by simpa using hf3))
      (Subtype.ext (hdc z hzR)) (Subtype.ext hfz.symm) (Subtype.ext (hdc f hfR).symm)
      (fun h1 => hz1 (by simpa using congrArg Subtype.val h1)) (fun n hn => ?_)
      (fun n m hnm => ?_)
    · have hzd : z ^ n = d := by simpa using congrArg Subtype.val hn
      have hd1 : d ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hdp; norm_num at hdp
      apply hzK
      have h1 := mem_zpowers_of_mem_zpowers_of_prime Nat.prime_three hzp
        (hzd ▸ Subgroup.npow_mem_zpowers z n) hd1
      exact (Subgroup.zpowers_le.mpr hdK) h1
    · have hzdf : z ^ n * d ^ m = f := by simpa using congrArg Subtype.val hnm
      apply hfK
      rw [← hzdf]
      have hc : Commute (z ^ n) (d ^ m) :=
        ((show Commute z d from hdc z hzR).pow_left n).pow_right m
      rw [hc.eq]
      exact Subgroup.mul_mem_sup (K.pow_mem hdK m)
        ((Subgroup.centralizer (K : Set X)).pow_mem hzc n)
  have hQ3 : 3 ≤ Open.pRank 3 S := by
    have h1 := pRank_map_of_injective 3 Nat.prime_three S.subtype S.subtype_injective ⊤
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype] at h1
    rw [h1]
    exact h3top
  have hNQ : Subgroup.normalizer (Q : Set X) ≤ X₀ :=
    (normalizer_le_weakCore 3 hQR hQ2 hQ3).trans h.weakCore_le
  have hS1 : ∀ k : K, φ k = k → k ∈ X₀.comap K.subtype := by
    intro k hk
    have hkf : f * k * f⁻¹ = k := by rw [← hφ k, hk]
    have hkf' : (k : X) * f = f * k := by
      calc (k : X) * f = f * k * f⁻¹ * f := by rw [hkf]
        _ = f * k := by group
    have hkz : (k : X) * z = z * k := Subgroup.mem_centralizer_iff.mp hzc k k.2
    have hkq : ∀ q ∈ Q, (k : X) * q * (k : X)⁻¹ = q := by
      rintro _ ⟨i, j, rfl⟩
      have h1 : Commute (k : X) (z ^ i) := (show Commute (k : X) z from hkz).pow_right i
      have h2 : Commute (k : X) (f ^ j) := (show Commute (k : X) f from hkf').pow_right j
      rw [(h1.mul_right h2).eq, mul_inv_cancel_right]
    change (k : X) ∈ X₀
    refine hNQ (Subgroup.mem_normalizer_iff.mpr fun q => ⟨fun hq => ?_, fun hq => ?_⟩)
    · rw [hkq q hq]
      exact hq
    · have h1 := hkq _ hq
      have h2 : (k : X) * q * (k : X)⁻¹ = q :=
        mul_left_cancel (mul_right_cancel (h1.trans (by group)))
      rw [← h2]
      exact hq
  have hS2 : Subgroup.normalizer ((T₀ : Subgroup K) : Set K) ≤ X₀.comap K.subtype := by
    intro k hk
    have hk' : (k : X) ∈ Subgroup.normalizer
        (((R : Subgroup X) ⊓ K : Subgroup X) : Set X) := by
      rw [← hT₀]
      exact Subgroup.le_normalizer_map K.subtype ⟨k, hk, rfl⟩
    exact hNU _ le_rfl hRKne ⟨k.2, hk'⟩
  have htop := hGen K hL T₀ φ hφ3 hφout hφT _ hS1 hS2
  intro x hx
  have : (⟨x, hx⟩ : K) ∈ X₀.comap K.subtype := htop ▸ Subgroup.mem_top _
  exact this

end CFSG.AGLEmbedding
