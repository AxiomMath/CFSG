module

public import CFSG.GH74.Uniqueness.SU.KI6Main
public import CFSG.GH74.KGroups.KI5D
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuaternionReduction
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreFreeTwoLayer

public section

namespace CFSG.GH74.Uniqueness.SU.K.R6

open Subgroup CFSG CFSG.Blueprint CFSG.ProperTwoGeneratedCore CFSG.GH74.Uniqueness.SU.K.R3

variable {H : Type} [Group H] [Finite H]

open CFSG.LocalCores in
theorem Cfg.center_component_mem_pCore {T : Sylow 2 H} {H₀ : Subgroup H} (h : Cfg H T H₀)
    {L : Subgroup H} (hL : IsComponent L) {z : H} (hzL : z ∈ L)
    (hzc : ∀ l ∈ L, z * l = l * z) : z ∈ pCore 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzE : z ∈ layer H := le_sSup (show L ∈ {K : Subgroup H | IsComponent K} from hL) hzL
  have hcentral : ∀ g ∈ layer H, z * g = g * z := by
    have hle : layer H ≤ centralizer ({z} : Set H) := by
      refine sSup_le fun K hK => ?_
      rcases distinct_components_commute hL hK with hLK | hLK
      · rw [← hLK]
        intro l hl
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (hzc l hl).symm
      · intro k hk
        rw [Subgroup.mem_centralizer_singleton_iff]
        have := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hLK hzL
        exact Subgroup.mem_centralizer_iff.mp this k hk
    intro g hg
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hg)).symm
  have hzF : z ∈ fittingSubgroup H := by
    apply CFSG.ComponentClassification.UnbalancedLayer.center_layer_le_fittingSubgroup
    refine ⟨⟨z, hzE⟩, ?_, rfl⟩
    exact Subgroup.mem_center_iff.mpr (fun g => Subtype.ext (hcentral g g.2).symm)
  rwa [Fitting_eq_pcore H 2 h.odd] at hzF

theorem Cfg.isPGroup_center_component {T : Sylow 2 H} {H₀ : Subgroup H} (h : Cfg H T H₀)
    {L : Subgroup H} (hL : IsComponent L) : IsPGroup 2 ↥(center ↥L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro z
  have hzp : (z : H) ∈ pCore 2 H :=
    h.center_component_mem_pCore hL (z : ↥L).2 (fun l hl =>
      congrArg Subtype.val (Subgroup.mem_center_iff.mp z.2 ⟨l, hl⟩).symm)
  obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := H)) ⟨(z : H), hzp⟩
  refine ⟨n, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  have := congrArg Subtype.val hn
  simpa using this

@[expose] def KI6Z4 : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (T : Sylow 2 H) (H₀ : Subgroup H), Cfg H T H₀ →
    ∀ L : Subgroup H, IsComponent L → 2 ≤ Open.pRank 2 L → 4 ≤ Nat.card (center ↥L) → False

@[expose] def KI6TwoA9 : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (T : Sylow 2 H) (H₀ : Subgroup H), Cfg H T H₀ →
    ∀ L : Subgroup H, IsComponent L → 2 ≤ Open.pRank 2 L → IsTwoAlt ↥L 9 →
      (L = ⊤ ∧ IsTwoAlt ↥L 9 ∧ IsTwoAlt ↥H₀ 8) ∧ IsCyclic ↥(center ↥(T : Subgroup H))

theorem eq_of_involution_mem_centralizer {t : H} (htc : t ∈ center H) (ht2 : orderOf t = 2)
    {L : Subgroup H} (hrk : Open.pRank 2 (centralizer (L : Set H)) = 1) {z : H}
    (hzC : z ∈ centralizer (L : Set H)) (hz2 : orderOf z = 2) : z = t := by
  by_contra hne
  have hz2' : z * z = 1 := mul_self_eq_one_of_orderOf_two hz2
  have ht2' : t * t = 1 := mul_self_eq_one_of_orderOf_two ht2
  have hz1 : z ≠ 1 := by
    intro h1; rw [h1, orderOf_one] at hz2; omega
  have hcomm : z * t = t * z := Subgroup.mem_center_iff.mp htc z
  have hnot : t ∉ zpowers z := by
    intro hmem
    rcases LemmaYAux.eq_one_or_eq_of_mem_zpowers hz2' hmem with h1 | h1
    · rw [h1, orderOf_one] at ht2; omega
    · exact hne h1.symm
  obtain ⟨hel, hcard⟩ := SU1.isElemAbelian_card_sup_zpowers Nat.prime_two (a := z) (y := t)
    (by rw [pow_two]; exact hz2') (by rw [pow_two]; exact ht2') hz1 hnot hcomm
  have hle : zpowers z ⊔ zpowers t ≤ centralizer (L : Set H) := by
    refine sup_le (Subgroup.zpowers_le.mpr hzC) (Subgroup.zpowers_le.mpr ?_)
    exact Subgroup.mem_centralizer_iff.mpr fun l _ => Subgroup.mem_center_iff.mp htc l
  have := SU1.le_pRank (p := 2) (by norm_num) hle hel (k := 2) (by simp [hcard])
  omega

section Sz8

variable {T : Sylow 2 H} {H₀ : Subgroup H}

theorem central_involution_mem_component {t : H} (htc : t ∈ center H) (ht2 : orderOf t = 2)
    {L : Subgroup H} (hZp : IsPGroup 2 ↥(center ↥L)) (hZne : center ↥L ≠ ⊥)
    (hrk : Open.pRank 2 (centralizer (L : Set H)) = 1) : t ∈ L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdvd : 2 ∣ Nat.card ↥(center ↥L) := by
    rcases hZp.card_eq_or_dvd with h1 | h1
    · exact absurd (Subgroup.card_eq_one.mp h1) hZne
    · exact h1
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥(center ↥L)) 2 hdvd
  have hzo : orderOf (((z : ↥L)) : H) = 2 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]; exact hz
  have hzC : (((z : ↥L)) : H) ∈ centralizer (L : Set H) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp z.2 ⟨l, hl⟩)
  have := eq_of_involution_mem_centralizer htc ht2 hrk hzC hzo
  rw [← this]
  exact (z : ↥L).2

theorem Cfg.ki6A_sz8
    (h : Cfg H T H₀) {L : Subgroup H} (hL : IsComponent L)
    (hrank : 2 ≤ Open.pRank 2 L) (hcard2 : Nat.card (center ↥L) = 2)
    (e : (↥L ⧸ center ↥L) ≃* CFSG.Theory.Comparator.SzModel 1) :
    (IsTwoSz8 ↥L ∧ L ⊔ centralizer (L : Set H) = ⊤ ∧
      Subgroup.closure {g : H | g ∈ (T : Subgroup H) ∧ g * g = 1} ≤ L) ∧
      IsCyclic ↥(center ↥(T : Subgroup H)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hLn, -, -, hrk, TL, hTL, -, -⟩ := h.rank2_component hL hrank
  have := hLn
  obtain ⟨t, htc, ht2⟩ := exists_central_involution h.odd h.cen
  have hZp := h.isPGroup_center_component hL
  have hZne : center ↥L ≠ ⊥ := by
    intro hc; rw [hc] at hcard2; simp at hcard2
  have htL := central_involution_mem_component htc ht2 hZp hZne hrk
  obtain ⟨-, hc2, -, hc4, hc5, -⟩ := CFSG.GH74.KGroups.KI5D.ki5 ↥L hL.1 hZp hZne ⟨e⟩
  have hsup : L ⊔ centralizer (L : Set H) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨g, hg⟩ := hc4 hcard2 (MulAut.conjNormal x : MulAut ↥L)
    have hxg : (g : H)⁻¹ * x ∈ centralizer (L : Set H) := by
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have h2 : x * l * x⁻¹ = (g : H) * l * (g : H)⁻¹ := by
        have := congrArg (fun φ : MulAut ↥L => ((φ ⟨l, hl⟩ : ↥L) : H)) hg
        simpa [MulAut.conjNormal_apply, MulAut.conj_apply] using this
      calc l * ((g : H)⁻¹ * x) = (g : H)⁻¹ * ((g : H) * l * (g : H)⁻¹) * x := by group
        _ = (g : H)⁻¹ * (x * l * x⁻¹) * x := by rw [h2]
        _ = ((g : H)⁻¹ * x) * l := by group
    have hx : x = (g : H) * ((g : H)⁻¹ * x) := by group
    rw [hx]
    exact Subgroup.mul_mem_sup g.2 hxg
  have hinv : ∀ u : H, u * u = 1 → u ∈ L := by
    intro u hu2
    have huLC : u ∈ L ⊔ centralizer (L : Set H) := by rw [hsup]; exact Subgroup.mem_top u
    obtain ⟨l, hl, c, hc, hlc⟩ := SU1.mem_sup_of_commute
      (fun a ha b hb => Subgroup.mem_centralizer_iff.mp hb a ha) huLC
    have hcl : c * l = l * c := (Subgroup.mem_centralizer_iff.mp hc l hl).symm
    have hll : (l * l) * (c * c) = 1 := by
      calc (l * l) * (c * c) = l * (l * c) * c := by group
        _ = l * (c * l) * c := by rw [← hcl]
        _ = (l * c) * (l * c) := by group
        _ = 1 := by rw [hlc]; exact hu2
    have hl2C : l * l ∈ centralizer (L : Set H) := by
      have : l * l = (c * c)⁻¹ := eq_inv_of_mul_eq_one_left hll
      rw [this]
      exact Subgroup.inv_mem _ (Subgroup.mul_mem _ hc hc)
    let l' : ↥L := ⟨l, hl⟩
    have hl2Z : l' ^ 2 ∈ center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      have := Subgroup.mem_centralizer_iff.mp hl2C (y : H) y.2
      simpa [pow_two, l'] using this
    have hl'p : IsPGroup 2 ↥(Subgroup.zpowers l') := by
      obtain ⟨n, hn⟩ := hZp ⟨l' ^ 2, hl2Z⟩
      have hn' : (l' ^ 2) ^ 2 ^ n = 1 := by
        have := congrArg Subtype.val hn
        exact this
      have hl'n : l' ^ 2 ^ (n + 1) = 1 := by rw [pow_succ', pow_mul]; exact hn'
      rintro ⟨x, hx⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      refine ⟨n + 1, ?_⟩
      apply Subtype.ext
      change (l' ^ k) ^ 2 ^ (n + 1) = 1
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hl'n, one_zpow]
    obtain ⟨P, hP⟩ := hl'p.exists_le_sylow
    have hl'2 : l' ^ 2 = 1 := hc5 P l' (hP (Subgroup.mem_zpowers l')) hl2Z
    have hll1 : l * l = 1 := by
      have := congrArg Subtype.val hl'2
      simpa [pow_two, l'] using this
    have hcc : c * c = 1 := by rwa [hll1, one_mul] at hll
    by_cases hc1 : c = 1
    · rw [← hlc, hc1, mul_one]; exact hl
    · have hc2' : orderOf c = 2 := orderOf_eq_prime (by rw [pow_two]; exact hcc) hc1
      have hct := eq_of_involution_mem_centralizer htc ht2 hrk hc hc2'
      rw [← hlc, hct]
      exact L.mul_mem hl htL
  refine ⟨⟨⟨hL.1, inferInstance, hcard2, ⟨e⟩⟩, hsup, ?_⟩, ?_⟩
  · rw [Subgroup.closure_le]
    rintro g ⟨-, hg2⟩
    exact hinv g hg2
  · have hTp : IsPGroup 2 ↥(T : Subgroup H) := T.isPGroup'
    have hCp : IsPGroup 2 ↥(center ↥(T : Subgroup H)) := hTp.to_subgroup _
    obtain ⟨m, hm⟩ := hCp.exists_card_eq
    have key : ∀ w : ↥(center ↥(T : Subgroup H)), orderOf w = 2 →
        (((w : ↥(T : Subgroup H)) : ↥(T : Subgroup H)) : H) = t := by
      intro w hw
      have hzo : orderOf (((w : ↥(T : Subgroup H)) : ↥(T : Subgroup H)) : H) = 2 := by
        rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]; exact hw
      have hz2 : (((w : ↥(T : Subgroup H)) : ↥(T : Subgroup H)) : H) *
          (((w : ↥(T : Subgroup H)) : ↥(T : Subgroup H)) : H) = 1 :=
        mul_self_eq_one_of_orderOf_two hzo
      set z : H := (((w : ↥(T : Subgroup H)) : ↥(T : Subgroup H)) : H) with hz
      have hzL : z ∈ L := hinv z hz2
      have hzT : z ∈ (T : Subgroup H) := (w : ↥(T : Subgroup H)).2
      have hzcT : ∀ y ∈ (T : Subgroup H), y * z = z * y := fun y hy => by
        have := Subgroup.mem_center_iff.mp w.2 ⟨y, hy⟩
        exact congrArg Subtype.val this
      have hzTL : (⟨z, hzL⟩ : ↥L) ∈ (TL : Subgroup ↥L) := by
        have hmem : z ∈ (T : Subgroup H) ⊓ L := ⟨hzT, hzL⟩
        rw [← hTL] at hmem
        obtain ⟨y, hy, hyz⟩ := hmem
        have hyeq : y = ⟨z, hzL⟩ := Subtype.ext hyz
        rwa [hyeq] at hy
      have hw' : (⟨(⟨z, hzL⟩ : ↥L), hzTL⟩ : ↥(TL : Subgroup ↥L)) ∈
          center ↥(TL : Subgroup ↥L) := by
        rw [Subgroup.mem_center_iff]
        intro y
        apply Subtype.ext
        apply Subtype.ext
        have hyT : ((y : ↥L) : H) ∈ (T : Subgroup H) := by
          have hmem : ((y : ↥L) : H) ∈ (T : Subgroup H) ⊓ L := by
            rw [← hTL]; exact ⟨(y : ↥L), y.2, rfl⟩
          exact hmem.1
        exact hzcT _ hyT
      have hw'' : (⟨(⟨z, hzL⟩ : ↥L), hzTL⟩ : ↥(TL : Subgroup ↥L)) ∈
          (center ↥L).subgroupOf (TL : Subgroup ↥L) := by
        rw [← hc2 TL]; exact hw'
      have hzZ : (⟨z, hzL⟩ : ↥L) ∈ center ↥L := Subgroup.mem_subgroupOf.mp hw''
      have hzC : z ∈ centralizer (L : Set H) := by
        rw [Subgroup.mem_centralizer_iff]
        intro l hl
        exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hzZ ⟨l, hl⟩)
      exact eq_of_involution_mem_centralizer htc ht2 hrk hzC hzo
    let : CommGroup ↥(center ↥(T : Subgroup H)) :=
      { (inferInstance : Group ↥(center ↥(T : Subgroup H))) with
        mul_comm := fun a b => Subtype.ext (Subgroup.mem_center_iff.mp b.2 a) }
    exact
      CFSG.TwoRankLowerBound.Helpers.abelian_two_group_cyclic_of_unique_involution_of_card_eq_pow
      m _ hCp hm
      (fun left right hleft hright =>
        Subtype.ext (Subtype.ext ((key left hleft).trans (key right hright).symm)))

end Sz8

theorem ki6A_of
    (hQ : CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleProperCoreClassification)
    (hZ4 : KI6Z4) (hA9 : KI6TwoA9) : KI6A := by
  intro H _ _ T H₀ h L hL hrank hns
  obtain ⟨hLn, -, -, hrk, TL, hTL, hΓL, hDlt⟩ := h.rank2_component hL hrank
  have := hLn
  have hZp := h.isPGroup_center_component hL
  have hZne : center ↥L ≠ ⊥ := by
    intro hcen
    apply hns
    let e : (↥L ⧸ center ↥L) ≃* ↥L :=
      (QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot
    have := hL.1.2.1
    exact e.symm.isSimpleGroup
  obtain ⟨k, hk⟩ := hZp.exists_card_eq
  by_cases hk1 : k = 1
  · have hcard2 : Nat.card (center ↥L) = 2 := by rw [hk, hk1, pow_one]
    have hrankL : 2 ≤ Open.twoRank ↥L := by
      have h1 := SU4.pRank_map_of_injective L.subtype L.subtype_injective (⊤ : Subgroup ↥L)
      have h2 : (⊤ : Subgroup ↥L).map L.subtype = L := by
        rw [Subgroup.map_top]; exact Subgroup.range_subtype _
      rw [h2] at h1
      unfold Open.twoRank
      omega
    have hTLle : (TL : Subgroup ↥L) ≤ H₀.subgroupOf L := by
      intro x hx
      have hx' : (x : H) ∈ (T : Subgroup H) ⊓ L := by rw [← hTL]; exact ⟨x, hx, rfl⟩
      exact Subgroup.mem_subgroupOf.mpr (h.sylow_le hx'.1)
    rcases hQ ↥L hL.1.1 hL.1.2.1 hcard2 hrankL TL (H₀.subgroupOf L) hTLle hDlt.ne hΓL with
      ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · obtain ⟨hc, hcyc⟩ := hA9 H T H₀ h L hL hrank ⟨hL.1, inferInstance, hcard2, ⟨e⟩⟩
      exact ⟨Or.inl hc, hcyc⟩
    · obtain ⟨hd, hcyc⟩ := h.ki6A_sz8 hL hrank hcard2 e
      exact ⟨Or.inr hd, hcyc⟩
  · exfalso
    refine hZ4 H T H₀ h L hL hrank ?_
    have hk2 : 2 ≤ k := by
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · rw [h0, pow_zero] at hk; exact absurd (Subgroup.card_eq_one.mp hk) hZne
      · omega
    rw [hk]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2

end CFSG.GH74.Uniqueness.SU.K.R6
