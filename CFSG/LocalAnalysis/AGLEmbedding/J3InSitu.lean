module

public import CFSG.LocalAnalysis.AGLEmbedding.J3Facts
import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeKillAux
import CFSG.LocalAnalysis.AGLEmbedding.OneLieReduced

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.PreuniquenessRankFour.Helpers
open CFSG.ComponentClassification.OuterAutomorphisms

section Helpers

variable {Y : Type} [Group Y] [Finite Y]

omit [Finite Y] in
theorem sq_mem_of_card_outer_le_two {K : Subgroup Y} [K.Normal] [Finite (Outer K)]
    (hOut : Nat.card (Outer K) ≤ 2) (hC : Subgroup.centralizer (K : Set Y) = ⊥) (y : Y) :
    y ^ 2 ∈ K := by
  have h1 : QuotientGroup.mk' (inner K) (MulAut.conjNormal (y ^ 2)) = 1 := by
    have hc := pow_card_eq_one' (x := QuotientGroup.mk' (inner K) (MulAut.conjNormal y))
    rw [map_pow, map_pow]
    rcases (by have := Nat.card_pos (α := Outer K); omega :
        Nat.card (Outer K) = 1 ∨ Nat.card (Outer K) = 2) with h | h
    · rw [h, pow_one] at hc
      rw [hc, one_pow]
    · rwa [h] at hc
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  obtain ⟨k, hk⟩ := (show MulAut.conjNormal (y ^ 2) ∈ (MulAut.conj : K →* MulAut K).range from h1)
  have hmem := inv_mul_mem_centralizer_of_conjNormal_eq hk.symm
  rw [hC, Subgroup.mem_bot, inv_mul_eq_one] at hmem
  exact hmem ▸ k.2

omit [Finite Y] in
theorem isPGroup_zpowers_of_pow_prime_pow_eq_one {p n : ℕ} {x : Y} (hx : x ^ p ^ n = 1) :
    IsPGroup p (Subgroup.zpowers x) := by
  rintro ⟨_, k, rfl⟩
  refine ⟨n, Subtype.ext ?_⟩
  change (x ^ k) ^ p ^ n = 1
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]

omit [Finite Y] in
theorem mem_of_mem_normalizer_of_pow_eq_one {p n : ℕ} (T : Sylow p Y) {x : Y}
    (hxN : x ∈ Subgroup.normalizer ((T : Subgroup Y) : Set Y)) (hx : x ^ p ^ n = 1) :
    x ∈ (T : Subgroup Y) := by
  have h : Subgroup.zpowers x ⊓ Subgroup.normalizer ((T : Subgroup Y) : Set Y) =
      Subgroup.zpowers x ⊓ (T : Subgroup Y) :=
    IsPGroup.inf_normalizer_sylow (isPGroup_zpowers_of_pow_prime_pow_eq_one hx) T
  have hmem : x ∈ Subgroup.zpowers x ⊓ Subgroup.normalizer ((T : Subgroup Y) : Set Y) :=
    ⟨Subgroup.mem_zpowers x, hxN⟩
  rw [h] at hmem
  exact hmem.2

end Helpers

theorem j3InSitu_of (hS : KFactJ3Sylow) (hO : KFactJ3OuterInvolution) (hOR : KFactJ3OuterRank)
    {Y : Type} [Group Y] [Finite Y] {K : Subgroup Y} (hKn : K.Normal)
    (hK : Nonempty (K ≃* (TauCeti.CFSGIndex.sporadic .J3).Group))
    (hC : Subgroup.centralizer (K : Set Y) = ⊥) (T : Sylow 3 Y) {Y₀ : Subgroup Y}
    (hY₀ : Subgroup.normalizer ((T : Subgroup Y) : Set Y) ≤ Y₀) (hne : Y₀ ≠ ⊤) :
    J3InSitu (T : Subgroup Y) Y₀ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite (MulAut K) := MulEquiv.finite_left
  obtain ⟨hOut2, hrank⟩ := hOR K hK
  have hOut3 : ¬ 3 ∣ Nat.card (Outer K) := fun hd => by
    have := Nat.le_of_dvd Nat.card_pos hd
    omega
  have h3K : ∀ x : Y, ∀ n : ℕ, x ^ 3 ^ n = 1 → x ∈ K := fun x n hx => by
    have := mem_sup_centralizer_of_pow Nat.prime_three hOut3 hx
    rwa [hC, sup_bot_eq] at this
  have hsq : ∀ y : Y, y ^ 2 ∈ K := sq_mem_of_card_outer_le_two hOut2 hC
  set T' : Subgroup Y := (T : Subgroup Y)
  have hTK : T' ≤ K := fun t ht => by
    obtain ⟨n, hn⟩ := T.isPGroup' ⟨t, ht⟩
    exact h3K t n (by simpa using congrArg Subtype.val hn)
  have hF : J3SylowFacts K (T'.subgroupOf K) := by
    have h := hS K hK (T.subtype hTK)
    rwa [Sylow.coe_subtype] at h
  have hZmap : (centerOf (T'.subgroupOf K)).map K.subtype = centerOf T' := by
    rw [map_subtype_centerOf, Subgroup.map_subgroupOf_eq_of_le hTK]
  have hZK : centerOf T' ≤ K := inf_le_left.trans hTK
  have hmemZ : ∀ z : K, z ∈ centerOf (T'.subgroupOf K) → (z : Y) ∈ centerOf T' := fun z hz =>
    hZmap ▸ Subgroup.mem_map_of_mem K.subtype hz
  have hNK : ∀ k : K, k ∈ Subgroup.normalizer ((T'.subgroupOf K : Subgroup K) : Set K) ↔
      (k : Y) ∈ Subgroup.normalizer (T' : Set Y) := fun k => by
    rw [← Subgroup.subgroupOf_normalizer_eq hTK, Subgroup.mem_subgroupOf]
  have hY0K : Y₀.subgroupOf K = Subgroup.normalizer ((T'.subgroupOf K : Subgroup K) : Set K) := by
    rcases hF.maximal (Y₀.subgroupOf K) (fun k hk =>
        Subgroup.mem_subgroupOf.mpr (hY₀ ((hNK k).mp hk))) with h | h
    · exact h
    · refine absurd ?_ hne
      have hKY : K ≤ Y₀ := fun k hk => by
        have : (⟨k, hk⟩ : K) ∈ Y₀.subgroupOf K := h ▸ Subgroup.mem_top _
        exact Subgroup.mem_subgroupOf.mp this
      rw [eq_top_iff, ← Sylow.normalizer_sup_eq_top' (N := K) T hTK]
      exact sup_le hY₀ hKY
  have hle : Y₀ ≤ Subgroup.normalizer (T' : Set Y) := by
    have key : ∀ y ∈ Y₀, ∀ t ∈ T', y * t * y⁻¹ ∈ T' := by
      intro y hy t ht
      have htY : t ∈ Y₀ := hY₀ (Subgroup.le_normalizer ht)
      have hmK : y * t * y⁻¹ ∈ K := hKn.conj_mem t (hTK ht) y
      have hmN : y * t * y⁻¹ ∈ Subgroup.normalizer (T' : Set Y) := by
        have : (⟨_, hmK⟩ : K) ∈ Y₀.subgroupOf K :=
          Subgroup.mem_subgroupOf.mpr (Y₀.mul_mem (Y₀.mul_mem hy htY) (Y₀.inv_mem hy))
        rw [hY0K] at this
        exact (hNK _).mp this
      obtain ⟨n, hn⟩ := T.isPGroup' ⟨t, ht⟩
      have hp : (y * t * y⁻¹) ^ 3 ^ n = 1 := by
        rw [conj_pow, show t ^ 3 ^ n = 1 by simpa using congrArg Subtype.val hn, mul_one,
          mul_inv_cancel]
      exact mem_of_mem_normalizer_of_pow_eq_one T hmN hp
    exact le_normalizer_of_forall_mul_mul_inv_mem key
  have hCK : ∀ c ∈ Subgroup.centralizer (centerOf T' : Set Y), c ∈ K → c ∈ T' := by
    intro c hc hcK
    have hc' : (⟨c, hcK⟩ : K) ∈ Subgroup.centralizer (centerOf (T'.subgroupOf K) : Set K) := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hc _ (hmemZ z hz))
    exact Subgroup.mem_subgroupOf.mp (hF.centralizer_center hc')
  refine ⟨hle, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro c hc
    by_cases hcK : c ∈ K
    · exact hCK c hc hcK
    exfalso
    have hc2 : c ^ 2 ∈ T' := hCK _ (Subgroup.pow_mem _ hc 2) (hsq c)
    obtain ⟨a, ha⟩ := T.isPGroup' ⟨c ^ 2, hc2⟩
    have ha' : (c ^ 2) ^ 3 ^ a = 1 := by simpa using congrArg Subtype.val ha
    set w := c ^ 3 ^ a with hw
    have hw2 : w ^ 2 = 1 := by rw [hw, ← pow_mul, mul_comm, pow_mul, ha']
    have hwC : w ∈ Subgroup.centralizer (centerOf T' : Set Y) := Subgroup.pow_mem _ hc _
    have hwK : w ∉ K := by
      intro hwK
      apply hcK
      obtain ⟨j, hj⟩ : Odd (3 ^ a) := Odd.pow (by decide)
      have e : c = w * ((c ^ 2) ^ j)⁻¹ := by
        rw [hw, hj, pow_succ, ← pow_mul, mul_comm 2 j]
        group
      rw [e]
      exact K.mul_mem hwK (K.inv_mem (K.pow_mem (hsq c) j))
    have hα2 : (MulAut.conjNormal w : MulAut K) ^ 2 = 1 := by rw [← map_pow, hw2, map_one]
    have hαout : (MulAut.conjNormal w : MulAut K) ∉ (MulAut.conj : K →* MulAut K).range := by
      rintro ⟨k, hk⟩
      have hmem := inv_mul_mem_centralizer_of_conjNormal_eq hk.symm
      rw [hC, Subgroup.mem_bot, inv_mul_eq_one] at hmem
      exact hwK (hmem ▸ k.2)
    obtain ⟨x, hx, hxα⟩ := hO K hK _ hα2 hαout (centerOf (T'.subgroupOf K)) hF.center_elem.1
      hF.center_elem.2
    apply hxα
    apply Subtype.ext
    rw [MulAut.conjNormal_apply, ← Subgroup.mem_centralizer_iff.mp hwC _ (hmemZ x hx)]
    group
  ·
    intro W hW hY₀W
    have hWK : W ≤ K := hW.trans hZK
    have hWZ : W.subgroupOf K ≤ centerOf (T'.subgroupOf K) := by
      intro k hk
      have hkZ : (k : Y) ∈ centerOf T' := hW (Subgroup.mem_subgroupOf.mp hk)
      rw [← hZmap] at hkZ
      exact (Subgroup.mem_map_iff_mem K.subtype_injective).mp hkZ
    have hN : Subgroup.normalizer ((T'.subgroupOf K : Subgroup K) : Set K) ≤
        Subgroup.normalizer ((W.subgroupOf K : Subgroup K) : Set K) := by
      rw [← Subgroup.subgroupOf_normalizer_eq hTK, ← Subgroup.subgroupOf_normalizer_eq hWK]
      exact Subgroup.subgroupOf_mono K (hY₀.trans hY₀W)
    rcases hF.center_irreducible _ hWZ hN with h | h
    · left
      rw [← Subgroup.map_subgroupOf_eq_of_le hWK, h, Subgroup.map_bot]
    · right
      rw [← Subgroup.map_subgroupOf_eq_of_le hWK, h, hZmap]
  ·
    obtain ⟨a, ha, b, hb, hab⟩ := hF.nonabelian
    exact ⟨a, Subgroup.mem_subgroupOf.mp ha, b, Subgroup.mem_subgroupOf.mp hb,
      fun h => hab (Subtype.ext (by simpa using h))⟩
  ·
    obtain ⟨E, -, hE, hEcard⟩ := pRank_attained 3 Nat.prime_three (⊤ : Subgroup Y)
    have hEK : E ≤ K := fun x hx => h3K x 1 (by rw [pow_one]; exact hE.2 x hx)
    have h1 : Open.pRank 3 (⊤ : Subgroup Y) ≤ Open.pRank 3 K :=
      le_csSup (pRank_bddAbove 3 Nat.prime_three K) ⟨E, hEK, hE, hEcard⟩
    have h2 : Open.pRank 3 K = Open.pRank 3 (⊤ : Subgroup K) := by
      rw [← pRank_map_of_injective 3 Nat.prime_three K.subtype K.subtype_injective,
        ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    omega
  ·
    obtain ⟨s, hsN, hs2, hsW⟩ := hF.singer
    have hsY : (s : Y) ∈ Subgroup.normalizer (T' : Set Y) := (hNK s).mp hsN
    refine ⟨s, ⟨hY₀ hsY, hsY⟩, ?_, ?_⟩
    · have h := hs2.map K.subtype
      rwa [MonoidHom.map_zpowers] at h
    · intro W hWT hWidx hsW'
      have hWK : W ≤ K := hWT.trans hTK
      refine hsW (W.subgroupOf K) (Subgroup.subgroupOf_mono K hWT)
        (by rw [Subgroup.relIndex_subgroupOf hTK]; exact hWidx) ?_
      rw [← Subgroup.subgroupOf_normalizer_eq hWK, Subgroup.mem_subgroupOf]
      simpa using hsW'
  ·
    intro y hy
    have hy2 : (⟨y ^ 2, hsq y⟩ : K) ∈
        Subgroup.normalizer ((T'.subgroupOf K : Subgroup K) : Set K) := by
      rw [← hY0K]
      exact Subgroup.mem_subgroupOf.mpr (Y₀.pow_mem hy 2)
    obtain ⟨e, he⟩ := hF.two_top _ hy2
    refine ⟨e + 1, ?_⟩
    have h := Subgroup.mem_subgroupOf.mp he
    rw [pow_succ', pow_mul]
    simpa using h

section Consequences

variable {Y : Type} [Group Y] [Finite Y] {T Y₀ : Subgroup Y}

omit [Finite Y] in
theorem conj_mem_centerOf_of_mem_normalizer {y z : Y}
    (hy : y ∈ Subgroup.normalizer (T : Set Y)) (hz : z ∈ centerOf T) :
    y * z * y⁻¹ ∈ centerOf T := by
  refine ⟨(Subgroup.mem_normalizer_iff.mp hy z).mp hz.1,
    Subgroup.mem_centralizer_iff.mpr fun t ht => ?_⟩
  have ht' : y⁻¹ * t * y ∈ T := by
    simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hy) t).mp ht
  have hc := Subgroup.mem_centralizer_iff.mp hz.2 _ ht'
  calc t * (y * z * y⁻¹) = y * ((y⁻¹ * t * y) * z) * y⁻¹ := by group
    _ = y * (z * (y⁻¹ * t * y)) * y⁻¹ := by rw [hc]
    _ = y * z * y⁻¹ * t := by group

theorem J3InSitu.centerOf_ne_bot (h : J3InSitu T Y₀) (hT : T ≠ ⊤) : centerOf T ≠ ⊥ := by
  intro hZ
  refine hT (eq_top_iff.mpr fun y _ => h.centralizer_center ?_)
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  rw [hZ, SetLike.mem_coe, Subgroup.mem_bot] at hz
  rw [hz, one_mul, mul_one]

theorem J3InSitu.eq_bot_or_le (h : J3InSitu T Y₀) (hT : IsPGroup 3 T) (hTY : T ≤ Y₀)
    {W : Subgroup Y} (hW : W ≤ Y₀) (hWn : Y₀ ≤ Subgroup.normalizer (W : Set Y)) :
    W = ⊥ ∨ centerOf T ≤ W := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZn : Y₀ ≤ Subgroup.normalizer (centerOf T : Set Y) :=
    le_normalizer_of_forall_mul_mul_inv_mem fun y hy _ hz =>
      conj_mem_centerOf_of_mem_normalizer (h.le_normalizer hy) hz
  have hVn : Y₀ ≤ Subgroup.normalizer ((W ⊓ centerOf T : Subgroup Y) : Set Y) :=
    le_normalizer_of_forall_mul_mul_inv_mem fun y hy v hv =>
      ⟨(Subgroup.mem_normalizer_iff.mp (hWn hy) v).mp hv.1,
        (Subgroup.mem_normalizer_iff.mp (hZn hy) v).mp hv.2⟩
  rcases h.center_irreducible _ inf_le_right hVn with hV | hV
  · left
    have hWC : W ≤ Subgroup.centralizer (centerOf T : Set Y) := by
      intro w hw
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      have h1 : w * z * w⁻¹ * z⁻¹ ∈ W ⊓ centerOf T := by
        refine ⟨?_, (centerOf T).mul_mem
          ((Subgroup.mem_normalizer_iff.mp (hZn (hW hw)) z).mp hz) ((centerOf T).inv_mem hz)⟩
        have : z * w⁻¹ * z⁻¹ ∈ W :=
          (Subgroup.mem_normalizer_iff.mp (hWn (hTY hz.1)) _).mp (W.inv_mem hw)
        simpa [mul_assoc] using W.mul_mem hw this
      rw [hV, Subgroup.mem_bot] at h1
      calc z * w = (w * z * w⁻¹ * z⁻¹)⁻¹ * (w * z) := by group
        _ = w * z := by rw [h1, inv_one, one_mul]
    have hWT : W ≤ T := hWC.trans h.centralizer_center
    by_contra hne
    have : Group.IsNilpotent T := hT.isNilpotent
    have : (W.subgroupOf T).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hWT).mpr (hTY.trans hWn)
    have hW1 : W.subgroupOf T ≠ ⊥ := by
      intro h0
      apply hne
      rw [← Subgroup.map_subgroupOf_eq_of_le hWT, h0, Subgroup.map_bot]
    obtain ⟨⟨z, hzW, hzZ⟩, hz1⟩ :=
      Subgroup.ne_bot_iff_exists_ne_one.mp (Group.IsNilpotent.inf_center_ne_bot_of_normal hW1)
    have hz : (z : Y) ∈ W ⊓ centerOf T := ⟨Subgroup.mem_subgroupOf.mp hzW, z.2,
      Subgroup.mem_centralizer_iff.mpr fun t ht =>
        congrArg Subtype.val (Subgroup.mem_center_iff.mp hzZ ⟨t, ht⟩)⟩
    rw [hV, Subgroup.mem_bot] at hz
    exact hz1 (Subtype.ext (Subtype.ext hz))
  · right
    rw [← hV]
    exact inf_le_left

end Consequences

end CFSG.AGLEmbedding
