module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.Sec217ThetaOne
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.Sec217Invariant
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J3FrameExists
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.I417Gen
import CFSG.RankThree.PartTwo.Sec13.Item13Res5ProofCenter

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open Subgroup CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec21 CFSG.Blueprint

theorem isElemAbelian_mono {G : Type*} [Group G] {A B : Subgroup G}
    (h : CFSG.Assembly.IsElemAbelian 3 B) (hAB : A ≤ B) : CFSG.Assembly.IsElemAbelian 3 A := by
  rw [isElemAbelian_iff] at h ⊢
  exact ⟨fun a ha b hb => h.1 a (hAB ha) b (hAB hb), fun a ha => h.2 a (hAB ha)⟩

theorem isElemAbelian_zpowers {G : Type*} [Group G] {g : G} (h : g ^ 3 = 1) :
    CFSG.Assembly.IsElemAbelian 3 (zpowers g) := by
  rw [isElemAbelian_iff]
  refine ⟨?_, ?_⟩
  · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact (Commute.zpow_zpow_self g i j).eq
  · rintro _ ⟨i, rfl⟩
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h, one_zpow]

theorem isElemAbelian_card_eq_pow {G : Type*} [Group G] [Finite G] {E : Subgroup G}
    (h : CFSG.Assembly.IsElemAbelian 3 E) : ∃ k : ℕ, Nat.card E = 3 ^ k := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : IsPGroup 3 E := fun g => ⟨1, Subtype.ext (by simpa using (isElemAbelian_iff.1 h).2 g g.2)⟩
  exact IsPGroup.iff_card.1 hp

theorem mem_zpowers_of_pow_three {G : Type*} [Group G] {g x : G} (hg : g ^ 3 = 1)
    (hx : x ∈ zpowers g) : x = 1 ∨ x = g ∨ x = g ^ 2 := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  have hk : k = k % 3 + 3 * (k / 3) := by omega
  have h3m : g ^ (3 * (k / 3)) = 1 := by rw [zpow_mul, zpow_ofNat, hg, one_zpow]
  have hgk : g ^ k = g ^ (k % 3) := by
    conv_lhs => rw [hk]
    rw [zpow_add, h3m, mul_one]
  have hr : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rw [hgk]
  rcases hr with h | h | h <;> rw [h]
  · left; simp
  · right; left; simp
  · right; right; simp

open CFSG.ComponentClassification.OuterAutomorphisms (Outer) in
theorem inner_of_pow_three_generic {X : Type} [Group X] (hp : Group.IsPerfect X)
    {Y : Type} [Group Y] (e : X ⧸ center X ≃* Y) (hY : ¬ 3 ∣ Nat.card (Outer Y)) (σ : MulAut X)
    (hσ : σ ^ 3 = 1) : ∃ k : X, σ = MulAut.conj k := by
  obtain ⟨k, hk⟩ := Sec13.Res5Proof.mem_range_conj_of_not_three_dvd_outer hp e hY hσ
  exact ⟨k, hk.symm⟩

section J3Outer


set_option linter.unusedSectionVars false

open CFSG.ComponentClassification.OuterAutomorphisms (Outer) in
theorem not_three_dvd_outer_J3 : ¬ 3 ∣ Nat.card (Outer NativeSporadic.J3) := by
  have : Finite NativeSporadic.J3 := (CFSG.Sporadic.J3.fam_j3_simplicity).1
  have : Finite (Outer NativeSporadic.J3) := Sec13.Res5Proof.finite_outer _
  exact Sec13.Res5Proof.not_three_dvd_of_card_le_two Sec4.card_outer_J3

theorem inner_of_pow_three_J3 {X : Type} [Group X] (hp : Group.IsPerfect X)
    (e : X ⧸ center X ≃* NativeSporadic.J3) (σ : MulAut X) (hσ : σ ^ 3 = 1) :
    ∃ k : X, σ = MulAut.conj k := by
  have e' : X ⧸ center X ≃* NativeSporadic.Carrier .J3 := e
  have hY : ¬ 3 ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer
    (NativeSporadic.Carrier .J3)) := not_three_dvd_outer_J3
  exact inner_of_pow_three_generic hp e' hY σ hσ

end J3Outer

section Main

variable {G : Type} [Group G] [Finite G]


set_option linter.unusedSectionVars false

set_option maxRecDepth 20000 in
theorem Cover217.false_of_big_kernel {A E U : Subgroup G} {c : G} {L : Subgroup G}
    (h : Cover217 A E U c L) (hθ : aschbacherSolvableCore 3 L = ⊥)
    (Dg : Subgroup G) (hDA : Dg ≤ A) (hDC : ∀ d ∈ Dg, ∀ x ∈ L, d * x = x * d)
    (hD9 : 9 ≤ Nat.card Dg) : False := by
  obtain ⟨hq, hZ3⟩ := h.quasi_card_center hθ
  obtain ⟨e⟩ := h.quot
  obtain ⟨a, y, W, ha, ha3, hy3, hy1, hay, hyD, hW0, hW2, haW, hyN⟩ :=
    exists_local_frame_cover hq hZ3 e
  set aG : G := (a : G) with haG
  set yG : G := (y : G) with hyG
  have haG3 : aG ^ 3 = 1 := by have := congrArg Subtype.val ha3; simpa using this
  have hyG3 : yG ^ 3 = 1 := by have := congrArg Subtype.val hy3; simpa using this
  have haG1 : aG ≠ 1 := by
    intro h1
    apply ha
    have : a = 1 := Subtype.ext h1
    rw [this]; exact one_mem _
  have hyG1 : yG ≠ 1 := fun h1 => hy1 (Subtype.ext h1)
  have hDa : ∀ d ∈ Dg, d * aG = aG * d := fun d hd => hDC d hd aG a.2
  have hDy : ∀ d ∈ Dg, d * yG = yG * d := fun d hd => hDC d hd yG y.2
  have hay' : aG * yG = yG * aG := congrArg Subtype.val hay
  have hAe := h.isElemAbelian_A
  have hDe : CFSG.Assembly.IsElemAbelian 3 Dg := isElemAbelian_mono hAe hDA
  have hae : CFSG.Assembly.IsElemAbelian 3 (zpowers aG) := isElemAbelian_zpowers haG3
  have hye : CFSG.Assembly.IsElemAbelian 3 (zpowers yG) := isElemAbelian_zpowers hyG3
  have hcommz : ∀ {H : Subgroup G} {g : G}, H ≤ centralizer ({g} : Set G) →
      ∀ x ∈ H, ∀ b ∈ zpowers g, x * b = b * x := by
    intro H g hH x hx b hb
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    have : Commute x g := mem_centralizer_singleton_iff.1 (hH hx)
    exact (this.zpow_right i).eq
  have hDa_le : Dg ≤ centralizer ({aG} : Set G) := fun d hd =>
    mem_centralizer_singleton_iff.2 (hDa d hd)
  have hDy_le : Dg ≤ centralizer ({yG} : Set G) := fun d hd =>
    mem_centralizer_singleton_iff.2 (hDy d hd)
  have haz_y : zpowers aG ≤ centralizer ({yG} : Set G) := by
    rw [zpowers_le]; exact mem_centralizer_singleton_iff.2 hay'
  set R₁ : Subgroup G := Dg ⊔ zpowers aG with hR₁
  set R₂ : Subgroup G := R₁ ⊔ zpowers yG with hR₂
  have hR₁e : CFSG.Assembly.IsElemAbelian 3 R₁ :=
    isElemAbelian_sup_of_commute hDe hae (hcommz hDa_le)
  have hR₁y : R₁ ≤ centralizer ({yG} : Set G) := sup_le hDy_le haz_y
  have hR₂e : CFSG.Assembly.IsElemAbelian 3 R₂ :=
    isElemAbelian_sup_of_commute hR₁e hye (hcommz hR₁y)
  have hcenter : ∀ z : ↥L, (z : G) ∈ Dg → z ∈ center ↥L := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hDC z hz g g.2).symm
  have hord_a : orderOf aG = 3 := orderOf_eq_prime haG3 haG1
  have hord_y : orderOf yG = 3 := orderOf_eq_prime hyG3 hyG1
  have hdisj1 : Disjoint Dg (zpowers aG) := by
    rw [Subgroup.disjoint_def]
    intro x hxD hxa
    rcases mem_zpowers_of_pow_three haG3 hxa with h1 | h1 | h1
    · exact h1
    · exfalso
      rw [h1] at hxD
      exact ha (hcenter a hxD)
    · exfalso
      rw [h1] at hxD
      have h2 : (a ^ 2 : ↥L) ∈ center ↥L := hcenter (a ^ 2) (by simpa using hxD)
      apply ha
      have : a = (a ^ 2) ^ 2 := by
        have : (a ^ 2) ^ 2 = a ^ 3 * a := by group
        rw [this, ha3, one_mul]
      rw [this]; exact pow_mem h2 2
  have hcard1 : 3 * Nat.card Dg ≤ Nat.card R₁ := by
    have := card_mul_le_card_sup_of_disjoint Dg (zpowers aG) hdisj1
    rw [Nat.card_zpowers, hord_a] at this
    rw [hR₁]
    omega
  have hy_not_R₁ : yG ∉ R₁ := by
    intro hyR
    obtain ⟨d, hd, b, hb, hdb⟩ := (mem_sup_of_commute (hcommz hDa_le)).1 hyR
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    apply hyD
    have hdL : d ∈ L := by
      have : d = yG * (aG ^ i)⁻¹ := by rw [← hdb]; group
      rw [this]
      exact L.mul_mem y.2 (L.inv_mem (L.zpow_mem a.2 i))
    have hz : (⟨d, hdL⟩ : ↥L) ∈ center ↥L := hcenter _ hd
    have hy' : y = (⟨d, hdL⟩ : ↥L) * a ^ i := by
      apply Subtype.ext
      simpa using hdb.symm
    rw [hy']
    exact mul_mem (mem_sup_right hz) (mem_sup_left (zpow_mem_zpowers a i))
  have hdisj2 : Disjoint R₁ (zpowers yG) := by
    rw [Subgroup.disjoint_def]
    intro x hxR hxy
    rcases mem_zpowers_of_pow_three hyG3 hxy with h1 | h1 | h1
    · exact h1
    · exact absurd (h1 ▸ hxR) hy_not_R₁
    · exfalso
      rw [h1] at hxR
      apply hy_not_R₁
      have : yG = (yG ^ 2) ^ 2 := by
        have : (yG ^ 2) ^ 2 = yG ^ 3 * yG := by group
        rw [this, hyG3, one_mul]
      rw [this]; exact pow_mem hxR 2
  have hcard2 : 3 * Nat.card R₁ ≤ Nat.card R₂ := by
    have := card_mul_le_card_sup_of_disjoint R₁ (zpowers yG) hdisj2
    rw [Nat.card_zpowers, hord_y] at this
    rw [hR₂]
    omega
  have hcard81 : 81 ≤ Nat.card R₂ := by omega
  set WG : Subgroup G := W.map L.subtype with hWG
  have hWG0 : WG ≠ ⊥ := by
    intro h0
    apply hW0
    rw [eq_bot_iff]
    intro w hw
    have : (w : G) ∈ WG := Subgroup.mem_map_of_mem L.subtype hw
    rw [h0, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.2 (Subtype.ext this)
  have hWG2 : IsPGroup 2 WG := hW2.of_surjective (L.subtype.subgroupMap W)
    (L.subtype.subgroupMap_surjective W)
  have hDN : Dg ≤ normalizer (WG : Set G) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer (WG : Set G))
    intro d hd
    rw [mem_centralizer_iff]
    rintro _ ⟨w, -, rfl⟩
    exact (hDC d hd w w.2).symm
  have haN : zpowers aG ≤ normalizer (WG : Set G) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer (WG : Set G))
    rw [zpowers_le, mem_centralizer_iff]
    rintro _ ⟨w, hw, rfl⟩
    exact (congrArg Subtype.val (haW w hw)).symm
  have hyN' : zpowers yG ≤ normalizer (WG : Set G) := by
    rw [zpowers_le]
    exact Subgroup.le_normalizer_map L.subtype (Subgroup.mem_map_of_mem L.subtype hyN)
  have hR₂N : R₂ ≤ normalizer (WG : Set G) := sup_le (sup_le hDN haN) hyN'
  obtain ⟨k, hk⟩ := isElemAbelian_card_eq_pow hR₂e
  have hk4 : 4 ≤ k := by
    by_contra hk4
    have : 3 ^ k ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hle := le_localRank_of_elemAbelian hWG0 hWG2 hR₂e hR₂N hk
  have h3 : CFSG.Assembly.RankThreeEven.localRank 3 G = 3 :=
    h.pair.standing.toTheoremFourHyp.localRank_three
  omega

open CFSG.ComponentClassification.OuterAutomorphisms (Outer) in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem sec217ALe_of (h45 : Sec4.Item4_5) : Sec217ALe (G := G) := by
  intro A E U c L h
  have hpairs := mem_lThreeStarPairs_iff.mp h.pair.mem_pair
  have hcA : c ∈ A := h.c_mem_A
  have hLc : L ∈ thetaComponentsAt 3 c := (lZeroStarAt_subset A c) hpairs.2.2.1
  have hAN : A ≤ normalizer (L : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 h.pair.standing.toTheoremFourHyp
      h.pair.mem_S.1.1 hcA hpairs.2.1 L hLc
  have hθ := sec217ThetaOne_holds A E U c L h
  obtain ⟨hq, hZ3⟩ := h.quasi_card_center hθ
  obtain ⟨e⟩ := h.quot
  have hTri : Sec4.IsTripleCover ↥L NativeSporadic.J3 := ⟨hZ3, ⟨e⟩⟩
  have hAe := h.isElemAbelian_A
  have hAe' := isElemAbelian_iff.1 hAe
  have hmax := h.pair.mem_S.1.2.1
  set ρ : ↥A →* MulAut ↥L := L.normalizerMonoidHom.comp (Subgroup.inclusion hAN) with hρ
  have hρapp : ∀ (a : ↥A) (x : ↥L), (((ρ a) x : ↥L) : G) = (a : G) * x * (a : G)⁻¹ :=
    fun a x => rfl
  have hinn : ∀ a : ↥A, ∃ k : ↥L, ρ a = MulAut.conj k := by
    intro a
    have h3 : ρ a ^ 3 = 1 := by
      rw [← map_pow]
      have : a ^ 3 = 1 := Subtype.ext (by simpa using hAe'.2 a a.2)
      rw [this, map_one]
    exact inner_of_pow_three_J3 hq.1 e (ρ a) h3
  have hkerρ : ∀ a : ↥A, a ∈ ρ.ker ↔ (a : G) ∈ centralizer (L : Set G) := by
    intro a
    rw [MonoidHom.mem_ker, mem_centralizer_iff]
    constructor
    · intro h1 x hx
      have h2 : x = (a : G) * x * (a : G)⁻¹ := by
        have := hρapp a ⟨x, hx⟩
        rw [h1, MulAut.one_apply] at this
        exact this
      calc x * (a : G) = ((a : G) * x * (a : G)⁻¹) * (a : G) := by rw [← h2]
        _ = (a : G) * x := by group
    · intro hc
      ext x
      rw [hρapp, MulAut.one_apply]
      have := hc x x.2
      rw [← this]; group
  have hcker : (⟨c, hcA⟩ : ↥A) ∈ ρ.ker := by
    rw [hkerρ]
    rw [mem_centralizer_iff]
    intro x hx
    exact (h.c_comm x hx).symm
  have hordc : orderOf (⟨c, hcA⟩ : ↥A) = 3 := by
    rw [← Subgroup.orderOf_coe]; exact h.orderOf_c
  have hAcard : Nat.card A = 3 ^ 4 := h.card
  have hkr := Subgroup.card_ker_mul_card_range ρ
  have hdvd3 : 3 ∣ Nat.card ρ.ker := hordc ▸ Subgroup.orderOf_dvd_natCard _ hcker
  have hdvd81 : Nat.card ρ.ker ∣ 3 ^ 4 := ⟨_, by rw [← hAcard, ← hkr]⟩
  obtain ⟨j, hj, hjk⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd81
  have hj1 : 1 ≤ j := by
    by_contra h0
    have : j = 0 := by omega
    rw [this, pow_zero] at hjk
    rw [hjk] at hdvd3
    omega
  by_cases hbig : 2 ≤ j
  · exfalso
    refine h.false_of_big_kernel hθ (ρ.ker.map A.subtype) (Subgroup.map_subtype_le _) ?_ ?_
    · rintro _ ⟨a, ha, rfl⟩ x hx
      exact ((mem_centralizer_iff.1 ((hkerρ a).1 ha)) x hx).symm
    · rw [Subgroup.card_map_of_injective A.subtype_injective, hjk]
      calc 9 = 3 ^ 2 := by norm_num
        _ ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) hbig
  have hj1' : j = 1 := by omega
  have hker3 : Nat.card ρ.ker = 3 := by rw [hjk, hj1']; norm_num
  have hrange3 : 3 * Nat.card ρ.range = 3 ^ 4 := by
    have h := hkr
    rw [hker3, hAcard] at h
    exact h
  set K : Subgroup ↥L := ρ.range.comap (MulAut.conj : ↥L →* MulAut ↥L) with hK
  have hmemK : ∀ k : ↥L, k ∈ K ↔ MulAut.conj k ∈ ρ.range := fun k => Iff.rfl
  have hZK : center ↥L ≤ K := fun z hz => by
    rw [hmemK, CFSG.RankThree.PartTwo.Sec21.Item2113Res3Proof.conj_eq_one_iff_mem_center.mpr hz]
    exact ρ.range.one_mem
  set κ : K →* MulAut ↥L := (MulAut.conj : ↥L →* MulAut ↥L).comp K.subtype with hκ
  have hκker : κ.ker = (center ↥L).subgroupOf K := by
    ext ⟨k, hk⟩
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact CFSG.RankThree.PartTwo.Sec21.Item2113Res3Proof.conj_eq_one_iff_mem_center (k := k)
  have hκrange : κ.range = ρ.range := by
    ext σ
    constructor
    · intro hσ
      obtain ⟨⟨k, hk⟩, rfl⟩ := MonoidHom.mem_range.mp hσ
      exact (hmemK k).mp hk
    · intro hσ
      obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hσ
      obtain ⟨k, hk⟩ := hinn a
      have hkK : k ∈ K := by rw [hmemK, ← hk]; exact MonoidHom.mem_range.mpr ⟨a, rfl⟩
      exact MonoidHom.mem_range.mpr ⟨⟨k, hkK⟩, hk.symm⟩
  have hK81 : Nat.card K = 3 ^ 4 := by
    have h := Subgroup.card_ker_mul_card_range κ
    rw [hκker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZK).toEquiv, hZ3, hκrange] at h
    omega
  have hρcomm : ∀ σ ∈ ρ.range, ∀ τ ∈ ρ.range, σ * τ = τ * σ := by
    intro σ hσ τ hτ
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hσ
    obtain ⟨b, rfl⟩ := MonoidHom.mem_range.mp hτ
    rw [← map_mul, ← map_mul]
    exact congrArg ρ (Subtype.ext (hAe'.1 a a.2 b b.2))
  have hρcube : ∀ σ ∈ ρ.range, σ ^ 3 = 1 := by
    intro σ hσ
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hσ
    rw [← map_pow]
    have : a ^ 3 = 1 := Subtype.ext (by simpa using hAe'.2 a a.2)
    rw [this, map_one]
  have hKcomm : ∀ x ∈ K, ∀ y ∈ K, x * y * x⁻¹ * y⁻¹ ∈ center ↥L := by
    intro x hx y hy
    rw [← CFSG.RankThree.PartTwo.Sec21.Item2113Res3Proof.conj_eq_one_iff_mem_center, map_mul,
      map_mul, map_mul, map_inv, map_inv, hρcomm _ ((hmemK x).mp hx) _ ((hmemK y).mp hy),
      mul_inv_cancel_right, mul_inv_cancel]
  have hKcube : ∀ x ∈ K, x ^ 3 ∈ center ↥L := by
    intro x hx
    rw [← CFSG.RankThree.PartTwo.Sec21.Item2113Res3Proof.conj_eq_one_iff_mem_center, map_pow]
    exact hρcube _ ((hmemK x).mp hx)
  have hAK : ∀ a ∈ A, ∃ k ∈ K, ∀ x : ↥L, (a : G) * x * (a : G)⁻¹ = k * x * (k : G)⁻¹ := by
    intro a ha
    obtain ⟨k, hk⟩ := hinn ⟨a, ha⟩
    refine ⟨k, by rw [hmemK, ← hk]; exact MonoidHom.mem_range.mpr ⟨⟨a, ha⟩, rfl⟩, fun x => ?_⟩
    have h1 := hρapp ⟨a, ha⟩ x
    rw [hk] at h1
    exact h1.symm
  have hKea : CFSG.Assembly.IsElemAbelian 3 K :=
    ks217J3CoverPreimage_holds ↥L hq hTri K hZK hK81 hKcomm hKcube
  have hKea' := isElemAbelian_iff.1 hKea
  have hAcentral : ∀ a ∈ A, ∀ p ∈ K, (a : G) * (p : G) = p * a := by
    intro a ha p hp
    obtain ⟨k, hk, hkx⟩ := hAK a ha
    have h1 := hkx p
    have h2 : (k : ↥L) * p = p * k := hKea'.1 k hk p hp
    have h3 : (k : G) * p = p * k := congrArg Subtype.val h2
    have h4 : (a : G) * p * (a : G)⁻¹ = p := by rw [h1, h3]; group
    calc (a : G) * p = (a * p * a⁻¹) * a := by group
      _ = p * a := by rw [h4]
  have hP'e : CFSG.Assembly.IsElemAbelian 3 (K.map L.subtype) := isElemAbelian_map_hom _ hKea
  have hsup := isElemAbelian_sup_of_commute hAe hP'e (by
    rintro a ha _ ⟨p, hp, rfl⟩
    exact hAcentral a ha p hp)
  have hKA : K.map L.subtype ≤ A := le_sup_right.trans (hmax _ hsup le_sup_left).le
  have hKeqA : K.map L.subtype = A := by
    refine Subgroup.eq_of_le_of_card_ge hKA ?_
    rw [Subgroup.card_map_of_injective L.subtype_injective, hK81, hAcard]
  intro x hx
  rw [← hKeqA] at hx
  obtain ⟨k, -, rfl⟩ := hx
  exact k.2

end Main

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
