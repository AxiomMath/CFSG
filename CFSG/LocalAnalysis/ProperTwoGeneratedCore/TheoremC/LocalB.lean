module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremC.LocalBQuotient
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremC.LocalStatement

public section

namespace CFSG.ProperTwoGeneratedCore.TheoremC

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly CFSG.ShultStronglyClosedTI

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem eq_one_of_pow_two_pow_eq_one_of_odd {B : Subgroup X} (hB : Odd (Nat.card B)) {b : X}
    (hb : b ∈ B) {n : ℕ} (hbn : b ^ 2 ^ n = 1) : b = 1 := by
  have hcop : Nat.Coprime (2 ^ n) (Nat.card B) :=
    Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr hB)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hbn)
    (Subgroup.orderOf_dvd_natCard B hb))

omit [Finite X] in
theorem exists_pow_two_pow_eq_one_of_mul_self_mem {W : Subgroup X} (hW : IsPGroup 2 W) {g : X}
    (hg : g * g ∈ W) : ∃ n : ℕ, g ^ 2 ^ n = 1 := by
  obtain ⟨k, hk⟩ := hW ⟨g * g, hg⟩
  refine ⟨k + 1, ?_⟩
  have h := congrArg Subtype.val hk
  simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at h
  rw [pow_succ', pow_mul, pow_two, h]

omit [Finite X] in
theorem mem_of_mem_sup_of_pow_two_pow_eq_one {A B : Subgroup X} (hAn : A.Normal) (hBn : B.Normal)
    (hA : IsPGroup 2 A) (hB : Odd (Nat.card B)) {g : X} (hg : g ∈ A ⊔ B) {n : ℕ}
    (hgn : g ^ 2 ^ n = 1) : g ∈ A := by
  have hdis : Disjoint A B := by
    rw [Subgroup.disjoint_def]
    intro y hyA hyB
    obtain ⟨k, hk⟩ := hA ⟨y, hyA⟩
    have h := congrArg Subtype.val hk
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at h
    exact eq_one_of_pow_two_pow_eq_one_of_odd hB hyB h
  obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hg
  have hab : Commute a b := Subgroup.commute_of_normal_of_disjoint A B hAn hBn hdis a b ha hb
  rw [hab.mul_pow] at hgn
  have hbA : b ^ 2 ^ n ∈ A := by
    rw [eq_inv_of_mul_eq_one_right hgn]
    exact A.inv_mem (A.pow_mem ha _)
  have hb1 : b ^ 2 ^ n = 1 := Subgroup.disjoint_def.mp hdis hbA (B.pow_mem hb _)
  rw [eq_one_of_pow_two_pow_eq_one_of_odd hB hb hb1, mul_one]
  exact ha

theorem disjoint_component_of_isPGroup {J W : Subgroup X} (hJ : CFSG.IsComponent J)
    (hJs : IsSimpleGroup J) (hWn : W.Normal) (hW : IsPGroup 2 W) : Disjoint J W := by
  have hD : (W.subgroupOf J).Normal := hWn.subgroupOf J
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (W.subgroupOf J) with h | h
  · rw [Subgroup.disjoint_def]
    intro x hxJ hxW
    have hmem : (⟨x, hxJ⟩ : J) ∈ W.subgroupOf J := Subgroup.mem_subgroupOf.mpr hxW
    rw [h, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  · exfalso
    have hJW : J ≤ W := by
      intro x hx
      have hmem : (⟨x, hx⟩ : J) ∈ W.subgroupOf J := by
        rw [h]
        exact Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp hmem
    have hJp : IsPGroup 2 J := hW.to_le hJW
    have hZ : Nontrivial (Subgroup.center J) := hJp.center_nontrivial
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center J) with hc | hc
    · exact (Subgroup.nontrivial_iff_ne_bot _).mp hZ hc
    · obtain ⟨-, -, a, b, hab⟩ := hJ.1
      have h1 : ∀ q : J ⧸ Subgroup.center J, q = 1 := by
        intro q
        obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
        exact (QuotientGroup.eq_one_iff g).mpr (hc ▸ Subgroup.mem_top g)
      exact hab (by rw [h1 a, h1 b])

theorem false_of_mem_component_sup {Y : Subgroup X} {u z : X} (hc : CoreConfig Y u z)
    {J W : Subgroup X} (hJ : CFSG.IsComponent J) (hJs : IsSimpleGroup J) (hJn : J.Normal)
    (huJ : u ∉ J) (hWn : W.Normal) (hW : IsPGroup 2 W) (hWY : W ≤ Y) {x m : X}
    (hx : x ∈ J ⊔ W) (hxx : x * x ∈ W) (hxW : x ∉ W) (hm : m ∉ Y) (hxY : x ∈ Y)
    (hmx : m * x * m⁻¹ ∈ Y) : False := by
  have hdis := disjoint_component_of_isPGroup hJ hJs hWn hW
  obtain ⟨j, hj, w, hw, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hx
  have hjw : Commute j w := Subgroup.commute_of_normal_of_disjoint J W hJn hWn hdis j w hj hw
  have hjj : j * j = 1 := by
    refine Subgroup.disjoint_def.mp hdis (J.mul_mem hj hj) ?_
    have h : j * j = j * w * (j * w) * (w * w)⁻¹ := by
      rw [mul_assoc j w, ← mul_assoc w j w, ← hjw.eq]
      group
    rw [h]
    exact W.mul_mem hxx (W.inv_mem (W.mul_mem hw hw))
  have hj1 : j ≠ 1 := by
    rintro rfl
    exact hxW (by rwa [one_mul])
  have hjord : orderOf j = 2 := orderOf_eq_prime (by rw [pow_two]; exact hjj) hj1
  have hjY : j ∈ Y := by
    have h : j = j * w * w⁻¹ := by group
    rw [h]
    exact Y.mul_mem hxY (Y.inv_mem (hWY hw))
  have hmj : m * j * m⁻¹ ∈ Y := by
    have h : m * j * m⁻¹ = m * (j * w) * m⁻¹ * (m * w⁻¹ * m⁻¹) := by group
    rw [h]
    exact Y.mul_mem hmx (hWY (hWn.conj_mem _ (W.inv_mem hw) m))
  exact huJ (hc.eq_of_conj_mem hm hjY hmj hjord ▸ hj)

theorem quasiRankThree : QuasiRankThree := by
  intro X _ _ Y u z IH hI hc V R z' hV hOV hVO _ _ hNY hRN hRY hR hRmax hz'R hz'c hz'z hRrank
    x hx hxx hxO ℓ hℓ hℓY hxY hℓxY
  set N := Subgroup.normalizer (V : Set X)
  have huN : u ∈ N := Subgroup.center_le_normalizer _ hc.center
  have hz' : orderOf z' = 2 := order_two_of_mem_pointClass hc.lever_order hz'z
  have hne : z' ≠ u := by
    intro h
    obtain ⟨g, hg⟩ := hz'z
    apply hc.lever_ne
    have hg' : g⁻¹ * z * g = u := hg.trans h
    calc z = g * (g⁻¹ * z * g) * g⁻¹ := by group
      _ = u := by rw [hg', (hc.commute_center g).eq, mul_inv_cancel_right]
  obtain ⟨hKY, hc'⟩ :=
    rankThree_quotient_coreConfig hc huN hNY hRN hRY hR hRmax hz'R hz'c hz' hne hRrank
  set K := pPrimeCore 2 N
  have hKodd : Odd (Nat.card K) := Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2))
  obtain ⟨J, hJ, huJ⟩ := IH (N ⧸ K)
    (card_quotient_subgroup_lt (normalizer_ne_top_of_not_le_twoCore hV hVO) K) _ _ _ hc'
  obtain ⟨hJs, hJn, hinv⟩ := hI (N ⧸ K) _ _ _ hc' J hJ huJ
  have hON : CFSG.Open.pCore 2 X ≤ N := hOV.trans Subgroup.le_normalizer
  have hOY : CFSG.Open.pCore 2 X ≤ Y := by
    obtain ⟨P, hPY, -, -, -⟩ := hc.sylow
    exact ((twoCore_isPGroup X).le_sylow_of_normal P).trans hPY
  have huO : u ∈ CFSG.Open.pCore 2 X := by
    refine le_twoCore (Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hc.center)) ?_
      (Subgroup.mem_zpowers u)
    exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hc.order, pow_one])
  have hA : IsPGroup 2 ((CFSG.Open.pCore 2 X).subgroupOf N) :=
    (twoCore_isPGroup X).of_equiv (Subgroup.subgroupOfEquivOfLe hON).symm
  have hAn : ((CFSG.Open.pCore 2 X).subgroupOf N).Normal := twoCore_normal.subgroupOf N
  set W := ((CFSG.Open.pCore 2 X).subgroupOf N).map (QuotientGroup.mk' K)
  have hWn : W.Normal := hAn.map _ (QuotientGroup.mk'_surjective K)
  have hWp : IsPGroup 2 W := hA.map _
  have hWY : W ≤ (Y.subgroupOf N).map (QuotientGroup.mk' K) := Subgroup.map_mono fun g hg =>
    Subgroup.mem_subgroupOf.mpr (hOY (Subgroup.mem_subgroupOf.mp hg))
  have huW : QuotientGroup.mk' K ⟨u, huN⟩ ∈ W :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr huO)
  have hle : quasiHull z V ≤ ((J ⊔ W).comap (QuotientGroup.mk' K)).map N.subtype := by
    refine sup_le ((Subgroup.closure_le _).mpr ?_) fun g hg => ?_
    · rintro g ⟨hgz, hgN⟩
      refine ⟨⟨g, hgN⟩, Subgroup.mem_comap.mpr ?_, rfl⟩
      have hgord : orderOf (QuotientGroup.mk' K ⟨g, hgN⟩) = 2 := orderOf_mk_eq_two hKodd (by
        rw [Subgroup.orderOf_mk]
        exact order_two_of_mem_pointClass hc.lever_order hgz)
      rcases hinv _ hgord with h | h
      · exact Subgroup.mem_sup_left h
      · have h' : QuotientGroup.mk' K ⟨g, hgN⟩ = (QuotientGroup.mk' K ⟨u, huN⟩)⁻¹ *
            (QuotientGroup.mk' K ⟨u, huN⟩ * QuotientGroup.mk' K ⟨g, hgN⟩) := by group
        rw [h']
        exact (J ⊔ W).mul_mem (Subgroup.mem_sup_right (W.inv_mem huW))
          (Subgroup.mem_sup_left h)
    · exact ⟨⟨g, hON hg⟩, Subgroup.mem_comap.mpr (Subgroup.mem_sup_right
        (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hg))), rfl⟩
  obtain ⟨xN, hxJW, rfl⟩ := Subgroup.mem_map.mp (hle hx)
  obtain ⟨ℓN, -, rfl⟩ := Subgroup.mem_map.mp (hle hℓ)
  refine false_of_mem_component_sup (x := QuotientGroup.mk' K xN)
    (m := QuotientGroup.mk' K ℓN) hc' hJ hJs hJn huJ hWn hWp hWY
    (Subgroup.mem_comap.mp hxJW) ?_ ?_ ?_ ?_ ?_
  · rw [← map_mul]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hxx)
  · rintro ⟨a, ha, hax⟩
    apply hxO
    have hxN : xN ∈ (CFSG.Open.pCore 2 X).subgroupOf N ⊔ K := by
      have h : xN = a * (a⁻¹ * xN) := by group
      rw [h]
      exact Subgroup.mul_mem_sup ha (QuotientGroup.eq.mp hax)
    obtain ⟨n, hn⟩ := exists_pow_two_pow_eq_one_of_mul_self_mem (g := xN) hA
      (Subgroup.mem_subgroupOf.mpr hxx)
    exact Subgroup.mem_subgroupOf.mp
      (mem_of_mem_sup_of_pow_two_pow_eq_one hAn inferInstance hA hKodd hxN hn)
  · intro h
    apply hℓY
    have hker : (QuotientGroup.mk' K).ker ≤ Y.subgroupOf N := by
      rw [QuotientGroup.ker_mk']
      exact hKY
    have h' : ℓN ∈ Y.subgroupOf N := by
      rw [← Subgroup.comap_map_eq_self hker]
      exact h
    exact Subgroup.mem_subgroupOf.mp h'
  · exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hxY)
  · rw [← map_inv, ← map_mul, ← map_mul]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hℓxY)

end CFSG.ProperTwoGeneratedCore.TheoremC
