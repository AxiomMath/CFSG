module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremC.LocalAQuotient

public section

namespace CFSG.ProperTwoGeneratedCore.TheoremC

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly CFSG.ShultStronglyClosedTI
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

variable {X : Type} [Group X] [Finite X] {Y : Subgroup X} {u z : X}

theorem exists_conj_of_mem_zpowers_sup {K : Type} [Group K] {O : Subgroup K} [O.Normal]
    (hO : Odd (Nat.card O)) {t k : K} (ht : orderOf t = 2) (hk : orderOf k = 2)
    (hkt : k ∈ Subgroup.zpowers t ⊔ O) : ∃ n ∈ O, n⁻¹ * t * n = k := by
  obtain ⟨y, hy, o, ho, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hkt
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have htt : t ^ (2 : ℤ) = 1 := by
    rw [zpow_two, ← pow_two]
    simpa only [ht] using pow_orderOf_eq_one t
  rcases Int.even_or_odd' j with ⟨m, rfl | rfl⟩
  · rw [zpow_mul, htt, one_zpow, one_mul] at hk
    exact absurd hO (not_odd_card_of_orderOf_eq_two ho hk)
  · rw [zpow_add_one, zpow_mul, htt, one_zpow, one_mul] at hk ⊢
    refine exists_conj_of_mk_eq hO ht hk ?_
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, ← mul_assoc,
      inv_mul_cancel, one_mul]
    exact ho

theorem mk_eq_of_mem_class_of_pRank_le_two (hc : CoreConfig Y u z) {R : Subgroup X} {z' : X}
    (huR : u ∈ R) (hz'R : z' ∈ R) (hz'c : ∀ r ∈ R, Commute r z')
    (hz'cl : z' ∈ involutionPointClass z) (hrank : CFSG.Open.pRank 2 R ≤ 2) {s : X}
    (hsR : s ∈ R) (hscl : s ∈ involutionPointClass z) :
    QuotientGroup.mk' (CFSG.Open.pCore 2 X) s = QuotientGroup.mk' (CFSG.Open.pCore 2 X) z' := by
  by_cases hsz' : s = z'
  · rw [hsz']
  by_cases hsuz' : s = u * z'
  · rw [hsuz', map_mul, (mk_twoCore_eq_one_iff u).mpr hc.mem_twoCore, one_mul]
  exfalso
  have := three_le_pRank_of_commuting_involutions huR hz'R hsR hc.order
    (order_two_of_mem_pointClass hc.lever_order hz'cl)
    (order_two_of_mem_pointClass hc.lever_order hscl) (hc.commute_center z').symm
    (hc.commute_center s).symm (hz'c s hsR).symm (hc.ne_center_of_mem_class hz'cl).symm
    (hc.ne_center_of_mem_class hscl) hsz' hsuz'
  omega

theorem quasiHullTwoPointOdd_of_pRank_le_two (hc : CoreConfig Y u z)
    {a : X ⧸ CFSG.Open.pCore 2 X} (ha : orderOf a = 2) {R : Subgroup X} {z' : X}
    (hRN : R ≤ Subgroup.normalizer (quasiPreimage a : Set X)) (hR2 : IsPGroup 2 R)
    (hRmax : ∀ R' : Subgroup X, R' ≤ Subgroup.normalizer (quasiPreimage a : Set X) →
      IsPGroup 2 R' → Nat.card R' ≤ Nat.card R)
    (huR : u ∈ R) (hz'R : z' ∈ R) (hz'c : ∀ r ∈ R, Commute r z')
    (hz'cl : z' ∈ involutionPointClass z) (hrank : CFSG.Open.pRank 2 R ≤ 2) :
    QuasiHullTwoPointOdd Y z (quasiPreimage a) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (CFSG.Open.pCore 2 X)
  set N := Subgroup.normalizer (quasiPreimage a : Set X)
  have hclassR : ∀ s ∈ R, s ∈ involutionPointClass z → π s = π z' := fun s hsR hscl =>
    mk_eq_of_mem_class_of_pRank_le_two hc huR hz'R hz'c hz'cl hrank hsR hscl
  have hconjR : ∀ t ∈ N, t ∈ involutionPointClass z →
      ∃ c ∈ N, π t = π c * π z' * (π c)⁻¹ := by
    intro t htN htcl
    obtain ⟨c, hcN, hc'⟩ := exists_conj_mem_of_card_le hRN hR2 hRmax
      (Subgroup.zpowers_le.mpr htN)
      (isPGroup_zpowers_of_orderOf_eq_two (order_two_of_mem_pointClass hc.lever_order htcl))
    have h1 := hclassR _ (hc' t (Subgroup.mem_zpowers t)) (conj_mem_involutionPointClass htcl c)
    refine ⟨c, hcN, ?_⟩
    rw [← h1, map_mul, map_mul, map_inv]
    group
  have hiso : ∀ t ∈ N, t ∈ involutionPointClass z → Commute (π t) (π z') → π t = π z' := by
    intro t htN htcl htc
    set C := (Subgroup.centralizer ({π z'} : Set (X ⧸ CFSG.Open.pCore 2 X))).comap π
    have hRC : R ≤ C := fun r hr => by
      rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
        (hz'c r hr).eq]
    have htC : t ∈ C := by
      rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
      exact htc.eq
    obtain ⟨c, hcK, hc'⟩ := exists_conj_mem_of_card_le (le_inf hRN hRC) hR2
      (fun Q hQ hQ2 => hRmax Q (hQ.trans inf_le_left) hQ2)
      (Subgroup.zpowers_le.mpr (⟨htN, htC⟩ : t ∈ N ⊓ C))
      (isPGroup_zpowers_of_orderOf_eq_two (order_two_of_mem_pointClass hc.lever_order htcl))
    have h1 := hclassR _ (hc' t (Subgroup.mem_zpowers t)) (conj_mem_involutionPointClass htcl c)
    have hcz : π c * π z' = π z' * π c := Subgroup.mem_centralizer_singleton_iff.mp hcK.2
    calc π t = π c * π (c⁻¹ * t * c) * (π c)⁻¹ := by rw [map_mul, map_mul, map_inv]; group
      _ = π z' := by rw [h1, hcz, mul_inv_cancel_right]
  set Ct := Subgroup.centralizer ({a} : Set (X ⧸ CFSG.Open.pCore 2 X))
  have hmemCt : ∀ n ∈ N, π n ∈ Ct := fun n hn =>
    Subgroup.mem_centralizer_singleton_iff.mpr ((mem_normalizer_quasiPreimage_iff ha n).mp hn).eq
  have hz'N : z' ∈ N := hRN hz'R
  have hz'2 : orderOf z' = 2 := order_two_of_mem_pointClass hc.lever_order hz'cl
  set t : Ct := ⟨π z', hmemCt z' hz'N⟩
  have ht1 : t ≠ 1 := by
    intro h
    have h' : π z' = 1 := congrArg Subtype.val h
    exact hc.not_mem_twoCore_of_mem_class hz'cl ((mk_twoCore_eq_one_iff z').mp h')
  have hz'z' : z' * z' = 1 := by simpa only [hz'2, pow_two] using pow_orderOf_eq_one z'
  have htt : t * t = 1 := by
    apply Subtype.ext
    change π z' * π z' = 1
    rw [← map_mul, hz'z', map_one]
  have ht2 : orderOf t = 2 := by
    refine orderOf_eq_prime ?_ ht1
    rw [pow_two, htt]
  let : Fintype Ct := Fintype.ofFinite Ct
  obtain ⟨Ob, hOb, hObodd, hObt⟩ := CFSG.ZStar.glauberman_zStar Ct t ht1 htt (by
    intro g hg
    obtain ⟨n, hn⟩ := QuotientGroup.mk'_surjective (CFSG.Open.pCore 2 X)
      (g : X ⧸ CFSG.Open.pCore 2 X)
    have hnN : n ∈ N := (mem_normalizer_quasiPreimage_iff ha n).mpr (by
      rw [hn]
      exact Subgroup.mem_centralizer_singleton_iff.mp g.2)
    have hcl : n * z' * n⁻¹ ∈ involutionPointClass z := by
      have h := conj_mem_involutionPointClass hz'cl n⁻¹
      rwa [inv_inv] at h
    have hmem : n * z' * n⁻¹ ∈ N := N.mul_mem (N.mul_mem hnN hz'N) (N.inv_mem hnN)
    have hval : π (n * z' * n⁻¹) = ((g * t * g⁻¹ : Ct) : X ⧸ CFSG.Open.pCore 2 X) := by
      rw [map_mul, map_mul, map_inv, hn]
      rfl
    have hcomm : Commute (π (n * z' * n⁻¹)) (π z') := by
      rw [hval]
      exact congrArg Subtype.val hg
    apply Subtype.ext
    rw [← hval]
    exact hiso _ hmem hcl hcomm)
  set Kt : Subgroup Ct := Subgroup.zpowers t ⊔ Ob
  have hgen : quasiHull z (quasiPreimage a) ≤ (Kt.map Ct.subtype).comap π := by
    refine sup_le ((Subgroup.closure_le _).mpr ?_) ?_
    · rintro s ⟨hscl, hsN⟩
      obtain ⟨c, hcN, hcs⟩ := hconjR s hsN hscl
      set ct : Ct := ⟨π c, hmemCt c hcN⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_map]
      refine ⟨ct * t * ct⁻¹, ?_, ?_⟩
      · have h2 : ct * t * ct⁻¹ = (ct * t * ct⁻¹ * t⁻¹) * t := by group
        rw [h2]
        exact Kt.mul_mem (Subgroup.mem_sup_right (hObt ct))
          (Subgroup.mem_sup_left (Subgroup.mem_zpowers t))
      · rw [hcs]
        rfl
    · intro x hx
      rw [Subgroup.mem_comap, Subgroup.mem_map]
      refine ⟨1, Kt.one_mem, ?_⟩
      rw [map_one]
      exact ((mk_twoCore_eq_one_iff x).mpr hx).symm
  intro x hxQ hxx hxO ℓ _ hℓY hxY hℓx
  obtain ⟨k, hkK, hk⟩ := Subgroup.mem_map.mp (Subgroup.mem_comap.mp (hgen hxQ))
  have hx2 : orderOf (π x) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow, pow_two, (mk_twoCore_eq_one_iff _).mpr hxx]
    · rw [Ne, mk_twoCore_eq_one_iff]
      exact hxO
  have hk2 : orderOf k = 2 := by
    have hk' : (k : X ⧸ CFSG.Open.pCore 2 X) = π x := hk
    rw [← Subgroup.orderOf_coe, hk']
    exact hx2
  have : Ob.Normal := hOb
  obtain ⟨n, -, hn⟩ := exists_conj_of_mem_zpowers_sup hObodd ht2 hk2 hkK
  obtain ⟨m, hm⟩ := QuotientGroup.mk'_surjective (CFSG.Open.pCore 2 X)
    (n : X ⧸ CFSG.Open.pCore 2 X)
  set w := m⁻¹ * z' * m with hw
  have hwx : π w = π x := by
    rw [← hk, ← hn, hw, map_mul, map_mul, map_inv, hm]
    rfl
  have hwO : w⁻¹ * x ∈ CFSG.Open.pCore 2 X := by
    rw [← mk_twoCore_eq_one_iff, map_mul, map_inv, hwx, inv_mul_cancel]
  have hwY : w ∈ Y := by
    have h := Y.mul_mem hxY (Y.inv_mem (hc.twoCore_le hwO))
    convert h using 1
    group
  have hℓw : ℓ * w * ℓ⁻¹ ∈ Y := by
    have h := Y.mul_mem hℓx (hc.twoCore_le
      ((twoCore_normal (X := X)).conj_mem _ (Subgroup.inv_mem _ hwO) ℓ))
    convert h using 1
    group
  have hwcl : w ∈ involutionPointClass z := conj_mem_involutionPointClass hz'cl m
  exact hc.ne_center_of_mem_class hwcl
    (hc.eq_of_conj_mem hℓY hwY hℓw (order_two_of_mem_pointClass hc.lever_order hwcl))

end CFSG.ProperTwoGeneratedCore.TheoremC
