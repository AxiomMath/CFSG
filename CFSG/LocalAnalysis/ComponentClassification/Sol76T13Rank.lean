module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76T13Balanced

public section

namespace CFSG.ComponentClassification.Sol76T13

open CFSG Subgroup CFSG.ComponentClassification.FooteLit CFSG.ComponentClassification.Sol76
  CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem pRank_succ_le_of_commute {B M : Subgroup G} {t : G} (hBM : B ≤ M) (htM : t ∈ M)
    (ht2 : orderOf t = 2) (htB : ∀ y ∈ B, y * t = t * y) (htnB : t ∉ B) :
    CFSG.Open.pRank 2 B + 1 ≤ CFSG.Open.pRank 2 M := by
  classical
  obtain ⟨E, hEB, hE, hcard⟩ := SectionRank.exists_pRank (p := 2) (by norm_num) B
  have hzt : ∀ y ∈ zpowers t, y = 1 ∨ y = t := by
    intro y hy
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
    rw [← zpow_mod_orderOf, ht2]
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · left
      rw [show ((2 : ℕ) : ℤ) = 2 from rfl, h, zpow_zero]
    · right
      rw [show ((2 : ℕ) : ℤ) = 2 from rfl, h, zpow_one]
  have ht1 : t ^ 2 = 1 := by rw [← ht2]; exact pow_orderOf_eq_one t
  have hEt : E ⊓ zpowers t = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hyE, hyt⟩
    rcases hzt y hyt with h | h
    · exact h ▸ one_mem _
    · exact absurd (h ▸ hEB hyE) htnB
  have hEc := hE.1
  have hc : ∀ (x : E) (y : zpowers t), Commute (E.subtype x) ((zpowers t).subtype y) := by
    intro x y
    rcases hzt y y.2 with h | h
    · change Commute (x : G) (y : G)
      rw [h]
      exact Commute.one_right _
    · change Commute (x : G) (y : G)
      rw [h]
      exact htB x (hEB x.2)
  let f : E × zpowers t →* G := MonoidHom.noncommCoprod E.subtype (zpowers t).subtype hc
  have hf : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨x, y⟩ hxy
    have hxy' : (x : G) * y = 1 := hxy
    have hyE : (y : G) ∈ E := by
      rw [eq_inv_of_mul_eq_one_right hxy']
      exact E.inv_mem x.2
    have hy1 : (y : G) = 1 := by
      have : (y : G) ∈ E ⊓ zpowers t := ⟨hyE, y.2⟩
      rw [hEt, mem_bot] at this
      exact this
    rw [hy1, mul_one] at hxy'
    have hx1 : x = 1 := Subtype.ext hxy'
    have hy1' : y = 1 := Subtype.ext hy1
    rw [hx1, hy1']
    rfl
  refine SectionRank.le_pRank_of_injective (A := E × zpowers t) (by norm_num) ?_ ?_ ?_ f hf ?_
  · rintro ⟨x₁, y₁⟩ ⟨x₂, y₂⟩
    refine Prod.ext (mul_comm' x₁ x₂) (Subtype.ext ?_)
    change (y₁ : G) * y₂ = y₂ * y₁
    rcases hzt y₁ y₁.2 with h | h <;> rcases hzt y₂ y₂.2 with h' | h' <;> simp [h, h']
  · rintro ⟨x, y⟩
    refine Prod.ext (Subtype.ext (hE.2 x x.2)) (Subtype.ext ?_)
    change (y : G) ^ 2 = 1
    rcases hzt y y.2 with h | h
    · rw [h, one_pow]
    · rw [h, ht1]
  · rw [Nat.card_prod, hcard, Nat.card_zpowers, ht2, pow_succ]
  · rintro _ ⟨⟨x, y⟩, rfl⟩
    rcases hzt y y.2 with h | h
    · change (x : G) * y ∈ M
      rw [h, mul_one]
      exact hBM (hEB x.2)
    · change (x : G) * y ∈ M
      rw [h]
      exact mul_mem (hBM (hEB x.2)) htM

theorem pRank_map_le_of_odd {A B : Type*} [Group A] [Group B] [Finite A] [Finite B] (f : A →* B)
    (H : Subgroup A) (hodd : ¬ 2 ∣ Nat.card (f.ker.subgroupOf H)) :
    CFSG.Open.pRank 2 (H.map f) ≤ CFSG.Open.pRank 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hker : (f.subgroupMap H).ker = f.ker.subgroupOf H := by
    ext x
    simp [MonoidHom.mem_ker, mem_subgroupOf, Subtype.ext_iff]
  let e : H ⧸ f.ker.subgroupOf H ≃* H.map f :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective _ (MonoidHom.subgroupMap_surjective f H))
  rw [SectionRank.pRank_eq_pRank_top_subgroup H, SectionRank.pRank_eq_pRank_top_subgroup (H.map f),
    ← SectionRank.pRank_quotient_eq _ hodd, SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e]

theorem pRank_le_of_sup_oddCoreIn {Y C : Subgroup G} (hCY : C ≤ Y)
    (hsup : C ⊔ oddCoreIn Y = Y) : CFSG.Open.pRank 2 Y ≤ CFSG.Open.pRank 2 C := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O' := pPrimeCore 2 ↥Y with hO'
  set π := QuotientGroup.mk' O' with hπ
  set C₀ := C.subgroupOf Y with hC₀
  have hO'odd : ¬ 2 ∣ Nat.card O' := by
    have h := coprime_card_oddCoreIn Y
    rw [oddCoreIn, card_map_of_injective Y.subtype_injective] at h
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp h
  have htop : C₀.map π = ⊤ := by
    rw [eq_top_iff]
    rintro z -
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective O' z
    have hy : (y : G) ∈ oddCoreIn Y ⊔ C := by rw [sup_comm, hsup]; exact y.2
    obtain ⟨o, ho, c, hc, he⟩ :=
      exists_mul_of_mem_sup_normalizer (hCY.trans (le_normalizer_oddCoreIn Y)) hy
    obtain ⟨o', ho', rfl⟩ := mem_map.mp ho
    refine ⟨⟨c, hCY hc⟩, by simpa [hC₀, mem_subgroupOf] using hc, ?_⟩
    have hyo : y = o' * ⟨c, hCY hc⟩ := Subtype.ext he
    have ho1 : π o' = 1 := (QuotientGroup.eq_one_iff o').mpr ho'
    rw [hyo, map_mul, ho1, one_mul]
  have hodd : ¬ 2 ∣ Nat.card (π.ker.subgroupOf C₀) := by
    rw [hπ, QuotientGroup.ker_mk']
    intro h
    apply hO'odd
    refine h.trans ?_
    have hc : Nat.card (O'.subgroupOf C₀) = Nat.card ↥(O' ⊓ C₀) := by
      rw [← subgroupOf_map_subtype, card_map_of_injective C₀.subtype_injective]
    rw [hc]
    exact card_dvd_of_le inf_le_left
  calc CFSG.Open.pRank 2 Y = CFSG.Open.pRank 2 (⊤ : Subgroup ↥Y) :=
        SectionRank.pRank_eq_pRank_top_subgroup Y
    _ = CFSG.Open.pRank 2 (⊤ : Subgroup (↥Y ⧸ O')) := (SectionRank.pRank_quotient_eq O' hO'odd).symm
    _ = CFSG.Open.pRank 2 (C₀.map π) := by rw [htop]
    _ ≤ CFSG.Open.pRank 2 C₀ := pRank_map_le_of_odd π C₀ hodd
    _ ≤ CFSG.Open.pRank 2 (C₀.map Y.subtype) :=
        SectionRank.pRank_le_map (by norm_num) Y.subtype Y.subtype_injective C₀
    _ = CFSG.Open.pRank 2 C := by rw [hC₀, subgroupOf_map_subtype, inf_of_le_left hCY]

theorem three_le_pRank_sup_of_isTwoComponentIn {H X Y : Subgroup G} (hX : IsTwoComponentIn X H)
    (hY : IsTwoComponentIn Y H) (hXY : X ≠ Y) {t : G} (htX : t ∈ X) (ht2 : orderOf t = 2)
    (htc : ∃ x ∈ X, ⁅x, t⁆ ∉ oddCoreIn X) (hY2 : 2 ≤ CFSG.Open.pRank 2 Y) :
    3 ≤ CFSG.Open.pRank 2 (X ⊔ Y) := by
  have hXk : X ≤ coreActionKernel Y :=
    GSThmB.B5a.le_coreActionKernel_of_ne hY.1 hX.1 hY.2 hX.2 (Ne.symm hXY)
  have hU2 : IsPGroup 2 (zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht2, pow_one])
  have hcov := inf_centralizer_sup_oddCoreIn_eq hU2 (zpowers_le.mpr (hXk htX))
  set C := Y ⊓ centralizer ((zpowers t : Subgroup G) : Set G) with hC
  have hCr : CFSG.Open.pRank 2 Y ≤ CFSG.Open.pRank 2 C := pRank_le_of_sup_oddCoreIn inf_le_left hcov
  have htC : ∀ y ∈ C, y * t = t * y := fun y hy =>
    ((mem_centralizer_iff.mp hy.2) t (mem_zpowers t)).symm
  have htnC : t ∉ C := by
    intro htC'
    obtain ⟨x, hxX, hxc⟩ := htc
    apply hxc
    have h1 : ⁅x, t⁆ ∈ oddCoreIn H :=
      FooteLit.commutator_le_oddCoreIn_of_ne hX hY hXY (commutator_mem_commutator hxX htC'.1)
    have h2 : ⁅x, t⁆ ∈ X := by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hxX htX) (inv_mem hxX)) (inv_mem htX)
    exact oddCoreIn_inf_le hX.1 (mem_inf.mpr ⟨h1, h2⟩)
  have key := pRank_succ_le_of_commute (B := C) (M := X ⊔ Y) (inf_le_left.trans le_sup_right)
    (mem_sup_left htX) ht2 htC htnC
  omega

theorem exists_involution_mk_eq {A : Type*} [Group A] [Finite A] (N : Subgroup A) [N.Normal]
    (hN : ¬ 2 ∣ Nat.card N) {y : A ⧸ N} (hy : orderOf y = 2) :
    ∃ t : A, orderOf t = 2 ∧ (t : A ⧸ N) = y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective y
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos a).ne'
  have hm0 : m ≠ 0 := hm.pos.ne'
  set t := a ^ m with ht
  have hy1 : ((a : A ⧸ N)) ^ 2 = 1 := by rw [← hy]; exact pow_orderOf_eq_one _
  have hmk : ((t : A ⧸ N)) = (a : A ⧸ N) := by
    obtain ⟨j, rfl⟩ := hm
    rw [ht, QuotientGroup.mk_pow, pow_succ, pow_mul, hy1, one_pow, one_mul]
  have htord : orderOf t = 2 ^ k := by
    rw [ht, orderOf_pow' a hm0, hkm, Nat.gcd_mul_left_left]
    exact Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm0)
  have ht2N : t ^ 2 ∈ N := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hmk, hy1]
  have hsq : t ^ 2 = 1 := by
    have h1 := orderOf_dvd_natCard (⟨t ^ 2, ht2N⟩ : N)
    rw [Subgroup.orderOf_mk] at h1
    have h2 : orderOf (t ^ 2) ∣ 2 ^ k := by
      rw [← htord]; exact orderOf_pow_dvd 2
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2
    rcases i with _ | i
    · rw [pow_zero] at hi; exact orderOf_eq_one_iff.mp hi
    · exact absurd (hi ▸ h1) fun h => hN ((dvd_pow_self 2 (Nat.succ_ne_zero i)).trans h)
  refine ⟨t, orderOf_eq_prime hsq fun h1 => ?_, hmk⟩
  rw [h1, QuotientGroup.mk_one] at hmk
  rw [← hmk, orderOf_one] at hy
  norm_num at hy

theorem exists_noncentral_involution_of_isTwoComponentIn
    (hq : QuasisimpleTwoPartInput) {H K : Subgroup G} (hK : IsTwoComponentIn K H)
    (hcat : Blueprint.Catalog ((↥K ⧸ pPrimeCore 2 ↥K) ⧸ center (↥K ⧸ pPrimeCore 2 ↥K)))
    (hm : 2 ≤ CFSG.Open.pRank 2 K) :
    ∃ t ∈ K, orderOf t = 2 ∧ ∃ x ∈ K, ⁅x, t⁆ ∉ oddCoreIn K := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O' := pPrimeCore 2 ↥K with hO'
  set Q := ↥K ⧸ O' with hQ
  set π := QuotientGroup.mk' O' with hπ
  have hQq : IsQuasisimple Q := isQuasisimple_quotient_of_isPComponent hK.1 hK.2
  have hO'odd : ¬ 2 ∣ Nat.card O' := by
    have h := coprime_card_oddCoreIn K
    rw [oddCoreIn, card_map_of_injective K.subtype_injective] at h
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp h
  by_contra hall
  push Not at hall
  have hcen : ∀ z : Q, orderOf z = 2 → z ∈ center Q := by
    intro z hz
    obtain ⟨t, ht2, rfl⟩ := exists_involution_mk_eq O' hO'odd hz
    rw [mem_center_iff]
    intro w
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective w
    have ht2' : orderOf (t : G) = 2 := by rw [Subgroup.orderOf_coe]; exact ht2
    obtain ⟨c, hc, hce⟩ := mem_map.mp (hall t t.2 ht2' x x.2)
    have hc' : (c : G) = ⁅(x : G), (t : G)⁆ := hce
    have hxt : ⁅x, t⁆ ∈ O' := by
      have : ⁅x, t⁆ = c := by
        apply Subtype.ext
        rw [hc']
        simp [commutatorElement_def]
      rw [this]
      exact hc
    have h1 : ⁅(x : Q), (t : Q)⁆ = 1 := by
      have h2 : (QuotientGroup.mk' O') ⁅x, t⁆ = 1 := (QuotientGroup.eq_one_iff ⁅x, t⁆).mpr hxt
      rw [map_commutatorElement] at h2
      exact h2
    exact commutatorElement_eq_one_iff_mul_comm.mp h1
  have hmQ : 2 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup Q) := by
    rw [SectionRank.pRank_quotient_eq O' hO'odd, ← SectionRank.pRank_eq_pRank_top_subgroup K]
    exact hm
  obtain ⟨E, -, hE, hcard⟩ := SectionRank.exists_pRank (p := 2) (by norm_num) (⊤ : Subgroup Q)
  have := Fintype.ofFinite ↥E
  have h4 : 4 ≤ Fintype.card ↥E := by
    rw [← Nat.card_eq_fintype_card, hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ CFSG.Open.pRank 2 (⊤ : Subgroup Q) := Nat.pow_le_pow_right (by norm_num) hmQ
  obtain ⟨u, -, hu⟩ := Finset.exists_mem_ne (s := Finset.univ)
    (by rw [Finset.card_univ]; omega) (1 : ↥E)
  obtain ⟨v, hv, hvu⟩ := Finset.exists_mem_ne (s := Finset.univ.erase (1 : ↥E))
    (by rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]; omega) u
  have hv1 : v ≠ 1 := Finset.ne_of_mem_erase hv
  have hord : ∀ w : ↥E, w ≠ 1 → orderOf (w : Q) = 2 := fun w hw =>
    orderOf_eq_prime (hE.2 w w.2) fun h => hw (Subtype.ext h)
  obtain ⟨z, hz2, hzc⟩ := hq.1 Q hQq hcat u v (hord u hu) (hord v hv1)
    (fun h => hvu (Subtype.ext h).symm) (hcen u (hord u hu)) (hcen v (hord v hv1))
  exact hzc (hcen z hz2)

end CFSG.ComponentClassification.Sol76T13
