module

public import CFSG.CGT.PushingUpLit.LIT.A4.Leaves
public import CFSG.CharacterTheory.TwoRankLowerBound.CommutingInvolutions

public section

namespace CFSG.CGT.PushingUpLit.SEC

open CFSG.Open CFSG.TwoRankLowerBound.Helpers CFSG.CGT.PushingUpLit.A4

theorem eq_of_mem_sylow_of_twoRank_le_one {L : Type*} [Group L] [Finite L] (h : twoRank L ≤ 1)
    (P : Sylow 2 L) {s t : L} (hs : s ∈ (P : Subgroup L)) (ht : t ∈ (P : Subgroup L))
    (hso : orderOf s = 2) (hto : orderOf t = 2) : s = t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial (P : Subgroup L) := ⟨⟨⟨s, hs⟩, 1, fun h' => by
    have h1 : s = 1 := congrArg Subtype.val h'
    rw [h1, orderOf_one] at hso
    omega⟩⟩
  have : Nontrivial (Subgroup.center (P : Subgroup L)) := P.isPGroup'.center_nontrivial
  have hdiv : 2 ∣ Nat.card (Subgroup.center (P : Subgroup L)) := by
    rcases (P.isPGroup'.to_subgroup (Subgroup.center (P : Subgroup L))).card_eq_or_dvd with h1 | h1
    · exact absurd (Nat.card_eq_one_iff_unique.mp h1).1 (not_subsingleton _)
    · exact h1
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center (P : Subgroup L)) 2 hdiv
  have hwL : orderOf ((w : (P : Subgroup L)) : L) = 2 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hw]
  have hcomm : ∀ r : L, r ∈ (P : Subgroup L) → Commute r ((w : (P : Subgroup L)) : L) := by
    intro r hr
    have := Subgroup.mem_center_iff.mp w.2 ⟨r, hr⟩
    exact congrArg Subtype.val this
  have key : ∀ r : L, r ∈ (P : Subgroup L) → orderOf r = 2 → r = ((w : (P : Subgroup L)) : L) := by
    intro r hr hro
    by_contra hne
    have h2 := two_le_twoRank_of_commuting_involutions L r _ hro hwL hne (hcomm r hr)
    omega
  exact (key s hs hso).trans (key t ht hto).symm

theorem isConj_of_twoRank_le_one {L : Type*} [Group L] [Finite L] (h : twoRank L ≤ 1)
    {a b : L} (ha : orderOf a = 2) (hb : orderOf b = 2) : IsConj a b := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpg : ∀ s : L, orderOf s = 2 → IsPGroup 2 (Subgroup.zpowers s) := fun s hs =>
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hs]; norm_num)
  obtain ⟨Pa, hPa⟩ := (hpg a ha).exists_le_sylow
  obtain ⟨Pb, hPb⟩ := (hpg b hb).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq L Pa Pb
  have hbm : b ∈ ((g • Pa : Sylow 2 L) : Subgroup L) := by
    rw [hg]
    exact hPb (Subgroup.mem_zpowers b)
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hbm
  obtain ⟨y, hy, hyb⟩ := hbm
  have hyb' : g * y * g⁻¹ = b := by simpa [MulAut.conj_apply] using hyb
  have hyo : orderOf y = 2 := by
    have h1 : orderOf (g * y * g⁻¹) = orderOf y := by
      simpa [MulAut.conj_apply] using (MulAut.conj g).orderOf_eq y
    rw [← h1, hyb', hb]
  have hay : a = y :=
    eq_of_mem_sylow_of_twoRank_le_one h Pa (hPa (Subgroup.mem_zpowers a)) hy ha hyo
  exact isConj_iff.mpr ⟨g, by rw [hay]; exact hyb'⟩

theorem isPGroup_quotient_of_sq_mem {X : Type*} [Group X] (C : Subgroup X) [C.Normal]
    (h : ∀ a : X, a ^ 2 ∈ C) : IsPGroup 2 (X ⧸ C) := by
  intro y
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective y
  refine ⟨1, ?_⟩
  rw [pow_one, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
  exact h a

theorem noTwoQuotient_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (hA : NoTwoQuotient A) : NoTwoQuotient B := by
  intro N _ hN
  have hP : IsPGroup 2 (A ⧸ N.comap e.toMonoidHom) := by
    intro y
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨k, hk⟩ := hN (QuotientGroup.mk (e a))
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_comap]
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hk
    simpa using hk
  have htop := hA _ hP
  rw [eq_top_iff]
  intro b _
  obtain ⟨a, rfl⟩ := e.surjective b
  have : a ∈ N.comap e.toMonoidHom := htop ▸ Subgroup.mem_top a
  simpa using this

theorem noTwoQuotient_of_isSimpleGroup {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    {M : Subgroup G} (hM : M ≠ ⊤) {x : G} (hxM : x ∈ M) (hx : orderOf x = 2) : NoTwoQuotient G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro N hN hP
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  · exfalso
    have hG : IsPGroup 2 G := by
      intro g
      obtain ⟨k, hk⟩ := hP (QuotientGroup.mk g)
      refine ⟨k, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, h, Subgroup.mem_bot] at hk
      exact hk
    have : Nontrivial G := ⟨⟨x, 1, fun h1 => by rw [h1, orderOf_one] at hx; omega⟩⟩
    have : Nontrivial (Subgroup.center G) := hG.center_nontrivial
    have hc : Subgroup.center G = ⊤ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h1 | h1
      · exact absurd h1 ((Subgroup.center G).nontrivial_iff_ne_bot.mp inferInstance)
      · exact h1
    have hxc : x ∈ Subgroup.center G := hc ▸ Subgroup.mem_top x
    have : (Subgroup.zpowers x).Normal :=
      Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hxc)
    have hx1 : x ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hx; omega
    have hzp : Subgroup.zpowers x = ⊤ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.zpowers x) with h1 | h1
      · exact absurd (Subgroup.mem_bot.mp (h1 ▸ Subgroup.mem_zpowers x)) hx1
      · exact h1
    exact hM (eq_top_iff.mpr (hzp ▸ Subgroup.zpowers_le.mpr hxM))
  · exact h

end CFSG.CGT.PushingUpLit.SEC
