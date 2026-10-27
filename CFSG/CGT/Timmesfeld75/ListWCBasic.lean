module

public import CFSG.CGT.Timmesfeld75.L2Sylow

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open

variable {G : Type*} [Group G]

theorem IsWC.mem_normalizer_of_conj {T : Subgroup G} (hT : IsWC T) {x y : G} (hx : x ∈ T)
    (hy : y ∈ T) (hy1 : y ≠ 1) {g : G} (hg : g * x * g⁻¹ = y) :
    g ∈ Subgroup.normalizer (T : Set G) := by
  have hyc : y ∈ conjSubgroup g T := by
    rw [mem_conjSubgroup, ← hg]
    simpa [mul_assoc] using hx
  refine mem_normalizer_of_conjSubgroup_eq ((hT.2 y hy hy1).2 g fun z hz => ?_)
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact elemAbelian_mul_comm (isElemAbelian_conjSubgroup hT.1 g) hz hyc

theorem IsWC.exists_normalizer_conj_of_conj {T : Subgroup G} (hT : IsWC T) {x y : G}
    (hx : x ∈ T) (hy : y ∈ T) (hy1 : y ≠ 1) {g : G} (hg : g * x * g⁻¹ = y) :
    ∃ g ∈ Subgroup.normalizer (T : Set G), g * x * g⁻¹ = y :=
  ⟨g, hT.mem_normalizer_of_conj hx hy hy1 hg, hg⟩

theorem IsWC.transitive_of_isConj {T : Subgroup G} (hT : IsWC T)
    (h : ∀ x ∈ T, x ≠ 1 → ∀ y ∈ T, y ≠ 1 → IsConj x y) :
    ∀ x ∈ T, x ≠ 1 → ∀ y ∈ T, y ≠ 1 →
      ∃ g ∈ Subgroup.normalizer (T : Set G), g * x * g⁻¹ = y := by
  intro x hx hx1 y hy hy1
  obtain ⟨g, hg⟩ := isConj_iff.1 (h x hx hx1 y hy hy1)
  exact hT.exists_normalizer_conj_of_conj hx hy hy1 hg

theorem IsWC.le_normalizer_of_le_pGroup [Finite G] {T S : Subgroup G} (hT : IsWC T)
    (hS : IsPGroup 2 S) (hTS : T ≤ S) : S ≤ Subgroup.normalizer (T : Set G) := fun _ hs =>
  mem_normalizer_of_conjSubgroup_eq
    (eq_of_conj_le_pGroup hT hS hTS (conjSubgroup_le_of_le_of_mem hTS hs))

theorem ne_bot_of_four_le_card {T : Subgroup G} (h : 4 ≤ Nat.card T) : T ≠ ⊥ := by
  rintro rfl
  rw [Subgroup.card_bot] at h
  omega

section Lift

variable {Z : Subgroup G}

theorem eq_one_of_mem_of_odd {P : Subgroup G} (hP : IsPGroup 2 P) (hZodd : Odd (Nat.card Z))
    {x : G} (hxP : x ∈ P) (hxZ : x ∈ Z) : x = 1 := by
  obtain ⟨k, hk⟩ := hP ⟨x, hxP⟩
  have h1 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one (by
    have := congrArg Subtype.val hk
    simpa using this)
  have h2 : orderOf x ∣ Nat.card Z := by
    have := orderOf_dvd_natCard (⟨x, hxZ⟩ : Z)
    rwa [Subgroup.orderOf_mk] at this
  have hcop : Nat.Coprime (2 ^ k) (Nat.card Z) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hZodd)
  exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop h1 h2)

theorem eq_one_of_mul_self_of_odd_card (hZodd : Odd (Nat.card Z)) {x : G} (hxZ : x ∈ Z)
    (hx : x * x = 1) : x = 1 :=
  eq_one_of_mem_of_odd (P := Subgroup.zpowers x)
    (isPGroup_two_zpowers_of_mul_self_eq_one hx) hZodd
    (Subgroup.mem_zpowers x) hxZ

variable [Finite G] [Z.Normal]

theorem IsWC.exists_lift_central_odd (hZc : Z ≤ Subgroup.center G) (hZodd : Odd (Nat.card Z))
    {T : Subgroup (G ⧸ Z)} (hT : IsWC T) :
    ∃ T' : Subgroup G, IsWC T' ∧ T'.map (QuotientGroup.mk' Z) = T ∧
      ∀ x ∈ T', ∀ y ∈ T', (x : G ⧸ Z) = y → x = y := by
  set C : Subgroup G := T.comap (QuotientGroup.mk' Z) with hC
  obtain ⟨P⟩ : Nonempty (Sylow 2 C) := inferInstance
  set T' : Subgroup G := (P : Subgroup C).map C.subtype with hT'
  have hT'2 : IsPGroup 2 T' := P.isPGroup'.map _
  have hT'C : T' ≤ C := Subgroup.map_subtype_le _
  have hinj : ∀ x ∈ T', ∀ y ∈ T', (x : G ⧸ Z) = y → x = y := by
    intro x hx y hy hxy
    have hmem : x⁻¹ * y ∈ Z := QuotientGroup.eq.1 hxy
    have := eq_one_of_mem_of_odd hT'2 hZodd (T'.mul_mem (T'.inv_mem hx) hy) hmem
    rw [inv_mul_eq_one] at this
    exact this
  have himg : T'.map (QuotientGroup.mk' Z) = T := by
    apply le_antisymm
    · rw [Subgroup.map_le_iff_le_comap]
      exact hT'C
    · let φ : C →* T := ((QuotientGroup.mk' Z).comp C.subtype).codRestrict T (fun c => c.2)
      have hφ : Function.Surjective φ := by
        rintro ⟨t, ht⟩
        obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective t
        exact ⟨⟨g, ht⟩, rfl⟩
      have h2T : IsPGroup 2 T := isPGroup_two_of_isElemAbelian hT.1
      let Q : Sylow 2 T := P.mapSurjective hφ
      have hQ : (Q : Subgroup T) = ⊤ := (Q.is_maximal' (h2T.to_subgroup ⊤) le_top).symm
      intro t ht
      have htQ : (⟨t, ht⟩ : T) ∈ (Q : Subgroup T) := by rw [hQ]; trivial
      obtain ⟨c, hcP, hc⟩ := htQ
      exact ⟨c, ⟨c, hcP, rfl⟩, congrArg Subtype.val hc⟩
  have hmemT : ∀ x ∈ T', ((x : G) : G ⧸ Z) ∈ T := fun x hx => by
    rw [← himg]
    exact ⟨x, hx, rfl⟩
  have hel : IsElemAbelian 2 T' := by
    refine ⟨⟨⟨fun a b => Subtype.ext (hinj _ (T'.mul_mem a.2 b.2) _ (T'.mul_mem b.2 a.2) ?_)⟩⟩,
      fun x hx => ?_⟩
    · simp only [Subgroup.coe_mul, QuotientGroup.mk_mul]
      exact elemAbelian_mul_comm hT.1 (hmemT _ a.2) (hmemT _ b.2)
    · have := hT.1.2 _ (hmemT x hx)
      exact hinj _ (T'.pow_mem hx 2) _ T'.one_mem (by rw [QuotientGroup.mk_pow, this]; rfl)
  refine ⟨T', ⟨hel, fun t ht ht1 => ⟨fun x hx => ?_, fun g hg => ?_⟩⟩, himg, hinj⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    exact elemAbelian_mul_comm hel hx ht
  · have ht1' : ((t : G) : G ⧸ Z) ≠ 1 := fun h =>
      ht1 (hinj t ht 1 T'.one_mem (by rw [h]; rfl))
    have hconj : conjSubgroup (g : G ⧸ Z) T = T := by
      refine (hT.2 _ (hmemT t ht) ht1').2 _ ?_
      rw [← himg, show ((g : G) : G ⧸ Z) = QuotientGroup.mk' Z g from rfl, ← map_conjSubgroup]
      rintro _ ⟨y, hy, rfl⟩
      have hyc := hg hy
      rw [Subgroup.mem_centralizer_singleton_iff] at hyc ⊢
      simp only [QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, hyc]
    apply conjSubgroup_eq_of_le
    intro x hx
    have hxq : ((x : G) : G ⧸ Z) ∈ T := by
      rw [← hconj, show ((g : G) : G ⧸ Z) = QuotientGroup.mk' Z g from rfl, ← himg,
        ← map_conjSubgroup]
      exact ⟨x, hx, rfl⟩
    rw [← himg] at hxq
    obtain ⟨s, hs, hsx⟩ := hxq
    have hz : s⁻¹ * x ∈ Z := QuotientGroup.eq.1 hsx
    have hxx : x * x = 1 := elemAbelian_mul_self (isElemAbelian_conjSubgroup hel g) hx
    have hss : s * s = 1 := elemAbelian_mul_self hel hs
    set z := s⁻¹ * x with hzdef
    have hxz : x = s * z := by rw [hzdef]; group
    have hzs : s * z = z * s := Subgroup.mem_center_iff.1 (hZc hz) s
    have hz2 : z * z = 1 := by
      calc z * z = s * s * (z * z) := by rw [hss, one_mul]
        _ = s * (s * z) * z := by group
        _ = s * (z * s) * z := by rw [hzs]
        _ = (s * z) * (s * z) := by group
        _ = 1 := by rw [← hxz]; exact hxx
    have hz1 := eq_one_of_mul_self_of_odd_card hZodd hz hz2
    rw [hxz, hz1, mul_one]
    exact hs

end Lift

@[expose] def WCOrderConj (M : Type) [Group M] (n : ℕ) : Prop :=
  ∀ T : Subgroup M, IsWC T → 4 ≤ Nat.card T →
    Nat.card T = n ∧ ∀ x ∈ T, x ≠ 1 → ∀ y ∈ T, y ≠ 1 → IsConj x y

end CFSG.CGT.Timmesfeld75
