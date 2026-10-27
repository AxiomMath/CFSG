module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanFixedThreeGroup

public section

namespace CFSG.HardMathSupport.Lang.Coordinator

open CFSG.ComponentClassification.PerfectAutomorphisms (onCenterQuotient onCenterQuotient_apply_mk
  centerQuotientHom)
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer centerQuotientOuterHom
  centerQuotient_outer_injective)
open CFSG.AGLEmbedding.FixedThree (FixedThreeConclusion isPGroup_zpowers_of_pow_eq_one)

@[expose] def ThreePrimeFixedRich {K : Type*} [Group K] (β : MulAut K) : Prop :=
  ∃ S : Set K, (∀ s ∈ S, Nat.Coprime (orderOf s) 3 ∧ β s = s) ∧
    3 ∣ Nat.card (Subgroup.closure S) ∧ Nat.card (Subgroup.closure S) ≠ 0

theorem card_closure_image_mulEquiv {K K' : Type*} [Group K] [Group K'] (e : K ≃* K')
    (S : Set K) : Nat.card (Subgroup.closure (e '' S)) = Nat.card (Subgroup.closure S) := by
  have h : Subgroup.closure (e '' S) = (Subgroup.closure S).map e.toMonoidHom := by
    rw [MonoidHom.map_closure]
    rfl
  rw [h]
  exact Nat.card_congr ((Subgroup.closure S).equivMapOfInjective e.toMonoidHom
    e.injective).toEquiv.symm

theorem ThreePrimeFixedRich.map_equiv {K K' : Type*} [Group K] [Group K'] {β : MulAut K}
    (h : ThreePrimeFixedRich β) (e : K ≃* K') :
    ThreePrimeFixedRich ((e.symm.trans β).trans e) := by
  obtain ⟨S, hS, h3, h0⟩ := h
  refine ⟨e '' S, ?_, ?_, ?_⟩
  · rintro _ ⟨s, hs, rfl⟩
    refine ⟨by rw [MulEquiv.orderOf_eq]; exact (hS s hs).1, ?_⟩
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply, (hS s hs).2]
  · rwa [card_closure_image_mulEquiv]
  · rwa [card_closure_image_mulEquiv]

theorem ThreePrimeFixedRich.of_pair {K : Type*} [Group K] [Finite K] {β : MulAut K} {x y : K}
    (hx : β x = x) (hy : β y = y) (ox : Nat.Coprime (orderOf x) 3)
    (oy : Nat.Coprime (orderOf y) 3) (oxy : orderOf (x * y) = 3) : ThreePrimeFixedRich β := by
  refine ⟨{x, y}, ?_, ?_, Nat.card_pos.ne'⟩
  · rintro s (rfl | rfl)
    · exact ⟨ox, hx⟩
    · exact ⟨oy, hy⟩
  · have hxy : x * y ∈ Subgroup.closure ({x, y} : Set K) :=
      Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
    have := orderOf_dvd_natCard (⟨x * y, hxy⟩ : Subgroup.closure ({x, y} : Set K))
    rwa [Subgroup.orderOf_mk, oxy] at this

section Lift

variable {G : Type*} [Group G] [Finite G]

theorem exists_mk_eq_coprime_three (hZ : IsPGroup 3 (Subgroup.center G))
    (x : G ⧸ Subgroup.center G) (hx : Nat.Coprime (orderOf x) 3) :
    ∃ y : G, (QuotientGroup.mk y : G ⧸ Subgroup.center G) = x ∧ Nat.Coprime (orderOf y) 3 := by
  obtain ⟨y₀, rfl⟩ := QuotientGroup.mk_surjective x
  set m := orderOf (QuotientGroup.mk y₀ : G ⧸ Subgroup.center G) with hm
  have hm0 : 0 < m := orderOf_pos _
  have hmZ : y₀ ^ m ∈ Subgroup.center G := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hm, pow_orderOf_eq_one]
  obtain ⟨k, hk⟩ := hZ ⟨y₀ ^ m, hmZ⟩
  have hk' : (y₀ ^ m) ^ 3 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hcop : Nat.Coprime (3 ^ k) m := Nat.Coprime.pow_left k hx.symm
  obtain ⟨t, ht⟩ := exists_pow_eq_self_of_coprime (x := (QuotientGroup.mk y₀ :
    G ⧸ Subgroup.center G)) hcop
  refine ⟨y₀ ^ (3 ^ k * t), ?_, ?_⟩
  · rw [QuotientGroup.mk_pow, pow_mul, ht]
  · have h1' : (y₀ ^ (3 ^ k * t)) ^ m = 1 := by
      rw [← pow_mul, show 3 ^ k * t * m = m * 3 ^ k * t by ring, pow_mul, pow_mul, hk', one_pow]
    exact Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one h1') hx

omit [Finite G] in
theorem apply_eq_of_coprime_three (hZ : IsPGroup 3 (Subgroup.center G)) (α : MulAut G) {y : G}
    (hy : Nat.Coprime (orderOf y) 3)
    (hfix : onCenterQuotient α (QuotientGroup.mk' (Subgroup.center G) y) =
      QuotientGroup.mk' (Subgroup.center G) y) : α y = y := by
  rw [onCenterQuotient_apply_mk, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq] at hfix
  set c := (α y)⁻¹ * y with hc
  have hcZ : c ∈ Subgroup.center G := hfix
  have hcomm : Commute c (α y) := ((Subgroup.mem_center_iff.mp hcZ) (α y)).symm
  have hy' : y = α y * c := by rw [hc, mul_inv_cancel_left]
  have hord : orderOf (α y) = orderOf y := MulEquiv.orderOf_eq α y
  have hm1 : y ^ orderOf y = 1 := pow_orderOf_eq_one y
  have hm2 : (α y) ^ orderOf y = 1 := by rw [← hord]; exact pow_orderOf_eq_one (α y)
  have hcm : c ^ orderOf y = 1 := by
    have h1 : (α y * c) ^ orderOf y = (α y) ^ orderOf y * c ^ orderOf y :=
      hcomm.symm.mul_pow (orderOf y)
    rw [← hy', hm1, hm2, one_mul] at h1
    exact h1.symm
  obtain ⟨k, hk⟩ := hZ ⟨c, hcZ⟩
  have hk' : c ^ 3 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hc1 : orderOf c ∣ Nat.gcd (orderOf y) (3 ^ k) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hcm) (orderOf_dvd_of_pow_eq_one hk')
  rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right k hy)] at hc1
  have : c = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp hc1)
  rw [this, mul_one] at hy'
  exact hy'.symm

theorem exists_fixed_three_elt_of_rich (hZ : IsPGroup 3 (Subgroup.center G)) (α : MulAut G)
    (h : ThreePrimeFixedRich (onCenterQuotient α)) :
    ∃ g : G, (∃ k : ℕ, g ^ 3 ^ k = 1) ∧ α g = g ∧ g ∉ Subgroup.center G := by
  classical
  obtain ⟨S, hS, h3, -⟩ := h
  have hlift : ∀ s ∈ S, ∃ y : G, (QuotientGroup.mk y : G ⧸ Subgroup.center G) = s ∧
      Nat.Coprime (orderOf y) 3 := fun s hs => exists_mk_eq_coprime_three hZ s (hS s hs).1
  choose! ℓ hℓ using hlift
  set T : Set G := ℓ '' S with hT
  have hTfix : ∀ t ∈ T, α t = t := by
    rintro _ ⟨s, hs, rfl⟩
    refine apply_eq_of_coprime_three hZ α (hℓ s hs).2 ?_
    rw [QuotientGroup.mk'_apply, (hℓ s hs).1]
    exact (hS s hs).2
  set F : Subgroup G := MonoidHom.eqLocus (α : G →* G) (MonoidHom.id G) with hF
  have hTF : Subgroup.closure T ≤ F := (Subgroup.closure_le F).2 fun t ht => hTfix t ht
  have himage : (Subgroup.closure T).map (QuotientGroup.mk' (Subgroup.center G)) =
      Subgroup.closure S := by
    rw [MonoidHom.map_closure, hT, Set.image_image]
    congr 1
    calc (fun s => QuotientGroup.mk' (Subgroup.center G) (ℓ s)) '' S = (fun s => s) '' S :=
          Set.image_congr fun s hs => by rw [QuotientGroup.mk'_apply, (hℓ s hs).1]
      _ = S := Set.image_id' S
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.closure S) 3 h3
  have hxmem : (x : G ⧸ Subgroup.center G) ∈
      (Subgroup.closure T).map (QuotientGroup.mk' (Subgroup.center G)) := by
    rw [himage]
    exact x.2
  obtain ⟨g₀, hg₀T, hg₀x⟩ := Subgroup.mem_map.mp hxmem
  have hxord : orderOf (x : G ⧸ Subgroup.center G) = 3 := by
    rw [Subgroup.orderOf_coe]
    exact hx
  obtain ⟨e, m, hm3, hme⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos g₀).ne' 3
    (by norm_num)
  refine ⟨g₀ ^ m, ⟨e, ?_⟩, ?_, ?_⟩
  · rw [← pow_mul, mul_comm, ← hme, pow_orderOf_eq_one]
  · rw [map_pow, show α g₀ = g₀ from hTF hg₀T]
  · intro hmem
    have h1 : (QuotientGroup.mk' (Subgroup.center G) (g₀ ^ m)) = 1 :=
      (QuotientGroup.eq_one_iff _).2 hmem
    rw [map_pow, hg₀x] at h1
    have h2 := orderOf_dvd_of_pow_eq_one h1
    rw [hxord] at h2
    exact hm3 h2

end Lift

@[expose] noncomputable def centerQuotientConj {X : Type*} [Group X] (L : Subgroup X) {u : X}
    (huN : u ∈ Subgroup.normalizer (L : Set X)) : MulAut (L ⧸ Subgroup.center L) :=
  onCenterQuotient (L.normalizerMonoidHom ⟨u, huN⟩)

theorem centerQuotientConj_mk {X : Type*} [Group X] (L : Subgroup X) {u : X}
    (huN : u ∈ Subgroup.normalizer (L : Set X)) (l : L) :
    centerQuotientConj L huN (QuotientGroup.mk l) =
      QuotientGroup.mk (L.normalizerMonoidHom ⟨u, huN⟩ l) :=
  onCenterQuotient_apply_mk _ l

theorem centerQuotientConj_eq {X : Type*} [Group X] (L : Subgroup X) {u : X}
    (huN : u ∈ Subgroup.normalizer (L : Set X)) :
    centerQuotientConj L huN = centerQuotientHom L (L.normalizerMonoidHom ⟨u, huN⟩) :=
  rfl

theorem centerQuotientConj_pow_three {X : Type*} [Group X] (L : Subgroup X) {u : X}
    (huN : u ∈ Subgroup.normalizer (L : Set X)) (hu3 : u ^ 3 = 1) :
    centerQuotientConj L huN ^ 3 = 1 := by
  rw [centerQuotientConj_eq, ← map_pow, ← map_pow]
  have : (⟨u, huN⟩ : Subgroup.normalizer (L : Set X)) ^ 3 = 1 := Subtype.ext (by simpa using hu3)
  rw [this, map_one, map_one]

theorem centerQuotientConj_not_mem_inner {X : Type*} [Group X] {L : Subgroup X}
    (hperf : Group.IsPerfect L) {u : X}
    (huN : u ∈ Subgroup.normalizer (L : Set X))
    (hin : ∀ a ∈ L, ∃ l ∈ L, u * l * u⁻¹ ≠ a * l * a⁻¹) :
    centerQuotientConj L huN ∉ inner (L ⧸ Subgroup.center L) := by
  intro hmem
  set α : MulAut L := L.normalizerMonoidHom ⟨u, huN⟩ with hα
  have h1 : centerQuotientOuterHom L (QuotientGroup.mk' (inner L) α) = 1 := by
    change QuotientGroup.mk' (inner (L ⧸ Subgroup.center L)) (centerQuotientHom L α) = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hmem
  have h2 : QuotientGroup.mk' (inner L) α = 1 :=
    centerQuotient_outer_injective L (h1.trans (map_one _).symm)
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
  obtain ⟨a, ha⟩ := h2
  obtain ⟨l, hl, hne⟩ := hin a a.2
  apply hne
  have := congrArg (fun f : MulAut L => ((f ⟨l, hl⟩ : L) : X)) ha
  simpa [hα] using this.symm

theorem fixedThreeConclusion_of_rich {X : Type} [Group X] [Finite X] {L : Subgroup X}
    (hZ : IsPGroup 3 (Subgroup.center L)) {u : X} (huN : u ∈ Subgroup.normalizer (L : Set X))
    (h : ThreePrimeFixedRich (centerQuotientConj L huN)) : FixedThreeConclusion L u := by
  obtain ⟨g, ⟨k, hk⟩, hfix, hnc⟩ := exists_fixed_three_elt_of_rich hZ _ h
  left
  refine ⟨g, g.2, isPGroup_zpowers_of_pow_eq_one (k := k) ?_, ?_, ?_⟩
  · have := congrArg Subtype.val hk
    simpa using this
  · have h1 := congrArg Subtype.val hfix
    change u * (g : X) * u⁻¹ = g at h1
    calc (g : X) * u = u * g * u⁻¹ * u := by rw [h1]
      _ = u * g := by group
  · by_contra hall
    push Not at hall
    apply hnc
    rw [Subgroup.mem_center_iff]
    intro l
    exact Subtype.ext (hall l l.2).symm

end CFSG.HardMathSupport.Lang.Coordinator
