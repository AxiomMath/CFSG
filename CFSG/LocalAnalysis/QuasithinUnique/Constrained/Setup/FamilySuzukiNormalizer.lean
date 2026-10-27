module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilySuzukiModule
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyBinary
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyAction
public import CFSG.LocalAnalysis.SectionRank.SuzukiCover
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.SuzukiOuterOdd

public section

namespace CFSG.QuasithinUnique.Setup.Family

open Module CFSG.Quasithin CFSG.Blueprint CFSG.LieType.Ree

section Conjugation

variable {G : Type} [Group G] {H L : Subgroup G}

@[expose] def conjActionL (hLH : L ≤ H) (hLn : (L.subgroupOf H).Normal) : ↥H →* MulAut ↥L where
  toFun := conjAutL hLH hLn
  map_one' := MulEquiv.ext fun l => Subtype.ext (by simp [conjAutL_apply])
  map_mul' a b := MulEquiv.ext fun l => Subtype.ext (by simp [conjAutL_apply, mul_assoc])

end Conjugation

theorem suzuki_irreducible_normalizer_excludes
    (a : ℕ) (ha : 1 ≤ a) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1))
    (W : Type) [CommGroup W] [Finite W] [Nontrivial W] (hW : ∀ w : W, w * w = 1)
    (L : Subgroup (MulAut W)) (hLperf : Group.IsPerfect ↥L)
    (hLirr : ∀ U : Subgroup W, (∀ g ∈ L, ∀ u ∈ U, g u ∈ U) → U = ⊥ ∨ U = ⊤)
    (α : CQ L ≃* suzukiGroup a K) :
    Subgroup.center ↥L = ⊥ ∧
    Function.Bijective (fun l : ↥L => α (QuotientGroup.mk l)) ∧
    (∀ P : Subgroup (MulAut W), IsPGroup 2 P → P ≤ Subgroup.normalizer (L : Set (MulAut W)) →
      P ≤ L) ∧
    (∀ l : ↥L, orderOf l = 2 →
      2 ^ ((2 * a + 1) + 1) ≤ Nat.card (Set.range fun v : W => (l : MulAut W) v * v⁻¹)) ∧
    (∀ A : Subgroup (MulAut W), A ≠ ⊥ → IsElemAbelian2 A →
      A ≤ Subgroup.normalizer (L : Set (MulAut W)) →
      Nat.card A * Nat.card (fixV A) < Nat.card W) := by
  classical
  have : Fact (∀ w : W, w * w = 1) := ⟨hW⟩
  have hZodd := odd_card_center_of_irreducible hW hLirr
  let e := CFSG.ShultStronglyClosedTI.SuzukiModel.suzukiGroupEquivSuzukiMatrixGroup (a := a) hK
  let α' : CQ L ≃* CFSG.BenderSuzuki.MatrixGroups.SuzukiMatrixGroup a := α.trans e
  let π : ↥L →* CFSG.BenderSuzuki.MatrixGroups.SuzukiMatrixGroup a :=
    α'.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))
  have hπ : Function.Surjective π := α'.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = Subgroup.center ↥L := CFSG.SectionRank.center_eq_ker_of_mulEquiv α'
  have : Group.IsPerfect ↥L := hLperf
  have hZ : Subgroup.center ↥L = ⊥ := by
    have h := CFSG.SectionRank.suzuki_perfect_odd_cover_trivial a (by omega) π hπ hker.le
      (hker ▸ hZodd)
    rwa [hker] at h
  have hbij : Function.Bijective (fun l : ↥L => α (QuotientGroup.mk l)) := by
    constructor
    · intro l l' h
      have h1 : (QuotientGroup.mk l : CQ L) = QuotientGroup.mk l' := α.injective h
      rw [QuotientGroup.eq, hZ, Subgroup.mem_bot, inv_mul_eq_one] at h1
      exact h1
    · intro s
      obtain ⟨q, rfl⟩ := α.surjective s
      obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
      exact ⟨l, rfl⟩
  let θ : ↥L ≃* suzukiGroup a K :=
    MulEquiv.ofBijective (α.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))) hbij
  have hP2 : ∀ P : Subgroup (MulAut W), IsPGroup 2 P →
      P ≤ Subgroup.normalizer (L : Set (MulAut W)) → P ≤ L := by
    intro P hP hPN
    have hLN : L ≤ Subgroup.normalizer (L : Set (MulAut W)) := Subgroup.le_normalizer
    have hLn : (L.subgroupOf (Subgroup.normalizer (L : Set (MulAut W)))).Normal :=
      (Subgroup.normal_subgroupOf_iff hLN).2
        fun h k hh hk => (Subgroup.mem_normalizer_iff.1 hk h).1 hh
    let ψ : ↥P →* MulAut (suzukiGroup a K) :=
      (MulAut.congr θ).toMonoidHom.comp ((conjActionL hLN hLn).comp (Subgroup.inclusion hPN))
    have hψ2 : IsPGroup 2 ↥ψ.range := hP.of_surjective ψ.rangeRestrict ψ.rangeRestrict_surjective
    have hinner :=
      (CFSG.ProperTwoGeneratedCore.HighRankPair.suzuki_outer_automorphism_group_has_odd_order
        ha hK).2 _ hψ2
    refine le_of_inner_action (L := L) (P := P) ?_ ?_ ?_ ?_
    · intro x hx hxc
      have hmem : (⟨x, hx⟩ : ↥L) ∈ Subgroup.center ↥L := by
        rw [Subgroup.mem_center_iff]
        intro g
        exact Subtype.ext ((hxc g g.2).symm)
      rw [hZ, Subgroup.mem_bot] at hmem
      exact congrArg Subtype.val hmem
    · exact fun z hz k hk => eq_one_of_pow_two_pow hW hLirr hz k hk
    · intro p hp
      exact exists_pow_two_pow_eq_one hP hp
    · intro p hp
      obtain ⟨s, hs⟩ := hinner (⟨⟨p, hp⟩, rfl⟩ : ψ ⟨p, hp⟩ ∈ ψ.range)
      refine ⟨(θ.symm s : ↥L), (θ.symm s).2, fun y hy => ?_⟩
      have hφ : MulAut.congr θ (conjActionL hLN hLn (Subgroup.inclusion hPN ⟨p, hp⟩)) =
          MulAut.conj s := hs.symm
      have h1 := eq_conj_of_congr_eq_conj θ _ s hφ ⟨y, hy⟩
      have h2 := congrArg Subtype.val h1
      exact h2
  let ρ0 : suzukiGroup a K →* MulAut W := L.subtype.comp θ.symm.toMonoidHom
  have hρ0 : Function.Injective ρ0 := L.subtype_injective.comp θ.symm.injective
  let ρ' : suzukiGroup a K →* (Additive W ≃ₗ[ZMod 2] Additive W) := binaryLin.comp ρ0
  have hρ' : Function.Injective ρ' := binaryLin_injective.comp hρ0
  obtain ⟨hrank, hcard⟩ := suzuki_excludes_faithful_binary_FF hK ρ' hρ'
  refine ⟨hZ, hbij, hP2, ?_, ?_⟩
  · intro l hl
    have ht : orderOf (θ l) = 2 := by rw [MulEquiv.orderOf_eq]; exact hl
    have h1 := hrank (θ l) ht
    have h2 : ρ' (θ l) = binaryLin (l : MulAut W) := by simp [ρ', ρ0]
    rw [h2] at h1
    rw [card_range_displacement]
    exact Nat.pow_le_pow_right (by norm_num) h1
  · intro A hA0 hAel hAN
    have hAsq : ∀ x ∈ A, x * x = 1 := fun x hx => by
      rw [← pow_two]; exact hAel.2 x hx
    have hAL : A ≤ L := hP2 A (isPGroup_two_of_mul_self_eq_one A hAsq) hAN
    let A₀ : Subgroup (suzukiGroup a K) := (A.subgroupOf L).map θ.toMonoidHom
    have hA₀mem : ∀ g, g ∈ A₀ ↔ ∃ x : ↥L, (x : MulAut W) ∈ A ∧ θ x = g := by
      intro g
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x, hx, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x, hx, rfl⟩
    have hA₀ne : A₀ ≠ ⊥ := by
      obtain ⟨x, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hA0
      intro h
      have hxA : (x : MulAut W) ∈ A := x.2
      have : θ ⟨x, hAL hxA⟩ ∈ A₀ := (hA₀mem _).2 ⟨⟨x, hAL hxA⟩, hxA, rfl⟩
      rw [h, Subgroup.mem_bot] at this
      have h3 : (⟨x, hAL hxA⟩ : ↥L) = 1 := θ.injective (this.trans (map_one θ).symm)
      have h4 : ((⟨x, hAL hxA⟩ : ↥L) : MulAut W) = ((1 : ↥L) : MulAut W) :=
        congrArg Subtype.val h3
      exact hx1 (Subtype.ext h4)
    have hA₀c : ∀ x ∈ A₀, ∀ y ∈ A₀, x * y = y * x := by
      intro x hx y hy
      obtain ⟨u, hu, rfl⟩ := (hA₀mem x).1 hx
      obtain ⟨v, hv, rfl⟩ := (hA₀mem y).1 hy
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hAel.1 _ hu _ hv)
    have hA₀sq : ∀ x ∈ A₀, x * x = 1 := by
      intro x hx
      obtain ⟨u, hu, rfl⟩ := (hA₀mem x).1 hx
      rw [← map_mul, ← map_one θ]
      congr 1
      exact Subtype.ext (hAsq _ hu)
    have h1 := hcard A₀ hA₀ne hA₀c hA₀sq
    have hc1 : Nat.card A₀ = Nat.card A := by
      rw [Subgroup.card_map_of_injective (f := θ.toMonoidHom) θ.injective]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAL).toEquiv
    have hc2 : Nat.card {w : Additive W // ∀ g ∈ A₀, ρ' g w = w} = Nat.card (fixV A) := by
      refine (card_fixed_binaryLin ρ0 A₀).trans (Nat.card_congr (Equiv.subtypeEquiv (Equiv.refl W)
        fun w => ?_))
      constructor
      · intro h
        refine mem_fixV.2 fun x hx => ?_
        have := h (θ ⟨x, hAL hx⟩) ((hA₀mem _).2 ⟨⟨x, hAL hx⟩, hx, rfl⟩)
        simpa [ρ0] using this
      · intro h g hg
        obtain ⟨u, hu, rfl⟩ := (hA₀mem g).1 hg
        have := mem_fixV.1 h _ hu
        simpa [ρ0] using this
    have hc3 : Nat.card (Additive W) = Nat.card W := Nat.card_congr Additive.toMul
    rw [hc1, hc2, hc3] at h1
    exact h1

end CFSG.QuasithinUnique.Setup.Family
