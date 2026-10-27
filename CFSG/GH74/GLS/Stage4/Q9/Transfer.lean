module

public import CFSG.GH74.GLS.Stage4.Q9.Assembly
public import CFSG.GH74.GLS.Stage4.Q9.ChatOrders
public import CFSG.GH74.GLS.Stage4.Q9.Link1
public import CFSG.GH74.GLS.Stage4.Q9.Link2

public section

open scoped BigOperators Classical

namespace CFSG.GH74.GLS.Stage4.Q9

open Subgroup

@[expose] def ModelThetaData : Prop :=
  ∃ θq : Cq → ℂ, θq ∈ BlocksVChar Cq ∧ (∀ x : Cq, x ∉ Sset zq K1q K2q → θq x = 0) ∧
    BlocksInnerProduct θq θq = 3 ∧ BlocksInnerProduct θq 1 = 1 ∧ θq 1 = 0 ∧ θq zq = 0 ∧
    ∑ x ∈ (Finset.univ.filter fun x : Cq => orderOf x = 2 ∧ x ≠ zq),
      ∑ y ∈ (Finset.univ.filter fun y : Cq => orderOf y = 2 ∧ y ≠ zq), θq (x * y) = 43571520

@[expose] def ModelCounts : Prop :=
  Nat.card ↥(pSet 2 zq K1q K2q) = 42661 ∧ Nat.card ↥(pSet 3 zq K1q K2q) = 6560 ∧
    Nat.card ↥(pSet 5 zq K1q K2q) = 288

theorem blocksInnerProduct_comp_mulEquiv' {X Y : Type} [Group X] [Group Y] [Fintype X] [Fintype Y]
    (e : X ≃* Y) (f g : Y → ℂ) : BlocksInnerProduct (f ∘ e) (g ∘ e) = BlocksInnerProduct f g := by
  unfold BlocksInnerProduct
  rw [Nat.card_congr e.toEquiv]
  congr 1
  exact Fintype.sum_equiv e.toEquiv _ _ (fun x => rfl)

section Abstract

variable {G : Type} [Group G]

structure IsoC (z : G) (K₁ K₂ : Subgroup G) where
  e : Cq ≃* ↥(centralizer ({z} : Set G))
  e_z : ((e zq : ↥(centralizer ({z} : Set G))) : G) = z
  e_K₁ : ∀ x : Cq, ((e x : ↥(centralizer ({z} : Set G))) : G) ∈ K₁ ↔ x ∈ K1q
  e_K₂ : ∀ x : Cq, ((e x : ↥(centralizer ({z} : Set G))) : G) ∈ K₂ ↔ x ∈ K2q

namespace IsoC

variable {z : G} {K₁ K₂ : Subgroup G} (E : IsoC z K₁ K₂)

include E

theorem coe_eq_coe_iff {x y : Cq} :
    ((E.e x : ↥(centralizer ({z} : Set G))) : G) = ((E.e y : ↥(centralizer ({z} : Set G))) : G) ↔
      x = y :=
  ⟨fun h => E.e.injective (Subtype.ext h), fun h => by rw [h]⟩

theorem coe_eq_z_iff (x : Cq) : ((E.e x : ↥(centralizer ({z} : Set G))) : G) = z ↔ x = zq := by
  constructor
  · intro h
    apply (coe_eq_coe_iff E).mp
    rw [h]
    exact E.e_z.symm
  · intro h
    rw [h]
    exact E.e_z

theorem coe_eq_one_iff (x : Cq) : ((E.e x : ↥(centralizer ({z} : Set G))) : G) = 1 ↔ x = 1 := by
  constructor
  · intro h
    apply E.e.injective
    apply Subtype.ext
    rw [h]
    simp
  · intro h
    rw [h]
    simp

theorem orderOf_coe (x : Cq) : orderOf ((E.e x : ↥(centralizer ({z} : Set G))) : G) = orderOf x := by
  rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]

theorem mem_S2set_iff (x : Cq) :
    ((E.e x : ↥(centralizer ({z} : Set G))) : G) ∈ S2set z ↔ x ∈ S2set zq := by
  have hxC : ((E.e x : ↥(centralizer ({z} : Set G))) : G) ∈ centralizer ({z} : Set G) :=
    (E.e x).2
  constructor
  · rintro ⟨-, hz⟩
    refine ⟨mem_centralizer_zq x, ?_⟩
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hz
    refine Subgroup.mem_zpowers_iff.mpr ⟨n, ?_⟩
    apply (coe_eq_coe_iff E).mp
    have h1 : ((E.e (x ^ n) : ↥(centralizer ({z} : Set G))) : G) =
        ((E.e x : ↥(centralizer ({z} : Set G))) : G) ^ n := by
      rw [map_zpow]
      rfl
    rw [h1, hn]
    exact E.e_z.symm
  · rintro ⟨-, hz⟩
    refine ⟨hxC, ?_⟩
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hz
    refine Subgroup.mem_zpowers_iff.mpr ⟨n, ?_⟩
    have h1 : ((E.e (x ^ n) : ↥(centralizer ({z} : Set G))) : G) =
        ((E.e x : ↥(centralizer ({z} : Set G))) : G) ^ n := by
      rw [map_zpow]
      rfl
    rw [← h1, hn]
    exact E.e_z

theorem mem_S3set_iff (x : Cq) :
    ((E.e x : ↥(centralizer ({z} : Set G))) : G) ∈ S3set z ↔ x ∈ S3set zq := by
  constructor
  · rintro ⟨-, h⟩
    exact ⟨mem_centralizer_zq x, by rwa [orderOf_coe E] at h⟩
  · rintro ⟨-, h⟩
    exact ⟨(E.e x).2, by rwa [orderOf_coe E]⟩

theorem mem_S5set_iff (x : Cq) :
    ((E.e x : ↥(centralizer ({z} : Set G))) : G) ∈ S5set K₁ K₂ ↔ x ∈ S5set K1q K2q := by
  constructor
  · rintro ⟨h, h5⟩
    exact ⟨h.imp (fun h => (E.e_K₁ x).mp h) (fun h => (E.e_K₂ x).mp h), by rwa [orderOf_coe E] at h5⟩
  · rintro ⟨h, h5⟩
    exact ⟨h.imp (fun h => (E.e_K₁ x).mpr h) (fun h => (E.e_K₂ x).mpr h), by rwa [orderOf_coe E]⟩

theorem mem_Sset_iff (x : Cq) :
    ((E.e x : ↥(centralizer ({z} : Set G))) : G) ∈ Sset z K₁ K₂ ↔ x ∈ Sset zq K1q K2q := by
  unfold Sset
  simp only [Set.mem_union]
  rw [mem_S2set_iff E, mem_S3set_iff E, mem_S5set_iff E]

theorem mem_pSet_iff (p : ℕ) (x : Cq) :
    ((E.e x : ↥(centralizer ({z} : Set G))) : G) ∈ pSet p z K₁ K₂ ↔ x ∈ pSet p zq K1q K2q := by
  unfold pSet
  simp only [Set.mem_ofPred_eq]
  have h1 : ((E.e x : ↥(centralizer ({z} : Set G))) : G) ≠ 1 ↔ x ≠ 1 := not_congr (coe_eq_one_iff E x)
  rw [mem_Sset_iff E, orderOf_coe E, h1]

theorem card_pSet (hK₁ : K₁ ≤ centralizer ({z} : Set G)) (hK₂ : K₂ ≤ centralizer ({z} : Set G))
    (p : ℕ) : Nat.card ↥(pSet p z K₁ K₂) = Nat.card ↥(pSet p zq K1q K2q) := by
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (fun x => ⟨((E.e x.1 : ↥(centralizer ({z} : Set G))) : G), (mem_pSet_iff E p x.1).mpr x.2⟩)
    ⟨?_, ?_⟩)
  · intro a b h
    apply Subtype.ext
    have h' := Subtype.ext_iff.mp h
    exact (coe_eq_coe_iff E).mp h'
  · intro g
    have hgC : (g : G) ∈ centralizer ({z} : Set G) := Sset_subset_centralizer hK₁ hK₂ g.2.1
    refine ⟨⟨E.e.symm ⟨g, hgC⟩, ?_⟩, ?_⟩
    · refine (mem_pSet_iff E p _).mp ?_
      rw [MulEquiv.apply_symm_apply]
      exact g.2
    · apply Subtype.ext
      simp

theorem counts (hK₁ : K₁ ≤ centralizer ({z} : Set G)) (hK₂ : K₂ ≤ centralizer ({z} : Set G))
    (h : ModelCounts) :
    Nat.card ↥(pSet 2 z K₁ K₂) = 42661 ∧ Nat.card ↥(pSet 3 z K₁ K₂) = 6560 ∧
      Nat.card ↥(pSet 5 z K₁ K₂) = 288 := by
  obtain ⟨h2, h3, h5⟩ := h
  exact ⟨by rw [card_pSet E hK₁ hK₂, h2], by rw [card_pSet E hK₁ hK₂, h3],
    by rw [card_pSet E hK₁ hK₂, h5]⟩

theorem thetaData (h : ModelThetaData) [inst : Fintype ↥(centralizer ({z} : Set G))] :
    @ThetaData G _ z K₁ K₂ inst := by
  obtain ⟨θq, hv, hsupp, hnorm, hone, hθ1, hθz, hκ⟩ := h
  unfold ThetaData
  have hinvz : ∀ x : ↥(centralizer ({z} : Set G)),
      (orderOf x = 2 ∧ (x : G) ≠ z) ↔ (orderOf (E.e.symm x) = 2 ∧ E.e.symm x ≠ zq) := by
    intro x
    have h1 : orderOf (E.e.symm x) = orderOf x := MulEquiv.orderOf_eq E.e.symm x
    have h2 : ((x : ↥(centralizer ({z} : Set G))) : G) ≠ z ↔ E.e.symm x ≠ zq := by
      have := coe_eq_z_iff E (E.e.symm x)
      rw [MulEquiv.apply_symm_apply] at this
      exact not_congr this
    rw [h1, h2]
  refine ⟨θq ∘ E.e.symm, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact blocksVChar_comp (E.e.symm : ↥(centralizer ({z} : Set G)) →* Cq) hv
  · intro c hc
    apply hsupp
    intro hx
    apply hc
    have := (mem_Sset_iff E (E.e.symm c)).mpr hx
    rwa [MulEquiv.apply_symm_apply] at this
  · rw [blocksInnerProduct_comp_mulEquiv' E.e.symm θq θq]
    exact hnorm
  · have h1 : (1 : ↥(centralizer ({z} : Set G)) → ℂ) = (1 : Cq → ℂ) ∘ E.e.symm := rfl
    rw [h1, blocksInnerProduct_comp_mulEquiv' E.e.symm θq 1]
    exact hone
  · show θq (E.e.symm 1) = 0
    rw [map_one]
    exact hθ1
  · intro y hy
    show θq (E.e.symm y) = 0
    have : E.e.symm y = zq := by
      apply (coe_eq_z_iff E (E.e.symm y)).mp
      rw [MulEquiv.apply_symm_apply]
      exact hy
    rw [this]
    exact hθz
  · rw [← hκ]
    refine Finset.sum_equiv E.e.symm.toEquiv ?_ ?_
    · intro x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hinvz x
    · intro x hx
      refine Finset.sum_equiv E.e.symm.toEquiv ?_ ?_
      · intro y
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact hinvz y
      · intro y hy
        simp only [Function.comp_apply, map_mul]
        rfl

end IsoC

section Construction

variable {z : G} {K₁ K₂ : Subgroup G}

theorem exists_isoC_aux (π : ↥Chat →* G) (hπC : ∀ c, π c ∈ centralizer ({z} : Set G))
    (hπsurj : ∀ g ∈ centralizer ({z} : Set G), ∃ c, π c = g)
    (hπker : ∀ c : ↥Chat, π c = 1 ↔ (c : Lg × Lg) = 1 ∨ (c : Lg × Lg) = kappa0) :
    ∃ e : Cq ≃* ↥(centralizer ({z} : Set G)),
      ∀ c : ↥Chat, ((e (mkC c) : ↥(centralizer ({z} : Set G))) : G) = π c := by
  let π' : ↥Chat →* ↥(centralizer ({z} : Set G)) := π.codRestrict _ hπC
  have hker : π'.ker = zpowers kappaC := by
    ext c
    rw [MonoidHom.mem_ker, mem_zpowers_kappaC_iff]
    have h1 : π' c = 1 ↔ π c = 1 := by
      constructor
      · intro h
        exact congrArg Subtype.val h
      · intro h
        exact Subtype.ext h
    rw [h1, hπker]
    constructor
    · rintro (h | h)
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h)
    · rintro (h | h)
      · exact Or.inl (by rw [h]; rfl)
      · exact Or.inr (by rw [h]; rfl)
  have hsurj : Function.Surjective π' := fun g => by
    obtain ⟨c, hc⟩ := hπsurj g g.2
    exact ⟨c, Subtype.ext hc⟩
  refine ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective π' hsurj), fun c => ?_⟩
  rfl

theorem coe_mem_iff_mem_map {K : Subgroup G} (ψ : ↥K ≃* SL2) (ι : SL2 →* ↥Chat)
    (e : Cq ≃* ↥(centralizer ({z} : Set G))) (π : ↥Chat →* G)
    (he : ∀ c : ↥Chat, ((e (mkC c) : ↥(centralizer ({z} : Set G))) : G) = π c)
    (hι : ∀ M : SL2, π (ι M) = ((ψ.symm M : ↥K) : G)) (x : Cq) :
    ((e x : ↥(centralizer ({z} : Set G))) : G) ∈ K ↔ x ∈ (ι.range).map mkC := by
  constructor
  · intro hk
    have h1 : e (mkC (ι (ψ ⟨((e x : ↥(centralizer ({z} : Set G))) : G), hk⟩))) = e x := by
      apply Subtype.ext
      rw [he, hι, MulEquiv.symm_apply_apply]
    exact Subgroup.mem_map.mpr ⟨_, MonoidHom.mem_range.mpr ⟨_, rfl⟩, e.injective h1⟩
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨M, rfl⟩ := MonoidHom.mem_range.mp hy
    rw [he, hι]
    exact (ψ.symm M).2

variable {F₁ F₂ : Type} [Field F₁] [Field F₂]

theorem isoC (S : Q9Setting G z K₁ K₂ F₁ F₂) : Nonempty (IsoC z K₁ K₂) := by
  obtain ⟨ψ₁, ψ₂, hz₁, hz₂, ht₁, ht₂⟩ := q9_link S
  obtain ⟨ι₁, ι₂, π, hι₁, hι₂, hι₁i, hι₂i, hι₁t, hι₂t, hπC, hπsurj, hπker, hπpair, hπt⟩ :=
    q9_link2 S ψ₁ ψ₂ hz₁ hz₂ ht₁ ht₂
  obtain ⟨e, he⟩ := exists_isoC_aux π hπC hπsurj hπker
  have hinl : ∀ M : SL2, π (inl1 M) = ((ψ₁.symm M : ↥K₁) : G) := fun M => by
    have e1 : inl1 M = ⟨(innerL M, innerL 1), Chat_inner_pair M 1⟩ := Subtype.ext (by simp)
    rw [e1, hπpair M 1]
    simp
  have hinr : ∀ M : SL2, π (inr1 M) = ((ψ₂.symm M : ↥K₂) : G) := fun M => by
    have e1 : inr1 M = ⟨(innerL 1, innerL M), Chat_inner_pair 1 M⟩ := Subtype.ext (by simp)
    rw [e1, hπpair 1 M]
    simp
  refine ⟨⟨e, ?_, ?_, ?_⟩⟩
  · show ((e (mkC (inl1 minusOne)) : ↥(centralizer ({z} : Set G))) : G) = z
    rw [he, hinl]
    have hzsymm : ψ₁.symm minusOne = ⟨z, S.z_mem₁⟩ := ψ₁.symm_apply_eq.mpr (hz₁ _ rfl).symm
    rw [hzsymm]
  · intro x
    exact coe_mem_iff_mem_map ψ₁ inl1 e π he hinl x
  · intro x
    exact coe_mem_iff_mem_map ψ₂ inr1 e π he hinr x

end Construction

end Abstract

end CFSG.GH74.GLS.Stage4.Q9
