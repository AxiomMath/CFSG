module

public import CFSG.LargeExtraspecial.S4SevenA
public import CFSG.LargeExtraspecial.S4SevenInput

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S4

open Subgroup

universe u

variable {O : Type u} [Group O] [Finite O] {R N N0 L : Subgroup O}

omit [Finite O] in
theorem normal_subgroupOf_of_conj (hN0 : ∀ r ∈ R, ∀ x ∈ N0, r * x * r⁻¹ ∈ N0) :
    (N0.subgroupOf R).Normal :=
  ⟨fun x hx r => by
    rw [mem_subgroupOf] at hx ⊢
    exact hN0 r r.2 x hx⟩

section Quotient

variable [(N0.subgroupOf R).Normal]

@[expose] noncomputable def imgL (R N0 L : Subgroup O) [(N0.subgroupOf R).Normal] :
    Subgroup (R ⧸ N0.subgroupOf R) :=
  (L.subgroupOf R).map (QuotientGroup.mk' _)

omit [Finite O] in
theorem mk_mem_imgL_iff (hN0R : N0 ≤ R) (x : R) :
    (QuotientGroup.mk x : R ⧸ N0.subgroupOf R) ∈ imgL R N0 L ↔
      ∃ l ∈ L, l⁻¹ * (x : O) ∈ N0 := by
  constructor
  · intro hx
    obtain ⟨l, hl, hlx⟩ := hx
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq] at hlx
    exact ⟨l, hl, hlx⟩
  · intro hx
    obtain ⟨l, hl, hlx⟩ := hx
    have hlR : l ∈ R := by
      have := mul_mem x.2 (inv_mem (hN0R hlx))
      rwa [show (x : O) * (l⁻¹ * x)⁻¹ = l by group] at this
    refine ⟨⟨l, hlR⟩, hl, ?_⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq]
    exact hlx

variable {V : Type u} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] noncomputable def liftQ (φ : R →* (V ≃ₗ[ZMod 2] V)) (hN0 : N0.subgroupOf R ≤ φ.ker) :
    (R ⧸ N0.subgroupOf R) →* (V ≃ₗ[ZMod 2] V) :=
  QuotientGroup.lift _ φ hN0

omit [Finite O] in
theorem liftQ_mk (φ : R →* (V ≃ₗ[ZMod 2] V)) (hN0 : N0.subgroupOf R ≤ φ.ker) (x : R) :
    liftQ φ hN0 (QuotientGroup.mk x) = φ x :=
  QuotientGroup.lift_mk _ _ x

end Quotient

variable {V : Type u} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

theorem eq_of_centralExtInput (hCE : CentralExtInput.{u}) (hN0N : N0 ≤ N) (hNR : N ≤ R)
    (hLR : L ≤ R) (hN0 : ∀ r ∈ R, ∀ x ∈ N0, r * x * r⁻¹ ∈ N0)
    (φ : R →* (V ≃ₗ[ZMod 2] V)) (hker : ∀ x : R, φ x = 1 ↔ (x : O) ∈ N)
    {X E₀ : Subgroup (V ≃ₗ[ZMod 2] V)} {a : V} (ha : a ≠ 0) (hpair : NaturalPair X E₀ a)
    (hrange : φ.range = X) (hmapL : (L.subgroupOf R).map φ = E₀)
    (hcomm : ∀ n ∈ N, ∀ r ∈ R, n * r * n⁻¹ * r⁻¹ ∈ N0) (hLN : L ⊓ N ≤ N0)
    (hgen : R ≤ closure {u | ∃ r ∈ R, ∃ l ∈ L, u = r * l * r⁻¹})
    (hnorm : ∀ x : R, φ x a = a → (x : O) ∈ normalizer (L : Set O))
    (hwc : ∀ r ∈ R, (∀ y ∈ L.map (MulAut.conj r).toMonoidHom, ∀ l ∈ L, ∃ l' ∈ L,
      l'⁻¹ * (y * l * y⁻¹) ∈ N0) → L.map (MulAut.conj r).toMonoidHom = L) :
    N = N0 ∨ (A6Pair X E₀ a ∧ (N0.subgroupOf N).index = 3) := by
  have hNorm : (N0.subgroupOf R).Normal := normal_subgroupOf_of_conj hN0
  have hN0R : N0 ≤ R := hN0N.trans hNR
  have hφN : N0.subgroupOf R ≤ φ.ker := fun x hx => (hker x).mpr (hN0N hx)
  have hπ : ∀ x : R, liftQ φ hφN (QuotientGroup.mk x) = φ x := liftQ_mk φ hφN
  have hπ1 : ∀ x : R, liftQ φ hφN (QuotientGroup.mk x) = 1 ↔ (x : O) ∈ N := fun x => by
    rw [hπ]
    exact hker x
  have h1 : (liftQ φ hφN).range = X := by
    rw [← hrange]
    ext e
    constructor
    · intro he
      obtain ⟨q, rfl⟩ := he
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
      exact ⟨x, (hπ x).symm⟩
    · intro he
      obtain ⟨x, rfl⟩ := he
      exact ⟨QuotientGroup.mk x, hπ x⟩
  have h2 : (liftQ φ hφN).ker ≤ center (R ⧸ N0.subgroupOf R) := by
    intro q hq
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    rw [MonoidHom.mem_ker, hπ1] at hq
    rw [Subgroup.mem_center_iff]
    intro q'
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q'
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, mem_subgroupOf]
    have h := hcomm _ (inv_mem hq) _ (inv_mem y.2)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    convert h using 1
    group
  have h3 : imgL R N0 L ⊓ (liftQ φ hφN).ker = ⊥ := by
    rw [eq_bot_iff]
    intro q hq
    obtain ⟨hqE, hqK⟩ := Subgroup.mem_inf.mp hq
    obtain ⟨l, hl, rfl⟩ := hqE
    rw [MonoidHom.mem_ker, QuotientGroup.mk'_apply, hπ1] at hqK
    rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hLN (Subgroup.mem_inf.mpr ⟨hl, hqK⟩)
  have h4 : (imgL R N0 L).map (liftQ φ hφN) = E₀ := by
    rw [← hmapL]
    ext e
    constructor
    · intro he
      obtain ⟨q, ⟨l, hl, rfl⟩, rfl⟩ := he
      exact ⟨l, hl, (hπ l).symm⟩
    · intro he
      obtain ⟨l, hl, rfl⟩ := he
      exact ⟨QuotientGroup.mk l, ⟨l, hl, rfl⟩, hπ l⟩
  have h5 : closure {k | ∃ x : R ⧸ N0.subgroupOf R, ∃ e ∈ imgL R N0 L, k = x * e * x⁻¹} = ⊤ := by
    rw [eq_top_iff]
    intro q _
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    let P : Subgroup O :=
      { carrier := {y | ∃ hy : y ∈ R, (QuotientGroup.mk ⟨y, hy⟩ : R ⧸ N0.subgroupOf R) ∈
          closure {k | ∃ x : R ⧸ N0.subgroupOf R, ∃ e ∈ imgL R N0 L, k = x * e * x⁻¹}}
        mul_mem' := by
          intro y₁ y₂ h₁ h₂
          obtain ⟨h₁, h₁'⟩ := h₁
          obtain ⟨h₂, h₂'⟩ := h₂
          refine ⟨mul_mem h₁ h₂, ?_⟩
          have := mul_mem h₁' h₂'
          rwa [← QuotientGroup.mk_mul] at this
        one_mem' := ⟨one_mem _, one_mem _⟩
        inv_mem' := by
          intro y hy
          obtain ⟨hy, hy'⟩ := hy
          refine ⟨inv_mem hy, ?_⟩
          have := inv_mem hy'
          rwa [← QuotientGroup.mk_inv] at this }
    have hRP : R ≤ P := by
      refine hgen.trans ((closure_le _).mpr ?_)
      rintro _ ⟨r, hr, l, hl, rfl⟩
      refine ⟨mul_mem (mul_mem hr (hLR hl)) (inv_mem hr), subset_closure
        ⟨QuotientGroup.mk ⟨r, hr⟩, QuotientGroup.mk ⟨l, hLR hl⟩, ⟨⟨l, hLR hl⟩, hl, rfl⟩, ?_⟩⟩
      rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      exact congrArg _ (Subtype.ext rfl)
    obtain ⟨hy, hy'⟩ := hRP x.2
    exact hy'
  have h6 : ∀ q : R ⧸ N0.subgroupOf R, liftQ φ hφN q a = a →
      q ∈ normalizer (imgL R N0 L : Set (R ⧸ N0.subgroupOf R)) := by
    intro q hq
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    rw [hπ] at hq
    have hxN := hnorm x hq
    refine mem_normalizer_of_conj_le fun e he => ?_
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective e
    obtain ⟨l, hl, hly⟩ := (mk_mem_imgL_iff hN0R y).mp he
    rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
      mk_mem_imgL_iff hN0R]
    refine ⟨(x : O) * l * (x : O)⁻¹, (mem_normalizer_iff.mp hxN l).mp hl, ?_⟩
    have := hN0 _ x.2 _ hly
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    convert this using 1
    group
  have h7 : ∀ q : R ⧸ N0.subgroupOf R, (imgL R N0 L).map (MulAut.conj q).toMonoidHom ≤
      normalizer (imgL R N0 L : Set (R ⧸ N0.subgroupOf R)) →
        (imgL R N0 L).map (MulAut.conj q).toMonoidHom = imgL R N0 L := by
    intro q hq
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    have hL : L.map (MulAut.conj (x : O)).toMonoidHom = L := by
      refine hwc x x.2 fun y hy l hl => ?_
      obtain ⟨l₀, hl₀, rfl⟩ := hy
      have hmem := hq ⟨_, ⟨⟨l₀, hLR hl₀⟩, hl₀, rfl⟩, rfl⟩
      have hlE : (QuotientGroup.mk ⟨l, hLR hl⟩ : R ⧸ N0.subgroupOf R) ∈ imgL R N0 L :=
        ⟨⟨l, hLR hl⟩, hl, rfl⟩
      have h := (mem_normalizer_iff.mp hmem _).mp hlE
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, QuotientGroup.mk'_apply] at h
      rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
        ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
        mk_mem_imgL_iff hN0R] at h
      obtain ⟨l', hl', hl'N⟩ := h
      refine ⟨l', hl', ?_⟩
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply] at hl'N ⊢
      convert hl'N using 1
    have hle : (imgL R N0 L).map (MulAut.conj (QuotientGroup.mk x :
        R ⧸ N0.subgroupOf R)).toMonoidHom ≤ imgL R N0 L := by
      rintro _ ⟨e, ⟨l, hl, rfl⟩, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, QuotientGroup.mk'_apply]
      rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
        mk_mem_imgL_iff hN0R]
      refine ⟨(x : O) * l * (x : O)⁻¹, ?_, by
        convert one_mem N0 using 1
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group⟩
      rw [← hL]
      exact ⟨l, hl, rfl⟩
    exact eq_of_le_of_card_ge hle (by
      rw [card_map_of_injective (MulAut.conj _).injective])
  rcases hCE V X E₀ a ha hpair (R ⧸ N0.subgroupOf R) (liftQ φ hφN) (imgL R N0 L) h1 h2 h3 h4
      h5 h6 h7 with hk | ⟨hA6, hc⟩
  · left
    refine le_antisymm (fun n hn => ?_) hN0N
    have : (QuotientGroup.mk ⟨n, hNR hn⟩ : R ⧸ N0.subgroupOf R) ∈ (liftQ φ hφN).ker :=
      (hπ1 _).mpr hn
    rw [hk, mem_bot, QuotientGroup.eq_one_iff] at this
    exact this
  · right
    refine ⟨hA6, ?_⟩
    let f : N →* R ⧸ N0.subgroupOf R := (QuotientGroup.mk' _).comp (Subgroup.inclusion hNR)
    have hfker : f.ker = N0.subgroupOf N := by
      ext n
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff, mem_subgroupOf, mem_subgroupOf]
      rfl
    have hfrange : f.range = (liftQ φ hφN).ker := by
      ext q
      constructor
      · intro hq
        obtain ⟨n, rfl⟩ := hq
        exact (hπ1 _).mpr n.2
      · intro hq
        obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
        exact ⟨⟨x, (hπ1 x).mp hq⟩, rfl⟩
    rw [← hfker, Subgroup.index_ker, hfrange, hc]

end CFSG.LargeExtraspecial.S4
