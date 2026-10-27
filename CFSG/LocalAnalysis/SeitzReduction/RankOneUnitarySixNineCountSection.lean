module

import Mathlib.Tactic.Group
public import Mathlib.Algebra.Group.End
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.GroupTheory.QuotientGroup.Defs

public section

namespace CFSG.SeitzReduction.RankOne

namespace SixNineCount

open Subgroup

variable {G : Type*} [Group G]

structure SecHyp (U R : Subgroup G) : Prop where
  le : R ≤ U
  normal : ∀ u ∈ U, ∀ r ∈ R, u * r * u⁻¹ ∈ R
  comm : ∀ a ∈ U, ∀ b ∈ U, a * b * a⁻¹ * b⁻¹ ∈ R
  sq : ∀ a ∈ U, a ^ 2 ∈ R

section Sec

variable (U R : Subgroup G) [hUR : Fact (SecHyp U R)]

instance secNormal : (R.subgroupOf U).Normal :=
  ⟨fun n hn g => by
    rw [mem_subgroupOf] at hn ⊢
    exact hUR.out.normal g g.2 n hn⟩

instance secCommGroup : CommGroup (U ⧸ R.subgroupOf U) :=
  { (inferInstance : Group (U ⧸ R.subgroupOf U)) with
    mul_comm := by
      intro a b
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, mem_subgroupOf]
      have h := hUR.out.comm _ (U.inv_mem b.2) _ (U.inv_mem a.2)
      have e : (((a * b)⁻¹ * (b * a) : U) : G) =
          (b : G)⁻¹ * (a : G)⁻¹ * (b : G)⁻¹⁻¹ * (a : G)⁻¹⁻¹ := by
        push_cast; group
      rw [e]
      exact h }

abbrev Sec : Type _ := Additive (U ⧸ R.subgroupOf U)

@[expose] def secMk (a : U) : Sec U R := Additive.ofMul (QuotientGroup.mk a)

variable {U R}

omit hUR in
theorem secMk_surjective : Function.Surjective (secMk U R) := by
  intro v
  obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective v.toMul
  exact ⟨a, by rw [secMk, ha]; rfl⟩

omit hUR in
theorem secMk_eq_iff {a b : U} : secMk U R a = secMk U R b ↔ (a : G)⁻¹ * b ∈ R := by
  rw [secMk, secMk, Additive.ofMul.apply_eq_iff_eq, QuotientGroup.eq, mem_subgroupOf]
  push_cast
  rfl

theorem secMk_eq_zero_iff {a : U} : secMk U R a = 0 ↔ (a : G) ∈ R := by
  have h : (0 : Sec U R) = secMk U R 1 := rfl
  rw [h, secMk_eq_iff]
  constructor
  · intro h'
    have := R.inv_mem h'
    simpa using this
  · intro h'
    simpa using R.inv_mem h'

theorem secMk_add (a b : U) : secMk U R a + secMk U R b = secMk U R (a * b) := rfl

theorem Sec.add_self (v : Sec U R) : v + v = 0 := by
  obtain ⟨a, rfl⟩ := secMk_surjective v
  rw [secMk_add, secMk_eq_zero_iff]
  have h := hUR.out.sq a a.2
  rwa [pow_two] at h

instance [Finite G] : Finite (Sec U R) :=
  Finite.of_surjective (secMk U R) secMk_surjective

end Sec

section Rep

variable {U R : Subgroup G} [hUR : Fact (SecHyp U R)]

@[expose] def conjU (g : G) (hgU : g ∈ normalizer (U : Set G)) : U →* U where
  toFun u := ⟨g * u * g⁻¹, (mem_normalizer_iff.mp hgU u).mp u.2⟩
  map_one' := by ext; simp
  map_mul' a b := by ext; simp [mul_assoc]

omit hUR in
@[simp] theorem coe_conjU (g : G) (hgU : g ∈ normalizer (U : Set G)) (u : U) :
    ((conjU g hgU u : U) : G) = g * u * g⁻¹ := rfl

@[expose] def secConj (g : G) (hgU : g ∈ normalizer (U : Set G))
    (hgR : g ∈ normalizer (R : Set G)) : Sec U R →+ Sec U R :=
  MonoidHom.toAdditive (QuotientGroup.map (R.subgroupOf U) (R.subgroupOf U) (conjU g hgU) (by
    intro r hr
    rw [mem_comap, mem_subgroupOf] at *
    exact (mem_normalizer_iff.mp hgR r).mp hr))

@[expose] def secRep (N : Subgroup G) (hNU : N ≤ normalizer (U : Set G))
    (hNR : N ≤ normalizer (R : Set G)) : N →* (AddMonoid.End (Sec U R))ˣ :=
  MonoidHom.toHomUnits
    { toFun := fun g => secConj (g : G) (hNU g.2) (hNR g.2)
      map_one' := by
        ext v
        obtain ⟨a, rfl⟩ := secMk_surjective v
        change secMk U R (conjU _ _ a) = secMk U R a
        congr 1
        ext
        simp
      map_mul' := by
        intro g h
        ext v
        obtain ⟨a, rfl⟩ := secMk_surjective v
        change secMk U R (conjU _ _ a) = secMk U R (conjU _ _ (conjU _ _ a))
        congr 1
        ext
        simp [mul_assoc] }

variable {N : Subgroup G} {hNU : N ≤ normalizer (U : Set G)} {hNR : N ≤ normalizer (R : Set G)}

theorem secRep_apply (g : N) (a : U) :
    ((secRep N hNU hNR g : AddMonoid.End (Sec U R))) (secMk U R a) =
      secMk U R (conjU (g : G) (hNU g.2) a) := rfl

theorem secRep_eq_one_iff (g : N) :
    secRep N hNU hNR g = 1 ↔ ∀ a ∈ U, (g : G) * a * (g : G)⁻¹ * a⁻¹ ∈ R := by
  constructor
  · intro h a ha
    have h1 : ((secRep N hNU hNR g : AddMonoid.End (Sec U R)))
        (secMk U R ⟨a⁻¹, U.inv_mem ha⟩) = secMk U R ⟨a⁻¹, U.inv_mem ha⟩ := by
      rw [h]; rfl
    rw [secRep_apply, secMk_eq_iff] at h1
    have e : ((conjU (g : G) (hNU g.2) ⟨a⁻¹, U.inv_mem ha⟩ : U) : G)⁻¹ * a⁻¹ =
        (g : G) * a * (g : G)⁻¹ * a⁻¹ := by
      rw [coe_conjU]; group
    rwa [e] at h1
  · intro h
    apply Units.ext
    ext v
    obtain ⟨a, rfl⟩ := secMk_surjective v
    show secMk U R (conjU (g : G) (hNU g.2) a) = secMk U R a
    rw [secMk_eq_iff]
    have h1 := h _ (U.inv_mem a.2)
    have e : ((conjU (g : G) (hNU g.2) a : U) : G)⁻¹ * a =
        (g : G) * (a : G)⁻¹ * (g : G)⁻¹ * (a : G)⁻¹⁻¹ := by
      rw [coe_conjU]; group
    rw [e]
    exact h1

theorem fixed_eq_zero_of_free (g : N)
    (hfree : ∀ a ∈ U, (g : G) * a * (g : G)⁻¹ * a⁻¹ ∈ R → a ∈ R) :
    ∀ v : Sec U R, ((secRep N hNU hNR g : AddMonoid.End (Sec U R))) v = v → v = 0 := by
  intro v hv
  obtain ⟨a, rfl⟩ := secMk_surjective v
  rw [secRep_apply, secMk_eq_iff] at hv
  rw [secMk_eq_zero_iff]
  have e : ((conjU (g : G) (hNU g.2) a : U) : G)⁻¹ * a =
      (g : G) * (a : G)⁻¹ * (g : G)⁻¹ * (a : G)⁻¹⁻¹ := by
    rw [coe_conjU]; group
  rw [e] at hv
  have h1 := hfree _ (U.inv_mem a.2) hv
  simpa using R.inv_mem h1

end Rep

section Dictionary

variable {U R : Subgroup G} [hUR : Fact (SecHyp U R)]

@[expose] def secImg (Y : Subgroup G) : AddSubgroup (Sec U R) where
  carrier := {v | ∃ a : U, (a : G) ∈ Y ∧ secMk U R a = v}
  zero_mem' := ⟨1, Y.one_mem, rfl⟩
  add_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a * b, Y.mul_mem ha hb, rfl⟩
  neg_mem' := by
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨a⁻¹, Y.inv_mem ha, rfl⟩

@[expose] def secPre (W : AddSubgroup (Sec U R)) : Subgroup G where
  carrier := {g | ∃ a : U, secMk U R a ∈ W ∧ (a : G) = g}
  one_mem' := ⟨1, W.zero_mem, rfl⟩
  mul_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a * b, W.add_mem ha hb, rfl⟩
  inv_mem' := by
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨a⁻¹, W.neg_mem ha, rfl⟩

theorem secPre_le (W : AddSubgroup (Sec U R)) : secPre W ≤ U := by
  rintro _ ⟨a, _, rfl⟩
  exact a.2

theorem le_secPre (W : AddSubgroup (Sec U R)) : R ≤ secPre W := fun r hr =>
  ⟨⟨r, hUR.out.le hr⟩, by rw [secMk_eq_zero_iff.mpr hr]; exact W.zero_mem, rfl⟩

theorem secImg_secPre (W : AddSubgroup (Sec U R)) : secImg (secPre W) = W := by
  ext v
  constructor
  · rintro ⟨a, ⟨b, hb, hba⟩, rfl⟩
    have hab : a = b := Subtype.ext hba.symm
    rw [hab]
    exact hb
  · intro hv
    obtain ⟨a, rfl⟩ := secMk_surjective v
    exact ⟨a, ⟨a, hv, rfl⟩, rfl⟩

theorem secImg_eq_bot : (secImg R : AddSubgroup (Sec U R)) = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨a, ha, rfl⟩
  rw [AddSubgroup.mem_bot, secMk_eq_zero_iff]
  exact ha

theorem secImg_eq_top : (secImg U : AddSubgroup (Sec U R)) = ⊤ := by
  rw [eq_top_iff]
  intro v _
  obtain ⟨a, rfl⟩ := secMk_surjective v
  exact ⟨a, a.2, rfl⟩

theorem secPre_le_of_le {W : AddSubgroup (Sec U R)} {X : Subgroup G} (hRX : R ≤ X)
    (hW : W ≤ secImg X) : secPre W ≤ X := by
  rintro _ ⟨a, ha, rfl⟩
  obtain ⟨b, hb, hba⟩ := hW ha
  have h := secMk_eq_iff.mp hba
  have e : (a : G) = b * ((b : G)⁻¹ * a) := by group
  rw [e]
  exact X.mul_mem hb (hRX h)

theorem le_secPre_of_le {W : AddSubgroup (Sec U R)} {X : Subgroup G} (hXU : X ≤ U)
    (hW : secImg X ≤ W) : X ≤ secPre W := fun x hx =>
  ⟨⟨x, hXU hx⟩, hW ⟨⟨x, hXU hx⟩, hx, rfl⟩, rfl⟩

variable {N : Subgroup G} {hNU : N ≤ normalizer (U : Set G)} {hNR : N ≤ normalizer (R : Set G)}

theorem secImg_invariant {X : Subgroup G} (g : N) (hgX : (g : G) ∈ normalizer (X : Set G)) :
    ∀ v ∈ secImg X, ((secRep N hNU hNR g : AddMonoid.End (Sec U R))) v ∈ secImg X := by
  rintro _ ⟨a, ha, rfl⟩
  rw [secRep_apply]
  exact ⟨_, (mem_normalizer_iff.mp hgX a).mp ha, rfl⟩

theorem secPre_mem_normalizer {W : AddSubgroup (Sec U R)} (g : N)
    (hg : ∀ w ∈ W, ((secRep N hNU hNR g : AddMonoid.End (Sec U R))) w ∈ W)
    (hg' : ∀ w ∈ W, (((secRep N hNU hNR g)⁻¹ : (AddMonoid.End (Sec U R))ˣ) :
      AddMonoid.End (Sec U R)) w ∈ W) :
    (g : G) ∈ normalizer (secPre W : Set G) := by
  refine mem_normalizer_iff.mpr fun x => ⟨?_, ?_⟩
  · rintro ⟨a, ha, rfl⟩
    have h := hg _ ha
    rw [secRep_apply] at h
    exact ⟨_, h, rfl⟩
  · rintro ⟨a, ha, hax⟩
    have h := hg' _ ha
    rw [← map_inv, secRep_apply] at h
    refine ⟨_, h, ?_⟩
    rw [coe_conjU, hax]
    simp [mul_assoc]

theorem irr_low_transfer {X : Subgroup G} (hRX : R ≤ X) (ε x : N)
    (hirr : ∀ Y : Subgroup G, R ≤ Y → Y ≤ X → (ε : G) ∈ normalizer (Y : Set G) →
      (x : G) ∈ normalizer (Y : Set G) → Y = R ∨ Y = X) :
    ∀ W : AddSubgroup (Sec U R),
      (∀ g ∈ ({secRep N hNU hNR ε, secRep N hNU hNR x, (secRep N hNU hNR ε)⁻¹,
        (secRep N hNU hNR x)⁻¹} : Set (AddMonoid.End (Sec U R))ˣ),
        ∀ w ∈ W, (g : AddMonoid.End (Sec U R)) w ∈ W) →
      W ≤ secImg X → W = ⊥ ∨ W = secImg X := by
  intro W hW hWX
  have hε := secPre_mem_normalizer (hNU := hNU) (hNR := hNR) ε (hW _ (Set.mem_insert _ _))
    (hW _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))))
  have hx := secPre_mem_normalizer (hNU := hNU) (hNR := hNR) x
    (hW _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
    (hW _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))))
  rcases hirr (secPre W) (le_secPre W) (secPre_le_of_le hRX hWX) hε hx with h | h
  · left
    rw [← secImg_secPre W, h, secImg_eq_bot]
  · right
    rw [← secImg_secPre W, h]

theorem irr_high_transfer {X : Subgroup G} (hXU : X ≤ U) (ε x : N)
    (hirr : ∀ Y : Subgroup G, X ≤ Y → Y ≤ U → (ε : G) ∈ normalizer (Y : Set G) →
      (x : G) ∈ normalizer (Y : Set G) → Y = X ∨ Y = U) :
    ∀ W : AddSubgroup (Sec U R),
      (∀ g ∈ ({secRep N hNU hNR ε, secRep N hNU hNR x, (secRep N hNU hNR ε)⁻¹,
        (secRep N hNU hNR x)⁻¹} : Set (AddMonoid.End (Sec U R))ˣ),
        ∀ w ∈ W, (g : AddMonoid.End (Sec U R)) w ∈ W) →
      secImg X ≤ W → W = secImg X ∨ W = ⊤ := by
  intro W hW hXW
  have hε := secPre_mem_normalizer (hNU := hNU) (hNR := hNR) ε (hW _ (Set.mem_insert _ _))
    (hW _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))))
  have hx := secPre_mem_normalizer (hNU := hNU) (hNR := hNR) x
    (hW _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
    (hW _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))))
  rcases hirr (secPre W) (le_secPre_of_le hXU hXW) (secPre_le W) hε hx with h | h
  · left
    rw [← secImg_secPre W, h]
  · right
    rw [← secImg_secPre W, h, secImg_eq_top]

end Dictionary

end SixNineCount

end CFSG.SeitzReduction.RankOne
