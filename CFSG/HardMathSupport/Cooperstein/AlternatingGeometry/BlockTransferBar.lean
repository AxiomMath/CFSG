module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.BlockSolvableTransfer

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open Subgroup Pointwise CFSG.Open CFSG.QuasithinUnique
open CFSG.AGLEmbedding (Asc81bHyp barM)

variable {G : Type} [Group G]

theorem mem_barM_iff {X T : Subgroup G} {x : ↥X ⧸ CFSG.pCore 2 ↥X} :
    x ∈ barM X T ↔ ∃ (t : G) (ht : t ∈ X), t ∈ T ∧ QuotientGroup.mk (⟨t, ht⟩ : ↥X) = x := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.1, y.2, hy, rfl⟩
  · rintro ⟨t, ht, htT, rfl⟩
    exact ⟨⟨t, ht⟩, htT, rfl⟩

def preB (X L : Subgroup G) (Bb : Subgroup (↥X ⧸ CFSG.pCore 2 ↥X)) : Subgroup G where
  carrier := {l | l ∈ L ∧ ∃ h : l ∈ X, QuotientGroup.mk (⟨l, h⟩ : ↥X) ∈ Bb}
  mul_mem' := by
    rintro a b ⟨haL, haX, ha⟩ ⟨hbL, hbX, hb⟩
    exact ⟨L.mul_mem haL hbL, X.mul_mem haX hbX, Bb.mul_mem ha hb⟩
  one_mem' := ⟨L.one_mem, X.one_mem, Bb.one_mem⟩
  inv_mem' := by
    rintro a ⟨haL, haX, ha⟩
    exact ⟨L.inv_mem haL, X.inv_mem haX, Bb.inv_mem ha⟩

theorem preB_le_X {X L : Subgroup G} {Bb : Subgroup (↥X ⧸ CFSG.pCore 2 ↥X)} : preB X L Bb ≤ X :=
  fun _ h => h.2.1

theorem mk_eq_one_iff {X : Subgroup G} {g : G} (h : g ∈ X) :
    (QuotientGroup.mk (⟨g, h⟩ : ↥X) : ↥X ⧸ CFSG.pCore 2 ↥X) = 1 ↔ g ∈ pCoreOf 2 X := by
  rw [QuotientGroup.eq_one_iff]
  constructor
  · intro hg; exact ⟨⟨g, h⟩, hg, rfl⟩
  · rintro ⟨y, hy, hyg⟩
    have : y = ⟨g, h⟩ := Subtype.ext hyg
    rwa [this] at hy

theorem conj_mem_preB {X S L : Subgroup G} (hSX : S ≤ X) (hSL : S ≤ normalizer (L : Set G))
    {Bb : Subgroup (↥X ⧸ CFSG.pCore 2 ↥X)}
    (hnorm : ∀ s ∈ barM X S, ∀ b ∈ Bb, s * b * s⁻¹ ∈ Bb) {s : G} (hs : s ∈ S) {b : G}
    (hb : b ∈ preB X L Bb) : s * b * s⁻¹ ∈ preB X L Bb := by
  obtain ⟨hbL, hbX, hbB⟩ := hb
  refine ⟨?_, X.mul_mem (X.mul_mem (hSX hs) hbX) (X.inv_mem (hSX hs)), ?_⟩
  · exact (mem_normalizer_iff.1 (hSL hs) b).1 hbL
  · have hsm : (QuotientGroup.mk (⟨s, hSX hs⟩ : ↥X) : ↥X ⧸ CFSG.pCore 2 ↥X) ∈ barM X S :=
      mem_barM_iff.2 ⟨s, hSX hs, hs, rfl⟩
    exact hnorm _ hsm _ hbB

theorem S_le_normalizer_preB {X S L : Subgroup G} (hSX : S ≤ X) (hSL : S ≤ normalizer (L : Set G))
    {Bb : Subgroup (↥X ⧸ CFSG.pCore 2 ↥X)}
    (hnorm : ∀ s ∈ barM X S, ∀ b ∈ Bb, s * b * s⁻¹ ∈ Bb) :
    S ≤ normalizer (preB X L Bb : Set G) := by
  intro s hs
  rw [mem_normalizer_iff]
  intro b
  refine ⟨fun hb => conj_mem_preB hSX hSL hnorm hs hb, fun hb => ?_⟩
  have := conj_mem_preB hSX hSL hnorm (S.inv_mem hs) hb
  simpa [mul_assoc] using this

theorem mk_mem_of_mem_preB {X L : Subgroup G} {Bb : Subgroup (↥X ⧸ CFSG.pCore 2 ↥X)} {l : G}
    (hl : l ∈ preB X L Bb) (hX : l ∈ X) :
    (QuotientGroup.mk (⟨l, hX⟩ : ↥X) : ↥X ⧸ CFSG.pCore 2 ↥X) ∈ Bb := by
  obtain ⟨-, h0, h⟩ := hl
  exact h

theorem isSolvable_of_ker_isPGroup {A B : Type*} [Group A] [Group B] [Finite A] (f : A →* B)
    (hker : IsPGroup 2 f.ker) [Group.IsSolvable B] : Group.IsSolvable A := by
  have : Finite f.ker := inferInstance
  have h1 : Group.IsNilpotent f.ker := hker.isNilpotent
  have h2 : Group.IsSolvable f.ker := inferInstance
  exact Group.isSolvable_of_ker_le_range f.ker.subtype f (by simp)

def preBHom (X L : Subgroup G) (Bb : Subgroup (↥X ⧸ CFSG.pCore 2 ↥X)) :
    ↥(preB X L Bb) →* ↥Bb where
  toFun b := ⟨QuotientGroup.mk (⟨b.1, preB_le_X b.2⟩ : ↥X), mk_mem_of_mem_preB b.2 _⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem preBHom_ker {X L : Subgroup G} {Bb : Subgroup (↥X ⧸ CFSG.pCore 2 ↥X)}
    (b : ↥(preB X L Bb)) : b ∈ (preBHom X L Bb).ker ↔ b.1 ∈ pCoreOf 2 X := by
  rw [MonoidHom.mem_ker, ← mk_eq_one_iff (preB_le_X b.2)]
  constructor
  · intro h; exact congrArg Subtype.val h
  · intro h; exact Subtype.ext h

theorem solvable_preB [Finite G] {X L : Subgroup G} {Bb : Subgroup (↥X ⧸ CFSG.pCore 2 ↥X)}
    (hsolv : Group.IsSolvable ↥Bb) : Group.IsSolvable ↥(preB X L Bb) := by
  have : Group.IsSolvable ↥Bb := hsolv
  refine isSolvable_of_ker_isPGroup (preBHom X L Bb) ?_
  intro k
  have hk : (k : ↥(preB X L Bb)).1 ∈ pCoreOf 2 X := (preBHom_ker k.1).1 k.2
  obtain ⟨n, hn⟩ := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 X ⟨_, hk⟩
  refine ⟨n, ?_⟩
  apply Subtype.ext; apply Subtype.ext
  have := congrArg Subtype.val hn
  simpa using this

theorem preBHom_surjective {X L : Subgroup G} {Bb : Subgroup (↥X ⧸ CFSG.pCore 2 ↥X)}
    (hBL : Bb ≤ barM X L) : Function.Surjective (preBHom X L Bb) := by
  rintro ⟨x, hx⟩
  obtain ⟨l, hlX, hlL, hlx⟩ := mem_barM_iff.1 (hBL hx)
  refine ⟨⟨l, hlL, hlX, by rw [hlx]; exact hx⟩, ?_⟩
  apply Subtype.ext
  exact hlx

theorem comap_preBHom_eq {X S L : Subgroup G} (hQS : pCoreOf 2 X ≤ S)
    {Bb : Subgroup (↥X ⧸ CFSG.pCore 2 ↥X)} :
    ((barM X (S ⊓ L)).subgroupOf Bb).comap (preBHom X L Bb) =
      (S ⊓ preB X L Bb).subgroupOf (preB X L Bb) := by
  ext b
  simp only [mem_comap, mem_subgroupOf]
  constructor
  · intro h
    obtain ⟨t, htX, htSL, hteq⟩ := mem_barM_iff.1 h
    have hq : t⁻¹ * b.1 ∈ pCoreOf 2 X := by
      have h1 : (QuotientGroup.mk (⟨t⁻¹ * b.1, X.mul_mem (X.inv_mem htX) (preB_le_X b.2)⟩ : ↥X) :
          ↥X ⧸ CFSG.pCore 2 ↥X) = 1 := by
        have : (QuotientGroup.mk (⟨t⁻¹ * b.1, X.mul_mem (X.inv_mem htX) (preB_le_X b.2)⟩ : ↥X) :
            ↥X ⧸ CFSG.pCore 2 ↥X) = (QuotientGroup.mk (⟨t, htX⟩ : ↥X))⁻¹ *
              QuotientGroup.mk (⟨b.1, preB_le_X b.2⟩ : ↥X) := rfl
        rw [this, hteq]
        exact inv_mul_cancel _
      exact (mk_eq_one_iff _).1 h1
    have hbS : b.1 ∈ S := by
      have := S.mul_mem htSL.1 (hQS hq)
      simpa using this
    exact ⟨hbS, b.2⟩
  · intro h
    have hbS : b.1 ∈ S := h.1
    have hbL : b.1 ∈ L := b.2.1
    exact mem_barM_iff.2 ⟨b.1, preB_le_X b.2, ⟨hbS, hbL⟩, rfl⟩

theorem isSylowTwoOf_preB [Finite G] {X S L : Subgroup G} (hS2 : IsPGroup 2 S)
    (hQS : pCoreOf 2 X ≤ S) {Bb : Subgroup (↥X ⧸ CFSG.pCore 2 ↥X)} (hBL : Bb ≤ barM X L)
    (hodd : ¬ 2 ∣ ((barM X (S ⊓ L)).subgroupOf Bb).index) :
    IsSylowTwoOf (S ⊓ preB X L Bb) (preB X L Bb) := by
  refine ⟨inf_le_right, hS2.to_le inf_le_left, ?_⟩
  rw [← comap_preBHom_eq hQS, index_comap_of_surjective _ (preBHom_surjective hBL)]
  exact hodd

theorem hB3_preB {X L : Subgroup G} {Bb : Subgroup (↥X ⧸ CFSG.pCore 2 ↥X)} (hBL : Bb ≤ barM X L)
    (hB3 : ∀ R : Subgroup (↥X ⧸ CFSG.pCore 2 ↥X), R ≤ Bb → (∀ b ∈ Bb, ∀ r ∈ R, b * r * b⁻¹ ∈ R) →
      (∀ r ∈ R, ∃ m : ℕ, r ^ (3 ^ m) = 1) → R = ⊥) :
    ∀ R' : Subgroup G, R' ≤ preB X L Bb → (∀ b ∈ preB X L Bb, ∀ r ∈ R', b * r * b⁻¹ ∈ R') →
      (∀ r ∈ R', ∃ m : ℕ, r ^ (3 ^ m) ∈ pCoreOf 2 X) → R' ≤ pCoreOf 2 X := by
  intro R' hR'B hnorm hpow
  have hR'X : R' ≤ X := hR'B.trans preB_le_X
  set Rb : Subgroup (↥X ⧸ CFSG.pCore 2 ↥X) := (R'.subgroupOf X).map (QuotientGroup.mk' _) with hRb
  have hmemRb : ∀ r (hr : r ∈ R'),
      (QuotientGroup.mk (⟨r, hR'X hr⟩ : ↥X) : ↥X ⧸ CFSG.pCore 2 ↥X) ∈ Rb :=
    fun r hr => ⟨⟨r, hR'X hr⟩, hr, rfl⟩
  have hRbB : Rb ≤ Bb := by
    rintro _ ⟨y, hy, rfl⟩
    exact mk_mem_of_mem_preB (hR'B hy) _
  have hRbn : ∀ b ∈ Bb, ∀ r ∈ Rb, b * r * b⁻¹ ∈ Rb := by
    intro b hb r hr
    obtain ⟨l, hlX, hlL, hlb⟩ := mem_barM_iff.1 (hBL hb)
    obtain ⟨y, hy, rfl⟩ := hr
    have hlB : l ∈ preB X L Bb := ⟨hlL, hlX, by rw [hlb]; exact hb⟩
    have hlr := hnorm l hlB y.1 hy
    have : b * QuotientGroup.mk' (CFSG.pCore 2 ↥X) y * b⁻¹ =
        QuotientGroup.mk (⟨l * y.1 * l⁻¹, hR'X hlr⟩ : ↥X) := by
      rw [← hlb]; rfl
    rw [this]
    exact hmemRb _ hlr
  have hRb3 : ∀ r ∈ Rb, ∃ m : ℕ, r ^ (3 ^ m) = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨m, hm⟩ := hpow y.1 hy
    refine ⟨m, ?_⟩
    have h1 := (mk_eq_one_iff (X.pow_mem y.2 (3 ^ m))).2 hm
    have e : (⟨y.1 ^ (3 ^ m), X.pow_mem y.2 _⟩ : ↥X) = y ^ (3 ^ m) := rfl
    rw [e] at h1
    calc (QuotientGroup.mk' (CFSG.pCore 2 ↥X) y) ^ (3 ^ m)
        = QuotientGroup.mk' (CFSG.pCore 2 ↥X) (y ^ (3 ^ m)) := (map_pow _ _ _).symm
      _ = 1 := h1
  have hbot := hB3 Rb hRbB hRbn hRb3
  intro r hr
  have h1 := hmemRb r hr
  rw [hbot] at h1
  exact (mk_eq_one_iff (hR'X hr)).1 (Subgroup.mem_bot.1 h1)

theorem blockTransfer_bar [Finite G] {X S L : Subgroup G} (hA : Asc81bHyp X S)
    (hSL : S ≤ normalizer (L : Set G)) {Bb : Subgroup (↥X ⧸ CFSG.pCore 2 ↥X)}
    (hBL : Bb ≤ barM X L) (hnorm : ∀ s ∈ barM X S, ∀ b ∈ Bb, s * b * s⁻¹ ∈ Bb)
    (hsolv : Group.IsSolvable ↥Bb)
    (hodd : ¬ 2 ∣ ((barM X (S ⊓ L)).subgroupOf Bb).index)
    (hB3 : ∀ R : Subgroup (↥X ⧸ CFSG.pCore 2 ↥X), R ≤ Bb → (∀ b ∈ Bb, ∀ r ∈ R, b * r * b⁻¹ ∈ R) →
      (∀ r ∈ R, ∃ m : ℕ, r ^ (3 ^ m) = 1) → R = ⊥)
    (hLB : SolvableSylowNormalizer X S) : Bb ≤ barM X (normalizer (S : Set G) ⊓ L) := by
  have hSX : S ≤ X := hA.twoRadical.1
  have hQS : pCoreOf 2 X ≤ S := hA.twoCore_le
  have hS2 : IsPGroup 2 S := hA.twoRadical.isPGroup
  have hN := blockTransfer hA preB_le_X (S_le_normalizer_preB hSX hSL hnorm) (solvable_preB hsolv)
    (isSylowTwoOf_preB hS2 hQS hBL hodd) (hB3_preB hBL hB3) hLB
  intro x hx
  obtain ⟨l, hlX, hlL, hlx⟩ := mem_barM_iff.1 (hBL hx)
  have hlB : l ∈ preB X L Bb := ⟨hlL, hlX, by rw [hlx]; exact hx⟩
  exact mem_barM_iff.2 ⟨l, hlX, ⟨hN hlB, hlL⟩, hlx⟩

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
