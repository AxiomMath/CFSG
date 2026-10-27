module

public import CFSG.RankThree.PartTwo.Sec5.Tools
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section
namespace CFSG.AGLEmbedding

open CFSG.Open

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

omit [Finite G] [Fact p.Prime] in
theorem mem_center_subtype_iff {X : Subgroup G} (x : X) :
    x ∈ Subgroup.center X ↔ (x : G) ∈ Subgroup.centralizer (X : Set G) := by
  rw [Subgroup.mem_center_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h y hy
    exact congrArg Subtype.val (h ⟨y, hy⟩)
  · intro h y
    exact Subtype.ext (h y y.2)

theorem card_commutator_of_extraspecial {X : Subgroup G} (hcard : Nat.card X = p ^ 3)
    (hZ : ⁅X, X⁆ = X ⊓ Subgroup.centralizer (X : Set G)) :
    Nat.card (⁅X, X⁆ : Subgroup G) = p := by
  have hp : p.Prime := Fact.out
  set Z := ⁅X, X⁆ with hZdef
  have hZX : Z ≤ X := Subgroup.commutator_le_self X
  have hnab : ¬ ∀ a b : X, a * b = b * a := by
    intro hab
    have hbot : Z = ⊥ := by
      rw [hZdef, Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact congrArg Subtype.val (hab ⟨y, hy⟩ ⟨x, hx⟩)
    have hXC : X ≤ Subgroup.centralizer (X : Set G) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact congrArg Subtype.val (hab ⟨y, hy⟩ ⟨x, hx⟩)
    have hX : X = ⊥ := by
      rw [← inf_of_le_left hXC, ← hZ, hbot]
    rw [hX, Subgroup.card_bot] at hcard
    have := Nat.one_lt_pow (by norm_num : 3 ≠ 0) hp.one_lt
    omega
  obtain ⟨k, hk3, hk⟩ := (Nat.dvd_prime_pow hp).mp (hcard ▸ Subgroup.card_dvd_of_le hZX)
  have hcen : (Subgroup.center X).map X.subtype = Z := by
    rw [hZ]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, (mem_center_subtype_iff y).mp hy⟩
    · rintro ⟨hxX, hxC⟩
      exact ⟨⟨x, hxX⟩, (mem_center_subtype_iff ⟨x, hxX⟩).mpr hxC, rfl⟩
  have hcenc : Nat.card (Subgroup.center X) = Nat.card Z := by
    rw [← hcen, Subgroup.card_map_of_injective X.subtype_injective]
  interval_cases k
  · exfalso
    apply hnab
    intro a b
    have h1 : Nat.card (Subgroup.center X) = 1 := by rw [hcenc, hk, pow_zero]
    have hbot : Subgroup.center X = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
    have hZbot : Z = ⊥ := by rw [← hcen, hbot, Subgroup.map_bot]
    have := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hZbot
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (this b.2) a a.2)
  · simpa using hk
  · exfalso
    apply hnab
    have hq : Nat.card (↥X ⧸ Subgroup.center X) = p := by
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center X)
      rw [hcenc, hk, hcard] at h1
      have h2 : p ^ 3 = p * p ^ 2 := by ring
      rw [h2] at h1
      exact (Nat.eq_of_mul_eq_mul_right (pow_pos hp.pos 2) h1).symm
    have : IsCyclic (↥X ⧸ Subgroup.center X) := isCyclic_of_prime_card hq
    have hc := MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center
      (QuotientGroup.mk' (Subgroup.center X)) (le_of_eq (QuotientGroup.ker_mk' _))
    exact fun a b => hc.is_comm.comm a b
  · exfalso
    apply hnab
    have hZX' : Z = X := Subgroup.eq_of_le_of_card_ge hZX (by rw [hk, hcard])
    intro a b
    have hb : (b : G) ∈ Subgroup.centralizer (X : Set G) := by
      have : (b : G) ∈ Z := hZX'.symm ▸ b.2
      rw [hZ] at this
      exact this.2
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hb a a.2)

theorem commutator_le_of_normal_of_extraspecial {X N : Subgroup G} (hcard : Nat.card X = p ^ 3)
    (hZ : ⁅X, X⁆ = X ⊓ Subgroup.centralizer (X : Set G)) (hNX : N ≤ X)
    (hXN : X ≤ Subgroup.normalizer (N : Set G)) (hN : N ≠ ⊥) : ⁅X, X⁆ ≤ N := by
  have hp : p.Prime := Fact.out
  set N' : Subgroup X := N.subgroupOf X with hN'
  have hN'n : N'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNX).mpr hXN
  have hXp : IsPGroup p X := IsPGroup.of_card hcard
  have : Group.IsNilpotent X := hXp.isNilpotent
  have hN'bot : N' ≠ ⊥ := by
    intro h
    apply hN
    rw [eq_bot_iff]
    intro n hn
    have : (⟨n, hNX hn⟩ : X) ∈ N' := Subgroup.mem_subgroupOf.mpr hn
    rw [h, Subgroup.mem_bot] at this
    simpa using congrArg Subtype.val this
  have hne := Group.IsNilpotent.inf_center_ne_bot_of_normal hN'bot
  have hcen : (Subgroup.center X).map X.subtype = ⁅X, X⁆ := by
    rw [hZ]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, (mem_center_subtype_iff y).mp hy⟩
    · rintro ⟨hxX, hxC⟩
      exact ⟨⟨x, hxX⟩, (mem_center_subtype_iff ⟨x, hxX⟩).mpr hxC, rfl⟩
  have hcenc : Nat.card (Subgroup.center X) = p := by
    rw [← card_commutator_of_extraspecial hcard hZ, ← hcen,
      Subgroup.card_map_of_injective X.subtype_injective]
  have hle : Subgroup.center X ≤ N' := by
    set W := (N' ⊓ Subgroup.center X).subgroupOf (Subgroup.center X) with hW
    have : Fact (Nat.card (Subgroup.center X)).Prime := ⟨hcenc ▸ hp⟩
    rcases Subgroup.eq_bot_or_eq_top_of_prime_card W with hW0 | hW1
    · exfalso
      apply hne
      rw [eq_bot_iff]
      intro x hx
      have : (⟨x, hx.2⟩ : Subgroup.center X) ∈ W := Subgroup.mem_subgroupOf.mpr hx
      rw [hW0, Subgroup.mem_bot] at this
      simpa using congrArg Subtype.val this
    · intro x hx
      have : (⟨x, hx⟩ : Subgroup.center X) ∈ W := hW1 ▸ Subgroup.mem_top _
      exact (Subgroup.mem_subgroupOf.mp this).1
  rw [← hcen]
  rintro _ ⟨x, hx, rfl⟩
  exact Subgroup.mem_subgroupOf.mp (hle hx)

theorem exists_elemAbelian_sq_of_extraspecial {X : Subgroup G} (hcard : Nat.card X = p ^ 3)
    (hZ : ⁅X, X⁆ = X ⊓ Subgroup.centralizer (X : Set G)) (hexp : ∀ x ∈ X, x ^ p = 1) :
    ∃ E : Subgroup G, E ≤ X ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 2 := by
  have hp : p.Prime := Fact.out
  have hZc := card_commutator_of_extraspecial hcard hZ
  have hZX : ⁅X, X⁆ ≤ X := Subgroup.commutator_le_self X
  obtain ⟨z₀, hz₀Z, hz₀1, hZeq⟩ :=
    CFSG.RankThree.PartTwo.Sec5.exists_eq_zpowers_of_card_eq_prime hp hZc
  obtain ⟨x, hxX, hxZ⟩ : ∃ x ∈ X, x ∉ ⁅X, X⁆ := by
    by_contra hno
    push Not at hno
    have := Subgroup.card_le_of_le (show X ≤ (⁅X, X⁆ : Subgroup G) from hno)
    rw [hcard, hZc] at this
    have := Nat.pow_lt_pow_right hp.one_lt (show 1 < 3 by norm_num)
    rw [pow_one] at this
    omega
  have hA : CFSG.Assembly.IsElemAbelian p (Subgroup.zpowers z₀) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩
    · obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp a.2
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp b.2
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hi, ← hj, ← zpow_add, ← zpow_add, add_comm]
    · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hexp z₀ (hZX hz₀Z),
        one_zpow]
  have hxA : x ∉ Subgroup.zpowers z₀ := fun h => hxZ (hZeq ▸ h)
  have hxA' : ∀ a ∈ Subgroup.zpowers z₀, a * x = x * a := by
    intro a ha
    have haZ : a ∈ ⁅X, X⁆ := hZeq ▸ ha
    rw [hZ] at haZ
    exact (Subgroup.mem_centralizer_iff.mp haZ.2 x hxX).symm
  obtain ⟨hE, hEcard⟩ :=
    CFSG.RankThree.PartTwo.Sec5.isElemAbelian_sup_zpowers hA hxA (hexp x hxX) hxA'
  refine ⟨Subgroup.zpowers z₀ ⊔ Subgroup.zpowers x,
    sup_le (Subgroup.zpowers_le.mpr (hZX hz₀Z)) (Subgroup.zpowers_le.mpr hxX), ⟨hE.1, hE.2⟩, ?_⟩
  rw [hEcard, Nat.card_zpowers, ← hZc, hZeq, Nat.card_zpowers]
  ring

end CFSG.AGLEmbedding
