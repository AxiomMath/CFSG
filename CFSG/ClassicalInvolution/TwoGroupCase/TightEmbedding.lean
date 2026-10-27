module

public import CFSG.ClassicalInvolution.Basic

public section

namespace CFSG.ClassicalInvolution

open CFSG.Open
open scoped Pointwise

variable {G : Type*} [Group G]

abbrev conjSubgroup (g : G) (A : Subgroup G) : Subgroup G :=
  A.map (MulAut.conj g).toMonoidHom

theorem mem_conjSubgroup_iff {A : Subgroup G} {g x : G} :
    x ∈ conjSubgroup g A ↔ g⁻¹ * x * g ∈ A := mem_map_conj_iff

theorem mem_conjSubgroup_of_mem {A : Subgroup G} {g a : G} (ha : a ∈ A) :
    g * a * g⁻¹ ∈ conjSubgroup g A :=
  Subgroup.mem_map.mpr ⟨a, ha, by simp⟩

theorem conjSubgroup_mono {g : G} {A B : Subgroup G} (h : A ≤ B) :
    conjSubgroup g A ≤ conjSubgroup g B := Subgroup.map_mono h

theorem conjSubgroup_inf (g : G) (A B : Subgroup G) :
    conjSubgroup g (A ⊓ B) = conjSubgroup g A ⊓ conjSubgroup g B :=
  Subgroup.map_inf_eq A B (MulAut.conj g).toMonoidHom (MulAut.conj g).injective

theorem conjSubgroup_conjSubgroup (g h : G) (A : Subgroup G) :
    conjSubgroup g (conjSubgroup h A) = conjSubgroup (g * h) A := by
  unfold conjSubgroup
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [mul_assoc]

theorem conjSubgroup_one (A : Subgroup G) : conjSubgroup 1 A = A := by
  ext x; simp

theorem conjSubgroup_inv_conjSubgroup (g : G) (A : Subgroup G) :
    conjSubgroup g⁻¹ (conjSubgroup g A) = A := by
  rw [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]

theorem conjSubgroup_conjSubgroup_inv (g : G) (A : Subgroup G) :
    conjSubgroup g (conjSubgroup g⁻¹ A) = A := by
  rw [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one]

theorem conjSubgroup_eq_self_iff {g : G} {A : Subgroup G} :
    conjSubgroup g A = A ↔ g ∈ Subgroup.normalizer (A : Set G) :=
  map_conj_eq_iff_mem_normalizer

theorem conjSubgroup_eq_self_of_mem {g : G} {A : Subgroup G} (hg : g ∈ A) :
    conjSubgroup g A = A :=
  conjSubgroup_eq_self_iff.mpr (Subgroup.le_normalizer hg)

theorem card_conjSubgroup (g : G) (A : Subgroup G) : Nat.card (conjSubgroup g A) = Nat.card A :=
  (Nat.card_congr (MulEquiv.subgroupMap (MulAut.conj g) A).toEquiv).symm

theorem isPGroup_conjSubgroup {p : ℕ} {g : G} {A : Subgroup G} (hA : IsPGroup p A) :
    IsPGroup p (conjSubgroup g A) :=
  hA.of_equiv (MulEquiv.subgroupMap (MulAut.conj g) A)

theorem conjSubgroup_eq_bot_iff {g : G} {A : Subgroup G} : conjSubgroup g A = ⊥ ↔ A = ⊥ :=
  Subgroup.map_eq_bot_iff_of_injective A (MulAut.conj g).injective

theorem mem_normalizer_conjSubgroup_iff {A : Subgroup G} {g x : G} :
    x ∈ Subgroup.normalizer (conjSubgroup g A : Set G) ↔
      g⁻¹ * x * g ∈ Subgroup.normalizer (A : Set G) := by
  rw [← conjSubgroup_eq_self_iff, ← conjSubgroup_eq_self_iff]
  constructor
  · intro h
    have : conjSubgroup (g⁻¹ * x * g) A = conjSubgroup g⁻¹ (conjSubgroup x (conjSubgroup g A)) := by
      rw [conjSubgroup_conjSubgroup, conjSubgroup_conjSubgroup]
    rw [this, h, conjSubgroup_inv_conjSubgroup]
  · intro h
    have : conjSubgroup x (conjSubgroup g A) = conjSubgroup g (conjSubgroup (g⁻¹ * x * g) A) := by
      rw [conjSubgroup_conjSubgroup, conjSubgroup_conjSubgroup]
      congr 1
      group
    rw [this, h]

@[expose] def IsSylow2Of (P A : Subgroup G) : Prop :=
  P ≤ A ∧ IsPGroup 2 P ∧ ∀ P' : Subgroup G, P' ≤ A → IsPGroup 2 P' → P ≤ P' → P' = P

theorem isSylow2Of_map_subtype {A : Subgroup G} (P : Sylow 2 A) :
    IsSylow2Of (P.map A.subtype) A := by
  refine ⟨Subgroup.map_subtype_le _, P.isPGroup'.map A.subtype, fun P' hP'A hP'2 hle => ?_⟩
  have hP'2' : IsPGroup 2 (P'.subgroupOf A) :=
    hP'2.of_equiv (Subgroup.subgroupOfEquivOfLe hP'A).symm
  have hle' : (P : Subgroup A) ≤ P'.subgroupOf A := fun x hx =>
    hle ⟨x, hx, rfl⟩
  have hPeq : P'.subgroupOf A = P := P.is_maximal' hP'2' hle'
  rw [← Subgroup.map_subgroupOf_eq_of_le hP'A, hPeq]

theorem IsSylow2Of.le_left {P A : Subgroup G} (h : IsSylow2Of P A) : P ≤ A := h.1

theorem IsSylow2Of.isPGroup {P A : Subgroup G} (h : IsSylow2Of P A) : IsPGroup 2 P := h.2.1

theorem IsSylow2Of.conj {P A : Subgroup G} (h : IsSylow2Of P A) (g : G) :
    IsSylow2Of (conjSubgroup g P) (conjSubgroup g A) := by
  refine ⟨conjSubgroup_mono h.1, isPGroup_conjSubgroup h.2.1, fun P' hP'A hP'2 hle => ?_⟩
  have h1 : conjSubgroup g⁻¹ P' ≤ A := by
    have := conjSubgroup_mono (g := g⁻¹) hP'A
    rwa [conjSubgroup_inv_conjSubgroup] at this
  have h2 : P ≤ conjSubgroup g⁻¹ P' := by
    have := conjSubgroup_mono (g := g⁻¹) hle
    rwa [conjSubgroup_inv_conjSubgroup] at this
  have h3 := h.2.2 _ h1 (isPGroup_conjSubgroup hP'2) h2
  rw [← conjSubgroup_conjSubgroup_inv g P', h3]

structure TightData (K H Q S : Subgroup G) : Prop where
  tight : classicalInvolutionTightlyEmbedded K
  sylow : IsSylow2Of Q (H ⊓ K)
  ne_bot : Q ≠ ⊥
  two : IsPGroup 2 S
  le_H : S ≤ H
  le_S : Q ≤ S

theorem conjSubgroup_eq_of_tight_of_two_group_le [Finite G] {K : Subgroup G}
    (hK : classicalInvolutionTightlyEmbedded K) {g : G} {P : Subgroup G} (hP : IsPGroup 2 P)
    (hP1 : P ≠ ⊥) (hPK : P ≤ K) (hPKg : P ≤ conjSubgroup g K) : conjSubgroup g K = K := by
  by_contra hne
  have hg : g ∉ Subgroup.normalizer (K : Set G) := fun h => hne (conjSubgroup_eq_self_iff.mpr h)
  obtain ⟨u, huP, hu⟩ := exists_mem_orderOf_eq_two_of_isPGroup_subgroup hP hP1
  have hu2 : 2 ∣ Nat.card (K ⊓ conjSubgroup g K : Subgroup G) := by
    have := Subgroup.orderOf_dvd_natCard (K ⊓ conjSubgroup g K) (x := u) ⟨hPK huP, hPKg huP⟩
    rwa [hu] at this
  exact (hK g hg).not_two_dvd_nat hu2

theorem tightlyEmbedded_conjSubgroup [Finite G] {K : Subgroup G}
    (hK : classicalInvolutionTightlyEmbedded K) (g : G) :
    classicalInvolutionTightlyEmbedded (conjSubgroup g K) := by
  intro x hx
  have hx' : g⁻¹ * x * g ∉ Subgroup.normalizer (K : Set G) := fun h =>
    hx (mem_normalizer_conjSubgroup_iff.mpr h)
  have h1 : conjSubgroup x (conjSubgroup g K) = conjSubgroup g (conjSubgroup (g⁻¹ * x * g) K) := by
    rw [conjSubgroup_conjSubgroup, conjSubgroup_conjSubgroup]
    congr 1
    group
  have h2 := hK _ hx'
  show Odd (Nat.card (conjSubgroup g K ⊓ conjSubgroup x (conjSubgroup g K) : Subgroup G))
  rw [h1, ← conjSubgroup_inf, card_conjSubgroup]
  exact h2

theorem conjSubgroup_inf_eq_or_inf_eq_bot_of_tight [Finite G] {K S : Subgroup G}
    (hK : classicalInvolutionTightlyEmbedded K) (hS : IsPGroup 2 S) {g : G}
    (hg : g ∈ Subgroup.normalizer (S : Set G)) :
    conjSubgroup g (S ⊓ K) = S ⊓ K ∨ (S ⊓ K) ⊓ conjSubgroup g (S ⊓ K) = ⊥ := by
  have hQg : conjSubgroup g (S ⊓ K) = S ⊓ conjSubgroup g K := by
    rw [conjSubgroup_inf, conjSubgroup_eq_self_iff.mpr hg]
  by_cases h : (S ⊓ K) ⊓ conjSubgroup g (S ⊓ K) = ⊥
  · exact Or.inr h
  · left
    have hKK : conjSubgroup g K = K :=
      conjSubgroup_eq_of_tight_of_two_group_le hK
        (hS.to_le (inf_le_left.trans inf_le_left)) h
        (inf_le_left.trans inf_le_right)
        (inf_le_right.trans (conjSubgroup_mono inf_le_right))
    rw [hQg, hKK]

namespace TightData

variable [Finite G] {K H Q S : Subgroup G} (d : TightData K H Q S)
include d

omit [Finite G] in
theorem le_K : Q ≤ K := d.sylow.1.trans inf_le_right

omit [Finite G] in
theorem isPGroup_Q : IsPGroup 2 Q := d.sylow.2.1

omit [Finite G] in
theorem eq_inf : Q = S ⊓ K :=
  (d.sylow.2.2 (S ⊓ K) (inf_le_inf_right K d.le_H) (d.two.to_le inf_le_left)
    (le_inf d.le_S d.le_K)).symm

theorem conj {g : G} (hgH : g ∈ H) (hgS : conjSubgroup g Q ≤ S) :
    TightData (conjSubgroup g K) H (conjSubgroup g Q) S := by
  refine ⟨tightlyEmbedded_conjSubgroup d.tight g, ?_, ?_, d.two, d.le_H, hgS⟩
  · have := d.sylow.conj g
    rwa [conjSubgroup_inf, conjSubgroup_eq_self_of_mem hgH] at this
  · exact fun h => d.ne_bot (conjSubgroup_eq_bot_iff.mp h)

theorem inf_conj_eq_bot {g : G} (hgH : g ∈ H) (hgS : conjSubgroup g Q ≤ S)
    (hne : conjSubgroup g Q ≠ Q) : Q ⊓ conjSubgroup g Q = ⊥ := by
  by_contra h
  have d' := d.conj hgH hgS
  have hK : conjSubgroup g K = K :=
    conjSubgroup_eq_of_tight_of_two_group_le d.tight (d.isPGroup_Q.to_le inf_le_left) h
      (inf_le_left.trans d.le_K) (inf_le_right.trans d'.le_K)
  apply hne
  rw [d'.eq_inf, hK, ← d.eq_inf]

theorem conj_eq_or_inf_eq_bot {g : G} (hg : g ∈ Subgroup.normalizer (S : Set G)) :
    conjSubgroup g Q = Q ∨ Q ⊓ conjSubgroup g Q = ⊥ := by
  rw [d.eq_inf]
  exact conjSubgroup_inf_eq_or_inf_eq_bot_of_tight d.tight d.two hg

theorem normalizer_le_normalizer {X : Subgroup G} (hXQ : X ≤ Q) (hX1 : X ≠ ⊥) :
    Subgroup.normalizer (X : Set G) ≤ Subgroup.normalizer (K : Set G) := by
  intro g hg
  rw [← conjSubgroup_eq_self_iff]
  refine conjSubgroup_eq_of_tight_of_two_group_le d.tight (d.isPGroup_Q.to_le hXQ) hX1
    (hXQ.trans d.le_K) ?_
  rw [← conjSubgroup_eq_self_iff.mpr hg]
  exact conjSubgroup_mono (hXQ.trans d.le_K)
  
theorem normalizer_inf_le {X : Subgroup G} (hXQ : X ≤ Q) (hX1 : X ≠ ⊥) {g : G} (hgS : g ∈ S)
    (hg : g ∈ Subgroup.normalizer (X : Set G)) : g ∈ Subgroup.normalizer (Q : Set G) := by
  have hK := conjSubgroup_eq_self_iff.mpr (d.normalizer_le_normalizer hXQ hX1 hg)
  rw [← conjSubgroup_eq_self_iff, d.eq_inf, conjSubgroup_inf, hK,
    conjSubgroup_eq_self_of_mem hgS]

end TightData

@[expose] def TightlyEmbeddedIn (T S : Subgroup G) : Prop :=
  Even (Nat.card T) ∧
    ∀ s ∈ S, s ∉ Subgroup.normalizer (T : Set G) → Odd (Nat.card (T ⊓ conjSubgroup s T : Subgroup G))

theorem tightlyEmbeddedIn_of_ti [Finite G] {S T : Subgroup G} (hT2 : IsPGroup 2 T) (hT1 : T ≠ ⊥)
    (hTI : ∀ s ∈ S, conjSubgroup s T = T ∨ T ⊓ conjSubgroup s T = ⊥) : TightlyEmbeddedIn T S := by
  refine ⟨?_, fun s hs hsn => ?_⟩
  · obtain ⟨u, huT, hu⟩ := exists_mem_orderOf_eq_two_of_isPGroup_subgroup hT2 hT1
    have := Subgroup.orderOf_dvd_natCard T huT
    rw [hu] at this
    exact even_iff_two_dvd.mpr this
  · rcases hTI s hs with h | h
    · exact absurd (conjSubgroup_eq_self_iff.mp h) hsn
    · rw [h, Subgroup.card_bot]
      exact odd_one

namespace TightData

variable [Finite G] {K H Q S : Subgroup G} (d : TightData K H Q S)
include d

theorem tightlyEmbeddedIn : TightlyEmbeddedIn Q S :=
  tightlyEmbeddedIn_of_ti d.isPGroup_Q d.ne_bot fun _ hs =>
    d.conj_eq_or_inf_eq_bot (Subgroup.le_normalizer hs)

end TightData

theorem exists_mem_normalizer_not_mem [Finite G] {p : ℕ} [Fact p.Prime] {S N : Subgroup G}
    (hS : IsPGroup p S)
    (hNS : N ≤ S) (hne : N ≠ S) :
    ∃ s ∈ S, s ∈ Subgroup.normalizer (N : Set G) ∧ s ∉ N := by
  have : Group.IsNilpotent S := hS.isNilpotent
  have hnc : NormalizerCondition S := Group.normalizerCondition_of_isNilpotent
  have hlt : N.subgroupOf S < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun h => hne (le_antisymm hNS fun x hx => ?_)
    have : (⟨x, hx⟩ : S) ∈ N.subgroupOf S := by rw [h]; exact Subgroup.mem_top _
    exact this
  obtain ⟨x, hx, hxn⟩ := IsConcreteLE.exists_of_lt (hnc _ hlt)
  refine ⟨(x : G), x.2, ?_, hxn⟩
  rw [Subgroup.mem_normalizer_iff]
  intro g
  by_cases hgS : g ∈ S
  · have := (Subgroup.mem_normalizer_iff.mp hx) ⟨g, hgS⟩
    exact this
  · have hg1 : g ∉ N := fun h => hgS (hNS h)
    have hg2 : (x : G) * g * (x : G)⁻¹ ∉ N := fun h => by
      have h1 := S.mul_mem (S.mul_mem (S.inv_mem x.2) (hNS h)) x.2
      have h3 : (x : G)⁻¹ * ((x : G) * g * (x : G)⁻¹) * (x : G) = g := by group
      rw [h3] at h1
      exact hgS h1
    exact ⟨fun h => absurd h hg1, fun h => absurd h hg2⟩

namespace TightData

variable [Finite G] {K H Q S : Subgroup G} (d : TightData K H Q S)
include d

theorem card_sq_le_card_normalizer (hS : ¬ S ≤ Subgroup.normalizer (Q : Set G)) :
    Nat.card Q * Nat.card Q ≤ Nat.card (S ⊓ Subgroup.normalizer (Q : Set G) : Subgroup G) := by
  set N : Subgroup G := S ⊓ Subgroup.normalizer (Q : Set G) with hN
  have hNS : N ≤ S := inf_le_left
  have hQN : Q ≤ N := le_inf d.le_S Subgroup.le_normalizer
  have hne : N ≠ S := fun e => hS (e ▸ inf_le_right)
  obtain ⟨x, hxS, hxN, hxnot⟩ := exists_mem_normalizer_not_mem d.two hNS hne
  have hxQ : conjSubgroup x Q ≠ Q := fun e => hxnot ⟨hxS, conjSubgroup_eq_self_iff.mp e⟩
  have hle : conjSubgroup x Q ≤ N := by
    rw [← conjSubgroup_eq_self_iff.mpr hxN]
    exact conjSubgroup_mono hQN
  have hbot := d.inf_conj_eq_bot (d.le_H hxS) (hle.trans hNS) hxQ
  have hinj : Function.Injective
      (fun p : Q × conjSubgroup x Q =>
        (⟨(p.1 : G) * p.2, N.mul_mem (hQN p.1.2) (hle p.2.2)⟩ : N)) := by
    intro p p' hpp
    have h1 : (p.1 : G) * p.2 = p'.1 * p'.2 := congrArg Subtype.val hpp
    have h2 : (p'.1 : G)⁻¹ * p.1 = p'.2 * (p.2 : G)⁻¹ := by
      calc (p'.1 : G)⁻¹ * p.1 = (p'.1 : G)⁻¹ * (p.1 * p.2) * (p.2 : G)⁻¹ := by group
        _ = (p'.1 : G)⁻¹ * (p'.1 * p'.2) * (p.2 : G)⁻¹ := by rw [h1]
        _ = p'.2 * (p.2 : G)⁻¹ := by group
    have h3 : (p'.1 : G)⁻¹ * p.1 ∈ Q ⊓ conjSubgroup x Q :=
      ⟨Q.mul_mem (Q.inv_mem p'.1.2) p.1.2, h2 ▸ (conjSubgroup x Q).mul_mem p'.2.2
        ((conjSubgroup x Q).inv_mem p.2.2)⟩
    rw [hbot, Subgroup.mem_bot] at h3
    have h4 : p.1 = p'.1 := Subtype.ext (inv_mul_eq_one.mp h3).symm
    have h5 : (p.2 : G) = p'.2 := by
      have : (p.1 : G) * p.2 = p.1 * p'.2 := by rw [h1, ← h4]
      exact mul_left_cancel this
    exact Prod.ext h4 (Subtype.ext h5)
  have hcard := Nat.card_le_card_of_injective _ hinj
  rwa [Nat.card_prod, card_conjSubgroup] at hcard

theorem le_normalizer_of_card_le (h : Nat.card S ≤ Nat.card Q * Nat.card Q) :
    S ≤ Subgroup.normalizer (Q : Set G) := by
  by_contra hS
  have h1 := d.card_sq_le_card_normalizer hS
  have h2 : Nat.card (S ⊓ Subgroup.normalizer (Q : Set G) : Subgroup G) ≤ Nat.card S :=
    Subgroup.card_le_of_le inf_le_left
  have h3 : S ⊓ Subgroup.normalizer (Q : Set G) = S :=
    Subgroup.eq_of_le_of_card_ge inf_le_left (by omega)
  exact hS (h3 ▸ inf_le_right)

theorem commute_of_le_normalizer {g : G} (hgH : g ∈ H) (hne : conjSubgroup g Q ≠ Q)
    (hle : conjSubgroup g Q ≤ S ⊓ Subgroup.normalizer (Q : Set G)) :
    Q ⊓ conjSubgroup g Q = ⊥ ∧ ∀ x ∈ Q, ∀ y ∈ conjSubgroup g Q, x * y = y * x := by
  have hgS : conjSubgroup g Q ≤ S := hle.trans inf_le_left
  have hgN : conjSubgroup g Q ≤ Subgroup.normalizer (Q : Set G) := hle.trans inf_le_right
  have hbot := d.inf_conj_eq_bot hgH hgS hne
  have d' := d.conj hgH hgS
  set X : Subgroup G := conjSubgroup g Q ⊔ Q with hX
  have hXS : X ≤ S := sup_le hgS d.le_S
  have hXcard : Nat.card X ≤ Nat.card (conjSubgroup g Q) * Nat.card (conjSubgroup g Q) := by
    have hmul : (X : Set G) = (conjSubgroup g Q : Set G) * (Q : Set G) :=
      Subgroup.coe_mul_of_left_le_normalizer_right _ _ hgN
    let f : conjSubgroup g Q × Q → X := fun p => ⟨p.1 * p.2, by
      rw [← SetLike.mem_coe, hmul]
      exact Set.mul_mem_mul p.1.2 p.2.2⟩
    have hf : Function.Surjective f := by
      rintro ⟨x, hx⟩
      rw [← SetLike.mem_coe, hmul] at hx
      obtain ⟨a, ha, b, hb, rfl⟩ := hx
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
    have h1 := Nat.card_le_card_of_surjective f hf
    rw [Nat.card_prod, ← card_conjSubgroup g Q] at h1
    exact h1
  have d'' : TightData (conjSubgroup g K) H (conjSubgroup g Q) X :=
    ⟨d'.tight, d'.sylow, d'.ne_bot, d.two.to_le hXS, hXS.trans d.le_H, le_sup_left⟩
  have hXN : X ≤ Subgroup.normalizer (conjSubgroup g Q : Set G) :=
    d''.le_normalizer_of_card_le hXcard
  refine ⟨hbot, fun x hx y hy => ?_⟩
  have hQX : Q ≤ X := le_sup_right
  have hxN : x ∈ Subgroup.normalizer (conjSubgroup g Q : Set G) := hXN (hQX hx)
  have hyN : y ∈ Subgroup.normalizer (Q : Set G) := hgN hy
  have h1 : x * y * x⁻¹ * y⁻¹ ∈ conjSubgroup g Q :=
    (conjSubgroup g Q).mul_mem ((Subgroup.mem_normalizer_iff.mp hxN y).mp hy)
      ((conjSubgroup g Q).inv_mem hy)
  have h2 : x * y * x⁻¹ * y⁻¹ ∈ Q := by
    have h := (Subgroup.mem_normalizer_iff.mp hyN x⁻¹).mp (Q.inv_mem hx)
    have e : x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) := by group
    rw [e]
    exact Q.mul_mem hx h
  have h3 : x * y * x⁻¹ * y⁻¹ ∈ Q ⊓ conjSubgroup g Q := ⟨h2, h1⟩
  rw [hbot, Subgroup.mem_bot] at h3
  calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
    _ = y * x := by rw [h3, one_mul]

end TightData

theorem TightData.of_sylow [Finite G] {K H S : Subgroup G}
    (hK : classicalInvolutionTightlyEmbedded K) (Q : Sylow 2 ↥(H ⊓ K))
    (hQ1 : (Q : Subgroup ↥(H ⊓ K)).map (H ⊓ K).subtype ≠ ⊥) (hS2 : IsPGroup 2 S) (hSH : S ≤ H)
    (hQS : (Q : Subgroup ↥(H ⊓ K)).map (H ⊓ K).subtype ≤ S) :
    TightData K H ((Q : Subgroup ↥(H ⊓ K)).map (H ⊓ K).subtype) S :=
  ⟨hK, isSylow2Of_map_subtype Q, hQ1, hS2, hSH, hQS⟩

theorem normalizer_eq_centralizer_and_tightlyEmbedded [Finite G] {R : Subgroup G} (S : Sylow 2 R)
    (hS : ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup R) ≃* QuaternionGroup (2 ^ (r - 2)))) {t : G}
    (ht : t ∈ (S : Subgroup R).map R.subtype) (hto : orderOf t = 2)
    (hRC : R ≤ Subgroup.centralizer ({t} : Set G))
    (hRn : (R.subgroupOf (Subgroup.centralizer ({t} : Set G))).Normal) :
    Subgroup.normalizer (R : Set G) = Subgroup.centralizer ({t} : Set G) ∧
      classicalInvolutionTightlyEmbedded R := by
  have htR : t ∈ R := Subgroup.map_subtype_le _ ht
  have hCN : Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (R : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRC).mp hRn
  have hTE : classicalInvolutionTightlyEmbedded R :=
    (tightlyEmbedded_iff_centralizer_le_normalizer htR hto hRC S hS).mpr hCN
  exact ⟨(centralizer_eq_normalizer_of_tightlyEmbedded htR hto
    (fun _ hu hu2 => eq_of_orderOf_eq_two_of_quaternion_sylow htR hto hRC S hS hu hu2) hTE).symm,
    hTE⟩

end CFSG.ClassicalInvolution
