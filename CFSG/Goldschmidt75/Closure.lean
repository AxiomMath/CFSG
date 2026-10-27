module

public import CFSG.Goldschmidt75.Basic

public section

namespace CFSG.Goldschmidt75

open CFSG.Open CFSG.Goldschmidt Subgroup
open scoped Pointwise

variable {G : Type*} [Group G]

@[expose] def FullyNormalized (p : ℕ) (P S₀ : Subgroup G) : Prop :=
  Nat.card ↥(P ⊓ normalizer (S₀ : Set G)) =
    p ^ (Nat.card ↥(normalizer (S₀ : Set G))).factorization p

theorem mem_normalizer_conjSub_iff {y x : G} {A : Subgroup G} :
    x ∈ normalizer (conjSub y A : Set G) ↔ y * x * y⁻¹ ∈ normalizer (A : Set G) := by
  rw [mem_normalizer_iff, mem_normalizer_iff]
  constructor
  · intro h w
    have := h (y⁻¹ * w * y)
    simp only [mem_conjSub] at this
    rw [show y * (y⁻¹ * w * y) * y⁻¹ = w by group,
      show y * (x * (y⁻¹ * w * y) * x⁻¹) * y⁻¹ = y * x * y⁻¹ * w * (y * x * y⁻¹)⁻¹ by group]
      at this
    exact this
  · intro h z
    simp only [mem_conjSub]
    rw [h (y * z * y⁻¹),
      show y * x * y⁻¹ * (y * z * y⁻¹) * (y * x * y⁻¹)⁻¹ = y * (x * z * x⁻¹) * y⁻¹ by group]

theorem normalizer_conjSub (y : G) (A : Subgroup G) :
    normalizer (conjSub y A : Set G) = conjSub y (normalizer (A : Set G)) := by
  ext x
  rw [mem_normalizer_conjSub_iff, mem_conjSub]

section Closure

variable {p : ℕ} (P : Sylow p G) {S : Subgroup G}

theorem sylow_le_normalizer (hSP : S ≤ P) (hS : fusionStronglyClosed (S : Set G) P) :
    (P : Subgroup G) ≤ normalizer (S : Set G) := by
  intro x hx
  rw [mem_normalizer_iff]
  intro s
  constructor
  · intro hs
    have := conj_mem_of_stronglyClosed hSP hS (P.inv_mem hx) hs
    simpa using this
  · intro hs
    have := conj_mem_of_stronglyClosed hSP hS hx hs
    simpa [mul_assoc] using this

theorem conjSub_le (hS : fusionStronglyClosed (S : Set G) P) {S₀ : Subgroup G} (hS₀ : S₀ ≤ S)
    {g : G} (hg : conjSub g S₀ ≤ P) : conjSub g S₀ ≤ S := by
  intro x hx
  have hx' := mem_conjSub.1 hx
  have h := hS _ (hS₀ hx') g (by simpa [mul_assoc] using hg hx)
  simpa [mul_assoc] using h

theorem fullyNormalized_self [Finite G] [Fact p.Prime] (hSP : S ≤ P)
    (hS : fusionStronglyClosed (S : Set G) P) :
    FullyNormalized p P S := by
  have hPN := sylow_le_normalizer P hSP hS
  unfold FullyNormalized
  rw [inf_eq_left.mpr hPN]
  set N := normalizer (S : Set G)
  have hP' : Nat.card (P.subtype hPN : Subgroup N) = p ^ (Nat.card N).factorization p :=
    Sylow.card_eq_multiplicity _
  rw [← hP']
  exact (Nat.card_congr (subgroupOfEquivOfLe hPN).toEquiv).symm.trans rfl

theorem le_normalizer_inf (hSP : S ≤ P) (hS : fusionStronglyClosed (S : Set G) P)
    {Q : Subgroup G} (hQ : Q ≤ P) : Q ≤ normalizer ((S ⊓ Q : Subgroup G) : Set G) := by
  intro x hx
  have hxS := sylow_le_normalizer P hSP hS (hQ hx)
  rw [mem_normalizer_iff] at hxS ⊢
  intro y
  simp only [mem_inf]
  rw [hxS y]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, Q.mul_mem (Q.mul_mem hx h2) (Q.inv_mem hx)⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    have := Q.mul_mem (Q.mul_mem (Q.inv_mem hx) h2) hx
    simpa [mul_assoc] using this

theorem normalizer_le_normalizer_inf [Finite G] (hS : fusionStronglyClosed (S : Set G) P)
    {Q : Subgroup G} (hQ : Q ≤ P) :
    normalizer (Q : Set G) ≤ normalizer ((S ⊓ Q : Subgroup G) : Set G) := by
  intro h hh
  apply mem_normalizer_of_conjSub_eq
  have hQh : conjSub h Q = Q := by
    have := conjSub_eq_of_mem_normalizer ((normalizer (Q : Set G)).inv_mem hh)
    have e : conjSub h (conjSub h⁻¹ Q) = Q := by
      rw [← conjSub_mul, inv_mul_cancel, conjSub_one]
    rw [this] at e
    exact e
  have hle : conjSub h (S ⊓ Q) ≤ S ⊓ Q := by
    intro x hx
    have hx' := mem_conjSub.1 hx
    have hxQ : x ∈ conjSub h Q := mem_conjSub.2 hx'.2
    rw [hQh] at hxQ
    have hxS : x ∈ S := by
      have := hS _ hx'.1 h (by simpa [mul_assoc] using hQ hxQ)
      simpa [mul_assoc] using this
    exact ⟨hxS, hxQ⟩
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_conjSub])

theorem exists_mem_center [Finite G] [Fact p.Prime] (hSP : S ≤ P)
    (hS : fusionStronglyClosed (S : Set G) P) (hS1 : S ≠ ⊥) :
    ∃ z ∈ S, z ≠ 1 ∧ z ∈ centralizer ((P : Subgroup G) : Set G) := by
  have : Group.IsNilpotent (P : Subgroup G) := P.isPGroup'.isNilpotent
  have : (S.subgroupOf P).Normal := normal_subgroupOf_of_stronglyClosed hSP hS
  have hne : S.subgroupOf P ≠ ⊥ := by
    intro h
    apply hS1
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hSP hx⟩ : (P : Subgroup G)) ∈ S.subgroupOf P := hx
    rw [h, mem_bot] at this
    simpa using congrArg Subtype.val this
  obtain ⟨z, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  refine ⟨((z : (P : Subgroup G)) : G), (mem_inf.1 z.2).1, fun h => hz1 (Subtype.ext
    (Subtype.ext h)), ?_⟩
  rw [mem_centralizer_iff]
  intro y hy
  have := mem_center_iff.mp (mem_inf.1 z.2).2 ⟨y, hy⟩
  exact congrArg Subtype.val this

theorem mem_normalizer_of_mem_normalizer_subgroupOf {S S₀ : Subgroup G} (hle : S₀ ≤ S)
    {s : S} (hs : s ∈ normalizer ((S₀.subgroupOf S : Subgroup S) : Set S)) :
    (s : G) ∈ normalizer (S₀ : Set G) := by
  rw [mem_normalizer_iff] at hs ⊢
  intro x
  by_cases hx : x ∈ S
  · have := hs ⟨x, hx⟩
    simpa [mem_subgroupOf] using this
  · have h1 : x ∉ S₀ := fun h => hx (hle h)
    have h2 : (s : G) * x * (s : G)⁻¹ ∉ S₀ := by
      intro h
      apply hx
      have := S.mul_mem (S.mul_mem (S.inv_mem s.2) (hle h)) s.2
      simpa [mul_assoc] using this
    exact iff_of_false h1 h2

theorem lt_inf_normalizer [Finite G] [Fact p.Prime] {S S₀ : Subgroup G} (hSp : IsPGroup p S)
    (hlt : S₀ < S) : S₀ < S ⊓ normalizer (S₀ : Set G) := by
  have : Group.IsNilpotent S := hSp.isNilpotent
  have hnc := Group.normalizerCondition_of_isNilpotent (G := S)
  have hH : S₀.subgroupOf S < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro h
    rw [subgroupOf_eq_top] at h
    exact hlt.not_ge h
  obtain ⟨s, hs, hsn⟩ := IsConcreteLE.exists_of_lt (hnc _ hH)
  refine lt_of_le_of_ne (le_inf hlt.le Subgroup.le_normalizer) fun heq => hsn ?_
  have hsG : (s : G) ∈ S ⊓ normalizer (S₀ : Set G) :=
    ⟨s.2, mem_normalizer_of_mem_normalizer_subgroupOf hlt.le hs⟩
  rw [← heq] at hsG
  exact hsG

theorem conjSub_mono {g : G} {A B : Subgroup G} (h : A ≤ B) : conjSub g A ≤ conjSub g B :=
  Subgroup.map_mono h

theorem card_le_of_isPGroup [Finite G] [Fact p.Prime] {H K : Subgroup G} (hHK : H ≤ K)
    (hH : IsPGroup p H) : Nat.card H ≤ p ^ (Nat.card K).factorization p := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hH
  have hdvd : p ^ k ∣ Nat.card K := hk ▸ Subgroup.card_dvd_of_le hHK
  rw [hk]
  exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos
    (((Fact.out : p.Prime).pow_dvd_iff_le_factorization Nat.card_pos.ne').mp hdvd)

theorem exists_conjSub_eq [Finite G] [Fact p.Prime] (Q : Sylow p G) :
    ∃ y : G, conjSub y (Q : Subgroup G) = P := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q P
  refine ⟨g⁻¹, ?_⟩
  ext x
  rw [mem_conjSub, inv_inv, ← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
  constructor
  · intro h
    exact ⟨g⁻¹ * x * g, h, by simp [MulAut.conj_apply, mul_assoc]⟩
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy

theorem exists_conj_fullyNormalized [Finite G] [Fact p.Prime] (hSP : S ≤ P)
    (hS : fusionStronglyClosed (S : Set G) P) {S₀ : Subgroup G} (hS₀ : S₀ ≤ S) :
    ∃ y : G, conjSub y ((P : Subgroup G) ⊓ normalizer (S₀ : Set G)) ≤ P ∧ conjSub y S₀ ≤ S ∧
      FullyNormalized p P (conjSub y S₀) := by
  set N := normalizer (S₀ : Set G)
  set A := (P : Subgroup G) ⊓ N
  have hAp : IsPGroup p A := P.isPGroup'.to_le inf_le_left
  obtain ⟨R, hR⟩ := (hAp.comap_subtype (K := N)).exists_le_sylow
  set RG := (R : Subgroup N).map N.subtype
  obtain ⟨Q, hQ⟩ := (R.2.map N.subtype).exists_le_sylow
  obtain ⟨y, hy⟩ := exists_conjSub_eq P Q
  have hAR : A ≤ RG := fun a ha => ⟨⟨a, ha.2⟩, hR (by simpa [mem_subgroupOf] using ha), rfl⟩
  have hRP : conjSub y RG ≤ P := hy ▸ conjSub_mono hQ
  have hS₀A : S₀ ≤ A := le_inf (hS₀.trans hSP) Subgroup.le_normalizer
  refine ⟨y, (conjSub_mono hAR).trans hRP,
    conjSub_le P hS hS₀ ((conjSub_mono (hS₀A.trans hAR)).trans hRP), ?_⟩
  unfold FullyNormalized
  rw [normalizer_conjSub, card_conjSub]
  refine le_antisymm ((card_le_of_isPGroup (K := conjSub y N) inf_le_right
    (P.isPGroup'.to_le inf_le_left)).trans_eq (by rw [card_conjSub])) ?_
  have hRN : conjSub y RG ≤ (P : Subgroup G) ⊓ conjSub y N :=
    le_inf hRP (conjSub_mono (Subgroup.map_subtype_le _))
  calc p ^ (Nat.card N).factorization p = Nat.card R := (Sylow.card_eq_multiplicity R).symm
    _ = Nat.card RG := (Nat.card_congr
        ((R : Subgroup N).equivMapOfInjective _ N.subtype_injective).toEquiv)
    _ = Nat.card (conjSub y RG) := (card_conjSub y RG).symm
    _ ≤ _ := Subgroup.card_le_of_le hRN

end Closure

end CFSG.Goldschmidt75
